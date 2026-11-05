#!/usr/bin/env python3.12
"""WP-S: the sandbox's own tests. No Lean and no Yosys: profile and argument-vector generation,
the supervisor's limits, the self-test (it must FAIL on a mechanism that does not sandbox), `configure`'s
modes, `Lean._run_sandboxed`'s plumbing with a stubbed supervisor, and (where the mechanism exists) the
real thing denying a canary.

    python3.12 tests/sandbox/test_sandbox.py
"""

import importlib.util
import os
import shutil
import signal
import subprocess
import sys
import tempfile
import textwrap
import time
import unittest
from unittest import mock

sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
SVGOLF = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, os.path.join(SVGOLF, "check"))
import sandbox  # noqa: E402
from sandbox import bwrap, core as policy_mod, seatbelt, selftest, supervisor  # noqa: E402
from sandbox.spec import Spec  # noqa: E402

REAL = sandbox.configure.__module__ and (
    (sys.platform == "darwin" and seatbelt.available()) or (sys.platform.startswith("linux") and bwrap.available()))


def dies(pid, within=8):
    """True when process `pid` is gone within `within` seconds."""
    end = time.time() + within
    while time.time() < end:
        try:
            os.kill(pid, 0)
        except ProcessLookupError:
            return True
        time.sleep(0.1)
    return False


def wait_pid(path, within=10):
    """The process id written to `path`, once it is there."""
    end = time.time() + within
    while time.time() < end:
        if os.path.exists(path):
            text = open(path).read().strip()
            if text:
                return int(text)
        time.sleep(0.05)
    raise AssertionError(f"no pid in {path}")


def lean_spec(tmp):
    return Spec(exec_paths=[os.path.join(tmp, "tc", "bin", "lean")], map_exec=[os.path.join(tmp, "tc")],
                read=[os.path.join(tmp, "tc"), os.path.join(tmp, "stage")], write=[os.path.join(tmp, "out")],
                label="lean")


class SeatbeltProfile(unittest.TestCase):
    def setUp(self):
        self.tmp = os.path.realpath(tempfile.mkdtemp(prefix="sbtest-"))
        for d in ("tc/bin", "stage", "out"):
            os.makedirs(os.path.join(self.tmp, d))
        open(os.path.join(self.tmp, "tc", "bin", "lean"), "w").close()

    def tearDown(self):
        shutil.rmtree(self.tmp, ignore_errors=True)

    def test_the_fixed_rules(self):
        p = seatbelt.profile(lean_spec(self.tmp))
        for rule in ("(deny default)", '(import "system.sb")', "(deny network*)", "(deny file-link)",
                     "(allow signal (target self))", "(allow file-read-metadata)"):
            self.assertIn(rule, p)
        self.assertNotIn("(allow default)", p)
        self.assertNotIn("process-fork", p)             # Lean and a model start nothing
        self.assertEqual(p.count("(allow process-exec"), 1)
        self.assertIn(f'(literal "{self.tmp}/tc/bin/lean")', p)

    def test_writes_are_exactly_the_given_trees(self):
        p = seatbelt.profile(lean_spec(self.tmp))
        w = p[p.index("(allow file-write*"):]
        w = w[:w.index(")\n") + 1]
        self.assertEqual(w.count("(subpath"), 1)
        self.assertIn(f'{self.tmp}/out', w)
        self.assertNotIn("(allow file-write*", seatbelt.profile(Spec(exec_paths=["/bin/echo"])))

    def test_tool_spec_forks_and_may_cache_xcrun(self):
        spec = sandbox.tool_spec(["/usr/bin/true"], read=[self.tmp], write=[self.tmp])
        p = seatbelt.profile(spec)
        self.assertIn("(allow process-fork)", p)
        self.assertIn("xcrun_db", p)
        self.assertNotIn("xcrun_db", seatbelt.profile(lean_spec(self.tmp)))

    def test_awkward_paths_are_quoted(self):
        for name in ('with space', 'quote"s', 'back\\slash', 'paren(thesis)', 'uni\u00e9\u4e2d'):
            d = os.path.join(self.tmp, name)
            os.makedirs(d, exist_ok=True)
            p = seatbelt.profile(Spec(exec_paths=["/bin/echo"], read=[d], write=[d]))
            lit = seatbelt.q(os.path.realpath(d))
            self.assertEqual(p.count(lit), 2, name)       # once under read, once under write
            self.assertTrue(lit.startswith('"') and lit.endswith('"'))
            # an embedded quote must never end the string early
            inner = lit[1:-1]
            self.assertNotRegex(inner.replace('\\\\', '').replace('\\"', ''), r'"')

    def test_deterministic(self):
        s = lean_spec(self.tmp)
        self.assertEqual(seatbelt.profile(s), seatbelt.profile(lean_spec(self.tmp)))

    def test_command_clears_the_environment_and_names_the_profile(self):
        argv, tag = seatbelt.command(lean_spec(self.tmp), ["/x/lean", "a.lean"], {"PATH": "/usr/bin", "K": "v"},
                                     self.tmp)
        self.assertEqual(argv[:2], ["/usr/bin/env", "-i"])
        self.assertIn("K=v", argv)
        i = argv.index(seatbelt.SANDBOX_EXEC)
        self.assertEqual(argv[i + 1], "-f")
        self.assertTrue(os.path.isfile(argv[i + 2]) and tag in argv[i + 2])
        self.assertEqual(argv[i + 3:], ["/x/lean", "a.lean"])

    def test_symlinked_paths_are_resolved(self):
        link = os.path.join(self.tmp, "link")
        os.symlink(os.path.join(self.tmp, "stage"), link)
        s = Spec(read=[link])
        self.assertEqual(s.read, [os.path.join(self.tmp, "stage")])


class BwrapArgv(unittest.TestCase):
    def setUp(self):
        self.tmp = os.path.realpath(tempfile.mkdtemp(prefix="bwtest-"))
        for d in ("tc/bin", "stage", "out"):
            os.makedirs(os.path.join(self.tmp, d))
        open(os.path.join(self.tmp, "tc", "bin", "lean"), "w").close()

    def tearDown(self):
        shutil.rmtree(self.tmp, ignore_errors=True)

    def test_vector(self):
        spec = lean_spec(self.tmp)
        a = bwrap.argv_for(spec, ["/tc/bin/lean", "x.lean"], {"LEAN_PATH": "/a:/b", "PATH": "/usr/bin:/bin"},
                           cwd=self.tmp + "/stage", bwrap="/usr/bin/bwrap")
        self.assertEqual(a[0], "/usr/bin/bwrap")
        for flag in ("--die-with-parent", "--new-session", "--unshare-all", "--clearenv", "--disable-userns"):
            self.assertIn(flag, a)
        self.assertEqual(a[a.index("--cap-drop") + 1], "ALL")
        self.assertEqual(a[a.index("--") + 1:], ["/tc/bin/lean", "x.lean"])
        # the environment is exactly the one given
        envs = [(a[i + 1], a[i + 2]) for i, x in enumerate(a) if x == "--setenv"]
        self.assertEqual(dict(envs), {"LEAN_PATH": "/a:/b", "PATH": "/usr/bin:/bin"})
        # only the given tree is writable; the read trees are read-only
        binds = [a[i + 1] for i, x in enumerate(a) if x == "--bind"]
        self.assertEqual(binds, [spec.write[0]])
        ro = [a[i + 1] for i, x in enumerate(a) if x == "--ro-bind-try"]
        self.assertIn(self.tmp + "/stage", ro)
        self.assertIn(self.tmp + "/tc", ro)
        self.assertEqual(a[a.index("--chdir") + 1], self.tmp + "/stage")

    def test_no_system_programs_for_a_lean_spec(self):
        a = bwrap.argv_for(lean_spec(self.tmp), ["/x"], {}, bwrap="bwrap")
        ro = [a[i + 1] for i, x in enumerate(a) if x == "--ro-bind-try"]
        for p in ("/usr", "/bin", "/sbin", "/usr/bin"):
            self.assertNotIn(p, ro, "a Lean file must find no /bin/sh to run")
        self.assertIn("/usr/lib", ro)             # the loader and libc

    def test_tool_spec_mounts_the_system(self):
        spec = sandbox.tool_spec(["/usr/bin/true"], read=[self.tmp], write=[self.tmp])
        a = bwrap.argv_for(spec, ["/x"], {}, bwrap="bwrap")
        ro = [a[i + 1] for i, x in enumerate(a) if x == "--ro-bind-try"]
        self.assertIn("/usr", ro)

    def test_merged_usr_links_are_recreated(self):
        a = bwrap.argv_for(lean_spec(self.tmp), ["/x"], {}, bwrap="bwrap", links=[("usr/bin", "/bin"), ("usr/lib", "/lib")])
        pairs = [(a[i + 1], a[i + 2]) for i, x in enumerate(a) if x == "--symlink"]
        self.assertEqual(pairs, [("usr/bin", "/bin"), ("usr/lib", "/lib")])

    def test_the_private_tmp_comes_before_every_bind(self):
        a = bwrap.argv_for(lean_spec(self.tmp), ["/x"], {}, bwrap="bwrap")
        self.assertLess(a.index("--tmpfs"), min(i for i, x in enumerate(a) if x in ("--ro-bind-try", "--bind")))

    def test_an_exec_spec_mounts_the_one_file_not_its_directory(self):
        spec = sandbox.exec_spec("/usr/bin/env", read=[self.tmp])
        a = bwrap.argv_for(spec, ["/usr/bin/env"], {}, bwrap="bwrap")
        ro = [a[i + 1] for i, x in enumerate(a) if x == "--ro-bind-try"]
        self.assertIn(os.path.realpath("/usr/bin/env"), ro)
        self.assertNotIn("/usr/bin", ro)

    def test_userns_flag_is_optional(self):
        a = bwrap.argv_for(lean_spec(self.tmp), ["/x"], {}, bwrap="bwrap", disable_userns=False)
        self.assertNotIn("--disable-userns", a)


class SupervisorLimits(unittest.TestCase):
    def run_sup(self, opts, code, timeout=60):
        p = subprocess.run([sys.executable, "-S", "-B", sandbox.SUPERVISOR] + opts + ["--", sys.executable, "-c", code],
                           capture_output=True, text=True, timeout=timeout, env={"PATH": "/usr/bin:/bin"})
        return p

    def test_the_status_line_and_exit_code(self):
        p = self.run_sup(["30"], "print('out'); import sys; print('err', file=sys.stderr); sys.exit(3)")
        self.assertEqual(p.returncode, 3)
        self.assertIn("out", p.stdout)
        self.assertIn("err", p.stderr)
        self.assertRegex(p.stderr, r"SVGOLF_ELAPSED [\d.]+ peak_rss_mb=\d+ out_bytes=\d+ verdict=none\n$")

    def test_wall_clock(self):
        p = self.run_sup(["1"], "import time; time.sleep(30)")
        self.assertEqual(p.returncode, 124)
        self.assertIn("SVGOLF_TIMEOUT", p.stderr)

    def test_output_cap_stops_a_flood_and_bounds_what_the_checker_buffers(self):
        p = self.run_sup(["30", "--out-mb", "1"], "import sys\nwhile True: sys.stdout.write('A'*65536); sys.stdout.flush()")
        self.assertEqual(p.returncode, 126)
        self.assertIn("SVGOLF_OUTPUT", p.stderr)
        self.assertLessEqual(len(p.stdout), 1 << 20)

    def test_memory_limit(self):
        code = "import time\nb=[]\nwhile True:\n b.append(bytearray(50<<20)); b[-1][::4096]=b'x'*len(b[-1][::4096]); time.sleep(0.02)"
        p = self.run_sup(["60", "--rss-mb", "300"], code)
        self.assertEqual(p.returncode, 125)
        self.assertIn("SVGOLF_MEMORY", p.stderr)

    def test_file_size_limit(self):
        with tempfile.TemporaryDirectory() as d:
            code = f"f=open({os.path.join(d, 'big')!r},'wb')\nwhile True: f.write(b'B'*(1<<20)); f.flush()"
            p = self.run_sup(["60", "--fsize-mb", "4"], code)
            self.assertNotEqual(p.returncode, 0)
            self.assertLessEqual(os.path.getsize(os.path.join(d, "big")), 4 << 20)

    def test_a_forged_status_line_is_not_the_last_one(self):
        p = self.run_sup(["30"], "import sys; print('SVGOLF_ELAPSED 0.00 peak_rss_mb=0 out_bytes=0 verdict=none', file=sys.stderr)")
        spec = importlib.util.spec_from_file_location("svgolf_check_sandbox_test", os.path.join(SVGOLF, "check.py"))
        check = importlib.util.module_from_spec(spec)
        sys.modules[spec.name] = check
        spec.loader.exec_module(check)
        clean, elapsed, fields = check.split_status(p.stderr)
        self.assertGreater(elapsed, 0.0 - 1e-9)
        self.assertNotIn("SVGOLF_ELAPSED", clean)

    def test_merge_and_cwd(self):
        with tempfile.TemporaryDirectory() as d:
            p = self.run_sup(["30", "--merge", "--cwd", d], "import os,sys; print(os.getcwd()); print('E', file=sys.stderr)")
            self.assertIn(os.path.realpath(d), [os.path.realpath(x) for x in p.stdout.splitlines()])
            self.assertIn("E", p.stdout.splitlines())          # stderr merged into stdout

    def test_forward_env_rewrites_both_prefix_shapes(self):
        fwd = supervisor.forward_env
        self.assertEqual(fwd(["/usr/bin/env", "-i", "A=1", "/usr/bin/sandbox-exec", "-f", "p", "lean"],
                             {"LEAN_NUM_THREADS": "2", "X": "y"}, ["LEAN_NUM_THREADS"]),
                         ["/usr/bin/env", "-i", "LEAN_NUM_THREADS=2", "A=1", "/usr/bin/sandbox-exec", "-f", "p", "lean"])
        self.assertEqual(fwd(["bwrap", "--unshare-all", "--clearenv", "--setenv", "A", "1", "--", "lean"],
                             {"LEAN_NUM_THREADS": "2"}, ["LEAN_NUM_THREADS"]),
                         ["bwrap", "--unshare-all", "--clearenv", "--setenv", "LEAN_NUM_THREADS", "2", "--setenv", "A",
                          "1", "--", "lean"])
        self.assertEqual(fwd(["echo", "hi"], {"LEAN_NUM_THREADS": "2"}, ["LEAN_NUM_THREADS"]), ["echo", "hi"])
        self.assertEqual(fwd(["/usr/bin/env", "-i", "A=1", "x"], {}, ["LEAN_NUM_THREADS"]), ["/usr/bin/env", "-i", "A=1", "x"])

    def test_forward_env_end_to_end(self):
        p = subprocess.run([sys.executable, "-S", "-B", sandbox.SUPERVISOR, "30", "--forward-env", "LEAN_NUM_THREADS",
                            "--", "/usr/bin/env", "-i", "A=1", "/usr/bin/env"],
                           capture_output=True, text=True, env={"PATH": "/usr/bin:/bin", "LEAN_NUM_THREADS": "2",
                                                                "SVGOLF_POSTSYNTH_SALT": "no"})
        self.assertEqual(sorted(p.stdout.split()), ["A=1", "LEAN_NUM_THREADS=2"])

    def background_sleep(self, pidfile):
        return [sys.executable, "-S", "-B", sandbox.SUPERVISOR, "30", "--",
                "sh", "-c", f"sleep 30 & echo $! > {pidfile}; wait"]

    def test_a_signal_to_the_supervisor_kills_the_group(self):
        with tempfile.TemporaryDirectory() as d:
            pidfile = os.path.join(d, "pid")
            p = subprocess.Popen(self.background_sleep(pidfile), env={"PATH": "/usr/bin:/bin"},
                                 stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, text=True)
            pid = wait_pid(pidfile)
            p.send_signal(signal.SIGTERM)
            _, err = p.communicate(timeout=20)
            self.assertEqual(p.returncode, 143)
            self.assertIn("SVGOLF_ABANDONED", err)
            self.assertTrue(dies(pid), "the command outlived a stopped supervisor")

    def test_a_dead_parent_kills_the_group(self):
        with tempfile.TemporaryDirectory() as d:
            pidfile = os.path.join(d, "pid")
            launcher = ("import os,subprocess,time\n"
                        f"subprocess.Popen({self.background_sleep(pidfile)!r})\n"
                        f"while not os.path.exists({pidfile!r}): time.sleep(0.05)\n"
                        "time.sleep(0.3)\n"
                        "os._exit(0)\n")
            subprocess.run([sys.executable, "-S", "-B", "-c", launcher], check=True, timeout=30,
                           env={"PATH": "/usr/bin:/bin"}, capture_output=True)
            self.assertTrue(dies(wait_pid(pidfile)), "the command outlived the checker that started it")

    def test_group_is_killed(self):
        with tempfile.TemporaryDirectory() as d:
            marker = os.path.join(d, "alive")
            code = ("import subprocess,sys,time\n"
                    f"subprocess.Popen([sys.executable,'-c',\"import time;time.sleep(3);open({marker!r},'w').write('x')\"])\n"
                    "time.sleep(60)")
            self.run_sup(["1"], code)
            import time
            time.sleep(4)
            self.assertFalse(os.path.exists(marker), "a grandchild outlived the supervisor's kill")


class UnsandboxedRun(unittest.TestCase):
    """`run` with no active sandbox: the behaviour of `subprocess.run`, and a timeout that kills the whole group."""

    def setUp(self):
        patcher = mock.patch.object(policy_mod, "policy", return_value=mock.Mock(active=False))
        patcher.start()
        self.addCleanup(patcher.stop)

    def test_output_status_and_input(self):
        p = policy_mod.run(["sh", "-c", "cat; echo err >&2; exit 3"], None, input_text="in\n")
        self.assertEqual((p.returncode, p.stdout, p.stderr), (3, "in\n", "err\n"))

    def test_a_timeout_kills_the_whole_group(self):
        with tempfile.TemporaryDirectory() as d:
            pidfile = os.path.join(d, "pid")
            with self.assertRaises(subprocess.TimeoutExpired):
                policy_mod.run(["sh", "-c", f"sleep 30 & echo $! > {pidfile}; wait"], None, timeout=1)
            self.assertTrue(dies(wait_pid(pidfile)), "a timeout left a grandchild running")


class SelfTest(unittest.TestCase):
    def test_a_mechanism_that_does_not_sandbox_fails_the_canary(self):
        def no_sandbox(spec, cmd, env, scratch, cwd):
            return ["/usr/bin/env", "-i"] + [f"{k}={v}" for k, v in env.items()] + list(cmd), "none"
        with tempfile.TemporaryDirectory() as d:
            ok, detail = selftest.run(no_sandbox, d)
        self.assertFalse(ok)
        for k in ("read_secret", "file_written_outside_exists", "tcp_connect", "spawn_sh"):
            self.assertIn(k, detail["wrong"])

    def test_an_environment_that_leaks_fails_the_canary(self):
        def leaky(spec, cmd, env, scratch, cwd):
            return ["/usr/bin/env", "SVGOLF_LEAK=1"] + list(cmd), "leaky"
        with tempfile.TemporaryDirectory() as d:
            ok, detail = selftest.run(leaky, d)
        self.assertFalse(ok)
        self.assertIn("env_secret_visible", detail["wrong"])

    @unittest.skipUnless(REAL, "no sandbox mechanism on this machine")
    def test_the_real_mechanism_passes(self):
        with tempfile.TemporaryDirectory() as d:
            pol = policy_mod.Policy("require")
            pol.mechanism = "seatbelt" if sys.platform == "darwin" else "bwrap"
            ok, detail = selftest.run(pol.raw_command, d)
        self.assertTrue(ok, detail)
        self.assertEqual(detail["results"]["write_inside"], "ok")


class Configure(unittest.TestCase):
    def tearDown(self):
        sandbox.configure("off")

    def test_off_is_inactive_and_adds_nothing(self):
        pol = sandbox.configure("off")
        self.assertFalse(pol.active)
        self.assertIsNone(pol.scratch)
        self.assertEqual(pol.report(), {"mode": "off", "mechanism": None, "active": False})

    def test_require_without_a_mechanism_is_an_error(self):
        with mock.patch.object(seatbelt, "available", return_value=False), \
                mock.patch.object(bwrap, "available", return_value=False):
            with self.assertRaises(sandbox.Unavailable) as cm:
                sandbox.configure("require")
        self.assertIn("require", str(cm.exception))

    def test_auto_without_a_mechanism_says_so_and_runs_unsandboxed(self):
        said = []
        with mock.patch.object(seatbelt, "available", return_value=False), \
                mock.patch.object(bwrap, "available", return_value=False):
            pol = sandbox.configure("auto", log=said.append)
        self.assertFalse(pol.active)
        self.assertTrue(any("NOT ACTIVE" in s for s in said), said)
        self.assertEqual(pol.report()["mode"], "auto")
        self.assertIn("reason", pol.report())

    def test_a_failed_self_test_is_not_a_sandbox(self):
        with mock.patch.object(selftest, "run", return_value=(False, {"wrong": ["tcp_connect"], "seconds": 0.0})):
            if not REAL:
                self.skipTest("no mechanism to fail")
            said = []
            pol = sandbox.configure("auto", log=said.append)
            self.assertFalse(pol.active)
            with self.assertRaises(sandbox.Unavailable):
                sandbox.configure("require")

    def test_the_default_policy_is_off(self):
        self.assertEqual(sandbox.policy().mode, "off")

    def test_bad_mode(self):
        with self.assertRaises(ValueError):
            sandbox.configure("maybe")


@unittest.skipUnless(REAL, "no sandbox mechanism on this machine")
class RealSandbox(unittest.TestCase):
    """The mechanism itself, on small commands (the Lean attacks are tests/run.py's `host_*`)."""

    @classmethod
    def setUpClass(cls):
        cls.pol = sandbox.configure("require", log=lambda *a: None)

    @classmethod
    def tearDownClass(cls):
        sandbox.configure("off")

    def test_run_gives_the_command_only_the_given_environment(self):
        os.environ["SVGOLF_POSTSYNTH_SALT"] = "must-not-be-seen"
        try:
            with tempfile.TemporaryDirectory() as d:
                spec = sandbox.tool_spec(["/usr/bin/env"], read=[d], write=[d])
                p = sandbox.run(["/usr/bin/env"], spec, env={"PATH": "/usr/bin:/bin", "K": "v"}, cwd=d, timeout=20)
        finally:
            del os.environ["SVGOLF_POSTSYNTH_SALT"]
        self.assertEqual(p.returncode, 0, p.stderr)
        self.assertIn("K=v", p.stdout)
        self.assertNotIn("must-not-be-seen", p.stdout + p.stderr)
        self.assertNotIn("SVGOLF_", p.stdout)

    def test_run_raises_timeout_like_subprocess(self):
        with tempfile.TemporaryDirectory() as d:
            spec = sandbox.tool_spec(["/bin/sleep"], read=[d], write=[d])
            with self.assertRaises(subprocess.TimeoutExpired):
                sandbox.run(["/bin/sleep", "30"], spec, env={"PATH": "/usr/bin:/bin"}, cwd=d, timeout=1)

    def test_a_sandboxed_tool_cannot_write_outside_its_directory_or_read_elsewhere(self):
        with tempfile.TemporaryDirectory() as d, tempfile.TemporaryDirectory() as other:
            secret = os.path.join(other, "secret.txt")
            with open(secret, "w") as fh:
                fh.write("s3cret\n")
            spec = sandbox.tool_spec(["/bin/sh"], read=[d], write=[d])
            env = {"PATH": "/usr/bin:/bin"}
            p = sandbox.run(["/bin/sh", "-c", f"cat {secret}; echo hi > {other}/w.txt; echo ok > {d}/w.txt"], spec,
                            env=env, cwd=d, timeout=20)
            self.assertNotIn("s3cret", p.stdout + p.stderr)
            self.assertFalse(os.path.exists(os.path.join(other, "w.txt")))
            self.assertTrue(os.path.exists(os.path.join(d, "w.txt")))

    def test_exec_spec_runs_only_itself(self):
        with tempfile.TemporaryDirectory() as d:
            spec = sandbox.exec_spec("/usr/bin/env", read=[d], label="model")
            ok = sandbox.run(["/usr/bin/env"], spec, env={"PATH": "/usr/bin:/bin", "K": "v"}, cwd=d, timeout=20)
            self.assertIn("K=v", ok.stdout)                       # it runs itself ...
            p = sandbox.run(["/usr/bin/env", "/usr/bin/id", "-un"], spec, env={"PATH": "/usr/bin:/bin"},
                            cwd=d, timeout=20)
            self.assertNotEqual(p.returncode, 0)                  # ... and starts nothing else
            self.assertEqual(p.stdout.strip(), "")


@unittest.skipUnless(REAL, "no sandbox mechanism on this machine")
class LeanPlumbing(unittest.TestCase):
    """`Lean._run_sandboxed` with the supervisor stubbed: what it asks the sandbox for, and what it adopts."""

    @classmethod
    def setUpClass(cls):
        spec = importlib.util.spec_from_file_location("svgolf_check_plumbing", os.path.join(SVGOLF, "check.py"))
        cls.check = importlib.util.module_from_spec(spec)
        sys.modules[spec.name] = cls.check
        spec.loader.exec_module(cls.check)

    def setUp(self):
        self.tmp = os.path.realpath(tempfile.mkdtemp(prefix="plumb-"))
        self.stage = os.path.join(self.tmp, "stage")
        os.makedirs(os.path.join(self.stage, "build", "Submission"))
        self.sysroot = os.path.join(self.tmp, "tc")
        os.makedirs(os.path.join(self.sysroot, "bin"))
        self.search = [os.path.join(self.tmp, "pkg", "lib"), os.path.join(self.stage, "build")]
        os.makedirs(self.search[0])
        self.pol = policy_mod.Policy("auto")
        self.seatbelt = sys.platform == "darwin"
        self.pol.active, self.pol.mechanism, self.pol.scratch = True, "seatbelt" if self.seatbelt else "bwrap", \
            tempfile.mkdtemp(prefix="scr-")
        self.calls = []
        self.produce = None

    def tearDown(self):
        shutil.rmtree(self.tmp, ignore_errors=True)
        self.pol.close()

    def run_lean(self, args, timeout=None, produce=None, bv_solver=False):
        lean = self.check.Lean(self.stage, ["/slot.sh"])
        lean._lake_env = (self.search, self.sysroot)
        calls = self.calls

        def fake_run(cmd, **kw):
            calls.append((cmd, kw))
            if produce:
                produce(cmd)
            return subprocess.CompletedProcess(cmd, 0, "out text\n", "SVGOLF_ELAPSED 1.50 peak_rss_mb=7 out_bytes=9 verdict=none\n")
        with mock.patch.object(sandbox, "policy", return_value=self.pol), mock.patch.object(self.check.subprocess, "run", fake_run):
            return lean.run(args, timeout, bv_solver=bv_solver)

    def outdir_of(self, cmd):
        i = cmd.index("-o")
        return os.path.dirname(cmd[i + 1])

    def test_compile_runs_the_toolchain_binary_under_the_supervisor_inside_the_slot(self):
        target = os.path.join(self.stage, "build", "Submission", "Solution.olean")
        rc, out, el = self.run_lean(["lean", "-R", self.stage, "-o", target, os.path.join(self.stage, "Submission", "Solution.lean")], 77)
        (cmd, kw), = self.calls
        self.assertEqual(cmd[0], "/slot.sh")                                  # the slot wrapper is outermost
        self.assertIn(sandbox.SUPERVISOR, cmd)
        self.assertEqual(cmd[cmd.index(sandbox.SUPERVISOR) + 1], "77")        # the task's wall-clock limit
        self.assertIn("--merge", cmd)
        self.assertNotIn("lake", cmd)                                         # lake is never inside
        self.assertIn(os.path.join(self.sysroot, "bin", "lean"), cmd)
        o = cmd[cmd.index("-o") + 1]
        self.assertNotEqual(o, target)                                        # the compile writes elsewhere ...
        self.assertTrue(o.startswith(self.pol.scratch))                       # ... in a fresh scratch directory
        self.assertEqual((rc, out, el), (0, "out text\n", 1.5))
        # the child's environment is exactly the minimal one
        if self.seatbelt:
            names = {a.split("=")[0] for a in cmd if "=" in a and a.split("=")[0].isupper() and not a.startswith("-")}
        else:
            names = {cmd[i + 1] for i, a in enumerate(cmd) if a == "--setenv"}
        self.assertTrue({"LEAN_PATH", "LEAN_SYSROOT", "PATH", "HOME"} <= names, names)
        self.assertFalse([n for n in names if n.startswith("SVGOLF")])
        self.assertEqual(kw["env"].get("SVGOLF_POSTSYNTH_SALT"), None)

    def spec_text(self, cmd):
        """What the run's Spec lets it do, as text: the Seatbelt profile, or the bubblewrap argument vector."""
        if self.seatbelt:
            with open([a for a in cmd if a.endswith(".sb")][0]) as fh:
                return fh.read()
        return " ".join(cmd)

    def env_of(self, cmd):
        if self.seatbelt:
            return dict(a.split("=", 1) for a in cmd[:cmd.index(sandbox.seatbelt.SANDBOX_EXEC)]
                        if "=" in a and a.split("=")[0].isupper() and not a.startswith("-"))
        return {cmd[i + 1]: cmd[i + 2] for i, a in enumerate(cmd) if a == "--setenv"}

    def test_while_bv_decide_is_unsupported_the_solver_is_never_granted(self):
        # Decided 2026-11-01: "Let's not support external solvers for now". `check.BV_DECIDE_SUPPORTED` is False, and the
        # grant below is dormant: even a caller that asks (`bv_solver=True`) gets no `cadical`, no `fork`, no TMPDIR
        self.assertIs(self.check.BV_DECIDE_SUPPORTED, False)
        solver = os.path.join(self.sysroot, "bin", "cadical")
        open(solver, "w").close()
        target = os.path.join(self.stage, "build", "Submission", "Solution.olean")
        for solver_asked in (False, True):
            self.calls.clear()
            self.run_lean(["lean", "-R", self.stage, "-o", target, "x.lean"], 77, bv_solver=solver_asked)
            (cmd, kw), = self.calls
            text = self.spec_text(cmd)
            self.assertNotIn("TMPDIR", self.env_of(cmd))
            self.assertNotIn("cadical", text)
            if self.seatbelt:
                self.assertNotIn("process-fork", text)
            else:
                self.assertNotIn(os.path.realpath(solver), cmd)
            self.assertEqual(len(self.pol.note["sandboxed"]), 1)
            self.assertNotIn("+cadical", " ".join(self.pol.note["sandboxed"]))

    def test_the_dormant_grant_when_forced_on_a_bv_decide_compile_may_start_cadical_and_write_one_temporary_directory(self):
        # WP-BV (groundwork, switched on here inside the test only): the tactic writes a CNF and an LRAT file into the
        # temporary directory and starts the toolchain's `cadical`; measured (probe/sbx_probe.py): all three are
        # needed and nothing else
        solver = os.path.join(self.sysroot, "bin", "cadical")
        open(solver, "w").close()
        target = os.path.join(self.stage, "build", "Submission", "Solution.olean")
        with mock.patch.object(self.check, "BV_DECIDE_SUPPORTED", True):
            self.run_lean(["lean", "-R", self.stage, "-o", target, "x.lean"], 77, bv_solver=True)
        (cmd, kw), = self.calls
        text = self.spec_text(cmd)
        env = self.env_of(cmd)
        tmp = env["TMPDIR"]
        self.assertTrue(tmp.startswith(os.path.realpath(self.pol.scratch)), tmp)    # a fresh directory of the scratch area
        self.assertTrue(os.path.isdir(tmp))
        self.assertNotEqual(tmp, self.outdir_of(cmd))                               # not the adopted output directory
        self.assertEqual(os.path.dirname(tmp), os.path.realpath(os.path.dirname(self.outdir_of(cmd))))
        solver = os.path.realpath(solver)
        if self.seatbelt:
            self.assertIn(f'(literal "{solver}")', text)                            # exec of cadical, listed
            self.assertIn(f'(literal "{os.path.realpath(os.path.join(self.sysroot, "bin", "lean"))}")', text)
            self.assertIn("(allow process-fork)", text)
            self.assertIn(f'(subpath "{tmp}")', text.split(";; writes")[1])           # the one extra write tree
        else:
            self.assertIn(solver, [cmd[i + 1] for i, a in enumerate(cmd) if a == "--ro-bind-try"])
            self.assertIn(tmp, [cmd[i + 1] for i, a in enumerate(cmd) if a == "--bind"])
        # still no network, no other program: the profile's other rules are the compile's
        if self.seatbelt:
            self.assertIn("(deny network*)", text)
            self.assertNotIn('(subpath "/bin")', text)
            self.assertNotIn('(literal "/bin/sh")', text)

    def test_every_other_lean_run_has_no_cadical_no_fork_and_no_temporary_directory(self):
        solver = os.path.join(self.sysroot, "bin", "cadical")
        open(solver, "w").close()
        comp = os.path.join(self.tmp, "Comparator.lean")
        open(comp, "w").close()
        target = os.path.join(self.stage, "build", "Submission", "Solution.olean")
        for args in (["lean", "-R", self.stage, "-o", target, "x.lean"],       # the generated design, the probes ...
                     ["lean", "--run", comp, "--goal", "G"],                    # ... the comparator
                     ["leanchecker", "Submission.Solution"]):
            self.calls.clear()
            self.run_lean(args, 9)                                              # (bv_solver is off unless asked for)
            (cmd, kw), = self.calls
            text = self.spec_text(cmd)
            self.assertNotIn("TMPDIR", self.env_of(cmd))
            if self.seatbelt:
                self.assertNotIn("cadical", text)
                self.assertNotIn("process-fork", text)
            else:
                self.assertNotIn(os.path.realpath(solver), cmd)
        # a toolchain without the binary: the flag grants nothing it cannot use
        os.remove(solver)
        self.calls.clear()
        with mock.patch.object(self.check, "BV_DECIDE_SUPPORTED", True):
            self.run_lean(["lean", "-R", self.stage, "-o", target, "x.lean"], 9, bv_solver=True)
        (cmd, kw), = self.calls
        self.assertNotIn("TMPDIR", self.env_of(cmd))

    def test_only_a_regular_file_of_the_expected_name_is_adopted(self):
        target = os.path.join(self.stage, "build", "Submission", "Solution.olean")

        def produce(cmd):
            d = self.outdir_of(cmd)
            with open(os.path.join(d, "Solution.olean"), "wb") as fh:
                fh.write(b"OLEAN")
            with open(os.path.join(d, "Evil.olean"), "wb") as fh:
                fh.write(b"x")
            os.symlink("/etc/hosts", os.path.join(d, "Link"))
        self.run_lean(["lean", "-R", self.stage, "-o", target, "x.lean"], 5, produce)
        with open(target, "rb") as fh:
            self.assertEqual(fh.read(), b"OLEAN")
        self.assertEqual(sorted(os.listdir(os.path.dirname(target))), ["Solution.olean"])
        self.assertEqual(sorted(self.pol.note["stray_outputs"]), ["Evil.olean", "Link"])

    def test_a_symlink_named_like_the_output_is_not_adopted(self):
        target = os.path.join(self.stage, "build", "Submission", "Solution.olean")

        def produce(cmd):
            os.symlink("/etc/hosts", os.path.join(self.outdir_of(cmd), "Solution.olean"))
        self.run_lean(["lean", "-R", self.stage, "-o", target, "x.lean"], 5, produce)
        self.assertFalse(os.path.exists(target))

    def test_the_comparator_run_may_read_its_source_and_writes_nothing(self):
        comp = os.path.join(self.tmp, "Comparator.lean")
        open(comp, "w").close()
        self.run_lean(["lean", "--run", comp, "--goal", "G"], 9)
        (cmd, kw), = self.calls
        self.assertNotIn("-o", cmd)
        if self.seatbelt:
            with open([a for a in cmd if a.endswith(".sb")][0]) as fh:
                text = fh.read()
            self.assertIn(comp, text)
            self.assertNotIn("(allow file-write*", text)
        else:
            self.assertIn(comp, [cmd[i + 1] for i, a in enumerate(cmd) if a == "--ro-bind-try"])
            self.assertNotIn("--bind", cmd)

    def test_printenv_returns_the_search_path_from_one_lake_call(self):
        lean = self.check.Lean(self.stage, [])
        lean._lake_env = (self.search, self.sysroot)
        with mock.patch.object(sandbox, "policy", return_value=self.pol):
            rc, out, el = lean.run(["printenv", "LEAN_PATH"])
        self.assertEqual((rc, out.strip().split(":")), (0, self.search))


if __name__ == "__main__":
    unittest.main(verbosity=1)
