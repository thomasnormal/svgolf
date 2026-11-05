#!/usr/bin/env python3.12
"""WP-S: the environment of every process that touches submitted text is an allowlist.

    python3.12 tests/sandbox/test_env.py

No Lean, no Yosys: (1) `scrubbed_env` unit tests; (2) `Lean.run` hands the Lean command a
scrubbed environment (a fake `lake` on PATH records what it was given); (3) a source lint:
every `subprocess` call in the checker, scorer and postsynth modules passes `env=` (or is one of
the two audited exceptions), so a new call site cannot quietly inherit the checker's secrets
(the competition salt `SVGOLF_POSTSYNTH_SALT` above all)."""

import ast
import importlib.util
import os
import stat
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
SVGOLF = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, os.path.join(SVGOLF, "check"))
import sandbox  # noqa: E402

SECRETS = {k: "wps-secret-value-of-" + k for k in (
    "SVGOLF_POSTSYNTH_SALT", "CLAUDE_CODE_MESSAGING_TOKEN", "AWS_SECRET_ACCESS_KEY", "GITHUB_TOKEN",
    "SSH_AUTH_SOCK", "MY_API_TOKEN", "SVGOLF_LEAN_WRAP", "SVGOLF_YOSYS")}


class ScrubbedEnv(unittest.TestCase):
    def test_secrets_never_pass(self):
        base = dict(SECRETS, PATH="/usr/bin", HOME="/home/u", LEAN_PATH="/a:/b", LEAN_NUM_THREADS="2")
        env = sandbox.scrubbed_env(base=base)
        for k in SECRETS:
            self.assertNotIn(k, env, k)
        self.assertEqual(env["PATH"], "/usr/bin")
        self.assertEqual(env["LEAN_PATH"], "/a:/b")
        self.assertEqual(env["LEAN_NUM_THREADS"], "2")

    def test_unknown_variables_do_not_pass(self):
        env = sandbox.scrubbed_env(base={"PATH": "/usr/bin", "SOMETHING_ELSE": "1", "XDG_RUNTIME_DIR": "/run"})
        self.assertEqual(env, {"PATH": "/usr/bin"})

    def test_a_deny_glob_beats_an_allowed_prefix(self):
        env = sandbox.scrubbed_env(base={"LEAN_API_TOKEN": "t", "LAKE_SECRET": "s", "PATH": "/b"})
        self.assertEqual(env, {"PATH": "/b"})

    def test_extra_and_overrides_are_the_callers_own(self):
        env = sandbox.scrubbed_env({"LEAN_PATH": "/x", "PATH": None}, base={"PATH": "/usr/bin"}, LC_ALL="C")
        self.assertEqual(env, {"LEAN_PATH": "/x", "LC_ALL": "C"})

    def test_default_base_is_os_environ_and_a_fresh_dict(self):
        os.environ["SVGOLF_POSTSYNTH_SALT"] = "from-os-environ"
        try:
            env = sandbox.scrubbed_env()
            self.assertNotIn("SVGOLF_POSTSYNTH_SALT", env)
            env["PATH"] = "changed"
            self.assertNotEqual(os.environ.get("PATH"), "changed")
        finally:
            del os.environ["SVGOLF_POSTSYNTH_SALT"]


class VenvConfigs(unittest.TestCase):
    """A Python started from a venv reads its `pyvenv.cfg` before its first line: the sandboxed tools
    (`tool_spec`, `python_spec`) may read exactly that file of each venv on PATH, or a checker run
    from a venv (pyslang installed by `pip install -r requirements.txt` into one) fails every
    extraction with `init_import_site`."""

    def test_the_config_of_each_venv_on_path_and_nothing_else(self):
        with tempfile.TemporaryDirectory() as d:
            for b in ("venv", "plain"):
                os.makedirs(os.path.join(d, b, "bin"))
            cfg = os.path.join(d, "venv", "pyvenv.cfg")
            with open(cfg, "w") as fh:
                fh.write("home = /usr/bin\n")
            path = os.pathsep.join([os.path.join(d, "venv", "bin") + os.sep, os.path.join(d, "plain", "bin"),
                                    os.path.join(d, "venv", "bin"), "venv/bin", ""])
            self.assertEqual(sandbox.tools.venv_configs(path), [os.path.realpath(cfg)])
            old = os.environ.get("PATH")
            os.environ["PATH"] = path
            try:
                self.assertIn(os.path.realpath(cfg), sandbox.tool_spec([sys.executable]).read)
            finally:
                os.environ["PATH"] = old
            self.assertEqual(sandbox.tools.venv_configs(os.path.join(d, "plain", "bin")), [])


def load_check():
    spec = importlib.util.spec_from_file_location("svgolf_check_env_test", os.path.join(SVGOLF, "check.py"))
    mod = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = mod
    spec.loader.exec_module(mod)
    return mod


class LeanRunEnvironment(unittest.TestCase):
    def test_the_lean_command_never_sees_the_salt(self):
        check = load_check()
        with tempfile.TemporaryDirectory() as tmp:
            dump = os.path.join(tmp, "env.dump")
            fake = os.path.join(tmp, "lake")
            with open(fake, "w") as fh:
                fh.write(f"#!/bin/sh\nenv > {dump}\n")
            os.chmod(fake, os.stat(fake).st_mode | stat.S_IXUSR)
            old = dict(os.environ)
            os.environ.update(SECRETS)
            os.environ["PATH"] = tmp + os.pathsep + old.get("PATH", "")
            try:
                rc, out, el = check.Lean(os.path.join(tmp, "stage"), []).run(["lean", "x.lean"])
            finally:
                os.environ.clear()
                os.environ.update(old)
            self.assertEqual(rc, 0, out)
            with open(dump) as fh:
                seen = fh.read()
            for k, v in SECRETS.items():
                self.assertNotIn(k + "=", seen, k)
                self.assertNotIn(v, seen, k)
            self.assertIn("LEAN_PATH=" + os.path.join(tmp, "stage", "build"), seen)


# Calls that may omit `env=`: (file relative to svgolf/, enclosing function) -> why.
NO_ENV_OK = {
    ("check/sandbox/supervisor.py", "main"): "the supervisor: its command carries its own `env -i ...` prefix "
                                             "(a sandboxed command) or the scrubbed environment it was given",
    ("check/postsynth.py", "run_group"): "defaults env= to scrubbed_env() (kw.setdefault)",
}
LINTED = ["check.py"] + [os.path.join("check", f) for f in sorted(os.listdir(os.path.join(SVGOLF, "check")))
                         if f.endswith(".py")] + \
         [os.path.join("check", "sandbox", f) for f in sorted(os.listdir(os.path.join(SVGOLF, "check", "sandbox")))
          if f.endswith(".py")] + \
         [os.path.join("score", f) for f in sorted(os.listdir(os.path.join(SVGOLF, "score")))
          if f.endswith(".py") and not f.startswith("test_") and f != "ppa_validate.py"]
SPAWNERS = {"run", "Popen", "check_output", "check_call", "call", "getoutput", "getstatusoutput"}


def spawns_without_env(path):
    with open(os.path.join(SVGOLF, path)) as fh:
        tree = ast.parse(fh.read())
    out = []

    class V(ast.NodeVisitor):
        stack = []

        def visit_FunctionDef(self, node):
            self.stack.append(node.name)
            self.generic_visit(node)
            self.stack.pop()

        visit_AsyncFunctionDef = visit_FunctionDef

        def visit_Call(self, node):
            f = node.func
            if isinstance(f, ast.Attribute) and f.attr in SPAWNERS and isinstance(f.value, ast.Name) \
                    and f.value.id == "subprocess":
                if not any(k.arg == "env" for k in node.keywords):
                    out.append((path, self.stack[-1] if self.stack else "<module>", node.lineno))
            elif isinstance(f, ast.Attribute) and isinstance(f.value, ast.Name) and f.value.id == "os" \
                    and f.attr in ("system", "popen", "execv", "execvp", "spawnv", "spawnvp"):
                out.append((path, self.stack[-1] if self.stack else "<module>", node.lineno))
            self.generic_visit(node)

    V().visit(tree)
    return out


class NoSpawnInheritsTheEnvironment(unittest.TestCase):
    def test_every_subprocess_call_passes_env(self):
        bad = []
        for path in LINTED:
            for p, fn, line in spawns_without_env(path):
                if (p, fn) not in NO_ENV_OK:
                    bad.append(f"{p}:{line} in {fn}()")
        self.assertEqual(bad, [], "subprocess call(s) without env=: they would inherit the checker's "
                                  "secrets (use sandbox.scrubbed_env())")

    def test_the_audited_exceptions_still_exist(self):
        for (path, fn), _why in NO_ENV_OK.items():
            self.assertTrue(any(f == fn for _p, f, _l in spawns_without_env(path)),
                            f"{path} {fn}: no longer spawns without env=; drop it from NO_ENV_OK")


if __name__ == "__main__":
    unittest.main(verbosity=1)
