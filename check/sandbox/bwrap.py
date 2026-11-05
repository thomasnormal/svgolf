"""Linux: bubblewrap (`bwrap`), unprivileged namespaces.

NOT RUN on the development machine (macOS; no Linux host was available in WP-S): the argument
vector is covered by unit tests, and the first Linux checker must pass `selftest.py` (every `auto`
and `require` start runs it) before anything is trusted to it.

Why bwrap: no daemon and no root, one small binary that Flatpak ships everywhere, the same model as
the Seatbelt profile (a Spec is a set of mounts), and it composes with `prlimit` and
`systemd-run --scope` for cgroups. nsjail bundles cgroups and seccomp but is usually built from
source; Docker or podman need an image holding a 10 GB toolchain.

What the vector does:
  --unshare-all                 new user, pid, ipc, uts, net and cgroup namespaces: no network at all,
                                no other process visible (so no `kill`, no /proc/<pid>/environ of others)
  --disable-userns              (bwrap 0.8+) no further user namespaces inside
  --cap-drop ALL --new-session --die-with-parent
  --clearenv + --setenv         the environment is exactly the one given
  mounts                        ONLY what the Spec lists, read-only, plus the loader's libraries; what is
                                not mounted does not exist, and what is mounted is all that can be executed
                                (no /bin/sh for a Lean file: the tool trees are mounted only for tool specs)
  --tmpfs /tmp (first)          a write to an unmounted path succeeds INTO THIS RAM DISK and dies with the
                                process: it never reaches the host (the self-test checks the host, not the call)
  --bind for `write` trees      the only paths whose writes reach the host
Unprivileged user namespaces must be enabled (Debian: kernel.unprivileged_userns_clone=1; Ubuntu 24.04:
the AppArmor restriction needs a bwrap profile): the self-test reports a refusal as "unavailable".
"""

import os
import shutil
import subprocess

LIB_TREES = ["/usr/lib", "/usr/lib32", "/usr/lib64", "/lib", "/lib32", "/lib64", "/etc/ld.so.cache",
             "/etc/ld.so.conf", "/etc/ld.so.conf.d"]


MERGED_USR = ("bin", "sbin", "lib", "lib32", "lib64")


def usr_links():
    """[(target, path)] for the top-level directories that are symlinks into /usr on this host (merged-/usr
    systems: /bin -> usr/bin ...). Specs hold resolved paths (/usr/bin/sh), but the command line says /bin/sh:
    the new root gets the same links."""
    return [(os.readlink("/" + n), "/" + n) for n in MERGED_USR if os.path.islink("/" + n)]


def find():
    return os.environ.get("SVGOLF_BWRAP") or shutil.which("bwrap")


def supports(bwrap, flag):
    try:
        out = subprocess.run([bwrap, "--help"], capture_output=True, text=True, timeout=20,
                             env={"PATH": "/usr/bin:/bin"})
        return flag in (out.stdout + out.stderr)
    except (OSError, subprocess.SubprocessError):
        return False


def argv_for(spec, cmd, env, cwd=None, bwrap="bwrap", disable_userns=True, tmpfs_mb=256, sized_tmpfs=True,
             links=()):
    """The complete argument vector (pure: no filesystem access, so it is unit-testable anywhere)."""
    a = [bwrap, "--die-with-parent", "--new-session", "--unshare-all", "--cap-drop", "ALL", "--clearenv"]
    if disable_userns:
        a.append("--disable-userns")
    for k, v in env.items():
        a += ["--setenv", k, str(v)]
    # the private /tmp comes FIRST: a later mount shows through it (the staging tree lives in /tmp), and a
    # write to an unmounted path lands in this tmpfs, which dies with the process
    a += ["--proc", "/proc", "--dev", "/dev"]
    a += (["--size", str(tmpfs_mb << 20)] if sized_tmpfs else []) + ["--tmpfs", "/tmp"]
    for target, path in links:
        a += ["--symlink", target, path]
    ro = [os.path.realpath(p) for p in LIB_TREES if os.path.lexists(p)]
    ro += spec.read + spec.exec_subpaths + spec.map_exec + spec.exec_paths
    seen = set()
    for p in ro:
        if p not in seen:
            seen.add(p)
            a += ["--ro-bind-try", p, p]
    for p in spec.write:
        a += ["--bind", p, p]
    if cwd:
        a += ["--chdir", cwd]
    return a + ["--"] + list(cmd)


def command(spec, cmd, env, scratch, cwd=None, debug=False):
    b = find()
    return argv_for(spec, cmd, env, cwd, bwrap=b, disable_userns=supports(b, "--disable-userns"),
                    sized_tmpfs=supports(b, "--size"), links=usr_links()), "bwrap"


def available():
    return bool(find())
