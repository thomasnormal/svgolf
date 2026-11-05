"""macOS: Seatbelt (`sandbox-exec -f PROFILE`), the kernel's own sandbox.

`sandbox-exec` is documented as deprecated and has been unchanged for a decade; Chrome, Bazel and
Nix use the same kernel interface. It cannot nest (`sandbox_apply: Operation not permitted`), so a
checker that already runs inside another Seatbelt sandbox falls back (`auto`) or stops (`require`):
`selftest.py` finds that out.

The profile is the Spec and a handful of fixed rules (WP-S gate 0 measured every one of them with
an attack that goes through without it: the ablations in svgolf/design/sandbox):

  (deny default)                       everything is denied unless a rule below allows it
  (import "system.sb")                 Apple's baseline for a command-line program (dyld, libSystem)
  process-exec, listed programs only   a hostile file cannot start /bin/sh, curl, kill ...
  file-read* on the listed trees       no ~/.ssh, no /etc, no other competitor's staging directory
  (allow file-read-metadata)           GLOBAL, on purpose: existence, size and mtime of any path,
                                       never content or a listing. `leanchecker` stats every module
                                       of the search path and a path-filtered rule made it 60% slower
                                       (13.7 s to 22 s); with this rule it is within noise
  file-write* on the listed trees      the fresh output directory, nothing else
  (deny network*)                      TCP, UDP, unix sockets, DNS: all denied
  (allow signal (target self))         no signal to any other process
  (deny file-link)                     a hard link is a second name for a file the profile never opened
"""

import hashlib
import os

SANDBOX_EXEC = "/usr/bin/sandbox-exec"


def q(path):
    """An SBPL string literal."""
    return '"' + path.replace("\\", "\\\\").replace('"', '\\"') + '"'


def profile(spec, debug=False):
    L = ["(version 1)", "(deny default)"]
    if debug:
        L.append("(debug deny)")      # denials go to the kernel log: `log show` (SVGOLF_SANDBOX_DEBUG=1)
    L.append('(import "system.sb")')
    L.append("")
    L.append(";; programs: the listed executables only (a child inherits the profile and cannot be new code)")
    execs = [f"(literal {q(p)})" for p in spec.exec_paths] + [f"(subpath {q(p)})" for p in spec.exec_subpaths]
    if execs:
        L.append("(allow process-exec " + " ".join(execs) + ")")
        # the dynamic libraries of the program (the Lean toolchain's libleanshared) are mapped executable
        trees = sorted(set(spec.map_exec + spec.exec_subpaths + [os.path.dirname(p) for p in spec.exec_paths]))
        L.append("(allow file-map-executable " + " ".join(f"(subpath {q(t)})" for t in trees) + ")")
    if spec.fork:
        L.append("(allow process-fork)")
    L.append("")
    L.append(";; reads")
    reads = sorted(set(spec.read + spec.exec_subpaths + [os.path.dirname(p) for p in spec.exec_paths]
                       + spec.write))
    if reads:
        L.append("(allow file-read*\n  " + "\n  ".join(f"(subpath {q(p)})" for p in reads) + ")")
    # a tool that is handed a FILE looks in its directory first (Verilator searches for its source): the
    # directory's entry names, never the sibling files' contents
    lists = sorted({os.path.dirname(p) for p in reads if os.path.isfile(p)}
                   - {p for p in reads if os.path.isdir(p)})
    if lists:
        L.append("(allow file-read-data\n  " + "\n  ".join(f"(literal {q(d)})" for d in lists) + ")")
    L.append("(allow file-read-metadata)")
    L.append("")
    L.append(";; writes")
    if spec.write:
        L.append("(allow file-write*\n  " + "\n  ".join(f"(subpath {q(p)})" for p in sorted(spec.write)) + ")")
    if spec.system == "tools":
        # Apple's /usr/bin shims (c++, make) cache their xcrun lookups in a per-user temp file, whatever TMPDIR says
        L.append('(allow file-read* file-write* (regex #"^/private/var/folders/[^/]+/[^/]+/T/xcrun_db(-[^/]*)?$"))')
    L.append("")
    L.append(";; no network of any kind, no signal to another process, no hard link")
    L.append("(deny network*)")
    L.append("(allow signal (target self))")
    L.append("(deny file-link)")
    return "\n".join(L) + "\n"


def command(spec, cmd, env, scratch, cwd=None, debug=False):
    """(argv, profile sha256 prefix). The environment is exactly `env`: `env -i` runs BEFORE the sandbox
    is entered (it is the supervisor's child, not the sandboxed program's). `cwd` is the supervisor's business here
    (sandbox-exec has no chdir)."""
    text = profile(spec, debug)
    sha = hashlib.sha256(text.encode()).hexdigest()
    d = os.path.join(scratch, "profiles")
    os.makedirs(d, exist_ok=True)
    path = os.path.join(d, sha[:16] + ".sb")
    if not os.path.exists(path):
        with open(path, "w") as fh:
            fh.write(text)
    argv = ["/usr/bin/env", "-i"] + [f"{k}={v}" for k, v in env.items()] + [SANDBOX_EXEC, "-f", path] + list(cmd)
    return argv, sha[:16]


def available():
    return os.path.exists(SANDBOX_EXEC)
