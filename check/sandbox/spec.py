"""What one sandboxed process may do: a `Spec`, the same for every mechanism.

The default is NOTHING: no network, no signals to others, no new programs, no writes. A Spec lists
the exceptions, by path, and the mechanisms (seatbelt.py, bwrap.py) turn it into a profile or an
argument vector. Paths are made absolute and symlink-resolved here, once: Seatbelt matches the
resolved path of the file a process opens, and bwrap mounts what it is given.
"""

import os


def real(path):
    return os.path.realpath(path)


class Spec:
    """exec_paths     exact executables that may run (the program itself, `leanchecker`, a model)
    exec_subpaths  trees whose executables may run (a tool tree: Yosys, make, the C++ compiler)
    read           files or trees the process may read (the toolchain, its inputs)
    write          trees it may write: ONLY directories created for the purpose, never a tree the
                   checker's later stages trust
    map_exec       trees the program may map executable code from (the toolchain's dynamic libraries);
                   a Seatbelt-only notion, on Linux mounting a tree is enough
    fork           may start child processes (build tools do; Lean and a model do not)
    system         the system tree it needs: "libs" (the C library and loader: Lean, a model) or
                   "tools" (/usr, /bin, ...: the tool specs). On macOS Seatbelt grants the libraries
                   itself (system.sb) and this only decides what else is readable and executable.
    """

    def __init__(self, exec_paths=(), exec_subpaths=(), read=(), write=(), fork=False, system="libs",
                 label="", map_exec=()):
        self.exec_paths = [real(p) for p in exec_paths]
        self.exec_subpaths = [real(p) for p in exec_subpaths]
        self.read = [real(p) for p in read]
        self.write = [real(p) for p in write]
        self.map_exec = [real(p) for p in map_exec]
        self.fork = bool(fork)
        self.system = system
        self.label = label

    def key(self):
        """A deterministic description (for the profile's file name and the result's digest)."""
        return repr((sorted(self.exec_paths), sorted(self.exec_subpaths), sorted(self.read),
                     sorted(self.write), sorted(self.map_exec), self.fork, self.system))


# The trees a TOOL (Yosys, Verilator, make, the C++ compiler, perl, the extractor's Python) lives in and
# may use. Nothing here is a secret: they are system and package-manager trees.
MACOS_TOOL_TREES = ["/usr", "/bin", "/sbin", "/System", "/Library/Developer", "/Library/Frameworks",
                    "/opt/homebrew", "/private/var/db/xcode_select_link", "/private/var/select",
                    "/private/etc"]
LINUX_TOOL_TREES = ["/usr", "/bin", "/sbin", "/lib", "/lib32", "/lib64", "/etc/alternatives"]


def tool_trees(*exes):
    """The trees a tool needs: the system trees plus the prefix of each given executable (its resolved
    path's grandparent when that is not already inside a system tree: a Yosys built into
    ~/tools/yosys/bin/yosys needs ~/tools/yosys)."""
    base = MACOS_TOOL_TREES if os.uname().sysname == "Darwin" else LINUX_TOOL_TREES
    trees = [t for t in base if os.path.exists(t)]
    for exe in exes:
        r = real(exe)
        if any(r == t or r.startswith(t + os.sep) for t in trees):
            continue
        d = os.path.dirname(os.path.dirname(r))
        if d and d != os.sep and d not in trees:
            trees.append(d)
    return trees
