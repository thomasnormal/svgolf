#!/usr/bin/env python3.12
"""The RATING BUILD of the pinned flow (decided 2026-11-24): YoWASP's WebAssembly build of Yosys 0.53 (git sha1
53c22ab7c), with ABC linked into the same module, run by wasmtime. One program for every machine: its C++ library,
its C library (`qsort` included), its allocator and its floating point are inside the module, so macOS and Linux
write byte-identical canonical RTLIL and netlists from the same design (measured on every record of 2026-11-24).

Why: the native builds of the same Yosys 0.53 source disagree. The C++ standard library (libc++ on macOS, libstdc++
on Linux) changes the order in which Yosys's passes visit cells and connections (Yosys recycles freed name indices
and orders by them; first visible in `opt_expr`), and the C library's `qsort` breaks the ties of ABC's cut sort
(`map`) in another order. On the board of 2026-11-24 a Linux build gave another netlist for 34 of 65 records and
another score for 33, up to 7.1 %, and reordered the matmul board.

Takes exactly the `yosys` command line:

    python3.12 score/yosys_wasm.py -q -s script.ys          # what score.py runs (score.yosys_argv)
    python3.12 score/yosys_wasm.py --self-check             # the module's sha256, the pins and the version line

score.py runs it unless $SVGOLF_YOSYS (or `--yosys`) names another Yosys; a native build is for research, its numbers
can differ from the board's, and every result says which build made it (`rating_build`).

Installed by `python3.12 -m pip install -r requirements.txt` (the three pins below). It never runs another module:
the installed yosys.wasm must have the pinned sha256 and the runtime packages the pinned versions, or it exits with
status 3 and the reason, and it never falls back to a native `yosys`. The module is compiled to machine code once
per machine into a cache, $YOWASP_CACHE_DIR, default `score/.wasm-cache/` (git-ignored, about 65 MB); the first
compile is serialized by a lock (parallel first runs raced on the cache file and died with SIGBUS, measured).
"""
import hashlib
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
PIN = {
    "package": "yowasp-yosys==0.53.0.0.post912",
    "packages": {"yowasp-yosys": "0.53.0.0.post912", "yowasp-runtime": "1.96", "wasmtime": "47.0.1"},
    "version_line": "Yosys 0.53 (git sha1 53c22ab7c, ccache clang 18.1.3 -O3 -flto -flto)",
    "wasm_sha256": "909a42f5c804ee9b29ca0570fc558419db55df4d5e817fdb02dbd808cbda2fad",
}
# the version line of ABC inside the module: `yosys-abc` is not a separate program in this build
ABC_VERSION = "ABC linked into " + PIN["package"] + " (yosys.wasm sha256 " + PIN["wasm_sha256"] + ")"
INSTALL = "python3.12 -m pip install -r requirements.txt"
EXIT_PIN = 3


class PinError(Exception):
    pass


def default_cache():
    return os.path.join(HERE, ".wasm-cache")


def cache_dir():
    """Where the module's machine code is cached: $YOWASP_CACHE_DIR, else score/.wasm-cache."""
    return os.environ.get("YOWASP_CACHE_DIR") or default_cache()


def _yowasp():
    try:
        import yowasp_yosys
        import yowasp_runtime  # noqa: F401
        import wasmtime  # noqa: F401
    except ImportError as e:
        raise PinError(f"the rating build is not installed ({e}): {INSTALL}")
    return yowasp_yosys


def wasm_path():
    return os.path.join(os.path.dirname(os.path.abspath(_yowasp().__file__)), "yosys.wasm")


def share_dir():
    """The module's data directory (Yosys's `share`: techmap.v, simcells.v, ...) on the host; inside the module it is
    `/share`."""
    return os.path.join(os.path.dirname(os.path.abspath(_yowasp().__file__)), "share")


def package_dirs():
    """The directories of the packages the launcher imports (for a sandbox's read and executable-map lists)."""
    import importlib
    out = []
    for name in ("yowasp_yosys", "yowasp_runtime", "wasmtime", "platformdirs"):
        mod = importlib.import_module(name)
        d = os.path.dirname(os.path.abspath(mod.__file__))
        out.append(d if os.path.basename(mod.__file__) == "__init__.py" else mod.__file__)
    return out


def _module_bytes():
    with open(wasm_path(), "rb") as fh:
        return fh.read()


_CHECKED = {}


def check_pin():
    """Raise PinError unless the installed module is the pinned one (its sha256) and the runtime packages are the
    pinned versions: a ranked number is never made by another module. Returns the module's bytes' sha1 (the name of
    its cache entry). Cached per process."""
    if "sha1" in _CHECKED:
        return _CHECKED["sha1"]
    _yowasp()
    from importlib import metadata
    bad = []
    for name, want in PIN["packages"].items():
        try:
            got = metadata.version(name)
        except metadata.PackageNotFoundError:
            got = None
        if got != want:
            bad.append(f"{name} is {got or 'not installed'}, the pin is {want}")
    data = _module_bytes()
    got = hashlib.sha256(data).hexdigest()
    if got != PIN["wasm_sha256"]:
        bad.append(f"yosys.wasm ({wasm_path()}) has sha256 {got}, the pinned module is {PIN['wasm_sha256']}")
    if bad:
        raise PinError("not the rating build: " + "; ".join(bad) + f" ({INSTALL})")
    _CHECKED["sha1"] = hashlib.sha1(data).hexdigest()
    return _CHECKED["sha1"]


def cache_file(cache=None):
    """The cache entry of the pinned module, where yowasp_runtime looks for it."""
    return os.path.join(cache or cache_dir(), "yowasp_yosys", "yosys.wasm", check_pin())


def warm(cache=None):
    """Compile the module into the cache once, under an exclusive lock (a no-op when its entry is there). Returns the
    entry's path."""
    cache = cache or cache_dir()
    entry = cache_file(cache)
    if os.path.isfile(entry) and os.path.getsize(entry) > 0:
        return entry
    os.makedirs(cache, exist_ok=True)
    try:
        import fcntl
    except ImportError:          # Windows: no lock; run the first check alone
        fcntl = None
    with open(os.path.join(cache, ".lock"), "w") as lock:
        if fcntl:
            fcntl.flock(lock, fcntl.LOCK_EX)
        if not (os.path.isfile(entry) and os.path.getsize(entry) > 0):
            saved_env = os.environ.get("YOWASP_CACHE_DIR")
            os.environ["YOWASP_CACHE_DIR"] = cache
            devnull = os.open(os.devnull, os.O_WRONLY)
            saved = os.dup(1)
            os.dup2(devnull, 1)
            try:
                rc = _yowasp().run_yosys(["-V"])
            finally:
                os.dup2(saved, 1)
                os.close(devnull)
                os.close(saved)
                if saved_env is None:
                    os.environ.pop("YOWASP_CACHE_DIR", None)
                else:
                    os.environ["YOWASP_CACHE_DIR"] = saved_env
            if rc != 0 or not os.path.isfile(entry):
                raise PinError(f"compiling the module into {cache} failed (exit {rc})")
    return entry


def self_check():
    """`--self-check`: the module's sha256 and the package versions against the pins, then the module's own version
    line; exit 0 only when every one is the pinned value."""
    try:
        check_pin()
        entry = warm()
    except PinError as e:
        print(f"yosys_wasm: {e}", file=sys.stderr)
        return EXIT_PIN
    import subprocess
    out = subprocess.run([sys.executable, os.path.abspath(__file__), "-V"], capture_output=True, text=True)
    line = out.stdout.strip()
    from importlib import metadata
    print(f"module   {wasm_path()}")
    print(f"sha256   {hashlib.sha256(_module_bytes()).hexdigest()}  (pinned {PIN['wasm_sha256']})")
    for name, want in PIN["packages"].items():
        print(f"package  {name}=={metadata.version(name)}  (pinned {want})")
    print(f"version  {line}")
    print(f"cache    {entry}")
    if out.returncode != 0 or line != PIN["version_line"]:
        print(f"yosys_wasm: the module's version line is {line!r}, the pin is {PIN['version_line']!r}",
              file=sys.stderr)
        return EXIT_PIN
    print("ok: the rating build (the same module on every machine)")
    return 0


def main(argv=None):
    argv = sys.argv[1:] if argv is None else argv
    if argv == ["--self-check"]:
        return self_check()
    try:
        check_pin()
        cache = cache_dir()
        warm(cache)
    except PinError as e:
        print(f"yosys_wasm: {e}", file=sys.stderr)
        return EXIT_PIN
    os.environ["YOWASP_CACHE_DIR"] = cache
    return _yowasp().run_yosys(list(argv))


if __name__ == "__main__":
    sys.exit(main())
