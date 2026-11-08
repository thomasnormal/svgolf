#!/usr/bin/env python3.12
"""svGolf's ONE extraction path: a SystemVerilog file -> an sv-0.2 envelope.

    python3.12 check/envelope.py DESIGN.sv [--task DIR | --top TOP [--probe-points P]]
                                 [--cache-dir DIR]

Every svGolf consumer of an envelope goes through this module, so the design a
proof is about is always extracted the same way:

* `check.py` (stages `source` and `extract`) calls `gate` and
  `run_extractor` on each submission, into its staging directory;
* the `load_sv` command (`SvGolf/LoadSv.lean`) runs THIS FILE as a program at
  elaboration time (the command line above) and loads the envelope it names
  exactly as `load_design_sv2` would;
* the validation scripts under `tests/` call `extract`.

The path, in order:

1. the SOURCE GATE (`score/srcgate.py`): directives, attributes, pragma
   comments and `unique`/`priority` qualifiers are refused, and every comment
   is blanked; the gate's CANONICAL text is what gets extracted (and what the
   banlist and Yosys read), never the file as written;
2. the PINNED lean-surfaces extractor (`extractors/sv/extract.py --top TOP`,
   symbolic mode) on the canonical text, with `--probe-points` whenever there
   are probe points: it writes the envelope and the multi-point cross-check
   sidecar (`<envelope minus .json>.probes.json`), which `load_design_sv2`
   reads next to the envelope.

A task's probe points (`probe_points`) are its `probe_points` plus its scoring
point and its backstop points, always: the scored design must be one the
cross-check saw.

The command line is the `load_sv` CACHE. With `--task DIR` the top module and
the probe points are the task's (`DIR/task.json`), exactly as `check.py` takes
them; with neither `--task` nor `--top`, the task is inferred from the design's
path (`tasks/<name>/...` or `tests/<name>/...` under the svGolf root means
`tasks/<name>`). The envelope is written to

    <cache-dir>/<path of DESIGN.sv relative to the svGolf root>.<key>.json

(and the sidecar next to it, `.probes.json`; the canonical text the extractor
read, `.sv`), where `<key>` hashes the canonical text, the design's file name,
the top, the probe points, the extractor's source, this file's source and the
pyslang version. The default cache directory is `<svgolf>/.lake/envelopes`.
An entry is reused while its key matches; a changed design, extractor or
argument extracts afresh (old entries are left behind: `rm -rf` the directory
to reclaim the space). Prints one JSON object: `envelope` and `probes` (paths,
relative to the current directory when inside it; `probes` is null without
probe points), `key`, `cached`. Exit status: 0 = written or reused,
1 = the source gate or the extractor refused the design (stderr says why),
2 = usage or infrastructure error (no pyslang, no extractor, bad task).

Environment: SVGOLF_LS_ROOT (the lean-surfaces checkout; default the parent
directory when svGolf sits inside lean-surfaces, else `.lake/packages/lean-models`:
check/layout.py), SVGOLF_PYTHON (the interpreter that runs the extractor; default
python3.12).
"""

import argparse
import hashlib
import importlib.metadata
import json
import os
import shutil
import stat
import subprocess
import sys
import tempfile

import sandbox  # noqa: E402  (check/sandbox/: the scrubbed environment of every child; this file's directory is on sys.path)
import layout  # noqa: E402  (check/layout.py: where lean-surfaces is, in either layout)

sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
SVGOLF = os.path.dirname(HERE)
# lean-surfaces: the parent directory inside it, `.lake/packages/lean-models` standalone (check/layout.py)
LS_ROOT = layout.LS_ROOT
LAYOUT = layout.LAYOUT
EXTRACTOR = os.path.join(LS_ROOT, "extractors", "sv", "extract.py")
# extract.py imports it (WP-PROC, 2026-11-01): the logic of the procedural / Verilog-2001 lowerings lives there
LOWER_PROC = os.path.join(LS_ROOT, "extractors", "sv", "lower_proc.py")
DEFAULT_CACHE = os.path.join(SVGOLF, ".lake", "envelopes")
# Bump when the cache layout or the meaning of an entry changes.
CACHE_VERSION = 1


class InfraError(Exception):
    """Not the design's fault: a missing tool, a bad task, a broken install."""


class Refused(Exception):
    """The design's fault: the source gate or the extractor refused it."""

    def __init__(self, stage, msg):
        super().__init__(msg)
        self.stage, self.msg = stage, msg


def python():
    return os.environ.get("SVGOLF_PYTHON", "python3.12")


def sha256_bytes(b):
    return hashlib.sha256(b).hexdigest()


def extractor_files():
    """The files of the pinned extractor: `extract.py` and the module it imports from its own directory
    (`lower_proc.py` since WP-PROC; an older ls-sv checkout has `extract.py` alone)."""
    return [EXTRACTOR] + ([LOWER_PROC] if os.path.isfile(LOWER_PROC) else [])


def extractor_sha256():
    """The identity of the pinned extractor program, for the stage record (and so the leaderboard) and the cache
    key: the sha256 of `extract.py` while it is the only file (the value of every record from before
    `lower_proc.py`), else the sha256 of the sorted `<name>:<sha256>` lines of all of its files."""
    files = extractor_files()
    if len(files) == 1:
        return sha256_file(files[0])
    lines = sorted("%s:%s" % (os.path.basename(f), sha256_file(f)) for f in files)
    return sha256_bytes("\n".join(lines).encode())


def sha256_file(path):
    with open(path, "rb") as fh:
        return sha256_bytes(fh.read())


def tail(text, n=4000):
    return text if len(text) <= n else "..." + text[-n:]


# ---------------------------------------------------------------------------
# parameter points
# ---------------------------------------------------------------------------

def parse_point(p):
    """`{"N": 16}` or `"N=16,M=2"` -> {"N": 16, "M": 2}."""
    if isinstance(p, dict):
        return {k: int(v) for k, v in p.items()}
    return {kv.split("=")[0].strip(): int(kv.split("=")[1]) for kv in p.split(",") if kv}


def point_str(p):
    return ",".join(f"{k}={v}" for k, v in p.items())


def probe_points(task):
    """The multi-point cross-check's points: the task's `probe_points`, plus
    the scoring point and the backstop points, always (the scored design
    must be one the cross-check saw). Empty for a parameterless top."""
    pts = []
    for p in (list(task.get("probe_points", [])) + [task["scoring"]["params"]]
              + list(task.get("backstop_points") or [])):
        q = parse_point(p)
        if q and q not in pts:
            pts.append(q)
    return pts


def load_task(task_dir):
    path = os.path.join(task_dir, "task.json")
    try:
        with open(path) as fh:
            return json.load(fh)
    except (OSError, json.JSONDecodeError) as e:
        raise InfraError(f"cannot read the task file {path}: {e}")


# ---------------------------------------------------------------------------
# the two steps
# ---------------------------------------------------------------------------

def gate(sv_path, name=None, clock=None):
    """The source gate: (canonical text or None, findings); `clock`: a clocked task's clock
    port (the gate's clocked rules, srcgate.py item 6)."""
    if os.path.join(SVGOLF, "score") not in sys.path:
        sys.path.insert(0, os.path.join(SVGOLF, "score"))
    try:
        import srcgate
        import pyslang  # noqa: F401  (srcgate imports it lazily; fail here, as infrastructure)
    except ImportError as e:
        raise InfraError(f"the source gate (score/srcgate.py) cannot run under {sys.executable}: "
                         f"{e}. It needs pyslang: install it for this interpreter "
                         "(`python3.12 -m pip install pyslang`), or run with a Python that has it")
    return srcgate.gate_file(sv_path, name=name, clock=clock)


# What to do when lean-surfaces (and with it the pinned extractor) is not where it should be: Lake fetches it into
# `.lake/packages/lean-models` (standalone) the first time the project is built.
BUILD_FIRST = "run `lake build` from the repository root first (README, Building)"


def missing_extractor_message():
    """The infrastructure error for an extractor that is not there, with the remedy."""
    where = (", or point SVGOLF_LS_ROOT at a lean-surfaces checkout" if os.environ.get("SVGOLF_LS_ROOT")
             else "")
    return (f"the pinned extractor {EXTRACTOR} does not exist (SVGOLF_LS_ROOT={LS_ROOT}): "
            f"{BUILD_FIRST}{where}")


def extractor_has_probe_points():
    try:
        out = subprocess.run([python(), EXTRACTOR, "--help"], capture_output=True, text=True,
                             env=sandbox.scrubbed_env())
    except OSError as e:
        raise InfraError(f"cannot run `{python()}` for the extractor ({e}); set SVGOLF_PYTHON")
    return "--probe-points" in out.stdout


def run_extractor(canon_path, top, probe_pts, env_path):
    """Run the pinned extractor on the canonical text at `canon_path`, writing
    the envelope to `env_path` (and, with probe points, the sidecar
    `<env_path minus .json>.probes.json`). The extractor runs in the canonical
    file's directory and is handed its BASE NAME, so the envelope records that
    name, not where the file happens to live. Returns (subprocess result,
    command line). Raises InfraError when the extractor is missing or cannot
    cross-check; the caller judges a nonzero exit."""
    if not os.path.isfile(EXTRACTOR):
        raise InfraError(missing_extractor_message())
    cmd = [python(), EXTRACTOR, "--top", top, os.path.basename(canon_path),
           "-o", os.path.abspath(env_path)]
    if probe_pts:
        if not extractor_has_probe_points():
            raise InfraError("the extractor has no --probe-points: the multi-point cross-check "
                             "(which includes the scoring point) cannot run; it is older than the "
                             f"lean-models revision the manifest pins: {BUILD_FIRST}")
        cmd += ["--probe-points", ";".join(point_str(p) for p in probe_pts)]
    pol = sandbox.policy()
    try:
        if pol.active:
            proc = _run_extractor_sandboxed(cmd, canon_path, env_path)
        else:
            proc = subprocess.run(cmd, cwd=os.path.dirname(os.path.abspath(canon_path)),
                                  capture_output=True, text=True, env=sandbox.scrubbed_env())
    except OSError as e:
        raise InfraError(f"cannot run `{python()}` for the extractor ({e}); set SVGOLF_PYTHON")
    return proc, cmd


def _run_extractor_sandboxed(cmd, canon_path, env_path):
    """The pinned extractor on the canonical text, under the sandbox (WP-S): it reads the text, its own
    directory, the interpreter and pyslang; it writes a fresh output directory, from which the checker
    adopts the envelope and the probe sidecar (and nothing else) into the staging tree."""
    pol = sandbox.policy()
    outdir = pol.mkdtemp("extract-")
    canon_dir = os.path.dirname(os.path.abspath(canon_path))
    spec, pyenv = sandbox.python_spec(cmd[0], os.path.dirname(EXTRACTOR), read=[canon_dir], write=[outdir],
                                      label="extractor")
    scmd = [cmd[0], "-s", "-B"] + cmd[1:]
    scmd[scmd.index("-o") + 1] = os.path.join(outdir, os.path.basename(env_path))
    proc = sandbox.run(scmd, spec, env=sandbox.tool_env(outdir, pyenv), cwd=canon_dir, timeout=600,
                       kind="tool", label="extractor")
    produced = {os.path.basename(env_path): env_path,
                os.path.basename(sidecar_path(env_path)): sidecar_path(env_path)}
    for name in sorted(os.listdir(outdir)):
        src = os.path.join(outdir, name)
        if name in produced and stat.S_ISREG(os.lstat(src).st_mode):
            shutil.copyfile(src, produced[name])
        elif name != "tmp":
            pol.note["stray_outputs"].append(name[:80])
    return proc


def sidecar_path(env_path):
    return (env_path[:-len(".json")] if env_path.endswith(".json") else env_path) + ".probes.json"


def extract(sv_path, top, probe_pts, out_dir, name=None):
    """Gate + extract `sv_path` into `out_dir` (canonical text under the
    design's own base name, envelope `<name>.json`, sidecar). Returns
    {canonical, canonical_sha256, envelope, probes}. Raises Refused/InfraError."""
    name = name or os.path.basename(sv_path)
    canon, findings = gate(sv_path, name=name)
    if findings:
        raise Refused("source", "the source gate refused the design:\n" + "\n".join(findings[:8]))
    os.makedirs(out_dir, exist_ok=True)
    sv = os.path.join(out_dir, name)
    with open(sv, "w", newline="") as fh:
        fh.write(canon)
    env = sv + ".json"
    proc, cmd = run_extractor(sv, top, probe_pts, env)
    if proc.returncode != 0 or not os.path.exists(env):
        raise Refused("extract", "the extractor refused the design:\n"
                      + tail(proc.stderr + proc.stdout) + "\n(command: " + " ".join(cmd) + ")")
    probes = sidecar_path(env) if probe_pts else None
    if probes and not os.path.exists(probes):
        raise InfraError("the extractor wrote no probe sidecar")
    return {"canonical": sv, "canonical_sha256": sha256_bytes(canon.encode()),
            "envelope": env, "probes": probes}


# ---------------------------------------------------------------------------
# the load_sv cache
# ---------------------------------------------------------------------------

def infer_task(rel):
    parts = rel.split("/")
    if len(parts) >= 3 and parts[0] in ("tasks", "tests"):
        d = os.path.join(SVGOLF, "tasks", parts[1])
        if os.path.isfile(os.path.join(d, "task.json")):
            return d
    return None


def cache_key(canon, name, top, probe_pts):
    try:
        pyslang = importlib.metadata.version("pyslang")
    except importlib.metadata.PackageNotFoundError:
        pyslang = None
    blob = json.dumps({
        "cache_version": CACHE_VERSION,
        "canonical_sha256": sha256_bytes(canon.encode()),
        "name": name, "top": top, "probe_points": [point_str(p) for p in probe_pts],
        "extractor_sha256": extractor_sha256(),
        "envelope_py_sha256": sha256_file(os.path.abspath(__file__)),
        "pyslang": pyslang,
    }, sort_keys=True)
    return sha256_bytes(blob.encode())[:16]


def shown(path):
    """`path` relative to the current directory when inside it."""
    rel = os.path.relpath(path)
    return path if rel.startswith("..") else rel


def cached(sv_path, top, probe_pts, cache_dir):
    sv_abs = os.path.realpath(sv_path)
    rel = os.path.relpath(sv_abs, os.path.realpath(SVGOLF))
    if rel.startswith(".."):
        rel = os.path.join("_abs", sv_abs.lstrip(os.sep))
    name = os.path.basename(sv_abs)
    canon, findings = gate(sv_abs, name=name)
    if findings:
        raise Refused("source", "the source gate refused the design:\n" + "\n".join(findings[:8]))
    if not os.path.isfile(EXTRACTOR):   # before the key, which hashes it
        raise InfraError(missing_extractor_message())
    key = cache_key(canon, name, top, probe_pts)
    base = os.path.join(cache_dir, rel) + "." + key
    env, probes = base + ".json", (base + ".probes.json" if probe_pts else None)
    res = {"envelope": shown(env), "probes": shown(probes) if probes else None, "key": key,
           "top": top, "probe_points": [point_str(p) for p in probe_pts]}
    if os.path.exists(env) and (probes is None or os.path.exists(probes)):
        return dict(res, cached=True)
    os.makedirs(os.path.dirname(base), exist_ok=True)
    tmp = tempfile.mkdtemp(prefix=".tmp-", dir=os.path.dirname(base))
    try:
        # The extractor sees the canonical text under the design's own name and
        # writes the envelope under its FINAL base name (the sidecar records it),
        # so moving both into place changes nothing they record.
        tsv = os.path.join(tmp, name)
        with open(tsv, "w", newline="") as fh:
            fh.write(canon)
        tenv = os.path.join(tmp, os.path.basename(env))
        proc, cmd = run_extractor(tsv, top, probe_pts, tenv)
        if proc.returncode != 0 or not os.path.exists(tenv):
            raise Refused("extract", f"the extractor refused {shown(sv_abs)}:\n"
                          + tail(proc.stderr + proc.stdout)
                          + f"\n(command, in {tmp}: " + " ".join(cmd) + ")")
        if probes:
            tprobes = sidecar_path(tenv)
            if not os.path.exists(tprobes):
                raise InfraError("the extractor wrote no probe sidecar")
            os.replace(tprobes, probes)
        shutil.copyfile(tsv, base + ".sv")
        os.replace(tenv, env)   # last: the envelope's presence marks a complete entry
    finally:
        shutil.rmtree(tmp, ignore_errors=True)
    return dict(res, cached=False)


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("design")
    ap.add_argument("--task", help="task directory: top and probe points from its task.json")
    ap.add_argument("--top", help="top module (without --task)")
    ap.add_argument("--probe-points", default="",
                    help="with --top: probe points, e.g. 'N=1;N=16' (default: none)")
    ap.add_argument("--cache-dir", default=DEFAULT_CACHE)
    args = ap.parse_args(argv)
    try:
        if not os.path.isfile(args.design):
            raise InfraError(f"no such design file: {args.design} (relative paths resolve "
                             f"against the current directory, {os.getcwd()})")
        if args.task and args.top:
            raise InfraError("give either --task or --top, not both")
        if args.top:
            top = args.top
            pts = [parse_point(p) for p in args.probe_points.split(";") if p.strip()]
        else:
            if args.probe_points:
                raise InfraError("--probe-points needs --top (a task brings its own)")
            task_dir = args.task
            if not task_dir:
                rel = os.path.relpath(os.path.realpath(args.design), os.path.realpath(SVGOLF))
                task_dir = infer_task(rel)
                if not task_dir:
                    raise InfraError(
                        f"cannot infer the task of {args.design}: it is not under tasks/<name>/ "
                        "or tests/<name>/ of the svGolf root with a tasks/<name>/task.json; "
                        "name the task (`(task := \"tasks/<name>\")`) or the top module "
                        "(`(top := \"...\")`)")
            task = load_task(task_dir)
            top, pts = task["top"], probe_points(task)
        print(json.dumps(cached(args.design, top, pts, args.cache_dir)))
        return 0
    except Refused as r:
        print(f"{r.stage}: {r.msg}", file=sys.stderr)
        return 1
    except InfraError as e:
        print(f"infrastructure: {e}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
