#!/usr/bin/env python3.12
"""prepare.py --out ROUND [--task T ...] [--jobs N]: the first of a round's three place-and-route steps
(score/pnr/README.md, "A round's runs, in one sequence"), run on the maintainers' machine in this tree, with the rating
build and the five ASAP7 liberty files. For every design file the routed course lists as WAITING for its run (a pending
entry of leaderboard/asap7pnr/<task>.json: a stored request and no run; an entry that shares another design's run,
`shares`, needs none: one run per netlist), the steps 0 and 1 of "The commands, for one design":

  0. its ASAP7 netlist, by the command leaderboard.py `run_asap7` builds (score/ppa.py DESIGN.sv --task tasks/T --pdk
     asap7 --no-mapped, --seq on a clocked task) with --repaired-netlist; its sha256 must be the entry's
     `netlist_sha256` (the netlist the entry binds), else the design is refused, named, and gets no job;
  1. its job at the stored request's seed (job.py, into ROUND/job), and `run_job.py run --dry-run` (the pins check of
     the config.mk, and the container command; a render needs the run's database, so it is made on the host).

Writes ROUND/jobs.json (per design: task, sv_sha256, of, seed, netlist, job), ROUND/jobs.txt (the job names, the small
tasks first and matmul last), ROUND/netlists/ (each netlist, ppa.py's output and log) and ROUND/tree.tar (the tree's
files as they are now, under svgolf/: the course host's steps run this tree's score/pnr, collect.py and
leaderboard.py). A design the course shows that has NO stored request is listed and refused: its request is the
maintainers' step, stored in the tree first (`leaderboard.py asap7pnr --request --task T --design FILE --write`).
Nothing in the tree is written. Each ppa.py runs at nice 19 with a one-hour limit, at most --jobs (default 2) at a time.
Exit 0: every waiting design prepared (or none waits); 1: a design refused (the others are prepared); 2: usage or
infrastructure."""

import argparse
import concurrent.futures
import json
import os
import subprocess
import sys
import tarfile
import time

sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
PNR_DIR = os.path.dirname(HERE)
sys.path.insert(0, PNR_DIR)
import pnr  # noqa: E402

sys.path.insert(0, os.path.join(pnr.SVGOLF, "leaderboard"))
import leaderboard as lb  # noqa: E402

ORDER = {"_example": 0, "add": 1, "aes_sbox": 2, "clmul": 3, "mul": 4, "arbiter": 5, "sorter": 6, "fdivp": 7,
         "matmul": 9}                          # the small tasks first, matmul last; any other task in between
PPA_TIMEOUT_S = 3600


def waiting(only=None):
    """(the designs waiting for a run, the designs with no request): [{task, sv_sha256, src, of, seq, seed, source,
    netlist, cycles}] from every task's routed table and the designs its pages show (`asap7_designs`), and [(task,
    sv_sha256, of)]. A table that cannot be read is an error (ValueError)."""
    with open(lb.EXPECTED_JSON, encoding="utf-8") as fh:
        expected = json.load(fh)
    records = lb.good_records(lb.load_records(lb.DEFAULT_DATA), warn=lambda m: print(m, file=sys.stderr))
    rows, none = [], []
    for name in lb.all_task_names(lb.DEFAULT_TASKS):
        if only and name not in only:
            continue
        task = lb.load_task(lb.DEFAULT_TASKS, name)
        designs = lb.asap7_designs(task, records, expected)
        if not designs:
            continue
        table, why = lb.read_asap7pnr(name)
        if why:
            raise ValueError(why)
        seq = lb.task_flow(task) == lb.SEQ_FLOW
        for sha in sorted(designs):
            e = lb.asap7pnr_entry(table, sha) if table else None
            if e is None:
                none.append((name, sha, sorted(designs[sha]["of"])))
                continue
            if e.get("status") != "pending" or lb.PNR_SHARES_KEY in e:
                continue
            rows.append({"task": name, "sv_sha256": sha, "src": designs[sha]["src"], "of": sorted(designs[sha]["of"]),
                         "seq": seq, "seed": e["request"]["seed"], "source": e["request"]["source"],
                         "netlist": e["netlist_sha256"], "cycles": e["cycles"]})
    rows.sort(key=lambda r: (ORDER.get(r["task"], 8), r["task"], r["sv_sha256"]))
    return rows, none


def netlist(row, out):
    """Step 0 for one design: its ASAP7 netlist under out/netlists/T/SV16.v; the row with `seconds`, `exit`,
    `got_netlist` and `ok` (the netlist is the entry's)."""
    d = os.path.join(out, "netlists", row["task"])
    os.makedirs(d, exist_ok=True)
    tmp = os.path.join(out, "tmp")
    os.makedirs(tmp, exist_ok=True)
    sv16 = row["sv_sha256"][:16]
    net = os.path.join(d, sv16 + ".v")
    cmd = [lb.checker_python(), lb.PPA_PY, row["src"], "--task", os.path.join(lb.DEFAULT_TASKS, row["task"]), "--pdk",
           "asap7", "--no-mapped"] + (["--seq"] if row["seq"] else []) + ["--repaired-netlist", net]
    t0 = time.time()
    try:
        p = subprocess.run(["nice", "-n", "19"] + cmd, capture_output=True, text=True, cwd=tmp, timeout=PPA_TIMEOUT_S,
                           env=dict(os.environ, TMPDIR=tmp))
        rc, so, se = p.returncode, p.stdout, p.stderr
    except subprocess.TimeoutExpired:
        rc, so, se = None, "", f"over {PPA_TIMEOUT_S} s"
    with open(os.path.join(d, sv16 + ".json"), "w", encoding="utf-8") as fh:
        fh.write(so)
    with open(os.path.join(d, sv16 + ".log"), "w", encoding="utf-8") as fh:
        fh.write(se[-200000:])
    got = pnr.sha256_file(net) if os.path.exists(net) else None
    return dict(row, seconds=round(time.time() - t0, 1), exit=rc, got_netlist=got, ok=rc == 0 and got == row["netlist"],
                netlist_file=net)


def job(row, out):
    """Step 1 for one design whose netlist is the entry's: job.py at the stored seed, then the run's dry run. The row
    with `job` and `why` (None when every step passed)."""
    jd = os.path.join(out, "job")
    p = subprocess.run([sys.executable, os.path.join(PNR_DIR, "job.py"), "--task", row["task"], "--netlist",
                        row["netlist_file"], "--seed", str(row["seed"]), "--out", jd], capture_output=True, text=True)
    lines = p.stdout.strip().splitlines()
    name = lines[-1].split()[0].rstrip(":") if p.returncode == 0 and lines else None
    if name is None:
        return dict(row, job=None, why=f"job.py exit {p.returncode}: {(p.stdout + p.stderr).strip()[-300:]}")
    d = subprocess.run([sys.executable, os.path.join(PNR_DIR, "run_job.py"), "run", jd, name, "--dry-run"],
                       capture_output=True, text=True)
    if d.returncode != 0:
        return dict(row, job=name, why=f"run_job.py run --dry-run exit {d.returncode}: {d.stderr.strip()[-300:]}")
    return dict(row, job=name, why=None)


def tree_tar(out):
    """ROUND/tree.tar: the tree's files as they are in the working tree now, under svgolf/ (git ls-files: the tracked
    ones and the new ones git does not ignore)."""
    root = os.path.dirname(pnr.SVGOLF)
    names = subprocess.run(["git", "-C", root, "ls-files", "-z", "--cached", "--others", "--exclude-standard", "--",
                            "svgolf"], capture_output=True, text=True, check=True).stdout.split("\0")
    path = os.path.join(out, "tree.tar")
    with tarfile.open(path, "w") as tar:
        for n in names:
            if n and os.path.isfile(os.path.join(root, n)):
                tar.add(os.path.join(root, n), arcname=n, recursive=False)
    return path


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--out", required=True, metavar="ROUND", help="the round's directory (created; must be new or empty)")
    ap.add_argument("--task", action="append", default=[], help="(repeatable) default: every task")
    ap.add_argument("--jobs", type=int, default=2, help="ppa.py runs at a time (default 2)")
    args = ap.parse_args(argv)
    out = os.path.abspath(args.out)
    if os.path.exists(out) and os.listdir(out):
        print(f"error: {out} is not empty: a round's directory is new", file=sys.stderr)
        return 2
    os.makedirs(out, exist_ok=True)
    try:
        rows, none = waiting(set(args.task))
    except (OSError, ValueError) as e:
        print(f"error: {e}", file=sys.stderr)
        return 2
    status = 0
    for name, sha, of in none:
        print(f"[refused] {name}/{sha[:12]} ({', '.join(of)}): no request stored: `leaderboard.py asap7pnr --request "
              f"--task {name} --design FILE --write` first")
        status = 1
    print(f"{len(rows)} designs wait for their run", flush=True)
    done = []
    with concurrent.futures.ThreadPoolExecutor(max(1, args.jobs)) as ex:
        for r in ex.map(lambda r: netlist(r, out), rows):
            if r["ok"]:
                r = job(r, out)
            else:
                r = dict(r, job=None, why=f"its ASAP7 netlist is {str(r['got_netlist'])[:16]}, the entry binds "
                         f"{r['netlist'][:16]} (ppa.py exit {r['exit']}): the tree's ASAP7 view is not current")
            done.append(r)
            print(f"{'[ok]' if r['why'] is None else '[refused]'} {r['task']}/{r['sv_sha256'][:12]} seed {r['seed']} "
                  f"{r['job'] or ''} ({r['seconds']} s){'' if r['why'] is None else ': ' + r['why']}", flush=True)
    done.sort(key=lambda r: (ORDER.get(r["task"], 8), r["task"], r["sv_sha256"]))
    with open(os.path.join(out, "jobs.json"), "w", encoding="utf-8") as fh:
        fh.write(json.dumps(done, indent=1, sort_keys=True) + "\n")
    jobs = [r["job"] for r in done if r["why"] is None]
    with open(os.path.join(out, "jobs.txt"), "w", encoding="utf-8") as fh:
        fh.write("".join(f"{j}\n" for j in jobs))
    tree_tar(out)
    status = status or (1 if any(r["why"] for r in done) else 0)
    print(f"prepared {len(jobs)} of {len(done)} jobs in {out} (jobs.txt, job/, tree.tar); next, on the course host: "
          "score/pnr/campaign/host.py run ROUND")
    return status


if __name__ == "__main__":
    sys.exit(main())
