#!/usr/bin/env python3.12
"""finish.py ROUND [--task T ...]: the last of a round's three place-and-route steps (score/pnr/README.md, "A round's
runs, in one sequence"), back on the maintainers' machine in this tree, with the five ASAP7 liberty files and Pillow:
ROUND/back.tar (host.py pack) unpacked into ROUND/back/, then, for every design prepare.py listed (ROUND/jobs.json),
the steps 3 and 4 of "The commands, for one design":

  per design whose run is VALID (its row: exit 0, DRC 0, every flow equivalence check IDENTICAL and the
  reference-against-routed check IDENTICAL):  encode.py (the picture and thumbnail into ROUND/out/T/images/T/), then
  `collect.py entry` (ROUND/entries/T/SV16.json); a design whose run is not valid is reported with the row's reason and
  stays pending: nothing is changed to make it pass (CONTRIBUTING.md, section 11);
  per task:  `collect.py sitedata --out ROUND/out/T` with its new entries, then `check_sitedata.py ROUND/out/T --task T
  --jobs ROUND/back/job`.

Nothing in the tree is written: it prints, per task whose check passed, the import the maintainers run
(`leaderboard.py asap7pnr --import ROUND/out/T --task T --write`), and writes ROUND/finish.json (per design: task,
sv_sha256, job, seed, valid, reason, area, delay, seconds, peak memory). Exit 0: every design valid and every check
passed; 1: a run not valid or a check failed (the rest is collected); 2: usage."""

import argparse
import json
import os
import subprocess
import sys
import tarfile

sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
PNR_DIR = os.path.dirname(HERE)
sys.path.insert(0, PNR_DIR)
import pnr  # noqa: E402


def row_validity(row):
    """(valid, reason) of a job's row (collect.py row): the course's validity rule as the row records it."""
    lr = (row.get("lec_reference") or {}).get("verdict")
    ok = (row.get("status") == "ok" and row.get("rc") == 0 and row.get("drc") == 0 and bool(row.get("lec"))
          and all(str(v).endswith(":IDENTICAL") for v in row["lec"]) and lr == "IDENTICAL")
    if ok:
        return True, None
    return False, (row.get("error") or row.get("error_code") or f"status {row.get('status')}, exit {row.get('rc')}, DRC "
                   f"{row.get('drc')}, the flow's checks {row.get('lec')}, the reference-against-routed check {lr}")


def unpack(rnd):
    """ROUND/back.tar into ROUND/back/ (members under job/ and logs/ only, no links, no absolute or parent paths)."""
    src, dst = os.path.join(rnd, "back.tar"), os.path.join(rnd, "back")
    with tarfile.open(src) as tar:
        members = []
        for m in tar.getmembers():
            parts = m.name.split("/")
            if not (m.isfile() or m.isdir()) or m.name.startswith("/") or ".." in parts or parts[0] not in ("job", "logs"):
                raise ValueError(f"back.tar: {m.name!r} is not a file of the round")
            members.append(m)
        tar.extractall(dst, members=members, filter="data")
    return os.path.join(dst, "job")


def run(cmd):
    p = subprocess.run(cmd, cwd=pnr.SVGOLF, capture_output=True, text=True,
                       env=dict(os.environ, PYTHONDONTWRITEBYTECODE="1"))
    return p.returncode, (p.stdout + p.stderr).strip()


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("round", help="the round's directory (prepare.py --out), with back.tar from the course host")
    ap.add_argument("--task", action="append", default=[], help="(repeatable) default: every task of jobs.json")
    args = ap.parse_args(argv)
    rnd = os.path.abspath(args.round)
    try:
        with open(os.path.join(rnd, "jobs.json"), encoding="utf-8") as fh:
            rows = [r for r in json.load(fh) if r.get("job") and (not args.task or r["task"] in args.task)]
        jd = unpack(rnd)
    except (OSError, ValueError, tarfile.TarError) as e:
        print(f"error: {e}", file=sys.stderr)
        return 2
    res, by_task, status = [], {}, 0
    for r in rows:
        t, sv, job = r["task"], r["sv_sha256"], r["job"]
        sv16 = sv[:16]
        x = {"task": t, "sv_sha256": sv, "job": job, "seed": r["seed"]}
        rp = os.path.join(jd, "rows", job + ".json")
        if not os.path.exists(rp):
            x.update(valid=False, reason="no row: the job did not finish on the course host")
        else:
            with open(rp, encoding="utf-8") as fh:
                row = json.load(fh)
            valid, why = row_validity(row)
            x.update(valid=valid, reason=why, seconds=row.get("seconds"), peak_mem_mb=row.get("peak_mem_mb"))
        if x["valid"]:
            out = os.path.join(rnd, "out", t)
            ent = os.path.join(rnd, "entries", t, sv16 + ".json")
            os.makedirs(os.path.dirname(ent), exist_ok=True)
            rc1, o1 = run([sys.executable, "-I", os.path.join(PNR_DIR, "encode.py"), os.path.join(jd, "img", job + ".png"),
                           os.path.join(out, "images"), t, sv16, "--json", os.path.join(jd, "img", f"{job}.{sv16}.json")])
            rc2, o2 = run([sys.executable, os.path.join(PNR_DIR, "collect.py"), "entry", "--task", t, "--sv", sv, jd, job,
                           "--out", ent]) if rc1 == 0 else (None, "")
            if rc1 == 0 and rc2 == 0:
                with open(ent, encoding="utf-8") as fh:
                    e = json.load(fh)
                vo = e["scores"]["v_owner"]
                x.update(area_um2=vo["area_e5um2"] / 1e5, time_ps=vo["time_ps"], um2ns=vo["um2ns"])
                by_task.setdefault(t, []).append(ent)
            else:
                x.update(valid=False, reason=f"encode.py exit {rc1}: {o1[-300:]}" if rc1 else
                         f"collect.py entry exit {rc2}: {o2[-300:]}")
        status = status or (0 if x["valid"] else 1)
        res.append(x)
        print(f"{'[valid]' if x['valid'] else '[NOT VALID]'} {t}/{sv[:12]} {job}"
              + (f": {x['area_um2']:.3f} um2 x {x['time_ps']} ps = {x['um2ns']:.4g} um2*ns" if x["valid"]
                 else f": {x['reason']}"), flush=True)
    imports = []
    for t, ents in sorted(by_task.items()):
        out = os.path.join(rnd, "out", t)
        rc3, o3 = run([sys.executable, os.path.join(PNR_DIR, "collect.py"), "sitedata", "--task", t, "--out", out]
                      + sorted(ents))
        rc4, o4 = run([sys.executable, os.path.join(PNR_DIR, "check_sitedata.py"), out, "--task", t, "--jobs", jd]) \
            if rc3 == 0 else (None, "")
        with open(os.path.join(rnd, f"check_sitedata_{t}.log"), "w", encoding="utf-8") as fh:
            fh.write(o3 + "\n" + o4 + "\n")
        ok = rc3 == 0 and rc4 == 0
        status = status or (0 if ok else 1)
        print(f"{'[ok]' if ok else '[FAIL]'} {t}: sitedata exit {rc3}, check_sitedata exit {rc4}: "
              + ((o4.splitlines() or [""])[-1] if rc3 == 0 else o3[-300:]))
        for x in res:
            if x["task"] == t:
                x.update(sitedata_ok=rc3 == 0, check_ok=rc4 == 0)
        if ok:
            imports.append(f"python3.12 leaderboard/leaderboard.py asap7pnr --import {out} --task {t} --write")
    with open(os.path.join(rnd, "finish.json"), "w", encoding="utf-8") as fh:
        fh.write(json.dumps(res, indent=1, sort_keys=True) + "\n")
    print(f"{sum(1 for x in res if x['valid'])} of {len(res)} designs valid; the imports (in svgolf/, then the gates):"
          + "".join(f"\n  {c}" for c in imports))
    return status


if __name__ == "__main__":
    sys.exit(main())
