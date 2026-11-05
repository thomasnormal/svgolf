#!/usr/bin/env python3.12
"""Fetch the third-party sources the X8 census reads, by pinned commit, and verify (or pin) their sha256.

    python3.12 -I fetch_src.py --list x8_files.tsv --dest DIR [--pin]

The files are NOT vendored in this repository (licences differ; see svgolf/design/real-world-sv/rb0/CENSUS.md for the
projects and their licences) and are untrusted data: they are parsed by pyslang, never executed. The commits are the
ones the RB0 census pinned (svgolf/design/real-world-sv/rb0/files.tsv). Each row of the list is
    project <TAB> repo <TAB> commit <TAB> path <TAB> sha256
With --pin, a row whose sha256 is `-` is filled in from the download and the list is rewritten; without it, every
file must match its recorded sha256 (exit status 1 otherwise).
"""
import argparse
import hashlib
import os
import sys
import urllib.request


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--list", required=True)
    ap.add_argument("--dest", required=True)
    ap.add_argument("--pin", action="store_true")
    a = ap.parse_args()
    rows, out, bad, n = [], [], 0, 0
    for line in open(a.list):
        if line.startswith("#") or not line.strip():
            out.append(line.rstrip("\n"))
            continue
        proj, repo, commit, path, sha = line.rstrip("\n").split("\t")
        dst = os.path.join(a.dest, proj, path)
        os.makedirs(os.path.dirname(dst), exist_ok=True)
        if not os.path.exists(dst):
            url = "https://raw.githubusercontent.com/%s/%s/%s" % (repo, commit, path)
            try:
                data = urllib.request.urlopen(url, timeout=60).read()
            except Exception as exc:  # noqa: BLE001
                print("FETCH FAILED %s@%s:%s (%s)" % (repo, commit, path, exc), file=sys.stderr)
                bad += 1
                out.append(line.rstrip("\n"))
                continue
            open(dst, "wb").write(data)
        got = hashlib.sha256(open(dst, "rb").read()).hexdigest()
        if sha == "-" and a.pin:
            sha = got
        elif got != sha:
            print("SHA MISMATCH %s: expected %s got %s" % (path, sha, got), file=sys.stderr)
            bad += 1
        n += 1
        out.append("\t".join([proj, repo, commit, path, sha]))
    if a.pin:
        open(a.list, "w").write("\n".join(out) + "\n")
    print("%d files in %s, %d problem(s)" % (n, a.dest, bad))
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
