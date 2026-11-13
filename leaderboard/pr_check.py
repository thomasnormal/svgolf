#!/usr/bin/env python3
"""The check of a pull request that adds records (decided 2026-11-11; README.md, "Leaderboard").

    python3.12 leaderboard/pr_check.py [--base REF] [--head REF] [--sandbox off|auto|require] [--summary FILE]

Run in a checkout of the pull request (`--head`, default HEAD, must be the commit checked out), it reads what the pull
request changes against `--base` (default HEAD^1: the first parent of the merge commit a pull request's check runs
on, the branch it goes to) and checks, in order:

  1. that it ADDS records and changes nothing else: every changed file is one of a record's three files
     (leaderboard/data/<task>/<record_hash>.json, .sv and .lean), added as a plain file (git's mode 100644: not a
     symbolic link, which would make the record's content another path's, and not an executable), and every record
     comes with all three, of a task this repository has, under a player's handle (`svgolf-reference` is
     par's handle, whose records are par: decided 2026-11-12); or a record's WRITEUP (decided 2026-11-13: the
     Markdown file leaderboard/writeups/<record_hash>.md, outside the record), added or improved as a plain file:
     data the site renders safely, never code the check runs, and checked by step 2 (`verify --offline` checks every
     writeup: it names a record, its title, its size, its characters, no internal marker, a body the site renders);
  2. `leaderboard.py verify --offline` on every record (hashes and arithmetic, the added ones included);
  3. `leaderboard.py verify --full` on the added records alone: check.py runs again on each pair, the whole check,
     with `--sandbox` as given (not run when step 1 failed: the pull request would bring the checker it runs).

It prints the result in Markdown, each added record with its board line (`leaderboard.py` `board_line`: the board as
the site shows it, under the rating build's pinned flow), and with `--summary FILE` appends it to FILE (a GitHub
workflow's job summary). The check is advisory: it runs the pull request's own files, this one included; the ranked
number is re-made on the rating build by a maintainer when the pull request is merged, which the text says.

The two refs are resolved to commits first (`git rev-parse --verify --end-of-options`), and one that begins with `-`
is refused, so that no argument can reach git as an option. Paths are read relative to svGolf's directory (`git diff
--relative`): in the public repository that is the whole repository; in a tree where svGolf is a subdirectory, a
change outside it is not seen.

Python 3, standard library only; git on PATH. Exit status: 0 every check passed, 1 a check failed or the pull
request changes more than records, 2 usage or infrastructure (git cannot compare the two refs).
"""

import argparse
import importlib.util
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
SVGOLF = os.path.dirname(HERE)
LEADERBOARD_PY = os.path.join(HERE, "leaderboard.py")


def _load_leaderboard():
    spec = importlib.util.spec_from_file_location("svgolf_leaderboard", LEADERBOARD_PY)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


lb = _load_leaderboard()

# a record's file, as a path relative to svGolf's directory: (task, record_hash, extension)
RECORD_FILE_RE = re.compile(r"leaderboard/data/([^/]+)/([0-9a-f]{64})\.(json|sv|lean)")
RECORD_EXTS = ("json", "sv", "lean")
# a record's writeup (decided 2026-11-13), as a path relative to svGolf's directory: (record_hash)
WRITEUP_FILE_RE = re.compile(r"leaderboard/writeups/([0-9a-f]{64})\.md")
STATUS_WORDS = {"A": "added", "M": "changed", "D": "deleted", "T": "changed in type"}
RATING_NOTE = "The ranked number is re-made on the rating build by a maintainer when the pull request is merged."
FILE_MODE = "100644"                          # git's mode of a plain, non-executable file
MODE_WORDS = {"120000": "a symbolic link", "100755": "an executable file", "160000": "a submodule"}


class GitError(Exception):
    pass


def git(repo, *args):
    proc = subprocess.run(["git", "-C", repo, *args], capture_output=True, text=True)
    if proc.returncode != 0:
        raise GitError(f"git {' '.join(args)}: {' '.join(proc.stderr.split())[-400:]}")
    return proc.stdout


def resolve(repo, ref, what):
    """The commit `ref` names, as a full hash; a ref that begins with `-` is refused (it would read as an option)."""
    if not ref or ref.startswith("-"):
        raise GitError(f"{what} {ref!r} is not a ref: it begins with `-` or is empty")
    return git(repo, "rev-parse", "--verify", "--end-of-options", f"{ref}^{{commit}}").strip()


def changes(repo, base, head):
    """[(status letter, path, new mode)] of what commit `head` changes against commit `base` (full hashes,
    `resolve`), paths relative to `repo` (svGolf's directory); a rename is a deletion and an addition."""
    out = git(repo, "diff", "--raw", "--no-abbrev", "--no-renames", "-z", "--relative", base, head, "--")
    parts = out.split("\0")
    rows = []
    for k in range(0, len(parts) - 1, 2):
        meta = parts[k].lstrip(":").split()          # src mode, dst mode, src sha, dst sha, status
        rows.append((meta[4][:1], parts[k + 1], meta[1]))
    return rows


def classify(changed):
    """({(task, record_hash): set of extensions added}, [problems]) of `changes`' list: what step 1 accepts and why it
    refuses the rest. Pure."""
    added, problems = {}, []
    for status, path, mode in changed:
        m = RECORD_FILE_RE.fullmatch(path)
        if m and status == "A" and mode != FILE_MODE:
            problems.append(f"`{path}` is added as {MODE_WORDS.get(mode, f'mode {mode}')}: a record's file is a plain "
                            f"file (mode {FILE_MODE})")
        elif m and status == "A":
            added.setdefault((m.group(1), m.group(2)), set()).add(m.group(3))
        elif m:
            problems.append(f"`{path}` is {STATUS_WORDS.get(status, status)}: a pull request of records adds records "
                            "and never edits or removes one")
        elif WRITEUP_FILE_RE.fullmatch(path) and status in ("A", "M") and mode != FILE_MODE:
            problems.append(f"`{path}` is {STATUS_WORDS.get(status, status)} as {MODE_WORDS.get(mode, f'mode {mode}')}:"
                            f" a writeup is a plain file (mode {FILE_MODE})")
        elif WRITEUP_FILE_RE.fullmatch(path) and status in ("A", "M"):
            pass                                  # a writeup added or improved: step 2 checks it (verify --offline)
        elif WRITEUP_FILE_RE.fullmatch(path):
            problems.append(f"`{path}` is {STATUS_WORDS.get(status, status)}: a pull request may add or improve a "
                            "writeup, never remove one")
        else:
            problems.append(f"`{path}` is {STATUS_WORDS.get(status, status)}: it is not a record's file, and a pull "
                            "request of records changes nothing else (it would bring the checker it runs)")
    for (task, h), exts in sorted(added.items()):
        missing = [e for e in RECORD_EXTS if e not in exts]
        if missing:
            problems.append(f"record `{task}/{h[:12]}` lacks " + ", ".join(f"`{h}.{e}`" for e in missing)
                            + ": a record is its three files")
    return added, problems


def handle_problems(added, data_dir):
    """Problems of the added records' handles: a record under par's handle (`lb.REFERENCE_PLAYER`)
    is not a player's record. A JSON file that cannot be read is left to `verify --offline`."""
    out = []
    for task_name, h in sorted(added):
        path = os.path.join(data_dir, task_name, f"{h}.json")
        try:
            with open(path, encoding="utf-8") as fh:
                player = json.load(fh).get("player")
        except (OSError, ValueError, AttributeError):
            continue
        if player == lb.REFERENCE_PLAYER:
            out.append(f"record `{task_name}/{h[:12]}` is under the handle `{player}`, par's own "
                       "(its records are par, not entries): a player's record needs a handle of its own")
    return out


def run_leaderboard(argv, *, data_dir, tasks_dir, check_py=None, writeups_dir=None):
    """leaderboard.py `argv` on `data_dir` (and the writeups of `writeups_dir`): (exit status, output)."""
    cmd = [sys.executable, LEADERBOARD_PY, *argv, "--data-dir", data_dir, "--tasks-dir", tasks_dir]
    if writeups_dir:
        cmd += ["--writeups-dir", writeups_dir]
    if check_py:
        cmd += ["--check-py", check_py]
    proc = subprocess.run(cmd, capture_output=True, text=True)
    return proc.returncode, (proc.stdout + proc.stderr).strip()


def flow_note(flows_now, pinned):
    """Whether this machine's Yosys is the rating build's (`lb.current_flows()` against `lb.pinned_flows()`), in one
    sentence. Pure."""
    now = (flows_now.get(lb.COMB_FLOW) or {}).get("yosys")
    pin = (pinned.get(lb.COMB_FLOW) or {}).get("yosys")
    if now == pin:
        return f"This machine's Yosys is the rating build's ({pin}), so the full check compared the scores too."
    return (f"This machine's Yosys ({now or 'none found'}) is not the rating build's ({pin}), so the full check "
            "compared no score: `verify` calls a record checked under another Yosys stale, which is not a failure.")


def report(*, added, problems, lines, offline, full, sandbox, note):
    """The Markdown text of the check. `lines`: {(task, hash): board line}; `offline`, `full`: (exit status, output)
    of the two verify runs, or None when it did not run. Pure."""
    passed = not problems and offline is not None and offline[0] == 0 and (full is None or full[0] == 0)
    n = len(added)
    out = ["## The records this pull request adds", ""]
    out.append(("Every check passed. " if passed else "**A check failed.** ")
               + (f"It adds {n} record{'s' if n != 1 else ''}." if n else "It adds no record."))
    out.append("")
    out += [f"- {lines[k]}" for k in sorted(lines)]
    if lines:
        out.append("")
    if problems:
        out += ["### Problems", ""] + [f"- {p}" for p in problems] + [""]

    def block(title, res, fold):
        if res is None:
            return [f"### {title}: not run", "", "Not run because of the problems above." if problems else
                    "No record to check.", ""]
        rc, text = res
        body = ["```text", text or "(no output)", "```"]
        if fold:
            body = ["<details><summary>the output</summary>", ""] + body + ["", "</details>"]
        return [f"### {title}: {'ok' if rc == 0 else 'FAILED'} (exit status {rc})", ""] + body + [""]
    out += block("`leaderboard.py verify --offline`, every record", offline, fold=True)
    out += block(f"`leaderboard.py verify --full --sandbox {sandbox}`, the records it adds", full, fold=False)
    out += [RATING_NOTE + " " + note, ""]
    return "\n".join(out), passed


def main(argv=None):
    ap = argparse.ArgumentParser(description="The check of a pull request that adds records.")
    ap.add_argument("--base", default="HEAD^1", help="the branch the pull request goes to (default: HEAD^1, the merge "
                    "commit's first parent)")
    ap.add_argument("--head", default="HEAD", help="the pull request, the commit checked out (default: HEAD)")
    ap.add_argument("--sandbox", choices=("off", "auto", "require"), default=lb.OFFICIAL_SANDBOX_MODE,
                    help="check.py's --sandbox for the full check (default: require)")
    ap.add_argument("--summary", metavar="FILE", help="append the result (Markdown) to FILE")
    ap.add_argument("--repo", default=SVGOLF, help=argparse.SUPPRESS)          # svGolf's directory (tests)
    ap.add_argument("--tasks-dir", default=None, help=argparse.SUPPRESS)
    ap.add_argument("--check-py", default=None, help=argparse.SUPPRESS)
    args = ap.parse_args(argv)
    repo = os.path.abspath(args.repo)
    data_dir = os.path.join(repo, "leaderboard", "data")
    tasks_dir = args.tasks_dir or os.path.join(repo, "tasks")
    try:
        head = resolve(repo, args.head, "--head")
        if head != git(repo, "rev-parse", "HEAD").strip():
            print(f"error: --head {args.head} is not the commit checked out: check it out first", file=sys.stderr)
            return 2
        base = resolve(repo, args.base, "--base")
        added, problems = classify(changes(repo, base, head))
    except GitError as e:
        print(f"error: {e}", file=sys.stderr)
        return 2
    problems += handle_problems(added, data_dir)
    lines = {}
    for task_name, h in sorted(added):
        if not os.path.isfile(os.path.join(tasks_dir, task_name, "task.json")):
            lines[(task_name, h)] = f"`{task_name}` record `{h[:12]}`: no board line: no such task"
            problems.append(f"record `{task_name}/{h[:12]}`: `{task_name}` is not a task of this repository (it has "
                            f"no `tasks/{task_name}/task.json`)")
            continue
        try:
            task = lb.load_task(tasks_dir, task_name)
            board, par = lb.board_now(task, data_dir, tasks_dir)
            lines[(task_name, h)] = lb.board_line(board, par, h)
        except (OSError, ValueError) as e:
            lines[(task_name, h)] = f"`{task_name}` record `{h[:12]}`: no board line: {e}"
            problems.append(f"record `{task_name}/{h[:12]}`: {e}")
    offline = run_leaderboard(["verify", "--offline"], data_dir=data_dir, tasks_dir=tasks_dir,
                              writeups_dir=os.path.join(args.repo, "leaderboard", "writeups"))
    full = None
    if added and not problems:
        with tempfile.TemporaryDirectory(prefix="svgolf-pr-") as tmp:      # the added records alone
            for task_name, h in sorted(added):
                os.makedirs(os.path.join(tmp, task_name), exist_ok=True)
                for ext in RECORD_EXTS:
                    shutil.copy2(os.path.join(data_dir, task_name, f"{h}.{ext}"), os.path.join(tmp, task_name))
            full = run_leaderboard(["verify", "--full", "--sandbox", args.sandbox], data_dir=tmp,
                                   tasks_dir=tasks_dir, check_py=args.check_py)
    text, passed = report(added=added, problems=problems, lines=lines, offline=offline, full=full,
                          sandbox=args.sandbox, note=flow_note(lb.current_flows(), lb.pinned_flows()))
    print(text)
    if args.summary:
        with open(args.summary, "a", encoding="utf-8") as fh:
            fh.write(text + "\n")
    return 0 if passed else 1


if __name__ == "__main__":
    sys.exit(main())
