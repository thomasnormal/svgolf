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
     par's handle, whose records are par: decided 2026-11-12); or a record's WRITEUP (decided 2026-11-13; HTML since
     2026-11-16: the file leaderboard/writeups/<record_hash>.html, outside the record), added or improved as a plain
     file: data the site renders from its allowlist sanitizer's tree, never code the check runs, and checked by step
     2 (`verify --offline` checks every writeup: it names a record, its title, its size, its characters, no internal
     marker, HTML the sanitizer accepts, each refusal naming the line and the element or attribute). A Markdown
     writeup (`.md`, the format until 2026-11-16) is refused with the advice to convert it;
  2. `leaderboard.py verify --offline` on every record (hashes and arithmetic, the added ones included);
  3. the rules for a record (decided 2026-11-25; leaderboard.py `record_rule_problems`, CONTRIBUTING.md, "The rules
     for a record") on each added record, against the board the pull request goes to (the base's records of its task,
     submitted no later than it, and the task's reference designs): (a) its writeup comes with it, and is more than
     the template; (b) no score number in its notes or its design's comments, and every score number of a writeup the
     pull request adds or changes is a measurement the tree holds; (c) a design or proof built on a board record or a
     reference design names it; (d) a licence notice of what the design is built on is kept; (e) the header comment
     is the design's own;
  4. `leaderboard.py verify --full` on the added records alone: check.py runs again on each pair, the whole check,
     with `--sandbox` as given (not run when step 1 failed: the pull request would bring the checker it runs).

It prints the result in Markdown, short first (what to fix, then one line per check saying what was compared: whether
the full check compared each record's scores, and the tool versions it ran with), then each added record with its
board line (`leaderboard.py` `board_line`: the board as the site shows it, under the rating build's pinned flow) and
the outputs; with `--summary FILE` it appends it to FILE (a GitHub workflow's job summary). The check is advisory: it
runs the pull request's own files, this one included; the maintainers then make the record again on the rating machine
and publish it (RATING_NOTE).

`--set-aside DIR` is the unit workflow's (decided 2026-11-25): on a pull request that only adds records (and their
writeups), it moves the added records' files and their writeups to DIR, paths kept, so that the tree's tests run on the
board the pull request goes to (the derived tables, the ASAP7 view, the routed course, the other sizes and the
schematics, are made by the maintainers when they make a record, so a records-only pull request cannot carry them);
on any other pull request it moves nothing. It writes what it did to the summary and exits 0 either way.

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
WRITEUP_FILE_RE = re.compile(r"leaderboard/writeups/([0-9a-f]{64})\.html")
WRITEUP_MD_RE = re.compile(r"leaderboard/writeups/([0-9a-f]{64})\.md")      # the old format (until 2026-11-16)
STATUS_WORDS = {"A": "added", "M": "changed", "D": "deleted", "T": "changed in type"}
RATING_NOTE = ("Once the checks pass, the maintainers make the record again on the rating machine, under its "
               "handle and with its files and writeup, publish it, and merge or close the pull request with a link to it (CONTRIBUTING.md, "
               "\"How a record reaches the board\").")
RULES_DOC = "CONTRIBUTING.md, \"The rules for a record\""
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
        elif WRITEUP_MD_RE.fullmatch(path) and status in ("A", "M"):
            problems.append(f"`{path}` is {STATUS_WORDS.get(status, status)}: writeups are HTML since 2026-11-16, so "
                            "name it `<record_hash>.html` and write it in HTML (README.md, \"Writeups\")")
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


def changed_writeups(changed):
    """The record hashes of the writeups `changes`' list adds or changes as plain files: whose score numbers the rules
    compare (step 3). Pure."""
    out = []
    for status, path, mode in changed:
        m = WRITEUP_FILE_RE.fullmatch(path)
        if m and status in ("A", "M") and mode == FILE_MODE:
            out.append(m.group(1))
    return sorted(set(out))


def rule_problems(added, writeups, *, data_dir, tasks_dir, writeups_dir):
    """Step 3: the rules for a record (lb.record_rule_problems) of each added record, against the base's records of its
    task submitted no later than it and the task's reference designs, and the score numbers of every writeup the pull
    request adds or changes (`writeups`: record hashes). [problem], each naming its record."""
    out = []
    meas = lb.tree_measurements([data_dir])
    done = set()
    added_hashes = {h for _, h in added}
    for task_name, h in sorted(added):
        jpath, spath, lpath = lb.record_paths(data_dir, task_name, h)
        try:
            task = lb.load_task(tasks_dir, task_name)
            with open(jpath, encoding="utf-8") as fh:
                rec = json.load(fh)
            with open(spath, encoding="utf-8", errors="replace") as fh:
                sv = fh.read()
            with open(lpath, encoding="utf-8", errors="replace") as fh:
                lean = fh.read()
            if not isinstance(rec, dict) or rec.get("record_hash") != h:
                continue                                  # verify --offline says what is wrong with it
            cands = lb.rule_candidates(task, tasks_dir, [data_dir], exclude=added_hashes,
                                       before=str(rec.get("submitted_at", "")))
            probs = lb.record_rule_problems(rec, sv, lean, cands, writeups_dir=writeups_dir, measurements=meas)
        except (OSError, ValueError, KeyError, TypeError):
            continue                                      # steps 1 and 2 report a record that cannot be read
        done.add(h)
        out += [f"record `{task_name}/{h[:12]}`: {p}" for p in probs]
    for h in writeups:
        if h in done:
            continue                                      # an added record's writeup: compared above
        path = os.path.join(writeups_dir, f"{h}.html")
        try:
            with open(path, encoding="utf-8", errors="replace") as fh:
                text = fh.read()
        except OSError:
            continue
        out += [f"writeup `{h[:12]}`: {p}" for p in lb.writeup_number_problems(text, meas)]
    return out


def flow_note(flows_now, pinned):
    """Whether this machine's Yosys is the rating build's (`lb.current_flows()` against `lb.pinned_flows()`), in one
    sentence. Pure."""
    now = (flows_now.get(lb.COMB_FLOW) or {}).get("yosys")
    pin = (pinned.get(lb.COMB_FLOW) or {}).get("yosys")
    if now == pin:
        return f"This machine's Yosys is the rating build's ({pin})."
    return (f"This machine's Yosys ({now or 'none found'}) is not the rating build's ({pin}), so the full check "
            "compared no score: `verify` calls a record checked under another Yosys stale, which is not a failure.")


def compared_lines(added, stale, machine_ok, full):
    """What the full check compared, one line per added record (pure): `stale` {(task, hash): [why its scores are
    not comparable]} (`verify_one`'s, offline), `machine_ok` whether this machine's Yosys is the rating build's,
    `full` the full check's (exit status, output) or None."""
    out = []
    for task_name, h in sorted(added):
        who = f"record `{task_name}/{h[:12]}`"
        why = stale.get((task_name, h)) or []
        if full is None:
            out.append(f"{who}: no score compared (the full check did not run)")
        elif not machine_ok:
            out.append(f"{who}: no score compared (this machine's Yosys is not the rating build's)")
        elif why:
            out.append(f"{who}: no score compared ({'; '.join(why)})")
        else:
            out.append(f"{who}: its scores compared with the record's own, column by column")
    return out


def tool_versions(flows_now, svgolf=SVGOLF):
    """The tools the check ran with, in one line (the rating build's Yosys through its launcher, which checks the
    module's sha256 and the package versions before it prints a version line; Verilator; the Lean toolchain)."""
    yosys = (flows_now.get(lb.COMB_FLOW) or {}).get("yosys") or "none (the launcher refused, or it is missing)"
    try:
        ver = subprocess.run(["verilator", "--version"], capture_output=True, text=True).stdout.strip() or "none found"
    except OSError:
        ver = "none found"
    try:
        with open(os.path.join(svgolf, "lean-toolchain"), encoding="utf-8") as fh:
            lean = fh.read().strip()
    except OSError:
        lean = "none found"
    return f"Yosys `{yosys}`; Verilator `{ver}`; Lean `{lean}`; Python `{sys.version.split()[0]}`"


def report(*, added, problems, lines, offline, full, sandbox, note, rules=None, compared=None, tools=None,
           writeups=()):
    """The Markdown text of the check, short first: the verdict and the board lines, what to fix, what was compared
    (one line per check), then the outputs. `lines`: {(task, hash): board line}; `offline`, `full`: (exit status,
    output) of the two verify runs, or None when it did not run; `rules`: step 3's problems (None: not run);
    `compared`: `compared_lines`; `tools`: `tool_versions`. Pure."""
    ran_rules, rules = rules is not None, rules or []
    passed = (not problems and not rules and offline is not None and offline[0] == 0
              and (full is None or full[0] == 0))
    n = len(added)
    out = ["## The records this pull request adds", ""]
    out.append(("Every check passed. " if passed else "**A check failed.** ")
               + (f"It adds {n} record{'s' if n != 1 else ''}." if n else "It adds no record."))
    out.append("")
    out += [f"- {lines[k]}" for k in sorted(lines)]
    if lines:
        out.append("")
    fix = list(problems) + list(rules)
    if offline is not None and offline[0] != 0:
        fix.append("`verify --offline` failed: its output is below")
    if full is not None and full[0] != 0:
        fix.append("the full check (`verify --full`) failed: its output is below")
    if fix:
        out += ["### What to fix", ""] + [f"- {p}" for p in fix] + [""]

    def state(res):
        return "not run" if res is None else ("ok" if res[0] == 0 else "FAILED")
    out += ["### What was compared", "",
            "- the files: " + ("only records and writeups" if not problems else "more than records and writeups, or "
                               "a record that cannot be one (above)")
            + f" ({n} record{'s' if n != 1 else ''}, {len(writeups)} writeup{'s' if len(writeups) != 1 else ''})",
            f"- every record, offline (`verify --offline`: hashes, arithmetic, every writeup's form): {state(offline)}",
            f"- the rules for a record ({RULES_DOC}: the writeup, score numbers, credits, licence notices, header "
            "comments): " + ("not run" if not ran_rules else
                             ("ok" if not rules else f"{len(rules)} problem{'s' if len(rules) != 1 else ''}")),
            f"- the full check of the records it adds (`verify --full --sandbox {sandbox}`): {state(full)}"]
    out += [f"- {c}" for c in (compared or [])]
    if tools:
        out.append(f"- tools: {tools}")
    out += ["", RATING_NOTE + " " + note, ""]

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
    return "\n".join(out), passed


def set_aside(repo, added, problems, dest):
    """`--set-aside DEST`: on a pull request that only adds records, move the added records' files and their writeups to
    DEST (the paths under svGolf's directory kept) and return the Markdown that says so; on any other, move nothing and
    say why. Never removes anything it did not move."""
    if problems or not added:
        why = ("it adds no record" if not problems else "it changes more than records and writeups")
        return (f"## The unit tests on this pull request\n\nNothing was set aside: {why}, so the tests run on the "
                "whole tree.\n")
    moved = []
    for task_name, h in sorted(added):
        rels = [f"leaderboard/data/{task_name}/{h}.{ext}" for ext in RECORD_EXTS] + [f"leaderboard/writeups/{h}.html"]
        for rel in rels:
            src = os.path.join(repo, rel)
            if not os.path.isfile(src) or os.path.islink(src):
                continue
            dst = os.path.join(dest, rel)
            os.makedirs(os.path.dirname(dst), exist_ok=True)
            shutil.move(src, dst)
            moved.append(rel)
    n = len(added)
    return ("## The unit tests on this pull request\n\n"
            f"It only adds records ({n}) and their writeups, so they were set aside ({len(moved)} files) and the tests "
            "below run on the board the pull request goes to. A record's derived tables (the ASAP7 view, the routed "
            "course, the other sizes, the schematics) are made by the maintainers when they make the record, so a "
            "pull request of records does not carry them, and the tests that compare them with the records are not "
            "this pull request's to pass. The records themselves are checked by the `records` workflow "
            "(leaderboard/pr_check.py).\n")


def main(argv=None):
    ap = argparse.ArgumentParser(description="The check of a pull request that adds records.")
    ap.add_argument("--base", default="HEAD^1", help="the branch the pull request goes to (default: HEAD^1, the merge "
                    "commit's first parent)")
    ap.add_argument("--head", default="HEAD", help="the pull request, the commit checked out (default: HEAD)")
    ap.add_argument("--sandbox", choices=("off", "auto", "require"), default=lb.OFFICIAL_SANDBOX_MODE,
                    help="check.py's --sandbox for the full check (default: require)")
    ap.add_argument("--summary", metavar="FILE", help="append the result (Markdown) to FILE")
    ap.add_argument("--set-aside", metavar="DIR", help="the unit workflow's: on a pull request that only adds records, "
                    "move them and their writeups to DIR so that the tree's tests run without them; check nothing")
    ap.add_argument("--repo", default=SVGOLF, help=argparse.SUPPRESS)          # svGolf's directory (tests)
    ap.add_argument("--tasks-dir", default=None, help=argparse.SUPPRESS)
    ap.add_argument("--check-py", default=None, help=argparse.SUPPRESS)
    args = ap.parse_args(argv)
    repo = os.path.abspath(args.repo)
    data_dir = os.path.join(repo, "leaderboard", "data")
    writeups_dir = os.path.join(repo, "leaderboard", "writeups")
    tasks_dir = args.tasks_dir or os.path.join(repo, "tasks")
    try:
        head = resolve(repo, args.head, "--head")
        if head != git(repo, "rev-parse", "HEAD").strip():
            print(f"error: --head {args.head} is not the commit checked out: check it out first", file=sys.stderr)
            return 2
        base = resolve(repo, args.base, "--base")
        changed = changes(repo, base, head)
        added, problems = classify(changed)
    except GitError as e:
        print(f"error: {e}", file=sys.stderr)
        return 2
    if args.set_aside:
        text = set_aside(repo, added, problems, os.path.abspath(args.set_aside))
        print(text)
        if args.summary:
            with open(args.summary, "a", encoding="utf-8") as fh:
                fh.write(text + "\n")
        return 0
    problems += handle_problems(added, data_dir)
    writeups = changed_writeups(changed)
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
                              writeups_dir=writeups_dir)
    rules = rule_problems(added, writeups, data_dir=data_dir, tasks_dir=tasks_dir, writeups_dir=writeups_dir) \
        if (added or writeups) and not problems else None
    full = None
    stale = {}
    if added and not problems:
        with tempfile.TemporaryDirectory(prefix="svgolf-pr-") as tmp:      # the added records alone
            for task_name, h in sorted(added):
                os.makedirs(os.path.join(tmp, task_name), exist_ok=True)
                for ext in RECORD_EXTS:
                    shutil.copy2(os.path.join(data_dir, task_name, f"{h}.{ext}"), os.path.join(tmp, task_name))
            full = run_leaderboard(["verify", "--full", "--sandbox", args.sandbox], data_dir=tmp,
                                   tasks_dir=tasks_dir, check_py=args.check_py)
        stale = stale_reasons(added, data_dir, tasks_dir)
    flows_now, pinned = lb.current_flows(), lb.pinned_flows()
    machine_ok = (flows_now.get(lb.COMB_FLOW) or {}).get("yosys") == (pinned.get(lb.COMB_FLOW) or {}).get("yosys")
    text, passed = report(added=added, problems=problems, lines=lines, offline=offline, full=full,
                          sandbox=args.sandbox, note=flow_note(flows_now, pinned), rules=rules,
                          compared=compared_lines(added, stale, machine_ok, full), tools=tool_versions(flows_now),
                          writeups=writeups)
    print(text)
    if args.summary:
        with open(args.summary, "a", encoding="utf-8") as fh:
            fh.write(text + "\n")
    return 0 if passed else 1


def stale_reasons(added, data_dir, tasks_dir):
    """{(task, hash): [why its scores are not comparable with the rating build's]} of the added records (verify's
    offline level, in this process: the flow, the scoring point, the statement, the sky130 identity)."""
    out = {}
    vargs = argparse.Namespace(offline=True, full=False, tasks_dir=tasks_dir, asap7_dir=lb.ASAP7_DIR,
                               score_py=lb.SCORE_PY, ppa_py=lb.PPA_PY, check_py=lb.CHECK_PY, lean_wrap=None,
                               sandbox=lb.OFFICIAL_SANDBOX_MODE)
    try:
        ctx = lb.verify_context()
    except (OSError, ValueError):
        return out
    for task_name, h in sorted(added):
        path = lb.record_paths(data_dir, task_name, h)[0]
        try:
            with open(path, encoding="utf-8") as fh:
                rec = json.load(fh)
            why = list(lb.verify_one(vargs, path, rec, ctx).stale)
            pb = rec.get(lb.PPA_KEY)
            if not (isinstance(pb, dict) and pb.get("available") is True):
                why.append("it carries no sky130 columns")
            out[(task_name, h)] = why
        except (OSError, ValueError, KeyError, TypeError, AttributeError):
            out[(task_name, h)] = ["it could not be read"]
    return out


if __name__ == "__main__":
    sys.exit(main())
