<!--
A record: `python3.12 leaderboard/leaderboard.py submit --task TASK --record HASH` opens this pull request
and fills in the three parts below (`--dry-run` prints them first). By hand: add the record's three files
under leaderboard/data/<task>/, as `leaderboard.py add` wrote them, and its writeup, and nothing else. The
check on the pull request verifies every record, checks the rules for a record (CONTRIBUTING.md, "The rules
for a record": the writeup, no score numbers in the notes or the design's comments, the record or reference
design it was built on named, its licence notice kept, a header comment of its own) and runs the full check
on the added ones; the maintainers then make the record again on the rating machine, under your handle and
with your files and writeup, publish it, and merge or close the pull request with a link to it.

Any other change: replace this text with what the change is and why (CONTRIBUTING.md).
-->

## Record

- task:
- handle:
- assisted by:
- files: `leaderboard/data/<task>/<hash>.json`, `.sv` and `.lean`, and the writeup `leaderboard/writeups/<hash>.html`
  (required: copy `leaderboard/writeups/TEMPLATE.html`; README.md, "Writeups")

## Board line

<!-- what `leaderboard.py submit --dry-run` prints after "board line:" -->

## Checks

<!-- the output of `python3.12 leaderboard/leaderboard.py verify --offline --task <task>` for the record -->
