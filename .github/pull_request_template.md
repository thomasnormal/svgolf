<!--
A record: `python3.12 leaderboard/leaderboard.py submit --task TASK --record HASH` opens this pull request
and fills in the three parts below (`--dry-run` prints them first). By hand: add the record's three files
under leaderboard/data/<task>/, as `leaderboard.py add` wrote them, and nothing else. The check on the pull
request verifies every record and runs the full check on the added ones; a maintainer re-makes the ranked
number on the rating build when the pull request is merged.

Any other change: replace this text with what the change is and why (CONTRIBUTING.md).
-->

## Record

- task:
- handle:
- assisted by:
- files: `leaderboard/data/<task>/<hash>.json`, `.sv` and `.lean`, and the writeup `leaderboard/writeups/<hash>.md`
  (encouraged, not required: copy `leaderboard/writeups/TEMPLATE.md`; README.md, "Writeups")

## Board line

<!-- what `leaderboard.py submit --dry-run` prints after "board line:" -->

## Checks

<!-- the output of `python3.12 leaderboard/leaderboard.py verify --offline --task <task>` for the record -->
