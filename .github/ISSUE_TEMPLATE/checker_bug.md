---
name: Checker bug
about: check.py, score/ppa.py or leaderboard.py crashes, stops with an infrastructure error, or prints a wrong number or a misleading message
title: ""
---

<!-- A design and proof that check.py accepts although they should be refused is a security report: SECURITY.md,
     not an issue. A design the loader refuses has its own template. -->

**What happened**

The command, and what it printed (the JSON result's `stage` and `errors`, or the last lines of stderr):

```
```

**What you expected**

**The files**

The task, and the `.sv` and `.lean` (attached, or a link), if you can share them.

**The machine**

- svGolf revision (`git rev-parse --short HEAD`):
- OS and version:
- `python3.12 --version`, `yosys -V`, `verilator --version`:
- the result's `sandbox` (`mode`, `mechanism`, `active`):
