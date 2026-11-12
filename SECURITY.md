# Security

`check.py` runs other people's files: it compiles and elaborates a submitted `Solution.lean`, and Yosys,
Verilator and a compiled model read the submitted `.sv`. The operating system's sandbox contains them
(README.md, "Sandbox", which also lists what the sandbox does not do). Two kinds of finding are security
reports:

- **a sandbox escape**: a submission that, while `check.py` checks it inside the sandbox, reads or writes a file
  outside what the sandbox allows, opens a network connection, starts another program, or reads the checker's
  environment (for example the salt `SVGOLF_POSTSYNTH_SALT`);
- **a checker bypass**: a design and a proof that `check.py` accepts although they should be refused: the proof
  does not prove the task's statement, it uses what the rules forbid (README.md, "Rules"), or the netlist that is
  scored is not the design the proof is about.

## How to report

Not in a public issue or pull request, please: until it is fixed, a bypass could be used to rank.

- If this repository's Security tab offers "Report a vulnerability" (GitHub's private vulnerability reporting),
  use it.
- If it does not, open an issue that says only that you have a security report, with no details. The maintainers
  will answer there with a private way to send it.

A report helps most with the task, the two files (the `.sv` and the `.lean`), the command, its output, the
platform and what `check.py` printed about the sandbox (`sandbox: ...`).

## What is not a security report

- What README.md's "Sandbox" already lists under "What the sandbox does not do", and any run with
  `--sandbox off`, which has no sandbox.
- A design the loader refuses, a wrong or unclear message, a crash, or a statement you find too strong or too
  weak with no accepted design that exploits it: open an issue (the templates ask for what helps).

The checker, the scorer, the leaderboard tools and the workflows of this repository are covered, on its main
branch. The SystemVerilog semantics, the loader and the tactics come from
[Proglib](https://github.com/thomasnormal/proglib); a flaw in them that lets a design pass svGolf's check is
reported here as well.
