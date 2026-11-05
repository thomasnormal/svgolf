# Real floating-point dividers (hunt of 2026-11-02)

Requested 2026-11-02: "Did you find some various fpdiv circuits on the internet that we can also prove are correct? Some of them may only cover certain (W,P) pairs, but if our proof interface is general, we can still prove them."

* `FDIV-HUNT.md`: the report (method, measured versus read, the table of nine circuits, what could be proved through the (W,P) interface, baselines and proof targets, constructs versus the tactic fragment, ordered recommendations, caveats).
* `table.json`, `evals.json` (the ten evaluations, structured), `searched.json` (the five searches), `recommendations.json`.
* `fdiv_oracle.py`: an independent exact-rational oracle for ANY (W,P) (checked against the repository's binary16 oracle on 200000 pairs and against CPython/float32 division on 52848 binary32 pairs).
* Third-party code and the evaluators' rewrites (unrolled FSMs, wrappers, flattened files) were written only under the session scratchpad and are NOT in the repository: licences were read from repository metadata only and not legally reviewed (DGrid and TEA state none, fontamsoc is GPL-2.0-only, drewbabel and fudian use licences that need review). Every area figure in the report is for an evaluator rewrite, not for the authors' code.
* Nobody ran Lean for this hunt; every "provable" statement is a judgement from the extractor, Yosys and the tactic fragment's shape.
