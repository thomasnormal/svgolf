# Real-world SystemVerilog survey (2026-11-01)

Requested 2026-11-01: look at how people write clmul, chacha_qr and the other circuit families in real SystemVerilog on GitHub and elsewhere, so that we support the constructs people commonly use.

* `SURVEY.md`: the report (method, headline numbers, measured facts, the ranked gap list, stale rows, per-topic styles, limits). Written by a synthesis agent over eight topic surveys (332 implementations, about 300 distinct files); its paths into the session scratchpad are provenance only.
* `top_gaps.json`, `construct_table.json` (77 constructs: count, topics, ls-sv status with register rows, tactic status, scorer status, priority), `per_topic.json`.
* `probes/` (241 reduced `.sv` probes, one per idiom, shaped as clmul / chacha-QR / S-box / adder tasks) and `probe_results.json` (177 `check.py --unproved --tactics` results: the stage that stopped each probe and its first message). `run_probe.py`, `probe_task.sh`, `summ2.py` and `realrun.py` are the drivers the synthesis agent used (they read scratchpad paths; adapt before reuse).
* The raw per-implementation data (URLs, licences, constructs) is not committed; the third-party code was never copied into the repository.
* Counts are lower bounds per file (a surveyor lists what it noticed); statuses are measured on `svgolf-prep` at the time (see the report's header), and the tactics' answer is `sv_structure?`, not a proof.
