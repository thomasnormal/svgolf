Fixtures of tests/pnr/test_pnr_tools.py: stored outputs of the routed course's runs of 2026-11-13 (the third
campaign), copied byte for byte unless said otherwise. Nothing here is synthetic; what the tests write themselves is
said in the tests.

example_job/            a job directory (score/pnr/pnr.py's layout) holding the job _example_38596d52847c__min_s1: the
                        scoring run of _example's design band_lp (record 92452078..., design file a5784d61...)
  designs/*.v           the placed netlist (the ASAP7 view's repaired netlist, sha256 38596d52...)
  sdc/*.sdc, cfg/*.mk   the job's SDC and config.mk as the campaign wrote them
  rows/*.json           the row the campaign's collector made of the finished job (its ORFS work tree stayed on the
                        course host), with ONE field removed: `host`, the course host's name (the tree's collector
                        never records it)
  logs/*.host.json      the host block the committed entry records for the run (CPU model, OS, kernel, runtime)
  logs/*.render.out     the picture job's log (layout.tcl's die and core boxes)
  img/*.png             OpenROAD's off-screen render of the run's 6_final.odb (1600 x 1600)
add_rerun/              the files fetched back of the same campaign's re-run of add's par design (netlist 3f31f3f2...,
                        reproduced byte for byte against the 2026-11-11 run the committed entry records)
  run/results/...       1_2_yosys.v and 6_final.v
  run/logs/...          the flow's equivalence log 6_final_lec_check.log
  logs/status.txt       the job's status line, its host field replaced by the run's date (the tree runner's format)
lec/                    the negative control's equivalence jobs (kepler-formal in the pinned image, 2026-11-13): add and
                        sorter, the unchanged ("positive") and the one-gate-changed ("perturbed") routed netlist, each
                        against reference A (the flow's 1_synth_lec.v of the unchanged run) and B (the netlist file the
                        course binds)
  logs/                 the eight kepler-formal logs (4 IDENTICAL, 4 DIFFERENT)
  cfg/                  the eight configurations they ran
  flow/<nick>.yml       each run's own configuration, as the flow wrote it (objects/asap7/<nick>/min_s1/6_final_lec_test.yml)
