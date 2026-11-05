Results of WP-H3 gate 0 (2026-11-02). D1 = fdivp.sv, D2 = fdivp2.sv. One JSON line per format for the exhaustive files
({"W","P","K","pairs","mismatches","mode"}); the vec_* files are the transcripts of run_vec.py (sampled, 200,000
vectors per format: python model vs oracle_int vs Fraction oracle, then Verilator vs oracle_int).
exh_K4-12_D1.txt, exh_K13-14_D1.txt   D1, every pair of every format with K = W + P <= 14 (66 formats)
exh_K4-12_D2.txt, exh_K13-14_D2.txt   D2, same
exh_2e32_D1.txt, exh_2e32_D2.txt      (5,11) and (8,8), every one of the 2^32 pairs, both designs
scores.txt                            score/score.py area (GE) / depth / gates
vec_D1.txt, vec_D2.txt                sampled runs (D1: 14 formats; D2: 7 formats); (24,8) and (28,4) were not run: the Python
                                      exact oracle needs shifts of 2^23 bits at W = 24 (gap G10 of H3-NOTE.md); the remaining
                                      queued formats ((7,9) etc. for D1, (2,62) etc. for D2) were stopped unfinished at
                                      load average 100+ and are not counted
model_vs_oracles_K4-10.txt            val_py.py: model vs oracle_int on every pair, K <= 10; oracle_int vs Fraction on K <= 8
cpp_vs_oracle_int_K4-9.txt            cmp_oracle_cpp.py: C++ oracle vs oracle_int (all pairs K <= 7, stride-7 divisors K = 8, 9)
