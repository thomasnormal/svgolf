
### add, N = 16
| design | GE (score) | depth (ltp) | gates | lib GE | depth, INV-expanded | LE delay (tau) | NLDM delay (ns) |
|---|--:|--:|--:|--:|--:|--:|--:|
| add_cmpcarry | 196.0 | 17 | 149 | 197.7 | 17 | 95.0 | 0.434 |
| add_kogge | 149.7 | 24 | 115 | 150.3 | 24 | 136.0 | 0.534 |
| add_ripple | 112.0 | 33 | 80 | 112.0 | 33 | 178.7 | 0.676 |
| add_sklansky | 127.7 | 28 | 95 | 127.7 | 28 | 157.3 | 0.636 |
| add_yosys | 118.0 | 33 | 86 | 118.0 | 33 | 194.7 | 0.760 |

Energy per operation (fJ), uniform random inputs, Nangate45 typical 1.1 V:

| design | toggles/op | E_sw | E_int | E_dyn (zero-delay) | E_dyn (glitch-aware) | glitch x | E_leak |
|---|--:|--:|--:|--:|--:|--:|--:|
| add_cmpcarry | 60.0 | 144.4 | 128.7 | 273.1 | 327.5 | 1.19 | 1.56 |
| add_kogge | 51.5 | 132.0 | 107.8 | 239.8 | 274.6 | 1.14 | 1.44 |
| add_ripple | 36.0 | 123.5 | 76.0 | 199.6 | 233.9 | 1.17 | 1.35 |
| add_sklansky | 42.6 | 122.4 | 90.6 | 213.0 | 254.1 | 1.19 | 1.46 |
| add_yosys | 38.9 | 119.2 | 84.1 | 203.3 | 246.4 | 1.21 | 1.60 |

Combined figures (area in lib GE, T = NLDM ns, E = glitch-aware dynamic + leakage, fJ):

| design | AT | AT^2 | EDP (fJ.ns) | EDP zero-delay E | ED^2P | ops per pJ | power at 1/T (mW) |
|---|--:|--:|--:|--:|--:|--:|--:|
| add_cmpcarry | 85.9 | 37.3 | 143.0 | 119.3 | 62.1 | 3.039 | 0.757 |
| add_kogge | 80.3 | 42.9 | 147.4 | 128.8 | 78.7 | 3.623 | 0.517 |
| add_ripple | 75.7 | 51.2 | 159.0 | 135.8 | 107.5 | 4.252 | 0.348 |
| add_sklansky | 81.2 | 51.7 | 162.6 | 136.4 | 103.5 | 3.914 | 0.402 |
| add_yosys | 89.7 | 68.2 | 188.6 | 155.8 | 143.4 | 4.032 | 0.326 |

Ranks (1 = best; ties share a rank):

| design | GE | depth | LE | NLDM | AT(GE x depth) | AT(NLDM) | E zero-delay | E glitch-aware | EDP (zero-delay E) | EDP (glitch E) |
|---|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|
| add_cmpcarry | 5 | 1 | 1 | 1 | 1 | 4 | 5 | 5 | 1 | 1 |
| add_kogge | 4 | 2 | 2 | 2 | 3 | 2 | 4 | 4 | 2 | 2 |
| add_ripple | 1 | 4 | 4 | 4 | 4 | 1 | 1 | 1 | 3 | 3 |
| add_sklansky | 3 | 3 | 3 | 3 | 2 | 3 | 3 | 3 | 4 | 4 |
| add_yosys | 2 | 4 | 5 | 5 | 5 | 5 | 2 | 2 | 5 | 5 |

Kendall tau against the present score components:

| metric | tau vs GE | tau vs depth |
|---|--:|--:|
| GE | +1.00 | -1.00 |
| depth | -1.00 | +1.00 |
| LE | -0.80 | +1.00 |
| NLDM | -0.80 | +1.00 |
| AT(GE x depth) | -0.60 | +0.78 |
| AT(NLDM) | +0.20 | -0.11 |
| E zero-delay | +1.00 | -1.00 |
| E glitch-aware | +1.00 | -1.00 |
| EDP (zero-delay E) | -0.60 | +0.78 |
| EDP (glitch E) | -0.60 | +0.78 |

Pareto frontiers (non-dominated designs):

* (GE, depth) = present: add_cmpcarry, add_kogge, add_ripple, add_sklansky
* (GE, LE delay): add_cmpcarry, add_kogge, add_ripple, add_sklansky
* (lib GE, NLDM delay): add_cmpcarry, add_kogge, add_ripple, add_sklansky
* (GE, depth, E zero-delay): add_cmpcarry, add_kogge, add_ripple, add_sklansky
* (lib GE, NLDM delay, E glitch-aware): add_cmpcarry, add_kogge, add_ripple, add_sklansky
* (E glitch-aware, NLDM delay): add_cmpcarry, add_kogge, add_ripple, add_sklansky

Same, without the banned-operator baseline (`*_yosys`):

* (GE, depth): add_cmpcarry, add_kogge, add_ripple, add_sklansky
* (lib GE, NLDM delay): add_cmpcarry, add_kogge, add_ripple, add_sklansky
* (lib GE, NLDM delay, E glitch-aware): add_cmpcarry, add_kogge, add_ripple, add_sklansky
* (E glitch-aware, NLDM delay): add_cmpcarry, add_kogge, add_ripple, add_sklansky

### mul, N = 16
| design | GE (score) | depth (ltp) | gates | lib GE | depth, INV-expanded | LE delay (tau) | NLDM delay (ns) |
|---|--:|--:|--:|--:|--:|--:|--:|
| mul_array | 1962.6 | 88 | 1408 | 1963.0 | 88 | 593.0 | 2.981 |
| mul_dadda_ks | 2076.5 | 48 | 1483 | 2100.3 | 48 | 286.0 | 1.326 |
| mul_dadda_rc | 1953.6 | 61 | 1408 | 1958.0 | 61 | 352.0 | 1.446 |
| mul_tree | 2034.9 | 63 | 1456 | 2035.7 | 63 | 370.7 | 1.652 |
| mul_tree_h | 2025.9 | 62 | 1450 | 2026.3 | 62 | 361.3 | 1.616 |
| mul_wallace | 2113.9 | 62 | 1502 | 2117.0 | 62 | 369.3 | 1.611 |
| mul_yosys | 2081.2 | 59 | 1486 | 2083.7 | 61 | 366.0 | 1.642 |

Energy per operation (fJ), uniform random inputs, Nangate45 typical 1.1 V:

| design | toggles/op | E_sw | E_int | E_dyn (zero-delay) | E_dyn (glitch-aware) | glitch x | E_leak |
|---|--:|--:|--:|--:|--:|--:|--:|
| mul_array | 483.7 | 1210.2 | 1161.9 | 2372.2 | 12415.9 | 5.23 | 105.17 |
| mul_dadda_ks | 527.4 | 1226.8 | 1220.9 | 2447.7 | 4532.4 | 1.85 | 50.66 |
| mul_dadda_rc | 477.8 | 1205.1 | 1118.3 | 2323.4 | 4058.8 | 1.75 | 50.83 |
| mul_tree | 494.0 | 1237.4 | 1190.6 | 2428.0 | 4879.1 | 2.01 | 60.50 |
| mul_tree_h | 492.5 | 1234.2 | 1187.4 | 2421.6 | 4860.9 | 2.00 | 58.89 |
| mul_wallace | 502.0 | 1253.0 | 1222.2 | 2475.3 | 4631.2 | 1.87 | 61.43 |
| mul_yosys | 500.3 | 1239.3 | 1206.7 | 2446.0 | 4638.9 | 1.90 | 61.56 |

Combined figures (area in lib GE, T = NLDM ns, E = glitch-aware dynamic + leakage, fJ):

| design | AT | AT^2 | EDP (fJ.ns) | EDP zero-delay E | ED^2P | ops per pJ | power at 1/T (mW) |
|---|--:|--:|--:|--:|--:|--:|--:|
| mul_array | 5851.1 | 17440.4 | 37321.4 | 7384.2 | 111244.0 | 0.080 | 4.201 |
| mul_dadda_ks | 2784.8 | 3692.4 | 6076.7 | 3312.5 | 8057.0 | 0.218 | 3.457 |
| mul_dadda_rc | 2830.9 | 4092.9 | 5941.8 | 3432.7 | 8590.6 | 0.243 | 2.842 |
| mul_tree | 3362.5 | 5554.2 | 8159.3 | 4110.5 | 13477.5 | 0.202 | 2.990 |
| mul_tree_h | 3274.2 | 5290.4 | 7949.3 | 4008.0 | 12844.5 | 0.203 | 3.045 |
| mul_wallace | 3410.5 | 5494.3 | 7559.8 | 4086.6 | 12178.9 | 0.213 | 2.913 |
| mul_yosys | 3420.6 | 5615.2 | 7716.4 | 4116.4 | 12667.2 | 0.213 | 2.863 |

Ranks (1 = best; ties share a rank):

| design | GE | depth | LE | NLDM | AT(GE x depth) | AT(NLDM) | E zero-delay | E glitch-aware | EDP (zero-delay E) | EDP (glitch E) |
|---|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|
| mul_array | 2 | 7 | 7 | 7 | 7 | 7 | 2 | 7 | 7 | 7 |
| mul_dadda_ks | 5 | 1 | 1 | 1 | 1 | 1 | 6 | 2 | 1 | 2 |
| mul_dadda_rc | 1 | 3 | 2 | 2 | 2 | 2 | 1 | 1 | 2 | 1 |
| mul_tree | 4 | 6 | 6 | 6 | 5 | 4 | 4 | 6 | 5 | 6 |
| mul_tree_h | 3 | 4 | 3 | 4 | 4 | 3 | 3 | 5 | 3 | 5 |
| mul_wallace | 7 | 4 | 5 | 3 | 6 | 5 | 7 | 3 | 4 | 3 |
| mul_yosys | 6 | 2 | 4 | 5 | 3 | 6 | 5 | 4 | 6 | 4 |

Kendall tau against the present score components:

| metric | tau vs GE | tau vs depth |
|---|--:|--:|
| GE | +1.00 | -0.20 |
| depth | -0.20 | +1.00 |
| LE | +0.05 | +0.80 |
| NLDM | -0.14 | +0.70 |
| AT(GE x depth) | +0.05 | +0.80 |
| AT(NLDM) | +0.14 | +0.50 |
| E zero-delay | +0.90 | -0.30 |
| E glitch-aware | -0.14 | +0.70 |
| EDP (zero-delay E) | +0.05 | +0.60 |
| EDP (glitch E) | -0.14 | +0.70 |

Pareto frontiers (non-dominated designs):

* (GE, depth) = present: mul_dadda_ks, mul_dadda_rc
* (GE, LE delay): mul_dadda_ks, mul_dadda_rc
* (lib GE, NLDM delay): mul_dadda_ks, mul_dadda_rc
* (GE, depth, E zero-delay): mul_dadda_ks, mul_dadda_rc, mul_yosys
* (lib GE, NLDM delay, E glitch-aware): mul_dadda_ks, mul_dadda_rc
* (E glitch-aware, NLDM delay): mul_dadda_ks, mul_dadda_rc

Same, without the banned-operator baseline (`*_yosys`):

* (GE, depth): mul_dadda_ks, mul_dadda_rc
* (lib GE, NLDM delay): mul_dadda_ks, mul_dadda_rc
* (lib GE, NLDM delay, E glitch-aware): mul_dadda_ks, mul_dadda_rc
* (E glitch-aware, NLDM delay): mul_dadda_ks, mul_dadda_rc

### Proved references only (the designs that can be entries today)

* mul (GE, depth) = present: mul_array, mul_tree_h
* mul (lib GE, NLDM delay): mul_array, mul_tree_h, mul_wallace
* mul (lib GE, NLDM delay, E glitch-aware): mul_array, mul_tree_h, mul_wallace
* mul (E glitch-aware, NLDM delay): mul_wallace
* mul (E zero-delay, NLDM delay): mul_array, mul_tree_h, mul_wallace


### Sampling noise of the zero-delay energy (seeds 1, 2, 3; 2000 vector transitions each)

| design | E_dyn seed 1 | seed 2 | seed 3 | max spread |
|---|--:|--:|--:|--:|
| add_cmpcarry | 273.1 | 273.9 | 273.4 | 0.29 % |
| add_kogge | 239.8 | 240.4 | 240.3 | 0.26 % |
| add_ripple | 199.6 | 200.4 | 199.7 | 0.40 % |
| add_sklansky | 213.0 | 214.0 | 213.5 | 0.48 % |
| add_yosys | 203.3 | 204.1 | 203.5 | 0.38 % |
| mul_array | 2372.2 | 2391.7 | 2373.6 | 0.82 % |
| mul_dadda_ks | 2447.7 | 2465.3 | 2445.1 | 0.82 % |
| mul_dadda_rc | 2323.4 | 2341.0 | 2321.7 | 0.83 % |
| mul_tree | 2428.0 | 2442.6 | 2418.2 | 1.00 % |
| mul_tree_h | 2421.6 | 2436.3 | 2411.7 | 1.01 % |
| mul_wallace | 2475.3 | 2491.1 | 2470.6 | 0.83 % |
| mul_yosys | 2446.0 | 2461.1 | 2437.2 | 0.98 % |

Largest spread: 1.01 %.

### Flow A: `abc -liberty` (Nangate45) re-mapping of the same canonical RTLIL

`&nf` = ABC's default liberty script (no sizing); `fast` = `-constr` flow with `buffer; upsize; dnsize` and no delay target; `loose` = same with the loosest target of the sweep. GE = um^2 / 0.798. T = engine NLDM STA (ABC `stime` agrees within 1.3 % on average).

| design | &nf GE | &nf T (ns) | &nf E_dyn zero (fJ) | &nf E_dyn glitch (fJ) | fast GE | fast T | fast E_dyn zero | fast E_dyn glitch | loose GE | loose T |
|---|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|
| add_cmpcarry | 173.7 | 0.465 | 272 | 317 | 187.7 | 0.406 | 292 | 340 | 174.7 | 0.465 |
| add_kogge | 179.7 | 0.533 | 310 | 345 | 197.3 | 0.488 | 349 | 392 | 183.7 | 0.533 |
| add_ripple | 122.7 | 0.653 | 213 | 246 | 160.7 | 0.531 | 299 | 353 | 122.7 | 0.653 |
| add_sklansky | 129.3 | 0.617 | 231 | 262 | 153.7 | 0.524 | 288 | 326 | 129.3 | 0.617 |
| add_yosys | 125.3 | 0.646 | 217 | 251 | 153.0 | 0.552 | 280 | 326 | 125.3 | 0.646 |
| mul_array | 1904.0 | 2.756 | 2645 | 10755 | 2220.7 | 2.670 | 3228 | 12453 | 2004.0 | 2.797 |
| mul_dadda_ks | 2025.0 | 1.156 | 2500 | 4410 | 2238.7 | 1.127 | 2952 | 4997 | 2103.0 | 1.260 |
| mul_dadda_rc | 1871.7 | 1.353 | 2339 | 4285 | 2098.7 | 1.227 | 2789 | 4990 | 1939.7 | 1.433 |
| mul_tree | 1968.3 | 1.583 | 2493 | 5346 | 2197.3 | 1.381 | 2935 | 6207 | 2051.3 | 1.629 |
| mul_tree_h | 1974.7 | 1.576 | 2491 | 5259 | 2241.0 | 1.352 | 3018 | 6233 | 2058.7 | 1.620 |
| mul_wallace | 2067.7 | 1.494 | 2607 | 4944 | 2254.7 | 1.319 | 2971 | 5599 | 2140.7 | 1.544 |
| mul_yosys | 2017.0 | 1.564 | 2527 | 4839 | 2218.0 | 1.419 | 2928 | 5528 | 2092.0 | 1.602 |

ABC `stime` vs the engine's NLDM STA over 72 sized netlists: mean |difference| 1.27 %, max 5.52 %.

Flow A frontier over all designs and delay targets, add (area GE, T ns): add_ripple@D800 (123, 0.653); add_ripple@D650 (124, 0.644); add_yosys@D650 (127, 0.639); add_sklansky@D650 (129, 0.617); add_sklansky@D550 (143, 0.546); add_sklansky@D0 (154, 0.524); add_cmpcarry@Dnf (174, 0.465); add_cmpcarry@D450 (179, 0.426); add_cmpcarry@D0 (188, 0.406)

Flow A frontier over all designs and delay targets, mul (area GE, T ns): mul_dadda_rc@Dnf (1872, 1.353); mul_dadda_ks@Dnf (2025, 1.156); mul_dadda_ks@D0 (2239, 1.127)

### Three mappings of the same canonical RTLIL (area in GE-equivalents = um^2 / 0.798; T by the same NLDM STA)

| design | `abc -g` + Nangate expansion (the scored netlist): GE / T | `abc -liberty` full Nangate45 (&nf): GE / T | `abc -liberty` 9-cell subset (&nf): GE / T |
|---|--:|--:|--:|
| add_cmpcarry | 197.7 / 0.434 | 173.7 / 0.465 | 185.7 / 0.471 |
| add_kogge | 150.3 / 0.534 | 179.7 / 0.533 | 151.0 / 0.569 |
| add_ripple | 112.0 / 0.676 | 122.7 / 0.653 | 112.0 / 0.676 |
| add_sklansky | 127.7 / 0.636 | 129.3 / 0.617 | 124.7 / 0.663 |
| add_yosys | 118.0 / 0.760 | 125.3 / 0.646 | 115.3 / 0.727 |

add: Kendall tau of the delay ranking between mappings: scored-vs-full +0.80, scored-vs-subset +1.00, full-vs-subset +0.80; of the area ranking: +0.80, +1.00, +0.80.

| design | `abc -g` + Nangate expansion (the scored netlist): GE / T | `abc -liberty` full Nangate45 (&nf): GE / T | `abc -liberty` 9-cell subset (&nf): GE / T |
|---|--:|--:|--:|
| mul_array | 1963.0 / 2.981 | 1904.0 / 2.756 | 1938.7 / 3.262 |
| mul_dadda_ks | 2100.3 / 1.326 | 2025.0 / 1.156 | 2040.7 / 1.254 |
| mul_dadda_rc | 1958.0 / 1.446 | 1871.7 / 1.353 | 1995.7 / 1.677 |
| mul_tree | 2035.7 / 1.652 | 1968.3 / 1.583 | 2114.0 / 1.703 |
| mul_tree_h | 2026.3 / 1.616 | 1974.7 / 1.576 | 2103.0 / 1.633 |
| mul_wallace | 2117.0 / 1.611 | 2067.7 / 1.494 | 2166.0 / 1.797 |
| mul_yosys | 2083.7 / 1.642 | 2017.0 / 1.564 | 2143.7 / 1.613 |

mul: Kendall tau of the delay ranking between mappings: scored-vs-full +0.90, scored-vs-subset +0.43, full-vs-subset +0.52; of the area ranking: +0.90, +0.62, +0.52.


### Sensitivity to N (NLDM delay in ns, GE, ltp depth)


add:

| design | N=8: GE / depth / T | N=16: GE / depth / T | N=32: GE / depth / T | N=64: GE / depth / T |
|---|--:|--:|--:|--:|
| add_cmpcarry | 83 / 10 / 0.31 | 196 / 17 / 0.43 | 392 / 25 / 0.63 | 855 / 30 / 0.76 |
| add_kogge | 66 / 15 / 0.36 | 150 / 24 / 0.53 | 325 / 47 / 1.07 | 789 / 66 / 1.65 |
| add_ripple | 56 / 17 / 0.39 | 112 / 33 / 0.68 | 224 / 65 / 1.25 | 448 / 129 / 2.40 |
| add_sklansky | 62 / 15 / 0.36 | 128 / 28 / 0.64 | 297 / 43 / 0.96 | 601 / 80 / 1.81 |
| add_yosys | 57 / 17 / 0.37 | 118 / 33 / 0.76 | 252 / 57 / 1.31 | 495 / 121 / 2.62 |

N=8: delay rank by depth vs NLDM differs for: add_kogge, add_ripple; Kendall tau(depth, NLDM) = +1.00, tau(depth, LE) = +1.00, tau(LE, NLDM) = +1.00

N=16: delay rank by depth vs NLDM differs for: add_yosys; Kendall tau(depth, NLDM) = +1.00, tau(depth, LE) = +1.00, tau(LE, NLDM) = +1.00

N=32: delay rank by depth vs NLDM differs for: add_yosys, add_ripple; Kendall tau(depth, NLDM) = +0.80, tau(depth, LE) = +1.00, tau(LE, NLDM) = +0.80

N=64: delay rank by depth vs NLDM differs for: add_yosys, add_ripple; Kendall tau(depth, NLDM) = +0.80, tau(depth, LE) = +0.80, tau(LE, NLDM) = +1.00

mul:

| design | N=8: GE / depth / T | N=16: GE / depth / T | N=32: GE / depth / T | N=64: GE / depth / T |
|---|--:|--:|--:|--:|
| mul_array | 448 / 40 / 1.39 | 1963 / 88 / 2.98 | 8192 / 184 / 6.15 | - |
| mul_dadda_ks | 484 / 24 / 0.83 | 2077 / 48 / 1.33 | - | - |
| mul_dadda_rc | 446 / 29 / 0.87 | 1954 / 61 / 1.45 | 8153 / 125 / 2.60 | - |
| mul_tree | 451 / 30 / 0.88 | 2035 / 63 / 1.65 | 8454 / 126 / 2.85 | - |
| mul_tree_h | 451 / 30 / 0.88 | 2026 / 62 / 1.62 | 8453 / 127 / 2.83 | - |
| mul_wallace | 483 / 30 / 0.91 | 2114 / 62 / 1.61 | 8768 / 124 / 2.74 | - |
| mul_yosys | 469 / 30 / 0.96 | 2081 / 59 / 1.64 | 8639 / 110 / 2.77 | - |

N=8: delay rank by depth vs NLDM differs for: mul_wallace, mul_yosys; Kendall tau(depth, NLDM) = +1.00, tau(depth, LE) = +1.00, tau(LE, NLDM) = +0.80

N=16: delay rank by depth vs NLDM differs for: mul_yosys, mul_dadda_rc, mul_wallace; Kendall tau(depth, NLDM) = +0.70, tau(depth, LE) = +0.80, tau(LE, NLDM) = +0.81

N=32: delay rank by depth vs NLDM differs for: mul_yosys, mul_dadda_rc, mul_tree, mul_tree_h; Kendall tau(depth, NLDM) = +0.47, tau(depth, LE) = +0.87, tau(LE, NLDM) = +0.60

### FPGA lane (Yosys only): LUT count and LUT levels

| design | GE | LUT4 | LUT4 levels | LUT6 | LUT6 levels | synth_ice40 LUT4 (+CARRY) | synth_xilinx xc7 LUT (+MUXF, CARRY4) |
|---|--:|--:|--:|--:|--:|--:|--:|
| add_ripple | 112 | 37 | 11 | 29 | 7 | 37 (+0) | 35 (+10, 0) |
| add_sklansky | 128 | 45 | 10 | 34 | 6 | 49 (+0) | 38 (+10, 0) |
| add_kogge | 150 | 58 | 8 | 40 | 5 | 82 (+0) | 48 (+12, 0) |
| add_cmpcarry | 196 | 63 | 6 | 46 | 4 | 48 (+133) | 76 (+11, 14) |
| add_yosys | 118 | 39 | 11 | 29 | 7 | 16 (+16) | 16 (+0, 5) |
| mul_array | 1963 | 716 | 38 | 552 | 24 | 761 (+0) | 890 (+339, 0) |
| mul_tree | 2035 | 637 | 22 | 484 | 14 | 642 (+0) | 615 (+196, 0) |
| mul_wallace | 2114 | 705 | 22 | 492 | 14 | 697 (+0) | 534 (+55, 0) |
| mul_tree_h | 2026 | 636 | 22 | 484 | 13 | 642 (+0) | 613 (+198, 0) |
| mul_dadda_rc | 1954 | 624 | 22 | 458 | 14 | 626 (+0) | 501 (+60, 0) |
| mul_dadda_ks | 2077 | 703 | 17 | 514 | 11 | 717 (+0) | 564 (+105, 0) |
| mul_yosys | 2081 | 698 | 22 | 504 | 13 | 655 (+24) | 0 (+0, 0) |

