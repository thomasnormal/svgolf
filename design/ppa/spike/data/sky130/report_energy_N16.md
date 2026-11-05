
### Energy per operation, flow A0' (scored netlist priced in sky130 cells); fJ; seeds 1..5 = 2001 vectors / 300 timed pairs each; seed 0 = public dev set (201 vectors / 100 pairs)

| design | act mean | act CV | act range % | glitch mean | glitch CV | glitch range % | glitch factor | gm3 glitch (seeds 1-3) vs gm5 | dev seed 0 glitch vs gm5 | dev seed 0 act vs gm5 |
|---|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|
| add_ripple (proved) | 728 | 0.33% | 1.0 | 847 | 0.61% | 1.4 | 1.16 | +0.1% | +4.5% | +0.6% |
| add_sklansky | 811 | 0.33% | 1.0 | 1003 | 0.61% | 1.5 | 1.23 | -0.0% | +3.5% | +0.3% |
| add_kogge | 893 | 0.33% | 0.9 | 1087 | 0.92% | 2.7 | 1.21 | +0.4% | +1.9% | +0.1% |
| add_cmpcarry | 1040 | 0.25% | 0.7 | 1373 | 0.74% | 2.1 | 1.31 | +0.2% | +2.3% | +0.1% |
| add_yosys (banned) | 767 | 0.28% | 0.9 | 951 | 0.62% | 1.9 | 1.24 | +0.2% | +3.4% | +0.3% |
| mul_array (proved) | 8633 | 0.40% | 1.1 | 39459 | 1.49% | 3.7 | 4.53 | -0.8% | +0.7% | -0.7% |
| mul_tree (proved) | 8851 | 0.42% | 1.0 | 16393 | 1.15% | 3.2 | 1.84 | -0.5% | +1.6% | -1.1% |
| mul_wallace (proved) | 9051 | 0.35% | 0.9 | 15535 | 1.15% | 2.9 | 1.70 | -0.6% | +1.4% | -0.7% |
| mul_tree_h (proved) | 8827 | 0.43% | 1.0 | 16335 | 1.13% | 3.1 | 1.83 | -0.4% | +1.7% | -1.1% |
| mul_dadda_rc | 8540 | 0.46% | 1.1 | 14559 | 1.16% | 2.9 | 1.69 | -0.5% | +1.0% | -0.9% |
| mul_dadda_ks | 9095 | 0.45% | 1.1 | 16500 | 1.08% | 2.6 | 1.80 | -0.5% | +1.3% | -0.9% |
| mul_yosys (banned) | 8951 | 0.42% | 1.0 | 15707 | 1.23% | 3.1 | 1.74 | -0.5% | +0.7% | -0.5% |
| sbox_bp | 1162 | 0.27% | 0.8 | 3788 | 1.31% | 4.0 | 3.28 | -0.1% | -2.3% | -0.3% |
| sbox_table | 3523 | 0.70% | 2.1 | 4772 | 1.33% | 3.6 | 1.35 | +0.1% | +3.4% | -0.2% |

add, activity energy ranks per seed (1 = lowest), flow a0:

| design | seed 0 | seed 1 | seed 2 | seed 3 | seed 4 | seed 5 | gm5 rank | rank interval over seeds |
|---|--:|--:|--:|--:|--:|--:|--:|--:|
| add_ripple (proved) | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1..1 |
| add_sklansky | 3 | 3 | 3 | 3 | 3 | 3 | 3 | 3..3 |
| add_kogge | 4 | 4 | 4 | 4 | 4 | 4 | 4 | 4..4 |
| add_cmpcarry | 5 | 5 | 5 | 5 | 5 | 5 | 5 | 5..5 |
| add_yosys (banned) | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 2..2 |

Kendall tau between seed pairs (seeds 1..5): min +1.00, mean +1.00.

add, glitch-aware energy ranks per seed (1 = lowest), flow a0:

| design | seed 0 | seed 1 | seed 2 | seed 3 | seed 4 | seed 5 | gm5 rank | rank interval over seeds |
|---|--:|--:|--:|--:|--:|--:|--:|--:|
| add_ripple (proved) | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1..1 |
| add_sklansky | 3 | 3 | 3 | 3 | 3 | 3 | 3 | 3..3 |
| add_kogge | 4 | 4 | 4 | 4 | 4 | 4 | 4 | 4..4 |
| add_cmpcarry | 5 | 5 | 5 | 5 | 5 | 5 | 5 | 5..5 |
| add_yosys (banned) | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 2..2 |

Kendall tau between seed pairs (seeds 1..5): min +1.00, mean +1.00.

mul, activity energy ranks per seed (1 = lowest), flow a0:

| design | seed 0 | seed 1 | seed 2 | seed 3 | seed 4 | seed 5 | gm5 rank | rank interval over seeds |
|---|--:|--:|--:|--:|--:|--:|--:|--:|
| mul_array (proved) | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 2..2 |
| mul_tree (proved) | 4 | 4 | 4 | 4 | 4 | 4 | 4 | 4..4 |
| mul_wallace (proved) | 6 | 6 | 6 | 6 | 6 | 6 | 6 | 6..6 |
| mul_tree_h (proved) | 3 | 3 | 3 | 3 | 3 | 3 | 3 | 3..3 |
| mul_dadda_rc | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1..1 |
| mul_dadda_ks | 7 | 7 | 7 | 7 | 7 | 7 | 7 | 7..7 |
| mul_yosys (banned) | 5 | 5 | 5 | 5 | 5 | 5 | 5 | 5..5 |

Kendall tau between seed pairs (seeds 1..5): min +1.00, mean +1.00.

mul, glitch-aware energy ranks per seed (1 = lowest), flow a0:

| design | seed 0 | seed 1 | seed 2 | seed 3 | seed 4 | seed 5 | gm5 rank | rank interval over seeds |
|---|--:|--:|--:|--:|--:|--:|--:|--:|
| mul_array (proved) | 7 | 7 | 7 | 7 | 7 | 7 | 7 | 7..7 |
| mul_tree (proved) | 5 | 5 | 5 | 5 | 5 | 5 | 5 | 5..5 |
| mul_wallace (proved) | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 2..2 |
| mul_tree_h (proved) | 4 | 4 | 4 | 4 | 4 | 4 | 4 | 4..4 |
| mul_dadda_rc | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1..1 |
| mul_dadda_ks | 6 | 6 | 6 | 6 | 6 | 6 | 6 | 6..6 |
| mul_yosys (banned) | 3 | 3 | 3 | 3 | 3 | 3 | 3 | 3..3 |

Kendall tau between seed pairs (seeds 1..5): min +1.00, mean +1.00.

### Energy per operation, flow A1'u (abc -liberty); fJ; seeds 1..5 = 2001 vectors / 300 timed pairs each; seed 0 = public dev set (201 vectors / 100 pairs)

| design | act mean | act CV | act range % | glitch mean | glitch CV | glitch range % | glitch factor | gm3 glitch (seeds 1-3) vs gm5 | dev seed 0 glitch vs gm5 | dev seed 0 act vs gm5 |
|---|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|
| add_ripple (proved) | 793 | 0.27% | 0.9 | 997 | 0.88% | 2.2 | 1.25 | -0.2% | -0.7% | -0.2% |
| add_sklansky | 861 | 0.26% | 0.8 | 1010 | 0.41% | 1.2 | 1.17 | -0.1% | +0.3% | +0.2% |
| add_kogge | 890 | 0.28% | 0.9 | 1008 | 0.41% | 1.0 | 1.13 | +0.0% | +1.7% | +0.6% |
| add_cmpcarry | 994 | 0.28% | 0.9 | 1171 | 0.71% | 2.2 | 1.17 | +0.3% | +0.2% | +0.1% |
| add_yosys (banned) | 800 | 0.30% | 0.9 | 959 | 0.69% | 1.8 | 1.19 | +0.2% | -0.3% | -0.3% |
| mul_array (proved) | 9168 | 0.40% | 1.1 | 28010 | 0.96% | 2.8 | 3.03 | -0.6% | -0.6% | -0.8% |
| mul_tree (proved) | 9348 | 0.38% | 1.0 | 16315 | 0.97% | 2.9 | 1.73 | -0.2% | -0.4% | -1.2% |
| mul_wallace (proved) | 9562 | 0.31% | 0.8 | 15824 | 0.86% | 2.4 | 1.64 | -0.4% | +0.5% | -0.9% |
| mul_tree_h (proved) | 9372 | 0.38% | 1.0 | 16116 | 0.94% | 2.6 | 1.71 | -0.3% | +0.3% | -1.3% |
| mul_dadda_rc | 8967 | 0.40% | 0.9 | 15537 | 1.25% | 3.1 | 1.72 | -0.6% | +0.8% | -1.0% |
| mul_dadda_ks | 9418 | 0.40% | 0.9 | 15024 | 1.03% | 2.4 | 1.58 | -0.6% | -0.4% | -0.9% |
| mul_yosys (banned) | 9522 | 0.39% | 1.0 | 15589 | 1.09% | 3.0 | 1.62 | -0.3% | -0.6% | -0.4% |
| sbox_bp | 1464 | 0.31% | 0.9 | 3524 | 1.84% | 5.4 | 2.41 | +0.5% | -2.6% | -0.1% |
| sbox_table | 3009 | 0.64% | 1.9 | 3634 | 1.37% | 3.8 | 1.20 | +0.3% | +1.8% | +0.1% |

add, activity energy ranks per seed (1 = lowest), flow u:

| design | seed 0 | seed 1 | seed 2 | seed 3 | seed 4 | seed 5 | gm5 rank | rank interval over seeds |
|---|--:|--:|--:|--:|--:|--:|--:|--:|
| add_ripple (proved) | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1..1 |
| add_sklansky | 3 | 3 | 3 | 3 | 3 | 3 | 3 | 3..3 |
| add_kogge | 4 | 4 | 4 | 4 | 4 | 4 | 4 | 4..4 |
| add_cmpcarry | 5 | 5 | 5 | 5 | 5 | 5 | 5 | 5..5 |
| add_yosys (banned) | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 2..2 |

Kendall tau between seed pairs (seeds 1..5): min +1.00, mean +1.00.

add, glitch-aware energy ranks per seed (1 = lowest), flow u:

| design | seed 0 | seed 1 | seed 2 | seed 3 | seed 4 | seed 5 | gm5 rank | rank interval over seeds |
|---|--:|--:|--:|--:|--:|--:|--:|--:|
| add_ripple (proved) | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 2..2 |
| add_sklansky | 3 | 4 | 3 | 4 | 4 | 3 | 4 | 3..4 |
| add_kogge | 4 | 3 | 4 | 3 | 3 | 4 | 3 | 3..4 |
| add_cmpcarry | 5 | 5 | 5 | 5 | 5 | 5 | 5 | 5..5 |
| add_yosys (banned) | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1..1 |

Kendall tau between seed pairs (seeds 1..5): min +0.80, mean +0.88.

mul, activity energy ranks per seed (1 = lowest), flow u:

| design | seed 0 | seed 1 | seed 2 | seed 3 | seed 4 | seed 5 | gm5 rank | rank interval over seeds |
|---|--:|--:|--:|--:|--:|--:|--:|--:|
| mul_array (proved) | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 2..2 |
| mul_tree (proved) | 3 | 3 | 3 | 3 | 3 | 3 | 3 | 3..3 |
| mul_wallace (proved) | 6 | 7 | 7 | 7 | 7 | 7 | 7 | 7..7 |
| mul_tree_h (proved) | 4 | 4 | 4 | 4 | 4 | 4 | 4 | 4..4 |
| mul_dadda_rc | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1..1 |
| mul_dadda_ks | 5 | 5 | 5 | 5 | 5 | 5 | 5 | 5..5 |
| mul_yosys (banned) | 7 | 6 | 6 | 6 | 6 | 6 | 6 | 6..6 |

Kendall tau between seed pairs (seeds 1..5): min +1.00, mean +1.00.

mul, glitch-aware energy ranks per seed (1 = lowest), flow u:

| design | seed 0 | seed 1 | seed 2 | seed 3 | seed 4 | seed 5 | gm5 rank | rank interval over seeds |
|---|--:|--:|--:|--:|--:|--:|--:|--:|
| mul_array (proved) | 7 | 7 | 7 | 7 | 7 | 7 | 7 | 7..7 |
| mul_tree (proved) | 6 | 6 | 6 | 6 | 6 | 6 | 6 | 6..6 |
| mul_wallace (proved) | 4 | 4 | 4 | 4 | 4 | 4 | 4 | 4..4 |
| mul_tree_h (proved) | 5 | 5 | 5 | 5 | 5 | 5 | 5 | 5..5 |
| mul_dadda_rc | 3 | 2 | 2 | 2 | 3 | 2 | 2 | 2..3 |
| mul_dadda_ks | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1..1 |
| mul_yosys (banned) | 2 | 3 | 3 | 3 | 2 | 3 | 3 | 2..3 |

Kendall tau between seed pairs (seeds 1..5): min +0.90, mean +0.96.

### Does the energy ranking carry information beyond area? Kendall tau, flow A0', gm5 of seeds 1..5

add: tau(act, area) +1.00; tau(glitch, area) +1.00; tau(glitch, depth_v1) -1.00; tau(glitch, T) -0.80; tau(act, glitch) +1.00

mul: tau(act, area) +0.90; tau(glitch, area) -0.05; tau(glitch, depth_v1) +0.30; tau(glitch, T) +0.33; tau(act, glitch) +0.05

