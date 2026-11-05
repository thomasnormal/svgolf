
### add, N = 16 (sbox: fixed)

| design | GE_v1 | depth_v1 | A0' um^2 | A0' GE | A0' T ps | A1'u um^2 | A1'u cells | A1'u depth | A1'u T ps | A1's um^2 | A1's T ps | Nangate A0 GE | Nangate A0 T ps |
|---|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|
| add_ripple (proved) | 112.0 | 33 | 460 | 122.7 | 2487 | 440 | 48 | 16 | 6313 | 460 | 5292 | 112.0 | 676 |
| add_sklansky | 127.7 | 28 | 542 | 144.3 | 2328 | 499 | 69 | 12 | 3357 | 542 | 2845 | 127.7 | 636 |
| add_kogge | 149.7 | 24 | 642 | 171.0 | 1947 | 568 | 92 | 10 | 2665 | 588 | 2605 | 150.3 | 534 |
| add_cmpcarry | 196.0 | 17 | 857 | 228.3 | 1870 | 661 | 105 | 9 | 1833 | 688 | 1751 | 197.7 | 434 |
| add_yosys (banned) | 118.0 | 33 | 498 | 132.7 | 3024 | 489 | 74 | 11 | 3558 | 528 | 3007 | 118.0 | 760 |

Ranks by area (1 = best; ties share the best rank):

| design | GE_v1 | A0' um2 | A1'u um2 | A1's um2 | A1'l um2 | A1'r um2 | Nangate A0 GE |
|---|--:|--:|--:|--:|--:|--:|--:|
| add_ripple (proved) | 1 | 1 | 1 | 1 | 1 | 1 | 1 |
| add_sklansky | 3 | 3 | 3 | 3 | 3 | 3 | 3 |
| add_kogge | 4 | 4 | 4 | 4 | 5 | 4 | 4 |
| add_cmpcarry | 5 | 5 | 5 | 5 | 4 | 5 | 5 |
| add_yosys (banned) | 2 | 2 | 2 | 2 | 2 | 2 | 2 |

Kendall tau of the area rankings over the 5 designs:

| | GE_v1 | A0' um2 | A1'u um2 | A1's um2 | A1'l um2 | A1'r um2 | Nangate A0 GE |
|---|--:|--:|--:|--:|--:|--:|--:|
| GE_v1 | +1.00 | +1.00 | +1.00 | +1.00 | +0.80 | +1.00 | +1.00 |
| A0' um2 | +1.00 | +1.00 | +1.00 | +1.00 | +0.80 | +1.00 | +1.00 |
| A1'u um2 | +1.00 | +1.00 | +1.00 | +1.00 | +0.80 | +1.00 | +1.00 |
| A1's um2 | +1.00 | +1.00 | +1.00 | +1.00 | +0.80 | +1.00 | +1.00 |
| A1'l um2 | +0.80 | +0.80 | +0.80 | +0.80 | +1.00 | +0.80 | +0.80 |
| A1'r um2 | +1.00 | +1.00 | +1.00 | +1.00 | +0.80 | +1.00 | +1.00 |
| Nangate A0 GE | +1.00 | +1.00 | +1.00 | +1.00 | +0.80 | +1.00 | +1.00 |

Ranks by delay (1 = best; ties share the best rank):

| design | depth_v1 | A0' T | A1'u T | A1's T | A1'f T | A1'l T | A1'h T | Nangate A0 T |
|---|--:|--:|--:|--:|--:|--:|--:|--:|
| add_ripple (proved) | 4 | 4 | 5 | 5 | 5 | 5 | 5 | 4 |
| add_sklansky | 3 | 3 | 3 | 3 | 2 | 3 | 3 | 3 |
| add_kogge | 2 | 2 | 2 | 2 | 1 | 1 | 2 | 2 |
| add_cmpcarry | 1 | 1 | 1 | 1 | 3 | 2 | 1 | 1 |
| add_yosys (banned) | 4 | 5 | 4 | 4 | 4 | 4 | 4 | 5 |

Kendall tau of the delay rankings over the 5 designs:

| | depth_v1 | A0' T | A1'u T | A1's T | A1'f T | A1'l T | A1'h T | Nangate A0 T |
|---|--:|--:|--:|--:|--:|--:|--:|--:|
| depth_v1 | +1.00 | +1.00 | +1.00 | +1.00 | +0.56 | +0.78 | +1.00 | +1.00 |
| A0' T | +1.00 | +1.00 | +0.80 | +0.80 | +0.40 | +0.60 | +0.80 | +1.00 |
| A1'u T | +1.00 | +0.80 | +1.00 | +1.00 | +0.60 | +0.80 | +1.00 | +0.80 |
| A1's T | +1.00 | +0.80 | +1.00 | +1.00 | +0.60 | +0.80 | +1.00 | +0.80 |
| A1'f T | +0.56 | +0.40 | +0.60 | +0.60 | +1.00 | +0.80 | +0.60 | +0.40 |
| A1'l T | +0.78 | +0.60 | +0.80 | +0.80 | +0.80 | +1.00 | +0.80 | +0.60 |
| A1'h T | +1.00 | +0.80 | +1.00 | +1.00 | +0.60 | +0.80 | +1.00 | +0.80 |
| Nangate A0 T | +1.00 | +1.00 | +0.80 | +0.80 | +0.40 | +0.60 | +0.80 | +1.00 |

### mul, N = 16 (sbox: fixed)

| design | GE_v1 | depth_v1 | A0' um^2 | A0' GE | A0' T ps | A1'u um^2 | A1'u cells | A1'u depth | A1'u T ps | A1's um^2 | A1's T ps | Nangate A0 GE | Nangate A0 T ps |
|---|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|
| mul_array (proved) | 1962.6 | 88 | 8290 | 2208.7 | 10642 | 8645 | 834 | 45 | 16462 | 9060 | 15223 | 1963.0 | 2981 |
| mul_tree (proved) | 2034.9 | 63 | 8603 | 2292.0 | 5932 | 7975 | 1074 | 31 | 7539 | 8264 | 6258 | 2035.7 | 1652 |
| mul_wallace (proved) | 2113.9 | 62 | 8966 | 2388.7 | 5786 | 8398 | 1217 | 32 | 7328 | 8808 | 6072 | 2117.0 | 1611 |
| mul_tree_h (proved) | 2025.9 | 62 | 8563 | 2281.3 | 5797 | 8134 | 1050 | 30 | 6188 | 8466 | 5987 | 2026.3 | 1616 |
| mul_dadda_rc | 1953.6 | 61 | 8230 | 2192.7 | 5281 | 7551 | 1125 | 31 | 6709 | 7971 | 5280 | 1958.0 | 1446 |
| mul_dadda_ks | 2076.5 | 48 | 8937 | 2381.0 | 5029 | 8265 | 1063 | 20 | 5514 | 8626 | 5184 | 2100.3 | 1326 |
| mul_yosys (banned) | 2081.2 | 59 | 8826 | 2351.3 | 6081 | 8454 | 1145 | 26 | 6170 | 8901 | 5579 | 2083.7 | 1642 |

Ranks by area (1 = best; ties share the best rank):

| design | GE_v1 | A0' um2 | A1'u um2 | A1's um2 | A1'l um2 | A1'r um2 | Nangate A0 GE |
|---|--:|--:|--:|--:|--:|--:|--:|
| mul_array (proved) | 2 | 2 | 7 | 7 | 7 | 2 | 2 |
| mul_tree (proved) | 4 | 4 | 2 | 2 | 2 | 5 | 4 |
| mul_wallace (proved) | 7 | 7 | 5 | 5 | 4 | 7 | 7 |
| mul_tree_h (proved) | 3 | 3 | 3 | 3 | 3 | 4 | 3 |
| mul_dadda_rc | 1 | 1 | 1 | 1 | 1 | 1 | 1 |
| mul_dadda_ks | 5 | 6 | 4 | 4 | 5 | 3 | 6 |
| mul_yosys (banned) | 6 | 5 | 6 | 6 | 6 | 6 | 5 |

Kendall tau of the area rankings over the 7 designs:

| | GE_v1 | A0' um2 | A1'u um2 | A1's um2 | A1'l um2 | A1'r um2 | Nangate A0 GE |
|---|--:|--:|--:|--:|--:|--:|--:|
| GE_v1 | +1.00 | +0.90 | +0.33 | +0.33 | +0.24 | +0.81 | +0.90 |
| A0' um2 | +0.90 | +1.00 | +0.24 | +0.24 | +0.14 | +0.71 | +1.00 |
| A1'u um2 | +0.33 | +0.24 | +1.00 | +1.00 | +0.90 | +0.14 | +0.24 |
| A1's um2 | +0.33 | +0.24 | +1.00 | +1.00 | +0.90 | +0.14 | +0.24 |
| A1'l um2 | +0.24 | +0.14 | +0.90 | +0.90 | +1.00 | +0.05 | +0.14 |
| A1'r um2 | +0.81 | +0.71 | +0.14 | +0.14 | +0.05 | +1.00 | +0.71 |
| Nangate A0 GE | +0.90 | +1.00 | +0.24 | +0.24 | +0.14 | +0.71 | +1.00 |

Ranks by delay (1 = best; ties share the best rank):

| design | depth_v1 | A0' T | A1'u T | A1's T | A1'f T | A1'l T | A1'h T | Nangate A0 T |
|---|--:|--:|--:|--:|--:|--:|--:|--:|
| mul_array (proved) | 7 | 7 | 7 | 7 | 7 | 7 | 7 | 7 |
| mul_tree (proved) | 6 | 5 | 6 | 6 | 5 | 4 | 5 | 6 |
| mul_wallace (proved) | 4 | 3 | 5 | 5 | 3 | 6 | 3 | 3 |
| mul_tree_h (proved) | 4 | 4 | 3 | 4 | 4 | 3 | 4 | 4 |
| mul_dadda_rc | 3 | 2 | 4 | 2 | 6 | 5 | 6 | 2 |
| mul_dadda_ks | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 |
| mul_yosys (banned) | 2 | 6 | 2 | 3 | 2 | 2 | 2 | 5 |

Kendall tau of the delay rankings over the 7 designs:

| | depth_v1 | A0' T | A1'u T | A1's T | A1'f T | A1'l T | A1'h T | Nangate A0 T |
|---|--:|--:|--:|--:|--:|--:|--:|--:|
| depth_v1 | +1.00 | +0.60 | +0.90 | +0.90 | +0.70 | +0.70 | +0.70 | +0.70 |
| A0' T | +0.60 | +1.00 | +0.43 | +0.62 | +0.33 | +0.24 | +0.33 | +0.90 |
| A1'u T | +0.90 | +0.43 | +1.00 | +0.81 | +0.71 | +0.81 | +0.71 | +0.52 |
| A1's T | +0.90 | +0.62 | +0.81 | +1.00 | +0.52 | +0.62 | +0.52 | +0.71 |
| A1'f T | +0.70 | +0.33 | +0.71 | +0.52 | +1.00 | +0.71 | +1.00 | +0.43 |
| A1'l T | +0.70 | +0.24 | +0.81 | +0.62 | +0.71 | +1.00 | +0.71 | +0.33 |
| A1'h T | +0.70 | +0.33 | +0.71 | +0.52 | +1.00 | +0.71 | +1.00 | +0.43 |
| Nangate A0 T | +0.70 | +0.90 | +0.52 | +0.71 | +0.43 | +0.33 | +0.43 | +1.00 |

The proved mul references only (mul_array, mul_tree, mul_wallace, mul_tree_h), ranks by area / delay:

| metric | mul_array | mul_tree | mul_wallace | mul_tree_h | order |
|---|--:|--:|--:|--:|--:|
| GE_v1 | 1 | 3 | 4 | 2 | mul_array < mul_tree_h < mul_tree < mul_wallace |
| A0' um2 | 1 | 3 | 4 | 2 | mul_array < mul_tree_h < mul_tree < mul_wallace |
| A1'u um2 | 4 | 1 | 3 | 2 | mul_tree < mul_tree_h < mul_wallace < mul_array |
| A1's um2 | 4 | 1 | 3 | 2 | mul_tree < mul_tree_h < mul_wallace < mul_array |
| A1'l um2 | 4 | 1 | 3 | 2 | mul_tree < mul_tree_h < mul_wallace < mul_array |
| A1'r um2 | 1 | 3 | 4 | 2 | mul_array < mul_tree_h < mul_tree < mul_wallace |
| Nangate A0 GE | 1 | 3 | 4 | 2 | mul_array < mul_tree_h < mul_tree < mul_wallace |
| depth_v1 | 4 | 3 | 1 | 1 | mul_wallace < mul_tree_h < mul_tree < mul_array |
| A0' T | 4 | 3 | 1 | 2 | mul_wallace < mul_tree_h < mul_tree < mul_array |
| A1'u T | 4 | 3 | 2 | 1 | mul_tree_h < mul_wallace < mul_tree < mul_array |
| A1's T | 4 | 3 | 2 | 1 | mul_tree_h < mul_wallace < mul_tree < mul_array |
| A1'f T | 4 | 3 | 1 | 2 | mul_wallace < mul_tree_h < mul_tree < mul_array |
| A1'l T | 4 | 2 | 3 | 1 | mul_tree_h < mul_tree < mul_wallace < mul_array |
| A1'h T | 4 | 3 | 1 | 2 | mul_wallace < mul_tree_h < mul_tree < mul_array |
| Nangate A0 T | 4 | 3 | 1 | 2 | mul_wallace < mul_tree_h < mul_tree < mul_array |

### sbox, N = 16 (sbox: fixed)

| design | GE_v1 | depth_v1 | A0' um^2 | A0' GE | A0' T ps | A1'u um^2 | A1'u cells | A1'u depth | A1'u T ps | A1's um^2 | A1's T ps |
|---|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|
| sbox_bp | 201.0 | 21 | 892 | 237.7 | 4145 | 1095 | 129 | 13 | 4112 | 1265 | 3784 |
| sbox_table | 786.9 | 11 | 3446 | 918.0 | 2102 | 2343 | 378 | 6 | 1657 | 2658 | 1697 |

Ranks by area (1 = best; ties share the best rank):

| design | GE_v1 | A0' um2 | A1'u um2 | A1's um2 | A1'l um2 | A1'r um2 |
|---|--:|--:|--:|--:|--:|--:|
| sbox_bp | 1 | 1 | 1 | 1 | 1 | 1 |
| sbox_table | 2 | 2 | 2 | 2 | 2 | 2 |

Ranks by delay (1 = best; ties share the best rank):

| design | depth_v1 | A0' T | A1'u T | A1's T | A1'f T | A1'l T | A1'h T |
|---|--:|--:|--:|--:|--:|--:|--:|
| sbox_bp | 2 | 2 | 2 | 2 | 2 | 2 | 2 |
| sbox_table | 1 | 1 | 1 | 1 | 1 | 1 | 1 |

### Compound-cell gain: full library (A1'u) against the 2-input + MUX sub-library (A1'r) and against A0'

| design | A0' um^2 | A1'r um^2 | A1'u um^2 | u / r | u / A0' | compound cells in u | share of u cells | a21oi+o21ai | mux2 | maj3 | inv | buf |
|---|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|
| add_ripple | 460 | 460 | 440 | 0.957 | 0.957 | 0 | 0.00 | 0 | 0 | 16 | 0 | 0 |
| add_sklansky | 542 | 512 | 499 | 0.976 | 0.921 | 13 | 0.19 | 3 | 0 | 7 | 1 | 0 |
| add_kogge | 642 | 599 | 568 | 0.948 | 0.885 | 23 | 0.25 | 5 | 0 | 2 | 1 | 0 |
| add_cmpcarry | 857 | 736 | 661 | 0.898 | 0.771 | 27 | 0.26 | 12 | 0 | 2 | 2 | 0 |
| add_yosys | 498 | 478 | 489 | 1.024 | 0.982 | 12 | 0.16 | 3 | 0 | 5 | 0 | 0 |
| mul_array | 8290 | 8115 | 8645 | 1.065 | 1.043 | 42 | 0.05 | 23 | 0 | 203 | 32 | 0 |
| mul_tree | 8603 | 8583 | 7975 | 0.929 | 0.927 | 109 | 0.10 | 68 | 0 | 152 | 9 | 0 |
| mul_wallace | 8966 | 8851 | 8398 | 0.949 | 0.937 | 162 | 0.13 | 76 | 0 | 103 | 35 | 0 |
| mul_tree_h | 8563 | 8526 | 8134 | 0.954 | 0.950 | 104 | 0.10 | 51 | 0 | 152 | 4 | 0 |
| mul_dadda_rc | 8230 | 8088 | 7551 | 0.934 | 0.917 | 168 | 0.15 | 103 | 0 | 96 | 20 | 0 |
| mul_dadda_ks | 8937 | 8339 | 8265 | 0.991 | 0.925 | 157 | 0.15 | 54 | 0 | 140 | 23 | 0 |
| mul_yosys | 8826 | 8720 | 8454 | 0.970 | 0.958 | 114 | 0.10 | 66 | 0 | 126 | 16 | 0 |
| sbox_bp | 892 | 826 | 1095 | 1.326 | 1.227 | 33 | 0.26 | 12 | 1 | 0 | 3 | 0 |
| sbox_table | 3446 | 2959 | 2343 | 0.792 | 0.680 | 229 | 0.61 | 91 | 0 | 0 | 5 | 0 |

u / r area: min 0.792, median 0.955, max 1.326.

### Sizing and buffering at the fixed loads: A1's (buffer; upsize; dnsize) against A1'u

| design | u um^2 | s um^2 | s/u area | u T ps | s T ps | s/u T | cells not _0/_1 in s | buffers s | buffers u |
|---|--:|--:|--:|--:|--:|--:|--:|--:|--:|
| add_ripple | 440 | 460 | 1.045 | 6313 | 5292 | 0.838 | 16 | 0 | 0 |
| add_sklansky | 499 | 542 | 1.085 | 3357 | 2845 | 0.847 | 11 | 0 | 0 |
| add_kogge | 568 | 588 | 1.035 | 2665 | 2605 | 0.978 | 7 | 0 | 0 |
| add_cmpcarry | 661 | 688 | 1.042 | 1833 | 1751 | 0.956 | 6 | 1 | 0 |
| add_yosys | 489 | 528 | 1.079 | 3558 | 3007 | 0.845 | 13 | 0 | 0 |
| mul_array | 8645 | 9060 | 1.048 | 16462 | 15223 | 0.925 | 166 | 52 | 0 |
| mul_tree | 7975 | 8264 | 1.036 | 7539 | 6258 | 0.830 | 49 | 49 | 0 |
| mul_wallace | 8398 | 8808 | 1.049 | 7328 | 6072 | 0.829 | 66 | 62 | 0 |
| mul_tree_h | 8134 | 8466 | 1.041 | 6188 | 5987 | 0.967 | 48 | 55 | 0 |
| mul_dadda_rc | 7551 | 7971 | 1.056 | 6709 | 5280 | 0.787 | 70 | 64 | 0 |
| mul_dadda_ks | 8265 | 8626 | 1.044 | 5514 | 5184 | 0.940 | 55 | 62 | 0 |
| mul_yosys | 8454 | 8901 | 1.053 | 6170 | 5579 | 0.904 | 70 | 54 | 0 |
| sbox_bp | 1095 | 1265 | 1.155 | 4112 | 3784 | 0.920 | 26 | 4 | 0 |
| sbox_table | 2343 | 2658 | 1.134 | 1657 | 1697 | 1.024 | 43 | 56 | 0 |

### Mapper-to-mapper spread per design (max / min - 1 over A0' and the A1' variants u s f l h r)

| design | area spread | T spread | area range um^2 | T range ps | area rank range (of mappers) | A0' vs best-T mapper: T |
|---|--:|--:|---|---|---|---|
| add_ripple | 72% | 154% | 440..757 | 2487..6313 | | |
| add_sklansky | 72% | 143% | 499..861 | 1384..3357 | | |
| add_kogge | 111% | 107% | 568..1197 | 1287..2665 | | |
| add_cmpcarry | 39% | 33% | 622..863 | 1405..1870 | | |
| add_yosys | 40% | 98% | 478..668 | 1795..3558 | | |
| mul_array | 62% | 55% | 8115..13154 | 10642..16462 | | |
| mul_tree | 18% | 42% | 7953..9354 | 5320..7539 | | |
| mul_wallace | 18% | 85% | 8290..9772 | 5162..9535 | | |
| mul_tree_h | 16% | 20% | 7929..9211 | 5288..6342 | | |
| mul_dadda_rc | 23% | 73% | 7535..9281 | 5280..9127 | | |
| mul_dadda_ks | 43% | 49% | 8265..11796 | 3695..5514 | | |
| mul_yosys | 40% | 62% | 8454..11856 | 3803..6170 | | |
| sbox_bp | 99% | 16% | 826..1643 | 3784..4377 | | |
| sbox_table | 52% | 38% | 2260..3446 | 1657..2290 | | |

Spread over designs: area median 41%, max 111%; T median 58%, max 154%.
