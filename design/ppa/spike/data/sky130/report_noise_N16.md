### Structure noise: the same circuit, rewritten (variants of tests/canon/variants.py), N = 16

Layout (oneline) and rename (ren_random) variants: canonical RTLIL byte-identical to the base on every design: True; every number identical.

Deviation of the worst variant from the base (max over variants of |x/base - 1|), by kind (order = hoist, reverse, 4 shuffles; commute = every commutative operand swapped):

| design | kind | GE_v1 (legacy) | depth_v1 | A0' area | A0' T | A1'u area | A1'u T | A1's area | A1's T |
|---|---|--:|--:|--:|--:|--:|--:|--:|--:|
| add_kogge | order | 0.0% | 0.0% | 0.0% | 0.0% | 0.0% | 0.0% | 0.0% | 0.0% |
| add_kogge | commute | 0.0% | 0.0% | 0.0% | 0.0% | 0.0% | 0.0% | 0.0% | 0.0% |
| add_ripple | order | 0.0% | 0.0% | 0.0% | 0.0% | 0.0% | 0.0% | 0.0% | 0.0% |
| add_ripple | commute | 0.0% | 0.0% | 0.0% | 4.1% | 0.0% | 0.1% | 0.0% | 0.1% |
| add_sklansky | order | 0.0% | 0.0% | 0.0% | 0.0% | 0.0% | 0.0% | 0.0% | 0.0% |
| add_sklansky | commute | 2.1% | 7.1% | 2.3% | 13.5% | 0.3% | 15.6% | 8.1% | 13.3% |
| mul_array | order | 0.0% | 0.0% | 0.0% | 0.0% | 0.2% | 1.0% | 0.3% | 0.1% |
| mul_array | commute | 6.3% | 0.0% | 11.3% | 31.8% | 0.9% | 0.2% | 0.7% | 1.5% |
| mul_tree | order | 0.0% | 0.0% | 0.0% | 0.0% | 0.0% | 0.0% | 0.0% | 0.0% |
| mul_tree | commute | 4.0% | 0.0% | 7.2% | 1.9% | 1.9% | 7.7% | 3.1% | 4.7% |
| mul_tree_h | order | 0.0% | 0.0% | 0.0% | 0.0% | 0.0% | 0.0% | 0.0% | 0.0% |
| mul_tree_h | commute | 4.3% | 0.0% | 7.6% | 1.8% | 0.1% | 20.1% | 0.1% | 13.3% |
| sbox_bp | order | 4.1% | 4.8% | 3.5% | 18.4% | 9.9% | 5.5% | 13.5% | 8.2% |
| sbox_bp | commute | 0.3% | 0.0% | 0.7% | 7.5% | 15.5% | 6.4% | 13.8% | 1.5% |

Median / max over the designs of that deviation:

| kind | GE_v1 (legacy) | depth_v1 | A0' area | A0' T | A1'u area | A1'u T | A1's area | A1's T |
|---|--:|--:|--:|--:|--:|--:|--:|--:|
| order | 0.0% / 4.1% | 0.0% / 4.8% | 0.0% / 3.5% | 0.0% / 18.4% | 0.0% / 9.9% | 0.0% / 5.5% | 0.0% / 13.5% | 0.0% / 8.2% |
| commute | 2.1% / 6.3% | 0.0% / 7.1% | 2.3% / 11.3% | 4.1% / 31.8% | 0.3% / 15.5% | 6.4% / 20.1% | 0.7% / 13.8% | 1.5% / 13.3% |

Spread (max/min - 1) over ALL variants including base, per design:

| design | GE_v1 (legacy) | depth_v1 | A0' area | A0' T | A1'u area | A1'u T | A1's area | A1's T |
|---|--:|--:|--:|--:|--:|--:|--:|--:|
| add_kogge | 0.0% | 0.0% | 0.0% | 0.0% | 0.0% | 0.0% | 0.0% | 0.0% |
| add_ripple | 0.0% | 0.0% | 0.0% | 4.1% | 0.0% | 0.1% | 0.0% | 0.1% |
| add_sklansky | 2.1% | 7.1% | 2.4% | 13.5% | 0.3% | 18.4% | 8.1% | 15.4% |
| mul_array | 6.3% | 0.0% | 11.3% | 31.8% | 0.9% | 1.2% | 0.7% | 1.6% |
| mul_tree | 4.0% | 0.0% | 7.2% | 1.9% | 1.9% | 8.3% | 3.1% | 5.0% |
| mul_tree_h | 4.3% | 0.0% | 7.6% | 1.8% | 0.1% | 20.1% | 0.1% | 13.3% |
| sbox_bp | 5.2% | 4.8% | 4.7% | 18.6% | 18.4% | 12.7% | 16.1% | 9.8% |
