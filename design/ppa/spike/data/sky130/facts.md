### Areas, GE and pin capacitances of the relevant cells (um^2; GE = area / nand2_1; caps in fF)

| cell | area um^2 | GE | input caps fF | leakage nW (average) | function |
|---|--:|--:|---|--:|---|
| inv_1 | 3.7536 | 1.000 | A 2.30 | 0.0053 | Y=(!A) |
| buf_1 | 3.7536 | 1.000 | A 2.10 | 0.0012 | X=(A) |
| nand2_1 | 3.7536 | 1.000 | A 2.31, B 2.32 | 0.0021 | Y=(!A) \| (!B) |
| nor2_1 | 3.7536 | 1.000 | A 2.37, B 2.35 | 0.0020 | Y=(!A&!B) |
| and2_1 | 6.2560 | 1.667 | A 1.46, B 1.50 | 0.0027 | X=(A&B) |
| or2_1 | 6.2560 | 1.667 | A 1.47, B 1.46 | 0.0018 | X=(A) \| (B) |
| xor2_1 | 8.7584 | 2.333 | A 4.38, B 4.34 | 0.0043 | X=(A&!B) \| (!A&B) |
| xnor2_1 | 8.7584 | 2.333 | A 4.51, B 4.56 | 0.0021 | Y=(!A&!B) \| (A&B) |
| mux2_1 | 11.2608 | 3.000 | A0 1.56, A1 1.88, S 3.40 | 0.0040 | X=(A0&!S) \| (A1&S) |
| nand2b_1 | 6.2560 | 1.667 | A_N 1.40, B 2.40 | 0.0023 | Y=(A_N) \| (!B) |
| nor2b_1 | 6.2560 | 1.667 | A 2.37, B_N 1.49 | 0.0022 | Y=(!A&B_N) |
| and2b_1 | 7.5072 | 2.000 | A_N 1.56, B 1.64 | 0.0053 | X=(!A_N&B) |
| or2b_1 | 7.5072 | 2.000 | A 1.73, B_N 1.42 | 0.0036 | X=(A) \| (!B_N) |
| nand3_1 | 5.0048 | 1.333 | A 2.30, B 2.40, C 2.35 | 0.0010 | Y=(!A) \| (!B) \| (!C) |
| nor3_1 | 5.0048 | 1.333 | A 2.44, B 2.38, C 2.32 | 0.0009 | Y=(!A&!B&!C) |
| a21oi_1 | 5.0048 | 1.333 | A1 2.35, A2 2.32, B1 2.32 | 0.0017 | Y=(!A1&!B1) \| (!A2&!B1) |
| o21ai_1 | 5.0048 | 1.333 | A1 2.33, A2 2.46, B1 2.00 | 0.0010 | Y=(!A1&!A2) \| (!B1) |
| a21o_1 | 7.5072 | 2.000 | A1 2.39, A2 2.33, B1 2.42 | 0.0059 | X=(A1&A2) \| (B1) |
| o21a_1 | 7.5072 | 2.000 | A1 2.36, A2 2.42, B1 2.37 | 0.0022 | X=(A1&B1) \| (A2&B1) |
| a22oi_1 | 7.5072 | 2.000 | A1 2.36, A2 2.38, B1 2.34, B2 2.32 | 0.0026 | Y=(!A1&!B1) \| (!A1&!B2) \| (!A2&!B1) \| (!A2&!B2) |
| maj3_1 | 10.0096 | 2.667 | A 2.75, B 2.54, C 3.05 | 0.0021 | X=(A&B) \| (A&C) \| (B&C) |
| mux2i_1 | 10.0096 | 2.667 | A0 2.21, A1 2.26, S 4.65 | 0.0059 | Y=(!A0&!S) \| (!A1&S) |
| fa_1 | 20.0192 | 5.333 | A 6.73, B 6.03, CIN 4.52 | 0.0073 | COUT=(A&B) \| (A&CIN) \| (B&CIN); SUM=(A&!B&!CIN) \| (!A&B&!CIN) \| (!A&!B&CIN) \| (A&B&CIN) |
| ha_1 | 12.5120 | 3.333 | A 3.03, B 2.84 | 0.0078 | COUT=(A&B); SUM=(A&!B) \| (!A&B) |
| conb_1 | 3.7536 | 1.000 | - | 0.0032 | HI=1; LO=0 |
| dfxtp_1 | 20.0192 | 5.333 | D 1.68 | 0.0084 | sequential |
| dfrtp_1 | 25.0240 | 6.667 | D 1.98, RESET_B 3.60 | 0.0117 | sequential |
| dfstp_1 | 26.2752 | 7.000 | D 2.36, SET_B 3.40 | 0.0100 | sequential |
| dfbbp_1 | 32.5312 | 8.667 | D 1.59, RESET_B 1.60, SET_B 3.44 | 0.0136 | sequential |
| dlxtp_1 | 15.0144 | 4.000 | D 1.77 | 0.0079 | sequential |

### The GE table derived from sky130 against score/ge.json

| Yosys gate | sky130 cell | um^2 | derived GE | ge.json | derived / ge.json |
|---|---|--:|--:|--:|--:|
| BUF | buf_1 | 3.7536 | 1.0000 | 0.000 | n/a |
| NOT | inv_1 | 3.7536 | 1.0000 | 0.667 | 1.499 |
| NAND | nand2_1 | 3.7536 | 1.0000 | 1.000 | 1.000 |
| NOR | nor2_1 | 3.7536 | 1.0000 | 1.000 | 1.000 |
| AND | and2_1 | 6.2560 | 1.6667 | 1.333 | 1.250 |
| OR | or2_1 | 6.2560 | 1.6667 | 1.333 | 1.250 |
| ANDNOT | nor2b_1 | 6.2560 | 1.6667 | 1.333 | 1.250 |
| ORNOT | nand2b_1 | 6.2560 | 1.6667 | 1.333 | 1.250 |
| XOR | xor2_1 | 8.7584 | 2.3333 | 2.000 | 1.167 |
| XNOR | xnor2_1 | 8.7584 | 2.3333 | 2.000 | 1.167 |
| MUX | mux2_1 | 11.2608 | 3.0000 | 2.333 | 1.286 |

ANDNOT / ORNOT alternatives: $_ANDNOT_: nor2b_1 1.667 GE, and2b_1 2.000 GE, inv_1+nor2_1 2.000 GE; $_ORNOT_: nand2b_1 1.667 GE, or2b_1 2.000 GE, inv_1+nand2_1 2.000 GE

The two inverter-like costs: inv_1 = 3.7536 um^2, inv_2 = 3.7536, inv_4 = 6.2560; clkinv_1 = 3.7536; buf_1 = 3.7536; nand2_2 = 6.2560.

### Flip-flops and latches: price and timing (clk slew 0.05 ns, data slew 0.05 ns, Q load 10 fF; ps)

| cell | um^2 | GE | clk->Q | setup D | hold D | async->Q | recovery | removal | notes |
|---|--:|--:|--:|--:|--:|--:|--:|--:|---|
| dfxtp_1 | 20.0192 | 5.333 | 349 | 112 | -32 | - | - | - | plain D flip-flop |
| dfxtp_2 | 21.2704 | 5.667 | 334 | 114 | -32 | - | - | - |  |
| dfxtp_4 | 23.7728 | 6.333 | 344 | 113 | -32 | - | - | - |  |
| dfxbp_1 | 23.7728 | 6.333 | 409 | 112 | -33 | - | - | - | Q and Q_N |
| dfrtp_1 | 25.0240 | 6.667 | 394 | 115 | -35 | 239 | -231 | 323 | async reset (RESET_B) |
| dfrtp_2 | 26.2752 | 7.000 | 409 | 117 | -35 | 255 | -219 | 323 |  |
| dfstp_1 | 26.2752 | 7.000 | 542 | 70 | -14 | 391 | -138 | 156 | async set (SET_B) |
| dfbbp_1 | 32.5312 | 8.667 | 541 | 177 | -51 | 357 | 65 | -39 | async set and reset, Q and Q_N |
| dfrbp_1 | 28.7776 | 7.667 | 507 | 114 | -36 | 350 | -226 | 323 | async reset, Q and Q_N |
| edfxtp_1 | 30.0288 | 8.000 | 412 | 249 | -107 | - | - | - | enable flop (mux inside) |
| sdfxtp_1 | 26.2752 | 7.000 | 350 | 209 | -74 | - | - | - | scan flop |
| dlxtp_1 | 15.0144 | 4.000 | 353 | 195 | -25 | - | - | - | latch, active-high gate |
| dlxtn_1 | 15.0144 | 4.000 | 437 | 157 | -106 | - | - | - | latch, active-low gate |
| dlrtp_1 | 16.2656 | 4.333 | 373 | 221 | -25 | 165 | -47 | 62 | latch with reset |
| dlclkp_1 | 17.5168 | 4.667 | - | - | - | - | - | - | clock-gate latch |

T_clk,min = clk->Q + T_comb + setup (+ nothing else: ideal clock, zero skew). For dfxtp_1 the register overhead is clk->Q 349 ps + setup 112 ps = 461 ps; dfrtp_1: 509 ps.

### Drive-strength variants: area and delay at a fixed condition (input slew 50 ps, load 10 fF; worst arc; ps)

| family | size | um^2 | GE | input cap fF (pin A or A1) | delay rise | delay fall | delay at load 40 fF (rise) |
|---|--:|--:|--:|--:|--:|--:|--:|
| inv | 1 | 3.7536 | 1.00 | 2.30 | 92 | 62 | 261 |
| inv | 2 | 3.7536 | 1.00 | 4.46 | 66 | 42 | 159 |
| inv | 4 | 6.2560 | 1.67 | 9.00 | 55 | 33 | 111 |
| inv | 8 | 11.2608 | 3.00 | 17.65 | 49 | 28 | 80 |
| inv | 16 | 20.0192 | 5.33 | 33.44 | 48 | 28 | 67 |
| buf | 1 | 3.7536 | 1.00 | 2.10 | 140 | 123 | 377 |
| buf | 2 | 5.0048 | 1.33 | 1.73 | 119 | 136 | 219 |
| buf | 4 | 7.5072 | 2.00 | 2.40 | 110 | 140 | 169 |
| buf | 8 | 15.0144 | 4.00 | 7.01 | 90 | 118 | 124 |
| buf | 16 | 27.5264 | 7.33 | 13.64 | 94 | 124 | 118 |
| nand2 | 1 | 3.7536 | 1.00 | 2.31 | 108 | 87 | 291 |
| nand2 | 2 | 6.2560 | 1.67 | 4.43 | 84 | 65 | 188 |
| nand2 | 4 | 11.2608 | 3.00 | 8.54 | 71 | 51 | 130 |
| nand2 | 8 | 20.0192 | 5.33 | 16.93 | 67 | 48 | 101 |
| nor2 | 1 | 3.7536 | 1.00 | 2.37 | 187 | 66 | 552 |
| nor2 | 2 | 6.2560 | 1.67 | 4.40 | 148 | 49 | 371 |
| nor2 | 4 | 11.2608 | 3.00 | 8.73 | 120 | 41 | 247 |
| nor2 | 8 | 20.0192 | 5.33 | 16.98 | 109 | 39 | 183 |
| and2 | 0 | 6.2560 | 1.67 | 1.60 | 187 | 194 | 471 |
| and2 | 1 | 6.2560 | 1.67 | 1.46 | 166 | 185 | 363 |
| and2 | 2 | 7.5072 | 2.00 | 1.45 | 160 | 209 | 266 |
| and2 | 4 | 8.7584 | 2.33 | 2.32 | 146 | 164 | 209 |
| or2 | 0 | 6.2560 | 1.67 | 1.53 | 176 | 269 | 484 |
| or2 | 1 | 6.2560 | 1.67 | 1.47 | 138 | 263 | 327 |
| or2 | 2 | 6.2560 | 1.67 | 1.49 | 125 | 322 | 230 |
| or2 | 4 | 8.7584 | 2.33 | 2.41 | 120 | 258 | 184 |
| xor2 | 1 | 8.7584 | 2.33 | 4.38 | 241 | 187 | 644 |
| xor2 | 2 | 16.2656 | 4.33 | 8.98 | 195 | 185 | 434 |
| xor2 | 4 | 27.5264 | 7.33 | 17.36 | 175 | 184 | 315 |
| xnor2 | 1 | 8.7584 | 2.33 | 4.51 | 255 | 161 | 700 |
| xnor2 | 2 | 16.2656 | 4.33 | 8.68 | 197 | 152 | 446 |
| xnor2 | 4 | 27.5264 | 7.33 | 16.77 | 173 | 145 | 319 |
| mux2 | 1 | 11.2608 | 3.00 | 1.56 | 238 | 359 | 420 |
| mux2 | 2 | 11.2608 | 3.00 | 1.88 | 248 | 354 | 357 |
| mux2 | 4 | 15.0144 | 4.00 | 2.27 | 210 | 312 | 276 |
| mux2 | 8 | 26.2752 | 7.00 | 4.77 | 247 | 352 | 290 |
| a21oi | 1 | 5.0048 | 1.33 | 2.35 | 240 | 98 | 661 |
| a21oi | 2 | 8.7584 | 2.33 | 4.44 | 179 | 67 | 419 |
| a21oi | 4 | 16.2656 | 4.33 | 8.57 | 161 | 58 | 300 |
| o21ai | 0 | 5.0048 | 1.33 | 1.75 | 303 | 147 | 914 |
| o21ai | 1 | 5.0048 | 1.33 | 2.33 | 220 | 105 | 605 |
| o21ai | 2 | 8.7584 | 2.33 | 4.83 | 176 | 73 | 400 |
| o21ai | 4 | 16.2656 | 4.33 | 9.14 | 161 | 62 | 299 |
| nand3 | 1 | 5.0048 | 1.33 | 2.30 | 128 | 123 | 338 |
| nand3 | 2 | 10.0096 | 2.67 | 4.34 | 90 | 94 | 195 |
| nand3 | 4 | 17.5168 | 4.67 | 8.66 | 86 | 78 | 147 |

### Units and the sign convention of the power tables

Liberty header: time_unit 1ns, capacitive_load_unit 1.0000000000 pf, voltage_unit 1V, current_unit 1mA, leakage_power_unit 1nW -> internal_power tables are V x mA x ns = pJ; pin capacitances are pF (Nangate45: fF).

nand2_1 output Y, mean over its power tables, at input slew 50 ps; ½CV² with V = 1.8 V in the last column (fJ):

| load fF | rise_power fJ | fall_power fJ | rise + fall fJ | ½CV² fJ |
|--:|--:|--:|--:|--:|
| 0.5 | 4.88 | 1.89 | 6.77 | 0.81 |
| 2.0 | 7.44 | -0.36 | 7.08 | 3.24 |
| 5.0 | 12.43 | -5.02 | 7.41 | 8.10 |
| 10.0 | 20.68 | -12.94 | 7.74 | 16.20 |
| 40.0 | 68.65 | -61.36 | 7.29 | 64.80 |
| 166.6 | 271.49 | -266.39 | 5.10 | 269.89 |

rise_power is about +½CV² above a load-independent part and fall_power about -½CV² below it: the tables are SIGNED and already contain the load's charge/discharge. A rise followed by a fall (every net alternates) leaves 2 x the cell's own internal energy; a table value alone is not a per-toggle energy.

### Cell policy census (428 cell groups)

| class | cells | allowed in a combinational scored netlist | reason |
|---|--:|---|---|
| logic | 268 | yes | ordinary combinational cells, every drive strength (including _0, buffers, inverters, constant-free) |
| sequential | 68 | no | flip-flops (plain, reset/set, scan, enable): combinational tasks have none |
| low-power-flow | 34 | no | isolation, level shifter, bleeder, power-gated clock/decap cells need extra supply rails |
| clock | 20 | no | clock buffers/inverters/delay buffers (clkbuf, clkinv, clkinvlp, clkdlybuf*): clock-tree cells |
| tristate | 13 | no | tri-state: a third output state (z) the 2-state netlist simulation cannot see |
| physical-only | 9 | no | filler, decap, tap, antenna diode, probe point, spare cell: no logic function |
| multi-output | 9 | no | adder cells with two outputs: ABC's mapper handles single-output cells only; extract_fa is not in the flow |
| delay | 6 | no | delay cells (dlygate*, dlymetal*): a buffer chosen for its delay; ABC would use them to equalize paths |
| tie | 1 | no | tie cell: inserted by the flow's hilomap step, never chosen by the mapper |
