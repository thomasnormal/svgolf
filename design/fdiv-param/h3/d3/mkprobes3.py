#!/usr/bin/env python3
"""D3 acceptance probes: one tiny parametric module per construct; writes probes3/*.sv and probes3.lean."""
import os
HERE = os.path.dirname(os.path.abspath(__file__))
os.makedirs(f"{HERE}/probes3", exist_ok=True)
EW = "W+P+1"
HDR = """module {n} #(parameter int W = 5, parameter int P = 11) (
  input  logic [W+P-1:0] a,
  input  logic [W+P-1:0] b,
  output logic [W+P-1:0] q
);
  localparam integer K = W + P;
  localparam integer T = P - 1;
  localparam integer EW = W + P + 1;
{body}
endmodule
"""
PROBES = {
 "q01_red_in_bitwise": """  logic x;
  assign x = (&a[K-2:T]) & (|a[T-1:0]);
  assign q[0] = x;
  assign q[K-1:1] = '0;""",
 "q02_cmp_in_bitwise": """  logic x;
  assign x = (a[P-1:0] >= b[P-1:0]) & a[0];
  assign q[0] = x;
  assign q[K-1:1] = '0;""",
 "q03_shift_cmp_wide": """  logic [EW-1:0] d;
  logic x;
  assign d = {a[K-1:0], 1'b0};
  assign x = ((a[P:0] << d) != b[P:0]);
  assign q[0] = x;
  assign q[K-1:1] = '0;""",
 "q04_const_left_sub": """  logic [EW-1:0] e, d;
  assign e = {a[K-1:0], 1'b0};
  assign d = 1 - e;
  assign q[EW-2:0] = d[EW-2:0];""",
 "q05_fill_arm": """  logic c;
  assign c = a[0];
  assign q[K-1] = a[K-1];
  assign q[K-2:T] = c ? '1 : b[K-2:T];
  assign q[T-1:0] = '0;""",
 "q06_zero_arm": """  logic c;
  logic [W-1:0] y;
  assign c = a[0];
  assign y = c ? 0 : a[W-1:0];
  assign q[W-1:0] = y;
  assign q[K-1:W] = '0;""",
 "q07_wide_shift": """  logic [EW-1:0] d;
  logic [P:0] qs;
  assign d = {a[K-1:0], 1'b0};
  assign qs = b[P:0] >> d;
  assign q[P:0] = qs;
  assign q[K-1:P+1] = '0;""",
 "q08_not_plus_const": """  logic [EW-1:0] e, z;
  assign e = {a[K-1:0], 1'b0};
  assign z = ~e + 2;
  assign q[EW-2:0] = z[EW-2:0];""",
 "q09_red_concat_part": """  logic [P-1:0] ma;
  assign ma = {|a[K-2:T], a[T-1:0]};
  assign q[P-1:0] = ma;
  assign q[K-1:P] = '0;""",
 "q10_cmp_bit_target_family": """  logic [P:0] nbx;
  logic [P+2:0][P:0] rr;
  logic [P+1:0][P:0] dd;
  logic [P+1:0] qq;
  assign nbx = {1'b0, b[P-1:0]};
  assign rr[0] = {1'b0, a[P-1:0]};
  genvar k;
  generate
    for (k = 0; k < P + 2; k = k + 1) begin : div
      assign qq[P+1-k] = (rr[k] >= nbx);
      assign dd[k]     = rr[k] - nbx;
      assign rr[k+1]   = qq[P+1-k] ? (dd[k] << 1) : (rr[k] << 1);
    end
  endgenerate
  assign q[P+1:0] = qq;
  assign q[K-1:P+2] = '0;""",
 "q11_inline_mag": """  logic [W-1:0] ef;
  logic [P:0] qs;
  logic inc;
  logic [K-2:0] mag;
  assign ef = a[W-1:0];
  assign qs = b[P:0];
  assign inc = a[K-1];
  assign mag = {ef, qs[P-1:1]} + inc;
  assign q[K-2:0] = mag;
  assign q[K-1] = 1'b0;""",
 "q12_norm_family_inline_cond": """  logic [P-1:0][P-1:0] nr;
  logic [P-1:0][EW-1:0] yr;
  assign nr[0] = a[P-1:0];
  assign yr[0] = b[W-1:0];
  genvar i;
  generate
    for (i = 0; i < P - 1; i = i + 1) begin : norm
      assign nr[i+1] = nr[i][P-1] ? nr[i] : (nr[i] << 1);
      assign yr[i+1] = nr[i][P-1] ? yr[i] : (yr[i] - 1);
    end
  endgenerate
  assign q[P-1:0] = nr[P-1];
  assign q[K-1:P] = '0;""",
 "q13_red_cond": """  logic [W-1:0] y;
  assign y = (|a[W-1:0]) ? a[W-1:0] : 1;
  assign q[W-1:0] = y;
  assign q[K-1:W] = '0;""",
 "q14_bit_and_red": """  logic [EW-1:0] e;
  logic x;
  assign e = {a[K-1:0], 1'b0};
  assign x = ~e[EW-1] & (|e);
  assign q[0] = x;
  assign q[K-1:1] = '0;""",
 "q15_add_onebit_signal": """  logic ez;
  logic [W-1:0] y;
  assign ez = ~|a[W-1:0];
  assign y = a[W-1:0] + ez;
  assign q[W-1:0] = y;
  assign q[K-1:W] = '0;""",
 "q16_row_red_inline": """  logic [P+2:0][P:0] rr;
  logic [P+1:0] qq;
  logic st0;
  assign rr[0] = {1'b0, a[P-1:0]};
  genvar k;
  generate
    for (k = 0; k < P + 2; k = k + 1) begin : div
      assign qq[k] = rr[k][0];
      assign rr[k+1] = rr[k] << 1;
    end
  endgenerate
  assign st0 = (qq[P+1] & qq[0]) | (|rr[P+2]);
  assign q[0] = st0;
  assign q[K-1:1] = '0;""",
 "q17_low_family_bits": """  logic fin;
  logic [K-2:0] mag;
  assign fin = a[0];
  assign mag = a[K-2:0];
  assign q[K-1] = b[0];
  assign q[K-2:T] = mag[K-2:T];
  assign q[T-1] = fin | mag[T-1];
  genvar n;
  generate
    for (n = 0; n < T - 1; n = n + 1) begin : lo
      assign q[n] = fin & mag[n];
    end
  endgenerate""",
 "q18_ovf_inline": """  logic [EW-1:0] e;
  logic x;
  assign e = {a[K-1:0], 1'b0};
  assign x = ~e[EW-1] & ((|e[EW-2:W]) | (&e[W-1:0]));
  assign q[0] = x;
  assign q[K-1:1] = '0;""",
 "q19_sub_chain_emax": """  logic [EW-1:0] ya, yb, em, e;
  logic adj;
  assign ya = {a[K-1:0], 1'b0};
  assign yb = {b[K-1:0], 1'b0};
  assign adj = a[0];
  assign em[W-2:0] = '1;
  assign em[EW-1:W-1] = '0;
  assign e = ya - yb + em - adj;
  assign q[EW-2:0] = e[EW-2:0];""",
 "q20_concat_cmp_operand": """  logic [P:0] nbx;
  logic x;
  assign nbx = {1'b0, b[P-1:0]};
  assign x = (a[P:0] >= nbx);
  assign q[0] = x;
  assign q[K-1:1] = '0;""",
 "q21_ternary_chain_fields": """  logic cn, ci, cz, ovf, fin;
  logic [K-2:0] mag;
  assign cn = a[0]; assign ci = a[1]; assign cz = a[2]; assign ovf = a[3];
  assign mag = b[K-2:0];
  assign fin = ~(cn | ci | cz | ovf);
  assign q[K-1] = ~cn & a[K-1];
  assign q[K-2:T] = (cn | ci | (~cz & ovf)) ? '1 : (cz ? '0 : mag[K-2:T]);
  assign q[T-1] = cn | (fin & mag[T-1]);
  genvar n;
  generate
    for (n = 0; n < T - 1; n = n + 1) begin : lo
      assign q[n] = fin & mag[n];
    end
  endgenerate""",
}
W = os.path.join(os.environ["SCRATCH"], "wph3/d3")
lean = """import LeanModels.Sv.Ingest2
import SvGolf.LoadSv
import SvGolf.Comb
import LeanModels.Sv.CombEqTactic
import LeanModels.Sv.CombLib

open LeanModels.Sv LeanModels.Sv.CombView LeanModels.Sv.CombLib LeanModels.Sv.CombEq SvGolf
set_option maxRecDepth 100000
"""
for n, body in PROBES.items():
    open(f"{HERE}/probes3/{n}.sv", "w").write(HDR.format(n=n, body=body))
    lean += f"""
/-! ## {n} -/
load_sv {n} from "{W}/probes3/{n}.sv" (top := "{n}")
example (W P : Nat) : CombDesign ({n}.sem W P) := by
  sv_structure?
example (W P : Nat) (hc : CombDesign ({n}.sem W P)) (ha : Acyclic ({n}.sem W P)) (st : SvState)
    (heqs : CombEqs ({n}.sem W P) st) (hsh : StateShape ({n}.sem W P) st) : True := by
  sv_equations?
  trivial
"""
open(f"{HERE}/probes3.lean", "w").write(lean)
print(len(PROBES), "probes")
