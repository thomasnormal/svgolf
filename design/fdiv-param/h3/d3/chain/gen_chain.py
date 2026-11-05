# Generator used in WP-H3 gate 1 part 2 (design/fdiv-param/H3-G2-NOTE.md). The absolute paths are those of the work session:
# the input is the output of `sv_equations?` on D3 (meas/d3_hb_eq.lean); adapt the paths to rerun.
import os, re
base=os.path.join(os.environ["SCRATCH"], 'wph3/')
hyps=open(base+'chain/hyps.txt').read()
hyps=re.sub(r'\bW\b','f.w',hyps)
hyps=re.sub(r'\bP\b','f.p',hyps)
body=open(base+'chain/chain_body.txt').read()
hdr='''import tasks.fdivp.DpG4

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-!
# Task `fdivp`: the chain, from the printed equations of `sv_equations` to the value of `q`

WP-H3 design layer, continued (`DpG4.lean`). `chain` takes the 34 equations of the netlist `fdivp3.sv` exactly as
`sv_equations` states them (the signal `x` is the bit function `f_x`, `st.boolAt "x"` in the solution) and the two
operands as numbers, and concludes `XF.val q (W + P) = OutN f a b`, the value of the model of `DpQ.lean`, which
`OutN_fdivBits` identifies with the task function. Widths are `f.w`, `f.p` of a format `f`, which at the use site is
`⟨W, P, hW, hP⟩` (the projections reduce).
-/

namespace SvGolf.FdivParam
namespace Glue

open LeanModels.Sv LeanModels.Sv.CombView
open SvGolf.IEEE754

theorem chain (f : Format)
    (f_s f_ea_nz f_eb_nz f_c_nan f_c_inf f_c_zero f_na_r f_nb_r f_ya_r f_yb_r f_nbx f_rr f_adj f_qm f_onesW f_emw
      f_E f_ovf f_dsh f_qs f_inc f_ef f_mag f_q f_qq f_dd f_a f_b : Nat → Bool)
    (av bv : Nat)
    (ha : ∀ k, k < f.w + f.p → f_a k = av.testBit k) (hb : ∀ k, k < f.w + f.p → f_b k = bv.testBit k)
'''
ftr='''
end Glue
end SvGolf.FdivParam
'''
out=hdr+hyps+'    : XF.val (fun x => f_q x) (f.w + f.p) = OutN f av bv := by\n'+body+ftr
open(base+'wt/svgolf/tasks/fdivp/DpG5.lean','w').write(out)
print(len(out))
