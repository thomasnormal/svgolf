#!/usr/bin/env python3
"""generate the H2 G0 probe Lean file: one load_sv + sv_structure? + sv_equations? per block."""
import sys
blocks = sys.argv[1].split(",")
proc = set(sys.argv[2].split(",")) if len(sys.argv) > 2 and sys.argv[2] else set()
print("""import LeanModels.Sv.Ingest2
import SvGolf.LoadSv
import SvGolf.Comb
import LeanModels.Sv.CombEqTactic
import LeanModels.Sv.CombProcTactic
import LeanModels.Sv.CombLib

open LeanModels.Sv LeanModels.Sv.CombView LeanModels.Sv.CombLib LeanModels.Sv.CombEq SvGolf
set_option maxRecDepth 100000
""")
for b in blocks:
    sv = f"design/fdiv-param/h2/{b}.sv"
    print(f'/-! ===== {b} ===== -/')
    top = "fdiv16" if b.startswith("fdiv16") else b
    print(f'load_sv {b} from "{sv}" (top := "{top}")')
    if b in proc:
        print(f'example : ∃ d\', {b}.sem.lowerComb = some d\' ∧ CombDesign d\' ∧ Acyclic d\' := by\n  sv_structure?\n  all_goals sorry')
        print(f'example {{d\' : Design2}} (hl : {b}.sem.lowerComb = some d\') (hc : CombDesign d\') (ha : Acyclic d\') (st : SvState)\n    (heqs : CombEqs d\' st) (hsh : StateShape d\' st) : True := by\n  sv_equations?\n  trivial')
    else:
        print(f'example : CombDesign {b}.sem ∧ Acyclic {b}.sem := by\n  sv_structure?\n  all_goals sorry')
        print(f'example (hc : CombDesign {b}.sem) (ha : Acyclic {b}.sem) (st : SvState)\n    (heqs : CombEqs {b}.sem st) (hsh : StateShape {b}.sem st) : True := by\n  sv_equations?\n  trivial')
    print()
