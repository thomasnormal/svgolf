import LeanModels.Sv.CombKnownThm

/-!
# Exhaustive evaluation of a combinational design (`sv_exhaustive`, the evaluator)

A comb design's settled states satisfy `CombEqs`: every assign's target window holds its right-hand
side's value (`evalPure2`). For a design with few input bits, those values are COMPUTED here, on a
PACKED environment: one natural number, bit `off n + i` the value of bit `i` of signal `n` (the scheme
of PROVING.md §12, made generic: GMP arithmetic, no list accumulator). An assign is evaluated by
`evalPure2` itself, on a LOCAL state that holds only the names its right-hand side reads, built from the
packed bits; so the evaluator is E's evaluator, and its soundness rests on `evalPure2_congr_reads`.

The API is for CONES: a `BNet` is any list of sites with any layout, nothing assumes all of a design's
processes or all of its outputs.
-/

namespace LeanModels.Sv.Exh

/-- One site of a bit netlist: its target window `tgt[lo +: w]`, the windows `(name, lo, w)` it reads, and
its bit function (`f rd k`: bit `k` of the target window, given the read function `rd`). -/
structure BSite where
  tgt : String
  lo : Nat
  w : Nat
  rds : List (String × Nat × Nat)
  f : (String → Nat → Bool) → Nat → Bool

/-- The read function of a packed environment `e` under the layout `off`. -/
def rdOf (off : String → Nat) (e : Nat) : String → Nat → Bool := fun n i => e.testBit (off n + i)

/-- Set bits `[o, o + w)` of `e` that `g` says are `1` (the target bits start `0`). -/
def orBits (e o : Nat) (g : Nat → Bool) : Nat → Nat
  | 0 => e
  | w + 1 => if g w then orBits e o g w ||| 2 ^ (o + w) else orBits e o g w

/-- One site's step on the packed environment. -/
def BSite.step (off : String → Nat) (e : Nat) (b : BSite) : Nat :=
  orBits e (off b.tgt + b.lo) (b.f (rdOf off e)) b.w

/-- **The packed evaluation** of a site list, in order. -/
def run (off : String → Nat) : List BSite → Nat → Nat
  | [], e => e
  | b :: bs, e => run off bs (b.step off e)

/-! ## The sites of a design -/

/-- The declared width of `n` (`0` if undeclared). -/
def dwOf (d : Design2) (n : String) : Nat := (d.declWidth n).getD 0

/-- The window a read observes: a whole read observes the whole declared vector. -/
def winOf (d : Design2) : ReadWin → String × Nat × Nat
  | .whole n => (n, 0, dwOf d n)
  | .win n lo w => (n, lo, w)

/-- The local state of a right-hand side: its read names, at their declared widths, from `rd`. -/
def localSt (d : Design2) (rd : String → Nat → Bool) (ns : List String) : SvState :=
  ns.map fun n => (n, LVec.ofBoolFn (dwOf d n) (rd n))

/-- The site of an assign to a single window (`none` for a concatenated target or another process). -/
def procSite (d : Design2) : Process2 → Option BSite
  | .assign t e => (t.window? d).map fun W =>
      { tgt := W.1, lo := W.2.1, w := W.2.2, rds := e.reads.map (winOf d),
        f := fun rd k => match evalPure2 (localSt d rd (e.reads.map ReadWin.name)) e with
          | .ok v => (v.resizeU W.2.2).boolAt k
          | _ => false }
  | _ => none

/-- The sites of the processes `ord` (indices), in that order. -/
def sitesOf (d : Design2) (ord : List Nat) : List BSite :=
  ord.filterMap fun i => d.processes[i]?.bind (procSite d)

/-- The layout: the declarations in order, each at the sum of the widths before it. -/
def layoutL (d : Design2) : List (String × Nat) :=
  (d.decls.toList.foldl (fun (acc : List (String × Nat) × Nat) dc =>
    (acc.1 ++ [(dc.name, acc.2)], acc.2 + dc.width)) ([], 0)).1

def layout (d : Design2) (n : String) : Nat := ((layoutL d).lookup n).getD 0

end LeanModels.Sv.Exh
