import LeanModels.Sv.Basic

/-!
# X9: monotonicity of the pinned 4-state operator tables in the information order

**Status label:** measurement (kernel-checked facts about `LeanModels/Sv/Basic.lean`'s operators; no semantics is
defined here). WS4, 2026-11-02. Imported by nothing; run with `lake env lean` through the Lean slot.

**Order.** `x` below every value and every value below itself: the information order of ARCH-NOTE §4.3 R-X, in which a
2-state concretization refines every `x` to `0` or `1` (`x ⊑ z` too: `x` is the unknown of the 4-valued domain; with `z`
incomparable instead, `c ? z : z` on an ambiguous `c` gives `x` and so does a shift by an `x` amount of a `z` operand,
and both would be reported non-monotone for that reason alone). `z` is otherwise related only to itself (`order X`);
the variant `order XZ` also puts `z` below `0` and `1` (a 2-state view squashes `z` too). Vectors: same width, bitwise. A `Bool` result (a procedural
decision: `if` truthiness, a case match) is ordered by equality, so a decision is monotone iff no refinement of its
input flips it.

**Statement form.** For an operator `f`, `monoK f w = true` says: for all operands of width `w` (every `LVec` of width
`w`, every refinement of each operand), `f a b ⊑ f a' b'`. It is decided by the kernel (`decide +kernel`) at widths 1
and 2 (binary) and 1–3 (unary) — exhaustive at those widths, nothing claimed at others. A non-monotone operator gets a
`= false` theorem AND a named counterexample checked by the kernel.
-/

namespace X9
open LeanModels.Sv

/-- `a ⊑ b` on one 4-state bit: `x` is below every value (it is the unknown); `xz := true` also puts `z` below `0`
and `1` (a 2-state view refines `z` too). -/
def lle (xz : Bool) (a b : Logic) : Bool :=
  a == b || a == .lx || (xz && a == .lz && (b == .l0 || b == .l1))

/-- `a ⊑ b` on vectors: same width, bitwise. -/
def vle (xz : Bool) (a b : LVec) : Bool :=
  a.bits.size == b.bits.size && (a.bits.toList.zip b.bits.toList).all fun (p, q) => lle xz p q

def allLogic : List Logic := [.l0, .l1, .lx, .lz]

/-- Every vector of width `w`, as lists of bits. -/
def allBits : Nat → List (List Logic)
  | 0 => [[]]
  | w + 1 => (allBits w).flatMap fun bs => allLogic.map (· :: bs)

def allVecs (w : Nat) : List LVec := (allBits w).map fun bs => ⟨bs.toArray⟩

/-- The refinements of a bit / of a vector (itself included). -/
def refL (xz : Bool) (a : Logic) : List Logic := allLogic.filter (lle xz a)

def refBits (xz : Bool) : List Logic → List (List Logic)
  | [] => [[]]
  | a :: as => (refBits xz as).flatMap fun rest => (refL xz a).map (· :: rest)

def refs (xz : Bool) (v : LVec) : List LVec := (refBits xz v.bits.toList).map fun bs => ⟨bs.toArray⟩

/-- Monotonicity checkers, by result type. -/
def monoUV (xz : Bool) (f : LVec → LVec) (w : Nat) : Bool :=
  (allVecs w).all fun a => (refs xz a).all fun a' => vle xz (f a) (f a')
def monoUL (xz : Bool) (f : LVec → Logic) (w : Nat) : Bool :=
  (allVecs w).all fun a => (refs xz a).all fun a' => lle xz (f a) (f a')
def monoUB (xz : Bool) (f : LVec → Bool) (w : Nat) : Bool :=
  (allVecs w).all fun a => (refs xz a).all fun a' => f a == f a'
def monoBV (xz : Bool) (f : LVec → LVec → LVec) (w : Nat) : Bool :=
  (allVecs w).all fun a => (allVecs w).all fun b => (refs xz a).all fun a' => (refs xz b).all fun b' =>
    vle xz (f a b) (f a' b')
def monoBL (xz : Bool) (f : LVec → LVec → Logic) (w : Nat) : Bool :=
  (allVecs w).all fun a => (allVecs w).all fun b => (refs xz a).all fun a' => (refs xz b).all fun b' =>
    lle xz (f a b) (f a' b')
def monoBB (xz : Bool) (f : LVec → LVec → Bool) (w : Nat) : Bool :=
  (allVecs w).all fun a => (allVecs w).all fun b => (refs xz a).all fun a' => (refs xz b).all fun b' =>
    f a b == f a' b'
def monoLL (xz : Bool) (f : Logic → Logic → Logic) : Bool :=
  allLogic.all fun a => allLogic.all fun b => (refL xz a).all fun a' => (refL xz b).all fun b' =>
    lle xz (f a b) (f a' b')
def monoL (xz : Bool) (f : Logic → Logic) : Bool :=
  allLogic.all fun a => (refL xz a).all fun a' => lle xz (f a) (f a')
/-- The conditional operator: monotone in all three operands. -/
def monoTern (xz : Bool) (w : Nat) : Bool :=
  (allVecs 1).all fun c => (allVecs w).all fun a => (allVecs w).all fun b =>
    (refs xz c).all fun c' => (refs xz a).all fun a' => (refs xz b).all fun b' =>
      vle xz (LVec.ternary c a b) (LVec.ternary c' a' b')

/-! ## Scalar tables (`Logic`) -/

theorem and_mono : monoLL false Logic.and = true := by decide +kernel
theorem or_mono : monoLL false Logic.or = true := by decide +kernel
theorem xor_mono : monoLL false Logic.xor = true := by decide +kernel
theorem not_mono : monoL false Logic.not = true := by decide +kernel
theorem merge_mono : monoLL false Logic.merge = true := by decide +kernel
theorem and_mono_xz : monoLL true Logic.and = true := by decide +kernel
theorem or_mono_xz : monoLL true Logic.or = true := by decide +kernel
theorem xor_mono_xz : monoLL true Logic.xor = true := by decide +kernel
theorem not_mono_xz : monoL true Logic.not = true := by decide +kernel
theorem merge_mono_xz : monoLL true Logic.merge = true := by decide +kernel

/-! ## Vector operators returning a vector, widths 1 and 2 -/

theorem vand_mono : (monoBV false LVec.and 1 && monoBV false LVec.and 2) = true := by decide +kernel
theorem vor_mono : (monoBV false LVec.or 1 && monoBV false LVec.or 2) = true := by decide +kernel
theorem vxor_mono : (monoBV false LVec.xor 1 && monoBV false LVec.xor 2) = true := by decide +kernel
theorem vnot_mono : (monoUV false LVec.not 1 && monoUV false LVec.not 2 && monoUV false LVec.not 3) = true := by
  decide +kernel
theorem add_mono : (monoBV false LVec.add 1 && monoBV false LVec.add 2) = true := by decide +kernel
theorem sub_mono : (monoBV false LVec.sub 1 && monoBV false LVec.sub 2) = true := by decide +kernel
theorem mul_mono : (monoBV false LVec.mul 1 && monoBV false LVec.mul 2) = true := by decide +kernel
theorem div_mono : (monoBV false LVec.div 1 && monoBV false LVec.div 2) = true := by decide +kernel
theorem rem_mono : (monoBV false LVec.rem 1 && monoBV false LVec.rem 2) = true := by decide +kernel
theorem sdiv_mono : (monoBV false LVec.sdiv 1 && monoBV false LVec.sdiv 2) = true := by decide +kernel
theorem srem_mono : (monoBV false LVec.srem 1 && monoBV false LVec.srem 2) = true := by decide +kernel
theorem shl_mono : (monoBV false LVec.shl 1 && monoBV false LVec.shl 2) = true := by decide +kernel
theorem shr_mono : (monoBV false LVec.shr 1 && monoBV false LVec.shr 2) = true := by decide +kernel
theorem ashr_mono : (monoBV false (LVec.ashr true) 1 && monoBV false (LVec.ashr true) 2) = true := by decide +kernel
theorem pow_mono : (monoBV false (LVec.pow false false) 1 && monoBV false (LVec.pow false false) 2) = true := by
  decide +kernel
theorem spow_mono : (monoBV false (LVec.pow true true) 1 && monoBV false (LVec.pow true true) 2) = true := by
  decide +kernel
theorem pos_mono : (monoUV false LVec.pos 1 && monoUV false LVec.pos 2 && monoUV false LVec.pos 3) = true := by
  decide +kernel
theorem neg_mono : (monoUV false LVec.neg 1 && monoUV false LVec.neg 2 && monoUV false LVec.neg 3) = true := by
  decide +kernel
theorem vmerge_mono : (monoBV false LVec.merge 1 && monoBV false LVec.merge 2) = true := by decide +kernel
theorem concat_mono : (monoBV false LVec.concat 1 && monoBV false LVec.concat 2) = true := by decide +kernel
theorem ternary_mono : (monoTern false 1 && monoTern false 2) = true := by decide +kernel
theorem resizeSigned_mono : (monoUV false (LVec.resizeSigned · 3) 1 && monoUV false (LVec.resizeSigned · 3) 2) = true :=
  by decide +kernel

/-! ## Vector operators returning one bit -/

theorem lt_mono : (monoBL false LVec.lt 1 && monoBL false LVec.lt 2) = true := by decide +kernel
theorem le_mono : (monoBL false LVec.le 1 && monoBL false LVec.le 2) = true := by decide +kernel
theorem gt_mono : (monoBL false LVec.gt 1 && monoBL false LVec.gt 2) = true := by decide +kernel
theorem ge_mono : (monoBL false LVec.ge 1 && monoBL false LVec.ge 2) = true := by decide +kernel
theorem slt_mono : (monoBL false LVec.slt 1 && monoBL false LVec.slt 2) = true := by decide +kernel
theorem sge_mono : (monoBL false LVec.sge 1 && monoBL false LVec.sge 2) = true := by decide +kernel
theorem eqLogical_mono : (monoBL false LVec.eqLogical 1 && monoBL false LVec.eqLogical 2) = true := by decide +kernel
theorem neLogical_mono : (monoBL false LVec.neLogical 1 && monoBL false LVec.neLogical 2) = true := by decide +kernel
theorem land_mono : (monoBL false LVec.land 1 && monoBL false LVec.land 2) = true := by decide +kernel
theorem lor_mono : (monoBL false LVec.lor 1 && monoBL false LVec.lor 2) = true := by decide +kernel
theorem lnot_mono : (monoUL false LVec.lnot 1 && monoUL false LVec.lnot 2 && monoUL false LVec.lnot 3) = true := by
  decide +kernel
theorem truthy_mono : (monoUL false LVec.truthy 1 && monoUL false LVec.truthy 2 && monoUL false LVec.truthy 3) = true :=
  by decide +kernel
theorem redOr_mono : (monoUL false LVec.redOr 1 && monoUL false LVec.redOr 2 && monoUL false LVec.redOr 3) = true := by
  decide +kernel
theorem redAnd_mono : (monoUL false LVec.redAnd 1 && monoUL false LVec.redAnd 2 && monoUL false LVec.redAnd 3) = true :=
  by decide +kernel
theorem redXor_mono : (monoUL false LVec.redXor 1 && monoUL false LVec.redXor 2 && monoUL false LVec.redXor 3) = true :=
  by decide +kernel

/-! ## The non-monotone ones, each with a kernel-checked counterexample -/

/-- Case equality `===`: `x === x` is `1`, its refinement `0 === x` is `0`. -/
theorem eqCase_not_mono : monoBL false LVec.eqCase 1 = false := by decide +kernel
theorem eqCase_cex : LVec.eqCase (.lit "x") (.lit "x") = .l1 ∧ LVec.eqCase (.lit "0") (.lit "x") = .l0 := by
  decide +kernel
theorem neCase_not_mono : monoBL false LVec.neCase 1 = false := by decide +kernel

/-- Wildcard equality `==?`: an `x` in the RIGHT operand is a wildcard; refining it to a care bit changes the answer:
`1 ==? x` is `1`, `1 ==? 0` is `0`. -/
theorem eqWildcard_not_mono : monoBL false LVec.eqWildcard 1 = false := by decide +kernel
theorem eqWildcard_cex :
    LVec.eqWildcard (.lit "1") (.lit "x") = .l1 ∧ LVec.eqWildcard (.lit "1") (.lit "0") = .l0 := by decide +kernel
theorem neWildcard_not_mono : monoBL false LVec.neWildcard 1 = false := by decide +kernel

/-- `if (c)` truthiness, the procedural decision: `if (x)` takes the else branch, `if (1)` the then branch. -/
theorem condTrue_not_mono : monoUB false LVec.condTrue 1 = false := by decide +kernel
theorem condTrue_cex : LVec.condTrue (.lit "x") = false ∧ LVec.condTrue (.lit "1") = true := by decide +kernel

/-- `casez` / `casex` item matching (a `Bool` decision). -/
theorem casez_not_mono : monoBB false (LVec.matchesCase false) 1 = false := by decide +kernel
theorem casex_not_mono : monoBB false (LVec.matchesCase true) 1 = false := by decide +kernel
theorem casex_cex : LVec.matchesCase true (.lit "x") (.lit "1") = true ∧
    LVec.matchesCase true (.lit "0") (.lit "1") = false := by decide +kernel

/-- `isKnownZero` and `allKnown` are knownness TESTS (the `$isunknown` family): non-monotone by design. -/
theorem isKnownZero_not_mono : monoUB false LVec.isKnownZero 1 = false := by decide +kernel
theorem allKnown_not_mono : monoUB false LVec.allKnown 1 = false := by decide +kernel

/-- `toTwoState` (the 2-state storage boundary, `x`/`z` ↦ `0`) is not monotone: `x ↦ 0` but its refinement `1 ↦ 1`. -/
theorem toTwoState_not_mono : monoUV false LVec.toTwoState 1 = false := by decide +kernel

/-! ## `z`: which verdicts change when `z` is also below `0` and `1` -/

theorem vand_mono_xz : monoBV true LVec.and 2 = true := by decide +kernel
theorem add_mono_xz : monoBV true LVec.add 2 = true := by decide +kernel
theorem eqLogical_mono_xz : monoBL true LVec.eqLogical 2 = true := by decide +kernel
theorem ternary_mono_xz : monoTern true 2 = true := by decide +kernel
theorem shl_mono_xz : monoBV true LVec.shl 2 = true := by decide +kernel

/-! ## Axioms: every theorem above, pinned (only `propext`, `Classical.choice`, `Quot.sound` may appear) -/

#print axioms and_mono
#print axioms or_mono
#print axioms xor_mono
#print axioms not_mono
#print axioms merge_mono
#print axioms and_mono_xz
#print axioms or_mono_xz
#print axioms xor_mono_xz
#print axioms not_mono_xz
#print axioms merge_mono_xz
#print axioms vand_mono
#print axioms vor_mono
#print axioms vxor_mono
#print axioms vnot_mono
#print axioms add_mono
#print axioms sub_mono
#print axioms mul_mono
#print axioms div_mono
#print axioms rem_mono
#print axioms sdiv_mono
#print axioms srem_mono
#print axioms shl_mono
#print axioms shr_mono
#print axioms ashr_mono
#print axioms pow_mono
#print axioms spow_mono
#print axioms pos_mono
#print axioms neg_mono
#print axioms vmerge_mono
#print axioms concat_mono
#print axioms ternary_mono
#print axioms resizeSigned_mono
#print axioms lt_mono
#print axioms le_mono
#print axioms gt_mono
#print axioms ge_mono
#print axioms slt_mono
#print axioms sge_mono
#print axioms eqLogical_mono
#print axioms neLogical_mono
#print axioms land_mono
#print axioms lor_mono
#print axioms lnot_mono
#print axioms truthy_mono
#print axioms redOr_mono
#print axioms redAnd_mono
#print axioms redXor_mono
#print axioms eqCase_not_mono
#print axioms eqCase_cex
#print axioms neCase_not_mono
#print axioms eqWildcard_not_mono
#print axioms eqWildcard_cex
#print axioms neWildcard_not_mono
#print axioms condTrue_not_mono
#print axioms condTrue_cex
#print axioms casez_not_mono
#print axioms casex_not_mono
#print axioms casex_cex
#print axioms isKnownZero_not_mono
#print axioms allKnown_not_mono
#print axioms toTwoState_not_mono
#print axioms vand_mono_xz
#print axioms add_mono_xz
#print axioms eqLogical_mono_xz
#print axioms ternary_mono_xz
#print axioms shl_mono_xz

end X9
