import tests.arbiter.negative.Refute

/-!
# Task `arbiter`: kernel refutations of generated mutants of the reference (untrusted, kernel-checked; 2026-11-07)

Nothing here is part of the trusted base. `tests/mutate.py` generates the mutants of
`tasks/arbiter/reference/rr_mask.sv` from Slang's syntax tree, and `tests/arbiter/mutants/classify.py`
sorts them: killed by the task's checks, proved equivalent to the reference, or a survivor
(`tests/arbiter/mutants/MANIFEST.json`). This file refutes a SAMPLE of the killed ones by the statement
itself, each by ONE run that the kernel evaluates (`decide +kernel`), in the style of `Refute.lean`
(whose plumbing it reuses): at `N = 2`, `K = 1` (one of them at `N = 4`, `K = 3`: it is equivalent to the
reference at `N ≤ 3`), from the all-zero power-up state, on one known stimulus.

Each mutant's source is in `tests/arbiter/mutants/<id>.sv` (the generator's output under a three-line
header); its hand-built twin `<id>D` is the reference's twin `refD` with the one mutated node changed, and
is checked equal to the design `load_sv` loads, at `N = 2` (and `4`) and `N = 8` (`#guard reprStr …`: the compiled
evaluator compares the two printed designs; the kernel does not reduce the generate expansion). The
reference's own twin is checked the same way, so each twin differs from a checked reference in one node.

| mutant | operator | edit (rr_mask.sv) | clause | refutation |
|---|---|---|---|---|
| m061 | RST | the reset gives `gnt <= '1` | G0: the reset snapshot shows `gnt = 11` | `m061_refuted` |
| m032 | BOR | `mreq & (~mreq + 1'b1)` becomes `mreq \| (~mreq + 1'b1)` | G1: both clients request, both are granted | `m032_refuted` |
| m016 | SA1 | `mreq = req & mask` reads `req` as `'1` | G2: nobody requests, client 0 is granted | `m016_refuted` |
| m056 | NEG | `if (rst)` becomes `if (!(rst))` | G3: client 0 requests alone, nobody is granted | `m056_refuted` |
| m089 | DEL | the mask update `mask <= ~((pick << 1) - 1'b1)` deleted | G4: the mask stays all ones, client 1 starves | `m089_refuted` |
| m102 | CRP (shift) | `pick << 1` becomes `pick << 2` | G4: at `N = 2` the mask clears, client 1 starves | `m102_refuted` |
| m040 | UOR | `~mreq + 1'b1` becomes `-mreq + 1'b1` | G3: client 0 is the only masked requester, nobody is granted | `m040_refuted` |
| m099 | OSW | `pick << 1` becomes `1 << pick` | G4 at `N = 4` (`K = 3`): client 3 requests four times, is never granted | `m099_refuted` |

`m099` is the one whose kill depends on `N`: `1 << pick` equals `pick << 1` for the one-hot picks `1` and
`2`, so the mutant is EQUIVALENT to the reference at `N = 1, 2, 3` (proved, the manifest) and wrong from
`N = 4`. All eight are killed by the simulation statement (`tests/arbiter/sim.py`) at the refutation's `N`
and rejected by `check.py --unproved` at `postsynth` (the manifest records the clause and the point).
-/

namespace SvGolf.Tasks.Arbiter.Mutants

open LeanModels.Sv SvGolf SvGolf.Tasks.Arbiter.Refute

/-! ## The reference's twin, with the parts a mutant changes as arguments -/

/-- The declarations of `rr_mask.sv`: the ports, then `mask`, `mreq`, `pick`. -/
def rrDecls (N : Nat) : Array Decl :=
  declsN N ++ #[{ name := "mask", width := N }, { name := "mreq", width := N }, { name := "pick", width := N }]

/-- `mreq = req & mask`. -/
def mreqRef : Expr2 := .binary .and (.ident "req") (.ident "mask")

/-- `pick = (mreq != '0) ? <masked> : lowbit(req)`. -/
def pickOf (N : Nat) (masked : Expr2) : Expr2 :=
  .ternary (.binary .ne (.ident "mreq") (.lit (zw N))) masked (lowbit N (.ident "req"))

/-- The reference's pick: the lowest masked requester, else the lowest requester. -/
def pickRef (N : Nat) : Expr2 := pickOf N (lowbit N (.ident "mreq"))

/-- The reset branch: `gnt <= '0; mask <= '1;`. -/
def rstRef (N : Nat) : Array Stmt2 :=
  #[.nbaAssign (.ident "gnt") (.lit (zw N)), .nbaAssign (.ident "mask") (.lit (ow N))]

/-- `~((pick << k) - 1'b1)`: the thermometer above the pick (`k = 1`). -/
def thermo (N k : Nat) : Expr2 :=
  .unary .bnot (.binary .sub (.binary (.shl false) (.ident "pick") (.lit (LVec.ofInt 32 k))) (.resize N (.lit b1)))

/-- The else branch: `gnt <= pick; if (pick != '0) <upd>`. -/
def elseOf (N : Nat) (upd : Stmt2) : Array Stmt2 :=
  #[.nbaAssign (.ident "gnt") (.ident "pick"), .ifStmt (.binary .ne (.ident "pick") (.lit (zw N))) upd none]

/-- The reference's else branch: the mask becomes the thermometer above the pick. -/
def elseRef (N : Nat) : Array Stmt2 := elseOf N (.nbaAssign (.ident "mask") (thermo N 1))

/-- The design with the given parts: one `always_comb` (`mreq`, then `pick`) and one `always_ff`
(`if (<cond>) <reset branch> else <else branch>`). -/
def rrWith (N : Nat) (mreqE pickE cond : Expr2) (rstB elseB : Array Stmt2) : Design2 where
  name := "arbiter"
  decls := rrDecls N
  processes := #[
    .alwaysComb (.block #[.blockingAssign (.ident "mreq") mreqE, .blockingAssign (.ident "pick") pickE]),
    .alwaysFF "clk" (.block #[.ifStmt cond (.block rstB) (some (.block elseB))])]

/-- The reference `rr_mask.sv`. -/
def refD (N : Nat) : Design2 := rrWith N mreqRef (pickRef N) (.ident "rst") (rstRef N) (elseRef N)

/-! ## The six mutants (one node each) -/

/-- m061 (RST): the reset gives `gnt <= '1`. -/
def m061D (N : Nat) : Design2 :=
  rrWith N mreqRef (pickRef N) (.ident "rst")
    #[.nbaAssign (.ident "gnt") (.lit (ow N)), .nbaAssign (.ident "mask") (.lit (ow N))] (elseRef N)

/-- m032 (BOR): the masked pick `mreq | (~mreq + 1'b1)`. -/
def m032D (N : Nat) : Design2 :=
  rrWith N mreqRef
    (pickOf N (.binary .or (.ident "mreq") (.binary .add (.unary .bnot (.ident "mreq")) (.resize N (.lit b1)))))
    (.ident "rst") (rstRef N) (elseRef N)

/-- m016 (SA1): `mreq = '1 & mask`. -/
def m016D (N : Nat) : Design2 :=
  rrWith N (.binary .and (.lit (ow N)) (.ident "mask")) (pickRef N) (.ident "rst") (rstRef N) (elseRef N)

/-- m056 (NEG): `if (!(rst))`. -/
def m056D (N : Nat) : Design2 :=
  rrWith N mreqRef (pickRef N) (.unary .lnot (.ident "rst")) (rstRef N) (elseRef N)

/-- m089 (DEL): `if (pick != '0) ;` (the loader reads the null statement as an empty block). -/
def m089D (N : Nat) : Design2 :=
  rrWith N mreqRef (pickRef N) (.ident "rst") (rstRef N) (elseOf N (.block #[]))

/-- m102 (CRP, the shift amount): `mask <= ~((pick << 2) - 1'b1)`. -/
def m102D (N : Nat) : Design2 :=
  rrWith N mreqRef (pickRef N) (.ident "rst") (rstRef N) (elseOf N (.nbaAssign (.ident "mask") (thermo N 2)))

/-- m040 (UOR): the masked pick `mreq & (-mreq + 1'b1)`. -/
def m040D (N : Nat) : Design2 :=
  rrWith N mreqRef
    (pickOf N (.binary .and (.ident "mreq") (.binary .add (.unary .neg (.ident "mreq")) (.resize N (.lit b1)))))
    (.ident "rst") (rstRef N) (elseRef N)

/-- m099 (OSW): `mask <= ~((1 << pick) - 1'b1)`; the 32-bit `1` makes the loader size the expression at 32
bits and truncate it to `N` (`resize`). -/
def m099D (N : Nat) : Design2 :=
  rrWith N mreqRef (pickRef N) (.ident "rst") (rstRef N)
    (elseOf N (.nbaAssign (.ident "mask") (.resize N (.unary .bnot (.binary .sub
      (.binary (.shl false) (.lit (LVec.ofInt 32 1)) (.ident "pick")) (.resize 32 (.lit b1)))))))

load_sv refL from "tasks/arbiter/reference/rr_mask.sv"
load_sv m061L from "tests/arbiter/mutants/m061.sv"
load_sv m032L from "tests/arbiter/mutants/m032.sv"
load_sv m016L from "tests/arbiter/mutants/m016.sv"
load_sv m056L from "tests/arbiter/mutants/m056.sv"
load_sv m089L from "tests/arbiter/mutants/m089.sv"
load_sv m102L from "tests/arbiter/mutants/m102.sv"
load_sv m040L from "tests/arbiter/mutants/m040.sv"
load_sv m099L from "tests/arbiter/mutants/m099.sv"

-- the hand-built twins are the loaded designs (at the refutations' point and the scoring point)
#guard reprStr (refL.sem 2) == reprStr (refD 2)
#guard reprStr (refL.sem 8) == reprStr (refD 8)
#guard reprStr (m061L.sem 2) == reprStr (m061D 2)
#guard reprStr (m061L.sem 8) == reprStr (m061D 8)
#guard reprStr (m032L.sem 2) == reprStr (m032D 2)
#guard reprStr (m032L.sem 8) == reprStr (m032D 8)
#guard reprStr (m016L.sem 2) == reprStr (m016D 2)
#guard reprStr (m016L.sem 8) == reprStr (m016D 8)
#guard reprStr (m056L.sem 2) == reprStr (m056D 2)
#guard reprStr (m056L.sem 8) == reprStr (m056D 8)
#guard reprStr (m089L.sem 2) == reprStr (m089D 2)
#guard reprStr (m089L.sem 8) == reprStr (m089D 8)
#guard reprStr (m102L.sem 2) == reprStr (m102D 2)
#guard reprStr (m102L.sem 8) == reprStr (m102D 8)
#guard reprStr (m040L.sem 2) == reprStr (m040D 2)
#guard reprStr (m040L.sem 8) == reprStr (m040D 8)
#guard reprStr (m099L.sem 2) == reprStr (m099D 2)
#guard reprStr (m099L.sem 4) == reprStr (m099D 4)
#guard reprStr (m099L.sem 8) == reprStr (m099D 8)

/-! ## The refutations (`N = 2`, `K = 1`, from the all-zero power-up state) -/

/-- **m061 is rejected** (G0): a reset, then nobody requests; the reset snapshot shows `gnt = 11`. -/
theorem m061_refuted : ¬ Statement m061D := fun hs =>
  not_follows_of_run (N := 2) (K := 1) (d := m061D 2) (st0 := zeros (m061D 2)) (stim := stimNone)
    (tr := trOf (m061D 2) stimNone) (c1 := 1) (x0 := (0#2, ())) (xs := [(0#2, ())])
    (powerUp_zeros _) (by decide +kernel) (by decide +kernel)
    (released_of (by decide) (by decide +kernel) (by decide +kernel)) (insAt_of (by decide +kernel))
    (fun y0 ys hl hs hg => by
      have hl' : ys.length = 1 := hl
      have hv := showsAt_eq (vs := [3#2, 0#2]) (by show ys.length + 1 = 2; omega) hs
        (by decide +kernel)
      obtain ⟨h0, h1⟩ := List.cons.inj hv
      subst h0 h1
      exact absurd (show (3#2 : BitVec 2) = 0#2 from hg.1) (by decide))
    (hs 2 n2_inRange).2.2.1

/-- **m032 is rejected** (G1): a reset, then both clients request; both are granted. -/
theorem m032_refuted : ¬ Statement m032D := fun hs =>
  not_follows_of_run (N := 2) (K := 1) (d := m032D 2) (st0 := zeros (m032D 2)) (stim := stimBoth)
    (tr := trOf (m032D 2) stimBoth) (c1 := 1) (x0 := (0#2, ())) (xs := [(3#2, ())])
    (powerUp_zeros _) (by decide +kernel) (by decide +kernel)
    (released_of (by decide) (by decide +kernel) (by decide +kernel)) (insAt_of (by decide +kernel))
    (fun y0 ys hl hs hg => by
      have hl' : ys.length = 1 := hl
      have hv := showsAt_eq (vs := [0#2, 3#2]) (by show ys.length + 1 = 2; omega) hs
        (by decide +kernel)
      obtain ⟨h0, h1⟩ := List.cons.inj hv
      subst h0 h1
      exact absurd (grants_iff.1 (hg.2.1 0 _ _ rfl rfl)) (by decide))
    (hs 2 n2_inRange).2.2.1

/-- **m016 is rejected** (G2): a reset, then nobody requests; client 0 is granted. -/
theorem m016_refuted : ¬ Statement m016D := fun hs =>
  not_follows_of_run (N := 2) (K := 1) (d := m016D 2) (st0 := zeros (m016D 2)) (stim := stimNone)
    (tr := trOf (m016D 2) stimNone) (c1 := 1) (x0 := (0#2, ())) (xs := [(0#2, ())])
    (powerUp_zeros _) (by decide +kernel) (by decide +kernel)
    (released_of (by decide) (by decide +kernel) (by decide +kernel)) (insAt_of (by decide +kernel))
    (fun y0 ys hl hs hg => by
      have hl' : ys.length = 1 := hl
      have hv := showsAt_eq (vs := [0#2, 1#2]) (by show ys.length + 1 = 2; omega) hs
        (by decide +kernel)
      obtain ⟨h0, h1⟩ := List.cons.inj hv
      subst h0 h1
      exact absurd (grants_iff.1 (hg.2.1 0 _ _ rfl rfl)) (by decide))
    (hs 2 n2_inRange).2.2.1

/-- **m056 is rejected** (G3): a reset (the negated condition takes the else branch, which grants
nobody), then client 0 requests alone (the negated condition resets): nobody is granted. -/
theorem m056_refuted : ¬ Statement m056D := fun hs =>
  not_follows_of_run (N := 2) (K := 1) (d := m056D 2) (st0 := zeros (m056D 2)) (stim := stimLone)
    (tr := trOf (m056D 2) stimLone) (c1 := 1) (x0 := (0#2, ())) (xs := [(1#2, ())])
    (powerUp_zeros _) (by decide +kernel) (by decide +kernel)
    (released_of (by decide) (by decide +kernel) (by decide +kernel)) (insAt_of (by decide +kernel))
    (fun y0 ys hl hs hg => by
      have hl' : ys.length = 1 := hl
      have hv := showsAt_eq (vs := [0#2, 0#2]) (by show ys.length + 1 = 2; omega) hs
        (by decide +kernel)
      obtain ⟨h0, h1⟩ := List.cons.inj hv
      subst h0 h1
      exact absurd (grants_iff.1 (hg.2.1 0 _ _ rfl rfl)) (by decide))
    (hs 2 n2_inRange).2.2.1

/-- **m089 is rejected** (G4 with `K = 1`): the mask stays all ones, so both clients requesting twice
are answered `01, 01`, and client 1 starves. -/
theorem m089_refuted : ¬ Statement m089D :=
  starves_refuted (sem := m089D) (zeros (m089D 2)) (powerUp_zeros _) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

/-- **m102 is rejected** (G4 with `K = 1`): at `N = 2`, `pick << 2` is `0`, the mask clears after the
first grant, and the lowest requester wins again: `01, 01`, client 1 starves. -/
theorem m102_refuted : ¬ Statement m102D :=
  starves_refuted (sem := m102D) (zeros (m102D 2)) (powerUp_zeros _) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

/-- **m040 is rejected** (G3): a reset, then client 0 requests alone; it is the only masked requester, and
`1 & (-1 + 1) = 0`: nobody is granted. -/
theorem m040_refuted : ¬ Statement m040D := fun hs =>
  not_follows_of_run (N := 2) (K := 1) (d := m040D 2) (st0 := zeros (m040D 2)) (stim := stimLone)
    (tr := trOf (m040D 2) stimLone) (c1 := 1) (x0 := (0#2, ())) (xs := [(1#2, ())])
    (powerUp_zeros _) (by decide +kernel) (by decide +kernel)
    (released_of (by decide) (by decide +kernel) (by decide +kernel)) (insAt_of (by decide +kernel))
    (fun y0 ys hl hs hg => by
      have hl' : ys.length = 1 := hl
      have hv := showsAt_eq (vs := [0#2, 0#2]) (by show ys.length + 1 = 2; omega) hs
        (by decide +kernel)
      obtain ⟨h0, h1⟩ := List.cons.inj hv
      subst h0 h1
      exact absurd (grants_iff.1 (hg.2.1 0 _ _ rfl rfl)) (by decide))
    (hs 2 n2_inRange).2.2.1

theorem n4_inRange : task.inRange 4 := by simp [task]

/-- A reset, then the requests `1100, 1001, 1111, 1111` at `N = 4` (ABC's counterexample, `classify.py`). -/
def stim099 : List SvState := [entry 4 1 0, entry 4 0 12, entry 4 0 9, entry 4 0 15, entry 4 0 15]

/-- **m099 is rejected** (G4 at `N = 4`, `K = 3`): client 3 requests at the four entries of the segment
and the snapshots grant `0100, 0001, 0010, 0100`: after the grant to client 2 the mask is
`~((1 << 4) - 1)`, which is `0000` at four bits, where the reference's is `1000`. -/
theorem m099_refuted : ¬ Statement m099D := fun hs =>
  not_follows_of_run (N := 4) (K := 3) (d := m099D 4) (st0 := zeros (m099D 4)) (stim := stim099)
    (tr := trOf (m099D 4) stim099) (c1 := 1) (x0 := (0#4, ()))
    (xs := [(12#4, ()), (9#4, ()), (15#4, ()), (15#4, ())])
    (powerUp_zeros _) (by decide +kernel) (by decide +kernel)
    (released_of (by decide) (by decide +kernel) (by decide +kernel)) (insAt_of (by decide +kernel))
    (fun y0 ys hl hs hg => by
      have hl' : ys.length = 4 := hl
      have hv := showsAt_eq (vs := [0#4, 4#4, 1#4, 2#4, 4#4]) (by show ys.length + 1 = 5; omega) hs
        (by decide +kernel)
      obtain ⟨h0, h1⟩ := List.cons.inj hv
      subst h0 h1
      obtain ⟨i, y, hi, hy, hg1⟩ := hg.2.2 (⟨3, by decide⟩ : Fin 4) 0 (by decide) (fun i x hi hx => by
        have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
        rcases this with rfl | rfl | rfl | rfl <;>
          (have hx' := Option.some.inj hx; subst hx'; exact rfl))
      have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases this with rfl | rfl | rfl | rfl <;>
        (have hy' := Option.some.inj hy; subst hy'; exact Bool.false_ne_true hg1))
    (hs 4 n4_inRange).2.2.1

/-! ## Executable reading (`#guard`, not a proof): the reference passes where each mutant fails -/

#guard passes 2 (refD 2) workload
#guard passes 2 (refD 2) [3, 3, 3, 3]
#guard !passes 2 (m061D 2) workload
#guard !passes 2 (m032D 2) workload
#guard !passes 2 (m016D 2) workload
#guard !passes 2 (m056D 2) workload
#guard !passes 2 (m089D 2) workload
#guard !passes 2 (m102D 2) workload
-- m040 passes `workload`: its failing input is client 0 alone while the mask is all ones (after a reset)
#guard passes 2 (m040D 2) workload
#guard !passes 2 (m040D 2) [1, 3, 3]
-- m099 is the reference at N = 2 (it passes there) and fails at N = 4
#guard passes 2 (m099D 2) workload
#guard passes 4 (refD 4) [12, 9, 15, 15]
#guard !passes 4 (m099D 4) [12, 9, 15, 15]

#print axioms m061_refuted
#print axioms m032_refuted
#print axioms m016_refuted
#print axioms m056_refuted
#print axioms m089_refuted
#print axioms m102_refuted
#print axioms m040_refuted
#print axioms m099_refuted

end SvGolf.Tasks.Arbiter.Mutants
