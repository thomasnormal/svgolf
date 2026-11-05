import Submission.Design
import SvGolf.Comb
import LeanModels.Sv.Gen2
import LeanModels.Sv.Hier2Gen
import LeanModels.Sv.Known2

/-!
# Reference solution for task `add` (N-bit adder with carry): the proof

This is a submission file like any player's `Solution.lean`. The checker
generates the module `Submission.Design`, which loads the player's envelope as
`Submission.design` and names the statement to prove `Submission.Goal`
(`SvGolf.Tasks.Add.Statement Submission.design.sem`). This file proves

    theorem Submission.solution : Submission.Goal

for EVERY `N ≥ 1`: `N` stays a variable from the envelope to the conclusion,
nothing is unrolled at a fixed width and nothing is bit-blasted. The design
(`reference/add_n.sv`) is a ripple-carry adder written with one `generate for`
over the bit index.

The proof is lean-surfaces' `Examples/system-verilog/ripple_add` acceptance
proof (`gen.lean` + `proof.lean`), COPIED here with `ripple_add` renamed to
`design` (svGolf never imports `Examples`), plus the last step that connects
its settled-state lemma to the task's `fn`.

## Route

1. **The design at symbolic `N`** (`ripple_sem_processes`, `ripple_sem_decls`):
   `instantiate2` split into its stages by `PDesign.instantiate2_of_ok`; the
   generate-for expanded by `GenItem.expand2_genFor_ascending_processes`; the
   one-driver guard of `name.sem` discharged for every `N`
   (`ripple_driversOk`). The instantiated design is

       0:      c[0]   = cin
       1:      cout   = c[N]
       2i+2:   s[i]   = a[i] ^ b[i] ^ c[i]                       (i < N)
       2i+3:   c[i+1] = (a[i] & b[i]) | (c[i] & (a[i] ^ b[i]))   (i < N)

2. **The comb profile and acyclicity** (`ripple_comb`, `ripple_acyclic`, rank
   certificate `rippleRank`: carry-in 0, bit `i`'s cells `i + 1`, carry-out
   `N + 1`).
3. **The settled state** (`ripple_settled`): in every solution of the
   design's equations, the carry chain holds core's `BitVec.carry` window by
   window (induction on the bit index, one process equation per step), so `s`
   is `x + y + ci` and `cout` is `2^N ≤ x + y + ci`.
4. **The statement** (`solution`): `CombTask.satisfiedAt_of_comb`
   (`SvGolf/Comb.lean`) reduces it to the interface and step 3;
   `sum_eq_ofNat` and `carry_eq_ofNat` turn the `BitVec` sum and carry into
   the task's `Nat` form.

## Adapting it to another design

Steps 1a-1e pin THIS envelope: `ripple_generates` and `ripple_static_source`
are `rfl` statements of its generate loop and static assigns (the loop's
`resolved_count`, `some 16`, is the slang count at the default `N = 16`, so
even changing the default changes it), and the instantiation lemmas follow
from them. A different design restates those and re-proves steps 2-3; the
reduction in step 4 and its `Nat` bridges carry over unchanged.
-/

namespace Submission

open LeanModels.Sv SvGolf

/-! ## 1a. The envelope's shape (pinned by `rfl`) -/

/-- The sum-bit template `assign s[i] = a[i] ^ b[i] ^ c[i];`. -/
def sumT : PProcess :=
  .assignL (.bitSel "s" (.genvarRef "i"))
    (.binary (.m0 .xor)
      (.binary (.m0 .xor) (.bitSel (.ident "a") (.genvarRef "i"))
        (.bitSel (.ident "b") (.genvarRef "i")))
      (.bitSel (.ident "c") (.genvarRef "i")))

/-- The carry template `assign c[i+1] = (a[i] & b[i]) | (c[i] & (a[i] ^ b[i]));`. -/
def carryT : PProcess :=
  .assignL (.bitSel "c" (.binary (.m0 .add) (.genvarRef "i") (.int 1)))
    (.binary (.m0 .or)
      (.binary (.m0 .and) (.bitSel (.ident "a") (.genvarRef "i"))
        (.bitSel (.ident "b") (.genvarRef "i")))
      (.binary (.m0 .and) (.bitSel (.ident "c") (.genvarRef "i"))
        (.binary (.m0 .xor) (.bitSel (.ident "a") (.genvarRef "i"))
          (.bitSel (.ident "b") (.genvarRef "i")))))

/-- The one generate item: `for (i = 0; i s< N; i++)` over the two
templates (`resolved_count` 4 is the defaults metadata). -/
theorem ripple_generates :
    design.pdesign.generates =
      [.genFor (some "g_bit") "i" (.int 0) (.binary .slt (.genvarRef "i") (.paramRef "N" none))
        (.unary .inc (.genvarRef "i")) (some 16) ([sumT, carryT].map GenItem.process)] := rfl

/-- The two static continuous assigns, in source order. Their labels are
static (`0`, `N`) over the parameter-dependent `[N:0]`, so both selects are
`ArraySel` paths, normalized against the declared range at every point
(2026-10-28; the legacy `BitSel` read a label as an offset from bit 0). -/
theorem ripple_static_source :
    design.pdesign.processes =
      [.assignL (.arrayElem "c" [.int 0]) (.ident "cin"),
       .assign "cout" (.arrayElem "c" [.paramRef "N" none])] := rfl

/-! ## 1b. The instantiated vocabulary -/

/-- `c[0] = cin`. -/
def cinProc : Process2 := .assign (.slice "c" 0 1) (.ident "cin")

/-- `cout = c[N]`. -/
def coutProc (N : Nat) : Process2 := .assign (.ident "cout") (.slice (.ident "c") N 1)

/-- `s[i] = a[i] ^ b[i] ^ c[i]` at bit `i`. -/
def sumProc (i : Nat) : Process2 :=
  .assign (.slice "s" i 1)
    (.binary .xor (.binary .xor (.slice (.ident "a") i 1) (.slice (.ident "b") i 1))
      (.slice (.ident "c") i 1))

/-- `c[i+1] = (a[i] & b[i]) | (c[i] & (a[i] ^ b[i]))` at bit `i`. -/
def carryProc (i : Nat) : Process2 :=
  .assign (.slice "c" (i + 1) 1)
    (.binary .or (.binary .and (.slice (.ident "a") i 1) (.slice (.ident "b") i 1))
      (.binary .and (.slice (.ident "c") i 1)
        (.binary .xor (.slice (.ident "a") i 1) (.slice (.ident "b") i 1))))

/-- The whole instantiated process list, in `instantiate2`'s order: static
processes, then the generate family bit by bit (sum before carry). -/
def rippleProcs (N : Nat) : List Process2 :=
  cinProc :: coutProc N :: (List.range N).flatMap fun i => [sumProc i, carryProc i]

/-- The instantiated declarations (ports first, then `c`), for `N ≥ 1`. -/
def rippleDecls (N : Nat) : List Decl :=
  [{ name := "a", width := N, isInput := true },
   { name := "b", width := N, isInput := true },
   { name := "cin", width := 1, isInput := true },
   { name := "s", width := N, isOutput := true },
   { name := "cout", width := 1, isOutput := true },
   { name := "c", width := N + 1 }]

/-! ## 1c. The stages of `instantiate2` at symbolic `N` -/

/-- The declaration scope: `N` bound, its declared type `int` 32 bits. -/
def rippleScope (N : Int) : IEnv := { vals := [("N", N)], pwidths := [("N", 32)] }

/-- The parameter environment: the declaration scope plus the packed-array
geometry table evaluated in it (`dimTable` — every `instantiate2`
environment carries it). -/
def rippleEnv (N : Int) : IEnv :=
  { rippleScope N with dims := dimTable (rippleScope N) design.pdesign.decls }

/-- Declarations at raw widths: `wv` = `|N-1| + 1` (the `[N-1:0]` ports),
`wc` = `|N| + 1` (`c[N:0]`) — the width rule is total in `N`, which is why
the process-list theorems below need no `1 ≤ N`. -/
def rippleDeclsRaw (wv wc : Nat) : List Decl :=
  [{ name := "a", width := wv, isInput := true },
   { name := "b", width := wv, isInput := true },
   { name := "cin", width := 1, isInput := true },
   { name := "s", width := wv, isOutput := true },
   { name := "cout", width := 1, isOutput := true },
   { name := "c", width := wc }]

/-- Every declaration is 1-D: element width 1. -/
def rippleElems : List (String × Nat) :=
  [("a", 1), ("b", 1), ("cin", 1), ("s", 1), ("cout", 1), ("c", 1)]

/-- The parameter stage binds `N` (by `rfl`). -/
theorem ripple_paramEnv (N : Int) : design.pdesign.paramEnv2 [N] = .ok (rippleEnv N) := by
  rfl

/-- The declaration stage at symbolic `N`: the raw widths `|N-1| + 1` and
`|N| + 1`. -/
theorem ripple_decls (N : Int) :
    buildDecls (rippleEnv N) design.pdesign.decls =
      .ok (rippleDeclsRaw ((N - 1).natAbs + 1) (N.natAbs + 1)) := by
  simp [design.pdesign, buildDecls, instDecl, PType.width_packed_cons, PDim.width, evalInt,
    rippleEnv, rippleScope, List.lookup, rippleDeclsRaw, Gen2.except_ok_bind]

/-- The element-width stage: every declaration has element width 1. -/
theorem ripple_elems (N : Int) :
    buildElems (rippleEnv N) design.pdesign.decls = .ok rippleElems := by
  simp [design.pdesign, buildElems, PType.width_packed_cons, PDim.width, evalInt, rippleEnv,
    rippleScope, List.lookup, rippleElems, Gen2.except_ok_bind]

/-- The sum template at a `Nat`-cast genvar (any surrounding environment:
the template reads only element widths and the genvar). -/
theorem ripple_sum_inst (env : IEnv) (i : Nat) :
    instProcess2 (env.bindVal "i" i) rippleElems sumT = sumProc i := by
  sv2_inst_simp [rippleElems, sumT, sumProc]

/-- The carry template at a `Nat`-cast genvar (`c[i+1]`: offset `i + 1`). -/
theorem ripple_carry_inst (env : IEnv) (i : Nat) :
    instProcess2 (env.bindVal "i" i) rippleElems carryT = carryProc i := by
  sv2_inst_simp [rippleElems, carryT, carryProc]

/-- The static processes (`cout = c[N]` reads the PARAMETER-indexed bit). -/
theorem ripple_static (N : Nat) (wv wc : Nat) :
    design.pdesign.processes.map
        (instProcess2 ((rippleEnv N).withDecls (rippleDeclsRaw wv wc)) rippleElems) =
      [cinProc, coutProc N] := by
  sv2_inst_simp [design.pdesign, rippleEnv, rippleScope, rippleDeclsRaw, rippleElems, cinProc,
    coutProc, dimTable, dimTableStep, PType.width_packed_cons, PDim.width, Int.lt_add_one_iff]

/-- The generate expansion at the surface fuel: the bit-indexed family. -/
theorem ripple_gens (N : Nat) (wv wc : Nat) :
    expandList2 ((rippleEnv N).withDecls (rippleDeclsRaw wv wc)) rippleElems
      (PDesign.surfaceFuel [(N : Int)]) design.pdesign.generates =
      .ok ((List.range N).flatMap fun i => [sumProc i, carryProc i]) := by
  rw [ripple_generates]
  apply expandList2_singleton_ok
  rw [GenItem.expand2_genFor_ascending_processes (N := (N : Int)) (evalInt_int 0)
    (fun i => by simp [rippleEnv, rippleScope, List.lookup])
    (fun i => by simp [evalInt, rippleEnv, rippleScope, List.lookup])
    (by
      have := Nat.le_mul_self (N + 2)
      simp [PDesign.surfaceFuel]
      omega)]
  simp only [Int.sub_zero, Int.toNat_natCast, intRange_zero, List.flatMap_map, List.map_cons,
    List.map_nil, ripple_sum_inst, ripple_carry_inst]

/-- **`instantiate2` at symbolic `N`**: succeeds, and is the assembled
design of the stages above. -/
theorem ripple_instantiate2 (N : Nat) :
    design.pdesign.instantiate2 [(N : Int)] (PDesign.surfaceFuel [(N : Int)]) =
      .ok (design.pdesign.assemble2 (rippleEnv N)
        (rippleDeclsRaw (((N : Int) - 1).natAbs + 1) ((N : Int).natAbs + 1)) rippleElems
        ((List.range N).flatMap fun i => [sumProc i, carryProc i])) :=
  PDesign.instantiate2_of_ok rfl (ripple_paramEnv N) (ripple_decls N) (ripple_elems N)
    (ripple_gens N _ _)

/-! ## 1d. The instantiated design, for every `N` -/

/-- **The instantiated process list, for every `N`** (no unrolling): `c[0] =
cin`, `cout = c[N]`, then `s[i]`, `c[i+1]` for each `i < N`. -/
theorem ripple_processes (N : Nat) :
    (design.pdesign.instantiateD2 [(N : Int)]).processes.toList = rippleProcs N := by
  rw [PDesign.instantiateD2_of_ok (ripple_instantiate2 N), PDesign.assemble2_processes,
    ripple_static]
  simp [rippleProcs, design.pdesign]

/-- **Membership characterization, both directions**:
a process of the instantiated adder is the carry-in, the carry-out, or the
sum/carry cell of some bit `i < N`. -/
theorem mem_ripple_processes (N : Nat) (p : Process2) :
    p ∈ (design.pdesign.instantiateD2 [(N : Int)]).processes.toList ↔
      p = cinProc ∨ p = coutProc N ∨ ∃ i < N, p = sumProc i ∨ p = carryProc i := by
  rw [ripple_processes]
  simp [rippleProcs]

/-- The process count: `2N + 2`. -/
theorem ripple_processes_length (N : Nat) :
    (design.pdesign.instantiateD2 [(N : Int)]).processes.toList.length = 2 * N + 2 := by
  rw [ripple_processes]
  simp only [rippleProcs, List.length_cons, List.length_flatMap, List.length_nil,
    List.map_const', List.sum_replicate_nat, List.length_range]
  omega

/-- **The instantiated declarations** for `N ≥ 1`: `a`, `b`, `s` are `N`
bits, `cin`/`cout` 1 bit, the carry chain `c` is `N + 1` bits. -/
theorem ripple_decls_instantiated (N : Nat) (hN : 1 ≤ N) :
    (design.pdesign.instantiateD2 [(N : Int)]).decls.toList = rippleDecls N := by
  rw [PDesign.instantiateD2_of_ok (ripple_instantiate2 N), PDesign.assemble2_decls]
  have hv : ((N : Int) - 1).natAbs + 1 = N := by omega
  have hc : (N : Int).natAbs = N := Int.natAbs_natCast N
  rw [hv, hc]
  rfl

/-! ## 1e. The one-driver rule, for every `N`

`design.sem N` is `instantiateGD2`: the instantiated design under the
one-driver rule (`Hier2.lean`, "Drivers" — a flat top is checked at every
parameter point since 2026-10-28). The rule holds for every `N`, by the
process-list recipe of `Hier2Gen.lean`: compute the driver windows of
`rippleProcs N` (`ripple_driverWins`), split the generate family with
`pairwise_flatMap_range`, close each pair with `omega`. -/

/-- The envelope's declared names and input ports (parameter-free). -/
theorem ripple_declNames : design.pdesign.declNames = ["a", "b", "cin", "s", "cout", "c"] :=
  rfl

theorem ripple_inputNames_pd : design.pdesign.inputNames = ["a", "b", "cin"] := rfl

/-- The windows bit `i` drives: `s[i]` and `c[i+1]`. -/
def rippleWins (i : Nat) : List DrvWin := [("s", some (i, 1)), ("c", some (i + 1, 1))]

/-- The continuous-driver windows of the instantiated adder, for every `N`. -/
theorem ripple_driverWins (N : Nat) :
    driverWins ["a", "b", "cin", "s", "cout", "c"] (rippleProcs N) =
      [("c", some (0, 1)), ("cout", none)] ++ (List.range N).flatMap rippleWins := by
  have hs : ["a", "b", "cin", "s", "cout", "c"].contains "s" = true := by decide
  have hc : ["a", "b", "cin", "s", "cout", "c"].contains "c" = true := by decide
  have ho : ["a", "b", "cin", "s", "cout", "c"].contains "cout" = true := by decide
  simp only [rippleProcs, driverWins_cons, driverWins_nil, driverWins_flatMap, cinProc, coutProc,
    sumProc, carryProc, Process2.drvWins, Lhs2.drvWins, List.filter_cons, List.filter_nil, hs, hc,
    ho, ↓reduceIte, List.cons_append, List.nil_append, List.append_nil]
  rfl

/-- **The one-driver rule holds for every `N`**: no procedural process;
`c[0]`, the whole `cout`, and per bit `s[i]`, `c[i+1]` are pairwise
disjoint; none is an input port. -/
theorem ripple_driversOk (N : Nat) :
    driversOk design.pdesign.declNames design.pdesign.inputNames (rippleProcs N) = true := by
  rw [ripple_declNames, ripple_inputNames_pd]
  apply driversOk_of_continuous
  · rw [List.flatMap_eq_nil_iff]
    intro p hp
    simp only [rippleProcs, List.mem_cons, List.mem_flatMap, List.mem_range, List.not_mem_nil,
      or_false] at hp
    rcases hp with rfl | rfl | ⟨k, _, rfl | rfl⟩ <;> rfl
  · rw [ripple_driverWins, List.pairwise_append]
    refine ⟨by decide, pairwise_flatMap_range (fun k _ => ?_) (fun j k hjk _ a ha b hb => ?_), ?_⟩
    · simp [rippleWins]
    · simp only [rippleWins, List.mem_cons, List.not_mem_nil, or_false] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp [DrvWin.overlaps] <;> omega
    · intro a ha b hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      simp only [List.mem_flatMap, List.mem_range, rippleWins, List.mem_cons, List.not_mem_nil,
        or_false] at hb
      obtain ⟨k, _, hb⟩ := hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp [DrvWin.overlaps]
  · intro w hw
    rw [ripple_driverWins] at hw
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_flatMap,
      List.mem_range, rippleWins] at hw
    rcases hw with (rfl | rfl) | ⟨k, _, (rfl | rfl)⟩ <;> rfl

/-- **`design.sem N` is the instantiated design**, for every `N` (the
guard of `instantiateGD2` passes: `ripple_driversOk`). -/
theorem ripple_sem_eq (N : Nat) :
    design.sem N = design.pdesign.instantiateD2 [(N : Int)] := by
  show design.pdesign.instantiateGD2 [(N : Int)] = _
  apply PDesign.instantiateGD2_of_driversOk
  rw [ripple_processes]
  exact ripple_driversOk N

/-- The `load_design_sv2` family member `design.sem N` is the same
design (`Int.ofNat N` is the binder encoding of `(N : Int)`; the one-driver
guard passes, `ripple_sem_eq`). -/
theorem ripple_sem_processes (N : Nat) :
    (design.sem N).processes.toList = rippleProcs N := by
  rw [ripple_sem_eq]
  exact ripple_processes N

/-- `mem_ripple_processes` for the family member `design.sem N`. -/
theorem mem_ripple_sem_processes (N : Nat) (p : Process2) :
    p ∈ (design.sem N).processes.toList ↔
      p = cinProc ∨ p = coutProc N ∨ ∃ i < N, p = sumProc i ∨ p = carryProc i := by
  rw [ripple_sem_eq]
  exact mem_ripple_processes N p

/-- `ripple_decls_instantiated` for the family member `design.sem N`. -/
theorem ripple_sem_decls (N : Nat) (hN : 1 ≤ N) :
    (design.sem N).decls.toList = rippleDecls N := by
  rw [ripple_sem_eq]
  exact ripple_decls_instantiated N hN

/-! ## 2a. The process table -/

/-- Indexing the bit-interleaved family `[f 0, g 0, f 1, g 1, …]`: entry `m`
is `f (m / 2)` at even `m`, `g (m / 2)` at odd `m`, below `2N`. -/
theorem getElem?_flatMap_pair {α : Type} (N : Nat) : ∀ (f g : Nat → α) (m : Nat),
    ((List.range N).flatMap fun i => [f i, g i])[m]? =
      if m < 2 * N then some (if m % 2 = 0 then f (m / 2) else g (m / 2)) else none := by
  induction N with
  | zero => intro f g m; simp
  | succ N ih =>
    intro f g m
    rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
    match m with
    | 0 => simp
    | 1 => simp; omega
    | m + 2 =>
      rw [List.cons_append, List.cons_append, List.nil_append, List.getElem?_cons_succ,
        List.getElem?_cons_succ]
      rw [ih (fun i => f (i + 1)) (fun i => g (i + 1)) m]
      have h1 : (m + 2) / 2 = m / 2 + 1 := by omega
      have h2 : (m + 2) % 2 = m % 2 := by omega
      rw [h1, h2]
      by_cases h : m < 2 * N
      · have h' : m + 2 < 2 * (N + 1) := by omega
        simp only [h, h', if_true]
      · have h' : ¬ (m + 2 < 2 * (N + 1)) := by omega
        simp only [h, h', if_false]

/-- The process array of `design.sem N` is `rippleProcs N` (`ripple_sem_processes`). -/
theorem ripple_getElem? (N j : Nat) :
    (design.sem N).processes[j]? = (rippleProcs N)[j]? := by
  rw [← Array.getElem?_toList, ripple_sem_processes]

/-- **The process table, by index** (every `N`): carry-in at 0, carry-out at
1, then bit `i`'s sum cell at `2i + 2` and carry cell at `2i + 3`. -/
theorem ripple_proc {N j : Nat} {p : Process2} :
    (design.sem N).processes[j]? = some p ↔
      (j = 0 ∧ p = cinProc) ∨ (j = 1 ∧ p = coutProc N) ∨
      ∃ i < N, (j = 2 * i + 2 ∧ p = sumProc i) ∨ (j = 2 * i + 3 ∧ p = carryProc i) := by
  rw [ripple_getElem?]
  match j with
  | 0 => simp [rippleProcs, eq_comm]
  | 1 => simp [rippleProcs, eq_comm]
  | m + 2 =>
    simp only [rippleProcs, List.getElem?_cons_succ, getElem?_flatMap_pair]
    constructor
    · intro h
      by_cases hm : m < 2 * N
      · rw [if_pos hm] at h
        right; right
        refine ⟨m / 2, by omega, ?_⟩
        by_cases h2 : m % 2 = 0
        · rw [if_pos h2, Option.some.injEq] at h
          exact Or.inl ⟨by omega, h.symm⟩
        · rw [if_neg h2, Option.some.injEq] at h
          exact Or.inr ⟨by omega, h.symm⟩
      · rw [if_neg hm] at h
        cases h
    · rintro (⟨h, -⟩ | ⟨h, -⟩ | ⟨i, hi, ⟨h, rfl⟩ | ⟨h, rfl⟩⟩)
      · omega
      · omega
      · obtain rfl : m = 2 * i := by omega
        rw [if_pos (by omega), if_pos (by omega), Nat.mul_div_cancel_left _ (by omega)]
      · obtain rfl : m = 2 * i + 1 := by omega
        rw [if_pos (by omega), if_neg (by omega)]
        congr 2
        omega

/-- Process 0 is the carry-in `c[0] = cin`. -/
theorem ripple_proc_cin (N : Nat) : (design.sem N).processes[0]? = some cinProc :=
  ripple_proc.mpr (Or.inl ⟨rfl, rfl⟩)

/-- Process 1 is the carry-out `cout = c[N]`. -/
theorem ripple_proc_cout (N : Nat) : (design.sem N).processes[1]? = some (coutProc N) :=
  ripple_proc.mpr (Or.inr (Or.inl ⟨rfl, rfl⟩))

/-- Process `2i + 2` is bit `i`'s sum cell. -/
theorem ripple_proc_sum {N i : Nat} (hi : i < N) :
    (design.sem N).processes[2 * i + 2]? = some (sumProc i) :=
  ripple_proc.mpr (Or.inr (Or.inr ⟨i, hi, Or.inl ⟨rfl, rfl⟩⟩))

/-- Process `2i + 3` is bit `i`'s carry cell. -/
theorem ripple_proc_carry {N i : Nat} (hi : i < N) :
    (design.sem N).processes[2 * i + 3]? = some (carryProc i) :=
  ripple_proc.mpr (Or.inr (Or.inr ⟨i, hi, Or.inr ⟨rfl, rfl⟩⟩))

/-! ## 2b. Declarations, windows, driven signals (`1 ≤ N`) -/

section Decls

variable {N : Nat} (hN : 1 ≤ N)
include hN

/-- Declared widths are looked up in `rippleDecls N`. -/
theorem ripple_declWidth (n : String) :
    (design.sem N).declWidth n =
      ((rippleDecls N).find? fun dc => dc.name == n).map Decl.width := by
  simp only [Design2.declWidth, ripple_sem_decls N hN]

/-- `s` is `N` bits. -/
theorem ripple_declWidth_s : (design.sem N).declWidth "s" = some N := by
  simp [ripple_declWidth hN, rippleDecls]

/-- `cout` is 1 bit. -/
theorem ripple_declWidth_cout : (design.sem N).declWidth "cout" = some 1 := by
  simp [ripple_declWidth hN, rippleDecls]

/-- The carry chain `c` is `N + 1` bits. -/
theorem ripple_declWidth_c : (design.sem N).declWidth "c" = some (N + 1) := by
  simp [ripple_declWidth hN, rippleDecls]

/-- The input ports, in declaration order. -/
theorem ripple_inputNames : (design.sem N).inputNames.toList = ["a", "b", "cin"] := by
  simp [Design2.inputNames, ripple_sem_decls N hN, rippleDecls]

/-- **The write windows**: carry-in writes `c[0]`, carry-out the whole 1-bit
`cout`, bit `i`'s sum cell `s[i]` and its carry cell `c[i+1]`. -/
theorem ripple_writes {j : Nat} {wn : Win} : (design.sem N).Writes j wn ↔
    (j = 0 ∧ wn = ("c", 0, 1)) ∨ (j = 1 ∧ wn = ("cout", 0, 1)) ∨
    ∃ i < N, (j = 2 * i + 2 ∧ wn = ("s", i, 1)) ∨
      (j = 2 * i + 3 ∧ wn = ("c", i + 1, 1)) := by
  constructor
  · rintro ⟨t, e, hp, hw⟩
    rcases ripple_proc.mp hp with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨i, hi, ⟨rfl, h⟩ | ⟨rfl, h⟩⟩ <;>
      simp only [cinProc, coutProc, sumProc, carryProc, Process2.assign.injEq] at h <;>
      obtain ⟨rfl, rfl⟩ := h <;>
      simp [ripple_declWidth_cout hN] at hw <;> subst hw
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inr ⟨i, hi, Or.inl ⟨rfl, rfl⟩⟩)
    · exact Or.inr (Or.inr ⟨i, hi, Or.inr ⟨rfl, rfl⟩⟩)
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨i, hi, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩)
    · exact ⟨_, _, ripple_proc_cin N, by simp⟩
    · exact ⟨_, _, ripple_proc_cout N, by simp [ripple_declWidth_cout hN]⟩
    · exact ⟨_, _, ripple_proc_sum hi, by simp⟩
    · exact ⟨_, _, ripple_proc_carry hi, by simp⟩

/-- The driven signals: the carry chain, the carry-out, the sum. -/
theorem ripple_driven {n : String} : Driven (design.sem N) n ↔
    n = "c" ∨ n = "cout" ∨ n = "s" := by
  constructor
  · rintro ⟨j, lo, w, h⟩
    rcases (ripple_writes hN).mp h with ⟨-, h⟩ | ⟨-, h⟩ | ⟨i, -, ⟨-, h⟩ | ⟨-, h⟩⟩ <;>
      simp only [Prod.mk.injEq] at h <;> simp [h.1]
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, 0, 1, (ripple_writes hN).mpr (Or.inl ⟨rfl, rfl⟩)⟩
    · exact ⟨1, 0, 1, (ripple_writes hN).mpr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
    · exact ⟨2, 0, 1,
        (ripple_writes hN).mpr (Or.inr (Or.inr ⟨0, hN, Or.inl ⟨rfl, rfl⟩⟩))⟩

end Decls

/-! ## 2c. The comb profile and the acyclicity certificate -/

/-- **The ripple adder is in the comb profile** (every `N ≥ 1`): continuous
assigns over 1-bit windows, in range, one driver per bit, no input driven,
no loud node, every read declared, no initializers. -/
theorem ripple_comb (N : Nat) (hN : 1 ≤ N) : CombDesign (design.sem N) where
  nodup := by
    rw [ripple_sem_decls N hN]
    simp only [rippleDecls, List.map_cons, List.map_nil]
    decide
  assign := by
    intro j p hp
    rcases ripple_proc.mp hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨i, hi, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact ⟨_, _, _, rfl, rfl⟩
    · exact ⟨_, _, [("cout", 0, 1)], rfl, by simp [ripple_declWidth_cout hN]⟩
    · exact ⟨_, _, _, rfl, rfl⟩
    · exact ⟨_, _, _, rfl, rfl⟩
  inWidth := by
    intro j n lo w h
    rcases (ripple_writes hN).mp h with ⟨-, h⟩ | ⟨-, h⟩ | ⟨i, hi, ⟨-, h⟩ | ⟨-, h⟩⟩ <;>
      simp only [Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl, rfl⟩ := h
    · exact ⟨_, ripple_declWidth_c hN, by omega⟩
    · exact ⟨_, ripple_declWidth_cout hN, by omega⟩
    · exact ⟨_, ripple_declWidth_s hN, by omega⟩
    · exact ⟨_, ripple_declWidth_c hN, by omega⟩
  notInput := by
    intro n hn
    rw [ripple_inputNames hN]
    rcases (ripple_driven hN).mp hn with rfl | rfl | rfl <;> decide
  disjoint := by
    intro j k wj wk hjk hj hk
    rcases (ripple_writes hN).mp hj with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨i, hi, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ <;>
    rcases (ripple_writes hN).mp hk with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨i', hi', ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ <;>
      rw [Win.overlaps_eq_false] <;> first | (left; decide) | (right; omega) | omega
  selfDisjoint := by
    intro j t e hp
    rcases ripple_proc.mp hp with ⟨-, h⟩ | ⟨-, h⟩ | ⟨i, -, ⟨-, h⟩ | ⟨-, h⟩⟩ <;>
      simp only [cinProc, coutProc, sumProc, carryProc, Process2.assign.injEq] at h <;>
      obtain ⟨rfl, -⟩ := h <;> exact Lhs2.wins_pairwise_of_leaf (fun _ h => by cases h) _
  rhsFree := by
    intro j t e hp
    rcases ripple_proc.mp hp with ⟨-, h⟩ | ⟨-, h⟩ | ⟨i, -, ⟨-, h⟩ | ⟨-, h⟩⟩ <;>
      simp only [cinProc, coutProc, sumProc, carryProc, Process2.assign.injEq] at h <;>
      obtain ⟨-, rfl⟩ := h <;> rfl
  rhsDeclared := by
    intro j t e hp
    rw [ripple_sem_decls N hN]
    rcases ripple_proc.mp hp with ⟨-, h⟩ | ⟨-, h⟩ | ⟨i, -, ⟨-, h⟩ | ⟨-, h⟩⟩ <;>
      simp only [cinProc, coutProc, sumProc, carryProc, Process2.assign.injEq] at h <;>
      obtain ⟨-, rfl⟩ := h <;> simp [Expr2.idents, rippleDecls]
  initWidth := by
    intro n _ dc hdc _ v hv
    rw [ripple_sem_decls N hN] at hdc
    simp [rippleDecls] at hdc
    rcases hdc with rfl | rfl | rfl | rfl | rfl | rfl <;> cases hv
  inFourState := by
    intro dc hdc _
    rw [ripple_sem_decls N hN] at hdc
    simp [rippleDecls] at hdc
    rcases hdc with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- The rank certificate: carry-in 0, bit `i`'s sum and carry cells (indices
`2i + 2`, `2i + 3`) both `i + 1`, carry-out `N + 1`. -/
def rippleRank (N : Nat) (j : Nat) : Nat :=
  if j = 0 then 0 else if j = 1 then N + 1 else (j - 2) / 2 + 1

/-- **The ripple adder is acyclic**: bit `i`'s cells read `a[i]`, `b[i]` (inputs,
never written) and `c[i]`, written by the carry-in (`i = 0`, rank 0) or by bit
`i - 1`'s carry cell (rank `i`); the carry-out reads `c[N]`, written by bit
`N - 1`'s carry cell (rank `N`). -/
theorem ripple_acyclic (N : Nat) (hN : 1 ≤ N) : Acyclic (design.sem N) := by
  refine ⟨rippleRank N, ?_⟩
  intro j k tj ej tk ek wk hj hk hw hex
  have hWk := (ripple_writes hN).mp ⟨tk, ek, hk, hw⟩
  rcases ripple_proc.mp hj with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨i, hi, ⟨rfl, h⟩ | ⟨rfl, h⟩⟩ <;>
    simp only [cinProc, coutProc, sumProc, carryProc, Process2.assign.injEq] at h <;>
    obtain ⟨-, rfl⟩ := h <;>
    rcases hWk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨i', hi', ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ <;>
    simp [Expr2.reads, Expr2.sliceReads, ReadWin.overlaps, Win.overlaps_eq_true] at hex <;>
    unfold rippleRank <;> (repeat' split) <;> omega

/-! ## 3a. Gate algebra on known 1-bit values -/

section Gates

variable {st : SvState}

/-- A bit select `n[i]` of a known signal (in range). -/
theorem eval_bit {n : String} {w : Nat} {x : BitVec w} {i : Nat}
    (h : SvState.lookup st n = some (LVec.ofBitVec x)) (hi : i < w) :
    evalPure2 st (.slice (.ident n) i 1) = .ok (LVec.ofBitVec (BitVec.ofBool (x.getLsbD i))) :=
  evalPure2_bit_ofBitVec (evalPure2_ident_ofBitVec h) hi

/-- A 1-bit window `n[k]` of a signal whose OTHER bits may be unknown: only the
window's own value matters (the carry chain is known one bit at a time). -/
theorem eval_win {n : String} {u : LVec} {k : Nat} {b : Bool}
    (h : SvState.lookup st n = some u) (hk : u.extract k 1 = LVec.ofBitVec (BitVec.ofBool b)) :
    evalPure2 st (.slice (.ident n) k 1) = .ok (LVec.ofBitVec (BitVec.ofBool b)) := by
  simp only [evalPure2_slice, evalPure2_ident_of_lookup h, Pure2.res_ok_bind, Pure2.res_pure_eq,
    hk]

/-- The sum cell `l ^ m ^ r` over known bits. -/
theorem eval_xor3 {l m r : Expr2} {p q b : Bool}
    (hl : evalPure2 st l = .ok (LVec.ofBitVec (BitVec.ofBool p)))
    (hm : evalPure2 st m = .ok (LVec.ofBitVec (BitVec.ofBool q)))
    (hr : evalPure2 st r = .ok (LVec.ofBitVec (BitVec.ofBool b))) :
    evalPure2 st (.binary .xor (.binary .xor l m) r) =
      .ok (LVec.ofBitVec (BitVec.ofBool (p ^^ q ^^ b))) := by
  rw [evalPure2_xor_ofBitVec (evalPure2_xor_ofBitVec hl hm) hr, BitVec.ofBool_xor_ofBool,
    BitVec.ofBool_xor_ofBool]

/-- The carry cell `(l & m) | (r & (l ^ m))` over known bits is core's
majority `Bool.atLeastTwo` (the gate of `BitVec.carry_succ`). -/
theorem eval_carry {l m r : Expr2} {p q b : Bool}
    (hl : evalPure2 st l = .ok (LVec.ofBitVec (BitVec.ofBool p)))
    (hm : evalPure2 st m = .ok (LVec.ofBitVec (BitVec.ofBool q)))
    (hr : evalPure2 st r = .ok (LVec.ofBitVec (BitVec.ofBool b))) :
    evalPure2 st (.binary .or (.binary .and l m) (.binary .and r (.binary .xor l m))) =
      .ok (LVec.ofBitVec (BitVec.ofBool (Bool.atLeastTwo p q b))) := by
  rw [evalPure2_or_ofBitVec (evalPure2_and_ofBitVec hl hm)
    (evalPure2_and_ofBitVec hr (evalPure2_xor_ofBitVec hl hm)), BitVec.ofBool_xor_ofBool,
    BitVec.ofBool_and_ofBool, BitVec.ofBool_and_ofBool, BitVec.ofBool_or_ofBool]
  cases p <;> cases q <;> cases b <;> rfl

end Gates

/-! ## 3b. The settled state -/

/-- **The ripple adder, one settled state.** In any state that solves the
design's equations and has the comb shape, known inputs `x y : BitVec N`,
`ci : Bool` on `a b cin` give `x + y + ci` (mod `2^N`) on `s` and the carry-out
`2^N ≤ x + y + ci` on `cout`. -/
theorem ripple_settled {N : Nat} (hN : 1 ≤ N) {st : SvState}
    (heqs : CombEqs (design.sem N) st) (hs : StateShape (design.sem N) st)
    {x y : BitVec N} {ci : Bool}
    (ha : SvState.lookup st "a" = some (LVec.ofBitVec x))
    (hb : SvState.lookup st "b" = some (LVec.ofBitVec y))
    (hc : SvState.lookup st "cin" = some (LVec.ofBitVec (BitVec.ofBool ci))) :
    SvState.lookup st "s" = some (LVec.ofBitVec (x + y + (BitVec.ofBool ci).setWidth N)) ∧
      SvState.lookup st "cout" =
        some (LVec.ofBitVec (BitVec.ofBool (2 ^ N ≤ x.toNat + y.toNat + ci.toNat))) := by
  obtain ⟨u, hu, -⟩ := hs.driven "c" ((ripple_driven hN).mpr (Or.inl rfl))
  -- the carry chain, window by window: `c[k]` holds core's `carry k`
  have hcarry : ∀ k, k ≤ N →
      u.extract k 1 = LVec.ofBitVec (BitVec.ofBool (BitVec.carry k x y ci)) := by
    intro k
    induction k with
    | zero =>
      intro _
      obtain ⟨old, hold, hext⟩ :=
        CombEqs.extract_slice heqs (ripple_proc_cin N) (evalPure2_ident_ofBitVec hc)
      rw [hu, Option.some.injEq] at hold
      subst hold
      rw [hext, LVec.resizeU_ofBitVec, BitVec.setWidth_eq, BitVec.carry_zero]
    | succ k ih =>
      intro hk
      have hkN : k < N := by omega
      obtain ⟨old, hold, hext⟩ := CombEqs.extract_slice heqs (ripple_proc_carry hkN)
        (eval_carry (eval_bit ha hkN) (eval_bit hb hkN) (eval_win hu (ih (by omega))))
      rw [hu, Option.some.injEq] at hold
      subst hold
      rw [hext, LVec.resizeU_ofBitVec, BitVec.setWidth_eq, BitVec.carry_succ]
  -- the sum, from its 1-bit windows
  obtain ⟨sv, hsv, hsw⟩ := hs.driven "s" ((ripple_driven hN).mpr (Or.inr (Or.inr rfl)))
  rw [ripple_declWidth_s hN, Option.some.injEq] at hsw
  have hS : sv = LVec.ofBitVec (x + y + (BitVec.ofBool ci).setWidth N) := by
    apply LVec.eq_ofBitVec_of_extract_one hsw.symm
    intro i hi
    obtain ⟨old, hold, hext⟩ := CombEqs.extract_slice heqs (ripple_proc_sum hi)
      (eval_xor3 (eval_bit ha hi) (eval_bit hb hi) (eval_win hu (hcarry i (by omega))))
    rw [hsv, Option.some.injEq] at hold
    subst hold
    rw [hext, LVec.resizeU_ofBitVec, BitVec.setWidth_eq, BitVec.getLsbD_add_add_bool hi,
      Bool.xor_assoc]
  -- the carry-out: `c[N]` is the final carry
  have hco := CombEqs.lookup_ident (ripple_comb N hN) heqs hs (ripple_proc_cout N)
    (eval_win hu (hcarry N (Nat.le_refl N))) (ripple_declWidth_cout hN)
  rw [LVec.resizeU_ofBitVec, BitVec.setWidth_eq, BitVec.carry_width] at hco
  exact ⟨hS ▸ hsv, hco⟩

/-- **The arithmetic reading** of the two outputs: carry-out times `2^N` plus
the truncated sum is the full sum `x + y + ci`. -/
theorem ripple_arith {N : Nat} (hN : 1 ≤ N) (x y : BitVec N) (ci : Bool) :
    (decide (2 ^ N ≤ x.toNat + y.toNat + ci.toNat)).toNat * 2 ^ N +
      (x + y + (BitVec.ofBool ci).setWidth N).toNat = x.toNat + y.toNat + ci.toNat := by
  have hx := x.isLt
  have hy := y.isLt
  have hc : ci.toNat ≤ 1 := Bool.toNat_le ci
  have h2 : 2 ≤ 2 ^ N := Nat.pow_le_pow_right (n := 2) (by decide) hN
  have hcM : ci.toNat < 2 ^ N := by omega
  simp only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofBool]
  rw [Nat.mod_eq_of_lt hcM, Nat.mod_add_mod]
  generalize 2 ^ N = M at *
  by_cases h : M ≤ x.toNat + y.toNat + ci.toNat
  · rw [decide_eq_true h, Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
    simp only [Bool.toNat_true]
    omega
  · rw [decide_eq_false h, Nat.mod_eq_of_lt (by omega)]
    simp only [Bool.toNat_false]
    omega

/-! ## 4. From the settled state to the task's function -/

/-- A 1-bit vector is the `ofBool` of its only bit. -/
theorem bv1_eq_ofBool (v : BitVec 1) : v = BitVec.ofBool (v.getLsbD 0) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  obtain rfl : i = 0 := by omega
  simp

/-- The sum the adder computes is the task's `s`: `(x + y + ci) mod 2^N`. -/
theorem sum_eq_ofNat {N : Nat} (hN : 1 ≤ N) (x y : BitVec N) (ci : Bool) :
    x + y + (BitVec.ofBool ci).setWidth N =
      BitVec.ofNat N (x.toNat + y.toNat + (BitVec.ofBool ci).toNat) := by
  apply BitVec.eq_of_toNat_eq
  have h2 : 2 ≤ 2 ^ N := Nat.pow_le_pow_right (n := 2) (by decide) hN
  have hc : ci.toNat < 2 ^ N := by have := Bool.toNat_le ci; omega
  simp only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofBool, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt hc, Nat.mod_add_mod]

/-- The carry-out the adder computes is the task's `cout`: `t / 2^N`, for
any `t < 2 · 2^N`. -/
theorem carry_eq_ofNat {N : Nat} (t : Nat) (ht : t < 2 * 2 ^ N) :
    BitVec.ofBool (decide (2 ^ N ≤ t)) = BitVec.ofNat 1 (t / 2 ^ N) := by
  by_cases h : 2 ^ N ≤ t
  · have hq : t / 2 ^ N = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
    simp [h, hq]
  · have hq : t / 2 ^ N = 0 := Nat.div_eq_of_lt (by omega)
    simp [h, hq]

/-- The interface: inputs `a b : N`, `cin : 1`; outputs `s : N`, `cout : 1`. -/
theorem add_interface (N : Nat) (hN : 1 ≤ N) :
    SvGolf.Tasks.Add.task.Interface N (design.sem N) := by
  simp [CombTask.Interface, inputPorts, outputPorts, ripple_sem_decls N hN, rippleDecls,
    SvGolf.Tasks.Add.task]

/-- **The reference solution**: the `add` statement, for every `N ≥ 1`. -/
theorem solution : Goal := by
  intro N hN
  have hN' : 1 ≤ N := hN
  refine CombTask.satisfiedAt_of_comb (add_interface N hN') (ripple_comb N hN')
    (ripple_acyclic N hN') ?_
  intro st heqs hs v hv
  obtain ⟨x, y, ci, ⟨⟩⟩ := v
  obtain ⟨c0, rfl⟩ : ∃ c0, ci = BitVec.ofBool c0 := ⟨_, bv1_eq_ofBool ci⟩
  simp only [SvGolf.Tasks.Add.task, HoldAll_cons, HoldAll_nil, and_true] at hv ⊢
  obtain ⟨ha, hb, hc⟩ := hv
  obtain ⟨hs', hco⟩ := ripple_settled hN' heqs hs ha hb hc
  have ht : x.toNat + y.toNat + c0.toNat < 2 * 2 ^ N := by
    have : x.toNat < 2 ^ N := x.isLt
    have : y.toNat < 2 ^ N := y.isLt
    have := Bool.toNat_le c0
    have h2 : 2 ≤ 2 ^ N := Nat.pow_le_pow_right (n := 2) (by decide) hN'
    omega
  refine ⟨?_, ?_⟩
  · rw [hs', sum_eq_ofNat hN']
  · rw [hco, carry_eq_ofNat _ ht, BitVec.toNat_ofBool]

/-! ## Axiom pins

Standard axioms only: no `sorry`, no `native_decide`, no `bv_decide`. -/

/--
info: 'Submission.solution' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms solution

end Submission
