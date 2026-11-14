import Lean
import SvGolf.Clocked

/-!
# `sv_mirror` and `sv_cycle`: the opening block of a clocked proof, generated (untrusted, kernel-checked)

Every clocked proof on the board opens the same way: it writes the loaded design out again by hand (the
"mirror": its declarations and its processes as `Design2` terms, the generate loops as `List.range` families),
proves the loaded family equal to it, then evaluates one clock cycle of it into a next-state function over the
registers. All of that is determined by the loaded design. These two commands write it, at symbolic parameters
(`PROVING.md`, section 19.4).

```
sv_mirror mm := design (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW)
theorem mm_disj (N W AccW : Nat) : (mm.procs N W AccW).Pairwise ProcDisj := …   -- the player's one fact
sv_cycle mm using mm_disj N W AccW
```

**`sv_mirror X := design (params) (hyps)`** reads `design.pdesign` (the literal `load_sv` defines) and defines:

* `X.env`, `X.decls`, `X.elems`: the parameter environment, the declarations and the element widths, as
  `instantiate2` computes them (`X.paramEnv`, `X.buildDecls`, `X.buildElems` say so);
* one definition per process: the module's processes `X.p0`, `X.p1`, … in source order and, per process inside
  a generate loop, `X.<label>` (the label of its innermost generate block) taking the genvars as `Nat`
  arguments (`X.static`, `X.gens` say so); `X.procs`, the process list, each generate loop a `List.range`
  family, never unrolled; `X.D`, the design;
* `X.instantiate`: `instantiate2` at the surface fuel is `.ok (X.D …)`, under the hypotheses `hyps`.

The instantiation is the library's own `instantiate2`, normalized by `simp` (the set every clocked proof uses),
`unfold instExpr2` where its `resize` equation is out of `simp`'s reach, then the private helpers unfolded and the
casts pulled out of the window offsets. A side condition it leaves (a part select inside its vector, a declared
range not empty, a width comparison) is proved or refuted by `sv_disch` (positivity, `omega`, and `sv_window` for
windows of products of parameters and genvars), added as a hypothesis, and the normalization runs again with it,
so that `simp` decides it on the way. A condition neither proved nor refuted stops the command with the condition
printed; the player gives a tactic for it with `sv_mirror X (window := by tac) := …`.

**`sv_cycle X using h`**, `h : (X.procs params).Pairwise ProcDisj` (which process writes which window: the
player's; `ProcDisj.of_all` decides one pair), defines and proves:

* `X.sem_eq`: `design.sem params = X.D params` (the one-driver rule from `h`); `X.profile`: `X.D` is in the
  FF-only profile;
* `X.St x₁ … xₙ`: the positional state, one `LVec` per declaration, in declaration order; `X.apply`: the inputs
  of a cycle on it (`appIn` for each input port);
* per process, its updates `X.<p>Q params … x₁ … xₙ` (nested `if`s over `condTrue` of the evaluated conditions,
  as the players write them) and `X.<p>_run`, `X.<p>_runQ`: the process run on `X.St …` issues them;
* `X.next params x₁ … xₙ`: the commit of every process's updates, in process order (`X.updates`), and
  **`X.cycle`**: one `cycleStep2` of `design.sem params` from `X.St …`, any schedule, any stimulus entry, any
  fuel from the bound it prints (30 unless `sv_cycle X (fuel := n) using h` asks for more), is `X.next` of
  the applied inputs;
* `X.powerUp`: every power-up state of `design.sem params` is `X.St x₁ … xₙ` with every `xᵢ` of its declared
  width; `X.init`: the initial state.

**One comb process beside the registers** (an `always_comb` or a continuous `assign` at the module level, with
the `always_ff` processes): the cycle settles it before the edge and after the commit (`cycleStep2`'s
`combSettle2`, to a fixpoint, passes in schedule order). `sv_cycle` then also defines the comb process's values on
`X.St …` (`X.comb_<signal>`, the signals it writes; `X.comb`, the settled state) and proves `X.<p>_comb` (one run
gives them), `X.comb_stable` (a second run gives them again: proved, not assumed) and **`X.settle`** (the settle
ends at `X.comb` under every schedule, `combSettle2_single`); the edge's updates are `X.edgeQ` (`X.updates`), their
commit signal by signal `X.commit`, and `X.next` is the comb values of that commit; `X.cycle` is the same theorem
with `∃ k'` for the step counter (it counts the comb passes, which depend on the values) and fuel from `K + 2`.
A `localparam` chosen by a comparison of the parameters is refused with the comparison printed; under the case as
one of `hyps` (`(h : W < AccW)`, `(h : ¬ W < AccW)`, one `sv_mirror` per case) the parameter environment
evaluates and the command proceeds.

There is no `X.profile` (the design is not FF-only). Two comb processes, or one in a generate loop, are refused:
their settle in every schedule order needs a lemma that every order of the passes reaches one fixpoint, not
proved yet.

Nothing the commands produce is trusted: every definition and theorem is added to the environment through the
kernel, and every proof is a proof term built by `simp`, `omega` and the library lemmas below, checked like
hand-written Lean (no axiom, no `sorry`, no `native_decide`, no `bv_decide`); the player's terms (binders, window
tactic, disjointness) are elaborated without error recovery, and one that contains `sorry` is refused. A command
that stops adds nothing to the environment. A shape they do not cover is a refusal that names the construct (a
second comb process or one in a generate loop, an asynchronous reset, a plain `always`, a blocking assignment in an
`always_ff`, a nonblocking write to a dynamic index, two clocks, a process writing an input, an out-of-tier node,
a procedural loop whose iterations depend on the parameters, a generate `if`, a generate loop other than
`for (g = 0; g < e; g++)`, a loop bound that can be negative, a module instance, package parameters, a parameter
environment that does not evaluate at symbolic parameters, a process whose run is not a success), never an
approximation. The parameters are matched by position (a binder named after another parameter is refused), and
a generate block labelled like a generated name gets the next free one. Options: `sv_cycle.verbose` (print every
normal form, the time of each step and the rounds of each normalization), `sv_cycle.stageHeartbeats` (each
stage's heartbeat budget).
-/

namespace SvGolf.Cycle

open LeanModels.Sv

set_option autoImplicit false

/-! ## 1. Library lemmas the generated proofs cite -/

/-- A loop bound below the parameters' sum is below the surface fuel. -/
theorem lt_fuel_of_le {M s : Nat} (h : M ≤ s) : M < (s + 2) * (s + 2) + 64 := by
  have := Nat.le_mul_self (s + 2); omega

/-- A loop bound below the square of the parameters' sum is below the surface fuel. -/
theorem lt_fuel_of_le_sq {M s : Nat} (h : M ≤ s * s) : M < (s + 2) * (s + 2) + 64 := by
  have : s * s ≤ (s + 2) * (s + 2) := Nat.mul_le_mul (by omega) (by omega)
  omega

/-- `1 ≤ x` from `0 < x` over `Int` (the form of a declared range's emptiness test). -/
theorem one_le_of_pos {x : Int} (h : 0 < x) : 1 ≤ x := by omega

/-- A parameter of type `int` (`logic signed [31:0]`) is of the INT class. -/
theorem int_declConstType (env : IEnv) :
    declConstType env (some (PType.packed [{ msb := PExpr.int 31, lsb := PExpr.int 0 }] (some 32))) none =
      .ok none := rfl

/-- The type `int` is 32 bits wide. -/
theorem int_width (env : IEnv) :
    (PType.packed [{ msb := PExpr.int 31, lsb := PExpr.int 0 }] (some 32)).width env = .ok 32 := rfl

/-- A `Res`-valued `if` of two successes is a success. -/
theorem ite_res_ok {α : Type} (c : Prop) [Decidable c] (a b : α) :
    (if c then Res.ok a else Res.ok b) = Res.ok (if c then a else b) := by
  split <;> rfl

/-- An `if` of two pairs with the same first component. -/
theorem ite_pair {α β : Type} (c : Prop) [Decidable c] (a : α) (x y : β) :
    (if c then (a, x) else (a, y)) = (a, if c then x else y) := by
  split <;> rfl

/-- A statement after an `if` appends its updates to both branches' queue: keep the queue once. -/
theorem ite_append_self {α : Type} (c : Prop) [Decidable c] (a b : List α) :
    (if c then a ++ b else a) = a ++ (if c then b else []) := by
  split <;> simp

/-- The same, the update on the `else` side. -/
theorem ite_self_append {α : Type} (c : Prop) [Decidable c] (a b : List α) :
    (if c then a else a ++ b) = a ++ (if c then [] else b) := by
  split <;> simp

/-! ### Two `evalExpr2` cases whose `match` returns a success on every branch

A signed comparison matches on the operands' two's-complement values and a dynamic select read on the index's
value; every branch is a success, but `simp` cannot move `Res.ok` out of a `match`, so a run that reads one would
not normalize to a success. The values are named here, and the run is a success of the named value. -/

/-- The value of a signed comparison `op` of `a` and `b` (`evalExpr2`'s `scmp` case, LRM §11.8.1). -/
def scmpVal (op : BinOp) (a b : LVec) : LVec :=
  match a.toInt?, b.toInt? with
  | some x, some y => .ofLogic (match op with
      | .lt => if x < y then .l1 else .l0
      | .le => if x ≤ y then .l1 else .l0
      | .gt => if x > y then .l1 else .l0
      | .ge => if x ≥ y then .l1 else .l0
      | _ => .lx)
  | _, _ => .ofLogic .lx

/-- The value of the select `bv[iv]` of `elemW`-bit elements (`evalExpr2`'s `index` case). -/
def indexVal (bv iv : LVec) (elemW : Nat) : LVec :=
  match iv.toNat? with
  | some i => if (i + 1) * elemW ≤ bv.width then bv.extract (i * elemW) elemW else LVec.xVec elemW
  | none => LVec.xVec elemW

theorem evalExpr2_scmp (f : Nat) (st : SvState) (op : BinOp) (l r : Expr2) :
    evalExpr2 (f + 1) st (.scmp op l r) =
      (do let a ← evalExpr2 f st l; let b ← evalExpr2 f st r; return scmpVal op a b) := by
  simp only [evalExpr2]
  cases evalExpr2 f st l <;> cases evalExpr2 f st r <;>
    simp only [Res.ok_bind, Res.timeout_bind, Res.unsupported_bind, Res.pure_eq]
  rename_i a b
  unfold scmpVal
  cases a.toInt? <;> cases b.toInt? <;> rfl

theorem evalExpr2_index (f : Nat) (st : SvState) (base idx : Expr2) (elemW : Nat) :
    evalExpr2 (f + 1) st (.index base idx elemW) =
      (do let bv ← evalExpr2 f st base; let iv ← evalExpr2 f st idx; return indexVal bv iv elemW) := by
  simp only [evalExpr2]
  cases evalExpr2 f st base <;> cases evalExpr2 f st idx <;>
    simp only [Res.ok_bind, Res.timeout_bind, Res.unsupported_bind, Res.pure_eq]
  rename_i bv iv
  unfold indexVal
  cases iv.toNat? with
  | none => rfl
  | some i => exact ite_res_ok _ _ _

/-! ### The inputs of a cycle (`applyInputs2`) on a state that binds each declaration once -/

/-- The value the signal `n` holds after sub-step 1 of a cycle (`applyInputs2` over the declarations `ds`):
an input takes the stimulus entry's value (made 2-state for a 2-state declaration) when the entry binds it,
everything else keeps `v`. -/
def appInDecl (ds : List Decl) (e : SvState) (n : String) (v : LVec) : LVec :=
  match ds.find? (fun dc => dc.name == n) with
  | some dc =>
      if dc.isInput then ((SvState.lookup e n).map fun w => if dc.twoState then w.toTwoState else w).getD v
      else v
  | none => v

/-- `SvState.set` on a state with distinct names that binds `n`: the entry `n` takes `v`. -/
theorem set_eq_map : ∀ (s : SvState) (n : String) (v : LVec), n ∈ s.map Prod.fst → (s.map Prod.fst).Nodup →
    SvState.set s n v = s.map fun p => if p.1 = n then (n, v) else p
  | [], _, _, h, _ => absurd h (by simp)
  | (k, w) :: rest, n, v, h, hnd => by
    have hk : k ∉ rest.map Prod.fst := (List.nodup_cons.mp hnd).1
    have hr : (rest.map Prod.fst).Nodup := (List.nodup_cons.mp hnd).2
    by_cases hkn : k = n
    · subst hkn
      have hrest : (rest.map fun p => if p.1 = k then (k, v) else p) = rest := by
        refine (List.map_congr_left fun p hp => ?_).trans (List.map_id rest)
        have : p.1 ≠ k := fun he => hk (he ▸ List.mem_map_of_mem hp)
        simp [this]
      simp [SvState.set, hrest]
    · have hn : n ∈ rest.map Prod.fst := by
        simp only [List.map_cons, List.mem_cons] at h
        rcases h with h | h
        · exact absurd h.symm hkn
        · exact h
      have hb : (k == n) = false := by simp [hkn]
      simp only [SvState.set, hb, Bool.false_eq_true, ↓reduceIte, List.map_cons, if_neg hkn]
      exact congrArg _ (set_eq_map rest n v hn hr)

private theorem find?_none_of_not_mem {ds : List Decl} {n : String} (h : n ∉ ds.map Decl.name) :
    ds.find? (fun dc => dc.name == n) = none := by
  rw [List.find?_eq_none]
  intro dc hdc
  have : dc.name ≠ n := fun he => h (he ▸ List.mem_map_of_mem hdc)
  simp [this]

/-- The fold of `applyInputs2` over a declaration list, on a state with distinct names binding every
declaration of the list: each entry takes `appInDecl`. -/
theorem foldl_apply (e : SvState) : ∀ (ds : List Decl) (st : SvState), (st.map Prod.fst).Nodup →
    (∀ dc ∈ ds, dc.name ∈ st.map Prod.fst) → (ds.map Decl.name).Nodup →
    ds.foldl (fun s declaration =>
      if declaration.isInput then
        match SvState.lookup e declaration.name with
        | some v => SvState.set s declaration.name (if declaration.twoState then v.toTwoState else v)
        | none => s
      else s) st = st.map fun p => (p.1, appInDecl ds e p.1 p.2)
  | [], st, _, _, _ => by
    simp only [List.foldl_nil, appInDecl, List.find?_nil]
    exact (List.map_id' st).symm
  | dc :: ds, st, hnd, hall, hdn => by
    have hdc : dc.name ∉ ds.map Decl.name := (List.nodup_cons.mp (by simpa using hdn)).1
    have hdn' : (ds.map Decl.name).Nodup := (List.nodup_cons.mp (by simpa using hdn)).2
    have hmem : dc.name ∈ st.map Prod.fst := hall dc List.mem_cons_self
    -- the first step, as a `map` over the state
    have step : (if dc.isInput then
        match SvState.lookup e dc.name with
        | some v => SvState.set st dc.name (if dc.twoState then v.toTwoState else v)
        | none => st
      else st) = st.map fun p => (p.1, if p.1 = dc.name then appInDecl [dc] e p.1 p.2 else p.2) := by
      have hid : st = st.map fun p => (p.1, p.2) := (List.map_id' st).symm
      by_cases hin : dc.isInput = true
      · cases hl : SvState.lookup e dc.name with
        | none =>
          simp only [hin, ↓reduceIte]
          conv => lhs; rw [hid]
          refine List.map_congr_left fun p _ => ?_
          by_cases hp : p.1 = dc.name <;> simp [hp, appInDecl, hin, hl]
        | some w =>
          simp only [hin, ↓reduceIte]
          rw [set_eq_map st dc.name _ hmem hnd]
          refine List.map_congr_left fun p _ => ?_
          by_cases hp : p.1 = dc.name
          · simp [hp, appInDecl, hin, hl]
          · simp [hp]
      · simp only [hin, Bool.false_eq_true, ↓reduceIte]
        conv => lhs; rw [hid]
        refine List.map_congr_left fun p _ => ?_
        by_cases hp : p.1 = dc.name <;> simp [hp, appInDecl, hin]
    rw [List.foldl_cons, step]
    have hnd1 : ((st.map fun p => (p.1, if p.1 = dc.name then appInDecl [dc] e p.1 p.2 else p.2)).map
        Prod.fst).Nodup := by simpa [List.map_map, Function.comp_def] using hnd
    have hall1 : ∀ d ∈ ds, d.name ∈ (st.map fun p =>
        (p.1, if p.1 = dc.name then appInDecl [dc] e p.1 p.2 else p.2)).map Prod.fst := by
      intro d hd
      simpa [List.map_map, Function.comp_def] using hall d (List.mem_cons_of_mem _ hd)
    rw [foldl_apply e ds _ hnd1 hall1 hdn', List.map_map]
    refine List.map_congr_left fun p _ => ?_
    simp only [Function.comp_apply]
    by_cases hp : p.1 = dc.name
    · rw [if_pos hp, hp]
      have h1 : appInDecl ds e dc.name (appInDecl [dc] e dc.name p.2) = appInDecl [dc] e dc.name p.2 := by
        simp [appInDecl, find?_none_of_not_mem hdc]
      rw [h1]
      simp [appInDecl]
    · rw [if_neg hp]
      have hb : (dc.name == p.1) = false := by simp [Ne.symm hp]
      simp [appInDecl, hb]

/-- **The inputs of a cycle**, on a state that binds every declaration once, in declaration order: every
entry takes `appInDecl` (a stimulus value for an input it binds, the old value otherwise). -/
theorem applyInputs2_eq_map (d : Design2) (e st : SvState)
    (hnames : st.map Prod.fst = d.decls.toList.map Decl.name)
    (hnd : (d.decls.toList.map Decl.name).Nodup) :
    applyInputs2 d e st = st.map fun p => (p.1, appInDecl d.decls.toList e p.1 p.2) := by
  unfold applyInputs2
  rw [← Array.foldl_toList]
  exact foldl_apply e d.decls.toList st (hnames ▸ hnd)
    (fun dc hdc => hnames ▸ List.mem_map_of_mem hdc) hnd

/-! ### One cycle of an FF-only design: the commit of the processes' updates -/

/-- The updates a process issues on `st` at fuel `F` (none when its run fails). -/
def runQ (F : Nat) (st : SvState) (p : Process2) : NbaQueue2 :=
  match runEdgeProcess2 F st [] p with
  | .ok (_, q) => q
  | _ => []

theorem runQ_of {F : Nat} {st st' : SvState} {p : Process2} {q : NbaQueue2}
    (h : runEdgeProcess2 F st [] p = .ok (st', q)) : runQ F st p = q := by
  simp [runQ, h]

/-- **One cycle of a design in the FF-only profile**: every process runs on the applied state and leaves it
alone; the cycle is the commit of their updates, in process order, under every schedule. -/
theorem cycleStep2_eq_commit {d : Design2} (hp : d.ffOnlyProfileB = true) (σ : ScheduleOracle) {F : Nat}
    (hF : 1 ≤ F) (e st : SvState) (k : Nat)
    (hrun : ∀ p ∈ d.processes.toList, ∃ q,
      runEdgeProcess2 F (applyInputs2 d e st) [] p = .ok (applyInputs2 d e st, q))
    (hnd : ((applyInputs2 d e st).map Prod.fst).Nodup) :
    cycleStep2 d σ F e st k =
      .ok (commitNba2 (applyInputs2 d e st) (d.processes.toList.flatMap (runQ F (applyInputs2 d e st))),
        k + 3) := by
  have hedge : ∀ p ∈ d.processes.toList, p.isEdgePhase = true := by
    intro p hp'
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp'
    have hi' : i < d.processes.size := by simpa using hi
    obtain ⟨c, b, hpb, -⟩ := (FFOnly.ofProfile hp).procs i d.processes[i]
      (by rw [Array.getElem?_eq_getElem hi'])
    simp only [Array.getElem_toList]
    rcases hpb with h | h <;> rw [h] <;> rfl
  rw [cycleStep2_profile hp σ e st k
    (fun i p hp' => hrun p (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hp'))) hnd hF]
  unfold clockStep
  rw [flatMap_ffUpd F _ hedge]
  rfl

/-! ### The checks of the one-driver rule and the profile, as `List.all` -/

/-- An `always_ff` process. -/
def isFF : Process2 → Bool
  | .alwaysFF _ _ => true
  | _ => false

theorem ff_of_all {ps : List Process2} (h : ps.all isFF = true) : ∀ p ∈ ps, ∃ c b, p = .alwaysFF c b := by
  intro p hp
  have := List.all_eq_true.mp h p hp
  cases p <;> simp_all [isFF]

/-- **Two processes write disjoint windows**, decided pair by pair: on a concrete pair `simp` evaluates both
window lists and `DrvWin.overlaps`, leaving the window arithmetic (`omega`, with the row-major facts). -/
theorem _root_.SvGolf.ProcDisj.of_all {p q : Process2}
    (h : (p.procWins.all fun a => q.procWins.all fun b => !a.overlaps b) = true) : SvGolf.ProcDisj p q := by
  intro a ha b hb
  have := List.all_eq_true.mp (List.all_eq_true.mp h a ha) b hb
  simpa using this

theorem noInput_of_all {ps : List Process2} {inputs : List String}
    (h : ps.all (fun p => p.procWrites.all fun n => !inputs.contains n) = true) :
    ∀ n ∈ ps.flatMap Process2.procWrites, inputs.contains n = false := by
  intro n hn
  obtain ⟨p, hp, hn⟩ := List.mem_flatMap.mp hn
  have := List.all_eq_true.mp (List.all_eq_true.mp h p hp) n hn
  simpa using this


/-! ### One cycle with a comb process beside the `always_ff` processes

`cycleStep2` settles the comb processes (to a fixpoint, passes in schedule order) before the edge and after the
commit. With one comb process whose run on a state `s` gives `S` and whose run on `S` gives `S` again, the settle ends
at `S` under every schedule (`combSettle2_single`); `cycleStep2_mixed` puts the cycle together from the two settles,
the edge runs and the disjointness of the updates. -/

/-- An `always_ff @(posedge …)` with a reset event (`alwaysFFR`). -/
def isResetProc : Process2 → Bool
  | .alwaysFFR _ _ _ _ => true
  | _ => false

/-- A design with no asynchronous-reset process has no reset event. -/
theorem resetIndices_nil_of {d : Design2} (h : d.processes.toList.all (fun p => !isResetProc p) = true)
    (a b : SvState) : d.resetIndices a b = [] := by
  simp only [Design2.resetIndices, List.filter_eq_nil_iff, List.mem_range]
  intro i hi
  have hp := List.all_eq_true.mp h d.processes[i] (Array.getElem_mem_toList _)
  rw [Array.getElem?_eq_getElem hi]
  generalize d.processes[i] = p at hp ⊢
  cases p <;> simp_all [isResetProc]

/-- **The edge pass**, when every edge process is an `always_ff` with nonblocking assignments that runs on `st`
and leaves it: the state, and the updates of the listed processes in list order. -/
theorem edgePass2_of_ff {d : Design2} {fuel : Nat} {st : SvState}
    (hff : ∀ (i : Nat) (p : Process2), d.processes[i]? = some p → p.isEdgePhase = true →
      ∃ c b, p = .alwaysFF c b ∧ b.nbaOnly = true)
    (hrun : ∀ (i : Nat) (p : Process2), d.processes[i]? = some p → p.isEdgePhase = true →
      ∃ q, runEdgeProcess2 fuel st [] p = .ok (st, q)) :
    ∀ (l : List Nat), (∀ i ∈ l, i ∈ d.edgeIndices) → ∀ (nba : NbaQueue2),
      edgePass2 d fuel st nba l = .ok (st, nba ++ l.flatMap (d.ffUpd fuel st))
  | [], _, nba => by simp [edgePass2]
  | i :: l, hl, nba => by
      have hi : i ∈ d.edgeIndices := hl i List.mem_cons_self
      have hrest : ∀ j ∈ l, j ∈ d.edgeIndices := fun j hj => hl j (List.mem_cons_of_mem _ hj)
      cases hp : d.processes[i]? with
      | none =>
          simp only [edgePass2, hp, Res.pure_eq, Res.ok_bind]
          rw [edgePass2_of_ff hff hrun l hrest nba]
          simp [Design2.ffUpd, hp]
      | some p =>
          have he : p.isEdgePhase = true := by
            simp only [Design2.edgeIndices, List.mem_filter, List.mem_range] at hi
            rw [hp] at hi
            exact hi.2
          obtain ⟨c, b, rfl, hb⟩ := hff i _ hp he
          obtain ⟨q, hq⟩ := hrun i _ hp he
          have hshift := runEdgeProcess2_shift (fuel := fuel) (st := st) (p := .alwaysFF c b)
            (fun c' b' h => by
              rcases h with h | h <;> cases h
              exact hb) ⟨c, b, Or.inl rfl⟩ nba
          simp only [edgePass2, hp, List.flatMap_cons]
          rw [hshift, hq]
          simp only [liftQ, Res.ok_bind]
          rw [edgePass2_of_ff hff hrun l hrest (nba ++ q)]
          simp [Design2.ffUpd, hp, hq, List.append_assoc]

/-- **The updates of distinct processes are disjoint** when every edge process is an `always_ff` with
nonblocking assignments and the processes write pairwise disjoint windows (`ffDisjB`); the comb processes issue
no update. -/
theorem ffUpd_disj_of {d : Design2}
    (hff : ∀ (i : Nat) (p : Process2), d.processes[i]? = some p → p.isEdgePhase = true →
      ∃ c b, p = .alwaysFF c b ∧ b.nbaOnly = true)
    (hd : d.ffDisjB = true) (fuel : Nat) (st : SvState) :
    ∀ i j, i ≠ j → ∀ u ∈ d.ffUpd fuel st i, ∀ u' ∈ d.ffUpd fuel st j, NbaDisj u u' := by
  intro i j hij u hu u' hu'
  have cov : ∀ r, ∀ x ∈ d.ffUpd fuel st r, ∃ p, d.processes[r]? = some p ∧
      ∃ a ∈ p.procWins, Covers a x := by
    intro r x hx
    simp only [Design2.ffUpd] at hx
    split at hx
    · rename_i p hp
      split at hx
      · rename_i st' q hq
        cases p with
        | alwaysFF c b =>
            have hq' : execStmt2 fuel st [] b = .ok (st', q) := by simpa [runEdgeProcess2] using hq
            rcases (upd_covered fuel).1 st b [] _ q hq' x hx with hx | hx
            · cases hx
            · exact ⟨_, hp, by simpa [Process2.procWins] using hx⟩
        | alwaysPlain c b =>
            obtain ⟨c', b', he, -⟩ := hff r _ hp rfl
            cases he
        | alwaysFFR c rn b high =>
            obtain ⟨c', b', he, -⟩ := hff r _ hp rfl
            cases he
        | alwaysComb b =>
            simp only [runEdgeProcess2, Res.ok.injEq, Prod.mk.injEq] at hq
            rw [← hq.2] at hx
            cases hx
        | assign t e =>
            simp only [runEdgeProcess2, Res.ok.injEq, Prod.mk.injEq] at hq
            rw [← hq.2] at hx
            cases hx
        | unsupported k t => simp [runEdgeProcess2] at hq
      · cases hx
    · cases hx
  obtain ⟨p, hp, a, ha, hca⟩ := cov i u hu
  obtain ⟨q, hq, b, hb, hcb⟩ := cov j u' hu'
  simp only [Design2.ffDisjB, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq] at hd
  have hin := hd i (Array.getElem?_eq_some_iff.mp hp).1 j (Array.getElem?_eq_some_iff.mp hq).1
  rcases hin with hij' | hin
  · exact absurd hij' hij
  · simp only [hp, hq, Option.map_some, Option.getD_some, Bool.not_eq_true'] at hin
    exact covers_disj (hin a ha b hb) hca hcb

/-- **The comb settle with one comb process**: when one run of it on `s` gives `S` and a run on `S` gives `S`
again, the settle ends at `S` under every schedule (one or two passes). -/
theorem combSettle2_single {d : Design2} {c : Nat} {P : Process2} (hc : d.combIndices = [c])
    (hp : d.processes[c]? = some P) (σ : ScheduleOracle) {K F : Nat} (hF : K + 2 ≤ F) {s S : SvState}
    (h1 : ∀ f, K ≤ f → runCombProcess2 f s P = .ok S)
    (h2 : ∀ f, K ≤ f → runCombProcess2 f S P = .ok S) (k : Nat) :
    ∃ k', combSettle2 d σ F s k = .ok (S, k') := by
  have hch : ∀ j, σ.choose j d.combIndices = [c] := fun j => by
    rw [hc]; exact List.perm_singleton.mp (σ.choose_perm j [c])
  have hpass : ∀ f t T, runCombProcess2 f t P = .ok T → ∀ j, combPass2 d f t (σ.choose j d.combIndices) = .ok T :=
    fun f t T h j => by simp [hch, combPass2, hp, h]
  obtain ⟨f, rfl⟩ : ∃ f, F = f + K + 2 := ⟨F - K - 2, by omega⟩
  rw [show f + K + 2 = (f + K + 1) + 1 by omega, combSettle2.eq_2, hpass _ _ _ (h1 _ (by omega))]
  simp only [Res.ok_bind]
  by_cases hb : (S == s) = true
  · rw [if_pos hb]; exact ⟨_, rfl⟩
  · rw [if_neg hb, show f + K + 1 = (f + K) + 1 by omega, combSettle2.eq_2, hpass _ _ _ (h2 _ (by omega))]
    simp only [Res.ok_bind]
    rw [beq_self_eq_true, if_pos rfl]
    exact ⟨_, rfl⟩

/-- **One cycle of a design whose edge processes are `always_ff`s beside comb processes**: the comb settle of
the applied inputs ends at `S1`, every edge process runs on `S1` and leaves it, the updates of distinct processes
are disjoint, and the settle of the commit (in index order) ends at `S2`: the cycle ends at `S2`, under every
schedule. -/
theorem cycleStep2_mixed {d : Design2} (σ : ScheduleOracle) {F : Nat} (e st : SvState) (k : Nat)
    {S1 S2 : SvState}
    (hset1 : ∀ j, ∃ k', combSettle2 d σ F (applyInputs2 d e st) j = .ok (S1, k'))
    (hreset : ∀ a b, d.resetIndices a b = [])
    (hff : ∀ (i : Nat) (p : Process2), d.processes[i]? = some p → p.isEdgePhase = true →
      ∃ c b, p = .alwaysFF c b ∧ b.nbaOnly = true)
    (hrun : ∀ (i : Nat) (p : Process2), d.processes[i]? = some p → p.isEdgePhase = true →
      ∃ q, runEdgeProcess2 F S1 [] p = .ok (S1, q))
    (hd : d.ffDisjB = true) (hnd : (S1.map Prod.fst).Nodup)
    (hset2 : ∀ j, ∃ k', combSettle2 d σ F (commitNba2 S1 (d.edgeIndices.flatMap (d.ffUpd F S1))) j =
      .ok (S2, k')) :
    ∃ k', cycleStep2 d σ F e st k = .ok (S2, k') := by
  obtain ⟨k1, h1⟩ := hset1 k
  have hperm := σ.choose_perm k1 d.edgeIndices
  have hnde : d.edgeIndices.Nodup := List.nodup_range.filter _
  have hE := edgePass2_of_ff hff hrun (σ.choose k1 d.edgeIndices)
    (fun i hi => hperm.subset hi) []
  have hC : commitNba2 S1 ((σ.choose k1 d.edgeIndices).flatMap (d.ffUpd F S1)) =
      commitNba2 S1 (d.edgeIndices.flatMap (d.ffUpd F S1)) :=
    commitNba2_perm (ffUpd_disj_of hff hd F S1) hperm (hperm.nodup_iff.mpr hnde) hnd
  obtain ⟨k2, h2⟩ := hset2 (k1 + 1)
  refine ⟨k2, ?_⟩
  simp only [cycleStep2, h1, Res.ok_bind, hreset, Res.pure_eq, hE, List.nil_append, hC, h2]

/-- **The one-driver rule** from the player's disjointness of the processes' procedural windows, when the
continuous drivers' windows are disjoint among themselves and from every procedural window and none is an input. -/
theorem driversOk_of_procDisj {names inputs : List String} {ps : List Process2}
    (hdw : (driverWins names ps).Pairwise (fun a b => a.overlaps b = false))
    (hdv : ∀ w ∈ driverWins names ps, inputs.contains w.1 = false ∧
      ∀ v ∈ ps.flatMap Process2.procWins, w.overlaps v = false)
    (hin : ∀ n ∈ ps.flatMap Process2.procWrites, inputs.contains n = false)
    (hdisj : ps.Pairwise fun p q => ∀ a ∈ p.procWins, ∀ b ∈ q.procWins, a.overlaps b = false) :
    driversOk names inputs ps = true := by
  rw [driversOk_iff]
  refine ⟨hdw, hdv, hin, hdisj.imp fun {p q} h => ?_⟩
  have hany : ((p.procWinsOn names).any fun a => (q.procWinsOn names).any fun b => a.overlaps b) =
      false := by
    rw [List.any_eq_false]
    intro a ha
    rw [Bool.not_eq_true, List.any_eq_false]
    intro b hb
    rw [h a (List.mem_filter.mp ha).1 b (List.mem_filter.mp hb).1]
    exact Bool.false_ne_true
  simp [Process2.exclClash, hany]

/-- `filter` then `flatMap` is `flatMap` when the dropped elements map to nothing. -/
theorem flatMap_filter_of {α β : Type} (p : α → Bool) (f : α → List β) : ∀ (l : List α),
    (∀ x ∈ l, p x = false → f x = []) → (l.filter p).flatMap f = l.flatMap f
  | [], _ => rfl
  | x :: l, h => by
    have ih := flatMap_filter_of p f l (fun y hy => h y (List.mem_cons_of_mem _ hy))
    by_cases hx : p x = true
    · simp [hx, ih]
    · have hfx : f x = [] := h x List.mem_cons_self (by simpa using hx)
      simp [hx, ih, hfx]

/-- **The updates of a clock edge are the processes' updates in process order**: an index left out of the
edge pass (a comb process, a loud one) issues no update. -/
theorem flatMap_ffUpd_all (d : Design2) (F : Nat) (st : SvState) :
    d.edgeIndices.flatMap (d.ffUpd F st) = d.processes.toList.flatMap (runQ F st) := by
  have h1 : d.edgeIndices.flatMap (d.ffUpd F st) = (List.range d.processes.size).flatMap (d.ffUpd F st) := by
    unfold Design2.edgeIndices
    refine flatMap_filter_of _ _ _ fun i _ hi => ?_
    unfold Design2.ffUpd
    cases hp : d.processes[i]? with
    | none => rfl
    | some p =>
        rw [hp] at hi
        cases p <;> simp_all [Process2.isEdgePhase, runEdgeProcess2]
  rw [h1, ← Array.length_toList]
  refine CombView.flatMap_range_eq _ _ _ fun i hi => ?_
  have hi' : i < d.processes.size := by simpa using hi
  unfold Design2.ffUpd runQ
  rw [Array.getElem?_eq_getElem hi', Array.getElem_toList]
  dsimp only
  cases runEdgeProcess2 F st [] d.processes[i] <;> rfl

/-- A list with no duplicate whose members are exactly `c` is `[c]`. -/
theorem eq_singleton_of_mem_iff {l : List Nat} {c : Nat} (hnd : l.Nodup) (h : ∀ x, x ∈ l ↔ x = c) : l = [c] := by
  match l, hnd with
  | [], _ => exact absurd ((h c).mpr rfl) (by simp)
  | a :: t, hnd =>
    have ha : a = c := (h a).mp List.mem_cons_self
    subst ha
    have ht : t = [] := List.eq_nil_iff_forall_not_mem.mpr fun x hx =>
      (List.nodup_cons.mp hnd).1 (((h x).mp (List.mem_cons_of_mem _ hx)) ▸ hx)
    rw [ht]

/-- **The one comb process**: a design whose process list is `pre ++ P :: post`, `P` a comb process and no
other one, has `P` as its only comb index. -/
theorem combIndices_of_split {d : Design2} {pre post : List Process2} {P : Process2}
    (h : d.processes.toList = pre ++ P :: post) (hP : P.isCombPhase = true)
    (hpre : pre.all (fun p => !p.isCombPhase) = true) (hpost : post.all (fun p => !p.isCombPhase) = true) :
    d.combIndices = [pre.length] ∧ d.processes[pre.length]? = some P := by
  have hget : ∀ i, d.processes[i]? = (pre ++ P :: post)[i]? := fun i => by
    rw [← h, Array.getElem?_toList]
  have hP' : d.processes[pre.length]? = some P := by rw [hget]; simp
  refine ⟨eq_singleton_of_mem_iff (List.nodup_range.filter _) fun x => ?_, hP'⟩
  simp only [Design2.combIndices, List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨-, hx⟩
    rw [hget] at hx
    rcases Nat.lt_trichotomy x pre.length with hlt | heq | hgt
    · rw [List.getElem?_append_left hlt] at hx
      have hm : pre[x] ∈ pre := List.getElem_mem hlt
      have := List.all_eq_true.mp hpre _ hm
      rw [List.getElem?_eq_getElem hlt] at hx
      simp_all
    · exact heq
    · rw [List.getElem?_append_right (by omega)] at hx
      obtain ⟨k, hk⟩ : ∃ k, x - pre.length = k + 1 := ⟨x - pre.length - 1, by omega⟩
      rw [hk, List.getElem?_cons_succ] at hx
      cases hq : post[k]? with
      | none => simp [hq] at hx
      | some q =>
          rw [hq] at hx
          have hm : q ∈ post := List.mem_of_getElem? hq
          have := List.all_eq_true.mp hpost _ hm
          simp_all
  · rintro rfl
    refine ⟨?_, by rw [hP']; exact hP⟩
    have := congrArg List.length h
    simp only [Array.length_toList, List.length_append, List.length_cons] at this
    omega

/-- Every edge process an `always_ff` with nonblocking assignments, decided as a `List.all`. -/
def ffNba : Process2 → Bool
  | .alwaysFF _ b => b.nbaOnly
  | p => !p.isEdgePhase

theorem ff_of_ffNba {d : Design2} (h : d.processes.toList.all ffNba = true) :
    ∀ (i : Nat) (p : Process2), d.processes[i]? = some p → p.isEdgePhase = true →
      ∃ c b, p = .alwaysFF c b ∧ b.nbaOnly = true := by
  intro i p hp he
  have := List.all_eq_true.mp h p (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hp))
  cases p with
  | alwaysFF c b => exact ⟨c, b, rfl, by simpa [ffNba] using this⟩
  | _ => simp_all [ffNba, Process2.isEdgePhase]

/-! ## 2. The dischargers -/

/-- `(x - 1).natAbs + 1` of a positive `x` (a declared range `[x-1:0]`'s width). -/
theorem natAbs_sub_one_add_one' {x : Int} (h : 0 < x) : (x - 1).natAbs + 1 = x.natAbs := by omega

/-- The range `[w-1:0]` of a positive width: its high end. -/
theorem max_sub_one_zero {w : Int} (h : 0 < w) : max (w - 1) 0 = w - 1 := by omega

/-- The range `[w-1:0]` of a positive width: its low end. -/
theorem min_sub_one_zero {w : Int} (h : 0 < w) : min (w - 1) 0 = 0 := by omega

/-- `↑n - 1` of a positive `n`, as a cast (the bound `N - 1` of a generate loop, a window `(N - 1) * W`). -/
theorem natCast_sub_one {n : Nat} (h : 1 ≤ n) : (n : Int) - 1 = ((n - 1 : Nat) : Int) := by omega

/-- `↑n + 1` as a cast (a window `(k + 1) * W`). -/
theorem natCast_add_one' (n : Nat) : (n : Int) + 1 = ((n + 1 : Nat) : Int) := by omega

/-- The same, read back in `Int`. -/
theorem natAbs_cast_sub_one_add_one {x : Int} (h : 0 < x) : (((x - 1).natAbs : Nat) : Int) + 1 = x := by omega

/-- `sv_pos`'s steps (`sv_pos` runs them with error recovery off, so that no failing branch is admitted). -/
syntax "sv_pos_core" : tactic
macro_rules
  | `(tactic| sv_pos_core) => `(tactic| first
      | omega
      | with_reducible exact Int.natCast_nonneg _
      | (with_reducible apply Nat.mul_pos) <;> sv_pos_core
      | (with_reducible apply Int.mul_pos) <;> sv_pos_core
      | (with_reducible apply Int.mul_nonneg) <;> sv_pos_core
      | (with_reducible apply Int.add_nonneg) <;> sv_pos_core
      | (with_reducible apply Int.add_pos_of_nonneg_of_pos) <;> sv_pos_core
      | (with_reducible apply Int.add_pos_of_pos_of_nonneg) <;> sv_pos_core
      | (with_reducible apply SvGolf.Cycle.one_le_of_pos) <;> sv_pos_core)

/-- Positivity of the parameters' products and the non-negativity of cast terms (no `Mathlib`). -/
elab "sv_pos" : tactic => do
  Lean.Elab.Tactic.withoutRecover <| Lean.Elab.Tactic.evalTactic (← `(tactic| sv_pos_core))

section window
open Lean Meta Elab Tactic

/-- A `Nat` polynomial as monomials `(coefficient, atoms)`: products distributed over sums. -/
partial def natPoly (e : Lean.Expr) : MetaM (List (Nat × List Lean.Expr)) := do
  match_expr e with
  | HAdd.hAdd _ _ _ _ a b => return (← natPoly a) ++ (← natPoly b)
  | HMul.hMul _ _ _ _ a b =>
      let pa ← natPoly a
      let pb ← natPoly b
      return pa.flatMap fun (ca, xa) => pb.map fun (cb, xb) => (ca * cb, xa ++ xb)
  | OfNat.ofNat _ n _ =>
      match n with
      | .lit (.natVal k) => return [(k, [])]
      | _ => return [(1, [e])]
  | _ => return [(1, [e])]

/-- The product of `xs` (`1` for none). -/
def natProd (xs : List Lean.Expr) : MetaM Lean.Expr :=
  match xs with
  | [] => return mkNatLit 1
  | x :: rest => rest.foldlM (fun acc y => mkAppM ``HMul.hMul #[acc, y]) x

/-- Remove one occurrence of `a` (up to `==`). -/
def removeOne (a : Lean.Expr) : List Lean.Expr → List Lean.Expr
  | [] => []
  | x :: xs => if x == a then xs else x :: removeOne a xs

/-- Prove `ty` with `omega`, or `none`. -/
def omegaProof? (ty : Lean.Expr) : TacticM (Option Lean.Expr) := do
  let mv ← mkFreshExprMVar ty
  try
    let gs ← Tactic.run mv.mvarId! (Tactic.withoutRecover (Tactic.evalTactic (← `(tactic| omega))))
    if gs.isEmpty then return some (← instantiateMVars mv) else return none
  catch _ => return none

/-- `sv_window`: a window of a register family is inside its vector, `lo + w ≤ total` over `Nat`, with
products of parameters and genvars. Each genvar (or other atom, `N - 1` included) of a monomial of the
left side is replaced by its bound (`a + c ≤ P`, `c` the largest of 2 and 1 that `omega` proves, `P` a
variable), and each parameter factor of a monomial of the right side is dropped (`X ≤ P * X` from
`1 ≤ P`), each step a `Nat.mul_le_mul_right` fact; then `omega` closes the linear combination. -/
elab "sv_window" : tactic => withMainContext do
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  let (L, R, strict) ← match_expr ty with
    | LE.le α _ a b => do
        unless ← isDefEq α (Lean.mkConst ``Nat) do throwError "sv_window: not a `Nat` inequality"
        pure (a, b, false)
    | LT.lt α _ a b => do
        unless ← isDefEq α (Lean.mkConst ``Nat) do throwError "sv_window: not a `Nat` inequality"
        pure (a, b, true)
    | _ => throwError "sv_window: not an inequality"
  let _ := strict
  let vars : Array Lean.Expr := (← getLCtx).foldl (init := #[]) fun acc d =>
    if d.isImplementationDetail then acc
    else if d.type.isConstOf ``Nat then acc.push d.toExpr else acc
  let one := mkNatLit 1
  let mut facts : Array Lean.Expr := #[]
  -- bump: an atom `a` of a monomial of `L` to its bound
  for (_, atoms) in ← natPoly L do
    for a in atoms.eraseDups do
      let mut found := false
      for c in [2, 1] do
        if found then break
        for P in vars do
          if found then break
          if P == a then continue
          let hbTy ← mkAppM ``LE.le #[← mkAppM ``HAdd.hAdd #[a, mkNatLit c], P]
          if let some hb ← omegaProof? hbTy then
            let X ← natProd (removeOne a atoms)
            facts := facts.push (← mkAppM ``Nat.mul_le_mul_right #[X, hb])
            found := true
  -- insertion: drop a parameter factor of a monomial of `R`, twice
  let mut frontier : List (List Lean.Expr) := (← natPoly R).map (·.2)
  for _ in [0:2] do
    let mut next : List (List Lean.Expr) := []
    for atoms in frontier do
      for P in atoms.eraseDups do
        let h1Ty ← mkAppM ``LE.le #[one, P]
        if let some h1 ← omegaProof? h1Ty then
          let rest := removeOne P atoms
          let X ← natProd rest
          facts := facts.push (← mkAppM ``Nat.mul_le_mul_right #[X, h1])
          next := rest :: next
    frontier := next
  -- add the facts, normalize products, `omega`
  let mut g := g
  for f in facts do
    let (_, g') ← (← g.assert `hw (← inferType f) f).intro1P
    g := g'
  replaceMainGoal [g]
  -- (`Nat.mul_two`: a bump by 2 leaves the numeral inside a product, `N * (W * 2)`, which `omega` reads as an
  -- atom; spelled out, `N * W + N * W`, it is linear)
  withoutRecover <| evalTactic (← `(tactic| (simp only [Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm,
    Nat.mul_left_comm, Nat.one_mul, Nat.mul_one, Nat.mul_two, Nat.two_mul] at *) <;> omega))

end window

/-- `sv_disch`'s steps. -/
syntax "sv_disch_core" : tactic
macro_rules
  | `(tactic| sv_disch_core) => `(tactic| first
      | assumption
      | decide
      | omega
      | sv_pos_core
      | (refine ⟨?_, ?_⟩ <;> sv_disch_core)
      | (with_reducible apply not_and_of_not_left) <;> sv_disch_core
      | (with_reducible apply not_and_of_not_right) <;> sv_disch_core
      | ((try simp (disch := sv_pos_core) only [SvGolf.Cycle.natCast_sub_one,
            SvGolf.Cycle.natAbs_cast_sub_one_add_one, SvGolf.Cycle.natAbs_sub_one_add_one', Int.natAbs_mul,
            Int.natAbs_natCast, Int.natCast_add, Int.natCast_mul])
         (try simp only [Int.sub_one_lt_iff])
         (try simp only [← Int.natCast_one, ← Int.natCast_mul, ← Int.natCast_add, Int.ofNat_le, Int.ofNat_lt])
         first | omega | sv_window))

/-- The side conditions of an instantiation `simp`: a hypothesis, a closed decision, linear arithmetic,
positivity, a conjunction of these, or a window once the casts are pulled out of the products
(`sv_window`). Error recovery is off: a branch that fails is never admitted. -/
elab "sv_disch" : tactic => do
  Lean.Elab.Tactic.withoutRecover <| Lean.Elab.Tactic.evalTactic (← `(tactic| sv_disch_core))

/-! ## 3. The generator -/

open Lean Meta Elab Term Command

register_option sv_cycle.verbose : Bool := {
  defValue := false
  descr := "sv_mirror/sv_cycle: log every normal form the generator computes" }

register_option sv_cycle.stageHeartbeats : Nat := {
  defValue := 1000000
  descr := "sv_mirror/sv_cycle: the heartbeat budget (in thousands, like `maxHeartbeats`) of each stage of the \
    generation (one normalization, one proof); the stages between them are bookkeeping" }

/-- Run one stage of the generation with its own heartbeat budget (`sv_cycle.stageHeartbeats`). -/
def withStage {α : Type} (x : TermElabM α) : TermElabM α := do
  let hb := sv_cycle.stageHeartbeats.get (← getOptions)
  withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := hb * 1000 }) (withCurrHeartbeats x)

/-- The whole command: each stage is bounded by `withStage`, the bookkeeping between them is not. -/
def withStagesBudget {α : Type} (x : TermElabM α) : TermElabM α :=
  withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := 0 }) x

/-- Run `x`; when it fails (a refusal, a failed proof, a timeout), the environment is restored, so that a
command that stops adds no declaration. -/
def atomically {α : Type} (x : TermElabM α) : TermElabM α := do
  let env ← getEnv
  tryCatchRuntimeEx x fun ex => do
    setEnv env
    throw ex

/-- The fields of the literal design `pdC` (`load_sv` defines it as one structure literal), each as the simp
lemma `PDesign.f pdC = <its literal>` (by `rfl`). A normalization rewrites the fields it reads with them instead
of unfolding the whole design, whose processes and generate items it would otherwise simplify each time. -/
def designFieldLemmas (pdC : Name) : TermElabM (Array (TSyntax ``Lean.Parser.Tactic.simpLemma)) := do
  let pdE := Lean.mkConst pdC
  let some v := (← getConstInfo pdC).value? | throwError "sv_mirror: `{pdC}` is not a definition"
  let v ← whnfR v
  let fields := getStructureFields (← getEnv) ``PDesign
  unless v.isAppOfArity ``PDesign.mk fields.size do
    throwError "sv_mirror: internal error: `{pdC}` is not a structure literal"
  let args := v.getAppArgs
  (fields.zip args).mapM fun (f, a) => do
    let ty ← mkEq (← mkAppM (``PDesign ++ f) #[pdE]) a
    let pf ← mkExpectedTypeHint (← mkEqRefl a) ty
    `(Lean.Parser.Tactic.simpLemma| $(← exprToSyntax pf):term)

/-- The payload `x` of `Res.ok x` (or `Except.ok x`). -/
def okPayload? (e : Lean.Expr) : Option Lean.Expr :=
  if e.isAppOfArity ``Res.ok 2 then some e.appArg!
  else if e.isAppOfArity ``Except.ok 3 then some e.appArg!
  else none

/-- The elements of a list literal (`whnf` on every tail). -/
partial def listLit? (e : Lean.Expr) : MetaM (Option (Array Lean.Expr)) := do
  let e ← whnf e
  if e.isAppOfArity ``List.nil 1 then return some #[]
  else if e.isAppOfArity ``List.cons 3 then
    match ← listLit? e.appArg! with
    | some rest => return some (#[e.appFn!.appArg!] ++ rest)
    | none => return none
  else return none

/-- The elements of a list literal, syntactically (no `whnf`). -/
partial def listLitSyn? (e : Lean.Expr) : Option (Array Lean.Expr) :=
  if e.isAppOfArity ``List.nil 1 then some #[]
  else if e.isAppOfArity ``List.cons 3 then
    (listLitSyn? e.appArg!).map fun rest => #[e.appFn!.appArg!] ++ rest
  else none

/-- A string literal. -/
def strLit? (e : Lean.Expr) : Option String :=
  match e with
  | .lit (.strVal s) => some s
  | _ => none

/-- The constructor at the head of `e` (after `whnf`), with its arguments. -/
def ctorOf (e : Lean.Expr) : MetaM (Name × Array Lean.Expr) := do
  let e ← whnf e
  match e.getAppFn with
  | .const n _ => return (n, e.getAppArgs)
  | _ => return (.anonymous, e.getAppArgs)

/-- Run a `conv` sequence on `e`: `(rhs, proof : e = rhs)`. -/
def convNorm (e : Lean.Expr) (conv : TSyntax ``Lean.Parser.Tactic.Conv.convSeq) : TermElabM (Lean.Expr × Lean.Expr) :=
  withStage do
  let out ← IO.mkRef (none : Option (Lean.Expr × Lean.Expr))
  let g ← mkFreshExprMVar (Lean.mkConst ``True)
  discard <| Tactic.run g.mvarId! do
    let r ← Tactic.Conv.convert e (Tactic.withoutRecover (Tactic.evalTactic (← `(conv| ($conv)))))
    out.set (some r)
  match ← out.get with
  | some (rhs, pf) => return (← instantiateMVars rhs, ← instantiateMVars pf)
  | none => throwError "sv_mirror: internal error: the conversion returned nothing"

/-- Prove `type` with a tactic sequence (error recovery off). A failure is an error that starts with `what`
(followed by the tactic's own message unless `detail := false`); a proof containing `sorry` is refused. -/
def proveBy (what : String) (type : Lean.Expr) (tac : TSyntax ``Lean.Parser.Tactic.tacticSeq)
    (detail : Bool := true) : TermElabM Lean.Expr :=
  withStage do
  let mv ← mkFreshExprSyntheticOpaqueMVar type
  let gs ← try Tactic.run mv.mvarId! (Tactic.withoutRecover (Tactic.evalTactic tac))
    catch ex => if detail then throwError "{what}: {ex.toMessageData}" else throwError "{what}"
  unless gs.isEmpty do
    if detail then throwError "{what}: goals left:\n{goalsToMessageData gs}" else throwError "{what}"
  let pf ← instantiateMVars mv
  if pf.hasSorry then throwError "{what}: the proof contains `sorry`"
  return pf

/-- Add `n := fun xs => body`. -/
def addDefn (n : Name) (xs : Array Lean.Expr) (body : Lean.Expr) (doc : String) : TermElabM Unit := do
  let body ← instantiateMVars body
  if body.hasMVar then throwError "sv_mirror: internal error: the body of `{n}` has metavariables:\n{body}"
  let value ← mkLambdaFVars xs body
  let type ← instantiateMVars (← mkForallFVars xs (← inferType body))
  let hints := ReducibilityHints.regular (getMaxHeight (← getEnv) value + 1)
  let decl := Declaration.defnDecl (← mkDefinitionValInferringUnsafe n [] type value hints)
  addDecl decl
  enableRealizationsForConst n
  try compileDecl decl (logErrors := false) catch _ => pure ()
  addDocStringCore n doc

/-- Add `theorem n : ∀ xs, type := fun xs => proof` (the kernel checks it). -/
def addThm (n : Name) (xs : Array Lean.Expr) (type proof : Lean.Expr) (doc : String) : TermElabM Unit := do
  let type ← instantiateMVars (← mkForallFVars xs type)
  let value ← instantiateMVars (← mkLambdaFVars xs proof)
  if type.hasMVar || value.hasMVar then
    throwError "sv_mirror: internal error: `{n}` has metavariables"
  addDecl (.thmDecl { name := n, levelParams := [], type, value })
  enableRealizationsForConst n
  addDocStringCore n doc

/-- Log a normal form when `sv_cycle.verbose` is set. -/
def verbose (msg : MessageData) : TermElabM Unit := do
  if sv_cycle.verbose.get (← getOptions) then logInfo msg

/-- The constants that must not occur in a finished normal form (each names what was left unevaluated). -/
def unfinishedHeads : List Name :=
  [``instExpr2, ``instStmt2, ``instLhs2, ``fitExpr2, ``instProcess2, ``instParts2, ``evalInt, ``evalAt,
   ``ite, ``dite, ``Except.error, ``Stmt2.unsupported, ``Expr2.unsupported, ``Process2.unsupported,
   ``Res.unsupported, ``Res.timeout, ``execStmt2, ``evalExpr2, ``execStmts2, ``evalExprs2, ``resolveLhs2,
   ``runEdgeProcess2, ``runCombProcess2, ``forValues2]

/-- The loud nodes of the semantics (`unsupported` statements, expressions and processes), named in plain
words with their kind and text, the way a refusal names them. -/
def loudNode? (t : Lean.Expr) : MetaM (Option MessageData) := do
  let fn := t.getAppFn.constName?.getD .anonymous
  let what := if fn == ``Stmt2.unsupported || fn == ``PStmt.unsupported then "statement"
    else if fn == ``Expr2.unsupported || fn == ``PExpr.unsupported then "expression"
    else if fn == ``Process2.unsupported || fn == ``PProcess.unsupported then "process" else ""
  if what.isEmpty || t.getAppNumArgs != 2 then return none
  let k ← whnf (t.getArg! 0)
  let x ← whnf (t.getArg! 1)
  let kS := strLit? k |>.getD (toString k)
  let xS := strLit? x |>.getD (toString x)
  return some m!"an out-of-tier {what} `{kS}` ({xS})"

/-- The first unfinished subterm of a normal form, if any: an unevaluated function, a condition the
dischargers could not decide (`ite`/`dite`, shown by its condition), a loud node, or a `match` left over.
With `allowIte`, `if`s and `match`es are a finished shape (the updates of a process branch on the state's
values, e.g. a signed comparison matches on `LVec.toInt?`). -/
def firstUnfinished? (e : Lean.Expr) (allowIte : Bool := false) : MetaM (Option MessageData) := do
  -- a loud node first: it names the construct (an unevaluated function around it would not)
  let loud := [``Stmt2.unsupported, ``Expr2.unsupported, ``Process2.unsupported, ``PStmt.unsupported,
    ``PExpr.unsupported, ``PProcess.unsupported]
  if let some l := e.find? (fun t => loud.any (t.isAppOfArity · 2)) then
    if let some why ← loudNode? l then return some why
  let some sub := e.find? fun t =>
      match t.getAppFn with
      | .const n _ =>
          (unfinishedHeads.contains n && !(allowIte && (n == ``ite || n == ``dite))) ||
            (!allowIte && n.isStr && n.getString!.startsWith "match_")
      | _ => false
    | return none
  let fn := sub.getAppFn.constName!
  if let some loud ← loudNode? sub then return some loud
  if fn == ``ite || fn == ``dite then
    let args := sub.getAppArgs
    return some m!"a condition it cannot decide:{indentExpr args[1]!}"
  else if fn == ``Except.error || fn == ``Res.unsupported then
    return some m!"an error branch:{indentExpr sub}"
  else if fn == ``forValues2 then
    return some m!"a procedural `for` loop whose iterations depend on the parameters (the library unrolls a \
      procedural loop at instantiation, so at symbolic parameters it cannot; a generate loop can be kept as a \
      family):{indentExpr sub}"
  else
    return some m!"an unevaluated `{fn}`:{indentExpr sub}"

/-! ### Shapes refused by name, before any proof is attempted

The profile and the run proofs would fail on these too, but with the message of a failed `simp`; each is
named here from the instantiated process term (a scan for diagnostics only: nothing proved depends on it). -/

/-- Every subterm of `e` satisfying `p` (not below one that does). -/
def subtermsWith (e : Lean.Expr) (p : Lean.Expr → Bool) : Array Lean.Expr := Id.run do
  let mut acc : Array Lean.Expr := #[]
  let mut todo : Array Lean.Expr := #[e]
  while !todo.isEmpty do
    let t := todo.back!
    todo := todo.pop
    if p t then acc := acc.push t
    else
      match t with
      | .app f a => todo := (todo.push a).push f
      | .lam _ ty b _ | .forallE _ ty b _ => todo := (todo.push b).push ty
      | .letE _ ty v b _ => todo := ((todo.push b).push v).push ty
      | .mdata _ b | .proj _ _ b => todo := todo.push b
      | _ => pure ()
  return acc

/-- The signal an assignment target names, when it is a literal. -/
def lhsName? (l : Lean.Expr) : MetaM (Option String) := do
  let (k, as) ← ctorOf l
  unless (k == ``Lhs2.ident || k == ``Lhs2.slice || k == ``Lhs2.index) && as.size > 0 do return none
  let n ← whnf as[0]!
  return strLit? n

/-- The plain-words name of a source process kind (`PProcess`) the generator does not cover. -/
def processKindRefusal (p : Lean.Expr) : MetaM MessageData := do
  let (pk, as) ← ctorOf p
  let str (i : Nat) : MetaM String := do return (strLit? (← whnf as[i]!)).getD "?"
  if pk == ``PProcess.alwaysComb then
    return m!"an `always_comb` process"
  else if pk == ``PProcess.assign || pk == ``PProcess.assignL then
    return m!"a continuous assignment (`assign`)"
  else if pk == ``PProcess.alwaysFFR then
    let high := (← whnf as[3]!).isConstOf ``Bool.true
    return m!"an asynchronous reset (`always_ff @(posedge {← str 0} or {if high then "posedge" else "negedge"} \
      {← str 1})`): the clock step's reset-event phase is not covered; only `always_ff @(posedge clk)` with a \
      synchronous reset (an `if` in the body) is"
  else if pk == ``PProcess.alwaysPlain then
    return m!"a plain `always @(posedge {← str 0})` process: only `always_ff` processes are covered"
  else if pk == ``PProcess.unsupported then
    return m!"an out-of-tier process `{← str 0}` ({← str 1})"
  else
    return m!"a `{pk}` process"

/-- The clocked shapes the FF-only clock step needs, read off an instantiated process `p` (a `Process2`
term): an `always_ff`, its clock, nonblocking assignments only, static targets (a whole signal, a constant
part or bit select), no input written. The clock is returned. -/
def scanFF (what : MessageData) (inputs : List String) (p : Lean.Expr) : MetaM String := do
  let (k, as) ← ctorOf p
  unless k == ``Process2.alwaysFF && as.size == 2 do
    throwError "sv_mirror: refused: {what} is not an `always_ff` process after instantiation:{indentExpr p}"
  let some clk := strLit? (← whnf as[0]!)
    | throwError "sv_mirror: internal error: the clock of {what} is not a literal"
  let body := as[1]!
  if let some l := (subtermsWith body fun t =>
      t.isAppOfArity ``Stmt2.unsupported 2 || t.isAppOfArity ``Expr2.unsupported 2)[0]? then
    if let some why ← loudNode? l then throwError "sv_mirror: refused: {why} in {what}"
  if let some b := (subtermsWith body (·.isAppOfArity ``Stmt2.blockingAssign 2))[0]? then
    let n ← lhsName? (b.getArg! 0)
    throwError "sv_mirror: refused: a blocking assignment (`=`) to `{n.getD "?"}` in {what}: the FF-only clock \
      step takes nonblocking assignments (`<=`) only (`Stmt2.nbaOnly`)"
  for t in subtermsWith body (·.isAppOfArity ``Stmt2.nbaAssign 2) do
    let l := t.getArg! 0
    let (lk, las) ← ctorOf l
    let n := (← lhsName? l).getD "?"
    if lk == ``Lhs2.concat then
      throwError "sv_mirror: refused: a concatenated target (`{"{"}…{"}"} <= …`) in {what}: a clocked process \
        does not resolve it (`resolveLhs2`)"
    if lk == ``Lhs2.index then
      unless (← whnfR las[1]!).isAppOf ``Expr2.lit do
        throwError "sv_mirror: refused: a nonblocking assignment to a dynamic index `{n}[…]` in {what}: the \
          target is not a static window (`Stmt2.nbaStaticB`)"
    if inputs.contains n then
      throwError "sv_mirror: refused: {what} writes the input `{n}` (the one-driver rule and the profile forbid it)"
  return clk

/-- The decls of `X.decls params`: `(name, width, isInput, twoState)`. -/
def readDecls (declsE : Lean.Expr) : MetaM (Array (String × Lean.Expr × Bool × Bool)) := do
  let some ds ← listLit? declsE | throwError "sv_cycle: internal error: `decls` is not a list literal"
  ds.mapM fun d => do
    let d ← whnf d
    unless d.isAppOfArity ``Decl.mk 7 do throwError "sv_cycle: internal error: a declaration is not a literal: {d}"
    let as := d.getAppArgs
    let some nm := strLit? (← whnf as[0]!) | throwError "sv_cycle: internal error: a declaration name is not a literal"
    let isIn ← whnf as[4]!
    let tw ← whnf as[3]!
    return (nm, as[1]!, isIn.isConstOf ``Bool.true, tw.isConstOf ``Bool.true)

/-- The shapes the comb settle needs, read off an instantiated comb process `p`: an `always_comb` with blocking
assignments only, or an `assign`; static targets (a whole signal, a constant part or bit select); no input
written. -/
def scanComb (what : MessageData) (inputs : List String) (p : Lean.Expr) : MetaM Unit := do
  if let some why ← loudNode? p then throwError "sv_mirror: refused: {why} ({what})"
  let (k, as) ← ctorOf p
  let loud (e : Lean.Expr) : MetaM Unit := do
    if let some l := (subtermsWith e fun t =>
        t.isAppOfArity ``Stmt2.unsupported 2 || t.isAppOfArity ``Expr2.unsupported 2)[0]? then
      if let some why ← loudNode? l then throwError "sv_mirror: refused: {why} in {what}"
  let targets : Array Lean.Expr ← do
    if k == ``Process2.alwaysComb && as.size == 1 then
      loud as[0]!
      if let some b := (subtermsWith as[0]! (·.isAppOfArity ``Stmt2.nbaAssign 2))[0]? then
        let n ← lhsName? (b.getArg! 0)
        throwError "sv_mirror: refused: a nonblocking assignment (`<=`) to `{n.getD "?"}` in {what}: an \
          `always_comb` with a nonblocking assignment is outside the cycle semantics (`runCombProcess2`)"
      pure ((subtermsWith as[0]! (·.isAppOfArity ``Stmt2.blockingAssign 2)).map (·.getArg! 0))
    else if k == ``Process2.assign && as.size == 2 then
      loud as[1]!
      pure #[as[0]!]
    else
      throwError "sv_mirror: refused: {what} is not an `always_comb` or an `assign` after instantiation:\
        {indentExpr p}"
  for l in targets do
    let (lk, las) ← ctorOf l
    let n := (← lhsName? l).getD "?"
    if lk == ``Lhs2.concat then
      throwError "sv_mirror: refused: a concatenated target (`{"{"}…{"}"} = …`) in {what}: not covered"
    if lk == ``Lhs2.index then
      unless (← whnfR las[1]!).isAppOf ``Expr2.lit do
        throwError "sv_mirror: refused: an assignment to a dynamic index `{n}[…]` in {what}: not covered (the \
          settled value would depend on the index's value)"
    if inputs.contains n then
      throwError "sv_mirror: refused: {what} writes the input `{n}` (the one-driver rule forbids it)"

/-- Whether an instantiated process term is a comb process (`always_comb` or `assign`). -/
def isCombTerm (p : Lean.Expr) : MetaM Bool := do
  let (k, _) ← ctorOf p
  return k == ``Process2.alwaysComb || k == ``Process2.assign

/-- The binder-name-safe form of a label. -/
def labelName (s : String) : Name := Name.mkSimple (s.map fun c => if c.isAlphanum || c == '_' then c else '_')

/-- The fixed names `sv_mirror` defines under its prefix. -/
def mirrorNames : List Name :=
  [`env, `decls, `elems, `paramEnv, `buildDecls, `buildElems, `static, `gens, `procs, `D, `instantiate]

/-- The fixed names `sv_cycle` defines under the prefix. -/
def cycleNames : List Name :=
  [`sem_eq, `profile, `St, `apply, `next, `updates, `cycle, `powerUp, `init]

/-- The names `sv_cycle` derives from a process's name `p`: its updates and their two run theorems. -/
def derivedNames (p : Name) : List Name :=
  [p.appendAfter "Q", p.appendAfter "_run", p.appendAfter "_runQ"]

/-- The context of one generation. -/
structure Ctx where
  /-- the prefix of every generated name -/
  X : Name
  /-- `design.pdesign`, `design.sem` -/
  pdC : Name
  semC : Name
  /-- the parameters (`Nat` free variables, declaration order) and the hypotheses -/
  params : Array Lean.Expr
  hyps : Array Lean.Expr
  /-- `[↑N, ↑W, …] : List Int` -/
  args : Lean.Expr
  /-- the window tactic, if the player gave one -/
  window? : Option (TSyntax ``Lean.Parser.Tactic.tacticSeq)
  /-- the design's fields as `simp` lemmas (`designFieldLemmas`) -/
  fields : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) := #[]
  /-- the input ports (no process may write one) -/
  inputs : List String := []
  /-- the first clock seen, and the process it came from (one clock per design) -/
  clock : IO.Ref (Option (String × String))
  /-- the process names allocated so far (with the names `sv_cycle` will derive from them) -/
  taken : IO.Ref (List Name)
  /-- the side conditions decided so far that mention only the parameters and the hypotheses, with their
  proofs: every later normalization starts with them (the parameters' positivity first) -/
  known : IO.Ref (Array (Lean.Expr × Lean.Expr))

/-- Record the clock of the process `what`; a second clock is refused by name. -/
def Ctx.noteClock (c : Ctx) (what : String) (clk : String) : TermElabM Unit := do
  match ← c.clock.get with
  | none => c.clock.set (some (clk, what))
  | some (k, w) =>
      unless k == clk do
        throwError "sv_mirror: refused: two clocks, `{k}` ({w}) and `{clk}` ({what}): the FF-only clock step has \
          one clock (`Design2.ffOnlyProfileB`)"

/-- `X.c params` -/
def Ctx.app (c : Ctx) (n : Name) (extra : Array Lean.Expr := #[]) : Lean.Expr :=
  mkAppN (Lean.mkConst (c.X ++ n)) (c.params ++ extra)

/-- The instantiation `simp` set, the generated definitions `extra` added. -/
def instConv (c : Ctx) (extra : Array Name) : TermElabM (TSyntax ``Lean.Parser.Tactic.Conv.convSeq) := do
  let ex : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) ←
    extra.mapM fun n => `(Lean.Parser.Tactic.simpLemma| $(mkCIdent n):ident)
  let ex := ex ++ c.fields
  `(Lean.Parser.Tactic.Conv.convSeq|
      simp (config := { decide := true }) [instProcess2, instLhs2, instLhsLeaf2, fitExpr2,
        instExpr2, rigidExpr, selfWidth2, selfWidthSum2, elemOf, instParts2, evalInt, IEnv.bindVal,
        PExpr.isInt, SymBinOp.intArith, SymBinOp.constClass, ctype, ctypeList, evalAt, evalAtList,
        PExpr.readsSignal, PExpr.readsSignalList, PExpr.readsSignalConst, PExpr.readsSignalConstList,
        PExpr.signalRoot?, PExpr.pushedTarget, PExpr.ctxPropagates, PExpr.isSquash2, PExpr.negGenvarAt,
        PExpr.mentionsAny, PExpr.mentionsAnyList, paramSelectOk, arraySelWidth, arrayElemRead, arrayPartRead,
        arrayElemTarget, arrayPartTarget, arrayElemWindow, arrayPartGeom, arrayDims, evalDims, dynPartPlan,
        dynBaseRead, arrayFlatWidth, partOffsetsWild, concatLeafExact, walkIndices, partLabels, labelOffset,
        dimCount, dimsStride, List.lookup, Gen2.except_ok_bind, Gen2.except_error_bind, Gen2.int_add_nonneg,
        Gen2.int_mul_nonneg, evalSized, Gen2.except_pure, Lib.min_add_sub_one_self, Lib.max_add_sub_one_self,
        Lib.add_sub_one_sub_add_one, SvGolf.Cycle.max_sub_one_zero, SvGolf.Cycle.min_sub_one_zero, instStmt2,
        instStmts2, dimTable, dimTableStep, PType.width_packed_cons,
        PDim.width, ctxOpWidth2, rigidMax2, PExpr.constLeaf, PExpr.negGenvarWidened, LVec.width,
        divOperandWidth2, instDivOperand2, fitDivOperand2, IEnv.withDecls, $ex,*, *])

/-- Prove a side condition `c` of an instantiation with `sv_disch` (then the player's window tactic). -/
def proveCond (c : Ctx) (cond : Lean.Expr) : TermElabM (Option Lean.Expr) := withStage do
  let disch : TSyntax ``Lean.Parser.Tactic.tacticSeq ← match c.window? with
    | some w => `(Lean.Parser.Tactic.tacticSeq| first | sv_disch | ($w))
    | none => `(Lean.Parser.Tactic.tacticSeq| sv_disch)
  let mv ← mkFreshExprSyntheticOpaqueMVar cond
  try
    let gs ← Tactic.run mv.mvarId! (Tactic.withoutRecover (Tactic.evalTactic disch))
    if gs.isEmpty then
      let pf ← instantiateMVars mv
      if pf.hasSyntheticSorry || pf.hasSorry then return none
      return some pf
    else return none
  catch _ => return none

/-- Run `k` with the facts `facts` (types) as local hypotheses. -/
partial def withFacts {α : Type} (facts : List Lean.Expr) (k : Array Lean.Expr → TermElabM α) : TermElabM α :=
  go facts #[]
where
  go : List Lean.Expr → Array Lean.Expr → TermElabM α
    | [], acc => k acc
    | ty :: rest, acc => withLocalDeclD (Name.mkSimple s!"hc{acc.size}") ty fun h => go rest (acc.push h)

/-- The first condition of an `if` in `e` that mentions no bound variable (one the context decides). -/
def firstClosedCond? (e : Lean.Expr) : Option Lean.Expr :=
  let isIf (t : Lean.Expr) := t.isAppOfArity ``ite 5 || t.isAppOfArity ``dite 5
  let isDec (t : Lean.Expr) := t.isAppOfArity ``Decidable.decide 2
  let cond (t : Lean.Expr) : Lean.Expr := if isDec t then t.getArg! 0 else t.getArg! 1
  (e.find? fun t =>
      (isIf t || isDec t) && !(cond t).hasLooseBVars && !(cond t).hasMVar &&
        ((cond t).find? fun u => isIf u || isDec u).isNone &&
        !(cond t).isConstOf ``True && !(cond t).isConstOf ``False).map cond

/-- Every subterm of `e` satisfying `p`, below a match too (each distinct subterm visited once). -/
def subtermsAll (e : Lean.Expr) (p : Lean.Expr → Bool) : Array Lean.Expr := Id.run do
  let mut acc : Array Lean.Expr := #[]
  let mut seen : Std.HashSet Lean.Expr := {}
  let mut todo : Array Lean.Expr := #[e]
  while !todo.isEmpty do
    let t := todo.back!
    todo := todo.pop
    if seen.contains t then continue
    seen := seen.insert t
    if p t then acc := acc.push t
    match t with
    | .app f a => todo := (todo.push a).push f
    | .lam _ ty b _ | .forallE _ ty b _ => todo := (todo.push b).push ty
    | .letE _ ty v b _ => todo := ((todo.push b).push v).push ty
    | .mdata _ b | .proj _ _ b => todo := todo.push b
    | _ => pure ()
  return acc

/-- Every condition of an `if` in `e` that mentions no bound variable, each once (`firstClosedCond?`'s test). -/
def allClosedConds (e : Lean.Expr) : Array Lean.Expr := Id.run do
  let isIf (t : Lean.Expr) := t.isAppOfArity ``ite 5 || t.isAppOfArity ``dite 5
  let isDec (t : Lean.Expr) := t.isAppOfArity ``Decidable.decide 2
  let mut acc : Array Lean.Expr := #[]
  for t in subtermsAll e (fun t => isIf t || isDec t) do
    let c := if isDec t then t.getArg! 0 else t.getArg! 1
    if !c.hasLooseBVars && !c.hasMVar && (c.find? fun u => isIf u || isDec u).isNone &&
        !c.isConstOf ``True && !c.isConstOf ``False && !acc.contains c then
      acc := acc.push c
  return acc

/-- The outcome of one round of `instNorm`. -/
inductive NormRound where
  | done (rhs proof : Lean.Expr)
  | need (conds : Array Lean.Expr) (rhs proof : Lean.Expr)
  | stuck (rhs : Lean.Expr) (why : MessageData)

/-- The bits of a literal `LVec.mk #[b₀, …]` whose every bit is known: `(width, value)` (bit 0 first). -/
def bitLit? (e : Lean.Expr) : Option (Nat × Nat) := do
  guard (e.isAppOfArity ``LVec.mk 1)
  let arr := e.appArg!
  let l ← if arr.isAppOfArity ``List.toArray 2 then some arr.appArg!
    else if arr.isAppOfArity ``Array.mk 2 then some arr.appArg! else none
  let bs ← listLitSyn? l
  let mut v := 0
  let mut i := 0
  for b in bs do
    if b.isConstOf ``Logic.l1 then v := v + 2 ^ i
    else if !b.isConstOf ``Logic.l0 then none
    i := i + 1
  some (bs.size, v)

/-- Fold every known literal of two or more bits in `r` into `LVec.ofBitVec (v#w)` (each equation by
`decide`): the form the library's value lemmas (`LVec.add_ofBitVec`, …) take. -/
def foldLits (r : Lean.Expr) : TermElabM (Option (Lean.Expr × Lean.Expr)) := do
  let found := Id.run do
    let mut acc : Array Lean.Expr := #[]
    let mut todo : Array Lean.Expr := #[r]
    while !todo.isEmpty do
      let t := todo.back!
      todo := todo.pop
      match bitLit? t with
      | some (w, _) => if w ≥ 2 && !acc.contains t then acc := acc.push t
      | none =>
        match t with
        | .app f a => todo := (todo.push f).push a
        | .lam _ ty b _ | .forallE _ ty b _ => todo := (todo.push ty).push b
        | .letE _ ty v b _ => todo := ((todo.push ty).push v).push b
        | .mdata _ b | .proj _ _ b => todo := todo.push b
        | _ => pure ()
    return acc
  let lits := found
  if lits.isEmpty then return none
  let mut eqs : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) := #[]
  for t in lits do
    let some (w, v) := bitLit? t | continue
    let folded ← mkAppOptM ``LVec.ofBitVec #[some (mkNatLit w), some (← mkAppM ``BitVec.ofNat #[mkNatLit w, mkNatLit v])]
    let ty ← mkEq t folded
    let pf ← proveBy "sv_mirror: a literal" ty (← `(Lean.Parser.Tactic.tacticSeq| decide))
    eqs := eqs.push (← `(Lean.Parser.Tactic.simpLemma| $(← exprToSyntax pf):term))
  let r' ← convNorm r (← `(Lean.Parser.Tactic.Conv.convSeq| simp only [$eqs,*]))
  return some r'

/-- The parameters' positivity, `Nat` and `Int` (the facts every player states first), decided once per
command and kept in `c.known`. -/
def seedKnown (c : Ctx) : TermElabM Unit := do
  let mut facts : Array (Lean.Expr × Lean.Expr) := #[]
  for P in c.params do
    let one ← mkAppM ``LE.le #[mkNatLit 1, P]
    if (← proveCond c one).isSome then
      let pos ← mkAppM ``LT.lt #[mkNatLit 0, P]
      if let some pf ← proveCond c pos then facts := facts.push (pos, pf)
      let posI ← mkAppM ``LT.lt #[toExpr (0 : Int), ← mkAppOptM ``Nat.cast #[some (Lean.mkConst ``Int), none, some P]]
      if let some pf ← proveCond c posI then facts := facts.push (posI, pf)
  c.known.set facts

/-- Normalize `lhs` with the instantiation `simp` set, the way a player does: the main pass and, while it is
left, `unfold instExpr2` (whose `resize` equation `simp` cannot use) with the main pass again. Every condition
left undecided is proved (or refuted) by `sv_disch` (or the player's window tactic) in the context and added as
a hypothesis, and the main pass runs again on the normal form reached so far, so that `simp` decides them and
drops the branches they rule out. The conditions found are carried forward, never rediscovered: a round decides
every condition it shows (not only the first), continues from where the last one stopped (not from `lhs`), and
a decided condition that mentions only the parameters joins `c.known`, the facts every later normalization of
the command starts with. A condition that is neither proved nor refuted while another of its round is decided
waits for the next round, where the decided one may have removed it. The private helpers of the instantiation
(`intLit2`, …) are unfolded at the end. -/
def instNorm (c : Ctx) (what : String) (lhs : Lean.Expr) (extra : Array Name) : TermElabM (Lean.Expr × Lean.Expr) := do
  verbose m!"sv_mirror: instantiating {what}"
  let t0 ← IO.monoMsNow
  let mut tCond := 0
  let main ← instConv c extra
  let unfoldConv ← `(Lean.Parser.Tactic.Conv.convSeq| unfold LeanModels.Sv.instExpr2)
  let step (conv : TSyntax ``Lean.Parser.Tactic.Conv.convSeq) (e : Lean.Expr) :
      TermElabM (Option (Lean.Expr × Lean.Expr)) := do
    try
      let (r, p) ← convNorm e conv
      if r == e then return none else return some (r, p)
    catch ex =>
      verbose m!"sv_mirror: a pass made no progress on {what}: {ex.toMessageData}"
      return none
  -- the facts decided earlier in the command (the parameters' positivity first)
  let mut facts : Array (Lean.Expr × Lean.Expr) ← c.known.get
  let global (e : Lean.Expr) : Bool :=
    !e.hasAnyFVar fun fv => !(c.params ++ c.hyps).any (·.fvarId! == fv)
  let mut rounds := 0
  -- the normal form so far, and its proof abstracted over the first `curK` facts (a round continues from it)
  let mut cur : Option (Lean.Expr × Lean.Expr) := none
  let mut curK := 0
  for _ in [0:40] do
    rounds := rounds + 1
    let cur' := cur
    let curK' := curK
    let round ← withFacts (facts.map (·.1)).toList fun hs => do
      let (start, pStart) ← match cur' with
        | none => pure (lhs, ← mkEqRefl lhs)
        | some (r, pAbs) => pure (r, mkAppN pAbs (hs.extract 0 curK'))
      let some (r0, p0) ← (do match ← step main start with
          | some x => pure (some x)
          | none => if cur'.isNone then pure none else pure (some (start, ← mkEqRefl start)))
        | return NormRound.stuck start m!"the instantiation `simp` made no progress"
      let mut r := r0
      let mut p ← mkEqTrans pStart p0
      -- `instExpr2` where its `resize` equation is out of `simp`'s reach, and the library's private helpers
      -- (`maxW2` of a fill's absent width, …), unfolded, then the main pass again
      let isPriv (t : Lean.Expr) : Bool := match t.getAppFn with
        | .const n _ => isPrivateName n
        | _ => false
      for _ in [0:12] do
        let (r1, p1) ← if (r.find? fun t => t.isAppOf ``instExpr2).isSome then
            match ← step unfoldConv r with
            | some x => pure x
            | none => break
          else if (r.find? isPriv).isSome then
            let rd ← deltaExpand r isPrivateName
            if rd == r then break
            pure (rd, ← mkExpectedTypeHint (← mkEqRefl r) (← mkEq r rd))
          else break
        let (r2, p2) ← (do match ← step main r1 with
          | some x => pure x
          | none => pure (r1, ← mkEqRefl r1))
        p ← mkEqTrans p (← mkEqTrans p1 p2)
        r := r2
      -- an `always_comb`'s self-read guard, decided on the instantiated body (`combGuardProc_of_admits`): the
      -- guard reads the body's windows, so it is evaluated once the body is in normal form
      for g in subtermsWith r (·.isAppOfArity ``combGuardProc 2) do
        let admTy ← mkEq (← mkAppM ``Stmt2.combAdmits #[g.getArg! 0, g.getArg! 1]) (Lean.mkConst ``Bool.true)
        let admPf ← proveBy "sv_mirror: refused: an `always_comb` that reads bits of a signal before it writes \
            them on some path (the library's self-read guard, `combGuardProc`, makes it a loud process)" admTy
          (← `(Lean.Parser.Tactic.tacticSeq| simp (config := { decide := true }) [Stmt2.combAdmits,
            Stmt2.combViol, Stmt2.listCombViol, Stmt2.mayW, Stmt2.listMayW, Stmt2.mustW, Lhs2.mayW, Lhs2.mustW,
            Lhs2.rdW, Expr2.rdW, CombGuard.readsViol, CombGuard.whole, CombGuard.BWin.inter, CombGuard.BWin.sub,
            CombGuard.BWin.subAll, List.lookup])) (detail := false)
        let eqPf ← mkAppM ``combGuardProc_of_admits #[admPf]
        let (r2, p2) ← convNorm r (← `(Lean.Parser.Tactic.Conv.convSeq|
          simp only [$(← exprToSyntax eqPf):term]))
        p ← mkEqTrans p p2
        r := r2
      let conds := allClosedConds r
      if !conds.isEmpty then
        if let some cond := conds.find? (·.hasAnyFVar fun fv => hs.any (·.fvarId! == fv)) then
          return NormRound.stuck r m!"a condition that mentions a decided one:{indentExpr cond}"
        return NormRound.need conds r (← mkLambdaFVars hs p)
      -- the private helpers unfolded
      let rd ← deltaExpand r isPrivateName
      if rd != r then
        let (r2, p2) ← (do match ← step (← `(Lean.Parser.Tactic.Conv.convSeq|
            simp only [Option.getD_some, Option.getD_none])) rd with
          | some x => pure x
          | none => pure (rd, ← mkEqRefl rd))
        p ← mkEqTrans (← mkExpectedTypeHint p (← mkEq lhs rd)) p2
        r := r2
      -- casts pulled out of the window offsets: `((↑i * ↑N + ↑j) * ↑AccW).toNat` is `(i * N + j) * AccW`
      if let some (r2, p2) ← step (← `(Lean.Parser.Tactic.Conv.convSeq|
          simp (disch := omega) only [SvGolf.Cycle.natCast_sub_one, SvGolf.Cycle.natCast_add_one',
            ← Int.natCast_mul, ← Int.natCast_add, Int.toNat_natCast])) r then
        p ← mkEqTrans p p2
        r := r2
      -- known literals of two or more bits as `LVec.ofBitVec (v#w)`
      if let some (r2, p2) ← (try foldLits r catch _ => pure none) then
        p ← mkEqTrans p p2
        r := r2
      if let some why ← firstUnfinished? r then
        return NormRound.stuck r m!"the instantiation leaves {why}"
      if r.hasAnyFVar (fun fv => hs.any (·.fvarId! == fv)) then
        return NormRound.stuck r m!"the normal form depends on a decided condition"
      return NormRound.done r (← mkLambdaFVars hs p)
    match round with
    | .done r pf =>
        verbose m!"sv_mirror: {what} ({rounds} round(s), {(← IO.monoMsNow) - t0} ms, of which {tCond} ms \
          deciding {facts.size - (← c.known.get).size} local condition(s)):{indentExpr r}"
        return (r, mkAppN pf (facts.map (·.2)))
    | .stuck r why =>
        throwError "sv_mirror: cannot instantiate {what}: {why}\nIf it is a window of a register family, \
          give a tactic that proves it with `sv_mirror X (window := by …) := …` (run on every side condition left, \
          with the genvars and their bounds in scope); otherwise report the construct.\nThe normal form:\
          {indentExpr r}"
    | .need conds r pAbs =>
        cur := some (r, pAbs)
        curK := facts.size
        let tc0 ← IO.monoMsNow
        let mut added := 0
        let mut undecided : Option Lean.Expr := none
        let mut seen : Option Lean.Expr := none
        for cond in conds do
          let ncond := mkNot cond
          if facts.any (fun f => f.1 == cond || f.1 == ncond) then
            seen := seen <|> some cond
            continue
          if let some pf ← proveCond c cond then
            verbose m!"sv_mirror: {what}: decided{indentExpr cond}"
            facts := facts.push (cond, pf)
            if global cond then c.known.modify (·.push (cond, pf))
            added := added + 1
          else if let some pf ← proveCond c ncond then
            verbose m!"sv_mirror: {what}: refuted{indentExpr cond}"
            facts := facts.push (ncond, pf)
            if global ncond then c.known.modify (·.push (ncond, pf))
            added := added + 1
          else
            undecided := undecided <|> some cond
        tCond := tCond + ((← IO.monoMsNow) - tc0)
        if added == 0 then
          if let some cond := undecided then
            throwError "sv_mirror: cannot instantiate {what}: the condition{indentExpr cond}\nis neither \
              proved nor refuted by `sv_disch`. If it is a window of a register family inside its vector, give \
              a tactic that proves it with `sv_mirror X (window := by …) := …` (it runs on the condition, with the \
              genvars and their bounds in scope)."
          if let some cond := seen then
            throwError "sv_mirror: cannot instantiate {what}: the condition{indentExpr cond}\nis decided but \
              `simp` does not use it"
  throwError "sv_mirror: cannot instantiate {what}: too many conditions"

/-- The `Nat` form of an `Int` loop bound `b` (`↑x`, sums, differences, products, numerals). -/
partial def natOfInt? (b : Lean.Expr) : MetaM (Option Lean.Expr) := do
  match_expr b with
  | Nat.cast _ _ x => return some x
  | Int.ofNat x => return some x
  | HAdd.hAdd _ _ _ _ x y => bin ``HAdd.hAdd x y
  | HSub.hSub _ _ _ _ x y => bin ``HSub.hSub x y
  | HMul.hMul _ _ _ _ x y => bin ``HMul.hMul x y
  | OfNat.ofNat _ n _ =>
      match n.rawNatLit? with
      | some k => return some (mkNatLit k)
      | none => return none
  | _ => return none
where
  bin (op : Name) (x y : Lean.Expr) : MetaM (Option Lean.Expr) := do
    let some x' ← natOfInt? x | return none
    let some y' ← natOfInt? y | return none
    return some (← mkAppM op #[x', y'])

/-- A generate loop or process item, walked: the processes it expands to and the expansion proof. -/
structure Walked where
  procs : Lean.Expr
  proof : Lean.Expr

/-- Make a fresh, unused process name `X.base` (`X.base_1`, … on a clash): neither it nor the names
`sv_cycle` derives from it (`X.baseQ`, `X.base_run`, `X.base_runQ`) may exist, be one of the commands' fixed
names, or be taken by (or derived from) another process of the design. -/
def freshName (c : Ctx) (base : Name) : TermElabM Name := do
  let env ← getEnv
  let taken ← c.taken.get
  let fixed := mirrorNames ++ cycleNames
  let free (n : Name) : Bool := (n :: derivedNames n).all fun m =>
    !env.contains (c.X ++ m) && !fixed.contains m && !taken.contains m
  let mut n := base
  let mut k := 0
  while !free n do
    k := k + 1
    n := base.appendAfter s!"_{k}"
  c.taken.set (taken ++ n :: derivedNames n)
  return n

mutual
/-- Walk a list of generate items in the environment `env` (genvars `gvs`, bounds `ghs` in scope). -/
partial def walkItems (c : Ctx) (env elems fuel : Lean.Expr) (gvs ghs : Array Lean.Expr) (label : Option String)
    (items : Array Lean.Expr) : TermElabM Walked := do
  if items.isEmpty then
    return { procs := ← mkAppOptM ``List.nil #[some (Lean.mkConst ``Process2)],
             proof := ← mkAppOptM ``expandList2_nil #[some env, some elems, some fuel] }
  let w ← walkItem c env elems fuel gvs ghs label items[0]!
  if items.size == 1 then
    return { procs := w.procs, proof := ← mkAppM ``expandList2_singleton_ok #[w.proof] }
  let rest ← walkItems c env elems fuel gvs ghs label items[1:].toArray
  return { procs := ← mkAppM ``HAppend.hAppend #[w.procs, rest.procs],
           proof := ← mkAppM ``expandList2_cons_ok #[w.proof, rest.proof] }

/-- Walk one generate item. -/
partial def walkItem (c : Ctx) (env elems fuel : Lean.Expr) (gvs ghs : Array Lean.Expr) (label : Option String)
    (it : Lean.Expr) : TermElabM Walked := do
  let (k, as) ← ctorOf it
  if k == ``GenItem.process then
    let p := as[0]!
    let (pk, _) ← ctorOf p
    unless pk == ``PProcess.alwaysFF do
      let why := if pk == ``PProcess.alwaysComb || pk == ``PProcess.assign || pk == ``PProcess.assignL then
          m!": a family of comb processes is not covered (their settle in every schedule order needs the \
            commutation of their runs over a permutation, `combPass2` of a family, which is not proved yet)"
        else m!""
      throwError "sv_mirror: refused: {← processKindRefusal p} inside generate block \
        `{label.getD "(unnamed)"}`{why}"
    let what := s!"the process of generate block `{label.getD "(unnamed)"}`"
    let base ← freshName c (labelName (label.getD "gen"))
    let lhs ← mkAppM ``instProcess2 #[env, elems, p]
    let (rhs, pf) ← instNorm c what lhs #[c.X ++ `env, c.X ++ `decls, c.X ++ `elems]
    if rhs.hasAnyFVar (fun fv => c.hyps.any (·.fvarId! == fv) || ghs.any (·.fvarId! == fv)) then
      throwError "sv_mirror: internal error: the instantiated process depends on a hypothesis"
    c.noteClock what (← scanFF what c.inputs rhs)
    addDefn (c.X ++ base) (c.params ++ gvs) rhs
      s!"The process of generate block `{label.getD "(unnamed)"}` at genvars {gvs.size}, instantiated (`sv_mirror`)."
    let leaf := c.app base gvs
    -- `(.process p).expand2 env elems F = .ok [instProcess2 env elems p] = .ok [leaf]`
    let h1 ← mkAppOptM ``GenItem.expand2_process #[some env, some elems, some fuel, some p]
    let hl ← mkListLit (Lean.mkConst ``Process2) [leaf]
    let ty ← mkEq (← mkAppM ``GenItem.expand2 #[env, elems, fuel, it]) (← mkAppM ``Res.ok #[hl])
    let okOne ← withLocalDeclD `x (Lean.mkConst ``Process2) fun x => do
      mkLambdaFVars #[x] (← mkAppM ``Res.ok #[← mkListLit (Lean.mkConst ``Process2) [x]])
    let proof ← mkExpectedTypeHint (← mkEqTrans h1 (← mkCongrArg okOne pf)) ty
    return { procs := hl, proof }
  else if k == ``GenItem.genFor then
    let lbl? : Option String ← do
      match ← ctorOf as[0]! with
      | (``Option.some, xs) => pure (strLit? (← whnf xs[1]!))
      | _ => pure none
    let some g := strLit? (← whnf as[1]!)
      | throwError "sv_mirror: internal error: a genvar name is not a string literal"
    let (ik, iargs) ← ctorOf as[2]!
    let initZero ← (do
      if ik == ``PExpr.int then
        let v ← whnf iargs[0]!
        isDefEq v (toExpr (0 : Int))
      else pure false)
    unless initZero do
      throwError "sv_mirror: refused: generate loop `{lbl?.getD g}` does not start at 0 (only `for (g = 0; g < e; g++)` is covered)"
    let (ck, cargs) ← ctorOf as[3]!
    let (sk, sargs) ← ctorOf as[4]!
    let okCond ← (do
      if ck == ``PExpr.binary then
        let (opk, _) ← ctorOf cargs[0]!
        let (lk, largs) ← ctorOf cargs[1]!
        pure (opk == ``SymBinOp.slt && lk == ``PExpr.genvarRef && strLit? (← whnf largs[0]!) == some g)
      else pure false)
    let okStep ← (do
      if sk == ``PExpr.unary then
        let (opk, _) ← ctorOf sargs[0]!
        let (ak, aargs) ← ctorOf sargs[1]!
        pure (opk == ``SymUnaryOp.inc && ak == ``PExpr.genvarRef && strLit? (← whnf aargs[0]!) == some g)
      else pure false)
    unless okCond && okStep do
      throwError "sv_mirror: refused: generate loop `{lbl?.getD g}` is not `for ({g} = 0; {g} < e; {g}++)` (a descending, stepped or `<=` loop is not covered)"
    let bound := cargs[2]!
    -- the bound, evaluated
    let (Mi, _) ← withLocalDeclD `i (Lean.mkConst ``Int) fun i => do
      let lhs ← mkAppM ``evalInt #[← mkAppM ``IEnv.bindVal #[env, mkStrLit g, i], bound]
      let (rhs, pf) ← instNorm c s!"the bound of generate loop `{lbl?.getD g}`" lhs
        #[c.X ++ `env, c.X ++ `decls, c.X ++ `elems]
      let some b := okPayload? rhs
        | throwError "sv_mirror: refused: the bound of generate loop `{lbl?.getD g}` does not evaluate:{indentExpr rhs}"
      if b.containsFVar i.fvarId! then
        throwError "sv_mirror: refused: the bound of generate loop `{lbl?.getD g}` depends on its genvar"
      return (b, pf)
    let some M ← natOfInt? Mi
      | throwError "sv_mirror: refused: the bound of generate loop `{lbl?.getD g}` is not a `Nat` expression of the parameters:{indentExpr Mi}"
    let envBind (i : Lean.Expr) : MetaM Lean.Expr := do mkAppM ``IEnv.bindVal #[env, mkStrLit g, i]
    -- `hei : ∀ i : Int, bound.isInt (env.bindVal g i) = true`, `he : ∀ i, evalInt … = .ok ↑M`
    let simpIds : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) ←
      #[c.X ++ `env, c.X ++ `decls, c.X ++ `elems].mapM fun n => `(Lean.Parser.Tactic.simpLemma| $(mkCIdent n):ident)
    let hei ← withLocalDeclD `i (Lean.mkConst ``Int) fun i => do
      let ty ← mkEq (← mkAppM ``PExpr.isInt #[← envBind i, bound]) (Lean.mkConst ``Bool.true)
      let pr ← proveBy s!"sv_mirror: the bound of generate loop `{lbl?.getD g}` is an integer" ty
        (← `(Lean.Parser.Tactic.tacticSeq| simp [PExpr.isInt, IEnv.bindVal, IEnv.withDecls, List.lookup,
              SymBinOp.intArith, $simpIds,*]))
      mkLambdaFVars #[i] pr
    let Mint ← mkAppOptM ``Nat.cast #[some (Lean.mkConst ``Int), none, some M]
    let he ← withLocalDeclD `i (Lean.mkConst ``Int) fun i => do
      let ty ← mkEq (← mkAppM ``evalInt #[← envBind i, bound])
        (← mkAppOptM ``Except.ok #[some (Lean.mkConst ``String), some (Lean.mkConst ``Int), some Mint])
      let pr ← proveBy s!"sv_mirror: refused: the bound of generate loop `{lbl?.getD g}` is not proved to be the \
          `Nat` `{← ppExpr M}` under the hypotheses (a bound such as `N - 1` needs a hypothesis that keeps it \
          non-negative, e.g. `1 ≤ N`)" ty
        (← `(Lean.Parser.Tactic.tacticSeq| first
              | (simp [evalInt, IEnv.bindVal, IEnv.withDecls, List.lookup, Gen2.except_ok_bind, $simpIds,*]; done)
              | (simp [evalInt, IEnv.bindVal, IEnv.withDecls, List.lookup, Gen2.except_ok_bind, $simpIds,*]
                 <;> push_cast <;> omega))) (detail := false)
      mkLambdaFVars #[i] pr
    let hF ← proveBy s!"sv_mirror: refused: the bound of generate loop `{lbl?.getD g}` is not proved below the \
        surface fuel `(s + 2) * (s + 2) + 64` (s the sum of the parameters), where the library's generate \
        expansion stops"
      (← mkAppM ``LT.lt #[M, fuel])
      (← `(Lean.Parser.Tactic.tacticSeq|
            simp only [PDesign.surfaceFuel, List.map, List.sum_cons, List.sum_nil, Int.natAbs_natCast]
            first
            | (apply SvGolf.Cycle.lt_fuel_of_le; omega)
            | (apply SvGolf.Cycle.lt_fuel_of_le_sq; apply Nat.mul_le_mul <;> omega))) (detail := false)
    let some body := listLitSyn? (← whnf as[6]!) <|> (← listLit? as[6]!)
      | throwError "sv_mirror: internal error: a generate body is not a list literal"
    withLocalDeclD (Name.mkSimple g) (Lean.mkConst ``Nat) fun v => do
    withLocalDeclD (Name.mkSimple ("h" ++ g)) (← mkAppM ``LT.lt #[v, M]) fun hv => do
      let vI ← mkAppOptM ``Nat.cast #[some (Lean.mkConst ``Int), none, some v]
      let env' ← envBind vI
      let wb ← walkItems c env' elems fuel (gvs.push v) (ghs.push hv) (lbl? <|> label) body
      let f ← mkLambdaFVars #[v] wb.procs
      let hf ← mkLambdaFVars #[v, hv] wb.proof
      let pr ← mkAppOptM ``SvGolf.GenItem.expand2_range_flatMap
        #[none, none, none, some as[0]!, none, none, some as[5]!, none, none, none, some hei, some he, some hF, some hf]
      -- the processes, as the lemma states them
      let procs ← mkAppM ``List.flatMap #[f, ← mkAppM ``List.range #[M]]
      return { procs, proof := pr }
  else if k == ``GenItem.genIf then
    throwError "sv_mirror: refused: a generate `if` (only generate `for` loops over processes are covered)"
  else if k == ``GenItem.inst then
    throwError "sv_mirror: refused: a module instance (hierarchy is not covered)"
  else if k == ``GenItem.unsupported then
    throwError "sv_mirror: refused: an out-of-tier generate item `{← whnf as[0]!}`"
  else
    throwError "sv_mirror: internal error: an unknown generate item {it}"
end

/-- One `(window := by tac)` option. -/
syntax svWindowOpt := " (" &"window" " := " term ")"

/--
`sv_mirror X := design (N … : Nat) (h₁ : …) …` writes the instantiated design at symbolic parameters and
proves it is what `instantiate2` builds (the module docstring of `SvGolf.Cycle`). The window tactic, when one
is needed, goes before `:=` (after the binders it would read as one more binder):
`sv_mirror X (window := by tac) := design …`.
-/
syntax (name := svMirror) "sv_mirror " ident (svWindowOpt)? " := " ident (ppSpace bracketedBinder)* : command

@[command_elab svMirror] def elabSvMirror : CommandElab := fun stx => do
  let Xs := stx[1].getId
  let dId := stx[4]
  let binders := stx[5].getArgs
  let window? : Option (TSyntax ``Lean.Parser.Tactic.tacticSeq) :=
    if stx[2].getNumArgs > 0 then
      let t := stx[2][0][3]
      if t.getKind == ``Lean.Parser.Term.byTactic then some ⟨t[1]⟩ else none
    else none
  if stx[2].getNumArgs > 0 && window?.isNone then
    throwErrorAt stx[2] "sv_mirror: `(window := by tac)` expects a `by` block"
  withScope (fun sc => { sc with opts := sc.opts.setBool `linter.unusedSimpArgs false
                                   |>.setBool `linter.unusedVariables false }) do
  liftTermElabM <| withStagesBudget <| atomically do
    let X := (← getCurrNamespace) ++ Xs
    let dName ← realizeGlobalConstNoOverloadWithInfo (mkIdentFrom dId (dId.getId ++ `pdesign))
    let semName ← realizeGlobalConstNoOverloadWithInfo (mkIdentFrom dId (dId.getId ++ `sem))
    let pdE := Lean.mkConst dName
    let some params ← listLit? (← mkAppM ``PDesign.params #[pdE])
      | throwError "sv_mirror: `{dName}` is not a literal design"
    let pNames ← params.mapM fun p => do
      return (strLit? (← whnf (← mkAppM ``PParam.name #[p]))).getD "?"
    -- the names this command defines must be free (a clash with the player's would be an obscure error)
    for n in mirrorNames do
      if (← getEnv).contains (X ++ n) then
        throwError "sv_mirror: `{X ++ n}` already exists (an earlier `sv_mirror {Xs}` or a declaration of yours): \
          choose another name than `{Xs}`"
    -- the binders, elaborated without error recovery: an ill-formed binder stops the command here
    Term.withoutErrToSorry <| elabBinders binders fun xs => do
      if xs.size < params.size then
        throwError "sv_mirror: `{dId}` has {params.size} parameters: give them first, as `Nat` binders"
      let ps := xs[:params.size].toArray
      let hs := xs[params.size:].toArray
      for p in ps, i in [:ps.size] do
        unless ← isDefEq (← inferType p) (Lean.mkConst ``Nat) do
          throwError "sv_mirror: the parameter `{p}` must be a `Nat`"
        -- the binders are matched to the design's parameters by position: a binder named after ANOTHER
        -- parameter is a swap (every theorem would be true, and about the swapped point)
        let b := (← p.fvarId!.getUserName).toString
        if b != pNames[i]! && pNames.contains b then
          throwError "sv_mirror: the binder `{b}` is in the position of the design's parameter `{pNames[i]!}`: \
            give the parameters in the design's order, ({" ".intercalate pNames.toList} : Nat)"
      for h in hs do
        unless ← Meta.isProp (← inferType h) do
          throwError "sv_mirror: after the parameters only hypotheses may follow (`{h}` is not a proposition)"
        if (← instantiateMVars (← inferType h)).hasSorry then
          throwError "sv_mirror: the hypothesis `{h}` contains `sorry`"
      let args ← ps.foldrM (fun (p : Lean.Expr) (acc : Lean.Expr) => do
        mkAppM ``List.cons #[← mkAppOptM ``Nat.cast #[some (Lean.mkConst ``Int), none, some p], acc])
        (← mkAppOptM ``List.nil #[some (Lean.mkConst ``Int)])
      let fieldLs ← designFieldLemmas dName
      let c0 : Ctx := { X, pdC := dName, semC := semName, params := ps, hyps := hs, args, window?, fields := fieldLs,
                        clock := ← IO.mkRef none, taken := ← IO.mkRef [], known := ← IO.mkRef #[] }
      let c := c0
      let all := ps ++ hs
      let tm0 ← IO.monoMsNow
      let mark (step : String) : TermElabM Unit := do
        verbose m!"sv_mirror: [{(← IO.monoMsNow) - tm0} ms] {step}"
      -- refusals that need no evaluation
      let (lpN, _) ← ctorOf (← mkAppM ``PDesign.packageParams #[pdE])
      unless lpN == ``List.nil do throwError "sv_mirror: refused: package parameters are not covered"
      let some others ← listLit? (← mkAppM ``PDesign.others #[pdE])
        | throwError "sv_mirror: internal error: `others` is not a list literal"
      unless others.isEmpty do
        throwError "sv_mirror: refused: the design has out-of-tier members ({others.size}): {← whnf others[0]!}"
      let some sprocs ← listLit? (← mkAppM ``PDesign.processes #[pdE])
        | throwError "sv_mirror: internal error: `processes` is not a list literal"
      let mut nComb := 0
      for p in sprocs do
        let (pk, _) ← ctorOf p
        if pk == ``PProcess.alwaysComb || pk == ``PProcess.assign || pk == ``PProcess.assignL then
          nComb := nComb + 1
          if nComb > 1 then
            throwError "sv_mirror: refused: a second comb process ({← processKindRefusal p}): one `always_comb` \
              or `assign` beside the `always_ff` processes is covered; several need the settle in every schedule \
              order of runs that read each other's outputs (a lemma that every order of `combPass2` reaches the \
              same fixpoint, from an acyclic order of the comb processes), which is not proved yet"
        else unless pk == ``PProcess.alwaysFF do
          throwError "sv_mirror: refused: {← processKindRefusal p}"
      mark "1. the parameter environment"
      -- 1. the parameter environment
      let lhsEnv ← mkAppM ``PDesign.paramEnv2 #[pdE, args]
      -- in two passes: the parameters and localparams first, then the dimension table of the declarations (in one
      -- pass `simp` takes ten times longer, measured)
      let (rhsEnv, pfEnv) ← convNorm lhsEnv (← `(Lean.Parser.Tactic.Conv.convSeq|
        simp (config := { decide := true }) [PDesign.paramEnv2, $fieldLs,*, bindPackageParams,
          bindPackageEnums, bindParamsRes, bindParams, bindLocals, bindLocal, evalIntTarget, evalInt, bindEnums,
          IEnv.bindVal, Gen2.except_ok_bind, Except.mapError, List.lookup, List.filterMapM,
          List.filterMapM.loop, SvGolf.Cycle.int_declConstType, SvGolf.Cycle.int_width,
          PType.width_packed_cons, PDim.width, *]
        try simp (config := { decide := true }) [dimTable, dimTableStep, PType.width_packed_cons, PDim.width,
          evalDims, evalInt, IEnv.bindVal, List.lookup, Gen2.except_ok_bind, *]))
      verbose m!"sv_mirror: parameter environment:{indentExpr rhsEnv}"
      -- a localparam chosen by a comparison of the parameters (`(AccW > W) ? AccW - W : 1`) leaves an `if`: the
      -- player states the case as a hypothesis, `simp` decides the comparison with it (one `sv_mirror` per case)
      if let some cond := firstClosedCond? rhsEnv then
        throwError "sv_mirror: refused: the parameter environment depends on the comparison{indentExpr cond}\n\
          of the parameters (a localparam chosen by it): give the case as a hypothesis, `(h : <the comparison>)`, \
          and a second `sv_mirror` under `(h : ¬ <the comparison>)` for the other case"
      let some envR := okPayload? rhsEnv
        | throwError "sv_mirror: refused: the parameter environment does not evaluate at symbolic parameters:{indentExpr rhsEnv}"
      addDefn (X ++ `env) ps envR "The parameter environment of the design (`sv_mirror`)."
      addThm (X ++ `paramEnv) all
        (← mkEq lhsEnv (← mkAppM ``Res.ok #[c.app `env])) pfEnv
        "`instantiate2`'s parameter environment (`sv_mirror`)."
      mark "2. the declarations"
      -- 2. the declarations
      let lhsD ← mkAppM ``buildDecls #[c.app `env, ← mkAppM ``PDesign.decls #[pdE]]
      let (rhsD, pfD) ← convNorm lhsD (← `(Lean.Parser.Tactic.Conv.convSeq|
        simp [$fieldLs,*, buildDecls, instDecl, PType.width_packed_cons, PDim.width, evalInt,
          $(mkCIdent (X ++ `env)):ident, List.lookup, Gen2.except_ok_bind]
        try simp (disch := sv_pos) only [SvGolf.Cycle.natCast_add_one', ← Int.natCast_mul, ← Int.natCast_add,
          ← Int.natCast_sub, Lib.natAbs_sub_one_add_one, Int.natAbs_natCast]))
      verbose m!"sv_mirror: declarations:{indentExpr rhsD}"
      let some declsR := okPayload? rhsD
        | throwError "sv_mirror: refused: the declarations do not evaluate:{indentExpr rhsD}"
      addDefn (X ++ `decls) ps declsR "The declarations, at the parameters (`sv_mirror`)."
      addThm (X ++ `buildDecls) all (← mkEq lhsD (← mkAppM ``Res.ok #[c.app `decls])) pfD
        "`instantiate2`'s declarations (`sv_mirror`)."
      let inputs := ((← readDecls declsR).filter (·.2.2.1)).map (·.1) |>.toList
      let c := { c with inputs }
      seedKnown c
      mark "3. the element widths"
      -- 3. the element widths
      let lhsE ← mkAppM ``buildElems #[c.app `env, ← mkAppM ``PDesign.decls #[pdE]]
      let (rhsE, pfE) ← convNorm lhsE (← `(Lean.Parser.Tactic.Conv.convSeq|
        simp [$fieldLs,*, buildElems, PType.width_packed_cons, PDim.width, evalInt,
          $(mkCIdent (X ++ `env)):ident, List.lookup, Gen2.except_ok_bind]))
      let some elemsR := okPayload? rhsE
        | throwError "sv_mirror: refused: the element widths do not evaluate:{indentExpr rhsE}"
      addDefn (X ++ `elems) ps elemsR "The element widths (`sv_mirror`)."
      addThm (X ++ `buildElems) all (← mkEq lhsE (← mkAppM ``Res.ok #[c.app `elems])) pfE
        "`instantiate2`'s element widths (`sv_mirror`)."
      let envD ← mkAppM ``IEnv.withDecls #[c.app `env, c.app `decls]
      mark "4. the static processes"
      -- 4. the static processes
      let mut statics : Array Lean.Expr := #[]
      if !sprocs.isEmpty then
        let lhsS ← mkAppM ``List.map #[← mkAppM ``instProcess2 #[envD, c.app `elems],
          ← mkAppM ``PDesign.processes #[pdE]]
        let (rhsS, pfS) ← instNorm c "the module's processes" lhsS #[X ++ `env, X ++ `decls, X ++ `elems]
        let some ls := listLitSyn? rhsS
          | throwError "sv_mirror: internal error: the processes did not normalize to a list:{indentExpr rhsS}"
        if rhsS.hasAnyFVar (fun fv => hs.any (·.fvarId! == fv)) then
          throwError "sv_mirror: internal error: the instantiated processes depend on a hypothesis"
        for i in [:ls.size] do
          let what := s!"the module's process {i} (in source order)"
          if ← isCombTerm ls[i]! then scanComb what c.inputs ls[i]!
          else c.noteClock what (← scanFF what c.inputs ls[i]!)
          let pn := Name.mkSimple s!"p{i}"
          let env ← getEnv
          if (pn :: derivedNames pn).any fun m => env.contains (X ++ m) then
            throwError "sv_mirror: `{X ++ pn}` or a name derived from it already exists: choose another name \
              than `{Xs}`"
          c.taken.modify (· ++ pn :: derivedNames pn)
          addDefn (X ++ pn) ps ls[i]!
            s!"The module's process {i} (in source order), instantiated (`sv_mirror`)."
          statics := statics.push (c.app pn)
        addThm (X ++ `static) all (← mkEq lhsS (← mkListLit (Lean.mkConst ``Process2) statics.toList)) pfS
          "`instantiate2`'s static processes (`sv_mirror`)."
      mark "5. the generate loops"
      -- 5. the generate loops
      let fuel ← mkAppM ``PDesign.surfaceFuel #[args]
      let some gens ← listLit? (← mkAppM ``PDesign.generates #[pdE])
        | throwError "sv_mirror: internal error: `generates` is not a list literal"
      let w ← walkItems c envD (c.app `elems) fuel #[] #[] none gens
      -- tidy the family: `flatMap (fun j => [p j])` is `map p`
      let (famR, pfFam) ← convNorm w.procs (← `(Lean.Parser.Tactic.Conv.convSeq|
        try simp only [← List.map_eq_flatMap, List.append_nil]))
      let gensE ← mkAppM ``PDesign.generates #[pdE]
      let lhsG ← mkAppM ``expandList2 #[envD, c.app `elems, fuel, gensE]
      let gensTy ← mkEq lhsG (← mkAppM ``Res.ok #[famR])
      let gensPf ← proveBy "sv_mirror: the generate expansion" gensTy
        (← `(Lean.Parser.Tactic.tacticSeq|
              rw [← $(← exprToSyntax pfFam):term]; exact $(← exprToSyntax w.proof):term))
      addThm (X ++ `gens) all gensTy gensPf "`instantiate2`'s generate expansion (`sv_mirror`)."
      mark "6. the process list and the design"
      -- 6. the process list and the design
      let procsB ← statics.foldrM (fun p acc => mkAppM ``List.cons #[p, acc]) famR
      addDefn (X ++ `procs) ps procsB "The instantiated processes, generate loops as `List.range` families (`sv_mirror`)."
      let some nm := strLit? (← whnf (← mkAppM ``PDesign.name #[pdE]))
        | throwError "sv_mirror: internal error: the design name is not a literal"
      let dB ← mkAppM ``Design2.mk #[mkStrLit nm, ← mkAppM ``List.toArray #[c.app `decls],
        ← mkAppM ``List.toArray #[c.app `procs]]
      addDefn (X ++ `D) ps dB "The instantiated design at the parameters (`sv_mirror`)."
      mark "7. instantiate2 is .ok (X.D …)"
      -- 7. `instantiate2` is `.ok (X.D …)`
      let instTy ← mkEq (← mkAppM ``PDesign.instantiate2 #[pdE, args, fuel]) (← mkAppM ``Res.ok #[c.app `D])
      let appAll (n : Name) : TermElabM Term := do
        exprToSyntax (mkAppN (Lean.mkConst (X ++ n)) all)
      let staticRw : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) ← if statics.isEmpty then pure #[] else
        pure #[← `(Lean.Parser.Tactic.simpLemma| $(← appAll `static):term)]
      let instPf ← proveBy "sv_mirror: `instantiate2`" instTy (← `(Lean.Parser.Tactic.tacticSeq|
        rw [PDesign.instantiate2_of_ok rfl $(← appAll `paramEnv) $(← appAll `buildDecls) $(← appAll `buildElems)
          $(← appAll `gens)]
        have hoth : ($(mkCIdent dName):ident).others = [] := rfl
        simp only [PDesign.assemble2, hoth, List.map_nil, List.append_nil, List.nil_append, $staticRw,*]
        rfl))
      addThm (X ++ `instantiate) all instTy instPf
        "**`instantiate2` builds `X.D`** at every parameter point the hypotheses allow (`sv_mirror`)."
      mark "done"
      logInfo m!"sv_mirror: defined {X}.env, .decls, .elems, {statics.size} static process(es), .procs, .D and \
        proved .instantiate"

/-! ## 4. `sv_cycle`: the clock step of the mirror -/

/-- The heads of a `List.cons` chain and its tail (`X.procs`: the static processes, then the families). -/
partial def consChain (e : Lean.Expr) : Array Lean.Expr × Lean.Expr :=
  if e.isAppOfArity ``List.cons 3 then
    let (hs, t) := consChain e.appArg!
    (#[e.appFn!.appArg!] ++ hs, t)
  else (#[], e)

/-- The names `sv_cycle` defines for a design with a comb process, besides `cycleNames`. -/
def combNames : List Name := [`comb, `comb_stable, `settle, `commit, `edgeQ]

/-- The constants `X.*` (other than `X.procs`) that occur in `e`: the processes of the mirror. -/
def mirrorLeaves (X : Name) (e : Lean.Expr) : Array Name :=
  e.foldConsts #[] fun n acc =>
    if X.isPrefixOf n && n != X ++ `procs && !acc.contains n then acc.push n else acc

/-- `sv_cycle X using h` (the module docstring of `SvGolf.Cycle`); `sv_cycle X (fuel := n) using h` starts the
fuel search at `n` (the option goes before `using`: after the term it would read as a named argument). -/
syntax (name := svCycle) "sv_cycle " ident (" (" &"fuel" " := " num ")")? " using " term : command

@[command_elab svCycle] def elabSvCycle : CommandElab := fun stx => do
  let Xs := stx[1].getId
  let hStx := stx[4]
  let fuel0 : Nat := if stx[2].getNumArgs > 0 then stx[2][0][3].isNatLit?.getD 30 else 30
  withScope (fun sc => { sc with opts := sc.opts.setBool `linter.unusedSimpArgs false
                                   |>.setBool `linter.unusedVariables false }) do
  liftTermElabM <| withStagesBudget <| atomically do
    let X := (← getCurrNamespace) ++ Xs
    let some instC := (← getEnv).find? (X ++ `instantiate)
      | throwError "sv_cycle: `{X}.instantiate` does not exist: run `sv_mirror {Xs} := …` first"
    -- the design: `design.pdesign.instantiate2 …` in the statement
    forallTelescope instC.type fun xs body => do
      let some (_, lhsI, _) := body.eq? | throwError "sv_cycle: internal error: `{X}.instantiate` is not an equation"
      let pdE := lhsI.getAppArgs[0]!
      let some pdC := pdE.constName? | throwError "sv_cycle: internal error: no design constant"
      let semC := pdC.getPrefix ++ `sem
      let nParams := (← getConstInfo (X ++ `D)).type.getForallBinderNames.length
      let ps := xs[:nParams].toArray
      let hs := xs[nParams:].toArray
      let all := ps ++ hs
      let app (n : Name) (extra : Array Lean.Expr := #[]) : Lean.Expr := mkAppN (Lean.mkConst (X ++ n)) (ps ++ extra)
      let thm (n : Name) : Lean.Expr := mkAppN (Lean.mkConst (X ++ n)) all
      let ident (n : Name) : Ident := mkCIdent (X ++ n)
      let lem (n : Name) : TermElabM (TSyntax ``Lean.Parser.Tactic.simpLemma) :=
        `(Lean.Parser.Tactic.simpLemma| $(mkCIdent n):ident)
      let fieldLs ← designFieldLemmas pdC
      -- the disjointness, elaborated without error recovery (an ill-typed term stops the command here, before
      -- any theorem is added)
      let procsE := app `procs
      let pairTy ← mkAppM ``List.Pairwise #[Lean.mkConst ``SvGolf.ProcDisj, procsE]
      let hE ← Term.withoutErrToSorry do
        let hE ← Term.elabTermEnsuringType hStx pairTy
        Term.synthesizeSyntheticMVarsNoPostponing
        instantiateMVars hE
      if hE.hasMVar then throwError "sv_cycle: the disjointness term has holes"
      if hE.hasSorry then
        throwError "sv_cycle: the disjointness term contains `sorry` (a lemma of yours may be unfinished while you \
          work; the command's argument may not)"
      -- the processes: refusals
      let procsV ← instantiateValueLevelParams (← getConstInfo (X ++ `procs)) []
      let procsB := procsV.beta ps
      let leaves := mirrorLeaves X procsB
      let leafSimps ← leaves.mapM lem
      -- the comb process, if any: one static `always_comb` or `assign` (`sv_mirror` refuses more)
      let (heads, famTail) := consChain procsB
      let mut comb? : Option Nat := none
      for i in [:heads.size] do
        if ← isCombTerm heads[i]! then comb? := some i
      let mixed := comb?.isSome
      -- the names this command defines must be free
      let env ← getEnv
      for n in cycleNames ++ (if mixed then combNames else []) ++
          (leaves.toList.flatMap fun l => derivedNames l.componentsRev.head! ++ [l.componentsRev.head!.appendAfter "_comb"]) do
        if env.contains (X ++ n) then
          throwError "sv_cycle: `{X ++ n}` already exists (an earlier `sv_cycle {Xs}` or a declaration of yours)"
      let tm0 ← IO.monoMsNow
      let mark (step : String) : TermElabM Unit := do
        verbose m!"sv_cycle: [{(← IO.monoMsNow) - tm0} ms] {step}"
      -- 1. sem_eq
      let semTy ← mkEq (mkAppN (Lean.mkConst semC) ps) (app `D)
      let hTerm ← exprToSyntax hE
      let semPf ← if mixed then proveBy "sv_cycle: the one-driver rule" semTy (← `(Lean.Parser.Tactic.tacticSeq|
        show PDesign.instantiateGD2 _ _ = _
        refine PDesign.instantiateGD2_of_ok $(← exprToSyntax (thm `instantiate)) ?_
        refine SvGolf.Cycle.driversOk_of_procDisj ?_ ?_ (SvGolf.Cycle.noInput_of_all ?_) ?_
        · simp (config := { decide := true }) [$(ident `D):ident, $(ident `procs):ident, driverWins,
            Process2.drvWins, Lhs2.drvWins, Lhs2.drvWinsList, PDesign.declNames, $fieldLs,*, List.flatMap_cons,
            List.flatMap_append, List.flatMap_map, $leafSimps,*]
        · simp (config := { decide := true }) [$(ident `D):ident, $(ident `procs):ident, driverWins,
            Process2.drvWins, Lhs2.drvWins, Lhs2.drvWinsList, PDesign.declNames, PDesign.inputNames, $fieldLs,*,
            Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList, CaseItem2.drvWinsList,
            CaseItem2.drvWins, DrvWin.overlaps, List.forall_mem_flatMap, List.forall_mem_map, $leafSimps,*]
        · simp (config := { decide := true }) [$(ident `D):ident, $(ident `procs):ident, List.all_append,
            List.all_flatMap, List.all_map, List.all_cons, PDesign.inputNames, $fieldLs,*,
            Process2.procWrites, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList,
            Lhs2.drvWins, Lhs2.drvWinsList, CaseItem2.drvWinsList, CaseItem2.drvWins, $leafSimps,*]
        · exact $hTerm))
      else proveBy "sv_cycle: the one-driver rule" semTy (← `(Lean.Parser.Tactic.tacticSeq|
        show PDesign.instantiateGD2 _ _ = _
        refine PDesign.instantiateGD2_of_ok $(← exprToSyntax (thm `instantiate)) ?_
        refine driversOk_of_ff (SvGolf.Cycle.ff_of_all ?_) (SvGolf.Cycle.noInput_of_all ?_) ?_
        · simp (config := { decide := true }) [$(ident `D):ident, $(ident `procs):ident, List.all_append,
            List.all_flatMap, List.all_map, List.all_cons, SvGolf.Cycle.isFF, $leafSimps,*]
        · simp (config := { decide := true }) [$(ident `D):ident, $(ident `procs):ident, List.all_append,
            List.all_flatMap, List.all_map, List.all_cons, PDesign.inputNames, $fieldLs,*,
            Process2.procWrites, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList,
            Lhs2.drvWins, Lhs2.drvWinsList, CaseItem2.drvWinsList, CaseItem2.drvWins, $leafSimps,*]
        · exact $hTerm))
      addThm (X ++ `sem_eq) all semTy semPf
        "**The loaded family is the mirror** `X.D` at every parameter point the hypotheses allow (`sv_cycle`)."
      mark "2. the profile"
      -- 2. the profile (an FF-only design; with a comb process the cycle is put together from its parts)
      if !mixed then
        let profTy ← mkEq (← mkAppM ``Design2.ffOnlyProfileB #[app `D]) (Lean.mkConst ``Bool.true)
        let profPf ← proveBy "sv_cycle: the FF-only profile" profTy (← `(Lean.Parser.Tactic.tacticSeq|
          simp only [Design2.ffOnlyProfileB, Bool.and_eq_true]
          refine ⟨?_, ffDisjB_of_pairwise $hTerm⟩
          simp (config := { decide := true }) [$(ident `D):ident, $(ident `procs):ident, $(ident `decls):ident,
            List.all_append, List.all_flatMap, List.all_map, List.all_cons, Stmt2.nbaOnly, Stmt2.optNbaOnly,
            Stmt2.listNbaOnly, CaseItem2.listNbaOnly, Stmt2.nbaStaticB, Stmt2.optNbaStaticB, Stmt2.listNbaStaticB,
            CaseItem2.listNbaStaticB, Lhs2.window?, Design2.declWidth, Design2.inputNames, Stmt2.drvWins,
            Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins, Lhs2.drvWinsList, CaseItem2.drvWinsList,
            CaseItem2.drvWins, $leafSimps,*]))
        addThm (X ++ `profile) all profTy profPf "The mirror is in the FF-only profile (`sv_cycle`)."
      mark "3. the positional state"
      -- 3. the positional state
      let decls ← readDecls (← whnfD (app `decls))
      let lvT := Lean.mkConst ``LVec
      let sigNames := decls.map fun (n, _) => Name.mkSimple (n.map fun c => if c.isAlphanum || c == '_' then c else '_')
      let pairsOf (vs : Array Lean.Expr) : MetaM Lean.Expr := do
        let ents ← (decls.zip vs).mapM fun ((n, _), v) => mkAppM ``Prod.mk #[mkStrLit n, v]
        mkListLit (← mkAppM ``Prod #[Lean.mkConst ``String, lvT]) ents.toList
      withLocalDeclsDND (sigNames.map (·, lvT)) fun vs => do
      addDefn (X ++ `St) vs (← pairsOf vs)
        "The positional state of the mirror: one value per declaration, in declaration order (`sv_cycle`)."
      let st (ws : Array Lean.Expr) : Lean.Expr := mkAppN (Lean.mkConst (X ++ `St)) ws
      mark "4. the inputs of a cycle"
      -- 4. the inputs of a cycle
      withLocalDeclD `e (← mkAppM ``List #[← mkAppM ``Prod #[Lean.mkConst ``String, lvT]]) fun e => do
      let applied ← (decls.zip vs).mapM fun ((n, _, isIn, tw), v) => do
        if !isIn then return v
        else if tw then
          return ← mkAppM ``Option.getD #[← mkAppM ``Option.map #[Lean.mkConst ``LVec.toTwoState,
            ← mkAppM ``SvState.lookup #[e, mkStrLit n]], v]
        else return ← mkAppM ``appIn #[e, mkStrLit n, v]
      let applyTy ← mkEq (← mkAppM ``applyInputs2 #[app `D, e, st vs]) (st applied)
      let applyPf ← proveBy "sv_cycle: the inputs of a cycle" applyTy (← `(Lean.Parser.Tactic.tacticSeq|
        rw [SvGolf.Cycle.applyInputs2_eq_map _ _ _ (by simp [$(ident `St):ident, $(ident `D):ident,
          $(ident `decls):ident]) (by simp [$(ident `D):ident, $(ident `decls):ident])]
        simp [$(ident `St):ident, $(ident `D):ident, $(ident `decls):ident, SvGolf.Cycle.appInDecl, appIn]))
      addThm (X ++ `apply) (ps ++ #[e] ++ vs) applyTy applyPf
        "The inputs of a cycle, applied to the positional state (`sv_cycle`)."
      mark "5. per process: its updates and its run"
      -- 5. per process: its updates and its run
      withLocalDeclD `f (Lean.mkConst ``Nat) fun fv => do
      let mut K := fuel0
      let mut leafInfo : Array (Name × Nat) := #[]   -- (leaf, number of genvars)
      let mut runQSimps : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) := #[]
      let mut runSimps : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) := #[]
      let mut gvNames : Array (Array Name) := #[]
      for leaf in leaves do
        let lty ← inferType (Lean.mkConst leaf)
        let ngv := lty.getForallBinderNames.length - nParams
        leafInfo := leafInfo.push (leaf, ngv)
        let rec lamNames : Lean.Expr → List Name
          | .lam n _ b _ => n :: lamNames b
          | _ => []
        let names := (lamNames ((← getConstInfo leaf).value!)).drop nParams
        gvNames := gvNames.push ((Array.range ngv).map fun k => names.getD k (Name.mkSimple s!"g{k}"))
      -- the fuel: enough for every process (doubled until no run is stuck)
      let mut done := false
      let mut results : Array (Name × Nat × Lean.Expr × Lean.Expr) := #[]   -- leaf, ngv, Q (abstracted over gvs), proof
      for _ in [0:4] do
        if done then break
        results := #[]
        let mut stuck := false
        for ((leaf, ngv), gns) in leafInfo.zip gvNames do
          let r ← withLocalDeclsDND (gns.map fun n => (n, Lean.mkConst ``Nat)) fun gvs => do
            let P := mkAppN (Lean.mkConst leaf) (ps ++ gvs)
            let lhs ← mkAppM ``runEdgeProcess2 #[← mkAppM ``HAdd.hAdd #[fv, mkNatLit K], st vs,
              ← mkAppOptM ``List.nil #[some (← mkAppM ``Prod #[Lean.mkConst ``String,
                ← mkAppM ``Prod #[Lean.mkConst ``Nat, lvT]])], P]
            let (rhs, pf) ← convNorm lhs (← `(Lean.Parser.Tactic.Conv.convSeq|
              simp only [↓ SvGolf.Cycle.evalExpr2_scmp, ↓ SvGolf.Cycle.evalExpr2_index, runEdgeProcess2, execStmt2,
                execStmts2, evalExpr2, evalExprs2, resolveLhs2, readSignal,
                $(ident `St):ident, SvState.lookup, evalBinOp, evalUnaryOp, Res.ok_bind, Res.pure_eq,
                SvGolf.Cycle.ite_res_ok, SvGolf.Cycle.ite_pair, List.nil_append, List.toList_toArray,
                Array.toArray_toList, $(mkCIdent leaf):ident, beq_iff_eq, String.reduceEq, ↓reduceIte,
                Bool.false_eq_true, Bool.true_eq_false, Option.some.injEq, List.singleton_append,
                List.cons_append, List.append_assoc, SvGolf.Cycle.ite_append_self, SvGolf.Cycle.ite_self_append]))
            verbose m!"sv_cycle: the run of {leaf}:{indentExpr rhs}"
            let some payload := okPayload? rhs
              | return (none, some m!"the run of `{leaf}` is not a success:{indentExpr rhs}")
            let payload ← whnfR payload
            unless payload.isAppOfArity ``Prod.mk 4 do
              return (none, some m!"the run of `{leaf}` is not a pair:{indentExpr payload}")
            let Q := payload.appArg!
            if (Q.find? fun t => t.isAppOf ``execStmt2 || t.isAppOf ``evalExpr2 || t.isAppOf ``execStmts2
                || t.isAppOf ``evalExprs2 || t.isAppOf ``resolveLhs2).isSome then
              return (none, none)   -- out of fuel: try a larger one
            if let some why ← firstUnfinished? Q (allowIte := true) then
              return (none, some m!"the updates of `{leaf}` leave {why}")
            unless ← isDefEq (payload.appFn!.appArg!) (st vs) do
              return (none, some m!"the run of `{leaf}` changes the state")
            return (some (← mkLambdaFVars gvs Q, ← mkLambdaFVars (gvs) pf), none)
          match r with
          | (some (Q, pf), _) => results := results.push (leaf, ngv, Q, pf)
          | (none, some why) => throwError "sv_cycle: refused: {why}"
          | (none, none) => stuck := true
        if stuck then K := 2 * K else done := true
      unless done do throwError "sv_cycle: a process run needs more fuel than {K}"
      for ((leaf, ngv, Q, pf), gns) in results.zip gvNames do
        let _ := ngv
        let base := leaf.componentsRev.head!
        let qName := X ++ base.appendAfter "Q"
        -- `X.<leaf>Q params gvs xs`
        withLocalDeclsDND (gns.map fun n => (n, Lean.mkConst ``Nat)) fun gvs => do
          let Qb := Q.beta gvs
          addDefn qName (ps ++ gvs ++ vs) Qb s!"The updates `{leaf}` issues on the state `X.St …` (`sv_cycle`)."
          let P := mkAppN (Lean.mkConst leaf) (ps ++ gvs)
          let qApp := mkAppN (Lean.mkConst qName) (ps ++ gvs ++ vs)
          let fuelE ← mkAppM ``HAdd.hAdd #[fv, mkNatLit K]
          let nilQ ← mkAppOptM ``List.nil #[some (← mkAppM ``Prod #[Lean.mkConst ``String,
                ← mkAppM ``Prod #[Lean.mkConst ``Nat, lvT]])]
          let runTy ← mkEq (← mkAppM ``runEdgeProcess2 #[fuelE, st vs, nilQ, P])
            (← mkAppM ``Res.ok #[← mkAppM ``Prod.mk #[st vs, qApp]])
          addThm (X ++ base.appendAfter "_run") (ps ++ gvs ++ vs ++ #[fv]) runTy (pf.beta gvs)
            s!"The run of `{leaf}` on `X.St …` at every fuel from {K} (`sv_cycle`)."
          let runQTy ← mkEq (← mkAppM ``SvGolf.Cycle.runQ #[fuelE, st vs, P]) qApp
          let runQPf ← mkAppM ``SvGolf.Cycle.runQ_of #[mkAppN (Lean.mkConst (X ++ base.appendAfter "_run")) (ps ++ gvs ++ vs ++ #[fv])]
          addThm (X ++ base.appendAfter "_runQ") (ps ++ gvs ++ vs ++ #[fv]) runQTy runQPf
            s!"The updates of `{leaf}`, as `runQ` (`sv_cycle`)."
        runQSimps := runQSimps.push (← lem (X ++ base.appendAfter "_runQ"))
        runSimps := runSimps.push (← lem (X ++ base.appendAfter "_run"))
      if mixed then
        let c := comb?.get!
        let Pc := heads[c]!
        let pcLeaf := Pc.getAppFn.constName!
        let fuelE ← mkAppM ``HAdd.hAdd #[fv, mkNatLit K]
        mark "5b. the comb process"
        -- 5b. the comb process: one run on `X.St …`, its values, their stability, the settle
        let lhsC ← mkAppM ``runCombProcess2 #[fuelE, st vs, Pc]
        let (rhsC, pfC) ← convNorm lhsC (← `(Lean.Parser.Tactic.Conv.convSeq|
          simp only [↓ SvGolf.Cycle.evalExpr2_scmp, ↓ SvGolf.Cycle.evalExpr2_index, runCombProcess2, execStmt2,
            execStmts2, evalExpr2, evalExprs2, resolveLhs2, readSignal, $(ident `St):ident, SvState.lookup,
            SvState.set, evalBinOp, evalUnaryOp, Res.ok_bind, Res.pure_eq, SvGolf.Cycle.ite_res_ok,
            SvGolf.Cycle.ite_pair, List.nil_append, List.toList_toArray, Array.toArray_toList,
            $(mkCIdent pcLeaf):ident, beq_iff_eq, String.reduceEq, ↓reduceIte, Bool.false_eq_true,
            Bool.true_eq_false, Option.some.injEq, LVec.insertAt_zero_of_width_eq, LVec.width_resizeU,
            LVec.width_insertAt]))
        verbose m!"sv_cycle: the run of the comb process {pcLeaf}:{indentExpr rhsC}"
        let some stC := okPayload? rhsC
          | throwError "sv_cycle: refused: the run of the comb process `{pcLeaf}` is not a success:{indentExpr rhsC}"
        if (stC.find? fun t => t.isAppOf ``execStmt2 || t.isAppOf ``evalExpr2 || t.isAppOf ``execStmts2
            || t.isAppOf ``evalExprs2 || t.isAppOf ``resolveLhs2).isSome then
          throwError "sv_cycle: the run of the comb process `{pcLeaf}` needs more fuel than {K}: give \
            `sv_cycle {Xs} (fuel := {2 * K}) using …`"
        if let some why ← firstUnfinished? stC (allowIte := true) then
          throwError "sv_cycle: refused: the values of the comb process `{pcLeaf}` leave {why}"
        let some ents := listLitSyn? stC
          | throwError "sv_cycle: refused: the run of the comb process `{pcLeaf}` does not keep the state's \
              shape:{indentExpr stC}"
        unless ents.size == decls.size do
          throwError "sv_cycle: refused: the run of the comb process `{pcLeaf}` does not keep the state's \
            shape:{indentExpr stC}"
        let mut ys : Array Lean.Expr := #[]
        let mut combDefs : Array Name := #[]
        for k in [:ents.size] do
          let en ← whnfR ents[k]!
          unless en.isAppOfArity ``Prod.mk 4 do
            throwError "sv_cycle: internal error: a binding of the comb run's state: {en}"
          unless strLit? (← whnf en.appFn!.appArg!) == some decls[k]!.1 do
            throwError "sv_cycle: refused: the run of the comb process `{pcLeaf}` does not keep the state's \
              shape:{indentExpr stC}"
          let v := en.appArg!
          if v == vs[k]! then ys := ys.push vs[k]!
          else
            let cn := X ++ Name.mkSimple ("comb_" ++ (decls[k]!.1.map fun ch => if ch.isAlphanum || ch == '_' then ch else '_'))
            if (← getEnv).contains cn then
              throwError "sv_cycle: `{cn}` already exists (an earlier `sv_cycle {Xs}` or a declaration of yours)"
            addDefn cn (ps ++ vs) v
              s!"The value of `{decls[k]!.1}` after one run of the comb process `{pcLeaf}` on `X.St …` (`sv_cycle`)."
            combDefs := combDefs.push cn
            ys := ys.push (mkAppN (Lean.mkConst cn) (ps ++ vs))
        addDefn (X ++ `comb) (ps ++ vs) (st ys)
          "The settled state: `X.St …` with the comb process's values (`sv_cycle`)."
        let combApp (ws : Array Lean.Expr) : Lean.Expr := mkAppN (Lean.mkConst (X ++ `comb)) (ps ++ ws)
        let combRunN := X ++ (pcLeaf.componentsRev.head!).appendAfter "_comb"
        addThm combRunN (ps ++ vs ++ #[fv]) (← mkEq lhsC (← mkAppM ``Res.ok #[combApp vs])) pfC
          s!"One run of the comb process `{pcLeaf}` on `X.St …`, at every fuel from {K} (`sv_cycle`)."
        let combDefIds ← combDefs.mapM lem
        let stableTy ← mkEq (combApp ys) (combApp vs)
        let stablePf ← proveBy s!"sv_cycle: refused: the values of the comb process `{pcLeaf}` are not proved \
            stable (a second run on them changes them: the process reads a signal it writes, other than through \
            its width; the settle of such a process needs a rank argument over its passes, not proved yet)"
          stableTy (← `(Lean.Parser.Tactic.tacticSeq|
            simp [$(ident `comb):ident, $(ident `St):ident, $combDefIds,*, LVec.width_resizeU, LVec.width_insertAt]))
          (detail := false)
        addThm (X ++ `comb_stable) (ps ++ vs) stableTy stablePf
          "The comb process's values are settled: a second run gives them again (`sv_cycle`)."
        -- the comb process is the only comb index
        let pre := heads.extract 0 c
        let post ← (heads.extract (c + 1) heads.size).foldrM (fun h acc => mkAppM ``List.cons #[h, acc]) famTail
        let preL ← mkListLit (Lean.mkConst ``Process2) pre.toList
        let splitTy ← mkEq (← mkAppM ``Array.toList #[← mkAppM ``Design2.processes #[app `D]])
          (← mkAppM ``HAppend.hAppend #[preL, ← mkAppM ``List.cons #[Pc, post]])
        let splitPf ← mkExpectedTypeHint (← proveBy "sv_cycle: the process list" splitTy
          (← `(Lean.Parser.Tactic.tacticSeq| first | rfl | simp [$(ident `D):ident, $(ident `procs):ident]))) splitTy
        let hPTy ← mkEq (← mkAppM ``Process2.isCombPhase #[Pc]) (Lean.mkConst ``Bool.true)
        let hPPf ← mkExpectedTypeHint (← proveBy "sv_cycle: the comb process" hPTy
          (← `(Lean.Parser.Tactic.tacticSeq| first | rfl | simp [$(mkCIdent pcLeaf):ident, Process2.isCombPhase])))
          hPTy
        let notComb ← withLocalDeclD `p (Lean.mkConst ``Process2) fun p => do
          mkLambdaFVars #[p] (← mkAppM ``not #[← mkAppM ``Process2.isCombPhase #[p]])
        let tacAll ← `(Lean.Parser.Tactic.tacticSeq| simp [Process2.isCombPhase, List.all_cons, List.all_append,
          List.all_map, List.all_flatMap, $leafSimps,*])
        let preTy ← mkEq (← mkAppM ``List.all #[preL, notComb]) (Lean.mkConst ``Bool.true)
        let postTy ← mkEq (← mkAppM ``List.all #[post, notComb]) (Lean.mkConst ``Bool.true)
        let hpre ← mkExpectedTypeHint (← proveBy "sv_cycle: the processes before the comb process" preTy tacAll)
          preTy
        let hpost ← mkExpectedTypeHint (← proveBy "sv_cycle: the processes after the comb process" postTy tacAll)
          postTy
        let hci ← mkAppM ``SvGolf.Cycle.combIndices_of_split #[splitPf, hPPf, hpre, hpost]
        let hciS ← exprToSyntax hci
        withLocalDeclD `σ (Lean.mkConst ``ScheduleOracle) fun σ => do
        withLocalDeclD `kk (Lean.mkConst ``Nat) fun kv => do
        let exOk (lhs rhsSt : Lean.Expr) : MetaM Lean.Expr := do
          let ex ← withLocalDeclD `k' (Lean.mkConst ``Nat) fun k' => do
            mkLambdaFVars #[k'] (← mkEq lhs (← mkAppM ``Res.ok #[← mkAppM ``Prod.mk #[rhsSt, k']]))
          mkAppM ``Exists #[ex]
        withLocalDeclD `F (Lean.mkConst ``Nat) fun Fv => do
        withLocalDeclD `hF (← mkAppM ``LE.le #[mkNatLit (K + 2), Fv]) fun hFv => do
          let settleTy ← exOk (← mkAppM ``combSettle2 #[app `D, σ, Fv, st vs, kv]) (combApp vs)
          let runS (ws : Array Lean.Expr) : TermElabM Term := exprToSyntax (mkAppN (Lean.mkConst combRunN) (ps ++ ws))
          let stableS ← exprToSyntax (mkAppN (Lean.mkConst (X ++ `comb_stable)) (ps ++ vs))
          let settlePf ← proveBy "sv_cycle: the comb settle" settleTy (← `(Lean.Parser.Tactic.tacticSeq|
            exact SvGolf.Cycle.combSettle2_single ($hciS).1 ($hciS).2 $(← exprToSyntax σ) $(← exprToSyntax hFv)
              (fun f hf => by
                obtain ⟨g, hg⟩ : ∃ g, f = g + $(quote K) := ⟨f - $(quote K), by omega⟩
                subst hg
                exact $(← runS vs) g)
              (fun f hf => by
                obtain ⟨g, hg⟩ : ∃ g, f = g + $(quote K) := ⟨f - $(quote K), by omega⟩
                subst hg
                exact ($(← runS ys) g).trans (congrArg Res.ok $stableS))
              $(← exprToSyntax kv)))
          addThm (X ++ `settle) (ps ++ hs ++ vs ++ #[σ, Fv, kv, hFv]) settleTy settlePf
            s!"**The comb settle** of the loaded design's mirror from `X.St …`, any schedule, any fuel from \
              {K + 2}: the comb process's values, `X.comb` (`sv_cycle`)."
        mark "6. the updates at the edge and the next state"
        -- 6. the updates at the edge, the commit entry by entry, the next state
        let allQ ← mkAppM ``List.flatMap #[← mkAppM ``SvGolf.Cycle.runQ #[fuelE, st vs],
          ← mkAppM ``Array.toList #[← mkAppM ``Design2.processes #[app `D]]]
        let (qN, qPf) ← convNorm allQ (← `(Lean.Parser.Tactic.Conv.convSeq|
          simp only [$(ident `D):ident, List.toList_toArray, $(ident `procs):ident, List.flatMap_append,
            List.flatMap_cons, List.flatMap_nil, List.append_nil, List.flatMap_assoc, List.flatMap_map,
            $runQSimps,*]))
        if qN.containsFVar fv.fvarId! then
          throwError "sv_cycle: internal error: the updates still mention the fuel:{indentExpr qN}"
        addDefn (X ++ `edgeQ) (ps ++ vs) qN
          "The updates of every process at the clock edge, on `X.St …`, in process order (`sv_cycle`)."
        let edgeQApp (ws : Array Lean.Expr) : Lean.Expr := mkAppN (Lean.mkConst (X ++ `edgeQ)) (ps ++ ws)
        addThm (X ++ `updates) (ps ++ vs ++ #[fv]) (← mkEq allQ (edgeQApp vs)) qPf
          "The updates of every process on `X.St …`, in process order (`sv_cycle`)."
        let qT ← mkAppM ``List #[← mkAppM ``Prod #[Lean.mkConst ``String, ← mkAppM ``Prod #[Lean.mkConst ``Nat, lvT]]]
        let folded (q : Lean.Expr) (ws : Array Lean.Expr) : MetaM (Array Lean.Expr) :=
          (decls.zip ws).mapM fun ((n, _), w) => mkAppM ``nbaFold #[mkStrLit n, q, w]
        withLocalDeclD `q qT fun qv => do
          let commitTy ← mkEq (← mkAppM ``commitNba2 #[st vs, qv]) (st (← folded qv vs))
          let commitPf ← proveBy "sv_cycle: the commit" commitTy (← `(Lean.Parser.Tactic.tacticSeq|
            rw [SvGolf.commitNba2_eq_map _ _ (by simp [$(ident `St):ident])]
            rfl))
          addThm (X ++ `commit) (vs ++ #[qv]) commitTy commitPf
            "The commit of updates on `X.St …`, signal by signal (`sv_cycle`)."
        let zs ← folded (edgeQApp ys) ys
        addDefn (X ++ `next) (ps ++ vs) (combApp zs)
          "One cycle's next state from the pre-edge values (inputs applied): the comb process settled, every \
          process's updates on that state committed, the comb process settled again (`sv_cycle`)."
        let nextApp (ws : Array Lean.Expr) := mkAppN (Lean.mkConst (X ++ `next)) (ps ++ ws)
        mark "7. the cycle"
        -- 7. the cycle
        -- every process runs on a positional state and leaves it alone
        let hallTy ← withLocalDeclD `p (Lean.mkConst ``Process2) fun p => do
          let mem ← mkAppM ``Membership.mem #[← mkAppM ``Array.toList #[← mkAppM ``Design2.processes #[app `D]], p]
          let nilQ ← mkAppOptM ``List.nil #[some (← mkAppM ``Prod #[Lean.mkConst ``String,
            ← mkAppM ``Prod #[Lean.mkConst ``Nat, lvT]])]
          let ex ← withLocalDeclD `q qT fun q => do
            let eq ← mkEq (← mkAppM ``runEdgeProcess2 #[fuelE, st vs, nilQ, p])
              (← mkAppM ``Res.ok #[← mkAppM ``Prod.mk #[st vs, q]])
            mkAppM ``Exists #[← mkLambdaFVars #[q] eq]
          mkForallFVars #[p] (← mkArrow mem ex)
        let hallPf ← proveBy "sv_cycle: every process runs" hallTy (← `(Lean.Parser.Tactic.tacticSeq|
          simp only [$(ident `D):ident, List.toList_toArray, $(ident `procs):ident, List.forall_mem_cons,
            List.forall_mem_flatMap, List.forall_mem_map, List.forall_mem_append]
          simp [$runSimps,*]))
        let hallGen ← mkLambdaFVars (vs ++ #[fv]) hallPf
        let ysA := ys.map (·.replaceFVars vs applied)
        let zsA := zs.map (·.replaceFVars vs applied)
        let fv2 ← mkAppM ``HAdd.hAdd #[fv, mkNatLit 2]
        let fuelM ← mkAppM ``HAdd.hAdd #[fv2, mkNatLit K]
        withLocalDeclD `σ (Lean.mkConst ``ScheduleOracle) fun σ => do
        withLocalDeclD `kk (Lean.mkConst ``Nat) fun kv => do
        let exOk (lhs rhsSt : Lean.Expr) : MetaM Lean.Expr := do
          let ex ← withLocalDeclD `k' (Lean.mkConst ``Nat) fun k' => do
            mkLambdaFVars #[k'] (← mkEq lhs (← mkAppM ``Res.ok #[← mkAppM ``Prod.mk #[rhsSt, k']]))
          mkAppM ``Exists #[ex]
        let cycTy ← exOk (← mkAppM ``cycleStep2 #[mkAppN (Lean.mkConst semC) ps, σ, fuelM, e, st vs, kv])
          (nextApp applied)
        let hapS ← exprToSyntax (mkAppN (Lean.mkConst (X ++ `apply)) (ps ++ #[e] ++ vs))
        let settleS (ws : Array Lean.Expr) : TermElabM Term :=
          exprToSyntax (mkAppN (Lean.mkConst (X ++ `settle)) (ps ++ hs ++ ws ++ #[σ, fuelM]))
        let cycPf ← proveBy "sv_cycle: the clock step" cycTy (← `(Lean.Parser.Tactic.tacticSeq|
          rw [$(← exprToSyntax (thm `sem_eq)):term]
          exact SvGolf.Cycle.cycleStep2_mixed $(← exprToSyntax σ) $(← exprToSyntax e) _ $(← exprToSyntax kv)
            (S1 := $(← exprToSyntax (st ysA))) (S2 := $(← exprToSyntax (nextApp applied)))
            (fun j => by
              rw [$hapS:term]
              exact $(← settleS applied) j (by omega))
            (SvGolf.Cycle.resetIndices_nil_of (by
              simp [$(ident `D):ident, $(ident `procs):ident, SvGolf.Cycle.isResetProc, List.all_cons,
                List.all_append, List.all_map, List.all_flatMap, $leafSimps,*]))
            (SvGolf.Cycle.ff_of_ffNba (by
              simp (config := { decide := true }) [$(ident `D):ident, $(ident `procs):ident,
                SvGolf.Cycle.ffNba, Stmt2.nbaOnly, Stmt2.optNbaOnly, Stmt2.listNbaOnly, CaseItem2.listNbaOnly,
                Process2.isEdgePhase, List.all_cons, List.all_append, List.all_map, List.all_flatMap, $leafSimps,*]))
            (fun i p hp _ => $(← exprToSyntax (mkAppN hallGen (ysA.push fv2))) p
              (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hp)))
            (ffDisjB_of_pairwise $hTerm)
            (by simp [$(ident `St):ident])
            (fun j => by
              rw [SvGolf.Cycle.flatMap_ffUpd_all,
                $(← exprToSyntax (mkAppN (Lean.mkConst (X ++ `updates)) (ps ++ ysA ++ #[fv2]))):term,
                $(← exprToSyntax (mkAppN (Lean.mkConst (X ++ `commit)) (ysA.push (edgeQApp ysA)))):term]
              exact $(← settleS zsA) j (by omega))))
        withLocalDeclD `F (Lean.mkConst ``Nat) fun Fv => do
        withLocalDeclD `hF (← mkAppM ``LE.le #[mkNatLit (K + 2), Fv]) fun hFv => do
          let cycTyF ← exOk (← mkAppM ``cycleStep2 #[mkAppN (Lean.mkConst semC) ps, σ, Fv, e, st vs, kv])
            (nextApp applied)
          let cycAux ← mkLambdaFVars #[fv] cycPf
          let cycPfF ← proveBy "sv_cycle: the clock step at every fuel" cycTyF (← `(Lean.Parser.Tactic.tacticSeq|
            obtain ⟨f, hf⟩ : ∃ f, $(← exprToSyntax Fv) = f + 2 + $(quote K) :=
              ⟨$(← exprToSyntax Fv) - 2 - $(quote K), by omega⟩
            rw [hf]
            exact $(← exprToSyntax cycAux) f))
          addThm (X ++ `cycle) (ps ++ hs ++ #[σ, e] ++ vs ++ #[kv, Fv, hFv]) cycTyF cycPfF
            s!"**One cycle of the loaded design** from `X.St …`, any schedule, any stimulus entry, any fuel from \
              {K + 2}: `X.next` of the applied inputs, the step counter some `k'` (it counts the comb passes, \
              which depend on the values) (`sv_cycle`)."
      else
        mark "6. the next state: the updates of every process, in process order"
        -- 6. the next state: the updates of every process, in process order
        let fuelE ← mkAppM ``HAdd.hAdd #[fv, mkNatLit K]
        let allQ ← mkAppM ``List.flatMap #[← mkAppM ``SvGolf.Cycle.runQ #[fuelE, st vs],
          ← mkAppM ``Array.toList #[← mkAppM ``Design2.processes #[app `D]]]
        let (qN, qPf) ← convNorm allQ (← `(Lean.Parser.Tactic.Conv.convSeq|
          simp only [$(ident `D):ident, List.toList_toArray, $(ident `procs):ident, List.flatMap_append,
            List.flatMap_cons, List.flatMap_nil, List.append_nil, List.flatMap_assoc, List.flatMap_map,
            $runQSimps,*]))
        if qN.containsFVar fv.fvarId! then
          throwError "sv_cycle: internal error: the updates still mention the fuel:{indentExpr qN}"
        addDefn (X ++ `next) (ps ++ vs) (← mkAppM ``commitNba2 #[st vs, qN])
          "One cycle's next state from the pre-edge values (inputs applied): the commit of every process's \
          updates, in process order (`sv_cycle`)."
        let nextApp (ws : Array Lean.Expr) := mkAppN (Lean.mkConst (X ++ `next)) (ps ++ ws)
        addThm (X ++ `updates) (ps ++ vs ++ #[fv]) (← mkEq allQ (← mkAppM ``commitNba2 #[st vs, qN]).appArg!) qPf
          "The updates of every process on `X.St …`, in process order (`sv_cycle`)."
        mark "7. the cycle"
        -- 7. the cycle
        withLocalDeclD `σ (Lean.mkConst ``ScheduleOracle) fun σ => do
        withLocalDeclD `kk (Lean.mkConst ``Nat) fun kv => do
        let stA := st applied
        -- every process runs on the applied state and leaves it alone
        let hallTy ← withLocalDeclD `p (Lean.mkConst ``Process2) fun p => do
          let mem ← mkAppM ``Membership.mem #[← mkAppM ``Array.toList #[← mkAppM ``Design2.processes #[app `D]], p]
          let nilQ ← mkAppOptM ``List.nil #[some (← mkAppM ``Prod #[Lean.mkConst ``String,
            ← mkAppM ``Prod #[Lean.mkConst ``Nat, lvT]])]
          let ex ← withLocalDeclD `q (← mkAppM ``List #[← mkAppM ``Prod #[Lean.mkConst ``String,
              ← mkAppM ``Prod #[Lean.mkConst ``Nat, lvT]]]) fun q => do
            let eq ← mkEq (← mkAppM ``runEdgeProcess2 #[fuelE, stA, nilQ, p]) (← mkAppM ``Res.ok #[← mkAppM ``Prod.mk #[stA, q]])
            mkAppM ``Exists #[← mkLambdaFVars #[q] eq]
          mkForallFVars #[p] (← mkArrow mem ex)
        let hallPf ← proveBy "sv_cycle: every process runs" hallTy (← `(Lean.Parser.Tactic.tacticSeq|
          simp only [$(ident `D):ident, List.toList_toArray, $(ident `procs):ident, List.forall_mem_cons,
            List.forall_mem_flatMap, List.forall_mem_map, List.forall_mem_append]
          simp [$runSimps,*]))
        let hndTy ← mkAppM ``List.Nodup #[← mkAppM ``List.map #[← mkAppOptM ``Prod.fst #[some (Lean.mkConst ``String), some lvT], stA]]
        let hndPf ← proveBy "sv_cycle: the state's names are distinct" hndTy (← `(Lean.Parser.Tactic.tacticSeq|
          simp [$(ident `St):ident]))
        let cycTy ← mkEq (← mkAppM ``cycleStep2 #[mkAppN (Lean.mkConst semC) ps, σ, fuelE, e, st vs, kv])
          (← mkAppM ``Res.ok #[← mkAppM ``Prod.mk #[nextApp applied, ← mkAppM ``HAdd.hAdd #[kv, mkNatLit 3]]])
        let hapS ← exprToSyntax (mkAppN (Lean.mkConst (X ++ `apply)) (ps ++ #[e] ++ vs))
        let cycPf ← proveBy "sv_cycle: the clock step" cycTy (← `(Lean.Parser.Tactic.tacticSeq|
          rw [$(← exprToSyntax (thm `sem_eq)):term, SvGolf.Cycle.cycleStep2_eq_commit
            $(← exprToSyntax (thm `profile)) _ (by omega) _ _ _ (by rw [$hapS:term]; exact $(← exprToSyntax hallPf))
            (by rw [$hapS:term]; exact $(← exprToSyntax hndPf)), $hapS:term,
            $(← exprToSyntax (mkAppN (Lean.mkConst (X ++ `updates)) (ps ++ applied ++ #[fv]))):term]
          rfl))
        withLocalDeclD `F (Lean.mkConst ``Nat) fun Fv => do
        withLocalDeclD `hF (← mkAppM ``LE.le #[mkNatLit K, Fv]) fun hFv => do
        let cycTyF ← mkEq (← mkAppM ``cycleStep2 #[mkAppN (Lean.mkConst semC) ps, σ, Fv, e, st vs, kv])
          (← mkAppM ``Res.ok #[← mkAppM ``Prod.mk #[nextApp applied, ← mkAppM ``HAdd.hAdd #[kv, mkNatLit 3]]])
        let cycAux ← mkLambdaFVars #[fv] cycPf
        let cycPfF ← proveBy "sv_cycle: the clock step at every fuel" cycTyF (← `(Lean.Parser.Tactic.tacticSeq|
          obtain ⟨f, hf⟩ : ∃ f, $(← exprToSyntax Fv) = f + $(quote K) :=
            ⟨$(← exprToSyntax Fv) - $(quote K), by omega⟩
          rw [hf]
          exact $(← exprToSyntax cycAux) f))
        addThm (X ++ `cycle) (ps ++ hs ++ #[σ, e] ++ vs ++ #[kv, Fv, hFv]) cycTyF cycPfF
          s!"**One cycle of the loaded design** from `X.St …`, any schedule, any stimulus entry, any fuel from \
            {K}: `X.next` of the applied inputs (`sv_cycle`)."
      mark "8. power-up and the initial state"
      -- 8. power-up and the initial state
      withLocalDeclD `st (← mkAppM ``List #[← mkAppM ``Prod #[Lean.mkConst ``String, lvT]]) fun stv => do
      let puH ← mkAppM ``SvGolf.PowerUp #[mkAppN (Lean.mkConst semC) ps, stv]
      withLocalDeclD `h puH fun hv => do
      -- `∃ x₁ … xₙ, st = X.St x₁ … xₙ ∧ x₁.width = w₁ ∧ … ∧ xₙ.width = wₙ`
      let puTy ← withLocalDeclsDND (sigNames.map (·, lvT)) fun ws => do
        let mut conj : Array Lean.Expr := #[← mkEq stv (st ws)]
        for ((_, w, _), x) in decls.zip ws do
          conj := conj.push (← mkEq (← mkAppM ``LVec.width #[x]) w)
        let mut ex := conj.back!
        for c in conj.pop.reverse do
          ex ← mkAppM ``And #[c, ex]
        for x in ws.reverse do
          ex ← mkAppM ``Exists #[← mkLambdaFVars #[x] ex]
        return ex
      let xIds : Array Ident := (Array.range decls.size).map fun k => mkIdent (Name.mkSimple s!"x{k}")
      let wIds : Array Term := (Array.range decls.size).map fun k => ⟨mkIdent (Name.mkSimple s!"w_x{k}")⟩
      let xTerms : Array Term := xIds.map fun i => ⟨i⟩
      let rflT : Term := ⟨mkCIdent ``rfl⟩
      let hId := mkIdent `h
      let allArgs : Array Term := xTerms ++ #[rflT] ++ wIds
      let puPf ← proveBy "sv_cycle: the power-up states" puTy (← `(Lean.Parser.Tactic.tacticSeq|
        rw [$(← exprToSyntax (thm `sem_eq)):term] at $hId:ident
        powerUp_cases $hId:ident with $xIds*
        exact ⟨$allArgs,*⟩))
      addThm (X ++ `powerUp) (all ++ #[stv, hv]) puTy puPf
        "Every power-up state of the loaded design is `X.St x₁ … xₙ`, each value of its declared width (`sv_cycle`)."
      -- the initial state
      let (initN, initPf) ← convNorm (← mkAppM ``initState2 #[app `D]) (← `(Lean.Parser.Tactic.Conv.convSeq|
        simp [initState2, $(ident `D):ident, $(ident `decls):ident]))
      let some ents := listLitSyn? initN
        | throwError "sv_cycle: internal error: the initial state is not a list literal:{indentExpr initN}"
      let initVals ← ents.mapM fun en => do
        let en ← whnfR en
        unless en.isAppOfArity ``Prod.mk 4 do throwError "sv_cycle: internal error: an initial binding: {en}"
        return en.appArg!
      let initTy ← mkEq (← mkAppM ``initState2 #[mkAppN (Lean.mkConst semC) ps]) (st initVals)
      let initPf' ← proveBy "sv_cycle: the initial state" initTy (← `(Lean.Parser.Tactic.tacticSeq|
        rw [$(← exprToSyntax (thm `sem_eq)):term]
        exact $(← exprToSyntax initPf)))
      addThm (X ++ `init) all initTy initPf' "The initial state of the loaded design (`sv_cycle`)."
      mark "done"
      if mixed then
        logInfo m!"sv_cycle: proved {X}.sem_eq, .apply, .settle (fuel from {K + 2}), .cycle (fuel from {K + 2}), \
          .powerUp, .init; defined {X}.St, .comb (the comb process's values), .edgeQ, .next and the updates of \
          {results.size} process(es)"
      else
        logInfo m!"sv_cycle: proved {X}.sem_eq, .profile, .apply, .cycle (fuel from {K}), .powerUp, .init; defined \
          {X}.St, .next and the updates of {results.size} process(es)"

/-! ## 5. The simp sets, prepared once

`simp [f]` builds the equation lemmas of a definition `f` the first time a file uses them (`f.eq_1`, …), and the
instantiation and run sets name a hundred definitions of the semantics: about 1.6 s of every proof that uses them
(measured: the first instantiation `simp` of a file 1.7 s, the same `simp` again 0.13 s). Using each set once here,
in the library, builds them once: they are stored with this module, and a proof that imports it finds them. -/

set_option linter.unusedSimpArgs false in
/-- The instantiation and run `simp` sets of `sv_mirror`/`sv_cycle`, used once (see above). -/
theorem simpSets_ready (P : Prop) (h : P) : P := by
  simp (config := { decide := true }) only [instProcess2, instLhs2, instLhsLeaf2, fitExpr2,
    instExpr2, rigidExpr, selfWidth2, selfWidthSum2, elemOf, instParts2, evalInt, IEnv.bindVal,
    PExpr.isInt, SymBinOp.intArith, SymBinOp.constClass, ctype, ctypeList, evalAt, evalAtList,
    PExpr.readsSignal, PExpr.readsSignalList, PExpr.readsSignalConst, PExpr.readsSignalConstList,
    PExpr.signalRoot?, PExpr.pushedTarget, PExpr.ctxPropagates, PExpr.isSquash2, PExpr.negGenvarAt,
    PExpr.mentionsAny, PExpr.mentionsAnyList, paramSelectOk, arraySelWidth, arrayElemRead, arrayPartRead,
    arrayElemTarget, arrayPartTarget, arrayElemWindow, arrayPartGeom, arrayDims, evalDims, dynPartPlan,
    dynBaseRead, arrayFlatWidth, partOffsetsWild, concatLeafExact, walkIndices, partLabels, labelOffset,
    dimCount, dimsStride, List.lookup, instStmt2, instStmts2, dimTable, dimTableStep, PType.width_packed_cons,
    PDim.width, ctxOpWidth2, rigidMax2, PExpr.constLeaf, PExpr.negGenvarWidened, LVec.width,
    divOperandWidth2, instDivOperand2, fitDivOperand2, IEnv.withDecls, PDesign.paramEnv2, bindPackageParams,
    bindPackageEnums, bindParamsRes, bindParams, bindLocals, bindLocal, evalIntTarget, bindEnums,
    Except.mapError, List.filterMapM, List.filterMapM.loop, buildDecls, instDecl, buildElems,
    runEdgeProcess2, execStmt2, execStmts2, evalExpr2, evalExprs2, resolveLhs2, readSignal, SvState.lookup,
    evalBinOp, evalUnaryOp, Stmt2.nbaOnly, Stmt2.optNbaOnly, Stmt2.listNbaOnly, CaseItem2.listNbaOnly,
    Stmt2.nbaStaticB, Stmt2.optNbaStaticB, Stmt2.listNbaStaticB, CaseItem2.listNbaStaticB, Lhs2.window?,
    Design2.declWidth, Design2.inputNames, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins,
    Lhs2.drvWinsList, CaseItem2.drvWinsList, CaseItem2.drvWins, Process2.procWrites, Process2.procWins,
    initState2, PDesign.inputNames, runCombProcess2, SvState.set, combGuardProc, Stmt2.combAdmits,
    Stmt2.combViol, Stmt2.listCombViol, Stmt2.mayW, Stmt2.listMayW, Stmt2.mustW, Lhs2.mayW, Lhs2.mustW,
    Lhs2.rdW, Expr2.rdW, CombGuard.readsViol, CombGuard.whole, CombGuard.BWin.inter, CombGuard.BWin.sub,
    CombGuard.BWin.subAll, driverWins, PDesign.declNames, h]

#print axioms applyInputs2_eq_map
#print axioms cycleStep2_eq_commit
#print axioms SvGolf.ProcDisj.of_all

end SvGolf.Cycle
