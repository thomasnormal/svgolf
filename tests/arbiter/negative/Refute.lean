import tasks.arbiter.Spec
import SvGolf.LoadSv
import LeanModels.Sv.Known2

/-!
# Task `arbiter`: non-vacuity and tightness checks (untrusted, kernel-checked; 2026-11-04, moved here 2026-11-05; txtask-v2's rules 2026-11-06)

Nothing here is part of the trusted base. The wrong designs are hand-built `Design2` families at
`N = 2`, so that the checks need no extraction; their SystemVerilog counterparts are the attacks of
`tests/arbiter/attacks/` and the negatives of this directory, which `tests/run.py` takes through
`check.py` (`tests/expected.json`). Since 2026-11-06 the statement's runs start from EVERY power-up
state (txtask-v2's rule 2), so each refutation names one power-up state (`zeros`: every bit 0, or
`onesAt`: the named signals all ones) and one known stimulus, both decided (`PowerUp`, `KnownStim`).

* **Wrong designs REJECTED by the statement** (each refuted at `N = 2`, `K = 1`, by ONE run of the
  design from one power-up state that the kernel evaluates, `decide +kernel`):
  - `never_refuted`: never grant (breaks G3, work conservation);
  - `everyone_refuted`: grant every requester (breaks G1, mutual exclusion);
  - `zero_refuted`: always grant client 0 (breaks G2, no spurious grant);
  - `fixed_refuted`: fixed priority, the lowest requester wins (breaks G4, client 1 starves);
  - `mealy_refuted`: a correct registered grant hidden behind a Mealy output (breaks `MooreOut`);
    `mealy_silicon` shows, on a concrete run, why it must be rejected: every snapshot shows one
    grant, while the value a synchronous consumer sees before the next edge grants both clients;
  - `xopt_refuted` (review, 11/04): a correct round-robin behind `if (~u)` on a never-reset register
    `u` that holds itself; from the power-up `u = 0` it is fixed priority (G4). Under txtask-v1 it
    was refuted by the known-state clause (`u` was `x` from ls-sv's start); that clause is gone, and
    rule 2 refutes it directly. `a16_refuted`: the same for the attack `a16_xopt.sv` itself, whose
    twin `a16D` is checked equal to the loaded design (`#guard`, below);
  - **`ring_refuted`** (the universal-correctness audit, 2026-11-06; `bit_ring.sv`): the reference
    round-robin plus a never-reset 2-state ring `u`, fixed priority when `&u`; ls-sv's start gives
    a 2-state variable 0, so `u` stayed 0 and txtask-v1 accepted it; from the power-up `u` all ones
    it is fixed priority for ever (G4);
  - **`reset_edge_refuted`** (the same audit; `reset_edge.sv`): a flag `bad` set at the first reset
    edge from the PRE-reset `&u`; ls-sv's start read `u` as `x` there and took the else branch;
    from the power-up `u` all ones the first segment is fixed priority (G4).
  The twins `ringD`, `edgeD`, `a16D` are checked equal to the designs `load_sv` loads from the
  `.sv` files, at `N = 2` and `N = 8` (`#guard reprStr …`: the compiled evaluator compares the two
  printed designs; the kernel does not reduce the generate expansion).
* **`MooreOut` on right designs** (review, 11/04): `rr2_moore` (FF-only: `S` = the inputs) and
  `merged_not_moore`, the recorded over-strong case (one `always_comb` that both computes the next
  grant from `req` and copies a flop to `gnt`).
* **The bound is tight** (`bound_tight`): for every `N ≥ 2`, NO design satisfies the statement with
  the response bound `N - 2`. So `K = N - 1` is the least bound, and the task fixes it. Its run is
  from the all-zero power-up state on a stimulus that is known for every design meeting `Interface`
  (`knownEntry_of_interface`: the distinct names make each port's first declaration the port).
* **The window argument of the proof route** moved to the svGolf proof library on 2026-11-05
  (`SvGolf.ReactTask.responds_of_rank`, `SvGolf/React.lean`), where the reduction
  `ReactTask.satisfiedAt_of_rank` and the proved reference `tasks/arbiter/reference/rr_mask.lean` use it.
* **A round-robin arbiter passes** the executable reading of the guarantee on concrete runs where
  the wrong designs fail (`#guard`, labelled: an executable reading, not a proof of the statement),
  and the designs with an unreset register pass from one power-up and fail from another.
-/

namespace SvGolf.Tasks.Arbiter.Refute

open LeanModels.Sv SvGolf

/-! ## Hand-built design families (ports `clk, rst, req[N]` in, `gnt[N]` out) -/

/-- The task's ports at `N`, in order. -/
def declsN (N : Nat) : Array Decl :=
  #[{ name := "clk", width := 1, isInput := true }, { name := "rst", width := 1, isInput := true },
    { name := "req", width := N, isInput := true }, { name := "gnt", width := N, isOutput := true }]

/-- The `N`-bit constant `k`. -/
def litN (N k : Nat) : Expr2 := .lit (LVec.ofNat N k)

/-- `gnt <= e`. -/
def gntGets (e : Expr2) : Stmt2 := .nbaAssign (.ident "gnt") e

/-- A registered grant: `always_ff @(posedge clk) if (rst) gnt <= '0; else gnt <= e;`. -/
def regGrant (N : Nat) (e : Expr2) : Process2 :=
  .alwaysFF "clk" (.ifStmt (.ident "rst") (gntGets (litN N 0)) (some (gntGets e)))

/-- A design with the task's ports, extra declarations and processes. -/
def arbD (name : String) (N : Nat) (extra : Array Decl) (ps : Array Process2) : Design2 :=
  { name, decls := declsN N ++ extra, processes := ps }

/-- WRONG: never grant. -/
def neverF (N : Nat) : Design2 := arbD "never" N #[] #[regGrant N (litN N 0)]

/-- WRONG: grant every requester (`gnt <= req`). -/
def everyoneF (N : Nat) : Design2 := arbD "everyone" N #[] #[regGrant N (.ident "req")]

/-- WRONG: always grant client 0 (`gnt <= 1`). -/
def zeroF (N : Nat) : Design2 := arbD "zero" N #[] #[regGrant N (litN N 1)]

/-- WRONG: fixed priority, the lowest requester wins (`gnt <= req & -req`). -/
def fixedF (N : Nat) : Design2 :=
  arbD "fixed" N #[] #[regGrant N (.binary .and (.ident "req") (.unary .neg (.ident "req")))]

/-- WRONG (in silicon): a registered fixed-priority grant `g`, and the Mealy output
`assign gnt = (req == last) ? g : req` with `last <= req`. In every ls-sv snapshot `req == last`. -/
def mealyF (N : Nat) : Design2 :=
  arbD "mealy" N #[{ name := "last", width := N }, { name := "g", width := N }]
    #[.alwaysFF "clk" (.block #[.nbaAssign (.ident "last") (.ident "req"),
        .ifStmt (.ident "rst") (.nbaAssign (.ident "g") (litN N 0))
          (some (.nbaAssign (.ident "g") (.binary .and (.ident "req") (.unary .neg (.ident "req")))))]),
      .assign (.ident "gnt")
        (.ternary (.binary .eq (.ident "req") (.ident "last")) (.ident "g") (.ident "req"))]

/-- RIGHT (at `N = 2`): round-robin with a one-bit pointer `ptr` (the client with priority);
after a grant to client `i` the priority passes to the other client. Registered, FF-only. -/
def rr2 : Design2 :=
  let req (i : Expr2) : Expr2 := .index (.ident "req") i 1
  let p : Expr2 := .ident "ptr"
  let np : Expr2 := .unary .bnot (.ident "ptr")
  let onehot (i : Expr2) : Expr2 := .ternary i (litN 2 2) (litN 2 1)
  arbD "rr2" 2 #[{ name := "ptr", width := 1 }]
    #[.alwaysFF "clk"
      (.ifStmt (.ident "rst")
        (.block #[gntGets (litN 2 0), .nbaAssign (.ident "ptr") (litN 1 0)])
        (some (.ifStmt (req p)
          (.block #[gntGets (onehot p), .nbaAssign (.ident "ptr") np])
          (some (.ifStmt (req np)
            (.block #[gntGets (onehot np)])
            (some (gntGets (litN 2 0))))))))]

/-! ## Stimuli and runs from a power-up state -/

/-- One stimulus entry: `rst` and `req` (the clock is not driven: it is not observed). -/
def entry (N r v : Nat) : SvState := [("rst", LVec.ofNat 1 r), ("req", LVec.ofNat N v)]

/-- The power-up state of `d` with every bit 0. -/
def zeros (d : Design2) : SvState := d.decls.toList.map fun dc => (dc.name, LVec.ofNat dc.width 0)

/-- The power-up state of `d` with the signals `ns` all ones and every other bit 0. -/
def onesAt (d : Design2) (ns : List String) : SvState :=
  d.decls.toList.map fun dc => (dc.name, LVec.ofNat dc.width (if dc.name ∈ ns then 2 ^ dc.width - 1 else 0))

/-- The trace of `d` from the power-up state `st0` on `stim` under the source schedule (`[]` if the
run does not complete). -/
def trAt (d : Design2) (st0 : SvState) (stim : List SvState) : List SvState :=
  ((run2At d σ_src 64 st0 stim).toOption).getD []

/-- The trace of `d` from the all-zero power-up state. -/
def trOf (d : Design2) (stim : List SvState) : List SvState := trAt d (zeros d) stim

/-- The value of signal `n` in snapshot `c`. -/
def sigAt (tr : List SvState) (c : Nat) (n : String) : Option LVec :=
  (tr[c]?).bind fun st => SvState.lookup st n

/-- The all-zero state is a power-up state of every design. -/
theorem powerUp_zeros (d : Design2) : PowerUp d (zeros d) := by
  unfold PowerUp zeros
  generalize d.decls.toList = ds
  refine ⟨by simp, ?_⟩
  induction ds with
  | nil => simp
  | cons dc ds ih =>
    intro b hb
    simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at hb
    rcases hb with rfl | hb
    · exact ⟨LVec.width_ofNat _ _, LVec.allKnown_ofNat _ _⟩
    · exact ih b hb

/-! ## Plumbing: the statement's hypotheses on concrete stimuli, its conclusion on concrete traces -/

theorem released_of {stim : List SvState} {c1 h : Nat} (h0 : 0 < c1)
    (hr : (stim[c1 - 1]?).bind (fun e => SvState.lookup e "rst") = some (LVec.ofNat 1 1))
    (hoff : ∀ c, c < h → c1 ≤ c →
      (stim[c]?).bind (fun e => SvState.lookup e "rst") = some (LVec.ofNat 1 0)) :
    Released "rst" stim c1 h := by
  refine ⟨h0, ?_, fun c h1 h2 => ?_⟩
  · cases he : stim[c1 - 1]? with
    | none => rw [he] at hr; simp at hr
    | some e => rw [he] at hr; exact ⟨e, he, hr⟩
  · have hc := hoff c h2 h1
    cases he : stim[c]? with
    | none => rw [he] at hc; simp at hc
    | some e => rw [he] at hc; exact ⟨e, he, hc⟩

theorem insAt_of {N : Nat} {stim : List SvState} {c : Nat} {xs : List (BitVec N × Unit)}
    (h : ∀ j, j < xs.length → (stim[c + j]?).bind (fun e => SvState.lookup e "req") =
      (xs[j]?).map (fun x => LVec.ofBitVec x.1)) :
    task.InsAt N stim c xs := by
  intro j x hx
  have hx2 : xs[j]? = some (x : BitVec N × Unit) := hx
  have hj : j < xs.length := (List.getElem?_eq_some_iff.mp hx2).1
  have hc := h j hj
  rw [hx2] at hc
  cases he : stim[c + j]? with
  | none => rw [he] at hc; cases hc
  | some e => rw [he] at hc; exact ⟨e, rfl, And.intro hc trivial⟩

/-- The known outputs a segment's snapshots show are the trace's grant vectors. (Stated at the
plain pair type: `task.Out N` is the same type only up to unfolding `task`, which `simp` and `rw`
do not do.) -/
theorem showsAt_eq {N : Nat} {tr : List SvState} {c : Nat} {ys : List (BitVec N × Unit)}
    {vs : List (BitVec N)} (hl : ys.length = vs.length) (hs : task.ShowsAt N tr c ys)
    (hk : ∀ j, j < vs.length → sigAt tr (c + j) "gnt" = (vs[j]?).map LVec.ofBitVec) :
    ys = vs.map fun v => (v, ()) := by
  apply List.ext_getElem (by simp [hl])
  intro j h1 h2
  have hj : j < vs.length := hl ▸ h1
  obtain ⟨st, hst, hh⟩ := hs j ys[j] (List.getElem?_eq_getElem h1)
  have hk' := hk j hj
  rw [sigAt, hst, List.getElem?_eq_getElem hj] at hk'
  have key : ∀ y : BitVec N × Unit, HoldAll st (task.outputs N) y → y = (vs[j], ()) := by
    intro y hy
    obtain ⟨a, u⟩ := y
    cases u
    have hh' : SvState.lookup st "gnt" = some (LVec.ofBitVec a) ∧ True := hy
    have h3 : SvState.lookup st "gnt" = some (LVec.ofBitVec vs[j]) := hk'
    rw [hh'.1] at h3
    rw [LVec.ofBitVec_inj.mp (Option.some.inj h3)]
  rw [List.getElem_map]
  exact key _ hh

/-- The statement at one point refuted by its conclusion's failure on one completed run from a
power-up state on a known stimulus. -/
theorem not_follows_of_run {N K : Nat} {d : Design2} {st0 : SvState} {stim tr : List SvState}
    {c1 : Nat} {x0 : task.In N} {xs : List (task.In N)} (hpu : PowerUp d st0)
    (hks : KnownStim d stim) (hrun : run2At d σ_src 64 st0 stim = .ok tr)
    (hrel : Released "rst" stim c1 (c1 + xs.length)) (hins : task.InsAt N stim (c1 - 1) (x0 :: xs))
    (hbad : ∀ y0 ys, ys.length = xs.length → task.ShowsAt N tr (c1 - 1) (y0 :: ys) →
      ¬ task.Guar N K xs y0 ys) :
    ¬ task.Follows N K d := fun hf => by
  obtain ⟨y0, ys, hl, hs, hg⟩ := hf st0 hpu σ_src stim tr hks ⟨64, hrun⟩ c1 x0 xs hrel hins
  exact hbad y0 ys hl hs hg

/-! ## The refutations -/

/-- A reset, then client 0 alone requests. -/
def stimLone : List SvState := [entry 2 1 0, entry 2 0 1]
/-- A reset, then both clients request. -/
def stimBoth : List SvState := [entry 2 1 0, entry 2 0 3]
/-- A reset, then nobody requests. -/
def stimNone : List SvState := [entry 2 1 0, entry 2 0 0]
/-- A reset, then both clients request twice. -/
def stimBoth2 : List SvState := [entry 2 1 0, entry 2 0 3, entry 2 0 3]

theorem n2_inRange : task.inRange 2 := by simp [task]

/-- **Never grant** is rejected (G3: client 0 requests alone, nobody is granted). -/
theorem never_refuted : ¬ Statement neverF := fun hs =>
  not_follows_of_run (N := 2) (K := 1) (d := neverF 2) (st0 := zeros (neverF 2)) (stim := stimLone)
    (tr := trOf (neverF 2) stimLone) (c1 := 1) (x0 := (0#2, ())) (xs := [(1#2, ())])
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

/-- **Grant everyone** is rejected (G1: both request, both are granted). -/
theorem everyone_refuted : ¬ Statement everyoneF := fun hs =>
  not_follows_of_run (N := 2) (K := 1) (d := everyoneF 2) (st0 := zeros (everyoneF 2)) (stim := stimBoth)
    (tr := trOf (everyoneF 2) stimBoth) (c1 := 1) (x0 := (0#2, ())) (xs := [(3#2, ())])
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

/-- **Always grant client 0** is rejected (G2: nobody requests, client 0 is granted). -/
theorem zero_refuted : ¬ Statement zeroF := fun hs =>
  not_follows_of_run (N := 2) (K := 1) (d := zeroF 2) (st0 := zeros (zeroF 2)) (stim := stimNone)
    (tr := trOf (zeroF 2) stimNone) (c1 := 1) (x0 := (0#2, ())) (xs := [(0#2, ())])
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

/-- **The starvation refutation** at `N = 2`: one run from the power-up state `st0` on `stimBoth2`
(a reset, then both clients request twice) whose snapshots show the grants `00, 01, 01`. Client 1
requests at two consecutive entries and is granted in neither, so G4 with `K = 1` fails. Mutual
exclusion, no spurious grant and work conservation all hold on such a run. -/
theorem starves_refuted {sem : Nat → Design2} (st0 : SvState) (hpu : PowerUp (sem 2) st0)
    (hks : KnownStim (sem 2) stimBoth2)
    (hrun : run2At (sem 2) σ_src 64 st0 stimBoth2 = .ok (trAt (sem 2) st0 stimBoth2))
    (hg : ∀ j, j < [0#2, 1#2, 1#2].length → sigAt (trAt (sem 2) st0 stimBoth2) (1 - 1 + j) "gnt" =
      ([0#2, 1#2, 1#2][j]?).map LVec.ofBitVec) :
    ¬ Statement sem := fun hs =>
  not_follows_of_run (N := 2) (K := 1) (d := sem 2) (st0 := st0) (stim := stimBoth2)
    (tr := trAt (sem 2) st0 stimBoth2) (c1 := 1) (x0 := (0#2, ())) (xs := [(3#2, ()), (3#2, ())])
    hpu hks hrun (released_of (by decide) (by decide +kernel) (by decide +kernel))
    (insAt_of (by decide +kernel))
    (fun y0 ys hl hs hg' => by
      have hl' : ys.length = 2 := hl
      have hv := showsAt_eq (vs := [0#2, 1#2, 1#2]) (by show ys.length + 1 = 3; omega) hs hg
      obtain ⟨h0, h1⟩ := List.cons.inj hv
      subst h0 h1
      obtain ⟨i, y, hi, hy, hg1⟩ := hg'.2.2 (⟨1, by decide⟩ : Fin 2) 0 (by decide) (fun i x hi hx => by
        have : i = 0 ∨ i = 1 := by omega
        rcases this with rfl | rfl <;> (have hx' := Option.some.inj hx; subst hx'; exact rfl))
      have : i = 0 ∨ i = 1 := by omega
      rcases this with rfl | rfl <;>
        (have hy' := Option.some.inj hy; subst hy'; exact Bool.false_ne_true hg1))
    (hs 2 n2_inRange).2.2.1

/-- **Fixed priority** is rejected (G4 with `K = 1`: both request twice, client 1 is never
granted), from the all-zero power-up state. -/
theorem fixed_refuted : ¬ Statement fixedF :=
  starves_refuted (sem := fixedF) (zeros (fixedF 2)) (powerUp_zeros _) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

/-- **A Mealy output is rejected** by `MooreOut`: every set containing the inputs and closed
under the comb processes contains `gnt`, because `assign gnt = …` mentions `req`. -/
theorem mealy_not_moore : ¬ MooreOut (mealyF 2) := by
  rintro ⟨S, hin, hcl, hout⟩
  have hreq : S "req" := hin "req" (by decide +kernel)
  have hg := hcl _ (List.mem_cons_of_mem _ (List.mem_singleton.2 rfl)) rfl
    ⟨"req", by decide +kernel, hreq⟩ "gnt" (by decide +kernel)
  exact hout "gnt" (by decide +kernel) hg

theorem mealy_refuted : ¬ Statement mealyF := fun hs =>
  mealy_not_moore (hs 2 n2_inRange).2.1.1.2

/-- **Why**: the run `reset; req = 01; req = 11` of `mealyF 2`. The snapshots show one grant each
(`gnt = 01`, the hidden fixed-priority `g`), as every snapshot claim of the statement would see.
But in silicon the grant shown after the edge of cycle 1 stays on the wire while the requesters
drive cycle 2's `req = 11`, and the value of `gnt` there, the PRE-EDGE sample of cycle 2 (entry 2
applied to snapshot 1, then the combinational settle), grants BOTH clients. -/
def stimM : List SvState := [entry 2 1 0, entry 2 0 1, entry 2 0 3]

/-- The pre-edge sample of cycle `c + 1`: entry `c + 1` applied to snapshot `c`, then the settle. -/
def preSample (d : Design2) (stim tr : List SvState) (c : Nat) : Option SvState :=
  match tr[c]?, stim[c + 1]? with
  | some st, some e => ((combSettle2 d σ_src 64 (applyInputs2 d e st) 0).toOption).map Prod.fst
  | _, _ => none

theorem mealy_silicon :
    sigAt (trOf (mealyF 2) stimM) 1 "gnt" = some (LVec.ofNat 2 1) ∧
    sigAt (trOf (mealyF 2) stimM) 2 "gnt" = some (LVec.ofNat 2 1) ∧
    ((preSample (mealyF 2) stimM (trOf (mealyF 2) stimM) 1).bind fun st =>
      SvState.lookup st "gnt") = some (LVec.ofNat 2 3) := by
  decide +kernel

/-! ## x-optimism on a never-reset register (review, 2026-11-04; attack A16b) -/

/-- WRONG in silicon and in the scored netlist, RIGHT in every ls-sv snapshot (attack A16b at
`N = 2`): `rr2` plus a register `u` that is never reset and holds itself, and `if (~u) gnt <=
fixed priority; else <rr2's decision>`. In ls-sv `u` is `x` for ever, `~x = x`, and `if` on `x`
takes the else branch, so every snapshot is `rr2`'s; Yosys reads `u` as a don't-care 0 and keeps
the fixed-priority branch (MEASURED on the SystemVerilog `a16b_xopt.sv`, README "Review"). -/
def xopt2 : Design2 :=
  let req (i : Expr2) : Expr2 := .index (.ident "req") i 1
  let p : Expr2 := .ident "ptr"
  let np : Expr2 := .unary .bnot (.ident "ptr")
  let onehot (i : Expr2) : Expr2 := .ternary i (litN 2 2) (litN 2 1)
  arbD "xopt2" 2 #[{ name := "ptr", width := 1 }, { name := "u", width := 1 }]
    #[.alwaysFF "clk" (.nbaAssign (.ident "u") (.ident "u")),
      .alwaysFF "clk"
      (.ifStmt (.ident "rst")
        (.block #[gntGets (litN 2 0), .nbaAssign (.ident "ptr") (litN 1 0)])
        (some (.ifStmt (.unary .bnot (.ident "u"))
          (gntGets (.binary .and (.ident "req") (.unary .neg (.ident "req"))))
          (some (.ifStmt (req p)
            (.block #[gntGets (onehot p), .nbaAssign (.ident "ptr") np])
            (some (.ifStmt (req np)
              (.block #[gntGets (onehot np)])
              (some (gntGets (litN 2 0))))))))))]

/-- The family (the point `N = 2` is all the refutation needs). -/
def xoptF (_ : Nat) : Design2 := xopt2

/-- **x-optimism is rejected** by rule 2 (every power-up): from the power-up state `u = 0`, `~u`
is 1 and the design is fixed priority (G4). (From `u = 1` it is `rr2`: the `#guard`s below.) -/
theorem xopt_refuted : ¬ Statement xoptF :=
  starves_refuted (sem := xoptF) (zeros xopt2) (powerUp_zeros _) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

/-! ## Unreset registers and the first reset edge (the universal-correctness audit, 2026-11-06)

Three designs that txtask-v1 accepted because ls-sv's start state is `x` (`0` for a 2-state
variable) and not a power-up value, written as the SystemVerilog files `load_sv` loads below, and
as hand-built families checked equal to them. Each is the reference mask round-robin (its comb
block, plus `fix`, the lowest requester) with one unreset register. -/

/-- `'0`, `'1` at width `w`, and the one-bit `1'b1`, `1'b0`. -/
abbrev zw (w : Nat) : LVec := LVec.replicate w .l0
abbrev ow (w : Nat) : LVec := LVec.replicate w .l1
abbrev b1 : LVec := ⟨#[.l1]⟩
abbrev b0 : LVec := ⟨#[.l0]⟩

/-- `e & (~e + 1'b1)` at width `N`: the lowest set bit of `e`. -/
def lowbit (N : Nat) (e : Expr2) : Expr2 :=
  .binary .and e (.binary .add (.unary .bnot e) (.resize N (.lit b1)))

/-- The comb block: `mreq = req & mask; pick = (mreq != '0) ? lowbit(mreq) : lowbit(req);
fix = lowbit(req)`. -/
def combFix (N : Nat) : Process2 :=
  .alwaysComb (.block #[
    .blockingAssign (.ident "mreq") (.binary .and (.ident "req") (.ident "mask")),
    .blockingAssign (.ident "pick") (.ternary (.binary .ne (.ident "mreq") (.lit (zw N)))
      (lowbit N (.ident "mreq")) (lowbit N (.ident "req"))),
    .blockingAssign (.ident "fix") (lowbit N (.ident "req"))])

/-- `if (c) gnt <= fix; else gnt <= pick;`, then `if (pick != '0) mask <= ~((pick << 1) - 1'b1);`. -/
def selTail (N : Nat) (c : Expr2) : Array Stmt2 :=
  #[.ifStmt c (.nbaAssign (.ident "gnt") (.ident "fix")) (some (.nbaAssign (.ident "gnt") (.ident "pick"))),
    .ifStmt (.binary .ne (.ident "pick") (.lit (zw N)))
      (.nbaAssign (.ident "mask") (.unary .bnot (.binary .sub
        (.binary (.shl false) (.ident "pick") (.lit (LVec.ofInt 32 1))) (.resize N (.lit b1)))))
      none]

/-- The ports, the extra declarations, then `mask`, `mreq`, `pick`, `fix`. -/
def rrDeclsX (N : Nat) (extra : Array Decl) : Array Decl :=
  declsN N ++ extra ++ #[{ name := "mask", width := N }, { name := "mreq", width := N },
    { name := "pick", width := N }, { name := "fix", width := N }]

/-- The attack `a16_xopt.sv`: `u <= u`, never reset; `if (!u) gnt <= fix; else gnt <= pick;`. -/
def a16D (N : Nat) : Design2 where
  name := "arbiter"
  decls := rrDeclsX N #[{ name := "u", width := 1 }]
  processes := #[.alwaysFF "clk" (.nbaAssign (.ident "u") (.ident "u")), combFix N,
    .alwaysFF "clk" (.block #[.ifStmt (.ident "rst")
      (.block #[.nbaAssign (.ident "gnt") (.lit (zw N)), .nbaAssign (.ident "mask") (.lit (ow N))])
      (some (.block (selTail N (.unary .lnot (.ident "u")))))])]

/-- `negative/bit_ring.sv`: a never-reset 2-state ring `bit [31:0] u`, `u <= {u[30:0], u[31]}`;
`if (&u) gnt <= fix; else gnt <= pick;`. -/
def ringD (N : Nat) : Design2 where
  name := "arbiter"
  decls := rrDeclsX N #[{ name := "u", width := 32, twoState := true }]
  processes := #[.alwaysFF "clk" (.nbaAssign (.ident "u")
      (.squash2 (.concat #[.slice (.ident "u") 0 31, .slice (.ident "u") 31 1]))), combFix N,
    .alwaysFF "clk" (.block #[.ifStmt (.ident "rst")
      (.block #[.nbaAssign (.ident "gnt") (.lit (zw N)), .nbaAssign (.ident "mask") (.lit (ow N))])
      (some (.block (selTail N (.reduce .and (.ident "u")))))])]

/-- `negative/reset_edge.sv`: the reset branch sets `bad` from the PRE-reset `&u` (and resets `u`);
`if (bad) gnt <= fix; else gnt <= pick;`, `u` an LFSR after the reset. -/
def edgeD (N : Nat) : Design2 where
  name := "arbiter"
  decls := rrDeclsX N #[{ name := "u", width := 32 }, { name := "bad", width := 1 }]
  processes := #[combFix N,
    .alwaysFF "clk" (.block #[.ifStmt (.ident "rst")
      (.block #[.nbaAssign (.ident "u") (.lit (zw 32)),
        .ifStmt (.reduce .and (.ident "u")) (.nbaAssign (.ident "bad") (.lit b1))
          (some (.nbaAssign (.ident "bad") (.lit b0))),
        .nbaAssign (.ident "gnt") (.lit (zw N)), .nbaAssign (.ident "mask") (.lit (ow N))])
      (some (.block (#[.nbaAssign (.ident "u") (.concat #[.slice (.ident "u") 0 31,
          .unary .bnot (.binary .xor (.binary .xor (.binary .xor (.slice (.ident "u") 31 1)
            (.slice (.ident "u") 21 1)) (.slice (.ident "u") 1 1)) (.slice (.ident "u") 0 1))])]
        ++ selTail N (.ident "bad"))))])]

load_sv a16L from "tests/arbiter/attacks/a16_xopt.sv"
load_sv ringL from "tests/arbiter/negative/bit_ring.sv"
load_sv edgeL from "tests/arbiter/negative/reset_edge.sv"

-- the hand-built twins are the loaded designs (at the refutations' point and the scoring point)
#guard reprStr (a16L.sem 2) == reprStr (a16D 2)
#guard reprStr (a16L.sem 8) == reprStr (a16D 8)
#guard reprStr (ringL.sem 2) == reprStr (ringD 2)
#guard reprStr (ringL.sem 8) == reprStr (ringD 8)
#guard reprStr (edgeL.sem 2) == reprStr (edgeD 2)
#guard reprStr (edgeL.sem 8) == reprStr (edgeD 8)

/-- **The attack `a16_xopt.sv` is rejected** by rule 2: from the power-up state `u = 0`, `!u` is 1
and the design is fixed priority (G4). -/
theorem a16_refuted : ¬ Statement a16D :=
  starves_refuted (sem := a16D) (zeros (a16D 2)) (powerUp_zeros _) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

/-- **`bit_ring.sv` is rejected** by rule 2: from the power-up state with the 2-state ring `u` all
ones (every rotation of it is all ones), `&u` is 1 at every edge and the design is fixed priority
(G4). ls-sv's own start gives the 2-state `u` the value 0, where the design is the round-robin. -/
theorem ring_refuted : ¬ Statement ringD :=
  starves_refuted (sem := ringD) (onesAt (ringD 2) ["u"]) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

/-- **`reset_edge.sv` is rejected** by rule 2: from the power-up state with `u` all ones, the first
reset edge reads `&u` = 1 and sets `bad`, and the first segment is fixed priority (G4). ls-sv's own
start reads `u` as `x` at that edge and takes the else branch. -/
theorem reset_edge_refuted : ¬ Statement edgeD :=
  starves_refuted (sem := edgeD) (onesAt (edgeD 2) ["u"]) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

/-- Rule 3 does not see these designs (no x-creating construct): the runs are what refutes them. -/
example : XSafe (a16D 2) ∧ XSafe (ringD 2) ∧ XSafe (edgeD 2) := by decide +kernel

/-! ## `MooreOut` on a right design, both ways (review, 2026-11-04) -/

/-- The FF-only `rr2` is Moore: `S` = the input ports. -/
theorem rr2_moore : MooreOut rr2 :=
  ⟨fun n => n ∈ ["clk", "rst", "req"], by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- RIGHT in silicon (`rr2`'s decision, registered), but written with ONE `always_comb` block
that computes the next grant `nxt` from `req` AND drives `gnt = gq`. `gnt` is a flop's copy, yet
`MooreOut` puts every target of a comb process that reads an input into the cone: a recorded
restriction (split the block). -/
def merged2 : Design2 :=
  let req (i : Expr2) : Expr2 := .index (.ident "req") i 1
  let p : Expr2 := .ident "ptr"
  let np : Expr2 := .unary .bnot (.ident "ptr")
  let onehot (i : Expr2) : Expr2 := .ternary i (litN 2 2) (litN 2 1)
  let nxtGets (e : Expr2) : Stmt2 := .blockingAssign (.ident "nxt") e
  arbD "merged2" 2
    #[{ name := "ptr", width := 1 }, { name := "gq", width := 2 }, { name := "nxt", width := 2 }]
    #[.alwaysComb (.block #[
        .ifStmt (req p) (nxtGets (onehot p))
          (some (.ifStmt (req np) (nxtGets (onehot np)) (some (nxtGets (litN 2 0))))),
        .blockingAssign (.ident "gnt") (.ident "gq")]),
      .alwaysFF "clk"
        (.ifStmt (.ident "rst")
          (.block #[.nbaAssign (.ident "gq") (litN 2 0), .nbaAssign (.ident "ptr") (litN 1 0)])
          (some (.block #[.nbaAssign (.ident "gq") (.ident "nxt"),
            .ifStmt (req p) (.nbaAssign (.ident "ptr") np) none])))]

theorem merged_not_moore : ¬ MooreOut merged2 := by
  rintro ⟨S, hin, hcl, hout⟩
  have hreq : S "req" := hin "req" (by decide +kernel)
  have hg := hcl _ (List.mem_cons_self ..) rfl ⟨"req", by decide +kernel, hreq⟩ "gnt"
    (by decide +kernel)
  exact hout "gnt" (by decide +kernel) hg

/-! ## The response bound `N - 1` is tight: no design meets `N - 2` -/

/-- Pigeonhole: an injective map from `{0, …, n-1}` into `{0, …, m-1}` needs `n ≤ m`. -/
theorem pigeon : ∀ (n m : Nat) (f : Nat → Nat), (∀ i, i < n → f i < m) →
    (∀ i j, i < n → j < n → f i = f j → i = j) → n ≤ m
  | 0, m, _, _, _ => Nat.zero_le m
  | n + 1, m, f, hlt, hinj => by
    have hm : f n < m := hlt n (by omega)
    have hne : ∀ i, i < n → f i ≠ f n := fun i hi h => by
      have := hinj i n (by omega) (by omega) h; omega
    have h1 : ∀ i, i < n → (if f i < f n then f i else f i - 1) < m - 1 := by
      intro i hi
      have := hne i hi
      have := hlt i (by omega)
      split <;> omega
    have h2 : ∀ i j, i < n → j < n →
        (if f i < f n then f i else f i - 1) = (if f j < f n then f j else f j - 1) → i = j := by
      intro i j hi hj hg
      have := hne i hi
      have := hne j hj
      apply hinj i j (by omega) (by omega)
      split at hg <;> split at hg <;> omega
    have := pigeon n (m - 1) (fun i => if f i < f n then f i else f i - 1) h1 h2
    omega

/-- An entry with `rst = r` and the request vector `v`. -/
def entryV (N r : Nat) (v : BitVec N) : SvState := [("rst", LVec.ofNat 1 r), ("req", LVec.ofBitVec v)]

/-- A reset, then all `N` clients requesting for `N - 1` cycles. -/
def tightStim (N : Nat) : List SvState :=
  entryV N 1 0#N :: List.replicate (N - 1) (entryV N 0 (BitVec.allOnes N))

/-- The segment's request vectors. -/
def tightXs (N : Nat) : List (BitVec N × Unit) := List.replicate (N - 1) (BitVec.allOnes N, ())

/-- Two declarations of one list with the same name are the same declaration, when the names are
distinct. -/
theorem eq_of_name_eq {l : List Decl} (hnd : (l.map Decl.name).Nodup) {a b : Decl} (ha : a ∈ l)
    (hb : b ∈ l) (h : a.name = b.name) : a = b := by
  induction l with
  | nil => cases ha
  | cons c l ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨hc, hnd⟩ := hnd
    rcases List.mem_cons.mp ha with h1 | h1 <;> rcases List.mem_cons.mp hb with h2 | h2
    · rw [h1, h2]
    · exact absurd (List.mem_map.mpr ⟨b, h2, by rw [← h, h1]⟩) hc
    · exact absurd (List.mem_map.mpr ⟨a, h1, by rw [h, h2]⟩) hc
    · exact ih hnd h1 h2

/-- With distinct declaration names, an input port's declared width is the width `KnownEntry`
reads (`sigWidth`, the first declaration of the name). -/
theorem sigWidth_of_port {d : Design2} {n : String} {w : Nat}
    (hnd : (d.decls.toList.map Decl.name).Nodup) (h : (n, w) ∈ inputPorts d) : sigWidth d n = some w := by
  unfold inputPorts at h
  obtain ⟨dc, hdc, he⟩ := List.mem_filterMap.mp h
  have hn : dc.name = n ∧ dc.width = w := by
    by_cases hi : dc.isInput = true
    · simp only [hi, if_true, Option.some.injEq, Prod.mk.injEq] at he; exact he
    · simp only [hi] at he; cases he
  unfold sigWidth
  cases hf : d.decls.toList.find? (fun dc => dc.name == n) with
  | none => exact absurd (List.find?_eq_none.mp hf dc hdc) (by simp [hn.1])
  | some dc' =>
    have heq : dc' = dc := eq_of_name_eq hnd (List.mem_of_find?_eq_some hf) hdc
      (by rw [hn.1]; simpa using List.find?_some hf)
    simp [heq, hn.2]

/-- `Design2.inputNames` lists the input ports' names. -/
theorem inputNames_eq (d : Design2) : d.inputNames.toList = (inputPorts d).map Prod.fst := by
  simp only [Design2.inputNames, inputPorts, Array.toList_filterMap]
  generalize d.decls.toList = l
  induction l with
  | nil => rfl
  | cons dc l ih => by_cases h : dc.isInput = true <;> simp [h, ih]

/-- **A known entry of every design with the task's interface**: an entry that binds `rst` to a bit
and `req` to an `N`-bit vector (the distinct names of `Interface` make each port's first declaration
the port). -/
theorem knownEntry_of_interface {N : Nat} {d : Design2} (hI : task.Interface N d) (r : Nat)
    (v : BitVec N) : KnownEntry d (entryV N r v) := by
  obtain ⟨hin, -, hnd⟩ := hI
  have hrst : sigWidth d "rst" = some 1 := sigWidth_of_port hnd (by rw [hin]; simp [task])
  have hreq : sigWidth d "req" = some N := sigWidth_of_port hnd (by rw [hin]; simp [task])
  intro n hn
  rw [inputNames_eq, hin] at hn
  simp only [task, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl
  · simp [entryV, SvState.lookup]
  · simp [entryV, SvState.lookup, hrst]
  · simp [entryV, SvState.lookup, hreq, LVec.allKnown_ofBitVec, LVec.width_ofBitVec]

/-- **The bound is tight.** For `N ≥ 2`, no design satisfies the task with the response bound
`N - 2`: after a reset, let all `N` clients request for `N - 1` cycles; mutual exclusion allows at
most `N - 1` grants, so some client is not granted in a window of `N - 1` requests. The run is from
the all-zero power-up state on a stimulus every design with the task's interface takes as known. -/
theorem bound_tight {N : Nat} (hN : 2 ≤ N) (d : Design2) : ¬ task.SatisfiedAt N (N - 2) d := by
  rintro ⟨hI, ⟨-, ht⟩, hf, -⟩
  have hlen : (tightXs N).length = N - 1 := by simp [tightXs]
  have hks : KnownStim d (tightStim N) := by
    intro e he
    simp only [tightStim, List.mem_cons, List.mem_replicate] at he
    rcases he with rfl | ⟨-, rfl⟩
    · exact knownEntry_of_interface hI _ _
    · exact knownEntry_of_interface hI _ _
  obtain ⟨tr, hr⟩ := ht (zeros d) (powerUp_zeros d) σ_src (tightStim N) hks
  have hstim : ∀ c, 1 ≤ c → c < N → (tightStim N)[c]? = some (entryV N 0 (BitVec.allOnes N)) := by
    intro c h1 h2
    obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
    simp only [tightStim, List.getElem?_cons_succ, List.getElem?_replicate]
    rw [if_pos (by omega)]
  have hrel : Released "rst" (tightStim N) 1 (1 + (tightXs N).length) := by
    refine ⟨by decide, ⟨entryV N 1 0#N, rfl, rfl⟩, fun c h1 h2 => ?_⟩
    exact ⟨_, hstim c h1 (by omega), rfl⟩
  have hins : task.InsAt N (tightStim N) (1 - 1) ((0#N, ()) :: tightXs N) := by
    intro j x hx
    have hx2 : (((0#N, ()) :: tightXs N : List (BitVec N × Unit)))[j]? =
        some (x : BitVec N × Unit) := hx
    cases j with
    | zero =>
      rw [List.getElem?_cons_zero] at hx2
      cases hx2
      exact ⟨entryV N 1 0#N, by simp [tightStim], And.intro rfl trivial⟩
    | succ j =>
      rw [List.getElem?_cons_succ] at hx2
      simp only [tightXs, List.getElem?_replicate] at hx2
      split at hx2
      · cases hx2
        rw [show 1 - 1 + (j + 1) = 1 + j by omega]
        exact ⟨_, hstim (1 + j) (by omega) (by omega), And.intro rfl trivial⟩
      · cases hx2
  obtain ⟨y0, ys, hl, -, -, hsafe, hresp⟩ :=
    hf (zeros d) (powerUp_zeros d) σ_src (tightStim N) tr hks hr 1 (0#N, ()) (tightXs N) hrel hins
  -- the same length at the task's list type (`omega` sees the two `List.length`s as different atoms)
  have hlen2 : @List.length (task.In N) (tightXs N) = N - 1 := hlen
  -- every client is granted somewhere in the `N - 1` snapshots
  have hex : ∀ o : Fin N, ∃ i, i < N - 1 ∧
      ∃ g : BitVec N, ys[0 + i]? = some (g, ()) ∧ g.getLsbD o.val = true := by
    intro o
    obtain ⟨i, y, hi, hy, hg⟩ := hresp o 0 (by omega) (fun i x hi hx => by
      have hx2 : (tightXs N)[0 + i]? = some (x : BitVec N × Unit) := hx
      simp only [tightXs, List.getElem?_replicate] at hx2
      split at hx2
      · cases hx2; show (BitVec.allOnes N).getLsbD o.val = true; simp [o.isLt]
      · cases hx2)
    obtain ⟨g, u⟩ := y
    cases u
    exact ⟨i, by omega, g, hy, hg⟩
  -- at most one client per snapshot
  have hone : ∀ (k : Nat) (g : BitVec N), ys[k]? = some (g, ()) → AtMostOne g := by
    intro k g hy
    have hi : k < ys.length := (List.getElem?_eq_some_iff.mp hy).1
    have hx : (tightXs N)[k]? = some (BitVec.allOnes N, ()) := by
      simp only [tightXs, List.getElem?_replicate]; rw [if_pos (by omega)]
    exact (show Grants (BitVec.allOnes N) g from hsafe k _ _ hx hy).1
  obtain ⟨f, hf⟩ : ∃ f : Nat → Nat, ∀ o (h : o < N), f o < N - 1 ∧
      ∃ g : BitVec N, ys[0 + f o]? = some (g, ()) ∧ g.getLsbD o = true :=
    ⟨fun o => if h : o < N then Classical.choose (hex ⟨o, h⟩) else 0, fun o h => by
      simp only [dif_pos h]; exact Classical.choose_spec (hex ⟨o, h⟩)⟩
  have hf2 : ∀ a b, a < N → b < N → f a = f b → a = b := by
    intro a b ha hb hab
    obtain ⟨-, ga, hya, hga⟩ := hf a ha
    obtain ⟨-, gb, hyb, hgb⟩ := hf b hb
    have h3 : ys[0 + f a]? = ys[0 + f b]? := by rw [hab]
    have h4 := hya.symm.trans (h3.trans hyb)
    have : ga = gb := congrArg Prod.fst (Option.some.inj h4)
    subst this
    exact hone _ ga hya a b hga hgb
  have := pigeon N (N - 1) f (fun o h => (hf o h).1) hf2
  omega

/-! ## Executable reading: round-robin passes where the wrong designs fail (`#guard`, not a proof) -/

/-- The known value of an `N`-bit signal in snapshot `c`. -/
def bvAt (N : Nat) (tr : List SvState) (c : Nat) (n : String) : Option (BitVec N) :=
  (sigAt tr c n).bind fun v => v.toNat?.map (BitVec.ofNat N)

/-- The guarantee on one segment, as a `Bool` (an executable reading of `task.Guar`). -/
def guarB (N K : Nat) (xs : List (BitVec N)) (y0 : BitVec N) (ys : List (BitVec N)) : Bool :=
  let one (g : BitVec N) := (List.range N).all fun i => (List.range N).all fun j =>
    !(g.getLsbD i && g.getLsbD j) || i == j
  y0 == 0#N && xs.length == ys.length &&
  (xs.zip ys).all (fun (r, g) => one g && (g &&& ~~~r) == 0#N && (r == 0#N || g != 0#N)) &&
  (List.range N).all fun o => (List.range xs.length).all fun j =>
    !(j + K < xs.length && (List.range (K + 1)).all (fun i => (xs.getD (j + i) 0#N).getLsbD o)) ||
    (List.range (K + 1)).any fun i => (ys.getD (j + i) 0#N).getLsbD o

/-- Run `d` (at `N`) from the power-up state `st0` on a reset followed by the request vectors
`reqs`, and check the guarantee with the bound `N - 1` on the segment. -/
def passesFrom (N : Nat) (d : Design2) (st0 : SvState) (reqs : List Nat) : Bool :=
  let stim := entry N 1 0 :: reqs.map (entry N 0)
  let tr := trAt d st0 stim
  match bvAt N tr 0 "gnt", ((List.range reqs.length).mapM fun j => bvAt N tr (j + 1) "gnt") with
  | some y0, some ys => tr.length == stim.length && guarB N (N - 1) (reqs.map (BitVec.ofNat N)) y0 ys
  | _, _ => false

/-- `passesFrom` the all-zero power-up state. -/
def passes (N : Nat) (d : Design2) (reqs : List Nat) : Bool := passesFrom N d (zeros d) reqs

/-- Persistent and changing requests at `N = 2`. -/
def workload : List Nat := [3, 3, 3, 1, 0, 2, 3, 2, 2, 3, 1, 1, 3]

-- the designs with an unreset register are right from one power-up state and wrong from another
-- (the statement claims every power-up state: rule 2)
#guard passesFrom 2 xopt2 (onesAt xopt2 ["u"]) workload
#guard !passes 2 xopt2 workload
#guard passesFrom 2 (a16D 2) (onesAt (a16D 2) ["u"]) workload
#guard !passes 2 (a16D 2) workload
#guard passes 2 (ringD 2) workload
#guard !passesFrom 2 (ringD 2) (onesAt (ringD 2) ["u"]) workload
#guard passes 2 (edgeD 2) workload
#guard !passesFrom 2 (edgeD 2) (onesAt (edgeD 2) ["u"]) workload

#guard passes 2 merged2 workload
#guard passes 2 rr2 workload
#guard passes 2 rr2 [3, 3, 3, 3]
#guard passesFrom 2 rr2 (onesAt rr2 ["gnt", "ptr"]) workload
#guard !passes 2 (neverF 2) workload
#guard !passes 2 (everyoneF 2) workload
#guard !passes 2 (zeroF 2) workload
#guard !passes 2 (fixedF 2) workload
-- the Mealy design passes the snapshot checks on a workload where fixed priority is fair enough:
-- it is rejected by `MooreOut`, not by `Follows`
#guard passes 2 (mealyF 2) [1, 1, 2, 2, 0, 1]

#print axioms never_refuted
#print axioms everyone_refuted
#print axioms zero_refuted
#print axioms fixed_refuted
#print axioms mealy_refuted
#print axioms mealy_silicon
#print axioms bound_tight
#print axioms xopt_refuted
#print axioms a16_refuted
#print axioms ring_refuted
#print axioms reset_edge_refuted
#print axioms rr2_moore
#print axioms merged_not_moore

end SvGolf.Tasks.Arbiter.Refute
