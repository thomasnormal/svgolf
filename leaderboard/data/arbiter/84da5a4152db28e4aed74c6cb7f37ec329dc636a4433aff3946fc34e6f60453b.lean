import Submission.Design
import LeanModels.Sv.Gen2
import LeanModels.Sv.Hier2Gen
import LeanModels.Sv.Known2
import LeanModels.Sv.Mono2
import LeanModels.Sv.SeqFamily
import SvGolf.Seq
import SvGolf.React
import SvGolf.RoundRobin

/-!
# Reference solution for task `arbiter`: the registered mask round-robin, every `N ≥ 1`

`reference/rr_mask.sv` (own code; the real-world candidates wait on ls-sv, `tasks/arbiter/README.md` (j)) keeps
`gnt` and a thermometer `mask` in one `always_ff`, and computes the pick in one `always_comb`: the lowest
requester among `req & mask`, else the lowest requester. Proved for every `N ≥ 1` (`N` stays a variable)
through `ReactTask.satisfiedAt_of_rank` (`SvGolf/React.lean`):

1. **Agreement** (`rr_sem_eq`): `design.sem N` is the hand-built `rrD N` (`sv2_inst_simp`; the comb
   block's self-read guard by `comb_admits`). One proof-side lemma, `inst_ne_fill`: `x != '0` lowers at
   `x`'s width. `sv2_inst_simp` alone stops there, because ls-sv's private `maxW2` has a simp lemma for two
   known widths only (`maxW2_some`) and a fill has none (`tasks/arbiter/README.md` F11).
2. **One cycle in closed form** (`rr_cycle`, any values, `x` included): the inputs applied, the comb settle
   (one pass computes the block, a second changes nothing: `settle_rr`), the edge (`ff_run`), the commit
   (`commit_ff`), the comb settle again. `Terminates2` and the shape follow (`rr_terminates`). ls-sv's
   clock-step library has this closed form for FF-only designs only (`cycleStep2_ffOnly`); a design with a
   comb process proves its own settle here (README F10).
3. **The cycle on known values** (`rrNext_reset`, `rrNext_run`): from a reset, `gnt = 0` and `mask` all
   ones; otherwise `gnt = pick req mask` and `mask` the thermometer above the pick
   (`SvGolf.RoundRobin.pick`, `next`).
4. **The rank model** (`model`): the invariant `ArbInv` (every signal but `clk` known, the mask a
   thermometer with edge `e`), the outputs `gnt`, the rank of client `i` its cyclic distance from the edge
   (`RoundRobin.dist`, at most `N - 1`). Safety is `pick_grants`; progress is `RoundRobin.step`: a
   requester that loses gets strictly closer to the edge.
5. **Every power-up** (txtask-v2's rule 2, 2026-11-06): every power-up state of `rrD N` has the shape
   (`rr_powerUp`, by `powerUp_cons` once per declaration), so the rank model's claim holds from each,
   and termination from each (`rr_terminates`, `TerminatesPU.of_invariant`). The reset lemma already
   held from ANY state of the shape, so nothing else changed.
6. **Structure**: `Interface` (`rfl` on `rrD`, the names distinct by `decide`), `ClockedBy clk none`,
   `MooreOut` (no comb process writes an output: `mooreOut_of_combTargets`), and rule 3 (`rr_xsafe`,
   `xsafeB` by `simp`: equal operand widths, no division, no dynamic index).
-/

namespace Submission

open LeanModels.Sv SvGolf

/-! ## 1. Agreement: the loaded family is the hand-built `rrD` -/

/-- The `N`-bit fills `'0`, `'1` and the literal `1'b1`. -/
abbrev z0 (N : Nat) : LVec := LVec.replicate N .l0
abbrev z1 (N : Nat) : LVec := LVec.replicate N .l1
abbrev one1 : LVec := ⟨#[.l1]⟩

/-- The `always_comb` body: `mreq = req & mask; pick = (mreq != '0) ? lowbit(mreq) : lowbit(req)`. -/
def combBody (N : Nat) : Stmt2 :=
  .block #[
    .blockingAssign (.ident "mreq") (.binary .and (.ident "req") (.ident "mask")),
    .blockingAssign (.ident "pick")
      (.ternary (.binary .ne (.ident "mreq") (.lit (z0 N)))
        (.binary .and (.ident "mreq") (.binary .add (.unary .bnot (.ident "mreq")) (.resize N (.lit one1))))
        (.binary .and (.ident "req") (.binary .add (.unary .bnot (.ident "req")) (.resize N (.lit one1)))))]

/-- The `always_ff` body: reset, else `gnt <= pick` and the mask above the pick. -/
def ffBody (N : Nat) : Stmt2 :=
  .block #[
    .ifStmt (.ident "rst")
      (.block #[.nbaAssign (.ident "gnt") (.lit (z0 N)), .nbaAssign (.ident "mask") (.lit (z1 N))])
      (some (.block #[.nbaAssign (.ident "gnt") (.ident "pick"),
        .ifStmt (.binary .ne (.ident "pick") (.lit (z0 N)))
          (.nbaAssign (.ident "mask") (.unary .bnot (.binary .sub
            (.binary (.shl false) (.ident "pick") (.lit (LVec.ofInt 32 1))) (.resize N (.lit one1)))))
          none]))]

/-- The comb process. -/
def combP (N : Nat) : Process2 := .alwaysComb (combBody N)

/-- The flop process. -/
def ffP (N : Nat) : Process2 := .alwaysFF "clk" (ffBody N)

/-- The declarations at width `n`. -/
def rrDeclsW (n : Nat) : List Decl :=
  [{ name := "clk", width := 1, isInput := true }, { name := "rst", width := 1, isInput := true },
   { name := "req", width := n, isInput := true }, { name := "gnt", width := n, isOutput := true },
   { name := "mask", width := n }, { name := "mreq", width := n }, { name := "pick", width := n }]

/-- **The hand-built design** at `N`. -/
def rrD (N : Nat) : Design2 where
  name := "arbiter"
  decls := (rrDeclsW N).toArray
  processes := #[combP N, ffP N]

def rrScope (N : Int) : IEnv := { vals := [("N", N)], pwidths := [("N", 32)] }

def rrEnv (N : Int) : IEnv := { rrScope N with dims := dimTable (rrScope N) design.pdesign.decls }

theorem rr_paramEnv (N : Int) : design.pdesign.paramEnv2 [N] = .ok (rrEnv N) := rfl

def rrElems : List (String × Nat) := ["clk", "rst", "req", "gnt", "mask", "mreq", "pick"].map (·, 1)

theorem rr_decls (N : Int) :
    buildDecls (rrEnv N) design.pdesign.decls = .ok (rrDeclsW ((N - 1).natAbs + 1)) := by
  simp [design.pdesign, buildDecls, instDecl, PType.width_packed_cons, PDim.width, evalInt,
    rrEnv, rrScope, List.lookup, rrDeclsW, Gen2.except_ok_bind]

theorem rr_elems (N : Int) : buildElems (rrEnv N) design.pdesign.decls = .ok rrElems := by
  simp [design.pdesign, buildElems, PType.width_packed_cons, PDim.width, evalInt, rrEnv,
    rrScope, List.lookup, rrElems, Gen2.except_ok_bind]

/-- The instantiation environment. -/
abbrev rrE (N : Nat) : IEnv := (rrEnv N).withDecls (rrDeclsW N)

/-- The source bodies of the two processes. -/
def combT : PStmt := match design.pdesign.processes with
  | [.alwaysComb b, _] => b
  | _ => .block []

def ffT : PStmt := match design.pdesign.processes with
  | [_, .alwaysFF _ b] => b
  | _ => .block []

theorem rr_procs_src : design.pdesign.processes = [.alwaysComb combT, .alwaysFF "clk" ffT] := rfl

/-- `x != '0` lowers at the width of `x` (the fill takes the comparison's width). Stated with the
width lookup itself, so that `sv2_inst_simp` meets no `max` of a width and the fill's none. -/
theorem inst_ne_fill (E : IEnv) (el : List (String × Nat)) (n : String) (b : Logic) :
    instExpr2 E el none (.binary (.m0 .ne) (.ident n) (.fill b)) =
      .binary .ne (fitExpr2 E el (E.widths.lookup n) (.ident n))
        (fitExpr2 E el (E.widths.lookup n) (.fill b)) := by
  simp only [instExpr2, selfWidth2]
  cases E.widths.lookup n <;> rfl

macro "rr_inst_simp" : tactic => `(tactic| sv2_inst_simp [↓ inst_ne_fill, evalSized, ctype, evalAt,
  ctypeList, evalAtList, SymBinOp.constClass, PExpr.pushedTarget, PExpr.readsSignal, PExpr.readsSignalList,
  Gen2.except_pure, instStmt2, instStmts2, design.pdesign, rrEnv, rrScope, rrDeclsW, rrElems, combT, ffT,
  combBody, ffBody, dimTable, dimTableStep, PType.width_packed_cons, PDim.width, ctxOpWidth2, rigidMax2,
  PExpr.ctxPropagates, PExpr.constLeaf, PExpr.negGenvarWidened, LVec.width, divOperandWidth2,
  instDivOperand2, fitDivOperand2, *])

theorem comb_inst (N : Nat) (hN : 1 ≤ N) : instStmt2 (rrE N) rrElems combT = combBody N := by
  have h0 : (0 : Int) < N := by omega
  rr_inst_simp
  try and_intros
  all_goals first | rfl | (change fitExpr2 _ _ (some N) _ = _; rr_inst_simp) | skip

theorem ff_inst (N : Nat) (hN : 1 ≤ N) : instStmt2 (rrE N) rrElems ffT = ffBody N := by
  have h0 : (0 : Int) < N := by omega
  rr_inst_simp
  try and_intros
  all_goals first | rfl | (change fitExpr2 _ _ (some N) _ = _; rr_inst_simp) | skip

/-- The comb block's self-read guard admits the body at every `N` (every read the walk compares is
on another signal than the bits written after it). -/
theorem comb_admits (N : Nat) : (combBody N).combAdmits (fun n => (rrE N).widths.lookup n) = true := by
  simp [Stmt2.combAdmits, combBody, Stmt2.combViol, Stmt2.listCombViol, Stmt2.mayW,
    Stmt2.listMayW, Stmt2.mustW, Lhs2.mayW, Lhs2.mustW, Lhs2.rdW, Expr2.rdW, CombGuard.readsViol,
    CombGuard.whole, CombGuard.BWin.inter, CombGuard.BWin.sub, CombGuard.BWin.subAll, List.lookup,
    rrDeclsW]

theorem rr_static (N : Nat) (hN : 1 ≤ N) :
    design.pdesign.processes.map (instProcess2 (rrE N) rrElems) = [combP N, ffP N] := by
  rw [rr_procs_src]
  simp only [List.map_cons, List.map_nil, instProcess2, comb_inst N hN, ff_inst N hN,
    combGuardProc_of_admits (comb_admits N), combP, ffP]

theorem rr_instantiate2 (N : Nat) (hN : 1 ≤ N) :
    design.pdesign.instantiate2 [(N : Int)] (PDesign.surfaceFuel [(N : Int)]) =
      .ok (design.pdesign.assemble2 (rrEnv N) (rrDeclsW N) rrElems []) := by
  have hd := rr_decls N
  rw [Lib.natAbs_sub_one_add_one hN] at hd
  exact PDesign.instantiate2_of_ok rfl (rr_paramEnv _) hd (rr_elems _)
    (by simp [design.pdesign])

theorem rr_processes (N : Nat) (hN : 1 ≤ N) :
    (design.pdesign.instantiateD2 [(N : Int)]).processes.toList = [combP N, ffP N] := by
  rw [PDesign.instantiateD2_of_ok (rr_instantiate2 N hN), PDesign.assemble2_processes,
    rr_static N hN]
  simp [design.pdesign]

theorem rr_driversOk (N : Nat) :
    driversOk design.pdesign.declNames design.pdesign.inputNames [combP N, ffP N] = true := by
  first
  | (simp [driversOk, driverWins, Process2.drvWins, Process2.procWins, Process2.procWrites,
      Process2.exclusive, Process2.exclClash, Process2.procWinsOn, procExclusiveOk,
      drvWinsDisjoint, DrvWin.overlaps, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList,
      Lhs2.drvWins, combP, combBody, ffP, ffBody, design.pdesign, PDesign.declNames, PDesign.inputNames]; done)
  | rfl

/-- **The loaded family is `rrD`**, at every `N ≥ 1`. -/
theorem rr_sem_eq (N : Nat) (hN : 1 ≤ N) : design.sem N = rrD N := by
  have h1 : design.sem N = design.pdesign.instantiateD2 [(N : Int)] := by
    show design.pdesign.instantiateGD2 [(N : Int)] = _
    exact PDesign.instantiateGD2_of_driversOk (by rw [rr_processes N hN]; exact rr_driversOk N)
  rw [h1, PDesign.instantiateD2_of_ok (rr_instantiate2 N hN)]
  simp only [PDesign.assemble2, rr_static N hN, rrD]
  simp [design.pdesign]

/-! ## 2. One cycle, in closed form (any values, `x` included) -/

/-- The seven signals of `rrD`, in declaration order. -/
def SS (ck r q g m mr pk : LVec) : SvState :=
  [("clk", ck), ("rst", r), ("req", q), ("gnt", g), ("mask", m), ("mreq", mr), ("pick", pk)]

theorem apply_rr (N : Nat) (e : SvState) (ck r q g m mr pk : LVec) :
    applyInputs2 (rrD N) e (SS ck r q g m mr pk) =
      SS (appIn e "clk" ck) (appIn e "rst" r) (appIn e "req" q) g m mr pk := by
  unfold applyInputs2
  rw [← Array.foldl_toList]
  cases h1 : SvState.lookup e "clk" <;> cases h2 : SvState.lookup e "rst" <;>
    cases h3 : SvState.lookup e "req" <;>
    simp [rrD, rrDeclsW, SS, appIn, h1, h2, h3, SvState.set]

/-- A write of a full-width part at bit `0` is the part. -/
theorem insertAt_zero_full (v p : LVec) (h : p.width = v.width) : v.insertAt 0 p = p := by
  apply LVec.ext_getElem?
  intro i
  simp only [LVec.insertAt, Array.getElem?_ofFn]
  by_cases hi : i < v.width
  · have hp : i < p.bits.size := by simp only [LVec.width] at h hi; omega
    rw [dif_pos hi, Array.getElem?_eq_getElem hp]
    simp [h, hi, Array.getElem?_eq_getElem hp]
  · have hp : p.bits.size ≤ i := by simp only [LVec.width] at h hi; omega
    rw [dif_neg hi, Array.getElem?_eq_none hp]

theorem width_resizeU' (v : LVec) (w : Nat) : (v.resizeU w).width = w := by
  simp [LVec.resizeU, LVec.width]

/-- The pick the comb block computes from `req` and `mreq`. -/
def pickV (N : Nat) (q mr : LVec) : LVec :=
  LVec.ternary (.ofLogic (mr.neLogical (z0 N))) (mr.and (mr.not.add (one1.resizeU N)))
    (q.and (q.not.add (one1.resizeU N)))

/-- `mreq` after the comb block. -/
def MRv (q m mr : LVec) : LVec := (q.and m).resizeU mr.width

/-- `pick` after the comb block. -/
def PKv (N : Nat) (q m mr pk : LVec) : LVec := (pickV N q (MRv q m mr)).resizeU pk.width

/-- The state after the comb block. -/
def combS (N : Nat) (ck r q g m mr pk : LVec) : SvState :=
  SS ck r q g m (MRv q m mr) (PKv N q m mr pk)

theorem MRv_width (q m mr : LVec) : (MRv q m mr).width = mr.width := width_resizeU' _ _
theorem PKv_width (N : Nat) (q m mr pk : LVec) : (PKv N q m mr pk).width = pk.width :=
  width_resizeU' _ _

theorem comb_run (N F : Nat) (hF : 20 ≤ F) (ck r q g m mr pk : LVec) :
    runCombProcess2 F (SS ck r q g m mr pk) (combP N) = .ok (combS N ck r q g m mr pk) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 20 := ⟨F - 20, by omega⟩
  simp [combP, combBody, combS, MRv, PKv, pickV, runCombProcess2, execStmt2, execStmts2, evalExpr2,
    resolveLhs2, readSignal, SS, SvState.lookup, SvState.set, insertAt_zero_full]

theorem choose_single (σ : ScheduleOracle) (k i : Nat) : σ.choose k [i] = [i] :=
  List.perm_singleton.mp (σ.choose_perm k [i])

/-- **The comb settle**: one pass computes the block, a second pass changes nothing. -/
theorem settle_rr (N : Nat) (σ : ScheduleOracle) (F k : Nat) (hF : 24 ≤ F) (ck r q g m mr pk : LVec) :
    ∃ k', combSettle2 (rrD N) σ F (SS ck r q g m mr pk) k = .ok (combS N ck r q g m mr pk, k') := by
  have hci : (rrD N).combIndices = [0] := rfl
  have hp0 : (rrD N).processes[0]? = some (combP N) := rfl
  have hpass : ∀ f', 20 ≤ f' → ∀ (ck r q g m mr pk : LVec) (j : Nat),
      combPass2 (rrD N) f' (SS ck r q g m mr pk) (σ.choose j (rrD N).combIndices) =
        .ok (combS N ck r q g m mr pk) := by
    intro f' hf' ck r q g m mr pk j
    rw [hci, choose_single]
    simp only [combPass2, hp0, comb_run N f' hf', Res.ok_bind]
  have hidem : combS N ck r q g m (MRv q m mr) (PKv N q m mr pk) = combS N ck r q g m mr pk := by
    simp only [combS, MRv, PKv, width_resizeU']
  have hpass2 : ∀ f', 20 ≤ f' → ∀ j, combPass2 (rrD N) f' (combS N ck r q g m mr pk)
      (σ.choose j (rrD N).combIndices) = .ok (combS N ck r q g m mr pk) := by
    intro f' hf' j
    show combPass2 (rrD N) f' (SS ck r q g m (MRv q m mr) (PKv N q m mr pk)) _ = _
    rw [hpass f' hf', hidem]
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 24 := ⟨F - 24, by omega⟩
  rw [combSettle2.eq_2, hpass (f + 23) (by omega)]
  simp only [Res.ok_bind]
  by_cases hb : (combS N ck r q g m mr pk == SS ck r q g m mr pk) = true
  · rw [if_pos hb]; exact ⟨_, rfl⟩
  · rw [if_neg hb, combSettle2.eq_2, hpass2 (f + 22) (by omega)]
    simp only [Res.ok_bind]
    rw [beq_self_eq_true, if_pos rfl]
    exact ⟨_, rfl⟩

/-- `pick != '0`, the mask-update condition. -/
def NZ (N : Nat) (pk : LVec) : Bool := (LVec.ofLogic (pk.neLogical (z0 N))).condTrue

/-- The next mask `~((pick << 1) - 1)`. -/
def MaskV (N : Nat) (pk : LVec) : LVec :=
  ((pk.shl (LVec.ofInt 32 1)).sub (one1.resizeU N)).not

/-- The flop updates of a cycle, from the pre-edge `rst`, `gnt`, `mask` and `pick`. -/
def ffQ (N : Nat) (r g m pk : LVec) : NbaQueue2 :=
  if r.condTrue then [("gnt", 0, (z0 N).resizeU g.width), ("mask", 0, (z1 N).resizeU m.width)]
  else ("gnt", 0, pk.resizeU g.width) ::
    (if NZ N pk then [("mask", 0, (MaskV N pk).resizeU m.width)] else [])

theorem ff_run (N F : Nat) (hF : 30 ≤ F) (ck r q g m mr pk : LVec) :
    runEdgeProcess2 F (SS ck r q g m mr pk) [] (ffP N) = .ok (SS ck r q g m mr pk, ffQ N r g m pk) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 30 := ⟨F - 30, by omega⟩
  unfold ffQ NZ
  by_cases h1 : r.condTrue = true <;>
    by_cases h2 : (LVec.ofLogic (pk.neLogical (LVec.ofBitVec (0#N)))).condTrue = true <;>
    simp [ffP, ffBody, MaskV, runEdgeProcess2, execStmt2, execStmts2, evalExpr2, resolveLhs2, readSignal, SS,
      SvState.lookup, evalBinOp, h1, h2]

/-- `gnt` after the edge. -/
def Gv (N : Nat) (r g pk : LVec) : LVec :=
  if r.condTrue then (z0 N).resizeU g.width else pk.resizeU g.width

/-- `mask` after the edge. -/
def Mv (N : Nat) (r m pk : LVec) : LVec :=
  if r.condTrue then (z1 N).resizeU m.width else if NZ N pk then (MaskV N pk).resizeU m.width else m

theorem commit_ff (N : Nat) (ck r q g m mr pk : LVec) :
    commitNba2 (SS ck r q g m mr pk) (ffQ N r g m pk) = SS ck r q (Gv N r g pk) (Mv N r m pk) mr pk := by
  unfold ffQ Gv Mv
  by_cases h1 : r.condTrue = true <;> by_cases h2 : NZ N pk = true <;>
    simp [h1, h2, commitNba2, SS, SvState.lookup, SvState.set, insertAt_zero_full]

/-- **One cycle of `rrD`**, in closed form: the inputs, the comb block, the edge, the commit,
the comb block again. -/
def rrNext (N : Nat) (e : SvState) (ck r q g m mr pk : LVec) : SvState :=
  combS N (appIn e "clk" ck) (appIn e "rst" r) (appIn e "req" q)
    (Gv N (appIn e "rst" r) g (PKv N (appIn e "req" q) m mr pk))
    (Mv N (appIn e "rst" r) m (PKv N (appIn e "req" q) m mr pk))
    (MRv (appIn e "req" q) m mr) (PKv N (appIn e "req" q) m mr pk)

theorem rr_cycle (N : Nat) (σ : ScheduleOracle) (e : SvState) (ck r q g m mr pk : LVec)
    (kk F : Nat) (hF : 64 ≤ F) :
    ∃ k', cycleStep2 (rrD N) σ F e (SS ck r q g m mr pk) kk = .ok (rrNext N e ck r q g m mr pk, k') := by
  have hF' : 24 ≤ F := by omega
  obtain ⟨k1, h1⟩ := settle_rr N σ F kk hF' (appIn e "clk" ck) (appIn e "rst" r) (appIn e "req" q)
    g m mr pk
  obtain ⟨k2, h2⟩ := settle_rr N σ F (k1 + 1) hF' (appIn e "clk" ck) (appIn e "rst" r)
    (appIn e "req" q) (Gv N (appIn e "rst" r) g (PKv N (appIn e "req" q) m mr pk))
    (Mv N (appIn e "rst" r) m (PKv N (appIn e "req" q) m mr pk))
    (MRv (appIn e "req" q) m mr) (PKv N (appIn e "req" q) m mr pk)
  have hE : edgePass2 (rrD N) F (combS N (appIn e "clk" ck) (appIn e "rst" r) (appIn e "req" q) g m mr pk)
      [] (σ.choose k1 (rrD N).edgeIndices) =
      .ok (combS N (appIn e "clk" ck) (appIn e "rst" r) (appIn e "req" q) g m mr pk,
        ffQ N (appIn e "rst" r) g m (PKv N (appIn e "req" q) m mr pk)) := by
    rw [show (rrD N).edgeIndices = [1] from rfl, choose_single]
    simp only [edgePass2, combS, show (rrD N).processes[1]? = some (ffP N) from rfl,
      ff_run N F (by omega), Res.ok_bind]
  have hC : commitNba2 (combS N (appIn e "clk" ck) (appIn e "rst" r) (appIn e "req" q) g m mr pk)
      (ffQ N (appIn e "rst" r) g m (PKv N (appIn e "req" q) m mr pk)) =
      SS (appIn e "clk" ck) (appIn e "rst" r) (appIn e "req" q)
        (Gv N (appIn e "rst" r) g (PKv N (appIn e "req" q) m mr pk))
        (Mv N (appIn e "rst" r) m (PKv N (appIn e "req" q) m mr pk))
        (MRv (appIn e "req" q) m mr) (PKv N (appIn e "req" q) m mr pk) :=
    commit_ff N _ _ _ g m _ _
  have hre : ∀ a b, (rrD N).resetIndices a b = [] := fun _ _ => rfl
  refine ⟨k2, ?_⟩
  simp only [cycleStep2, apply_rr, h1, Res.ok_bind, Res.pure_eq, hre, hE, hC, h2] <;> rfl

/-! ## 3. The state shape, initially and through a cycle -/

/-- The states the design can be in: the seven signals, the registers and nets `N` bits wide. -/
def Shp (N : Nat) (st : SvState) : Prop :=
  ∃ ck r q g m mr pk, st = SS ck r q g m mr pk ∧ g.width = N ∧ m.width = N ∧ mr.width = N ∧ pk.width = N

theorem width_xVec (w : Nat) : (LVec.xVec w).width = w := by
  simp [LVec.xVec, LVec.replicate, LVec.width]

theorem rr_init (N : Nat) : Shp N (initState2 (rrD N)) :=
  ⟨LVec.xVec 1, LVec.xVec 1, LVec.xVec N, LVec.xVec N, LVec.xVec N, LVec.xVec N, LVec.xVec N, rfl,
    width_xVec N, width_xVec N, width_xVec N, width_xVec N⟩

theorem Gv_width (N : Nat) (r g pk : LVec) : (Gv N r g pk).width = g.width := by
  unfold Gv; split <;> exact width_resizeU' _ _

theorem Mv_width (N : Nat) (r m pk : LVec) : (Mv N r m pk).width = m.width := by
  unfold Mv
  split
  · exact width_resizeU' _ _
  · split
    · exact width_resizeU' _ _
    · rfl

theorem rrNext_shp {N : Nat} {e : SvState} {ck r q g m mr pk : LVec} (hg : g.width = N)
    (hm : m.width = N) (hmr : mr.width = N) (hpk : pk.width = N) :
    Shp N (rrNext N e ck r q g m mr pk) :=
  ⟨_, _, _, _, _, _, _, rfl, by rw [Gv_width, hg], by rw [Mv_width, hm],
    by rw [MRv_width, MRv_width, hmr], by rw [PKv_width, PKv_width, hpk]⟩

/-- One cycle from a state of the shape. -/
def Stp (N : Nat) (e prev st : SvState) : Prop :=
  ∃ ck r q g m mr pk, prev = SS ck r q g m mr pk ∧
    (g.width = N ∧ m.width = N ∧ mr.width = N ∧ pk.width = N) ∧ st = rrNext N e ck r q g m mr pk

/-! ## 4. The cycle on known values -/

theorem one_resize {N : Nat} : one1.resizeU N = LVec.ofBitVec (1#N) := by
  have h : one1 = LVec.ofBitVec (BitVec.ofBool true) := LVec.ofLogic_l1
  rw [h, LVec.resizeU_ofBitVec]
  congr 1
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [hi]

theorem ofInt_one : LVec.ofInt 32 1 = LVec.ofBitVec (1#32) := by
  first | decide | simp [LVec.ofInt] | rfl

/-- `<<` of known vectors (a known shift amount) is `BitVec`'s left shift by the amount's value. -/
theorem shl_ofBitVec {w v : Nat} (x : BitVec w) (y : BitVec v) :
    (LVec.ofBitVec x).shl (LVec.ofBitVec y) = LVec.ofBitVec (x <<< y.toNat) := by
  rw [LVec.eq_ofBitVec_iff]
  refine ⟨by simp [LVec.shl, LVec.shiftAmount?, LVec.width]; exact LVec.width_ofBitVec x, fun i hi => ?_⟩
  simp only [LVec.shl, LVec.shiftAmount?, LVec.toNat?_ofBitVec, Array.getElem?_ofFn,
    LVec.width_ofBitVec, hi, dite_true, BitVec.getLsbD_shiftLeft]
  by_cases h : i < y.toNat
  · simp [h, Logic.ofBool]
  · have h2 : i - y.toNat < w := by omega
    simp [h, h2, LVec.getElem?_ofBitVec]

theorem mr_val {N : Nat} (x m : BitVec N) (mr : LVec) (hmr : mr.width = N) :
    MRv (LVec.ofBitVec x) (LVec.ofBitVec m) mr = LVec.ofBitVec (x &&& m) := by
  simp [MRv, hmr]

theorem pickV_val {N : Nat} (x s : BitVec N) :
    pickV N (LVec.ofBitVec x) (LVec.ofBitVec s) =
      LVec.ofBitVec (if s = 0#N then x &&& (~~~x + 1#N) else s &&& (~~~s + 1#N)) := by
  unfold pickV
  rw [one_resize]
  by_cases h : s = 0#N <;>
    simp [h, LVec.add_ofBitVec]

theorem pk_val {N : Nat} (x m : BitVec N) (mr pk : LVec) (hmr : mr.width = N)
    (hpk : pk.width = N) :
    PKv N (LVec.ofBitVec x) (LVec.ofBitVec m) mr pk = LVec.ofBitVec (RoundRobin.pick x m) := by
  unfold PKv RoundRobin.pick
  rw [mr_val x m mr hmr, pickV_val, hpk, LVec.resizeU_ofBitVec, BitVec.setWidth_eq]

theorem NZ_val {N : Nat} (p : BitVec N) : NZ N (LVec.ofBitVec p) = decide (p ≠ 0#N) := by
  by_cases h : p = 0#N <;> simp [NZ, h]

theorem MaskV_val {N : Nat} (p : BitVec N) :
    MaskV N (LVec.ofBitVec p) = LVec.ofBitVec (~~~((p <<< 1) - 1#N)) := by
  unfold MaskV
  rw [ofInt_one, shl_ofBitVec, one_resize, LVec.sub_ofBitVec, LVec.not_ofBitVec]
  simp

theorem Gv_reset {N : Nat} {g : LVec} (pk : LVec) (hg : g.width = N) :
    Gv N (knownBit true) g pk = LVec.ofBitVec 0#N := by
  simp [Gv, hg]

theorem Mv_reset {N : Nat} {m : LVec} (pk : LVec) (hm : m.width = N) :
    Mv N (knownBit true) m pk = LVec.ofBitVec (BitVec.allOnes N) := by
  simp [Mv, hm]

theorem Gv_run {N : Nat} {g : LVec} (p : BitVec N) (hg : g.width = N) :
    Gv N (knownBit false) g (LVec.ofBitVec p) = LVec.ofBitVec p := by
  simp [Gv, hg]

theorem Mv_run {N : Nat} (x mk : BitVec N) :
    Mv N (knownBit false) (LVec.ofBitVec mk) (LVec.ofBitVec (RoundRobin.pick x mk)) =
      LVec.ofBitVec (RoundRobin.next x mk) := by
  unfold Mv RoundRobin.next
  rw [condTrue_knownBit, NZ_val, MaskV_val]
  by_cases h : RoundRobin.pick x mk = 0#N <;> simp [h]

theorem rrNext_reset {N : Nat} {e : SvState} {ck r q g m mr pk : LVec} {x : BitVec N}
    (hb : BitIs e "rst" true) (hq : SvState.lookup e "req" = some (LVec.ofBitVec x))
    (hg : g.width = N) (hm : m.width = N) (hmr : mr.width = N) (hpk : pk.width = N) :
    rrNext N e ck r q g m mr pk = SS (appIn e "clk" ck) (knownBit true) (LVec.ofBitVec x)
      (LVec.ofBitVec 0#N) (LVec.ofBitVec (BitVec.allOnes N))
      (LVec.ofBitVec (x &&& BitVec.allOnes N))
      (LVec.ofBitVec (RoundRobin.pick x (BitVec.allOnes N))) := by
  have hr : appIn e "rst" r = knownBit true := BitIs.appIn_eq hb r
  have hq' : appIn e "req" q = LVec.ofBitVec x := by simp only [appIn, hq, Option.getD_some]
  unfold rrNext combS
  rw [hr, hq', Gv_reset _ hg, Mv_reset _ hm,
    mr_val x _ (MRv (LVec.ofBitVec x) m mr) (by rw [MRv_width, hmr]),
    pk_val x _ (MRv (LVec.ofBitVec x) m mr) (PKv N (LVec.ofBitVec x) m mr pk)
      (by rw [MRv_width, hmr]) (by rw [PKv_width, hpk])]

theorem rrNext_run {N : Nat} {e : SvState} {ck r q g m mr pk : LVec} {x mk : BitVec N}
    (hb : BitIs e "rst" false) (hq : SvState.lookup e "req" = some (LVec.ofBitVec x))
    (hm : m = LVec.ofBitVec mk) (hg : g.width = N) (hmr : mr.width = N) (hpk : pk.width = N) :
    rrNext N e ck r q g m mr pk = SS (appIn e "clk" ck) (knownBit false) (LVec.ofBitVec x)
      (LVec.ofBitVec (RoundRobin.pick x mk)) (LVec.ofBitVec (RoundRobin.next x mk))
      (LVec.ofBitVec (x &&& RoundRobin.next x mk))
      (LVec.ofBitVec (RoundRobin.pick x (RoundRobin.next x mk))) := by
  subst hm
  have hr : appIn e "rst" r = knownBit false := BitIs.appIn_eq hb r
  have hq' : appIn e "req" q = LVec.ofBitVec x := by simp only [appIn, hq, Option.getD_some]
  unfold rrNext combS
  rw [hr, hq', pk_val x mk mr pk hmr hpk, mr_val x mk mr hmr, Gv_run _ hg, Mv_run,
    mr_val x _ (LVec.ofBitVec (x &&& mk)) (LVec.width_ofBitVec _),
    pk_val x _ (LVec.ofBitVec (x &&& mk)) (LVec.ofBitVec (RoundRobin.pick x mk))
      (LVec.width_ofBitVec _) (LVec.width_ofBitVec _)]

/-! ## 5. The rank model -/

/-- The known `N`-bit value of signal `n` (`0`-filled where unknown; read only in invariant states). -/
def bvOf (N : Nat) (n : String) (st : SvState) : BitVec N :=
  BitVec.ofNat N ((SvState.lookup st n).getD (LVec.xVec N)).toNat

theorem bvOf_gnt {N : Nat} {ck r q m mr pk : LVec} {g : BitVec N} :
    bvOf N "gnt" (SS ck r q (LVec.ofBitVec g) m mr pk) = g := by
  simp [bvOf, SS, SvState.lookup, BitVec.ofNat_toNat]

theorem bvOf_mask {N : Nat} {ck r q g mr pk : LVec} {mk : BitVec N} :
    bvOf N "mask" (SS ck r q g (LVec.ofBitVec mk) mr pk) = mk := by
  simp [bvOf, SS, SvState.lookup, BitVec.ofNat_toNat]

theorem SS_mask {ck r q g m mr pk ck' r' q' g' m' mr' pk' : LVec}
    (h : SS ck r q g m mr pk = SS ck' r' q' g' m' mr' pk') : m = m' := by
  simp only [SS, List.cons.injEq, Prod.mk.injEq, true_and, and_true] at h
  exact h.2.2.2.2.1

open Classical in
/-- The edge of a thermometer mask (`0` for any other vector). -/
noncomputable def edgeOf {N : Nat} (mk : BitVec N) : Nat :=
  if h : ∃ e, RoundRobin.Thermo mk e then Classical.choose h else 0

theorem edgeOf_eq {N : Nat} {mk : BitVec N} {e : Nat} (h : RoundRobin.Thermo mk e) : edgeOf mk = e := by
  have hex : ∃ e, RoundRobin.Thermo mk e := ⟨e, h⟩
  unfold edgeOf
  rw [dif_pos hex]
  exact (Classical.choose_spec hex).unique h

/-- **The invariant** of the snapshots from a reset on: every signal but `clk` known, the mask a
thermometer, `mreq` and `pick` the comb block's values. -/
def ArbInv (N : Nat) (st : SvState) : Prop :=
  ∃ (ck : LVec) (b : Bool) (x g mk : BitVec N) (e : Nat),
    st = SS ck (knownBit b) (LVec.ofBitVec x) (LVec.ofBitVec g) (LVec.ofBitVec mk)
      (LVec.ofBitVec (x &&& mk)) (LVec.ofBitVec (RoundRobin.pick x mk)) ∧ RoundRobin.Thermo mk e

theorem pick_grants {N : Nat} (x mk : BitVec N) : Tasks.Arbiter.Grants x (RoundRobin.pick x mk) :=
  ⟨fun _ _ hi hj => RoundRobin.pick_atMostOne hi hj, fun _ hi => RoundRobin.pick_sub hi,
    fun hx h => hx (RoundRobin.pick_eq_zero.1 h)⟩

/-- **The rank model** of the reference at `N`, with the response bound `N - 1`. -/
noncomputable def model (N : Nat) (hN : 1 ≤ N) :
    Tasks.Arbiter.task.RankModel N (N - 1) (design.sem N) where
  Shape := Shp N
  Step := Stp N
  init := by rw [rr_sem_eq N hN]; exact rr_init N
  cycle := by
    rintro σ F e prev k st k' ⟨ck, r, q, g, m, mr, pk, rfl, hw⟩ hc
    rw [rr_sem_eq N hN] at hc
    obtain ⟨k2, h2⟩ := rr_cycle N σ e ck r q g m mr pk k 64 (Nat.le_refl _)
    exact ⟨ck, r, q, g, m, mr, pk, rfl, hw, (Prod.mk.inj (cycleStep2_det hc h2)).1⟩
  shape := by
    rintro e prev st - ⟨ck, r, q, g, m, mr, pk, -, ⟨hg, hm, hmr, hpk⟩, rfl⟩
    exact rrNext_shp hg hm hmr hpk
  Inv := fun _ st => ArbInv N st
  out := fun st => (bvOf N "gnt" st, ())
  shows := by
    rintro - st ⟨ck, b, x, g, mk, e, rfl, -⟩
    show SvState.lookup _ "gnt" = some (LVec.ofBitVec (bvOf N "gnt" _)) ∧ True
    rw [bvOf_gnt]
    exact ⟨by simp [SS, SvState.lookup], trivial⟩
  rank := fun o st => RoundRobin.dist N (edgeOf (bvOf N "mask" st)) o.val
  rank_le := by
    rintro o - st ⟨ck, b, x, g, mk, e, rfl, hth⟩
    show RoundRobin.dist N (edgeOf (bvOf N "mask" _)) o.val ≤ N - 1
    rw [bvOf_mask, edgeOf_eq hth]
    exact RoundRobin.dist_le hth.1 o.isLt
  reset := by
    rintro e prev st ⟨x, ⟨⟩⟩ - ⟨ck, r, q, g, m, mr, pk, -, ⟨hg, hm, hmr, hpk⟩, rfl⟩ hb hx
    have hq : SvState.lookup e "req" = some (LVec.ofBitVec x) := hx.1
    rw [rrNext_reset hb hq hg hm hmr hpk]
    refine ⟨⟨_, true, x, 0#N, BitVec.allOnes N, 0, rfl, RoundRobin.thermo_allOnes N⟩, ?_⟩
    show bvOf N "gnt" _ = 0#N
    rw [bvOf_gnt]
  step := by
    rintro e prev st - ⟨x, ⟨⟩⟩ - ⟨ck, r, q, g, m, mr, pk, rfl, ⟨hg, hm, hmr, hpk⟩, rfl⟩
      ⟨ck', b', xp, gp, mk, ed, hprev, hth⟩ hb hx
    have hq : SvState.lookup e "req" = some (LVec.ofBitVec x) := hx.1
    have hmm : m = LVec.ofBitVec mk := SS_mask hprev
    have hmask : bvOf N "mask" (SS ck r q g m mr pk) = mk := by rw [hmm, bvOf_mask]
    rw [rrNext_run hb hq hmm hg hmr hpk]
    obtain ⟨e', hth', hprog⟩ := RoundRobin.step (x := x) hth
    refine ⟨⟨_, false, x, _, _, e', rfl, hth'⟩, ?_, fun o ho => ?_⟩
    · show Tasks.Arbiter.Grants x (bvOf N "gnt" _)
      rw [bvOf_gnt]
      exact pick_grants x mk
    · have ho' : x.getLsbD o.val = true := ho
      by_cases hp : (RoundRobin.pick x mk).getLsbD o.val = true
      · left
        show (bvOf N "gnt" _).getLsbD o.val = true
        rw [bvOf_gnt]
        exact hp
      · right
        show RoundRobin.dist N (edgeOf (bvOf N "mask" _)) o.val <
          RoundRobin.dist N (edgeOf (bvOf N "mask" _)) o.val
        rw [bvOf_mask, hmask, edgeOf_eq hth', edgeOf_eq hth]
        exact hprog o.val o.isLt ho' (by simpa using hp)

/-! ## 6. Structure, and the statement -/

theorem rr_interface (N : Nat) (hN : 1 ≤ N) : Tasks.Arbiter.task.Interface N (design.sem N) := by
  rw [rr_sem_eq N hN]
  exact ⟨rfl, rfl, by show (["clk", "rst", "req", "gnt", "mask", "mreq", "pick"] : List String).Nodup; decide⟩

theorem rr_moore (N : Nat) : MooreOut (rrD N) := by
  apply mooreOut_of_combTargets
  · simp [rrD, rrDeclsW, Design2.outputNames, Design2.inputNames]
  · simp [rrD, combP, combBody, ffP, ffBody, Process2.isCombPhase, processTargets, stmtTargets, stmtListTargets,
      stmtOptTargets, lhsTargets, Design2.outputNames, rrDeclsW]

theorem rr_disciplined (N : Nat) (hN : 1 ≤ N) : Tasks.Arbiter.task.Disciplined (design.sem N) := by
  rw [rr_sem_eq N hN]
  refine ⟨⟨by simp [Tasks.Arbiter.task, rrD, rrDeclsW, Design2.inputNames], fun p hp => ?_⟩, rr_moore N⟩
  have hm : p = combP N ∨ p = ffP N := by simpa [rrD] using hp
  rcases hm with rfl | rfl <;>
    simp [Tasks.Arbiter.task, combP, combBody, ffP, ffBody, edgeClock, asyncReset, processDataNames, stmtNames,
      stmtOptNames, stmtListNames, lhsNames, exprNames, Process2.isEdgePhase]

/-- **Every power-up state has the shape** (txtask-v2's rule 2): the seven signals in declaration
order, each at its declared width. -/
theorem rr_powerUp (N : Nat) : ∀ st, PowerUp (rrD N) st → Shp N st := by
  intro st h
  have h' : st.map Prod.fst = (rrDeclsW N).map Decl.name ∧
      ∀ b ∈ st.zip (rrDeclsW N), b.1.2.width = b.2.width ∧ b.1.2.allKnown = true := h
  rw [rrDeclsW] at h'
  obtain ⟨ck, r1, rfl, -, -, h1⟩ := powerUp_cons.mp h'
  obtain ⟨r, r2, rfl, -, -, h2⟩ := powerUp_cons.mp h1
  obtain ⟨q, r3, rfl, -, -, h3⟩ := powerUp_cons.mp h2
  obtain ⟨g, r4, rfl, hg, -, h4⟩ := powerUp_cons.mp h3
  obtain ⟨m, r5, rfl, hm, -, h5⟩ := powerUp_cons.mp h4
  obtain ⟨mr, r6, rfl, hmr, -, h6⟩ := powerUp_cons.mp h5
  obtain ⟨pk, r7, rfl, hpk, -, h7⟩ := powerUp_cons.mp h6
  obtain rfl := powerUp_nil.mp h7
  exact ⟨ck, r, q, g, m, mr, pk, rfl, hg, hm, hmr, hpk⟩

theorem rr_terminates (N : Nat) (hN : 1 ≤ N) : TerminatesPU (design.sem N) := by
  rw [rr_sem_eq N hN]
  refine TerminatesPU.of_invariant (Shp N) (rr_powerUp N) (fun σ => ⟨64, ?_⟩) ?_
  · rintro e _ kk ⟨ck, r, q, g, m, mr, pk, rfl, hg, hm, hmr, hpk⟩
    obtain ⟨k', h⟩ := rr_cycle N σ e ck r q g m mr pk kk 64 (Nat.le_refl _)
    exact ⟨_, _, h, rrNext_shp hg hm hmr hpk⟩
  · first
    | rfl
    | simp [rrD, combP, combBody, ffP, ffBody, Process2.hasQualifiedCase, Stmt2.hasQualifiedCase,
        Stmt2.listHasQualifiedCase]

theorem one1_allKnown : one1.allKnown = true := by
  rw [show one1 = LVec.ofBitVec (BitVec.ofBool true) from LVec.ofLogic_l1]
  exact LVec.allKnown_ofBitVec _
theorem one1_width : one1.width = 1 := rfl

/-- **Rule 3**: no construct of the design can create an `x` from known operands (every operand
pair of `&`, `!=`, `?:` has one width; no division, no dynamic index). -/
theorem rr_xsafe (N : Nat) (hN : 1 ≤ N) : XSafe (design.sem N) := by
  rw [rr_sem_eq N hN]
  simp [XSafe, xsafeB, rrD, rrDeclsW, combP, ffP, combBody, ffBody, xsProc, xsStmt, xsStmts, xsOpt,
    xsLhs, xsWidth, binW, sigWidth, ofInt_one, one1_allKnown, one1_width]

/-- **The reference satisfies the arbiter statement**, at every `N` in range. -/
theorem solution : Goal := by
  intro N hN
  obtain ⟨hN1, -⟩ := hN
  exact Tasks.Arbiter.task.satisfiedAt_of_rank (rr_interface N hN1) (rr_disciplined N hN1)
    (rr_terminates N hN1) (model N hN1)
    (fun st h => rr_powerUp N st (by rw [rr_sem_eq N hN1] at h; exact h)) (rr_xsafe N hN1)

/--
info: 'Submission.solution' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms solution

end Submission
