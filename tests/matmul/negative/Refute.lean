import tasks.matmul.Spec
import tests.sorter.negative.Refute

/-!
# Task `matmul`: kernel refutations of wrong designs (untrusted, kernel-checked; 2026-11-08)

Nothing here is part of the trusted base. The statement (`tasks/matmul/Spec.lean`, `TxTask.StatementV2`) is refuted
for a wrong design by ONE run that the kernel evaluates (`decide +kernel`), from one power-up state, on one known
stimulus: a reset, then one start with the operands `A`, `B` held at every entry (the rely holds on it whatever the
design shows: `rely_txn`), and the refutation holds for EVERY latency function:

* `hold_refuted`: after the start, a snapshot shows `done` = 1, and at that snapshot or a later one (before any other
  start) the design does not show `done` = 1 with `C = A·B`, which the guarantee asks from the first `done` to the
  next start. The run ends at that snapshot: no latency enters.
* `never_refuted`: the run comes to rest (a fixed point of the idle entry, `cycleStep2_fixed` of the sorter's
  `Refute.lean`, whose run lemmas this file reuses) without `done` ever rising after the start, so for every `lat`
  the run on the prefix and `lat + 1` more idle entries never shows `done`, which the guarantee asks within `lat`.
* `early_refuted`: a run with no start at all whose snapshot after the release shows `done` = 1, where the
  guarantee asks `done` = 0 before the first start (decided 2026-11-09). No latency enters.

The wrong designs are hand-built twins at one point of the family, `(N, W, AccW) = (2, 2, 4)` (or `(2, 2, 5)`, for
an attack that is wrong only when `AccW > 2W`), checked equal to the instance there of the design `load_sv` loads
(`#guard reprStr …`), and each refutation is stated for every family whose instance at that point is the twin.

A third shape, `hold2_refuted`, runs two transactions on the same operands (the second start is `Idle`: the first's
`done` is shown before it) and refutes the hold at the second one.

Here: the plumbing, the reference's twin, and the refutations of all seven attack designs of `tests/matmul/attacks/`
(`tests/expected.json` pins six at the `solution` stage with the reference's proof and `async_reset` at `source`;
these show that no proof exists, for any latency). The generated mutants are refuted in `Mutants.lean`.

| attack | point | run (`A`, `B` held from a start at entry 1) | refutation |
|---|---|---|---|
| `done_early` | (2, 2, 4) | `done` at snapshot 2, one product short | `done_early_refuted` |
| `off_by_one_k` | (2, 2, 4) | `done` at snapshot 2, one product short | `off_by_one_k_refuted` |
| `unsigned_product` | (2, 2, 4) | negative entries: `C` wrong at `done` | `unsigned_product_refuted` |
| `acc_2w` | (2, 2, 5) | `[[-2,-2],[-2,-2]]` squared: 8 wraps in the 4-bit accumulator | `acc_2w_refuted` |
| `missing_sign_ext` | (2, 2, 5) | one negative product per entry of row 0: off by 16 | `missing_sign_ext_refuted` |
| `no_clear_on_start` | (2, 2, 4) | the second transaction adds onto the first's `C` | `no_clear_on_start_refuted` |
| `async_reset` | (2, 2, 4) | no run: the control process has an asynchronous reset, which `Disciplined` refuses (since 2026-11-09) | `async_reset_refuted` |
-/

namespace SvGolf.Tasks.Matmul.Refute

open LeanModels.Sv SvGolf
open SvGolf.Tasks.Sorter.Refute (lastOr runFrom2_append runFrom2_fixed run2At_eq keeps cycleStep2_fixed trAt zeros
  onesAt powerUp_onesAt powerUp_zeros bitOf bitOf_of_bitIs bitIs_iff)

/-! ## Stimuli: a reset, then one start with the operands held -/

/-- One stimulus entry: `rst`, `start`, `A`, `B` (`m` bits each; the clock is not driven: it is not observed). -/
abbrev MRow (m : Nat) := Bool × Bool × BitVec m × BitVec m

/-- The entry of a row. -/
def ment {m : Nat} (r : MRow m) : SvState :=
  [("rst", LVec.ofBitVec (BitVec.ofBool r.1)), ("start", LVec.ofBitVec (BitVec.ofBool r.2.1)),
   ("A", LVec.ofBitVec r.2.2.1), ("B", LVec.ofBitVec r.2.2.2)]

/-- `n` rows: a reset (row 0), then rows with `rst` = 0 and `start` = 1 exactly at row `s`; `A = a`, `B = b` at every
row. -/
def txnRows {m : Nat} (a b : BitVec m) (s n : Nat) : List (MRow m) :=
  (List.range n).map fun c => (c == 0, c == s && c != 0, a, b)

theorem txnRows_length {m : Nat} (a b : BitVec m) (s n : Nat) : (txnRows a b s n).length = n := by
  simp [txnRows]

theorem txnRows_get {m : Nat} {a b : BitVec m} {s n c : Nat} (hc : c < n) :
    (txnRows a b s n)[c]? = some (c == 0, c == s && c != 0, a, b) := by
  simp [txnRows, hc]

/-- A longer stimulus of the same form begins with the shorter one. -/
theorem txnRows_add {m : Nat} (a b : BitVec m) (s n L : Nat) :
    txnRows a b s (n + L) = txnRows a b s n ++ (List.range L).map fun j =>
      (n + j == 0, n + j == s && n + j != 0, a, b) := by
  simp [txnRows, List.range_add, List.map_append, List.map_map, Function.comp_def]

theorem lookup_ment_rst {m : Nat} (r : MRow m) :
    SvState.lookup (ment r) "rst" = some (LVec.ofBitVec (BitVec.ofBool r.1)) := by
  simp [ment, SvState.lookup]

theorem lookup_ment_start {m : Nat} (r : MRow m) :
    SvState.lookup (ment r) "start" = some (LVec.ofBitVec (BitVec.ofBool r.2.1)) := by
  simp [ment, SvState.lookup]

theorem lookup_ment_A {m : Nat} (r : MRow m) : SvState.lookup (ment r) "A" = some (LVec.ofBitVec r.2.2.1) := by
  simp [ment, SvState.lookup]

theorem lookup_ment_B {m : Nat} (r : MRow m) : SvState.lookup (ment r) "B" = some (LVec.ofBitVec r.2.2.2) := by
  simp [ment, SvState.lookup]

/-- The start bit of the entry `c` of `txnRows`. -/
theorem stimBit_txn_start {m : Nat} {a b : BitVec m} {s n c : Nat} {bit : Bool} :
    StimBit ((txnRows a b s n).map ment) c "start" bit ↔ c < n ∧ (c == s && c != 0) = bit := by
  constructor
  · rintro ⟨e, he, hb⟩
    rw [List.getElem?_map] at he
    by_cases hc : c < n
    · rw [txnRows_get hc] at he
      simp only [Option.map_some, Option.some.injEq] at he
      subst he
      exact ⟨hc, (bitIs_iff (lookup_ment_start _) bit).1 hb⟩
    · simp [txnRows, hc] at he
  · rintro ⟨hc, hb⟩
    exact ⟨_, by rw [List.getElem?_map, txnRows_get hc]; rfl, (bitIs_iff (lookup_ment_start _) bit).2 hb⟩

theorem stimBit_txn_rst {m : Nat} {a b : BitVec m} {s n c : Nat} {bit : Bool} (hc : c < n) (hb : (c == 0) = bit) :
    StimBit ((txnRows a b s n).map ment) c "rst" bit :=
  ⟨_, by rw [List.getElem?_map, txnRows_get hc]; rfl, (bitIs_iff (lookup_ment_rst _) bit).2 hb⟩

/-! ## The reference's twin at `(N, W) = (2, 2)` and `AccW = aw`, with the parts a mutant changes as arguments -/

/-- A 32-bit constant. -/
def l32 (v : Nat) : Expr2 := .lit (LVec.ofNat 32 v)
/-- A 1-bit constant. -/
def l1 (v : Nat) : Expr2 := .lit (LVec.ofNat 1 v)
/-- `n <= e`. -/
def asg (n : String) (e : Expr2) : Stmt2 := .nbaAssign (.ident n) e
/-- The null statement `;` (the loader reads it as an empty block). -/
def nop : Stmt2 := .block #[]

/-- The declarations of `matmul_g1.sv` at `(2, 2, aw)`: the ports, then `k`, `busy`, `a_sh`, `b_sh`. -/
def mDecls (aw : Nat) : Array Decl :=
  #[{ name := "clk", width := 1, isInput := true }, { name := "rst", width := 1, isInput := true },
    { name := "start", width := 1, isInput := true }, { name := "A", width := 8, isInput := true },
    { name := "B", width := 8, isInput := true }, { name := "done", width := 1, isOutput := true },
    { name := "C", width := 4 * aw, isOutput := true }, { name := "k", width := 32 }, { name := "busy", width := 1 },
    { name := "a_sh", width := 8 }, { name := "b_sh", width := 8 }]

/-- The control process: `if (<rc>) <rs> else if (start) <ss> else if (busy) <bs>`. -/
def ctrlP (rc : Expr2) (rs ss bs : Stmt2) : Process2 :=
  .alwaysFF "clk" (.ifStmt rc rs (some (.ifStmt (.ident "start") ss (some (.ifStmt (.ident "busy") bs none)))))

def rstS : Stmt2 := .block #[asg "busy" (l1 0), asg "done" (l1 0), asg "k" (l32 0)]
/-- The start branch, with its five assignments as arguments. -/
def startW (bu dn kk aa bb : Stmt2) : Stmt2 := .block #[bu, dn, kk, aa, bb]
def stBusy : Stmt2 := asg "busy" (l1 1)
def stDone : Stmt2 := asg "done" (l1 0)
def stK : Stmt2 := asg "k" (l32 0)
def stA : Stmt2 := asg "a_sh" (.ident "A")
def stB : Stmt2 := asg "b_sh" (.ident "B")
def startS : Stmt2 := startW stBusy stDone stK stA stB
/-- The step branch: `k <= k + 1; a_sh <= a_sh >> W; b_sh <= b_sh >> (N*W); if (<cond>) <fin>`. -/
def stepW (kk aa bb : Stmt2) (cond : Expr2) (fin : Stmt2) : Stmt2 := .block #[kk, aa, bb, .ifStmt cond fin none]
def stepK : Stmt2 := asg "k" (.binary .add (.ident "k") (l32 1))
def stepA : Stmt2 := asg "a_sh" (.binary (.shr false) (.ident "a_sh") (l32 2))
def stepB : Stmt2 := asg "b_sh" (.binary (.shr false) (.ident "b_sh") (.binary .mul (l32 2) (l32 2)))
def stepCond : Expr2 := .binary .eq (.ident "k") (.binary .sub (l32 2) (l32 1))
def finS : Stmt2 := .block #[asg "busy" (l1 0), asg "done" (l1 1)]
def stepS : Stmt2 := stepW stepK stepA stepB stepCond finS
def ctrlRef : Process2 := ctrlP (.ident "rst") rstS startS stepS

/-- `C[(i*2+j)*aw +: aw]`. -/
def cR (aw i j : Nat) : Expr2 := .slice (.ident "C") ((i * 2 + j) * aw) aw
def cW (aw i j : Nat) (e : Expr2) : Stmt2 := .nbaAssign (.slice "C" ((i * 2 + j) * aw) aw) e
/-- `{{r{v[lo+1]}}, v[lo +: 2]}`: a 2-bit entry sign-extended by `r` copies of its sign bit. -/
def sext (r : Nat) (v : String) (lo : Nat) : Expr2 :=
  .concat #[.repl r (.concat #[.slice (.ident v) (lo + 1) 1]), .slice (.ident v) lo 2]
/-- The accumulation `C[i][j] + {..a..} * {..b..}`, at the operands' `aw + 2` bits, cut to `aw` (`op` the `+`). -/
def macE (op : BinOp) (aw i j : Nat) : Expr2 :=
  .resize aw (.binary op (.resize (aw + 2) (cR aw i j)) (.binary .mul (sext aw "a_sh" (i * 4)) (sext aw "b_sh" (j * 2))))
/-- The accumulator process of entry `(i, j)`: `if (start) <clr> else if (busy) <upd>`. -/
def macP (clr upd : Stmt2) : Process2 :=
  .alwaysFF "clk" (.ifStmt (.ident "start") clr (some (.ifStmt (.ident "busy") upd none)))
def macRef (aw i j : Nat) : Process2 := macP (cW aw i j (.lit (LVec.ofNat aw 0))) (cW aw i j (macE .add aw i j))

/-- The design with the control process `ctrl` and the accumulator process `mac i j` of every entry, in the loader's
order. -/
def mWith (aw : Nat) (ctrl : Process2) (mac : Nat → Nat → Process2) : Design2 :=
  { name := "matmul", decls := mDecls aw, processes := #[ctrl, mac 0 0, mac 0 1, mac 1 0, mac 1 1] }

/-- The reference `matmul_g1.sv` at `(2, 2, aw)`. -/
def refD (aw : Nat) : Design2 := mWith aw ctrlRef (macRef aw)

/-- The four entries `(i, j)` in the generate loops' order. -/
def entries : List (Nat × Nat) := [(0, 0), (0, 1), (1, 0), (1, 1)]

/-- A design with the given declarations, control process and per-entry processes (in the generate loops' order). -/
def mWithL (decls : Array Decl) (ctrl : Process2) (per : Nat → Nat → List Process2) : Design2 :=
  { name := "matmul", decls, processes := (ctrl :: entries.flatMap fun (i, j) => per i j).toArray }

load_sv refL from "tasks/matmul/reference/matmul_g1.sv"

#guard reprStr (refL.sem 2 2 4) == reprStr (refD 4)
#guard reprStr (refL.sem 2 2 5) == reprStr (refD 5)

/-! ## The attacks of `tests/matmul/attacks/` (twins checked as above) -/

/-- `done_early.sv`: `done` is set one step early (`k == N - 2`, its own `if`); `busy` still clears at `k == N - 1`. -/
def doneEarlyD : Design2 :=
  mWith 4 (ctrlP (.ident "rst") rstS startS (.block #[stepK, stepA, stepB,
      .ifStmt (.binary .eq (.ident "k") (.binary .sub (l32 2) (l32 2))) (asg "done" (l1 1)) none,
      .ifStmt stepCond (asg "busy" (l1 0)) none]))
    (macRef 4)

/-- `off_by_one_k.sv`: the step counter starts at 1 on start (`k <= 32'd1`). -/
def offByOneKD : Design2 := mWith 4 (ctrlP (.ident "rst") rstS (startW stBusy stDone (asg "k" (l32 1)) stA stB) stepS)
  (macRef 4)

/-- `unsigned_product.sv`: `C + a * b` with the W-bit selects zero-extended to the AccW-bit context. -/
def unsignedProductD : Design2 :=
  mWith 4 ctrlRef fun i j => macP (cW 4 i j (.lit (LVec.ofNat 4 0)))
    (cW 4 i j (.binary .add (cR 4 i j) (.binary .mul (.resize 4 (.slice (.ident "a_sh") (i * 4) 2))
      (.resize 4 (.slice (.ident "b_sh") (j * 2) 2)))))

/-- `acc_2w.sv` at `AccW = 5`: a 2W-bit accumulator `acc`, and `C` its sign extension by continuous assignments. -/
def acc2wD : Design2 :=
  mWithL (mDecls 5 |>.push { name := "acc", width := 16 }) ctrlRef fun i j =>
    let lo := (i * 2 + j) * 4
    [macP (.nbaAssign (.slice "acc" lo 4) (.lit (LVec.ofNat 4 0)))
       (.nbaAssign (.slice "acc" lo 4) (.resize 4 (.binary .add (.resize 6 (.slice (.ident "acc") lo 4))
         (.binary .mul (sext 4 "a_sh" (i * 4)) (sext 4 "b_sh" (j * 2)))))),
     .assign (.slice "C" ((i * 2 + j) * 5) 5)
       (.resize 5 (.concat #[.repl 5 (.concat #[.slice (.ident "acc") (lo + 3) 1]), .slice (.ident "acc") lo 4]))]

/-- `missing_sign_ext.sv` at `AccW = 5`: the product `p` sign-extended to 2W bits only, then zero-extended into `C`. -/
def missingSignExtD : Design2 :=
  mWithL (mDecls 5 |>.push { name := "p", width := 16 }) ctrlRef fun i j =>
    let lo := (i * 2 + j) * 4
    [.assign (.slice "p" lo 4) (.binary .mul (sext 2 "a_sh" (i * 4)) (sext 2 "b_sh" (j * 2))),
     macP (cW 5 i j (.lit (LVec.ofNat 5 0)))
       (cW 5 i j (.binary .add (cR 5 i j) (.resize 5 (.slice (.ident "p") lo 4))))]

/-- `no_clear_on_start.sv`: the accumulators are cleared by the reset, not by the start. -/
def noClearOnStartD : Design2 :=
  mWith 4 ctrlRef fun i j => .alwaysFF "clk" (.ifStmt (.ident "rst") (cW 4 i j (.lit (LVec.ofNat 4 0)))
    (some (.ifStmt (.ident "busy") (cW 4 i j (macE .add 4 i j)) none)))

/-- The control process of `async_reset.sv`: the reference's body under `always_ff @(posedge clk or posedge rst)`. -/
def ctrlAsync : Process2 :=
  .alwaysFFR "clk" "rst" (.ifStmt (.ident "rst") rstS (some (.ifStmt (.ident "start") startS
    (some (.ifStmt (.ident "busy") stepS none))))) true

/-- `async_reset.sv`: the reference with an asynchronous reset in its control process. -/
def asyncResetD : Design2 := mWith 4 ctrlAsync (macRef 4)

load_sv doneEarlyL from "tests/matmul/attacks/done_early.sv"
load_sv offByOneKL from "tests/matmul/attacks/off_by_one_k.sv"
load_sv unsignedProductL from "tests/matmul/attacks/unsigned_product.sv"
load_sv acc2wL from "tests/matmul/attacks/acc_2w.sv"
load_sv missingSignExtL from "tests/matmul/attacks/missing_sign_ext.sv"
load_sv noClearOnStartL from "tests/matmul/attacks/no_clear_on_start.sv"
load_sv asyncResetL from "tests/matmul/attacks/async_reset.sv"

#guard reprStr (doneEarlyL.sem 2 2 4) == reprStr doneEarlyD
#guard reprStr (offByOneKL.sem 2 2 4) == reprStr offByOneKD
#guard reprStr (unsignedProductL.sem 2 2 4) == reprStr unsignedProductD
#guard reprStr (acc2wL.sem 2 2 5) == reprStr acc2wD
#guard reprStr (missingSignExtL.sem 2 2 5) == reprStr missingSignExtD
#guard reprStr (noClearOnStartL.sem 2 2 4) == reprStr noClearOnStartD
#guard reprStr (asyncResetL.sem 2 2 4) == reprStr asyncResetD

/-! ## The rely, and the two refutations -/

/-- The operands of the row stimulus are `(a, b)` at every entry. -/
theorem opsAt_txn {aw : Nat} {a b : BitVec 8} {s n c : Nat} (hc : c < n) :
    task.OpsAt (2, 2, aw) ((txnRows a b s n).map ment) c (a, b, ()) := by
  refine ⟨ment (c == 0, c == s && c != 0, a, b), by rw [List.getElem?_map, txnRows_get hc]; rfl, ?_⟩
  show SvState.lookup _ "A" = some (LVec.ofBitVec a) ∧ SvState.lookup _ "B" = some (LVec.ofBitVec b) ∧ True
  exact ⟨lookup_ment_A _, lookup_ment_B _, trivial⟩

theorem ops_unique {aw : Nat} {a b : BitVec 8} {s n c : Nat} {x : task.Ops (2, 2, aw)}
    (h : task.OpsAt (2, 2, aw) ((txnRows a b s n).map ment) c x) : x = (a, b, ()) := by
  obtain ⟨e, he, h1, h2, -⟩ := h
  rw [List.getElem?_map] at he
  by_cases hc : c < n
  · rw [txnRows_get hc] at he
    simp only [Option.map_some, Option.some.injEq] at he
    subst he
    obtain ⟨xa, xb, xu⟩ := x
    cases xu
    have ha : LVec.ofBitVec a = LVec.ofBitVec xa := Option.some.inj ((lookup_ment_A _).symm.trans h1)
    have hb : LVec.ofBitVec b = LVec.ofBitVec xb := Option.some.inj ((lookup_ment_B _).symm.trans h2)
    rw [LVec.ofBitVec_inj.mp ha, LVec.ofBitVec_inj.mp hb]
  · simp [txnRows, hc] at he

/-- **The rely holds** on `txnRows a b s n` from the release `1` at the horizon `n`, for every trace: the one start
is at `s`, after no earlier start, and the operands never change. -/
theorem rely_txn {aw : Nat} {a b : BitVec 8} {s n : Nat} (tr : List SvState) :
    task.Rely (2, 2, aw) ((txnRows a b s n).map ment) tr 1 n := by
  have hst : ∀ c, StimBit ((txnRows a b s n).map ment) c "start" true → c = s ∧ c ≠ 0 := by
    intro c h
    obtain ⟨-, h⟩ := stimBit_txn_start.1 h
    simpa using h
  intro c h1 h2
  refine ⟨⟨c == s && c != 0, stimBit_txn_start.2 ⟨h2, rfl⟩⟩, ⟨_, opsAt_txn h2⟩, ?_, ?_⟩
  · intro hc s' _ h2' hs'
    exact absurd ((hst s' hs').1.trans (hst c hc).1.symm) (by omega)
  · intro s' x _ _ _ hx _
    rw [ops_unique hx]
    exact opsAt_txn h2

theorem released_txn {m : Nat} {a b : BitVec m} {s n : Nat} (hn : 0 < n) :
    Released "rst" ((txnRows a b s n).map ment) 1 n :=
  ⟨by decide, stimBit_txn_rst hn rfl, fun c h1 h2 => stimBit_txn_rst h2 (by simp; omega)⟩

/-- `trA[c]` shows `done` = 1 and the payload `C = v`, decided. -/
def holdsAt {w : Nat} (tr : List SvState) (c : Nat) (v : BitVec w) : Bool :=
  match tr[c]? with
  | some st => bitOf st "done" && (SvState.lookup st "C" == some (LVec.ofBitVec v))
  | none => false

/-- **The hold refutation**, for every latency: after the start `s` (`0 < s < n`), the snapshot `c'` shows `done` =
1, and the snapshot `c` (`c' ≤ c < n`) does not show `done` = 1 with `C = A·B`. -/
theorem hold_refuted {aw : Nat} {lat : Nat} {d : Design2} (st0 : SvState) (hpu : PowerUp d st0) (a b : BitVec 8)
    (s n c' c : Nat) (hs : 0 < s ∧ s ≤ c' ∧ c' ≤ c ∧ c < n)
    (hks : KnownStim d ((txnRows a b s n).map ment))
    (hrun : run2At d σ_src 64 st0 ((txnRows a b s n).map ment) = .ok (trAt d st0 ((txnRows a b s n).map ment)))
    (hdone : (trAt d st0 ((txnRows a b s n).map ment))[c']?.map (bitOf · "done") = some true)
    (hbad : holdsAt (trAt d st0 ((txnRows a b s n).map ment)) c (product 2 2 aw a b) = false) :
    ¬ task.FollowsPU (2, 2, aw) lat d := fun hf => by
  have hg := hf st0 hpu σ_src _ _ hks ⟨64, hrun⟩ 1 n (released_txn (by omega)) (rely_txn _)
  have hss : StimBit ((txnRows a b s n).map ment) s "start" true :=
    stimBit_txn_start.2 ⟨by omega, by simp; omega⟩
  obtain ⟨-, hhold⟩ := hg.2.2 s (a, b, ()) (by omega) (by omega) hss (opsAt_txn (by omega))
  have hc' : TraceBit (trAt d st0 ((txnRows a b s n).map ment)) c' task.done true := by
    cases ht : (trAt d st0 ((txnRows a b s n).map ment))[c']? with
    | none => rw [ht] at hdone; cases hdone
    | some st =>
      rw [ht, Option.map_some, Option.some.injEq] at hdone
      refine ⟨st, ht, ?_⟩
      unfold bitOf at hdone
      exact beq_iff_eq.mp hdone
  obtain ⟨st, hst, hb, hC, -⟩ := hhold c (by omega) (by omega) ⟨c', by omega, by omega, hc'⟩
    (fun s' h1 h2 hs' => by have := stimBit_txn_start.1 hs'; simp at this; omega)
  unfold holdsAt at hbad
  rw [hst] at hbad
  simp only [Bool.and_eq_false_iff] at hbad
  rcases hbad with h | h
  · rw [bitOf_of_bitIs (n := "done") hb] at h; cases h
  · have : SvState.lookup st "C" = some (LVec.ofBitVec (product 2 2 aw a b)) := hC
    simp [this] at h

/-- **The never-done refutation**, for every latency: after the start `s` (`0 < s < n`) no snapshot of the prefix
shows `done` = 1, and its last snapshot is a fixed point of the idle entry (`start` = 0, the operands still held)
showing `done` = 0. Then for every `lat` the run on `txnRows a b s (n + lat + 1)` is the prefix's trace and copies of
its last snapshot, and `done` never rises within `lat` of the start. -/
theorem never_refuted {aw : Nat} {lat : Nat} {d : Design2} (st0 : SvState) (hpu : PowerUp d st0) (a b : BitVec 8)
    (s n : Nat) (hs : 0 < s ∧ s < n) (hq : d.processes.toList.any Process2.hasQualifiedCase = false)
    (hks : KnownStim d ((txnRows a b s n).map ment)) (hki : KnownEntry d (ment (false, false, a, b)))
    (hrun : run2At d σ_src 64 st0 ((txnRows a b s n).map ment) = .ok (trAt d st0 ((txnRows a b s n).map ment)))
    (hfix : ∀ k, cycleStep2 d σ_src 64 (ment (false, false, a, b)) (lastOr st0 (trAt d st0 ((txnRows a b s n).map ment)))
      k = .ok (lastOr st0 (trAt d st0 ((txnRows a b s n).map ment)), k + 3))
    (hrest : bitOf (lastOr st0 (trAt d st0 ((txnRows a b s n).map ment))) "done" = false)
    (hnone : ∀ c, c < n → s ≤ c → (trAt d st0 ((txnRows a b s n).map ment))[c]?.map (bitOf · "done") = some false) :
    ¬ task.FollowsPU (2, 2, aw) lat d := fun hf => by
  rw [run2At_eq hq] at hrun
  generalize trAt d st0 ((txnRows a b s n).map ment) = trA at hrun hfix hrest hnone
  generalize hstF : lastOr st0 trA = stF at hfix hrest
  have hlenA : trA.length = n := by simpa [txnRows_length] using runFrom2_length hrun
  have hrows : txnRows a b s (n + (lat + 1)) = txnRows a b s n ++ List.replicate (lat + 1) (false, false, a, b) := by
    rw [txnRows_add]
    congr 1
    rw [List.eq_replicate_iff]
    refine ⟨by simp, fun x hx => ?_⟩
    simp only [List.mem_map, List.mem_range] at hx
    obtain ⟨j, -, rfl⟩ := hx
    have h1 : (n + j == 0) = false := by simp; omega
    have h2 : (n + j == s && n + j != 0) = false := by simp; omega
    rw [h1, h2]
  have hstim : (txnRows a b s (n + (lat + 1))).map ment =
      (txnRows a b s n).map ment ++ List.replicate (lat + 1) (ment (false, false, a, b)) := by
    rw [hrows, List.map_append, List.map_replicate]
  have hrunF : RunsAt d σ_src st0 ((txnRows a b s (n + (lat + 1))).map ment) (trA ++ List.replicate (lat + 1) stF) := by
    refine ⟨64, ?_⟩
    rw [run2At_eq hq, hstim]
    exact runFrom2_append hrun fun k' => by rw [hstF]; exact runFrom2_fixed hfix (lat + 1) k'
  have hksF : KnownStim d ((txnRows a b s (n + (lat + 1))).map ment) := by
    rw [hstim]
    intro e he
    rcases List.mem_append.mp he with he | he
    · exact hks e he
    · rw [List.eq_of_mem_replicate he]; exact hki
  have hg := hf st0 hpu σ_src _ _ hksF hrunF 1 (n + (lat + 1)) (released_txn (by omega)) (rely_txn _)
  have hss : StimBit ((txnRows a b s (n + (lat + 1))).map ment) s "start" true :=
    stimBit_txn_start.2 ⟨by omega, by simp; omega⟩
  obtain ⟨hlate, -⟩ := hg.2.2 s (a, b, ()) (by omega) (by omega) hss (opsAt_txn (by omega))
  obtain ⟨c, hc1, hc2, st, hst, hb⟩ := hlate (by omega)
  have hb' := bitOf_of_bitIs (n := "done") hb
  rcases Nat.lt_or_ge c n with hc | hc
  · have := hnone c hc hc1
    rw [List.getElem?_append_left (by omega)] at hst
    rw [hst, Option.map_some, Option.some.injEq, hb'] at this
    cases this
  · rw [List.getElem?_append_right (by omega), List.getElem?_replicate] at hst
    split at hst
    · cases hst; rw [hrest] at hb'; cases hb'
    · cases hst

/-- **The early-`done` refutation**, for every latency: a run with no start at all (`txnRows a b 0 n`: a reset,
then rows with `rst` = 0 and `start` = 0) whose snapshot `c` after the release shows `done` = 1. `done` = 1 claims a
result, and before the first start there is none: the guarantee asks `done` = 0 there (decided 2026-11-09). -/
theorem early_refuted {aw : Nat} {lat : Nat} {d : Design2} (st0 : SvState) (hpu : PowerUp d st0) (a b : BitVec 8)
    (n c : Nat) (hc : 1 ≤ c ∧ c < n)
    (hks : KnownStim d ((txnRows a b 0 n).map ment))
    (hrun : run2At d σ_src 64 st0 ((txnRows a b 0 n).map ment) = .ok (trAt d st0 ((txnRows a b 0 n).map ment)))
    (hdone : (trAt d st0 ((txnRows a b 0 n).map ment))[c]?.map (bitOf · "done") = some true) :
    ¬ task.FollowsPU (2, 2, aw) lat d := fun hf => by
  have hg := hf st0 hpu σ_src _ _ hks ⟨64, hrun⟩ 1 n (released_txn (by omega)) (rely_txn _)
  obtain ⟨st, hst, hb⟩ := hg.2.1 c hc.1 hc.2 fun s' _ _ hs' => by
    have := stimBit_txn_start.1 hs'
    simp at this
  rw [hst, Option.map_some, Option.some.injEq, bitOf_of_bitIs (n := "done") hb] at hdone
  cases hdone

/-! ## Two transactions (an attack that is wrong only from the second) -/

/-- `n` rows: a reset (row 0), then rows with `rst` = 0 and `start` = 1 exactly at rows `s1` and `s2`; `A = a`,
`B = b` at every row. -/
def txnRows2 {m : Nat} (a b : BitVec m) (s1 s2 n : Nat) : List (MRow m) :=
  (List.range n).map fun c => (c == 0, (c == s1 || c == s2) && c != 0, a, b)

theorem txnRows2_get {m : Nat} {a b : BitVec m} {s1 s2 n c : Nat} (hc : c < n) :
    (txnRows2 a b s1 s2 n)[c]? = some (c == 0, (c == s1 || c == s2) && c != 0, a, b) := by
  simp [txnRows2, hc]

theorem stimBit_txn2_start {m : Nat} {a b : BitVec m} {s1 s2 n c : Nat} {bit : Bool} :
    StimBit ((txnRows2 a b s1 s2 n).map ment) c "start" bit ↔ c < n ∧ ((c == s1 || c == s2) && c != 0) = bit := by
  constructor
  · rintro ⟨e, he, hb⟩
    rw [List.getElem?_map] at he
    by_cases hc : c < n
    · rw [txnRows2_get hc] at he
      simp only [Option.map_some, Option.some.injEq] at he
      subst he
      exact ⟨hc, (bitIs_iff (lookup_ment_start _) bit).1 hb⟩
    · simp [txnRows2, hc] at he
  · rintro ⟨hc, hb⟩
    exact ⟨_, by rw [List.getElem?_map, txnRows2_get hc]; rfl, (bitIs_iff (lookup_ment_start _) bit).2 hb⟩

theorem opsAt_txn2 {aw : Nat} {a b : BitVec 8} {s1 s2 n c : Nat} (hc : c < n) :
    task.OpsAt (2, 2, aw) ((txnRows2 a b s1 s2 n).map ment) c (a, b, ()) := by
  refine ⟨ment (c == 0, (c == s1 || c == s2) && c != 0, a, b), by rw [List.getElem?_map, txnRows2_get hc]; rfl, ?_⟩
  show SvState.lookup _ "A" = some (LVec.ofBitVec a) ∧ SvState.lookup _ "B" = some (LVec.ofBitVec b) ∧ True
  exact ⟨lookup_ment_A _, lookup_ment_B _, trivial⟩

theorem ops_unique2 {aw : Nat} {a b : BitVec 8} {s1 s2 n c : Nat} {x : task.Ops (2, 2, aw)}
    (h : task.OpsAt (2, 2, aw) ((txnRows2 a b s1 s2 n).map ment) c x) : x = (a, b, ()) := by
  obtain ⟨e, he, h1, h2, -⟩ := h
  rw [List.getElem?_map] at he
  by_cases hc : c < n
  · rw [txnRows2_get hc] at he
    simp only [Option.map_some, Option.some.injEq] at he
    subst he
    obtain ⟨xa, xb, xu⟩ := x
    cases xu
    have ha : LVec.ofBitVec a = LVec.ofBitVec xa := Option.some.inj ((lookup_ment_A _).symm.trans h1)
    have hb : LVec.ofBitVec b = LVec.ofBitVec xb := Option.some.inj ((lookup_ment_B _).symm.trans h2)
    rw [LVec.ofBitVec_inj.mp ha, LVec.ofBitVec_inj.mp hb]
  · simp [txnRows2, hc] at he

/-- **The rely holds** on the two-start rows at the horizon `n` for a trace that shows `done` = 1 at a snapshot
`c''` from the first start on and before the second (`Idle` at the second start). -/
theorem rely_txn2 {aw : Nat} {a b : BitVec 8} {s1 s2 n : Nat} (tr : List SvState) (hs : 0 < s1 ∧ s1 < s2)
    (hidle : ∃ c'', s1 ≤ c'' ∧ c'' < s2 ∧ TraceBit tr c'' task.done true) :
    task.Rely (2, 2, aw) ((txnRows2 a b s1 s2 n).map ment) tr 1 n := by
  have hst : ∀ c, StimBit ((txnRows2 a b s1 s2 n).map ment) c "start" true → (c = s1 ∨ c = s2) ∧ c ≠ 0 := by
    intro c h
    obtain ⟨-, h⟩ := stimBit_txn2_start.1 h
    simpa using h
  intro c h1 h2
  refine ⟨⟨(c == s1 || c == s2) && c != 0, stimBit_txn2_start.2 ⟨h2, rfl⟩⟩, ⟨_, opsAt_txn2 h2⟩, ?_, ?_⟩
  · intro hc s' h1' h2' hs'
    obtain ⟨hc, -⟩ := hst c hc
    obtain ⟨hs', -⟩ := hst s' hs'
    obtain ⟨c'', h3, h4, h5⟩ := hidle
    rcases hc with rfl | rfl <;> rcases hs' with rfl | rfl
    · omega
    · omega
    · exact ⟨c'', h3, h4, h5⟩
    · omega
  · intro s' x _ _ _ hx _
    rw [ops_unique2 hx]
    exact opsAt_txn2 h2

/-- **The hold refutation at the second start** `s2`, for every latency: the first transaction ends (a snapshot
`c''` in `[s1, s2)` shows `done` = 1, so the second start is `Idle`); after `s2` the snapshot `c'` shows `done` = 1
and the snapshot `c` does not show `done` = 1 with `C = A·B`. -/
theorem hold2_refuted {aw : Nat} {lat : Nat} {d : Design2} (st0 : SvState) (hpu : PowerUp d st0) (a b : BitVec 8)
    (s1 c'' s2 n c' c : Nat) (hs : 0 < s1 ∧ s1 ≤ c'' ∧ c'' < s2 ∧ s2 ≤ c' ∧ c' ≤ c ∧ c < n)
    (hks : KnownStim d ((txnRows2 a b s1 s2 n).map ment))
    (hrun : run2At d σ_src 64 st0 ((txnRows2 a b s1 s2 n).map ment) =
      .ok (trAt d st0 ((txnRows2 a b s1 s2 n).map ment)))
    (hd1 : (trAt d st0 ((txnRows2 a b s1 s2 n).map ment))[c'']?.map (bitOf · "done") = some true)
    (hdone : (trAt d st0 ((txnRows2 a b s1 s2 n).map ment))[c']?.map (bitOf · "done") = some true)
    (hbad : holdsAt (trAt d st0 ((txnRows2 a b s1 s2 n).map ment)) c (product 2 2 aw a b) = false) :
    ¬ task.FollowsPU (2, 2, aw) lat d := fun hf => by
  have tb : ∀ k, (trAt d st0 ((txnRows2 a b s1 s2 n).map ment))[k]?.map (bitOf · "done") = some true →
      TraceBit (trAt d st0 ((txnRows2 a b s1 s2 n).map ment)) k task.done true := by
    intro k hk
    cases ht : (trAt d st0 ((txnRows2 a b s1 s2 n).map ment))[k]? with
    | none => rw [ht] at hk; cases hk
    | some st =>
      rw [ht, Option.map_some, Option.some.injEq] at hk
      refine ⟨st, ht, ?_⟩
      unfold bitOf at hk
      exact beq_iff_eq.mp hk
  have hg := hf st0 hpu σ_src _ _ hks ⟨64, hrun⟩ 1 n
    ⟨by decide, ⟨_, by rw [List.getElem?_map, txnRows2_get (c := 0) (by omega)]; rfl,
      (bitIs_iff (lookup_ment_rst _) true).2 rfl⟩,
     fun k h1 h2 => ⟨_, by rw [List.getElem?_map, txnRows2_get h2]; rfl,
      (bitIs_iff (lookup_ment_rst _) false).2 (by simp; omega)⟩⟩
    (rely_txn2 _ ⟨by omega, by omega⟩ ⟨c'', by omega, by omega, tb c'' hd1⟩)
  have hss : StimBit ((txnRows2 a b s1 s2 n).map ment) s2 "start" true :=
    stimBit_txn2_start.2 ⟨by omega, by simp; omega⟩
  obtain ⟨-, hhold⟩ := hg.2.2 s2 (a, b, ()) (by omega) (by omega) hss (opsAt_txn2 (by omega))
  obtain ⟨st, hst, hb, hC, -⟩ := hhold c (by omega) (by omega) ⟨c', by omega, by omega, tb c' hdone⟩
    (fun s' h1 h2 hs' => by have := stimBit_txn2_start.1 hs'; simp at this; omega)
  unfold holdsAt at hbad
  rw [hst] at hbad
  simp only [Bool.and_eq_false_iff] at hbad
  rcases hbad with h | h
  · rw [bitOf_of_bitIs (n := "done") hb] at h; cases h
  · have : SvState.lookup st "C" = some (LVec.ofBitVec (product 2 2 aw a b)) := hC
    simp [this] at h

/-- Every hypothesis of `hold2_refuted` but `PowerUp`, decided at once. -/
def hold2Check (aw : Nat) (d : Design2) (st0 : SvState) (a b : BitVec 8) (s1 c'' s2 n c' c : Nat) : Bool :=
  decide (0 < s1 ∧ s1 ≤ c'' ∧ c'' < s2 ∧ s2 ≤ c' ∧ c' ≤ c ∧ c < n) &&
    decide (KnownStim d ((txnRows2 a b s1 s2 n).map ment)) &&
    decide (run2At d σ_src 64 st0 ((txnRows2 a b s1 s2 n).map ment) =
      .ok (trAt d st0 ((txnRows2 a b s1 s2 n).map ment))) &&
    ((trAt d st0 ((txnRows2 a b s1 s2 n).map ment))[c'']?.map (bitOf · "done") == some true) &&
    ((trAt d st0 ((txnRows2 a b s1 s2 n).map ment))[c']?.map (bitOf · "done") == some true) &&
    !holdsAt (trAt d st0 ((txnRows2 a b s1 s2 n).map ment)) c (product 2 2 aw a b)

theorem hold2_refuted_of_check {aw : Nat} {d : Design2} {st0 : SvState} (hpu : PowerUp d st0) {a b : BitVec 8}
    {s1 c'' s2 n c' c : Nat} (h : hold2Check aw d st0 a b s1 c'' s2 n c' c = true) (lat : Nat) :
    ¬ task.FollowsPU (2, 2, aw) lat d := by
  simp only [hold2Check, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨hs, hks⟩, hrun⟩, hd1⟩, hdone⟩, hbad⟩ := h
  exact hold2_refuted st0 hpu a b s1 c'' s2 n c' c hs hks hrun hd1 hdone hbad

/-! ## The refutations as one decided check each -/

/-- Every hypothesis of `hold_refuted` but `PowerUp`, decided at once. -/
def holdCheck (aw : Nat) (d : Design2) (st0 : SvState) (a b : BitVec 8) (s n c' c : Nat) : Bool :=
  decide (0 < s ∧ s ≤ c' ∧ c' ≤ c ∧ c < n) && decide (KnownStim d ((txnRows a b s n).map ment)) &&
    decide (run2At d σ_src 64 st0 ((txnRows a b s n).map ment) = .ok (trAt d st0 ((txnRows a b s n).map ment))) &&
    ((trAt d st0 ((txnRows a b s n).map ment))[c']?.map (bitOf · "done") == some true) &&
    !holdsAt (trAt d st0 ((txnRows a b s n).map ment)) c (product 2 2 aw a b)

theorem hold_refuted_of_check {aw : Nat} {d : Design2} {st0 : SvState} (hpu : PowerUp d st0) {a b : BitVec 8}
    {s n c' c : Nat} (h : holdCheck aw d st0 a b s n c' c = true) (lat : Nat) : ¬ task.FollowsPU (2, 2, aw) lat d := by
  simp only [holdCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨hs, hks⟩, hrun⟩, hdone⟩, hbad⟩ := h
  exact hold_refuted st0 hpu a b s n c' c hs hks hrun hdone hbad

/-- Every hypothesis of `never_refuted` but `PowerUp`, decided at once. -/
def neverCheck (d : Design2) (st0 : SvState) (a b : BitVec 8) (s n : Nat) : Bool :=
  decide (0 < s ∧ s < n) && !(d.processes.toList.any Process2.hasQualifiedCase) &&
    decide (KnownStim d ((txnRows a b s n).map ment)) && decide (KnownEntry d (ment (false, false, a, b))) &&
    decide (run2At d σ_src 64 st0 ((txnRows a b s n).map ment) = .ok (trAt d st0 ((txnRows a b s n).map ment))) &&
    d.ffOnlyProfileB &&
    d.processes.toList.all (keeps 64 (applyInputs2 d (ment (false, false, a, b))
      (lastOr st0 (trAt d st0 ((txnRows a b s n).map ment))))) &&
    decide (((applyInputs2 d (ment (false, false, a, b)) (lastOr st0 (trAt d st0 ((txnRows a b s n).map ment)))).map
      Prod.fst).Nodup) &&
    decide (clockStep d 64 (applyInputs2 d (ment (false, false, a, b))
      (lastOr st0 (trAt d st0 ((txnRows a b s n).map ment)))) d.edgeIndices =
        lastOr st0 (trAt d st0 ((txnRows a b s n).map ment))) &&
    !bitOf (lastOr st0 (trAt d st0 ((txnRows a b s n).map ment))) "done" &&
    (List.range n).all fun c => decide (c < s) ||
      ((trAt d st0 ((txnRows a b s n).map ment))[c]?.map (bitOf · "done") == some false)

theorem never_refuted_of_check {aw : Nat} {d : Design2} {st0 : SvState} (hpu : PowerUp d st0) {a b : BitVec 8}
    {s n : Nat} (h : neverCheck d st0 a b s n = true) (lat : Nat) : ¬ task.FollowsPU (2, 2, aw) lat d := by
  simp only [neverCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.not_eq_true', List.all_eq_true,
    List.mem_range, Bool.or_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hs, hq⟩, hks⟩, hki⟩, hrun⟩, hp⟩, hk⟩, hnd⟩, hfix⟩, hrest⟩, hnone⟩ := h
  refine never_refuted st0 hpu a b s n hs hq hks hki hrun (cycleStep2_fixed hp (List.all_eq_true.mpr hk) hnd hfix) hrest
    (fun c hc hsc => ?_)
  rcases hnone c hc with h | h
  · omega
  · exact h

/-- Every hypothesis of `early_refuted` but `PowerUp`, decided at once. -/
def earlyCheck (d : Design2) (st0 : SvState) (a b : BitVec 8) (n c : Nat) : Bool :=
  decide (1 ≤ c ∧ c < n) && decide (KnownStim d ((txnRows a b 0 n).map ment)) &&
    decide (run2At d σ_src 64 st0 ((txnRows a b 0 n).map ment) = .ok (trAt d st0 ((txnRows a b 0 n).map ment))) &&
    ((trAt d st0 ((txnRows a b 0 n).map ment))[c]?.map (bitOf · "done") == some true)

theorem early_refuted_of_check {aw : Nat} {d : Design2} {st0 : SvState} (hpu : PowerUp d st0) {a b : BitVec 8}
    {n c : Nat} (h : earlyCheck d st0 a b n c = true) (lat : Nat) : ¬ task.FollowsPU (2, 2, aw) lat d := by
  simp only [earlyCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨hc, hks⟩, hrun⟩, hdone⟩ := h
  exact early_refuted st0 hpu a b n c hc hks hrun hdone

/-- `(2, 2, aw)` is in range for `aw ≥ 1`. -/
theorem p22_inRange (aw : Nat) (h : 1 ≤ aw) (h' : aw < 2 ^ 27) : task.inRange (2, 2, aw) := by
  simp only [task]; omega

/-- The refutation at `(2, 2, aw)` of every family whose instance there is `d`, for every latency function. -/
theorem refuted_of_sat {aw : Nat} (haw : 1 ≤ aw ∧ aw < 2 ^ 27) {d : Design2}
    (h : ∀ lat, ¬ task.SatisfiedAtV2 (2, 2, aw) lat d) (sem : Nat → Nat → Nat → Design2)
    (lat : Nat → Nat → Nat → Nat) (hd : sem 2 2 aw = d) : ¬ Statement sem lat := fun hs => by
  have hf : task.SatisfiedAtV2 (2, 2, aw) (lat 2 2 aw) (sem 2 2 aw) := hs (2, 2, aw) (p22_inRange aw haw.1 haw.2)
  rw [hd] at hf
  exact h _ hf

/-- The same from `¬ FollowsPU` (rule 2's claims). -/
theorem refuted_of {aw : Nat} (haw : 1 ≤ aw ∧ aw < 2 ^ 27) {d : Design2} (h : ∀ lat, ¬ task.FollowsPU (2, 2, aw) lat d)
    (sem : Nat → Nat → Nat → Design2) (lat : Nat → Nat → Nat → Nat) (hd : sem 2 2 aw = d) : ¬ Statement sem lat :=
  refuted_of_sat haw (fun lat hs => h lat hs.2.2.2.1) sem lat hd

/-- A 2×2 matrix of 2-bit entries, row-major (`[[m00, m01], [m10, m11]]`, each entry's two's-complement code), as
the flat operand. -/
def mat (m00 m01 m10 m11 : Nat) : BitVec 8 := BitVec.ofNat 8 (m00 + 4 * m01 + 16 * m10 + 64 * m11)

/-- `A = [[-1, 1], [-2, 1]]`. -/
def matA : BitVec 8 := mat 3 1 2 1
/-- `B = [[1, -1], [-2, 1]]` (`A·B = [[-3, 2], [-4, 3]]`). -/
def matB : BitVec 8 := mat 1 3 2 1
/-- `[[-2, -2], [-2, -2]]` (its square is `[[8, 8], [8, 8]]`, outside the signed 4-bit range). -/
def matM : BitVec 8 := mat 2 2 2 2
/-- `[[-1, 1], [1, 1]]`. -/
def matP : BitVec 8 := mat 3 1 1 1
/-- `[[1, 1], [1, 1]]` (`matP · matO = [[0, 0], [2, 2]]`: one negative product in each entry of row 0). -/
def matO : BitVec 8 := mat 1 1 1 1

theorem aw4 : 1 ≤ 4 ∧ 4 < 2 ^ 27 := by decide
theorem aw5 : 1 ≤ 5 ∧ 5 < 2 ^ 27 := by decide

/-! ## The attacks refuted, for every latency function -/

/-- **`done_early` is rejected**: `done` shows 1 at snapshot 2, one step before the last product is added: `C` is
not `A·B` there. -/
theorem done_early_refuted (sem : Nat → Nat → Nat → Design2) (lat : Nat → Nat → Nat → Nat)
    (hd : sem 2 2 4 = doneEarlyD) : ¬ Statement sem lat :=
  refuted_of aw4 (hold_refuted_of_check (powerUp_zeros _) (a := matA) (b := matB) (s := 1) (n := 6) (c' := 2) (c := 2)
    (by decide +kernel)) sem lat hd

/-- **`off_by_one_k` is rejected**: one step short, `done` shows 1 at snapshot 2 with a partial `C`. -/
theorem off_by_one_k_refuted (sem : Nat → Nat → Nat → Design2) (lat : Nat → Nat → Nat → Nat)
    (hd : sem 2 2 4 = offByOneKD) : ¬ Statement sem lat :=
  refuted_of aw4 (hold_refuted_of_check (powerUp_zeros _) (a := matA) (b := matB) (s := 1) (n := 6) (c' := 2) (c := 2)
    (by decide +kernel)) sem lat hd

/-- **`unsigned_product` is rejected**: with negative entries, the zero-extended products are wrong at `done`. -/
theorem unsigned_product_refuted (sem : Nat → Nat → Nat → Design2) (lat : Nat → Nat → Nat → Nat)
    (hd : sem 2 2 4 = unsignedProductD) : ¬ Statement sem lat :=
  refuted_of aw4 (hold_refuted_of_check (powerUp_zeros _) (a := matA) (b := matB) (s := 1) (n := 6) (c' := 3) (c := 3)
    (by decide +kernel)) sem lat hd

/-- **`acc_2w` is rejected** at `AccW = 5`: `[[-2, -2], [-2, -2]]` squared is 8 in every entry, which the 4-bit
accumulator wraps to -8 (`C` shows 24, not 8). -/
theorem acc_2w_refuted (sem : Nat → Nat → Nat → Design2) (lat : Nat → Nat → Nat → Nat)
    (hd : sem 2 2 5 = acc2wD) : ¬ Statement sem lat :=
  refuted_of aw5 (hold_refuted_of_check (powerUp_zeros _) (a := matM) (b := matM) (s := 1) (n := 6) (c' := 3) (c := 3)
    (by decide +kernel)) sem lat hd

/-- **`missing_sign_ext` is rejected** at `AccW = 5`: in row 0 of `[[-1, 1], [1, 1]] · [[1, 1], [1, 1]]` one product
is -1, zero-extended from 4 bits to 15, so `C[0][j]` is 16, not 0. -/
theorem missing_sign_ext_refuted (sem : Nat → Nat → Nat → Design2) (lat : Nat → Nat → Nat → Nat)
    (hd : sem 2 2 5 = missingSignExtD) : ¬ Statement sem lat :=
  refuted_of aw5 (hold_refuted_of_check (powerUp_zeros _) (a := matP) (b := matO) (s := 1) (n := 6) (c' := 3) (c := 3)
    (by decide +kernel)) sem lat hd

/-- **`no_clear_on_start` is rejected** by two transactions on the same operands: the first ends with `done` at
snapshot 3 and `C = A·B`; the second (started at entry 4, `Idle`) adds onto it, and at its `done` (snapshot 6) `C`
is `2·A·B`. -/
theorem no_clear_on_start_refuted (sem : Nat → Nat → Nat → Design2) (lat : Nat → Nat → Nat → Nat)
    (hd : sem 2 2 4 = noClearOnStartD) : ¬ Statement sem lat :=
  refuted_of aw4 (hold2_refuted_of_check (powerUp_zeros _) (a := matA) (b := matB) (s1 := 1) (c'' := 3) (s2 := 4)
    (n := 8) (c' := 6) (c := 6) (by decide +kernel)) sem lat hd

/-! ## No asynchronous reset (decided 2026-11-09) -/

/-- `async_reset` fails the clock discipline: its control process has the asynchronous reset `rst`, and
`TxTask.Disciplined` is `ClockedBy clk none`. -/
theorem async_reset_not_disciplined : ¬ task.Disciplined asyncResetD := by
  rintro ⟨-, hp⟩
  have h := (hp ctrlAsync (by simp [asyncResetD, mWith])).2.1 "rst" rfl
  cases h

/-- **`async_reset` is rejected**, for every latency function, by the statement itself (the clocked source gate
refuses it earlier, at `source`). -/
theorem async_reset_refuted (sem : Nat → Nat → Nat → Design2) (lat : Nat → Nat → Nat → Nat)
    (hd : sem 2 2 4 = asyncResetD) : ¬ Statement sem lat :=
  refuted_of_sat aw4 (fun _ hs => async_reset_not_disciplined hs.2.1.1) sem lat hd

/-! ## The reference passes the same runs (an executable reading, not a proof) -/

#guard holdsAt (trAt (refD 4) (zeros (refD 4)) ((txnRows2 matA matB 1 4 8).map ment)) 6 (product 2 2 4 matA matB)

#guard holdsAt (trAt (refD 4) (zeros (refD 4)) ((txnRows matA matB 1 6).map ment)) 3 (product 2 2 4 matA matB)
#guard holdsAt (trAt (refD 5) (zeros (refD 5)) ((txnRows matM matM 1 6).map ment)) 3 (product 2 2 5 matM matM)
#guard holdsAt (trAt (refD 5) (zeros (refD 5)) ((txnRows matP matO 1 6).map ment)) 3 (product 2 2 5 matP matO)

#print axioms hold_refuted
#print axioms never_refuted
#print axioms early_refuted
#print axioms done_early_refuted
#print axioms off_by_one_k_refuted
#print axioms unsigned_product_refuted
#print axioms acc_2w_refuted
#print axioms missing_sign_ext_refuted
#print axioms no_clear_on_start_refuted
#print axioms async_reset_refuted

end SvGolf.Tasks.Matmul.Refute
