import SvGolf.Clocked

/-!
# Tests of `SvGolf.Clocked`: every lemma at two sizes

Each lemma of `SvGolf/Clocked.lean` applied at two instances of different size (two and three registers, families
of two and three entries, widths 4 and 8, …), and where the instance is closed, checked against a direct evaluation
(`decide`). Built with the `tests` library (`tests.lean`).
-/

namespace SvGolfTests.Clocked

open LeanModels.Sv SvGolf

/-! ## 1. The commit, register by register -/

/-- Positional states with one input and two, or three, registers. -/
def S2 (ck a b : LVec) : SvState := [("clk", ck), ("a", a), ("b", b)]
def S3 (ck a b c : LVec) : SvState := [("clk", ck), ("a", a), ("b", b), ("c", c)]

example (q : NbaQueue2) (ck a b : LVec) (h : ∀ u ∈ q, u.1 ∈ ["a", "b"]) :
    commitNba2 (S2 ck a b) q = S2 ck (nbaFold "a" q a) (nbaFold "b" q b) := by
  rw [commitNba2_eq_map_of_names (by simp [S2]) h]; simp [S2]

example (q : NbaQueue2) (ck a b c : LVec) (h : ∀ u ∈ q, u.1 ∈ ["a", "b", "c"]) :
    commitNba2 (S3 ck a b c) q = S3 ck (nbaFold "a" q a) (nbaFold "b" q b) (nbaFold "c" q c) := by
  rw [commitNba2_eq_map_of_names (by simp [S3]) h]; simp [S3]

example (q : NbaQueue2) (ck a b : LVec) :
    commitNba2 (S2 ck a b) q = S2 (nbaFold "clk" q ck) (nbaFold "a" q a) (nbaFold "b" q b) := by
  rw [commitNba2_eq_map q _ (by simp [S2])]; rfl

example (q : NbaQueue2) (ck a b c : LVec) :
    commitNba2 (S3 ck a b c) q = S3 (nbaFold "clk" q ck) (nbaFold "a" q a) (nbaFold "b" q b) (nbaFold "c" q c) := by
  rw [commitNba2_eq_map q _ (by simp [S3])]; rfl

/-- Closed instances, checked against the commit itself. -/
example : commitNba2 (S2 (LVec.ofNat 1 0) (LVec.ofNat 4 3) (LVec.ofNat 4 5))
      [("a", 0, LVec.ofNat 2 2), ("b", 2, LVec.ofNat 2 3)] =
    S2 (LVec.ofNat 1 0) (LVec.ofNat 4 2) (LVec.ofNat 4 13) := by
  rw [commitNba2_eq_map_of_names (regs := ["a", "b"]) (by decide) (by decide)]; decide

example : commitNba2 (S3 (LVec.ofNat 1 0) (LVec.ofNat 8 3) (LVec.ofNat 8 5) (LVec.ofNat 8 7))
      [("c", 4, LVec.ofNat 4 15), ("a", 0, LVec.ofNat 4 0), ("c", 0, LVec.ofNat 1 0)] =
    S3 (LVec.ofNat 1 0) (LVec.ofNat 8 0) (LVec.ofNat 8 5) (LVec.ofNat 8 246) := by
  rw [commitNba2_eq_map_of_names (regs := ["a", "b", "c"]) (by decide) (by decide)]; decide

example (x : LVec) : nbaFold "a" [] x = x := nbaFold_nil "a" x
example (q : NbaQueue2) (x v : LVec) : nbaFold "a" (("a", 3, v) :: q) x = nbaFold "a" q (x.insertAt 3 v) :=
  nbaFold_cons_self "a" 3 v q x
example (q : NbaQueue2) (x v : LVec) : nbaFold "a" (("b", 3, v) :: q) x = nbaFold "a" q x :=
  nbaFold_cons_ne (by decide) 3 v q x
example (q : NbaQueue2) (x v : LVec) : nbaFold "data" (("tok", 7, v) :: q) x = nbaFold "data" q x :=
  nbaFold_cons_ne (by decide) 7 v q x

example (ck a b v : LVec) : nbaStep (S2 ck a b) ("b", 2, v) = S2 ck a (b.insertAt 2 v) := by
  rw [nbaStep_eq_map _ _ (by simp [S2])]; simp [S2]
example (ck a b c v : LVec) : nbaStep (S3 ck a b c) ("c", 4, v) = S3 ck a b (c.insertAt 4 v) := by
  rw [nbaStep_eq_map _ _ (by simp [S3])]; simp [S3]

example (x v w : LVec) : nbaFold "a" [("b", 0, w), ("a", 1, v)] x = x.insertAt 1 v := by simp
example (x v w : LVec) : nbaFold "a" [("a", 0, w), ("b", 1, v), ("a", 2, v)] x = (x.insertAt 0 w).insertAt 2 v := by
  simp

example (u : String × Nat × LVec) (q : NbaQueue2) (x : LVec) :
    nbaFold "a" (u :: q) x = nbaFold "a" q (if u.1 = "a" then x.insertAt u.2.1 u.2.2 else x) := nbaFold_cons ..

example (c : Bool) (v w x : LVec) :
    nbaFold "a" (if c = true then [("a", 0, v)] else [("b", 0, w)]) x = if c = true then x.insertAt 0 v else x := by
  rw [nbaFold_ite]; simp
example (c : Bool) (v w x : LVec) :
    nbaFold "b" (if c = true then [("a", 0, v), ("a", 1, v)] else [("b", 0, w)]) x =
      if c = true then x else x.insertAt 0 w := by
  rw [nbaFold_ite]; simp

example (v w x : LVec) : nbaFold "clk" [("a", 0, v), ("b", 1, w)] x = x :=
  nbaFold_of_forall_ne (by simp) x
example (v w x : LVec) : nbaFold "clk" [("a", 0, v), ("b", 1, w), ("c", 2, v)] x = x :=
  nbaFold_of_forall_ne (by simp) x

example (v w x : LVec) : nbaFold "clk" [("a", 0, v), ("b", 1, w)] x = x :=
  nbaFold_of_names (ns := ["a", "b"]) (by simp) (by decide) x
example (v w x : LVec) : nbaFold "clk" [("a", 0, v), ("b", 1, w), ("c", 2, v)] x = x :=
  nbaFold_of_names (ns := ["a", "b", "c"]) (by simp) (by decide) x

example (v w : LVec) : ∀ u ∈ [("a", 0, v), ("b", 1, w)], u.1 ∈ ["a", "b"] := nbaNames_of_all (by simp)
example (v w : LVec) : ∀ u ∈ [("a", 0, v), ("b", 1, w), ("c", 2, v)], u.1 ∈ ["a", "b", "c"] :=
  nbaNames_of_all (by simp)

example (v w : LVec) : ∀ u ∈ [("a", 0, v)] ++ [("b", 1, w)], u.1 ∈ ["a", "b"] :=
  nbaNames_append (by simp) (by simp)
example (v w : LVec) : ∀ u ∈ [("a", 0, v)] ++ ([("b", 1, w)] ++ [("c", 2, v)]), u.1 ∈ ["a", "b", "c"] :=
  nbaNames_append (by simp) (nbaNames_append (by simp) (by simp))

example (g : Nat → LVec) : ∀ u ∈ (List.range 2).flatMap (fun r => [("C", r * 4, g r)]), u.1 ∈ ["C"] :=
  nbaNames_flatMap fun _ => by simp
example (g : Nat → LVec) : ∀ u ∈ (List.range 3).flatMap (fun r => [("C", r * 8, g r), ("D", r, g r)]),
    u.1 ∈ ["C", "D"] :=
  nbaNames_flatMap fun _ => by simp

example (g : Nat → LVec) (x : LVec) :
    nbaFold "C" ((List.range 2).map fun r => ("C", r * 4, g r)) x = LVec.insertEntries 4 g 2 x :=
  nbaFold_map_insertEntries ..
example (g : Nat → LVec) (x : LVec) :
    nbaFold "C" ((List.range 3).map fun r => ("C", r * 8, g r)) x = LVec.insertEntries 8 g 3 x :=
  nbaFold_map_insertEntries ..

example : (List.range 2).flatMap (fun j => [j * 5]) = (List.range 2).map (· * 5) :=
  flatMap_range_singleton fun _ _ => rfl
example : (List.range 3).flatMap (fun j => [j * 5]) = (List.range 3).map (· * 5) :=
  flatMap_range_singleton fun _ _ => rfl

example : ((List.range 2).flatMap fun i => (List.range 2).flatMap fun j => [i * 2 + j]) = (List.range 4).map id :=
  flatMap_range_rowMajor id fun _ _ _ _ => rfl
example : ((List.range 2).flatMap fun i => (List.range 3).flatMap fun j => [(i * 3 + j) * 4]) =
    (List.range 6).map (· * 4) :=
  flatMap_range_rowMajor (· * 4) fun _ _ _ _ => rfl

/-! ## 2. Register families, window by window -/

example (g g' : Nat → LVec) (c : LVec) (h : ∀ r, r < 2 → g r = g' r) :
    LVec.insertEntries 4 g 2 c = LVec.insertEntries 4 g' 2 c := LVec.insertEntries_congr c 2 h
example (g g' : Nat → LVec) (c : LVec) (h : ∀ r, r < 3 → g r = g' r) :
    LVec.insertEntries 8 g 3 c = LVec.insertEntries 8 g' 3 c := LVec.insertEntries_congr c 3 h

example (g : Nat → LVec) (hg : ∀ k, (g k).width = 4) (c : LVec) (hc : c.width = 8) :
    (LVec.insertEntries 4 g 2 c).extract (1 * 4) 4 = g 1 :=
  LVec.extract_insertEntries hg c 2 (by omega) 1 (by decide)
example (g : Nat → LVec) (hg : ∀ k, (g k).width = 8) (c : LVec) (hc : c.width = 24) :
    (LVec.insertEntries 8 g 3 c).extract (2 * 8) 8 = g 2 :=
  LVec.extract_insertEntries hg c 3 (by omega) 2 (by decide)

example (v : LVec) : LVec.insertEntries 4 (fun r => v.extract (r * 4) 4) 2 v = v := LVec.insertEntries_extract_self ..
example (v : LVec) : LVec.insertEntries 8 (fun r => v.extract (r * 8) 8) 3 v = v := LVec.insertEntries_extract_self ..

example : LVec.ofBitVec 0xB4#8 = LVec.ofBitVec (packBV 4 2 fun r => if r = 0 then 0x4#4 else 0xB#4) :=
  LVec.eq_ofBitVec_packBV (by decide) fun r hr => match r, hr with
    | 0, _ => by decide
    | 1, _ => by decide
example : LVec.ofBitVec 0x1B#6 = LVec.ofBitVec (packBV 2 3 fun r => if r = 0 then 3#2 else if r = 1 then 2#2 else 1#2) :=
  LVec.eq_ofBitVec_packBV (by decide) fun r hr => match r, hr with
    | 0, _ => by decide
    | 1, _ => by decide
    | 2, _ => by decide

/-! ## 3. Disjoint windows -/

example (a b : Option (Nat × Nat)) : DrvWin.overlaps ("C", a) ("k", b) = false := DrvWin.overlaps_of_ne (by decide) a b
example (a b : Option (Nat × Nat)) : DrvWin.overlaps ("busy", a) ("done", b) = false :=
  DrvWin.overlaps_of_ne (by decide) a b

example (E : Nat) : DrvWin.overlaps ("C", some (0 * E, E)) ("C", some (1 * E, E)) = false :=
  DrvWin.overlaps_rowMajor (by decide)
example (E : Nat) : DrvWin.overlaps ("C", some (2 * E, E)) ("C", some (1 * E, E)) = false :=
  DrvWin.overlaps_rowMajor (by decide)
example : DrvWin.overlaps ("C", some (2 * 4, 4)) ("C", some (1 * 4, 4)) = false := by decide

/-- One write of a constant to a window of `n`. -/
def wP (n : String) (lo w : Nat) : Process2 := .alwaysFF "clk" (.nbaAssign (.slice n lo w) (.lit (LVec.ofNat w 0)))

example : ProcDisj (wP "C" (0 * 4) 4) (wP "C" (1 * 4) 4) := ProcDisj.of_units (by decide) rfl rfl
example : ProcDisj (wP "C" (2 * 8) 8) (wP "C" (0 * 8) 8) := ProcDisj.of_units (by decide) rfl rfl

example : ProcDisj (wP "C" 0 4) (wP "k" 0 4) := ProcDisj.of_names (n := "C") (n' := "k") (by decide) (by simp [wP, Process2.procWins,
  Stmt2.drvWins, Lhs2.drvWins]) (by simp [wP, Process2.procWins, Stmt2.drvWins, Lhs2.drvWins])
example : ProcDisj (wP "ps" 8 8) (wP "dl" 8 8) := ProcDisj.of_names (n := "ps") (n' := "dl") (by decide) (by simp [wP, Process2.procWins,
  Stmt2.drvWins, Lhs2.drvWins]) (by simp [wP, Process2.procWins, Stmt2.drvWins, Lhs2.drvWins])

example : ProcDisj (wP "C" 0 4) (wP "k" 0 4) := ProcDisj.of_nameLists (ns := ["C", "D"]) (ms := ["k"])
  (by simp [wP, Process2.procWins, Stmt2.drvWins, Lhs2.drvWins]) (by simp [wP, Process2.procWins, Stmt2.drvWins,
    Lhs2.drvWins]) (by decide)
example : ProcDisj (wP "ps" 8 8) (wP "dl" 0 8) := ProcDisj.of_nameLists (ns := ["ps"]) (ms := ["dl", "C", "k"])
  (by simp [wP, Process2.procWins, Stmt2.drvWins, Lhs2.drvWins]) (by simp [wP, Process2.procWins, Stmt2.drvWins,
    Lhs2.drvWins]) (by decide)

example : ∀ p ∈ (List.range 2).map (fun r => wP "C" (r * 4) 4), ∀ q ∈ (List.range 2).map (fun r => wP "k" r 1),
    ProcDisj p q :=
  ProcDisj.of_lists (n := "C") (n' := "k") (by decide) (by simp [wP, Process2.procWins, Stmt2.drvWins, Lhs2.drvWins])
    (by simp [wP, Process2.procWins, Stmt2.drvWins, Lhs2.drvWins])
example : ∀ p ∈ (List.range 3).map (fun r => wP "C" (r * 8) 8), ∀ q ∈ (List.range 3).map (fun r => wP "k" r 1),
    ProcDisj p q :=
  ProcDisj.of_lists (n := "C") (n' := "k") (by decide) (by simp [wP, Process2.procWins, Stmt2.drvWins, Lhs2.drvWins])
    (by simp [wP, Process2.procWins, Stmt2.drvWins, Lhs2.drvWins])

example : 1 * 3 + 2 < 2 * 3 + 0 := rowMajor_lt (by decide) (by decide)
example (N : Nat) (hN : 4 < N) : 1 * N + 4 < 2 * N + 0 := rowMajor_lt hN (by decide)
example : 1 * 3 + 2 ≠ 2 * 3 + 2 := rowMajor_ne (by decide) (by decide) (.inl (by decide))
example (N : Nat) (hN : 4 < N) : 1 * N + 4 ≠ 1 * N + 3 := rowMajor_ne hN (by omega) (.inr (by decide))
example : (2 * 3 + 2) / 3 = 2 := rowMajor_div (by decide)
example (N i : Nat) (hN : 4 < N) : (i * N + 4) / N = i := rowMajor_div hN

example : ((List.range 4).map (· * 3)).Pairwise (· < ·) := pairwise_map_range fun _ _ h _ => by omega
example : ((List.range 5).map (· + 7)).Pairwise (· ≠ ·) := pairwise_map_range fun _ _ h _ => by omega

example : ((List.range 2).flatMap fun k => (List.range 2).map fun j => k * 2 + j).Pairwise (· < ·) :=
  pairwise_rowMajor fun _ _ _ _ _ _ _ _ h => h
example : ((List.range 2).flatMap fun k => (List.range 3).map fun j => wP "C" ((k * 3 + j) * 4) 4).Pairwise ProcDisj :=
  pairwise_rowMajor fun _ _ _ _ _ _ _ _ h => ProcDisj.of_units (Nat.ne_of_lt h) rfl rfl

/-! ## 4. Generate loops -/

/-- A process template (its instantiation, whatever it is, is the `f` of the lemmas). -/
def tmpl : PProcess := .alwaysFF "clk" (.block [])

/-- A scope with `N = n`. -/
def envN (n : Int) : IEnv := { vals := [("N", n)] }

/-- `for (i = 0; i < N; i++)` over `tmpl`. -/
def loop1 : GenItem :=
  .genFor (some "g") "i" (.int 0) (.binary .slt (.genvarRef "i") (.paramRef "N" none)) (.unary .inc (.genvarRef "i"))
    (some 4) ([tmpl].map GenItem.process)

/-- `for (i = 0; i < N; i++) for (j = 0; j < N; j++)` over `tmpl`. -/
def loop2 : GenItem :=
  .genFor (some "g") "i" (.int 0) (.binary .slt (.genvarRef "i") (.paramRef "N" none)) (.unary .inc (.genvarRef "i"))
    (some 4) [.genFor (some "h") "j" (.int 0) (.binary .slt (.genvarRef "j") (.paramRef "N" none))
      (.unary .inc (.genvarRef "j")) (some 4) ([tmpl].map GenItem.process)]

example : loop1.expand2 (envN 2) [] 8 = .ok ((List.range 2).map fun v : Nat => instProcess2 ((envN 2).bindVal "i" v) [] tmpl) :=
  GenItem.expand2_param_map (fun _ => rfl) (by decide) fun _ _ => rfl
example : loop1.expand2 (envN 3) [] 8 = .ok ((List.range 3).map fun v : Nat => instProcess2 ((envN 3).bindVal "i" v) [] tmpl) :=
  GenItem.expand2_param_map (fun _ => rfl) (by decide) fun _ _ => rfl

example : loop2.expand2 (envN 2) [] 8 = .ok ((List.range 2).flatMap fun v : Nat => (List.range 2).map fun w : Nat =>
    instProcess2 (((envN 2).bindVal "i" v).bindVal "j" w) [] tmpl) :=
  GenItem.expand2_param_map₂ (fun _ => rfl) (fun _ _ => rfl) (by decide) (by decide) fun _ _ _ _ => rfl
example : loop2.expand2 (envN 3) [] 8 = .ok ((List.range 3).flatMap fun v : Nat => (List.range 3).map fun w : Nat =>
    instProcess2 (((envN 3).bindVal "i" v).bindVal "j" w) [] tmpl) :=
  GenItem.expand2_param_map₂ (fun _ => rfl) (fun _ _ => rfl) (by decide) (by decide) fun _ _ _ _ => rfl

/-- `for (i = 0; i < N - 1; i++)` over `tmpl`: a bound that is not a parameter. -/
def loopM : GenItem :=
  .genFor (some "g") "i" (.int 0) (.binary .slt (.genvarRef "i") (.binary (.m0 .sub) (.paramRef "N" none) (.int 1)))
    (.unary .inc (.genvarRef "i")) (some 4) ([tmpl].map GenItem.process)

theorem loopM_expand (n : Nat) (hn : 1 ≤ n) : loopM.expand2 (envN n) [] 8 =
    .ok ((List.range (n - 1)).map fun v : Nat => instProcess2 ((envN n).bindVal "i" v) [] tmpl) ∨ 9 ≤ n := by
  by_cases h9 : 9 ≤ n
  · exact .inr h9
  exact .inl (GenItem.expand2_range_map (fun _ => isInt_binary_of rfl (isInt_paramRef_of rfl) rfl)
    (fun _ => by rw [Int.ofNat_sub hn]; exact evalInt_sub_of (isInt_paramRef_of rfl) rfl (evalInt_paramRef_of rfl) rfl)
    (by omega) fun _ _ => rfl)

example : loopM.expand2 (envN 2) [] 8 = .ok ((List.range 1).map fun v : Nat => instProcess2 ((envN 2).bindVal "i" v) [] tmpl) :=
  (loopM_expand 2 (by decide)).resolve_right (by decide)
example : loopM.expand2 (envN 3) [] 8 = .ok ((List.range 2).map fun v : Nat => instProcess2 ((envN 3).bindVal "i" v) [] tmpl) :=
  (loopM_expand 3 (by decide)).resolve_right (by decide)

example : loop2.expand2 (envN 2) [] 8 = .ok ((List.range 2).flatMap fun v : Nat =>
    (List.range 2).map fun w : Nat => instProcess2 (((envN 2).bindVal "i" v).bindVal "j" w) [] tmpl) :=
  GenItem.expand2_range_flatMap (fun _ => isInt_paramRef_of rfl) (fun _ => evalInt_paramRef_of rfl) (by decide)
    fun _ _ => expandList2_singleton_ok (GenItem.expand2_param_map (fun _ => rfl) (by decide) fun _ _ => rfl)
example : loop2.expand2 (envN 3) [] 8 = .ok ((List.range 3).flatMap fun v : Nat =>
    (List.range 3).map fun w : Nat => instProcess2 (((envN 3).bindVal "i" v).bindVal "j" w) [] tmpl) :=
  GenItem.expand2_range_flatMap (fun _ => isInt_paramRef_of rfl) (fun _ => evalInt_paramRef_of rfl) (by decide)
    fun _ _ => expandList2_singleton_ok (GenItem.expand2_param_map (fun _ => rfl) (by decide) fun _ _ => rfl)
example : loop2.expand2 (envN 2) [] 8 = .ok ((List.range 2).flatMap fun v : Nat =>
    (List.range 2).map fun w : Nat => instProcess2 (((envN 2).bindVal "i" v).bindVal "j" w) [] tmpl) :=
  GenItem.expand2_range_map₂ (fun _ => isInt_paramRef_of rfl) (fun _ => evalInt_paramRef_of rfl)
    (fun _ _ => isInt_paramRef_of rfl) (fun _ _ => evalInt_paramRef_of rfl) (by decide) (by decide) fun _ _ _ _ => rfl
example : loop2.expand2 (envN 3) [] 8 = .ok ((List.range 3).flatMap fun v : Nat =>
    (List.range 3).map fun w : Nat => instProcess2 (((envN 3).bindVal "i" v).bindVal "j" w) [] tmpl) :=
  GenItem.expand2_range_map₂ (fun _ => isInt_paramRef_of rfl) (fun _ => evalInt_paramRef_of rfl)
    (fun _ _ => isInt_paramRef_of rfl) (fun _ _ => evalInt_paramRef_of rfl) (by decide) (by decide) fun _ _ _ _ => rfl

/-! ## 5. Power-up -/

/-- Two and four declarations, one of them an input. -/
def d2 (n : Nat) : Design2 where
  name := "t2"
  decls := [{ name := "clk", width := 1, isInput := true }, { name := "q", width := n }].toArray
  processes := #[]

def d4 (n : Nat) : Design2 where
  name := "t4"
  decls := [{ name := "clk", width := 1, isInput := true }, { name := "a", width := n },
    { name := "b", width := 2 * n }, { name := "c", width := 32 }].toArray
  processes := #[]

example (st : SvState) (h : PowerUp (d2 2) st) : ∃ ck q, st = [("clk", ck), ("q", q)] ∧ q.width = 2 := by
  powerUp_cases h with ck q
  exact ⟨ck, q, rfl, w_q⟩

example (n : Nat) (st : SvState) (h : PowerUp (d4 n) st) :
    ∃ ck a b c, st = [("clk", ck), ("a", a), ("b", b), ("c", c)] ∧ a.width = n ∧ b.width = 2 * n ∧ c.width = 32 := by
  powerUp_cases h with ck a b c
  exact ⟨ck, a, b, c, rfl, w_a, w_b, w_c⟩

/-! ## 6. Values -/

example : (LVec.ofBitVec 5#4).shl (LVec.ofBitVec 1#2) = LVec.ofBitVec 10#4 := by rw [LVec.shl_ofBitVec]; decide
example : (LVec.ofBitVec 0x81#8).shl (LVec.ofBitVec 3#3) = LVec.ofBitVec 0x08#8 := by rw [LVec.shl_ofBitVec]; decide
example (x : BitVec 8) (k : BitVec 32) : (LVec.ofBitVec x).shl (LVec.ofBitVec k) = LVec.ofBitVec (x <<< k.toNat) := by
  simp

example : (⟨#[.l0]⟩ : LVec).allKnown = true := LVec.allKnown_l0
example : (⟨#[.l1]⟩ : LVec).allKnown = true := LVec.allKnown_l1
example : (⟨#[.l0]⟩ : LVec).allKnown && (⟨#[.l1]⟩ : LVec).allKnown = true := by simp

example : LVec.concatMany #[LVec.replVec 2 (LVec.concatMany #[(LVec.ofBitVec 0b1011#4).extract (1 + 2 - 1) 1]),
    (LVec.ofBitVec 0b1011#4).extract 1 2] = LVec.ofBitVec ((0b01#2).signExtend (2 + 2)) :=
  LVec.sext_of_extract (by decide) (by decide)
example : LVec.concatMany #[LVec.replVec 1 (LVec.concatMany #[(LVec.ofBitVec 0xA6#8).extract (4 + 4 - 1) 1]),
    (LVec.ofBitVec 0xA6#8).extract 4 4] = LVec.ofBitVec ((0xA#4).signExtend (1 + 4)) :=
  LVec.sext_of_extract (by decide) (by decide)

example (a b : BitVec 3) : (a.signExtend 8 * b.signExtend 8).setWidth 6 = BitVec.ofInt 6 (a.toInt * b.toInt) :=
  Lib.setWidth_mul_signExtend (by decide) a b
example (a b : BitVec 8) : (a.signExtend 16 * b.signExtend 16).setWidth 16 = BitVec.ofInt 16 (a.toInt * b.toInt) :=
  Lib.setWidth_mul_signExtend (by decide) a b
example : ((5#3).signExtend 8 * (6#3).signExtend 8).setWidth 6 = BitVec.ofInt 6 ((5#3).toInt * (6#3).toInt) := by
  decide

#print axioms loopM_expand

end SvGolfTests.Clocked
