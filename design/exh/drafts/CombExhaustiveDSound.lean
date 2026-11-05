import LeanModels.Sv.CombExhaustive

/-!
# The packed evaluation is sound (`sv_exhaustive`, the soundness)

`run_sound`: if a read function `rd` (a settled state's `boolAt`) meets every site's equation, the order
check `topoAux` holds and the inputs are packed into the start environment, then every bit a site writes
is the packed evaluation's bit. Stated for ANY list of sites (a cone).
-/

namespace LeanModels.Sv.Exh

/-! ## Bits -/

theorem testBit_orBits (e o : Nat) (g : Nat → Bool) (j : Nat) : ∀ w,
    (orBits e o g w).testBit j = (e.testBit j || (decide (o ≤ j) && decide (j < o + w) && g (j - o)))
  | 0 => by
      have : ¬ (o ≤ j ∧ j < o + 0) := by omega
      cases h1 : decide (o ≤ j) <;> cases h2 : decide (j < o + 0) <;> simp_all [orBits]
  | w + 1 => by
      have ih := testBit_orBits e o g j w
      by_cases hj : j = o + w
      · subst hj
        have h1 : ¬ (o + w < o + w) := by omega
        unfold orBits; split <;> simp_all [Nat.testBit_or, Nat.testBit_two_pow]
      · have h2 : (j < o + (w + 1)) = (j < o + w) := by apply propext; omega
        unfold orBits; split <;> simp_all [Nat.testBit_or, Nat.testBit_two_pow, Ne.symm hj]

/-! ## The order check -/

/-- Bit `i` of `n` is written by a site of `bs`. -/
def writtenB (bs : List BSite) (n : String) (i : Nat) : Bool :=
  bs.any fun b => b.tgt == n && decide (b.lo ≤ i) && decide (i < b.lo + b.w)

/-- **The order check** (bit granularity), after the sites `done`: each site writes, inside the width of a
non-input name of `ns`, bits no earlier site wrote; and every bit it reads lies inside its name's width
and is an input bit or a bit an earlier site wrote. -/
def topoAux (wd : String → Nat) (ns ins : List String) : List BSite → List BSite → Bool
  | _, [] => true
  | done, b :: bs =>
      ns.contains b.tgt && !(ins.contains b.tgt) && decide (b.lo + b.w ≤ wd b.tgt) &&
      ((List.range b.w).all fun k => !writtenB done b.tgt (b.lo + k)) &&
      (b.rds.all fun r => ns.contains r.1 && decide (r.2.1 + r.2.2 ≤ wd r.1) &&
        (ins.contains r.1 || (List.range r.2.2).all fun j => writtenB done r.1 (r.2.1 + j))) &&
      topoAux wd ns ins (done ++ [b]) bs

/-- The layout keeps the names of `ns` apart. -/
def layoutOk (off wd : String → Nat) (ns : List String) : Bool :=
  ns.all fun n => ns.all fun m => n == m || decide (off n + wd n ≤ off m) || decide (off m + wd m ≤ off n)

/-- A site's bits depend on its reads only through the windows it lists. -/
def Congr (b : BSite) : Prop :=
  ∀ rd rd' : String → Nat → Bool, (∀ r ∈ b.rds, ∀ j < r.2.2, rd r.1 (r.2.1 + j) = rd' r.1 (r.2.1 + j)) →
    ∀ k < b.w, b.f rd k = b.f rd' k

/-! ## Soundness -/

section
variable {off wd : String → Nat} {ns ins : List String} {rd : String → Nat → Bool}

/-- What the packed environment holds after the sites `done`. -/
def Inv (off wd : String → Nat) (ns ins : List String) (rd : String → Nat → Bool) (done : List BSite)
    (e : Nat) : Prop :=
  ∀ n ∈ ns, ∀ i < wd n, e.testBit (off n + i) = (if n ∈ ins ∨ writtenB done n i = true then rd n i else false)

theorem inv_step (hL : layoutOk off wd ns = true) {done : List BSite} {b : BSite} {e : Nat}
    (hc : Congr b) (heq : ∀ k < b.w, rd b.tgt (b.lo + k) = b.f rd k)
    (hns : ns.contains b.tgt = true) (hni : ins.contains b.tgt = false) (hw : b.lo + b.w ≤ wd b.tgt)
    (hfresh : ∀ k < b.w, writtenB done b.tgt (b.lo + k) = false)
    (hrd : ∀ r ∈ b.rds, ns.contains r.1 = true ∧ r.2.1 + r.2.2 ≤ wd r.1 ∧
      (ins.contains r.1 = true ∨ ∀ j < r.2.2, writtenB done r.1 (r.2.1 + j) = true))
    (hI : Inv off wd ns ins rd done e) : Inv off wd ns ins rd (done ++ [b]) (b.step off e) := by
  intro n hn i hi
  simp only [layoutOk, List.all_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hL
  have htg : b.tgt ∈ ns := by simpa using hns
  have hwin : writtenB (done ++ [b]) n i = (writtenB done n i ||
      (decide (b.tgt = n) && decide (b.lo ≤ i) && decide (i < b.lo + b.w))) := by
    simp [writtenB, List.any_append]
  rw [BSite.step, testBit_orBits, hI n hn i hi, hwin]
  by_cases hin : n = b.tgt ∧ b.lo ≤ i ∧ i < b.lo + b.w
  · obtain ⟨rfl, h1, h2⟩ := hin
    have hk := hfresh (i - b.lo) (by omega)
    rw [show b.lo + (i - b.lo) = i by omega] at hk
    have hnin : b.tgt ∉ ins := by simpa using hni
    have hagree : ∀ r ∈ b.rds, ∀ j < r.2.2, rdOf off e r.1 (r.2.1 + j) = rd r.1 (r.2.1 + j) := by
      intro r hr j hj
      obtain ⟨hrns, hrw, hrr⟩ := hrd r hr
      have hrns' : r.1 ∈ ns := by simpa using hrns
      simp only [rdOf, hI r.1 hrns' (r.2.1 + j) (by omega)]
      rcases hrr with hm | hm
      · rw [if_pos (.inl (by simpa using hm))]
      · rw [if_pos (.inr (hm j hj))]
    have := hc (rdOf off e) rd hagree (i - b.lo) (by omega)
    have he := heq (i - b.lo) (by omega)
    rw [show b.lo + (i - b.lo) = i by omega] at he
    simp only [hnin, hk, false_or, Bool.false_eq_true, ↓reduceIte, Bool.false_or, decide_true,
      Bool.true_and, Bool.or_true]
    rw [if_pos (Or.inr rfl), show off b.tgt + i - (off b.tgt + b.lo) = i - b.lo by omega, this, he]
    simp only [decide_eq_true (show off b.tgt + b.lo ≤ off b.tgt + i by omega),
      decide_eq_true (show off b.tgt + i < off b.tgt + b.lo + b.w by omega), Bool.true_and]
  · have hout : ¬ (off b.tgt + b.lo ≤ off n + i ∧ off n + i < off b.tgt + b.lo + b.w) := by
      intro ⟨h1, h2⟩
      by_cases hnt : n = b.tgt
      · subst hnt; exact hin ⟨rfl, by omega, by omega⟩
      · rcases hL n hn b.tgt htg with h | h | h
        · exact hnt h
        · omega
        · omega
    by_cases h1 : off b.tgt + b.lo ≤ off n + i <;> by_cases h2 : off n + i < off b.tgt + b.lo + b.w <;>
      by_cases h3 : b.tgt = n <;> by_cases h4 : b.lo ≤ i <;> by_cases h5 : i < b.lo + b.w <;>
      simp_all

theorem inv_run (hL : layoutOk off wd ns = true) :
    ∀ (bs done : List BSite) (e : Nat), topoAux wd ns ins done bs = true → (∀ b ∈ bs, Congr b) →
      (∀ b ∈ bs, ∀ k < b.w, rd b.tgt (b.lo + k) = b.f rd k) → Inv off wd ns ins rd done e →
      Inv off wd ns ins rd (done ++ bs) (run off bs e)
  | [], done, e, _, _, _, hI => by simpa [run] using hI
  | b :: bs, done, e, ht, hc, heq, hI => by
      simp only [topoAux, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true', decide_eq_true_eq,
        List.mem_range, Bool.or_eq_true] at ht
      obtain ⟨⟨⟨⟨⟨hns, hni⟩, hw⟩, hfresh⟩, hrd⟩, hrest⟩ := ht
      have h1 := inv_step hL (hc b (List.mem_cons_self ..)) (heq b (List.mem_cons_self ..)) hns hni
        hw hfresh (fun r hr => ⟨(hrd r hr).1.1, (hrd r hr).1.2, (hrd r hr).2⟩) hI
      have := inv_run hL bs (done ++ [b]) _ hrest (fun b' hb => hc b' (List.mem_cons_of_mem _ hb))
        (fun b' hb => heq b' (List.mem_cons_of_mem _ hb)) h1
      simpa [run, List.append_assoc] using this

/-- **Soundness of the packed evaluation**: a bit some site of `bs` writes is the evaluation's bit. -/
theorem run_sound (hL : layoutOk off wd ns = true) (ht : topoAux wd ns ins [] bs = true)
    (hc : ∀ b ∈ bs, Congr b) (heq : ∀ b ∈ bs, ∀ k < b.w, rd b.tgt (b.lo + k) = b.f rd k) {e₀ : Nat}
    (hin : ∀ n ∈ ns, n ∈ ins → ∀ i < wd n, e₀.testBit (off n + i) = rd n i)
    (hz : ∀ n ∈ ns, n ∉ ins → ∀ i < wd n, e₀.testBit (off n + i) = false)
    {n : String} {i : Nat} (hn : n ∈ ns) (hi : i < wd n) (hw : writtenB bs n i = true) :
    rd n i = (run off bs e₀).testBit (off n + i) := by
  have h0 : Inv off wd ns ins rd [] e₀ := fun m hm j hj => by
    by_cases h : m ∈ ins
    · rw [if_pos (.inl h)]; exact hin m hm h j hj
    · rw [if_neg (by simp [writtenB, h])]; exact hz m hm h j hj
  rw [inv_run hL bs [] e₀ ht hc heq h0 n hn i hi, if_pos (.inr (by simpa using hw))]

end

/-! ## The sites of a design: congruence and equations -/

section
variable {d : Design2}

theorem lookup_localSt (d : Design2) (rd : String → Nat → Bool) :
    ∀ (ns : List String) (n : String), n ∈ ns →
      SvState.lookup (localSt d rd ns) n = some (LVec.ofBoolFn (dwOf d n) (rd n))
  | [], _, h => absurd h List.not_mem_nil
  | m :: ms, n, h => by
      show SvState.lookup ((m, _) :: localSt d rd ms) n = _
      rw [SvState.lookup_cons]
      by_cases hmn : m = n
      · subst hmn; simp
      · rw [if_neg hmn]; exact lookup_localSt d rd ms n (by simpa [Ne.symm hmn] using h)

theorem extract_ofBoolFn_congr {W lo w : Nat} {f g : Nat → Bool} (h : ∀ j < w, f (lo + j) = g (lo + j)) :
    (LVec.ofBoolFn W f).extract lo w = (LVec.ofBoolFn W g).extract lo w := by
  have h' : ∀ i : Fin w, f (lo + i.val) = g (lo + i.val) := fun i => h i.val i.isLt
  simp only [LVec.extract, LVec.getElem?_ofBoolFn, h']

/-- The local states of two read functions that agree on an expression's read windows agree on its reads. -/
theorem localSt_agree {rd rd' : String → Nat → Bool} {e : Expr2}
    (h : ∀ r ∈ e.reads.map (winOf d), ∀ j < r.2.2, rd r.1 (r.2.1 + j) = rd' r.1 (r.2.1 + j)) :
    ∀ r ∈ e.reads, r.agree (localSt d rd (e.reads.map ReadWin.name)) (localSt d rd' (e.reads.map ReadWin.name)) := by
  intro r hr
  have hn : r.name ∈ e.reads.map ReadWin.name := List.mem_map_of_mem hr
  have hw := h (winOf d r) (List.mem_map_of_mem hr)
  cases r with
  | whole n =>
      simp only [ReadWin.agree, lookup_localSt d _ _ n hn]
      exact congrArg some (LVec.ofBoolFn_congr fun j hj => by simpa [winOf] using hw j hj)
  | win n lo w =>
      simp only [ReadWin.agree, lookup_localSt d _ _ n hn, Option.map_some, LVec.width_ofBoolFn,
        extract_ofBoolFn_congr (W := dwOf d n) (fun j hj => by simpa [winOf] using hw j hj)]

theorem procSite_congr {p : Process2} {b : BSite} (hb : procSite d p = some b) : Congr b := by
  cases p with
  | assign t e =>
      simp only [procSite, Option.map_eq_some_iff] at hb
      obtain ⟨W, -, rfl⟩ := hb
      intro rd rd' h k _
      simp only [evalPure2_congr_reads (localSt_agree (d := d) h)]
  | _ => simp [procSite] at hb

theorem boolAt_extract {u : LVec} {lo w k : Nat} (hk : k < w) : (u.extract lo w).boolAt k = u.boolAt (lo + k) := by
  simp [LVec.extract, LVec.boolAt, hk]

/-- **The sites meet their equations** in a settled state with known inputs (via `CombKnown.reads_known`: every
read is known, so the local state of a right-hand side agrees with the state on its reads). `hpos`: no read
window is empty. -/
theorem sitesOf_eqs (hd : CombDesign d) (ha : Acyclic d) (hx : d.XFree) (hc : d.Covered) {st : SvState}
    (heqs : CombEqs d st) (hs : StateShape d st) (hin : d.InputsKnown st)
    (hpos : ∀ i t e, d.processes[i]? = some (.assign t e) → ∀ r ∈ e.reads, 0 < (winOf d r).2.2)
    (ord : List Nat) : ∀ b ∈ sitesOf d ord, ∀ k < b.w, st.boolAt b.tgt (b.lo + k) = b.f st.boolAt k := by
  intro b hb k hk
  obtain ⟨i, -, hi⟩ := List.mem_filterMap.mp hb
  obtain ⟨p, hp, hpb⟩ := Option.bind_eq_some_iff.mp hi
  cases p with
  | assign t e =>
    simp only [procSite, Option.map_eq_some_iff] at hpb
    obtain ⟨⟨n, lo, w⟩, hW, rfl⟩ := hpb
    obtain ⟨old, v, hold, hv, hext⟩ := heqs i t e n lo w 0 hp (by simp [Lhs2.wins_of_window? hW, Win.placed])
    have hknown := CombKnown.reads_known hd ha hx hc heqs hs hin hp
    have hagree : ∀ r ∈ e.reads, r.agree (localSt d st.boolAt (e.reads.map ReadWin.name)) st := by
      intro r hr
      have hn : r.name ∈ e.reads.map ReadWin.name := List.mem_map_of_mem hr
      have hk' := hknown r hr
      -- the read's name is bound at its declared width
      have hwid : ∃ vn, SvState.lookup st r.name = some vn ∧ dwOf d r.name = vn.width := by
        cases r with
        | whole m =>
            obtain ⟨W', vn, hW', hvn, hw', -⟩ := hk'
            exact ⟨vn, hvn, by simp [dwOf, hW', hw']⟩
        | win m lo' w' =>
            have h0 := hpos i t e hp _ hr
            obtain ⟨vn, hvn, -⟩ := hk' 0 (by simpa [winOf] using h0)
            rcases hc i t e hp _ hr 0 (by simpa [winOf] using h0) with ⟨hmi, W', hW', -⟩ | ⟨j, lo2, w2, hWj, -, -⟩
            · obtain ⟨v', hv', -, hw'⟩ := hin m hmi
              rw [hvn] at hv'; cases hv'
              exact ⟨vn, hvn, by simp [dwOf, hw']⟩
            · obtain ⟨v', hv', hw'⟩ := hs.driven m ⟨j, lo2, w2, hWj⟩
              rw [hvn] at hv'; cases hv'
              exact ⟨vn, hvn, by simp [dwOf, hw']⟩
      obtain ⟨vn, hvn, hdw⟩ := hwid
      cases r with
      | whole m =>
          obtain ⟨W', vn', hW', hvn', hw', hall⟩ := hk'
          simp only [ReadWin.agree, lookup_localSt d _ _ m hn, hvn']
          have hb : st.boolAt m = vn'.boolAt := funext fun k => by simp [SvState.boolAt, hvn']
          have he : vn' = LVec.ofBoolFn (dwOf d m) vn'.boolAt := by
            rw [show dwOf d m = vn'.width by simp [dwOf, hW', hw']]; exact LVec.eq_ofBoolFn_of_allKnown hall
          rw [hb]; exact congrArg some he.symm
      | win m lo' w' =>
          simp only [ReadWin.agree, lookup_localSt d _ _ m hn, hvn, Option.map_some, LVec.width_ofBoolFn,
            Option.some.injEq, Prod.mk.injEq]
          refine ⟨hdw, extract_eq_of_bits fun j hj => ?_⟩
          obtain ⟨vn', hvn', bj, hbj, hkn⟩ := hk' j hj
          rw [hvn] at hvn'; cases hvn'
          have hlt : lo' + j < vn.width := by
            have := (Array.getElem?_eq_some_iff.mp hbj).1; simpa [LVec.width] using this
          simp only [LVec.extract, LVec.getElem?_ofBoolFn, hbj, if_pos (show lo' + j < dwOf d m by omega),
            SvState.boolAt, hvn, LVec.boolAt, Option.getD_some, Logic.ofBool_beq_l1_of_isKnown hkn]
    simp only [evalPure2_congr_reads hagree, hv]
    have hk2 := congrArg (fun u => u.boolAt k) hext
    simp only [boolAt_extract hk] at hk2
    simp only [SvState.boolAt, hold, hk2, Win.sumWidth, Nat.add_zero, Nat.zero_add]
  | _ => simp [procSite] at hpb

/-! ### The two design facts `CombKnown` needs, decided -/

/-- Every assign's right-hand side is in the x-free fragment. -/
def xfreeB (d : Design2) : Bool := d.processes.toList.all fun
  | .assign _ e => (e.xfWidth d).isSome
  | _ => true

/-- Bit `k` of `n` is an input bit or some assign writes it. -/
def sourcedB (d : Design2) (n : String) (k : Nat) : Bool :=
  (d.inputNames.toList.contains n && decide (k < dwOf d n) && (d.declWidth n).isSome) ||
  (List.range d.processes.size).any fun i => match d.processes[i]? with
    | some (.assign t _) => (t.wins d).any fun W => W.1 == n && decide (W.2.1 ≤ k) && decide (k < W.2.1 + W.2.2)
    | _ => false

/-- Every bit an assign reads is sourced. -/
def coveredB (d : Design2) : Bool := d.processes.toList.all fun
  | .assign _ e => e.reads.all fun
      | .whole n => (d.declWidth n).isSome && decide (0 < dwOf d n) && (List.range (dwOf d n)).all (sourcedB d n)
      | .win n lo w => (List.range w).all fun k => sourcedB d n (lo + k)
  | _ => true

theorem mem_toList_of_getElem? {i : Nat} {p : Process2} (hp : d.processes[i]? = some p) :
    p ∈ d.processes.toList := by
  rw [← Array.getElem?_toList] at hp; exact List.mem_of_getElem? hp

theorem xfree_of_xfreeB (h : xfreeB d = true) : d.XFree := fun i t e hp => by
  have := List.all_eq_true.mp h _ (mem_toList_of_getElem? hp)
  simpa [Option.isSome_iff_exists] using this

theorem sourced_of_sourcedB {n : String} {k : Nat} (h : sourcedB d n k = true) : d.Sourced n k := by
  simp only [sourcedB, Bool.or_eq_true, Bool.and_eq_true, List.contains_iff_mem, decide_eq_true_eq,
    List.any_eq_true, List.mem_range] at h
  rcases h with ⟨⟨hn, hk⟩, hw⟩ | ⟨i, -, hi⟩
  · obtain ⟨W, hW⟩ := Option.isSome_iff_exists.mp hw
    exact .inl ⟨by simpa using hn, W, hW, by simpa [dwOf, hW] using hk⟩
  · split at hi
    · next t e hp =>
        obtain ⟨W, hW, hc⟩ := List.any_eq_true.mp hi
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
        obtain ⟨⟨rfl, h1⟩, h2⟩ := hc
        exact .inr ⟨i, W.2.1, W.2.2, ⟨t, e, hp, hW⟩, h1, h2⟩
    · simp at hi

theorem covered_of_coveredB (h : coveredB d = true) : d.Covered := fun i t e hp r hr => by
  have := List.all_eq_true.mp (by simpa using List.all_eq_true.mp h _ (mem_toList_of_getElem? hp)) r hr
  cases r with
  | whole n =>
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at this
      obtain ⟨⟨hw, hpos⟩, hall⟩ := this
      obtain ⟨W, hW⟩ := Option.isSome_iff_exists.mp hw
      exact ⟨W, hW, by simpa [dwOf, hW] using hpos, fun k hk =>
        sourced_of_sourcedB (hall k (by simpa [dwOf, hW] using hk))⟩
  | win n lo w =>
      simp only [List.all_eq_true, List.mem_range] at this
      exact fun k hk => sourced_of_sourcedB (this k hk)

theorem sitesOf_congr (ord : List Nat) : ∀ b ∈ sitesOf d ord, Congr b := by
  intro b hb
  obtain ⟨i, -, hi⟩ := List.mem_filterMap.mp hb
  obtain ⟨p, -, hp⟩ := Option.bind_eq_some_iff.mp hi
  exact procSite_congr hp

/-- A bit the sites of `ord` write comes from an assign to a single window. -/
theorem written_site {ord : List Nat} {y : String} {j : Nat} (h : writtenB (sitesOf d ord) y j = true) :
    ∃ i t e lo w, d.processes[i]? = some (.assign t e) ∧ t.window? d = some (y, lo, w) ∧ lo ≤ j ∧ j < lo + w := by
  obtain ⟨b, hb, hc⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
  obtain ⟨i, -, hi⟩ := List.mem_filterMap.mp hb
  obtain ⟨p, hp, hpb⟩ := Option.bind_eq_some_iff.mp hi
  cases p with
  | assign t e =>
      simp only [procSite, Option.map_eq_some_iff] at hpb
      obtain ⟨⟨n, lo, w⟩, hW, rfl⟩ := hpb
      obtain ⟨⟨rfl, h1⟩, h2⟩ := hc
      exact ⟨i, t, e, lo, w, hp, hW, h1, h2⟩
  | _ => simp [procSite] at hpb

theorem bv_congr {W : Nat} {f g : Nat → Bool} (h : ∀ j < W, f j = g j) : XF.bv W f = XF.bv W g :=
  BitVec.eq_of_getLsbD_eq fun j hj => by rw [XF.getLsbD_bv hj, XF.getLsbD_bv hj, h j hj]

/-- **An output, read off the packed evaluation**: when the sites write every bit of `y`, the settled state
holds the evaluation's bits of `y`, as a known vector. -/
theorem out_lookup (hd : CombDesign d) (ha : Acyclic d) (hx : d.XFree) (hc : d.Covered) {st : SvState}
    (heqs : CombEqs d st) (hs : StateShape d st) (hin : d.InputsKnown st)
    (hpos : ∀ i t e, d.processes[i]? = some (.assign t e) → ∀ r ∈ e.reads, 0 < (winOf d r).2.2)
    {off : String → Nat} {ns ins : List String} {ord : List Nat} {e₀ : Nat}
    (hL : layoutOk off (dwOf d) ns = true) (ht : topoAux (dwOf d) ns ins [] (sitesOf d ord) = true)
    (hin0 : ∀ n ∈ ns, n ∈ ins → ∀ i < dwOf d n, e₀.testBit (off n + i) = st.boolAt n i)
    (hz : ∀ n ∈ ns, n ∉ ins → ∀ i < dwOf d n, e₀.testBit (off n + i) = false)
    {y : String} {W : Nat} (hy : y ∈ ns) (hW : d.declWidth y = some W) (hW0 : 0 < W)
    (hall : ∀ j < W, writtenB (sitesOf d ord) y j = true) :
    SvState.lookup st y = some (LVec.ofBitVec (XF.bv W fun j => (run off (sitesOf d ord) e₀).testBit (off y + j))) := by
  have hb : ∀ j < W, st.boolAt y j = (run off (sitesOf d ord) e₀).testBit (off y + j) := fun j hj =>
    run_sound hL ht (sitesOf_congr ord) (sitesOf_eqs hd ha hx hc heqs hs hin hpos ord)
      (fun n hn hni i hi => (hin0 n hn hni i hi).symm ▸ rfl) hz hy (by simp [dwOf, hW]; omega) (hall j hj)
  obtain ⟨i, t, e, lo, w, hp, hWin, h1, h2⟩ := written_site (hall 0 hW0)
  obtain ⟨v, hv, hvw⟩ := hs.driven y ⟨i, lo, w, t, e, hp, by rw [Lhs2.wins_of_window? hWin]; simp⟩
  have hvW : v.width = W := by rw [hW] at hvw; exact (Option.some.inj hvw).symm
  have hk : ∀ j < W, KnownBit st y j := fun j hj => by
    obtain ⟨i, t, e, lo, w, hp, hWin, h1, h2⟩ := written_site (hall j hj)
    have := (CombKnown.settled hd ha hx hc heqs hs hin i t e y lo w 0 hp
      (by simp [Lhs2.wins_of_window? hWin, Win.placed]) (j - lo) (by omega)).1
    rwa [show lo + (j - lo) = j by omega] at this
  rw [hv, SvState.lookup_eq_ofBitVec_bv hv hvW hk, bv_congr hb]

end

end LeanModels.Sv.Exh
