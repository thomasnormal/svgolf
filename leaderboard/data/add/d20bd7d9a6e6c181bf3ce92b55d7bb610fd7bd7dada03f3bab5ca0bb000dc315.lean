import Submission.Design
import SvGolf.Comb
import LeanModels.Sv.CombEqTactic
import LeanModels.Sv.CombLib

/-!
# Carry-select arithmetic, for every block size `K` and every width `N`

Plain Lean over `Nat`-indexed Boolean functions; nothing here mentions the design. A carry-select
adder with `K`-bit blocks is `Q = N / K` blocks, each with two ripple chains (`c0` from carry-in 0,
`c1` from 1, chain `j` stored at `W * j + t`, `W = K + 1`), a multiplexer row `c (K*j+t)` choosing
by the block carry `cb j`, block carries `cb (j+1)` chosen the same way, and a ripple tail of
`N % K` bits from `cb Q`. `csel_carry` says the selected carries are THE ripple carries
(`rip g p 0 ci`), so the adder is `CombLib.AddView` (`csel_view`).
-/

namespace CselMath

open LeanModels.Sv.CombLib

/-- The ripple carry into position `b + t` when the carry into position `b` is `x0`. -/
def rip (g p : Nat → Bool) (b : Nat) (x0 : Bool) : Nat → Bool
  | 0 => x0
  | t + 1 => g (b + t) || (p (b + t) && rip g p b x0 t)

/-- A chain stored at offset `o` that starts at `x0` and takes the ripple steps of positions
`b, b+1, …` is the ripple carry from `b`. -/
theorem chain_eq (g p d : Nat → Bool) (b o K : Nat) (x0 : Bool) (h0 : d o = x0)
    (hs : ∀ t < K, d (o + t + 1) = (g (b + t) || (p (b + t) && d (o + t)))) :
    ∀ t ≤ K, d (o + t) = rip g p b x0 t := by
  intro t
  induction t with
  | zero => intro _; simpa [rip] using h0
  | succ t ih =>
    intro ht
    show d (o + t + 1) = _
    rw [hs t (by omega), ih (by omega)]
    try rfl

/-- Restarting the ripple at `b` from its own carry changes nothing. -/
theorem rip_add (g p : Nat → Bool) (ci : Bool) (b : Nat) :
    ∀ t, rip g p 0 ci (b + t) = rip g p b (rip g p 0 ci b) t := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih =>
    show rip g p 0 ci (b + t + 1) = _
    simp only [rip, Nat.zero_add, ih]

/-- A multiplexer between the two chains is the chain from the select value. -/
theorem mux_rip (g p : Nat → Bool) (b : Nat) (x : Bool) (t : Nat) :
    (if x = true then rip g p b true t else rip g p b false t) = rip g p b x t := by
  cases x <;> rfl

/-- **The selected carries are the ripple carries.** -/
theorem csel_carry (K W N : Nat) (hK : 0 < K) (hW : W = K + 1)
    (g p c0 c1 cb c : Nat → Bool) (ci : Bool)
    (hcb0 : cb 0 = ci)
    (h00 : ∀ j < N / K, c0 (W * j) = false)
    (h10 : ∀ j < N / K, c1 (W * j) = true)
    (h0s : ∀ j < N / K, ∀ t < K,
      c0 (W * j + t + 1) = (g (K * j + t) || (p (K * j + t) && c0 (W * j + t))))
    (h1s : ∀ j < N / K, ∀ t < K,
      c1 (W * j + t + 1) = (g (K * j + t) || (p (K * j + t) && c1 (W * j + t))))
    (hsel : ∀ j < N / K, ∀ t < K,
      c (K * j + t) = (if cb j = true then c1 (W * j + t) else c0 (W * j + t)))
    (hcbs : ∀ j < N / K,
      cb (j + 1) = (if cb j = true then c1 (W * j + K) else c0 (W * j + K)))
    (hcQ : c (K * (N / K)) = cb (N / K))
    (htail : ∀ t < N % K, c (K * (N / K) + t + 1) =
      (g (K * (N / K) + t) || (p (K * (N / K) + t) && c (K * (N / K) + t)))) :
    ∀ i ≤ N, c i = rip g p 0 ci i := by
  -- the two chains of block j
  have hc0 : ∀ j < N / K, ∀ t ≤ K, c0 (W * j + t) = rip g p (K * j) false t := fun j hj =>
    chain_eq g p c0 (K * j) (W * j) K false (h00 j hj) (h0s j hj)
  have hc1 : ∀ j < N / K, ∀ t ≤ K, c1 (W * j + t) = rip g p (K * j) true t := fun j hj =>
    chain_eq g p c1 (K * j) (W * j) K true (h10 j hj) (h1s j hj)
  -- the multiplexer between them
  have hmux : ∀ j < N / K, ∀ t ≤ K,
      (if cb j = true then c1 (W * j + t) else c0 (W * j + t)) = rip g p (K * j) (cb j) t := by
    intro j hj t ht
    rw [hc1 j hj t ht, hc0 j hj t ht, mux_rip]
  -- the block carries are the ripple carries at the block boundaries
  have hcb : ∀ j ≤ N / K, cb j = rip g p 0 ci (K * j) := by
    intro j
    induction j with
    | zero => intro _; rw [hcb0]; try rfl
    | succ j ih =>
      intro hj
      rw [hcbs j (by omega), hmux j (by omega) K (Nat.le_refl K), ih (by omega),
        ← rip_add, Nat.mul_add, Nat.mul_one]
  intro i hi
  by_cases hlo : i < K * (N / K)
  · -- inside a block
    have hj : i / K < N / K := by
      first
        | exact Nat.div_lt_of_lt_mul hlo
        | exact (Nat.div_lt_iff_lt_mul hK).2 (by rw [Nat.mul_comm]; exact hlo)
    have ht : i % K < K := Nat.mod_lt i hK
    have hi' : K * (i / K) + i % K = i := Nat.div_add_mod i K
    rw [← hi', hsel (i / K) hj (i % K) ht, hmux (i / K) hj (i % K) (by omega),
      hcb (i / K) (by omega), ← rip_add]
  · -- the tail
    have hN : K * (N / K) + N % K = N := Nat.div_add_mod N K
    obtain ⟨t, rfl⟩ : ∃ t, i = K * (N / K) + t := ⟨i - K * (N / K), by omega⟩
    have htl : t ≤ N % K := by omega
    clear hlo hi
    induction t with
    | zero => rw [Nat.add_zero, hcQ, hcb (N / K) (Nat.le_refl _)]
    | succ t ih =>
      rw [← Nat.add_assoc, htail t (by omega), ih (by omega)]
      show _ = rip g p 0 ci (K * (N / K) + t + 1)
      simp only [rip, Nat.zero_add]

/-- Bit `t` of block `j` lies below the tail. -/
theorem blk_lt {K N j t : Nat} (hj : j < N / K) (ht : t < K) : K * j + t < K * (N / K) := by
  have h1 : K * (j + 1) ≤ K * (N / K) := by
    first
      | exact Nat.mul_le_mul_left K (show j + 1 ≤ N / K by omega)
      | exact Nat.mul_le_mul (Nat.le_refl K) (show j + 1 ≤ N / K by omega)
  rw [Nat.mul_add, Nat.mul_one] at h1
  omega

/-- The carry into bit `i` of the carry-select adder: the block multiplexer row `cs` below
`K * (N / K)`, the tail carry `c` from there on. -/
def sel (K N : Nat) (cs c : Nat → Bool) (i : Nat) : Bool := if i < K * (N / K) then cs i else c i

theorem sel_lo {K N i : Nat} {cs c : Nat → Bool} (h : i < K * (N / K)) : sel K N cs c i = cs i :=
  if_pos h

theorem sel_hi {K N i : Nat} {cs c : Nat → Bool} (h : ¬ i < K * (N / K)) : sel K N cs c i = c i :=
  if_neg h

/-- **The carry-select adder is an adder**: its equations give `CombLib.AddView`, with `sel` (the
multiplexed block carries, then the tail carries) as the carry function. -/
theorem csel_view (K W N : Nat) (hK : 0 < K) (hW : W = K + 1) (x y : BitVec N) (ci : Bool)
    (g p c0 c1 cb cs c s : Nat → Bool) (cout : Bool)
    (hg : ∀ i < N, g i = (x.getLsbD i && y.getLsbD i))
    (hp : ∀ i < N, p i = (x.getLsbD i ^^ y.getLsbD i))
    (hcb0 : cb 0 = ci)
    (h00 : ∀ j < N / K, c0 (W * j) = false)
    (h10 : ∀ j < N / K, c1 (W * j) = true)
    (h0s : ∀ j < N / K, ∀ t < K,
      c0 (W * j + t + 1) = (g (K * j + t) || (p (K * j + t) && c0 (W * j + t))))
    (h1s : ∀ j < N / K, ∀ t < K,
      c1 (W * j + t + 1) = (g (K * j + t) || (p (K * j + t) && c1 (W * j + t))))
    (hsel : ∀ j < N / K, ∀ t < K,
      cs (K * j + t) = (if cb j = true then c1 (W * j + t) else c0 (W * j + t)))
    (hcbs : ∀ j < N / K,
      cb (j + 1) = (if cb j = true then c1 (W * j + K) else c0 (W * j + K)))
    (hcQ : c (K * (N / K)) = cb (N / K))
    (htail : ∀ t < N % K, c (K * (N / K) + t + 1) =
      (g (K * (N / K) + t) || (p (K * (N / K) + t) && c (K * (N / K) + t))))
    (hsb : ∀ j < N / K, ∀ t < K, s (K * j + t) = (p (K * j + t) ^^ cs (K * j + t)))
    (hst : ∀ t < N % K, s (K * (N / K) + t) = (p (K * (N / K) + t) ^^ c (K * (N / K) + t)))
    (hout : cout = c N) :
    AddView N x y ci (sel K N cs c) s cout := by
  have hN : K * (N / K) + N % K = N := Nat.div_add_mod N K
  have hlt : ∀ j < N / K, ∀ t < K, K * j + t < K * (N / K) := fun _ hj _ ht => blk_lt hj ht
  have hc := csel_carry K W N hK hW g p c0 c1 cb (sel K N cs c) ci hcb0 h00 h10 h0s h1s
    (fun j hj t ht => by rw [sel_lo (hlt j hj t ht)]; exact hsel j hj t ht)
    hcbs
    (by rw [sel_hi (Nat.lt_irrefl _)]; exact hcQ)
    (fun t ht => by
      rw [sel_hi (i := K * (N / K) + t + 1) (by omega), sel_hi (i := K * (N / K) + t) (by omega)]
      exact htail t ht)
  refine ⟨?_, fun i hi => ?_, fun i hi => ?_, ?_⟩
  · rw [hc 0 (Nat.zero_le _)]
    try rfl
  · rw [hc (i + 1) (by omega), hc i (by omega)]
    show (g (0 + i) || (p (0 + i) && rip g p 0 ci i)) = _
    rw [Nat.zero_add, hg i hi, hp i hi]
    generalize rip g p 0 ci i = r
    generalize x.getLsbD i = u
    generalize y.getLsbD i = v
    cases r <;> cases u <;> cases v <;> rfl
  · by_cases hlo : i < K * (N / K)
    · have hj : i / K < N / K := by
        first
          | exact Nat.div_lt_of_lt_mul hlo
          | exact (Nat.div_lt_iff_lt_mul hK).2 (by rw [Nat.mul_comm]; exact hlo)
      have hi' : K * (i / K) + i % K = i := Nat.div_add_mod i K
      have h := hsb (i / K) hj (i % K) (Nat.mod_lt i hK)
      rw [hi'] at h
      rw [h, hp i hi, sel_lo hlo]
    · obtain ⟨t, rfl⟩ : ∃ t, i = K * (N / K) + t := ⟨i - K * (N / K), by omega⟩
      rw [hst t (by omega), hp _ hi, sel_hi hlo]
  · rw [hout, sel_hi (i := N) (by omega)]

end CselMath

namespace Submission

open LeanModels.Sv LeanModels.Sv.CombView LeanModels.Sv.CombLib LeanModels.Sv.CombEq SvGolf

/-- The rank: each site's depth (K = 6). Plain sites: cb[0] = cin (0), the unused rows Q of c0,
c1, cs (1, 2, 3), c[6Q] = cb[Q] (4), cout (5). -/
def cselRank (N : Nat) : SiteId → Nat
  | .plain p => if p = 4 then N + 9 else if p = 5 then 3 * N + 30 else 0
  | .fam l p [i] =>
      if l = "g_pg" then 1
      else if l = "g_blk" then (if p ≤ 1 then 1 else 8 + i.toNat)
      else if l = "g_tail" then N + 10 + i.toNat
      else 3 * N + 30
  | .fam l p [j, t] => if l = "g_s" then 3 * N + 30 else if p ≤ 1 then t.toNat + 2 else 9 + j.toNat
  | .fam _ _ _ => 0

set_option maxHeartbeats 1000000 in
theorem csel_struct (N : Nat) (hN : 1 ≤ N) :
    CombDesign (design.sem N) ∧ Acyclic (design.sem N) ∧ SharedObl design.pdesign [N] := by
  sv_structure (rank := cselRank N)
  all_goals first
    | (intros; omega)
    | (intros; sv_rowmajor; omega)
    | fail "unclosed structure obligation"

theorem csel_interface (N : Nat) (hN : 1 ≤ N) (hc : CombDesign (design.sem N)) :
    SvGolf.Tasks.Add.task.Interface N (design.sem N) := by
  sv_interface

theorem bv1_eq_ofBool (v : BitVec 1) : v = BitVec.ofBool (v.getLsbD 0) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  obtain rfl : i = 0 := by omega
  simp

theorem knownBit_congr {st : SvState} {n : String} {a b : Nat} (h : KnownBit st n a) (e : a = b) :
    KnownBit st n b := e ▸ h

/-- **The player's arithmetic, at the ports.** From the netlist's equations over `Bool` (in `Nat`
index form, block size `K`, chain stride `W = K + 1`) and the knownness of `s` and `cout`: the task's
outputs. -/
theorem csel_final (K W : Nat) (hK : 0 < K) (hW : W = K + 1) {N : Nat} {st : SvState}
    {x y : BitVec N} {c0 : Bool}
    (hA : SvState.lookup st "a" = some (LVec.ofBitVec x))
    (hB : SvState.lookup st "b" = some (LVec.ofBitVec y))
    (hCi : SvState.lookup st "cin" = some (LVec.ofBitVec (BitVec.ofBool c0)))
    (hg : ∀ i < N, st.boolAt "g" i = (st.boolAt "a" i && st.boolAt "b" i))
    (hp : ∀ i < N, st.boolAt "p" i = (st.boolAt "a" i ^^ st.boolAt "b" i))
    (hcb0 : st.boolAt "cb" 0 = st.boolAt "cin" 0)
    (h00 : ∀ j < N / K, st.boolAt "c0" (W * j) = false)
    (h10 : ∀ j < N / K, st.boolAt "c1" (W * j) = true)
    (h0s : ∀ j < N / K, ∀ t < K, st.boolAt "c0" (W * j + t + 1) =
      (st.boolAt "g" (K * j + t) || (st.boolAt "p" (K * j + t) && st.boolAt "c0" (W * j + t))))
    (h1s : ∀ j < N / K, ∀ t < K, st.boolAt "c1" (W * j + t + 1) =
      (st.boolAt "g" (K * j + t) || (st.boolAt "p" (K * j + t) && st.boolAt "c1" (W * j + t))))
    (hsel : ∀ j < N / K, ∀ t < K, st.boolAt "cs" (K * j + t) =
      (if st.boolAt "cb" j = true then st.boolAt "c1" (W * j + t) else st.boolAt "c0" (W * j + t)))
    (hcbs : ∀ j < N / K, st.boolAt "cb" (j + 1) =
      (if st.boolAt "cb" j = true then st.boolAt "c1" (W * j + K) else st.boolAt "c0" (W * j + K)))
    (hcQ : st.boolAt "c" (K * (N / K)) = st.boolAt "cb" (N / K))
    (htail : ∀ t < N % K, st.boolAt "c" (K * (N / K) + t + 1) =
      (st.boolAt "g" (K * (N / K) + t) ||
        (st.boolAt "p" (K * (N / K) + t) && st.boolAt "c" (K * (N / K) + t))))
    (hsb : ∀ j < N / K, ∀ t < K,
      st.boolAt "s" (K * j + t) = (st.boolAt "p" (K * j + t) ^^ st.boolAt "cs" (K * j + t)))
    (hst : ∀ t < N % K, st.boolAt "s" (K * (N / K) + t) =
      (st.boolAt "p" (K * (N / K) + t) ^^ st.boolAt "c" (K * (N / K) + t)))
    (eout : st.boolAt "cout" 0 = st.boolAt "c" N)
    {vs : LVec} (hs : SvState.lookup st "s" = some vs) (hsw : vs.width = N)
    (hks : ∀ k, k < N → KnownBit st "s" k)
    {vc : LVec} (hc : SvState.lookup st "cout" = some vc) (hcw : vc.width = 1)
    (hkc : KnownBit st "cout" 0) :
    SvState.lookup st "s" = some (LVec.ofBitVec
        (BitVec.ofNat N (x.toNat + y.toNat + c0.toNat))) ∧
    SvState.lookup st "cout" = some (LVec.ofBitVec
        (BitVec.ofNat 1 ((x.toNat + y.toNat + c0.toNat) / 2 ^ N))) := by
  have hN : K * (N / K) + N % K = N := Nat.div_add_mod N K
  have hvs := SvState.lookup_eq_ofBitVec_bv hs hsw hks
  have hvc := SvState.lookup_eq_ofBitVec_bv hc hcw (fun k hk => by
    obtain rfl : k = 0 := by omega
    exact hkc)
  rw [hvs] at hs
  rw [hvc] at hc
  have hxb : XF.bv 1 (st.boolAt "cout") = BitVec.ofBool (st.boolAt "cout" 0) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    obtain rfl : i = 0 := by omega
    rw [XF.getLsbD_bv hi]; simp
  have ba : ∀ i, i < N → st.boolAt "a" i = x.getLsbD i := fun i hi => SvState.boolAt_ofBitVec hA hi
  have bb : ∀ i, i < N → st.boolAt "b" i = y.getLsbD i := fun i hi => SvState.boolAt_ofBitVec hB hi
  have bci : st.boolAt "cin" 0 = c0 := by
    rw [SvState.boolAt_ofBitVec hCi (by omega)]; simp
  have hv : AddView N x y c0 (CselMath.sel K N (st.boolAt "cs") (st.boolAt "c"))
      (XF.bv N (st.boolAt "s")).getLsbD (st.boolAt "cout" 0) :=
    CselMath.csel_view K W N hK hW x y c0 (st.boolAt "g") (st.boolAt "p") (st.boolAt "c0")
      (st.boolAt "c1") (st.boolAt "cb") (st.boolAt "cs") (st.boolAt "c")
      (XF.bv N (st.boolAt "s")).getLsbD (st.boolAt "cout" 0)
      (fun i hi => by rw [hg i hi, ba i hi, bb i hi])
      (fun i hi => by rw [hp i hi, ba i hi, bb i hi])
      (by rw [hcb0, bci]) h00 h10 h0s h1s hsel hcbs hcQ htail
      (fun j hj t ht => by
        have hlt := CselMath.blk_lt hj ht
        rw [XF.getLsbD_bv (show K * j + t < N by omega), hsb j hj t ht])
      (fun t ht => by rw [XF.getLsbD_bv (show K * (N / K) + t < N by omega), hst t ht]) eout
  obtain ⟨h1, h2⟩ := add_spec hv
  rw [hs, h1, hc, hxb, h2]
  exact ⟨rfl, rfl⟩

/-- A row-major cell at non-negative coordinates is the flat index `i * W + j` (`sv_bridge … with
rmN_flat` compares a 2-D read with a `Nat`-indexed one). -/
theorem rmN_flat {W i j : Int} (hW : 0 ≤ W) (hi : 0 ≤ i) (hj : 0 ≤ j) :
    rmN W i j = (i * W + j).toNat := by
  obtain ⟨w, rfl⟩ := Int.eq_ofNat_of_zero_le hW
  obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le hi
  obtain ⟨b, rfl⟩ := Int.eq_ofNat_of_zero_le hj
  unfold rmN
  first
    | rw [← Int.natCast_mul, ← Int.natCast_add, Int.toNat_natCast, Int.toNat_natCast,
        Int.toNat_natCast, Int.toNat_natCast]
    | simp only [Int.toNat_natCast, ← Int.natCast_mul, ← Int.natCast_add]

theorem toNatW : (7 : Int).toNat = 7 := rfl
theorem toNatK : (6 : Int).toNat = 6 := rfl

/-- The one-bit literals as `sv_equations` hands them over. -/
theorem lit0 : ({ bits := #[Logic.l0] } : LVec).boolAt 0 = false := by
  first | rfl | decide | simp [LVec.boolAt]
theorem lit1 : ({ bits := #[Logic.l1] } : LVec).boolAt 0 = true := by
  first | rfl | decide | simp [LVec.boolAt]

set_option maxHeartbeats 1000000 in
theorem solution : Goal := by
  intro N hN
  have hN' : 1 ≤ N := hN.1
  obtain ⟨hc, ha, hso⟩ := csel_struct N hN'
  refine CombTask.satisfiedAt_of_comb (csel_interface N hN' hc) hc ha ?_
  intro st heqs hs v hv
  obtain ⟨x, y, ci, ⟨⟩⟩ := v
  obtain ⟨c0, rfl⟩ : ∃ c0, ci = BitVec.ofBool c0 := ⟨_, bv1_eq_ofBool ci⟩
  simp only [SvGolf.Tasks.Add.task, HoldAll_cons, HoldAll_nil, and_true, BitVec.toNat_ofBool]
    at hv ⊢
  obtain ⟨hA, hB, hCi⟩ := hv
  sv_equations
  · have hknown : ∃ vs, SvState.lookup st "s" = some vs ∧ vs.width = N := by
      by_cases hQ : 6 ≤ N
      · obtain ⟨⟨vs, hvs, hvsw⟩, -⟩ := known_s_1 0 (by omega) 0 (by omega)
        exact ⟨vs, hvs, by omega⟩
      · obtain ⟨⟨vs, hvs, hvsw⟩, -⟩ := known_s_2 0 (by omega)
        exact ⟨vs, hvs, by omega⟩
    obtain ⟨vs, hvs, hvsw⟩ := hknown
    have hks : ∀ k, k < N → KnownBit st "s" k := by
      intro k hk
      by_cases hkq : k < 6 * (N / 6)
      · exact knownBit_congr (known_s_1 (k / 6) (by omega) (k % 6) (by omega)).2 (by omega)
      · exact knownBit_congr (known_s_2 (k - 6 * (N / 6)) (by omega)).2 (by omega)
    obtain ⟨⟨vc, hvc, hvcw⟩, hkc⟩ := known_cout_1
    refine csel_final 6 7 (by decide) rfl hA hB hCi ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hvs
      hvsw hks hvc hvcw hkc
    · sv_bridge eq_g_1
    · sv_bridge eq_p_1
    · sv_bridge eq_cb_1
    · first
        | sv_bridge eq_c0_2 with rmN, toNatW, toNatK, Int.toNat_natCast
        | sv_bridge eq_c0_2 with rmN_flat
    · first
        | sv_bridge eq_c1_2 with rmN, toNatW, toNatK, Int.toNat_natCast
        | sv_bridge eq_c1_2 with rmN_flat
    · first
        | sv_bridge eq_c0_3 with rmN, toNatW, toNatK, Int.toNat_natCast
        | sv_bridge eq_c0_3 with rmN_flat
    · first
        | sv_bridge eq_c1_3 with rmN, toNatW, toNatK, Int.toNat_natCast
        | sv_bridge eq_c1_3 with rmN_flat
    · first
        | sv_bridge eq_cs_2 with rmN, toNatW, toNatK, Int.toNat_natCast
        | sv_bridge eq_cs_2 with rmN_flat
    · first
        | sv_bridge eq_cb_2 with rmN, toNatW, toNatK, Int.toNat_natCast
        | sv_bridge eq_cb_2 with rmN_flat
    · sv_bridge eq_c_1
    · sv_bridge eq_c_2
    · first
        | sv_bridge eq_s_1 with rmN, toNatW, toNatK, Int.toNat_natCast
        | sv_bridge eq_s_1 with rmN_flat
    · sv_bridge eq_s_2
    · sv_bridge eq_cout_1
  all_goals first
    | (intros; omega)
    | rfl
    | (intros; rfl)
    | decide
    | sv_cover
    | (refine inKnown_ofBitVec hA ?_; omega)
    | (refine inKnown_ofBitVec hB ?_; omega)
    | (refine inKnown_ofBitVec hCi ?_; omega)
    | fail "unclosed obligation"

/--
info: 'Submission.solution' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms solution

end Submission
