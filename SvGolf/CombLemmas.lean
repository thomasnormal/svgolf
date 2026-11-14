import SvGolf.Comb
import LeanModels.Sv.CombLib
import LeanModels.Sv.CombKnownBits
import LeanModels.Sv.XorSum
import LeanModels.Sv.Known2
import LeanModels.Sv.Comb2

/-!
# Lemmas for combinational proofs (untrusted, kernel-checked)

Nothing here is part of the trusted base. These are the helper lemmas that the combinational proofs on the board
(`add`, `mul`, `clmul`) stated and proved for themselves, one copy per proof, in the same or nearly the same words:
here once, for every width and size. Each section says which step of a combinational proof (`PROVING.md`, sections 1
to 5) it serves.

* **Values of bit functions** (the arithmetic, over `CombLib.bfVal`): `CombLib.bfVal_eq_val` (`bfVal` is `XF.val`,
  so the `Lib.XFVal` lemmas apply), `CombLib.bfVal_false`, `CombLib.bfVal_lt`, `CombLib.bfVal_mod`,
  `CombLib.bfVal_not`, `CombLib.bfVal_window`, `CombLib.bfVal_or`, and the half adder `CombLib.halfAdder_arith`.
* **Carry-save arithmetic** (multipliers): the 3:2 row with its carry row shifted one column
  (`CombLib.csa_row`), the 4:2 node of two such rows (`CombLib.node_sum`), sums of consecutive rows (`CombLib.csum`,
  `CombLib.csum_front`, `CombLib.csum_front3`, `CombLib.csum_mod`), the carry-save tape (`CombLib.tape_sum`: a queue
  of 3:2 adders keeps the sum of its rows modulo `2^W`), and the final adder (`CombLib.ripple_mod`: a ripple row
  with carry-in `0` and the top carry dropped is the sum modulo `2^W`).
* **XOR sums and carry-less products** (over `XorSum.bx`): `XorSum.bx_succ`, `XorSum.bx_congr`, `XorSum.bx_trunc`,
  `XorSum.bx_false`, `XorSum.bx_add`, `XorSum.bx_xor`, `XorSum.bx_and`, `XorSum.bx_pair`; the carry-less product
  `XorSum.cl` with `XorSum.cl_congr`, `XorSum.cl_big`, `XorSum.cl_shift`, `XorSum.cl_trunc`, `XorSum.cl_sum`, and
  one Karatsuba step (`XorSum.karatsuba`, `XorSum.karatsuba_full`, `XorSum.karatsuba_cols`).
* **Adder results as the task states them** (`add`): `Lib.bv1_eq_ofBool`, `Lib.sum_eq_ofNat`, `Lib.carry_eq_ofNat`.
* **Reading the ports** (the settled-state lemma): `SvState.lookup_eq_ofBitVec_of_bits` and
  `SvState.lookup_eq_ofBitVec_of_bv` (an output port all of whose bits are known holds `ofBitVec y`), and the
  statement from its three parts, `CombTask.statement_of_comb`.
* **The by-hand route** (a design the comb tactics refuse, `PROVING.md` section 5): `LeafProcs` (every process is a
  continuous assign to one window) gives the comb profile (`LeafProcs.combDesign`), acyclicity from a rank on the
  processes (`LeafProcs.acyclic`), the writes (`LeafProcs.writes`, `LeafProcs.writes_pos`) and the positions
  (`LeafProcs.getElem?_of_mem`, `LeafProcs.mem_of_getElem?`); the gates on known one-bit values in `Bool` form
  (`evalPure2_bit_of_lookup`, `evalPure2_slice_of_extract`, `evalPure2_lit_l0`, `evalPure2_and_bool`,
  `evalPure2_or_bool`, `evalPure2_xor_bool`), an assign read back on a state solving the
  equations (`CombEqs.readback`, `CombEqs.readback1`), and a window known bit by bit
  (`LVec.extract_eq_ofBitVec_of_bits`).

The names sit in sub-namespaces of `SvGolf` named after the library's own (`SvGolf.CombLib`, `SvGolf.XorSum`,
`SvGolf.Lib`, `SvGolf.SvState`, `SvGolf.CombEqs`, `SvGolf.LVec`), so that after
`open LeanModels.Sv SvGolf` a proof writes `CombLib.csa_row` or `XorSum.bx_congr`, the names they would have in
`LeanModels.Sv`; `open SvGolf.CombLib` (or `SvGolf.XorSum`) next to `open LeanModels.Sv.CombLib` gives the bare
names.
-/

namespace SvGolf

open LeanModels.Sv

set_option autoImplicit false

/-! ## 1. Values of bit functions -/

namespace CombLib

open LeanModels.Sv.CombLib

/-- `bfVal` is `XF.val` (the same sum under the name the word-level lemmas of `Lib.XFVal` use). -/
theorem bfVal_eq_val (f : Nat → Bool) : ∀ n, bfVal f n = XF.val f n
  | 0 => rfl
  | n + 1 => by rw [bfVal, XF.val, bfVal_eq_val f n]

/-- Bits that are all `false` have the value `0`. -/
theorem bfVal_false {f : Nat → Bool} {n : Nat} (h : ∀ j < n, f j = false) : bfVal f n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [bfVal]
    rw [ih (fun j hj => h j (by omega)), h n (by omega)]
    simp

/-- `n` bits have a value below `2^n`. -/
theorem bfVal_lt (f : Nat → Bool) (n : Nat) : bfVal f n < 2 ^ n := by
  induction n with
  | zero => simp [bfVal]
  | succ n ih =>
    simp only [bfVal, Nat.pow_succ]
    have h2 : 2 ^ n * (f n).toNat ≤ 2 ^ n := by
      rcases Bool.eq_false_or_eq_true (f n) with h | h <;> simp [h]
    omega

/-- The low `n` bits of `m ≥ n` bits: the value modulo `2^n`. -/
theorem bfVal_mod (f : Nat → Bool) {n m : Nat} (h : n ≤ m) : bfVal f m % 2 ^ n = bfVal f n := by
  obtain ⟨d, rfl⟩ : ∃ d, m = n + d := ⟨m - n, by omega⟩
  rw [bfVal_split, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (bfVal_lt f n)]

/-- The complement: `val (!f) + val f + 1 = 2^n`. -/
theorem bfVal_not (f : Nat → Bool) (n : Nat) :
    bfVal (fun j => !f j) n + bfVal f n + 1 = 2 ^ n := by
  induction n with
  | zero => simp [bfVal]
  | succ n ih =>
    simp only [bfVal, Nat.pow_succ]
    rcases Bool.eq_false_or_eq_true (f n) with h | h <;>
      simp only [h, Bool.not_true, Bool.not_false, Bool.toNat_true, Bool.toNat_false,
        Nat.mul_one, Nat.mul_zero, Nat.add_zero] <;> omega

/-- A function that is `false` outside `[lo, lo + w)`: its value is that window's, shifted by `lo`. -/
theorem bfVal_window (f : Nat → Bool) (lo w n : Nat) (hn : lo + w ≤ n)
    (hlo : ∀ c, c < lo → f c = false) (hhi : ∀ c, lo + w ≤ c → f c = false) :
    bfVal f n = 2 ^ lo * bfVal (fun j => f (lo + j)) w := by
  obtain ⟨r, rfl⟩ : ∃ r, n = lo + (w + r) := ⟨n - lo - w, by omega⟩
  have h3 : bfVal f lo = 0 := bfVal_false (fun j hj => hlo j hj)
  have h4 : bfVal (fun j => f (lo + (w + j))) r = 0 :=
    bfVal_false (fun j _ => hhi _ (by omega))
  rw [bfVal_split f lo (w + r), bfVal_split (fun j => f (lo + j)) w r, h3]
  simp only [h4, Nat.mul_zero, Nat.add_zero, Nat.zero_add]

/-- An OR of two functions that are never both `true` is a sum. -/
theorem bfVal_or {h f g : Nat → Bool} (n : Nat) (hfg : ∀ c, h c = (f c || g c))
    (hd : ∀ c, f c = true → g c = true → False) :
    bfVal h n = bfVal f n + bfVal g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [bfVal]
    rw [ih, hfg n]
    rcases Bool.eq_false_or_eq_true (f n) with h1 | h1 <;>
      rcases Bool.eq_false_or_eq_true (g n) with h2 | h2
    · exact (hd n h1 h2).elim
    all_goals (simp only [h1, h2, Bool.or_true, Bool.or_false,
      Bool.toNat_true, Bool.toNat_false, Nat.mul_one, Nat.mul_zero, Nat.add_zero] <;> omega)

/-- One half adder, as arithmetic: `sum + 2·carry = x + y` (the twin of `fullAdder_arith`). -/
theorem halfAdder_arith (x y : Bool) : (x ^^ y).toNat + 2 * (x && y).toNat = x.toNat + y.toNat := by
  cases x <;> cases y <;> decide

/-! ## 2. Carry-save arithmetic -/

/-- **A row of 3:2 counters**, the carry row `sh` shifted one column (`sh (c+1) = cy c`, `sh 0 = false`): the
column-weighted sum is kept, up to the dropped top carry `cy n`. -/
theorem csa_row (n : Nat) (x y z s cy sh : Nat → Bool)
    (hs : ∀ c < n + 1, s c = (x c ^^ y c ^^ z c))
    (hcy : ∀ c < n + 1, cy c = ((x c && y c) || (z c && (x c ^^ y c))))
    (hsh0 : sh 0 = false) (hsh : ∀ c, c + 1 < n + 1 → sh (c + 1) = cy c) :
    bfVal s (n + 1) + bfVal sh (n + 1) + 2 ^ (n + 1) * (cy n).toNat =
      bfVal x (n + 1) + bfVal y (n + 1) + bfVal z (n + 1) := by
  have key : ∀ m, m ≤ n + 1 →
      bfVal s m + 2 * bfVal cy m = bfVal x m + bfVal y m + bfVal z m := by
    intro m
    induction m with
    | zero => intro _; simp [bfVal]
    | succ m ih =>
      intro hm
      have ih := ih (by omega)
      have hfa := fullAdder_arith (x m) (y m) (z m)
      rw [← hs m (by omega), ← hcy m (by omega)] at hfa
      simp only [bfVal]
      have : 2 ^ m * ((s m).toNat + 2 * (cy m).toNat) =
          2 ^ m * ((x m).toNat + (y m).toNat + (z m).toNat) := by rw [hfa]
      generalize (s m).toNat = S0 at *
      generalize (cy m).toNat = C0 at *
      generalize (x m).toNat = X0 at *
      generalize (y m).toNat = Y0 at *
      generalize (z m).toNat = Z0 at *
      generalize 2 ^ m = P at *
      grind
  have hsh' : bfVal sh (n + 1) = 2 * bfVal cy n := by
    rw [bfVal_shift, hsh0]
    have : bfVal (fun j => sh (j + 1)) n = bfVal cy n :=
      bfVal_congr (fun j hj => hsh j (by omega))
    rw [this]; simp
  have hk := key (n + 1) (Nat.le_refl _)
  rw [hsh']
  simp only [bfVal, Nat.pow_succ] at hk ⊢
  generalize 2 ^ n = P at *
  generalize (cy n).toNat = C0 at *
  grind

/-- **A 4:2 compressor node**: two stacked rows of 3:2 counters on a window of `n+1` columns keep the sum,
up to the two dropped top carries. -/
theorem node_sum (n : Nat) (SL CL SR CR S C X Y : Nat → Bool)
    (hX : ∀ c < n + 1, X c = (SL c ^^ CL c ^^ SR c))
    (hY0 : Y 0 = false)
    (hY : ∀ c, c + 1 < n + 1 → Y (c + 1) = ((SL c && CL c) || (SR c && (SL c ^^ CL c))))
    (hS : ∀ c < n + 1, S c = (X c ^^ Y c ^^ CR c))
    (hC0 : C 0 = false)
    (hC : ∀ c, c + 1 < n + 1 → C (c + 1) = ((X c && Y c) || (CR c && (X c ^^ Y c)))) :
    ∃ q, bfVal S (n + 1) + bfVal C (n + 1) + 2 ^ (n + 1) * q =
      (bfVal SL (n + 1) + bfVal CL (n + 1)) + (bfVal SR (n + 1) + bfVal CR (n + 1)) := by
  have h1 := csa_row n SL CL SR X (fun c => (SL c && CL c) || (SR c && (SL c ^^ CL c))) Y
    hX (fun _ _ => rfl) hY0 hY
  have h2 := csa_row n X Y CR S (fun c => (X c && Y c) || (CR c && (X c ^^ Y c))) C
    hS (fun _ _ => rfl) hC0 hC
  refine ⟨(((SL n && CL n) || (SR n && (SL n ^^ CL n))).toNat) +
    ((X n && Y n) || (CR n && (X n ^^ Y n))).toNat, ?_⟩
  simp only [Nat.mul_add] at h1 h2 ⊢
  generalize 2 ^ (n + 1) = P at *
  omega

/-- `csum V s n = V s + V (s + 1) + … + V (s + n - 1)`: the sum of `n` consecutive rows from row `s`. -/
def csum (V : Nat → Nat) : Nat → Nat → Nat
  | _, 0 => 0
  | s, n + 1 => csum V s n + V (s + n)

theorem csum_zero (V : Nat → Nat) (s : Nat) : csum V s 0 = 0 := rfl

theorem csum_succ (V : Nat → Nat) (s n : Nat) : csum V s (n + 1) = csum V s n + V (s + n) := rfl

/-- The first row off the front. -/
theorem csum_front (V : Nat → Nat) (n : Nat) : ∀ s, csum V s (n + 1) = V s + csum V (s + 1) n := by
  induction n with
  | zero => intro s; simp [csum]
  | succ n ih =>
    intro s
    have e : s + 1 + n = s + (n + 1) := by omega
    have e2 : csum V (s + 1) (n + 1) = csum V (s + 1) n + V (s + 1 + n) := rfl
    rw [csum, ih s, e2, e]
    omega

/-- Three rows off the front. -/
theorem csum_front3 (V : Nat → Nat) (n s : Nat) :
    csum V s (n + 3) = V s + V (s + 1) + V (s + 2) + csum V (s + 3) n := by
  rw [csum_front, csum_front, csum_front]
  simp only [Nat.add_assoc, Nat.reduceAdd]

/-- Rows equal modulo `M` have sums equal modulo `M`. -/
theorem csum_mod (V G : Nat → Nat) (M n : Nat) (h : ∀ k, k < n → V k = G k % M) :
    csum V 0 n % M = csum G 0 n % M := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [csum, Nat.zero_add]
    rw [Nat.add_mod, ih (fun k hk => h k (by omega)), h n (by omega), Nat.mod_mod, ← Nat.add_mod]

/-- **The carry-save tape** (`R ≥ 2` rows of `W` bits at the start): adder `g < R - 2` reads rows `3g`, `3g+1`,
`3g+2` and appends its sum row at `R + 2g` and its carry row, shifted one column, at `R + 1 + 2g`. The two rows left
at `3R - 6` and `3R - 5` have the sum of the `R` first rows, modulo `2^W`. -/
theorem tape_sum (W R : Nat) (hW : 1 ≤ W) (hR : 2 ≤ R) (T : Nat → Nat → Bool)
    (hsum : ∀ g, g < R - 2 → ∀ c, c < W →
      T (R + 2 * g) c = (T (3 * g) c ^^ T (3 * g + 1) c ^^ T (3 * g + 2) c))
    (hcar0 : ∀ g, g < R - 2 → T (R + 1 + 2 * g) 0 = false)
    (hcar : ∀ g, g < R - 2 → ∀ c, c < W - 1 →
      T (R + 1 + 2 * g) (c + 1) = ((T (3 * g) c && T (3 * g + 1) c) ||
        (T (3 * g + 2) c && (T (3 * g) c ^^ T (3 * g + 1) c)))) :
    (bfVal (T (3 * R - 6)) W + bfVal (T (3 * R - 5)) W) % 2 ^ W =
      csum (fun m => bfVal (T m) W) 0 R % 2 ^ W := by
  obtain ⟨n, hn⟩ : ∃ n, W = n + 1 := ⟨W - 1, by omega⟩
  let V : Nat → Nat := fun m => bfVal (T m) W
  have hcsa : ∀ g, g < R - 2 → ∃ q, V (R + 2 * g) + V (R + 1 + 2 * g) + 2 ^ W * q =
      V (3 * g) + V (3 * g + 1) + V (3 * g + 2) := by
    intro g hg
    have h := csa_row n (T (3 * g)) (T (3 * g + 1)) (T (3 * g + 2)) (T (R + 2 * g))
      (fun c => (T (3 * g) c && T (3 * g + 1) c) || (T (3 * g + 2) c && (T (3 * g) c ^^ T (3 * g + 1) c)))
      (T (R + 1 + 2 * g))
      (fun c hc => hsum g hg c (by omega)) (fun _ _ => rfl) (hcar0 g hg)
      (fun c hc => hcar g hg c (by omega))
    rw [← hn] at h
    exact ⟨_, by simp only [V]; omega⟩
  have hwin : ∀ g, g ≤ R - 2 → csum V (3 * g) (R - g) % 2 ^ W = csum V 0 R % 2 ^ W := by
    intro g
    induction g with
    | zero => intro _; simp
    | succ g ih =>
      intro hg
      have ih := ih (by omega)
      obtain ⟨q, hq⟩ := hcsa g (by omega)
      have e1 : csum V (3 * g) (R - g) = V (3 * g) + V (3 * g + 1) + V (3 * g + 2) +
          csum V (3 * g + 3) (R - 3 - g) := by
        rw [show R - g = (R - 3 - g) + 3 by omega, csum_front3]
      have e2 : csum V (3 * (g + 1)) (R - (g + 1)) =
          csum V (3 * g + 3) (R - 3 - g) + V (R + 2 * g) + V (R + 1 + 2 * g) := by
        rw [show R - (g + 1) = (R - 3 - g) + 2 by omega, show 3 * (g + 1) = 3 * g + 3 by omega]
        show csum V (3 * g + 3) (R - 3 - g + 1) + V (3 * g + 3 + (R - 3 - g + 1)) = _
        show csum V (3 * g + 3) (R - 3 - g) + V (3 * g + 3 + (R - 3 - g)) +
          V (3 * g + 3 + (R - 3 - g + 1)) = _
        rw [show 3 * g + 3 + (R - 3 - g) = R + 2 * g by omega,
          show 3 * g + 3 + (R - 3 - g + 1) = R + 1 + 2 * g by omega]
      rw [e1] at ih
      rw [e2]
      have h3 : (csum V (3 * g + 3) (R - 3 - g) + V (R + 2 * g) + V (R + 1 + 2 * g) +
          2 ^ W * q) % 2 ^ W =
          (V (3 * g) + V (3 * g + 1) + V (3 * g + 2) + csum V (3 * g + 3) (R - 3 - g)) % 2 ^ W := by
        congr 1; omega
      rw [Nat.add_mul_mod_self_left] at h3
      rw [h3, ih]
  have hlast := hwin (R - 2) (Nat.le_refl _)
  rw [show R - (R - 2) = 2 by omega] at hlast
  have e3 : csum V (3 * (R - 2)) 2 = V (3 * R - 6) + V (3 * R - 5) := by
    show csum V (3 * (R - 2)) 0 + V (3 * (R - 2) + 0) + V (3 * (R - 2) + 1) = _
    rw [show 3 * (R - 2) + 0 = 3 * R - 6 by omega, show 3 * (R - 2) + 1 = 3 * R - 5 by omega]
    simp [csum]
  rw [e3] at hlast
  exact hlast

/-- **The final adder of a multiplier**: a ripple row with carry-in `0` whose top carry is dropped computes the sum
of its two rows modulo `2^W`. -/
theorem ripple_mod {W : Nat} (x y : Nat → Bool) (p : BitVec W) (K : Nat → Bool) (hK0 : K 0 = false)
    (hp : ∀ c < W, p.getLsbD c = (x c ^^ y c ^^ K c))
    (hK : ∀ c < W, K (c + 1) = ((x c && y c) || (K c && (x c ^^ y c)))) :
    p.toNat = (bfVal x W + bfVal y W) % 2 ^ W := by
  have hrip := ripple_row W x y (fun c => x c ^^ y c) p.getLsbD K (fun _ _ => rfl) hp hK
  rw [hK0, bfVal_bv] at hrip
  simp only [Bool.toNat_false, Nat.add_zero] at hrip
  exact (sum_split p.isLt hrip.symm).1

end CombLib

/-! ## 3. XOR sums and carry-less products -/

namespace XorSum

open LeanModels.Sv.XorSum

theorem bx_succ (f : Nat → Bool) (n : Nat) : bx f (n + 1) = (bx f n ^^ f n) := rfl

theorem bx_congr {f g : Nat → Bool} {n : Nat} (h : ∀ j, j < n → f j = g j) : bx f n = bx g n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [bx]; rw [ih (fun j hj => h j (by omega)), h n (by omega)]

/-- Terms `n ≤ j < m` that are `false` do not change the sum. -/
theorem bx_trunc {f : Nat → Bool} {n m : Nat} (hnm : n ≤ m) (h : ∀ j, n ≤ j → j < m → f j = false) :
    bx f m = bx f n := by
  induction m with
  | zero =>
    have : n = 0 := by omega
    subst this; rfl
  | succ m ih =>
    by_cases hn : n = m + 1
    · subst hn; rfl
    · simp only [bx]
      rw [ih (by omega) (fun j hj1 hj2 => h j hj1 (by omega)), h m (by omega) (by omega)]
      simp

theorem bx_false {f : Nat → Bool} {n : Nat} (h : ∀ t, t < n → f t = false) : bx f n = false := by
  induction n with
  | zero => rfl
  | succ n ih => rw [bx_succ, ih (fun t ht => h t (by omega)), h n (by omega)]; rfl

/-- A sum over `m + n` terms, split at `m`. -/
theorem bx_add (f : Nat → Bool) (m n : Nat) :
    bx f (m + n) = (bx f m ^^ bx (fun t => f (m + t)) n) := by
  induction n with
  | zero => simp [bx]
  | succ n ih =>
    rw [← Nat.add_assoc, bx_succ, ih, bx_succ]
    cases bx f m <;> cases bx (fun t => f (m + t)) n <;> cases f (m + n) <;> rfl

theorem bx_xor (f g : Nat → Bool) (n : Nat) :
    bx (fun t => f t ^^ g t) n = (bx f n ^^ bx g n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [bx_succ, ih, bx_succ, bx_succ]
    cases bx f n <;> cases bx g n <;> cases f n <;> cases g n <;> rfl

theorem bx_and (c : Bool) (f : Nat → Bool) (n : Nat) :
    bx (fun t => c && f t) n = (c && bx f n) := by
  induction n with
  | zero => simp [bx]
  | succ n ih =>
    rw [bx_succ, ih, bx_succ]
    cases c <;> cases bx f n <;> cases f n <;> rfl

/-- The inner sum of a carry-less product: one term `j = k - i` survives. -/
theorem bx_pair (i k : Nat) (x : Bool) (c : Nat → Bool) (n : Nat) :
    bx (fun j => decide (i + j = k) && x && c j) n = (decide (i ≤ k ∧ k - i < n) && x && c (k - i)) := by
  induction n with
  | zero => simp [bx]
  | succ n ih =>
    simp only [bx, ih]
    by_cases h : i + n = k
    · have h1 : k - i = n := by omega
      have h3 : i ≤ k ∧ k - i < n + 1 := by omega
      simp [h, h1, h3]
    · have h4 : (decide (i ≤ k ∧ k - i < n + 1)) = (decide (i ≤ k ∧ k - i < n)) := by
        apply decide_eq_decide.mpr; omega
      have h5 : decide (i + n = k) = false := by simp [h]
      rw [h5, h4]; simp

/-- The carry-less product of two `n`-bit operands, bit `k`: the XOR over `i + j = k`, `i, j < n`, of
`A i && B j`. -/
def cl (n : Nat) (A B : Nat → Bool) (k : Nat) : Bool :=
  bx (fun i => bx (fun j => decide (i + j = k) && A i && B j) n) n

theorem cl_congr {n : Nat} {A A' B B' : Nat → Bool} (hA : ∀ i, i < n → A i = A' i)
    (hB : ∀ j, j < n → B j = B' j) (k : Nat) : cl n A B k = cl n A' B' k := by
  unfold cl
  apply bx_congr
  intro i hi
  apply bx_congr
  intro j hj
  rw [hA i hi, hB j hj]

/-- Bits `k ≥ 2n - 1` of an `n`-bit product are `false`. -/
theorem cl_big {n : Nat} {A B : Nat → Bool} {k : Nat} (hk : 2 * n ≤ k + 1) : cl n A B k = false := by
  unfold cl
  apply bx_false
  intro i hi
  apply bx_false
  intro j hj
  have : ¬ (i + j = k) := by omega
  simp [this]

/-- A double sum shifted by `s`: only `k ≥ s` sees it, at `k - s`. -/
theorem cl_shift (n s k : Nat) (P Q : Nat → Bool) :
    bx (fun i => bx (fun j => decide (i + j + s = k) && P i && Q j) n) n =
      (decide (s ≤ k) && cl n P Q (k - s)) := by
  by_cases h : s ≤ k
  · have e : ∀ i j, decide (i + j + s = k) = decide (i + j = k - s) := by
      intro i j; apply decide_eq_decide.mpr; omega
    simp only [e, h, decide_true, Bool.true_and]
    rfl
  · have e : ∀ i j, decide (i + j + s = k) = false := by
      intro i j; simp; omega
    have h' : decide (s ≤ k) = false := by simp; omega
    simp only [e, h', Bool.false_and]
    apply bx_false; intro i hi; apply bx_false; intro j hj; rfl

/-- Operands that vanish from `N` on: the sums over `M ≥ N` positions see only the first `N`. -/
theorem cl_trunc {N M : Nat} (hNM : N ≤ M) {A B : Nat → Bool} (hA : ∀ i, N ≤ i → A i = false)
    (hB : ∀ j, N ≤ j → B j = false) (k : Nat) : cl M A B k = cl N A B k := by
  unfold cl
  have inner : ∀ i, bx (fun j => decide (i + j = k) && A i && B j) M =
      bx (fun j => decide (i + j = k) && A i && B j) N := by
    intro i
    apply bx_trunc hNM
    intro j hj _
    rw [hB j hj]; simp
  simp only [inner]
  apply bx_trunc hNM
  intro i hi _
  rw [bx_false]
  intro j hj
  rw [hA i hi]; simp

/-- The product of the half sums is the sum of the four half products. -/
theorem cl_sum (H : Nat) (X Y : Nat → Bool) (m : Nat) :
    cl H (fun i => X i ^^ X (H + i)) (fun j => Y j ^^ Y (H + j)) m =
      (cl H X Y m ^^ (cl H X (fun j => Y (H + j)) m ^^ (cl H (fun i => X (H + i)) Y m ^^
        cl H (fun i => X (H + i)) (fun j => Y (H + j)) m))) := by
  unfold cl
  have e : ∀ i j, (decide (i + j = m) && (X i ^^ X (H + i)) && (Y j ^^ Y (H + j))) =
      ((decide (i + j = m) && X i && Y j) ^^ ((decide (i + j = m) && X i && Y (H + j)) ^^
        ((decide (i + j = m) && X (H + i) && Y j) ^^ (decide (i + j = m) && X (H + i) && Y (H + j))))) := by
    intro i j
    cases decide (i + j = m) <;> cases X i <;> cases X (H + i) <;> cases Y j <;> cases Y (H + j) <;> rfl
  simp only [e, bx_xor]

/-- **One Karatsuba split** of a `2H`-bit carry-less product into its four half products. -/
theorem karatsuba (H : Nat) (X Y : Nat → Bool) (k : Nat) :
    cl (H + H) X Y k =
      (cl H X Y k ^^
        ((decide (H ≤ k) && cl H X (fun j => Y (H + j)) (k - H)) ^^
          ((decide (H ≤ k) && cl H (fun i => X (H + i)) Y (k - H)) ^^
            (decide (H + H ≤ k) && cl H (fun i => X (H + i)) (fun j => Y (H + j)) (k - (H + H)))))) := by
  have h1 : ∀ i, bx (fun j => decide (i + j = k) && X i && Y j) (H + H) =
      (bx (fun j => decide (i + j = k) && X i && Y j) H ^^
        bx (fun u => decide (i + (H + u) = k) && X i && Y (H + u)) H) := fun i => bx_add _ H H
  have hA01 : bx (fun i => bx (fun u => decide (i + (H + u) = k) && X i && Y (H + u)) H) H =
      (decide (H ≤ k) && cl H X (fun j => Y (H + j)) (k - H)) := by
    have e : ∀ i u, decide (i + (H + u) = k) = decide (i + u + H = k) := by
      intro i u; apply decide_eq_decide.mpr; omega
    simp only [e]
    exact cl_shift H H k X (fun j => Y (H + j))
  have hA10 : bx (fun t => bx (fun u => decide (H + t + u = k) && X (H + t) && Y u) H) H =
      (decide (H ≤ k) && cl H (fun i => X (H + i)) Y (k - H)) := by
    have e : ∀ t u, decide (H + t + u = k) = decide (t + u + H = k) := by
      intro t u; apply decide_eq_decide.mpr; omega
    simp only [e]
    exact cl_shift H H k (fun i => X (H + i)) Y
  have hA11 : bx (fun t => bx (fun u => decide (H + t + (H + u) = k) && X (H + t) && Y (H + u)) H) H =
      (decide (H + H ≤ k) && cl H (fun i => X (H + i)) (fun j => Y (H + j)) (k - (H + H))) := by
    have e : ∀ t u, decide (H + t + (H + u) = k) = decide (t + u + (H + H) = k) := by
      intro t u; apply decide_eq_decide.mpr; omega
    simp only [e]
    exact cl_shift H (H + H) k (fun i => X (H + i)) (fun j => Y (H + j))
  show bx (fun i => bx (fun j => decide (i + j = k) && X i && Y j) (H + H)) (H + H) = _
  rw [bx_add]
  simp only [h1, bx_xor]
  rw [hA01, hA10, hA11]
  have hL : cl H X Y k = bx (fun i => bx (fun j => decide (i + j = k) && X i && Y j) H) H := rfl
  rw [hL]
  simp only [Bool.xor_assoc]

/-- **One Karatsuba step**: the middle terms from the product of the half sums. -/
theorem karatsuba_full (H : Nat) (X Y : Nat → Bool) (k : Nat) :
    cl (H + H) X Y k =
      (cl H X Y k ^^
        ((decide (H ≤ k) && (cl H (fun i => X i ^^ X (H + i)) (fun j => Y j ^^ Y (H + j)) (k - H) ^^
            cl H X Y (k - H) ^^ cl H (fun i => X (H + i)) (fun j => Y (H + j)) (k - H))) ^^
          (decide (H + H ≤ k) && cl H (fun i => X (H + i)) (fun j => Y (H + j)) (k - (H + H))))) := by
  rw [karatsuba, cl_sum]
  generalize cl H X Y k = l0
  generalize cl H X Y (k - H) = l1
  generalize cl H X (fun j => Y (H + j)) (k - H) = a
  generalize cl H (fun i => X (H + i)) Y (k - H) = b
  generalize cl H (fun i => X (H + i)) (fun j => Y (H + j)) (k - H) = h1
  generalize cl H (fun i => X (H + i)) (fun j => Y (H + j)) (k - (H + H)) = h2
  generalize decide (H ≤ k) = c1
  generalize decide (H + H ≤ k) = c2
  cases l0 <;> cases l1 <;> cases a <;> cases b <;> cases h1 <;> cases h2 <;> cases c1 <;> cases c2 <;> rfl

/-- **A Karatsuba node, column by column**: the low product `PL`, the high product `PH` and the middle product
`PM` (of the half sums), each `2H - 1` bits, combined into the `4H - 1` columns `PF` as
`PF = PL + x^H (PM + PL + PH) + x^2H PH`, give the `2H`-bit product. -/
theorem karatsuba_cols {H : Nat} (hH : 1 ≤ H) {X Y : Nat → Bool} {PL PH PM PF : Nat → Bool}
    (hL : ∀ k, k < 2 * H - 1 → PL k = cl H X Y k)
    (hHh : ∀ k, k < 2 * H - 1 → PH k = cl H (fun i => X (H + i)) (fun j => Y (H + j)) k)
    (hM : ∀ k, k < 2 * H - 1 → PM k = cl H (fun i => X i ^^ X (H + i)) (fun j => Y j ^^ Y (H + j)) k)
    (c0 : ∀ i, i < H → PF i = PL i)
    (c1 : ∀ i, i + 1 < H → PF (H + i) = (PL (H + i) ^^ (PM i ^^ PL i ^^ PH i)))
    (c1' : PF (2 * H - 1) = (PM (H - 1) ^^ PL (H - 1) ^^ PH (H - 1)))
    (c2 : ∀ i, i + 1 < H → PF (2 * H + i) = (PH i ^^ (PM (H + i) ^^ PL (H + i) ^^ PH (H + i))))
    (c3 : ∀ i, i < H → PF (3 * H - 1 + i) = PH (H - 1 + i)) :
    ∀ k, k < 4 * H - 1 → PF k = cl (H + H) X Y k := by
  intro k hk
  rw [karatsuba_full]
  have big : ∀ (A B : Nat → Bool) m, 2 * H - 1 ≤ m → cl H A B m = false :=
    fun A B m hm => cl_big (by omega)
  by_cases h1 : k < H
  · have d1 : decide (H ≤ k) = false := by simp; omega
    have d2 : decide (H + H ≤ k) = false := by simp; omega
    rw [c0 k h1, hL k (by omega), d1, d2]; simp
  by_cases h2 : k < 2 * H - 1
  · obtain ⟨i, rfl⟩ : ∃ i, k = H + i := ⟨k - H, by omega⟩
    have d1 : decide (H ≤ H + i) = true := by simp
    have d2 : decide (H + H ≤ H + i) = false := by simp; omega
    have e1 : H + i - H = i := by omega
    rw [c1 i (by omega), hL (H + i) h2, hL i (by omega), hHh i (by omega), hM i (by omega), d1, d2, e1]
    simp
  by_cases h3 : k = 2 * H - 1
  · subst h3
    have d1 : decide (H ≤ 2 * H - 1) = true := by simp; omega
    have d2 : decide (H + H ≤ 2 * H - 1) = false := by simp; omega
    have e1 : 2 * H - 1 - H = H - 1 := by omega
    rw [c1', hM (H - 1) (by omega), hL (H - 1) (by omega), hHh (H - 1) (by omega), d1, d2, e1,
      big X Y (2 * H - 1) (by omega)]
    simp
  by_cases h4 : k < 3 * H - 1
  · obtain ⟨i, rfl⟩ : ∃ i, k = 2 * H + i := ⟨k - 2 * H, by omega⟩
    have d1 : decide (H ≤ 2 * H + i) = true := by simp; omega
    have d2 : decide (H + H ≤ 2 * H + i) = true := by simp; omega
    have e1 : 2 * H + i - H = H + i := by omega
    have e2 : 2 * H + i - (H + H) = i := by omega
    rw [c2 i (by omega), hHh i (by omega), hM (H + i) (by omega), hL (H + i) (by omega),
      hHh (H + i) (by omega), d1, d2, e1, e2, big X Y (2 * H + i) (by omega)]
    simp only [Bool.true_and, Bool.false_xor]
    generalize cl H (fun i => X (H + i)) (fun j => Y (H + j)) i = a
    generalize cl H (fun i => X i ^^ X (H + i)) (fun j => Y j ^^ Y (H + j)) (H + i) = m
    generalize cl H X Y (H + i) = l
    generalize cl H (fun i => X (H + i)) (fun j => Y (H + j)) (H + i) = h
    cases a <;> cases m <;> cases l <;> cases h <;> rfl
  · obtain ⟨i, rfl⟩ : ∃ i, k = 3 * H - 1 + i := ⟨k - (3 * H - 1), by omega⟩
    have d1 : decide (H ≤ 3 * H - 1 + i) = true := by simp; omega
    have d2 : decide (H + H ≤ 3 * H - 1 + i) = true := by simp; omega
    have e1 : 3 * H - 1 + i - H = 2 * H - 1 + i := by omega
    have e2 : 3 * H - 1 + i - (H + H) = H - 1 + i := by omega
    have bm : cl H (fun i => X i ^^ X (H + i)) (fun j => Y j ^^ Y (H + j)) (2 * H - 1 + i) = false :=
      big _ _ _ (by omega)
    have bl : cl H X Y (2 * H - 1 + i) = false := big _ _ _ (by omega)
    have bh : cl H (fun i => X (H + i)) (fun j => Y (H + j)) (2 * H - 1 + i) = false := big _ _ _ (by omega)
    have bl0 : cl H X Y (3 * H - 1 + i) = false := big _ _ _ (by omega)
    rw [c3 i (by omega), hHh (H - 1 + i) (by omega), d1, d2, e1, e2, bm, bl, bh, bl0]
    simp

end XorSum

/-! ## 4. Adder results as the task states them -/

namespace Lib

/-- A 1-bit vector is the `ofBool` of its only bit (core: `BitVec.setWidth_one` with `BitVec.setWidth_eq`). -/
theorem bv1_eq_ofBool (v : BitVec 1) : v = BitVec.ofBool (v.getLsbD 0) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  obtain rfl : i = 0 := by omega
  simp

/-- `x + y + ci` at width `N ≥ 1`, with the carry-in truncated to `N` bits, is `(x + y + ci) mod 2^N`. -/
theorem sum_eq_ofNat {N : Nat} (hN : 1 ≤ N) (x y : BitVec N) (ci : Bool) :
    x + y + (BitVec.ofBool ci).setWidth N =
      BitVec.ofNat N (x.toNat + y.toNat + (BitVec.ofBool ci).toNat) := by
  apply BitVec.eq_of_toNat_eq
  have h2 : 2 ≤ 2 ^ N := Nat.pow_le_pow_right (n := 2) (by decide) hN
  have hc : ci.toNat < 2 ^ N := by have := Bool.toNat_le ci; omega
  simp only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofBool, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt hc, Nat.mod_add_mod]

/-- The carry out `2^N ≤ t` is `t / 2^N` on one bit, for any `t < 2 · 2^N`. -/
theorem carry_eq_ofNat {N : Nat} (t : Nat) (ht : t < 2 * 2 ^ N) :
    BitVec.ofBool (decide (2 ^ N ≤ t)) = BitVec.ofNat 1 (t / 2 ^ N) := by
  by_cases h : 2 ^ N ≤ t
  · have hq : t / 2 ^ N = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
    simp [h, hq]
  · have hq : t / 2 ^ N = 0 := Nat.div_eq_of_lt (by omega)
    simp [h, hq]

end Lib

/-! ## 5. Reading the ports, and the statement -/

/-- **An output port read back bit by bit.** A signal bound to `v` of width `W`, all of whose bits are known and
equal to the bits of `y`, holds `ofBitVec y`. -/
theorem SvState.lookup_eq_ofBitVec_of_bits {st : SvState} {n : String} {v : LVec} {W : Nat} {y : BitVec W}
    (hv : SvState.lookup st n = some v) (hw : v.width = W) (hk : ∀ k, k < W → KnownBit st n k)
    (hb : ∀ k, k < W → st.boolAt n k = y.getLsbD k) :
    SvState.lookup st n = some (LVec.ofBitVec y) := by
  rw [hv, SvState.lookup_eq_ofBitVec_bv hv hw hk]
  congr 2
  apply BitVec.eq_of_getLsbD_eq
  intro k hk'
  rw [XF.getLsbD_bv hk', hb k hk']

/-- **An output port read back as a word**: the same, given the word `XF.bv W (st.boolAt n)` of its bits. -/
theorem SvState.lookup_eq_ofBitVec_of_bv {st : SvState} {n : String} {v : LVec} {W : Nat} {y : BitVec W}
    (hv : SvState.lookup st n = some v) (hw : v.width = W) (hk : ∀ k, k < W → KnownBit st n k)
    (hy : XF.bv W (st.boolAt n) = y) :
    SvState.lookup st n = some (LVec.ofBitVec y) := by
  rw [hv, SvState.lookup_eq_ofBitVec_bv hv hw hk, hy]

/-- **The statement from its three parts**: at every parameter value in range, the comb profile with acyclicity
(and a third fact `P N`: the shared obligations `SharedObl design.pdesign [N]` that `sv_structure` proves on
request, or `True`), the interface, and the settled-state lemma (`CombTask.satisfiedAt_of_comb` at each `N`). The
settled-state lemma is given the three facts as hypotheses, because `sv_equations` reads `CombDesign (X.sem N)` and
the shared obligations from the context: `intro N hN hc ha hso st heqs hs v hv`. -/
theorem CombTask.statement_of_comb {t : CombTask} {sem : Nat → Design2} {P : Nat → Prop}
    (hstruct : ∀ N, t.inRange N → CombDesign (sem N) ∧ Acyclic (sem N) ∧ P N)
    (hI : ∀ N, t.inRange N → CombDesign (sem N) → t.Interface N (sem N))
    (hset : ∀ N, t.inRange N → CombDesign (sem N) → Acyclic (sem N) → P N → ∀ st, CombEqs (sem N) st →
      StateShape (sem N) st → ∀ v, HoldAll st (t.inputs N) v → HoldAll st (t.outputs N) (t.fn N v)) :
    t.Statement sem := by
  intro N hN
  obtain ⟨hc, ha, hp⟩ := hstruct N hN
  exact CombTask.satisfiedAt_of_comb (hI N hN hc) hc ha (hset N hN hc ha hp)

/-! ## 6. The by-hand route

A design the comb tactics refuse is proved by hand (`PROVING.md` section 5): its instantiation pinned as a list of
processes `procs`, each a continuous assign to one window `win p`. `LeafProcs` records that, and gives the comb
profile and acyclicity from facts about the list alone. -/

/-- The processes of `d` are the list `procs`, and each is a continuous assign whose target has the one write
window `win p`. -/
structure LeafProcs (d : Design2) (procs : List Process2) (win : Process2 → Win) : Prop where
  procs_eq : d.processes.toList = procs
  leaf : ∀ p ∈ procs, ∃ t e, p = .assign t e ∧ t.windows? d = some [win p]

/-- The rank of process `k` of `d`: `rk` of the process (`0` past the end). -/
def procRank (d : Design2) (rk : Process2 → Nat) (k : Nat) : Nat :=
  match d.processes[k]? with
  | some p => rk p
  | none => 0

namespace LeafProcs

variable {d : Design2} {procs : List Process2} {win : Process2 → Win}

/-- A process of the list sits at some position of `d`. -/
theorem getElem?_of_mem (h : LeafProcs d procs win) {p : Process2} (hp : p ∈ procs) :
    ∃ k : Nat, d.processes[k]? = some p := by
  rw [← h.procs_eq, List.mem_iff_getElem?] at hp
  obtain ⟨k, hk⟩ := hp
  rw [Array.getElem?_toList] at hk
  exact ⟨k, hk⟩

/-- Every process of `d` is in the list. -/
theorem mem_of_getElem? (h : LeafProcs d procs win) {k : Nat} {p : Process2}
    (hk : d.processes[k]? = some p) : p ∈ procs := by
  rw [← h.procs_eq, List.mem_iff_getElem?]
  exact ⟨k, by rw [Array.getElem?_toList]; exact hk⟩

/-- The write windows of an assign of the list: its one window. -/
theorem wins_eq (h : LeafProcs d procs win) {p : Process2} (hp : p ∈ procs) {t : Lhs2} {e : Expr2}
    (he : p = .assign t e) : t.wins d = [win p] := by
  obtain ⟨t', e', he', hw⟩ := h.leaf p hp
  rw [he, Process2.assign.injEq] at he'
  obtain ⟨rfl, -⟩ := he'
  exact Lhs2.wins_of_windows? hw

/-- What process `j` writes: the window of its entry. -/
theorem writes (h : LeafProcs d procs win) {j : Nat} {w : Win} (hw : d.Writes j w) :
    ∃ p, d.processes[j]? = some p ∧ p ∈ procs ∧ w = win p := by
  obtain ⟨t, e, hp, hmem⟩ := hw
  have hm := h.mem_of_getElem? hp
  rw [h.wins_eq hm rfl, List.mem_singleton] at hmem
  exact ⟨_, hp, hm, hmem⟩

/-- Pairwise disjoint windows in list order give the one-driver condition. -/
theorem disjoint (h : LeafProcs d procs win)
    (hpw : (procs.map win).Pairwise fun a b => Win.overlaps a b = false) :
    ∀ i j wi wj, i ≠ j → d.Writes i wi → d.Writes j wj → Win.overlaps wi wj = false := by
  intro i j wi wj hij hi hj
  obtain ⟨p, hp, -, rfl⟩ := h.writes hi
  obtain ⟨q, hq, -, rfl⟩ := h.writes hj
  have hpw' : procs.Pairwise fun p q => Win.overlaps (win p) (win q) = false := List.pairwise_map.mp hpw
  rw [← h.procs_eq, List.pairwise_iff_getElem] at hpw'
  rw [← Array.getElem?_toList, List.getElem?_eq_some_iff] at hp hq
  obtain ⟨hil, hp⟩ := hp
  obtain ⟨hjl, hq⟩ := hq
  rcases Nat.lt_or_gt_of_ne hij with hlt | hlt
  · have := hpw' i j hil hjl hlt
    rw [hp, hq] at this
    exact this
  · have := hpw' j i hjl hil hlt
    rw [hp, hq] at this
    rw [Win.overlaps_comm]
    exact this

/-- Every write window has positive width, when every window of the list has (the side condition of
`PDesign.instantiateGD2_of_combDesign`). -/
theorem writes_pos (h : LeafProcs d procs win) (hpos : ∀ p ∈ procs, 0 < (win p).2.2) :
    ∀ i n lo w, d.Writes i (n, lo, w) → 0 < w := by
  intro i n lo w hw
  obtain ⟨p, -, hm, hpw⟩ := h.writes hw
  have := hpos p hm
  rw [← hpw] at this
  exact this

/-- **The comb profile** of a design whose processes are assigns to one window each, from facts about the list:
the windows are pairwise disjoint and inside their signals, no window is of an input, every right-hand side is
free of unsupported nodes and names only declared signals; and from facts about the declarations: distinct names,
no initializer, no 2-state input. -/
theorem combDesign (h : LeafProcs d procs win)
    (hnodup : (d.decls.toList.map Decl.name).Nodup)
    (hpw : (procs.map win).Pairwise fun a b => Win.overlaps a b = false)
    (hwidth : ∀ p ∈ procs, ∃ dw, d.declWidth (win p).1 = some dw ∧ (win p).2.1 + (win p).2.2 ≤ dw)
    (hin : ∀ p ∈ procs, (win p).1 ∉ d.inputNames.toList)
    (hfree : ∀ p ∈ procs, ∀ t e, p = .assign t e → e.unsupportedFree = true)
    (hdecl : ∀ p ∈ procs, ∀ t e, p = .assign t e → ∀ x ∈ e.idents, x ∈ d.decls.toList.map Decl.name)
    (hinit : ∀ dc ∈ d.decls.toList, dc.init = none)
    (hfour : ∀ dc ∈ d.decls.toList, dc.isInput = true → dc.twoState = false) :
    CombDesign d where
  nodup := hnodup
  assign := by
    intro j p hp
    obtain ⟨t, e, rfl, hw⟩ := h.leaf p (h.mem_of_getElem? hp)
    exact ⟨t, e, _, rfl, hw⟩
  inWidth := by
    intro j n lo w hw
    obtain ⟨p, -, hm, hpw⟩ := h.writes hw
    obtain ⟨dw, hdw, hle⟩ := hwidth p hm
    rw [← hpw] at hdw hle
    exact ⟨dw, hdw, hle⟩
  notInput := by
    rintro n ⟨j, lo, w, hw⟩
    obtain ⟨p, -, hm, hpw⟩ := h.writes hw
    have := hin p hm
    rw [← hpw] at this
    exact this
  disjoint := h.disjoint hpw
  selfDisjoint := by
    intro j t e hp
    rw [h.wins_eq (h.mem_of_getElem? hp) rfl]
    exact List.pairwise_singleton _ _
  rhsFree := fun _ t e hp => hfree _ (h.mem_of_getElem? hp) t e rfl
  rhsDeclared := fun _ t e hp => hdecl _ (h.mem_of_getElem? hp) t e rfl
  initWidth := by
    intro n _ dc hdc _ v hv
    rw [hinit dc hdc] at hv
    cases hv
  inFourState := hfour

/-- **Acyclicity from a rank on the processes**: every read of a process `p` that overlaps the window of a
process `q` of the list has `rk q < rk p`. -/
theorem acyclic (h : LeafProcs d procs win) (rk : Process2 → Nat)
    (hrk : ∀ p ∈ procs, ∀ q ∈ procs, ∀ t e, p = .assign t e → ∀ r ∈ e.reads,
      r.overlaps (win q) = true → rk q < rk p) :
    Acyclic d := by
  refine ⟨procRank d rk, ?_⟩
  intro i j ti ei tj ej wj hi hj hwj ⟨r, hr, hov⟩
  have hmi := h.mem_of_getElem? hi
  have hmj := h.mem_of_getElem? hj
  rw [h.wins_eq hmj rfl, List.mem_singleton] at hwj
  subst hwj
  have hlt := hrk _ hmi _ hmj ti ei rfl r hr hov
  simp only [procRank, hi, hj]
  exact hlt

end LeafProcs

/-! ### Gates on known one-bit values, in `Bool` form -/

section Gates

variable {st : SvState}

/-- Bit `i` of a signal holding a known vector. -/
theorem evalPure2_bit_of_lookup {n : String} {w : Nat} {x : BitVec w} {i : Nat}
    (h : SvState.lookup st n = some (LVec.ofBitVec x)) (hi : i < w) :
    evalPure2 st (.slice (.ident n) i 1) = .ok (LVec.ofBitVec (BitVec.ofBool (x.getLsbD i))) :=
  evalPure2_bit_ofBitVec (evalPure2_ident_ofBitVec h) hi

/-- A part select of a signal whose window is known (the rest of the signal may be unknown). -/
theorem evalPure2_slice_of_extract {n : String} {u : LVec} {lo w : Nat} {x : BitVec w}
    (h : SvState.lookup st n = some u) (hx : u.extract lo w = LVec.ofBitVec x) :
    evalPure2 st (.slice (.ident n) lo w) = .ok (LVec.ofBitVec x) := by
  simp only [evalPure2_slice, evalPure2_ident_of_lookup h, Pure2.res_ok_bind, Pure2.res_pure_eq, hx]

/-- The one-bit literal `1'b0`. -/
theorem evalPure2_lit_l0 : evalPure2 st (.lit { bits := #[Logic.l0] }) =
    .ok (LVec.ofBitVec (BitVec.ofBool false)) := by
  simp only [evalPure2_lit]
  rfl

theorem evalPure2_and_bool {l r : Expr2} {p q : Bool}
    (hl : evalPure2 st l = .ok (LVec.ofBitVec (BitVec.ofBool p)))
    (hr : evalPure2 st r = .ok (LVec.ofBitVec (BitVec.ofBool q))) :
    evalPure2 st (.binary .and l r) = .ok (LVec.ofBitVec (BitVec.ofBool (p && q))) := by
  rw [evalPure2_and_ofBitVec hl hr, BitVec.ofBool_and_ofBool]

theorem evalPure2_or_bool {l r : Expr2} {p q : Bool}
    (hl : evalPure2 st l = .ok (LVec.ofBitVec (BitVec.ofBool p)))
    (hr : evalPure2 st r = .ok (LVec.ofBitVec (BitVec.ofBool q))) :
    evalPure2 st (.binary .or l r) = .ok (LVec.ofBitVec (BitVec.ofBool (p || q))) := by
  rw [evalPure2_or_ofBitVec hl hr, BitVec.ofBool_or_ofBool]

theorem evalPure2_xor_bool {l r : Expr2} {p q : Bool}
    (hl : evalPure2 st l = .ok (LVec.ofBitVec (BitVec.ofBool p)))
    (hr : evalPure2 st r = .ok (LVec.ofBitVec (BitVec.ofBool q))) :
    evalPure2 st (.binary .xor l r) = .ok (LVec.ofBitVec (BitVec.ofBool (p ^^ q))) := by
  rw [evalPure2_xor_ofBitVec hl hr, BitVec.ofBool_xor_ofBool]

end Gates

/-- **A slice assign read back** on a state solving the equations: the window it writes holds its right-hand
side's value, truncated to the window. -/
theorem CombEqs.readback {d : Design2} {st : SvState} (heqs : CombEqs d st) {k : Nat} {n : String}
    {lo w : Nat} {e : Expr2} (hk : d.processes[k]? = some (.assign (.slice n lo w) e))
    {u : LVec} (hu : SvState.lookup st n = some u) {wv : Nat} {x : BitVec wv}
    (he : evalPure2 st e = .ok (LVec.ofBitVec x)) :
    u.extract lo w = LVec.ofBitVec (x.setWidth w) := by
  obtain ⟨old, hold, hext⟩ := CombEqs.extract_slice heqs hk he
  rw [hu, Option.some.injEq] at hold
  subst hold
  rw [hext, LVec.resizeU_ofBitVec]

/-- The same for a one-bit assign of a known bit. -/
theorem CombEqs.readback1 {d : Design2} {st : SvState} (heqs : CombEqs d st) {k : Nat} {n : String}
    {lo : Nat} {e : Expr2} (hk : d.processes[k]? = some (.assign (.slice n lo 1) e))
    {u : LVec} (hu : SvState.lookup st n = some u) {b : Bool}
    (he : evalPure2 st e = .ok (LVec.ofBitVec (BitVec.ofBool b))) :
    u.extract lo 1 = LVec.ofBitVec (BitVec.ofBool b) := by
  rw [CombEqs.readback heqs hk hu he, BitVec.setWidth_eq]

/-- **A window known bit by bit** is the `ofBitVec` of its bits. -/
theorem LVec.extract_eq_ofBitVec_of_bits {v : LVec} {lo k : Nat} {x : BitVec k}
    (h : ∀ j, j < k → v.extract (lo + j) 1 = LVec.ofBitVec (BitVec.ofBool (x.getLsbD j))) :
    v.extract lo k = LVec.ofBitVec x :=
  LVec.eq_ofBitVec_of_extract_one (LVec.width_extract _ _ _) fun j hj => by
    rw [LVec.extract_extract _ (by omega)]
    exact h j hj

#print axioms CombLib.bfVal_eq_val
#print axioms CombLib.tape_sum
#print axioms CombLib.ripple_mod
#print axioms CombLib.node_sum
#print axioms XorSum.karatsuba_cols
#print axioms XorSum.cl_trunc
#print axioms Lib.sum_eq_ofNat
#print axioms SvState.lookup_eq_ofBitVec_of_bits
#print axioms CombTask.statement_of_comb
#print axioms LeafProcs.combDesign
#print axioms LeafProcs.acyclic
#print axioms CombEqs.readback1
#print axioms LVec.extract_eq_ofBitVec_of_bits

end SvGolf
