import SvGolf.CombLemmas
import SvGolf.SpecFacts

/-!
# Tests of `SvGolf.CombLemmas` and `SvGolf.SpecFacts`: every lemma at two sizes

Each lemma of `SvGolf/CombLemmas.lean` and `SvGolf/SpecFacts.lean` applied at two instances of different size
(widths 3 and 8, rows of 4 and 8 columns, tapes of 3 and 5 rows, products of 2 and 4 bits, designs of 2 and 3
processes, …), and where the instance is closed, checked against the definitions by `decide`. Built with the
`tests` library (`tests.lean`).
-/

namespace SvGolfTests.Comb

open LeanModels.Sv SvGolf
open LeanModels.Sv.CombLib SvGolf.CombLib
open LeanModels.Sv.XorSum SvGolf.XorSum

/-! ## 1. Values of bit functions -/

/-- Closed values, from the definition. -/
example : bfVal (fun j => decide (j % 2 = 0)) 4 = 5 := by decide
example : bfVal (fun j => decide (j % 3 = 0)) 7 = 73 := by decide

example (f : Nat → Bool) : bfVal f 3 = XF.val f 3 := bfVal_eq_val f 3
example (f : Nat → Bool) : bfVal f 8 = XF.val f 8 := bfVal_eq_val f 8

example : bfVal (fun _ => false) 3 = 0 := bfVal_false fun _ _ => rfl
example : bfVal (fun j => decide (8 ≤ j)) 8 = 0 := bfVal_false fun j hj => decide_eq_false (by omega)

example (f : Nat → Bool) : bfVal f 3 < 8 := bfVal_lt f 3
example (f : Nat → Bool) : bfVal f 8 < 256 := bfVal_lt f 8

example (f : Nat → Bool) : bfVal f 6 % 2 ^ 3 = bfVal f 3 := bfVal_mod f (by decide)
example (f : Nat → Bool) : bfVal f 8 % 2 ^ 5 = bfVal f 5 := bfVal_mod f (by decide)

example (f : Nat → Bool) : bfVal (fun j => !f j) 3 + bfVal f 3 + 1 = 8 := bfVal_not f 3
example (f : Nat → Bool) : bfVal (fun j => !f j) 8 + bfVal f 8 + 1 = 256 := bfVal_not f 8
example : bfVal (fun j => !decide (j = 0)) 3 = 6 := by decide

example : bfVal (fun j => decide (2 ≤ j ∧ j < 4)) 6 =
    2 ^ 2 * bfVal (fun j => decide (2 ≤ 2 + j ∧ 2 + j < 4)) 2 :=
  bfVal_window _ 2 2 6 (by decide) (fun c hc => decide_eq_false (by omega))
    (fun c hc => decide_eq_false (by omega))
example (f : Nat → Bool) : bfVal (fun j => decide (1 ≤ j ∧ j < 4) && f j) 8 =
    2 ^ 1 * bfVal (fun j => decide (1 ≤ 1 + j ∧ 1 + j < 4) && f (1 + j)) 3 :=
  bfVal_window _ 1 3 8 (by decide) (fun c hc => by simp; omega) (fun c hc => by simp; omega)

example : bfVal (fun c => decide (c = 0) || decide (c = 2)) 3 =
    bfVal (fun c => decide (c = 0)) 3 + bfVal (fun c => decide (c = 2)) 3 :=
  bfVal_or 3 (fun _ => rfl) fun c h1 h2 => by simp at h1 h2; omega
example : bfVal (fun c => decide (c < 3) || decide (6 ≤ c)) 8 =
    bfVal (fun c => decide (c < 3)) 8 + bfVal (fun c => decide (6 ≤ c)) 8 :=
  bfVal_or 8 (fun _ => rfl) fun c h1 h2 => by simp at h1 h2; omega

example : (true ^^ true).toNat + 2 * (true && true).toNat = true.toNat + true.toNat := halfAdder_arith true true
example (x : Bool) : (x ^^ false).toNat + 2 * (x && false).toNat = x.toNat + false.toNat :=
  halfAdder_arith x false

/-! ## 2. Carry-save arithmetic -/

section csa

variable (x y z s cy sh : Nat → Bool)

/-- Rows of 4 and of 8 columns. -/
example (hs : ∀ c < 4, s c = (x c ^^ y c ^^ z c))
    (hcy : ∀ c < 4, cy c = ((x c && y c) || (z c && (x c ^^ y c))))
    (hsh0 : sh 0 = false) (hsh : ∀ c, c + 1 < 4 → sh (c + 1) = cy c) :
    bfVal s 4 + bfVal sh 4 + 2 ^ 4 * (cy 3).toNat = bfVal x 4 + bfVal y 4 + bfVal z 4 :=
  csa_row 3 x y z s cy sh hs hcy hsh0 hsh
example (hs : ∀ c < 8, s c = (x c ^^ y c ^^ z c))
    (hcy : ∀ c < 8, cy c = ((x c && y c) || (z c && (x c ^^ y c))))
    (hsh0 : sh 0 = false) (hsh : ∀ c, c + 1 < 8 → sh (c + 1) = cy c) :
    bfVal s 8 + bfVal sh 8 + 2 ^ 8 * (cy 7).toNat = bfVal x 8 + bfVal y 8 + bfVal z 8 :=
  csa_row 7 x y z s cy sh hs hcy hsh0 hsh

end csa

/-- A closed 3:2 row: `x = 0110`, `y = 0011`, `z = 0101`. -/
def xs (c : Nat) : Bool := decide (c = 1 ∨ c = 2)
def ys (c : Nat) : Bool := decide (c = 0 ∨ c = 1)
def zs (c : Nat) : Bool := decide (c = 0 ∨ c = 2)
def mj (c : Nat) : Bool := (xs c && ys c) || (zs c && (xs c ^^ ys c))
def shf (c : Nat) : Bool := if c = 0 then false else mj (c - 1)

example : bfVal (fun c => xs c ^^ ys c ^^ zs c) 4 + bfVal shf 4 + 2 ^ 4 * (mj 3).toNat =
    bfVal xs 4 + bfVal ys 4 + bfVal zs 4 :=
  csa_row 3 xs ys zs _ mj shf (fun _ _ => rfl) (fun _ _ => rfl) rfl fun c _ => by simp [shf]
example : bfVal (fun c => xs c ^^ ys c ^^ zs c) 4 + bfVal shf 4 + 2 ^ 4 * (mj 3).toNat = 6 + 3 + 5 := by
  decide

section node

variable (SL CL SR CR S C X Y : Nat → Bool)

example (hX : ∀ c < 4, X c = (SL c ^^ CL c ^^ SR c)) (hY0 : Y 0 = false)
    (hY : ∀ c, c + 1 < 4 → Y (c + 1) = ((SL c && CL c) || (SR c && (SL c ^^ CL c))))
    (hS : ∀ c < 4, S c = (X c ^^ Y c ^^ CR c)) (hC0 : C 0 = false)
    (hC : ∀ c, c + 1 < 4 → C (c + 1) = ((X c && Y c) || (CR c && (X c ^^ Y c)))) :
    ∃ q, bfVal S 4 + bfVal C 4 + 2 ^ 4 * q = (bfVal SL 4 + bfVal CL 4) + (bfVal SR 4 + bfVal CR 4) :=
  node_sum 3 SL CL SR CR S C X Y hX hY0 hY hS hC0 hC
example (hX : ∀ c < 8, X c = (SL c ^^ CL c ^^ SR c)) (hY0 : Y 0 = false)
    (hY : ∀ c, c + 1 < 8 → Y (c + 1) = ((SL c && CL c) || (SR c && (SL c ^^ CL c))))
    (hS : ∀ c < 8, S c = (X c ^^ Y c ^^ CR c)) (hC0 : C 0 = false)
    (hC : ∀ c, c + 1 < 8 → C (c + 1) = ((X c && Y c) || (CR c && (X c ^^ Y c)))) :
    ∃ q, bfVal S 8 + bfVal C 8 + 2 ^ 8 * q = (bfVal SL 8 + bfVal CL 8) + (bfVal SR 8 + bfVal CR 8) :=
  node_sum 7 SL CL SR CR S C X Y hX hY0 hY hS hC0 hC

end node

/-- Closed sums of consecutive rows. -/
example : csum (fun m => m * m) 2 3 = 4 + 9 + 16 := by decide
example : csum (fun m => m + 1) 0 5 = 15 := by decide

example (V : Nat → Nat) : csum V 3 0 = 0 := csum_zero V 3
example (V : Nat → Nat) : csum V 3 2 = csum V 3 1 + V 4 := csum_succ V 3 1

example (V : Nat → Nat) : csum V 2 4 = V 2 + csum V 3 3 := csum_front V 3 2
example (V : Nat → Nat) : csum V 0 8 = V 0 + csum V 1 7 := csum_front V 7 0

example (V : Nat → Nat) : csum V 0 3 = V 0 + V 1 + V 2 + csum V 3 0 := csum_front3 V 0 0
example (V : Nat → Nat) : csum V 4 9 = V 4 + V 5 + V 6 + csum V 7 6 := csum_front3 V 6 4

example (V G : Nat → Nat) (h : ∀ k, k < 3 → V k = G k % 4) : csum V 0 3 % 4 = csum G 0 3 % 4 :=
  csum_mod V G 4 3 h
example (V G : Nat → Nat) (h : ∀ k, k < 8 → V k = G k % 16) : csum V 0 8 % 16 = csum G 0 8 % 16 :=
  csum_mod V G 16 8 h

section tape

variable (T : Nat → Nat → Bool)

/-- A tape of 3 rows of 4 bits (one adder), and of 5 rows of 8 bits (three adders). -/
example (hsum : ∀ g, g < 1 → ∀ c, c < 4 → T (3 + 2 * g) c = (T (3 * g) c ^^ T (3 * g + 1) c ^^ T (3 * g + 2) c))
    (hcar0 : ∀ g, g < 1 → T (3 + 1 + 2 * g) 0 = false)
    (hcar : ∀ g, g < 1 → ∀ c, c < 3 → T (3 + 1 + 2 * g) (c + 1) =
      ((T (3 * g) c && T (3 * g + 1) c) || (T (3 * g + 2) c && (T (3 * g) c ^^ T (3 * g + 1) c)))) :
    (bfVal (T 3) 4 + bfVal (T 4) 4) % 2 ^ 4 = csum (fun m => bfVal (T m) 4) 0 3 % 2 ^ 4 :=
  tape_sum 4 3 (by decide) (by decide) T hsum hcar0 hcar
example (hsum : ∀ g, g < 3 → ∀ c, c < 8 → T (5 + 2 * g) c = (T (3 * g) c ^^ T (3 * g + 1) c ^^ T (3 * g + 2) c))
    (hcar0 : ∀ g, g < 3 → T (5 + 1 + 2 * g) 0 = false)
    (hcar : ∀ g, g < 3 → ∀ c, c < 7 → T (5 + 1 + 2 * g) (c + 1) =
      ((T (3 * g) c && T (3 * g + 1) c) || (T (3 * g + 2) c && (T (3 * g) c ^^ T (3 * g + 1) c)))) :
    (bfVal (T 9) 8 + bfVal (T 10) 8) % 2 ^ 8 = csum (fun m => bfVal (T m) 8) 0 5 % 2 ^ 8 :=
  tape_sum 8 5 (by decide) (by decide) T hsum hcar0 hcar

end tape

/-- The final adder at 4 and at 8 bits; closed: `5 + 6 = 11` on 4 bits, `200 + 100 = 300 mod 256` on 8. -/
example (x y K : Nat → Bool) (p : BitVec 4) (hK0 : K 0 = false)
    (hp : ∀ c < 4, p.getLsbD c = (x c ^^ y c ^^ K c))
    (hK : ∀ c < 4, K (c + 1) = ((x c && y c) || (K c && (x c ^^ y c)))) :
    p.toNat = (bfVal x 4 + bfVal y 4) % 2 ^ 4 := ripple_mod x y p K hK0 hp hK
example (x y K : Nat → Bool) (p : BitVec 8) (hK0 : K 0 = false)
    (hp : ∀ c < 8, p.getLsbD c = (x c ^^ y c ^^ K c))
    (hK : ∀ c < 8, K (c + 1) = ((x c && y c) || (K c && (x c ^^ y c)))) :
    p.toNat = (bfVal x 8 + bfVal y 8) % 2 ^ 8 := ripple_mod x y p K hK0 hp hK
example : (bfVal (Nat.testBit 5) 4 + bfVal (Nat.testBit 6) 4) % 2 ^ 4 = (11 : BitVec 4).toNat := by decide
example : (bfVal (Nat.testBit 200) 8 + bfVal (Nat.testBit 100) 8) % 2 ^ 8 = (300 : BitVec 8).toNat := by
  decide

/-! ## 3. XOR sums and carry-less products -/

/-- Closed XOR sums and products, from the definitions: `(x + 1)^2 = x^2 + 1` (2 bits) and
`(x^3 + x + 1)(x^2 + 1) = x^5 + x^2 + x + 1` (4 bits). -/
def two11 (i : Nat) : Bool := decide (i < 2)
def a1011 (i : Nat) : Bool := decide (i = 0 ∨ i = 1 ∨ i = 3)
def a0101 (i : Nat) : Bool := decide (i = 0 ∨ i = 2)

example : bx (fun i => decide (i % 2 = 0)) 5 = true := by decide
example : (List.range 3).map (cl 2 two11 two11) = [true, false, true] := by decide
example : (List.range 7).map (cl 4 a1011 a0101) = [true, true, true, false, false, true, false] := by decide

example (f : Nat → Bool) : bx f 3 = (bx f 2 ^^ f 2) := bx_succ f 2
example (f : Nat → Bool) : bx f 8 = (bx f 7 ^^ f 7) := bx_succ f 7

example (f g : Nat → Bool) (h : ∀ j, j < 3 → f j = g j) : bx f 3 = bx g 3 := bx_congr h
example (f g : Nat → Bool) (h : ∀ j, j < 8 → f j = g j) : bx f 8 = bx g 8 := bx_congr h

example (f : Nat → Bool) (h : ∀ j, 2 ≤ j → j < 5 → f j = false) : bx f 5 = bx f 2 := bx_trunc (by decide) h
example (f : Nat → Bool) (h : ∀ j, 3 ≤ j → j < 8 → f j = false) : bx f 8 = bx f 3 := bx_trunc (by decide) h

example : bx (fun _ => false) 3 = false := bx_false fun _ _ => rfl
example : bx (fun t => decide (8 ≤ t)) 8 = false := bx_false fun t ht => decide_eq_false (by omega)

example (f : Nat → Bool) : bx f (2 + 1) = (bx f 2 ^^ bx (fun t => f (2 + t)) 1) := bx_add f 2 1
example (f : Nat → Bool) : bx f (3 + 5) = (bx f 3 ^^ bx (fun t => f (3 + t)) 5) := bx_add f 3 5

example (f g : Nat → Bool) : bx (fun t => f t ^^ g t) 3 = (bx f 3 ^^ bx g 3) := bx_xor f g 3
example (f g : Nat → Bool) : bx (fun t => f t ^^ g t) 8 = (bx f 8 ^^ bx g 8) := bx_xor f g 8

example (c : Bool) (f : Nat → Bool) : bx (fun t => c && f t) 3 = (c && bx f 3) := bx_and c f 3
example (c : Bool) (f : Nat → Bool) : bx (fun t => c && f t) 8 = (c && bx f 8) := bx_and c f 8

example (x : Bool) (c : Nat → Bool) :
    bx (fun j => decide (1 + j = 2) && x && c j) 3 = (decide (1 ≤ 2 ∧ 2 - 1 < 3) && x && c (2 - 1)) :=
  bx_pair 1 2 x c 3
example (x : Bool) (c : Nat → Bool) :
    bx (fun j => decide (2 + j = 9) && x && c j) 8 = (decide (2 ≤ 9 ∧ 9 - 2 < 8) && x && c (9 - 2)) :=
  bx_pair 2 9 x c 8

example (A A' B B' : Nat → Bool) (hA : ∀ i, i < 2 → A i = A' i) (hB : ∀ j, j < 2 → B j = B' j) :
    cl 2 A B 1 = cl 2 A' B' 1 := cl_congr hA hB 1
example (A A' B B' : Nat → Bool) (hA : ∀ i, i < 8 → A i = A' i) (hB : ∀ j, j < 8 → B j = B' j) :
    cl 8 A B 9 = cl 8 A' B' 9 := cl_congr hA hB 9

example (A B : Nat → Bool) : cl 2 A B 3 = false := cl_big (by decide)
example (A B : Nat → Bool) : cl 4 A B 9 = false := cl_big (by decide)

example (P Q : Nat → Bool) :
    bx (fun i => bx (fun j => decide (i + j + 1 = 2) && P i && Q j) 2) 2 = (decide (1 ≤ 2) && cl 2 P Q (2 - 1)) :=
  cl_shift 2 1 2 P Q
example (P Q : Nat → Bool) :
    bx (fun i => bx (fun j => decide (i + j + 4 = 3) && P i && Q j) 4) 4 = (decide (4 ≤ 3) && cl 4 P Q (3 - 4)) :=
  cl_shift 4 4 3 P Q

example (A B : Nat → Bool) (hA : ∀ i, 2 ≤ i → A i = false) (hB : ∀ j, 2 ≤ j → B j = false) :
    cl 4 A B 2 = cl 2 A B 2 := cl_trunc (by decide) hA hB 2
example (A B : Nat → Bool) (hA : ∀ i, 3 ≤ i → A i = false) (hB : ∀ j, 3 ≤ j → B j = false) :
    cl 8 A B 5 = cl 3 A B 5 := cl_trunc (by decide) hA hB 5

example (X Y : Nat → Bool) (m : Nat) := cl_sum 1 X Y m
example (X Y : Nat → Bool) (m : Nat) := cl_sum 4 X Y m

/-- One Karatsuba step at half widths 1 and 2; closed at half width 2 over every column. -/
example (X Y : Nat → Bool) (k : Nat) := karatsuba 1 X Y k
example (X Y : Nat → Bool) (k : Nat) := karatsuba_full 2 X Y k
example : ∀ k, k < 7 → cl (2 + 2) a1011 a0101 k =
    (cl 2 a1011 a0101 k ^^
      ((decide (2 ≤ k) && (cl 2 (fun i => a1011 i ^^ a1011 (2 + i)) (fun j => a0101 j ^^ a0101 (2 + j)) (k - 2) ^^
          cl 2 a1011 a0101 (k - 2) ^^ cl 2 (fun i => a1011 (2 + i)) (fun j => a0101 (2 + j)) (k - 2))) ^^
        (decide (2 + 2 ≤ k) && cl 2 (fun i => a1011 (2 + i)) (fun j => a0101 (2 + j)) (k - (2 + 2))))) :=
  fun k _ => karatsuba_full 2 a1011 a0101 k

section kcols

variable {X Y PL PH PM PF : Nat → Bool}

example (hL : ∀ k, k < 2 * 1 - 1 → PL k = cl 1 X Y k)
    (hHh : ∀ k, k < 2 * 1 - 1 → PH k = cl 1 (fun i => X (1 + i)) (fun j => Y (1 + j)) k)
    (hM : ∀ k, k < 2 * 1 - 1 → PM k = cl 1 (fun i => X i ^^ X (1 + i)) (fun j => Y j ^^ Y (1 + j)) k)
    (c0 : ∀ i, i < 1 → PF i = PL i)
    (c1 : ∀ i, i + 1 < 1 → PF (1 + i) = (PL (1 + i) ^^ (PM i ^^ PL i ^^ PH i)))
    (c1' : PF (2 * 1 - 1) = (PM (1 - 1) ^^ PL (1 - 1) ^^ PH (1 - 1)))
    (c2 : ∀ i, i + 1 < 1 → PF (2 * 1 + i) = (PH i ^^ (PM (1 + i) ^^ PL (1 + i) ^^ PH (1 + i))))
    (c3 : ∀ i, i < 1 → PF (3 * 1 - 1 + i) = PH (1 - 1 + i)) :
    ∀ k, k < 4 * 1 - 1 → PF k = cl (1 + 1) X Y k :=
  karatsuba_cols (by decide) hL hHh hM c0 c1 c1' c2 c3
example (hL : ∀ k, k < 2 * 4 - 1 → PL k = cl 4 X Y k)
    (hHh : ∀ k, k < 2 * 4 - 1 → PH k = cl 4 (fun i => X (4 + i)) (fun j => Y (4 + j)) k)
    (hM : ∀ k, k < 2 * 4 - 1 → PM k = cl 4 (fun i => X i ^^ X (4 + i)) (fun j => Y j ^^ Y (4 + j)) k)
    (c0 : ∀ i, i < 4 → PF i = PL i)
    (c1 : ∀ i, i + 1 < 4 → PF (4 + i) = (PL (4 + i) ^^ (PM i ^^ PL i ^^ PH i)))
    (c1' : PF (2 * 4 - 1) = (PM (4 - 1) ^^ PL (4 - 1) ^^ PH (4 - 1)))
    (c2 : ∀ i, i + 1 < 4 → PF (2 * 4 + i) = (PH i ^^ (PM (4 + i) ^^ PL (4 + i) ^^ PH (4 + i))))
    (c3 : ∀ i, i < 4 → PF (3 * 4 - 1 + i) = PH (4 - 1 + i)) :
    ∀ k, k < 4 * 4 - 1 → PF k = cl (4 + 4) X Y k :=
  karatsuba_cols (by decide) hL hHh hM c0 c1 c1' c2 c3

end kcols

/-! ## 4. Adder results -/

example (v : BitVec 1) : v = BitVec.ofBool (v.getLsbD 0) := Lib.bv1_eq_ofBool v
example : (1#1 : BitVec 1) = BitVec.ofBool ((1#1 : BitVec 1).getLsbD 0) := Lib.bv1_eq_ofBool 1#1

example (x y : BitVec 3) (ci : Bool) :
    x + y + (BitVec.ofBool ci).setWidth 3 = BitVec.ofNat 3 (x.toNat + y.toNat + (BitVec.ofBool ci).toNat) :=
  Lib.sum_eq_ofNat (by decide) x y ci
example (x y : BitVec 8) (ci : Bool) :
    x + y + (BitVec.ofBool ci).setWidth 8 = BitVec.ofNat 8 (x.toNat + y.toNat + (BitVec.ofBool ci).toNat) :=
  Lib.sum_eq_ofNat (by decide) x y ci

example : BitVec.ofBool (decide (2 ^ 3 ≤ 12)) = BitVec.ofNat 1 (12 / 2 ^ 3) := Lib.carry_eq_ofNat 12 (by decide)
example : BitVec.ofBool (decide (2 ^ 8 ≤ 200)) = BitVec.ofNat 1 (200 / 2 ^ 8) := Lib.carry_eq_ofNat 200 (by decide)

/-! ## 5. Reading the ports, and the statement -/

example (st : SvState) (v : LVec) (y : BitVec 3) (hv : SvState.lookup st "p" = some v) (hw : v.width = 3)
    (hk : ∀ k, k < 3 → KnownBit st "p" k) (hb : ∀ k, k < 3 → st.boolAt "p" k = y.getLsbD k) :
    SvState.lookup st "p" = some (LVec.ofBitVec y) := SvState.lookup_eq_ofBitVec_of_bits hv hw hk hb
example (st : SvState) (v : LVec) (y : BitVec 8) (hv : SvState.lookup st "s" = some v) (hw : v.width = 8)
    (hk : ∀ k, k < 8 → KnownBit st "s" k) (hb : ∀ k, k < 8 → st.boolAt "s" k = y.getLsbD k) :
    SvState.lookup st "s" = some (LVec.ofBitVec y) := SvState.lookup_eq_ofBitVec_of_bits hv hw hk hb

example (st : SvState) (v : LVec) (y : BitVec 3) (hv : SvState.lookup st "p" = some v) (hw : v.width = 3)
    (hk : ∀ k, k < 3 → KnownBit st "p" k) (hy : XF.bv 3 (st.boolAt "p") = y) :
    SvState.lookup st "p" = some (LVec.ofBitVec y) := SvState.lookup_eq_ofBitVec_of_bv hv hw hk hy
example (st : SvState) (v : LVec) (y : BitVec 8) (hv : SvState.lookup st "s" = some v) (hw : v.width = 8)
    (hk : ∀ k, k < 8 → KnownBit st "s" k) (hy : XF.bv 8 (st.boolAt "s") = y) :
    SvState.lookup st "s" = some (LVec.ofBitVec y) := SvState.lookup_eq_ofBitVec_of_bv hv hw hk hy

/-- The statement from its parts, with no third fact and with one the settled-state lemma reads. -/
example (t : CombTask) (sem : Nat → Design2)
    (hs : ∀ N, t.inRange N → CombDesign (sem N) ∧ Acyclic (sem N) ∧ True)
    (hI : ∀ N, t.inRange N → CombDesign (sem N) → t.Interface N (sem N))
    (hset : ∀ N, t.inRange N → ∀ st, CombEqs (sem N) st → StateShape (sem N) st →
      ∀ v, HoldAll st (t.inputs N) v → HoldAll st (t.outputs N) (t.fn N v)) :
    t.Statement sem :=
  CombTask.statement_of_comb hs hI fun N hN _ _ _ => hset N hN
example (t : CombTask) (sem : Nat → Design2) (Q : Nat → Prop)
    (hs : ∀ N, t.inRange N → CombDesign (sem N) ∧ Acyclic (sem N) ∧ Q N)
    (hI : ∀ N, t.inRange N → CombDesign (sem N) → t.Interface N (sem N))
    (hset : ∀ N, Q N → ∀ st, CombEqs (sem N) st → StateShape (sem N) st →
      ∀ v, HoldAll st (t.inputs N) v → HoldAll st (t.outputs N) (t.fn N v)) :
    t.Statement sem :=
  CombTask.statement_of_comb hs hI fun N _ _ _ hq => hset N hq

/-! ## 6. The by-hand route: two closed designs

`chain n`: an input `a`, `y[0] = a[0]` and `y[i+1] = y[i] & a[i+1]` (an AND chain), at `n = 2` and `n = 3`: two
and three single-bit assigns, process `i` writing `y[i]` and reading `y[i-1]`. -/

def bit (n : String) (i : Nat) : Expr2 := .slice (.ident n) i 1

def cell : Nat → Process2
  | 0 => .assign (.slice "y" 0 1) (bit "a" 0)
  | i + 1 => .assign (.slice "y" (i + 1) 1) (.binary .and (bit "y" i) (bit "a" (i + 1)))

def procs (n : Nat) : List Process2 := (List.range n).map cell

def chain (n : Nat) : Design2 where
  name := "chain"
  decls := #[{ name := "a", width := n, isInput := true }, { name := "y", width := n, isOutput := true }]
  processes := (procs n).toArray

/-- The window of a single-bit assign, and its right-hand side. -/
def winOf : Process2 → Win
  | .assign (.slice n lo w) _ => (n, lo, w)
  | _ => ("", 0, 0)

def rhsOf : Process2 → Expr2
  | .assign _ e => e
  | _ => .lit ⟨#[]⟩

theorem cell_assign (i : Nat) : ∃ e, cell i = .assign (.slice "y" i 1) e := by
  cases i <;> exact ⟨_, rfl⟩

theorem chain_leaf (n : Nat) : LeafProcs (chain n) (procs n) winOf := by
  refine ⟨by simp [chain], fun p hp => ?_⟩
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hp
  obtain ⟨e, he⟩ := cell_assign i
  exact ⟨_, e, he, by rw [he]; rfl⟩

/-- `LeafProcs.combDesign`, its list facts stated so that `decide` checks them on a closed design. -/
theorem chain_comb_of (n : Nat) (hnd : ((chain n).decls.toList.map Decl.name).Nodup)
    (hpw : ((procs n).map winOf).Pairwise fun a b => Win.overlaps a b = false)
    (hw : ∀ p ∈ procs n, (chain n).declWidth (winOf p).1 = some n ∧ (winOf p).2.1 + (winOf p).2.2 ≤ n)
    (hin : ∀ p ∈ procs n, (winOf p).1 ∉ (chain n).inputNames.toList)
    (hfree : ∀ p ∈ procs n, (rhsOf p).unsupportedFree = true)
    (hdecl : ∀ p ∈ procs n, ∀ x ∈ (rhsOf p).idents, x ∈ (chain n).decls.toList.map Decl.name) :
    CombDesign (chain n) :=
  (chain_leaf n).combDesign hnd hpw (fun p hp => ⟨n, hw p hp⟩) hin
    (fun p hp t e he => by subst he; exact hfree _ hp) (fun p hp t e he => by subst he; exact hdecl _ hp)
    (fun dc hdc => by simp [chain] at hdc; rcases hdc with rfl | rfl <;> rfl)
    (fun dc hdc => by simp [chain] at hdc; rcases hdc with rfl | rfl <;> simp)

/-- `LeafProcs.acyclic` with the offset of the written bit as the rank. -/
theorem chain_acyclic_of (n : Nat)
    (h : ∀ p ∈ procs n, ∀ q ∈ procs n, ∀ r ∈ (rhsOf p).reads,
      r.overlaps (winOf q) = true → (winOf q).2.1 < (winOf p).2.1) :
    Acyclic (chain n) :=
  (chain_leaf n).acyclic (fun p => (winOf p).2.1) fun p hp q hq t e he r hr hov => by
    subst he
    exact h _ hp q hq r hr hov

theorem chain2_comb : CombDesign (chain 2) :=
  chain_comb_of 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem chain3_comb : CombDesign (chain 3) :=
  chain_comb_of 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem chain2_acyclic : Acyclic (chain 2) := chain_acyclic_of 2 (by decide)
theorem chain3_acyclic : Acyclic (chain 3) := chain_acyclic_of 3 (by decide)

/-- The rank `LeafProcs.acyclic` builds, at a process and past the end. -/
example : procRank (chain 3) (fun p => (winOf p).2.1) 2 = 2 := rfl
example : procRank (chain 2) (fun p => (winOf p).2.1) 5 = 0 := rfl

example : ∃ k : Nat, (chain 2).processes[k]? = some (cell 1) :=
  (chain_leaf 2).getElem?_of_mem (List.mem_map.mpr ⟨1, by simp, rfl⟩)
example : ∃ k : Nat, (chain 3).processes[k]? = some (cell 2) :=
  (chain_leaf 3).getElem?_of_mem (List.mem_map.mpr ⟨2, by simp, rfl⟩)

example (p : Process2) (h : (chain 2).processes[1]? = some p) : p ∈ procs 2 := (chain_leaf 2).mem_of_getElem? h
example (p : Process2) (h : (chain 3).processes[2]? = some p) : p ∈ procs 3 := (chain_leaf 3).mem_of_getElem? h

example : (Lhs2.slice "y" 1 1).wins (chain 2) = [winOf (cell 1)] := (chain_leaf 2).wins_eq
  (List.mem_map.mpr ⟨1, by simp, rfl⟩) rfl
example : (Lhs2.slice "y" 2 1).wins (chain 3) = [winOf (cell 2)] := (chain_leaf 3).wins_eq
  (List.mem_map.mpr ⟨2, by simp, rfl⟩) rfl

example (j : Nat) (w : Win) (h : (chain 2).Writes j w) : ∃ p, (chain 2).processes[j]? = some p ∧ p ∈ procs 2 ∧
    w = winOf p := (chain_leaf 2).writes h
example (j : Nat) (w : Win) (h : (chain 3).Writes j w) : ∃ p, (chain 3).processes[j]? = some p ∧ p ∈ procs 3 ∧
    w = winOf p := (chain_leaf 3).writes h

example : ∀ i j wi wj, i ≠ j → (chain 2).Writes i wi → (chain 2).Writes j wj → Win.overlaps wi wj = false :=
  (chain_leaf 2).disjoint (by decide)
example : ∀ i j wi wj, i ≠ j → (chain 3).Writes i wi → (chain 3).Writes j wj → Win.overlaps wi wj = false :=
  (chain_leaf 3).disjoint (by decide)

example : ∀ i n lo w, (chain 2).Writes i (n, lo, w) → 0 < w := (chain_leaf 2).writes_pos (by decide)
example : ∀ i n lo w, (chain 3).Writes i (n, lo, w) → 0 < w := (chain_leaf 3).writes_pos (by decide)

/-! ### Gates on known bits, at widths 3 and 8 -/

def st3 : SvState := [("a", LVec.ofBitVec (5#3))]
def st8 : SvState := [("a", LVec.ofBitVec (0xa6#8))]

example : evalPure2 st3 (bit "a" 2) = .ok (LVec.ofBitVec (BitVec.ofBool ((5#3).getLsbD 2))) :=
  evalPure2_bit_of_lookup rfl (by decide)
example : evalPure2 st8 (bit "a" 7) = .ok (LVec.ofBitVec (BitVec.ofBool ((0xa6#8).getLsbD 7))) :=
  evalPure2_bit_of_lookup rfl (by decide)

example : evalPure2 st3 (.slice (.ident "a") 1 2) = .ok (LVec.ofBitVec ((5#3).extractLsb' 1 2)) :=
  evalPure2_slice_of_extract rfl (LVec.extract_ofBitVec _ (by decide))
example : evalPure2 st8 (.slice (.ident "a") 2 5) = .ok (LVec.ofBitVec ((0xa6#8).extractLsb' 2 5)) :=
  evalPure2_slice_of_extract rfl (LVec.extract_ofBitVec _ (by decide))

example : evalPure2 st3 (.lit { bits := #[Logic.l0] }) = .ok (LVec.ofBitVec (BitVec.ofBool false)) :=
  evalPure2_lit_l0
example : evalPure2 st8 (.lit { bits := #[Logic.l0] }) = .ok (LVec.ofBitVec (BitVec.ofBool false)) :=
  evalPure2_lit_l0

example : evalPure2 st3 (.binary .and (bit "a" 0) (bit "a" 2)) =
    .ok (LVec.ofBitVec (BitVec.ofBool ((5#3).getLsbD 0 && (5#3).getLsbD 2))) :=
  evalPure2_and_bool (evalPure2_bit_of_lookup rfl (by decide)) (evalPure2_bit_of_lookup rfl (by decide))
example : evalPure2 st8 (.binary .and (bit "a" 1) (bit "a" 6)) =
    .ok (LVec.ofBitVec (BitVec.ofBool ((0xa6#8).getLsbD 1 && (0xa6#8).getLsbD 6))) :=
  evalPure2_and_bool (evalPure2_bit_of_lookup rfl (by decide)) (evalPure2_bit_of_lookup rfl (by decide))

example : evalPure2 st3 (.binary .or (bit "a" 1) (bit "a" 2)) =
    .ok (LVec.ofBitVec (BitVec.ofBool ((5#3).getLsbD 1 || (5#3).getLsbD 2))) :=
  evalPure2_or_bool (evalPure2_bit_of_lookup rfl (by decide)) (evalPure2_bit_of_lookup rfl (by decide))
example : evalPure2 st8 (.binary .or (bit "a" 0) (bit "a" 3)) =
    .ok (LVec.ofBitVec (BitVec.ofBool ((0xa6#8).getLsbD 0 || (0xa6#8).getLsbD 3))) :=
  evalPure2_or_bool (evalPure2_bit_of_lookup rfl (by decide)) (evalPure2_bit_of_lookup rfl (by decide))

example : evalPure2 st3 (.binary .xor (bit "a" 0) (bit "a" 2)) =
    .ok (LVec.ofBitVec (BitVec.ofBool ((5#3).getLsbD 0 ^^ (5#3).getLsbD 2))) :=
  evalPure2_xor_bool (evalPure2_bit_of_lookup rfl (by decide)) (evalPure2_bit_of_lookup rfl (by decide))
example : evalPure2 st8 (.binary .xor (bit "a" 5) (bit "a" 7)) =
    .ok (LVec.ofBitVec (BitVec.ofBool ((0xa6#8).getLsbD 5 ^^ (0xa6#8).getLsbD 7))) :=
  evalPure2_xor_bool (evalPure2_bit_of_lookup rfl (by decide)) (evalPure2_bit_of_lookup rfl (by decide))

/-! ### Assigns read back, at the designs of 2 and 3 processes -/

example (st : SvState) (heqs : CombEqs (chain 2) st) (u : LVec) (hu : SvState.lookup st "y" = some u) (b : Bool)
    (he : evalPure2 st (.binary .and (bit "y" 0) (bit "a" 1)) = .ok (LVec.ofBitVec (BitVec.ofBool b))) :
    u.extract 1 1 = LVec.ofBitVec (BitVec.ofBool b) :=
  CombEqs.readback1 heqs (k := 1) rfl hu he
example (st : SvState) (heqs : CombEqs (chain 3) st) (u : LVec) (hu : SvState.lookup st "y" = some u) (b : Bool)
    (he : evalPure2 st (.binary .and (bit "y" 1) (bit "a" 2)) = .ok (LVec.ofBitVec (BitVec.ofBool b))) :
    u.extract 2 1 = LVec.ofBitVec (BitVec.ofBool b) :=
  CombEqs.readback1 heqs (k := 2) rfl hu he

example (st : SvState) (heqs : CombEqs (chain 2) st) (u : LVec) (hu : SvState.lookup st "y" = some u)
    (x : BitVec 3) (he : evalPure2 st (bit "a" 0) = .ok (LVec.ofBitVec x)) :
    u.extract 0 1 = LVec.ofBitVec (x.setWidth 1) :=
  CombEqs.readback heqs (k := 0) rfl hu he
example (st : SvState) (heqs : CombEqs (chain 3) st) (u : LVec) (hu : SvState.lookup st "y" = some u)
    (x : BitVec 8) (he : evalPure2 st (bit "a" 0) = .ok (LVec.ofBitVec x)) :
    u.extract 0 1 = LVec.ofBitVec (x.setWidth 1) :=
  CombEqs.readback heqs (k := 0) rfl hu he

example (v : LVec) (x : BitVec 3)
    (h : ∀ j, j < 3 → v.extract (2 + j) 1 = LVec.ofBitVec (BitVec.ofBool (x.getLsbD j))) :
    v.extract 2 3 = LVec.ofBitVec x := LVec.extract_eq_ofBitVec_of_bits h
example (v : LVec) (x : BitVec 8)
    (h : ∀ j, j < 8 → v.extract (0 + j) 1 = LVec.ofBitVec (BitVec.ofBool (x.getLsbD j))) :
    v.extract 0 8 = LVec.ofBitVec x := LVec.extract_eq_ofBitVec_of_bits h
example : (LVec.ofBitVec (0xa6#8)).extract 1 3 = LVec.ofBitVec (3#3) :=
  LVec.extract_eq_ofBitVec_of_bits fun j hj => by
    rw [LVec.extract_one_ofBitVec _ (by omega)]
    congr 2
    match j, hj with
    | 0, _ => rfl
    | 1, _ => rfl
    | 2, _ => rfl

/-! ## 7. The `clmul` Spec's definitions -/

open SvGolf.Tasks.Clmul in
example (a b : BitVec 2) (k : Nat) :
    coeff 2 a b k = bx (fun i => bx (fun j => decide (i + j = k) && a.getLsbD i && b.getLsbD j) 2) 2 :=
  coeff_eq 2 a b k
open SvGolf.Tasks.Clmul in
example (a b : BitVec 8) (k : Nat) :
    coeff 8 a b k = bx (fun i => bx (fun j => decide (i + j = k) && a.getLsbD i && b.getLsbD j) 8) 8 :=
  coeff_eq 8 a b k
open SvGolf.Tasks.Clmul in
example : (List.range 5).map (coeff 3 5#3 3#3) = (List.range 5).map (cl 3 (5#3).getLsbD (3#3).getLsbD) := by
  decide

open SvGolf.Tasks.Clmul in
example (f : Nat → Bool) : (ofBits 3 f).getLsbD 5 = (decide (5 < 3) && f 5) := getLsbD_ofBits 3 f 5
open SvGolf.Tasks.Clmul in
example (f : Nat → Bool) : (ofBits 8 f).getLsbD 6 = f 6 := getLsbD_ofBits_lt (by decide)
open SvGolf.Tasks.Clmul in
example : (ofBits 3 fun k => decide (k = 1)).getLsbD 1 = true := by rw [getLsbD_ofBits_lt (by decide)]; rfl

end SvGolfTests.Comb
