import SvGolf.Task

/-!
# Task `aes_sbox`: the AES S-box (TRUSTED)

The AES S-box (FIPS 197 Section 5.1.1), fixed size: eight bits in, eight bits out. Module (no
parameter; port order as written):

```systemverilog
module aes_sbox (
  input  logic [7:0] x,
  output logic [7:0] y
);
```

Statement: the design has exactly the ports `x` (input, 8 bits) and `y` (output, 8 bits), every run
terminates, no process is clocked, there is no combinational loop, and in every cycle whose stimulus
drives `x` with a known value
the snapshot's `y` is `sbox x`: the multiplicative inverse in
GF(2^8) = GF(2)[x]/(x^8+x^4+x^3+x+1) (with 0 mapped to 0) followed by the affine transformation
`b ^ rotl b 1 ^ rotl b 2 ^ rotl b 3 ^ rotl b 4 ^ 0x63`. It is `CombTask.StatementFixed` of
`SvGolf/Task.lean` (the statement at the one "parameter value" `0`, which the task's interface and
function ignore). Bit order: `BitVec 8`, `x[7]` is the most significant bit, as in the standard.

The function is DEFINED algebraically (below), the way the standard defines it; the 256-entry table
of FIPS 197 (Table 4 of the 2023 edition, Figure 7 of the 2001 one) appears only as a cross-check
(`sboxTable`, an `example` that the algebra reproduces it, and the standard's own worked values).
Sources used to cross-check (none trusted): `oracle.py` (the same algebra in Python), the
independently derived 113-gate Boyar-Peralta circuit (`reference/sbox_bp.sv`, equal to the table on
all 256 inputs), and a textbook AES-128 that reproduces the FIPS 197 (2001) Appendix C.1 ciphertext
through this S-box and agrees with OpenSSL on random blocks (`tests/aes_sbox/validate/validate.py`);
the table itself was compared with Table 4 parsed from the NIST PDF.
-/

namespace SvGolf.Tasks.AesSbox

open SvGolf

/-! ## GF(2^8) -/

/-- Multiplication by `x` in GF(2^8) (FIPS 197, XTIMES, Equation (4.5), Section 4.2). -/
def xtime (a : BitVec 8) : BitVec 8 := (a <<< 1) ^^^ (if a.msb then 0x1b#8 else 0#8)

/-- `gmulAux n a b acc`: shift-and-add multiplication, `n` steps (FIPS 197, Section 4.2). -/
def gmulAux : Nat → BitVec 8 → BitVec 8 → BitVec 8 → BitVec 8
  | 0, _, _, acc => acc
  | n + 1, a, b, acc => gmulAux n (xtime a) (b >>> 1) (if b.getLsbD 0 then acc ^^^ a else acc)

/-- Multiplication in GF(2^8) (FIPS 197, Section 4.2). -/
def gmul (a b : BitVec 8) : BitVec 8 := gmulAux 8 a b 0

/-- The multiplicative inverse, `0` for `0`: `a^254 = a^2 * a^4 * ... * a^128` (the group has order 255). -/
def ginv (a : BitVec 8) : BitVec 8 :=
  let a2 := gmul a a
  let a4 := gmul a2 a2
  let a8 := gmul a4 a4
  let a16 := gmul a8 a8
  let a32 := gmul a16 a16
  let a64 := gmul a32 a32
  let a128 := gmul a64 a64
  gmul (gmul (gmul a2 a4) (gmul a8 a16)) (gmul (gmul a32 a64) a128)

/-- The affine transformation of Section 5.1.1, Equations (5.3) and (5.4) of the 2023 edition:
`b'_i = b_i ^ b_(i+4) ^ b_(i+5) ^ b_(i+6) ^ b_(i+7) ^ c_i` with `c = 0x63` (indices mod 8). -/
def affine (b : BitVec 8) : BitVec 8 :=
  b ^^^ b.rotateLeft 1 ^^^ b.rotateLeft 2 ^^^ b.rotateLeft 3 ^^^ b.rotateLeft 4 ^^^ 0x63#8

/-- **The AES S-box.** -/
def sbox (x : BitVec 8) : BitVec 8 := affine (ginv x)

/-! ## The task -/

/-- The task: input `x : BitVec 8`, output `y = sbox x`. Fixed size (statement at `N = 0`). -/
def task : CombTask where
  inRange N := N = 0
  inputs _ := [("x", 8)]
  outputs _ := [("y", 8)]
  fn _ := fun (x, ()) => (sbox x, ())

/-- **The challenge statement** for the parameterless design `Submission.design.sem : Design2`. -/
abbrev Statement : LeanModels.Sv.Design2 → Prop := task.StatementFixed

/-! ## Sanity checks (closed; `decide +kernel` is kernel evaluation, no axiom) -/

example : task.inRange 0 := rfl

/-- The statement's point `N = 0` is the task's (only) point, and the interface is `x : 8` in,
`y : 8` out. -/
example : task.inputs 0 = [("x", 8)] ∧ task.outputs 0 = [("y", 8)] := ⟨rfl, rfl⟩

/-- The input names are distinct (the non-vacuity theorem `CombTask.SatisfiedAt.exists_run` needs
it). -/
example : ((task.inputs 0).map Prod.fst).Nodup := by decide

/-- The function on concrete values (the standard's own worked example, Section 5.1.1: `S(53) = ed`,
and the two ends of Table 4). -/
example : (task.fn 0 (0x53#8, ())).1 = 0xed#8 := by decide +kernel
example : (task.fn 0 (0x00#8, ())).1 = 0x63#8 := by decide +kernel
example : (task.fn 0 (0xff#8, ())).1 = 0x16#8 := by decide +kernel

/-- FIPS 197 (2023) Section 4.2, Equation (4.7): `{57} * {13} = {fe}`; (2001 edition) Section 4.2: `{57} * {83} = {c1}`. -/
example : gmul 0x57#8 0x83#8 = 0xc1#8 ∧ gmul 0x57#8 0x13#8 = 0xfe#8 := by decide

/-- FIPS 197 Section 5.1.1 and Table 4: `S(00) = 63`, `S(53) = ed` (the standard's own example), `S(ff) = 16`. -/
example : sbox 0x00#8 = 0x63#8 ∧ sbox 0x53#8 = 0xed#8 ∧ sbox 0xff#8 = 0x16#8 := by decide +kernel

/-- The table of FIPS 197 Table 4 (row-major, `S(16 r + c)` at index `16 r + c`), as a cross-check only. -/
def sboxTable : List Nat :=
  [0x63, 0x7c, 0x77, 0x7b, 0xf2, 0x6b, 0x6f, 0xc5, 0x30, 0x01, 0x67, 0x2b, 0xfe, 0xd7, 0xab, 0x76,
   0xca, 0x82, 0xc9, 0x7d, 0xfa, 0x59, 0x47, 0xf0, 0xad, 0xd4, 0xa2, 0xaf, 0x9c, 0xa4, 0x72, 0xc0,
   0xb7, 0xfd, 0x93, 0x26, 0x36, 0x3f, 0xf7, 0xcc, 0x34, 0xa5, 0xe5, 0xf1, 0x71, 0xd8, 0x31, 0x15,
   0x04, 0xc7, 0x23, 0xc3, 0x18, 0x96, 0x05, 0x9a, 0x07, 0x12, 0x80, 0xe2, 0xeb, 0x27, 0xb2, 0x75,
   0x09, 0x83, 0x2c, 0x1a, 0x1b, 0x6e, 0x5a, 0xa0, 0x52, 0x3b, 0xd6, 0xb3, 0x29, 0xe3, 0x2f, 0x84,
   0x53, 0xd1, 0x00, 0xed, 0x20, 0xfc, 0xb1, 0x5b, 0x6a, 0xcb, 0xbe, 0x39, 0x4a, 0x4c, 0x58, 0xcf,
   0xd0, 0xef, 0xaa, 0xfb, 0x43, 0x4d, 0x33, 0x85, 0x45, 0xf9, 0x02, 0x7f, 0x50, 0x3c, 0x9f, 0xa8,
   0x51, 0xa3, 0x40, 0x8f, 0x92, 0x9d, 0x38, 0xf5, 0xbc, 0xb6, 0xda, 0x21, 0x10, 0xff, 0xf3, 0xd2,
   0xcd, 0x0c, 0x13, 0xec, 0x5f, 0x97, 0x44, 0x17, 0xc4, 0xa7, 0x7e, 0x3d, 0x64, 0x5d, 0x19, 0x73,
   0x60, 0x81, 0x4f, 0xdc, 0x22, 0x2a, 0x90, 0x88, 0x46, 0xee, 0xb8, 0x14, 0xde, 0x5e, 0x0b, 0xdb,
   0xe0, 0x32, 0x3a, 0x0a, 0x49, 0x06, 0x24, 0x5c, 0xc2, 0xd3, 0xac, 0x62, 0x91, 0x95, 0xe4, 0x79,
   0xe7, 0xc8, 0x37, 0x6d, 0x8d, 0xd5, 0x4e, 0xa9, 0x6c, 0x56, 0xf4, 0xea, 0x65, 0x7a, 0xae, 0x08,
   0xba, 0x78, 0x25, 0x2e, 0x1c, 0xa6, 0xb4, 0xc6, 0xe8, 0xdd, 0x74, 0x1f, 0x4b, 0xbd, 0x8b, 0x8a,
   0x70, 0x3e, 0xb5, 0x66, 0x48, 0x03, 0xf6, 0x0e, 0x61, 0x35, 0x57, 0xb9, 0x86, 0xc1, 0x1d, 0x9e,
   0xe1, 0xf8, 0x98, 0x11, 0x69, 0xd9, 0x8e, 0x94, 0x9b, 0x1e, 0x87, 0xe9, 0xce, 0x55, 0x28, 0xdf,
   0x8c, 0xa1, 0x89, 0x0d, 0xbf, 0xe6, 0x42, 0x68, 0x41, 0x99, 0x2d, 0x0f, 0xb0, 0x54, 0xbb, 0x16]

set_option maxRecDepth 100000 in
/-- The algebra reproduces the table on all 256 inputs. -/
example : ∀ x : Fin 256, (sbox (BitVec.ofNat 8 x.val)).toNat = sboxTable.getD x.val 0 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The S-box is a permutation of the bytes (a sanity check of the spec, not a part of the statement). -/
example : ((List.range 256).map fun x => (sbox (BitVec.ofNat 8 x)).toNat).Nodup := by decide +kernel

end SvGolf.Tasks.AesSbox
