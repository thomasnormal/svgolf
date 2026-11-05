import SvGolf.Task

/-!
# DRAFT task `chacha_qr`: the ChaCha quarter round (RFC 8439, Section 2.1; fixed size, 32-bit words)

**UNTRUSTED DRAFT** (week-2 task study, WP-T0), not part of the `tasks` library.

Module (fixed size; port order as written; no `do` as a name: it is a SystemVerilog keyword):

```systemverilog
module chacha_qr (
  input  logic [31:0] a, b, c, d,
  output logic [31:0] ra, rb, rc, rd
);
```

Statement: exactly these ports; no clocked process; every run terminates; and in every cycle whose
stimulus drives `a b c d` with known values the snapshot holds `(ra, rb, rc, rd) = qr a b c d`.
Run-time `+ - * / % **` are banned (the four 32-bit additions are the task: the player builds
adders from gates, as in `add`); rotations by constants and XOR are free wiring and gates.
-/

namespace SvGolf.Tasks.ChachaQr

open SvGolf

/-- RFC 8439 Section 2.1: `a += b; d ^= a; d <<<= 16; c += d; b ^= c; b <<<= 12;
a += b; d ^= a; d <<<= 8; c += d; b ^= c; b <<<= 7`, additions modulo `2^32`. -/
def qr (a b c d : BitVec 32) : BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 :=
  let a := a + b
  let d := (d ^^^ a).rotateLeft 16
  let c := c + d
  let b := (b ^^^ c).rotateLeft 12
  let a := a + b
  let d := (d ^^^ a).rotateLeft 8
  let c := c + d
  let b := (b ^^^ c).rotateLeft 7
  (a, b, c, d)

/-- The task (fixed size: statement at `N = 0`). -/
def task : CombTask where
  inRange N := N = 0
  inputs _ := [("a", 32), ("b", 32), ("c", 32), ("d", 32)]
  outputs _ := [("ra", 32), ("rb", 32), ("rc", 32), ("rd", 32)]
  fn _ := fun (a, b, c, d, ()) => let r := qr a b c d; (r.1, r.2.1, r.2.2.1, r.2.2.2, ())

abbrev Statement : LeanModels.Sv.Design2 → Prop := task.StatementFixed

example : task.inRange 0 := rfl
example : ((task.inputs 0).map Prod.fst).Nodup := by decide

/-- RFC 8439 Section 2.1.1, the quarter-round test vector. -/
example : qr 0x11111111#32 0x01020304#32 0x9b8d6f43#32 0x01234567#32 =
    (0xea2a92f4#32, 0xcb1cf8ce#32, 0x4581472e#32, 0x5881c4bb#32) := by decide

/-- RFC 8439 Section 2.2.1, the quarter round on words 2, 7, 8, 13 of the example state. -/
example : qr 0x516461b1#32 0x2a5f714c#32 0x53372767#32 0x3d631689#32 =
    (0xbdb886dc#32, 0xcfacafd2#32, 0xe46bea80#32, 0xccc07c79#32) := by decide

/-- The same through the task function. -/
example : (task.fn 0 (0x11111111#32, 0x01020304#32, 0x9b8d6f43#32, 0x01234567#32, ())).2.2.1 =
    0x4581472e#32 := by decide

end SvGolf.Tasks.ChachaQr
