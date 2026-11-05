import SvGolf.Task
import LeanModels.Rv.Decode
import LeanModels.Rv.Exec

/-!
# WP-RB0 / G2: the statements of the three first targets (STATEMENTS ONLY: nothing here is proved)

Each target is a real block of an open-source RISC-V core; its trusted spec is a definition of
`LeanModels.Rv` (the ISA model of this repository), not a re-derivation. The statements are
`CombTask`-shaped (svgolf/SvGolf/Task.lean), so the existing machinery (`CombTask.satisfiedAt_of_comb`,
`sv_structure`, `sv_equations`) applies unchanged; the third is relational and needs the twin
`RelTask` defined at the top (about 20 lines, not in SvGolf today).

Typechecked by `lake env lean` from the svgolf project (batch E of WP-RB0). The `#eval`/`example`
lines at the end are sanity checks of the spec functions against the RTL's documented behaviour, not
proofs about the RTL.
-/

namespace RB0

open SvGolf LeanModels.Sv LeanModels.Rv

/-! ## A relational twin of `CombTask` (for blocks with don't-care outputs) -/

/-- Like `CombTask` for a parameterless block, but the outputs are constrained by a RELATION of the
inputs (a decoder's `instr_o` is a don't-care when `illegal_instr_o` is set). -/
structure RelTask where
  inputs : List Sig
  outputs : List Sig
  rel : Vals (inputs.map Prod.snd) → Vals (outputs.map Prod.snd) → Prop

namespace RelTask
variable (t : RelTask)

/-- In every completed run, every cycle whose stimulus drives each input with a known value ends in a
snapshot whose outputs are known and related to the inputs. -/
def Computes (d : Design2) : Prop :=
  d ⊨₂ spec2 fun stim tr =>
    ∀ (c : Nat) (inputs st : SvState), stim[c]? = some inputs → tr[c]? = some st →
      ∀ v, HoldAll inputs t.inputs v → ∃ o, HoldAll st t.outputs o ∧ t.rel v o

def SatisfiedAt (d : Design2) : Prop :=
  (inputPorts d = t.inputs ∧ outputPorts d = t.outputs) ∧ (Unclocked d ∧ Terminates2 d) ∧ t.Computes d
end RelTask

/-! ## Target 1: ultraembedded/riscv `riscv_alu` (biRISC-V), spec `Rv.aluSem` -/

namespace BiriscvAlu

/-- The block's 4-bit op codes (riscv_defs.v: `ALU_SHIFTL` 1, `ALU_SHIFTR` 2, `ALU_SHIFTR_ARITH` 3, `ALU_ADD` 4,
`ALU_SUB` 6, `ALU_AND` 7, `ALU_OR` 8, `ALU_XOR` 9, `ALU_LESS_THAN` 10 (unsigned), `ALU_LESS_THAN_SIGNED` 11)
as the ISA's `AluOp`; every other code is the RTL's `default:` arm (the result is operand a). -/
def opOf? : BitVec 4 → Option AluOp
  | 1 => some .sll | 2 => some .srl | 3 => some .sra | 4 => some .add | 6 => some .sub
  | 7 => some .and | 8 => some .or | 9 => some .xor | 10 => some .sltu | 11 => some .slt
  | _ => none

def task : CombTask where
  inRange _ := True
  inputs _ := [("alu_op_i", 4), ("alu_a_i", 32), ("alu_b_i", 32)]
  outputs _ := [("alu_p_o", 32)]
  fn _ := fun (op, a, b, ()) => (match opOf? op with | some o => aluSem o a b | none => a, ())

/-- The statement for the parameterless design `riscv_alu.sem`. -/
abbrev Statement : Design2 → Prop := task.StatementFixed
end BiriscvAlu

/-! ## Target 2: Hazard3 `hazard3_branchcmp`, spec `Rv.branchSem` -/

namespace Hazard3Branchcmp

/-- `cmp` of the block: funct3 bit 14 = 0 is the equality test (the block returns `a != b`; BEQ vs BNE is the
inversion bit 12, applied OUTSIDE the block), bit 14 = 1 is `<`, signed when bit 13 = 0 and unsigned when it is 1.
Stated through `branchSem` (`ne`, `lt`, `ltu`). -/
def cmpOf (cir a b : BitVec 32) : Bool :=
  if cir.getLsbD 14 then (if cir.getLsbD 13 then branchSem .ltu a b else branchSem .lt a b) else branchSem .ne a b

/-- The block has the 50-odd configuration parameters of `hazard3_config.vh`; the statement is at `W_DATA = 32`
(the width of `Rv.branchSem`) and every other parameter at its default, so the family is applied by the caller:
`Statement (branchcmp.sem <defaults>)`. -/
def task : CombTask where
  inRange _ := True
  inputs _ := [("cir", 32), ("op_a", 32), ("op_b", 32)]
  outputs _ := [("cmp", 1)]
  fn _ := fun (cir, a, b, ()) => (BitVec.ofBool (cmpOf cir a b), ())

abbrev Statement : Design2 → Prop := task.StatementFixed
end Hazard3Branchcmp

/-! ## Target 2b: biRISC-V `riscv_decoder`, spec `Rv.decode` (completeness direction) -/

namespace BiriscvDecoder

def isExec : Instr → Bool | .alu .. => true | _ => false
def isLsu : Instr → Bool | .mem .. => true | _ => false
def isBranch : Instr → Bool | .branch .. => true | .jump .. => true | _ => false
def isMul : Instr → Bool
  | .mulDiv op .. => op == .mul || op == .mulh || op == .mulhsu || op == .mulhu
  | _ => false
def isDiv : Instr → Bool
  | .mulDiv op .. => !(op == .mul || op == .mulh || op == .mulhsu || op == .mulhu)
  | _ => false
def isMulDiv : Instr → Bool | .mulDiv .. => true | _ => false
def isSystem : Instr → Bool | .system _ => true | _ => false
def rdValid : Instr → Bool
  | .alu .. => true | .jump .. => true | .mulDiv .. => true
  | .mem (.load _) .. => true | .system (.csr ..) => true | _ => false

def b (x : Bool) : BitVec 1 := if x then 1#1 else 0#1

/-- COMPLETENESS of the block against the ISA model: every word the model decodes is accepted (`invalid_o` is 0, except
that an M-extension word is invalid while `enable_muldiv_i` is 0) and classified as the flags say. The converse is not
claimed: the block also accepts `lwu`, `sfence.vma`, `sret`/`uret` (masks of riscv_defs.v) that `Rv.decode` rejects; a
second theorem would list exactly those codes. -/
def rel (valid fault mdE : BitVec 1) (w : BitVec 32) (inv ex ls br mu dv cs rdv : BitVec 1) : Prop :=
  ∀ i, decode w = some i →
    inv = b (valid == 1#1 && isMulDiv i && mdE == 0#1) ∧ ex = b (isExec i) ∧ ls = b (isLsu i) ∧ br = b (isBranch i) ∧
    mu = b (mdE == 1#1 && isMul i) ∧ dv = b (mdE == 1#1 && isDiv i) ∧
    cs = b (isSystem i || inv == 1#1 || fault == 1#1) ∧ rdv = b (rdValid i)

def task : RelTask where
  inputs := [("valid_i", 1), ("fetch_fault_i", 1), ("enable_muldiv_i", 1), ("opcode_i", 32)]
  outputs := [("invalid_o", 1), ("exec_o", 1), ("lsu_o", 1), ("branch_o", 1), ("mul_o", 1), ("div_o", 1),
              ("csr_o", 1), ("rd_valid_o", 1)]
  rel := fun (v, f, m, w, ()) (inv, ex, ls, br, mu, dv, cs, rdv, ()) => rel v f m w inv ex ls br mu dv cs rdv

abbrev Statement (d : Design2) : Prop := task.SatisfiedAt d
end BiriscvDecoder

/-! ## Target 3: CV32E40P `cv32e40p_compressed_decoder` at `FPU = 0`, spec `Rv.expandC` -/

namespace Cv32e40pRvc

/-- `instr_i`, `instr_o`, `is_compressed_o`, `illegal_instr_o`: the RTL's own contract
(`expandC` is documented as matching this RTL at `FPU = 0`; `none` is the RTL's `illegal_instr_o`;
`instr_o` is a don't-care for an illegal encoding, so the statement is relational). -/
def rel (i : BitVec 32) (o : BitVec 32) (isC illegal : BitVec 1) : Prop :=
  isC = (if i.extractLsb' 0 2 = 3#2 then 0#1 else 1#1) ∧
  (i.extractLsb' 0 2 = 3#2 → o = i ∧ illegal = 0#1) ∧
  (i.extractLsb' 0 2 ≠ 3#2 →
    (expandC (i.extractLsb' 0 16) = none ↔ illegal = 1#1) ∧
    ∀ w, expandC (i.extractLsb' 0 16) = some w → o = w)

def task : RelTask where
  inputs := [("instr_i", 32)]
  outputs := [("instr_o", 32), ("is_compressed_o", 1), ("illegal_instr_o", 1)]
  rel := fun (i, ()) (o, c, ill, ()) => rel i o c ill

/-- The statement for the design at `(FPU, ZFINX) = (0, 0)`: `Statement (decoder.sem 0 0)`. -/
abbrev Statement (d : Design2) : Prop := task.SatisfiedAt d
end Cv32e40pRvc

/-! ## Sanity checks of the spec functions (not proofs about the RTL) -/

open BiriscvAlu Hazard3Branchcmp in
example : (match opOf? 11 with | some o => aluSem o 0xFFFFFFFF#32 1#32 | none => 0#32) = 1#32 := by decide   -- slt: -1 < 1
open BiriscvAlu in
example : (match opOf? 10 with | some o => aluSem o 0xFFFFFFFF#32 1#32 | none => 0#32) = 0#32 := by decide   -- sltu
open BiriscvAlu in
example : (match opOf? 1 with | some o => aluSem o 1#32 33#32 | none => 0#32) = 2#32 := by decide              -- sll by 33 = by 1 (low 5 bits)
open BiriscvAlu in
example : (match opOf? 15 with | some o => aluSem o 7#32 9#32 | none => 7#32) = 7#32 := by decide              -- unused code: result = a
open Hazard3Branchcmp in
example : cmpOf 0x00004000#32 0xFFFFFFFF#32 1#32 = true := by decide   -- funct3 = 100 (BLT) shape: -1 < 1
open Hazard3Branchcmp in
example : cmpOf 0x00006000#32 0xFFFFFFFF#32 1#32 = false := by decide  -- funct3 = 110 (BLTU): 0xFFFFFFFF < 1 is false
open BiriscvDecoder in
example : decode 0x007302b3#32 = some (.alu .add 5 (.reg 6) (.reg 7)) := by decide   -- add x5, x6, x7
open BiriscvDecoder in
example : isExec (.alu .add 5 (.reg 6) (.reg 7)) = true ∧ isBranch (.jump 1 .pc 4) = true := by decide
-- c.addi4spn x8, 4: halfword 0x0040 expands to `addi x8, x2, 4` = 0x00410413
example : expandC 0x0040#16 = some 0x00410413#32 := by decide
-- the all-zero halfword is illegal
example : expandC 0x0000#16 = none := by decide

end RB0
