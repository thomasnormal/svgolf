import tasks.fdivp.IEEE754

/-!
# Batch runner for the differential validation (untrusted tooling)

    lake env lean --run tasks/fdivp/spec_validate/Run.lean <impl> <w> <p> <mode> <pairs.bin> <out.bin>   (from svgolf/)

`<impl>` is `spec` (this repo's `SvGolf.IEEE754.divide`) or `core` (Lean core's own logical
float model `Float.Model.UnpackedFloat.div`, an independent implementation shipped with the
toolchain; roundTiesToEven only). `<mode>` is one of `rne rna rtp rtn rtz`.

`pairs.bin` is a flat array of little-endian operand pairs `a b`, each operand `⌈k/8⌉` bytes
(`k = w + p`); `out.bin` receives one result word of the same width per pair.
Driven by `validate.py`; see svgolf/tasks/fdivp/spec_validate/README.md.
-/

open SvGolf.IEEE754

def parseMode : String → Option RoundingMode
  | "rne" => some .roundTiesToEven
  | "rna" => some .roundTiesToAway
  | "rtp" => some .roundTowardPositive
  | "rtn" => some .roundTowardNegative
  | "rtz" => some .roundTowardZero
  | _ => none

/-- Read the little-endian word of `nb` bytes at byte offset `off`. -/
def readWord (ba : ByteArray) (off nb : Nat) : Nat := Id.run do
  let mut acc := 0
  for i in [0:nb] do
    acc := acc + (ba.get! (off + i)).toNat * 2 ^ (8 * i)
  return acc

def pushWord (ba : ByteArray) (x nb : Nat) : ByteArray := Id.run do
  let mut out := ba
  for i in [0:nb] do
    out := out.push (UInt8.ofNat (x / 2 ^ (8 * i) % 256))
  return out

/-- Lean core's logical float model at the same parameters (independent cross-check). -/
def coreDiv (f : Format) (a b : BitVec f.k) : BitVec f.k :=
  let spec : Float.Model.Format :=
    { mantissaBitsWithoutImplicit := f.p - 1, hm := by have := f.hp; omega,
      exponentBits := f.w, he := by have := f.hw; omega }
  have h : spec.numBits = f.k := rfl
  h ▸ Float.Model.UnpackedFloat.pack spec
    (Float.Model.UnpackedFloat.div spec
      (Float.Model.UnpackedFloat.unpack spec (h ▸ a))
      (Float.Model.UnpackedFloat.unpack spec (h ▸ b)))

def main (args : List String) : IO UInt32 := do
  match args with
  | [impl, ws, ps, ms, inp, outp] =>
    let some w := ws.toNat? | throw (IO.userError "bad w")
    let some p := ps.toNat? | throw (IO.userError "bad p")
    let some mode := parseMode ms | throw (IO.userError "bad mode")
    if h : 2 ≤ w ∧ 2 ≤ p then
      let f : Format := { w := w, p := p, hw := h.1, hp := h.2 }
      let nb := (f.k + 7) / 8
      let op : BitVec f.k → BitVec f.k → BitVec f.k ←
        match impl with
        | "spec" => pure (divide f mode)
        | "core" =>
          if mode == .roundTiesToEven then pure (coreDiv f)
          else throw (IO.userError "core model is roundTiesToEven only")
        | _ => throw (IO.userError "impl must be spec or core")
      let data ← IO.FS.readBinFile inp
      let n := data.size / (2 * nb)
      let mut out := ByteArray.emptyWithCapacity (n * nb)
      for i in [0:n] do
        let a := readWord data (2 * nb * i) nb
        let b := readWord data (2 * nb * i + nb) nb
        let r := op (BitVec.ofNat f.k a) (BitVec.ofNat f.k b)
        out := pushWord out r.toNat nb
      IO.FS.writeBinFile outp out
      IO.println s!"{impl} w={w} p={p} {ms}: {n} pairs"
      return 0
    else
      throw (IO.userError "need 2 ≤ w and 2 ≤ p")
  | _ =>
    IO.eprintln "usage: Run.lean <spec|core> <w> <p> <rne|rna|rtp|rtn|rtz> <pairs.bin> <out.bin>"
    return 2
