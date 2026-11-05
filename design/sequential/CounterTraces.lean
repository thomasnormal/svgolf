import CounterCycle

/-!
# The counter fixture's contract on concrete traces (Gate 0 step 3 of `svgolf/PLAN4.md`)

`CONTRACT.md` asks for concrete legal and illegal traces of the counter fixture as `#guard`s over
`run2`, so that the contract can be executed before any checker exists. Here:
- the counter (`cntD`, the design `cnt.sv` loads to; `CounterInst.lean` proves the two equal at
  every `N ≥ 1`) and three wrong variants run on concrete stimuli;
- `counterOK`, an EXECUTABLE READING of `cntTask`'s claim (`SeqTask.Follows`), checks the
  resulting traces: from every entry that asserts reset on, as long as the inputs are known, the
  snapshot's `q` is the spec counter's value.

`counterOK` is an illustration of the claim, not a proved equivalent of it. The trusted statement is
the `Prop`, and `CounterCycle.lean`'s `cnt_statement` proves it for every `N`.
-/

namespace SvGolf.Seq.Counter

open LeanModels.Sv

/-- The executable reading of the counter's claim on one finite run: walk the stimulus and the
trace together, tracking the spec state from the most recent reset (`none` before the first reset,
or after an entry whose inputs are not known); wherever it is tracked, `q` must equal it. -/
def counterOK (N : Nat) (stim tr : List SvState) : Bool :=
  go (stim.zip tr) none
where
  go : List (SvState × SvState) → Option (BitVec N) → Bool
    | [], _ => true
    | (e, st) :: rest, s =>
        let one := some (LVec.ofBitVec 1#1)
        let zero := some (LVec.ofBitVec 0#1)
        let r := SvState.lookup e "rst"
        let en := SvState.lookup e "en"
        let s' : Option (BitVec N) :=
          if r == one then some 0#N
          else if r == zero then
            match s with
            | some v => if en == one then some (v + 1#N) else if en == zero then some v else none
            | none => none
          else none
        (match s' with
         | some v => SvState.lookup st "q" == some (LVec.ofBitVec v)
         | none => true) && go rest s'

/-- One stimulus entry: `rst` and `en` (the clock is not driven: it is not observed). -/
def entry (rst en : Nat) : SvState := [("rst", LVec.ofNat 1 rst), ("en", LVec.ofNat 1 en)]

/-- Run a design on a stimulus (source schedule) and check the claim. -/
def runOK (N : Nat) (d : Design2) (stim : List SvState) : Bool :=
  match run2 d σ_src 1000 stim with
  | .ok tr => counterOK N stim tr
  | _ => false

/-! ## The designs: the counter and three wrong variants (same ports) -/

/-- The counter's ports with another `always_ff` body. -/
def cntWith (N : Nat) (body : Stmt2) : Design2 := { cntD N with processes := #[.alwaysFF "clk" body] }

def qInc (N : Nat) : Expr2 := .binary .add (.ident "q") (.resize N (.lit ⟨#[.l1]⟩))
def qZero (N : Nat) : Expr2 := .lit (LVec.replicate N .l0)

/-- WRONG: the enable is ignored (counts every cycle). -/
def cntNoEn (N : Nat) : Design2 :=
  cntWith N (.ifStmt (.ident "rst") (.nbaAssign (.ident "q") (qZero N))
    (some (.nbaAssign (.ident "q") (qInc N))))

/-- WRONG: the reset is not honoured (`q` is never cleared, so it stays x). -/
def cntNoRst (N : Nat) : Design2 :=
  cntWith N (.ifStmt (.ident "en") (.nbaAssign (.ident "q") (qInc N)) none)

/-- WRONG: an off-by-one at the wrap (counts `0 .. 2^N - 2`, then back to 0). -/
def cntWrapEarly (N : Nat) : Design2 :=
  cntWith N (.ifStmt (.ident "rst") (.nbaAssign (.ident "q") (qZero N))
    (some (.ifStmt (.ident "en")
      (.ifStmt (.binary .eq (.ident "q") (.lit (LVec.ofNat N (2 ^ N - 2))))
        (.nbaAssign (.ident "q") (qZero N))
        (some (.nbaAssign (.ident "q") (qInc N))))
      none)))

/-! ## The traces -/

/-- LEGAL: a reset, five enabled cycles (`q` wraps from 3 to 0 at `N = 2`), a held cycle, a
mid-run reset with the enable high (the reset wins), one more count. -/
def stimLegal : List SvState :=
  [entry 1 0, entry 0 1, entry 0 1, entry 0 1, entry 0 1, entry 0 1, entry 0 0, entry 0 1,
   entry 1 1, entry 0 1]

/-- No reset at all: the claim is vacuous (C1: nothing before the first reset). -/
def stimNoReset : List SvState := [entry 0 1, entry 0 0, entry 0 1, entry 0 1]

-- the counter satisfies the claim on the legal trace, at N = 2 (with the wrap) and N = 4
#guard runOK 2 (cntD 2) stimLegal
#guard runOK 4 (cntD 4) stimLegal
-- each wrong design is caught on it
#guard !runOK 2 (cntNoEn 2) stimLegal
#guard !runOK 2 (cntNoRst 2) stimLegal
#guard !runOK 2 (cntWrapEarly 2) stimLegal
-- the loaded `cnt.sv` behaves as `cntD` here too (the `#guard` twin of `cnt_sem_eq`)
#guard runOK 2 (cntSv.sem 2) stimLegal
-- without a reset nothing is claimed, so even a wrong design passes (vacuously)
#guard runOK 2 (cntNoEn 2) stimNoReset

end SvGolf.Seq.Counter
