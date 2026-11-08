import SvGolf.TaskReact

/-!
# Task `arbiter`: a fair N-client arbiter
# (TRUSTED text, final, decided 2026-11-07; written 2026-11-05, txtask-v2's rules 2026-11-06; the reactive kind `ReactTask`, `SvGolf/TaskReact.lean`)

Module (port order as written; `N` is the module's parameter):

```systemverilog
module arbiter #(parameter int N = 8) (
  input  logic         clk, rst,
  input  logic [N-1:0] req,
  output logic [N-1:0] gnt
);
```

## What the statement says (`Statement sem`)

For every `N` with `1 ≤ N` and `N·N < 2^31`, the design `sem N`:

1. has exactly the ports above, and no two declarations of one name (`Interface`);
2. is clocked by `clk` alone with no asynchronous reset, never reads `clk` as data (`ClockedBy clk
   none`), has no combinational path from an input port to an output port (`MooreOut`), and
   terminates from every power-up state under every schedule and known stimulus (`TerminatesPU`);
3. has no construct that can create an `x` from known operands (`XSafe`, txtask-v2's rule 3);
4. from EVERY power-up state (every register and variable, 2-state ones included, starts at some
   0/1 value, one value per signal), under every schedule, on every known stimulus, in every
   completed run, at every RESET RELEASE `c1` (the entry `c1 - 1` asserts `rst`) and for every list
   `x0 :: xs` of request vectors that the entries `c1 - 1, c1, c1 + 1, …` drive (the reset entry,
   then the entries with `rst` = 0), the snapshots `c1 - 1, c1, c1 + 1, …` show known grant vectors
   `y0, ys[0], ys[1], …` with
   * **G0, reset**: `y0 = 0` (no grant comes out of reset);
   * **G1, mutual exclusion**: every `ys[j]` has at most one bit set;
   * **G2, no spurious grant**: a bit of `ys[j]` is set only if the same bit of `xs[j]` is;
   * **G3, work conservation**: `xs[j] ≠ 0` implies `ys[j] ≠ 0`;
   * **G4, bounded fairness** with `K = N - 1`: if requester `i` requests at all `N` entries
     `j, …, j + N - 1` of the segment, then `ys[j + k]` grants `i` for some `k ≤ N - 1`.

The grant in snapshot `c` answers the request of entry `c` (the one the edge of cycle `c`
samples); by `MooreOut` it is what the requesters see on `gnt` for the whole next clock period,
while they drive entry `c + 1`. So a requester learns of its grant one period after it asserts its
request: a REGISTERED (Moore) arbiter, like verilog-axis `arbiter.v` (`grant_reg`), or a Mealy one
(OpenTitan `prim_arbiter_tree`) behind one output register.

## Decided 2026-11-05 (the study's defaults; reasons in `README.md`)

* Moore observation (`MooreOut`), from the kind.
* Safety (G1 to G3, per cycle: the ghost state is `Unit`) and bounded response (G4) with the bound
  `K = N - 1` fixed here, not declared by the golfer: no design can beat it (`bound_tight`, among the
  task's kernel-checked refutations, `tests/arbiter/negative/`), so a declared `K` would be a dead column.
* No environment assumption beyond reset and known inputs.
* "Any fair" policy: the statement pins fairness, not a grant order.
* Scored at `N = 8` (`task.json`).

## Why it cannot be satisfied vacuously or gamed (the kind's list, `SvGolf/TaskReact.lean`, plus)

* **Request-ignoring designs.** The free-running token ring that is SYNTCOMP-minimal for the
  simple and round-robin arbiter families grants without requests (G2), the time-sliced ring
  gated by the requests wastes slots (G3), grant-everyone breaks G1, never-grant breaks G3 and G4,
  fixed priority starves (G4). The task's refutations (`tests/arbiter/negative/`) refute four of them
  by kernel-evaluated runs.
* **The Mealy phantom.** Register `last <= req` and drive `gnt = (req == last) ? g : req` from a
  correct registered grant `g`: every snapshot shows `g`, while in silicon `gnt = req` whenever
  `req` changes, which breaks mutual exclusion. `MooreOut` rejects it (`mealy_refuted`).
* **Unknown and unreset values** (rules 2 and 3). The claims hold from every power-up state, so a
  design may keep an unreset register only where its value does not matter. A correct round-robin
  behind `if (~u)` on a never-reset, self-holding `u` fails G4 from the power-up `u = 0`
  (`xopt_refuted`); behind `if (&u)` on a never-reset 2-state rotating ring `u`, from `u` all ones
  (`ring_refuted`; ls-sv's `x` start would have made `u` 0 for ever); and with a flag set at the
  first reset edge from the pre-reset `&u`, from `u` all ones (`reset_edge_refuted`). These runs
  are ls-sv's: that the scored netlist agrees with them on defined values (obligation C) is
  SAMPLED by the post-synthesis check, not proved. Yosys keeps such a register as a flop that
  powers up to some value, and the checker refuses a never-loaded one (`u <= u`) where the pinned
  flow removes its flip-flop while reads of it remain (it resolves each read separately).
* **Never-reset grant flops.** G0 requires a KNOWN zero at every reset snapshot, from every
  power-up.

## What it does NOT pin, on purpose

* which requester wins (any policy meeting G4 is legal: round-robin pointer, mask, rotating
  priority, matrix/LRU), and the state encoding (one-hot mask, binary pointer, matrix);
* the grant of a requester that drops its request before `N` consecutive requests: the reference
  round-robin itself starves a requester that asks at every other entry (measured, `README.md`),
  so a stronger form would reject every round-robin;
* anything while `rst` = 1 except the reset snapshot, and anything before the first reset.
-/

namespace SvGolf

open LeanModels.Sv

namespace Tasks.Arbiter

/-- At most one bit of `g` is set (one-hot or zero). -/
def AtMostOne {N : Nat} (g : BitVec N) : Prop :=
  ∀ i j, g.getLsbD i = true → g.getLsbD j = true → i = j

/-- **One cycle of arbitration**: `gnt` grants at most one requester (G1), only a requester of
`req` (G2), and someone whenever anyone requests (G3). Together: `gnt = 0` if `req = 0`, else `gnt`
is one bit of `req`. -/
def Grants {N : Nat} (req gnt : BitVec N) : Prop :=
  AtMostOne gnt ∧ (∀ i, gnt.getLsbD i = true → req.getLsbD i = true) ∧ (req ≠ 0#N → gnt ≠ 0#N)

/-- **The task.** The ghost state is trivial (the safety property is per cycle); the obligations
are the requesters `i < N`: requesting triggers, being granted responds. -/
def task : ReactTask Nat where
  inRange N := 1 ≤ N ∧ N * N < 2 ^ 31
  clk := "clk"
  rst := "rst"
  inputs N := [("req", N)]
  outputs N := [("gnt", N)]
  atReset N := fun (g, ()) => g = 0#N
  Ghost _ := Unit
  ginit _ := ()
  gnext _ _ _ _ := ()
  safe _ _ := fun (r, ()) (g, ()) => Grants r g
  Obl N := Fin N
  trig _ i := fun (r, ()) => r.getLsbD i.val = true
  resp _ i := fun (g, ()) => g.getLsbD i.val = true

/-- **The challenge statement**: the task at every `N` in range with the response bound `N - 1`
(G4: `N` consecutive requests are granted at least once). -/
abbrev Statement (sem : Nat → LeanModels.Sv.Design2) : Prop :=
  task.Statement sem (fun N => N - 1)

/-! ## Sanity checks on the statement's data (proved; they add nothing to the trusted base) -/

/-- The scoring point `N = 8` and the probe points are in range; `N = 0` is not, nor any `N` with
`N·N ≥ 2^31` (a matrix arbiter declares `N·N` bits). -/
example : task.inRange 1 ∧ task.inRange 2 ∧ task.inRange 3 ∧ task.inRange 8 ∧
    ¬ task.inRange 0 ∧ ¬ task.inRange 46341 := by
  simp [task]

/-- The port names are distinct. -/
example : ["clk", "rst", "req"].Nodup ∧ "gnt" ∉ ["clk", "rst", "req"] := by decide

/-- `Grants` with the bit indices bounded by `N` (bits at `i ≥ N` read `false`): decidable on
concrete vectors. -/
theorem grants_iff {N : Nat} {r g : BitVec N} : Grants r g ↔
    (∀ i, i < N → ∀ j, j < N → g.getLsbD i = true → g.getLsbD j = true → i = j) ∧
    (∀ i, i < N → g.getLsbD i = true → r.getLsbD i = true) ∧ (r ≠ 0#N → g ≠ 0#N) := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨fun i _ j _ hi hj => h1 i j hi hj, fun i _ hi => h2 i hi, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨fun i j hi hj => h1 i (BitVec.lt_of_getLsbD hi) j (BitVec.lt_of_getLsbD hj) hi hj,
      fun i hi => h2 i (BitVec.lt_of_getLsbD hi) hi, h3⟩

/-- A one-hot grant of a requester is a legal arbitration; so is no grant without requests. -/
example : Grants (0b1011#4) (0b0010#4) ∧ Grants (0#4) (0#4) :=
  ⟨grants_iff.2 (by decide), grants_iff.2 (by decide)⟩

/-- The trivial answers are not legal arbitrations: grant everyone (G1), grant client 0 always
(G2), never grant (G3). -/
example : ¬ Grants (0b11#2) (0b11#2) ∧ ¬ Grants (0b00#2) (0b01#2) ∧ ¬ Grants (0b01#2) (0b00#2) :=
  ⟨fun h => absurd (grants_iff.1 h) (by decide), fun h => absurd (grants_iff.1 h) (by decide),
    fun h => absurd (grants_iff.1 h) (by decide)⟩

/-- **Fixed priority starves** (G4 at `N = 2`, `K = 1`): both clients request twice in a row and
client 0 is granted both times, so the segment's guarantee fails for client 1. -/
example : ¬ task.Guar 2 1 [(0b11#2, ()), (0b11#2, ())] (0#2, ()) [(0b01#2, ()), (0b01#2, ())] := by
  rintro ⟨-, -, hr⟩
  obtain ⟨i, y, hi, hy, hg⟩ := hr (⟨1, by decide⟩ : Fin 2) 0 (by decide) (fun i x hi hx => by
    have : i = 0 ∨ i = 1 := by omega
    rcases this with rfl | rfl <;> (have hx' := Option.some.inj hx; subst hx'; exact rfl))
  have : i = 0 ∨ i = 1 := by omega
  rcases this with rfl | rfl <;> (have hy' := Option.some.inj hy; subst hy'; exact Bool.false_ne_true hg)

end Tasks.Arbiter

end SvGolf
