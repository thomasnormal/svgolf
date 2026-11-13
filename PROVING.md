# Proving a svGolf task

This guide is for contestants. It explains how to prove that your circuit meets a task's
statement, using the `sv_comb` tactics (`sv_structure`, `sv_equations`, `sv_cover`, `sv_bridge`) of
[Proglib](https://github.com/thomasnormal/proglib) (formerly lean-surfaces) and the plain-Lean library
`LeanModels.Sv.CombLib`. Two complete, checked examples
are the references of the `add` and `mul` tasks:

| task | tactic proof (read this first) | by-hand proof (no tactics, the fallback) |
|---|---|---|
| `add` | `tasks/add/reference/add_n.lean` | `tasks/add/reference/add_n_byhand.lean` |
| `mul` | `tasks/mul/reference/mul_n.lean` | `tasks/mul/reference/mul_n_byhand.lean` |
| `clmul` (section 3.1) | `tasks/clmul/reference/clmul_n.lean` (the array without carries; zero-iteration loops, a `(row, 0, 0)` rank) | |
| `aes_sbox` (fixed size, 113 flat sites; section 12) | `tasks/aes_sbox/reference/sbox_bp.lean` (`sv_structure` and `sv_equations` decide the flat netlist's obligations) | |
| `fdivp` (two parameters `W`, `P`; word-level sites and generate families) | `tasks/fdivp/reference/fdivp.lean` (restoring division, one `Glue.chain` from the 34 printed equations); `tasks/fdivp/reference/fdivp_newton.lean` (Newton-Raphson: the run-time `*` and a `$clog2` localparam, sections 4 and 17); `tasks/fdivp/reference/fdivp_srt.lean` (radix-4 SRT: a family of 19 sites per stage, the selection tables as `?:` trees over constants checked by `decide`, the shared obligations of `sv_structure` handed to `sv_equations`) | |
| `matmul` (clocked, `TxTask`; section 19) | `tasks/matmul/reference/matmul_g1.lean` (`N²` multiply-accumulate units, `lat = N`; `TxTask.satisfiedAtV2_of_phases`) | |
| `sorter` (clocked stream, `StreamTask`; section 19) | `tasks/sorter/reference/sorter_ins.lean` (the insertion-cell array, `lat = 2N`; `StreamTask.satisfiedAtV2_of_phases`) | |
| `arbiter` (clocked, reactive, `ReactTask`; section 20) | `tasks/arbiter/reference/rr_mask.lean` (the registered mask round-robin, every `N` with `1 ≤ N`, `N·N < 2^31`; `ReactTask.satisfiedAt_of_rank` with an invariant and a rank) | |

Both proofs are for every `N` in their task's range (`1 ≤ N < 2^31` for `add`, `1 ≤ N < 2^30` for `mul`),
accepted by `check.py`, and depend only on `propext`,
`Classical.choice` and `Quot.sound`. [README.md](README.md) has the rules and the checker's
stages; [REFUSALS.md](REFUSALS.md) lists everything the checker refuses. Paths under `LeanModels/`, `docs/`,
`extractors/` and `Examples/` are Proglib's (the Lake package `lean-models`; in a clone of svGolf's public repository,
under `.lake/packages/lean-models/` after `lake build`); every other path is svGolf's.

## 0. The loop

A submission is `solution.sv` and `Solution.lean`. Run the checker once with `--keep`:

```bash
python3.12 check.py tasks/add solution.sv Solution.lean --keep
```

Even if the proof fails, the result's `dev_hint` is a command that recompiles your `Solution.lean`
against the staged design (`Submission.Design`), so you can iterate on the proof alone, without
the scoring and simulation stages (3 and 7 seconds for the two tactic references with the default light post-synthesis check; the full one, which `leaderboard.py add` runs, is 3 and 45 seconds). The tactics print what they see when you
ask them: `sv_structure?` and `sv_equations?` change nothing and print the design's sites and
the obligations. Use them first.

**Score first, prove later.** `python3.12 score/ppa.py solution.sv --task tasks/add --no-mapped [--path]`
gives the ranked area and delay (their product is the ranked number) in about 2 seconds with no Lean: the
source gate and the pinned flow only, no banlist, no 4-state rules, no ls-sv and no simulation. Choose the
design you will prove with it, then run `--unproved` on that one.

**The loop that works before you have a proof.** `--unproved` runs every stage that needs no
proof (15 seconds) and, with `--stage-dir`, leaves the staged design in a directory of your
choice, so you can compile probe files against it without ever running the full checker:

```bash
python3.12 check.py tasks/add solution.sv --unproved --stage-dir stage   # source ... postsynth, then stops
LEAN_PATH=stage/build lake env lean Probe.lean                           # the probe file below
```

(`--unproved` with `--keep` or `--stage-dir` prints a `dev_hint` too: exactly this command, with a
literal `<YourFile>.lean` for the probe file, which starts with `import Submission.Design`. Your
Lean wrapper (`SVGOLF_LEAN_WRAP` / `--lean-wrap`) is already in front of `lake` in every `dev_hint`.
`--stage-dir` is the stable alternative to `--keep`, which leaves a fresh temporary directory
behind on every run.) Once `Solution.lean` exists, the same
`LEAN_PATH=... lake env lean Solution.lean` is the fast inner loop; the full run
(`check.py tasks/add solution.sv Solution.lean`) takes about a minute and is the only one that
accepts.

**The time limit counts CPU seconds** (decided 2026-11-05, 300 s since 2026-11-06; README.md, "Proof effort"): 300 s of
user plus system time of the Lean process that compiles `Solution.lean`, every thread counted, so
a loaded machine does not push a proof over it; a wall-clock backstop of 5 times it (1500 s) stops a
proof that waits instead of computing. The `solution` stage's stderr line gives both readings
(`Lean used 37.2 CPU s of the task's 300 s CPU limit (12%), in 29.5 s of wall clock`) and warns past
half of the limit. In the inner loop, `/usr/bin/time -p` in front of `lake env lean` reads the same
two numbers (its `user` plus `sys` are the CPU seconds, `real` the wall clock; `lake` adds a fraction
of a second).

**A probe file.** `sv_structure?` and `sv_equations?` take no arguments (`sv_structure? (rank := …)` is a
syntax error): they print what the tactics see and change nothing. This `Probe.lean` prints both listings
for the `add` reference staged as above (compiled against it, 2026-11-05); for your own design, change
the rank in part 2 once part 1 has shown you the sites:

```lean
import Submission.Design
import SvGolf.Comb
import LeanModels.Sv.CombEqTactic
import LeanModels.Sv.CombLib

namespace Submission
open LeanModels.Sv LeanModels.Sv.CombView LeanModels.Sv.CombLib LeanModels.Sv.CombEq SvGolf

-- 1. The sites and the relation a rank must satisfy. `sv_structure?` takes no arguments;
--    `sv_structure` (no rank) then proves `CombDesign` alone, so this part compiles.
example (N : Nat) (hN : 1 ≤ N) : CombDesign (design.sem N) := by
  sv_structure?
  sv_structure
  all_goals (intros; omega)

-- 2. With a rank chosen from that listing: the triple the solution takes apart.
theorem probe_struct (N : Nat) (hN : 1 ≤ N) :
    CombDesign (design.sem N) ∧ Acyclic (design.sem N) ∧ SharedObl design.pdesign [N] := by
  sv_structure (rank := rippleRank (fun p => if p = 0 then 0 else N + 1) (fun _ _ i => i.toNat + 1))
  all_goals (intros; omega)

-- 3. The solution's first lines, then `sv_equations?`: the equations and the obligations, printed.
--    The goal stays open, so Lean ends with `unsolved goals`: the goal `sv_equations` starts from.
example : Goal := by
  intro N hN
  have hN' : 1 ≤ N := hN.1
  obtain ⟨hc, ha, hso⟩ := probe_struct N hN'
  refine CombTask.satisfiedAt_of_comb (by sv_interface) hc ha ?_
  intro st heqs hs v hv
  sv_equations?

end Submission
```

What it prints (the two listings whole, then the first obligations and the end of the error, which
is part 3's open goal; parts 1 and 2 compile, and that one `unsolved goals` is the only error):

```
sv_structure: parameters [N]
declarations:
  input  a [N - 1 : 0]
  input  b [N - 1 : 0]
  input  cin
  output s [N - 1 : 0]
  output cout
         c [N : 0]
plain sites (module-level assigns):
  plain#0 : drives c[0]   reads [cin]
  plain#1 : drives cout   reads [c[N]]
family `g_bit`: for i in [0, N):
  g_bit#0[i] : drives s[i]   reads [a[i], b[i], c[i]]
  g_bit#1[i] : drives c[i + 1]   reads [a[i], b[i], c[i], a[i], b[i]]
rank relation a certificate must satisfy (writer < reader whenever the read window
overlaps the written window; ranks are functions of the site identity):
  rank(plain#0) < rank(plain#1)   [plain#1 reads c[N]; plain#0 drives c[0]]
  rank(g_bit#1[i']) < rank(plain#1)   [plain#1 reads c[N]; g_bit#1[i'] drives c[i' + 1]]
  rank(plain#0) < rank(g_bit#0[i])   [g_bit#0[i] reads c[i]; plain#0 drives c[0]]
  rank(g_bit#1[i']) < rank(g_bit#0[i])   [g_bit#0[i] reads c[i]; g_bit#1[i'] drives c[i' + 1]]
  rank(plain#0) < rank(g_bit#1[i])   [g_bit#1[i] reads c[i]; plain#0 drives c[0]]
  rank(g_bit#1[i']) < rank(g_bit#1[i])   [g_bit#1[i] reads c[i]; g_bit#1[i'] drives c[i' + 1]]
sv_equations: the netlist view and the obligations
  (Boolean equations: every supported read is known in a settled state, `CombKnown.reads_known`)
  eq_c_plain_0 : st.boolAt "c" 0 = st.boolAt "cin" 0
  eq_cout_plain_1 : st.boolAt "cout" 0 = st.boolAt "c" N
  eq_s_g_bit_0 : ∀ (i : Nat), i < N → st.boolAt "s" i = (st.boolAt "a" i ^^ st.boolAt "b" i ^^ st.boolAt "c" i)
  eq_c_g_bit_1 : ∀ (i : Nat),
  i < N →
    st.boolAt "c" (i + 1) =
      (st.boolAt "a" i && st.boolAt "b" i || st.boolAt "c" i && (st.boolAt "a" i ^^ st.boolAt "b" i))
  known_c_plain_0 : (∃ v, st.lookup "c" = some v ∧ v.width = N + 1) ∧ KnownBit st "c" 0
  known_cout_plain_1 : (∃ v, st.lookup "cout" = some v ∧ v.width = 1) ∧ KnownBit st "cout" 0
  known_s_g_bit_0 : ∀ (i : Nat), i < N → (∃ v, st.lookup "s" = some v ∧ v.width = (↑N + -1).natAbs + 1) ∧ KnownBit st "s" i
  known_c_g_bit_1 : ∀ (i : Nat), i < N → (∃ v, st.lookup "c" = some v ∧ v.width = N + 1) ∧ KnownBit st "c" (i + 1)
  stable aliases (copies of the above; same statements):
    eq_c_1 := eq_c_plain_0    known_c_1 := known_c_plain_0
    eq_cout_1 := eq_cout_plain_1    known_cout_1 := known_cout_plain_1
    eq_s_1 := eq_s_g_bit_0    known_s_1 := known_s_g_bit_0
    eq_c_2 := eq_c_g_bit_1    known_c_2 := known_c_g_bit_1
  auto, inRange: from `hso` (the shared obligations of the structure stage, `SharedObl`)
  [bitRead_1] ⊢ ∀ (i : Int), 0 ≤ i → i < ↑N → i ≤ ↑(↑N + -1).natAbs ∧ i ≤ ↑N
  [bitRead_2] ⊢ ∀ (i : Int), 0 ≤ i → i < ↑N → i ≤ ↑(↑N + -1).natAbs ∧ i ≤ ↑N ∧ i ≤ ↑(↑N + -1).natAbs
  ... (cover_1-3, inputsKnown_1-3)
Probe.lean:24:18: error: unsolved goals
N : Nat
hN : Tasks.Add.task.inRange N
hN' : 1 ≤ N
...
⊢ HoldAll st (Tasks.Add.task.outputs N) (Tasks.Add.task.fn N v)
```

How the listings name things. `plain#k` is the k-th module-level `assign` in source order, from 0 (here
`assign c[0] = cin;` is `plain#0` and `assign cout = c[N];` is `plain#1`); `g_bit#k[i]` is the k-th
assign, from 0, inside the generate block labelled `g_bit`, at genvar value `i`. A rank's `pr p` gets the
`k` of `plain#k`, its `fr label pos i` the label, the `k` and `i` of a family site (section 2.1). Each
site's equation is named after it (`eq_c_plain_0`, `eq_s_g_bit_0`) and has a stable alias
`eq_<signal>_<n>` that counts, from 1, the assigns writing that signal (`eq_c_1`, `eq_c_2`): use the
aliases in a proof, and a reordering inside a block will not rename them.

**A loop that does not start at 0, and a constant index.** Taking bit 0 of the adder out of its loop
(module-level `assign c[1] = (a[0] & b[0]) | (a[0] & cin) | (b[0] & cin);`, the loop from `i = 1`) prints
two shapes worth knowing:

```
eq_c_plain_1 : st.boolAt "c" (Int.toNat 1) =
  (st.boolAt "a" 0 && st.boolAt "b" 0 || st.boolAt "a" 0 && st.boolAt "cin" 0 || st.boolAt "b" 0 && st.boolAt "cin" 0)
eq_c_g_bit_0 : ∀ (i : Nat), 1 ≤ ↑i → i < N → st.boolAt "c" (i + 1) =
  (st.boolAt "a" i && st.boolAt "b" i || st.boolAt "c" i && (st.boolAt "a" i ^^ st.boolAt "b" i))
```

(as `sv_equations?` printed them for a newcomer's design, 2026-11-05). The constant index stays
`Int.toNat 1`, so `rw [h]` against a goal that says `st.boolAt "c" 1` finds no match: normalize the
hypothesis first, `rw [show Int.toNat 1 = 1 from rfl] at h`. The loop's lower bound is a comparison over
`Int` (`1 ≤ ↑i`) while the upper one is over `Nat`: pass `(by omega)` for it, not a `Nat` fact
(`eq_c_g_bit_0 i (by omega) hi`). A proof of such a design splits on `i = 0` or `1 ≤ i` wherever the
reference used one equation for every bit.

Two advisory checks of `--unproved` save a proof attempt that cannot work; neither changes the
verdict (the stage stays `unproved`). **Is the design wrong?** If the task ships an oracle (README,
the `oracle` row of the task table), `--unproved` compares your design's outputs on its ~250
light post-synthesis vectors (~4000 with `--postsynth full`) with the task's function and, on a disagreement, prints one `functional:` warning (stderr,
and `warnings` in the JSON) naming the first failing input, with `stages.postsynth.functional`
holding up to three examples. A wrong design has no proof, and this is much easier to read than the
`Application type mismatch` the proof then fails with. **Can the tactics read the design?** Add
`--tactics` (one extra Lean job, about 2 seconds, combinational tasks): the result gets
`tactics: {"in_fragment": true|false, "message": ...}`, the message being `ok` or the first line of
`sv_structure?`'s own refusal, the ones listed in section 4 (`?:`, `localparam`, `always_comb`, ...).
`in_fragment: true` means the tactics parse the design, not that your proof will go through.

A proof file starts like this (the tactic modules are on the import allowlist, like all of
`LeanModels.Sv.*`):

```lean
import Submission.Design
import SvGolf.Comb
import LeanModels.Sv.CombEqTactic   -- sv_structure, sv_equations, sv_cover, CombView
import LeanModels.Sv.CombLib        -- bit functions, ripple row, AddView, MulNetlistView

namespace Submission
open LeanModels.Sv LeanModels.Sv.CombView LeanModels.Sv.CombLib LeanModels.Sv.CombEq SvGolf
```

and ends with `theorem solution : Goal`.

## 1. The shape of a proof

`Submission.Goal` is the task's statement for your design: for every `N` in range,

1. **Interface**: the input and output ports are exactly the task's (names, order, widths);
2. **No clocked process, no combinational loop, and every run terminates** (no loop: the design lowers
   to continuous assigns with an `Acyclic` rank, the certificate the helpers below ask for anyway);
3. **Computes**: whenever the inputs are driven with known values, the outputs hold exactly the
   task's function of them.

`CombTask.satisfiedAt_of_comb` (in `SvGolf/Comb.lean`) reduces the statement, for a design made of
continuous assigns, to four things, and that is the shape of every tactic proof:

| obligation | what it says | tool | what you write |
|---|---|---|---|
| ports | the declared inputs and outputs are the task's | `sv_interface` | nothing (one line, see 2.2) |
| structure | every process is an `assign` writing in-range bits, no two assigns write the same bit, and there is a rank that orders every read after its write (so no combinational loop) | `sv_structure` (`CombDesign` and `Acyclic` in one theorem) | closers for the small goals it returns; the rank |
| equations and knownness | each assign as an equation over `Bool` (`st.boolAt "c" (i+1) = ...`), and every driven bit is known (not `x`/`z`) | `sv_equations` | closers for the obligations it returns; the coverage goals the search cannot do |
| arithmetic | the equations imply the task's function | plain Lean, `CombLib` | one theorem, the only real mathematics |

Everything else (the statement's bookkeeping about runs, schedules and clocks) is done by
`CombTask.satisfiedAt_of_comb` and the tactics' soundness theorems; none of it is yours.

## 2. A worked example: the adder

`reference/add_n.sv` is a ripple-carry adder in one generate loop: `c[0] = cin`,
`s[i] = a[i] ^ b[i] ^ c[i]`, `c[i+1] = (a[i] & b[i]) | (c[i] & (a[i] ^ b[i]))`, `cout = c[N]`.
The whole proof, `reference/add_n.lean`, is 84 code lines (the by-hand one: 509).

### 2.1 Structure

```lean
theorem add_struct (N : Nat) (hN : 1 ≤ N) : CombDesign (design.sem N) ∧ Acyclic (design.sem N) := by
  sv_structure (rank := rippleRank (fun p => if p = 0 then 0 else N + 1) (fun _ _ i => i.toNat + 1))
  all_goals (intros; omega)
```

One theorem proves both facts: the tactic applies the soundness theorem once and normalizes each
obligation once. (The two separate theorems of the older recipe, `CombDesign` alone with
`sv_structure` and `Acyclic` with `sv_structure (rank := …) [using hc]`, repeat the in-range
normalizations: 15 to 22 % of the elaboration work of the five references, section 11. They still work, and
are the way to get one fact without the rank.) The solution takes the two apart with
`obtain ⟨hc, ha⟩ := add_struct N hN`.

**Hand the in-range obligations to `sv_equations` (perf, 2026-11-04).** `sv_equations` needs two of the obligations
`sv_structure` has just normalized, `auto` and `inRange`, and without help it normalizes them a second time (fdivp 104,
Newton 139, `mul_tree` 78, `add_n` 19 thousand heartbeats: 5 to 14% of the file). Ask `sv_structure` for them as a third
conjunct and the second normalization goes:

```lean
theorem add_struct (N : Nat) (hN : 1 ≤ N) :
    CombDesign (design.sem N) ∧ Acyclic (design.sem N) ∧ SharedObl design.pdesign [N] := by
  sv_structure (rank := rippleRank (fun p => if p = 0 then 0 else N + 1) (fun _ _ i => i.toNat + 1))
  all_goals (intros; omega)
```

`SharedObl X.pdesign args` (`LeanModels/Sv/CombShared.lean`) is the two obligations stated once for the design family
(`design.pdesign`, the literal `load_sv` defines next to `design.sem`) at the parameter list (`[N]`; `[W, P]` for two
parameters, in the order of `design.sem`'s binders). `sv_structure` returns the same goals as for the bundle. The
solution takes the three apart, `obtain ⟨hc, ha, hso⟩ := add_struct N hN`, and `sv_equations` finds `hso` in the context:
it returns no `auto_k` and no `inRange_k` goal (`sv_equations?` says `auto, inRange: from hso`). Without the third
conjunct both tactics behave as before. (Not yet for a design with an `always_comb` body: its recognizer is another one.)

`sv_structure?` shows how the tactic reads the design: the declarations, the **sites** (every
assign, with the bits it drives and the bits it reads: `plain#k` for the module-level assigns,
`g_bit#0[i]` for the first assign of generate block `g_bit` at index `i`) and the relation a rank
must satisfy:

```
plain sites (module-level assigns):
  plain#0 : drives c[0]   reads [cin]
  plain#1 : drives cout   reads [c[N]]
family `g_bit`: for i in [0, N):
  g_bit#0[i] : drives s[i]   reads [a[i], b[i], c[i]]
  g_bit#1[i] : drives c[i + 1]   reads [a[i], b[i], c[i], a[i], b[i]]
rank relation a certificate must satisfy (writer < reader whenever the read window
overlaps the written window; ranks are functions of the site identity):
  rank(plain#0) < rank(plain#1)   [plain#1 reads c[N]; plain#0 drives c[0]]
  rank(g_bit#1[i']) < rank(plain#1)   [plain#1 reads c[N]; g_bit#1[i'] drives c[i' + 1]]
  rank(plain#0) < rank(g_bit#0[i])   [g_bit#0[i] reads c[i]; plain#0 drives c[0]]
  ...
```

Your rank is a function of the site identity: here carry-in gets 0, bit `i`'s two cells get
`i + 1`, and the carry-out `N + 1`. A good rank is the site's **depth in the dependency graph**:
a write must come strictly before every read of it, so give each site one more than the deepest
site that writes anything it reads. `rippleRank pr fr` takes two functions, `pr` for the module-level
assigns (argument: their position, `plain#k`) and `fr label pos i` for the generate families
(arguments: the block's label as a string, the assign's position in the block, and the genvar as an
`Int`); both may branch on those arguments, which is the way to rank a design with several
generate blocks:

```lean
sv_structure (rank := rippleRank (fun p => if p = 0 then 0 else if p = 1 then 2 else N + 2)
  (fun l p i => if l = "g_cla" then i.toNat + 2 else if p = 2 then i.toNat + 2 else 1))
```

(The adder's reference ignores the label and the position because its two assigns in the
generate block can share a rank.) `rippleRank` covers the module-level assigns and the ONE-index
families only: it gives every site of a two-level family (`.fam l p [j, t]`) rank 0. For nested
loops, write the rank as your own definition by cases on the site, which `sv_structure` unfolds
because it is a named definition; the shape (from an accepted carry-select adder, 2026-11-05;
`tasks/add/README.md`, "Proving a new design", has it whole):

```lean
def myRank (N : Nat) : SiteId → Nat
  | .plain p => …              -- module-level assign number p
  | .fam l p [i] => …          -- assign p of the one-level loop labelled l, at index i
  | .fam l p [j, t] => …       -- assign p of a two-level loop, at indices j, t
  | .fam _ _ _ => 0
-- sv_structure (rank := myRank N)
```

A lexicographic key per site (`sv_structure (lexRank := key N)`, a `SiteId → Key`) is the other
way: `tasks/mul/reference/mul_n.lean`'s `mulKey`. In the `sv_structure?` listing, the relation
`rank(A) < rank(B)  [B reads x[..]; A drives x[..]]` is a *conditional* one: it only has to hold
for the instances whose windows overlap. A line such as `rank(plain#1) < rank(plain#1)` is the
case of one assign that reads a vector it also drives (different bits): it constrains nothing
when the bits differ (and would be a genuine combinational loop if they overlapped). The listing
is long for a design with many reads (40 lines for a stride-4 lookahead): read the left-hand sides
for which sites exist, and choose ranks by depth.
 `sv_structure` samples your rank at small `N` and, if it is
wrong, says which read has a writer of equal or larger rank (a genuine violation, with the
sites named) instead of leaving an unprovable goal.

What `sv_structure` leaves for you (`trace_state` after it) are small arithmetic goals over
integers, one tag each: `inRange_k` (a write or read stays inside its declared vector),
`driverDisjoint_k` (two assigns never write the same bit) and, for `Acyclic`, `rankDecreases_k`.
For the adder, five goals for `CombDesign` and seven for `Acyclic` (the `CombDesign ∧ Acyclic` form
returns the seven: those of `CombDesign` are among them), for example

```
case driverDisjoint_2
⊢ ∀ (i : Int), 0 ≤ i → i < ↑N → ∀ (i_1 : Int), 0 ≤ i_1 → i_1 < ↑N → ¬i = i_1 →
    i_1.toNat + 1 ≤ i.toNat ∨ i.toNat + 1 ≤ i_1.toNat
```

and `intros; omega` closes all of them (`hN : 1 ≤ N` is in the context; keep it in the
theorem statement). For a separate `Acyclic` theorem, if you already have `hc : CombDesign (design.sem N)`,
`sv_structure (rank := ...) using hc` does not ask the `driverDisjoint` goals again (the comb
profile already is the one-driver rule); the `inRange` goals stay.

**A flat netlist leaves nothing (since 2026-10-31).** When every site is plain (no `generate` loop) and the design
has no free parameter (`aes_sbox`; a CRC, a MixColumns network or a SECDED encoder written gate by gate),
the four obligations (`inRange`, `auto`, `driverDisjoint`, `rankDecreases`) are closed statements about the
list of sites, and `sv_structure` DECIDES them itself (`closeByDecide`, through the lemmas of
`LeanModels/Sv/CombViewPlain.lean`) instead of normalizing them with `simp`: the call returns no goal, not
even the `rank[4] < rank[5]` goals the normalization would leave for a rank given as a table, and there is no
`all_goals (intros; omega)` below it. The cost is linear in the number of sites (113 sites: 12 s, 122 M
heartbeats, section 12) where the normalization is quadratic. Any other design takes the route above,
unchanged: a generate loop, a free parameter (the goal then mentions `N`), an `always_comb`, or a closed
statement that is false (the sampling stage names the offending sites first).

### 2.2 The ports

The statement also pins the port names, order and widths (conjunct 1). One tactic proves it from
the comb profile:

```lean
theorem add_interface (N : Nat) (hN : 1 ≤ N) (hc : CombDesign (design.sem N)) :
    SvGolf.Tasks.Add.task.Interface N (design.sem N) := by
  sv_interface
```

`sv_interface` reads the declarations of `design.sem N` off the recognizer (the theorem `decls_view`:
the instantiation succeeded because `hc` says so, and its declarations are the summary's), unfolds
the task's `inputs`/`outputs` and leaves the width arithmetic to `simp` and `omega`. It needs `hc :
CombDesign (design.sem N)` in the context, and nothing else: no `Summary.sound`, `σL`, `Aff.eval`,
`hauto`/`hin` obligations. A design with localparams (section 4) needs no change. A wrong port (a
name, an order, a width) is reported by the tactic ("the declared ports do not match the task's
interface"). (Until 2026-10-30 this step was a 23-line recipe applying `Summary.sound` by hand; it is
still valid, nothing it uses was removed.)

### 2.3 Equations and knownness

The task's statement is reduced to the settled-state lemma and its context is set up:

```lean
theorem solution : Goal := by
  intro N hN
  have hN' : 1 ≤ N := hN.1
  obtain ⟨hc, ha, hso⟩ := add_struct N hN'   -- the triple of section 2.1
  refine CombTask.satisfiedAt_of_comb (add_interface N hN' hc) hc ha ?_
  intro st heqs hs v hv           -- st: a state that solves the design's equations
  obtain ⟨x, y, ci, ⟨⟩⟩ := v      -- the known input values
  obtain ⟨c0, rfl⟩ : ∃ c0, ci = BitVec.ofBool c0 := ⟨_, bv1_eq_ofBool ci⟩
  simp only [SvGolf.Tasks.Add.task, HoldAll_cons, HoldAll_nil, and_true, BitVec.toNat_ofBool]
    at hv ⊢
  obtain ⟨hA, hB, hCi⟩ := hv      -- hA : st.lookup "a" = some (LVec.ofBitVec x) ...
  sv_equations
```

`sv_equations` needs `CombEqs`, `StateShape` (the `heqs` and `hs` above), `CombDesign` and
`Acyclic` in the context. `sv_equations?` prints what it will produce (try it at that point):

```
eq_c_plain_0 : st.boolAt "c" 0 = st.boolAt "cin" 0
eq_cout_plain_1 : st.boolAt "cout" 0 = st.boolAt "c" N
eq_s_g_bit_0 : ∀ i, i < N → st.boolAt "s" i = (st.boolAt "a" i ^^ st.boolAt "b" i ^^ st.boolAt "c" i)
eq_c_g_bit_1 : ∀ i, i < N → st.boolAt "c" (i + 1) =
  (st.boolAt "a" i && st.boolAt "b" i || st.boolAt "c" i && (st.boolAt "a" i ^^ st.boolAt "b" i))
known_s_g_bit_0 : ∀ i, i < N → (∃ v, st.lookup "s" = some v ∧ v.width = ...) ∧ KnownBit st "s" i
... (one `eq_*` and one `known_*` per site)
stable aliases (copies of the above; same statements):
  eq_c_1 := eq_c_plain_0    known_c_1 := known_c_plain_0
  eq_cout_1 := eq_cout_plain_1    known_cout_1 := known_cout_plain_1
  eq_s_1 := eq_s_g_bit_0    known_s_1 := known_s_g_bit_0
  eq_c_2 := eq_c_g_bit_1    known_c_2 := known_c_g_bit_1
auto, inRange: from `hso` (the shared obligations of the structure stage, `SharedObl`)
[bitRead_1] [bitRead_2] [cover_1] [cover_2] [cover_3]
[inputsKnown_1] [inputsKnown_2] [inputsKnown_3]
```

These are the SystemVerilog assigns, transcribed one to one over `Bool`, with the gate structure
kept (`a ^^ b ^^ c` left-associated, like `a ^ b ^ c`). They are derived from the real
semantics by a theorem proved once; no equation is typed by hand. Each is available under two names.
The GENERATED name is `eq_<signal>_<block>_<position>` (the position is the assign's index in its
block), which a renamed block or an assign added above renumbers. The STABLE ALIAS is
`eq_<signal>_<k>`, `known_<signal>_<k>`: the target signal and the ordinal (from 1, in source order) of
the assign among the assigns that write that signal. In the adder `eq_c_1` is `c[0] = cin`, `eq_c_2`
the carry cell, `eq_s_1` the sum cell, `eq_cout_1` the carry-out. Use the aliases in a proof; the
generated names remain (they are what an older proof, or an error message, uses) and the aliases are
copies, so a proof can move between the two without change. An edit that does not add, remove or reorder
the assigns of a signal keeps that signal's aliases.

*Why the equations may be written over `Bool`:* in a state that solves the design's equations, with
known inputs and a rank, every supported read is known (a bit read is `0` or `1`, never `x`/`z`); this is
the library theorem `CombKnown.reads_known` (`LeanModels/Sv/CombKnownThm.lean`), which `sv_equations`
stands on through `CombKnown.settled`. A four-state `&`, `|`, `^` of known bits is the Boolean gate.

Besides the main goal (the first one, with the `eq_*` and `known_*` in its context) the tactic
returns its obligations as further goals, each tagged:

| tag | meaning | closer |
|---|---|---|
| `inRange_k` | a write or read window lies inside its declared vector | `intros; omega` |
| `width_k` | operands are as wide as the target (no implicit resize) | `intros; omega` |
| `bitRead_k` | a bit select lies inside its vector | `intros; omega` |
| `cover_k` | every bit an assign reads has a source: an input bit or a bit some assign writes | `sv_cover` (a site as the witness; the cells of a 2-D array: the 2-D rule; both below) |
| `inputsKnown_k` | the input ports hold fully known vectors of their declared width | `inKnown_ofBitVec hA (by omega)` |

(With the shared obligations of section 2.1 in the context there are no `auto_k`/`inRange_k` goals. A `cover_k` goal that
is a conjunction with a quantified part, `… ∧ ∀ k, k < w → …`, the coverage of a site that writes a vector, is split by
`sv_cover` itself, each part a call of its own; until 2026-11-04 the search spent its budget on such a conjunction as a
whole and failed, and a cascade had to split it.)

**A flat netlist has no `width_k` and no `cover_k` (since 2026-10-31).** For a design whose sites are all plain and that
has no free parameter (`aes_sbox`), `sv_equations` DECIDES `auto`, `inRange`, `width`, `bitRead` and `cover`
(closed statements about the site list: `LeanModels/Sv/CombViewPlain.lean`, `CombEqPlain.lean`) and returns
the main goal and the `inputsKnown_k` goals only. A proof must not name the others (`case cover_5 => …` is
the error `Case tag cover_5 not found`), and `sv_equations?` says what it decided:
`decided (flat netlist: every site plain, no parameter): auto, inRange, width, bitRead, cover`. A premise
that is false (a read of a net nobody drives) is not decided: the tactic falls back to the normalization and
the unprovable `cover_k` goal is there, as for any design. The tactics run with `maxRecDepth` raised to
100000, so no `set_option maxRecDepth` is needed in your file for a netlist of a hundred sites. If the last
assign of the file drives a bit of a vector output (the knownness fact of that site is a pair), the stable
names are still produced for every site.

**Literal, part-select and concatenation assigns.** The examples above only have bit selects.
An assign of a literal or a concatenation is handed over in a raw form, for example
`assign pp[2:0] = 3'b111;` gives

```
eq_pp_plain_0 : ∀ k, k < Int.toNat 3 → st.boolAt "pp" k = { bits := #[Logic.l1, Logic.l1, Logic.l1] }.boolAt k
```

and `assign cc[3:0] = {cin, cin, cin, cin};` a nest `if k < 3 then if k < 2 then ... else
st.boolAt "cin" (k - 1)` selecting the concatenation's operand by the index. They are not
hard, only unfamiliar: specialise `k` to each value of its (small) range and the right-hand side
computes, so `obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by omega` and then `all_goals rfl`
(or `simp`) turns them into the plain bits you need.

`inputsKnown_k` is your premise: the tactic cannot know how the inputs were obtained, and
`hA : st.lookup "a" = some (LVec.ofBitVec x)` says they are known; `inKnown_ofBitVec` turns that
into the goal. The reference closes everything in one line:

```lean
  all_goals first
    | (intros; omega)
    | sv_cover
    | (refine inKnown_ofBitVec hA ?_; omega)
    | (refine inKnown_ofBitVec hB ?_; omega)
    | (refine inKnown_ofBitVec hCi ?_; omega)
    | fail "unclosed obligation"
```

End the `first` with a `fail`: when no alternative closes a goal, Lean reports the error of the
**last** alternative, which would otherwise be a type mismatch of `inKnown_ofBitVec` against a
goal it was never meant for. `fail "..."` prints the message together with the goal (its tag,
for example `cover_5`, and its statement), so you see which obligation is left. (A design with 2-D reads is the exception: end the `first` with
`sv_cover` itself, as the multiplier references do, so that `sv_cover`'s own message about a cell it cannot
cover is the one reported.) A `cover_k`
goal has one conjunct for every *read occurrence* in the assign (a lookahead that reads `g[i]` four
times lists it four times), each a disjunction "this bit is an input, or written by assign 1, or by
some instance of assign 2"; when `sv_cover` cannot find the witness, a small helper lemma stating
"the bit `j` of this family is written by instance `j - o`" and `repeat' apply And.intro` followed
by `all_goals first | exact helper _ _ (by omega) (by omega) | ...` closes them all (about 6 lines
per family).

When the design is flat but the fast path does not apply (a free parameter that the sites do not use, say),
the witness of a read of a net is a SITE:
`∃ b, (b = site₀ ∨ … ∨ b = siteₘ₋₁) ∧ …`, a disjunction as long as the netlist. (A design WITH a generate loop never
keeps this form: when the normalization of the whole coverage obligation runs out of `simp` steps and leaves it,
`sv_equations` renormalizes each coverage goal on its own (since 2026-11-01), and the goal comes out as the explicit disjunction of
the 2-D rule; the one-level Karatsuba multiplier of `design/tasks-week2/clmul/karatsuba/`, 19 sites and 26 operand reads,
is the case that needed it.) `sv_cover` picks the writer
by NAME (the sites whose target is the signal the goal states), proves the membership directly and closes the
rest, so you write no `Or.inr (Or.inr … (Or.inl rfl))`; the search it replaces gave up at about 25 sites
(`Examples/system-verilog/flat_net/sv_cover_site.lean`: 26 plain sites and a parameter; the normalization
route still costs `maxHeartbeats 2000000` there).

**Coverage of a 2-D read (since 2026-10-31).** The `cover_k` goals of a design with 2-D arrays say that the cell a read
observes lies in the window of some writer. The conjunct for the read `s[i][0]` of the array multiplier is

```
(rmN (↑N + 1) 0 0 ≤ rmN (↑N + 1) i 0 ∧ rmN (↑N + 1) i 0 < rmN (↑N + 1) 0 0 + (N + 1))          -- the packed row s[0] = {1'b0, pp[0]}
  ∨ (∃ a, 1 ≤ ↑a ∧ a < N ∧ ∃ b, b < N ∧ rmN (↑N + 1) ↑a ↑b ≤ rmN (↑N + 1) i 0 ∧ rmN (↑N + 1) i 0 < rmN (↑N + 1) ↑a ↑b + 1)
  ∨ (∃ a, 1 ≤ ↑a ∧ a < N ∧ rmN (↑N + 1) ↑a ↑N ≤ rmN (↑N + 1) i 0 ∧ rmN (↑N + 1) i 0 < rmN (↑N + 1) ↑a ↑N + 1)
```

(a plain assign's window, the cells of the row loop, the cell `s[a][N]`). Until 2026-10-31 each such goal was closed by
hand, by choosing the disjunct, naming the loop indices and handing the window arithmetic to a macro: 29 to 75
lines in each multiplier reference (sections 3, 8, 9, 10 keep the numbers). `sv_cover` now closes them itself
(`LeanModels/Sv/CombCover.lean`, tried before the older search):

* it SOLVES each `∃`-variable from the affine equations of the read's row and column: `a := i.toNat` above;
  for a loop that steps by 2 (the Wallace tape, rows `N + 2g + 1`) `g := ((r - N - 1) / 2).toNat`, the parity
  staying in the condition it states;
* it states the writer's condition at those witnesses as a linear proposition (the bounds, `row = R`,
  `c₀ ≤ C + e < c₀ + wd`: the premises of the one lemma it needs about `rmN`, `CombCover.rmN_win_suff`) and walks the
  writers with `Classical.em`: the condition gives the writer (the proof term is built from its components), its
  negation goes on to the next writer, and `omega` closes the last one from the negations. A writer the
  hypotheses alone refute is skipped (one small `omega`), which keeps the last `omega` free of negated
  conjunctions with `Int.toNat` and division;
* a conjunct that occurs twice in a goal (the carry cell reads `T[3g][c]` twice) is proved once.

A goal whose shape the rule does not read (an `∃` over something that is not a `Nat`, an equation with two
unknowns, a nonlinear index, a writer that is a site) takes the older search, unchanged. A goal it reads and
cannot prove is reported, with the read and the condition each writer would need at the solved witnesses:

```
sv_cover: the cell is not covered
  rmN (↑N + 1) i✝ 0
needs, for one of its writers (witnesses solved from the read's index), one of:
  (1) 1 ≤ ↑i✝.toNat ∧ i✝.toNat < N ∧ Int.toNat 0 < N ∧ ↑i✝.toNat = i✝ ∧ 0 ≤ 0 ∧ ↑(Int.toNat 0) ≤ 0 ∧ 0 < ↑(Int.toNat 0) + 1
and none of them follows from the hypotheses
```

(here the plain window of row 0 is missing from the design: the only writer needs `1 ≤ i`). Read the list for the
atom that is false: a bound that is too small, a row nobody writes, a parity. The error comes from the writers'
conditions, not from a search, so it is the same at every `N`.

### 2.4 The arithmetic

The main goal, after `sv_equations`, is: from the equations, the outputs `s` and `cout` hold
the task's values. The reference states this as a lemma, `add_final`, whose hypotheses are the
`eq_*` and `known_*` exactly as printed, and applies it:

```lean
  · obtain ⟨⟨vs, hvs, hvsw⟩, -⟩ := known_s_1 0 (by omega)
    obtain ⟨⟨vc, hvc, hvcw⟩, hkc⟩ := known_cout_1
    exact add_final hA hB hCi eq_c_1 eq_c_2 eq_s_1 eq_cout_1 hvs
      (by omega) (fun k hk => (known_s_1 k hk).2) hvc hvcw hkc
```

(A 1-D design like this one passes the printed equations to a lemma that states them as hypotheses. With 2-D
`rmN` indices the printed forms and the `Nat`-indexed facts of the arithmetic differ by a layer of casts;
`sv_bridge` closes each fact from the printed equation and nothing is restated: section 3.)

Inside `add_final` the mathematics is three steps:

1. **Bits to a value.** The four equations are exactly the library structure `AddView` (carry in,
   carry step, sum bit, carry out). `add_value` (via `ripple_row`, the ripple-carry induction)
   gives `Σ 2^j s_j + 2^N · cout = a + b + cin`, and `add_spec` turns it into
   `s = BitVec.ofNat N (a + b + cin) ∧ ofBool cout = BitVec.ofNat 1 ((a + b + cin) / 2^N)`.
2. **Ports to bits.** The port `s` is a four-state vector in the state; it is known
   (`known_s_*`) and `N` bits wide, so `SvState.lookup_eq_ofBitVec_bv` says it is the `BitVec`
   built from its Boolean bits, `XF.bv N (st.boolAt "s")`.
3. **Glue.** `SvState.boolAt_ofBitVec` reads the inputs' bits back (`hA` etc.), `XF.getLsbD_bv`
   reads the output's.

## 3. The multiplier

`reference/mul_n.sv` is an `N × N → 2N` array multiplier with 2-D packed signals `pp`, `s`, `c`,
`t` (`logic [N-1:0][N:0] s;`), nested generate loops and a part-select target
`assign p[2*N-1:N] = s[N-1][N:1]`. The proof, `reference/mul_n.lean`, has 70 code lines (by
hand: 1385). It has the same four parts as the adder; the differences are:

* **2-D arrays.** Signals are flat bit vectors; `s[i][j]` is bit `i*(N+1) + j`, written
  `rmN (N+1) i j` in the goals ("row-major"). The one nonlinear fact behind every goal that
  compares two cells, that row-major order is lexicographic order, is the library lemma
  `rmN_lt_iff` / `rmN_le_iff` / `rmN_inj` (`CombViewArith.lean`). `sv_rowmajor` rewrites the goals
  with it, so the closer of the structure goals is `intros; sv_rowmajor; omega`.
* **Positions count the inner loop.** Inside a generate block, the assigns and any inner loop are
  numbered in source order, so in `g_row` an `assign` written after the inner `for` is `g_row#1`
  (the inner loop is position 0), not `#0`: `sv_structure?` prints the numbering, and a rank or
  a key that branches on the position must use it.
* **The rank is a lexicographic key** `(row, column, phase)` of the site identity, passed as
  `sv_structure (lexRank := mulKey N)`. The reference's key: partial products and the zero rows
  first; within a row, column by column, the propagate `t`, then the carry `c`, then the sum `s`;
  the row's top bit after its last column; the outputs last. Site identities have the shape
  `.plain k`, `.fam "g_bit" pos [i, j]` (label, position in the block, indices).
* **Heartbeats.** `mul_struct` (the `CombDesign ∧ Acyclic` theorem) needs `set_option maxHeartbeats 400000
  in` (the default 200000 times out inside `simp`; the `Acyclic` obligation has 51 goals). So does
  `solution`, for a different reason: it uses 183 M of the default 200 M, which is an edge (heartbeat
  counts move by a few percent between runs), so it keeps `set_option maxHeartbeats 400000 in`.
* **Twenty-odd obligations**: `sv_structure` returns 24 goals for `CombDesign` and 51 for
  `Acyclic`; `sv_equations` 22. All close by `intros; omega` or `sv_cover` **except**
  `inputsKnown_1/2` (as in the adder). That includes six **coverage** goals of the nested 2-D reads
  (`cover_2`, `cover_4` to `cover_8`): `sv_cover`'s 2-D rule solves the loop indices of each writer from the
  read and walks the writers (section 2.3). Until 2026-10-31 they exceeded `sv_cover`'s search and were closed by
  hand, each by naming the writer and calling a six-line `cov_leaf` macro, about 75 lines of the reference.
* **The bridge and the arithmetic.** The arithmetic is `ideal_mul_view` of `CombLib`: the eleven equations
  are the fields of `MulNetlistView` (partial products, row 0, the ripple rows, the output bits); the
  library proves the row invariant `low bits so far + 2^i · row i = a · (b mod 2^(i+1))` by `ripple_row` and
  induction. The fields are `Nat`-indexed (`s (i - 1) (j + 1)`), the printed equations are not
  (`st.boolAt "s" (rmN (↑N + 1) (↑i + -1) (↑j + 1))`). Until `sv_bridge` (2026-10-31) a theorem restated every printed equation
  as a hypothesis (`mul_final`, 82 lines: the statement, then one `show` / `rw [show ((i - 1 : Nat) : Int) = …
  by omega]` / `exact` per field). Now `solution` instantiates the arithmetic lemma and closes each field with
  `sv_bridge`:

  ```lean
    refine ideal_mul_view hN' (pp := st.cell "pp" N) (t := st.cell "t" N)
      (s := st.cell "s" ((N : Int) + 1)) (c := st.cell "c" ((N : Int) + 1))
      { pp_def := ?_, s0 := ?_, s0_top := ?_, c0 := ?_, t0 := ?_, ci0 := ?_, t_def := ?_, s_def := ?_,
        c_def := ?_, s_top := ?_, p_low := ?_, p_high := ?_ }
    · sv_bridge eq_pp_g_pp_j_0 with ba, bb
    · sv_bridge eq_s_plain_0 with if_pos
    · sv_bridge (eq_s_plain_0 N (by omega)) with if_neg
    · sv_bridge eq_c_plain_1
    ...
  ```

  `st.cell "s" W i j` is bit `(i, j)` of the 2-D signal `s` with rows of `W` bits, in `Nat` coordinates
  (`st.boolAt "s" (rmN W i j)`). `sv_bridge e` introduces the goal's binders, instantiates the printed
  equation `e` (its index binders take the goal's, its premises are proved by `omega`), and compares goal
  and instance along the Boolean structure, proving every pair of index terms that differs by `omega`.
  The `with` lemmas rewrite the instance first: `ba` / `bb` (an input bit as the bit of the `BitVec`),
  `if_pos` / `if_neg` (the packed `s[0] = {1'b0, pp[0]}`), `XF.getLsbD_bv` (an output bit). An instance
  the goal does not bind (`s 0 N`) is given explicitly. Section 6 lists the tactic and its error.

### 3.1 The carry-less array: `mul` without carries (`clmul`)

`tasks/clmul/reference/clmul_n.{sv,lean}` is `mul_n`'s array with XOR where `mul_n` has a full adder, and no carries:
one 2-D signal `r` (`N` rows of `N` bits, `r[i][j] = r[i-1][j+1] ^ (a[i] & b[j])`), four generate loops, `p[i] = r[i][0]`
and `p[N+m] = r[N-1][m+1]` (`2N-1` output bits). The proof is 206 code lines (284 with comments), of which 143 are the
plain-Lean arithmetic, and the `solution` stage takes 7.4 to 7.7 s of wall clock (three cold `check.py` runs; the time limit
is 300 CPU s). It was written in one pass from the `mul` recipe; what differed:

* **Zero-iteration loops.** The upper output bits are a loop over `N - 1` positions (`for (m = 0; m < N-1; m++)`), because a
  part select `p[2*N-2:N]` is the reversed range `[0:1]` at `N = 1`. A loop with no iteration at `N = 1` is fine for the
  tactics (the obligations are universally quantified over the genvar).
* **Row 0 and the printed forms.** `assign r[0][j] = …` prints as `st.boolAt "r" i` (the row-major offset of row 0 is the
  column), and the high output reads `st.boolAt "r" (rmN ↑N (↑N + -1) (↑i + 1))` with the knownness index `(↑N + ↑i).toNat`;
  `sv_bridge` closes both against the `Nat`-indexed fields of the arithmetic lemma (`View`), no restating.
* **The rank** is the lexicographic key `(row, 0, 0)` of the site identity (`clmulKey`): a row reads only the row above, the
  outputs come last. It is exhaustive, with no wildcard rank: a partial classifier (`clmulFamily?`, on the static key
  `idKey`: block label, position in the block, number of loop indices) names the five families and answers `none` for
  anything else, and `clmul_sites_classified` proves, by `decide` over the design's summary, that no site is `none`. So a
  change to the generated layout fails that theorem, and a pinned `#eval` beside it names the unclassified sites. The closer `intros; sv_rowmajor; omega` of the multiplier leaves ONE goal here, `driverDisjoint_5`
  (two output bits `p[i]`, `p[i']`; the window comparison arrives as `(0 < 0 ∨ True ∧ i' + ↑1 ≤ i) ∨ …`, which `omega`
  does not see through): the fallback `first | omega | (simp [clmulFamily?, idKey, ClmulFamily.key, siteIdx] <;> omega)`
  closes it (the `simp` also unfolds the classifier).
* **The mathematics** is a row invariant by induction on the row, `r i j = XOR over t ≤ i of A t & B (i + j - t)` (a term whose
  `B` index reaches `N` is 0), then the collapse of the Spec's double sum over `i + j = k` into the single sum the invariant
  gives (`bx_pair`), for `k < N` (the low outputs) and `k ≥ N` (the last row). `bx f n` is the XOR of `f 0 … f (n-1)`; the
  Spec's nested `List.foldl` becomes `bx` by `foldl_xor` (both in `LeanModels.Sv.XorSum`, section 6; the reference carries
  its own copy); `getLsbD_ofBits` reads the Spec's `ofBits` vector bit by bit.
* **A generate-for start must be an integer literal** (`for (i = 0; …)`): `for (i = N; i < 2*N-1; i++)`, the natural way to zero-fill
  a padded vector, is refused with `generate-for header outside for (g = <int>; g < <affine>; g++)`; write the loop from `0`
  and index `ap[N+i]`.

## 4. What the tactics accept, and what they refuse

**Accepted** (the "v1 fragment", `LeanModels/Sv/CombView.lean`):

* a flat top module whose processes are continuous assigns: `assign x = e`, `x[idx] = e`,
  `x[i][j] = e`, a whole row of a 2-D array `x[i] = e`, a part `x[hi:lo] = e` (a netlist of any number of
  such assigns with no loop and no parameter is a FLAT netlist: its obligations are decided, sections 2.1,
  2.3 and 12);
* `generate for (g = c0; g < bound; g++)` loops, any number of them, with such assigns in the
  body and, one level down, further `generate for` loops of such assigns (two levels deep,
  mixed bodies); the step is `g++`, and `g = g + 1` works as well: the extractor writes it as `g++`
  (measured 2026-11-05: `add_n.sv` with `i = i + 1` passes `--unproved` with `tactics.in_fragment: true`,
  and the envelope's step is `++`). The `design` stage accepts the other step forms README's "Rules" list;
  they are not measured with the tactics;
* the number of iterations of a generate loop is at most `4 · Σ|parameters| + 60` (the generate
  fuel of ls-sv is `(Σ|parameters| + 2)² + 64`; this linear bound was `Σ|parameters| + 60` until
  2026-10-30, and a loop over `2*N` columns needs the larger one): `sv_structure` returns the
  obligation as an `auto_k` goal `2 * ↑N ≤ 4 * ↑N + 60` (a closed form `omega` proves);
* **localparams**: `localparam integer L = <e>;` (or `localparam int`, see below) where `<e>` is an
  integer constant expression built from integer literals, the parameters, EARLIER localparams, `+`,
  `-`, `*` with an integer-literal factor, `/` or `%` by a positive integer literal
  (`H = (N + 1) / 2`, `R = N % 2`, `T = 2 * H - R`, `M = N - 1`), and `$clog2` (`L = $clog2(N) + 1`). A localparam is one more named
  constant of the design: it may stand wherever a parameter may (an affine index or bound, a
  declaration range, another localparam's definition), and `sv_structure?` prints its definition in a
  `localparams:` block. The obligations come out with the definition INLINED, `/` and `%` as the floor
  forms `omega` reads (`(↑N + 1) / 2`): the elaborated design truncates toward zero, and the tactics
  rewrite one into the other where the numerator is provably non-negative from your hypotheses
  (`hN : 1 ≤ N`; an `(N - 5) / 2` stays as `Int.tdiv` in the goal, where `omega` cannot see through
  it). A `$clog2` is not linear: in the obligations its value is an opaque atom, `↑(clog2 n)` for the natural
  number `n` of its argument, a non-negative unknown to `omega`. The facts about it a proof needs are yours to
  supply: `CombView.clog2_le` (`clog2 n ≤ n`, the generate-fuel bound `auto_k` of a loop it bounds) and
  `CombView.le_two_pow_clog2` (`n ≤ 2 ^ clog2 n`); `Examples/system-verilog/comb_word/sq_chain.sv` is a loop bounded
  by one (section 17). Use `integer`, the 4-state type, for a localparam with a `/` or `%`: the extractor
  squashes them under a 2-state `int` target, and the elaborated design then wraps the value at 2^31, so its
  closed form would be false for the huge `N` a for-all-`N` theorem ranges over (refused, see below). A
  `$clog2` may be either (`localparam int L = $clog2(N + 1);` is read since 2026-11-05, the same opaque atom).
  The tactics do not trust their own reading of the definition: each design's `hag` goal (closed by
  `rfl`) checks that the localparam really sits in the instantiation environment at the value the
  tactics computed, so a mismatch stops the tactic instead of proving something false. Proofs of
  designs with localparams may need `set_option maxHeartbeats 1000000` (the quotient and remainder cost
  the tactics' own `simp` and `omega`); the interface step (`sv_interface`, section 2.2) needs no change
* declarations: scalars, 1-D and 2-D packed arrays `logic [hi:lo]` and `logic [h1:l1][h2:l2]`
  with bounds affine in the parameters (`N-1`, `2*N-1`, `N`); unsigned four-state declarations
  only (`logic`, as in the references; not `bit`, not signed);
* every index and bound AFFINE in the parameters and enclosing genvars: a sum of constants times
  parameters and genvars (`i`, `i+1`, `i-1`, `N`, `2*N-1`); non-affine index arithmetic
  (`i*j`, `i >> l`) is outside the fragment;
* right-hand sides: an expression over accesses and known literals built from `&`, `|`, `^`, `~`,
  `!`, the six reductions, `&&`, `||`, `==`, `!=` and the conditional `c ? a : b` (section 14), a
  concatenation of accesses and known literals, or a fill `'0` / `'1`; every operand exactly as wide as
  the target (`sv_equations` returns a `width` goal, which is false if one is not).

**Refused**, with the message you will see (`sv_structure: outside the supported fragment — ...`
for most of them; the checker still accepts the design, and a by-hand proof or a different
design may exist). Measured on small variants of the adder and on the prefix-adder baselines:

| you wrote | message |
|---|---|
| `localparam int H = (N+1)/2;` (a 2-state `int` with `/` or `%`; write `integer`) | ``localparam `H`: a 2-state `int` localparam initialised by `/` or `%` is squashed to 2 states and wraps at 2^31 in the elaborated design (its closed arithmetic form would be false for huge parameters); declare it `localparam integer H = …;``` |
| `localparam integer Q = N * N;` | ``localparam `Q`: a product of two non-constant factors is outside the v1 fragment (`*` needs an integer-literal factor, ...)`` |
| `localparam integer H = N / N;` | ``localparam `H`: `/` by a non-literal is outside the v1 fragment (a localparam may divide by an integer literal)`` |
| `localparam integer S = N << 1;` (any other operator) | ``localparam `S`: operator `<<` is outside the v1 fragment (a localparam may use + - *, / % by an integer literal, and `$clog2`)`` |
| `localparam logic [7:0] K = 8'd3;` (any type but `int`/`integer`) | ``localparam `K`: only `int`/`integer` (32-bit signed) localparams are in the v1 fragment`` |
| `-x` (unary minus) | ``site `plain#0`: unary operator `-` or `+` (outside the v1 fragment: it has `~` and `!`)`` (`~x`, `!x`, `p ? c : a`, reductions, `&&`, `\|\|`, `==`, `!=` are IN the fragment since 2026-10-31: section 14) |
| `x <<< y`, `x >>> y`, a signed `x >> y` (word-level operators that are not in the fragment yet; `+`, `-`, `*`, a width conversion of an operation, the six comparisons and the run-time shifts `<<`, `>>` are IN the fragment since 2026-11-01: sections 14 and 17) | ``site `plain#0`: operator `...` is outside the v1 fragment (it has the bitwise gates `&`, `\|`, `^`, the word-level `+`, `-` and `*`, the six comparisons, the run-time shifts `<<` and `>>` and the logical `&&`, `\|\|`; `<<<`, `>>>`, a signed `>>`, `/`, `%` and `**` are word-level operators it does not have yet)`` |
| `(a + b) * (a - b)` (a product neither of whose factors is a signal access) | ``site `plain#0`: a product neither of whose factors is a signal access (outside the v1 fragment: the elaboration folds a product of constants, so `*` is read with at least one factor a signal access, bare or zero-extended; write one factor into a signal first)`` |
| `(a + b) << 1`, `a << (s + 1)`, `a << (N - 1)` (a shift whose left operand is an operation, or whose amount is an expression or a parameter) | ``site `plain#0`: operand of a shift that is not a signal access, a sized literal or an unsized constant (outside the v1 fragment: ...; write the operand into a signal first)`` |
| a width conversion around a NESTED conversion or a constant that is not an unsized integer (around a signal access, a sized literal, a concatenation or an operation of the fragment the conversion is read since 2026-11-01: zero extension, truncation) | ``site `plain#0`: width conversion of a nested conversion or a constant that is not an unsized integer (outside the v1 fragment: ...)`` |
| `c ? a : '0` (a fill inside an operator; a concatenation of literals and accesses is accepted there since 2026-11-01) | `site …: unbased unsized literal '0/'1 inside an expression (outside the v1 fragment; allowed as a whole right-hand side)` (write a sized literal) |
| `v ? a : b` with a multi-bit `v` | accepted; the `width` obligation is then FALSE (the condition must be one bit): write `\|v ? a : b` |
| `always_comb` with a `case` (plain, constant items, a `default`, single-assignment arms) | accepted (section 15) |
| `case` without `default` (a latch) | ``site `plain#0`: always_comb `case` has no `default`: it does not assign its target on every path (a latch)`` |
| `case` item that is not a sized literal as wide as the subject (`1:`, `3'd1:` on a 2-bit subject) | ``site `plain#0`: width conversion (an operand is not as wide as its context ...)`` (the subject is zero-extended to the item) or ``…: `case` item is not a sized literal (write `8'd5` ...)`` |
| `case` arm in `begin … end`, or an `if`/`case` inside an arm | ``site `plain#0`: `case` arm is not a single assignment `t = v;` (the first fragment has no `begin … end`, `if` or `case` inside an arm)`` |
| `case … inside`, `unique`/`priority case` | ``site `plain#0`: always_comb statement `case … inside` (outside the first fragment)`` |
| a `case` item with an `x`/`z` bit (`2'b1x:`) | `sv_structure` accepts it; `sv_equations`: ``a right-hand side is outside the fragment of `sv_equations` (an expression over accesses and known literals ...)`` |
| `always_comb` with an `if` and no `else` (a latch) | ``site `g_bit#1`: always_comb does not assign its target on every path (an `if` without `else` is a latch)`` |
| `always_comb` that writes a window in two SEPARATE groups of statements (`y = a; z = b; if (e) y = b;`) | ``site `plain#0`: an always_comb body writes a window in two separate groups of statements (outside the second fragment: put the statements of one window together)`` (a body that writes SEVERAL windows, each in its own group, is accepted by `sv_structure` since 2026-11-01: one site with further windows, `Examples/system-verilog/comb_multi`; `sv_equations` still refuses it) |
| `always_comb` with a second UNCONDITIONAL assignment of the target (`y = a; y = b;`) | ``site `g_bit#1`: a second unconditional assignment of the target in an always_comb block (outside the second fragment: only `if (c) …;` overrides can follow the first statement)`` |
| `always_comb` with an `if … else` after the first statement, a nested `begin … end` with several statements as a statement of a block, or an override writing another window | ``…: an `if … else` after the first statement of an always_comb block (outside the second fragment: only `if (c) …;` without `else` can follow, as a default-then-override body)`` / ``…: a `begin … end` with several statements as a statement of a block (outside the second fragment: write its statements in the outer block)`` / the `writes more than one window` message |
| an override that READS the window it writes (`y = a; if (e) y = y ^ b;`) | the `noSelfRead` / `reads the window it writes` message of section 13 (SSA substitution of the earlier value is NOT modelled) |
| `always_ff`, `always @(...)`, any other process | `site g_bit#0: procedural process (always): outside the combinational-assign fragment` |
| `if (...) begin ... end` inside a generate loop | `conditional generate inside a generate loop (outside the v1 fragment)` |
| a dynamic write `s[b] = ...` | `site g_bit#0: write to s[…] has a non-affine (dynamic) index: the driven window cannot be determined` |
| a generate bound that is not affine (`for (j = 0; j < N/2; j++)`) | `generate bound is not affine` |
| a 3-D packed array | `only scalar, 1-D and 2-D packed declarations are in the v1 fragment` |
| a part select of a vector whose range is not zero-based (`logic [8:1] v; … v[4:2]`) | ``site `plain#0`: `v`: part selects need a zero-based descending dimension `[hi:0]` `` (accepted for `[hi:0]` since 2026-11-01) |
| a whole row of a 2-D array whose first range is not zero-based (`logic [4:1][2:0] r; r[1] = x`) | `structural check failed: site `plain#0`: the access `r[0]` does not match the declaration of `r` (a select needs zero-based descending packed dimensions `[hi:0]`, …)` |
| three nested generate loops | `an inner generate loop holds a nested generate ...` |
| `bit` or `signed` declarations | `declaration a is signed or 2-state (outside the v1 fragment ...)` |
| a submodule instance (a hand-built full adder) | ``sv_structure: this design instantiates modules, and the `sv_comb` tactics cannot summarize module instances yet. …`` (the same text from `sv_interface` and `sv_equations` since 2026-11-01, pinned in `Examples/system-verilog/ripple_fa/comb_errors.lean`). The loader, the scorer and the post-synthesis check accept the design; flatten it in the source, or prove the structure by hand as `ripple_fa/gen.lean` does. Before then the message was `cannot read a load_design_sv2 family (X.sem N) off the design in the goal`, which did not mention instances |
| a right-hand side the recognizer reads but `sv_equations` cannot (an `x` literal, a width mismatch) | `sv_equations: ...` from the decidable check: a long `decide` failure that does not name the site |

**Patterns that stay in the fragment** (the layouts of the from-scratch designs accepted on
2026-11-05; each task README's "Proving a new design" has them for its task):

* blocks as the rows of 2-D arrays, `c[j][t]`, not a flat `c[K*j + t]`: `sv_cover` finds the assign
  that writes a read by solving ONE unknown per index equation (its fallback tries the context's
  variables, `± 1`, `0` and `1`), so a flat read whose writer needs `j = i / K` and `t = i % K` is not
  covered, while every read of the 2-D layout is;
* block counts as `localparam integer Q = N / K;` and `localparam integer R = N % K;`, with a tail
  loop over the `R` leftover bits;
* every declared bit driven at the scoring point: an unused row gets a literal (`assign c0[Q] =
  7'b0;`), whose `width` goal closes by `rfl`;
* a zero-padded copy of an input where a row starts at a moving column (`mul`'s tree references:
  `ae[c + 2*N - 1 - j] & b[j]`);
* with nested loops, your own rank by cases on the site (section 2.1).

Some refusals are not source-located (the last row). Note that several of these are checker-legal
designs: the checker only needs *a* proof. `docs/sv-refusals.md` of Proglib (the language
tier) and [REFUSALS.md](REFUSALS.md) (the checker) are the generated lists of what is refused
elsewhere.

The tactics also check your obligations by sampling: a rank that does not decrease, a write out of
range, two assigns driving the same bit are reported with the sites and the sampled `N`, as
`... (sampled at [N] = [1]; a genuine violation, not a missing proof, ...)`. (`N = lb .. lb + 4` are tried.) A
rank that does not decrease also names the read that forms the edge, on a second line:

```
sv_structure: the rank does not decrease along a read: `g_bit#0[1, 0]` (rank (1, 0, 1)) reads a window of `s` driven by `g_bit#1[2, 1]` (rank (2, 1, 3), window s[9]); a driver must have a SMALLER rank than its reader (sampled at [N] = [3]; a genuine violation, not a missing proof, unless your hypotheses exclude this point)
  the read that forms the edge: `s[2][1]` of `g_bit#0[1, 0]`, written by `g_bit#1[2, 1]` (window s[9])
```

the access as it reads in the source, with the loop indices of the sampled instance filled in.

## 5. When to fall back to a by-hand proof

If the design is outside the fragment (a prefix adder with a `$clog2` `localparam` and a conditional
generate, a design with an `always_comb` outside the first fragment of section 13, or instances), the tactics are no help for the structure,
but the **reduction and the arithmetic still are**:

* `CombTask.satisfiedAt_of_comb` needs `CombDesign`, `Acyclic` and one settled-state lemma; give
  them in whatever way works. The by-hand references are complete examples of that route:
  `tasks/add/reference/add_n_byhand.lean` (509 code lines: walk the generate loop symbolically,
  one-driver rule, rank certificate, the settled state by induction on the bit index) and
  `tasks/mul/reference/mul_n_byhand.lean` (1385 code lines, 2-D). The proved prefix adders
  `tests/add/baselines/add_n_sklansky.lean` and `add_n_kogge_stone.lean` take the same route through a
  conditional generate inside an inner generate loop, and `tests/clmul/baselines/kara_lv.lean` through a
  level-by-level Karatsuba with `**` in a localparam.
* the plain-Lean part is reusable as it is: `CombLib` (below) has the bit-function value
  `bfVal`, the ripple-row lemma, the full-adder identity, the bridges to `BitVec`.
* a by-hand proof compiles about 2.3 times faster (CPU) than the tactic proof (README.md,
  "Proof effort"), and does not depend on the tactic library, but is four to six times longer for
  these two designs.

## 6. What the libraries already give you

Look here before you write a helper lemma: proofs on the board re-prove, or copy from a reference, lemmas that these
modules already have. The second column is the module to import: `LeanModels.Sv.` followed by the name shown, or
svGolf's own `SvGolf.…` (all are allowed). Write the name as it stands here, after the usual
`open LeanModels.Sv SvGolf`; core Lean's names need no import. The modules hold more than these rows: their docstrings
say what. A lemma that is in no library yet is named in its task's README, with the reference proof to copy it from.

**Bit vectors and slices**

| name | module | what it says | use it when |
|---|---|---|---|
| `LVec.extract_extract` | Comb2Base | a window of a window is a window of the vector | a part select of a part select |
| `LVec.extract_insertAt_self`, `LVec.extract_insertAt_of_disjoint` | Comb2Base | a write read back at its own window; every disjoint window is unchanged | reading a register after a select-write |
| `LVec.insertAt_zero_of_width_eq`, `LVec.resizeU_of_width` | Comb2Base, Comb2Proc | a full-width write at offset 0 is the written vector; a resize to the vector's own width changes nothing | a whole-register write, and the `resize` the loader puts around it |
| `LVec.extract_ofBitVec`, `LVec.extract_one_ofBitVec`, `LVec.eq_ofBitVec_of_extract_one` | Known2 | a window or a bit of a known vector, as a `BitVec`; a vector known bit by bit is `ofBitVec x` | going from `LVec` to `BitVec` (`Known2` has an `*_ofBitVec` lemma for each operator) |
| `SvState.boolAt`, `KnownBit`, `XF.bv`, `XF.getLsbD_bv` | CombKnownBits | a signal's bit as a `Bool`; that bit is known; the `BitVec` of a bit function, and its bits | the vocabulary of the printed equations |
| `SvState.lookup_eq_ofBitVec_bv`, `SvState.boolAt_ofBitVec` | CombKnownBits | a signal whose bits are all known is the `BitVec` of its bits; a bit of an input port is the bit of its `BitVec` | reading an output port back; reading an input bit |
| `CombEq.inKnown_ofBitVec` | CombEqThm | an input port holding `ofBitVec x` is known at its width | the `inputsKnown_k` goals of `sv_equations` |
| `Lib.setWidth_signExtend_of_le`, `Lib.setWidth_add_mul_signExtend` | Lib.BitVecArith | a sign extension truncated back; a multiply-accumulate at a wider width, truncated, is `x + ofInt (a.toInt * b.toInt)` | signed operands and accumulators |
| `LVec.ofBitVec_replicate_append_eq_signExtend` | Known2 | `{{m{y[lo+W-1]}}, y[lo +: W]}` is the window sign-extended to `m + W` bits | the hand-written sign extension of an entry |
| `RoundRobin.getLsbD_isolate`, `RoundRobin.isolate_eq_twoPow` | SvGolf.RoundRobin | `s & (~s + 1)` has exactly the lowest set bit of `s`: the one-hot `twoPow` | lowest-set-bit and priority logic |
| `BitVec.setWidth_one`, `BitVec.extractLsb'_setWidth_of_le`, `BitVec.eq_of_getLsbD_eq` | core | truncation to one bit is `ofBool` of bit 0 (with `BitVec.setWidth_eq`: a `BitVec 1` is `ofBool` of its bit); a part select of a truncation; equality bit by bit | a 1-bit port such as a carry; part selects of truncated words |

**Sums and XOR sums**

| name | module | what it says | use it when |
|---|---|---|---|
| `CombLib.bfVal`, `CombLib.bfVal_congr`, `CombLib.bfVal_split`, `CombLib.bfVal_shift`, `CombLib.bfVal_and`, `CombLib.bfVal_bv`, `CombLib.bfVal_bv_mod` | CombLib | `bfVal f n = Σ_{j<n} 2^j · f j`; congruence, a split at `m`, bit 0 taken off, a mask by one bit, the value of a `BitVec`'s bits (all, or the low `n`) | the value of the bit functions of a gate-level design |
| `XF.val`, `XF.val_congr_lt`, `XF.val_lt`, `XF.val_split`, `XF.val_prefix`, `XF.val_window`, `XF.val_cat`, `XF.val_not`, `XF.val_all_false` | Lib.XFVal, which imports CombWord and CombKnownBits | the same sum under another name: the bound `< 2^n`, splits, prefixes, windows, concatenations, the complement, all-false bits | a word-level design (its equations print `XF.*` helpers); a `bfVal` lemma does not rewrite `XF.val`, so state your arithmetic over the one your lemmas use |
| `XorSum.bx`, `XorSum.foldl_xor` | XorSum | `bx f n` is the XOR of `f 0, …, f (n-1)`; a `List.range` XOR fold is `bx` | GF(2) sums: carry-less products, parities, CRCs |
| `XorSum.andBit_known`, `XorSum.xorBit_known` | XorSum | the AND of two known bits; XOR-accumulating a known bit into bit `k` flips that bit and no other | a procedural XOR-accumulate loop on known vectors |
| `packBV`, `packBV_eq_ofNat`, `packBV_congr` | SeqFamily | `n` entries of `W` bits packed row-major into one `BitVec`; it is `Σ_r (v r) · 2^(r·W)`; it reads only the entries below `n` | a port that carries a matrix or a list of words |
| `List.range_succ`, `List.foldl_append` | core | `range (n + 1) = range n ++ [n]`; a fold over an append | taking the last term off a spec written as a `List.range` fold (matmul's `dot`) |

**Prefix and adder algebra**

| name | module | what it says | use it when |
|---|---|---|---|
| `CombLib.fullAdder_arith` | CombLib | `sum + 2 · carry = x + y + cin` for one full adder | a carry cell, however it is written |
| `CombLib.ripple_row` | CombLib | a ripple row's three equations give `val s + 2^N · c N = val x + val y + c 0` | any carry-propagate row: an adder, a multiplier's final adder |
| `CombLib.AddView`, `CombLib.add_value`, `CombLib.add_spec` | CombLib | the adder's four equations as a structure; its value; the task's `BitVec` form | an adder whose sum and carries are bit functions |
| `CombLib.sum_split`, `CombLib.bitvec_eq_ofNat_of_val`, `CombLib.ofBool_eq_ofNat` | CombLib | `s < 2^w` and `t = s + 2^w · q` give `s = t % 2^w` and `q = t / 2^w`; then the `BitVec` equation | the last step to a task's `BitVec` statement |
| `Lib.pgOp`, `Lib.pgOp_assoc`, `Lib.pgBlock`, `Lib.pgBlock_combine`, `Lib.grpG`, `Lib.grpP`, `Lib.grpG_combine` | Lib.Prefix | the carry operator on (generate, propagate) pairs is associative; the pair of a block of positions; adjacent blocks combine | the tree of a parallel-prefix adder (Kogge-Stone, Sklansky, Brent-Kung) |
| `Lib.rippleCarry`, `Lib.rippleCarry_eq_block`, `Lib.rippleCarry_bv` | Lib.Prefix | the carry into bit `k` is the group generate of positions `[0, k]`, and is core's `BitVec.carry` | joining a prefix tree to the sum bits |

**Multiplier arithmetic**

| name | module | what it says | use it when |
|---|---|---|---|
| `CombLib.MulNetlistView`, `CombLib.ideal_mul_view` | CombLib | an array multiplier's equations, as a structure, give `p = a * b` | an array shaped like `mul_n` |
| `XF.val_csa` | Lib.XFVal | a carry-save row: the value of `x ^ y ^ z` plus twice the value of the majority is the sum of the three values (unshifted, over `XF.val`) | 3:2 compressor rows (the shifted `csa_row` of the tree references is in no library yet: the `mul` README) |
| `XF.val_addBits`, `XF.val_subBits`, `XF.val_mulBits` | Lib.XFVal, CombWord | the value of a word-level `+`, `-`, `*`: the operands' values combined, modulo `2^w` | a design written with `+`, `-` and `*` |
| `CombLib.rowMajor_inj`, `CombLib.lexLt`, `CombLib.lexLt_wf` | CombLib | `i*W + j` with `j < W` fixes the row and the column; the lexicographic order on pairs is well founded | 2-D arrays of partial products; a rank for 2-D dependencies |

**Clocked designs: NBA folds, register windows, power-up**

| name | module | what it says | use it when |
|---|---|---|---|
| `cycleStep2_profile`, `ffDisjB_of_pairwise`, `driversOk_of_ff` | SeqProfile, SeqFamily | a cycle of an FF-only design runs every `always_ff` body on the pre-edge state, then commits the queue; the disjointness and one-driver conditions from pairwise-disjoint windows | one clock cycle (section 19, step 2) |
| `GenItem.expand2_genFor_ascending_processes`, `pairwise_flatMap_range`, `DrvWin.overlaps_some_eq_false` | Gen2, Hier2Gen | a generate loop expands to a `flatMap` over its indices; a family's windows are pairwise disjoint when each cell's are and every two cells' are; two windows are disjoint when the names differ or the ranges do not meet | the agreement (section 19, step 1) |
| `nbaFold`, `nbaFold_append`, `nbaFold_flatMap`, `nbaFold_flatMap_eq_self`, `lookup_commitNba2_of_not_mem` | NbaCommit | the commit restricted to one register; of an append; of a family's queues; a family that never writes the register leaves it; a register no write names is unchanged | committing one register at a time |
| `extract_ofBitVec_packBV`, `bvInsertAt_packBV`, `foldl_range_ofBitVec_packBV`, `LVec.insertEntries_ofBitVec`, `LVec.foldl_range_insertAt_last` | SeqFamily | read one entry of a packed family; write one entry; fold unit writes over entries `0 … m-1`; writing every entry gives `ofBitVec (packBV …)`; a reset that rewrites the same windows | register files and accumulators kept as one packed vector |
| `Lib.rowMajor_window_le`, `Lib.mul_add_mem_window_iff`, `rowMajor_le` | Lib.NatArith, Hier2Gen | entry `(i, j)` of an `M×N` row-major array ends inside it; bit `r·W + j` (`j < W`) lies in window `m` exactly when `r = m`; row `i` ends before a later row begins | bounds and disjointness of row-major entries |
| `powerUp_cons`, `powerUp_nil` | SvGolf.SeqV2 | a power-up state, one declaration at a time | rule 2: every power-up state has your register shape |

**Parameters, `$clog2` and index arithmetic**

| name | module | what it says | use it when |
|---|---|---|---|
| `clog2`, `CombView.clog2_le`, `CombView.le_two_pow_clog2` | Param, CombView | the LRM's `$clog2`; `clog2 n ≤ n`; `n ≤ 2 ^ clog2 n` | a `$clog2` localparam (an opaque value in the goals, section 4) |
| `Lib.natAbs_sub_one_add_one` | Lib.NatArith | `((x : Int) - 1).natAbs + 1 = x` for `x > 0` | the width of a declared range `[x-1:0]` |
| `Lib.window_bounds_of_natCast`, `Lib.min_add_sub_one_self`, `Lib.max_add_sub_one_self`, `Lib.add_sub_one_sub_add_one` | Lib.NatArith | the `Int` facts the range checks of an instantiated part select need | instantiation lemmas (`sv2_inst_simp`) of parametric windows |
| `LVec.ofInt_eq_ofBitVec`, `BitVec.ofInt_natCast` | Param, core | the loader's constant `LVec.ofInt w v` is `ofBitVec (BitVec.ofInt w v)`; `ofInt` of a natural number is `ofNat` | parameters and unsized constants (32-bit literals) |
| `CombView.rmN`, `CombView.rmN_inj`, `CombView.rmN_lt_iff`, `CombView.rmN_le_iff`, `CombView.rmN_add_col`, `CombView.Key`, `CombView.KLt` | CombViewArith | the row-major offset the equations print; injective and ordered lexicographically; a column offset added; the key order of `lexRank` | 2-D goals (`sv_rowmajor` uses them) |
| `SvState.cell` | CombBridge | bit `(r, c)` of a 2-D signal whose rows are `W` bits wide, in `Nat` coordinates (`st.boolAt n (rmN W r c)`) | stating a 2-D arithmetic lemma for `sv_bridge` (below) |
| `Lib.rmN_row0`, `Lib.rmN_succ0`, `Lib.rmN_last_col`, `Lib.rmN_eq` | Lib.RowMajor | `rmN` at natural coordinates, in the forms `sv_equations` prints | turning printed indices into `Nat` ones |
| `Nat.mul_add_mod_of_lt`, `Nat.add_mul_div_right` | core | `(a * b + c) % b = c` for `c < b`; `(x + y * z) / z = x / z + y` for `0 < z` | the column and the row of a row-major index |

**Floating-point value functions.** No library has the IEEE 754 format or rounding lemmas yet (the `fdivp` README
says where they are); these carry a datapath's netlist into `Nat`:

| name | module | what it says | use it when |
|---|---|---|---|
| `XF.val_shrBits`, `XF.val_shlBits_zext`, `XF.val_shlBits_one` | Lib.XFVal | the value of a logical right shift and of a left shift by a vector | normalizing, aligning and denormalizing shifters |
| `XF.top_bit_iff`, `XF.val_ne_zero_iff`, `XF.any_eq_decide_val` | Lib.XFVal | the top bit is the test `2^(P-1) ≤ value`; a value is nonzero exactly when a bit is set; an OR reduction is that test | leading-one tests, sticky bits |
| `XF.val_constBit`, `XF.val_ite`, `XF.val_zext` | Lib.XFVal, CombWord | the value of a constant, of a multiplexer, of a zero extension | exponent biases, special-case selection |
| `Lib.restRem`, `Lib.restQuo`, `Lib.restore_spec`, `Lib.val_restQuo` | Lib.Restoring | `n + 1` restoring steps give the quotient `⌊2^n · x / d⌋` and the remainder; the value of the row of quotient bits | a restoring divider's quotient |
| `Lib.scale_le`, `Lib.scale_ge`, `Lib.scale_lt`, `Lib.scale_gt` | Lib.NatArith | with `N · S = D · T`, comparing with `N / D` is comparing with `T / S` | rounding bounds stated by cross-multiplication |
| `Lib.log2_mul_two_pow` | Lib.NatArith | `log2 (e · 2^j) = log2 e + j` for `e ≠ 0` | an exponent after a shift |

### The tactics, Mathlib and habits

**The tactics at a glance.**

| tactic | goal it takes | what it does |
|---|---|---|
| `sv_structure (lexRank := k)` | `CombDesign (X.sem N) ∧ Acyclic (X.sem N)` (or either) | one application of the soundness theorem; returns the obligations (`inRange`, `driverDisjoint`, `rankDecreases`); samples `N = lb .. lb + 4` first and reports a violation with the sites, the keys and, for a rank, the read that forms the edge |
| `sv_interface` | the task's `Interface N (X.sem N)` | the ports, from the `CombDesign` profile |
| `sv_equations` | the settled-state goal | the `eq_*` / `known_*` hypotheses (generated names and stable aliases) and the obligations |
| `sv_cover` | a `cover_k` goal | a site as the witness; the cells of a 2-D array by the 2-D rule (section 2.3); an error that names the read and the writers' conditions |
| `sv_bridge e [with h₁, …]` | a `Nat`-indexed equation (a field of the arithmetic lemma) | closes it from the printed equation `e`, see below |
| `sv_rowmajor` | goals that compare `rmN` windows | rewrites them lexicographically (`rmN_lt_iff`, `rmN_le_iff`) |

**`sv_bridge`** (`LeanModels/Sv/CombBridge.lean`, since 2026-10-31). `sv_equations` prints each equation with the index
forms the summary computes: `Int` affine expressions of cast loop variables (`2 * ↑k + 1`, `↑N + ↑j + -1`),
1-D reads through `Int.toNat`, 2-D reads through `rmN W r c`. An arithmetic lemma is stated over `Nat`-indexed
Boolean functions (`S : Nat → Nat → Bool`, `S (2 * k + 1) c`, `k - 1`). `sv_bridge e` closes a goal of the
second form from the printed equation `e`:

1. it introduces the binders of the goal;
2. it instantiates `e`: its `Nat`/`Int` binders take the goal's index variables in order (a binder the goal
   does not bind is given in the term: `sv_bridge (eq_s_plain_0 N (by omega))`), its premises are proved by
   `omega` from the goal's;
3. it rewrites the instance with `rmN_add_col` (a part select `s[r][c0 +: n]` reads `rmN W r c0 + k`) and with
   the lemmas of the `with` clause, side conditions by `omega` (`with ba` turns `st.boolAt "a" k` into
   `x.getLsbD k`; `with if_pos` resolves the packed `if k < N then …`; `with XF.getLsbD_bv` reads an output bit);
4. it compares goal and instance by congruence along `&&`, `||`, `^^`, `st.boolAt` and `rmN`, and proves
   every pair of index terms that differs by `omega`; the second closer unfolds `rmN` first, for a row-0 cell
   against a flat index.

Everything it builds is a proof term the kernel checks; there is no new axiom. A failure names the index
equation it could not prove and the two reads:

```
sv_bridge: cannot prove the index equality
  ↑(2 * k✝ + 2) = 2 * ↑k✝ + 1
while matching the read
  st.boolAt "S" (rmN (2 * ↑N) ↑(2 * k✝ + 2) ↑c✝)
of the goal against
  st.boolAt "S" (rmN (2 * ↑N) (2 * ↑k✝ + 1) ↑c✝)
of the equation
```

(the goal asks for row `2k + 2`, the design writes `2k + 1`: a wrong design, or the wrong `eq_*` for the field.)
When the two sides differ in shape, not only in an index (a design that writes the constant `1'b0` where the
arithmetic reads the carry `c[i][N]`: the negative `tests/mul/negative/drop_carry.sv`), the message names them:

```
sv_bridge: the goal and the equation have different shapes here
  false
against
  st.boolAt "c" (rmN (↑N + 1) ↑i✝ ↑N)
```
Fields of a record are left as goals with `refine … { f₁ := ?_, … }` and closed one `sv_bridge` per bullet. The
shape of a bridged proof is `Examples/system-verilog/comb_bridge/bridge.lean` (pinned) and the four multiplier
references.

**Core Lean first; Mathlib when it pays.** Mathlib is allowed in a submission (README.md, "Mathlib
in submissions"), and for arithmetic that `omega` cannot do (a nonlinear identity, a `ring`
normal form, `positivity`, `norm_num`, `linarith` with hypotheses) it is the right tool:
`tests/imports/mathlib_band.lean` is a proof that uses `linarith`, `ring`, `positivity` and
`norm_num` and is accepted. Three things to know before you import it.

* **Import what you use.** Measured (README.md, same section): `import Mathlib.Tactic.Ring` or
  `.Linarith` costs 1.4 to 1.5 s of the proof's time limit once the files are in the OS cache
  (4 s the first time), `import Mathlib.Tactic` 2.2 s (11 s the first time) and 2.9 GB of memory.
  The limit counts the CPU seconds of the Lean process (decided 2026-11-05; README.md, "Proof
  effort"), so the machine's load does not count against you, but the wall-clock backstop of 5
  times the limit does see it: on a loaded or swapping machine the same import has taken ten
  times that wall clock, so leave room. The checker's comparator also replays the part of Mathlib your proof
  uses through the kernel (3,000 constants, a few seconds); `leanchecker` replays your own
  declarations. The whole-library `import Mathlib` is not available on every machine (it needs
  the whole `Batteries` build; it is then an infrastructure error, not a rejection), and a module
  that was renamed (`Mathlib.Data.Nat.Defs` no longer exists) is rejected at `imports`.
* **Mathlib's simp lemmas do not reach the tactics.** `sv_structure`, `sv_equations` and `sv_norm` finish their
  normalization with a `simp`, and a Mathlib import adds some 37,000 `@[simp]` entries to the ambient simp set
  (`Nat.cast_natAbs` turned the declared-range obligations into `|↑N + -1|`, which `omega` cannot read;
  `Order.add_one_le_iff` rewrote `x + 1 ≤ y`; and more). That used to break six of the seven shipped references
  under `import Mathlib.Tactic` and asked every Mathlib user to write `sv_core_simp`. Since 2026-11-01 the tactics'
  own `simp` calls are `sv_simp` (`LeanModels/Sv/CombCoreSimp.lean`): `simp` with the simp set of Lean core, the
  ambient one minus every tag a package of Mathlib's closure added, for that call only. So write nothing: all seven
  references are accepted with `import Mathlib.Tactic` and the proof unchanged (`tests/run.py`, `attacks`:
  `mathlib_tactics_*`). `ring`, `linarith` and `positivity` do not read the simp set and are unaffected; YOUR OWN
  `simp` and `norm_num` still see Mathlib's lemmas, which is what you want unless a proof of yours depends on core's
  set: then `import SvGolf.CoreSimp` and `sv_core_simp` (in a `section`, if you want Mathlib's `simp` elsewhere)
  erase the package tags for the rest of the file. Neither adds a declaration or an axiom; with no package imported
  both do nothing.
* **Axioms are unchanged.** Mathlib's tactics leave only `propext`, `Classical.choice` and
  `Quot.sound` (`ring`: `propext` alone; `norm_num`: `propext`; `linarith`, `positivity`: the three;
  `decide`, `decide +kernel`: none), and `native_decide` / `decide +native` / `bv_decide` add their generated
  `_native.*` axiom, which the comparator rejects wherever it is hidden.
* **`bv_decide` is not supported** (decided 2026-11-01: it runs an external SAT solver, which the checker does not
  support). A proof that uses it fails at `solution` with a hint when the sandbox is on (the solver cannot start:
  `operation not permitted`) and at `comparator` with `--sandbox off`. For a fixed-width fact use `decide +kernel` (no
  extra axiom; it enumerates, so it suits few cases), `omega` for linear facts, `simp`/`cases ... <;> rfl` for Boolean
  identities in a few variables, or the symbolic argument the task asks for anyway. README.md, "`bv_decide`", records why
  and what would enable it.

What you reach for from habit, and what to write when you would rather not import Mathlib:

| Mathlib | core Lean |
|---|---|
| `interval_cases k` | `obtain rfl \| rfl \| rfl : k = 0 ∨ k = 1 ∨ k = 2 := by omega` (one disjunct per value), then `all_goals rfl` |
| `Nat.strong_induction_on n`, `induction n using Nat.strong_induction_on` | `Nat.strongRecOn` (`induction n using Nat.strongRecOn with \| _ n ih => ...`) |
| `Nat.le_induction` | not in core; induct on the difference (`obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h`) |
| `norm_num`, `positivity`, `linarith`, `nlinarith` | `omega` for linear integer facts, `simp`, `decide` for closed or `Bool` statements, `cases x <;> cases y <;> rfl` for a Boolean identity in a few variables (a 9-variable identity is 512 cases and runs in seconds) |
| `decide` with free variables | `cases ... <;> rfl` (Lean's error says "Expected type must not contain free variables") |

Habits that help:

* State the arithmetic as a lemma **before** `sv_equations`, over `Nat`-indexed functions. For a 1-D design with
  no index casts, take exactly the printed `eq_*` as hypotheses (`add_final`): the lemma elaborates alone, fast,
  and the main goal becomes one `exact`/`refine`. For 2-D arrays (or any equation with `rmN` or `Int` index
  forms) do not restate the printed equations: instantiate the lemma in `solution` and close each hypothesis
  with `sv_bridge eq_x` (section 3); the restating theorem was 82 to 173 lines in the multiplier references.
* **Timeouts.** The default limit is `maxHeartbeats 200000` (200 M heartbeats; nothing in `check.py` or the
  lakefiles changes it). `deterministic timeout ... maxHeartbeats` errors that
  name `simp` come from the tactics' own `simp` calls (a 2-D `Acyclic` with 50 goals needs
  `set_option maxHeartbeats 400000 in` before the theorem); `maximum recursion depth` no longer comes from
  the tactics (they run with `maxRecDepth` 100000), only from your own long terms. A timeout reported at the start of
  `theorem solution` means some tactic inside it is slow, with no hint which: state the heavy
  parts as separate lemmas (`add_final`-style, or the structure theorems) and compile them one at a
  time with `LEAN_PATH=... lake env lean`, so the slow one shows itself.
* **A wrong design fails late in the proof, and loudly but opaquely.** In the proof, a functional bug
  (or a re-written but different expression) shows up as an `Application type mismatch` between two
  long Boolean terms that differ in one letter, at the line where you pass an `eq_*` hypothesis to
  your arithmetic lemma, followed by a `#guard_msgs` axioms error that is only a consequence. So
  simulate first: `check.py --unproved` already runs the design against the task's function (every
  task ships an `oracle.py`) on its post-synthesis vectors and prints a `functional:` warning naming
  the first failing input (section 0); no testbench of your own is needed. When the proof of a design
  that passes that check will not go through, suspect the proof.
* Keep `hN : 1 ≤ N` in the theorem statement: `omega` needs it for the range goals.
* **Do not put `decide +kernel` (or any tactic that adds an auxiliary lemma) early in a heavy theorem.**
  It adds the lemma by a synchronous `addDecl`, which in the file's asynchronous elaboration waits for
  the kernel check of the theorems before it: a step of a few tenths of a second then shows as tens of
  seconds in a profile and idles the thread (section 11). The tactics of this library do not do it any more
  (they decide natively and assign the proof term); your own proofs can put such a step last, or state the
  fact as its own small theorem, declared before the heavy one.
* Use `sv_structure?` / `sv_equations?` to pin down tags before writing `case inRange_3 => ...`;
  tags number from 1 in goal order.
* `all_goals first | (intros; omega) | sv_cover | ...` is the right shape for the closers; put
  the cheap ones first. `sv_cover` closes the coverage goals of nested 2-D reads (the 2-D rule); a
  goal outside its shapes takes the older search, which has a small budget and gives up (or hits the
  heartbeat limit) on nested 2-D goals.
* A functionally wrong design with the same structure (a wrong gate in the carry, say) is
  accepted by the structural tactics and rejected only by the arithmetic: if `add_final` will not
  go through, check the design (`--unproved` simulates it against the task's function) before blaming
  the proof.

### Common friction (2026-11-13)

Today's limits of the tools, as the proofs on the board met them: not rules of the game, and each may move.

* **Heartbeats.** The default `maxHeartbeats 200000` is enough for most declarations: the clocked references and eleven
  of the eighteen matmul proofs set nothing. The tactics' own `simp` needs more on a large or 2-D comb design (`mul_n`'s
  structure theorem and its `solution`: 400000), with a localparam that has `/` or `%`, and for `sv_exhaustive` on a
  flat netlist (1000000). Raise it for that declaration only, `set_option maxHeartbeats 400000 in` before the theorem.
  A file-wide `set_option maxHeartbeats` (seven matmul proofs, 1000000 to 4000000) hides which declaration needed it
  and lets a slow one run on toward the CPU limit; to find the slow one, compile the heavy parts as lemmas of their own
  ("Timeouts", above). A `whnf` timeout in a clocked run lemma has its own fix (section 19.3).
* **`instExpr2`'s `resize` equation.** In an instantiation lemma `simp`, and so `sv2_inst_simp`, cannot use it. Where
  your `sv2_inst_simp` call stops at an `instExpr2` term, unfold it by hand, `repeat (unfold instExpr2; <the same
  sv2_inst_simp call>)`, as `pe_inst` in `tasks/matmul/reference/matmul_g1.lean` does (16 of the 18 matmul proofs do).
* **What the `sv_comb` tactics do not read yet**: a conditional generate (`if`) inside a generate loop; `**` in a
  localparam (a `$clog2` localparam is read, as an opaque value: section 4); an inner loop bound computed from the
  outer genvar (`tests/mul/baselines/dadda_rc.sv`); an index or bound that is not affine in the parameters and the
  genvars (`i*j`, `i >> l`, a prefix adder's partner index). Know this before you design: the checker still accepts
  such a design, and the fallback is a by-hand proof (section 5; the Kogge-Stone, Sklansky, Dadda and Karatsuba
  baselines took it, about 1,000 to 3,200 code lines each). Section 4 lists every refusal with its message, and the
  [Refusals page](REFUSALS.md) what the checker and the language refuse.
* **Clocked designs need `always_ff` with fixed register windows.** The library's clock step (`cycleStep2_profile`)
  covers a design whose every process is an `always_ff` on one clock, with nonblocking writes to windows fixed at
  elaboration and distinct processes writing disjoint windows. An `assign` or an `always_comb` anywhere, an unregistered
  output included, means proving the combinational settle yourself, as the arbiter's proof does (section 20).

## 7. Known limits, honestly

* **Fragment.** See section 4. In particular no operators beyond those of sections 14 and 17, no `localparam` beyond
  the integer constant expressions of section 4,
  no conditional generate, no instances, no edge-triggered processes, and `always_comb` only in the first fragment of section 13. The prefix
  adders of `tests/add/baselines/` are refused today (conditional generate, non-affine indices); they are proved by
  hand (section 5). A design generated for one width (a flat netlist whose every width and index is a literal of that
  `N`) has no proof of a for-all-`N` statement at all: a multiplier proof needs a parametric design. What the tactics do not read yet is on the [refusals page](REFUSALS.md) as `later`, each row with what has to exist first
  (`sv_structure: outside the v1 fragment`).
  A parametric carry-save TREE (not a column-wise Wallace/Dadda tree) is inside the fragment after
  all, if its tree is indexed as a heap: see section 8; a row-wise Wallace tree is inside it too,
  if its rows are indexed as a tape: see section 9; a heap with `⌈N/2⌉` two-row leaves needs a
  `localparam` for the leaf count, which the tactics now read: see section 10.
* **Coverage of 2-D reads is `sv_cover`'s rule, with limits.** It reads a writer whose loop indices have a
  unit coefficient or a literal divisor in the read's row and column (`a`, `N - 1 + j`, `N + 2g + 1`) and
  whose `∃`-variables are `Nat`; a writer with two unknowns in one equation, a nonlinear index or a
  non-`Nat` binder takes the older search (it gave up on the multiplier's goals: until 2026-10-31 they were closed
  by hand, 29 to 75 lines per reference).
* **Elaboration is slower than a by-hand proof** (about 2.3 times the CPU time on these two), because
  the tactics normalize large goals with `simp`. Heartbeat limits can be hit: `mul_struct`
  needs 400000. A flat netlist with no parameter is the exception: its obligations are decided, not
  normalized (section 12), and a design that mixes plain sites with loops or a parameter still pays the
  normalization (quadratic in the number of sites for the one-driver and rank obligations).
* **The tactics are not trusted.** They run at elaboration time (their elaborators are `unsafe`
  Lean code) and only produce proof terms; the checker's kernel replay (comparator and
  `leanchecker`) re-checks every term, the final theorem depends on none of the `unsafe` code, and
  the axioms of the two references are the standard three. A tactic bug can make a proof fail, not
  make a false one pass.
* **`1 ≤ N` and `Int`/`toNat` are visible** in the goals; the goals are over `Int` indices.
* Several refusals are not source-located (see the last row of the table in section 4).

## 8. A tree multiplier: what it needed, what was hard

`tasks/mul/reference/mul_tree.{sv,lean}` is a parametric log-depth carry-save tree, proved for
every `N ≥ 1` with the same tactics (571 code lines on 2026-10-30, 322 since 2026-10-31; `check.py` `solution` stage 74.4 s before 2026-10-30, score
2034.904 GE / depth 63 at `N = 16`). An early trial found that a Dadda or Wallace tree needs a stage count
`⌈log_{3/2} N⌉`, column heights, a 3-D array, conditional generate and `localparam`, and that
`sv_structure` refuses each. This reference needs none of them, because of four choices about the
DESIGN; the tactics were not widened except for one bound (item 5):

1. **A heap instead of stages.** The tree is a binary heap in one 2-D array (`S`, `C`: row = node,
   column = bit): the root is node 0, node `k` reads its children `2k+1` and `2k+2`, the `N`
   leaves (the `N` partial-product rows, one per bit of `b`) are the nodes `N-1 .. 2N-2`. One
   generate loop over the internal nodes `k` (and an inner loop over the columns) writes the whole
   tree, so there is no stage index, no height table and no 3-D array; the tree depth is the depth
   of the heap, `⌈log₂ N⌉`. The rank of a site is `(stage, N-1-k, phase)`: a node comes after its
   children because they have the larger indices.
2. **Gather instead of shift.** A shifted partial product `a << j` is written as a read of a
   zero-padded copy `ae` of `a` at an affine offset (`ae[c + 2*N - 1 - j]`), never as a write at
   a shifted position, so every write window is inside its vector for every `j` and `c`, and
   there are no `i*j` or `N/2` terms.
3. **A constant select instead of a conditional.** The nodes whose children are both leaves
   (`2k+1 ≥ N-1`) should not compress, they should just pair their two leaves; the others are 4:2
   compressors. That is a conditional generate on `2k+1 ≥ N-1` (`≈ N/2`: not affine, refused), or a
   multiplexer on a CONSTANT: the vectors `th[x] = (x ≥ N-1)` and `nth` (its complement; `~` is not
   in the fragment) are built by two small generate loops (`N-1` zeros then `N` ones) and read at
   the affine index `2k+1`; `S[k][c] = (th[2k+1] & S[2k+1][c]) | (nth[2k+1] & <compressor>)`.
   Synthesis folds the constant select, so the pairing nodes cost nothing. (A first version
   without the select, with `(pp[2j], pp[2j+1])` pairs at `N` leaves, has a zero half: it scored
   2170.555 GE / depth 62 at `N = 16` against 2034.904 / 63, 6.7 % more area, because its root
   compresses a real pair with a zero pair; the select removed that, at the price of
   2 more small loops and 4 more equations.)
4. **Arithmetic modulo `2^(2N)`.** Every row is `2N` bits wide and its top carry is dropped; the
   proof never asks whether it is zero: node sums are equal modulo `2^(2N)` (`node_sum` carries the
   two dropped carries as a witness `q`), and the product `a · b < 2^(2N)` is the only value that
   needs to be exact.
5. **The one library change.** The loops over `2*N` columns violated the tactic's generate-fuel
   obligation `count ≤ N + 60` for `N > 60` (ls-sv's fuel is `(N+2)² + 64`, so the design was always
   fine; the obligation was just a conservative linear bound). `CombViewThm.AutoObl` and
   `CombViewSound.surfaceFuel_gt` now use `4 · Σ|parameters| + 60`.

**The proof** is the shape of section 3 with a different arithmetic: the tactics do the structure
(`tree_struct`, the `CombDesign ∧ Acyclic` bundle: 40 and 69 goals, all `intros; sv_rowmajor; omega`;
with the key `treeKey`), the ports and the equations (20 equations, of which the glue uses 18); the
coverage goals are the nested 2-D reads of the heap, closed by `sv_cover` (section 2.3; until 2026-10-31 one
macro per kind of read, `covS`, `covC`, `covX`, `covY`, `covT`, `covR`, named the writer and left the window
arithmetic to the `cov_leaf` of the `mul` reference: 99 code lines with the cases). The mathematics (`TreeArith`, plain Lean, 250 lines) is, in
order:

* `csa_row`: a row of 3:2 counters (`s = x ^^ y ^^ z`, carry `maj`, the carry row shifted one
  column) satisfies `val s + val sh + 2^W · (top carry) = val x + val y + val z`, by induction on
  the columns from `fullAdder_arith`; this is the column-weight preservation lemma a
  Wallace/Dadda proof needs, stated once;
* `node_sum`: two stacked rows give a 4:2 node (`val S + val C + 2^W · q = val SL + val CL + val
  SR + val CR`);
* `lane_gated`: a leaf row is `a · 2^j` gated by a bit of `b`, with `bfVal_split` at the shift;
* `tree_mul`: the CUT invariant. `T(t) = V(t) + … + V(2t)` (`csum V t (t+1)`) with `V(m)` the value
  of the pair at node `m`. For `t = N-1` this is the sum of the leaves, `a · b`; going from `t+1`
  to `t` replaces the children `2t+1`, `2t+2` by their parent `t`, which is `node_sum` (a
  compressing node) or an exact equation (a pairing node: its children are leaves, whose carry
  rows are zero, and `th` / `nth` are known constants there); at `t = 0` it is the root. The
  induction is on `d = N-1-t`, with all equalities modulo `2^(2N)` (`Nat.add_mul_mod_self_left`).
  The ripple final adder is `ripple_row`, and `sum_split` turns the value equation into the
  `BitVec` equation.

**What was hard**, in the order it cost time: (a) finding a design the fragment reads at all (a
stage loop, column heights and a 3-D array are all refused; the heap, the gather and the constant
select are what remove them); (b) the generate-fuel obligation of item 5, which is a library bound
and not a property of the design; (c) the glue (`tree_final`, 173 lines): each of the 18
hypotheses was the printed equation (copied from `sv_equations?`, replacing `↑N` by `(N : Int)`),
and each field of `tree_mul` needed a cast conversion (`((N - 1 + j : Nat) : Int) = ↑N + ↑j + -1` by
`omega`); since 2026-10-31 each field is one `sv_bridge eq_x` line (18 lines, `st.cell "S" (2 * N)` for the
2-D functions); (d) the coverage goals, which `sv_cover` did not reach: with the macros it was a handful
of lines per goal, and since 2026-10-31 `sv_cover` closes them (`all_goals … sv_cover`). **What the tactics did not need**: the nesting depth stays 2 (node loop, column
loop), the declarations are 1-D and 2-D, and there is no `localparam`, no `?:` and no `always`.
**What a better tree would need**: the column-wise Wallace/Dadda reduction (fewer half adders) needs
the stage and height tables of section 4's refusals; a Wallace/Dadda design that is regular enough
to be a heap is the open question (section 9 answers it for the row-wise Wallace reduction, with a
tape instead of a heap).

## 9. A Wallace tree as a tape: no heap, no stages

`tasks/mul/reference/mul_wallace.{sv,lean}` (423 code lines on 2026-10-30, 264 since 2026-10-31; `check.py` `solution` stage 40.9 s before 2026-10-30, score
2113.894 GE / depth 62 at `N = 16`) is Wallace's reduction by groups of three rows, proved for every
`N ≥ 1`. The design choice that keeps it in the fragment is again a numbering, now a TAPE: one 2-D
array `T` of `3N-1` rows of `2N` bits holds the `N` partial products (rows `0 .. N-1`), an all-zero
dummy row (row `N`, so that `N+1` rows are live and `N = 1` needs no case) and the rows the adders
append. CSA `g` (`g = 0 .. N-2`) reads the rows `3g`, `3g+1`, `3g+2` and writes the sum row `x ^ y ^ z`
at `N+1+2g` and the carry row `maj(x, y, z) << 1` at `N+2+2g`; after `N-1` adders the live window
`[3g, N+1+2g)` is the two rows `3N-3`, `3N-2`, which a `2N`-bit ripple adder adds. Everything is a
generate loop over `g` with an inner loop over the columns, reads at `3*g+k`, writes at `N+1+2*g` and
`N+2+2*g` (the carry row's column 0 is a separate plain assign, as in the array reference): affine,
two levels deep, no `localparam`, no `?:`, no division. Constant-zero operands are folded by
synthesis, so there is no hand-pruning.

**The proof** is the shape of section 8 with a simpler core. `tape_struct` (`CombDesign ∧ Acyclic`): 35 and 61
goals, all `intros; sv_rowmajor; omega`; the rank is the key `(stage, g)` (`tapeKey`, 9 lines: the
sum row and the carry row of the same adder share a rank, because both read only rows that EARLIER
adders wrote: row `3g+k ≥ N+1` was written by adder `⌊(3g+k-N-1)/2⌋ < g`, which `omega` finds, using
`g ≤ N-2`). The coverage goals (`cover_2` to `cover_5`) are all of the form "the tape cell `(r, c)` has
a writer"; `sv_cover` closes them (since 2026-10-31): the writer's adder index is `g := ((r - N - 1) / 2).toNat` for a
sum row and `((r - N - 2) / 2).toNat` for a carry row, and the parity of `r - N` is part of the condition
`omega` decides (until 2026-10-31 one macro `covT r c` split on `r < N` (a partial-product row), `r = N` (the
dummy row), or `r ≥ N+1` and then on the parity of `r - N`, and handed the window arithmetic, `/ 2` included,
to `cov_leaf`: 60 code lines with the cases; the rule costs about the same in seconds, 8 s of the file). The arithmetic (`TapeArith`, plain Lean, about 200
lines, compiles in 2 s) is: `csa_row` (a row of 3:2 counters preserves the column-weighted sum, the
carry row shifted left by one and truncated at `2N`), `lane_gated` (as in section 8), and `tape_mul`: with
`V r` the value of tape row `r`, the sum `csum V (3g) (N+1-g)` of the live window is congruent to
`a · b` modulo `2^(2N)` for every `g ≤ N-1`, by induction on `g`. At `g = 0` the window is the `N`
partial products and the dummy row, whose sum is `a · b`. The step `g → g+1` peels the rows
`3g, 3g+1, 3g+2` off the front of the window and appends the two rows `N+1+2g`, `N+2+2g` at its back,
and `csa_row` says that the sum is unchanged modulo `2^(2N)` (the dropped top carry is the witness).
At `g = N-1` the window is the two last rows, and `ripple_row` finishes. The
sliding window replaces the heap's cut of section 8, and there is no pairing case and no select
vector, so the glue has 11 hypotheses instead of 18 (11 `sv_bridge` lines since 2026-10-31) and the whole file was 25 % shorter.

**What a better tree would still need**: the column-wise Dadda schedule saves the half adders at
the edges of every row. Its column heights are not affine; that remains open.


## 10. A tree with two-row leaves: the first design that needs a localparam

`tasks/mul/reference/mul_tree_h.{sv,lean}` (522 code lines on 2026-10-30, 307 since 2026-10-31; `check.py` `solution` stage 83.6 s before 2026-10-30, score
2025.905 GE / depth 62 at `N = 16`) is the heap of section 8 with its leaves taken TWO partial
products at a time. There are `H = ⌈N/2⌉` leaves, each already a carry-save pair `(S, C) = (pp[2j],
pp[2j+1])`, in a heap of `2H-1` nodes (the root is node 0, node `k` has the children `2k+1` and `2k+2`,
the leaves are the nodes `H-1 .. 2H-2`), and EVERY internal node is a 4:2 compressor. The single-row
tree of section 8 has `N` leaves, so the nodes just above the leaves have to PAIR their children
instead of compressing, which is why it needs the constant select vectors `th` / `nth` (two small
loops, two more arrays, a multiplexer in every node). With `H` available the pairing nodes, the
select and their four equations in the glue are simply not there:

```systemverilog
localparam integer H = (N + 1) / 2;       // leaves
logic [2*H:0]            bb;              // b zero-extended
logic [2*H-2:0][2*N-1:0] S, C;            // heap nodes
...
assign bb[N-1:0] = b;   assign bb[2*H:N] = '0;
assign S[H-1+j][c] = ae[c + 2*N - 1 - 2*j] & bb[2*j];       // leaf j: rows 2j and 2j+1
assign C[H-1+j][c] = ae[c + 2*N - 2 - 2*j] & bb[2*j+1];
for (k = 0; k < H-1; k++) ...             // g_node: a 4:2 compressor on 2k+1, 2k+2
```

(`⌈N/2⌉` is not affine in `N`: before the localparam extension of the tactics this was a refusal,
`local parameters are outside the v1 fragment`, and the design could only be measured, not proved.)

**What the tactics do with `H`** (section 4): `sv_structure?` prints a `localparams:` block (`H = (N + 1)
/ 2`) and the obligations come out with the definition inlined, `(↑N + 1) / 2`, in every window and
bound: `39 + 65` structure goals (`CombDesign`, `Acyclic`), all `intros; sv_rowmajor; omega` as before,
now with `H` in them (the part select `bb[2*H:N]` needs `N ≤ 2H ≤ N + 1`, which `omega` derives from the
definition: floor division by a literal); `36` `sv_equations` obligations, `28` of them one-liners (the
reads of `ae` and `bb`, `cover_1` and `cover_2`, are `omega` too), `inputsKnown_1-2`, and six
coverage goals closed by `sv_cover` (until 2026-10-31 by five macros, `covS`, `covC`, `covX`, `covY`, `covR`, with the leaf / node
threshold `((N : Int) + 1) / 2 - 1`; no `covT`, there is no select: the rule solves the leaf row
`(N + 1) / 2 + j - 1` like any affine row). The rank key is the one of section 8 with
`(N + 1) / 2 - 1 - k` for the node order.

**What changed in the proof** against section 8 (522 lines instead of 571):

* the arithmetic (`HeapArith`, 237 code lines instead of 249) has NO pairing case: `heap_mul` takes
  `N ≤ 2H ≤ N + 1`, the zero-extended `b` as a bit function `bb`, a leaf value
  `g(2j)·(a·2^(2j)) + g(2j+1)·(a·2^(2j+1))` (two applications of `lane_gated`), and the cut-sum
  induction from `t = H - 1` (the leaves, `a · b` exactly, `csum_leaves2`) down to the root; every
  node is `node_sum`;
* the ports step (`tree_interface`) is `sv_interface` as for any design: the valuation of a design with
  localparams is `Summary.val`, which the tactic unfolds itself (section 2.2);
* the glue (`tree_final`, 154 lines instead of 173, until 2026-10-31) stated the printed equations with
  `((N : Int) + 1) / 2` and named `H` in its first step (`hHi : ((N : Int) + 1) / 2 = (((N + 1) / 2 : Nat) : Int)`,
  then `simp only [hHi] at …`); after that each fact was one `show` / `rw` / `exact` as in section 8. Now
  `refine HeapArith.heap_mul (H := (N + 1) / 2) …` and one `sv_bridge eq_x` per fact: `omega` reads the
  localparam's division in the index equalities, nothing is named (the fact `hbb2`, `bb k` for `k ≥ N`, is the
  one instance given explicitly, `sv_bridge (eq_bb_plain_4 (k - N) (by omega))`).

**The `int` trap.** Writing the localparam `localparam int H = (N + 1) / 2;` does not work: the extractor
squashes a `/` under a 2-state `int` target, and the elaborated design wraps the value modulo 2^32, so
`H = (N + 1) / 2` is false for `N ≥ 2^32` and no for-all-`N` proof can use it. The tactics refuse it
with a message that says so (section 4); `integer` (4-state) has no squash and is accepted.

**Scores** (`tests/expected.json`): `451.310 / 30`, `2025.905 / 62`, `8452.626 / 127` at `N = 8, 16, 32`
against the single-row tree's `451.310 / 30`, `2034.904 / 63`, `8453.626 / 126`: at `N = 16` 0.4 % less
area and one level shallower, at `N = 32` 1 GE less and one level deeper. What the localparam bought is the proof, not the circuit: the design is
simpler (no select, no pairing node) and the arithmetic is shorter, at about the same elaboration time.

**What a Dadda-style tree would still need** (a measurement, not a proof). A localparam bounds a
generate loop (`lp_add` and a `rect.sv` variant with a loop bound `S` and an inner loop bounded by `S`
are in the fragment), so a stage loop over a localparam `S` is expressible. The remaining obstacles are
the CONTENT of Dadda's schedule: (1) the stage count is `⌈log_{3/2}(N/2)⌉`-like, not a `+ - *` / literal
`/ %` function of `N`, nor a `$clog2` one (a `$clog2` localparam is read since 2026-11-03, as an opaque atom); (2)
the column heights of a stage are piecewise linear in the column and the stage (triangular: an inner
loop bound that mentions the OUTER genvar, `for (j = 0; j < i; j++)`, is refused, with a misleading
"nested generate" message); (3) the choice between a full adder, a half adder and a wire in a column is
a conditional generate, which is refused inside a generate loop; (4) a stage index wants a third array
dimension. The row-wise schedules of sections 8, 9 and 10 avoid all four by numbering (heap, tape) and
by gathering; a column-wise one has not been found that does. Without the tactics, by hand, the column-wise Dadda
tree is proved for every `N` since 2026-11-12: `tests/mul/baselines/dadda_rc.lean` (a ripple-carry final adder;
since 2026-11-12 an entry of `mul`, like every proved design but par's), whose design writes the stage count and the heights as constant `?:` chains, names
each stage's and column's counts with generate loops that run exactly once, and chooses a full adder, a half adder or
a wire with a generate `if` inside the loops.

## 11. Proof effort and speed (measured 2026-10-30)

How the proof files were measured, so that the numbers can be reproduced on another machine (all of it
is `lake env lean` against a staged design, `check.py --unproved --stage-dir`):

* **Sequential elaboration.** `-DElab.async=false` runs the theorems one after the other on the main
  thread, so each declaration's time is its own. With the default (asynchronous) elaboration the
  per-declaration times of `-Dtrace.profiler=true` overlap and include WAITS (below); the sum of the
  sequential times is the CPU time of the file.
* **Heartbeats.** The load of the machine moves wall and CPU seconds by 10 to 15 % between two identical
  runs (the development machine was shared). The main thread's allocation count is far steadier (a few
  percent between runs; a limit such as `maxHeartbeats` is a count of it): append
  `run_cmd do logInfo m!"HEARTBEATS {(← IO.getNumHeartbeats) / 1000}"` to the file and read the line. The
  table below is in millions of heartbeats, the import's own 6 M subtracted.
* **`-Dtrace.profiler=true -Dtrace.profiler.threshold=200`** gives the tree of tactic steps with their
  times; `-Dprofiler=true` the cumulative categories (`simp`, `tactic execution`, `type checking`
  (kernel), `typeclass inference`).

### Where the time went (before the speed work of 2026-10-30)

`mul_wallace`, sequential elaboration, CPU seconds (the other references have the same shape):

| theorem | seconds | of which |
|---|---|---|
| `tape_comb` (`CombDesign`) | 7.6 | `auto` 1.7, `inRange` 0.8, `driverDisjoint` 2.6 (the `simp` normalizations of the obligations), closers 1.7, kernel 0.6 |
| `tape_acyclic` (`Acyclic`, key) | 22.7 | `auto` 2.0, `inRange` 0.7, `driverDisjoint` 2.3, **`rankDecreases` 12.8**, closers 2.1, kernel 1.8 |
| `tape_interface` (the 23-line recipe) | 2.3 | `auto` and `inRange` AGAIN, 1.9 |
| `solution` | 20.0 | `sv_equations` 10.6 (**`cover` 6.4**, `auto` and `inRange` again 1.9, `width`/`bitRead` 1.1), the coverage macros `covT` 8.1 |
| the arithmetic (`tape_mul`, `tape_final`, lemmas) | 1.5 | |

* **The `simp` normalization of the obligations is two thirds of the file** (`sv_norm_core`, `simp only` with
  152 lemmas): 35 of 53 s for `mul_wallace`, 96 of 112 for `mul_tree_h`. The largest single items are
  the rank obligation (12.8, 14.3, 42.8 and 33.2 s for `mul_wallace`, `mul_n`, `mul_tree`, `mul_tree_h`; 77 triples
  (reader, read, writer) of `mul_wallace` give 26 goals) and the coverage obligation of `sv_equations` (6.4, 6.4, 22.5 for
  `mul_wallace`, `mul_n`, `mul_tree_h`). They scale with the number of (reader, read, writer) triples, not
  with the size of the design: a read that occurs twice in an assign (`a[i]` in the carry cell) is
  normalized twice.
* **Four tactic calls repeat the same obligations.** `auto` and `inRange` are normalized in `sv_structure`
  for `CombDesign`, again for `Acyclic`, again in the ports recipe and again in `sv_equations`; the
  one-driver obligation in `CombDesign` and (without `using hc`) in `Acyclic`. About a sixth of the file.
* **Not hotspots:** deriving the summary (`PDesign.summary` by `evalExpr`: 8 ms, 1 ms from the second call
  on; a cached summary would buy nothing), the `rfl`/`decide` steps of each call (0.3 to 0.7 s), `sv_rowmajor`
  in the closers (1 to 2 s per theorem), `leanchecker` (it replays only the submission's modules, not
  the imported library: 4.3 s CPU for `add_n`, of which 1.3 s is the import) and the comparator
  (6.5 s CPU for `add_n`).
* **A trap for profiles: the waits.** In the default asynchronous elaboration the ports theorem of
  `mul_wallace` showed 31 s of `decide +kernel` (`mul_tree`: 112 s), for a step of 0.3 s. `decide +kernel`
  makes an auxiliary lemma by a synchronous `addDecl`, which queues behind the kernel check of the
  declarations before it; the theorem sat idle until the heaviest earlier theorem had finished. Since 2026-10-30
  the tactics assign `of_decide_eq_true _ _ (Eq.refl true)` themselves after evaluating the decision natively
  (`closeByDecide`): no environment change, no wait (the ports theorem: 0.4 s in the same
  asynchronous trace).

### What the speed work of 2026-10-30 changed, and what it measured

* `sv_structure` on `CombDesign ∧ Acyclic`: one application of the soundness theorem and one round of
  obligations (section 2.1);
* `sv_interface`: the ports from `hc : CombDesign` alone, no `auto`/`inRange` re-derivation (section 2.2): 2.3 s
  of the old recipe become 0.3 s (`mul_wallace`);
* `closeByDecide` in the three tactics: no auxiliary lemma, no wait (above);
* stable aliases and `CombKnown.reads_known` (section 2.3).

Per reference, before -> after (elaboration of the whole file, sequential, the import's own 6 M heartbeats
subtracted; the CPU seconds come from the same runs on a shared machine and move by 10 to 15 % between
identical runs, the heartbeats move less; `Solution.olean` is the compiled proof, what the comparator and
`leanchecker` load; every file's `#print axioms` is pinned to `propext`, `Classical.choice`, `Quot.sound`;
warm build, the full reference suite was run on this tree):


| reference | code lines | M heartbeats | CPU s | `Solution.olean` MB | `maxHeartbeats` (structure / solution theorem) |
|---|---|---|---|---|---|
| `add_n` | 107 -> 84 | 171 -> 128 (-25 %) | 11.6 -> 7.1 | 2.88 -> 2.74 | default / default |
| `mul_n` | 235 -> 212 | 595 -> 479 (-20 %) | 40.5 -> 28.1 | 11.68 -> 11.34 | 0.4 M -> 0.4 M / default -> 0.4 M |
| `mul_tree` | 594 -> 571 | 1517 -> 1293 (-15 %) | 111.7 -> 83.8 | 26.36 -> 25.82 | 1 M -> 1 M / 4 M |
| `mul_wallace` | 446 -> 423 | 775 -> 655 (-16 %) | 56.9 -> 35.7 | 15.09 -> 14.69 | 1 M -> 1 M / 4 M |
| `mul_tree_h` | 546 -> 522 | 1286 -> 1083 (-16 %) | 102.9 -> 70.6 | 24.45 -> 23.85 | 1 M -> 1 M / 4 M |

The CPU column is the user time of the same runs, taken at different machine loads: only the heartbeat
column compares. Cold `check.py` runs of the `solution` stage (wall seconds, `LEAN_NUM_THREADS=2` and `nice`
on the loaded machine; before the change in brackets, from `score/time_limits.json`): `add_n` 6.1 and 6.6
(9.5 to 12.1), `mul_n` 29.6 (37.3), `mul_wallace` 34.9 (42.2), `mul_tree` 97.3 (87.1 to 100.0), `mul_tree_h`
94.4 (69.2 to 71.3). The two trees are not faster in wall time: their longest theorem is the rank
obligation (33 to 43 s), which the bundle does not shorten (the old `Acyclic` theorem already contained every
obligation of the new one; what goes is the parallel `CombDesign` theorem and the ports recipe, i.e. CPU,
not the critical path), and the machine was loaded during these runs. A comparison of seconds needs a
quiet machine (`score/time_limits.py`, README "Proof effort").

The default `maxHeartbeats` is 200000, that is 200 M heartbeats (the `HEARTBEATS` line above and the
tables here count in thousands or millions); nothing in `check.py` or the lakefiles raises it, so a
theorem that needs more carries `set_option maxHeartbeats N in`.

The `maxHeartbeats` column is a performance variable too: `mul_n`'s `solution` used 196.2 M of the default
200 M heartbeats before the change and still does, so it now carries `set_option maxHeartbeats 400000 in` (a hair
from the limit is a flaky proof); `mul_struct` passes at 400000 although it now proves two facts.

**Critical path (asynchronous elaboration, `mul_wallace`).** Before: `tape_interface` 34.2 s (31.2 s waiting),
`tape_acyclic` 29.5 s, `solution` 20.4 s, `tape_comb` 6.5 s, one behind the other where a `decide +kernel`
sat in between. After: `tape_struct` 21.4 s, `solution` 18.6 s, `tape_interface` 0.4 s, no waits, so
the wall clock of the file on a machine with two or more free cores should be about the longest of them plus
the import and the final kernel check, about 25 s, against the 37 to 42 s recorded for the `solution`
stage before (`score/time_limits.json`). That is an ESTIMATE from traces taken on a loaded machine
(one effective core: 51 s wall for 51 s of CPU): re-measure with `score/time_limits.py` on a quiet one.

### The glue and the coverage goals (measured 2026-10-31)

Two things the player still wrote in every multiplier reference were not the mathematics: the glue between the
printed equations and the `Nat`-indexed arithmetic (a theorem restating every printed equation, `mul_final` /
`tree_final` / `tape_final`, and one `show` / `rw` / `exact` per field), and the coverage goals of the 2-D reads
(macros and `case cover_k` bodies). `sv_bridge` (section 6) and the 2-D rule of `sv_cover` (section 2.3) replace
them.

Code lines (comments and blank lines removed, the count of `leaderboard.py`):

| reference | 2026-10-30 | `sv_bridge` | + 2-D `sv_cover` | glue before | coverage before |
|---|---|---|---|---|---|
| `mul_n` | 213 | 150 | 70 | 90 | 81 |
| `mul_tree` | 571 | 420 | 322 | 179 | 99 |
| `mul_tree_h` | 522 | 390 | 307 | 159 | 85 |
| `mul_wallace` | 423 | 323 | 264 | 119 | 60 |
| total | 1729 | 1283 | 963 | | |

("glue" is the statement and body of the restating theorem plus the lines that passed the equations to it,
"coverage" the macros, the `case cover_k` bodies and their closer.) The by-hand `mul_n_byhand.lean` is unchanged at 1385.

Heartbeats of `theorem solution` (thousands, the units of `maxHeartbeats`; `run_cmd` markers, sequential
elaboration; the glue theorem was a separate declaration before `sv_bridge`):

| | `mul_n` | `mul_tree` | `mul_tree_h` | `mul_wallace` |
|---|---|---|---|---|
| 2026-10-30: `solution` + glue theorem | 196,171 + 2,820 | 444,312 + 9,563 | 400,140 + 12,963 | 310,439 + 7,596 |
| with `sv_bridge` (glue inside) | 201,290 | 458,172 | 421,223 | 324,405 |
| with the 2-D `sv_cover` | 183,461 | 434,104 | 400,123 | 313,819 |
| `set_option maxHeartbeats` on `solution`, 2026-10-30 / now | 400000 / 400000 | 4000000 / 600000 | 4000000 / 600000 | 4000000 / 500000 |

The three tree references were far inside 4 M; 600000 and 500000 leave 38 to 59% over what they use.
`mul_n` uses 92% of the default 200 M and keeps its 400000.

Seconds (sequential elaboration, `-Dtrace.profiler=true`, `tools`-style breakdown of the profile; a run on a loaded
machine moves the unchanged parts by 3 to 8%, so read differences below that as noise):

| s | `mul_n` | `mul_tree` | `mul_tree_h` | `mul_wallace` |
|---|---|---|---|---|
| glue (theorem + call) before; the `sv_bridge` bullet after | 0.23; 0.35 | 0.68; 0.83 | 0.95; 1.32 | 0.53; 0.83 |
| coverage before (cases + macro definitions); the closer after | 1.10; 0.83 | 3.66; 2.21 | 3.29; 2.32 | 7.69; 8.22 |
| `sv_structure` (the four obligations) | 14.4 | 44.8 | 34.2 | 15.2 |
| of which the rank obligation | 9.8 | 34.5 | 25.6 | 10.7 |
| `sv_equations` | 8.3 | 20.1 | 17.6 | 9.4 |
| of which the cover obligation | 4.6 | 13.7 | 11.7 | 5.6 |
| whole file (sum of the commands), 2026-10-30 / now | 30.1 / 31.3 | 85.7 / 88.2 | 71.6 / 72.8 | 40.8 / 41.7 |

Unprofiled, default asynchronous elaboration (wall): 28.9 / 72.7 / 62.1 / 36.0 s before, 25.2 / 67.3 / 54.0 /
31.6 s after. The finding is that the glue and the coverage macros were never where the time goes: the glue
is at most 1.3% of a file and the coverage 4 to 19%; **the rank obligation is 26 to 40% and the cover
obligation inside `sv_equations` 14 to 16%**, and those are the tactics' own `simp` normalizations. `sv_bridge` and the 2-D rule
shorten the files by 44% and leave the seconds where they were. (`tests/run.py --only mul`: references 33/0,
negatives 6/0.) One cost lesson of the 2-D rule: the first version of the rule's last `omega` took the Wallace coverage
from 8 s to 18.7 s, because `Int.toNat` and `/` each cost `omega` a case split and a negated conjunction of
several writers multiplies them; skipping a writer that the hypotheses alone refute (one small `omega`) brought
it back to 8.2 s and made the heartbeats lower than the macros'.

### What still costs, in order (the candidates for the next speed work)

1. The rank obligation (`rankDecreases`): 12 to 43 s of 40 to 110 s. Three cheaper normalizations were
   tried on the `mul_wallace` goal and did not help (a `dsimp only` pass before the `simp only` set: no
   change; the same set in two passes, the cleanup lemmas last: 16 s against 11 s; the profile shows
   the cost is the volume of rewriting on the unfolded (reader, read, writer) triples, about 0.15 s each). What would help
   is fewer or cheaper triples: deduplicated reads in the summary's obligations, a static pre-filter of
   triples that cannot overlap, or a reflective obligation compiler (the summary is a value at tactic
   time; the goals are linear arithmetic).
2. The coverage obligation of `sv_equations` (6 to 22 s). (The coverage macros the player wrote, `covT`,
   8 s in `mul_wallace`, are gone since 2026-10-31; the 2-D rule costs about the same.)
3. The in-range and one-driver obligations (2 to 6 s each).
4. The default `simp` that ends `sv_norm` and the loop `repeat (sv_eq_norm; try simp)` (3 s of the 6.4 s
   `cover` normalization of `mul_wallace`; 14 s of `mul_tree_h`'s 112 s): a fixed `simp only` list
   would save about a tenth of the file, at the price of the normal form no longer being whatever
   the default set produces.

Since 2026-10-31 (section 12) candidates 1 to 3 are gone for a FLAT netlist with no parameter: the tactics decide
the five obligations as closed statements instead of normalizing them, so the rank, coverage, in-range and
one-driver costs above do not occur there. For a design with loops the list stands as measured.

### The proof's own share: four rules (2026-11-04)

A profile of the references (thousands of heartbeats, `-Dtrace.profiler.useHeartbeats=true`, sequential) found that
the largest single cost of `fdivp.lean` was not a tactic but the reference's own glue: `theorem chain`, 873 of 2 282,
852 of them in 32 `omega` calls. Four rules, each measured on `tasks/fdivp/reference/fdivp.lean`:

1. **`omega` pays for every case split in its context, not only for the goal's.** It splits on each `≠`, `¬(_ ∧ _)`,
   `_ ∨ _` and `↔` among the hypotheses, and on each `Nat` `-`, `Int.toNat`, `natAbs`, `min` and `max` in them, and
   the problem grows with the product: each such fact about doubles the cost (`≠`: 279 -> 3 084 thousand at seven
   facts). Division and remainder by a constant do not split; they add terms and inequalities, so their cost grows
   linearly (1 to 5 irrelevant `a / 3 + b % 5 = c` facts: 284, 354, 429, 517, 619). The same goal, `((w : Int) + p + -2).natAbs + 1 = w + t`, costs
   377 with no irrelevant fact in the context, then 603, 958, 1 411, 2 511, 5 360, 11 403 and 38 589 with one to
   seven facts of the kinds `chain` carries (`e ≠ 2 ^ w - 1`, `¬(e = 0 ∧ f = 0)`, `y + l = x ∨ y + l = x + z`), and
   481 after `clear` of the seven. So: state the arithmetic side conditions as `have`s at the top of the theorem, while
   the context is small; prove a fact that needs `omega` over a disjunctive premise in a `have` stated BEFORE the
   other premises enter (`hfin` in `chain`: `∀ x, ¬(nanN f x ∨ infN f x ∨ zeroN f x) → …`, proved right after
   `have hfp := f.hp`), or as a small lemma; and `clear` a case-split fact as soon as it is consumed
   (`clear hns hfa hfb hya_l hyb_l` in `chain`, after the two `norm_facts`). A propositional consequence of such a
   fact (`hfa` from `hns`) is a term (`Or.inl`, `Or.inr`), not an `omega` call. `chain` (profiled): 873 -> 242 with
   the `clear` alone; the two large calls left (the classifications `hfa`/`hfb`, 108 and 65, still run before the
   `clear`) went with the hoisted `hfin`. Unprofiled, the whole change: `chain` 817 -> 62 thousand heartbeats, the file
   2 035 -> 1 131 (-44%), 111 -> 63 s sequential.
2. **No `#print axioms` pin in a solution.** check.py's comparator checks the axioms of `Submission.solution` itself,
   against the task's allowed set (`--allow propext,Classical.choice,Quot.sound`; README, stage `comparator`), so a
   `#guard_msgs in #print axioms solution` at the end of the file checks nothing new. It is cheap but not free:
   unprofiled and sequential, fdivp's takes 756 ms and 8.8 thousand heartbeats (0.8% of the file), mul_tree's 184 ms.
   (Under the profiler it showed as 10.5 s, an artifact of tracing.) Pin the axioms of a library theorem where you want
   the documentation; leave the solution's to the checker.
3. **Close the obligations of `sv_equations` with the right closer, not with a long cascade.** A cascade
   `all_goals first | A | B | …` runs every failing alternative before the one that works, on every goal. fdivp's (60
   goals): 14 thousand in the alternatives that closed a goal, 76 thousand in those that failed first, almost all of it
   `sv_cover` searching three conjunctions it could not close as a whole (29 000, 29 000, 11 700 each; `sv_cover` now
   splits such a conjunction itself, section 2.3: the same cascade now spends 11 thousand in winners and 0.9 in failures,
   on 48 goals). Read the goals with `sv_equations?`, order the alternatives
   cheap-and-specific first, and close a family by its tag where you know its closer (`case inputsKnown_1 => …`, as the
   references do). `set_option sv_comb.profile true` prints what each obligation's normalization costs.
4. **Hand `auto` and `inRange` to `sv_equations`** (section 2.1): the triple `CombDesign D ∧ Acyclic D ∧ SharedObl
   design.pdesign [N]` from `sv_structure`, `obtain ⟨hc, ha, hso⟩`, and `sv_equations` does not normalize the two again
   (the synthetic chains of 24 sites: the equations theorem -16 to -28%).

Per reference, before -> after these rules (whole file, thousands of heartbeats, sequential, no profiler, the two
heartbeat markers of `run_cmd` after the imports and at the end; seconds sequential on the shared machine, load 5 to 11;
the nine references of the plain recognizer take the triple, the `always_comb` ones, the by-hand ones, the flat
`aes_sbox` ones and the clocked ones are unchanged, to the heartbeat; check.py's `solution` stage, one cold run each
after: fdivp 29.7 s (64 to 72 s recorded on 2026-11-03), Newton 39.8 s (45 to 46 s)):

| reference | before | after | change |
|---|---|---|---|
| `fdivp` | 2 034 879 (111 s) | 1 131 345 (63 s) | -44% (`chain` 817 -> 62, `solution` 427 -> 290) |
| `fdivp_newton` | 1 627 482 (96 s) | 1 458 240 (84 s) | -10% (`solution` 584 -> 415; its `chain` keeps its `omega` calls) |
| `mul_tree` | 631 587 | 571 337 | -10% |
| `mul_tree_h` | 596 887 | 543 499 | -9% |
| `mul_wallace` | 519 931 | 484 485 | -7% |
| `mul_n` | 318 441 | 284 016 | -11% |
| `clmul_n` | 187 278 | 165 436 | -12% |
| `add_mux` | 131 656 | 114 205 | -13% |
| `add_n` | 113 677 | 98 387 | -13% |

The same rules apply to the glue of the other references; the Newton reference's `chain` was left as it is (112
thousand heartbeats, 94 of them `omega`; `omega` is 20% of that file).
The SRT reference (`fdivp_srt`, 69 sites, registered 2026-11-05) took the triple when it was added after them:
`fdiv_struct` 670 -> 672 thousand heartbeats, `solution` 959 -> 700 (`sv_equations` alone was 749 before), with
`Elab.async false`; its `chain` is 90 thousand.

## 12. A flat 113-gate netlist: the first fixed-size tactic proof (2026-10-31)

`tasks/aes_sbox/reference/sbox_bp.lean` proves the AES S-box task for the Boyar-Peralta netlist
(`reference/sbox_bp.sv`): 113 continuous assigns over `^` and `&`, no generate loop, 105 internal nets, a
design with NO parameter (the statement is `CombTask.StatementFixed`; the tactics read a parameterless design
without change). It is the scalability test the project wanted: tactics tuned on loops (a few sites, many
instances) meet 113 distinct plain sites. It went through in two steps.

* **The first proof, by hand (the "before").** It went through, but not with `sv_structure`: two of the
  obligations are quadratic in the number of sites, so the proof applied the library theorem by hand and had the
  kernel decide them; `sv_equations` needed `set_option maxRecDepth 100000`, did not name the equations
  (a count off by one) and left 221 coverage goals that were closed one by one with the writer's position in a
  113-way disjunction. 654 lines (556 code lines), 99 s of CPU. Its measurements are kept below.
* **With the flat-netlist tactics (now).** The tactics decide the obligations of a flat netlist, name the equations whatever the last
  assign drives, run with `maxRecDepth` raised, and `sv_cover` picks a site witness by name. The proof is
  one `sv_structure` call, `sv_interface`, `sv_equations`, a 5-line local `elab` that chains the 113 equations
  into the induction, and the arithmetic: 295 lines (202 code lines), 47 s of CPU.

The file is generated from the netlist (`tests/aes_sbox/validate/gen_bp_proof.py`, template
`sbox_bp.lean.tmpl`): the tables are the gate list, the net each environment index stands for, the rank (each
gate's depth) and the 113 equation names; everything else is the template, about 100 lines of mathematics.

### What the proof does (now)

| step | how | seconds (CPU, sequential, profiler on) | heartbeats (M, kernel included) |
|---|---|---|---|
| `bp_struct`: `CombDesign ∧ Acyclic` | `sv_structure (rank := rippleRank (fun p => bpRank.getD p 0) (fun _ _ _ => 0))`: no goal left | 12.2 | 127 (default limit) |
| `bp_interface` | `sv_interface` | 6.1 | 54 |
| `bp_correct` | `decide +kernel`: the packed program on all 256 inputs | 10.5 | 66 |
| `solution` | `satisfiedAt_of_comb`, `sv_equations`, `gok_chain` over the 113 stable names, `bp_out` | 23.3 | 394 (set 1 000 000) |
| the other lemmas | induction over the gate list, `GOK`, `bp_vals`, … | under 0.1 each | about 1 each |

`sv_equations` returns the main goal and `inputsKnown` only; the in-range, width, bit-read and coverage
obligations are decided (`decided (flat netlist: …): auto, inRange, width, bitRead, cover`). `solution` takes
the 113 equations by their stable names: `eq_y14_1`, …, and `eq_y_1` … `eq_y_8` for the bits of `y` in source
order. Whole file: 47 s of CPU (`lake env lean`, default asynchronous elaboration, `LEAN_NUM_THREADS=2`, a
shared 16 GB laptop), axioms `propext`, `Classical.choice`, `Quot.sound`. `Solution.olean` is 18.2 MB
(14.5 MB in the first proof: each decided obligation puts the instantiated summary into the proof term), and the kernel
replay did not get slower (`leanchecker` 47 to 50 s, comparator 19 s). Three cold `check.py` runs
(`--postsynth full`, fresh staging directory each): `solution` stage 53.7, 51.0 and 50.9 s (96.0, 95.1 and 90.9 s
for the first proof), whole run 127 to 136 s. `bp_correct` no longer needs `set_option maxRecDepth`; `solution` keeps one
`set_option maxHeartbeats 1000000` (it needs about 400 M heartbeats, the default limit is 200 M).

### Now: what the tactics do for a flat netlist

* `sv_structure`: when every site is plain and the goal mentions no free variable, the four obligations
  (`auto`, `inRange`, `driverDisjoint`, `rankDecreases`) are applied through the `…_of_plain` lemmas of
  `LeanModels/Sv/CombViewPlain.lean` (`Loops.all [] σ P` is `P σ`) and their premises, closed decidable
  statements about the site list, are closed with `closeByDecide`. Nothing is returned.
* `sv_equations`: the same for `auto`, `inRange`, `width`, `bitRead` and `cover`
  (`LeanModels/Sv/CombEqPlain.lean`; the coverage goes through `SrcPlain`, the source predicate with the loop
  quantifier removed). It returns the main goal and `inputsKnown`. The stable names are produced for every
  site: the sites are the first `n` conjuncts of the normalized view, so a last assign that drives a bit of a
  vector (a knownness fact that is a pair) no longer defeats the count.
* `sv_structure`, `sv_interface`, `sv_equations` and `sv_cover` run with `maxRecDepth` raised to 100000
  (scoped to the tactic call), so a netlist of a hundred sites needs no `set_option maxRecDepth`.
* `sv_cover` picks a SITE witness by name when a design that is not decided has many plain sites.
* Any failure (a loop, a free parameter, an `always_comb`, a premise that is false) takes the old route with
  its old goals: the goal dumps of the references and of every `Examples/system-verilog` file that calls the
  tactics are byte-identical before and after.

`sv_structure` on the first `n` assigns of `sbox_bp.sv` (the rank is the gates' depth), CPU seconds of
`lake env lean` with the import (about 1 s) included, and the heartbeats of the theorem alone (import and
`load_sv` subtracted: 9 M), sequential elaboration:

| n | before: seconds | after: seconds | after: M heartbeats |
|---|---|---|---|
| 10 | 6.0 | 3.1 | 30.7 |
| 20 | 12.1 | 3.4 | 36.5 |
| 40 | 37.7 | 4.6 | 50.4 |
| 60 | 83.3 | 6.2 | 67.7 |
| 80 | | 7.9 | 84.6 |
| 100 | | 10.0 | 106.9 |
| 113 | fails: 4 min 23 s, then `maximum recursion depth` | 11.6 | 122.4 |

(The "before" seconds are the flat-netlist tactics' own runs with `maxHeartbeats 0`; the first proof's `simp` seconds were 2.5, 7.7, 27.3
and 63 for n = 10, 20, 40, 60.) The growth is linear, about 0.1 s per site; the mild upward bend is the kernel
check of the pairwise one-driver decision. There is a fixed cost of about 2 s per call. A first version that
decided only the one-driver and rank obligations took 17 s but 355 M heartbeats at 113 sites, over the default
200 M: the two LINEAR obligations (`auto`, `inRange`) cost about 250 M of `simp` there, which is why they are
decided too.

`sv_equations` on the 113 sites (sequential, profiler on): about 59 s before (obligations: `auto` 6.4,
`inRange` 4.1, `width` 5.5, `bitRead` 2.3, `cover` 30.8, normalization of the view 8.5, names 1) and
11 s after (the normalization of the view, 8 s, is what is left); `solution` 70 s -> 23 s. With a free parameter
the old route is back: the same netlist with an unused parameter takes the normalization of the obligations
again (26 sites need `maxHeartbeats 2000000`, `Examples/system-verilog/flat_net/sv_cover_site.lean`).

The reference proof, by hand -> with the flat-netlist tactics:

| | by hand | with the names | the tactics |
|---|---|---|---|
| lines / code lines | 654 / 556 | 517 / 425 | 295 / 202 |
| CPU seconds, whole file | 99 | 93 | 47 |
| `bp_struct` M heartbeats | 341 (set 600) | | 127 (default) |
| `solution` M heartbeats | 1 678 (set 2 500) | | 394 (set 1 000) |
| `set_option maxRecDepth` | structure, `solution`, `bp_correct` | `bp_correct` | none |

### Before: what the proof did by hand

This subsection and the next ("What did not scale") describe the tactics and the proof as they were BEFORE
the flat-netlist tactics (the measured "before": 654 lines, `sv_structure` not usable at 113 sites). The tactics have changed; the
numbers are kept as the baseline, and the recipe after them is the current one.


| step | how | seconds (CPU, sequential) | heartbeats (`maxHeartbeats` units) |
|---|---|---|---|
| `bp_struct`: `CombDesign ∧ Acyclic` | `comb_acyclic_view` applied by hand; `hs h1 harity hag` by `rfl`, `hok` and the two quadratic obligations by `decide +kernel`; `hauto`, `hin` by the tactic's own `sv_norm` | 18.8 | 341 k (set 600 k) |
| `bp_interface` | `sv_interface` | 6.1 | 54 k |
| `bp_correct` | `decide +kernel`: the packed program on all 256 inputs | 11.1 | 66 k |
| `solution` | `satisfiedAt_of_comb`, `sv_equations`, the 113 equations out of `key`, 221 coverage closers, `bp_out` | 47 | 1 678 k (set 2 500 k) |
| the other 11 lemmas and defs | induction over the gate list, `GOK`, `bp_vals`, ... | under 0.1 each | about 1 k each |

Leftover goals: `bp_struct` returns none (`hauto` and `hin` are closed by `sv_norm` itself, `hok`, `hdisj`,
`hrank` by the kernel); `sv_equations` returns 224: the main goal, `width` (`rfl`), `inputsKnown`
(`inKnown_ofBitVec`) and 221 `cover_k` (17 reads of an input bit, `Or.inl (by decide)`; 204 reads of a net,
closed with the writer's position in the disjunction).

Whole file: 99 s CPU (`lake env lean -DElab.async=false`, `LEAN_NUM_THREADS=2`, a shared 16 GB laptop), `.olean`
14.5 MB, axioms `propext`, `Classical.choice`, `Quot.sound`. `sv_equations` is 35 s of the `solution`'s 47.

### What did not scale, and the numbers (before the flat-netlist tactics)

1. **`sv_structure` (`CombDesign ∧ Acyclic`).** Measured on the first `n` assigns of the netlist (profiler,
   `maxHeartbeats 0`), total `simp` seconds: n = 10: 2.5, 20: 7.7, 30: 15.6, 40: 27.3, 60: 63, i.e. about
   `n^1.9`; the kernel check of the theorem 2.0, 3.2, 5.2, 7.7, 15.2 s. At n = 113: 4 min 23 s of CPU at
   4 000 000 heartbeats, then `maximum recursion depth has been reached` inside `simp`; at the default
   400 000 a heartbeat timeout after 23 s. The cause, from `CombViewThm.lean` and `CombViewTactic.lean`:
   * `DisjObl σ` is `s.lsites.Pairwise (DisjOne σ) ∧ …`; `sv_norm_core` unfolds it with `List.pairwise_cons`
     into n(n-1)/2 = 6 328 separate goals, each normalised by `simp` (the last `simp` of the four is the
     biggest, 4.9 / 10.5 / 18.9 / 45.1 s at n = 20 / 30 / 40 / 60).
   * `RankObl' R σ` is `∀ a ∈ s.lsites, ∀ r ∈ a.site.rds, ∀ b ∈ s.writersOf r.name, …`; unfolding `writersOf`
     (a `List.filter` over all sites) once per read gives 2n filters of n string comparisons each:
     191 s of `simp` and 60 s of `congr simp thm` at n = 113.
   Both statements are CLOSED when the design has no parameter and no generate loop (`hdrs = []` for every
   site): the kernel decides them in seconds.
2. **`sv_equations`** works (35 s) but needs `set_option maxRecDepth 100000` (the default dies with
   `maximum recursion depth`, and so does `sv_equations?`), and:
   * the stable aliases `eq_<signal>_<k>` are NOT produced: its naming heuristic (`countAnd`) finds 114
     knownness conjuncts for 113 sites, because the LAST assign (source order) drives a bit of the vector
     output `y`, whose knownness fact is a pair, which the right-spine count splits. The equations stay in
     `key` (`key : (e0 ∧ … ∧ e112) ∧ (k0 ∧ … ∧ k112)`); the proof takes element `k` out with projections
     (`(keyE.2^k).1`; an `obtain ⟨e0, …, e112⟩` on it cost 30 s, a third of the proof).
   * the 221 `cover_k` obligations are not closed by `sv_cover` (its witnesses are `Nat`/`Int` variables):
     for a plain site the goal is `∃ b, (b = site_0 ∨ … ∨ b = site_112) ∧ …`, and the proof gives the
     writer's position in the disjunction (`exact ⟨_, Or.inr (… (Or.inl rfl)), by simp only [LoopsE]; decide⟩`).
     An input bit is `Or.inl (by decide)`. A read of `x[0]` leaves no goal (the tactic's `simp` closes it).
3. **Kernel evaluation of an accumulator.** The first model of the netlist was a list environment extended
   gate by gate; `decide +kernel` of "each gate's value is its operator applied to its operands' values" over
   256 inputs ran 23 minutes without an answer: the kernel has no call-by-need, every use of the accumulator
   re-evaluates it (one evaluation was 0.35 s, so 256 x 113 x 3 of them). The packed model (the environment is
   ONE natural number, bit `i` the value of net `i`, `stepN e k g = if gate then e ||| 2 ^ (8 + k) else e`)
   is evaluated by GMP arithmetic: all 256 inputs in 11 s. The link between the equations of the state and
   the packed program is one induction over the gate list (`runN_inv`, `bp_vals`), not a computation.

### The recipe for a flat netlist (CRC, MixColumns, SECDED, MDS matrices)

* **Let the tactics decide it.** `sv_structure (rank := rippleRank (fun p => <depth of site p>) (fun _ _ _ => 0))`
  (the rank is the gate's depth in the dependency graph, section 2.1), then `sv_interface`, then in the main
  theorem `sv_equations`, which hands over `eq_<net>_<k>` and `known_<net>_<k>` for every gate and the
  `inputsKnown` goals; no `all_goals` closers except for `inputsKnown`. Do not name `width_k` or `cover_k`
  goals: they do not exist for such a design.
* **State the arithmetic as a program the kernel can run and an induction the equations can feed**: the gate
  list as data, the environment packed in one `Nat`, `GOK` (an inductive predicate: operands earlier than the
  result, the state meets the gate's equation), one induction (`runN_inv`) from `GOK` to "the state is the
  program's environment", and the 256-input table by `decide +kernel`. A 5-line local `elab` (`gok_chain`)
  builds `GOK` from the equation names in one loop of `refine GOK.cons …`, with no 113-deep term to elaborate.
  A first model of the netlist as a list environment extended gate by gate ran 23 minutes without an answer
  (the kernel has no call-by-need); the packed one takes 11 s.
* **Heartbeats**: the default is 200 M. `bp_struct` fits it (127 M); `solution` needs 394 M, mostly the
  normalization of the view into the 226 named hypotheses, and carries `set_option maxHeartbeats 1000000 in`.

### What the first proof asked of the tactics, and what became of it

* `runSvStructure`: close the obligations of a plain, parameter-free design with `closeByDecide` on closed
  statements instead of `sv_norm`; the lemmas moved into the library (`CombViewPlain.lean`). Done, and extended
  to `auto` and `inRange` (heartbeats), and to `sv_equations` (`width`, `bitRead`, `cover`: `CombEqPlain.lean`).
* `sv_equations`: count the sites structurally (the aliases are produced when the last site drives a vector
  bit), and close the `cover_k` goals of a plain site by the writer's name. Done twice: for a flat netlist the
  coverage is decided and the goals do not exist; for a design that is not decided, `sv_cover` picks the site
  by name.
* a default `maxRecDepth` for the tactics' own `simp` calls: done (`withDeepRec`, `Core.Context`, scoped to
  the tactic call).

## 13. An `always_comb` carry cell

`tasks/add/reference/add_proc.sv` is the ripple adder of section 2 with the carry cell written as a
procedural block inside the generate loop:

```systemverilog
always_comb begin
  if (p[i]) c[i+1] = c[i];
  else      c[i+1] = a[i];
end
```

and `tasks/add/reference/add_proc.lean` proves the same statement for every `N ≥ 1` (accepted by
`check.py`; it scores like `add_n`, because Yosys turns the mux into the same NAND/XOR netlist).

**What the tactics accept (the first fragment).** One `always_comb` per target window; the body is a
tree of `if (cond) ... else ...` (nested, `else if` chains, `begin ... end` around a branch) whose
leaves all assign the SAME single window (`c[i+1]`, or a whole signal) with a right-hand side of the
assign fragment (an expression of `& | ^`, `~ !`, reductions, `&& ||`, `== !=`, `?:`, section 14; a
concatenation; a fill), and whose conditions are such expressions over one-bit accesses and literals. The body may not read the window it writes (a verbatim read
is refused by the loader itself, `AlwaysComb:self-read`; a read that can overlap for some index
is the obligation `noSelfRead`, below). Everything else in a body is refused, each with a message
that names the site (table in section 4): an `if` without `else` (a latch), a second statement
or a second window, nonblocking assignment, a `case` outside the fragment of section 15. Those are the planned
next steps (several windows in one body, default-then-override, temporaries, `case` arms that are trees); a
design that needs them has the by-hand route of section 5.

**What changes in the proof.** The settle theory is about continuous assigns, and `design.sem N`
still contains the procedural process, so `CombDesign (design.sem N)` is false. What holds is the
same statement about the LOWERING of the design (`Design2.lowerComb`: each `always_comb` body replaced
by the one assign `assign {c[i+1]} = {...}` it computes). Three statements change shape; the tactics
and their syntax are the same, and `import LeanModels.Sv.CombProcTactic` and `import LeanModels.Sv.ProcNoQualified`
are the extra lines:

```lean
theorem add_struct (N : Nat) (hN : 1 ≤ N) :
    ∃ d', (design.sem N).lowerComb = some d' ∧ CombDesign d' ∧ Acyclic d' := by
  sv_structure (rank := rippleRank (fun p => if p = 0 then 0 else N + 1)
    (fun _ pos i => if pos = 0 then 0 else i.toNat + 1))
  all_goals (intros; omega)

theorem add_interface (N : Nat) (hN : 1 ≤ N) {d'} (hl : (design.sem N).lowerComb = some d') :
    SvGolf.Tasks.Add.task.Interface N (design.sem N) := by
  sv_interface

-- in `solution`:
  obtain ⟨d', hl, hc, ha⟩ := add_struct N hN'
  refine CombTask.satisfiedAt_of_lowered (add_interface N hN' hl) hl hc ha (NoQ.sem_noQ (by decide) _) ?_
  intro st heqs hs v hv        -- heqs : CombEqs d' st, hs : StateShape d' st
  ...
  sv_equations                 -- finds hl, hc, ha, heqs, hs by type
```

* `CombTask.satisfiedAt_of_lowered` (`SvGolf.Comb`) is `CombTask.satisfiedAt_of_comb` for a design that lowers; its
  argument `hnq` (no `unique` or `priority` `case`) is `NoQ.sem_noQ (by decide) _`. The reference keeps a ten-line copy
  of its own; a new proof uses the library's.
* `sv_structure` returns one more obligation, `noSelfRead` (no read of the body overlaps the window it
  writes), closed by `intros; omega` like the others; a violation at a sampled `N` is reported with the
  site.
* the carry cell's equation is the body's own, `eq_c_2 : ∀ i, i < N → st.boolAt "c" (i + 1) = if
  st.boolAt "p" i = true then st.boolAt "c" i else st.boolAt "a" i`; the arithmetic (`add_final`) turns
  it into the majority by a case split on three Booleans. The other equations, `known_*` facts,
  names (`eq_<signal>_<k>`) and obligations are as in section 2.3.
* the flat-netlist fast path of sections 2.1, 2.3 and 12 (the tactic DECIDES the obligations of a design
  with no loop and no parameter) is not taken for a design with an `always_comb`: its obligations are
  normalized as before. The stable names are produced for every site there too, also when the last process of
  the file drives a bit of a vector output (`Examples/system-verilog/flat_net/proc_hint.lean`).

**A refusal can never be accepted.** When a new elaborator refuses (the table above), it logs its
error and admits the goal, so the file does not compile, and the theorem depends on `sorryAx`, which
the checker's axiom check refuses too. `Examples/system-verilog/comb_proc/comb_errors.lean` pins the
messages and shows the `sorryAx`; `tests/add/negative/add_proc_case.sv` is a correct adder whose carry cell
is a `case`: `check.py` rejects it at the `solution` stage with the proof of the reference.

**The advisory `--tactics` probe** (README) asks the assign-only tactic and does not yet know the
`always_comb` shape: it reports `in_fragment: false` for `add_proc.sv` although `sv_structure` accepts
it in the lowered shape. Trust the shape above, not the advisory, for a design with an `always_comb`.


## 14. Operators in expressions: `~ !`, reductions, `&& ||`, `== !=`, `?:` and `+ -`

The right-hand side of an `assign`, a leaf of an `always_comb` and an `if` condition may be built from, besides
the gates `& | ^`:

| you write | the equation (`sv_equations`) | the width rule (the `width_k` goal is false otherwise) |
|---|---|---|
| `~e` | `!` over `Bool`: `st.boolAt "y" k = !(st.boolAt "a" k ^^ st.boolAt "b" k)` for `y = ~(a ^ b)` | `e` exactly as wide as the target |
| `c ? a : b` | `if <c's bit 0> = true then <a's bit k> else <b's bit k>`, the same shape as the `if` of an `always_comb` | `c` ONE bit wide, `a` and `b` exactly as wide as the target |
| `\|v`, `&v`, `^v`, `~\|v`, `~&v`, `~^v` | `XF.any N (st.boolAt "v")`, `XF.all`, `XF.parity`, negated for the `~` forms (for a one-bit `v`, `XF.any 1 f` is `f 0`) | the target is one bit |
| `!e` | `!XF.any N …` over the bits of `e` (`!v` of a vector is true only for the all-zero vector; for one bit it is `!st.boolAt "v" 0`) | the target is one bit; `e` of any width |
| `l && r`, `l \|\| r` | `XF.any … && XF.any …`, `XF.any … \|\| XF.any …` | the target is one bit; `l` and `r` of any width |
| `l == r`, `l != r` | `XF.eqv W …`, `!XF.eqv W …` (for one-bit operands `decide (f 0 = g 0)`) | the target is one bit; `l` and `r` the same width |
| `l + r`, `l - r` | `XF.addBits W (f) W (g) k`, `XF.subBits W (f) W (g) k` over the bit functions of the operands, in the nested form the SystemVerilog has (`(a + b) + c` is `XF.addBits W (XF.addBits W …) W …`); `W` is the CONTEXT width, the carry survives up to it | every operand at most as wide as the target, a bare signal exactly (a narrower one carries slang's `Resize`, next row) |
| an operand narrower than the target of a `+ - & \| ^ ~ ?:` (slang's implicit zero extension, the `Resize` marker) | `XF.zext n (st.boolAt "a") k`: `n` bits of `a`, zeros above | around a signal access or a sized literal only |

The operands of `!`, the reductions, `&&`, `||`, `==`, `!=` and the condition of `?:` are **self-determined**:
only their own operands have to agree (`a & b` needs `a` and `b` equally wide). Everything else is
**context-determined**: as wide as the target, or (since 2026-11-01) narrower with slang's zero extension. That is the
width rule `width_k` states. Where an operand is NARROWER than its context slang inserts a zero-extension
(`~a` into a wider target extends `a` first): around a signal access or a sized literal the tactics model it
(`XF.zext`, the `width_k` goal is then `n ≤ target`); around an operation (`!s` into a vector, a truncated sum
`y3 = a + b` with 4-bit operands) they refuse the design with the message `width conversion of something other
than a signal access or a sized literal (…)`. The operands of the self-determined operators stay v1: no `+`, `-`
and no marker inside a comparison, a reduction, `!`, `&&`, `||` or a `?:` condition (write the sum into a signal).

**The four-state contract these equations rely on.** A procedural `if` with an `x`/`z` condition takes the ELSE
branch; the conditional expression with an `x`/`z` condition MERGES the two arms bit by bit (equal known bits
survive, every other bit is `x`); `!` is not `~` (`!2'b1x = 0`, `!2'b0x = x`, `~2'b0x = 2'b1x`). The
equations above are all stated for KNOWN conditions: in a settled state with known inputs every supported read
is known (`CombKnown.reads_known`), so the condition of a `?:` or an `if` is `0` or `1` and the two rules
coincide with the Boolean `if`. When a condition can be `x` nothing is stated. The rows
`wpg_if_x`, `wpg_tern_x`, `wpg_not`, `wpg_tern_ctx`, `wpg_red` and `wpg_logic` pin the model against Xcelium
24.03 (`harness/sv/xcelium_golden.json`).

**Proof recipe.** The mux adder `Examples/system-verilog/comb_ops/add_mux.sv` and its proof
(`comb_proof.lean`) are `ripple_add`'s with one different lemma: `sv_equations` hands out

```
eq_e_1 : ∀ i, i < N → st.boolAt "e" i = !(st.boolAt "a" i ^^ st.boolAt "b" i)
eq_c_2 : ∀ i, i < N → st.boolAt "c" (i + 1) = if st.boolAt "e" i = true then st.boolAt "a" i else st.boolAt "c" i
eq_s_1 : ∀ i, i < N → st.boolAt "s" i = !(st.boolAt "e" i ^^ st.boolAt "c" i)
```

and `mux_final` rewrites them to `CombLib.AddView` with a case split on three Booleans (`cases a <;> cases b
<;> cases c <;> decide`). `tasks/add/reference/add_mux.lean` is the same proof for the `add` task (a registered reference: accepted by
`check.py`, 112.0 GE and depth 33 at N = 16, the score of `add_n.sv`, because the canonical flow maps the `?:`
carry to the same netlist). Its rank has to separate the THREE cells of a bit, `rippleRank … (fun _ p i => 3 * i.toNat +
p + 1)` (`e[i]` before the carry cell, which reads it, before the sum), where `add_n`'s two cells share the rank `i + 1`.

**Refused with a message** (`Examples/system-verilog/comb_ops/comb_errors.lean` and
`Examples/system-verilog/comb_word/comb_errors.lean` pin them): `a * b`, shifts and unary minus (word-level
operators that are not in the fragment yet), `'0` or a concatenation inside an operator or an arm (write a sized
literal). **Accepted, then false:** a multi-bit condition
`v ? a : b` leaves the goal `width_k` with a false statement; write `|v ? a : b`.

## 15. A plain `case`: look-up tables

**What is accepted.** In an `always_comb` (alone, or inside a `begin … end`, or as a branch of an `if` tree): a
PLAIN `case (subject)` with a `default`, whose items are lists of KNOWN SIZED LITERALS as wide as the subject
(`8'd5:`, `2'd0, 2'd3:`) and whose arms are SINGLE ASSIGNMENTS of the one target, `y = v;` (the value is a
right-hand side of the fragment of section 14, the same at every arm). The subject is an expression of the
fragment (an access, a gate tree, ...) read once. `unique`/`priority`/`inside`, `casez`/`casex`, a missing
`default`, unsized or computed items, `x`/`z` bits in an item, arms in `begin … end` or holding an `if`/`case`,
and arms that write different windows are refused, each with its own message (table in section 4;
`Examples/system-verilog/comb_case/comb_errors.lean` pins them). The first item that matches wins: a repeated
pattern is kept and never reached.

**How `sv_equations` states it: a fold, not a chain of `if`s.** The one place where the printed shape of a
procedural statement is not the statement's own: an `if` prints as an `if`, a `?:` as an `if` (section 14), but a
`case` prints as ONE call of `XF.caseSel`,

```
eq_y_1 : ∀ k < 8, st.boolAt "y" k =
  XF.caseSel 8 (fun x => st.boolAt "x" x)
    [([{ bits := #[Logic.l0, Logic.l0, …] }.boolAt], fun x => { bits := #[Logic.l1, Logic.l1, …] }.boolAt x), …]
    (fun x => { bits := #[…] }.boolAt x) k
```

`XF.caseSel w subject items default k` is bit `k` of the first item one of whose patterns equals the subject at
width `w` (`XF.eqv`), else of the default; `XF.caseSel_cons` unfolds one item, `simp [XF.caseSel]` all of them.
The reason is size: 256 nested `if`s are 700 printed lines and, evaluated bit by bit over the inputs, a kernel
`decide` of minutes and gigabytes (measured: 128 s and 6 GB for the 256 inputs of the S-box table; with `XF.val`
comparisons 12 s and 3.8 GB); one list stays one list.

**The bridge to numbers (`LeanModels/Sv/CombProcEq.lean`, section "A `case` over a table of literals").**
`XF.caseSel_table` says the fold over `tbl.map fun e => ([e.1.boolAt], e.2.boolAt)` (`tbl : List (LVec × LVec)`,
every pattern as wide as the subject) is bit `k` of `XF.lookupNat (XF.tblNat tbl) d.nat (XF.val xf w)`, a lookup in
the table of NUMBERS; `XF.caseSel_bv` reads the inputs as the bits of a `BitVec w`; `XF.caseSel_out` goes from
the equation `hy` of the target to `lookup st y = some (LVec.ofBitVec (f x))`. The one fact they ask for is a
closed `decide +kernel` (`hf`): the lookup in the table of numbers is `f` on every input. The statement of the
equation is matched against `tbl.map …` by unification (`exact`/`eq_y_1`), the list written once by the player
(a generator, for 256 items). This was the route of `tasks/aes_sbox/reference/sbox_table.lean` until
2026-11-03 (generated from `reference/sbox_table.sv`: structure, ports, equations, one 256-input kernel
evaluation, 4 s). The reference is now one line, `theorem solution : Goal := by sv_exhaustive`
(`LeanModels/Sv/CombExhaustiveTactic.lean`): the design is read through its lowering
(`CombTask.satisfiedAt_of_lowered`, `hnq` by `NoQ.sem_noQ`), the `case` of an access over literals is compiled
once into a word-level table lookup (one bitmap per output bit, built in one pass over the table, so the kernel
never scans the table per input), and the 256 inputs are decided by kernel evaluation, as their own auxiliary
theorem. Three cold `check.py` runs, `solution` stage 26.1, 25.0 and 24.7 s (load average 8 to 11); 278 M
heartbeats sequentially. A wrong entry fails with the first input and output bit where it differs. The small version with the
statement `lut_settles` is `Examples/system-verilog/comb_case/comb_proof.lean`.

**Measured** (the `case` of 16, 64, 256 items on an 8-bit subject, one Lean process, default heartbeats; the
`sv_structure` and `sv_equations` of the S-box table together): 4, 5 and 12.4 CPU seconds, about 1.3 GB; the
equation tactic itself needs between 160 M and 200 M heartbeats at 256 items (the default limit is 200 M: close,
and linear in the items). The `solution` stage of `check.py` on the S-box table reference: 31.6 s (shared machine);
`comparator` 17 s, `leanchecker` 34 s. A proxy (the same table as a 256-deep `else if` chain of `==`) costs the
same CPU time but 255 more reads of the subject.

**Not in this step.** Arms that are trees (an `if` or a `case` inside an arm: a follow-up, see section 16), several windows per
body and temporaries (section 18); unsized items; `inside`/`casez`/`casex`/`unique`. Default-then-override is section 16.

## 16. Default-then-override: several statements, one window

**What is accepted.** An `always_comb` body (or the body of an `if` branch in `begin … end`) with SEVERAL
statements that all write the SAME window: a first statement that is a tree (it assigns the window on every path:
an assignment, an `if/else` tree, a `case` of section 15, a block), then any number of OVERRIDES `if (c) tree;`
WITHOUT `else`, whose branch is a tree that again assigns the window on every path (an assignment, an `if/else`,
a `begin … end` holding a default and overrides of its own). The last write wins:

```
always_comb begin
  c[i+1] = a[i];             // the default
  if (p[i]) c[i+1] = c[i];   // the override
end
```

lowers to the assign `c[i+1] = p[i] ? c[i] : a[i]` (`PTree.ovr c a b` has the lowering of `ite c a b`: the `if`
guard on a KNOWN bit, section 13); `sv_equations` prints the same `if st.boolAt "p" i = true then … else …` as for
the `if/else` form, and a chain of overrides prints as a nested choice with the LAST override outermost.
`Examples/system-verilog/comb_ovr` has the adder cell (`add_ovr.sv`: the netlist and the equations of
`comb_proc/add_proc.sv`), a priority encoder (`prio_enc.sv`, proved in `comb_proof.lean`), and the refusals.

**What the tactics see.** The site lists its reads in SOURCE order (the statements before the `if`, then its
condition, then its branch): `g_bit#1[i] : drives c[i + 1]   reads [a[i], p[i], c[i]]`. The rank obligation is
the same as for any site. Nothing else changes for the player: `sv_structure`, `sv_interface`, `sv_equations`.

**What is NOT accepted** (each with its own message, section 4; `comb_ovr/comb_errors.lean` pins them):
a read of the written window after it is written (`y = a; if (e) y = y ^ b;` — substituting the earlier value, "SSA",
is not modelled: the summary's `noSelfRead` obligation orders writers before readers ACROSS sites and cannot
tell a read of the path value from a read of the signal, so supporting it is a summary change); a second
unconditional assignment; an `if … else` after the first statement (and so an `else if` chain WITHOUT a final
`else` after a default: add the `else`); a second window (section 18); a `case` whose arms are trees (a follow-up: the
arms of `PTree.cases` are leaves, and tree arms need an induction principle for the nested arm lists).

**Why the proof layer needed little.** The new node differs from `ite` only in its STATEMENT: the lowered
expression, its reads, widths and Boolean reading are `ite`'s, so every lemma about the expression is the old
arm. What is new is the symbolic execution of the later statements against a NON-EMPTY state (the window written
by the earlier ones): `symSubst_apart` shows a read that overlaps nothing of the window and is not empty is
unchanged by that state (a zero-width slice at the edge of a window is "covered" by it, which is why
`PTree.noRead` now asks `ReadWin.apart`, not only `overlaps = false`; `acc_rd_pos`, from the geometry of the
summary, supplies it); `write_single` and `join_single` give the single window back; the self-read guard walks
the statement list (`listCombViol_append`). Existing pins that changed: `drvWins_tree` gains `Quot.sound`.

## 17. `+` and `-`: word-level arithmetic

An `assign` right-hand side may add and subtract. Nothing else changes in the proof: `sv_structure` reads the
operands like any other (a bare signal and a signal under slang's zero extension are both reads), and
`sv_equations` states the value of the sum over the BIT FUNCTIONS of the operands, in the nested form of the
SystemVerilog (principle 10: no normalization, `(a + b) + c` stays `(a + b) + c`). For
`Examples/system-verilog/comb_word/addw.sv` (`logic [N:0] t; assign t = a + b + cin; assign s = t[N-1:0]; assign
cout = t[N];`) the tactic returns, verbatim (`W` is the width of an `[N-1:0]` signal, `(↑N + -1).natAbs + 1`):

```
eq_t_1 : ∀ k, k < N + 1 → st.boolAt "t" k =
  XF.addBits (N + 1) (fun x => XF.addBits (N + 1) (fun x => XF.zext W (fun k => st.boolAt "a" k) x) (N + 1)
    (fun x => XF.zext W (fun k => st.boolAt "b" k) x) x) (N + 1) (fun x => XF.zext 1 (fun k => st.boolAt "cin" k) x) k
eq_s_1 : ∀ k, k < W → st.boolAt "s" k = st.boolAt "t" k
eq_cout_1 : st.boolAt "cout" 0 = st.boolAt "t" N
```

`XF.addBits w f w g k` is bit `k` of `val f w + val g w` (the carry survives up to the CONTEXT width `w`),
`XF.subBits w f w g k` of `val f w + (2^w - val g w)` (modulo `2^w`), and `XF.zext n f` is `f` below `n` and `false`
above: the zero extension slang puts around an operand narrower than the context. The context width is the
width of the TARGET (for a nested sum: of the whole expression), not of the operands: `a + b` into `N + 1` bits
keeps the carry, into `N` bits wraps.

| you write | `width_k` (false otherwise) |
|---|---|
| `y = a + b`, all `N` bits | nothing new: operands exactly as wide as the target |
| `y = a + b`, `y` wider | each operand at most as wide as the target (slang's marker is the zero extension) |
| `t = a + b + cin` | the same at every `+`; `cin` is extended from 1 bit |
| `y = a - b`, `y` wider | the same; the operands are zero-extended (NOT sign-extended), `d[N]` is the borrow |

**Proof recipe** (`Examples/system-verilog/comb_word/comb_proof.lean`; no carry induction, no case split, a
symbolic width): the glue module `LeanModels/Sv/CombWord.lean` turns the equation into `BitVec` arithmetic:

```
XF.bv_addBits : (∀ k < w, g k = XF.addBits w f w f' k) → XF.bv w g = XF.bv w f + XF.bv w f'
XF.bv_subBits : (∀ k < w, g k = XF.subBits w f w f' k) → XF.bv w g = XF.bv w f - XF.bv w f'
XF.bv_zext    : n ≤ m → XF.bv m (XF.zext n f) = (XF.bv n f).setWidth m
```

and `SvState.lookup_eq_ofBitVec_bv` / `SvState.boolAt_ofBitVec` read the ports. `add_same_final` is four lines;
`addw_final` forms the `(N+1)`-bit sum once and reads `s` and `cout` off it with `cadd_low` / `cadd_carry`
(`Comb2ConcatExample`, proved for every `N`).

**Refused with a message** (`Examples/system-verilog/comb_word/comb_errors.lean` pins them verbatim):
a product neither of whose factors is a signal access (`(a + b) * (a - b)`); a shift whose left operand is an operation or whose amount is an expression (write it into a signal first); a width conversion around a concatenation or a nested conversion; `+`/`-`, a comparison or a
conversion under `!`, a reduction, `&&`, `||`, a comparison operand or a `?:` condition (write the value into a
signal first). A bare signal narrower than the target, or a marker wider than it, leaves a FALSE `width_k`
goal.

**Comparisons, truncation and unsized constants** (2026-11-01). The six comparisons `== != < <= > >=` are read
at the context-determined positions; the result is ONE bit and the operands are context-determined at the WIDER of their
own widths (a narrower operand is zero-extended, the carry of nothing is lost: `a < c` with `a` 4 and `c` 8 bits is
compared at 8). `Examples/system-verilog/comb_word/cmp_same.sv` prints

```
eq_lt_plain_2 : st.boolAt "lt" 0 = decide (XF.val (fun x => st.boolAt "a" x) W < XF.val (fun x => st.boolAt "b" x) W)
eq_eq_plain_0 : st.boolAt "eq" 0 = XF.eqv W (fun x => st.boolAt "a" x) fun x => st.boolAt "b" x
```

(`W = (↑N + -1).natAbs + 1`) and `LeanModels/Sv/CombWord.lean` turns the first into `BitVec` `<` (`XF.lt_bv`,
`XF.le_bv`; the proof is `cmp_same_final`, the whole `⊨₂` theorem `cmp_same_correct`). An UNSIZED constant is 32 bits
wide on its own, materialized at the context width: `a == 3` compares at `max W 32` (`XF.constBit 3 (max W 32)`),
`a + 1` is a 32-bit sum truncated to the target. A conversion around an OPERATION is a truncation (a sum into a
narrower target) or the zero extension of a result that does not follow the context (a comparison into a vector):
the printed equation carries the single `if` of `instExpr2` (`if w < tw then <the operation at tw> else
XF.zext w <the operation at w>`, for an operation that follows a wider context; the second arm only for one that does
not). `trunc_inc_y1_final` closes `y1 = a + 1` for every `N` with `XF.bv_zext_trunc`, `XF.bv_constBit` and
`setWidth_add_const`. The `width_k` obligations gain a goal per marker around an operation (the operand's contract at
the width it is lowered at) and, under `+`/`-`/`~`/`?:`, the rigid-width one (`(↑N + -1).natAbs + 1 ≤ tw`).

**Concatenations as operands** (2026-11-01). A concatenation `{hi, lo}` of literals and signal accesses is read at the
context-determined positions, wherever `rdsOfW?` reads an operand (the operands of `+ - & | ^` and of the six comparisons, the
arms of `?:`, under a `~`, under a `Resize` marker; the shape theorem is one arm, generic in the operator, and
`cat_add` exercises `+`, `?:`, `==` and the marker), while the self-determined positions (the operands of `&&`, `||`, `!`, the
reductions and the condition of `?:`) keep the v1 fragment. It is the same skeleton node as a whole-right-hand-side concatenation (`Sk.cat`), so no new vocabulary
appears. `Examples/system-verilog/comb_word/cat_add.sv` prints

```
eq_s_plain_0 : … st.boolAt "s" k = XF.addBits (N + 1) (fun x => XF.addBits (N + 1)
    (fun x => if x < W then st.boolAt "a" x else false) (N + 1) (fun x => if x < W then st.boolAt "b" x else false) x)
    (N + 1) (fun x => XF.zext 1 (fun k => st.boolAt "cin" k) x) k
```

(`W = (↑N + -1).natAbs + 1`; `{1'b0, a}` is the bit function `if j < W then a j else false`, a bare concatenation as wide as the
sum; `{b, 1'b0}` under a marker is `XF.zext (W + 1) (fun x => if x = 0 then false else st.boolAt "b" (x - 1))`). The glue is
plain Lean in `LeanModels/Sv/CombWord.lean`: `XF.bv_pad` (a zero pad above is `BitVec.setWidth`) and `XF.bv_cat2`
(`{hi, lo}` is `hi ++ lo`); a single-bit literal below or above is `BitVec.concat` / `BitVec.cons`
(`bv_concat_false`, `bv_cons_true` in `comb_proof.lean`), a multi-bit literal part prints as `LVec.boolAt` of the literal and
is closed by a one-line lemma (`boolAt_zero2`); its width obligation shows `{ bits := … }.width` (a one-bit `1'b0` is already a number), and `simp [LVec.width]` followed by `omega` closes it. `cat_add_correct` is, for every `N ≥ 1`, `s = x.setWidth (N+1) + y.setWidth (N+1)
+ …`, `t = x.setWidth (N+2) + (y.concat false).setWidth (N+2)`, `w = if ci then x.concat false else BitVec.cons true x` and
`e = decide (x ++ y = y ++ x)`. The obligations are the widths of the parts (every bare concatenation as wide as its context,
`width_k`) and, under a marker, that it does not truncate. **Not in the fragment:** a concatenation as the LEFT operand of a
shift (the amount and the left operand of a shift are a signal access, a literal or an unsized constant), and a part that is
not a literal or one signal access.

**Whole rows of a two-dimensional array and constant part selects** (2026-11-01). The extractor has two encodings of a
select of a declared signal; the symbolic one (`ArraySel`) was read since the stage-2 work, the LEGACY one (`BitSel`,
`PartSel`) was not for these two shapes. (1) `r[i + 1]` over a zero-based two-dimensional declaration `logic [R-1:0][C-1:0] r`
is a whole ROW of `C` bits, whatever the dimensions are made of (literals, localparams, parameters: `r[0]` and `r[3]` over
LITERAL dimensions are the legacy encoding too). It is read and written, in an `assign` and in an `always_comb` leaf, as the
same access the `ArraySel` form of a row had, so a loop-indexed chain of rows is an ordinary family:
`Examples/system-verilog/comb_word/row_chain.sv` (`r[0] = x`, `r[i + 1] = ~r[i]`, `y = r[N]`) prints

```
eq_r_g_0 : ∀ i, i < N → ∀ k, k < N → st.boolAt "r" (rmN ↑N (↑i + 1) 0 + k) = !st.boolAt "r" (rmN ↑N ↑i 0 + k)
```

(the row-major offset `rmN W r c` of section 2.3; the stride `W` is the printed row width: `↑N`, `2 * ↑N` for rows of `2N`
bits over localparams, `3` over literals). The structure goals close with `intros; sv_rowmajor; omega`, and the two
coverage goals of the chain (`cover_1`: row `N` is written by iteration `N - 1`; `cover_2`: row `i` by the plain site for
`i = 0`, else by iteration `i - 1`) are closed by naming the writer, as in `mul_array` (`row_chain_correct`,
`row_chain_lp_correct`, `row_chain_lit_correct`: `y = x` for an even number of rows, `~~~x` for an odd one, ONE induction
over the rows, `row_chain_gen`). (2) `x[hi:lo]` over a zero-based one-dimensional declaration is a window at `lo`, read as
a field, as a part of a concatenation, under a `Resize` marker or as a shift operand, and written as a target; the bounds
are literals OR affine in the genvars and parameters (`y[4*i+3:4*i] = ~x[4*i+3:4*i]` in a loop). `ps_rot.sv`
(`{x[8:0], x[15:9]}` is `x.rotateLeft 7`, the byte swap by two part-select targets is `x.rotateLeft 8`, the field
`x[14:10]` is `x.extractLsb' 10 5`) and `ps_gen.sv` are proved for the 16-bit word and for every `N ≥ 1`. **Refused:** a
part select of a base that is not a zero-based one-dimensional declaration (`logic [8:1] v; … v[4:2]`: `part selects need a
zero-based descending dimension [hi:0]`), a row select of a two-dimensional declaration whose first range is not zero-based,
a declaration of three packed dimensions, an indexed part select `x[i +: w]`.

**Replication `{N{x}}`** (2026-11-02). A replication of a SIZED LITERAL or of ONE bit select or part select, with a count that
is affine in the parameters and genvars, is read as a part of a concatenation or as a whole right-hand side in an `assign`
(`Sk.rep`; slang writes the braces of `{K{1'b0}}` as a one-part concatenation, which the recognizer reads through). The count is a
constant of the instance, like a genvar shift amount: the structural stage checks its names are parameters or enclosing loop
variables, and its non-negativity is a new guarded conjunct of the in-range obligation (`0 ≤ ↑K`; for a parameter count the
tactic closes it, so nothing is left). `Examples/system-verilog/comb_word/repl_pad.sv` (`y = { {K{1'b0}}, x }`) prints

```
eq_y_plain_0 : ∀ k, k < (↑N + ↑K + -1).natAbs + 1 → st.boolAt "y" k = if k < (↑N + -1).natAbs + 1 then st.boolAt "x" k else false
```

(the literal part is the high part: its positions are the `false` branch; `[width] ⊢ K + (…) = …` is left for `omega`) and
`repl_mask.sv` (`pp[i] = a & {N{b[i]}}`) prints `st.boolAt "pp" (rmN ↑N ↑i 0 + k) = (st.boolAt "a" k && st.boolAt "b" (i + k % 1))`: bit
`i` of `b` read at every position (`k % 1`, the width of the replicated bit). The glue is core's `BitVec.getLsbD_replicate` and
`getLsbD_setWidth`: `repl_pad_correct` is `y = x.setWidth (N + K)` for every `N ≥ 1` and every `K` (`K = 0` is the empty replication),
`repl_mask_correct` is, for every `N ≥ 1`, row `i` of `pp` is `if b.getLsbD i then a else 0#N`, bit by bit and known, and
`repl_bits_correct` is `y = BitVec.replicate 4 (x.extractLsb' 0 2)` for the literal count of `{4{x[1:0]}}`. **Not read:** a replication
of a WHOLE signal (`{2{a}}`: its width is the declared one, which the part does not carry: replicate a bit or a part select), of
an operation or of a concatenation of several parts (`{2{a & b}}`, `{2{a[0], b[1]}}`: write it into a signal first), a count that is
not affine (`{N*M{a[0]}}`), a replication in a self-determined position (`|{4{a[0]}}`) or in an `always_comb` leaf (the procedural chain
does not carry the scope of a constant). Measured on the clmul styles of `tests/clmul/attacks`: see `design/word-level/G26-NOTE.md`, section 14b,
for the first wall of each after this extension.

**A genvar as the amount of a shift** (2026-11-01). In a generate loop `a << i` shifts by the loop variable: the amount is
a CONSTANT of the instance, lowered like an unsized constant (32 bits, never widening the result) to the literal of the
genvar's value. `Examples/system-verilog/comb_word/shl_gen.sv` (`pp[i] = aw << i`, rows `2N` wide) prints

```
eq_pp_g_0 : ∀ i, i < N → ∀ k, k < (2 * ↑N).toNat → st.boolAt "pp" (rmN (2 * ↑N) ↑i 0 + k) =
    XF.shlBits (XF.zext W fun x => st.boolAt "aw" x) 32 (fun x => XF.constBit ↑i 32 x) k
```

(`W = (2 * ↑N + -1).natAbs + 1`; the same form `shl_const` has, with `↑i` in place of the number), and the glue is the one of
`shl_const` (`XF.bv_shlBits`, `XF.bv_constBit`) plus `toNat_ofInt32_nat` (the literal of `i < 2^32` reads back as `i`):
`shl_gen_correct` is, for every `N ≥ 1`, row `i` of `pp` is `x <<< i`, bit by bit, with the one side condition `N ≤ 2^32`
(the amount is 32 bits wide, so a genvar of `2^32` or more wraps; the printed equation is exact either way, the condition only
lets the BitVec statement be the whole story). The genvar must be an enclosing loop variable of the site: the structural
obligation checks it with the indices of the accesses (a genvar of another loop, or one the loop does not bind, is the
message `an index or a shift amount mentions …, which is neither a parameter nor an enclosing loop variable`). **Not read:** an amount that is an
expression over a genvar or a parameter (`a << (i + 1)`, `a << (N - 1)`: not planned yet), a parameter or localparam as the amount
(`a << N`: its width is a fact about the parameter's declared type, which the summary does not carry), and a genvar amount
inside an `always_comb` leaf (the procedural chain refuses a constant of the instance: write the shift into an `assign`).
Measured when the genvar amount was added, on the clmul styles of `tests/clmul/attacks` (the designs that use it; the first wall of each; the replication, above, is read since 2026-11-02):
`gen_word_pp_chain` (`pp[i] = b[i] ? (aw << i) : '0`), `gen_mask_replication` and `gen_always_step` stop on the
REPLICATION (`{{(N-1){1'b0}}, a}`, `{(2*N-1){b[i]}}`; read since 2026-11-02); `gen_size_cast` stops on the size cast `(2*N-1)'(a)` as the LEFT operand of the shift;
`gen_pp_zerofill` stops on its generate-for header `for (i = N; …)` (the start must be an integer literal). Behind those walls,
by reading the sources: the fill `'0` as an arm of `?:` (`gen_word_pp_chain`, `gen_pp_zerofill`), a compound `^=` over a row
(`gen_always_step`).

**Run-time shifts** (2026-11-01). `y = a << s` and `y = a >> s` with a RUN-TIME amount are read at the
context-determined positions. The left operand is context-determined (it is extended to the context BEFORE the shift,
`XF.zext W …`: a shift into a wider target keeps the bits shifted out of the operand), the amount is self-determined and
unsigned and never widens the result, and the result is truncated to the context. `Examples/system-verilog/comb_word/shl_n.sv`
(`output [N-1:0] y = a << s`, `s : [2:0]`) prints

```
eq_y_plain_0 : ∀ k, k < (↑N + -1).natAbs + 1 → st.boolAt "y" k =
  XF.shlBits (XF.zext ((↑N + -1).natAbs + 1) fun x => st.boolAt "a" x) (Int.natAbs 2 + 1) (fun x => st.boolAt "s" x) k
```

(`XF.shlBits f wr g k` is bit `k` of `f` shifted left by the value of the `wr`-bit amount `g`; `XF.shrBits w f wr g k` the
logical right shift of a `w`-bit operand). `LeanModels/Sv/CombWord.lean` turns it into `BitVec` shifting, no induction:

```
XF.bv_shlBits   : bv w (XF.shlBits (XF.zext wl f) wr g) = ((bv wl f).setWidth w) <<< (bv wr g).toNat
XF.bv_shrBits   : bv w (XF.shrBits wl f wr g)           = ((bv wl f) >>> (bv wr g).toNat).setWidth w
XF.bv_shlBits_s : bv w (XF.shlBits (XF.sext wl f) wr g) = ((bv wl f).signExtend w) <<< (bv wr g).toNat
```

The amount is a natural number, so an amount of `N` or more gives `0` as in the LRM: `shl_n_correct` is
`y = x <<< sv.toNat` for every `N`, `shr_n_correct` the same with `>>>`, `shl_wide_correct` (into `N + 1` bits)
`x.setWidth (N + 1) <<< sv.toNat`. An unsized constant is a SIGNED 32-bit integer: `y = 1 << s` (`onehot.sv`) is a signed
shift, computed at `max N 32` bits with `XF.sext 32 …` (a sign extension: `Expr2.resizeSigned` is in the x-free fragment
since 2026-11-01) and truncated into the target; the printed equation carries the single `if 32 < W` of the
truncation marker (above), and `onehot_correct` states `1#N <<< sv.toNat` for every `N ≥ 1` (`signExtend_one`, `one_shl_setWidth`).
A shift by an unsized constant (`a << 1`, `a >> 2`: the amount is `XF.constBit 1 32 …`, 32 bits) is `shl_const_correct`.
No new `width_k` goal appears for a shift: both operands are read at their own widths. **In the fragment:** the left
operand is a signal access, a sized literal or an unsized constant, bare or under the marker that keeps its signedness (the
`Resize` marker of an unsigned shift, the `SignedResize` marker of a signed one); the amount is a signal access, a sized
literal or an unsized constant. **Refused with a message** (write the operand into a signal first): a left operand that
is an operation (`(a + b) << 1`), an amount that is an expression (`a << (s + 1)`) or an expression over a parameter
(`a << (N - 1)`: the first candidate for a later extension), `<<<`, `>>>` and a signed `>>`.

**Products** (`*`, 2026-11-03). `y = a * b` is read like `+`: at the context-determined positions, each factor extended to
the CONTEXT width before the product, the product taken modulo `2^` the context width, a marker around it a truncation.
`Examples/system-verilog/comb_word/mul_word.sv` (`p = a * b` into `N` bits, `q = a * b` into `2N` bits) prints

```
eq_p_plain_0 : ∀ k, k < W → st.boolAt "p" k = XF.mulBits W (fun x => st.boolAt "a" x) W (fun x => st.boolAt "b" x) k
eq_q_plain_1 : ∀ k, k < W2 → st.boolAt "q" k =
  XF.mulBits W2 (fun x => XF.zext W (fun x => st.boolAt "a" x) x) W2 (fun x => XF.zext W (fun x => st.boolAt "b" x) x) k
```

(`W = (↑N + -1).natAbs + 1`, `W2 = (2 * ↑N + -1).natAbs + 1`; `XF.mulBits w f w g k` is bit `k` of `val f w * val g w`).
`LeanModels/Sv/CombWord.lean` has the glue and the value lemma:

```
XF.bv_mulBits  : (∀ k < w, g k = XF.mulBits w f w f' k) → XF.bv w g = XF.bv w f * XF.bv w f'
XF.val_mulBits : XF.val (fun k => XF.mulBits wa fa wb fb k) w = XF.val fa wa * XF.val fb wb % 2 ^ w
```

`mul_word_correct` (`Examples/system-verilog/comb_word/mul_proof.lean`) is `p = x * y` and
`q = x.setWidth (2 * N) * y.setWidth (2 * N)` for every `N ≥ 1`, and `mul_full` says the second is the exact product. **In the
fragment:** one factor is a signal access, bare or under slang's zero extension (the elaboration folds a product of
constants, and the tactics read `*` only where it cannot be folded); the other is any operand of the fragment. **Refused
with a message:** a product neither of whose factors is a signal access (`(a + b) * (a - b)`: write one factor into a signal
first); a signed factor narrower than the context (a `SignedResize` marker; signed declarations are outside anyway).
`Examples/system-verilog/comb_word/sq_chain.sv` squares a row per iteration of a loop bounded by a `$clog2` localparam
(`r[i + 1] = r[i] * r[i]` for `i < L`, `L = $clog2(N) + 1`); its equations carry `↑(clog2 N) + 1` as an opaque atom, and
`sq_chain_correct` (`y = x ^ (2 ^ L) mod 2 ^ N`) is one induction over the rows on `XF.val_mulBits`, with `clog2_le` for the
generate-fuel goal (section 4). The task-level example is the Newton reference of `fdivp`
(`tasks/fdivp/reference/fdivp_newton.{sv,lean}`): two products per step of a family bounded by
`NI = $clog2((P + 9) / 8) + 1`, two more after it, the family by the same induction (`newton_rows`), and a rank
certificate that puts every later site above every step with `clog2_le`.

**In an `always_comb` leaf** (2026-11-01): the leaves of an `if`/`case`/override tree read the same fragment, with
the same `width_k` contract per leaf (the target window's width is the context). `if (c) y = a + b; else y = a - b;`
into an `(N+1)`-bit `y` prints

```
eq_y_plain_0 : ∀ k, k < N + 1 → st.boolAt "y" k =
  if st.boolAt "c" 0 = true then XF.addBits (N + 1) (XF.zext W (…a…)) (N + 1) (XF.zext W (…b…)) k
  else XF.subBits (N + 1) (XF.zext W (…a…)) (N + 1) (XF.zext W (…b…)) k
```

and `Examples/system-verilog/comb_word/comb_proof.lean` proves it for every `N` (`addp_final`, `addp_settles`: the
three-line shape of the `assign` proofs, plus a case on `c`). The conditions and the subject of a `case` are
self-determined: they keep the v1 fragment (no `+` there).

**A known tight spot, and its fix.** `Examples/system-verilog/comb_ops/comb_proof.lean`'s `add_mux_correct` needed between
185 000 and 200 000 heartbeats at the default limit of 200 000 (as one declaration holding both `sv_structure` calls and
`sv_equations`), and the merge of two independent growths of the tactic vocabulary (the comparisons above, and the several windows of section 18) crossed
it. Every declaration has its own budget, so the proof is now three declarations (`add_mux_comb`, `add_mux_acyclic`,
`add_mux_settled`; the statement of `add_mux_correct` is unchanged): the largest needs between 100 000 and 140 000. The
advice stands for any proof that puts `sv_structure` and `sv_equations` in one declaration: measure it
(`lake env lean -DmaxHeartbeats=N file`) before adding names to the simp lists of the tactics.

## 18. Several windows in one body

One `always_comb` may write more than one window, for example the whole bit cell of the ripple adder:

```systemverilog
always_comb begin
  if (p[i]) c[i+1] = c[i];
  else      c[i+1] = a[i];
  s[i] = p[i] ^ c[i];
end
```

(`tasks/add/reference/add_proc_m.sv`, the same ripple adder as `add_proc.sv` with the carry cell and the sum bit in one
body.) Each window is a tree of the first fragment (sections 13, 15, 16: an `if`/`else` tree, a `case`, default-then-
override), and a new window starts at each statement that is not an override `if (c) …;` without `else`. The tactics
read the body as ONE site with further windows: `sv_structure` (the obligations count every window: in range, one driver
per bit against every other window AND within the body, no read of ANY window of the body, the rank is the site's) and
`sv_equations` (one equation and one knownness fact PER WINDOW).

**The names.** The head window of a body keeps the generated name of the single-window route
(`eq_<signal>_<block>_<position>`); window `j ≥ 1` of the same body is named after ITS signal, with the site's block and
position and `_w<j>` (`eq_s_g_bit_1_w1`). The facts come out as the heads of all sites in order, then the further
windows. **The stable aliases are the contract**: `eq_<signal>_<k>` is the equation of the `k`-th window that writes
`<signal>`, counting windows in source order, whether they are separate processes or windows of one body (`known_<signal>_<k>`
likewise). So `add_proc_m` has the aliases `eq_c_1`, `eq_p_1`, `eq_c_2`, `eq_s_1`, `eq_cout_1` with the SAME statements as
`add_proc`: **a proof written against the aliases of the split design holds for the one-body design unchanged**. The
reference proof `tasks/add/reference/add_proc_m.lean` is `add_proc.lean`'s, character for character (`tests/add/same_proof.py`
pins it; `check.py` accepts it, `--postsynth full` agrees on 4132 vectors, 112.0 GE, depth 33 at N = 16).

**The obligations.** The windows of one instance of a body must be pairwise disjoint (the obligation `within`). The
normalizer closes it when the windows are of different signals or at different literal positions (`add_proc_m`,
`multi_flat` and `multi_same` in `Examples/system-verilog/comb_multi`: no `within` goal is printed); it would leave a goal
only where disjointness depends on symbolic indices. `width_k` and `cover_k` count every window. A design with no such body
takes the single-window route, whose goals and cost are the ones of sections 13 to 16 (the multi-window route has its own
normalizer, selected only when some site has a further window). Two windows of ONE signal in one body get their aliases
from source order (`eq_y_1`, `eq_y_2` for `y[0] = …; y[1] = …;`).

**Still refused.** A read of the window the body wrote earlier (SSA: `y = a; z = y ^ b;`), temporaries, and a window
written in two separate groups of statements: the message of `sv_structure` names the site and the reason.

## 19. A clocked task: one cycle at a time, then the phases (`matmul`, `sorter`)

A clocked task with a latency (`kind` `tx-family` or `stream-family`) has no combinational fragment and no `sv_*`
tactic. Its statement (`TxTask.StatementV2` or `StreamTask.StatementV2` in `SvGolf/TaskSeq.lean`, final
since 2026-11-08, amended 2026-11-09 before any record of these tasks was published): the handshake's claims hold of
every run of the design from EVERY power-up state (every declared signal, 2-state ones included, at some 0/1 value),
under every schedule, on every known stimulus, from every reset release, under the environment's rely; every such run
terminates (`TerminatesPU`); no combinational path leads from any input port, `rst` included, to an output port
(`MooreOutDep d []`: nothing is exempt, rule 1); and no construct can create an `x` from known operands (`XSafe`,
rule 3). The proof declares the latency it claims (`Submission.lat`, and the header line
`-- svgolf-latency: n` with `n = lat` at the scoring point; at other points `lat` need only be a bound the proof
establishes, and at the points of the post-synthesis check the kernel must reduce it to a number, which the check
uses there, decided 2026-11-08). The untrusted library reduces the statement to facts about ONE clock cycle:
`TxTask.satisfiedAtV2_of_phases` and `StreamTask.satisfiedAtV2_of_phases` (`SvGolf/SeqV2.lean`), each taking the
interface, `Disciplined`, `TerminatesPU`, the latency facts (and, for a stream, that `spec` keeps the length), a **phase model** (`TxTask.PhaseModel`,
`StreamTask.PhaseModel`, `SvGolf/Seq.lean`), the proof that every power-up state has the model's shape, `MooreOutDep`
and `XSafe`. Both references follow the same five steps; the sorter's names are used here
(`tasks/sorter/reference/sorter_ins.lean`, section numbers of that file).

Nothing requires a reference's structure: any proof of `Goal lat` that the kernel accepts counts (README.md,
"Submitting"). A proof from scratch must still state what the loaded design does in one cycle and prove that it
agrees with `design.sem`. Steps 1 to 5 below are one way to do that, and starting from the nearest reference is the
shortest route today.

1. **Agreement** (§1, `so_sem_eq`): the loaded family `design.sem N W` equals a hand-built design `soD N W` at
   every in-range point. The generate loop is expanded with `expand2_genFor_ascending_processes`; at `N = 1` the
   cell family is empty and the same lemma covers it. The processes' windows are pairwise disjoint
   (`so_pairwise`), proved once, symbolically.
2. **One cycle** (§2 to §5, `so_profile`, `so_cycle`, `next_reset`, `next_run`): `soD` is in the FF-only profile
   (`so_profile`, the disjointness through `ffDisjB_of_pairwise`), so the library's clock step (`cycleStep2_profile`)
   says a cycle runs every `always_ff` body on the pre-edge state and commits the nonblocking queues. Write the
   queues per process (`topQ`, `outQ`, `cellQ`), commit them one register at a time (`nbaFold` in
   `LeanModels.Sv.NbaCommit`; `bvInsertAt_packBV`, `foldl_range_ofBitVec_packBV` in `LeanModels.Sv.SeqFamily`),
   and read each register as a function of the old one (`cell_data`, `cell_tok`). A reset that rewrites the same
   window wins because it is the later write (`LVec.foldl_range_insertAt_last`). The cycle holds from ANY state of
   the register shape (`I`: the declarations in order, the registers at their widths, any values), which is what
   rule 2 needs. A design with combinational logic proves its own settle, as the arbiter does (section 20).
3. **The invariant** (§6, §7): plain Lean over `List (BitVec W)`. A load is `tail ∘ insertAsc x` on the ascending
   cells (`hw_ins`), insertions commute (`ins_comm`), so `sortAsc (l ++ [x]) = insertAsc x (sortAsc l)`
   (`sort_snoc`) and `t` loads hold `[0]^(N-t) ++ sortAsc` of the inputs. `at_step` steps the whole state: cells
   `cv`, tokens `tokv`, `out_valid` `ovb`, `j` cycles after a start.
4. **The phases** (§8, `model`): a `StreamTask.PhaseModel` has `Ready` (here: the all-zero state) and `At ys j`
   (`j` cycles after a start, the inputs `ys` so far), a schedule `out xs j` of what the outputs show (here
   `out_valid` exactly when `N < j ≤ 2N`, carrying `(sortAsc xs)[j-N-1]`), and five one-step obligations: `reset`
   (a reset edge leads to `Ready`, from EVERY state of the shape: here a reset clears every cell and token),
   `hold` (an idle edge keeps `Ready`), `start`, `feed` (an input edge appends to `ys`) and `run` (an edge after
   the last input advances `j`). Three facts about the schedule close it: nothing is shown before the last input
   is sampled (`out_feed`), nothing after `lat` (`out_lat`), and the shown values are `spec xs` (`out_spec`). The
   reduction does the rest: the release, the horizon, `Idle`, back-to-back starts, `out_valid` = 0 before the
   first start. (`TxTask.PhaseModel` is the same idea with `Ready`, `Busy x m`, `Fin x` and `done`;
   `matmul_g1.lean`. Its `ready_done` asks `done` = 0 in `Ready`: the statement asks `done` = 0 between the
   release and the first start, as `out_valid` = 0 for the sorter.)
5. **The statement's three rules** (§9): rule 2 is `so_powerUp`, every power-up state has the shape `I`
   (`powerUp_cons` once per declaration, then `powerUp_nil`), with termination from the same cycle
   (`so_terminatesPU`, by `TerminatesPU.of_invariant` with the shape as the invariant); rule 1 is `so_moore`:
   every process is an `always_ff`, so the design has no combinational dependency at all
   (`MooreOutDep.of_noComb (combDeps_of_ffOnly (FFOnly.ofProfile so_profile))`, with a `simp` for its second
   argument, that no output port is an input port); rule 3 is `so_xsafe`, a `simp`
   over `xsafeB` and its helpers (`xsProc`, `xsStmt`, `xsWidth`, `binW`, `sigWidth`) with the window bounds
   (`rowMajor_le`) and `omega`. `solution` is one application of `StreamTask.satisfiedAtV2_of_phases`. A design
   with an `always_comb` block or a continuous `assign` proves `MooreOutDep` itself: give the set of signals the
   input ports reach along `combDeps`, every input port included (`rst` and `clk` too: nothing is exempt), which
   must contain no output port (the definition's witness), or evaluate `mooreOutDepB` (`MooreOutDep.of_check`).

**The loader's generate fuel.** `design.sem` expands each generate loop to at most `PDesign.surfaceFuel`
iterations at a point, `(s + 2)² + 64` with `s` the sum of the parameter values (`(N + W + 2)² + 64` for the sorter,
`(N + W + AccW + 2)² + 64` for matmul), per loop. A loop with more iterations makes `design.sem` the error design at
that point (no declarations, so its `Interface` is false), and no proof can hold there although the design is
correct. Write one generate loop per index and nest them (a nested loop gets the whole budget again): matmul's
`g_row`/`g_col` take `N` iterations each, the sorter's cell loop `N - 1`; one flat loop over the bits of a matmul
port (`N·N·W`) exceeds the bound at `(30, 10, 1)`, in range (MEASURED, the readiness review of 2026-11-08).

**What the attacks show.** Each design of `tests/sorter/attacks/` is the reference with one change. Seven are wrong
for some `N, W` (a token shift that reads the cell's own token, a missing `else`, the neighbour push reading the cell's own value, the
token entering with the start, a reset that leaves the cells, a top cell the drain does not clear, signed order).
Each fails at the `solution` stage, inside one of the steps above, and each of the seven is also rejected by the
clocked post-synthesis check alone (`check.py --unproved --latency 16`). The eighth, `rst_gate`
(`assign out_valid = ov_q & ~rst`), shows the reference's value in every snapshot, so the post-synthesis check
passes it; on the wire the snapshot before a reset entry is hidden during the reset cycle. Rule 1 refuses it (the
path from `rst` to `out_valid`; `rst_gate_refuted` in `tests/sorter/negative/Refute.lean`), and with the
reference's proof it fails at `solution` too, first in `so_decls` (its extra registers). A design that orders EQUAL
values differently (`>=` for `>`) is not an attack: equal values are interchangeable in the emitted list, the
statement cannot tell the two apart, and the proof's `insertAsc` only fixes where the reference puts them.

**Cost** (MEASURED 2026-11-08, line counts of `sorter_ins.lean`: 983 lines). Lines: the header 35, agreement 216,
one cycle 343 (the clock step 114, the commit 26, the registers 177, shape and termination 26), the sort 107, the
invariant 56, the phases and the statement 150, the three rules 76. Time: the `solution` stage 17.0 to 17.4 CPU s
in three cold `check.py` runs (2026-11-07, `score/time_limits.json`; the limit is 300 CPU s). Heartbeats and the
olean, measured 2026-11-04 on the 899-line v1 file (not measured again): in `maxHeartbeats` units, 123.3k for the
whole file, at most 21.1k for one declaration (`cell_run`; then `model` 14.2k, `apply_so` 9.5k), so no declaration
needs the default limit of 200k raised; the agreement and the clock step were two thirds of it (81.0k), the sort
and the invariant 7.5k; `Solution.olean` 12.9 MB, 1042 constants in the module, of which 104 written (70
theorems, 34 definitions), 739 generated equation lemmas and 199 auxiliary declarations. Axioms `propext`,
`Classical.choice`, `Quot.sound`.

### 19.1 A probe: what the loader made of your design

Step 1's hand-built design must equal the loaded one, and where the two differ, an instantiation lemma (`mm_ctrl`,
`pe_inst` in `matmul_g1.lean`; `so_static`, `cell_inst` in `sorter_ins.lean`) fails without saying where. For a
mirror of a changed control process, `mm_ctrl` printed nothing but

```
error: unsolved goals
N W AccW : Nat
⊢ False
```

Print what the loader made and compare it with your mirror. Stage the design with
`--unproved` (a task with a latency needs `--latency n` there) and compile a probe file against it, as in section 0:

```bash
python3.12 check.py tasks/matmul solution.sv --unproved --latency 4 --stage-dir stage
LEAN_PATH=stage/build lake env lean Probe.lean
```

```lean
import Submission.Design
open LeanModels.Sv
#eval (Submission.design.sem 2 3 5).processes.toList.take 1   -- the first process, at N = 2, W = 3, AccW = 5
```

`design` is `Submission.design`: without the prefix, or the `namespace Submission` of section 0's probe, Lean
answers ``Unknown identifier `design.sem` ``. Small parameter values keep the printout short; `.drop k` before
`.take 1` shows process `k`. The module's own processes come first, in source order, then those of the generate
loops (`sorter_ins.sv` writes its cell loop first, and `soD` lists `topP`, `outP`, then the cells). For a variant of
`matmul_g1.sv` whose control ends in `else if (busy) begin if (k == N - 1) begin … end end`, the probe printed
(2026-11-10; abridged):

```
(some (LeanModels.Sv.Stmt2.ifStmt
   (LeanModels.Sv.Expr2.ident "busy")
   (LeanModels.Sv.Stmt2.block
     #[LeanModels.Sv.Stmt2.ifStmt
         (LeanModels.Sv.Expr2.binary
           (LeanModels.Sv.BinOp.eq)
           (LeanModels.Sv.Expr2.ident "k")
...
```

The `begin … end` around the one `if` is a block of one statement, and a mirror that wrote that `if` bare was the
`⊢ False` above. What the loader writes, and so what the mirror must write (each from a proof the kernel accepted:
the references, unless another proof is named):

* `begin … end` is `.block #[…]`, also around one statement: in `topP`,
  `if (in_valid) begin if (…) … end else …` is `.ifStmt (.ident "in_valid") (.block #[.ifStmt …]) (some …)`.
  A statement without one stays bare: in `outP`,
  `if (rst) out_valid <= 1'b0;` is `.ifStmt (.ident "rst") (.nbaAssign …) none`, and `mmPE`, an `always_ff` whose
  body is one `if`, is `.alwaysFF "clk" (.ifStmt …)`. An `else if` is an `.ifStmt` in the `some` of the outer one.
* An operand or a right-hand side whose width is not its context's gets `Expr2.resize w`: in `mmPE`,
  `C[…] <= C[…] + {…} * {…}` is
  `.resize AccW (.binary .add (.resize (AccW + W) (.slice (.ident "C") …)) (.binary .mul …))`, the `AccW`-bit
  window widened to the expression's `AccW + W` bits and the sum cut back to `AccW`. In an
  accepted variant whose `a_sh` has `(N*N+3)*W` bits, `a_sh <= A` is
  `.nbaAssign (.ident "a_sh") (.resize ((N * N + 3) * W) (.ident "A"))`. `k <= k + 32'd1`, all 32 bits, has none.
* A parameter (the tasks' are `int`) or an unsized number in an expression is a 32-bit constant, `c32 v`
  (`.lit (LVec.ofInt 32 v)`): `a_sh >> W` is `.binary (.shr false) (.ident "a_sh") (c32 W)` and `k == N - 1` is
  `.binary .eq (.ident "k") (.binary .sub (c32 N) (c32 1))`; the probe above prints `W = 3` as a 32-bit literal.
* How a constant is spelled is free as long as it evaluates to the same bits: the loader's 1-bit zero is
  `⟨#[.l0]⟩`, which `mmCtrl` writes, and `outP` writes `zW 1`.

### 19.2 What changes when you change a reference

Measured on accepted variants of the two references (2026-11-10), declaration by declaration: a declaration counts
as changed when its text differs, a name added to a `simp` list included; lines are those `diff` removes plus those
it adds. The names are the references'; a row "on the row above" (or "against the four-step proof") is measured
against that proof. The variants' proofs are records on the board: `61bf6f8d17f7` (the sorter's cell rule),
`1ffe71156e90` (the k loop), `abdd0afdf025` (two steps), `9fdf50f9ae02` (the accumulators free-running) and
`263ce18b31ab` (the product register). The variant of the row "the operand registers and `k` free-running" is not on
the board; against the reference, `9fdf50f9ae02` (that row's change and the next row's together) changes 13 of the 86
declarations and adds 5, in 242 lines.

| the change | what changed in the proof | new declarations | lines |
|---|---|---|--:|
| `sorter_ins`, **the cell rule**: the cells' and the top cell's conditions rewritten (`d < in_data` for `in_data > d`, the input test first), latency `2N` kept | the mirror `cellP`, `topP`, their queues `cellQ`, `topQ` and runs `cell_run`, `top_run`; `gtc`, `gtc_ofBitVec` gone for `<` forms; in a `simp` list only, `so_simp`, `cell_data`, `so_disciplined`, `so_xsafe`. Unchanged: 95 of 107, the sort, the invariant, `model`, `so_moore` and `so_powerUp` among them | 16: the two conditions as `@[irreducible]` definitions with their evaluation lemmas (19.3), the 4-state `<`, `!`, `&&`, `||` as functions, the conditions' values and their values on known bits | 119 |
| `sorter_ins`, **the output stage, the latency, the token line** | no accepted proof has changed them yet. In the reference: the output register is `outP` (`outQ`, `out_run`); `lat` is `2 * N`, and `2 * N` is written into the schedules `ovb` (`out_valid`, `j` cycles after a start) and `tokv` (the tokens), which `at_step` steps and `model` uses (`out_lat`, with `zero_done`); the token line is `tstep`, `cell_tok`, `top_tok`, `tok_fold`, `tok_step`; `solution` passes `N ≤ lat` | | |
| `matmul_g1`, **the k loop**: four multiply-accumulates per PE per cycle, `k` stepping by 4, the operand registers padded by three entries and three rows, `lat = (N + 3) / 4` | `lat` and `solution` (its `1 ≤ lat`: the reference passes `hN`, its `lat` being `N`); the mirror `mmPE`, `mmCtrl`, `mmDecls`, `mmD`, `mmE` and, for the new widths, `mm_decls`, `pe_inst`, `mm_instantiate2`, `mm_init`, `Wd`, `pe_xsafe`; the queues and runs `ctrlQ`, `peV`, `ctrl_run`, `pe_run`; the steps `pe_step`, `ctrl_busy`, `next_step`, `next_start`, `mmNext_I`; the phase `BusyAt` and `model`; in a `simp` list only, `pe_simp`, `mm_noq`, `mm_disciplined`, `ctrl_xsafe`. 28 of 86 | 22: the padded operands, the shift amounts and windows, the four-product term, the four-step sum and their `BitVec` facts | 468 |
| `matmul_g1`, the same design at **two** steps per cycle (against the four-step proof) | the four products cut to two, the padding to one entry and one row: 26 declarations | 3 (5 gone) | 282 |
| `matmul_g1`, **the operand registers and `k` free-running**: loaded on `start`, stepped in every cycle that is not a start, no hold enable, `k` not reset | `mmCtrl`, `ctrlQ` (now the free-running writes, then `busy` and `done`), `next_idle`, `next_reset` (they now give `k`, `a_sh`, `b_sh` as some value), `model`; in a `simp` list only (a lemma for the appended queue: `List.cons_append`, `commitNba2_append`), `ctrl_busy`, `mmNext_I`, `next_start`. 8 of 86 | none | 133 |
| `matmul_g1`, **the accumulators free-running** (on the row above): `C` adds the operands' product in every cycle that is not a start, and holds once `b_sh` is shifted out | `mmPE`, `peQ`, `pe_step`, `next_step`, `next_idle`, `FinAt` (a finished state is now any `t ≥ N` cycles on), `model` | 5: past `N` steps the partial sums do not change, the control's idle and running steps | 157 |
| `matmul_g1`, **a product register per PE** (on the row above): `P <= a * b`, `C <= C + P`, `lat = N + 1` | the state `MS` gains a twelfth signal, and every declaration that names it changes: 44 of 91, among them `apply_mm`, the commits `nb_*`, `mmNext`, `mm_cycle`, `ctrlQ`, `peQ`, `Wd`, `I`, `mm_init`, `MS_inj`, `BusyAt`, `FinAt`, `Stp`, `model`, `mm_powerUp`, `lat` and `solution`; gone: `peV`, `commit_C`, `rowMajor_map`, `commit_map`, `peQ_C` | 13: the registered products and their sums, the commit of `C` and `P` together, `BitVec` and list facts | 560 |

No matmul row changed the agreement's frame (`mm_sem_eq`, `mm_processes`, `mm_gens`, `mm_pairwise`, `mm_driversOk`,
and `mm_ctrl`, whose text names `mmCtrl` only), `mm_profile`, the spec's arithmetic (`psum`, `accC`, `psum_succ`,
`product_eq`, `accC_N`), `mm_moore` or `mm_xsafe`, and every matmul row changed the mirror (step 1), a queue (step 2)
and `model` (step 4); a new register reaches every lemma that spells out the state. The sorter's cell rule changed
steps 1 and 2 only, apart from the two new definitions' names in the `simp` lists of `so_disciplined` and
`so_xsafe`.

### 19.3 Pitfalls

* **`⊢ False` from an instantiation lemma**: your mirror differs from the loaded process (19.1).
* **The latency fact.** `TxTask.satisfiedAtV2_of_phases` takes `1 ≤ lat`, `StreamTask.satisfiedAtV2_of_phases`
  takes `1 ≤ t.count p` and `t.count p ≤ lat`. The references pass `hN` (matmul's `lat` is `N`) and
  `show N ≤ 2 * N by omega` (the sorter's); a new `lat` needs its own (`show 1 ≤ (N + 3) / 4 by omega` in the
  four-step matmul variant).
* **A `whnf` timeout in a run lemma after a condition changed.** The reference's `cell_run` took 21.1k of the
  default 200k heartbeats (the v1 file, "Cost" above). In a sorter variant with rewritten cell conditions,
  `cell_run` stopped at ``(deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been
  reached``, in a compile of 298 CPU s, and with `set_option maxHeartbeats 1000000` one compile took 1334 s of user
  time alone (1376 s of wall clock), far past the 300 CPU s the check allows; `lake env lean` in the inner loop
  enforces no CPU-time limit, only Lean's heartbeat one (measured 2026-11-10). What made the same proof compile,
  in 20 CPU s for the whole file: (1)
  each new condition as its own `@[irreducible] def` of type `Expr2`, used in the mirror `cellP`, so that `simp`
  cannot unfold `evalExpr2` into it; (2) one evaluation lemma per condition, `evalExpr2 fuel st (c W k) = .ok v`
  under a hypothesis `8 ≤ fuel`, proved once (write `fuel` as `n + 8`, then `simp` with the definitions); (3) in
  the run lemma, after a `by_cases` on each condition's value, two stages:
  `simp (disch := omega) only [cellP, runEdgeProcess2, execStmt2, execStmts2, SS, <the evaluation lemmas>]`, then
  `simp [evalExpr2, resolveLhs2, readSignal, SvState.lookup, cellQ, <the cases>]`.
* **Mathlib's names are not in scope.** Between them the references use core tactics (`simp`, `omega`, `decide`,
  `rfl`, `rw`, `by_cases`, `split`, `induction`, `obtain`, `refine`, `exact`, `unfold`, `congr`, `funext`) and
  the library's `sv2_inst_simp`, and import no Mathlib: in a file like theirs `zify` is an `unknown tactic` and
  `Nat.le_induction` an ``Unknown constant `Nat.le_induction` ``. Section 6's table gives core forms of Mathlib
  habits (none for `zify`); for `Nat.le_induction`, `obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h` and then
  `induction d`, as an accepted matmul variant does. A proof may import Mathlib (README.md, "Mathlib in
  submissions", says what an import costs; in a clone of the public repository its build comes from
  `lake exe cache get`).

## 20. A reactive task: the arbiter (`ReactTask`)

A reactive task (`kind` `react-family`; the `arbiter`) is clocked, like section 19's, but has no transaction and no
latency: the statement (`ReactTask` in `SvGolf/TaskReact.lean`) is a safety property on every cycle and a bounded
response over the whole input trace, from every power-up state, under every schedule, on every known stimulus,
at every reset release. The design must be Moore (`MooreOut`: no combinational path from an input port to an
output port), terminate from every power-up (`TerminatesPU`) and contain no construct that can create an `x`
from known operands (`XSafe`). There is no `-- svgolf-latency:` line (the checker refuses one) and no `sv_*`
tactic; the score is the area times the register-to-register period, one decision per cycle.

The untrusted library reduces the statement at one parameter value to facts about ONE clock cycle:
`ReactTask.satisfiedAt_of_rank` (`SvGolf/React.lean`) takes the interface, `Disciplined` (`ClockedBy clk none`
and `MooreOut`), `TerminatesPU`, a **rank model**, the proof that every power-up state has the model's shape,
and `XSafe`. The release, the segment of entries with `rst` = 0, the safety monitor's ghost state and the
response window are discharged once, inside the reduction (`ReactTask.claim_of_rank`, with the window argument
`ReactTask.responds_of_rank`). The reference `tasks/arbiter/reference/rr_mask.lean` (the registered mask
round-robin: the lowest requester of `req & mask` wins, else the lowest requester; the mask is the thermometer
above the last grant) takes six steps; the names are that file's, the section numbers its own.

1. **Agreement** (§1, `rr_sem_eq`): the loaded family `design.sem N` equals a hand-built design `rrD N` for
   every `N ≥ 1`, by `sv2_inst_simp` (wrapped as `rr_inst_simp`). The comb block's self-read guard is
   `comb_admits`. One proof-side lemma, `inst_ne_fill`, lowers `x != '0` at `x`'s width: `sv2_inst_simp`
   alone stops at a comparison with a fill at a symbolic width.
2. **One cycle in closed form** (§2, `rr_cycle`, for any values, `x` included): the inputs applied, the comb
   settle, the edge (`ff_run`), the commit (`commit_ff`), the settle again. ls-sv's clock-step library has a
   closed form for flip-flop-only designs only (`cycleStep2_ffOnly`), so a design with an `always_comb` block
   proves its own settle: `settle_rr` shows that one pass computes the block from `req` and `mask`, which it
   does not write (it reads `mreq` only after writing it), and that a second pass changes nothing, which ends
   the settle loop under every schedule.
   Termination follows from the same lemma (`rr_terminates`, by `TerminatesPU.of_invariant` with the shape as
   the invariant).
3. **The shape** (§3, `Shp`, `rr_init`, `rrNext_shp`): the seven signals in declaration order, the registers
   and nets `N` bits wide; the shape is the rank model's `CycleModel.Shape` and every cycle keeps it.
4. **The cycle on known values** (§4, `rrNext_reset`, `rrNext_run`): after a reset entry `gnt = 0` and `mask`
   all ones, from ANY state of the shape; after an entry with `rst` = 0 and a known `req = x`, from a known
   mask `mk`, `gnt = RoundRobin.pick x mk` and `mask = RoundRobin.next x mk`. The bridge from `LVec` to `BitVec` is
   one lemma per operator of the block (`mr_val`, `pickV_val`, `NZ_val`, `MaskV_val`).
5. **The rank model** (§5, `model`): a `ReactTask.RankModel` extends the `CycleModel` with an invariant `Inv`
   of the snapshots from a reset on (here `ArbInv`: every signal but `clk` known, the mask a thermometer
   `RoundRobin.Thermo mk e` with its edge at `e`), the outputs a snapshot shows (`out`: the grant), and a
   `rank` per obligation, here requester `i`'s cyclic distance from the mask's edge, `RoundRobin.dist N e i`,
   at most `N - 1` (`rank_le`, by `dist_le`). Its two obligations are the RESET obligation (from any state of
   the shape, a reset cycle gives the invariant and `gnt = 0`) and the STEP obligation (from the invariant, a
   cycle with `rst` = 0 gives the invariant again, `Grants x gnt`, and for every requester that asks: it is
   granted, or its rank drops). Safety is `pick_grants` (from `pick_atMostOne`, `pick_sub`, `pick_eq_zero`);
   progress is `RoundRobin.step`: a requester that loses gets strictly closer to the edge, because the winner
   lies between the edge and it.
6. **Structure** (§6): `rr_interface` (`rfl`, the distinct names by `decide`), `rr_disciplined` (`ClockedBy` by
   `simp` over the two processes, `MooreOut` by `mooreOut_of_combTargets`: no comb process writes an output),
   `rr_powerUp` (every power-up state has the shape, by `powerUp_cons` once per declaration and `powerUp_nil`),
   `rr_xsafe` (`xsafeB` by `simp`: one width per operand pair of `&`, `!=` and the arms of `?:`, no division, no
   dynamic index), and `solution`, one application of `satisfiedAt_of_rank`.

**Another policy.** The reduction, the window argument and the lowest-set-bit lemmas (`IsLow`,
`getLsbD_isolate`, `isolate_eq_twoPow`, `isolate_eq_zero`: `x & (~x + 1)` is the one-hot of the lowest set bit)
serve every arbiter. `pick`, `next`, `Thermo` and `step` describe the mask policy, not this file's encoding, so
a golfer's mask round-robin with another netlist reuses them; a pointer, a rotating priority, a tree or a matrix
brings its own invariant and rank (for instance, for a rotating priority the distance from the pointer, for a
matrix the number of clients ahead in the order). Writing the comb logic as one block computed from signals it
does not write keeps step 2 to the same two-pass argument.

**What the attacks show.** The 17 designs of `tests/arbiter/attacks/` each break one conjunct: a Mealy output
(`MooreOut`), an unreset grant (G0), fixed priority or a forgotten mask update (G4), a time bomb after 4095
cycles (G4, seen only by the long reset-free run), a register that only holds itself (refused at `score`, the
never-loaded check). Each is rejected by `check.py --unproved`, before any proof; the kernel-checked
refutations of hand-built twins, and `bound_tight` (no design meets the statement with the bound `N - 2`), are
in `tests/arbiter/negative/Refute.lean`.

**Cost** (MEASURED 2026-11-07, line counts of `rr_mask.lean`: 667 lines, 487 of code). Code lines: agreement
107, one cycle in closed form 121, the shape 24, the cycle on known values 85, the rank model 83, the structure
and the statement 56, the imports 11. Time and heartbeats (READ, `tasks/arbiter/README.md`, section 5, measured
against the current statement): the `solution` stage 11.2 to 12.7 CPU s in three cold `check.py` runs (2026-11-07,
`score/time_limits.json`; the limit is 300 CPU s), 53.3 million heartbeats for the whole proof, at most 12.8
million for one declaration (`comb_admits`, the self-read guard at a symbolic width), each far under the default
limit of 200 million. Axioms `propext`, `Classical.choice`, `Quot.sound`.
