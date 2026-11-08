import tests.seq_counter.negative.Refute

/-!
# txtask-v2's acceptance table (the maintainers' fixtures, 2026-11-05)

Each fixture is the counter (`tests/seq_counter`, `SeqTask`, output `q`) with one construct the
maintainers' table asks about (fixtures 0 to 11) or the attack on revision 2 found (12 to 16, MEASURED
2026-11-06 the same way), hand-built as the extractor loads it (MEASURED, 2026-11-05: `load_sv` of
each `.sv` fixture through this branch's extractor, `(task := "tests/seq_counter")`, printed with
`reprStr`, and the definitions below are that print with default fields dropped and known
literals written `LVec.ofNat`; the `.sv` files are in the session scratchpad, not on the branch,
as for the probe's twins). The expected verdict of each, and how it is shown:

| # | fixture | verdict | by | shown |
|---|---|---|---|---|
| 0 | `f0`: `q + (1 ^ (u ^ u))`, `u` unreset | ACCEPT | rule 2 | rules 1, 3 kernel; rule 2 on every power-up (kernel); v1's x start REJECTS it (`#guard`) |
| 1 | `f1`: `t = u; t = 0; if (t)` | ACCEPT | | rules 1, 3 kernel; rule 2 on every power-up (kernel) |
| 2 | `f2`: W1, `t = u; if (!t) ...; t = 0` | REJECT | rule 2 | kernel: power-up `u = 0` saturates |
| 3 | `f3`: W2, `(d / d) != 1` | REJECT | rule 3 | kernel: `¬ XSafe`; rule 2 alone passes it (`#guard`) |
| 4 | `f4`: `q / 2'd3` | ACCEPT | | rules 1, 3 kernel (`constNZ`); rule 2 on every power-up (kernel) |
| 5 | `f5`: O1, unreset `b` behind `busy` | ACCEPT | | rules 1, 3 kernel; rule 2 on every power-up (kernel) |
| 6 | `f6`: W3 at `N = 2` | REJECT | rule 2 | kernel: power-up `q = 2, p = 0` counts by 2 |
| 7 | `f7`: `bit u` unreset | REJECT | rule 2 | kernel: power-up `u = 1` holds `q` |
| 8 | `f8`: `case (s)` unreset, default arm | REJECT | rule 2 | kernel: power-up `s = 1` holds `q` |
| 9 | `f9`: `s === 1'bx` | REJECT | rule 3 (and the gate) | kernel: `¬ XSafe` (an x literal); rule 2 alone passes it (`#guard`) |
| 10a | `f10a`: `a[i]`, `a` 3 bits, `i` 2 bits | REJECT | rule 3 (and `fourstate` (d)) | kernel: `¬ XSafe`; rule 2 alone passes it (`#guard`) |
| 10b | `f10b`: `a[i]`, `a` 4 bits | ACCEPT | | rules 1, 3 kernel; rule 2 on every power-up (`#guard`) |
| 11 | `u4`: W4, `unique case` violated before an edge | depends on ls-sv's W4 fix | | `#guard`: the run completes, the case check fails at the pre-edge state |
| 12 | `f12`: signed read index `m[i]`, `i = 2'b11` | REJECT | rule 3 (unsigned index; and `fourstate` (d)) | kernel: `¬ XSafe`; rule 2 alone passes it (`#guard`) |
| 13 | `f13`: signed write index `t[i] = 1` | REJECT | rule 3 (unsigned index; and `fourstate` (d)) | kernel: `¬ XSafe`; rule 2 alone passes it (`#guard`) |
| 14 | `f14`: unsigned write index out of range | ACCEPT | | rules 1, 3 kernel; rule 2 on every power-up (`#guard`) |
| 15 | `f15`: `m[$signed(i)]`, `i` unsigned | depends on ls-sv's W5 fix | (`fourstate` (d) today) | kernel: `XSafe` (the cast is not in the loaded design); rule 2 `#guard` |
| 16 | `f16`: `q + ((a + b) >> 1)`, the context width | ACCEPT at `N = 2`, REJECT at `N = 1` | rule 2 at `N = 1` | `N = 2`: rules 1, 3 and rule 2 on every power-up (kernel); `N = 1`: kernel `f16n1_refuted` |

"Rule 2 on every power-up (kernel)" is a kernel-checked theorem (`puRun`, with `puRun_spec`) that from
EVERY power-up state (all of them: `mem_powerUps`) the run on `stimA` (reset, count twice, hold, reset
while `en` is high, count) shows the counter in every snapshot. `#guard` rows (interpreted
evaluation) widen it to every stimulus of three entries over `rst`, `en` beginning with a reset,
under both schedules (`boundedPU`). Both are the rule's claim on the fixture's runs, not a proof of
`FollowsPU`, which quantifies over every stimulus: a full proof of an acceptance is a reference
proof's work, and the counter's (`tests/seq_counter/reference/cnt.lean`) is one.
-/

namespace SvGolf.Tests.SeqCounter.Table

open LeanModels.Sv SvGolf SvGolf.Tests.SeqCounter.Negative

/-! ## The fixtures, hand-built -/

/-- Fixture 0 (`f0_xpess.sv`): `u <= u` never reset, `q <= q + (1'b1 ^ (u ^ u))`. -/
def f0 : Design2 where
  name := "cnt"
  decls := #[{ name := "clk", width := 1, isInput := true },
             { name := "rst", width := 1, isInput := true },
             { name := "en", width := 1, isInput := true },
             { name := "q", width := 1, isOutput := true },
             { name := "u", width := 1 }]
  processes := #[Process2.alwaysFF
                   "clk"
                   (Stmt2.block
                     #[Stmt2.nbaAssign (Lhs2.ident "u") (Expr2.ident "u"),
                       Stmt2.ifStmt
                         (Expr2.ident "rst")
                         (Stmt2.nbaAssign
                           (Lhs2.ident "q")
                           (Expr2.lit ⟨#[.l0]⟩))
                         (some (Stmt2.ifStmt
                            (Expr2.ident "en")
                            (Stmt2.nbaAssign
                              (Lhs2.ident "q")
                              (Expr2.binary
                                .add
                                (Expr2.ident "q")
                                (Expr2.binary
                                  .xor
                                  (Expr2.resize
                                    1
                                    (Expr2.lit ⟨#[.l1]⟩))
                                  (Expr2.binary
                                    .xor
                                    (Expr2.resize 1 (Expr2.ident "u"))
                                    (Expr2.resize 1 (Expr2.ident "u"))))))
                            none))])]

/-- Fixture 1 (`f1_tover.sv`): `t = u; t = 0; if (t) lo = 1; else lo = 0;`, `if (en && !lo) q <= q + 1`. -/
def f1 : Design2 where
  name := "cnt"
  decls := #[{ name := "clk", width := 1, isInput := true },
             { name := "rst", width := 1, isInput := true },
             { name := "en", width := 1, isInput := true },
             { name := "q", width := 1, isOutput := true },
             { name := "u", width := 1 },
             { name := "t", width := 1 },
             { name := "lo", width := 1 }]
  processes := #[Process2.alwaysFF
                   "clk"
                   (Stmt2.nbaAssign (Lhs2.ident "u") (Expr2.ident "u")),
                 Process2.alwaysComb
                   (Stmt2.block
                     #[Stmt2.blockingAssign
                         (Lhs2.ident "t")
                         (Expr2.ident "u"),
                       Stmt2.blockingAssign
                         (Lhs2.ident "t")
                         (Expr2.lit ⟨#[.l0]⟩),
                       Stmt2.ifStmt
                         (Expr2.ident "t")
                         (Stmt2.blockingAssign
                           (Lhs2.ident "lo")
                           (Expr2.lit ⟨#[.l1]⟩))
                         (some (Stmt2.blockingAssign
                            (Lhs2.ident "lo")
                            (Expr2.lit ⟨#[.l0]⟩)))]),
                 Process2.alwaysFF
                   "clk"
                   (Stmt2.ifStmt
                     (Expr2.ident "rst")
                     (Stmt2.nbaAssign
                       (Lhs2.ident "q")
                       (Expr2.lit ⟨#[.l0]⟩))
                     (some (Stmt2.ifStmt
                        (Expr2.logical
                          true
                          (Expr2.ident "en")
                          (Expr2.unary .lnot (Expr2.ident "lo")))
                        (Stmt2.nbaAssign
                          (Lhs2.ident "q")
                          (Expr2.binary
                            .add
                            (Expr2.ident "q")
                            (Expr2.resize
                              1
                              (Expr2.lit ⟨#[.l1]⟩))))
                        none)))]

/-- Fixture 2, round 1's W1 (`w1_rare.sv`): `t = u; if (!t) lo = 1; else lo = 0; t = 0;`, `lo` makes the counter saturate. -/
def f2 : Design2 where
  name := "cnt"
  decls := #[{ name := "clk", width := 1, isInput := true },
             { name := "rst", width := 1, isInput := true },
             { name := "en", width := 1, isInput := true },
             { name := "q", width := 1, isOutput := true },
             { name := "u", width := 1 },
             { name := "t", width := 1 },
             { name := "lo", width := 1 }]
  processes := #[Process2.alwaysFF
                   "clk"
                   (Stmt2.nbaAssign (Lhs2.ident "u") (Expr2.ident "u")),
                 Process2.alwaysComb
                   (Stmt2.block
                     #[Stmt2.blockingAssign
                         (Lhs2.ident "t")
                         (Expr2.ident "u"),
                       Stmt2.ifStmt
                         (Expr2.unary .lnot (Expr2.ident "t"))
                         (Stmt2.blockingAssign
                           (Lhs2.ident "lo")
                           (Expr2.lit ⟨#[.l1]⟩))
                         (some (Stmt2.blockingAssign
                            (Lhs2.ident "lo")
                            (Expr2.lit ⟨#[.l0]⟩))),
                       Stmt2.blockingAssign
                         (Lhs2.ident "t")
                         (Expr2.lit ⟨#[.l0]⟩)]),
                 Process2.alwaysFF
                   "clk"
                   (Stmt2.ifStmt
                     (Expr2.ident "rst")
                     (Stmt2.nbaAssign
                       (Lhs2.ident "q")
                       (Expr2.lit ⟨#[.l0]⟩))
                     (some (Stmt2.ifStmt
                        (Expr2.ident "lo")
                        (Stmt2.block
                          #[Stmt2.ifStmt
                              (Expr2.reduce .and (Expr2.ident "q"))
                              (Stmt2.nbaAssign
                                (Lhs2.ident "q")
                                (Expr2.ident "q"))
                              (some (Stmt2.ifStmt
                                 (Expr2.ident "en")
                                 (Stmt2.nbaAssign
                                   (Lhs2.ident "q")
                                   (Expr2.binary
                                     .add
                                     (Expr2.ident "q")
                                     (Expr2.resize
                                       1
                                       (Expr2.lit ⟨#[.l1]⟩))))
                                 none))])
                        (some (Stmt2.ifStmt
                           (Expr2.ident "en")
                           (Stmt2.nbaAssign
                             (Lhs2.ident "q")
                             (Expr2.binary
                               .add
                               (Expr2.ident "q")
                               (Expr2.resize
                                 1
                                 (Expr2.lit ⟨#[.l1]⟩))))
                           none)))))]

/-- Fixture 3, round 1's W2 (`w2_div0.sv`): `assign d = q + 2`, `else if ((d / d) != 1) q <= q`. -/
def f3 : Design2 where
  name := "cnt"
  decls := #[{ name := "clk", width := 1, isInput := true },
             { name := "rst", width := 1, isInput := true },
             { name := "en", width := 1, isInput := true },
             { name := "q", width := 1, isOutput := true },
             { name := "d", width := 1 }]
  processes := #[Process2.assign
                   (Lhs2.ident "d")
                   (Expr2.resize
                     1
                     (Expr2.binary
                       .add
                       (Expr2.resize 2 (Expr2.ident "q"))
                       (Expr2.resize
                         2
                         (Expr2.lit (LVec.ofNat 2 2))))),
                 Process2.alwaysFF
                   "clk"
                   (Stmt2.ifStmt
                     (Expr2.ident "rst")
                     (Stmt2.nbaAssign
                       (Lhs2.ident "q")
                       (Expr2.lit ⟨#[.l0]⟩))
                     (some (Stmt2.ifStmt
                        (Expr2.binary
                          .ne
                          (Expr2.binary
                            .div
                            (Expr2.resize 32 (Expr2.ident "d"))
                            (Expr2.resize 32 (Expr2.ident "d")))
                          (Expr2.lit
                            (LVec.ofNat 32 1)))
                        (Stmt2.nbaAssign (Lhs2.ident "q") (Expr2.ident "q"))
                        (some (Stmt2.ifStmt
                           (Expr2.ident "en")
                           (Stmt2.nbaAssign
                             (Lhs2.ident "q")
                             (Expr2.binary
                               .add
                               (Expr2.ident "q")
                               (Expr2.resize
                                 1
                                 (Expr2.lit ⟨#[.l1]⟩))))
                           none)))))]

/-- Fixture 4 (`f4_divc.sv`): `if ((q / 2'd3) <= q) q <= q + 1; else q <= 0;` (a nonzero constant divisor). -/
def f4 : Design2 where
  name := "cnt"
  decls := #[{ name := "clk", width := 1, isInput := true },
             { name := "rst", width := 1, isInput := true },
             { name := "en", width := 1, isInput := true },
             { name := "q", width := 1, isOutput := true }]
  processes := #[Process2.alwaysFF
                   "clk"
                   (Stmt2.ifStmt
                     (Expr2.ident "rst")
                     (Stmt2.nbaAssign
                       (Lhs2.ident "q")
                       (Expr2.lit ⟨#[.l0]⟩))
                     (some (Stmt2.ifStmt
                        (Expr2.ident "en")
                        (Stmt2.block
                          #[Stmt2.ifStmt
                              (Expr2.binary
                                .le
                                (Expr2.binary
                                  .div
                                  (Expr2.resize 2 (Expr2.ident "q"))
                                  (Expr2.lit
                                    (LVec.ofNat 2 3)))
                                (Expr2.resize 2 (Expr2.ident "q")))
                              (Stmt2.nbaAssign
                                (Lhs2.ident "q")
                                (Expr2.binary
                                  .add
                                  (Expr2.ident "q")
                                  (Expr2.resize
                                    1
                                    (Expr2.lit ⟨#[.l1]⟩))))
                              (some (Stmt2.nbaAssign
                                 (Lhs2.ident "q")
                                 (Expr2.lit ⟨#[.l0]⟩)))])
                        none)))]

/-- Fixture 5 (`f5_guard.sv`), round 1's O1 shape: `b` is never reset, `if (busy) if (b) ...`. -/
def f5 : Design2 where
  name := "cnt"
  decls := #[{ name := "clk", width := 1, isInput := true },
             { name := "rst", width := 1, isInput := true },
             { name := "en", width := 1, isInput := true },
             { name := "q", width := 1, isOutput := true },
             { name := "busy", width := 1 },
             { name := "b", width := 1 }]
  processes := #[Process2.alwaysFF
                   "clk"
                   (Stmt2.block
                     #[Stmt2.ifStmt
                         (Expr2.ident "en")
                         (Stmt2.nbaAssign
                           (Lhs2.ident "b")
                           (Expr2.lit ⟨#[.l1]⟩))
                         none,
                       Stmt2.ifStmt
                         (Expr2.ident "rst")
                         (Stmt2.block
                           #[Stmt2.nbaAssign
                               (Lhs2.ident "q")
                               (Expr2.lit ⟨#[.l0]⟩),
                             Stmt2.nbaAssign
                               (Lhs2.ident "busy")
                               (Expr2.lit ⟨#[.l0]⟩)])
                         (some (Stmt2.ifStmt
                            (Expr2.ident "en")
                            (Stmt2.block
                              #[Stmt2.nbaAssign
                                  (Lhs2.ident "busy")
                                  (Expr2.lit ⟨#[.l1]⟩),
                                Stmt2.ifStmt
                                  (Expr2.ident "busy")
                                  (Stmt2.block
                                    #[Stmt2.ifStmt
                                        (Expr2.ident "b")
                                        (Stmt2.nbaAssign
                                          (Lhs2.ident "q")
                                          (Expr2.binary
                                            .add
                                            (Expr2.ident "q")
                                            (Expr2.resize
                                              1
                                              (Expr2.lit ⟨#[.l1]⟩))))
                                        (some (Stmt2.nbaAssign
                                           (Lhs2.ident "q")
                                           (Expr2.lit ⟨#[.l0]⟩)))])
                                  (some (Stmt2.nbaAssign
                                     (Lhs2.ident "q")
                                     (Expr2.binary
                                       .add
                                       (Expr2.ident "q")
                                       (Expr2.resize
                                         1
                                         (Expr2.lit ⟨#[.l1]⟩)))))])
                            none))])]

/-- Fixture 6, round 1's W3 (`w3_rstedge.sv`) at `N = 2`: the reset sets `g` from `q - p == 2`, which only a power-up state reaches. -/
def f6 : Design2 where
  name := "cnt"
  decls := #[{ name := "clk", width := 1, isInput := true },
             { name := "rst", width := 1, isInput := true },
             { name := "en", width := 1, isInput := true },
             { name := "q", width := 2, isOutput := true },
             { name := "p", width := 2 },
             { name := "g", width := 1 }]
  processes := #[Process2.alwaysFF
                   "clk"
                   (Stmt2.ifStmt
                     (Expr2.ident "rst")
                     (Stmt2.block
                       #[Stmt2.nbaAssign
                           (Lhs2.ident "q")
                           (Expr2.lit (LVec.ofNat 2 0)),
                         Stmt2.nbaAssign
                           (Lhs2.ident "p")
                           (Expr2.lit (LVec.ofNat 2 0)),
                         Stmt2.ifStmt
                           (Expr2.binary
                             .eq
                             (Expr2.binary
                               .sub
                               (Expr2.ident "q")
                               (Expr2.ident "p"))
                             (Expr2.resize
                               2
                               (Expr2.lit (LVec.ofNat 2 2))))
                           (Stmt2.nbaAssign
                             (Lhs2.ident "g")
                             (Expr2.lit ⟨#[.l1]⟩))
                           (some (Stmt2.nbaAssign
                              (Lhs2.ident "g")
                              (Expr2.lit ⟨#[.l0]⟩)))])
                     (some (Stmt2.block
                        #[Stmt2.nbaAssign (Lhs2.ident "p") (Expr2.ident "q"),
                          Stmt2.ifStmt
                            (Expr2.ident "en")
                            (Stmt2.nbaAssign
                              (Lhs2.ident "q")
                              (Expr2.binary
                                .add
                                (Expr2.binary
                                  .add
                                  (Expr2.ident "q")
                                  (Expr2.resize
                                    2
                                    (Expr2.lit ⟨#[.l1]⟩)))
                                (Expr2.resize 2 (Expr2.ident "g"))))
                            none])))]

/-- Fixture 7 (`f7_bit.sv`): `bit u; u <= u;` never reset, `else if (u) q <= '0`. -/
def f7 : Design2 where
  name := "cnt"
  decls := #[{ name := "clk", width := 1, isInput := true },
             { name := "rst", width := 1, isInput := true },
             { name := "en", width := 1, isInput := true },
             { name := "q", width := 1, isOutput := true },
             { name := "u", width := 1, twoState := true }]
  processes := #[Process2.alwaysFF
                   "clk"
                   (Stmt2.block
                     #[Stmt2.nbaAssign
                         (Lhs2.ident "u")
                         (Expr2.squash2 (Expr2.ident "u")),
                       Stmt2.ifStmt
                         (Expr2.ident "rst")
                         (Stmt2.nbaAssign
                           (Lhs2.ident "q")
                           (Expr2.lit ⟨#[.l0]⟩))
                         (some (Stmt2.ifStmt
                            (Expr2.ident "u")
                            (Stmt2.nbaAssign
                              (Lhs2.ident "q")
                              (Expr2.lit ⟨#[.l0]⟩))
                            (some (Stmt2.ifStmt
                               (Expr2.ident "en")
                               (Stmt2.nbaAssign
                                 (Lhs2.ident "q")
                                 (Expr2.binary
                                   .add
                                   (Expr2.ident "q")
                                   (Expr2.resize
                                     1
                                     (Expr2.lit ⟨#[.l1]⟩))))
                               none))))])]

/-- Fixture 8 (`f8_case.sv`): `s <= s` never reset, `case (s) 1'b1: q <= '0; default: if (en) q <= q + 1; endcase`. -/
def f8 : Design2 where
  name := "cnt"
  decls := #[{ name := "clk", width := 1, isInput := true },
             { name := "rst", width := 1, isInput := true },
             { name := "en", width := 1, isInput := true },
             { name := "q", width := 1, isOutput := true },
             { name := "s", width := 1 }]
  processes := #[Process2.alwaysFF
                   "clk"
                   (Stmt2.block
                     #[Stmt2.nbaAssign (Lhs2.ident "s") (Expr2.ident "s"),
                       Stmt2.ifStmt
                         (Expr2.ident "rst")
                         (Stmt2.nbaAssign
                           (Lhs2.ident "q")
                           (Expr2.lit ⟨#[.l0]⟩))
                         (some (Stmt2.caseStmt
                            (Expr2.ident "s")
                            #[CaseItem2.mk
                                #[Expr2.lit ⟨#[.l1]⟩]
                                (Stmt2.nbaAssign
                                  (Lhs2.ident "q")
                                  (Expr2.lit ⟨#[.l0]⟩))]
                            (some (Stmt2.ifStmt
                               (Expr2.ident "en")
                               (Stmt2.nbaAssign
                                 (Lhs2.ident "q")
                                 (Expr2.binary
                                   .add
                                   (Expr2.ident "q")
                                   (Expr2.resize
                                     1
                                     (Expr2.lit ⟨#[.l1]⟩))))
                               none))
                            (CaseMode.normal)
                            (CaseCheck.none)))])]

/-- Fixture 10a (`f10_oob.sv`): `a` is 3 bits, the 2-bit index `i` reaches 3: `if (a[i] == 1) q <= 0; else q <= q + 1;`. -/
def f10a : Design2 where
  name := "cnt"
  decls := #[{ name := "clk", width := 1, isInput := true },
             { name := "rst", width := 1, isInput := true },
             { name := "en", width := 1, isInput := true },
             { name := "q", width := 1, isOutput := true },
             { name := "a", width := 3 },
             { name := "i", width := 2 }]
  processes := #[Process2.alwaysFF
                   "clk"
                   (Stmt2.ifStmt
                     (Expr2.ident "rst")
                     (Stmt2.block
                       #[Stmt2.nbaAssign
                           (Lhs2.ident "q")
                           (Expr2.lit ⟨#[.l0]⟩),
                         Stmt2.nbaAssign
                           (Lhs2.ident "a")
                           (Expr2.lit
                             (LVec.ofNat 3 0)),
                         Stmt2.nbaAssign
                           (Lhs2.ident "i")
                           (Expr2.lit (LVec.ofNat 2 0))])
                     (some (Stmt2.block
                        #[Stmt2.nbaAssign
                            (Lhs2.ident "i")
                            (Expr2.binary
                              .add
                              (Expr2.ident "i")
                              (Expr2.resize
                                2
                                (Expr2.lit ⟨#[.l1]⟩))),
                          Stmt2.ifStmt
                            (Expr2.ident "en")
                            (Stmt2.block
                              #[Stmt2.ifStmt
                                  (Expr2.binary
                                    .eq
                                    (Expr2.index
                                      (Expr2.ident "a")
                                      (Expr2.ident "i")
                                      1)
                                    (Expr2.lit ⟨#[.l1]⟩))
                                  (Stmt2.nbaAssign
                                    (Lhs2.ident "q")
                                    (Expr2.lit ⟨#[.l0]⟩))
                                  (some (Stmt2.nbaAssign
                                     (Lhs2.ident "q")
                                     (Expr2.binary
                                       .add
                                       (Expr2.ident "q")
                                       (Expr2.resize
                                         1
                                         (Expr2.lit ⟨#[.l1]⟩)))))])
                            none])))]

/-- Fixture 10b (`f10_pow2.sv`): the same with `a` 4 bits: every index value is in range. -/
def f10b : Design2 where
  name := "cnt"
  decls := #[{ name := "clk", width := 1, isInput := true },
             { name := "rst", width := 1, isInput := true },
             { name := "en", width := 1, isInput := true },
             { name := "q", width := 1, isOutput := true },
             { name := "a", width := 4 },
             { name := "i", width := 2 }]
  processes := #[Process2.alwaysFF
                   "clk"
                   (Stmt2.ifStmt
                     (Expr2.ident "rst")
                     (Stmt2.block
                       #[Stmt2.nbaAssign
                           (Lhs2.ident "q")
                           (Expr2.lit ⟨#[.l0]⟩),
                         Stmt2.nbaAssign
                           (Lhs2.ident "a")
                           (Expr2.lit
                             (LVec.ofNat 4 0)),
                         Stmt2.nbaAssign
                           (Lhs2.ident "i")
                           (Expr2.lit (LVec.ofNat 2 0))])
                     (some (Stmt2.block
                        #[Stmt2.nbaAssign
                            (Lhs2.ident "i")
                            (Expr2.binary
                              .add
                              (Expr2.ident "i")
                              (Expr2.resize
                                2
                                (Expr2.lit ⟨#[.l1]⟩))),
                          Stmt2.ifStmt
                            (Expr2.ident "en")
                            (Stmt2.block
                              #[Stmt2.ifStmt
                                  (Expr2.binary
                                    .eq
                                    (Expr2.index
                                      (Expr2.ident "a")
                                      (Expr2.ident "i")
                                      1)
                                    (Expr2.lit ⟨#[.l1]⟩))
                                  (Stmt2.nbaAssign
                                    (Lhs2.ident "q")
                                    (Expr2.lit ⟨#[.l0]⟩))
                                  (some (Stmt2.nbaAssign
                                     (Lhs2.ident "q")
                                     (Expr2.binary
                                       .add
                                       (Expr2.ident "q")
                                       (Expr2.resize
                                         1
                                         (Expr2.lit ⟨#[.l1]⟩)))))])
                            none])))]

/-- Fixture 9: `s <= s` never reset, `else if (s === 1'bx) q <= '0`. Hand-built: the source gate
refuses the `x` literal (MEASURED: `srcgate.py --clock clk`, "x/z literal `1'bx`"), so no
envelope of it exists; this is fixture 8's shape with the condition `s === 1'bx`. -/
def f9 : Design2 where
  name := "cnt"
  decls := #[{ name := "clk", width := 1, isInput := true },
             { name := "rst", width := 1, isInput := true },
             { name := "en", width := 1, isInput := true },
             { name := "q", width := 1, isOutput := true },
             { name := "s", width := 1 }]
  processes := #[Process2.alwaysFF "clk" (Stmt2.block #[
    Stmt2.nbaAssign (Lhs2.ident "s") (Expr2.ident "s"),
    Stmt2.ifStmt (Expr2.ident "rst") (Stmt2.nbaAssign (Lhs2.ident "q") (Expr2.lit ⟨#[.l0]⟩))
      (some (Stmt2.ifStmt (Expr2.binary .caseEq (Expr2.ident "s") (Expr2.lit ⟨#[.lx]⟩))
        (Stmt2.nbaAssign (Lhs2.ident "q") (Expr2.lit ⟨#[.l0]⟩))
        (some (Stmt2.ifStmt (Expr2.ident "en")
          (Stmt2.nbaAssign (Lhs2.ident "q")
            (Expr2.binary .add (Expr2.ident "q") (Expr2.resize 1 (Expr2.lit ⟨#[.l1]⟩))))
          none))))])]

/-- Fixture 11, round 1's W4 (`u4.sv`, hand-built: the source gate refuses `unique`):
`m <= en; if (rst) q <= 0; else unique case (1'b1) en: q <= 1; !m: q <= 2; default: q <= q;`.
At every snapshot `m = en`, so one item matches; before the edge of an entry with `en = 1` after one
with `en = 0`, both do. -/
def u4 : Design2 where
  name := "u4"
  decls := #[{ name := "clk", width := 1, isInput := true },
             { name := "rst", width := 1, isInput := true },
             { name := "en", width := 1, isInput := true },
             { name := "q", width := 2, isOutput := true },
             { name := "m", width := 1 }]
  processes := #[.alwaysFF "clk" (.block #[
    .nbaAssign (.ident "m") (.ident "en"),
    .ifStmt (.ident "rst") (.nbaAssign (.ident "q") (.lit (LVec.ofNat 2 0)))
      (some (.caseStmt (.lit (LVec.ofNat 1 1))
        #[.mk #[.ident "en"] (.nbaAssign (.ident "q") (.lit (LVec.ofNat 2 1))),
          .mk #[.unary .lnot (.ident "m")] (.nbaAssign (.ident "q") (.lit (LVec.ofNat 2 2)))]
        (some (.nbaAssign (.ident "q") (.ident "q"))) .normal .unique))])]

/-! ## The attack on revision 2 (2026-11-06): signed and out-of-range dynamic indices, a context width -/

/-- Fixture 12 (`f12_sidx_read.sv`, the attack's finding 2): a SIGNED dynamic read index.
`m <= 4'b1000; i <= 2'b11` at reset, then `if (en && m[i]) q <= q + 1`. ls-sv reads `i` unsigned
(3, and `m[3] = 1`: the counter); IEEE 1800 reads it as -1, out of `[3:0]`, so `m[i]` is `x`. -/
def f12 : Design2 where
  name := "cnt"
  decls := #[{ name := "clk", width := 1, isInput := true },
             { name := "rst", width := 1, isInput := true },
             { name := "en", width := 1, isInput := true },
             { name := "q", width := 1, isOutput := true },
             { name := "m", width := 4 },
             { name := "i", width := 2, isSigned := true }]
  processes := #[Process2.alwaysFF "clk"
    (Stmt2.ifStmt (Expr2.ident "rst")
      (Stmt2.block #[Stmt2.nbaAssign (Lhs2.ident "q") (Expr2.lit ⟨#[.l0]⟩),
        Stmt2.nbaAssign (Lhs2.ident "m") (Expr2.lit (LVec.ofNat 4 8)),
        Stmt2.nbaAssign (Lhs2.ident "i") (Expr2.lit (LVec.ofNat 2 3))])
      (some (Stmt2.ifStmt
        (Expr2.logical true (Expr2.ident "en") (Expr2.index (Expr2.ident "m") (Expr2.ident "i") 1))
        (Stmt2.nbaAssign (Lhs2.ident "q")
          (Expr2.binary .add (Expr2.ident "q") (Expr2.resize 1 (Expr2.lit ⟨#[.l1]⟩))))
        none)))]

/-- Fixture 13 (`f13_sidx_write.sv`, finding 2): a SIGNED dynamic write index. `always_comb`
`t = 4'b0000; t[i] = 1'b1;`, `i <= 2'b11` at reset, then `if (en && t[3]) q <= q + 1`. ls-sv writes
`t[3]` (the counter); IEEE 1800 reads the index as -1, and the write has no effect. -/
def f13 : Design2 where
  name := "cnt"
  decls := #[{ name := "clk", width := 1, isInput := true },
             { name := "rst", width := 1, isInput := true },
             { name := "en", width := 1, isInput := true },
             { name := "q", width := 1, isOutput := true },
             { name := "t", width := 4 },
             { name := "i", width := 2, isSigned := true }]
  processes := #[Process2.alwaysComb
      (Stmt2.block #[Stmt2.blockingAssign (Lhs2.ident "t") (Expr2.lit (LVec.ofNat 4 0)),
        Stmt2.blockingAssign (Lhs2.index "t" (Expr2.ident "i") 1) (Expr2.lit ⟨#[.l1]⟩)]),
    Process2.alwaysFF "clk"
      (Stmt2.ifStmt (Expr2.ident "rst")
        (Stmt2.block #[Stmt2.nbaAssign (Lhs2.ident "q") (Expr2.lit ⟨#[.l0]⟩),
          Stmt2.nbaAssign (Lhs2.ident "i") (Expr2.lit (LVec.ofNat 2 3))])
        (some (Stmt2.ifStmt
          (Expr2.logical true (Expr2.ident "en") (Expr2.slice (Expr2.ident "t") 3 1))
          (Stmt2.nbaAssign (Lhs2.ident "q")
            (Expr2.binary .add (Expr2.ident "q") (Expr2.resize 1 (Expr2.lit ⟨#[.l1]⟩))))
          none)))]

/-- Fixture 14 (`f14_oob_write.sv`, finding 3): an UNSIGNED dynamic write index that leaves the
range. `always_comb` `t = 3'b000; t[k] = 1'b1;`, `k <= 2'd3` at reset, then
`if (en && t == 3'b000) q <= q + 1`. `t[3]` is out of range: the write has no effect (IEEE 1800
§11.5.1, ls-sv's `resolveLhs2`, Yosys), so `t = 0` and the counter counts. -/
def f14 : Design2 where
  name := "cnt"
  decls := #[{ name := "clk", width := 1, isInput := true },
             { name := "rst", width := 1, isInput := true },
             { name := "en", width := 1, isInput := true },
             { name := "q", width := 1, isOutput := true },
             { name := "t", width := 3 },
             { name := "k", width := 2 }]
  processes := #[Process2.alwaysComb
      (Stmt2.block #[Stmt2.blockingAssign (Lhs2.ident "t") (Expr2.lit (LVec.ofNat 3 0)),
        Stmt2.blockingAssign (Lhs2.index "t" (Expr2.ident "k") 1) (Expr2.lit ⟨#[.l1]⟩)]),
    Process2.alwaysFF "clk"
      (Stmt2.ifStmt (Expr2.ident "rst")
        (Stmt2.block #[Stmt2.nbaAssign (Lhs2.ident "q") (Expr2.lit ⟨#[.l0]⟩),
          Stmt2.nbaAssign (Lhs2.ident "k") (Expr2.lit (LVec.ofNat 2 3))])
        (some (Stmt2.ifStmt
          (Expr2.logical true (Expr2.ident "en")
            (Expr2.binary .eq (Expr2.ident "t") (Expr2.lit (LVec.ofNat 3 0))))
          (Stmt2.nbaAssign (Lhs2.ident "q")
            (Expr2.binary .add (Expr2.ident "q") (Expr2.resize 1 (Expr2.lit ⟨#[.l1]⟩))))
          none)))]

/-- Fixture 15 (`f15_cast_idx.sv`, finding 2): fixture 12 with `i` UNSIGNED and read through
`m[$signed(i)]`. IEEE 1800 gives fixture 12's behaviour (the index is -1); ls-sv's lowering drops
the cast, so the loaded design is fixture 12 with `i` declared unsigned. -/
def f15 : Design2 :=
  { f12 with decls := #[{ name := "clk", width := 1, isInput := true },
                        { name := "rst", width := 1, isInput := true },
                        { name := "en", width := 1, isInput := true },
                        { name := "q", width := 1, isOutput := true },
                        { name := "m", width := 4 },
                        { name := "i", width := 2 }] }

/-- Fixture 16 (`f16_ctx_width.sv`, finding 1) at `N = 2`: `a <= 1; b <= 1` at reset, then
`if (en) q <= q + ((a + b) >> 1)`. The context width (2) reaches the operands of `>>` (IEEE 1800
§11.6.1): `(1 + 1) >> 1 = 1`, the counter. -/
def f16 : Design2 where
  name := "cnt"
  decls := #[{ name := "clk", width := 1, isInput := true },
             { name := "rst", width := 1, isInput := true },
             { name := "en", width := 1, isInput := true },
             { name := "q", width := 2, isOutput := true },
             { name := "a", width := 1 },
             { name := "b", width := 1 }]
  processes := #[Process2.alwaysFF "clk"
    (Stmt2.ifStmt (Expr2.ident "rst")
      (Stmt2.block #[Stmt2.nbaAssign (Lhs2.ident "q") (Expr2.lit (LVec.ofNat 2 0)),
        Stmt2.nbaAssign (Lhs2.ident "a") (Expr2.lit ⟨#[.l1]⟩),
        Stmt2.nbaAssign (Lhs2.ident "b") (Expr2.lit ⟨#[.l1]⟩)])
      (some (Stmt2.ifStmt (Expr2.ident "en")
        (Stmt2.nbaAssign (Lhs2.ident "q")
          (Expr2.binary .add (Expr2.ident "q")
            (Expr2.binary (.shr false)
              (Expr2.binary .add (Expr2.resize 2 (Expr2.ident "a")) (Expr2.resize 2 (Expr2.ident "b")))
              (Expr2.lit (LVec.ofNat 32 1)))))
        none)))]

/-- Fixture 16 at `N = 1`: the context is 1 bit, so `1 + 1` wraps to 0 and `q` holds (as in IEEE
1800: Icarus holds `q` at `N = 1`). -/
def f16n1 : Design2 where
  name := "cnt"
  decls := #[{ name := "clk", width := 1, isInput := true },
             { name := "rst", width := 1, isInput := true },
             { name := "en", width := 1, isInput := true },
             { name := "q", width := 1, isOutput := true },
             { name := "a", width := 1 },
             { name := "b", width := 1 }]
  processes := #[Process2.alwaysFF "clk"
    (Stmt2.ifStmt (Expr2.ident "rst")
      (Stmt2.block #[Stmt2.nbaAssign (Lhs2.ident "q") (Expr2.lit ⟨#[.l0]⟩),
        Stmt2.nbaAssign (Lhs2.ident "a") (Expr2.lit ⟨#[.l1]⟩),
        Stmt2.nbaAssign (Lhs2.ident "b") (Expr2.lit ⟨#[.l1]⟩)])
      (some (Stmt2.ifStmt (Expr2.ident "en")
        (Stmt2.nbaAssign (Lhs2.ident "q")
          (Expr2.binary .add (Expr2.ident "q")
            (Expr2.binary (.shr false) (Expr2.binary .add (Expr2.ident "a") (Expr2.ident "b"))
              (Expr2.lit (LVec.ofNat 32 1)))))
        none)))]

/-! ## Bounded evidence: every power-up state, every stimulus of a length -/

/-- The counter's `q` after each entry of `es` from entry 0 (a reset first), at width `N`. -/
def cntSpecQ (N : Nat) : List (Nat × Nat) → Nat → List Nat
  | [], _ => []
  | (r, e) :: es, q =>
      let q' := if r == 1 then 0 else if e == 1 then (q + 1) % 2 ^ N else q
      q' :: cntSpecQ N es q'

/-- The counter's claim on one run, decided: every snapshot shows the counter's `q`. -/
def cntClaimB (N : Nat) (es : List (Nat × Nat)) (tr : List SvState) : Bool :=
  tr.length == es.length &&
    ((cntSpecQ N es 0).zipIdx.all fun (q, j) => qAt tr j == some (LVec.ofNat N q))

/-- Every stimulus of `L` entries over `rst`, `en` whose first entry is a reset. -/
def allStims : Nat → List (List (Nat × Nat))
  | 0 => [[]]
  | L + 1 => [(1, 0), (1, 1)].flatMap fun x => (tails L).map (x :: ·)
where
  tails : Nat → List (List (Nat × Nat))
    | 0 => [[]]
    | n + 1 => [(0, 0), (0, 1), (1, 0), (1, 1)].flatMap fun x => (tails n).map (x :: ·)

/-- The trace under the reverse schedule. -/
def trAtRev (d : Design2) (st0 : SvState) (stim : List SvState) : List SvState :=
  ((run2At d σ_rev 64 st0 stim).toOption).getD []

/-- **Rule 2 on a bounded family of runs, decided**: from every power-up state (`powerUps`, every
one by `mem_powerUps`), on every stimulus of `L` entries over `rst`, `en` starting with a reset,
under both schedules, every snapshot shows the counter's `q`. -/
def boundedPU (d : Design2) (N L : Nat) : Bool :=
  (powerUps d).all fun st0 => (allStims L).all fun es =>
    let stim := es.map fun x => entry x.1 x.2
    cntClaimB N es (trAt d st0 stim) && cntClaimB N es (trAtRev d st0 stim)

/-- **Rule 2 on one stimulus, decided**: from every power-up state (every one is enumerated:
`mem_powerUps`), the run on `es` (a reset first) shows the counter in every snapshot. -/
def puRun (d : Design2) (N : Nat) (es : List (Nat × Nat)) : Bool :=
  (powerUps d).all fun st0 => cntClaimB N es (trAt d st0 (es.map fun x => entry x.1 x.2))

/-- Reset, count twice, hold, reset while `en` is high, count: the run of `Refute.lean`'s round 1. -/
def stimA : List (Nat × Nat) := [(1, 0), (0, 1), (0, 1), (0, 0), (1, 1), (0, 1)]

/-- The same family under txtask-v1's run (ls-sv's own start state). -/
def boundedInit (d : Design2) (N L : Nat) : Bool :=
  (allStims L).all fun es =>
    let stim := es.map fun x => entry x.1 x.2
    cntClaimB N es (trOf d stim)

/-! ## Rejections by rule 2: one power-up state, one stimulus -/

/-- **Fixture 2 (W1) fails v2**: from the power-up state `u = 0` (every bit 0), `t = u = 0` makes
`lo = 1` before `t = 0` overwrites it, and the counter saturates: after `reset; en; en` it shows
`q = 1` where the counter wrapped to 0. -/
theorem f2_refuted : ¬ cntTask.SatisfiedAtV2 1 f2 := fun h =>
  cnt_not_followsPU (d := f2) (st0 := zeros f2) (stim := stimH3.map fun x => entry x.1 x.2)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (ps := psOf stimH3) rfl
    (drives_entries stimH3 (by decide)) (j := 2) (a := (0#1, (1#1, ()))) rfl (by decide +kernel)
    h.2.2.1

/-- **Fixture 6 (W3) fails v2** at `N = 2`: from the power-up state `q = 2, p = 0`, the reset sets
`g = 1`, and the next `en` counts by 2: `q = 2` where the counter is at 1. -/
theorem f6_refuted : ¬ cntTask.SatisfiedAtV2 2 f6 := fun h =>
  cnt_not_followsPU (d := f6) (st0 := pu f6 "q" 2) (stim := stimH.map fun x => entry x.1 x.2)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (ps := psOf stimH) rfl
    (drives_entries stimH (by decide)) (j := 1) (a := (1#2, (1#1, ()))) rfl (by decide +kernel)
    h.2.2.1

/-- **Fixture 7 fails v2**: from the power-up state `u = 1` of the never-reset 2-state register,
`else if (u) q <= '0` holds `q` at 0 (ls-sv's `initState2` starts `u` at 0, the standard's 2-state
initial value, and the counter runs: v1 admits it). -/
theorem f7_refuted : ¬ cntTask.SatisfiedAtV2 1 f7 := fun h =>
  cnt_not_followsPU (d := f7) (st0 := pu f7 "u" 1) (stim := stimH.map fun x => entry x.1 x.2)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (ps := psOf stimH) rfl
    (drives_entries stimH (by decide)) (j := 1) (a := (1#1, (1#1, ()))) rfl (by decide +kernel)
    h.2.2.1

/-- **Fixture 8 fails v2**: from the power-up state `s = 1`, the case takes its `1'b1` arm and holds
`q` at 0 (from v1's x start `s = x` matches no item and the default counts: v1 admits it). -/
theorem f8_refuted : ¬ cntTask.SatisfiedAtV2 1 f8 := fun h =>
  cnt_not_followsPU (d := f8) (st0 := pu f8 "s" 1) (stim := stimH.map fun x => entry x.1 x.2)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (ps := psOf stimH) rfl
    (drives_entries stimH (by decide)) (j := 1) (a := (1#1, (1#1, ()))) rfl (by decide +kernel)
    h.2.2.1

/-! ## Rejections by rule 3 -/

theorem f3_not_xsafe : ¬ XSafe f3 := by decide +kernel
theorem f9_not_xsafe : ¬ XSafe f9 := by decide +kernel
theorem f10a_not_xsafe : ¬ XSafe f10a := by decide +kernel

/-- **Fixture 3 (W2) fails v2**: `d / d` divides by a signal. -/
theorem f3_refuted : ¬ cntTask.SatisfiedAtV2 1 f3 := fun h => f3_not_xsafe h.2.2.2.2

/-- **Fixture 9 fails v2**: `1'bx` is an `x` literal outside a `casez`/`casex` pattern. -/
theorem f9_refuted : ¬ cntTask.SatisfiedAtV2 1 f9 := fun h => f9_not_xsafe h.2.2.2.2

/-- **Fixture 10a fails v2**: the 2-bit index `i` can address bit 3 of the 3-bit `a`. -/
theorem f10a_refuted : ¬ cntTask.SatisfiedAtV2 1 f10a := fun h => f10a_not_xsafe h.2.2.2.2

-- rule 2 alone passes all three: the x is made inside the run (0/0, `a[3]`) or tested against a
-- literal (`s === 1'bx` is 0 for every known `s`), and ls-sv's x-optimistic branch is the counter's
#guard boundedPU f3 1 3 && boundedPU f9 1 3 && boundedPU f10a 1 2

/-! ## Acceptances: rules 1 and 3 in the kernel, rule 2 on a bounded family of runs -/

theorem f0_xsafe : XSafe f0 := by decide +kernel
theorem f1_xsafe : XSafe f1 := by decide +kernel
theorem f4_xsafe : XSafe f4 := by decide +kernel
theorem f5_xsafe : XSafe f5 := by decide +kernel
theorem f10b_xsafe : XSafe f10b := by decide +kernel

theorem f0_moore : MooreOutDep f0 [] := MooreOutDep.of_check (by decide +kernel)
theorem f1_moore : MooreOutDep f1 [] := MooreOutDep.of_check (by decide +kernel)
theorem f4_moore : MooreOutDep f4 [] := MooreOutDep.of_check (by decide +kernel)
theorem f5_moore : MooreOutDep f5 [] := MooreOutDep.of_check (by decide +kernel)
theorem f10b_moore : MooreOutDep f10b [] := MooreOutDep.of_check (by decide +kernel)

/-- **Rule 2 on the fixture's run**: `puRun` holds exactly when the run on `es` from EVERY power-up
state shows the counter. -/
theorem puRun_spec {d : Design2} {N : Nat} {es : List (Nat × Nat)} (h : puRun d N es = true) :
    ∀ st0, PowerUp d st0 → cntClaimB N es (trAt d st0 (es.map fun x => entry x.1 x.2)) = true :=
  fun st0 hpu => List.all_eq_true.mp h st0 (mem_powerUps hpu)

theorem f0_everyPU : puRun f0 1 stimA = true := by decide +kernel
theorem f1_everyPU : puRun f1 1 stimA = true := by decide +kernel
theorem f4_everyPU : puRun f4 1 stimA = true := by decide +kernel
theorem f5_everyPU : puRun f5 1 stimA = true := by decide +kernel

-- every stimulus of three entries, both schedules, every power-up state (interpreted evaluation)
#guard boundedPU f0 1 3 && boundedPU f1 1 3 && boundedPU f4 1 3 && boundedPU f5 1 3
#guard boundedPU f10b 1 2
-- and the refuted fixtures fail the bounded check
#guard !boundedPU f2 1 3 && !boundedPU f6 2 2 && !boundedPU f7 1 2 && !boundedPU f8 1 2
-- the probe's twins too
#guard !boundedPU (h1x 1) 1 2 && !boundedPU (h1r 1) 1 3

/-! ## What txtask-v1's run (ls-sv's x start) says about the same fixtures -/

-- fixture 0 is x-pessimistic: from the x start `u ^ u` is x, so is `q`: v1 REJECTS it
#guard !boundedInit f0 1 2
-- fixtures 2, 7, 8 and the twins pass v1's run (x-optimism, the 2-state 0 start, an x subject
-- falling to the default); fixture 9's `s === 1'bx` is 1 at the x start, so v1 rejects it
#guard boundedInit f2 1 3 && boundedInit f7 1 3 && boundedInit f8 1 3
#guard boundedInit (h1x 1) 1 3 && boundedInit (h1r 1) 1 3
#guard !boundedInit f9 1 2
-- fixture 6 (W3) passes v1's run: the x start never makes `q - p == 2` true
#guard boundedInit f6 2 3
-- fixtures 3 and 10a pass v1's run too (0/0 and `a[3]` are x, and the x-optimistic branch counts);
-- the accepted fixtures 1, 4, 5, 10b pass it as well
#guard boundedInit f3 1 3 && boundedInit f10a 1 3
#guard boundedInit f1 1 3 && boundedInit f4 1 3 && boundedInit f5 1 3 && boundedInit f10b 1 3

/-! ## Fixture 11: `unique case` (round 1's W4), a dependency on ls-sv

ls-sv validates a `unique`/`priority` case on the snapshots (`validateTraceChecks2`), not where the
case executes. W4 violates the `unique` claim only in the state its edge reads, so the run completes
and v2 sees nothing: the verdict depends on ls-sv's fix (reported to the ls-sv lane). With the
fix the violating run would end loud, no run would complete on that stimulus, and `TerminatesPU`
would fail. The source gate refuses the qualifiers today (MEASURED: "`unique` qualifier"). -/

def stimU : List SvState := [entry 1 0, entry 0 0, entry 0 1, entry 0 1, entry 0 0]

-- the run from the zero power-up completes, under both schedules
#guard (run2At u4 σ_src 64 (zeros u4) stimU).toOption.isSome &&
  (run2At u4 σ_rev 64 (zeros u4) stimU).toOption.isSome
-- and the state the edge of entry 2 reads (snapshot 1 with entry 2 applied: an FF-only design has
-- no comb process) violates the `unique` claim
#guard match (trAt u4 (zeros u4) stimU)[1]?, stimU[2]? with
  | some prev, some e =>
      match validateProcessChecks2 64 (applyInputs2 u4 e prev) u4.processes.toList with
      | .unsupported m => m == "CaseCheck:unique"
      | _ => false
  | _, _ => false

/-! ## Fixtures 12 to 16 (the attack on revision 2)

Rule 3's dynamic-index clause now asks for an unsigned index (`unsignedIdx`). Revision 2's rule 3
admitted fixtures 12 and 13 (MEASURED, `xsafeB` true on the loaded designs before the change), and
rule 2 alone passes them: ls-sv's unsigned reading of `i` is the counter, which is exactly why they
must be refused (IEEE 1800, Icarus and the Yosys netlist hold `q` at 0, MEASURED). -/

theorem f12_not_xsafe : ¬ XSafe f12 := by decide +kernel
theorem f13_not_xsafe : ¬ XSafe f13 := by decide +kernel

/-- **Fixture 12 fails v2**: a signed dynamic read index. -/
theorem f12_refuted : ¬ cntTask.SatisfiedAtV2 1 f12 := fun h => f12_not_xsafe h.2.2.2.2

/-- **Fixture 13 fails v2**: a signed dynamic write index. -/
theorem f13_refuted : ¬ cntTask.SatisfiedAtV2 1 f13 := fun h => f13_not_xsafe h.2.2.2.2

-- rule 2 alone passes both (ls-sv's unsigned reading is the counter)
#guard boundedPU f12 1 2 && boundedPU f13 1 2

/-- Fixture 14 is ACCEPTED: an unsigned write index out of range writes nothing, in ls-sv and in
the standard, and rule 3 does not check a write index's range. -/
theorem f14_xsafe : XSafe f14 := by decide +kernel
theorem f14_moore : MooreOutDep f14 [] := MooreOutDep.of_check (by decide +kernel)
#guard boundedPU f14 1 2

/-- Fixture 15 is ACCEPTED by v2, wrongly: the loaded design is fixture 12 with `i` unsigned, which
the statement cannot tell from a correct design. The verdict depends on ls-sv's W5 fix (keep or
refuse the cast); the `fourstate` stage refuses the design today (rule (d), MEASURED). -/
theorem f15_xsafe : XSafe f15 := by decide +kernel
theorem f15_moore : MooreOutDep f15 [] := MooreOutDep.of_check (by decide +kernel)
#guard boundedPU f15 1 2

/-- Fixture 16 is ACCEPTED at `N = 2` (the context width reaches the operands of `>>`). -/
theorem f16_xsafe : XSafe f16 := by decide +kernel
theorem f16_moore : MooreOutDep f16 [] := MooreOutDep.of_check (by decide +kernel)
theorem f16_everyPU : puRun f16 2 stimA = true := by decide +kernel
#guard boundedPU f16 2 2

-- under txtask-v1's run (ls-sv's x start) fixtures 12 to 15 pass, and so does 16 at `N = 2`; 16 at
-- `N = 1` fails it (the 1-bit context, as in v2)
#guard boundedInit f12 1 3 && boundedInit f13 1 3 && boundedInit f14 1 3 && boundedInit f15 1 3
#guard boundedInit f16 2 3 && !boundedInit f16n1 1 2

/-- **Fixture 16 fails v2 at `N = 1`**, as it should: at a 1-bit context `1 + 1` is 0, and after
`reset; en` from the zero power-up `q` is 0 where the counter is at 1. -/
theorem f16n1_refuted : ¬ cntTask.SatisfiedAtV2 1 f16n1 := fun h =>
  cnt_not_followsPU (d := f16n1) (st0 := zeros f16n1) (stim := stimH.map fun x => entry x.1 x.2)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (ps := psOf stimH) rfl
    (drives_entries stimH (by decide)) (j := 1) (a := (1#1, (1#1, ()))) rfl (by decide +kernel)
    h.2.2.1

#print axioms f2_refuted
#print axioms f3_refuted
#print axioms f6_refuted
#print axioms f7_refuted
#print axioms f8_refuted
#print axioms f9_refuted
#print axioms f10a_refuted
#print axioms f0_xsafe
#print axioms f0_moore
#print axioms f0_everyPU
#print axioms puRun_spec
#print axioms f12_refuted
#print axioms f13_refuted
#print axioms f14_xsafe
#print axioms f15_xsafe
#print axioms f16_everyPU
#print axioms f16n1_refuted

end SvGolf.Tests.SeqCounter.Table
