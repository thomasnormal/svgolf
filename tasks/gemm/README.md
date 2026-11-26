# Task `gemm`: a streamed inference layer (exploration)

Build an accelerator for one neural-network layer beside an external read-only memory. A job is a layer applied to
a batch of activation vectors:

```
Y[i][b] = clamp( round( (sum_j W[i][j] * X[j][b]) * M >> s ) + zp, lo, hi )      0 <= i < N,  0 <= b < batch
```

`W` is an `N x N` matrix of signed 16-bit weights that the design reads from the memory in bursts. `X` arrives as
a stream of unsigned 16-bit activations, vector by vector. `Y`, unsigned 16-bit, leaves as a stream from the
design's own accumulators. The sums are exact for every weight matrix and every batch. The score is throughput
per area on ASAP7.

**Status: exploration, unproved entries.** The task has no trusted statement yet. Entries are checked by
simulation against [`oracle.py`](oracle.py) and shown on an exploration board, apart from the proved records of the
other tasks. A simulation shows less than a proof: [what the check does not show](#what-the-check-does-not-show).
[What a proof will have to show](#what-a-proof-will-have-to-show) describes the statement to come.

| file | what |
|---|---|
| [`task.json`](task.json) | kind `explore-stream`, the ports, the check points, the scored job |
| [`oracle.py`](oracle.py) | the software model: the arithmetic, the memory image, the stimulus, the protocol and result checks |
| [`env/tb.sv`](env/tb.sv) | the environment: the external memory, the activation source, the result sink |
| [`env/sram_asap7.sv`](env/sram_asap7.sv) | behavioural models of the SRAM catalogue blocks, for simulation |
| [`reference/par.sv`](reference/par.sv), [`par.json`](reference/par.json) | par: the plain classical array, and its declaration |
| `reference/<name>.sv`, `<name>.json` | the other reference entries (`task.json` lists them), each with its declaration |
| [`reference/gen.py`](reference/gen.py) | the generator of the reference designs (`gen_*.py` beside it: the designs that build on par) |

## The first entries

The board starts with five plain designs, published as they are: the classical array (par), the inner-product
form, and Strassen at one and two levels. Under this score the inner-product form leads: half the multipliers and a
shorter cell. The Strassen entries trail par. A level does save passes (11 % fewer cycles at one level, 20 % at two
on one array), but these designs pay more than that in area, in two places:

- **memory**: they hold the activation block sums in extra buffer banks and keep one accumulator group per result
  block, so the on-chip memory grows from 0.75 mm² in par to 1.65 at one level and 3.86 at two;
- **the cell**: the 17 x 17 and 18 x 18 products are written with a plain `*`, and the cell is 23 % and 35 %
  larger than par's 16 x 16 one.

As arithmetic on the board's figures, not a measurement: one level with par's memory would stand at about 1.03 x
par; with a cell that grows about 5 % per operand bit, about 1.13 x par; with both, about 0.95 x par. (A product
written as an unsigned core plus separate sign rows measured about 5 % per extra bit on this view, against about
14 % for the plain operator.) So the open moves are forming the block sums in the stream instead of storing them,
sharing accumulators between result blocks, and a cheaper wide product. The plain array has slack of its own: its
read-out pass idles the array, its result FIFO is flip-flops, and its accumulate add sets the period.

## The interface

```systemverilog
module gemm #(parameter int LGE = 7, parameter int LAT = 32) (
  input  logic                   clk, rst,
  input  logic                   job_valid,            // a job: the layer's size, batch and output stage
  input  logic [3:0]             job_lgn,              //   log2 N
  input  logic [15:0]            job_batch, job_mul,   //   the number of vectors; M
  input  logic [5:0]             job_shift,            //   s
  input  logic [15:0]            job_zp, job_lo, job_hi,
  input  logic                   rq_ready,             // the memory accepts a burst request
  input  logic                   rd_valid,             // a beat of the burst
  input  logic [16*(1<<LGE)-1:0] rd_data,
  input  logic                   x_valid,              // a beat of activations
  input  logic [16*(1<<LGE)-1:0] x_data,
  input  logic                   y_ready,              // the sink takes a result beat
  output logic                   job_ready,
  output logic                   rq_valid,             // a burst: rq_len beats from beat rq_addr
  output logic [31:0]            rq_addr,
  output logic [23:0]            rq_len,
  output logic                   rd_ready,
  output logic                   x_ready,
  output logic                   y_valid,              // a result beat and its position
  output logic [15:0]            y_vec,                //   the vector b
  output logic [4:0]             y_row,                //   the beat in the vector: rows y_row*E .. y_row*E + E - 1
  output logic [16*(1<<LGE)-1:0] y_data
);
```

`E = 2^LGE` entries make a beat (`16*E` bits; 128 entries, 2048 bits, at the scored `LGE = 7`); entry `k` is bits
`[16k+15:16k]`. On every channel a transfer happens in a cycle where valid and ready are both 1, and a sender
holds valid and its payload until then. Every output is a register.

- **Job.** `N = 2^job_lgn` with `E <= N <= 32*E` (128 to 4096 at the scored point), `1 <= batch`,
  `lo <= hi`. `round` is half up: `floor((sum*M + 2^(s-1)) / 2^s)` for `s >= 1`, `sum*M` for `s = 0`.
- **Memory.** It is addressed in beats and holds the job's weights in the entry's
  [declared layout](#the-memory-layout). Bursts are sequential: a request is accepted only when the previous
  burst has ended, the first beat is valid no earlier than `LAT` cycles after the request's transfer, and the later
  beats follow at full rate or slower. The image changes in the cycle after a job is accepted, and nothing of an
  earlier job stays.
- **Activations.** After its job is accepted, vector by vector, `N/E` beats per vector.
- **Results.** Every `(y_vec, y_row)` of a job exactly once, in any order, all of a job before any of the next.
  A result beat is `E` consecutive rows of one vector, whatever the design's own tile.
- **Timing.** The environment may pause any channel for any finite time and drives garbage on data lines whose
  valid is 0. The design starts from an arbitrary power-up state.
- **Data-independence.** The requests, every valid and ready the design drives and the result positions must not
  depend on weights or activations.

## What a design may use

- Any algorithm that gives the exact sums: the classical array, the inner-product form, Strassen at the top
  levels over a systolic array, several arrays, any tile and cell width.
- On-chip memory as flip-flops or as blocks of the open ASAP7 SRAM catalogue
  ([`score/sram_asap7.json`](../../score/sram_asap7.json): 36 blocks, 256 to 1024 words, 16 to 80 bits),
  instantiated by name with the ports `clk, ADDRESS, wd, banksel, read, write, dataout`. A block has one port and
  a one-cycle read; it must not be read and written in the same cycle. Its table area is counted.
- Run-time `/ % **` are banned, as in every task. Weights in a transformed basis, a reduced activation range and
  rounded block sums are not the task: the sums are exact.
- The design text must be legal at every `LGE` from 2 to 7 and every `LAT` from 1 to 64: the check runs it at
  small `LGE`. A `generate` on the parameters is allowed.

### The memory layout

Without a declaration the memory holds the matrix in `E x E` blocks, block after block (row-major over the
blocks), each block row-major, one block row per beat: block `(R, C)` starts at beat `(R*(N/E) + C)*E`.

An entry may declare another layout: a list of segments, each an exact integer combination of aligned square
blocks of the matrix (`sum_k c_k * W[block k]`), stored tile by tile at the width it needs. This is how a Strassen
design stores its weight-block sums at 17 or 18 bits. The format is `oracle.py`'s (`check_layout`, `image`). It
fixes the storage order (square blocks, tile after tile, the low 16 bits of a tile first), and a combination must
fit its declared width for every weight matrix; an order the format cannot express cannot be declared yet.

## Checking an entry

```bash
python3.12 check.py tasks/gemm design.sv --unproved --declare design.json
```

`design.json` is the entry's declaration: `{"cycles": "<formula>", "layout": null}`. `cycles` is the number of
cycles from one job's last result beat to the next job's, identical jobs back to back at nominal timing, as a
formula in `n`, `batch`, `e`, `lat` (integers, `+ - * // %`, `min`, `max`, `ceil_div`).

| stage | what it checks | at |
|---|---|---|
| source, extract, banlist, clocked_rules | the clocked tasks' source rules: one clock, synchronous reset, the ports, no banned operator | every check point |
| fourstate, the banlist's backstop | no value that can be `x`; no banned cell after elaboration | the small check points |
| hier | the [hierarchy rule](#scoring); every module synthesized once | the scored parameters |
| explore: results | every result beat once and right, requests inside the image, valid held, from random power-up states under random pauses; one job list has a job per shift 0 to 63 | every check point |
| explore: independence | the same run on data of another kind has the same schedule, cycle for cycle | every check point |
| explore: cycles | the declared formula equals the measured cycles per job | every check point |
| explore: the scored job | the scored job itself, twice back to back at nominal timing, with identity weights: every result right, and its measured cycles equal to the declared formula | the scored parameters |
| explore: netlist | the result runs on the gate netlist of the pinned passes, hierarchy kept as for the score | `LGE = 2, LAT = 3` |

The check points are `(LGE, LAT) = (2, 3), (2, 1), (3, 2)`, beats of 4 and 8 entries and layers of 4 to 128 rows,
and the scored parameters `(7, 32)` themselves. There the design text as it is scored runs short jobs (`N = 128`,
`256` and `4096`, one to three vectors) and then the scored job, `N = 4096` with a batch of 4096, twice. With
identity weights the reference's sums are the activations, so that job can be judged; its cycle count is measured,
and the declared formula must give the same number. `--no-score` leaves this run out.

## What the check does not show

No entry of this task is proved. The check is a simulation, and a wrong design can pass it:

- At the scored parameters, dense weights run only on short jobs; the scored job runs with identity weights. A
  design that is wrong only for dense weights on a large layer with a large batch passes.
- The stimulus is a fixed function of the task, the point and the seed, so a design can be fitted to it.
- Data-independence is checked on two data sets per run, not for every data set.
- The gate netlist is simulated at `LGE = 2` only. At the scored parameters the source text is simulated and the
  netlist is weighed.
- The composed period is not a routed one ([Scoring](#scoring) lists what it leaves out).

A proof closes the first four; a placed-and-routed score closes the last.

## Scoring

```
score = area x cycles x period        (lower is better; mm2*ms per job)
```

at the scored job `N = 4096`, `batch = 4096`, `LGE = 7`, `LAT = 32`, on the ASAP7 cells-only view. The score is
**composed** ([`score/hier.py`](../../score/hier.py)), because a design of this size cannot be flattened:

- **area**: every distinct module is synthesized once by the pinned passes, hierarchy kept; the area is the sum of
  instances times each module's own cells, plus the catalogue blocks at their table areas.
- **period**: the longest of the modules' own register-to-register periods at the scored parameters (each
  module alone, its child instances cut at their pins).
- **cycles**: the declared formula at the scored job.

The composition is meaningful because of the **hierarchy rule**: in every module below the top, each output is a
register output, a child instance's output or a module input passed through, and each input of a child instance is
driven by a register, a child output, a module input or a constant (the inputs of a catalogue block are exempt).
No combinational path then crosses a module boundary inside logic.

What the composed score leaves out: wires, the clock tree, the delay of nets that fan out across module
boundaries (their buffers are counted as area), the clock-to-output time of a register whose path continues in
another module (a module's inputs are timed from 0), and a catalogue block's own clock-to-output and setup times.
A placed-and-routed score of hardened blocks is the next stage.

## What a proof will have to show

The statement is not written yet. It will say, for every `LGE` and `LAT` in range, from every power-up state, for
every sequence of legal jobs and every legal timing of the environment, with the memory holding the declared
layout of each job's weights:

1. the result stream of every job is the reference's: each position once, with `oracle.py`'s value;
2. every requested beat lies in the job's image;
3. two runs that differ only in weights and activations show the same requests, valids, readys and result
   positions in every cycle;
4. every output is a register, and no construct creates an `x` from known operands.

An entry moves to a ranked board only with a kernel-checked proof of that statement.
