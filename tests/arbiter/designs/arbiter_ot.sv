// Task `arbiter`: a round-robin arbiter adapted from a real-world design, the candidate for the task's
// real-world reference. NOT the goalpost yet (MEASURED 2026-11-05): ls-sv does not instantiate generate-local
// declarations (`GenerateDecl:Var`, `GenerateDecl:LocalParam`; LeanModels/Sv/Ingest2.lean `parseGenItem`), and
// the upstream tree declares ten variables and five localparams inside its generate blocks, so svgolf-eval
// stops at "unsupported process 'GenerateDecl:Var'" and check.py's design stage would refuse it. Hoisting them
// would rewrite the design to get past ls-sv; it waits for ls-sv instead. Validated by simulation
// (tests/arbiter/sim.py, designs/).
//
// PROVENANCE. lowRISC OpenTitan, https://github.com/lowRISC/opentitan, commit
// 0a6ff6855bd9c6489110df167501e4d5f5c9bdbd, file hw/ip/prim/rtl/prim_arbiter_tree.sv
// (sha256 cad891e0479a377896ecbcddaf6dd7d5b9aa6e5b18ba23654b61795fcf3083e1), Apache-2.0: the upstream notice
// is kept below, and the licence text ships beside this file, LICENSES/Apache-2.0.txt (tests/arbiter/designs/LICENSES/). This file is a
// modified version of that file (Apache-2.0, section 4b): the changes are listed here. Kept verbatim: the
// request/priority/select/mask trees, the generate structure (no loop unrolled), the grant and mask-update
// equations, the comments. CHANGES, each with its reason (1 to 4 are the admission probe's,
// svgolf/design/reactive/rtl-probe/, built by its scripts/adapt_C.py; 5 to 8 make it the task's module):
//  1. `include "prim_assert.sv"`, `ASSERT_INIT`, and the whole assertions section (the `ASSERT`/`ASSUME`/
//     `ASSERT_KNOWN` macros and the `ifdef FPV_ON` block) are removed: the source gate refuses every directive
//     and macro, and the extractor marks every assertion Unsupported. They are verification-only (no
//     synthesized logic); the task statement carries their content (mutual exclusion, grant implies request,
//     work conservation, fairness).
//  2. The asynchronous active-low reset `always_ff @(posedge clk_i or negedge rst_ni) if (!rst_ni)` becomes the
//     synchronous active-high `always_ff @(posedge clk) if (rst)`: the task's synchronous reset, the clocked
//     rules of the source gate (one event, posedge clk) and the pinned sequential flow (no async-reset flop).
//  3. The unpacked port `input [DW-1:0] data_i [N]` becomes the packed `[N-1:0][DW-1:0] data_i` (the selects
//     data_i[0], data_i[offset] are unchanged): the extractor refuses unpacked ports and the selects from them.
//  4. The two packed 2-D trees `idx_tree` and `data_tree` are declared at module scope instead of inside the
//     generate block `gen_normal_case` (same type, same name, same uses): the pinned Yosys 0.53
//     `read_verilog -sv` stops at an element access of a packed multidimensional array declared in a generate
//     block ("Failed to detect width of signal access"; svgolf/design/reactive/rtl-probe/yosys-repro/).
//  5. The module is the task's `arbiter` with the one parameter `N`; `DW = 1` and `EnDataPort = 0` become
//     localparams: the task has no data port (EnDataPort = 0 is the upstream's pure-arbiter configuration).
//  6. The ports are the task's `clk, rst, req, gnt` (clk_i, rst_i, req_i renamed: the clock is read by the
//     edge only, never copied, as the clock discipline requires); the other upstream ports are internal
//     signals driven as in normal operation: req_chk_i = 1, ready_i = 1 (the task has no backpressure),
//     data_i = 0 (no data port); idx_o, valid_o, data_o are internal and unused.
//  7. The upstream grant gnt_o is combinational in req (a Mealy output); the task observes Moore outputs, so
//     gnt_o leaves through one output register, reset to 0 (+N flops, one cycle of latency).
//  8. At N = 1 the two trees of change 4 are tied to 0 in the bypass branch (upstream they do not exist there;
//     undriven, they would be x, which the task's known-state clause refuses).
// Nothing else changed.
//
// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// N:1 arbiter module
//
// Verilog parameter
//   N:           Number of request ports
//   DW:          Data width
//   DataPort:    Set to 1 to enable the data port. Otherwise that port will be ignored.
//
// This is a tree implementation of a round robin arbiter. It has the same behavior as the PPC
// implementation in prim_arbiter_ppc, and also uses a prefix summing approach to determine the next
// request to be granted. The main difference with respect to the PPC arbiter is that the leading 1
// detection and the prefix summation are performed with a binary tree instead of a sequential loop.
// Also, if the data port is enabled, the data is muxed based on the local arbitration decisions  at
// each node of the arbiter tree. This means that the data can propagate through the tree
// simultaneously with the requests, instead of waiting for the arbitration to determine the winner
// index first. As a result, this design has a shorter critical path than other implementations,
// leading to better overall timing.
//
// Note that the currently winning request is held if the data sink is not ready. This behavior is
// required by some interconnect protocols (AXI, TL). The module contains an assertion that checks
// this behavior.
//
// Also, this module contains a request stability assertion that checks that requests stay asserted
// until they have been served. This assertion can be gated by driving the req_chk_i low. This is
// a non-functional input and does not affect the designs behavior.
//
// See also: prim_arbiter_ppc

module arbiter #(
  parameter int N   = 8,
  // svGolf change 5: DW and EnDataPort are fixed (the task has no data port)
  localparam int DW  = 1,

  // Configurations
  // EnDataPort: {0, 1}, if 0, input data will be ignored
  localparam bit EnDataPort = 0,

  // Derived parameters
  localparam int IdxW = $clog2(N)
) (
  // svGolf change 6: the task's ports (clk_i -> clk, rst_i -> rst, req_i -> req; gnt is change 7's)
  input  logic         clk, rst,
  input  logic [N-1:0] req,
  output logic [N-1:0] gnt
);

  // svGolf change 6: the other upstream ports are internal signals, driven as in normal operation
  logic                    req_chk_i; // Used for gating assertions. Drive to 1 during normal
                                      // operation.
  logic [N-1:0][DW-1:0]    data_i;
  logic        [ N-1:0]    gnt_o;
  logic        [IdxW-1:0]  idx_o;
  logic                    valid_o;
  logic        [DW-1:0]    data_o;
  logic                    ready_i;
  assign req_chk_i = 1'b1;
  assign data_i    = '0;
  assign ready_i   = 1'b1;

  // req_chk_i is used for gating assertions only.
  logic unused_req_chk;
  assign unused_req_chk = req_chk_i;

  // svGolf change 4: the two packed 2-D trees are declared here, not in gen_normal_case
  logic [2**(IdxW+1)-2:0][IdxW-1:0] idx_tree;
  logic [2**(IdxW+1)-2:0][DW-1:0]   data_tree;

  // this case is basically just a bypass
  if (N == 1) begin : gen_degenerate_case

    assign valid_o  = req[0];
    assign data_o   = data_i[0];
    assign gnt_o[0] = valid_o & ready_i;
    assign idx_o    = '0;
    // svGolf change 8: the two trees of change 4 are unused here: tied off
    assign idx_tree  = '0;
    assign data_tree = '0;

  end else begin : gen_normal_case

    // align to powers of 2 for simplicity
    // a full binary tree with N levels has 2**N + 2**N-1 nodes
    logic [2**(IdxW+1)-2:0]           req_tree;
    logic [2**(IdxW+1)-2:0]           prio_tree;
    logic [2**(IdxW+1)-2:0]           sel_tree;
    logic [2**(IdxW+1)-2:0]           mask_tree;
    logic [N-1:0]                     prio_mask_d, prio_mask_q;

    for (genvar level = 0; level < IdxW+1; level++) begin : gen_tree
      //
      // level+1   C0   C1   <- "Base1" points to the first node on "level+1",
      //            \  /         these nodes are the children of the nodes one level below
      // level       Pa      <- "Base0", points to the first node on "level",
      //                         these nodes are the parents of the nodes one level above
      //
      // hence we have the following indices for the Pa, C0, C1 nodes:
      // Pa = 2**level     - 1 + offset       = Base0 + offset
      // C0 = 2**(level+1) - 1 + 2*offset     = Base1 + 2*offset
      // C1 = 2**(level+1) - 1 + 2*offset + 1 = Base1 + 2*offset + 1
      //
      localparam int Base0 = (2**level)-1;
      localparam int Base1 = (2**(level+1))-1;

      for (genvar offset = 0; offset < 2**level; offset++) begin : gen_level
        localparam int Pa = Base0 + offset;
        localparam int C0 = Base1 + 2*offset;
        localparam int C1 = Base1 + 2*offset + 1;

        // this assigns the gated interrupt source signals, their
        // corresponding IDs and priorities to the tree leafs
        if (level == IdxW) begin : gen_leafs
          if (offset < N) begin : gen_assign
            // forward path (requests and data)
            // all requests inputs are assigned to the request tree
            assign req_tree[Pa]      = req[offset];
            // we basically split the incoming request vector into two halves with the following
            // priority assignment. the prio_mask_q register contains a prefix sum that has been
            // computed using the last winning index, and hence masks out all requests at offsets
            // lower or equal the previously granted index. hence, all higher indices are considered
            // first in the arbitration tree nodes below, before considering the lower indices.
            assign prio_tree[Pa]     = req[offset] & prio_mask_q[offset];
            // input for the index muxes (used to compute the winner index)
            assign idx_tree[Pa]      = offset;
            // input for the data muxes
            assign data_tree[Pa]     = data_i[offset];

            // backward path (grants and prefix sum)
            // grant if selected, ready and request asserted
            assign gnt_o[offset]       = req[offset] & sel_tree[Pa] & ready_i;
            // only update mask if there is a valid request
            assign prio_mask_d[offset] = (|req) ?
                                         mask_tree[Pa] | sel_tree[Pa] & ~ready_i :
                                         prio_mask_q[offset];
          end else begin : gen_tie_off
            // forward path
            assign req_tree[Pa]  = '0;
            assign prio_tree[Pa] = '0;
            assign idx_tree[Pa]  = '0;
            assign data_tree[Pa] = '0;
            logic unused_sigs;
            assign unused_sigs = ^{mask_tree[Pa],
                                   sel_tree[Pa]};
          end
        // this creates the node assignments
        end else begin : gen_nodes
          // local helper variable
          logic sel;

          // forward path (requests and data)
          // each node looks at its two children, and selects the one with higher priority
          assign sel = ~req_tree[C0] | ~prio_tree[C0] & prio_tree[C1];
          // propagate requests
          assign req_tree[Pa]  = req_tree[C0] | req_tree[C1];
          assign prio_tree[Pa] = prio_tree[C1] | prio_tree[C0];
          // data and index muxes
          // Note: these ternaries have triggered a synthesis bug in Vivado versions older
          // than 2020.2. If the problem resurfaces again, have a look at issue #1408.
          assign idx_tree[Pa]  = (sel) ? idx_tree[C1]  : idx_tree[C0];
          assign data_tree[Pa] = (sel) ? data_tree[C1] : data_tree[C0];

          // backward path (grants and prefix sum)
          // this propagates the selection index back and computes a hot one mask
          assign sel_tree[C0] = sel_tree[Pa] & ~sel;
          assign sel_tree[C1] = sel_tree[Pa] &  sel;
          // this performs a prefix sum for masking the input requests in the next cycle
          assign mask_tree[C0] = mask_tree[Pa];
          assign mask_tree[C1] = mask_tree[Pa] | sel_tree[C0];
        end
      end : gen_level
    end : gen_tree

    // the results can be found at the tree root
    if (EnDataPort) begin : gen_data_port
      assign data_o      = data_tree[0];
    end else begin : gen_no_dataport
      logic [DW-1:0] unused_data;
      assign unused_data = data_tree[0];
      assign data_o = '1;
    end

    // This index is unused.
    logic unused_prio_tree;
    assign unused_prio_tree = prio_tree[0];

    assign idx_o       = idx_tree[0];
    assign valid_o     = req_tree[0];

    // the select tree computes a hot one signal that indicates which request is currently selected
    assign sel_tree[0] = 1'b1;
    // the mask tree is basically a prefix sum of the hot one select signal computed above
    assign mask_tree[0] = 1'b0;

    always_ff @(posedge clk) begin : p_mask_reg
      if (rst) begin
        prio_mask_q <= '0;
      end else begin
        prio_mask_q <= prio_mask_d;
      end
    end
  end

  // svGolf change 7: the grant leaves through one output register (the task's Moore observation:
  // gnt_o is combinational in req, a Mealy output)
  always_ff @(posedge clk) begin : p_gnt_reg
    if (rst) begin
      gnt <= '0;
    end else begin
      gnt <= gnt_o;
    end
  end

endmodule : arbiter
