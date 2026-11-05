// H2 style S6: multi-cycle shift/subtract divider as a clocked FSM (cva6 serdiv / ibex / dawsonjon style).
module s6_fsm (
  input  logic        clk, rst_n, start,
  input  logic [10:0] n, d,
  output logic [12:0] qq,
  output logic        done
);
  typedef enum logic [1:0] {IDLE, RUN, DONE} st_e;
  st_e         st_q, st_d;
  logic [11:0] r_q, r_d;
  logic [12:0] q_q, q_d;
  logic [3:0]  cnt_q, cnt_d;
  always_comb begin
    st_d = st_q; r_d = r_q; q_d = q_q; cnt_d = cnt_q;
    unique case (st_q)
      IDLE: if (start) begin r_d = {1'b0, n}; q_d = '0; cnt_d = 4'd0; st_d = RUN; end
      RUN: begin
        q_d = {q_q[11:0], (r_q >= {1'b0, d})};
        r_d = (r_q >= {1'b0, d}) ? ((r_q - {1'b0, d}) << 1) : (r_q << 1);
        cnt_d = cnt_q + 4'd1;
        if (cnt_q == 4'd12) st_d = DONE;
      end
      default: st_d = IDLE;
    endcase
  end
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin st_q <= IDLE; r_q <= '0; q_q <= '0; cnt_q <= '0; end
    else begin st_q <= st_d; r_q <= r_d; q_q <= q_d; cnt_q <= cnt_d; end
  end
  assign qq = q_q;
  assign done = (st_q == DONE);
endmodule
