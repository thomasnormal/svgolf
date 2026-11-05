// WP-I probe: port-connection forms of a hierarchical design (positional, .*, .name, constants, concatenations,
// an unconnected output, a narrower expression, a narrower bare net, 1-bit expression actuals, an instance array,
// an output into a concatenation). Only the extractor reads it: the context-width and net-width refusals are Lean-side.
module addc (input logic [3:0] x, input logic [3:0] y, input logic ci, output logic [3:0] s, output logic co);
  assign {co, s} = x + y + ci;
endmodule
module fa1 (input logic a, b, cin, output logic s, cout);
  assign s = a ^ b ^ cin;
  assign cout = (a & b) | (cin & (a ^ b));
endmodule
module top (input logic [3:0] a, b, input logic cin, input logic [1:0] n2, output logic [3:0] s1, s2, s3, s4, s5, s6, output logic c1, c2, c3, c4, c5, c6, input logic p, q);
  logic [3:0] x, y;
  logic ci;
  logic [3:0] s;
  logic co;
  assign x = a; assign y = b; assign ci = cin;
  // positional
  addc u1 (a, b, cin, s1, c1);
  // implicit .* (names x, y, ci, s, co exist in the parent)
  addc u2 (.*);
  // implicit .name
  addc u3 (.x, .y, .ci, .s(s3), .co(c3));
  // constants and concatenation actuals; unconnected output
  addc u4 (.x(4'd5), .y({a[1:0], b[1:0]}), .ci(1'b1), .s(s4), .co());
  // expression actual narrower than its port: n2 + n2 (2-bit operands) into a 4-bit port => context width
  addc u5 (.x(n2 + n2), .y(b), .ci(cin), .s(s5), .co(c5));
  // a bare net actual (input port n2, 2 bits) narrower than the 4-bit net port => net width
  addc u6 (.x(n2), .y(b), .ci(cin), .s(s6), .co(c6));
  // 1-bit port with expression
  logic t1, t2;
  fa1 f1 (.a(p & q), .b(p | q), .cin(~p), .s(t1), .cout(t2));
  // instance array
  logic [1:0] sv2, cv2;
  fa1 fv [1:0] (.a(a[1:0]), .b(b[1:0]), .cin(2'b00), .s(sv2), .cout(cv2));
  // output of a child into a concatenation of two parent windows (4-bit port s into {t8a, t8b})
  logic [1:0] t8a, t8b;  logic c8;
  addc u8 (.x(a), .y(b), .ci(cin), .s({t8a, t8b}), .co(c8));
  // single-bit outputs into separate parent signals
  logic u7a, u7b;
  fa1 f7 (.a(p), .b(q), .cin(1'b0), .s(u7a), .cout(u7b));
  assign c2 = t1 ^ t2 ^ u7a ^ u7b ^ sv2[0] ^ cv2[1];
  assign c4 = co ^ c8 ^ t8a[0] ^ t8b[1];
endmodule
