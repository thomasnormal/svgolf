/* asap7_a0_v1: the A0' netlist of module band after the repair (score/ppa.py, buffer_trees_v1): 0 buffers on 0 nets, 0 tie cells. */
module band(a, b, y);
  input [15:0] a;
  input [15:0] b;
  output [15:0] y;
  AND2x2_ASAP7_75t_R _00_ (.A(b[3]), .B(a[3]), .Y(y[3]));
  AND2x2_ASAP7_75t_R _01_ (.A(b[4]), .B(a[4]), .Y(y[4]));
  AND2x2_ASAP7_75t_R _02_ (.A(b[5]), .B(a[5]), .Y(y[5]));
  AND2x2_ASAP7_75t_R _03_ (.A(b[6]), .B(a[6]), .Y(y[6]));
  AND2x2_ASAP7_75t_R _04_ (.A(b[7]), .B(a[7]), .Y(y[7]));
  AND2x2_ASAP7_75t_R _05_ (.A(b[8]), .B(a[8]), .Y(y[8]));
  AND2x2_ASAP7_75t_R _06_ (.A(b[9]), .B(a[9]), .Y(y[9]));
  AND2x2_ASAP7_75t_R _07_ (.A(b[10]), .B(a[10]), .Y(y[10]));
  AND2x2_ASAP7_75t_R _08_ (.A(b[11]), .B(a[11]), .Y(y[11]));
  AND2x2_ASAP7_75t_R _09_ (.A(b[12]), .B(a[12]), .Y(y[12]));
  AND2x2_ASAP7_75t_R _10_ (.A(b[13]), .B(a[13]), .Y(y[13]));
  AND2x2_ASAP7_75t_R _11_ (.A(b[14]), .B(a[14]), .Y(y[14]));
  AND2x2_ASAP7_75t_R _12_ (.A(b[15]), .B(a[15]), .Y(y[15]));
  AND2x2_ASAP7_75t_R _13_ (.A(b[0]), .B(a[0]), .Y(y[0]));
  AND2x2_ASAP7_75t_R _14_ (.A(b[1]), .B(a[1]), .Y(y[1]));
  AND2x2_ASAP7_75t_R _15_ (.A(b[2]), .B(a[2]), .Y(y[2]));
endmodule
