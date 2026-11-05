module t #(parameter int N = 16) (input logic [N-1:0] a, output logic [N-1:0] y);
  case (N)
    16: begin : n16
      assign y = ~a;
    end
    default: begin : nd
      assign y = a;
    end
  endcase
endmodule
