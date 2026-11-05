import sys
W = 32
def gen(mode):
    L = [f"module qr(input logic [31:0] a0, b0, c0, d0, output logic [31:0] a4, b4, c4, d4);"]
    sig = []
    def vec(n): sig.append(n); return n
    def add(x, y, n):
        vec(n); 
        if mode == "plus":
            L.append(f"  assign {n} = {x} + {y};"); return n
        L.append(f"  logic [32:0] {n}_c; assign {n}_c[0] = 1'b0;")
        L.append(f"  genvar {n}_i; generate for ({n}_i = 0; {n}_i < 32; {n}_i++) begin : g_{n}")
        L.append(f"    assign {n}[{n}_i] = {x}[{n}_i] ^ {y}[{n}_i] ^ {n}_c[{n}_i];")
        L.append(f"    assign {n}_c[{n}_i+1] = ({x}[{n}_i] & {y}[{n}_i]) | ({n}_c[{n}_i] & ({x}[{n}_i] ^ {y}[{n}_i]));")
        L.append(f"  end endgenerate")
        return n
    def rot(x, k): return f"{{{x}[{32-k-1}:0], {x}[31:{32-k}]}}"
    L.append("  logic [31:0] a1, a2, a3, b1, b2, b3, c1, c2, c3, d1, d2, d3, d1x, d2x, d3x, d4x, b1x, b2x, b3x, b4x;")
    add("a0", "b0", "a1")
    L.append("  assign d1x = d0 ^ a1;"); L.append(f"  assign d1 = {rot('d1x',16)};")
    add("c0", "d1", "c1")
    L.append("  assign b1x = b0 ^ c1;"); L.append(f"  assign b1 = {rot('b1x',12)};")
    add("a1", "b1", "a2")
    L.append("  assign d2x = d1 ^ a2;"); L.append(f"  assign d2 = {rot('d2x',8)};")
    add("c1", "d2", "c2")
    L.append("  assign b2x = b1 ^ c2;"); L.append(f"  assign b2 = {rot('b2x',7)};")
    L.append("  assign a4 = a2; assign b4 = b2; assign c4 = c2; assign d4 = d2;")
    L.append("endmodule")
    return "\n".join(L) + "\n"
open("qr_ripple.sv", "w").write(gen("ripple")); open("qr_plus.sv", "w").write(gen("plus"))
