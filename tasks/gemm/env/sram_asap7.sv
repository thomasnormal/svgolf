// The open ASAP7 SRAM catalogue (score/sram_asap7.json), behavioural models for simulation.
// Generated (check/explore.py `sram_models`); do not edit.

module srambank_64x4x16_6t122 (
  input  logic clk,
  input  logic [7:0] ADDRESS,
  input  logic [15:0] wd,
  input  logic banksel, read, write,
  output logic [15:0] dataout
);
  logic [15:0] mem [0:255];
  always @(posedge clk)
    if (banksel) begin
      if (read & write) $display("SRAM-RULE read and write in one cycle: %m");
      if (write) mem[ADDRESS] <= wd;
      else if (read) dataout <= mem[ADDRESS];
    end
endmodule

module srambank_64x4x18_6t122 (
  input  logic clk,
  input  logic [7:0] ADDRESS,
  input  logic [17:0] wd,
  input  logic banksel, read, write,
  output logic [17:0] dataout
);
  logic [17:0] mem [0:255];
  always @(posedge clk)
    if (banksel) begin
      if (read & write) $display("SRAM-RULE read and write in one cycle: %m");
      if (write) mem[ADDRESS] <= wd;
      else if (read) dataout <= mem[ADDRESS];
    end
endmodule

module srambank_64x4x20_6t122 (
  input  logic clk,
  input  logic [7:0] ADDRESS,
  input  logic [19:0] wd,
  input  logic banksel, read, write,
  output logic [19:0] dataout
);
  logic [19:0] mem [0:255];
  always @(posedge clk)
    if (banksel) begin
      if (read & write) $display("SRAM-RULE read and write in one cycle: %m");
      if (write) mem[ADDRESS] <= wd;
      else if (read) dataout <= mem[ADDRESS];
    end
endmodule

module srambank_64x4x32_6t122 (
  input  logic clk,
  input  logic [7:0] ADDRESS,
  input  logic [31:0] wd,
  input  logic banksel, read, write,
  output logic [31:0] dataout
);
  logic [31:0] mem [0:255];
  always @(posedge clk)
    if (banksel) begin
      if (read & write) $display("SRAM-RULE read and write in one cycle: %m");
      if (write) mem[ADDRESS] <= wd;
      else if (read) dataout <= mem[ADDRESS];
    end
endmodule

module srambank_64x4x34_6t122 (
  input  logic clk,
  input  logic [7:0] ADDRESS,
  input  logic [33:0] wd,
  input  logic banksel, read, write,
  output logic [33:0] dataout
);
  logic [33:0] mem [0:255];
  always @(posedge clk)
    if (banksel) begin
      if (read & write) $display("SRAM-RULE read and write in one cycle: %m");
      if (write) mem[ADDRESS] <= wd;
      else if (read) dataout <= mem[ADDRESS];
    end
endmodule

module srambank_64x4x36_6t122 (
  input  logic clk,
  input  logic [7:0] ADDRESS,
  input  logic [35:0] wd,
  input  logic banksel, read, write,
  output logic [35:0] dataout
);
  logic [35:0] mem [0:255];
  always @(posedge clk)
    if (banksel) begin
      if (read & write) $display("SRAM-RULE read and write in one cycle: %m");
      if (write) mem[ADDRESS] <= wd;
      else if (read) dataout <= mem[ADDRESS];
    end
endmodule

module srambank_64x4x40_6t122 (
  input  logic clk,
  input  logic [7:0] ADDRESS,
  input  logic [39:0] wd,
  input  logic banksel, read, write,
  output logic [39:0] dataout
);
  logic [39:0] mem [0:255];
  always @(posedge clk)
    if (banksel) begin
      if (read & write) $display("SRAM-RULE read and write in one cycle: %m");
      if (write) mem[ADDRESS] <= wd;
      else if (read) dataout <= mem[ADDRESS];
    end
endmodule

module srambank_64x4x48_6t122 (
  input  logic clk,
  input  logic [7:0] ADDRESS,
  input  logic [47:0] wd,
  input  logic banksel, read, write,
  output logic [47:0] dataout
);
  logic [47:0] mem [0:255];
  always @(posedge clk)
    if (banksel) begin
      if (read & write) $display("SRAM-RULE read and write in one cycle: %m");
      if (write) mem[ADDRESS] <= wd;
      else if (read) dataout <= mem[ADDRESS];
    end
endmodule

module srambank_64x4x64_6t122 (
  input  logic clk,
  input  logic [7:0] ADDRESS,
  input  logic [63:0] wd,
  input  logic banksel, read, write,
  output logic [63:0] dataout
);
  logic [63:0] mem [0:255];
  always @(posedge clk)
    if (banksel) begin
      if (read & write) $display("SRAM-RULE read and write in one cycle: %m");
      if (write) mem[ADDRESS] <= wd;
      else if (read) dataout <= mem[ADDRESS];
    end
endmodule

module srambank_64x4x72_6t122 (
  input  logic clk,
  input  logic [7:0] ADDRESS,
  input  logic [71:0] wd,
  input  logic banksel, read, write,
  output logic [71:0] dataout
);
  logic [71:0] mem [0:255];
  always @(posedge clk)
    if (banksel) begin
      if (read & write) $display("SRAM-RULE read and write in one cycle: %m");
      if (write) mem[ADDRESS] <= wd;
      else if (read) dataout <= mem[ADDRESS];
    end
endmodule

module srambank_64x4x74_6t122 (
  input  logic clk,
  input  logic [7:0] ADDRESS,
  input  logic [73:0] wd,
  input  logic banksel, read, write,
  output logic [73:0] dataout
);
  logic [73:0] mem [0:255];
  always @(posedge clk)
    if (banksel) begin
      if (read & write) $display("SRAM-RULE read and write in one cycle: %m");
      if (write) mem[ADDRESS] <= wd;
      else if (read) dataout <= mem[ADDRESS];
    end
endmodule

module srambank_64x4x80_6t122 (
  input  logic clk,
  input  logic [7:0] ADDRESS,
  input  logic [79:0] wd,
  input  logic banksel, read, write,
  output logic [79:0] dataout
);
  logic [79:0] mem [0:255];
  always @(posedge clk)
    if (banksel) begin
      if (read & write) $display("SRAM-RULE read and write in one cycle: %m");
      if (write) mem[ADDRESS] <= wd;
      else if (read) dataout <= mem[ADDRESS];
    end
endmodule

module srambank_128x4x16_6t122 (
  input  logic clk,
  input  logic [8:0] ADDRESS,
  input  logic [15:0] wd,
  input  logic banksel, read, write,
  output logic [15:0] dataout
);
  logic [15:0] mem [0:511];
  always @(posedge clk)
    if (banksel) begin
      if (read & write) $display("SRAM-RULE read and write in one cycle: %m");
      if (write) mem[ADDRESS] <= wd;
      else if (read) dataout <= mem[ADDRESS];
    end
endmodule

module srambank_128x4x18_6t122 (
  input  logic clk,
  input  logic [8:0] ADDRESS,
  input  logic [17:0] wd,
  input  logic banksel, read, write,
  output logic [17:0] dataout
);
  logic [17:0] mem [0:511];
  always @(posedge clk)
    if (banksel) begin
      if (read & write) $display("SRAM-RULE read and write in one cycle: %m");
      if (write) mem[ADDRESS] <= wd;
      else if (read) dataout <= mem[ADDRESS];
    end
endmodule

module srambank_128x4x20_6t122 (
  input  logic clk,
  input  logic [8:0] ADDRESS,
  input  logic [19:0] wd,
  input  logic banksel, read, write,
  output logic [19:0] dataout
);
  logic [19:0] mem [0:511];
  always @(posedge clk)
    if (banksel) begin
      if (read & write) $display("SRAM-RULE read and write in one cycle: %m");
      if (write) mem[ADDRESS] <= wd;
      else if (read) dataout <= mem[ADDRESS];
    end
endmodule

module srambank_128x4x32_6t122 (
  input  logic clk,
  input  logic [8:0] ADDRESS,
  input  logic [31:0] wd,
  input  logic banksel, read, write,
  output logic [31:0] dataout
);
  logic [31:0] mem [0:511];
  always @(posedge clk)
    if (banksel) begin
      if (read & write) $display("SRAM-RULE read and write in one cycle: %m");
      if (write) mem[ADDRESS] <= wd;
      else if (read) dataout <= mem[ADDRESS];
    end
endmodule

module srambank_128x4x34_6t122 (
  input  logic clk,
  input  logic [8:0] ADDRESS,
  input  logic [33:0] wd,
  input  logic banksel, read, write,
  output logic [33:0] dataout
);
  logic [33:0] mem [0:511];
  always @(posedge clk)
    if (banksel) begin
      if (read & write) $display("SRAM-RULE read and write in one cycle: %m");
      if (write) mem[ADDRESS] <= wd;
      else if (read) dataout <= mem[ADDRESS];
    end
endmodule

module srambank_128x4x36_6t122 (
  input  logic clk,
  input  logic [8:0] ADDRESS,
  input  logic [35:0] wd,
  input  logic banksel, read, write,
  output logic [35:0] dataout
);
  logic [35:0] mem [0:511];
  always @(posedge clk)
    if (banksel) begin
      if (read & write) $display("SRAM-RULE read and write in one cycle: %m");
      if (write) mem[ADDRESS] <= wd;
      else if (read) dataout <= mem[ADDRESS];
    end
endmodule

module srambank_128x4x40_6t122 (
  input  logic clk,
  input  logic [8:0] ADDRESS,
  input  logic [39:0] wd,
  input  logic banksel, read, write,
  output logic [39:0] dataout
);
  logic [39:0] mem [0:511];
  always @(posedge clk)
    if (banksel) begin
      if (read & write) $display("SRAM-RULE read and write in one cycle: %m");
      if (write) mem[ADDRESS] <= wd;
      else if (read) dataout <= mem[ADDRESS];
    end
endmodule

module srambank_128x4x48_6t122 (
  input  logic clk,
  input  logic [8:0] ADDRESS,
  input  logic [47:0] wd,
  input  logic banksel, read, write,
  output logic [47:0] dataout
);
  logic [47:0] mem [0:511];
  always @(posedge clk)
    if (banksel) begin
      if (read & write) $display("SRAM-RULE read and write in one cycle: %m");
      if (write) mem[ADDRESS] <= wd;
      else if (read) dataout <= mem[ADDRESS];
    end
endmodule

module srambank_128x4x64_6t122 (
  input  logic clk,
  input  logic [8:0] ADDRESS,
  input  logic [63:0] wd,
  input  logic banksel, read, write,
  output logic [63:0] dataout
);
  logic [63:0] mem [0:511];
  always @(posedge clk)
    if (banksel) begin
      if (read & write) $display("SRAM-RULE read and write in one cycle: %m");
      if (write) mem[ADDRESS] <= wd;
      else if (read) dataout <= mem[ADDRESS];
    end
endmodule

module srambank_128x4x72_6t122 (
  input  logic clk,
  input  logic [8:0] ADDRESS,
  input  logic [71:0] wd,
  input  logic banksel, read, write,
  output logic [71:0] dataout
);
  logic [71:0] mem [0:511];
  always @(posedge clk)
    if (banksel) begin
      if (read & write) $display("SRAM-RULE read and write in one cycle: %m");
      if (write) mem[ADDRESS] <= wd;
      else if (read) dataout <= mem[ADDRESS];
    end
endmodule

module srambank_128x4x74_6t122 (
  input  logic clk,
  input  logic [8:0] ADDRESS,
  input  logic [73:0] wd,
  input  logic banksel, read, write,
  output logic [73:0] dataout
);
  logic [73:0] mem [0:511];
  always @(posedge clk)
    if (banksel) begin
      if (read & write) $display("SRAM-RULE read and write in one cycle: %m");
      if (write) mem[ADDRESS] <= wd;
      else if (read) dataout <= mem[ADDRESS];
    end
endmodule

module srambank_128x4x80_6t122 (
  input  logic clk,
  input  logic [8:0] ADDRESS,
  input  logic [79:0] wd,
  input  logic banksel, read, write,
  output logic [79:0] dataout
);
  logic [79:0] mem [0:511];
  always @(posedge clk)
    if (banksel) begin
      if (read & write) $display("SRAM-RULE read and write in one cycle: %m");
      if (write) mem[ADDRESS] <= wd;
      else if (read) dataout <= mem[ADDRESS];
    end
endmodule

module srambank_256x4x16_6t122 (
  input  logic clk,
  input  logic [9:0] ADDRESS,
  input  logic [15:0] wd,
  input  logic banksel, read, write,
  output logic [15:0] dataout
);
  logic [15:0] mem [0:1023];
  always @(posedge clk)
    if (banksel) begin
      if (read & write) $display("SRAM-RULE read and write in one cycle: %m");
      if (write) mem[ADDRESS] <= wd;
      else if (read) dataout <= mem[ADDRESS];
    end
endmodule

module srambank_256x4x18_6t122 (
  input  logic clk,
  input  logic [9:0] ADDRESS,
  input  logic [17:0] wd,
  input  logic banksel, read, write,
  output logic [17:0] dataout
);
  logic [17:0] mem [0:1023];
  always @(posedge clk)
    if (banksel) begin
      if (read & write) $display("SRAM-RULE read and write in one cycle: %m");
      if (write) mem[ADDRESS] <= wd;
      else if (read) dataout <= mem[ADDRESS];
    end
endmodule

module srambank_256x4x20_6t122 (
  input  logic clk,
  input  logic [9:0] ADDRESS,
  input  logic [19:0] wd,
  input  logic banksel, read, write,
  output logic [19:0] dataout
);
  logic [19:0] mem [0:1023];
  always @(posedge clk)
    if (banksel) begin
      if (read & write) $display("SRAM-RULE read and write in one cycle: %m");
      if (write) mem[ADDRESS] <= wd;
      else if (read) dataout <= mem[ADDRESS];
    end
endmodule

module srambank_256x4x32_6t122 (
  input  logic clk,
  input  logic [9:0] ADDRESS,
  input  logic [31:0] wd,
  input  logic banksel, read, write,
  output logic [31:0] dataout
);
  logic [31:0] mem [0:1023];
  always @(posedge clk)
    if (banksel) begin
      if (read & write) $display("SRAM-RULE read and write in one cycle: %m");
      if (write) mem[ADDRESS] <= wd;
      else if (read) dataout <= mem[ADDRESS];
    end
endmodule

module srambank_256x4x34_6t122 (
  input  logic clk,
  input  logic [9:0] ADDRESS,
  input  logic [33:0] wd,
  input  logic banksel, read, write,
  output logic [33:0] dataout
);
  logic [33:0] mem [0:1023];
  always @(posedge clk)
    if (banksel) begin
      if (read & write) $display("SRAM-RULE read and write in one cycle: %m");
      if (write) mem[ADDRESS] <= wd;
      else if (read) dataout <= mem[ADDRESS];
    end
endmodule

module srambank_256x4x36_6t122 (
  input  logic clk,
  input  logic [9:0] ADDRESS,
  input  logic [35:0] wd,
  input  logic banksel, read, write,
  output logic [35:0] dataout
);
  logic [35:0] mem [0:1023];
  always @(posedge clk)
    if (banksel) begin
      if (read & write) $display("SRAM-RULE read and write in one cycle: %m");
      if (write) mem[ADDRESS] <= wd;
      else if (read) dataout <= mem[ADDRESS];
    end
endmodule

module srambank_256x4x40_6t122 (
  input  logic clk,
  input  logic [9:0] ADDRESS,
  input  logic [39:0] wd,
  input  logic banksel, read, write,
  output logic [39:0] dataout
);
  logic [39:0] mem [0:1023];
  always @(posedge clk)
    if (banksel) begin
      if (read & write) $display("SRAM-RULE read and write in one cycle: %m");
      if (write) mem[ADDRESS] <= wd;
      else if (read) dataout <= mem[ADDRESS];
    end
endmodule

module srambank_256x4x48_6t122 (
  input  logic clk,
  input  logic [9:0] ADDRESS,
  input  logic [47:0] wd,
  input  logic banksel, read, write,
  output logic [47:0] dataout
);
  logic [47:0] mem [0:1023];
  always @(posedge clk)
    if (banksel) begin
      if (read & write) $display("SRAM-RULE read and write in one cycle: %m");
      if (write) mem[ADDRESS] <= wd;
      else if (read) dataout <= mem[ADDRESS];
    end
endmodule

module srambank_256x4x64_6t122 (
  input  logic clk,
  input  logic [9:0] ADDRESS,
  input  logic [63:0] wd,
  input  logic banksel, read, write,
  output logic [63:0] dataout
);
  logic [63:0] mem [0:1023];
  always @(posedge clk)
    if (banksel) begin
      if (read & write) $display("SRAM-RULE read and write in one cycle: %m");
      if (write) mem[ADDRESS] <= wd;
      else if (read) dataout <= mem[ADDRESS];
    end
endmodule

module srambank_256x4x72_6t122 (
  input  logic clk,
  input  logic [9:0] ADDRESS,
  input  logic [71:0] wd,
  input  logic banksel, read, write,
  output logic [71:0] dataout
);
  logic [71:0] mem [0:1023];
  always @(posedge clk)
    if (banksel) begin
      if (read & write) $display("SRAM-RULE read and write in one cycle: %m");
      if (write) mem[ADDRESS] <= wd;
      else if (read) dataout <= mem[ADDRESS];
    end
endmodule

module srambank_256x4x74_6t122 (
  input  logic clk,
  input  logic [9:0] ADDRESS,
  input  logic [73:0] wd,
  input  logic banksel, read, write,
  output logic [73:0] dataout
);
  logic [73:0] mem [0:1023];
  always @(posedge clk)
    if (banksel) begin
      if (read & write) $display("SRAM-RULE read and write in one cycle: %m");
      if (write) mem[ADDRESS] <= wd;
      else if (read) dataout <= mem[ADDRESS];
    end
endmodule

module srambank_256x4x80_6t122 (
  input  logic clk,
  input  logic [9:0] ADDRESS,
  input  logic [79:0] wd,
  input  logic banksel, read, write,
  output logic [79:0] dataout
);
  logic [79:0] mem [0:1023];
  always @(posedge clk)
    if (banksel) begin
      if (read & write) $display("SRAM-RULE read and write in one cycle: %m");
      if (write) mem[ADDRESS] <= wd;
      else if (read) dataout <= mem[ADDRESS];
    end
endmodule
