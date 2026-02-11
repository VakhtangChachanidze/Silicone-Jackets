import fp_types_pkg::*;

module fp_decoder_tb;

  logic        clk;
  logic        rst;
  logic [31:0] instr;

  logic [6:0]  fp_op;
  logic [4:0]  rs1;
  logic [4:0]  rs2;
  logic [4:0]  rs3;
  logic [4:0]  rd;
  logic signed [11:0] offset;
  logic        fp_read;
  logic        fp_write;
  logic        eff_read;
  logic        eff_write;
  logic [2:0]  rm;

  fp_decoder dut (
    .clk(clk),
    .rst(rst),
    .instr(instr),
    .fp_op(fp_op),
    .func(func),
    .fmt(fmt),
    .rs1(rs1),
    .rs2(rs2),
    .rs3(rs3),
    .rd(rd),
    .offset(offset),
    .fp_read(fp_read),
    .fp_write(fp_write),
    .eff_read(eff_read),
    .eff_write(eff_write),
    .int_read(int_read),
    .int_write(int_write),
    .rm(rm)
  );

  initial clk = 0;
  always #5 clk = ~clk;

  initial begin
    // Reset asserted high test case
    rst = 1'b1;
    instr = 32'd0;
    @(posedge clk);
    @(posedge clk);

    rst = 1'b0;

    logic [6:0]  TB_fp_op;
    logic [4:0]  TB_rs1;
    logic [4:0]  TB_rs2;
    logic [4:0]  TB_rs3;
    logic [4:0]  TB_rd;
    logic signed [11:0] TB_offset;
    logic        TB_fp_read;
    logic        TB_fp_write;
    logic        TB_eff_read;
    logic        TB_eff_write;
    logic [2:0]  TB_rm;

  end
endmodule