import fp_types_pkg::*;

module fp_decoder_tb;

  logic        clk;
  logic        rst;
  logic [31:0] instr;

  logic [6:0]  fp_op;
  logic [6:0]  func;
  logic [1:0]  fmt;
  logic [4:0]  rs1;
  logic [4:0]  rs2;
  logic [4:0]  rs3;
  logic [4:0]  rd;
  logic [11:0] offset;
  logic        fp_read;
  logic        fp_write;
  logic        eff_read;
  logic        eff_write;
  logic        int_read;
  logic        int_write;
  logic [2:0]  rm;

  typedef struct packed{
    logic [6:0]  fp_op;
    logic [6:0]  func;
    logic [1:0]  fmt;
    logic [4:0]  rs1;
    logic [4:0]  rs2;
    logic [4:0]  rs3;
    logic [4:0]  rd;
    logic [11:0] offset;
    logic        fp_read;
    logic        fp_write;
    logic        eff_read;
    logic        eff_write;
    logic        int_read;
    logic        int_write;
    logic [2:0]  rm;
  } fp_decoder_exp;

  FP_Instruction_Decoder dut (
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

  // Reset is synchronous in the DUT (sampled on posedge clk), so we check on posedge.
  property p_reset_nullifies_outputs;
    @(posedge clk)
      rst |-> (
        (fp_op     == FP_OP_NONE) &&
        (func      == FP_INSTR_NONE) &&
        (fmt       == 2'b00) &&
        (rs1       == 5'd0) &&
        (rs2       == 5'd0) &&
        (rs3       == 5'd0) &&
        (rd        == 5'd0) &&
        (offset    == 12'd0) &&
        (fp_read   == 1'b0) &&
        (fp_write  == 1'b0) &&
        (eff_read  == 1'b0) &&
        (eff_write == 1'b0) &&
        (int_read  == 1'b0) &&
        (int_write == 1'b0) &&
        (rm        == 3'b000)
      );
  endproperty

  a_reset_nullifies_outputs: assert property (p_reset_nullifies_outputs)
    else $fatal(1,
      "RESET CHECK FAILED: fp_op=%0h func=%0h fmt=%0h rs1=%0d rs2=%0d rs3=%0d rd=%0d offset=%0h fp_read=%0b fp_write=%0b eff_read=%0b eff_write=%0b int_read=%0b int_write=%0b rm=%0b",
      fp_op, func, fmt, rs1, rs2, rs3, rd, offset, fp_read, fp_write, eff_read, eff_write, int_read, int_write, rm);
  
  task automatic check_outputs(input string test_name, fp_decoder_exp exp);
    if (fp_op !== exp.fp_op) $fatal(1, "%s: fp_op exp=%0h got=%0h", test_name, exp.fp_op, fp_op);
    if (func !== exp.func) $fatal(1, "%s: func exp=%0h got=%0h", test_name, exp.func, func);
    if (fmt !== exp.fmt) $fatal(1, "%s: fmt exp=%0h got=%0h", test_name, exp.fmt, fmt);
    if (rs1 !== exp.rs1) $fatal(1, "%s: rs1 exp=%0h got=%0h", test_name, exp.rs1, rs1);
    if (rs2 !== exp.rs2) $fatal(1, "%s: rs2 exp=%0h got=%0h", test_name, exp.rs2, rs2);
    if (rs3 !== exp.rs3) $fatal(1, "%s: rs3 exp=%0h got=%0h", test_name, exp.rs3, rs3);
    if (rd !== exp.rd) $fatal(1, "%s: rd exp=%0h got=%0h", test_name, exp.rd, rd);
    if (offset !== exp.offset) $fatal(1, "%s: offset exp=%0h got=%0h", test_name, exp.offset, offset);
    if (fp_read !== exp.fp_read) $fatal(1, "%s: fp_read exp=%0h got=%0h", test_name, exp.fp_read, fp_read);
    if (fp_write !== exp.fp_write) $fatal(1, "%s: fp_write exp=%0h got=%0h", test_name, exp.fp_write, fp_write);
    if (eff_read !== exp.eff_read) $fatal(1, "%s: eff_read exp=%0h got=%0h", test_name, exp.eff_read, eff_read);
    if (eff_write !== exp.eff_write) $fatal(1, "%s: eff_write exp=%0h got=%0h", test_name, exp.eff_write, eff_write);
    if (int_read !== exp.int_read) $fatal(1, "%s: int_read exp=%0h got=%0h", test_name, exp.int_read, int_read);
    if (int_write !== exp.int_write) $fatal(1, "%s: int_write exp=%0h got=%0h", test_name, exp.int_write, int_write);
    if (rm !== exp.rm) $fatal(1, "%s: rm exp=%0h got=%0h", test_name, exp.rm, rm);
  endtask

  task automatic apply_instr_and_check(input string test_name, input logic [31:0] test_instr, input fp_decoder_exp exp);
    instr = instr_i;
    @(posedge clk);

    check_outputs(test_name, exp);
    $display("%s PASSED", test_name);
  endtask

  initial begin
    // Reset asserted high test case
    rst = 1'b1;
    instr = 32'hFFFF_FFFF;
    repeat (5) @(posedge clk);

    rst = 1'b0;
    instr = 32'd0;
    repeat (5) @(posedge clk);

    $display("Reset test passed.");

    // FLW instruction

    begin
      fp_decoder_exp exp_FLW;

      exp_FLW.fp_op = FP_OP_FLW;
      exp_FLW.func = FP_INSTR_NONE;
      exp_FLW.fmt = 0;
      exp_FLW.rs1 = 5'b11000;
      exp_FLW.rs2 = 0;
      exp_FLW.rs3 = 0;
      exp_FLW.rd = 5'b10110;
      exp_FLW.offset = 12'b110010010011;
      exp_FLW.fp_read = 0;
      exp_FLW.fp_write = 1;
      exp_FLW.eff_read = 1;
      exp_FLW.eff_write = 0;
      exp_FLW.int_read = 0;
      exp_FLW.int_write = 0;
      exp_FLW.rm = 0;

      logic [31:0] instr_FLW = {exp_FLW.offset, exp_FLW.rs1, 3'b000, exp_FLW.rd, exp_FLW.fp_op};
      apply_instr_and_check("FLW", instr_FLW, exp_FLW);
    end

    // FSW instruction

    begin
      fp_decoder_exp exp_FSW;

      exp_FSW.fp_op = FP_OP_FSW;
      exp_FSW.func = FP_INSTR_NONE;
      exp_FSW.fmt = 0;
      exp_FSW.rs1 = 5'b11000;
      exp_FSW.rs2 = 5'b10110;
      exp_FSW.rs3 = 0;
      exp_FSW.rd = 0;
      exp_FSW.offset = 12'b110010010011;
      exp_FSW.fp_read = 1;
      exp_FSW.fp_write = 0;
      exp_FSW.eff_read = 0;
      exp_FSW.eff_write = 1;
      exp_FSW.int_read = 0;
      exp_FSW.int_write = 0;
      exp_FSW.rm = 0;

      logic [31:0] instr_FSW = {exp_FSW.offset[11:5], exp_FSW.rs2, exp_FSW.rs1, 3'b000, exp_FSW.offset[4:0], exp_FSW.fp_op};
      apply_instr_and_check("FSW", instr_FSW, exp_FSW);
    end

    // FMADD.S instruction

    begin
      fp_decoder_exp exp_FMADD;

      exp_FMADD.fp_op = FP_OP_FMADD;
      exp_FMADD.func = FP_INSTR_NONE;
      exp_FMADD.fmt = 2'b00;
      exp_FMADD.rs1 = 5'b11000;
      exp_FMADD.rs2 = 5'b10110;
      exp_FMADD.rs3 = 5'b10010;
      exp_FMADD.rd = 5'b101110;
      exp_FMADD.offset = 0;
      exp_FMADD.fp_read = 1;
      exp_FMADD.fp_write = 1;
      exp_FMADD.eff_read = 0;
      exp_FMADD.eff_write = 0;
      exp_FMADD.int_read = 0;
      exp_FMADD.int_write = 0;
      exp_FMADD.rm = 3'b000;

      logic [31:0] instr_FMADD = {exp_FMADD.rs3, exo_FMADD.fmt, exp_FMADD.rs2, exp_FMADD.rs1, exp_FMADD.rm, exp_FMADD.rd, exp_FMADD.fp_op};
      apply_instr_and_check("FMADD", instr_FMADD, exp_FMADD);
    end

    // FMSUB.S instruction

    // FNMSUB.S instruction

    // FNMADD.S instruction

    // FADD.S instruction
    
    // FSUB.S instruction

    // FMUL.S instruction

    // FDIV.S instruction

    // FSQRT.S instruction

    // FSGNJN.S instruction

    // FSGNJX.S instruction
  
    // FMIN.S instruction

    // FMAX.S instruction

    // FCVT.W.S instruction

    // FCVT.WU.S instruction

    // FMV.X.W instruction

    // FEQ.S instruction

    // FLT.S instruction

    // FLE.S instruction

    // FCLASS.S instruction

    // FCVT.S.W instruction

    // FCVT.S.WU instruction

    // FMV.W.X instruction

    // FCVT.L.S instruction

    // FCVT.LU.S instruction

    // FCVT.S.L instruction

    // FCVT.S.LU instruction


  end
endmodule

/*
  fp_decoder_exp exp_FLW;

  exp_FLW.fp_op = FP_OP_NONE;
  exp_FLW.func = FP_INSTR_NONE;
  exp_FLW.fmt = 0;
  exp_FLW.rs1 = 0;
  exp_FLW.rs2 = 0;
  exp_FLW.rs3 = 0;
  exp_FLW.rd = 0;
  exp_FLW.offset = 0;
  exp_FLW.fp_read = 0;
  exp_FLW.fp_write = 0;
  exp_FLW.eff_read = 0;
  exp_FLW.eff_write = 0;
  exp_FLW.int_read = 0;
  exp_FLW.int_write = 0;
  exp_FLW.rm = 0;
*/