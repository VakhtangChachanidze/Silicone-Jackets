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

  /*
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
  */
  
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
    instr = test_instr;
    @(posedge clk);

    check_outputs(test_name, exp);
    $display("%s PASSED", test_name);
  endtask

  initial begin
    // Reset asserted high test case
    
    begin
      fp_decoder_exp exp_RST;

      exp_RST.fp_op = FP_OP_FLW;
      exp_RST.func = FP_INSTR_NONE;
      exp_RST.fmt = 0;
      exp_RST.rs1 = 5'b11000;
      exp_RST.rs2 = 0;
      exp_RST.rs3 = 0;
      exp_RST.rd = 5'b10110;
      exp_RST.offset = 12'b110010010011;
      exp_RST.fp_read = 0;
      exp_RST.fp_write = 1;
      exp_RST.eff_read = 1;
      exp_RST.eff_write = 0;
      exp_RST.int_read = 0;
      exp_RST.int_write = 0;
      exp_RST.rm = 0;

      // An FLW instruction is inputed instead of an invalid one. 
      logic [31:0] instr_RST = {12'b110010010011, 5'b11000, 3'b000, 5'b10110, FP_OP_FLW};
      apply_instr_and_check("FLW", instr_FLW, exp_FLW);
    end

    repeat (5) @(posedge clk);

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

    repeat (5) @(posedge clk);

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

    repeat (5) @(posedge clk);

    // FMADD.S instruction

    begin
      fp_decoder_exp exp_FMADD;

      exp_FMADD.fp_op = FP_OP_FMADD;
      exp_FMADD.func = FP_INSTR_NONE;
      exp_FMADD.fmt = 0;
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

      logic [31:0] instr_FMADD = {exp_FMADD.rs3, exp_FMADD.fmt, exp_FMADD.rs2, exp_FMADD.rs1, exp_FMADD.rm, exp_FMADD.rd, exp_FMADD.fp_op};
      apply_instr_and_check("FMADD", instr_FMADD, exp_FMADD);
    end

    repeat (5) @(posedge clk);

    // FMSUB.S instruction

    begin
      fp_decoder_exp exp_FMSUB;

      exp_FMSUB.fp_op = FP_OP_FMSUB;
      exp_FMSUB.func = FP_INSTR_NONE;
      exp_FMSUB.fmt = 0;
      exp_FMSUB.rs1 = 5'b11000;
      exp_FMSUB.rs2 = 5'b10110;
      exp_FMSUB.rs3 = 5'b10010;
      exp_FMSUB.rd = 5'b101110;
      exp_FMSUB.offset = 0;
      exp_FMSUB.fp_read = 1;
      exp_FMSUB.fp_write = 1;
      exp_FMSUB.eff_read = 0;
      exp_FMSUB.eff_write = 0;
      exp_FMSUB.int_read = 0;
      exp_FMSUB.int_write = 0;
      exp_FMSUB.rm = 3'b000;

      logic [31:0] instr_FMSUB = {exp_FMSUB.rs3, exp_FMSUB.fmt, exp_FMSUB.rs2, exp_FMSUB.rs1, exp_FMSUB.rm, exp_FMSUB.rd, exp_FMSUB.fp_op};
      apply_instr_and_check("FMSUB", instr_FMSUB, exp_FMSUB);
    end

    repeat (5) @(posedge clk);

    // FNMSUB.S instruction

    begin
      fp_decoder_exp exp_FNMSUB;

      exp_FNMSUB.fp_op = FP_OP_FNMSUB;
      exp_FNMSUB.func = FP_INSTR_NONE;
      exp_FNMSUB.fmt = 0;
      exp_FNMSUB.rs1 = 5'b11000;
      exp_FNMSUB.rs2 = 5'b10110;
      exp_FNMSUB.rs3 = 5'b10010;
      exp_FNMSUB.rd = 5'b101110;
      exp_FNMSUB.offset = 0;
      exp_FNMSUB.fp_read = 1;
      exp_FNMSUB.fp_write = 1;
      exp_FNMSUB.eff_read = 0;
      exp_FNMSUB.eff_write = 0;
      exp_FNMSUB.int_read = 0;
      exp_FNMSUB.int_write = 0;
      exp_FNMSUB.rm = 3'b000;

      logic [31:0] instr_FNMSUB = {exp_FNMSUB.rs3, exp_FNMSUB.fmt, exp_FNMSUB.rs2, exp_FNMSUB.rs1, exp_FNMSUB.rm, exp_FNMSUB.rd, exp_FNMSUB.fp_op};
      apply_instr_and_check("FNMSUB", instr_FNMSUB, exp_FNMSUB);
    end

    repeat (5) @(posedge clk);

    // FNMADD.S instruction

    begin
      fp_decoder_exp exp_FNMADD;

      exp_FNMADD.fp_op = FP_OP_FNMADD;
      exp_FNMADD.func = FP_INSTR_NONE;
      exp_FNMADD.fmt = 0;
      exp_FNMADD.rs1 = 5'b11000;
      exp_FNMADD.rs2 = 5'b10110;
      exp_FNMADD.rs3 = 5'b10010;
      exp_FNMADD.rd = 5'b101110;
      exp_FNMADD.offset = 0;
      exp_FNMADD.fp_read = 1;
      exp_FNMADD.fp_write = 1;
      exp_FNMADD.eff_read = 0;
      exp_FNMADD.eff_write = 0;
      exp_FNMADD.int_read = 0;
      exp_FNMADD.int_write = 0;
      exp_FNMADD.rm = 3'b000;

      logic [31:0] instr_FNMADD = {exp_FNMADD.rs3, exp_FNMADD.fmt, exp_FNMADD.rs2, exp_FNMADD.rs1, exp_FNMADD.rm, exp_FNMADD.rd, exp_FNMADD.fp_op};
      apply_instr_and_check("FNMADD", instr_FNMADD, exp_FNMADD);
    end

    repeat (5) @(posedge clk);

    // FADD.S instruction

    begin
      fp_decoder_exp exp_FADD;

      exp_FADD.fp_op = FP_OP;
      exp_FADD.func = FP_INSTR_FADD;
      exp_FADD.fmt = 0;
      exp_FADD.rs1 = 5'b11000;
      exp_FADD.rs2 = 5'b10110;
      exp_FADD.rs3 = 0;
      exp_FADD.rd = 5'b101110;
      exp_FADD.offset = 0;
      exp_FADD.fp_read = 1;
      exp_FADD.fp_write = 1;
      exp_FADD.eff_read = 0;
      exp_FADD.eff_write = 0;
      exp_FADD.int_read = 0;
      exp_FADD.int_write = 0;
      exp_FADD.rm = 3'b000;

      logic [31:0] instr_FADD = {exp_FADD.func, exp_FADD.rs2, exp_FADD.rs1, exp_FADD.rm, exp_FADD.rd, exp_FADD.fp_op};
      apply_instr_and_check("FADD", instr_FADD, exp_FADD);
    end

    repeat (5) @(posedge clk);
    
    // FSUB.S instruction

    begin
      fp_decoder_exp exp_FSUB;

      exp_FSUB.fp_op = FP_OP;
      exp_FSUB.func = FP_INSTR_FSUB;
      exp_FSUB.fmt = 0;
      exp_FSUB.rs1 = 5'b11000;
      exp_FSUB.rs2 = 5'b10110;
      exp_FSUB.rs3 = 0;
      exp_FSUB.rd = 5'b101110;
      exp_FSUB.offset = 0;
      exp_FSUB.fp_read = 1;
      exp_FSUB.fp_write = 1;
      exp_FSUB.eff_read = 0;
      exp_FSUB.eff_write = 0;
      exp_FSUB.int_read = 0;
      exp_FSUB.int_write = 0;
      exp_FSUB.rm = 3'b000;

      logic [31:0] instr_FSUB = {exp_FSUB.func, exp_FSUB.rs2, exp_FSUB.rs1, exp_FSUB.rm, exp_FSUB.rd, exp_FSUB.fp_op};
      apply_instr_and_check("FSUB", instr_FSUB, exp_FSUB);
    end

    repeat (5) @(posedge clk);

    // FMUL.S instruction

    // FDIV.S instruction

    // FSQRT.S instruction


    // FSGNJ.S instruction

    begin
      fp_decoder_exp exp_FSGNJ;

      exp_FSGNJ.fp_op = FP_OP;
      exp_FSGNJ.func = FP_INSTR_FSGNJ;
      exp_FSGNJ.fmt = 0;
      exp_FSGNJ.rs1 = 5'b11000;
      exp_FSGNJ.rs2 = 5'b10110;
      exp_FSGNJ.rs3 = 0;
      exp_FSGNJ.rd = 5'b101110;
      exp_FSGNJ.offset = 0;
      exp_FSGNJ.fp_read = 1;
      exp_FSGNJ.fp_write = 1;
      exp_FSGNJ.eff_read = 0;
      exp_FSGNJ.eff_write = 0;
      exp_FSGNJ.int_read = 0;
      exp_FSGNJ.int_write = 0;
      exp_FSGNJ.rm = 3'b000;

      logic [31:0] instr_FSGNJ = {exp_FSGNJ.func, exp_FSGNJ.rs2, exp_FSGNJ.rs1, exp_FSGNJ.rm, exp_FSGNJ.rd, exp_FSGNJ.fp_op};
      apply_instr_and_check("FSGNJ", instr_FSGNJ, exp_FSGNJ);
    end

    repeat (5) @(posedge clk);

    // FSGNJN.S instruction

    begin
      fp_decoder_exp exp_FSGNJS;

      exp_FSGNJS.fp_op = FP_OP;
      exp_FSGNJS.func = FP_INSTR_FSGNJ;
      exp_FSGNJS.fmt = 0;
      exp_FSGNJS.rs1 = 5'b11000;
      exp_FSGNJS.rs2 = 5'b10110;
      exp_FSGNJS.rs3 = 0;
      exp_FSGNJS.rd = 5'b101110;
      exp_FSGNJS.offset = 0;
      exp_FSGNJS.fp_read = 1;
      exp_FSGNJS.fp_write = 1;
      exp_FSGNJS.eff_read = 0;
      exp_FSGNJS.eff_write = 0;
      exp_FSGNJS.int_read = 0;
      exp_FSGNJS.int_write = 0;
      exp_FSGNJS.rm = 3'b001;

      logic [31:0] instr_FSGNJS = {exp_FSGNJS.func, exp_FSGNJS.rs2, exp_FSGNJS.rs1, exp_FSGNJS.rm, exp_FSGNJS.rd, exp_FSGNJS.fp_op};
      apply_instr_and_check("FSGNJS", instr_FSGNJS, exp_FSGNJS);
    end

    repeat (5) @(posedge clk);

    // FSGNJX.S instruction
  
    // FMIN.S instruction

    begin
      fp_decoder_exp exp_FMIN;

      exp_FMIN.fp_op = FP_OP;
      exp_FMIN.func = FP_INSTR_FMINMAX;
      exp_FMIN.fmt = 0;
      exp_FMIN.rs1 = 5'b11000;
      exp_FMIN.rs2 = 5'b10110;
      exp_FMIN.rs3 = 0;
      exp_FMIN.rd = 5'b101110;
      exp_FMIN.offset = 0;
      exp_FMIN.fp_read = 1;
      exp_FMIN.fp_write = 1;
      exp_FMIN.eff_read = 0;
      exp_FMIN.eff_write = 0;
      exp_FMIN.int_read = 0;
      exp_FMIN.int_write = 0;
      exp_FMIN.rm = 3'b000;

      logic [31:0] instr_FMIN = {exp_FMIN.func, exp_FMIN.rs2, exp_FMIN.rs1, exp_FMIN.rm, exp_FMIN.rd, exp_FMIN.fp_op};
      apply_instr_and_check("FMIN", instr_FMIN, exp_FMIN);
    end

    repeat (5) @(posedge clk);

    // FMAX.S instruction

    begin
      fp_decoder_exp exp_FMAX;

      exp_FMAX.fp_op = FP_OP;
      exp_FMAX.func = FP_INSTR_FMINMAX;
      exp_FMAX.fmt = 0;
      exp_FMAX.rs1 = 5'b11000;
      exp_FMAX.rs2 = 5'b10110;
      exp_FMAX.rs3 = 0;
      exp_FMAX.rd = 5'b101110;
      exp_FMAX.offset = 0;
      exp_FMAX.fp_read = 1;
      exp_FMAX.fp_write = 1;
      exp_FMAX.eff_read = 0;
      exp_FMAX.eff_write = 0;
      exp_FMAX.int_read = 0;
      exp_FMAX.int_write = 0;
      exp_FMAX.rm = 3'b001;

      logic [31:0] instr_FMAX = {exp_FMAX.func, exp_FMAX.rs2, exp_FMAX.rs1, exp_FMAX.rm, exp_FMAX.rd, exp_FMAX.fp_op};
      apply_instr_and_check("FMAX", instr_FMAX, exp_FMAX);
    end

    repeat (5) @(posedge clk);

    // FCVT.W.S instruction

    begin
      fp_decoder_exp exp_FCVTWS;

      exp_FCVTWS.fp_op = FP_OP;
      exp_FCVTWS.func = FP_INSTR_FCVT_W;
      exp_FCVTWS.fmt = 0;
      exp_FCVTWS.rs1 = 5'b11000;
      exp_FCVTWS.rs2 = 5'b00000;
      exp_FCVTWS.rs3 = 0;
      exp_FCVTWS.rd = 5'b101110;
      exp_FCVTWS.offset = 0;
      exp_FCVTWS.fp_read = 1;
      exp_FCVTWS.fp_write = 0;
      exp_FCVTWS.eff_read = 0;
      exp_FCVTWS.eff_write = 0;
      exp_FCVTWS.int_read = 0;
      exp_FCVTWS.int_write = 1;
      exp_FCVTWS.rm = 3'b000;

      logic [31:0] instr_FCVTWS = {exp_FCVTWS.func, exp_FCVTWS.rs2, exp_FCVTWS.rs1, exp_FCVTWS.rm, exp_FCVTWS.rd, exp_FCVTWS.fp_op};
      apply_instr_and_check("FCVT", instr_FCVTWS, exp_FCVTWS);
    end

    repeat (5) @(posedge clk);

    // FCVT.WU.S instruction

    // FMV.X.W instruction

    begin
      fp_decoder_exp exp_FMVXW;

      exp_FMVXW.fp_op = FP_OP;
      exp_FMVXW.func = FP_INSTR_FMV_X_W;
      exp_FMVXW.fmt = 0;
      exp_FMVXW.rs1 = 5'b11000;
      exp_FMVXW.rs2 = 5'b00000;
      exp_FMVXW.rs3 = 0;
      exp_FMVXW.rd = 5'b101110;
      exp_FMVXW.offset = 0;
      exp_FMVXW.fp_read = 1;
      exp_FMVXW.fp_write = 0;
      exp_FMVXW.eff_read = 0;
      exp_FMVXW.eff_write = 0;
      exp_FMVXW.int_read = 0;
      exp_FMVXW.int_write = 1;
      exp_FMVXW.rm = 3'b000;

      logic [31:0] instr_FMVXW = {exp_FMVXW.func, exp_FMVXW.rs2, exp_FMVXW.rs1, exp_FMVXW.rm, exp_FMVXW.rd, exp_FMVXW.fp_op};
      apply_instr_and_check("FMIN", instr_FMVXW, exp_FMVXW);
    end

    repeat (5) @(posedge clk);

    // FEQ.S instruction

    // FLT.S instruction

    // FLE.S instruction

    // FCLASS.S instruction

    // FCVT.S.W instruction

    begin
      fp_decoder_exp exp_FCVTSW;

      exp_FCVTSW.fp_op = FP_OP;
      exp_FCVTSW.func = FP_INSTR_FCVT_S;
      exp_FCVTSW.fmt = 0;
      exp_FCVTSW.rs1 = 5'b11000;
      exp_FCVTSW.rs2 = 5'b00000;
      exp_FCVTSW.rs3 = 0;
      exp_FCVTSW.rd = 5'b101110;
      exp_FCVTSW.offset = 0;
      exp_FCVTSW.fp_read = 0;
      exp_FCVTSW.fp_write = 1;
      exp_FCVTSW.eff_read = 0;
      exp_FCVTSW.eff_write = 0;
      exp_FCVTSW.int_read = 1;
      exp_FCVTSW.int_write = 0;
      exp_FCVTSW.rm = 3'b000;

      logic [31:0] instr_FCVTSW = {exp_FCVTSW.func, exp_FCVTSW.rs2, exp_FCVTSW.rs1, exp_FCVTSW.rm, exp_FCVTSW.rd, exp_FCVTSW.fp_op};
      apply_instr_and_check("FCVTSW", instr_FCVTSW, exp_FCVTSW);
    end

    repeat (5) @(posedge clk);

    // FCVT.S.WU instruction

    // FMV.W.X instruction

    begin
      fp_decoder_exp exp_FMVWX;

      exp_FMVWX.fp_op = FP_OP;
      exp_FMVWX.func = FP_INSTR_FMV_W_X;
      exp_FMVWX.fmt = 0;
      exp_FMVWX.rs1 = 5'b11000;
      exp_FMVWX.rs2 = 5'b00000;
      exp_FMVWX.rs3 = 0;
      exp_FMVWX.rd = 5'b101110;
      exp_FMVWX.offset = 0;
      exp_FMVWX.fp_read = 0;
      exp_FMVWX.fp_write = 1;
      exp_FMVWX.eff_read = 0;
      exp_FMVWX.eff_write = 0;
      exp_FMVWX.int_read = 1;
      exp_FMVWX.int_write = 0;
      exp_FMVWX.rm = 3'b000;

      logic [31:0] instr_FMVWX = {exp_FMVWX.func, exp_FMVWX.rs2, exp_FMVWX.rs1, exp_FMVWX.rm, exp_FMVWX.rd, exp_FMVWX.fp_op};
      apply_instr_and_check("FMVWX", instr_FMVWX, exp_FMVWX);
    end

    repeat (5) @(posedge clk);

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