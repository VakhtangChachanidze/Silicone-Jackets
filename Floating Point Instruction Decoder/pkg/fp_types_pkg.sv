package fp_types_pkg;

  typedef enum logic [6:0] {
    FP_OP = 7'b1010011,
    FP_OP_NONE = 7'd0,
    FP_OP_FLW = 7'b0000111,
    FP_OP_FSW = 7'b0100111,
    FP_OP_FMADD = 7'b1000011,
    FP_OP_FMSUB = 7'b1000111,
    FP_OP_FNMSUB = 7'b1001011,
    FP_OP_FNMADD = 7'b1001111
  } fp_op_e;

  typedef enum logic [6:0] {
      FP_INSTR_FADD = 7'b0000000,
      FP_INSTR_FSUB = 7'b0000100,
      FP_INSTR_FMUL = 7'b0001000,
      FP_INSTR_FDIV = 7'b0001100,
      FP_INSTR_FSQRT = 7'b0101100,
      FP_INSTR_FSGNJ = 7'b0010000,
      FP_INSTR_FMINMAX = 7'b0010100,
      FP_INSTR_FCVT_W = 7'b1100000,
      FP_INSTR_FMV_X_W = 7'b1110000,
      FP_INSTR_COMPARE = 7'b1010000,
      //FP_INSTR_FCLASS = 7'b1110000,
      FP_INSTR_FCVT_S = 7'b1101000,
      FP_INSTR_FMV_W_X = 7'b1111000,
      //FP_INSTR_FCVT_L = 7'b1100000,
      FP_INSTR_NONE = 7'b1111111
  } instr;

  typedef struct packed {
    logic fp_read;
    logic fp_write;
    logic eff_read;
    logic eff_write;
  } fp_ctrl_s;

  typedef enum logic [2:0] {
    RM_RNE       = 3'b000,
    RM_RTZ       = 3'b001,
    RM_RDN       = 3'b010,
    RM_RUP       = 3'b011,
    RM_RMM       = 3'b100,
    RM_RSVD_101  = 3'b101,
    RM_RSVD_110  = 3'b110,
    RM_DYN       = 3'b111
  } rm_e;

endpackage