import fp_types_pkg::*;

module FP_Instruction_Decoder (
    input logic [31:0] instr,
    input logic clk,
    input logic rst,

    output logic [6:0] fp_op,
    output logic [6:0] func,
    output logic [1:0] fmt,
    output logic [4:0] rs1,
    output logic[4:0] rs2,
    output logic [4:0] rs3,
    output logic [4:0] rd,
    output logic [11:0] offset,
    output logic fp_read,
    output logic fp_write,
    output logic eff_read,
    output logic eff_write,
    output logic int_read,
    output logic int_write,
    output logic [2:0] rm
);
    always_ff @(posedge clk) begin
        if(rst) begin
            fp_op <= FP_OP_NONE;
            func <= FP_INSTR_NONE;
            fmt <= 0;
            rs1 <= 0;
            rs2 <= 0;
            rs3 <= 0;
            rd <= 0;
            offset <= 0;
            fp_read <= 0;
            fp_write <= 0;
            eff_read <= 0;
            eff_write <= 0;
            int_read <= 0;
            int_write <= 0;
            rm <= 0;
        end
        else begin
            fp_op <= FP_OP_NONE;
            func <= FP_INSTR_NONE;
            fmt <= 0;
            rs1 <= 0;
            rs2 <= 0;
            rs3 <= 0;
            rd <= 0;
            offset <= 0;
            fp_read <= 0;
            fp_write <= 0;
            eff_read <= 0;
            eff_write <= 0;
            int_read <= 0;
            int_write <= 0;
            rm <= 0;

            //Load and store instructions start here. Either read from the memory and written to fp, or read from fp and written to memory.

            if(instr[6:0] == FP_OP_FLW) begin
                offset <= instr[31:20];
                rs1 <= instr[19:15];
                rd <= instr[11:7];
                fp_op <= instr[6:0];
                fp_write <= 1;
                eff_read <= 1; 
            end

            if(instr[6:0] == FP_OP_FSW) begin
                offset <= {instr[31:25], instr[11:7]};
                rs1 <= instr[19:15];
                rs2 <= instr[24:20];
                fp_op <= instr[6:0];
                fp_read <= 1;
                eff_write <= 1;
            end

            //Load and store instructions end here.
            //Floating-point fused instructions start here. Read from three fp registers and written to a fp register.

            if(instr[6:0] == FP_OP_FMADD) begin
                rs1 <= instr[19:15];
                rs2 <= instr[24:20];
                rs3 <= instr[31:27];
                fmt <= 2'b00;
                rm <= instr[14:12];
                rd <= instr[11:7];
                fp_op <= instr[6:0];
                fp_read <= 1;
                fp_write <= 1;
            end

            if(instr[6:0] == FP_OP_FMSUB) begin
                rs1 <= instr[19:15];
                rs2 <= instr[24:20];
                rs3 <= instr[31:27];
                fmt <= 2'b00;
                rm <= instr[14:12];
                rd <= instr[11:7];
                fp_op <= instr[6:0];
                fp_read <= 1;
                fp_write <= 1;
            end

            if(instr[6:0] == FP_OP_FNMSUB) begin
                rs1 <= instr[19:15];
                rs2 <= instr[24:20];
                rs3 <= instr[31:27];
                fmt <= 2'b00;
                rm <= instr[14:12];
                rd <= instr[11:7];
                fp_op <= instr[6:0];
                fp_read <= 1;
                fp_write <= 1;
            end

            if(instr[6:0] == FP_OP_FNMADD) begin
                rs1 <= instr[19:15];
                rs2 <= instr[24:20];
                rs3 <= instr[31:27];
                fmt <= 2'b00;
                rm <= instr[14:12];
                rd <= instr[11:7];
                fp_op <= instr[6:0];
                fp_read <= 1;
                fp_write <= 1;
            end

            //Floating-point fused arithmetic instructions end here.

            if(instr[6:0] == FP_OP) begin

                //In case of an invalid instr input, fp_op and func stay NONE.
                //Floating-point arithmetic instructions start here. Read and written to FP registers.

                if(instr[31:25] == FP_INSTR_FADD) begin
                    fp_op <= instr[6:0];
                    func <= FP_INSTR_FADD;
                    rs1 <= instr[19:15];
                    rs2 <= instr[24:20];
                    rm <= instr[14:12];
                    rd <= instr[11:7];
                    fp_read <= 1;
                    fp_write <= 1;
                end

                if(instr[31:25] == FP_INSTR_FSUB) begin
                    fp_op <= instr[6:0];
                    func <= FP_INSTR_FSUB;
                    rs1 <= instr[19:15];
                    rs2 <= instr[24:20];
                    rm <= instr[14:12];
                    rd <= instr[11:7];
                    fp_read <= 1;
                    fp_write <= 1;
                end

                if(instr[31:25] == FP_INSTR_FMUL) begin
                    fp_op <= instr[6:0];
                    func <= FP_INSTR_FMUL;
                    rs1 <= instr[19:15];
                    rs2 <= instr[24:20];
                    rm <= instr[14:12];
                    rd <= instr[11:7];
                    fp_read <= 1;
                    fp_write <= 1;
                end

                if(instr[31:25] == FP_INSTR_FDIV) begin
                    fp_op <= instr[6:0];
                    func <= FP_INSTR_FDIV;
                    rs1 <= instr[19:15];
                    rs2 <= instr[24:20];
                    rm <= instr[14:12];
                    rd <= instr[11:7];
                    fp_read <= 1;
                    fp_write <= 1;
                end

                if(instr[31:25] == FP_INSTR_FSQRT) begin
                    fp_op <= instr[6:0];
                    func <= FP_INSTR_FSQRT;
                    rs1 <= instr[19:15];
                    rs2 <= instr[24:20];
                    rm <= instr[14:12];
                    rd <= instr[11:7];
                    fp_read <= 1;
                    fp_write <= 1;
                end

                if(instr[31:25] == FP_INSTR_FMINMAX) begin
                    fp_op <= instr[6:0];
                    func <= FP_INSTR_FMINMAX;
                    rs1 <= instr[19:15];
                    rs2 <= instr[24:20];
                    rm <= instr[14:12];
                    rd <= instr[11:7];
                    fp_read <= 1;
                    fp_write <= 1;
                end

                // Floating-point arithmetic instructions end here.
                // Injection instruction covered in the next if statement. Read from and written to FP registers.

                if(instr[31:25] == FP_INSTR_FSGNJ) begin
                    fp_op <= instr[6:0];
                    func <= FP_INSTR_FSGNJ;
                    rs1 <= instr[19:15];
                    rs2 <= instr[24:20];
                    rd <= instr[11:7];
                    rm <= instr[14:12];
                    fp_read <= 1;
                    fp_write <= 1;
                end
                
                // Conversion instructions start here. Either read from a FP register and written to an integer register, or written to a FP
                // register and read from an integer register, depending on the instruction.

                // FCVT.W.S, FCVT.WU.S, FCVT.L.S, FCVT.LU.S share the same function codes. All covered in the next if statement. 
                if(instr[31:25] == FP_INSTR_FCVT_W) begin
                    fp_op <= instr[6:0];
                    func <= FP_INSTR_FCVT_W;
                    rs1 <= instr[19:15];
                    rs2 <= instr[24:20];
                    rd <= instr[11:7];
                    rm <= instr[14:12];
                    fp_read <= 1;
                    int_write <= 1;
                end

                //FCVT.S.W, FCVT.S.WU, FCVT.S.L, FCVT.S.LU all share the same function codes. All covered in the next if statement.
                if(instr[31:25] == FP_INSTR_FCVT_S) begin
                    fp_op <= instr[6:0];
                    func <= FP_INSTR_FCVT_S;
                    rs1 <= instr[19:15];
                    rs2 <= instr[24:20];
                    rm <= instr[14:12];
                    rd <= instr[11:7];
                    int_read <= 1;
                    fp_write <= 1;
                end

                //Conversion instructions end here.
                //Bit patterns movage instructions and Class instruction start here. Either read from fp and written to integers, or written to 
                //fp and read from integers.
                //FMV_X_W and FCLASS.S share the same function code. 

                if(instr[31:25] == FP_INSTR_FMV_X_W) begin
                    fp_op <= instr[6:0];
                    func <= FP_INSTR_FMV_X_W;
                    rs1 <= instr[19:15];
                    rs2 <= instr[24:20];
                    rm <= instr[14:12];
                    rd <= instr[11:7];
                    fp_read <= 1;
                    int_write <= 1;
                end

                if(instr[31:25] == FP_INSTR_FMV_W_X) begin
                    fp_op <= instr[6:0];
                    func <= FP_INSTR_FMV_W_X;
                    rs1 <= instr[19:15];
                    rs2 <= instr[24:20];
                    rm <= instr[14:12];
                    rd <= instr[11:7];
                    int_read <= 1;
                    fp_write <= 1;
                end

                // Bit patterns movage instructions end here
                // Compare instruction covered in the next if statement. read from two fp registers and written to an integer register.

                if(instr[31:25] == FP_INSTR_COMPARE) begin
                    fp_op <= instr[6:0];
                    func <= FP_INSTR_COMPARE;
                    rs1 <= instr[19:15];
                    rs2 <= instr[24:20];
                    rd <= instr[11:7];
                    rm <= instr[14:12];
                    fp_read <= 1;
                    int_write <= 1;
                end
            end
        end
    end
endmodule