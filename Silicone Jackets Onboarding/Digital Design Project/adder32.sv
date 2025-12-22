/*
* Module describing a 32-bit ripple carry adder, with no carry output or input
*/
import calculator_pkg::*;

module adder32(
    input logic [DATA_W - 1 : 0] a_i,
    input logic [DATA_W - 1 : 0] b_i,
    output logic [DATA_W - 1 : 0] sum_o
);
    logic [DATA_W:0] carry;
    assign carry[0] = 1'b0;
    genvar i;
    /*
    logic [DATA_W - 1 : 0] c_i;
    logic [DATA_W - 1 : 0] d_i;

    assign c_i = 32'b00001000011000010000111000000000;
    assign d_i = 32'b01100100010001010000101000000000;
    */
    //TODO: use a generate block to chain together 32 full adders. 
    // Imagine you are connecting 32 single-bit adder modules together. 
    
    generate
        for(i = 0; i < DATA_W; i = i + 1) begin : adder_loop
            full_adder fa(
                .a(a_i[i]),
                .b(b_i[i]),
                .cin(carry[i]),
                .s(sum_o[i]),
                .cout(carry[i+1])
            );
            /*
            assign sum_o[i] = a_i[i] ^ b_i[i] ^ carry[i];
            assign carry[i+1] = (a_i[i] & b_i[i]) | (a_i[i] & carry[i]) | (b_i[i] & carry[i]);
            */
            /*
            assign sum_o[i] = c_i[i] ^ d_i[i] ^ carry[i];
            assign carry[i+1] = (c_i[i] & d_i[i]) | (c_i[i] & carry[i]) | (d_i[i] & carry[i]);
            */
        end
    endgenerate
    

    //assign sum_o = 32'b10100111111000010001100011110101;

    // 512 expected 10100111111000010001100011110101
endmodule
