/*
* Module describing a 64-bit result buffer and the mux for controlling where
* in the buffer an adder's result is placed.
* 
* synchronous active high reset on posedge clk
*/
import calculator_pkg::*;

module result_buffer(

    input logic clk_i,                              //clock signal
    input logic rst_i,                              //reset signal

    input logic [DATA_W-1 : 0] result_i,       //result from ALU
    input logic loc_sel,                            //mux control signal
    output logic [MEM_WORD_SIZE-1 : 0] buffer_o   //64-bit output of buffer
);

    //declare 64-bit buffer
    logic [MEM_WORD_SIZE-1 : 0] internal_buffer;

    //TODO: Write a sequential block to write the next values into the buffer.
    
    always_ff @(posedge clk_i) begin
        
        if (rst_i) 
            internal_buffer <= '0;
        else if (loc_sel)
            internal_buffer[MEM_WORD_SIZE - 1 : DATA_W] <= result_i;
        else internal_buffer[DATA_W - 1 : 0] <= result_i;
        
    end
    
    assign buffer_o = internal_buffer;
    //assign buffer_o = 64'b1100001111100110011111101101010101000011111001100111111011010101;

endmodule
