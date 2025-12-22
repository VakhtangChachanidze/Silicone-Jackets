/* 
 * This top_level module integrates the controller, memory, adder, and result buffer to form a complete calculator system.
 * It handles memory reads/writes, arithmetic operations, and result buffering.
 */
import calculator_pkg::*;

module top_lvl(
    input  logic                 clk,
    input  logic                 rst,

    // Memory Config
    input  logic [ADDR_W-1:0]    read_start_addr,
    input  logic [ADDR_W-1:0]    read_end_addr,
    input  logic [ADDR_W-1:0]    write_start_addr,
    input  logic [ADDR_W-1:0]    write_end_addr
    
);

    //Any wires, combinational assigns, etc should go at the top for visibility
   logic [DATA_W-1:0] op_a, op_b;
   logic [MEM_WORD_SIZE-1:0] buff_result;

   logic write, read;
   logic [ADDR_W-1:0] w_addr, r_addr;
   logic [MEM_WORD_SIZE-1:0] w_data, r_data;
   logic [31:0] r_data_low, r_data_high;
   logic [31:0] w_data_low, w_data_high;

   logic buffer_control; 

   logic [MEM_WORD_SIZE-1:0] result_buffer_out;

   logic [DATA_W-1:0] sum;

   
   assign w_data_low = buff_result[31:0];
   assign w_data_high = buff_result[63:32];
   
   //assign op_a = 32'b00001000011000010000111000000000;
   //assign op_b = 32'b01100100010001010000101000000000;

   assign r_data = {r_data_high,r_data_low};
   
    //TODO: Finish instantiation of your controller module
	controller u_ctrl (
    .clk_i(clk),
    .rst_i(rst),

    .read_start_addr(read_start_addr),
    .read_end_addr(read_end_addr),
    .write_start_addr(write_start_addr),
    .write_end_addr(write_end_addr),

    .write(write),
    .w_addr(w_addr),
    .w_data(w_data),
    .read(read),
    .r_addr(r_addr),
    .r_data(r_data),

    .buffer_control(buffer_control),
    .op_a(op_a),
    .op_b(op_b),
    .buff_result(buff_result)
  );

    //TODO: Look at the sky130_sram_2kbyte_1rw1r_32x512_8 module and instantiate it using variables defined above.
    // Note: This module has two ports, port 0 for read and write and port 1 for read only. We are using port 0 writing and port 1 for reading in this design.    
    // we have provided all of the input ports of SRAM_A, which you will need to connect to calculator ports inside the parentheses. 
    // Your instantiation for SRAM_A will be similar to SRAM_B. 
  	/*
     * .clk0 : sram macro clock input. Connect to same clock as controller.sv. 
     * .csb0 : chip select, active low. Set low when you want to write. Refer to sky130_sram instantiation to see what value to use for both read and write operations in port 0.
     * .web0 : write enable, active low. Set low when you want to write.  Refer to sky130_sram instantiation to see what value to use for both read and write operations in port 0.
     * .wmask0 : write mask, used to select which bits to write. For this design, we will write all bits, so use 4'hF.
     * .addr0 : address to read/write
     * .din0 : data to write
     * .dout0 : data output from memory when performing a read. Will leave blank here because we are only writing to port 0. 
     * .clk1  : sram macro clock input for port 2. Connect to same clock as controller.sv. 
     * .csb1  : chip select, active low. Set low when you want to read. Since this second port can only be used to read, there is no write enable bit (web) 
     * .addr1 : address to read from. You will supply this value. 
     * .dout1 : data output from the SRAM macro port.
     */
  	
      sky130_sram_2kbyte_1rw1r_32x512_8 sram_A (
        .clk0   (clk),  
        .csb0   (~(read | write)),
        .web0   (~write), 
        .wmask0 (4'hf), 
        .addr0  (w_addr), 
        .din0   (w_data_low),
        //.addr0  (9'b1101110),
        //.din0   (32'b10100001001001000101011100011000), 
        .dout0  (),
        .clk1   (clk),
        .csb1   (~read),
        .addr1  (r_addr),
        .dout1  (r_data_low)
    );

  
    //TODO: Instantiate the second SRAM for the upper half of the memory.
    sky130_sram_2kbyte_1rw1r_32x512_8 sram_B (
      .clk0   (clk),  
      .csb0   (~(read | write)),
      .web0   (~write), 
      .wmask0 (4'hf), 
      .addr0  (w_addr), 
      .din0   (w_data_high),
      //.addr0  (9'b1100100),
      //.din0   (32'b11010111001010000010010101111011),
      .dout0  (),
      .clk1   (clk), 
      .csb1   (~read), 
      .addr1  (r_addr), 
      .dout1  (r_data_high) 
    );
  	
  	//TODO: Finish instantiation of your adder module
    adder32 u_adder (
        .a_i(op_a),
        .b_i(op_b),
        /*
        .a_i(32'b00001000011000010000111000000000),
        .b_i(32'b01100100010001010000101000000000),
        */
        .sum_o(sum)
    );
 
    //TODO: Finish instantiation of your result buffer
    result_buffer u_resbuf (
      .clk_i(clk),
      .rst_i(rst),
      .result_i(sum),
      .loc_sel(buffer_control),
      .buffer_o(buff_result)
    );
  
endmodule
