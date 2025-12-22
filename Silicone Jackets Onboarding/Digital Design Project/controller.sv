import calculator_pkg::*;

module controller (
  	input  logic              clk_i,
    input  logic              rst_i,
  
  	// Memory Access
    input  logic [ADDR_W-1:0] read_start_addr,
    input  logic [ADDR_W-1:0] read_end_addr,
    input  logic [ADDR_W-1:0] write_start_addr,
    input  logic [ADDR_W-1:0] write_end_addr,
  
  	// Control
    output logic write,
    output logic [ADDR_W-1:0] w_addr,
    output logic [MEM_WORD_SIZE-1:0] w_data,

    output logic read,
    output logic [ADDR_W-1:0] r_addr,
    input  logic [MEM_WORD_SIZE-1:0] r_data,

  	// Buffer Control (1 = upper, 0, = lower)
    output logic              buffer_control,
  
  	// These go into adder
  	output logic [DATA_W-1:0]       op_a,
    output logic [DATA_W-1:0]       op_b,
  
    input  logic [MEM_WORD_SIZE-1:0]       buff_result
  
); 


	//TODO: Write your controller state machine as you see fit. 
	//HINT: See "6.2 Two Always BLock FSM coding style" from refmaterials/1_fsm_in_systemVerilog.pdf
	// This serves as a good starting point, but you might find it more intuitive to add more than two always blocks.

	//See calculator_pkg.sv for state_t enum definition
  	state_t state, next;
	logic buffer_half;
	logic [ADDR_W-1:0] read_addr;
	logic [ADDR_W-1:0] write_addr;
	logic [ADDR_W-1:0] next_read_addr;
    logic [ADDR_W-1:0] next_write_addr;
    logic next_buffer_half;
	logic [DATA_W-1:0] op_a_reg, op_b_reg;
    logic pending_full, next_pending_full;

	//State reg, other registers as needed
	always_ff @(posedge clk_i) begin
		if (rst_i) begin
			state <= S_IDLE;
			read_addr <= read_start_addr;
			write_addr <= write_start_addr;
			buffer_half <= 0;
			op_a_reg <= 0;
			op_b_reg <= 0;
		end
		else begin
			state <= next;
			
			read_addr <= next_read_addr;
            write_addr <= next_write_addr;
			buffer_half <= next_buffer_half;
            pending_full <= next_pending_full;

			
			if(state == S_ADD) begin
				op_a_reg <= r_data[31:0];
				op_b_reg <= r_data[63:32];
			end
		end
	end
	
	//Next state logic, outputs
	always_comb begin
		read           = 1'b0;
		write          = 1'b0;
        w_addr         = write_addr;
        w_data         = buff_result;
        r_addr         = read_addr;
        buffer_control = buffer_half;
        next           = S_IDLE;
		next_read_addr = read_addr;
        next_write_addr = write_addr;
        next_buffer_half = buffer_half;
		next_pending_full = pending_full;

		case (state)
			S_IDLE: begin
				if(!rst_i)
					next = S_READ;
				else
					next = S_IDLE;
			end
			S_READ: begin
				if(pending_full && (read_addr > read_end_addr)) begin
					write = 1;
					next_write_addr   = write_addr + 1'b1;
					next_pending_full = 1'b0;
					next = S_END; 
				end else begin
					if(pending_full) begin
						write = 1;
						next_write_addr   = write_addr + 1'b1;
						next_pending_full = 1'b0;
					end
					if(read_addr <= read_end_addr) begin
						read = 1;
						next = S_ADD;
					end else begin
						next = S_END;
					end
				end
			end
			S_ADD: begin
				next = S_WRITE;
			end
			S_WRITE: begin
				if(buffer_half == 1'b0) begin
					next_buffer_half = 1'b1;
					next_read_addr   = read_addr + 1'b1;
					next = S_READ;
				end else begin
					next_buffer_half   = 1'b0;
					next_read_addr     = read_addr + 1'b1; 
					next_pending_full  = 1'b1;
					next = S_READ; 
				end
			end
			S_END: begin
				next = S_END;
			end
		endcase
	end
	assign op_a = op_a_reg;
	assign op_b = op_b_reg;
endmodule
