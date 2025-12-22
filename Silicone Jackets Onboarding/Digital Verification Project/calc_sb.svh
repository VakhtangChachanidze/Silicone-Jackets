class calc_sb #(int DataSize, int AddrSize);

  // Signals needed for the golden model implementation in the scoreboard
  // Physical memory is twice the logical depth so two physical addresses map
  // to one logical address (physical = 2*logical, 2*logical+1).
  int mem_a [2**(AddrSize+1)];
  int mem_b [2**(AddrSize+1)];
  logic second_read = 0;
  int golden_lower_data;
  int golden_upper_data;
  // Store the first operand values for the calculation
  int first_operand_a, first_operand_b;
  mailbox #(calc_seq_item #(DataSize, AddrSize)) sb_box;

  function new(mailbox #(calc_seq_item #(DataSize, AddrSize)) sb_box);
    this.sb_box = sb_box;
  endfunction

  task main();
  calc_seq_item #(DataSize, AddrSize) trans;
  logic [63:0] lower_sum, upper_sum;
  int second_operand_a, second_operand_b;
    forever begin
      sb_box.get(trans);

      // TODO: Implement the scoreboard's core functionality.
      // The scoreboard's task is to verify the DUT's behavior by comparing the
      // data received from the monitor against a golden reference model.

      // Use the transaction flags (`initialize`, `rdn_wr`) to handle three distinct operations:
      // - For initialization, update the scoreboard's local memory (`mem_a` and `mem_b`) to match the DUT's initial SRAM state.
      // - For read operations, compare the data from the SRAM in the DUT to the data stored in the scoreboard's memory.
      //       Think about how to account for the two sequential reads in the DUT for the single write operation. The values
      //       from both read operations need to be used to compare against the calculated values in the DUT when they are written
      //       to SRAM. The second_read, golden_lower_data, and golden_upper_data signals can be used for this purpose.
      // - For write operations, compare the DUT's output to the data calculated by the golden model in the scoreboard.
      // Use `$display` to log successful transactions and `$error` to report mismatches.
      // If a mismatch occurs, use `$finish` to terminate the simulation.

      //$display("Scoreboard: Received transaction - Initialize: %0b, Read/Write: %0b, RdAddr: 0x%0x, WrAddr: 0x%0x, Loc_Sel: %0b, Lower_Data: 0x%0x, Upper_Data: 0x%0x, second_read: %0b",
      //         trans.initialize, trans.rdn_wr, trans.curr_rd_addr, trans.curr_wr_addr, trans.loc_sel, trans.lower_data, trans.upper_data, second_read);
      if (trans.initialize) begin
        second_read      = 0;
        first_operand_a  = 0;
        first_operand_b  = 0;
        golden_lower_data = 0;
        golden_upper_data = 0;
        if (trans.loc_sel == 1'b0) begin
          mem_a[trans.curr_wr_addr] = trans.lower_data;
          //$display("Scoreboard: Initializing SRAM A at logical Addr: 0x%0x with Data: 0x%0x", trans.curr_wr_addr, trans.lower_data);
        end else begin
          mem_b[trans.curr_wr_addr] = trans.upper_data;
          //$display("Scoreboard: Initializing SRAM B at logical Addr: 0x%0x with Data: 0x%0x", trans.curr_wr_addr, trans.upper_data);
        end
        continue;
      end
      
      if(!trans.rdn_wr) begin
        if (trans.lower_data !== mem_a[trans.curr_rd_addr] && trans.upper_data !== mem_b[trans.curr_rd_addr]) begin
          $error("Scoreboard: read mismatch Addr=0x%0x, exp 0x%0x and exp=0x%0x, got 0x%0x and 0x%0x",
                trans.curr_rd_addr, mem_a[trans.curr_rd_addr], mem_b[trans.curr_rd_addr], trans.lower_data, trans.upper_data);
          $finish;
        end
        if (!second_read) begin
          //$display("Scoreboard: First Read from logical Addr: 0x%0x (phys 0x%0x,0x%0x), A: 0x%0x, B: 0x%0x",trans.curr_rd_addr, 2*trans.curr_rd_addr, 2*trans.curr_rd_addr+1,mem_a[2*trans.curr_rd_addr], mem_b[2*trans.curr_rd_addr]);
          first_operand_a = mem_a[trans.curr_rd_addr];
          first_operand_b = mem_b[trans.curr_rd_addr];
          second_read = 1;
          //$display("Scoreboard: Stored first read operands: A=0x%0x, B=0x%0x", first_operand_a, first_operand_b);
        end else begin
          second_operand_a = mem_a[trans.curr_rd_addr];
          second_operand_b = mem_b[trans.curr_rd_addr];
          lower_sum = first_operand_a + first_operand_b;
          upper_sum = second_operand_a + second_operand_b;
          golden_lower_data = lower_sum[DataSize-1:0];
          golden_upper_data = upper_sum[DataSize-1:0];
          second_read = 0;
          //$display("Scoreboard: Golden calculation: lower(0x%0x+0x%0x)=0x%0x, upper(0x%0x+0x%0x)=0x%0x",first_operand_a, first_operand_b, golden_lower_data, second_operand_a, second_operand_b, golden_upper_data);
        end
      end else begin
        if(trans.lower_data != golden_lower_data) begin
          $error("ERROR: Mismatch in lower data output at 0x%0x. Expected %0d, got %0d", trans.curr_wr_addr, golden_lower_data, trans.lower_data);
          $finish;
        end
        //else $display("Scoreboard: Lower data match at Addr: 0x%0x. Value: 0x%0x", trans.curr_wr_addr, trans.lower_data);
        if(trans.upper_data != golden_upper_data) begin
          $error("ERROR: Mismatch in upper data output at 0x%0x. Expected %0d, got %0d", trans.curr_wr_addr, golden_upper_data, trans.upper_data);
          $finish;
        end
        //else $display("Scoreboard: Upper data match at Addr: 0x%0x. Value: 0x%0x", trans.curr_wr_addr, trans.upper_data);
        //update local memory to reflect the write
        mem_a[trans.curr_wr_addr] = trans.lower_data;
        mem_b[trans.curr_wr_addr] = trans.upper_data;
      end
    end
  endtask

endclass : calc_sb
