module calc_tb_top;

  import calc_tb_pkg::*;
  import calculator_pkg::*;

  parameter int DataSize = DATA_W;
  parameter int AddrSize = ADDR_W;
  logic clk = 0;
  logic rst;
  state_t state;
  logic [DataSize-1:0] rd_data;

  bit did_add_reset = 0;   
  bit did_write_reset = 0; 
  int post_reset_idle_wait = 0; 

  task automatic do_sync_reset(int cycles = 5, string tag = "");
    //$display("%0t TB: do_sync_reset start cycles=%0d %s", $time, cycles, tag);
    calc_if.reset = 1'b1;
    repeat (cycles) @(posedge clk);
    calc_if.reset = 1'b0;
    @(posedge clk);
    //$display("%0t TB: do_sync_reset end state=%0s", $time, my_calc.u_ctrl.state.name);
  endtask

  // One-shot mid-operation reset when DUT first reaches S_ADD
  initial begin : one_shot_add_reset
    wait (my_calc.u_ctrl.state == S_ADD);
    if (!did_add_reset) begin
      did_add_reset = 1;
      //$display("%0t TB: One-shot reset during S_ADD", $time);
      calc_if.reset = 1'b1;
      repeat (5) @(posedge clk);
      calc_if.reset = 1'b0;
      @(posedge clk); 
      //$display("%0t TB: One-shot reset released (state=%0s)", $time, my_calc.u_ctrl.state.name);
    end
  end

  // One-shot mid-operation reset when DUT first reaches S_WRITE
  initial begin : one_shot_write_reset
    wait (my_calc.u_ctrl.state == S_WRITE);
    if (!did_write_reset) begin
      did_write_reset = 1;
      //$display("%0t TB: One-shot reset during S_WRITE", $time);
      calc_if.reset = 1'b1;
      repeat (5)@(posedge clk);
      calc_if.reset = 1'b0;
      @(posedge clk);
      //$display("%0t TB: One-shot reset released after S_WRITE reset (state=%0s)", $time, my_calc.u_ctrl.state.name);
    end
  end
  

  calc_if #(.DataSize(DataSize), .AddrSize(AddrSize)) calc_if(.clk(clk));
  top_lvl my_calc(
    .clk(clk),
    .rst(calc_if.reset),
    `ifdef VCS
    .read_start_addr(calc_if.read_start_addr),
    .read_end_addr(calc_if.read_end_addr),
    .write_start_addr(calc_if.write_start_addr),
    .write_end_addr(calc_if.write_end_addr)
    `endif
    `ifdef CADENCE
    .read_start_addr(calc_if.calc.read_start_addr),
    .read_end_addr(calc_if.calc.read_end_addr),
    .write_start_addr(calc_if.calc.write_start_addr),
    .write_end_addr(calc_if.calc.write_end_addr)
    `endif
  );

  assign rst = calc_if.reset;
  assign state = my_calc.u_ctrl.state;
  `ifdef VCS
  assign calc_if.wr_en = my_calc.write;
  assign calc_if.rd_en = my_calc.read;
  assign calc_if.wr_data = my_calc.w_data;
  assign calc_if.rd_data = my_calc.r_data;
  assign calc_if.ready = my_calc.u_ctrl.state == S_END;
  assign calc_if.curr_rd_addr = my_calc.r_addr;
  assign calc_if.curr_wr_addr = my_calc.w_addr;
  assign calc_if.loc_sel = my_calc.u_ctrl.buffer_control;
  `endif
  `ifdef CADENCE
  assign calc_if.calc.wr_en = my_calc.write;
  assign calc_if.calc.rd_en = my_calc.read;
  assign calc_if.calc.wr_data = my_calc.w_data;
  assign calc_if.calc.rd_data = my_calc.r_data;
  assign calc_if.calc.ready = my_calc.u_ctrl.state == S_END;
  assign calc_if.calc.curr_rd_addr = my_calc.r_addr;
  assign calc_if.calc.curr_wr_addr = my_calc.w_addr;
  assign calc_if.calc.loc_sel = my_calc.u_ctrl.buffer_control;
  `endif

  //write checker, checks if the DUT correctly stores data into SRAM
  logic [AddrSize-1:0] wr_addr_cap; 
  logic [31:0]         wr_lower_cap, wr_upper_cap;
  bit                  commit_pending;

  always @(posedge clk) begin
    if (rst) begin
      commit_pending <= 0;
      wr_addr_cap    <= '0;
      wr_lower_cap   <= '0;
      wr_upper_cap   <= '0;
    end else begin
      if (my_calc.write) begin
        wr_addr_cap   <= my_calc.w_addr;
        wr_lower_cap  <= my_calc.w_data_low; 
        wr_upper_cap  <= my_calc.w_data_high;  
        commit_pending <= 1;
        //$display("%0t TB: WRITE intent addr=%0d lower=0x%0h upper=0x%0h", $time, my_calc.w_addr, my_calc.w_data_low, my_calc.w_data_high);
      end else if (commit_pending) begin
        // One cycle after capture verify commit
        if (my_calc.sram_A.mem[wr_addr_cap] !== wr_lower_cap) begin
          $error("SRAM A store mismatch addr=%0d exp=0x%0h got=0x%0h", wr_addr_cap, wr_lower_cap, my_calc.sram_A.mem[wr_addr_cap]);
          $finish;
        end
        if (my_calc.sram_B.mem[wr_addr_cap] !== wr_upper_cap) begin
          $error("SRAM B store mismatch addr=%0d exp=0x%0h got=0x%0h", wr_addr_cap, wr_upper_cap, my_calc.sram_B.mem[wr_addr_cap]);
          $finish;
        end
        //$display("%0t TB: WRITE commit OK addr=%0d lower=0x%0h upper=0x%0h", $time, wr_addr_cap, wr_lower_cap, wr_upper_cap);
        commit_pending <= 0;
      end
    end
  end

  calc_tb_pkg::calc_driver #(.DataSize(DataSize), .AddrSize(AddrSize)) calc_driver_h;
  calc_tb_pkg::calc_sequencer #(.DataSize(DataSize), .AddrSize(AddrSize)) calc_sequencer_h;
  calc_tb_pkg::calc_monitor #(.DataSize(DataSize), .AddrSize(AddrSize)) calc_monitor_h;
  calc_tb_pkg::calc_sb #(.DataSize(DataSize), .AddrSize(AddrSize)) calc_sb_h;

  always #5 clk = ~clk;

  task write_sram(input [AddrSize-1:0] addr, input [DataSize-1:0] data, input logic block_sel);
    //$display($stime, "TB: Writing SRAM Addr=0x%0x Data=0x%0x Block=%0d", addr, data, block_sel);
    @(posedge clk);
    if (!block_sel) begin
      my_calc.sram_A.mem[addr] = data;
    end
    else begin
      my_calc.sram_B.mem[addr] = data;
    end
    calc_driver_h.initialize_sram(addr, data, block_sel);
  endtask

  initial begin
    `ifdef VCS
    $fsdbDumpon;
    $fsdbDumpfile("simulation.fsdb");
    $fsdbDumpvars(0, calc_tb_top, "+mda", "+all", "+trace_process");
    $fsdbDumpMDA;
    `endif
    `ifdef CADENCE
    $shm_open("waves.shm");
    $shm_probe("AC");
    `endif

    calc_monitor_h = new(calc_if);
    calc_sb_h = new(calc_monitor_h.mon_box);
    calc_sequencer_h = new();
    calc_driver_h = new(calc_if, calc_sequencer_h.calc_box);
    

    @(posedge clk);
    calc_if.cb.initialize <= 0;
    calc_if.cb.initialize_addr <= 0;
    calc_if.cb.initialize_data <= 0;
    calc_if.cb.initialize_loc_sel <= 0;
    @(posedge clk);
    
    fork
      calc_monitor_h.main();
      calc_sb_h.main();
    join_none
    
    do_sync_reset(2, "power_on");

    for (int i = 0; i < 2 ** AddrSize; i++) begin
      write_sram(i, $random, 0);
      write_sram(i, $random, 1);
    end

    repeat (20) @(posedge clk);
    

    // Directed part
    $display("Directed Testing");
    
    // Test case 1 - normal addition
    $display("Test case 1 - normal addition");
    // TODO: Finish test case 1
    calc_if.cb.read_start_addr <= 0;
    calc_if.cb.read_end_addr <= 3;
    calc_if.cb.write_start_addr <= 4;
    calc_if.cb.write_end_addr <= 7;

    //addition on the lower end of the data
    write_sram(0, 32'b00000000000000000000000000000111, 0);
    write_sram(0, 32'b00000000000000000000000000010011, 1);
    write_sram(1, 32'b00000000000000000000000000000110, 0);
    write_sram(1, 32'b00000000000000000000000000001001, 1);
    write_sram(2, 32'b00000000000000000000000000000101, 0);
    write_sram(2, 32'b00000000000000000000000000001010, 1);
    write_sram(3, 32'b00000000000000000000000000000101, 0);
    write_sram(3, 32'b00000000000000000000000000000101, 1);
    calc_driver_h.start_calc(0, 3, 4, 7, 1);
    repeat (20) @(posedge clk);

    //addition with overflow
    calc_if.cb.read_start_addr <= 4;
    calc_if.cb.read_end_addr <= 5;
    calc_if.cb.write_start_addr <= 11;
    calc_if.cb.write_end_addr <= 12;
    write_sram(4, 32'b10000000000000000000000000000001, 0);
    write_sram(4, 32'b10110011111111111111111111111111, 1);
    write_sram(5, 32'b01111111110011011011101111111111, 0);
    write_sram(5, 32'b11111001011111111101111111111111, 1);

    calc_driver_h.start_calc(4, 5, 11, 12, 1);
    repeat (20) @(posedge clk);

    //edge cases 
    calc_if.cb.read_start_addr <= 4;
    calc_if.cb.read_end_addr <= 7;
    calc_if.cb.write_start_addr <= 11;
    calc_if.cb.write_end_addr <= 14;
    write_sram(4, 32'b00000000000000000000000000000000, 0);
    write_sram(4, 32'b00000000000000000000000000000000, 1);
    write_sram(5, 32'b00000000000000000000000000000000, 0);
    write_sram(5, 32'b00000000000000000000000000000001, 1);
    write_sram(6, 32'b00000000000000000000000000000001, 0);
    write_sram(6, 32'b00000000000000000000000000000000, 1);
    write_sram(7, 32'b00000000000000000000000000000001, 0);
    write_sram(7, 32'b00000000000000000000000000000001, 1);

    calc_driver_h.start_calc(4, 7, 11, 14, 1);
    repeat (20) @(posedge clk);

    calc_if.cb.read_start_addr <= 4;
    calc_if.cb.read_end_addr <= 7;
    calc_if.cb.write_start_addr <= 11;
    calc_if.cb.write_end_addr <= 14;
    write_sram(4, 32'b00000000000000000000000000000000, 0);
    write_sram(4, 32'b11111111111111111111111111111111, 1);
    write_sram(5, 32'b11111111111111111111111111111111, 0);
    write_sram(5, 32'b00000000000000000000000000000000, 1);
    write_sram(6, 32'b11111111111111111111111111111111, 0);
    write_sram(6, 32'b00000000000000000000000000000001, 1);
    write_sram(7, 32'b00000000000000000000000000000001, 0);
    write_sram(7, 32'b11111111111111111111111111111110, 1);

    calc_driver_h.start_calc(4, 7, 11, 14, 1);
    repeat (20) @(posedge clk);

    calc_if.cb.read_start_addr <= 4;
    calc_if.cb.read_end_addr <= 5;
    calc_if.cb.write_start_addr <= 11;
    calc_if.cb.write_end_addr <= 12;
    write_sram(4, 32'b11111111111111111111111111111110, 0);
    write_sram(4, 32'b11111111111111111111111111111111, 1);
    write_sram(5, 32'b11111111111111111111111111111111, 0);
    write_sram(5, 32'b11111111111111111111111111111111, 1);

    calc_driver_h.start_calc(4, 5, 11, 12, 1);
    repeat (20) @(posedge clk);
    
    //small address length addition
    calc_if.cb.read_start_addr <= 0;
    calc_if.cb.read_end_addr <= 0;
    calc_if.cb.write_start_addr <= 1;
    calc_if.cb.write_end_addr <= 1;
    write_sram(0, 32'b00000000000000000000000000000001, 0);
    write_sram(0, 32'b00000000000000000000000000000001, 1);
    calc_driver_h.start_calc(0, 0, 1, 1, 1);
    repeat (20) @(posedge clk);

    calc_if.cb.read_start_addr <= 0;
    calc_if.cb.read_end_addr <= 0;
    calc_if.cb.write_start_addr <= 1;
    calc_if.cb.write_end_addr <= 1;
    write_sram(0, 32'b11111111111111111111111111111111, 0);
    write_sram(0, 32'b11111111111111111111111111111111, 1);
    calc_driver_h.start_calc(0, 0, 1, 1, 1);
    repeat (20) @(posedge clk);

    calc_if.cb.read_start_addr <= 0;
    calc_if.cb.read_end_addr <= 1;
    calc_if.cb.write_start_addr <= 2;
    calc_if.cb.write_end_addr <= 3;
    write_sram(0, 32'b00000000000000000000000000000001, 0);
    write_sram(0, 32'b00000000000000000000000000000001, 1);
    write_sram(1, 32'b11111111111111111111111111111111, 0);
    write_sram(1, 32'b00000000000000000000000000000001, 1);
    calc_driver_h.start_calc(0, 1, 2, 3, 1);
    repeat (20) @(posedge clk);

    calc_if.cb.read_start_addr <= 0;
    calc_if.cb.read_end_addr <= 2;
    calc_if.cb.write_start_addr <= 3;
    calc_if.cb.write_end_addr <= 5;
    write_sram(0, 32'b00000000000000000000000000000001, 0);
    write_sram(0, 32'b00000000000000000000000000000001, 1);
    write_sram(1, 32'b11111111111111111111111111111111, 0);
    write_sram(1, 32'b00000000000000000000000000000001, 1);
    write_sram(2, 32'b11111111111111111111111111111111, 0);
    write_sram(2, 32'b00000000000000000000000000000001, 1);
    calc_driver_h.start_calc(0, 2, 3, 5, 1);
    repeat (20) @(posedge clk);
    
    //addition with maximum address
    
    for (int a = 0; a <= (1 << (AddrSize-1)) - 1; a++) begin
      write_sram(a, $urandom, 0);
      write_sram(a, $urandom, 1);
    end

    calc_if.cb.read_start_addr  <= 0;
    calc_if.cb.read_end_addr    <= (1 << (AddrSize-1)) - 1;
    calc_if.cb.write_start_addr <= (1 << (AddrSize-1));
    calc_if.cb.write_end_addr   <= (1 << (AddrSize)) - 1;

    calc_driver_h.start_calc(0, (1 << (AddrSize-1)) - 1, (1 << (AddrSize-1)), (1 << (AddrSize)) - 1, 1);
    repeat (20) @(posedge clk);
    
    //back to back additions

    calc_if.cb.read_start_addr <= 0;
    calc_if.cb.read_end_addr <= 3;
    calc_if.cb.write_start_addr <= 8;
    calc_if.cb.write_end_addr <= 11;

    write_sram(0, 32'b00000000000000000000000000000000, 0);
    write_sram(0, 32'b00000000000000000000000000000000, 1);
    write_sram(1, 32'b00000000000000000000000000000000, 0);
    write_sram(1, 32'b00000000000000000000000000000001, 1);
    write_sram(2, 32'b00000000000000000000000000000001, 0);
    write_sram(2, 32'b00000000000000000000000000000000, 1);
    write_sram(3, 32'b00000000000000000000000000000001, 0);
    write_sram(3, 32'b00000000000000000000000000000001, 1);

    calc_driver_h.start_calc(0, 3, 8, 11, 1);
    @(posedge clk);
    wait (calc_if.cb.ready);

    @(posedge clk);
    calc_if.cb.read_start_addr <= 4;
    calc_if.cb.read_end_addr <= 7;
    calc_if.cb.write_start_addr <= 12;
    calc_if.cb.write_end_addr <= 15;

    write_sram(4, 32'b00000000000000000000000000000000, 0);
    write_sram(4, 32'b00000000000000000000000000000000, 1);
    write_sram(5, 32'b00000000000000000000000000000000, 0);
    write_sram(5, 32'b00000000000000000000000000000001, 1);
    write_sram(6, 32'b00000000000000000000000000000001, 0);
    write_sram(6, 32'b00000000000000000000000000000000, 1);
    write_sram(7, 32'b00000000000000000000000000000001, 0);
    write_sram(7, 32'b00000000000000000000000000000001, 1);

    calc_driver_h.start_calc(4, 7, 12, 15, 1);
    repeat (20) @(posedge clk);

    //Long carry chain test
    for (int a = 24; a <= 31; a++) begin
      write_sram(a, (a % 2) ? 32'b00000000000000000000000000000000 : 32'b11111111111111111111111111111111, 0);
      write_sram(a, 32'b00000000000000000000000000000001, 1);
    end
    calc_if.cb.read_start_addr  <= 24;
    calc_if.cb.read_end_addr    <= 31;
    calc_if.cb.write_start_addr <= 80;
    calc_if.cb.write_end_addr   <= 87;
    calc_driver_h.start_calc(24, 31, 80, 87, 1);
    repeat (40) @(posedge clk);

    //alternating pattern testcase
    for (int a = 32; a <= 39; a++) begin
      write_sram(a, (a % 2) ? 32'b10101010101010101010101010101010 : 32'b01010101010101010101010101010101, 0);
      write_sram(a, (a % 2) ? 32'b01010101010101010101010101010101 : 32'b10101010101010101010101010101010, 1);
    end
    calc_if.cb.read_start_addr  <= 32;
    calc_if.cb.read_end_addr    <= 39;
    calc_if.cb.write_start_addr <= 90;
    calc_if.cb.write_end_addr   <= 97;
    calc_driver_h.start_calc(32, 39, 90, 97, 1);

    //start request while still busy testcase
    for (int a = 40; a <= 43; a++) begin
      write_sram(a, 32'h0000_00A0 + a, 0);
      write_sram(a, 32'h0000_00B0 + a, 1);
    end
    calc_if.cb.read_start_addr  <= 40;
    calc_if.cb.read_end_addr    <= 43;
    calc_if.cb.write_start_addr <= 100;
    calc_if.cb.write_end_addr   <= 103;
    calc_driver_h.start_calc(40, 43, 100, 103, 1);

    $display("Test case 2 - addition with overflow");
    // TODO: Finish test case 1
    
    // TODO: Add test cases according to your test plan. If you need additional test cases to reach
    // 96% coverage, make sure to add them to your test plan

    // Random part
    $display("Randomized Testing");
    // TODO: Finish randomized testing
    // HINT: The sequencer is responsible for generating random input sequences. How can the
    // sequencer and driver be combined to generate multiple randomized test cases?
    
    for(int i = 0; i < 2000; i++) begin  
      logic [AddrSize-1:0] rand_read_start = $urandom_range(0, 400);
      logic [AddrSize-1:0] rand_read_end = rand_read_start + $urandom_range(1, 56);  // 1-56 addresses
      logic [AddrSize-1:0] rand_write_start = rand_read_end + 1 + $urandom_range(0, 3);  // Non-overlapping
      logic [AddrSize-1:0] rand_write_end = rand_write_start + (rand_read_end - rand_read_start);  // Same size
      /*
      $display("RANDOM TESTING: Random test %0d: Read[%0d:%0d] Write[%0d:%0d]", 
              i, rand_read_start, rand_read_end, rand_write_start, rand_write_end);
      */
      for(int addr = rand_read_start; addr <= rand_read_end; addr++) begin
        logic [DataSize-1:0] rand_data_a = $urandom & 32'hFFFF;  // Limit to avoid overflow
        logic [DataSize-1:0] rand_data_b = $urandom & 32'hFFFF;
        //$display("RANDOM TESTING: Initializing Addr=0x%0x with DataA=0x%0x", addr, rand_data_a);
        write_sram(addr, rand_data_a, 0);  // SRAM A
        //$display("RANDOM TESTING: Initializing Addr=0x%0x with DataB=0x%0x", addr, rand_data_b);
        write_sram(addr, rand_data_b, 1);  // SRAM B
      end
      
      calc_driver_h.start_calc(rand_read_start, rand_read_end, rand_write_start, rand_write_end, 1);
      
      repeat (50) @(posedge clk);
    end
    
    $display("TEST PASSED");
    $finish;
  end

  //====================
  //      ASSERTIONS
  //====================

  
  // TODO: Add Assertions
  // Option 1 reset check: at the falling edge of rst (i.e., first cycle with rst=0 and $past(rst)=1)
  // confirm that while reset was asserted the FSM was indeed in S_IDLE.
  // This avoids false failures when the FSM legitimately leaves S_IDLE immediately after reset deassert.
  always @(posedge clk) begin
    if (!$isunknown(rst) && $past(rst) && !rst) begin
      assert($past(state) == S_IDLE)
        else $error("Reset deassert: FSM was not in S_IDLE during last reset cycle (was %0d)", $past(state));
    end
    // Other protocol assertions (address ranges, loc_sel sanity)
    if (!rst) begin
      if (!$isunknown({calc_if.read_start_addr, calc_if.read_end_addr, calc_if.write_start_addr, calc_if.write_end_addr, calc_if.loc_sel})) begin
        assert(
          (calc_if.read_start_addr <= calc_if.read_end_addr) &&
          (calc_if.write_start_addr <= calc_if.write_end_addr) &&
          ((calc_if.read_end_addr < calc_if.write_start_addr) || (calc_if.write_end_addr < calc_if.read_start_addr))
        ) else $error("Invalid input address ranges");
        assert(calc_if.loc_sel == 1'b0 || calc_if.loc_sel == 1'b1) else $error("Buffer location select is not toggled");
      end
    end
  end

endmodule
