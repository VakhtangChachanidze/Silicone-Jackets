class calc_driver #(int DataSize, int AddrSize);

  mailbox #(calc_seq_item #(DataSize, AddrSize)) drv_box;

  virtual interface calc_if #(.DataSize(DataSize), .AddrSize(AddrSize)) calcVif;

  function new(virtual interface calc_if #(DataSize, AddrSize) calcVif,
      mailbox #(calc_seq_item #(DataSize, AddrSize)) drv_box);
    this.calcVif = calcVif;
    this.drv_box = drv_box;
  endfunction

  task reset_task();

    // TODO: Write the code to apply a reset sequence to the DUT.
    // HINT: Does the DUT does an active-high or active-low reset?
    // HINT: Use @(calcVif.cb) to wait for a clock cycle. This is called a clocking
    // event which is equivalent to @(posedge clk) if the clocking block (CB) uses the
    // same clock signal, but with the input signals in the CB being sampled with the
    // specified delay BEFORE the clock edge and the output signals in the CB being
    // sampled with the specified delay AFTER the clock edge. This helps with addressing
    // race conditions in simulation to keep testbenches deterministic.

    calcVif.cb.reset <= 1;
    repeat (3) @(calcVif.cb);
    calcVif.cb.reset <= 0;
    @(calcVif.cb);
    //$display("INFO: DUT has been reseted");
  endtask

  virtual task initialize_sram(input [AddrSize-1:0] addr, input [DataSize-1:0] data, input logic block_sel);
    //$display("INFO: Initializing SRAM at Addr: 0x%0x with Data: 0x%0x to Block: %0d", addr, data, block_sel);
    // TODO: Write the code to drive the signals for SRAM initialization.
    //       Add a display statement to make it clearer in the simulation log that the driver is
    //       initializing the SRAM (and which one out of A or B it is)
    // HINT: Think about which signals in the clocking block should be driven to allow the
    // monitor to determine that SRAM is being initialized.
    // Drive address/data/select first and let them settle
    calcVif.cb.initialize_addr <= addr;
    calcVif.cb.initialize_data <= data;
    calcVif.cb.initialize_loc_sel <= block_sel;
    //$display($stime, "DRIVER: driven init fields Addr=0x%0x Data=0x%0x Loc_sel=%0d", addr, data, block_sel);
    @(calcVif.cb);
    // Now pulse initialize high for one full clock so the monitor sees it
    calcVif.cb.initialize <= 1;
    //$display($stime, "DRIVER: pulsing initialize=1");
    @(calcVif.cb);
    calcVif.cb.initialize <= 0;
    //$display($stime, "DRIVER: deassert initialize=0");
    @(calcVif.cb);
  // $display("INFO: SRAM has been initialized at address 0x%0x with data 0x%0x to block %0d", addr, data, block_sel);
  endtask : initialize_sram

  virtual task start_calc(input logic [AddrSize-1:0] read_start_addr, input logic [AddrSize-1:0] read_end_addr,
      input logic [AddrSize-1:0] write_start_addr, input logic [AddrSize-1:0] write_end_addr,
      input bit direct = 1);
    
    calc_seq_item #(DataSize, AddrSize) trans;
    // TODO: Drive the calculation parameters to the DUT's interface.
    calcVif.cb.read_start_addr <= read_start_addr;
    calcVif.cb.read_end_addr <= read_end_addr;
    calcVif.cb.write_start_addr <= write_start_addr;
    calcVif.cb.write_end_addr <= write_end_addr;
    // HINT: Use calcVif.cb.signal_name <= value;
    //       Think about what the DUT's top level inputs are
    // TODO: Add a display statement to show the transaction is starting.
    //$display("INFO: Starting calculation with Read Start Addr: 0x%0x, Read End Addr: 0x%0x, Write Start Addr: 0x%0x, Write End Addr: 0x%0x", read_start_addr, read_end_addr, write_start_addr, write_end_addr);
    reset_task();
    @(calcVif.cb iff calcVif.cb.ready);

    if (!direct) begin 
      calc_seq_item #(DataSize, AddrSize) trans;
      if (drv_box.try_peek(trans)) begin
        int delay = $urandom_range(0, 5);
        repeat (delay) begin
          @(calcVif.cb);
        end
      end
    end
  endtask : start_calc

  virtual task drive();
    calc_seq_item #(DataSize, AddrSize) trans;
    while (drv_box.try_get(trans)) begin
      start_calc(trans.read_start_addr, trans.read_end_addr, trans.write_start_addr, trans.write_end_addr, 0);
    end
  endtask : drive

endclass : calc_driver
