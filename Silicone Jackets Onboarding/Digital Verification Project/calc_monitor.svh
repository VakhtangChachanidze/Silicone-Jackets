class calc_monitor #(int DataSize, int AddrSize);
  logic written = 0;

  virtual interface calc_if #(.DataSize(DataSize), .AddrSize(AddrSize)) calcVif;
  mailbox #(calc_seq_item #(DataSize, AddrSize)) mon_box;

  function new(virtual interface calc_if #(DataSize, AddrSize) calcVif);
    this.calcVif = calcVif;
    this.mon_box = new();
  endfunction

  task main();
    forever begin
      @(calcVif.cb);
      if (calcVif.cb.rd_en && calcVif.cb.wr_en) begin
        calc_seq_item #(DataSize, AddrSize) tr_rd = new();
        calc_seq_item #(DataSize, AddrSize) tr_wr = new();

        // Read transaction (sample rd_data and read address)
        tr_rd.rdn_wr = 1'b0;
        tr_rd.curr_rd_addr = calcVif.cb.curr_rd_addr;
        tr_rd.curr_wr_addr = calcVif.cb.curr_wr_addr;
        tr_rd.loc_sel = calcVif.cb.loc_sel;
        tr_rd.initialize = 1'b0;
        tr_rd.lower_data = calcVif.cb.rd_data[DataSize-1:0];
        tr_rd.upper_data = calcVif.cb.rd_data[DataSize*2-1:DataSize];
        //$display($stime, " Monitor: Simul rd+wr detected - enqueuing READ Addr: 0x%0x", tr_rd.curr_rd_addr);
        mon_box.put(tr_rd);

        // Write transaction (sample wr_data and write address)
        tr_wr.rdn_wr = 1'b1;
        tr_wr.curr_wr_addr = calcVif.cb.curr_wr_addr;
        tr_wr.curr_rd_addr = calcVif.cb.curr_rd_addr;
        tr_wr.loc_sel = calcVif.cb.loc_sel;
        tr_wr.initialize = 1'b0;
        tr_wr.lower_data = calcVif.cb.wr_data[DataSize-1:0];
        tr_wr.upper_data = calcVif.cb.wr_data[DataSize*2-1:DataSize];
        //$display($stime, " Monitor: Simul rd+wr detected - enqueuing WRITE Addr: 0x%0x", tr_wr.curr_wr_addr);
        mon_box.put(tr_wr);

        continue;
      end
      // Sample the transaction and send to scoreboard
      if (calcVif.cb.wr_en || calcVif.cb.rd_en) begin
        calc_seq_item #(DataSize, AddrSize) trans = new();
        // TODO: Assign all values in the "trans" sequence item object with relevant signals from the clocking block
        trans.rdn_wr = calcVif.cb.wr_en;
        trans.curr_wr_addr = calcVif.cb.curr_wr_addr;
        trans.curr_rd_addr = calcVif.cb.curr_rd_addr;
        trans.loc_sel = calcVif.cb.loc_sel;
        trans.initialize = 1'b0;
        if (trans.rdn_wr) 
        begin
          trans.lower_data = calcVif.cb.wr_data[DataSize-1:0];
          trans.upper_data = calcVif.cb.wr_data[DataSize*2-1:DataSize];
          
          if (!written) begin
            written = 1;
            // $display($stime, " Monitor: Write to Addr: 0x%0x, Lower: 0x%0x, Upper: 0x%0x",
            //          trans.curr_wr_addr, trans.lower_data, trans.upper_data);
            mon_box.put(trans);
          end
        end
        else if (!trans.rdn_wr)
        begin
          @(calcVif.cb);
          written = 0;
          // Capture full read data (both halves)
          trans.lower_data = calcVif.cb.rd_data[DataSize-1:0];
          trans.upper_data = calcVif.cb.rd_data[DataSize*2-1:DataSize];
      // $display($stime, " Monitor: Read from Addr: 0x%0x, A: 0x%0x, B: 0x%0x",
      //          trans.curr_rd_addr, trans.lower_data, trans.upper_data);
          mon_box.put(trans);
        end
      end

      if (calcVif.cb.initialize) begin
        calc_seq_item #(DataSize, AddrSize) trans = new();
        // TODO: Assign the right fields for the transaction from the clocking block signals that are
        // relevant to initializing SRAM
        // HINT: How do you differentiate which data belongs to which SRAM block?
        trans.initialize = 1'b1;
        // Not a read or write through DUT datapath
        trans.rdn_wr = 'x;
        trans.curr_wr_addr = calcVif.cb.initialize_addr;
        trans.loc_sel = calcVif.cb.initialize_loc_sel;

        if(trans.loc_sel == 1'b0) begin
          trans.lower_data = calcVif.cb.initialize_data;
          // Set the other half to 0 to avoid Xs in logs
          trans.upper_data = '0;
        end else begin
          trans.upper_data = calcVif.cb.initialize_data;
          // Set the other half to 0 to avoid Xs in logs
          trans.lower_data = '0;
        end
        //$display($stime, " Monitor: Initialize SRAM; Write to SRAM %s, Addr: 0x%0x, Data: 0x%0x\n", !calcVif.cb.initialize_loc_sel ? "A" : "B", calcVif.cb.initialize_addr, calcVif.cb.initialize_data);
        mon_box.put(trans);
      end
    end
  endtask : main

endclass : calc_monitor
