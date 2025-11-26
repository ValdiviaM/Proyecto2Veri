class coverage_seq extends base_seq;
  `uvm_object_utils(coverage_seq)

  function new(string name = "coverage_seq");
    super.new(name);
  endfunction

  virtual task body();
    seq_item req_item;

    // -------------------------------------------------------
    // LOOP 1: Hit the Source x Destination Matrix (Unicast)
    // -------------------------------------------------------
    // We loop through every Source (0-15) and every Dest (0-15)
    for (int s = 0; s < 16; s++) begin
      for (int d = 0; d < 16; d++) begin
        if (s == d) continue; // Skip if loopback is invalid in your DUT

        req_item = seq_item::type_id::create("req_item");
        start_item(req_item);
        
        // Force the specific Source and Destination
        assert(req_item.randomize() with {
            src == s;
            addr == d;
            broadcast == 0;      // Pure Unicast
            msg_error == seq_item::NO_ERROR; 
            cycles_between inside {[0:2]}; // Fast traffic
        });
        
        finish_item(req_item);
      end
    end

    // -------------------------------------------------------
    // LOOP 2: Hit the Broadcasts
    // -------------------------------------------------------
    // Make every source send a broadcast
    for (int s = 0; s < 16; s++) begin
        req_item = seq_item::type_id::create("req_item");
        start_item(req_item);
        assert(req_item.randomize() with {
            src == s;
            broadcast == 1; // Force Broadcast
        });
        finish_item(req_item);
    end

    // -------------------------------------------------------
    // LOOP 3: Error Injection
    // -------------------------------------------------------
    // Pick random sources to send Errors
    repeat(50) begin
        req_item = seq_item::type_id::create("req_item");
        start_item(req_item);
        assert(req_item.randomize() with {
            msg_error inside {seq_item::HDR_ERROR, seq_item::PAY_ERROR};
        });
        finish_item(req_item);
    end

  endtask
endclass
