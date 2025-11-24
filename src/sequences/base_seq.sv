// router_sequence.sv 
class router_sequence #(parameter ADDR_WIDTH = 8,
                        parameter DATA_WIDTH = 8,
                        parameter MAX_N_CYCLES = 16)
  extends uvm_sequence #(seq_item #(ADDR_WIDTH, DATA_WIDTH, MAX_N_CYCLES));

  `uvm_object_utils(router_sequence)


  // CONTROL FIELDS (set by base_test)
  int num_trans        = 200;
  int src_terminal     = -1;   // controlled by DRIVER
  int dst_terminal     = -1;   // destination terminal
  bit route_mode       = 1;    // 1=ROW_FIRST, 0=COL_FIRST
  bit force_broadcast  = 0;
  bit inject_error     = 0;
  bit reset_mid_tx     = 0;
  bit fifo_stress      = 0;

  function new(string name="router_sequence");
    super.new(name);
  endfunction


  // MAIN SEQUENCE BODY
  virtual task body();

    `uvm_info("SEQ", $sformatf("Starting sequence with %0d items", num_trans), UVM_MEDIUM)

    for (int i = 0; i < num_trans; i++) begin

      seq_item item = seq_item::type_id::create($sformatf("item_%0d", i));

      start_item(item);
      assert(item.randomize());


      // APPLY CONTROL OVERRIDES

      // DESTINATION terminal override
      if (dst_terminal != -1)
        item.addr = dst_terminal;

      // SRC terminal is overridden here for scoreboard reference
      if (src_terminal != -1)
        item.src = src_terminal;

      // ROUTE MODE
      item.mode = (route_mode) 
                  ? seq_item::ROW_FIRST
                  : seq_item::COL_FIRST;

      // BROADCAST FORCED
      if (force_broadcast)
        item.broadcast = 1;

      // ERROR TYPE OVERRIDE
      if (inject_error) begin
        // Randomly pick header or payload error
        if ($urandom_range(0,1))
            item.msg_error = seq_item::HDR_ERROR;
        else
            item.msg_error = seq_item::PAY_ERROR;
      end

      finish_item(item);

      // EXTRA EVENTS (stress and reset)
      if (reset_mid_tx && i == num_trans/2)
        `uvm_info("SEQ", "Mid-transfer reset requested", UVM_HIGH)

      if (fifo_stress && (i % 25 == 0))
        `uvm_info("SEQ", "FIFO stress event triggered", UVM_LOW)

    end

    `uvm_info("SEQ", "Sequence completed", UVM_MEDIUM)

  endtask

endclass

