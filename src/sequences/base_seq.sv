
// router_sequence.sv

class router_sequence #(parameter ADDR_WIDTH = 8,
                        parameter DATA_WIDTH = 8,
                        parameter MAX_N_CYCLES = 16)
  extends uvm_sequence #(seq_item #(ADDR_WIDTH, DATA_WIDTH, MAX_N_CYCLES));

  `uvm_object_utils(router_sequence)


  // CONTROLLED FROM TESTS (KNOBS)
  int num_trans        = 100;  // overridden by test_base
  int src_terminal     = -1;   // -1 = randomized
  int dst_terminal     = -1;   // -1 = randomized
  bit force_broadcast  = 0;
  bit inject_error     = 0;
  bit reset_mid_tx     = 0;
  bit fifo_stress      = 0;
  bit route_mode       = 1;    // default: ROW_FIRST

  function new(string name="router_sequence");
    super.new(name);
  endfunction


  // MAIN BODY
  virtual task body();

    `uvm_info("SEQ", 
       $sformatf("router_sequence starting with %0d transactions", num_trans),
       UVM_MEDIUM)

    for (int i=0; i<num_trans; i++) begin

      seq_item item;
      item = seq_item::type_id::create($sformatf("item_%0d", i));

      start_item(item);

      assert(item.randomize());


      // APPLY FORCED FIELDS (TEST CONTROLS)
      if (src_terminal != -1)
        item.addr = src_terminal;

      if (dst_terminal != -1)
        item.data = dst_terminal;

      if (force_broadcast)
        item.broadcast = 1;

      if (inject_error)
        item.msg_error = seq_item::HAS_ERR;

      // routing mode override
      item.mode = (route_mode) 
                  ? seq_item::ROW_FIRST 
                  : seq_item::COL_FIRST;

      finish_item(item);

      // reset injected in mid-transaction (Test 1.7)
      if (reset_mid_tx && (i == num_trans/2)) begin
         `uvm_info("SEQ", "Triggering mid-transfer reset", UVM_HIGH)
         // driver or top_tb must observe this flag
      end

      if ((i % 100) == 0)
        `uvm_info("SEQ",
                  $sformatf("Generated %0d / %0d items", i, num_trans),
                  UVM_LOW)

    end

    `uvm_info("SEQ", "Sequence COMPLETED", UVM_MEDIUM)

  endtask : body

endclass : router_sequence

