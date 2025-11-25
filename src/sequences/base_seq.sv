// router_sequence.sv

class router_sequence extends uvm_sequence #(seq_item);

  `uvm_object_utils(router_sequence)

  // CONTROL DESDE EL TEST
  int num_trans        = 200;
  int src_terminal     = -1;
  int dst_terminal     = -1;
  bit route_mode       = 1;   // 1=ROW_FIRST, 0=COL_FIRST
  bit force_broadcast  = 0;
  bit inject_error     = 0;
  bit reset_mid_tx     = 0;
  bit fifo_stress      = 0;

  function new(string name="router_sequence");
    super.new(name);
  endfunction

  virtual task body();

    `uvm_info("SEQ", $sformatf("Starting sequence with %0d items", num_trans), UVM_MEDIUM)

    for (int i = 0; i < num_trans; i++) begin
      seq_item item = seq_item::type_id::create($sformatf("item_%0d", i));

      start_item(item);
      assert(item.randomize());

      // Overrides
      if (dst_terminal != -1)
        item.addr = dst_terminal;

      if (src_terminal != -1)
        item.src = src_terminal;

      item.mode = (route_mode) 
                  ? seq_item::ROW_FIRST
                  : seq_item::COL_FIRST;

      if (force_broadcast)
        item.broadcast = 1;

      if (inject_error) begin
        if ($urandom_range(0,1))
            item.msg_error = seq_item::HDR_ERROR;
        else
            item.msg_error = seq_item::PAY_ERROR;
      end

      finish_item(item);

      if (reset_mid_tx && i == num_trans/2)
        `uvm_info("SEQ", "Mid-transfer reset requested", UVM_HIGH)

      if (fifo_stress && (i % 25 == 0))
        `uvm_info("SEQ", "FIFO stress event triggered", UVM_LOW)
    end

    `uvm_info("SEQ", "Sequence completed", UVM_MEDIUM)

  endtask

endclass

