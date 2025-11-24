// router_driver.sv


class router_driver extends uvm_driver #(seq_item#(ADDR_WIDTH, DATA_WIDTH, MAX_N_CYCLES));
  `uvm_component_utils(router_driver)

  virtual mesh_gen_if vif;
  seq_item#(ADDR_WIDTH, DATA_WIDTH, MAX_N_CYCLES) req;

  // Constructor
  function new(string name="router_driver", uvm_component parent=null);
    super.new(name, parent);
  endfunction

  // Build phase
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    if (!uvm_config_db#(virtual mesh_gen_if)::get(this, "", "vif", vif))
      `uvm_fatal("DRV", "No VIF found in config DB!")
    else
      `uvm_info("DRV", "Virtual interface OK", UVM_LOW)
  endfunction

  // Main run loop
  task run_phase(uvm_phase phase);
    super.run_phase(phase);

    forever begin
      seq_item_port.get_next_item(req);
      drive(req);
      seq_item_port.item_done();
    end
  endtask

  
  // DRIVE 1 TRANSACTION (PROTOCOL-COMPLIANT)
 
  task drive(seq_item t);

    int src_port;
    bit [DATA_WIDTH-1:0] local_data;

    // Select terminal: use t.src if present
    src_port = (t.src < (ROWS*2 + COLUMS*2)) ? t.src : 0;

    // Apply error type (simple example)
    local_data = t.data;

    if (t.msg_error == seq_item::HDR_ERROR)
      local_data[DATA_WIDTH-1] = ~local_data[DATA_WIDTH-1]; // corrupt MSB

    else if (t.msg_error == seq_item::PAY_ERROR)
      local_data[0] = ~local_data[0]; // corrupt LSB

    
    // PROTOCOL STEP 1: Drive TB request: data + pndng_i_in
    
    @(vif.cb);

    vif.cb.data_out_i_in[src_port] <= local_data;
    vif.cb.pndng_i_in[src_port]    <= 1'b1;

    `uvm_info("DRV",
      $sformatf("Sending packet on port %0d  data=0x%0h  dst=%0d  mode=%0d  bdcst=%0b  err=%0d",
                src_port, local_data, t.addr, t.mode, t.broadcast, t.msg_error),
      UVM_MEDIUM);


    // PROTOCOL STEP 2: Wait until DUT acknowledges with pop[src]
    
    @(vif.cb);
    wait (vif.cb.pop[src_port] == 1'b1);

    `uvm_info("DRV",
      $sformatf("DUT acknowledged pop on port %0d", src_port),
      UVM_LOW);

    
    // PROTOCOL STEP 3: Drop pndng_i_in after pop
    
    @(vif.cb);
    vif.cb.pndng_i_in[src_port] <= 1'b0;

    
    // PROTOCOL STEP 4: Idle cycles = gap
    
    repeat (t.cycles_between) @(vif.cb);

  endtask

endclass : router_driver

