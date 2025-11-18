`include "uvm_macros.svh"
import uvm_pkg::*;
import router_pkg::*;

// Driver class
class router_driver extends uvm_driver #(seq_item#(ADDR_WIDTH, DATA_WIDTH, MAX_N_CYCLES));
  `uvm_component_utils(router_driver)

  // virtual interface handle
  virtual mesh_gen_if vif;
  seq_item#(ADDR_WIDTH, DATA_WIDTH, MAX_N_CYCLES) req;


  // constructor
  function new(string name = "router_driver", uvm_component parent = null);
    super.new(name, parent);
    `uvm_info("DRV", "Inside constructor", UVM_HIGH);
  endfunction

  // build phase
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    `uvm_info("DRV", "build_phase", UVM_HIGH);

    // get the interface from config DB
    if (!uvm_config_db#(virtual mesh_gen_if)::get(this, "", "vif", vif))
      `uvm_fatal("DRV", "Cannot get virtual interface from config DB")
    else
      `uvm_info("DRV", "Got virtual interface OK", UVM_LOW);
  endfunction

  // run phase
  task run_phase(uvm_phase phase);
    super.run_phase(phase);
    `uvm_info("DRV", "Run phase", UVM_HIGH);

    forever begin
      // create / reuse request item
      if (req == null)
        req = seq_item::type_id::create("req", this);

      // Get item from sequencer
      seq_item_port.get_next_item(req);

      `uvm_info("DRV",
                $sformatf("Start driving: addr=%0d data=%0d mode=%0d",
                          req.addr, req.data, req.mode),
                UVM_MEDIUM);

      // drive the transaction
      drive(req);

      `uvm_info("DRV", "Finished Driving", UVM_HIGH);
      seq_item_port.item_done();
    end
  endtask

  // Drive task
  task drive(seq_item t);
    int unsigned port = 0;

    // wait for clocking block edge
    @(vif.cb);

    vif.cb.data_out_i_in[port] <= t.data;
    vif.cb.pndng_i_in[port]    <= 1'b1;

    `uvm_info("DRV",
              $sformatf("Driving port=%0d data=%0h", port, t.data),
              UVM_MEDIUM);

    // wait a cycle
    @(vif.cb);

    vif.cb.pndng_i_in[port] <= 1'b0;
  endtask

endclass : router_driver

