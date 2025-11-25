
// router_driver.sv 

`include "uvm_macros.svh"
import uvm_pkg::*;
import router_pkg::*;

class router_driver extends uvm_driver #(seq_item);
  `uvm_component_utils(router_driver)

  // Must match the TB modport passed by agent
  virtual mesh_gen_if #(ROWS, COLUMS, DATA_WIDTH).TB vif;

  seq_item req;

  // -------------------------------------------------------------
  function new(string name="router_driver", uvm_component parent=null);
    super.new(name, parent);
  endfunction

  // -------------------------------------------------------------
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    if (!uvm_config_db#(
          virtual mesh_gen_if #(ROWS, COLUMS, DATA_WIDTH).TB
        )::get(this, "", "vif", vif))
      `uvm_fatal("DRV", "Driver could not get TB modport VIF")
    else
      `uvm_info("DRV", "Driver VIF OK", UVM_LOW)
  endfunction

  // -------------------------------------------------------------
  task run_phase(uvm_phase phase);

    // Initialize all TB?DUT inputs to avoid X propagation
    for (int i = 0; i < NUM_PORTS; i++) begin
      vif.drv_pndng_i_in[i]    <= 1'b0;
      vif.drv_data_out_i_in[i] <= '0;
    end

    // Mandatory: wait for reset to go low
    @(posedge vif.clk);
    wait(vif.reset == 1'b0);

    `uvm_info("DRV", "Reset released  Driver ACTIVE", UVM_LOW)

    forever begin
      seq_item_port.get_next_item(req);
      drive(req);
      seq_item_port.item_done();
    end
  endtask


  // DRIVE ONE TRANSACTION

  task drive(seq_item t);

    int port = t.src;

    if (port >= NUM_PORTS) begin
      `uvm_error("DRV", $sformatf("Invalid source port %0d", port))
      return;
    end

    // Compute payload, apply errors
    bit [DATA_WIDTH-1:0] payload = t.data;

    case (t.msg_error)
      seq_item::HDR_ERROR: payload[DATA_WIDTH-1] = ~payload[DATA_WIDTH-1];
      seq_item::PAY_ERROR: payload[0]            = ~payload[0];
      default: /* NO_ERROR */ ;
    endcase


    // Step 1  Assert TB request to DUT

    @(posedge vif.clk);

    vif.drv_data_out_i_in[port] <= payload;
    vif.drv_pndng_i_in[port]    <= 1'b1;

    `uvm_info("DRV",
      $sformatf("SEND: port=%0d data=0x%0h dst=%0d mode=%0d bdcst=%0b err=%0d",
                port, payload, t.addr, t.mode, t.broadcast, t.msg_error),
      UVM_MEDIUM)


    // Step 2  Wait DUT ACK (pop)

    fork
      // ACK detection
      begin : wait_ack
        while (vif.pop[port] == 1'b0) @(posedge vif.clk);
        `uvm_info("DRV",
          $sformatf("ACK from DUT on port %0d", port),
          UVM_LOW)
      end

      // Watchdog (timeout)
      begin : watchdog
        repeat (200) @(posedge vif.clk);
        `uvm_error("DRV",
          $sformatf("TIMEOUT waiting for pop[%0d]", port))
      end
    join_any
    disable fork;


    // Step 3  Drop request

    @(posedge vif.clk);
    vif.drv_pndng_i_in[port] <= 1'b0;


    // Step 4  Inter-packet delay

    repeat (t.cycles_between) @(posedge vif.clk);

  endtask : drive

endclass : router_driver

