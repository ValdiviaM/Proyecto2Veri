// router_monitor.sv

`include "uvm_macros.svh"
import uvm_pkg::*;
import router_pkg::*;

class router_monitor extends uvm_monitor;
  `uvm_component_utils(router_monitor)

  uvm_analysis_port #(seq_item) ap_in;
  uvm_analysis_port #(seq_item) ap_out;

  virtual mesh_gen_if #(ROWS, COLUMS, DATA_WIDTH).MON vif;

  function new(string name="router_monitor", uvm_component parent=null);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    if (!uvm_config_db#(virtual mesh_gen_if #(ROWS, COLUMS, DATA_WIDTH).MON)::get(this, "", "vif", vif))
      `uvm_fatal("MON", "Could not get vif (MON)")
    
    ap_in  = new("ap_in",  this);
    ap_out = new("ap_out", this);
  endfunction

  virtual task run_phase(uvm_phase phase);
    int NUM_PORTS = ROWS*2 + COLUMS*2;

    forever begin
      @(posedge vif.clk);
      if (!vif.reset) begin
        for (int i = 0; i < NUM_PORTS; i++) begin
          // Lado de entrada (TB?DUT): pndng_i_in & pop
          if (vif.pndng_i_in[i] && vif.pop[i]) begin
            seq_item item_in = seq_item::type_id::create($sformatf("item_in_%0d", i), this);
            item_in.data = vif.data_out_i_in[i];
            item_in.src  = i[ADDR_WIDTH-1:0];
            ap_in.write(item_in);
          end

          // Lado de salida (DUT?TB): pndng & popin
          if (vif.pndng[i] && vif.popin[i]) begin
            seq_item item_out = seq_item::type_id::create($sformatf("item_out_%0d", i), this);
            item_out.out_dut  = vif.data_out[i];
            item_out.out_port = i[ADDR_WIDTH-1:0];
            ap_out.write(item_out);
          end
        end
      end
    end
  endtask

endclass

