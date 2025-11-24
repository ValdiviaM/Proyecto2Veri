// router_sequencer.sv 

class router_sequencer #(parameter ADDR_WIDTH = 8,
                         parameter DATA_WIDTH = 8,
                         parameter MAX_N_CYCLES = 16)
  extends uvm_sequencer #(seq_item#(ADDR_WIDTH, DATA_WIDTH, MAX_N_CYCLES));

  `uvm_component_param_utils(router_sequencer#(ADDR_WIDTH, DATA_WIDTH, MAX_N_CYCLES))

  function new(string name = "router_sequencer", uvm_component parent=null);
    super.new(name, parent);
  endfunction

endclass : router_sequencer
