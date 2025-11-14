
//Container of the entire UVM environment pkg.sv
package router_pkg;

// global parameters for UVM environment
parameter int ADDR_WIDTH = 8;
parameter int DATA_WIDTH = 8;
parameter int MAX_N_CYCLES = 16;

  // Import UVM
  import uvm_pkg::*;
  `include "uvm_macros.svh"

  // --- Sequence items ---
//  `include "sequence_items/seq_item.sv"

  // --- Sequences ---
//  `include "sequences/base_seq.sv"


  
endpackage : router_pkg
