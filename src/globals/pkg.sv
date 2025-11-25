package router_pkg;

  import uvm_pkg::*;
  `include "uvm_macros.svh"

  // Global parameters
  parameter int ADDR_WIDTH  = 8;
  parameter int DATA_WIDTH  = 8;
  parameter int MAX_N_CYCLES = 16;
  parameter int PCKG_SZ = 40;
  parameter int COLUMS = 4;
  parameter int ROWS = 4;


  // Sequence items
  `include "../sequence_items/seq_item.sv"


  // Sequences
  `include "../sequences/base_seq.sv"



  // Driver / Sequencer / Monitor

  `include "../router_agent/sequencer.sv"



endpackage : router_pkg

