package router_pkg;

  import uvm_pkg::*;
  `include "uvm_macros.svh"

  // Global parameters
  parameter int ADDR_WIDTH  = 8;
  parameter int DATA_WIDTH  = 8;
  parameter int MAX_N_CYCLES = 16;



  // Sequence items
  `include "../sequence_items/seq_item.sv"


  // Sequences
  `include "../sequences/base_seq.sv"
  // `include "../sequences/router_sequence.sv"


  // Driver / Sequencer / Monitor

  `include "../router_agent/sequencer.sv"
  //`include "../router_agent/monitor.sv"


 

  // Scoreboard
  //`include "../scoreboard/scoreboard.sv"
  //`include "../scoreboard/subscriber.sv"

endpackage : router_pkg

