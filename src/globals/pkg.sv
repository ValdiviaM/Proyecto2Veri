package router_pkg;

  import uvm_pkg::*;
  `include "uvm_macros.svh"

  // 1. Global Parameters
  parameter int ROWS       = 4;
  parameter int COLUMS     = 4;
  parameter int PCKG_SZ    = 40;
  parameter int DATA_WIDTH = PCKG_SZ;
  parameter int ADDR_WIDTH = 8;
  parameter int MAX_N_CYCLES = 16;
  
  parameter int NUM_PORTS  = (ROWS*2) + (COLUMS*2);

  // 2. Scoreboard Macro Definitions
  `uvm_analysis_imp_decl(_in)
  `uvm_analysis_imp_decl(_out)

  // 3. Class Includes
  `include "../sequence_items/seq_item.sv"
  `include "../sequences/base_seq.sv"
  `include "../sequences/sequence_lib.sv"    // <--- NEW

  `include "../router_agent/sequencer.sv"
  `include "../router_agent/driver.sv"
  `include "../router_agent/monitor.sv"
  `include "../router_agent/router_agent.sv"

  `include "../scoreboard/scoreboard.sv"
  `include "../scoreboard/router_subscriber.sv" 

  `include "../env/router_env.sv"

  `include "../tests/base_test.sv"
  `include "../tests/RouteRowFirstTest.sv"
  `include "../tests/test_lib.sv"           // <--- NEW

endpackage : router_pkg
