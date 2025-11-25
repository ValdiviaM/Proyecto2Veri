package router_pkg;

  import uvm_pkg::*;
  `include "uvm_macros.svh"

  // ----------------------------------------------------------
  // 1. Global Parameters
  // ----------------------------------------------------------
  parameter int ROWS       = 4;
  parameter int COLUMS     = 4;
  parameter int PCKG_SZ    = 40;           // Payload size (DATA_WIDTH)
  parameter int DATA_WIDTH = PCKG_SZ;      // Alias for consistency
  parameter int ADDR_WIDTH = 8;            // Adjust based on your DUT
  parameter int MAX_N_CYCLES = 16;
  
  // Derived parameters
  parameter int NUM_PORTS  = (ROWS*2) + (COLUMS*2);

  // ----------------------------------------------------------
  // 2. Scoreboard Macro Definitions
  // ----------------------------------------------------------
  // Defines 'uvm_analysis_imp_in' and 'uvm_analysis_imp_out'
  `uvm_analysis_imp_decl(_in)
  `uvm_analysis_imp_decl(_out)

  // ----------------------------------------------------------
  // 3. Class Includes (Order is strict!)
  // ----------------------------------------------------------
  
  // A. Transaction Object (Must be first)
  `include "../sequence_items/seq_item.sv"

  // B. Sequences (Needs seq_item)
  `include "../sequences/base_seq.sv"

  // C. Agent Components (Need seq_item)
  `include "../router_agent/sequencer.sv"
  `include "../router_agent/driver.sv"
  `include "../router_agent/monitor.sv"
  
  // D. The Agent (Needs driver, monitor, sequencer)
  `include "../router_agent/router_agent.sv"

  // E. Scoreboard (Needs seq_item)
  `include "../scoreboard/scoreboard.sv"
  `include "../scoreboard/router_subscriber.sv" 

  // F. Environment (Needs agent, scoreboard)
  `include "../env/router_env.sv"

  // G. Tests (Need env, sequences)
  `include "../tests/base_test.sv"
  `include "../tests/RouteRowFirstTest.sv"

endpackage : router_pkg
