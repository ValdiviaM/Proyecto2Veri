
//Container of the entire UVM environment pkg.sv
package router_pkg;

  // Import UVM
  import uvm_pkg::*;
  `include "uvm_macros.svh"

  // --- Sequence items ---
  `include "sequence_items/packets.sv"

  // --- Sequences ---
  `include "sequences/base_seq.sv"

  // --- Agent components ---
  `include "router_agent/driver.sv"
  `include "router_agent/monitor.sv"
  `include "router_agent/sequencer.sv"

  // --- Scoreboard components ---
  `include "scoreboard/scoreboard.sv"
  `include "scoreboard/subscriber.sv"

endpackage : router_pkg
