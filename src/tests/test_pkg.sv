package test_pkg;
  import uvm_pkg::*;
  `include "uvm_macros.svh"

  // Include base test
  `include "base_test.sv"

  // Routing tests
  `include "RouteRowFirstTest.sv"
  `include "RouteColumnFirstTest.sv"

  // Functional tests
  `include "PacketTransferTest.sv"
  `include "BroadcastTest.sv"
  `include "ErrorInjectionTest.sv"

  // FIFO / Flow control tests
  `include "FifoHandshakeTest.sv"
  `include "FifoOverflowTest.sv"

  // Arbiter tests
  `include "ArbiterContentionTest.sv"
  `include "ArbiterFairnessTest.sv"

  // Reset test
  `include "ResetMidTransferTest.sv"

  // Scalability test
  `include "ScalabilityTest.sv"

endpackage : test_pkg

