`timescale 1ns/1ps

import uvm_pkg::*;
import router_pkg::*;     
`include "uvm_macros.svh"

module tb;

    // Clock
    bit clk = 0;
    always #5 clk = ~clk;

    // Interface instance
    mesh_gen_if TB_IF (.clk(clk));

    initial begin
        // Give UVM the interface
        uvm_config_db#(virtual mesh_gen_if.TB)::set(
            null,
            "*",
            "vif",
            TB_IF
        );

        run_test();   // will use +UVM_TESTNAME=test_smoke
    end

endmodule