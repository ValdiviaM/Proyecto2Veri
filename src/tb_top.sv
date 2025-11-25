`timescale 1ns/1ps
import uvm_pkg::*;
import router_pkg::*;

module tb_top;

    localparam int ROWS    = router_pkg::ROWS;
    localparam int COLUMS  = router_pkg::COLUMS;
    localparam int PCK_SZ  = router_pkg::DATA_WIDTH; 

    bit clk;
    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end

    mesh_gen_if #(ROWS, COLUMS, PCK_SZ) vif(clk);

    mesh_gnrtr #(
        .ROWS(ROWS), 
        .COLUMS(COLUMS), 
        .pckg_sz(PCK_SZ), 
        .fifo_depth(4), 
        .bdcst({8{1'b1}})
    ) dut (
        .clk(clk),
        .reset(vif.reset),
        .pndng(vif.pndng),
        .data_out(vif.data_out),
        .popin(vif.popin),
        .pop(vif.pop),
        .data_out_i_in(vif.data_out_i_in),
        .pndng_i_in(vif.pndng_i_in)
    );

    // ======================================================
    // BLOCK 1: UVM STARTUP (MUST RUN AT TIME 0)
    // ======================================================
    initial begin
        // 1. Register Interface
        uvm_config_db#(virtual mesh_gen_if #(ROWS, COLUMS, PCK_SZ))::set(null, "*", "vif", vif);
        
        // 2. Start Test
        // Explicitly tell UVM which test to run
        run_test("base_test");  // <--- CHANGE THIS LINE
    end

    // ======================================================
    // BLOCK 2: RESET GENERATION (RUNS IN PARALLEL)
    // ======================================================
    initial begin
        vif.reset = 1'b1;
        
        // This delay is fine here because run_test() is already active
        // in the other block. The Driver will wait for this reset 
        // to drop before sending packets.
        repeat(10) @(posedge clk);
        vif.reset = 1'b0;
    end

    initial begin
        $dumpfile("router_dump.vcd");
        $dumpvars(0, tb_top);
    end

endmodule
