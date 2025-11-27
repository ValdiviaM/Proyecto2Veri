`timescale 1ns/1ps
import uvm_pkg::*;
import router_pkg::*;

module tb_top;

    // ======================================================
    // PARAMETERS
    // ======================================================
    localparam int ROWS    = router_pkg::ROWS;
    localparam int COLUMS  = router_pkg::COLUMS;
    localparam int PCK_SZ  = router_pkg::DATA_WIDTH; 

    // ======================================================
    // CLOCK GENERATION
    // ======================================================
    bit clk;
    initial begin
        clk = 0;
        forever #5 clk = ~clk; // Clock period = 10ns
    end

    // ======================================================
    // INTERFACE INSTANCE
    // ======================================================
    mesh_gen_if #(ROWS, COLUMS, PCK_SZ) vif(clk);

    // ======================================================
    // DUT INSTANCE
    // ======================================================
    mesh_gnrtr #(
        .ROWS(ROWS), 
        .COLUMS(COLUMS), 
        .pckg_sz(PCK_SZ), 
        .fifo_depth(4), 
        .bdcst({8{1'b1}})  // Broadcast mask
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
    // BLOCK 1: UVM STARTUP
    // ======================================================
    initial begin
        // 1. Register the virtual interface for UVM components
        uvm_config_db#(virtual mesh_gen_if #(ROWS, COLUMS, PCK_SZ))::set(null, "*", "vif", vif);
        
        // 2. Start the test
        // You can change the string to any UVM test name, e.g., "reset_test"
        run_test("base_test");  
    end

    // ======================================================
    // BLOCK 2: RESET GENERATION
    // ======================================================
    initial begin
        vif.reset = 1'b1;       // Assert reset
        repeat(10) @(posedge clk); // Hold reset for 10 clock cycles
        vif.reset = 1'b0;       // Release reset
    end

    // ======================================================
    // BLOCK 3: WAVEFORM DUMP (FOR DEBUGGING)
    // ======================================================
    initial begin
        $dumpfile("router_dump.vcd");
        $dumpvars(0, tb_top); // Dump all signals in tb_top hierarchy
    end

endmodule
