`timescale 1ns/1ps
`include "uvm_macros.svh"
import uvm_pkg::*;
import router_pkg::*;

module tb_top;   
  localparam int ROWS    = router_pkg::ROWS;
  localparam int COLUMS  = router_pkg::COLUMS;
  localparam int PCKG_SZ = router_pkg::PCKG_SZ;

  bit clk = 0;
  always #5 clk = ~clk;

  // Interface instance
  mesh_gen_if #(ROWS, COLUMS, PCKG_SZ) vif (.clk(clk));

  // DUT instantiation
  mesh_gnrtr #(
    .ROWS(ROWS),
    .COLUMS(COLUMS),
    .pckg_sz(PCKG_SZ),
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

  initial begin
      vif.reset = 1'b1;
      repeat (5) @(posedge clk);
      vif.reset = 1'b0;

      // DRIVER ? TB modport
      uvm_config_db#(
        virtual mesh_gen_if #(ROWS, COLUMS, PCKG_SZ).TB
      )::set(null, "*", "vif", vif.TB);

      // MONITOR ? MON modport
      uvm_config_db#(
        virtual mesh_gen_if #(ROWS, COLUMS, PCKG_SZ).MON
      )::set(null, "*", "vif", vif.MON);

      run_test();
  end

endmodule

