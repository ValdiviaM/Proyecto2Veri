`timescale 1ns/1ps

`include "uvm_macros.svh"
import uvm_pkg::*;
import router_pkg::*;

module tb;

  bit clk = 0;
  always #5 clk = ~clk;

  // Instancia de la interfaz
  mesh_gen_if #(ROWS, COLUMS, DATA_WIDTH) TB_IF (.clk(clk));

  // DUT
  router_top #(
    .ROWS    (ROWS),
    .COLUMS  (COLUMS),
    .PCKG_SZ (DATA_WIDTH)
  ) dut (
    .clk          (TB_IF.clk),
    .reset        (TB_IF.reset),

    // TB ? DUT
    .pndng_i_in    (TB_IF.pndng_i_in),
    .data_out_i_in (TB_IF.data_out_i_in),
    .popin         (TB_IF.popin),

    // DUT ? TB
    .pndng         (TB_IF.pndng),
    .data_out      (TB_IF.data_out),
    .pop           (TB_IF.pop)
  );

  initial begin
      // Reset
      TB_IF.reset = 1'b1;
      repeat (5) @(posedge clk);
      TB_IF.reset = 1'b0;

      // DRIVER gets TB modport
      uvm_config_db#(
        virtual mesh_gen_if #(ROWS, COLUMS, DATA_WIDTH).TB
      )::set(null, "*", "vif", TB_IF.TB);

      // MONITOR gets MON modport
      uvm_config_db#(
        virtual mesh_gen_if #(ROWS, COLUMS, DATA_WIDTH).MON
      )::set(null, "*", "vif", TB_IF.MON);

      run_test();
  end

endmodule

