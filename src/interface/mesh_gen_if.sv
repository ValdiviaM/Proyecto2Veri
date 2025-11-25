import uvm_pkg::*;
`include "uvm_macros.svh"

interface mesh_gen_if #(
    parameter int ROWS    = 4,
    parameter int COLUMS  = 4,
    parameter int PCKG_SZ = 40 // Ensure this matches your DATA_WIDTH
) (input logic clk);

    logic reset;

    // ============================================================
    // 1. WIRES (Physical connections to DUT)
    // ============================================================
    
    // Group A: DUT Outputs (Router -> TB)
    // The Router wants to send data out.
    wire                    pndng    [ROWS*2+COLUMS*2]; // Output Valid
    wire [PCKG_SZ-1:0]      data_out [ROWS*2+COLUMS*2]; // Output Data
    wire                    pop      [ROWS*2+COLUMS*2]; // Input Ack (DUT accepts TB injection)

    // Group B: DUT Inputs (TB -> Router)
    // The Router receives data or acknowledgements.
    wire                    pndng_i_in    [ROWS*2+COLUMS*2]; // Input Valid
    wire [PCKG_SZ-1:0]      data_out_i_in [ROWS*2+COLUMS*2]; // Input Data
    wire                    popin         [ROWS*2+COLUMS*2]; // Output Ack (TB accepts DUT output)

    // ============================================================
    // 2. DRIVER LOGIC (TB -> Wires)
    // ============================================================
    
    // Intermediate logic signals that the Driver/Sequencer will write to
    logic                    drv_pndng_i_in    [ROWS*2+COLUMS*2];
    logic [PCKG_SZ-1:0]      drv_data_out_i_in [ROWS*2+COLUMS*2];
    logic                    drv_popin         [ROWS*2+COLUMS*2]; // TB Acknowledgement

    // Connect Driver Logic to DUT Input Wires
    genvar gi;
    generate
      for (gi = 0; gi < ROWS*2+COLUMS*2; gi++) begin : BRIDGE
        assign pndng_i_in[gi]    = drv_pndng_i_in[gi];
        assign data_out_i_in[gi] = drv_data_out_i_in[gi];
        assign popin[gi]         = drv_popin[gi]; 
      end
    endgenerate

    // ============================================================
    // 3. DUMMY CONSUMER (Automatic ACK for Router Outputs)
    // ============================================================
    // If the Router has data (pndng), we assert popin (Ack) 
    // so the router empties its buffer.
    always @(posedge clk) begin
        if (reset) begin
            for (int k = 0; k < ROWS*2+COLUMS*2; k++)
                drv_popin[k] <= 1'b0;
        end else begin
            for (int k = 0; k < ROWS*2+COLUMS*2; k++)
                drv_popin[k] <= pndng[k]; 
        end
    end

    // ============================================================
    // 4. MODPORTS
    // ============================================================

    modport TB (
        input  clk,
        output reset,

        // TB Drives these (Injection)
        output drv_pndng_i_in,
        output drv_data_out_i_in,
        
        // TB Drives this (Ejection/Ack)
        output drv_popin,

        // TB Reads these (Monitoring/Handshake)
        input  pndng,
        input  data_out,
        input  pop // DUT Acknowledgement
    );

    modport MON (
        input clk, reset,
        input pndng, data_out, pop,
        input pndng_i_in, data_out_i_in, popin
    );

    modport DUT (
        input  clk, reset,
        // DUT inputs
        input  pndng_i_in,
        input  data_out_i_in,
        input  popin,
        // DUT outputs
        output pndng,
        output data_out,
        output pop
    );

    // ============================================================
    // 5. ASSERTIONS (Protocol Checkers)
    // ============================================================

    generate
      for (genvar i = 0; i < ROWS*2+COLUMS*2; i++) begin : PROTOCOL

        // A. Router Output Protocol (DUT -> TB)
        // -------------------------------------
        
        // 1. Data must remain stable while Pending is high, until acknowledged (popin)
        property data_stable_until_popin;
            @(posedge clk) disable iff (reset)
            (pndng[i] && !popin[i]) |=> $stable(data_out[i]);
        endproperty
        assert property(data_stable_until_popin) else `uvm_error("IF", $sformatf("Port %0d: Data changed while PNDNG high without POPIN", i));

        // 2. TB shouldn't ACK unless there is a request
        property popin_only_when_valid;
            @(posedge clk) disable iff (reset)
            popin[i] |-> pndng[i];
        endproperty
        assert property(popin_only_when_valid) else `uvm_error("IF", $sformatf("Port %0d: POPIN asserted without PNDNG", i));

        // B. Router Input Protocol (TB -> DUT)
        // ------------------------------------

        // 3. If TB requests injection (pndng_i_in), DUT must eventually ACK (pop)
        // Note: usage of [1:$] implies liveness. If simulation ends early, this might not fire.
        property tb_req_acknowledged;
            @(posedge clk) disable iff (reset)
            pndng_i_in[i] |-> ##[1:$] pop[i];
        endproperty
        assert property(tb_req_acknowledged) else `uvm_warning("IF", $sformatf("Port %0d: Request stuck, never acknowledged by DUT", i));

        // 4. TB Data must be stable during request until ACK
        property tb_data_stable_during_req;
            @(posedge clk) disable iff (reset)
            (pndng_i_in[i] && !pop[i]) |=> $stable(data_out_i_in[i]);
        endproperty
        assert property(tb_data_stable_during_req) else `uvm_error("IF", $sformatf("Port %0d: Driver changed Data during PNDNG without POP", i));

        // 5. DUT should only POP if TB is actually offering data
        property pop_only_when_tb_has_data;
            @(posedge clk) disable iff (reset)
            pop[i] |-> pndng_i_in[i];
        endproperty
        assert property(pop_only_when_tb_has_data) else `uvm_error("IF", $sformatf("Port %0d: DUT asserted POP without PNDNG_I_IN", i));

      end
    endgenerate

endinterface
