import uvm_pkg::*;
`include "uvm_macros.svh"

interface mesh_gen_if #(
    parameter int ROWS    = 4,
    parameter int COLUMS  = 4,
    parameter int PCKG_SZ = 40
) (input logic clk);

    logic reset;

    // ============================================================
    // 1. WIRES (Physical connections to DUT)
    // ============================================================
    
    // ------------------------------------------------------------
    // Group A: Injection Channels (TB -> DUT)
    // ------------------------------------------------------------
    // TB sends Data + Valid. DUT sends Ack (popin).
    logic                   drv_pndng_i_in    [ROWS*2+COLUMS*2]; // Driven by Driver
    logic [PCKG_SZ-1:0]     drv_data_out_i_in [ROWS*2+COLUMS*2]; // Driven by Driver
    wire                    popin             [ROWS*2+COLUMS*2]; // Driven by DUT (Ack)

    // Wires connecting logic to DUT inputs
    wire                    pndng_i_in        [ROWS*2+COLUMS*2];
    wire [PCKG_SZ-1:0]      data_out_i_in     [ROWS*2+COLUMS*2];

    // ------------------------------------------------------------
    // Group B: Ejection Channels (DUT -> TB)
    // ------------------------------------------------------------
    // DUT sends Data + Valid. TB sends Ack (pop).
    wire                    pndng             [ROWS*2+COLUMS*2]; // Driven by DUT
    wire [PCKG_SZ-1:0]      data_out          [ROWS*2+COLUMS*2]; // Driven by DUT
    
    logic                   drv_pop           [ROWS*2+COLUMS*2]; // Driven by Dummy Consumer
    wire                    pop               [ROWS*2+COLUMS*2]; // Connected to DUT Input

    // ============================================================
    // 2. ASSIGNMENTS (Logic -> Wire Bridges)
    // ============================================================
    genvar gi;
    generate
      for (gi = 0; gi < ROWS*2+COLUMS*2; gi++) begin : BRIDGE
        // Injection (TB -> DUT)
        assign pndng_i_in[gi]    = drv_pndng_i_in[gi];
        assign data_out_i_in[gi] = drv_data_out_i_in[gi];
        
        // Ejection (DUT -> TB) - TB drives 'pop'
        assign pop[gi]           = drv_pop[gi];
      end
    endgenerate

// ============================================================
    // 3. DUMMY CONSUMER (Auto-Ack for DUT Outputs)
    // ============================================================
    // OLD (Incorrect - causing 1 cycle delay error):
    /*
    always @(posedge clk) begin
        if (reset) begin
            for (int k = 0; k < ROWS*2+COLUMS*2; k++)
                drv_pop[k] <= 1'b0;
        end else begin
            for (int k = 0; k < ROWS*2+COLUMS*2; k++)
                drv_pop[k] <= pndng[k]; 
        end
    end
    */

    // - Combinatorial):
    // Immediately assert pop if pndng is high.
    // When DUT drops pndng, pop drops instantly.
    always_comb begin
        for (int k = 0; k < ROWS*2+COLUMS*2; k++) begin
            if (reset)
                drv_pop[k] = 1'b0;
            else
                drv_pop[k] = pndng[k]; 
        end
    end

    // ============================================================
    // 4. MODPORTS
    // ============================================================

    modport TB (
        input  clk,
        output reset,

        // Injection: TB Drives Data/Valid, Reads Ack (popin)
        output drv_pndng_i_in,
        output drv_data_out_i_in,
        input  popin,

        // Ejection: TB Reads Data/Valid (Ack handled by dummy logic above)
        input  pndng,
        input  data_out,
        // (Internal visibility of drv_pop if needed)
        output drv_pop
    );

    modport MON (
        input clk, reset,
        // Monitor needs to see all physical wires
        input pndng, data_out, pop,          // Ejection Side
        input pndng_i_in, data_out_i_in, popin // Injection Side
    );

    modport DUT (
        input  clk, reset,
        
        // Injection Inputs (from TB)
        input  pndng_i_in,
        input  data_out_i_in,
        // Injection Output (Ack to TB)
        output popin,

        // Ejection Outputs (to TB)
        output pndng,
        output data_out,
        // Ejection Input (Ack from TB)
        input  pop
    );

    // ============================================================
    // 5. ASSERTIONS
    // ============================================================
    // Note: 'popin' is DUT->TB (Ack for Injection)
    //       'pop'   is TB->DUT (Ack for Ejection)

    generate
      for (genvar i = 0; i < ROWS*2+COLUMS*2; i++) begin : PROTOCOL

        // --- EJECTION SIDE (DUT -> TB) ---
        // Data stable until TB acknowledges (pop)
        property data_stable_until_ack;
            @(posedge clk) disable iff (reset)
            (pndng[i] && !pop[i]) |=> $stable(data_out[i]);
        endproperty
        assert property(data_stable_until_ack) else `uvm_error("IF", $sformatf("Port %0d [Eject]: Data unstable during valid without Ack (pop)", i));

        // TB should only Ack if Data is Valid
        property ack_only_when_valid;
            @(posedge clk) disable iff (reset)
            pop[i] |-> pndng[i];
        endproperty
        assert property(ack_only_when_valid) else `uvm_error("IF", $sformatf("Port %0d [Eject]: TB asserted POP without PNDNG", i));


        // --- INJECTION SIDE (TB -> DUT) ---
        // DUT should eventually Ack (popin) a request
        property req_eventually_acked;
            @(posedge clk) disable iff (reset)
            pndng_i_in[i] |-> ##[1:$] popin[i];
        endproperty
        assert property(req_eventually_acked) else `uvm_warning("IF", $sformatf("Port %0d [Inject]: Request stuck, DUT never asserted POPIN", i));

        // Data stable until DUT Acknowledges (popin)
        property driver_data_stable;
            @(posedge clk) disable iff (reset)
            (pndng_i_in[i] && !popin[i]) |=> $stable(data_out_i_in[i]);
        endproperty
        assert property(driver_data_stable) else `uvm_error("IF", $sformatf("Port %0d [Inject]: Driver changed Data without Ack (popin)", i));

        // DUT should only Ack if Driver is requesting
        property dut_ack_valid;
            @(posedge clk) disable iff (reset)
            popin[i] |-> pndng_i_in[i];
        endproperty
        assert property(dut_ack_valid) else `uvm_error("IF", $sformatf("Port %0d [Inject]: DUT asserted POPIN without PNDNG_I_IN", i));

      end
    endgenerate

endinterface
