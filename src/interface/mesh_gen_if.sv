//------------------------------------------------------------------------------
// Interface: mesh_gen_if
//------------------------------------------------------------------------------
// Interfaz que conecta el testbench (TB) con el DUT para un router mesh.
// - Define señales físicas (injection/ejection).
// - Provee bridges entre lógica interna del TB y las líneas hacia el DUT.
// - Incluye un "dummy consumer" (auto-ack) para la salida del DUT.
// - Define modports para TB, MON y DUT.
// - Assertions del protocolo.
//------------------------------------------------------------------------------

import uvm_pkg::*;
`include "uvm_macros.svh"

interface mesh_gen_if #(
    parameter int ROWS    = 4,
    parameter int COLUMS  = 4,
    parameter int PCKG_SZ = 40
) (input logic clk);

    // Reset global
    logic reset;

    // ============================================================
    // 1. WIRES (Conexiones físicas entre TB <-> DUT)
    // ============================================================

    // ------------------------------------------------------------
    // Group A: Injection Channels (TB -> DUT)
    // - TB (Driver) envía: drv_pndng_i_in (valid) + drv_data_out_i_in (data)
    // - DUT devuelve ack por popin (popin = DUT -> TB ack)
    // ------------------------------------------------------------
    logic                   drv_pndng_i_in    [ROWS*2+COLUMS*2]; // Driven by Driver
    logic [PCKG_SZ-1:0]     drv_data_out_i_in [ROWS*2+COLUMS*2]; // Driven by Driver
    wire                    popin             [ROWS*2+COLUMS*2]; // Driven by DUT (Ack)

    // Wires que representan las entradas reales del DUT (bridge desde TB)
    wire                    pndng_i_in        [ROWS*2+COLUMS*2];
    wire [PCKG_SZ-1:0]      data_out_i_in     [ROWS*2+COLUMS*2];

    // ------------------------------------------------------------
    // Group B: Ejection Channels (DUT -> TB)
    // - DUT envía: pndng (valid) + data_out (data)
    // - TB responde con pop (ack). Aquí el TB ack es manejado por drv_pop
    // ------------------------------------------------------------
    wire                    pndng             [ROWS*2+COLUMS*2]; // Driven by DUT
    wire [PCKG_SZ-1:0]      data_out          [ROWS*2+COLUMS*2]; // Driven by DUT
    
    logic                   drv_pop           [ROWS*2+COLUMS*2]; // Driven by Dummy Consumer
    wire                    pop               [ROWS*2+COLUMS*2]; // Connected to DUT Input

    // ============================================================
    // 2. ASSIGNMENTS (Bridges: logic -> wire)
    // - Conecta las señales "drv_*" (lógicas del TB) a las líneas físicas
    //   que ve el DUT.
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
    // 3. DUMMY CONSUMER (Auto-Ack para salidas del DUT)
    // - Versión combinacional: pop se iguala inmediatamente a pndng.
    // - Evita delays de 1 ciclo que causaba la versión sincronizada.
    // ============================================================

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
    // - TB: driver/consumer (controla drv_* y observa popin/pndng)
    // - MON: monitor que necesita visibilidad completa de wires
    // - DUT: interfaz hacia el DUT
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
    // 5. ASSERTIONS (Protocolo)
    // - Verifican invarianzas básicas del handshake entre TB y DUT
    // - Abarcan ambos lados: Ejection (DUT->TB) e Injection (TB->DUT)
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
