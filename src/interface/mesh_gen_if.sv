// mesh_gen_if.sv
// Mesh Router Interface for UVM Verification

interface mesh_gen_if #(
    parameter int ROWS    = 4,
    parameter int COLUMS  = 4,
    parameter int PCKG_SZ = 32
) (input logic clk);

    // Reset (lo maneja el TB)
    logic reset;


    // DUT ? TB  (salidas del router)
    // El DUT maneja estas señales
    wire                    pndng    [ROWS*2+COLUMS*2];
    wire [PCKG_SZ-1:0]      data_out [ROWS*2+COLUMS*2];
    wire                    pop      [ROWS*2+COLUMS*2];  // ACK de DUT a petición TB


    // TB ? DUT  (entradas al router)
    // El TB (driver / dummy consumer) maneja estas señales
    logic                    drv_pndng_i_in    [ROWS*2+COLUMS*2];
    logic [PCKG_SZ-1:0]      drv_data_out_i_in [ROWS*2+COLUMS*2];
    logic                    drv_popin         [ROWS*2+COLUMS*2]; // ACK TB a salidas router

    // Wires que ve el DUT
    wire                    pndng_i_in    [ROWS*2+COLUMS*2];
    wire [PCKG_SZ-1:0]      data_out_i_in [ROWS*2+COLUMS*2];
    wire                    popin         [ROWS*2+COLUMS*2];

    // Bridge TB?DUT
    genvar gi;
    generate
      for (gi = 0; gi < ROWS*2+COLUMS*2; gi++) begin : BRIDGE
        assign pndng_i_in[gi]    = drv_pndng_i_in[gi];
        assign data_out_i_in[gi] = drv_data_out_i_in[gi];
        assign popin[gi]         = drv_popin[gi];
      end
    endgenerate


    // Dummy consumer: consume siempre los paquetes que salen del router
    // popin = 1 cuando pndng = 1 (un ciclo después)

    always @(posedge clk) begin
        if (reset) begin
            for (int k = 0; k < (ROWS*2+COLUMS*2); k++) begin
                drv_popin[k] <= 1'b0;
            end
        end else begin
            for (int k = 0; k < (ROWS*2+COLUMS*2); k++) begin
                drv_popin[k] <= pndng[k];
            end
        end
    end


    // MODPORTS
    // Driver TB (solo inyecta tráfico hacia el DUT)
    modport TB (
        input  clk,
        output reset,

        // TB?DUT
        output drv_pndng_i_in,
        output drv_data_out_i_in,

        // Lectura opcional de salidas
        input  pndng,
        input  data_out,
        input  pop
    );

    // Monitor pasivo
    modport MON (
        input clk, reset,
        input pndng, data_out, popin,
        input pndng_i_in, data_out_i_in, pop
    );

    // DUT
    modport DUT (
        input  clk, reset,
        // Entradas desde TB
        input  pndng_i_in,
        input  data_out_i_in,
        input  popin,
        // Salidas hacia TB
        output pndng,
        output data_out,
        output pop
    );


    // ASSERTIONS DE PROTOCOLO
    generate
      for (genvar i = 0; i < (ROWS*2+COLUMS*2); i++) begin : PROTOCOL

        // A1: data_out estable mientras pndng=1 hasta que popin
        property data_stable_until_popin;
            @(posedge clk)
            pndng[i] |-> ($stable(data_out[i]) or popin[i]);
        endproperty

        assert property(data_stable_until_popin)
          else $error("Protocol ERROR: data_out[%0d] cambió mientras pndng=1 y sin popin!", i);

        // A2: popin solo válido cuando pndng=1
        property popin_only_when_valid;
            @(posedge clk)
            popin[i] |-> pndng[i];
        endproperty

        assert property(popin_only_when_valid)
          else $error("Protocol ERROR: popin[%0d] en alto mientras pndng=0", i);

        // A3: después de popin, pndng debe bajar
        property popin_consumes_packet;
            @(posedge clk)
            popin[i] |=> !pndng[i];
        endproperty

        assert property(popin_consumes_packet)
          else $warning("Protocol WARNING: pndng[%0d] no bajó después de popin", i);

        // A4: si TB levanta pndng_i_in ? DUT debe hacer pop
        property tb_req_acknowledged;
            @(posedge clk)
            pndng_i_in[i] |-> ##[1:$] pop[i];
        endproperty

        assert property(tb_req_acknowledged)
          else $warning("Protocol WARNING: DUT nunca hizo pop[%0d] ante pndng_i_in", i);

        // A5: TB mantiene data_out_i_in estable mientras pndng_i_in=1
        property tb_data_stable_during_req;
            @(posedge clk)
            pndng_i_in[i] |-> ($stable(data_out_i_in[i]) or pop[i]);
        endproperty

        assert property(tb_data_stable_during_req)
          else $error("Protocol ERROR: data_out_i_in[%0d] cambió antes de pop!", i);

        // A6: DUT solo puede pop si hay pndng_i_in=1
        property pop_only_when_tb_has_data;
            @(posedge clk)
            pop[i] |-> pndng_i_in[i];
        endproperty

        assert property(pop_only_when_tb_has_data)
          else $error("Protocol ERROR: pop[%0d] en alto con pndng_i_in=0", i);

      end
    endgenerate

endinterface

