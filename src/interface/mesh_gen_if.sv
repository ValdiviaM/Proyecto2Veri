// mesh_gen_if.sv
// Final, fully corrected interface for router TB + UVM

interface mesh_gen_if #(
    parameter int ROWS    = 4,
    parameter int COLUMS  = 4,
    parameter int PCKG_SZ = 32
) (input logic clk);

    // Reset driven by TB
    logic reset;


    // DUT ? TB (router OUTPUT ports)

    wire                    pndng    [ROWS*2+COLUMS*2];
    wire [PCKG_SZ-1:0]      data_out [ROWS*2+COLUMS*2];
    wire                    pop       [ROWS*2+COLUMS*2];   // DUT ACK to TB



    // TB ? DUT (router INPUT ports)

    logic                    drv_pndng_i_in    [ROWS*2+COLUMS*2];
    logic [PCKG_SZ-1:0]      drv_data_out_i_in [ROWS*2+COLUMS*2];
    logic                    drv_popin         [ROWS*2+COLUMS*2]; // TB ACK to DUT


    // Wires seen by DUT
    wire                    pndng_i_in    [ROWS*2+COLUMS*2];
    wire [PCKG_SZ-1:0]      data_out_i_in [ROWS*2+COLUMS*2];
    wire                    popin         [ROWS*2+COLUMS*2];



    // BRIDGE: TB logic ? DUT wires

    genvar gi;
    generate
      for (gi = 0; gi < ROWS*2+COLUMS*2; gi++) begin : BRIDGE
        assign pndng_i_in[gi]    = drv_pndng_i_in[gi];
        assign data_out_i_in[gi] = drv_data_out_i_in[gi];
        assign popin[gi]         = drv_popin[gi];   // FIXED
      end
    endgenerate



    // Dummy consumer: DUT ? TB side auto-ACK

    always @(posedge clk) begin
        if (reset) begin
            for (int k = 0; k < ROWS*2+COLUMS*2; k++)
                drv_popin[k] <= 1'b0;
        end else begin
            for (int k = 0; k < ROWS*2+COLUMS*2; k++)
                drv_popin[k] <= pndng[k];  // TB acknowledges router output
        end
    end



    // MODPORTS (critical)

    modport TB (
        input  clk,
        output reset,

        // TB ? DUT
        output drv_pndng_i_in,
        output drv_data_out_i_in,
        output drv_popin,

        // TB reads DUT outputs
        input  pndng,
        input  data_out,
        input  pop
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



    // ASSERTIONS (unchanged, correct)

    generate
      for (genvar i = 0; i < ROWS*2+COLUMS*2; i++) begin : PROTOCOL

        property data_stable_until_popin;
            @(posedge clk)
            pndng[i] |-> ($stable(data_out[i]) or popin[i]);
        endproperty
        assert property(data_stable_until_popin);

        property popin_only_when_valid;
            @(posedge clk)
            popin[i] |-> pndng[i];
        endproperty
        assert property(popin_only_when_valid);

        property popin_consumes_packet;
            @(posedge clk)
            popin[i] |=> !pndng[i];
        endproperty
        assert property(popin_consumes_packet);

        property tb_req_acknowledged;
            @(posedge clk)
            pndng_i_in[i] |-> ##[1:$] pop[i];
        endproperty
        assert property(tb_req_acknowledged);

        property tb_data_stable_during_req;
            @(posedge clk)
            pndng_i_in[i] |-> ($stable(data_out_i_in[i]) or pop[i]);
        endproperty
        assert property(tb_data_stable_during_req);

        property pop_only_when_tb_has_data;
            @(posedge clk)
            pop[i] |-> pndng_i_in[i];
        endproperty
        assert property(pop_only_when_tb_has_data);

      end
    endgenerate

endinterface

