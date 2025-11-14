interface mesh_gen_if #(parameter ROWS = 4, parameter COLUMS = 4, parameter pckg_sz = 32, parameter fifo_depth = 4, parameter bdcst = {8{1'b1}})
	(
		input clk
	);

	bit reset;
	bit pndng [ROWS*2+COLUMS*2];
	bit [pckg_sz-1:0] data_out [ROWS*2+COLUMS*2];
	bit popin [ROWS*2+COLUMS*2];
	bit pop [ROWS*2+COLUMS*2];
	bit [pckg_sz-1:0] data_out_i_in [ROWS*2+COLUMS*2];
	bit pndng_i_in [ROWS*2+COLUMS*2];


  // --- Clocking Block --- 
  // sentido de las senales
  clocking cb @(posedge clk);
    default input #1 output #1;
    output data_out;
	output pndng;
	output popin;
    
	input  clk;
	input reset;
	output data_out_i_in;
	input pop;
	output pndng_i_in;
  endclocking


  // --- Modports (Conectores) ---
	modport TB(clocking cb);
	modport DUT (input  clk, reset,
                 input  popin, data_out, pndng,
                 output pop,   data_out_i_in, pndng_i_in);
	
	
	// Assertions protocol
	genvar i;
    generate
        for (i = 0; i < (ROWS*2+COLUMS*2); i++) begin : PROTOCOL

            //handshake desde el dut hacia el terminal - la salida del router
            // 1. Si pndng = 1, el dato debe estar estable
            //sin popin no se puede mandar otro paquete
            property data_stable_until_popin;
                @(posedge clk)
                pndng[i] |-> $stable(data_out[i]) or popin[i];
            endproperty

            assert property (data_stable_until_popin)
                else $error("Protocol ERROR: data_out[%0d] changed while pndng=1 before popin!", i);


            // 2. No puede haber popin si pndng = 0
            //    no hay datos que consumir
            property popin_only_when_valid;
                @(posedge clk)
                popin[i] |-> pndng[i];
            endproperty

            assert property(popin_only_when_valid)
                else $error("Protocol ERROR: popin[%0d] asserted while pndng=0", i);


            // 3. Después de popin, pndng debe bajar
            //    consumir paquete
            property popin_consumes_data;
                @(posedge clk)
                popin[i] |=> !pndng[i];
            endproperty

            assert property(popin_consumes_data)
                else $warning("Protocol WARNING: pndng[%0d] did not clear after popin", i);

            //Handshake opuesto - entrada al router
            // 4) Si TB levanta pndng_i_in, DUT debe reconocerlo con pop
            // fuerza ha hacer la operacion
            property tb_req_must_be_ack;
                @(posedge clk)
                pndng_i_in[i] |-> ##[1:$] pop[i];
            endproperty

            assert property(tb_req_must_be_ack)
                else $warning("Protocol WARNING: DUT never popped TB request at terminal %0d", i);


            // 5. Mientras pndng_i_in=1, TB debe mantener data_out_i_in estable
            // evitar leer paquetes corruptos
            property tb_data_stable_during_req;
                @(posedge clk)
                pndng_i_in[i] |-> $stable(data_out_i_in[i]) or pop[i];
            endproperty

            assert property(tb_data_stable_during_req)
                else $error("Protocol ERROR: TB changed data_out_i_in[%0d] before DUT pop", i);

            
            // 6. pop solo puede ocurrir si hay pndng_i_in=1
            //    solo se recibe lo que se esta enviando
            property pop_only_when_tb_has_data;
                @(posedge clk)
                pop[i] |-> pndng_i_in[i];
            endproperty

            assert property(pop_only_when_tb_has_data)
                else $error("Protocol ERROR: DUT pop[%0d] asserted while pndng_i_in=0", i);

        end
    endgenerate
endinterface
