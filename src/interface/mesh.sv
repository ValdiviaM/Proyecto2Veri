interface mesh_if #(parameter rows = 4, parameter colums = 4, parameter pckg_sz = 32, parameter fifo_depth = 4, parameter bdcst = {8{1'b1}})
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
endinterface