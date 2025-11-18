


class seq_item #(parameter ADDR_WIDTH = router_pkg::ADDR_WIDTH, parameter DATA_WIDTH = router_pkg::DATA_WIDTH, parameter 
				MAX_N_CYCLES = router_pkg::MAX_N_CYCLES) extends uvm_sequence_item;
	

	typedef enum logic [0:0] {
		ROW_FIRST = 1'b1,
		COL_FIRST = 1'b0
	} route_mode_e;

	typedef enum logic {
		NO_ERROR    = 1'b0,
		HAS_ERR = 1'b1
	} error_type_e;
        
        //typedef enum { EAST, WEST, NORTH, SOUTH } route_mode_e;
	// -------------------------------
	// Random fields
	// -------------------------------
	
	rand bit [ADDR_WIDTH-1:0] addr;
	rand bit [DATA_WIDTH-1:0] data;
	rand bit [$clog2(MAX_N_CYCLES)-1:0] cycles_between;
	rand route_mode_e mode;
	
	// Flags
	rand error_type_e msg_error;
	rand bit broadcast;     // Si el mensaje es broadcast

	//Salidas
	bit [DATA_WIDTH-1:0] out_dut;

	`uvm_object_utils_begin(seq_item)
		`uvm_field_int(addr,          UVM_ALL_ON)
		`uvm_field_int(data,          UVM_ALL_ON)
		`uvm_field_int(cycles_between,UVM_ALL_ON)
		`uvm_field_enum(route_mode_e, mode, UVM_ALL_ON)
		`uvm_field_enum(error_type_e, msg_error, UVM_ALL_ON)
		`uvm_field_int(broadcast,     UVM_ALL_ON)
	`uvm_object_utils_end

	// -------------------------------
	// Constraints
	// -------------------------------
	constraint gap_c { cycles_between < MAX_N_CYCLES; }
	constraint broadcast_c {
		broadcast dist { 1'b0 := 9, 1'b1 := 1};
	}
	constraint error_c {
		msg_error dist { NO_ERROR := 9, HAS_ERR := 1 };
	}
	constraint bdcst_addr_c {
		solve broadcast before addr;
		if (broadcast)
			addr == {ADDR_WIDTH{1'b1}};
	}


	// build phase (constructor)
	function new (string name = "seq_item");
		super.new(name);
	endfunction : new

endclass:seq_item

