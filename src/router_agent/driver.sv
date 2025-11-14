// Driver class
class router_driver extends uvm_driver#(seq_item) ;
	// declare the neccessary uvm macros to register in the uvm classes !
	`uvm_component_utils(router_driver)

	virtual mesh_gen_if.TB  inf; //connection of modport
	seq_item item;

	// constructor 
	function new (string name = "router_driver" ,uvm_component parent);
		super.new(name,parent);
		`uvm_info("Driver Class","Inside constructor",UVM_HIGH);
	endfunction 

	
	// build phase
	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		`uvm_info("Driver Class","build_phase",UVM_HIGH);
		// getting the interface with safety check
        if (!uvm_config_db#(virtual mesh_gen_if.TB)::get(this, "", "vif", inf))
            `uvm_fatal("Driver Class", "Cannot get virtual interface from config DB")
        else
            `uvm_info("Driver Class", "Got virtual interface OK", UVM_LOW)
    endfunction

	
	// run phase
	// note that that the run phase is implemented as a task as it can consume time
	task run_phase(uvm_phase phase);
		super.run_phase(phase);
		// build phase logic
		`uvm_info("Driver Class","Run phase",UVM_HIGH);
		forever begin 
			reg_item = seq_item::type_id::create("reg_item",this);
            
            //API used by the driver to interact with the sequencer "seq_item_port"
			//get an item from sequencer using get_next method
			seq_item_port.get_next_item(item); // blocks until a REQ sequence_item is available in the sequencers request FIFO 
           `uvm_info("Driver Class", $sformatf("Start driving:addr=%0d data=%0d mode=%0d", req.addr, req.data, req.mode), UVM_NONE);

			// driving the packet via task
			drive();
			
			// end of sending packet
			`uvm_info("Driver Class","Finished Driving",UVM_HIGH);
			seq_item_port.item_done();
		end 

	endtask 

    // Drive task
    task drive(seq_item item);
        @(posedge inf.cb);
        inf.cb.reset         <= item.msg_error;
        inf.cb.data_out_i_in <= item.data;
        inf.cb.pndng_i_in    <= 1'b1;

        repeat(item.cycles_between) @(posedge inf.cb);

        inf.cb.pndng_i_in    <= 1'b0;
    endtask

endclass : router_driver

