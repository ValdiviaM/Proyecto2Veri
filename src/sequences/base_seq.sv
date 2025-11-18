
class router_sequence #(parameter ADDR_WIDTH = 8,
                        parameter DATA_WIDTH = 8,
                        parameter MAX_N_CYCLES = 16)
    extends uvm_sequence #(seq_item#(ADDR_WIDTH, DATA_WIDTH, MAX_N_CYCLES));
	`uvm_object_utils(router_sequence)

	function new(string name="sequence");
		super.new(name);
	endfunction

	rand int n_items;

	constraint n_items_c { n_items inside {[500:2000]}; }

	virtual task body();
		for (int i = 0; i<n_items; i++) begin
			seq_item i_item = seq_item::type_id::create("i_item");
			start_item(i_item);
			i_item.randomize();

			`uvm_info("SEQ", $sformatf("Generate new item: "), UVM_LOW)
			i_item.print();
			
			finish_item(i_item);
			if ((i % 100) == 0)	// Logs every 100 items
			    `uvm_info("SEQ", $sformatf("Progress: %0d / %0d items generated", i, n_items), UVM_LOW)

		end
		`uvm_info("SEQ", $sformatf("Done generation of %0d items", n_items), UVM_LOW)
	endtask //

endclass:router_sequence
