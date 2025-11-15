class router_monitor extends uvm_monitor;
    `uvm_component_utils(router_monitor)
    function new(string name="monitor", uvm_component parent=null);
        super.new(name, parent)    
    endfunction //new()

    uvm_analysis_port #(seq_item) mon_analysis_port;
    virtual mesh_gen_if.MON vif;

    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        if (!uvm_config_db#(virtual mesh_gen_if.MON)::get(this, "", "mesh_gen_if", vif))
            `uvm_fatal("MON", "Could not get vif")
        mon_analysis_port = new("mon_analysis_port", this);
    endfunction

    virtual task run_phase(uvm_phase phase);
        super.run_phase(phase);

        forever begin
            @(vif.clk);
                if (!vif.reset) begin
                    seq_item item = seq_item::type_id::create("item");
                    //logica de leer interfaz y pasarlas al item
                //     input clk, reset,
                //  input popin, data_out, pndng,
                //  input pop, data_out_i_in, pndng_i_in
// rand bit [ADDR_WIDTH-1:0] addr;
// 	rand bit [DATA_WIDTH-1:0] data;
// 	rand bit [$clog2(MAX_N_CYCLES)-1:0] cycles_between;
// 	rand route_mode_e mode;
	
// 	// Flags
// 	rand error_type_e msg_error;
// 	rand bit broadcast;     // Si el mensaje es broadcast

// 	//Salidas
// 	bit [DATA_WIDTH-1:0] out_dut;

                    item.out_dut=vif.data_out_i_in

                    mon_analysis_port.write(item);
                `uvm_info("MON", $sformatf("Saw item %s", item.convert2str()), UVM_HIGH)
                end
        end
        
    endtask //
endclass //monitor extends uvm_monito