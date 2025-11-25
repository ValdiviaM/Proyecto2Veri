class router_monitor extends uvm_monitor;
    `uvm_component_utils(router_monitor)

    uvm_analysis_port #(seq_item) ap_in;
    uvm_analysis_port #(seq_item) ap_out;

    virtual mesh_gen_if #(ROWS, COLUMS, DATA_WIDTH).MON vif;

    function new(string name="monitor", uvm_component parent=null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        if (!uvm_config_db#(virtual mesh_gen_if #(ROWS, COLUMS, DATA_WIDTH).MON)::get(this, "", "vif", vif))
            `uvm_fatal("MON", "Could not get vif")
        ap_in  = new("ap_in", this);
        ap_out = new("ap_out", this);
    endfunction

    virtual task run_phase(uvm_phase phase);
        forever begin
            @(posedge vif.clk);
            if (!vif.reset) begin
                for (int i = 0; i < NUM_PORTS; i++) begin
                    
                    // 1. Monitor Injection (TB -> DUT)
                    // Valid: pndng_i_in | Ack: pop (DUT accepted it)
                    if (vif.pndng_i_in[i] === 1'b1 && vif.pop[i] === 1'b1) begin
                        seq_item item_in = seq_item::type_id::create("item_in");
                        
                        // Add Print with Semicolon
                        `uvm_info("MON", $sformatf("Detected INJECTION on Port %0d", i), UVM_LOW); 

                        item_in.data = vif.data_out_i_in[i];
                        item_in.src  = i; 
                        ap_in.write(item_in);
                    end

                    // 2. Monitor Ejection (DUT -> TB)
                    // Valid: pndng | Ack: popin (TB accepted it)
                    if (vif.pndng[i] === 1'b1 && vif.popin[i] === 1'b1) begin
                        seq_item item_out = seq_item::type_id::create("item_out");
                        
                        // Add Print with Semicolon (Fixed text to OUTPUT)
                        `uvm_info("MON", $sformatf("Detected OUTPUT on Port %0d", i), UVM_LOW);

                        item_out.data = vif.data_out[i];
                        item_out.addr = i; 
                        ap_out.write(item_out);
                    end
                end
            end
        end
    endtask 
endclass
