class router_driver extends uvm_driver #(seq_item);
    `uvm_component_utils(router_driver)

    virtual mesh_gen_if #(ROWS, COLUMS, DATA_WIDTH).TB vif;
    seq_item req;
    
    semaphore port_locks[(ROWS*2 + COLUMS*2)];

    function new(string name = "router_driver", uvm_component parent = null);
        super.new(name, parent);
        for(int i=0; i < (ROWS*2 + COLUMS*2); i++) begin
            port_locks[i] = new(1);
        end
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        if (!uvm_config_db#(virtual mesh_gen_if #(ROWS, COLUMS, DATA_WIDTH).TB)::get(this, "", "vif", vif))
            `uvm_fatal("DRV", "Cannot get virtual interface")
    endfunction

    task run_phase(uvm_phase phase);
        seq_item req_cloned;

        // Init signals
        for (int i = 0; i < (ROWS*2+COLUMS*2); i++) begin
            vif.drv_pndng_i_in[i] <= 1'b0;
            vif.drv_data_out_i_in[i] <= '0;
        end

        // Wait for Reset
        wait (vif.reset === 1'b0);
        @(posedge vif.clk);

        forever begin
            seq_item_port.get_next_item(req);
            $cast(req_cloned, req.clone());
            
            fork
                automatic seq_item t = req_cloned;
                begin
                    drive(t); 
                end
            join_none
            
            seq_item_port.item_done();
        end
    endtask

    task drive(seq_item t);
        int unsigned port = t.src; 

        if (port >= (ROWS*2 + COLUMS*2)) return;

        port_locks[port].get(); 

        // 1. Assert Request
        @(posedge vif.clk);
        vif.drv_data_out_i_in[port] <= t.data;
        vif.drv_pndng_i_in[port]    <= 1'b1;
        
        `uvm_info("DRV", $sformatf("Driving Port %0d with Data %0h", port, t.data), UVM_LOW);

        // 2. Wait for ACK from DUT
        // *** CRITICAL FIX: Wait for 'popin' (DUT Output Ack), NOT 'pop' ***
        fork
            begin : wait_for_ack
                do begin
                    @(posedge vif.clk);
                end while (vif.popin[port] === 1'b0); // Fixed!
            end
            begin : watchdog
                repeat(100) @(posedge vif.clk);
                `uvm_error("DRV", $sformatf("Timeout waiting for popin (Ack) on port %0d", port))
            end
        join_any
        disable fork;

        // 3. De-assert Request
        vif.drv_pndng_i_in[port] <= 1'b0;
        
        repeat (t.cycles_between) @(posedge vif.clk);

        port_locks[port].put();
    endtask

endclass
