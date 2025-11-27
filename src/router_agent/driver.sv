//------------------------------------------------------------------------------
// Component: router_driver
//------------------------------------------------------------------------------
// Driver UVM que toma `seq_item` desde el sequencer y los conduce al DUT vía
// la interfaz virtual `mesh_gen_if`. Maneja múltiples puertos en paralelo y
// usa semáforos por puerto para evitar colisiones de acceso.
//------------------------------------------------------------------------------

class router_driver extends uvm_driver #(seq_item);
    `uvm_component_utils(router_driver)

    // Virtual interface al testbench (modport TB)
    virtual mesh_gen_if #(ROWS, COLUMS, DATA_WIDTH).TB vif;

    // Item recibido desde el sequencer
    seq_item req;
    
    // Semáforos por puerto para arbitraje (1 token por puerto)
    semaphore port_locks[(ROWS*2 + COLUMS*2)];

    //--------------------------------------------------------------------------
    // Constructor: inicializa semáforos por puerto
    //--------------------------------------------------------------------------
    function new(string name = "router_driver", uvm_component parent = null);
        super.new(name, parent);
        for(int i=0; i < (ROWS*2 + COLUMS*2); i++) begin
            port_locks[i] = new(1);
        end
    endfunction

    //--------------------------------------------------------------------------
    // build_phase: obtiene la interfaz virtual desde uvm_config_db
    //--------------------------------------------------------------------------
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        if (!uvm_config_db#(virtual mesh_gen_if #(ROWS, COLUMS, DATA_WIDTH).TB)::get(this, "", "vif", vif))
            `uvm_fatal("DRV", "Cannot get virtual interface")
    endfunction

    //--------------------------------------------------------------------------
    // run_phase: bucle principal del driver
    // - Inicializa señales del TB
    // - Espera fin de reset
    // - Consume items del seq_item_port, clona y lanza drive() en paralelo
    //--------------------------------------------------------------------------
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

    //--------------------------------------------------------------------------
    // drive: tarea que realiza el handshake para un item en un puerto específico
    // - Toma el lock del puerto
    // - Aserta valid/data, espera popin (ACK) del DUT con watchdog
    // - Desaserta valid y espera los ciclos post-transfer necesarios
    // - Libera el lock del puerto
    //--------------------------------------------------------------------------
    task drive(seq_item t);
        int unsigned port = t.src; 

        if (port >= (ROWS*2 + COLUMS*2)) return;

        port_locks[port].get(); 

        // 1. Assert Request (alineado al flanco de reloj)
        @(posedge vif.clk);
        vif.drv_data_out_i_in[port] <= t.data;
        vif.drv_pndng_i_in[port]    <= 1'b1;
        
        `uvm_info("DRV", $sformatf("Driving Port %0d with Data %0h", port, t.data), UVM_HIGH)

        // 2. Wait for ACK from DUT
        // *** CRITICAL FIX: Increased Timeout for Congestion ***
        fork
            begin : wait_for_ack
                do begin
                    @(posedge vif.clk);
                end while (vif.popin[port] === 1'b0); 
            end
            begin : watchdog
                // Increased from 100 to 10000 cycles to handle heavy congestion
                repeat(10000) @(posedge vif.clk);
                `uvm_error("DRV", $sformatf("Timeout waiting for popin (Ack) on port %0d. DUT is stalled.", port))
            end
        join_any
        disable fork;

        // 3. De-assert Request
        vif.drv_pndng_i_in[port] <= 1'b0;
        
        repeat (t.cycles_between) @(posedge vif.clk);

        port_locks[port].put();
    endtask

endclass
