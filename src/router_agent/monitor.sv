class router_monitor extends uvm_monitor;
    `uvm_component_utils(router_monitor)

    uvm_analysis_port #(seq_item) ap_in;
    uvm_analysis_port #(seq_item) ap_out;

    virtual mesh_gen_if #(ROWS, COLUMS, DATA_WIDTH).MON vif;

    // --- NUEVO: Arrays para filtrar duplicados ---
    int last_seen_id_in [int]; 
    int last_seen_id_out [int];

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

    // Helper local para extraer ID (Idéntico al del scoreboard)
    function int get_packet_id(bit [DATA_WIDTH-1:0] data);
        return data[(DATA_WIDTH - 26) -: 8]; 
    endfunction

    virtual task run_phase(uvm_phase phase);
        // Inicialización de la memoria de filtro
        for(int i=0; i < (ROWS*2+COLUMS*2); i++) begin
            last_seen_id_in[i]  = -1;
            last_seen_id_out[i] = -1;
        end

        forever begin
            @(posedge vif.clk);
            #1step; // Pequeño delay para estabilidad si no se usa clocking block
            
            if (!vif.reset) begin
                for (int i = 0; i < NUM_PORTS; i++) begin
                    
                    // =========================================================
                    // 1. MONITOR INJECTION (Entrada)
                    // =========================================================
                    if (vif.pndng_i_in[i] === 1'b1 && vif.popin[i] === 1'b1) begin
                        int current_id = get_packet_id(vif.data_out_i_in[i]);
                        
                        // FILTRO: Solo enviamos si el ID es NUEVO para este puerto
                        if (last_seen_id_in[i] != current_id) begin
                            seq_item item_in = seq_item::type_id::create("item_in");
                            `uvm_info("MON", $sformatf("Detected INJECTION on Port %0d (ID: %0d)", i, current_id), UVM_LOW); 

                            item_in.data = vif.data_out_i_in[i];
                            item_in.src  = i; 
                            ap_in.write(item_in);

                            // Actualizamos el último visto
                            last_seen_id_in[i] = current_id;
                        end
                    end else begin
                        // Si baja el handshake, reseteamos para permitir el mismo ID en el futuro
                        last_seen_id_in[i] = -1;
                    end

                    // =========================================================
                    // 2. MONITOR EJECTION (Salida)
                    // =========================================================
                    if (vif.pndng[i] === 1'b1 && vif.pop[i] === 1'b1) begin
                        int current_id = get_packet_id(vif.data_out[i]);

                        // FILTRO: Solo enviamos si el ID es NUEVO para este puerto
                        if (last_seen_id_out[i] != current_id) begin
                            seq_item item_out = seq_item::type_id::create("item_out");
                            `uvm_info("MON", $sformatf("Detected OUTPUT on Port %0d (ID: %0d)", i, current_id), UVM_LOW);

                            item_out.data = vif.data_out[i];
                            item_out.addr = i; 
                            ap_out.write(item_out);

                            // Actualizamos el último visto
                            last_seen_id_out[i] = current_id;
                        end
                    end else begin
                        last_seen_id_out[i] = -1;
                    end
                end
            end
        end
    endtask 
endclass