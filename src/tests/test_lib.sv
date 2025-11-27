// ------------------------------------------------------------------
// TEST 1: EXHAUSTIVE COVERAGE (Fills the Matrix)
// ------------------------------------------------------------------
class exhaustive_test extends base_test;
    `uvm_component_utils(exhaustive_test)
    function new(string name = "exhaustive_test", uvm_component parent=null);
        super.new(name, parent); // Llamada al constructor de base_test
    endfunction

    task run_phase(uvm_phase phase);
        full_mesh_seq seq; // Usamos la secuencia full mesh
        phase.raise_objection(this); // Marcamos que el test está activo
        seq = full_mesh_seq::type_id::create("seq");
        seq.start(m_env.m_agent.m_sequencer); // Ejecutamos la secuencia
        fork
            begin
                // Esperar hasta que scoreboard haya recibido todos los paquetes
                #1000
                wait(m_env.m_sb.packet_db.size() == 0);
                `uvm_info("TEST", "All packets received! Drain complete.", UVM_LOW)
            end
            begin
                // Timeout de seguridad por si algún paquete se pierde
                #(cfg_num_msgs * 1000ns); 
                `uvm_error("TEST", "Timeout waiting for scoreboard to drain. Packets likely lost.")
            end
        join_any
        disable fork; // Terminar el thread que quedó vivo (wait o timeout)
        phase.drop_objection(this);
    endtask
endclass

// ------------------------------------------------------------------
// TEST 2: CONTENTION / ARBITRATION (TC1.7)
// ------------------------------------------------------------------
class contention_test extends base_test;
    `uvm_component_utils(contention_test)
    function new(string name="contention_test", uvm_component parent=null);
        super.new(name, parent);
    endfunction

    task run_phase(uvm_phase phase);
        hotspot_seq seq; // Secuencia para crear hotspots y contención
        phase.raise_objection(this);
        seq = hotspot_seq::type_id::create("seq");
        seq.start(m_env.m_agent.m_sequencer);
        fork
            begin
                // Espera hasta que scoreboard procese todos los paquetes
                #1000
                wait(m_env.m_sb.packet_db.size() == 0);
                `uvm_info("TEST", "All packets received! Drain complete.", UVM_LOW)
            end
            begin
                // Timeout de seguridad
                #(cfg_num_msgs * 1000ns); 
                `uvm_error("TEST", "Timeout waiting for scoreboard to drain. Packets likely lost.")
            end
        join_any
        disable fork;
        phase.drop_objection(this);
    endtask
endclass

// ------------------------------------------------------------------
// TEST 3: BROADCAST (TC1.9)
// ------------------------------------------------------------------
class broadcast_test extends base_test;
    `uvm_component_utils(broadcast_test)
    function new(string name = "broadcast_test", uvm_component parent=null);
        super.new(name, parent);
    endfunction

    task run_phase(uvm_phase phase);
        broadcast_seq seq; // Secuencia que fuerza broadcast
        phase.raise_objection(this);
        seq = broadcast_seq::type_id::create("seq");
        seq.start(m_env.m_agent.m_sequencer);
        fork
            begin
                #1000
                wait(m_env.m_sb.packet_db.size() == 0); // Espera que todos los broadcasts sean recibidos
                `uvm_info("TEST", "All packets received! Drain complete.", UVM_LOW)
            end
            begin
                #(cfg_num_msgs * 1000ns); // Timeout de seguridad
                `uvm_error("TEST", "Timeout waiting for scoreboard to drain. Packets likely lost.")
            end
        join_any
        disable fork;
        phase.drop_objection(this);
    endtask
endclass

// ------------------------------------------------------------------
// TEST 4: COLUMN FIRST ROUTING (TC1.3)
// ------------------------------------------------------------------
class col_first_test extends base_test;
    `uvm_component_utils(col_first_test)
    function new(string name="col_first_test", uvm_component parent=null);
        super.new(name, parent);
    endfunction

    task run_phase(uvm_phase phase);
        router_sequence seq; // Secuencia genérica
        phase.raise_objection(this);
        seq = router_sequence::type_id::create("seq");
        seq.route_mode = 0; // Forzar Column First
        seq.num_trans  = 50; // Número de transacciones
        seq.start(m_env.m_agent.m_sequencer);
        fork
            begin
                #1000
                wait(m_env.m_sb.packet_db.size() == 0);
                `uvm_info("TEST", "All packets received! Drain complete.", UVM_LOW)
            end
            begin
                #(cfg_num_msgs * 1000ns); // Timeout de seguridad
                `uvm_error("TEST", "Timeout waiting for scoreboard to drain. Packets likely lost.")
            end
        join_any
        disable fork;
        phase.drop_objection(this);
    endtask
endclass

// ------------------------------------------------------------------
// TEST 5: RESET RECOVERY (TC1.11)
// ------------------------------------------------------------------
class reset_test extends base_test;
    `uvm_component_utils(reset_test)
    virtual mesh_gen_if #(4, 4, 40) vif; // Interface handle específica

    function new(string name="reset_test", uvm_component parent=null);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        // Obtener la interfaz virtual configurada en el testbench
        if (!uvm_config_db#(virtual mesh_gen_if #(4, 4, 40))::get(this, "", "vif", vif))
            `uvm_fatal("TEST", "Could not get vif")
    endfunction

    task run_phase(uvm_phase phase);
        router_sequence seq;
        phase.raise_objection(this);
        
        seq = router_sequence::type_id::create("seq");
        seq.num_trans = 100; 

        fork
            seq.start(m_env.m_agent.m_sequencer); // Lanzar secuencia normal
            begin
                #6000;
                `uvm_info("TEST", ">>> ASSERTING RESET MID-SIMULATION <<<", UVM_NONE)
                vif.reset = 1; // Activar reset en la interfaz
                #200;
                vif.reset = 0; // Liberar reset
                `uvm_info("TEST", ">>> RESET RELEASED <<<", UVM_NONE)
            end
        join
        phase.drop_objection(this);
    endtask
endclass
