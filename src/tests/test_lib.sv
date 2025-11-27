

// ------------------------------------------------------------------
// TEST 1: EXHAUSTIVE COVERAGE (Fills the Matrix)
// ------------------------------------------------------------------
class exhaustive_test extends base_test;
    `uvm_component_utils(exhaustive_test)
    function new(string name = "exhaustive_test", uvm_component parent=null);
        super.new(name, parent);
    endfunction

    task run_phase(uvm_phase phase);
        full_mesh_seq seq;
        phase.raise_objection(this);
        seq = full_mesh_seq::type_id::create("seq");
        seq.start(m_env.m_agent.m_sequencer);
        fork
            begin
                // Esperar hasta que la base de datos de paquetes pendientes llegue a 0
                wait(m_env.m_sb.packet_db.size() == 0);
                `uvm_info("TEST", "All packets received! Drain complete.", UVM_LOW)
            end
            begin
                // Timeout de seguridad (por si se pierde un paquete de verdad)
                // Calculamos un tiempo MUY largo basado en tus paquetes
                #(cfg_num_msgs * 1000ns); 
                `uvm_error("TEST", "Timeout waiting for scoreboard to drain. Packets likely lost.")
            end
        join_any
        disable fork; // Matar el thread que no terminó (el timeout o el wait)

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
        hotspot_seq seq;
        phase.raise_objection(this);
        seq = hotspot_seq::type_id::create("seq");
        seq.start(m_env.m_agent.m_sequencer);
        fork
            begin
                // Esperar hasta que la base de datos de paquetes pendientes llegue a 0
                wait(m_env.m_sb.packet_db.size() == 0);
                `uvm_info("TEST", "All packets received! Drain complete.", UVM_LOW)
            end
            begin
                // Timeout de seguridad (por si se pierde un paquete de verdad)
                // Calculamos un tiempo MUY largo basado en tus paquetes
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
        broadcast_seq seq;
        phase.raise_objection(this);
        seq = broadcast_seq::type_id::create("seq");
        seq.start(m_env.m_agent.m_sequencer);
        fork
            begin
                // Esperar hasta que la base de datos de paquetes pendientes llegue a 0
                wait(m_env.m_sb.packet_db.size() == 0);
                `uvm_info("TEST", "All packets received! Drain complete.", UVM_LOW)
            end
            begin
                // Timeout de seguridad (por si se pierde un paquete de verdad)
                // Calculamos un tiempo MUY largo basado en tus paquetes
                #(cfg_num_msgs * 1000ns); 
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
        router_sequence seq;
        phase.raise_objection(this);
        seq = router_sequence::type_id::create("seq");
        seq.route_mode = 0; // Force Column First
        seq.num_trans  = 50;
        seq.start(m_env.m_agent.m_sequencer);
        fork
            begin
                // Esperar hasta que la base de datos de paquetes pendientes llegue a 0
                wait(m_env.m_sb.packet_db.size() == 0);
                `uvm_info("TEST", "All packets received! Drain complete.", UVM_LOW)
            end
            begin
                // Timeout de seguridad (por si se pierde un paquete de verdad)
                // Calculamos un tiempo MUY largo basado en tus paquetes
                #(cfg_num_msgs * 1000ns); 
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
    virtual mesh_gen_if #(4, 4, 40) vif;

    function new(string name="reset_test", uvm_component parent=null);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        if (!uvm_config_db#(virtual mesh_gen_if #(4, 4, 40))::get(this, "", "vif", vif))
            `uvm_fatal("TEST", "Could not get vif")
    endfunction

    task run_phase(uvm_phase phase);
        router_sequence seq;
        phase.raise_objection(this);
        
        seq = router_sequence::type_id::create("seq");
        seq.num_trans = 100; 

        fork
            seq.start(m_env.m_agent.m_sequencer);
            begin
                #6000;
                `uvm_info("TEST", ">>> ASSERTING RESET MID-SIMULATION <<<", UVM_NONE)
                vif.reset = 1;
                #200;
                vif.reset = 0;
                `uvm_info("TEST", ">>> RESET RELEASED <<<", UVM_NONE)
            end
        join
        phase.drop_objection(this);
    endtask
endclass
