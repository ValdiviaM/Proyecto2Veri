class router_test extends uvm_test;
    `uvm_component_utils(router_test)

    router_env m_env;

    function new(string name = "router_test", uvm_component parent=null);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        m_env = router_env::type_id::create("m_env", this);
    endfunction

    task run_phase(uvm_phase phase);
        router_sequence seq;

        phase.raise_objection(this);
        
        // Crear y lanzar la secuencia
        seq = router_sequence::type_id::create("seq");
        
        `uvm_info("TEST", "Starting Sequence...", UVM_LOW)
        
        // IMPORTANTE: Asegúrate de que m_sequencer sea visible en router_agent
        seq.start(m_env.m_agent.m_sequencer);
        
        `uvm_info("TEST", "Sequence Finished.", UVM_LOW)
        
        // Damos unos ciclos extra para que los últimos paquetes salgan del DUT
        #1000; 
        
        phase.drop_objection(this);
    endtask

endclass