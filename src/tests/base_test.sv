class base_test extends uvm_test;
    `uvm_component_utils(base_test)
    router_env m_env;

    // Configurable parameters available on command line or extended tests
    int cfg_num_msgs     = 50;
    int cfg_src_terminal = -1; // Default Random
    
    function new(string name = "base_test", uvm_component parent=null);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        m_env = router_env::type_id::create("m_env", this);
    endfunction

    task run_phase(uvm_phase phase);
        router_sequence seq;
        phase.raise_objection(this);
        
        seq = router_sequence::type_id::create("seq");
        
        // ---------------------------------------------------------
        // APPLY CONFIGURATION TO SEQUENCE KNOBS
        // ---------------------------------------------------------
        seq.num_trans    = cfg_num_msgs;
        seq.src_terminal = cfg_src_terminal; 
        
        // Example: If you want to force all packets to enter port 0:
        // seq.src_terminal = 0; 

        // Example: Enable error injection
        // seq.inject_error = 1;

        if(!seq.randomize()) `uvm_fatal("TEST", "Randomization failed")

        `uvm_info("TEST", "Starting Sequence with Configured Knobs...", UVM_LOW)
        seq.start(m_env.m_agent.m_sequencer);
        
        #2000; 
        phase.drop_objection(this);
    endtask
endclass
