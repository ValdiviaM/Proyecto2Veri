// 1. EXHAUSTIVE TEST (This will give you high coverage!)
class exhaustive_test extends base_test;
    `uvm_component_utils(exhaustive_test)

    function new(string name = "exhaustive_test", uvm_component parent=null);
        super.new(name, parent);
    endfunction

    task run_phase(uvm_phase phase);
        full_mesh_seq seq;
        phase.raise_objection(this);
        
        `uvm_info("TEST", "Running Exhaustive Matrix Test...", UVM_LOW)
        seq = full_mesh_seq::type_id::create("seq");
        seq.start(m_env.m_agent.m_sequencer);
        
        phase.drop_objection(this);
    endtask
endclass

// 2. BROADCAST TEST
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
        
        phase.drop_objection(this);
    endtask
endclass
