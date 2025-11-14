class test_smoke extends uvm_test;
    `uvm_component_utils(test_smoke)

    router_agent m_agent;
    router_sequence #(8,8,15) seq;

    function new(string name="test_smoke", uvm_component parent=null);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);

        m_agent = router_agent::type_id::create("m_agent", this);
    endfunction

    task run_phase(uvm_phase phase);
        phase.raise_objection(this);

        seq = router_sequence#(8,8,15)::type_id::create("seq");
        seq.start(m_agent.m_sequencer);

        #500;
        phase.drop_objection(this);
    endtask

endclass
