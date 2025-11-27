class RouteRowFirstTest extends base_test;
  `uvm_component_utils(RouteRowFirstTest)

  function new(string name="RouteRowFirstTest", uvm_component parent=null);
    super.new(name, parent);
  endfunction

  task run_phase(uvm_phase phase);
    router_sequence seq;
    phase.raise_objection(this);
    
    seq = router_sequence::type_id::create("seq");

    // Configure Knobs for this specific test
    seq.num_trans  = 100;
    seq.route_mode = 1; // Force ROW_FIRST
    seq.inject_error = 1; // Inject errors to see if scoreboard catches them

    seq.start(m_env.m_agent.m_sequencer);
    
    #1000;
    phase.drop_objection(this);
  endtask
endclass
