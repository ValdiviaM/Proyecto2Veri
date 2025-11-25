class router_env extends uvm_env;
    `uvm_component_utils(router_env)

    router_agent m_agent;
    scoreboard   m_sb;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Create Agent
        m_agent = router_agent::type_id::create("m_agent", this);
        
        // Create Scoreboard
        m_sb = scoreboard::type_id::create("m_sb", this);
    endfunction

    function void connect_phase(uvm_phase phase);
        // Connect Monitor Input Analysis Port -> Scoreboard Input Import
        m_agent.m_monitor.ap_in.connect(m_sb.m_analysis_imp_in);
        
        // Connect Monitor Output Analysis Port -> Scoreboard Output Import
        m_agent.m_monitor.ap_out.connect(m_sb.m_analysis_imp_out);
    endfunction

endclass
