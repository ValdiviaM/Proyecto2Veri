class router_env extends uvm_env;
    `uvm_component_utils(router_env)

    router_agent m_agent;
    scoreboard   m_sb;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        m_agent = router_agent::type_id::create("m_agent", this);
        m_sb    = scoreboard::type_id::create("m_sb", this);
    endfunction

    function void connect_phase(uvm_phase phase);
        // Conectar puertos del Monitor a los Exports del Scoreboard
        // Asegúrate de que el monitor dentro del agente se llame 'router_monitor' o similar
        // y que lo hayas instanciado como 'm_monitor' en el agente.
        
        // Input: Monitor -> Scoreboard
        m_agent.m_monitor.ap_in.connect(m_sb.m_analysis_imp_in);
        
        // Output: Monitor -> Scoreboard
        m_agent.m_monitor.ap_out.connect(m_sb.m_analysis_imp_out);
    endfunction

endclass