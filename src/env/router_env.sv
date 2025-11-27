class router_env extends uvm_env;
  `uvm_component_utils(router_env)

  router_agent      m_agent;
  scoreboard        m_sb;
  
  // 1. Declare Handle
  router_subscriber m_cov; 

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    m_agent = router_agent::type_id::create("m_agent", this);
    m_sb    = scoreboard::type_id::create("m_sb", this);
    
    // 2. Create Component
    m_cov   = router_subscriber::type_id::create("m_cov", this);
  endfunction

  function void connect_phase(uvm_phase phase);
    m_agent.m_monitor.ap_in.connect(m_sb.m_analysis_imp_in);
    m_agent.m_monitor.ap_out.connect(m_sb.m_analysis_imp_out);

    // 3. Connect Input Monitor -> Coverage Subscriber
    // We use ap_in because we want to see what we ATTEMPTED to drive
    m_agent.m_monitor.ap_in.connect(m_cov.analysis_export); 
  endfunction

endclass
