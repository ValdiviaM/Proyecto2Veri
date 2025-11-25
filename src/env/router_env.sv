// router_env.sv

class router_env extends uvm_env;
  `uvm_component_utils(router_env)

  router_agent m_agent;
  scoreboard   m_sb;

  function new(string name, uvm_component parent=null);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    m_agent = router_agent::type_id::create("m_agent", this);
    m_sb    = scoreboard  ::type_id::create("m_sb",    this);
  endfunction

  function void connect_phase(uvm_phase phase);
    m_agent.m_monitor.ap_in.connect (m_sb.m_analysis_imp_in);
    m_agent.m_monitor.ap_out.connect(m_sb.m_analysis_imp_out);
  endfunction

endclass

