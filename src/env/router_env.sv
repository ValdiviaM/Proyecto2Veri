// router_env.sv

`include "uvm_macros.svh"
import uvm_pkg::*;
import router_pkg::*;

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
    // Asumiendo que en scoreboard usas dos imps:
    //   imp_in  y imp_out, y en monitor ap_in / ap_out
    m_agent.m_monitor.ap_in.connect (m_sb.imp_in);
    m_agent.m_monitor.ap_out.connect(m_sb.imp_out);
  endfunction

endclass

