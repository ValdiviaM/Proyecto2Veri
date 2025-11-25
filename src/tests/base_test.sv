// tests/base_test.sv
`include "uvm_macros.svh"
import uvm_pkg::*;
import router_pkg::*;

class base_test extends uvm_test;
  `uvm_component_utils(base_test)

  router_env      m_env;
  router_sequence seq;

  // CONFIG
  int cfg_num_msgs      = 200;
  int cfg_src_terminal  = -1;
  int cfg_dst_terminal  = -1;
  bit cfg_mode          = 1;  // 1=ROW_FIRST, 0=COL_FIRST
  bit cfg_broadcast     = 0;
  bit cfg_inject_error  = 0;
  bit cfg_reset_mid_tx  = 0;
  bit cfg_fifo_stress   = 0;

  function new(string name="base_test", uvm_component parent=null);
    super.new(name,parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    m_env = router_env::type_id::create("m_env", this);
  endfunction

  task run_phase(uvm_phase phase);
    phase.raise_objection(this);

    seq = router_sequence::type_id::create("seq");

    // Pasar parámetros a la secuencia
    seq.num_trans       = cfg_num_msgs;
    seq.src_terminal    = cfg_src_terminal;
    seq.dst_terminal    = cfg_dst_terminal;
    seq.route_mode      = cfg_mode;
    seq.force_broadcast = cfg_broadcast;
    seq.inject_error    = cfg_inject_error;
    seq.reset_mid_tx    = cfg_reset_mid_tx;
    seq.fifo_stress     = cfg_fifo_stress;

    seq.start(m_env.m_agent.m_sequencer);

    #1000;
    phase.drop_objection(this);
  endtask

endclass

