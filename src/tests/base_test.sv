class base_test extends uvm_test;
  `uvm_component_utils(base_test)

  router_agent m_agent;
  router_sequence seq;

  //CONFIGURACIÓN PARA LOS TESTS 

  // Cantidad de mensajes a generar
  int cfg_num_msgs = 200;

  // Terminal origen (0 .. N-1)
  int cfg_src_terminal = -1;   // -1 = random

  // Terminal destino (0 .. N-1)
  int cfg_dst_terminal = -1;   // -1 = random

  // Modo de ruta
  bit cfg_mode = 1; // 1=ROW_FIRST, 0=COL_FIRST

  // broadcast
  bit cfg_broadcast = 0;

  // Error injection
  bit cfg_inject_error = 0;

  // Reset en medio de la transferencia
  bit cfg_reset_mid_tx = 0;

  // Activar estrés de FIFO
  bit cfg_fifo_stress = 0;


  function new(string name="base_test", uvm_component parent=null);
    super.new(name,parent);
  endfunction


  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    m_agent = router_agent::type_id::create("m_agent", this);
  endfunction


  task run_phase(uvm_phase phase);
    phase.raise_objection(this);

    seq = router_sequence#(
      router_pkg::ADDR_WIDTH,
      router_pkg::DATA_WIDTH,
      router_pkg::MAX_N_CYCLES
    )::type_id::create("seq");

    // PASAR PARAMETROS A LA SECUENCIA
    seq.n_items         = cfg_num_msgs;
    seq.force_src       = cfg_src_terminal;
    seq.force_dst       = cfg_dst_terminal;
    seq.force_mode      = cfg_mode;
    seq.force_broadcast = cfg_broadcast;
    seq.force_error     = cfg_inject_error;
    seq.do_reset_mid_tx = cfg_reset_mid_tx;
    seq.do_fifo_stress  = cfg_fifo_stress;

    seq.start(m_agent.m_sequencer);

    phase.drop_objection(this);
  endtask

endclass

