
// base_test.sv  TEST BASE PARA TODOS LOS DEMÁS TESTS




class base_test extends uvm_test;
  `uvm_component_utils(base_test)

  // Environment completo (agent + scoreboard)
  router_env m_env;

  // Secuencia principal
  router_sequence #(
    ADDR_WIDTH,
    DATA_WIDTH,
    MAX_N_CYCLES
  ) seq;

  
  // CONFIGURACIÓN PARA LOS TESTS DERIVADOS
  

  // Cantidad de mensajes a generar
  int cfg_num_msgs      = 200;

  // Terminal origen (0 .. NUM_PORTS-1)  (-1 = random en la sequence)
  int cfg_src_terminal  = -1;

  // Terminal destino (0 .. NUM_PORTS-1) (-1 = random en la sequence)
  int cfg_dst_terminal  = -1;

  // Modo de ruta (1 = ROW_FIRST, 0 = COL_FIRST)
  bit cfg_mode          = 1;

  // Broadcast
  bit cfg_broadcast     = 0;

  // Inyección de error
  bit cfg_inject_error  = 0;

  // Reset en medio de la transferencia (la lógica la podrías implementar luego)
  bit cfg_reset_mid_tx  = 0;

  // Estrés de FIFO (para futuros tests)
  bit cfg_fifo_stress   = 0;


  
  // CONSTRUCTOR
  
  function new(string name="base_test", uvm_component parent=null);
    super.new(name, parent);
  endfunction


  
  // BUILD PHASE  CREAR ENV
  
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    // El env internamente crea el agent, driver, sequencer, monitor, scoreboard
    m_env = router_env::type_id::create("m_env", this);
  endfunction


  
  // RUN PHASE  LANZAR LA SEQUENCE
  
  task run_phase(uvm_phase phase);
    phase.raise_objection(this);

    // Crear la secuencia con los parámetros globales del pkg
    seq = router_sequence#(
            ADDR_WIDTH,
            DATA_WIDTH,
            MAX_N_CYCLES
          )::type_id::create("seq");

    // Pasar los parámetros desde la configuración del test
    seq.num_trans        = cfg_num_msgs;
    seq.src_terminal     = cfg_src_terminal;
    seq.dst_terminal     = cfg_dst_terminal;
    seq.route_mode       = cfg_mode;
    seq.force_broadcast  = cfg_broadcast;
    seq.inject_error     = cfg_inject_error;
    seq.reset_mid_tx     = cfg_reset_mid_tx;
    seq.fifo_stress      = cfg_fifo_stress;

    // Arrancar la secuencia en el sequencer del agente dentro del env
    seq.start(m_env.m_agent.m_sequencer);

    phase.drop_objection(this);
  endtask

endclass : base_test

