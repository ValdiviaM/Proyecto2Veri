//------------------------------------------------------------------------------
// Environment: router_env
//------------------------------------------------------------------------------
// Contiene y conecta los componentes principales del ambiente UVM:
// - router_agent: maneja driver, sequencer y monitor.
// - scoreboard: verifica resultados comparando entradas/salidas.
// - router_subscriber: recolecta información para cobertura funcional.
//------------------------------------------------------------------------------
class router_env extends uvm_env;
  `uvm_component_utils(router_env)

  // Declaración de componentes del ambiente
  router_agent      m_agent;      // Agente principal del DUT
  scoreboard        m_sb;         // Scoreboard para verificación
  router_subscriber m_cov;        // Subscriber para cobertura

  //--------------------------------------------------------------------------
  // Constructor
  //--------------------------------------------------------------------------
  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  //--------------------------------------------------------------------------
  // build_phase: creación de componentes
  //--------------------------------------------------------------------------
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    // Crear agente
    m_agent = router_agent::type_id::create("m_agent", this);

    // Crear scoreboard
    m_sb    = scoreboard::type_id::create("m_sb", this);

    // Crear subscriber de cobertura
    m_cov   = router_subscriber::type_id::create("m_cov", this);
  endfunction

  //--------------------------------------------------------------------------
  // connect_phase: conexión de análisis entre monitor, scoreboard y subscriber
  //--------------------------------------------------------------------------
  function void connect_phase(uvm_phase phase);

    // Conectar análisis de entrada y salida hacia el scoreboard
    m_agent.m_monitor.ap_in.connect(m_sb.m_analysis_imp_in);
    m_agent.m_monitor.ap_out.connect(m_sb.m_analysis_imp_out);

    // Conectar bus de entrada al subscriber de cobertura
    // Se usa ap_in porque interesa medir lo que se intenta conducir al DUT
    m_agent.m_monitor.ap_in.connect(m_cov.analysis_export);
  endfunction

endclass
