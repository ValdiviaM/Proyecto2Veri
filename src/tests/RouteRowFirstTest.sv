class RouteRowFirstTest extends base_test;
  `uvm_component_utils(RouteRowFirstTest)

  function new(string name="RouteRowFirstTest", uvm_component parent=null);
    super.new(name, parent); // Llamada al constructor de base_test
  endfunction

  task run_phase(uvm_phase phase);
    router_sequence seq;
    phase.raise_objection(this); // Señalamos que el test está activo
    
    seq = router_sequence::type_id::create("seq"); // Instancia de secuencia

    // -----------------------------
    // Configurar "knobs" específicos para este test
    // -----------------------------
    seq.num_trans  = 100;   // Número de paquetes a enviar
    seq.route_mode = 1;     // Forzar modo ROW_FIRST
    seq.inject_error = 1;   // Inyectar errores para verificar que scoreboard los capture

    seq.start(m_env.m_agent.m_sequencer); // Lanzar secuencia en el sequencer del agent
    
    #1000; // Delay final antes de soltar objection
    phase.drop_objection(this); // Señalamos que el test ha terminado
  endtask
endclass
