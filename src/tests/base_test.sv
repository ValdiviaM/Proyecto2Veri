class base_test extends uvm_test;
    `uvm_component_utils(base_test)
    router_env m_env; // Instancia del environment

    // -----------------------------
    // Configurable parameters (pueden ser sobreescritos por tests extendidos)
    // -----------------------------
    int cfg_num_msgs     = 2000; // Número de transacciones a generar
    int cfg_src_terminal = -1;   // Terminal de origen por defecto: aleatorio

    function new(string name = "base_test", uvm_component parent=null);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        m_env = router_env::type_id::create("m_env", this); // Crear environment
    endfunction

    task run_phase(uvm_phase phase);
        router_sequence seq;
        phase.raise_objection(this); // Señalamos que el test está activo
        
        seq = router_sequence::type_id::create("seq"); // Instanciar secuencia base
        
        // -----------------------------
        // Aplicar configuración a los "knobs" de la secuencia
        // -----------------------------
        seq.num_trans    = cfg_num_msgs;     
        seq.src_terminal = cfg_src_terminal;

        // Ejemplo de opciones adicionales (descomentarlas si se desea)
        // seq.src_terminal = 0;        // Forzar todos los paquetes desde el puerto 0
        // seq.inject_error = 1;        // Activar inyección de errores

        if(!seq.randomize()) `uvm_fatal("TEST", "Randomization failed")

        `uvm_info("TEST", "Starting Sequence with Configured Knobs...", UVM_LOW)
        seq.start(m_env.m_agent.m_sequencer); // Lanzar la secuencia en el sequencer del agent
        
        // -----------------------------
        // Esperar que la base de datos de paquetes se vacíe o timeout de seguridad
        // -----------------------------
        fork
            begin
                // Wait hasta que todos los paquetes sean recibidos
                #1000
                wait(m_env.m_sb.packet_db.size() == 0);
                `uvm_info("TEST", "All packets received! Drain complete.", UVM_LOW)
            end
            begin
                // Timeout: evita bloqueo si se pierde algún paquete
                #(cfg_num_msgs * 1000ns); 
                `uvm_error("TEST", "Timeout waiting for scoreboard to drain. Packets likely lost.")
            end
        join_any
        disable fork; // Terminar el thread que no completó (timeout o wait)

        phase.drop_objection(this); // Señalamos que el test ha terminado
    endtask
endclass
