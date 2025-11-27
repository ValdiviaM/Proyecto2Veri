//------------------------------------------------------------------------------
// Component: router_agent
//------------------------------------------------------------------------------
// Agente UVM que agrupa sequencer, driver y monitor para el DUT.
// - Obtiene la interfaz virtual desde el testbench (tb_top).
// - Crea monitor siempre; crea driver+sequencer solo si el agente está activo.
// - Pasa modports específicos a cada subcomponente mediante uvm_config_db.
// - Conecta el driver al sequencer en connect_phase cuando es activo.
//------------------------------------------------------------------------------

class router_agent extends uvm_agent;
    `uvm_component_utils(router_agent)

    // Componentes del agente
    router_sequencer m_sequencer;
    router_driver    m_driver;
    router_monitor   m_monitor;

    // Handle de la interfaz virtual (sin modport específico aquí)
    virtual mesh_gen_if #(ROWS, COLUMS, DATA_WIDTH) vif;

    //--------------------------------------------------------------------------
    // Constructor
    //--------------------------------------------------------------------------
    function new(string name, uvm_component parent=null);
        super.new(name, parent);
    endfunction

    //--------------------------------------------------------------------------
    // build_phase: obtiene interfaz, crea componentes y configura modports
    //--------------------------------------------------------------------------
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);

        // 1. Get the interface that was set in tb_top
        if (!uvm_config_db#(virtual mesh_gen_if #(ROWS, COLUMS, DATA_WIDTH))::get(this, "", "vif", vif))
            `uvm_fatal("AGT", "Could not get virtual interface 'vif'")

        // 2. Create Components
        // Monitor siempre necesario (observador pasivo)
        m_monitor = router_monitor::type_id::create("m_monitor", this);

        // Driver y Sequencer solo si el agente es ACTIVE (genera tráfico)
        if (get_is_active() == UVM_ACTIVE) begin
            m_sequencer = router_sequencer::type_id::create("m_sequencer", this);
            m_driver    = router_driver::type_id::create("m_driver", this);
        end

        // 3. Pass Interface specific Modports to children
        // Asignamos modports concretos usando uvm_config_db para que cada
        // subcomponente use solo la vista que necesita.
        // Driver -> .TB (controla/produce señales hacia DUT)
        uvm_config_db#(virtual mesh_gen_if #(ROWS, COLUMS, DATA_WIDTH).TB)::set(this, "m_driver", "vif", vif.TB);
        
        // Monitor -> .MON (necesita visibilidad completa para observar)
        uvm_config_db#(virtual mesh_gen_if #(ROWS, COLUMS, DATA_WIDTH).MON)::set(this, "m_monitor", "vif", vif.MON);
    endfunction

    //--------------------------------------------------------------------------
    // connect_phase: conexiones entre componentes UVM
    //--------------------------------------------------------------------------
    function void connect_phase(uvm_phase phase);
        // Connect Driver to Sequencer cuando el agente es activo
        if (get_is_active() == UVM_ACTIVE) begin
            m_driver.seq_item_port.connect(m_sequencer.seq_item_export);
        end
    endfunction

endclass
