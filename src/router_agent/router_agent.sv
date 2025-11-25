class router_agent extends uvm_agent;
    `uvm_component_utils(router_agent)

    // Components
    router_sequencer m_sequencer;
    router_driver    m_driver;
    router_monitor   m_monitor;

    // Interface Handle
    virtual mesh_gen_if #(ROWS, COLUMS, DATA_WIDTH) vif;

    function new(string name, uvm_component parent=null);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);

        // 1. Get the interface that was set in tb_top
        if (!uvm_config_db#(virtual mesh_gen_if #(ROWS, COLUMS, DATA_WIDTH))::get(this, "", "vif", vif))
            `uvm_fatal("AGT", "Could not get virtual interface 'vif'")

        // 2. Create Components
        m_monitor = router_monitor::type_id::create("m_monitor", this);

        // Driver and Sequencer are only needed if the agent is ACTIVE (generating traffic)
        if (get_is_active() == UVM_ACTIVE) begin
            m_sequencer = router_sequencer::type_id::create("m_sequencer", this);
            m_driver    = router_driver::type_id::create("m_driver", this);
        end

        // 3. Pass Interface specific Modports to children
        // The Driver gets the .TB modport
        uvm_config_db#(virtual mesh_gen_if #(ROWS, COLUMS, DATA_WIDTH).TB)::set(this, "m_driver", "vif", vif.TB);
        
        // The Monitor gets the .MON modport
        uvm_config_db#(virtual mesh_gen_if #(ROWS, COLUMS, DATA_WIDTH).MON)::set(this, "m_monitor", "vif", vif.MON);
    endfunction

    function void connect_phase(uvm_phase phase);
        // Connect Driver to Sequencer
        if (get_is_active() == UVM_ACTIVE) begin
            m_driver.seq_item_port.connect(m_sequencer.seq_item_export);
        end
    endfunction

endclass
