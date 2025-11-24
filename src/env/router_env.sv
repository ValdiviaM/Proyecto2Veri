`include "uvm_macros.svh"
import uvm_pkg::*;
import router_pkg::*;

class router_agent extends uvm_agent;
    `uvm_component_utils(router_agent)

    router_sequencer m_sequencer;
    router_driver    m_driver;

    virtual mesh_gen_if vif;

    function new(string name, uvm_component parent=null);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);

        if (!uvm_config_db#(virtual mesh_gen_if)::get(this, "", "vif", vif))
            `uvm_fatal("AGT", "No virtual interface found")

        m_sequencer = router_sequencer::type_id::create("m_sequencer", this);
        m_driver    = router_driver   ::type_id::create("m_driver",    this);

        uvm_config_db#(virtual mesh_gen_if)::set(this, "m_driver", "vif", vif);
    endfunction

    function void connect_phase(uvm_phase phase);
        m_driver.seq_item_port.connect(m_sequencer.seq_item_export);
    endfunction

endclass
