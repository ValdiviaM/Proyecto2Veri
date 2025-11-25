class router_sequencer extends uvm_sequencer #(seq_item);
    `uvm_component_utils(router_sequencer)
    function new(string name = "router_sequencer", uvm_component parent=null);
        super.new(name, parent);
    endfunction
endclass
