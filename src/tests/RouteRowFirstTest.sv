class RouteRowFirstTest extends base_test;
  `uvm_component_utils(RouteRowFirstTest)

  function new(string name="RouteRowFirstTest", uvm_component parent=null);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    cfg_mode = 1; // ROW FIRST
    cfg_num_msgs = 200;

    `uvm_info("TEST", "RouteRowFirstTest configurado", UVM_LOW)
  endfunction
endclass

