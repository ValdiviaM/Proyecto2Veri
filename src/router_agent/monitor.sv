import uvm_pkg::*;
`include "uvm_macros.svh"
import router_pkg::*;


// Monitor for mesh_gen_if MON modport
// Observes DUT outputs (data_out, pndng, popin) and DUT inputs
// (data_out_i_in, pndng_i_in, pop) and sends seq_item to scoreboard

class router_monitor extends uvm_monitor;
  `uvm_component_utils(router_monitor)

  // Analysis port with PARAMETERIZED seq_item
  uvm_analysis_port #(
    seq_item#(ADDR_WIDTH, DATA_WIDTH, MAX_N_CYCLES)
  ) mon_analysis_port;

  // Virtual interface, using MODPORT MON
  virtual mesh_gen_if.MON vif;

  // Constructor
  function new(string name="router_monitor", uvm_component parent=null);
    super.new(name, parent);
  endfunction

  // Build phase
  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    // NOTE: use the SAME field name ("vif") as in the driver config_db
    if (!uvm_config_db#(virtual mesh_gen_if.MON)::get(this, "", "vif", vif))
      `uvm_fatal("MON", "Could not get vif from config_db")

    mon_analysis_port = new("mon_analysis_port", this);
  endfunction


  // Run phase: monitor handshake at each terminal
  // We create an item whenever the DUT sends a packet out:
  //   pndng[i] && popin[i]
  // and capture data_out[i] into item.out_dut, and i into item.addr

  virtual task run_phase(uvm_phase phase);
    super.run_phase(phase);

    int N;
    N = $size(vif.pndng);  // number of terminals

    `uvm_info("MON", $sformatf("Monitor started, N terminals = %0d", N), UVM_LOW)

    forever begin
      @(posedge vif.clk);

      if (!vif.reset) begin
        for (int i = 0; i < N; i++) begin

          // DUT terminal handshake: router has valid data and
          // environment accepts it (popin)
          if (vif.pndng[i] && vif.popin[i]) begin

            seq_item#(ADDR_WIDTH, DATA_WIDTH, MAX_N_CYCLES) item;
            item = seq_item#(ADDR_WIDTH, DATA_WIDTH, MAX_N_CYCLES)
                     ::type_id::create($sformatf("mon_item_port%0d", i), this);

            // We use addr as the observed DESTINATION TERMINAL
            item.addr    = i[ADDR_WIDTH-1:0];
            item.out_dut = vif.data_out[i];

            // Optional: we could also observe input side:
            // - vif.data_out_i_in
            // - vif.pndng_i_in
            // - vif.pop
            // if you want to build richer checks later.

            `uvm_info("MON",
              $sformatf("Observed packet: port=%0d, out_dut=0x%0h",
                        i, item.out_dut),
              UVM_MEDIUM)

            mon_analysis_port.write(item);
          end
        end
      end
    end
  endtask

endclass : router_monitor

