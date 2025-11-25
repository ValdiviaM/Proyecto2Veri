// router_driver.sv

`include "uvm_macros.svh"
import uvm_pkg::*;
import router_pkg::*;

class router_driver extends uvm_driver #(seq_item);
  `uvm_component_utils(router_driver)

  // Debe coincidir con el modport TB de la interfaz
  virtual mesh_gen_if #(ROWS, COLUMS, DATA_WIDTH).TB vif;
  
  localparam int NUM_PORTS = ROWS*2 + COLUMS*2;
  seq_item req;

  // -------------------------------------------------------------
  function new(string name="router_driver", uvm_component parent=null);
    super.new(name, parent);
  endfunction

  // -------------------------------------------------------------
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    if (!uvm_config_db#(
          virtual mesh_gen_if #(ROWS, COLUMS, DATA_WIDTH).TB
        )::get(this, "", "vif", vif))
      `uvm_fatal("DRV", "Driver could not get TB modport VIF")
    else
      `uvm_info("DRV", "Driver VIF OK", UVM_LOW)
  endfunction

  // -------------------------------------------------------------
  task run_phase(uvm_phase phase);

    // Inicializar entradas TB?DUT para evitar X
    for (int i = 0; i < NUM_PORTS; i++) begin
      vif.drv_pndng_i_in[i]    <= 1'b0;
      vif.drv_data_out_i_in[i] <= '0;
      // NO tocamos drv_popin aquí: lo maneja el dummy consumer de la IF
    end

    // Esperar a que se libere el reset
    @(posedge vif.clk);
    wait (vif.reset == 1'b0);

    `uvm_info("DRV", "Reset released  Driver ACTIVE", UVM_LOW)

    forever begin
      seq_item_port.get_next_item(req);
      drive(req);
      seq_item_port.item_done();
    end
  endtask

  // -------------------------------------------------------------
  // DRIVE ONE TRANSACTION
  // -------------------------------------------------------------
  task drive(seq_item t);

    int port;
    reg [DATA_WIDTH-1:0] payload;   // usar reg para compatibilidad VCS

    // Puerto de origen
    port = t.src;

    if (port >= NUM_PORTS) begin
      `uvm_error("DRV", $sformatf("Invalid source port %0d", port))
      return;
    end

    // Payload + errores
    payload = t.data;

    case (t.msg_error)
      seq_item::HDR_ERROR: payload[DATA_WIDTH-1] = ~payload[DATA_WIDTH-1];
      seq_item::PAY_ERROR: payload[0]            = ~payload[0];
      default: ; // NO_ERROR
    endcase

    // Paso 1  Assert petición TB?DUT
    @(posedge vif.clk);

    vif.drv_data_out_i_in[port] <= payload;
    vif.drv_pndng_i_in[port]    <= 1'b1;

    `uvm_info("DRV",
      $sformatf("SEND: port=%0d data=0x%0h dst=%0d mode=%0d bdcst=%0b err=%0d",
                port, payload, t.addr, t.mode, t.broadcast, t.msg_error),
      UVM_MEDIUM)

    // Paso 2  Esperar ACK del DUT (pop)
    fork
      // ACK
      begin : wait_ack
        while (vif.pop[port] == 1'b0) @(posedge vif.clk);
        `uvm_info("DRV",
          $sformatf("ACK from DUT on port %0d", port),
          UVM_LOW)
      end

      // Time-out
      begin : watchdog
        repeat (200) @(posedge vif.clk);
        `uvm_error("DRV",
          $sformatf("TIMEOUT waiting for pop[%0d]", port))
      end
    join_any
    disable fork;

    // Paso 3  Bajar petición
    @(posedge vif.clk);
    vif.drv_pndng_i_in[port] <= 1'b0;

    // Paso 4  Gap entre paquetes
    repeat (t.cycles_between) @(posedge vif.clk);

  endtask : drive

endclass : router_driver

