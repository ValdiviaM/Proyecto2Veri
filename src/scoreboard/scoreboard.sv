// scoreboard.sv

`include "uvm_macros.svh"
import uvm_pkg::*;
import router_pkg::*;

class scoreboard extends uvm_component;
  `uvm_component_utils(scoreboard)

  // Imp ports
  uvm_analysis_imp #(seq_item, scoreboard) imp_in;
  uvm_analysis_imp #(seq_item, scoreboard) imp_out;

  // DB por data (simple)
  typedef struct {
    time time_in;
    int  src_port;
    bit  [DATA_WIDTH-1:0] data;
  } pkt_info_t;

  // Clave: data (en un diseño real usarías ID)
  pkt_info_t in_db [bit [DATA_WIDTH-1:0]];

  function new(string name="scoreboard", uvm_component parent=null);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    imp_in  = new("imp_in",  this);
    imp_out = new("imp_out", this);
  endfunction

  // Entrada
  function void write(seq_item t); // se usa para imp_in
    pkt_info_t info;
    info.time_in  = $time;
    info.src_port = t.src;
    info.data     = t.data;
    in_db[t.data] = info;
    `uvm_info("SCB", $sformatf("IN: data=0x%0h src=%0d", t.data, t.src), UVM_MEDIUM)
  endfunction

  // Sobrecarga para la salida (imp_out)
  function void write_out(seq_item t);
    bit [DATA_WIDTH-1:0] key = t.out_dut;

    if (!in_db.exists(key)) begin
      `uvm_error("SCB", $sformatf("OUT: data=0x%0h no tiene match en IN", key))
      return;
    end

    pkt_info_t exp = in_db[key];
    in_db.delete(key);

    `uvm_info("SCB", $sformatf("OUT: data=0x%0h exp_src=%0d got_port=%0d",
                               key, exp.src_port, t.out_port), UVM_MEDIUM)
    // Aquí podrías agregar referencia XY ? puerto, etc.
  endfunction

endclass

