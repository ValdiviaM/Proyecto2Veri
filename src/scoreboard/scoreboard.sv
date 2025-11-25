// scoreboard.sv

`include "uvm_macros.svh"
import uvm_pkg::*;
import router_pkg::*;

`uvm_analysis_imp_decl(_in)
`uvm_analysis_imp_decl(_out)

class scoreboard extends uvm_component;
  `uvm_component_utils(scoreboard)

  // Declare the two analysis imps
  uvm_analysis_imp_in #(seq_item, scoreboard)  imp_in;
  uvm_analysis_imp_out #(seq_item, scoreboard) imp_out;

  typedef struct {
    time time_in;
    int  src_port;
    bit [DATA_WIDTH-1:0] data;
  } pkt_info_t;

  pkt_info_t in_db [bit [DATA_WIDTH-1:0]];

  function new(string name="scoreboard", uvm_component parent=null);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    imp_in  = new("imp_in",  this);
    imp_out = new("imp_out", this);
  endfunction



  //  IMP-IN maps to: write_in()

  function void write_in(seq_item t);
    pkt_info_t info;

    info.time_in  = $time;
    info.src_port = t.src;
    info.data     = t.data;

    in_db[t.data] = info;

    `uvm_info("SCB",
      $sformatf("IN: data=0x%0h src=%0d", t.data, t.src),
      UVM_MEDIUM)
  endfunction



  //  IMP-OUT maps to: write_out()

  function void write_out(seq_item t);

    bit [DATA_WIDTH-1:0] key = t.out_dut;

    if (!in_db.exists(key)) begin
      `uvm_error("SCB",
        $sformatf("OUT: data=0x%0h has no matching IN", key))
      return;
    end

    pkt_info_t exp = in_db[key];
    in_db.delete(key);

    `uvm_info("SCB",
      $sformatf("OUT: data=0x%0h exp_src=%0d got_port=%0d",
                key, exp.src_port, t.out_port),
      UVM_MEDIUM);

  endfunction

endclass

