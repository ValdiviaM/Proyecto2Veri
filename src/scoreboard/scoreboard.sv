// scoreboard.sv

// --------------------------------------------------------------------
// Declaración de analysis_imp con sufijos _in y _out
// (Asegúrate de NO repetir estas líneas en otros archivos)
// --------------------------------------------------------------------
`uvm_analysis_imp_decl(_in)
`uvm_analysis_imp_decl(_out)

// --------------------------------------------------------------------
// SCOREBOARD
// --------------------------------------------------------------------
class scoreboard extends uvm_component;
  `uvm_component_utils(scoreboard)

  // Conectan con ap_in / ap_out del monitor
  uvm_analysis_imp_in  #(seq_item, scoreboard) m_analysis_imp_in;
  uvm_analysis_imp_out #(seq_item, scoreboard) m_analysis_imp_out;

  // Info que guardamos cuando el paquete ENTRA al router
  typedef struct {
    time                   t_in;
    int                    src_port;
    bit [DATA_WIDTH-1:0]   data;
  } pkt_info_t;

  // DB indexada por data de entrada (clave = payload)
  pkt_info_t in_db [bit [DATA_WIDTH-1:0]];

  function new(string name="scoreboard", uvm_component parent=null);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    m_analysis_imp_in  = new("m_analysis_imp_in",  this);
    m_analysis_imp_out = new("m_analysis_imp_out", this);
  endfunction

  // ------------------------------------------------------------------
  // Canal de ENTRADA (desde monitor.ap_in)
  //
  // El monitor hace:
  //   item_in.data = vif.data_out_i_in[i];
  //   item_in.src  = i[ADDR_WIDTH-1:0];
  //
  // Aquí guardamos tiempo, puerto y payload.
  // ------------------------------------------------------------------
  function void write_in(seq_item t);
    pkt_info_t info;

    info.t_in     = $time;
    info.src_port = t.src;
    info.data     = t.data;

    in_db[t.data] = info;

    `uvm_info("SCB",
      $sformatf("IN : src=%0d data=0x%0h stored", t.src, t.data),
      UVM_MEDIUM)
  endfunction

  // ------------------------------------------------------------------
  // Canal de SALIDA (desde monitor.ap_out)
  //
  // El monitor hace:
  //   item_out.out_dut  = vif.data_out[i];
  //   item_out.out_port = i[ADDR_WIDTH-1:0];
  //
  // Aquí hacemos match por payload y calculamos delay.
  // ------------------------------------------------------------------
  function void write_out(seq_item t);
    bit [DATA_WIDTH-1:0] key;
    pkt_info_t           exp;
    time                 delay;

    key = t.out_dut;

    if (!in_db.exists(key)) begin
      `uvm_warning("SCB",
        $sformatf("OUT: data=0x%0h on port %0d without matching IN",
                  key, t.out_port))
      return;
    end

    exp   = in_db[key];
    delay = $time - exp.t_in;

    in_db.delete(key);

    `uvm_info("SCB",
      $sformatf("OK : data=0x%0h src=%0d -> dst=%0d delay=%0t",
                key, exp.src_port, t.out_port, delay),
      UVM_MEDIUM)

    // Aquí podrías agregar más checks, por ejemplo:
    //  - comparar t.out_port con una referencia calculada desde exp.data
    //  - analizar si delay < umbral, etc.
  endfunction

endclass

