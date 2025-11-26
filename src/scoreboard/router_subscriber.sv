class router_subscriber extends uvm_subscriber #(seq_item);
  `uvm_component_utils(router_subscriber)

  // 1. Transaction Handle (Fixes 'Identifier not declared' error)
  seq_item req; 

  // Parameters
  int ROWS = 4;
  int COLUMS = 4;

  // Derived variables for Coverage
  int m_hops;

  // ------------------------------------------------------------------------
  // COVERGROUP (Matches PDF Tables 5 & 6-14)
  // ------------------------------------------------------------------------
  covergroup router_cg;
    option.per_instance = 1;
    option.comment      = "Router Mesh Coverage";

    // --- PDF Table 5: Coverpoints ---

    // 1. ROUTE_MODE_CP
    cp_mode: coverpoint req.mode {
      bins row_first = {seq_item::ROW_FIRST};
      bins col_first = {seq_item::COL_FIRST};
    }

    // 2. SRC.TERMINAL.CP
    cp_src: coverpoint req.src {
      bins src[] = {[0:15]}; 
    }

    // 3. DST.TERMINAL.CP
    cp_dst: coverpoint req.addr {
      bins dst[] = {[0:15]};
    }

    // 4. BROADCAST.CP
    cp_bcast: coverpoint req.broadcast {
      bins non_bcst = {0};
      bins bcst     = {1};
    }

    // 10. ERROR_INJECT.CP
    cp_err_inj: coverpoint req.msg_error {
        bins no_err = {seq_item::NO_ERROR};
        bins err    = {seq_item::HDR_ERROR, seq_item::PAY_ERROR};
    }

    // 13. PATH.LENGTH.CP (Calculated in write function)
    cp_hops: coverpoint m_hops {
      bins hops[] = {[1:8]}; 
    }

    // 14. PAYLOAD.SIZE.CP (Covering data patterns)
    cp_data: coverpoint req.data {
        bins all_zeros = {'h0};
        bins all_ones  = {~0};
        bins others    = default;
    }

    // --- PDF Tables 6-14: Cross Coverage ---

    // CROSS 1: Source x Dest 
    // "Cobertura punto-a-punto entre todos los nodos"
    cx_src_dst: cross cp_src, cp_dst iff (req.broadcast == 0);

    // CROSS 2: Route Mode x Path Length
    // "Ambos modos deben ejercitar rutas de diferentes longitudes"
    cx_mode_hops: cross cp_mode, cp_hops;

    // CROSS 3: Broadcast x Source
    // Did every source send a broadcast?
    cx_src_bcast: cross cp_src, cp_bcast {
        bins src_did_bcast = binsof(cp_bcast.bcst);
    }

    // CROSS 6: Error Type x Dest
    // "Valida que errores ocurran sobre multiples destinos"
    cx_err_dst: cross cp_err_inj, cp_dst {
        bins err_at_dst = binsof(cp_err_inj.err);
    }

    // CROSS 8: Source x Route Mode
    // "Asegura uso de ambos modos de ruteo por todos los nodos origen"
    cx_src_mode: cross cp_src, cp_mode;

    // CROSS 9: Dest x Path Length
    // "Comprueba variabilidad de rutas hacia un mismo destino"
    cx_dst_hops: cross cp_dst, cp_hops;

  endgroup

  function new(string name, uvm_component parent);
    super.new(name, parent);
    router_cg = new();
  endfunction

  // ------------------------------------------------------------------------
  // Helper: Calculate Hops (Manhattan Distance)
  // ------------------------------------------------------------------------
  function void calculate_hops();
    int src_r, src_c, dst_r, dst_c;
    int dist_r, dist_c;

    src_r = req.src / COLUMS;
    src_c = req.src % COLUMS;
    
    if (req.broadcast) begin
        m_hops = 8; // Max hops concept for broadcast
        return;
    end

    dst_r = req.addr / COLUMS;
    dst_c = req.addr % COLUMS;

    dist_r = (src_r > dst_r) ? (src_r - dst_r) : (dst_r - src_r);
    dist_c = (src_c > dst_c) ? (src_c - dst_c) : (dst_c - src_c);

    m_hops = dist_r + dist_c;
    if (m_hops == 0) m_hops = 1; // Self-talk normalized
  endfunction

  function void write(seq_item t);
    req = t;
    calculate_hops();
    router_cg.sample();
  endfunction

endclass
