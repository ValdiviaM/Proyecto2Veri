//------------------------------------------------------------------------------
// Subscriber UVM para router_agent
// - Recibe seq_item desde analysis port
// - Calcula cobertura funcional: covergroup con coverpoints y crosses
// - Calcula "hops" para rutas y muestrea covergroup en write()
//------------------------------------------------------------------------------
class router_subscriber extends uvm_subscriber #(seq_item);
  `uvm_component_utils(router_subscriber)

  seq_item req;          // Handle a la transacción actual
  int ROWS = 4;
  int COLUMS = 4;
  int m_hops;            // Distancia Manhattan entre src y dst

  // Covergroup para métricas de funcionalidad y combinaciones
  covergroup router_cg;
    option.per_instance = 1;
    option.comment      = "Router Mesh Coverage";

    cp_mode: coverpoint req.mode { bins row_first = {seq_item::ROW_FIRST}; bins col_first = {seq_item::COL_FIRST}; }
    cp_src: coverpoint req.src   { bins src[] = {[0:15]}; }
    cp_dst: coverpoint req.addr  { bins dst[] = {[0:15]}; }
    cp_bcast: coverpoint req.broadcast { bins non_bcst = {0}; bins bcst = {1}; }
    cp_err_inj: coverpoint req.msg_error { bins no_err = {seq_item::NO_ERROR}; bins err = {seq_item::HDR_ERROR, seq_item::PAY_ERROR}; }
    cp_hops: coverpoint m_hops { bins hops[] = {[1:8]}; }
    cp_data: coverpoint req.data { bins all_zeros = {'h0}; bins all_ones = {~0}; bins others = default; }

    // Cross coverage
    cx_src_dst: cross cp_src, cp_dst iff (req.broadcast == 0);
    cx_mode_hops: cross cp_mode, cp_hops;
    cx_src_bcast: cross cp_src, cp_bcast { bins src_did_bcast = binsof(cp_bcast.bcst); }
    cx_err_dst: cross cp_err_inj, cp_dst { bins err_at_dst = binsof(cp_err_inj.err); }
    cx_src_mode: cross cp_src, cp_mode;
    cx_dst_hops: cross cp_dst, cp_hops;
  endgroup

  function new(string name, uvm_component parent);
    super.new(name, parent);
    router_cg = new();
  endfunction

  // Calcula hops entre src y dst (Manhattan distance)
  function void calculate_hops();
    int src_r = req.src / COLUMS;
    int src_c = req.src % COLUMS;
    if (req.broadcast) begin m_hops = 8; return; end
    int dst_r = req.addr / COLUMS;
    int dst_c = req.addr % COLUMS;
    int dist_r = (src_r > dst_r) ? (src_r - dst_r) : (dst_r - src_r);
    int dist_c = (src_c > dst_c) ? (src_c - dst_c) : (dst_c - src_c);
    m_hops = dist_r + dist_c;
    if (m_hops == 0) m_hops = 1;
  endfunction

  // Write: recibe item, calcula hops y samplea covergroup
  function void write(seq_item t);
    req = t;
    calculate_hops();
    router_cg.sample();
  endfunction

endclass
