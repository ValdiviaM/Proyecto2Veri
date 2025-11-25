class router_subscriber extends uvm_subscriber #(seq_item);
  `uvm_component_utils(router_subscriber)

  // ------------------------------------------------------------------------
  // 1. DEFINE THE MISSING VARIABLE
  // ------------------------------------------------------------------------
  seq_item req;  // <--- ADD THIS LINE. This fixes the "Undeclared" error.

  // Parameters
  int ROWS = 4;
  int COLUMS = 4;

  // Helper variables
  int m_hops;

  // ------------------------------------------------------------------------
  // COVERGROUP
  // ------------------------------------------------------------------------
  covergroup router_cg;
    option.per_instance = 1;
    option.comment      = "Router Functional Coverage";

    // Now 'req' exists in the class scope, so these lines work:
    cp_src: coverpoint req.src {
      bins ports[] = {[0:15]}; 
    }

    cp_dst: coverpoint req.addr {
      bins ports[] = {[0:15]};
    }

    cp_mode: coverpoint req.mode {
      bins row_first = {seq_item::ROW_FIRST};
      bins col_first = {seq_item::COL_FIRST};
    }

    cp_bcast: coverpoint req.broadcast {
      bins unicast = {0};
      bins bcast   = {1};
    }

    cp_delay: coverpoint req.cycles_between {
      bins back2back = {0};
      bins short_dly = {[1:5]};
      bins long_dly  = {[6:15]};
    }

    cp_hops: coverpoint m_hops {
      bins neighbor   = {1};
      bins short_path = {[2:3]};
      bins long_path  = {[4:8]}; 
    }

    cp_error: coverpoint req.msg_error {
      bins clean   = {seq_item::NO_ERROR};
      bins hdr_err = {seq_item::HDR_ERROR};
      bins pay_err = {seq_item::PAY_ERROR};
    }

    // CROSS COVERAGE (Recall the 'iff' fix from the previous step)
    cx_src_dst: cross cp_src, cp_dst iff (req.broadcast == 0);
    
    cx_stress_dst: cross cp_dst, cp_delay {
        bins stress_test = binsof(cp_delay.back2back);
    }

    cx_mode_hops: cross cp_mode, cp_hops;

  endgroup

  // ------------------------------------------------------------------------
  // CONSTRUCTOR
  // ------------------------------------------------------------------------
  function new(string name, uvm_component parent);
    super.new(name, parent);
    router_cg = new();
  endfunction

  // ------------------------------------------------------------------------
  // HELPER
  // ------------------------------------------------------------------------
  function void calculate_hops();
    int src_r, src_c, dst_r, dst_c;
    int dist_r, dist_c;

    // Use 'req' (now defined as a class member)
    src_r = req.src / COLUMS;
    src_c = req.src % COLUMS;
    
    if (req.broadcast) begin
        m_hops = 0; 
        return;
    end

    dst_r = req.addr / COLUMS;
    dst_c = req.addr % COLUMS;

    dist_r = (src_r > dst_r) ? (src_r - dst_r) : (dst_r - src_r);
    dist_c = (src_c > dst_c) ? (src_c - dst_c) : (dst_c - src_c);

    m_hops = dist_r + dist_c;
  endfunction

  // ------------------------------------------------------------------------
  // WRITE FUNCTION
  // ------------------------------------------------------------------------
  function void write(seq_item t);
    // Copy the incoming transaction 't' to the class member 'req'
    req = t;
    
    // Now calculate and sample
    calculate_hops();
    router_cg.sample();
  endfunction

endclass
