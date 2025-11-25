class router_subscriber extends uvm_subscriber #(seq_item);
  `uvm_component_utils(router_subscriber)

  // Parameters (Must match your Package/DUT)
  int ROWS = 4;
  int COLUMS = 4;

  // Helper variables for sampling
  int m_hops;
  int m_data_pat;

  // ------------------------------------------------------------------------
  // COVERGROUP DEFINITION
  // ------------------------------------------------------------------------
  covergroup router_cg;
    option.per_instance = 1;
    option.comment      = "Router Functional Coverage";

    // --- 1. Source & Destination (Topology) ---
    cp_src: coverpoint req.src {
      bins ports[] = {[0:15]}; // Ensure 0..15 are hit
    }

    cp_dst: coverpoint req.addr {
      bins ports[] = {[0:15]};
      // If broadcast is active, addr might be irrelevant, but we track it
    }

    // --- 2. Routing Mode (Algorithm) ---
    cp_mode: coverpoint req.mode {
      bins row_first = {seq_item::ROW_FIRST};
      bins col_first = {seq_item::COL_FIRST};
    }

    // --- 3. Broadcast (Special Features) ---
    cp_bcast: coverpoint req.broadcast {
      bins unicast = {0};
      bins bcast   = {1};
    }

    // --- 4. Timing / Stress (Inter-packet delay) ---
    // This helps infer FIFO stress (Back-to-back packets)
    cp_delay: coverpoint req.cycles_between {
      bins back2back = {0};       // Max Stress
      bins short_dly = {[1:5]};   // Normal
      bins long_dly  = {[6:15]};  // Idle gaps
    }

    // --- 5. Path Length (Calculated Variable) ---
    // Matches "PATH_LENGTH_CP" in your PDF
    cp_hops: coverpoint m_hops {
      bins neighbor   = {1};
      bins short_path = {[2:3]};
      bins long_path  = {[4:8]}; // Max hops in 4x4 is 6
    }

    // --- 6. Error Injection ---
    cp_error: coverpoint req.msg_error {
      bins clean   = {seq_item::NO_ERROR};
      bins hdr_err = {seq_item::HDR_ERROR};
      bins pay_err = {seq_item::PAY_ERROR};
    }

    // ----------------------------------------------------------------------
    // CROSS COVERAGE (The "Matrix")
    // ----------------------------------------------------------------------

    // Matrix: Did every Source talk to every Destination? (256 combinations)
    cx_src_dst: cross cp_src, cp_dst {
        // Ignore Broadcasts in the unicast matrix to keep it clean
        ignore_bins bcast_traffic = binsof(cp_dst) intersect {[0:15]} with (req.broadcast == 1);
        // Optional: Ignore self-talk if DUT forbids it
        // ignore_bins loopback = binsof(cp_src) intersect {0} && binsof(cp_dst) intersect {0};
    }

    // Stress Map: Did we send back-to-back packets to every node?
    cx_stress_dst: cross cp_dst, cp_delay {
        // Focus only on the back2back bin
        bins stress_test = binsof(cp_delay.back2back);
    }

    // Algorithm Validation: Did both modes handle long paths?
    cx_mode_hops: cross cp_mode, cp_hops;

  endgroup

  // ------------------------------------------------------------------------
  // CONSTRUCTOR
  // ------------------------------------------------------------------------
  function new(string name, uvm_component parent);
    super.new(name, parent);
    router_cg = new(); // Instantiate the group
  endfunction

  // ------------------------------------------------------------------------
  // HELPER: Calculate Hops (Manhattan Distance)
  // ------------------------------------------------------------------------
  function void calculate_hops();
    int src_r, src_c, dst_r, dst_c;
    int dist_r, dist_c;

    // Map Port ID to (Row, Col)
    src_r = req.src / COLUMS;
    src_c = req.src % COLUMS;
    
    // If Broadcast, hops is undefined (or max), handle accordingly
    if (req.broadcast) begin
        m_hops = 0; 
        return;
    end

    dst_r = req.addr / COLUMS;
    dst_c = req.addr % COLUMS;

    // Absolute differences
    dist_r = (src_r > dst_r) ? (src_r - dst_r) : (dst_r - src_r);
    dist_c = (src_c > dst_c) ? (src_c - dst_c) : (dst_c - src_c);

    m_hops = dist_r + dist_c;
  endfunction

  // ------------------------------------------------------------------------
  // WRITE FUNCTION (Triggered by Monitor)
  // ------------------------------------------------------------------------
  function void write(seq_item t);
    req = t;
    
    // Pre-calculate derived values before sampling
    calculate_hops();

    // Sample Coverage
    router_cg.sample();
  endfunction

endclass
