// 1. BROADCAST SEQUENCE: Forces Broadcast packets
class broadcast_seq extends router_sequence;
  `uvm_object_utils(broadcast_seq)

  function new(string name="broadcast_seq");
    super.new(name);
    num_trans       = 20;
    force_broadcast = 1; 
  endfunction
endclass

// 2. FULL MESH SEQUENCE: Hits every Source -> Dest pair (100% Connectivity)
class full_mesh_seq extends router_sequence;
  `uvm_object_utils(full_mesh_seq)

  function new(string name="full_mesh_seq");
    super.new(name);
  endfunction

  virtual task body();
    `uvm_info("SEQ", "Starting Full Mesh Exhaustive Sequence...", UVM_LOW)
    // Loop through all Sources
    for (int s = 0; s < 16; s++) begin
        // Loop through all Destinations
        for (int d = 0; d < 16; d++) begin
            if (s == d) continue; // Skip loopback

            req = seq_item::type_id::create("req");
            start_item(req);
            // Force precise src/dst pair
            assert(req.randomize() with {
                src == s;
                addr == d;
                broadcast == 0;
                msg_error == seq_item::NO_ERROR;
            });
            finish_item(req);
        end
    end
  endtask
endclass

// 3. HOTSPOT SEQUENCE (Arbitration Stress)
// Sends packets from many sources to ONE destination to cause congestion
class hotspot_seq extends router_sequence;
  `uvm_object_utils(hotspot_seq)

  function new(string name="hotspot_seq");
    super.new(name);
  endfunction

  virtual task body();
    int target_dst = 5; // Create traffic jam at Port 5
    `uvm_info("SEQ", "Starting Hotspot Sequence (Contention)...", UVM_LOW)

    for (int i = 0; i < 40; i++) begin
      req = seq_item::type_id::create("req");
      start_item(req);
      assert(req.randomize() with {
          addr == target_dst;
          src  != target_dst;
          broadcast == 0;
      });
      finish_item(req);
    end
  endtask
endclass

// 4. DIAGONAL SEQUENCE (Long Paths / Corners)
class diagonal_seq extends router_sequence;
  `uvm_object_utils(diagonal_seq)
  function new(string name="diagonal_seq");
    super.new(name);
  endfunction

  virtual task body();
    int corners[] = {0, 3, 12, 15};
    for (int i = 0; i < 30; i++) begin
      req = seq_item::type_id::create("req");
      start_item(req);
      assert(req.randomize() with {
         src inside {corners};
         addr inside {corners};
         src != addr;
         broadcast == 0;
      });
      finish_item(req);
    end
  endtask
endclass
