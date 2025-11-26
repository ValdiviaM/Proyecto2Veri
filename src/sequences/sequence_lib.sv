// 1. BROADCAST SEQUENCE: Forces Broadcast packets
class broadcast_seq extends router_sequence;
  `uvm_object_utils(broadcast_seq)

  function new(string name="broadcast_seq");
    super.new(name);
    // Uses the knobs defined in your 'router_sequence'
    num_trans       = 30;
    force_broadcast = 1; 
  endfunction
endclass

// 2. FULL MESH SEQUENCE: Hits every Source -> Dest pair
class full_mesh_seq extends router_sequence;
  `uvm_object_utils(full_mesh_seq)

  function new(string name="full_mesh_seq");
    super.new(name);
  endfunction

  // We override the body to force specific loops instead of random
  virtual task body();
    `uvm_info("SEQ", "Starting Full Mesh Exhaustive Sequence...", UVM_LOW)

    // Loop through all Sources (0 to 15)
    for (int s = 0; s < 16; s++) begin
        // Loop through all Destinations (0 to 15)
        for (int d = 0; d < 16; d++) begin
            if (s == d) continue; // Skip loopback

            // Create item
            req = seq_item::type_id::create("req");
            start_item(req);

            // Force specific Src and Dst
            if (!req.randomize() with {
                src == s;
                addr == d;
                broadcast == 0;
                msg_error == seq_item::NO_ERROR;
            }) `uvm_error("SEQ", "Randomization failed in full_mesh_seq");

            finish_item(req);
        end
    end
  endtask
endclass

// 3. ERROR INJECTION SEQUENCE
class error_seq extends router_sequence;
  `uvm_object_utils(error_seq)

  function new(string name="error_seq");
    super.new(name);
    num_trans    = 50;
    inject_error = 1; // Uses your knob
  endfunction
endclass
