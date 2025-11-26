 class broadcast_seq extends router_sequence; `uvm_object_utils(broadcast_seq) 

function new(string name="broadcast_seq"); super.new(name); 
num_trans = 20; 
force_broadcast = 1; 
endfunction // No requiere body(), usa el de router_sequence que ya corregimos con ID injection. 
endclass 

// 2. FULL MESH SEQUENCE 
class full_mesh_seq extends router_sequence; `uvm_object_utils(full_mesh_seq) 

function new(string name="full_mesh_seq"); super.new(name); endfunction 

virtual task body(); int pkt_id_cnt = 0; // Contador 
`uvm_info("SEQ", "Starting Full Mesh Exhaustive Sequence...", UVM_LOW) 

for (int s = 0; s < 16; s++) begin 
   for (int d = 0; d < 16; d++) begin 
       if (s == d) continue;  
 
       req = seq_item::type_id::create("req"); 
       start_item(req); 
       assert(req.randomize() with { 
           src == s; 
           addr == d; 
           broadcast == 0; 
           msg_error == seq_item::NO_ERROR; 
       }); 
        
       // FIX: INYECTAR ID UNICO 
       req.set_payload_id_for_scb(pkt_id_cnt++); 
 
       finish_item(req); 
   end 
end 
 

endtask 
endclass 

// 3. HOTSPOT SEQUENCE 
class hotspot_seq extends router_sequence; `uvm_object_utils(hotspot_seq) 

function new(string name="hotspot_seq"); super.new(name); endfunction 

virtual task body(); int target_dst = 5; `uvm_info("SEQ", "Starting Hotspot Sequence (Contention)...", UVM_LOW) 

for (int i = 0; i < 40; i++) begin 
 req = seq_item::type_id::create("req"); 
 start_item(req); 
 assert(req.randomize() with { 
     addr == target_dst; 
     src  != target_dst; 
     broadcast == 0; 
 }); 
  
 // FIX: INYECTAR ID UNICO 
 req.set_payload_id_for_scb(i); 
 
 finish_item(req); 
end 
 

endtask 
endclass 

// 4. DIAGONAL SEQUENCE 
class diagonal_seq extends router_sequence; `uvm_object_utils(diagonal_seq) function new(string name="diagonal_seq"); super.new(name); endfunction 

virtual task body(); int corners[] = {0, 3, 12, 15}; for (int i = 0; i < 30; i++) begin req = seq_item::type_id::create("req"); start_item(req); assert(req.randomize() with { src inside {corners}; addr inside {corners}; src != addr; broadcast == 0; }); 

// FIX: INYECTAR ID UNICO 
 req.set_payload_id_for_scb(i); 
 
 finish_item(req); 
end 
 

endtask 
endclass 
