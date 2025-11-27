class router_sequence extends uvm_sequence #(seq_item); 

`uvm_object_utils(router_sequence) 

// --- KNOBS (Control variables set by the Test) --- 
int num_trans = 50; int src_terminal = -1; // -1 means Random 
int dst_terminal = -1; // -1 means Random 
bit route_mode = 1; // 1=ROW_FIRST, 0=COL_FIRST 
bit force_broadcast = 0; bit inject_error = 0; bit reset_mid_tx = 0; bit fifo_stress = 0; 

function new(string name="router_sequence"); super.new(name); endfunction 

virtual task body(); 

`uvm_info("SEQ", $sformatf("Starting sequence with %0d items. Knobs: Src=%0d Dst=%0d Err=%0b",  
                           num_trans, src_terminal, dst_terminal, inject_error), UVM_MEDIUM) 
 
for (int i = 0; i < num_trans; i++) begin 
 seq_item item = seq_item::type_id::create($sformatf("item_%0d", i)); 
 
 start_item(item); 
  
 // 1. Randomize basic fields 
 if (!item.randomize()) `uvm_error("SEQ", "Randomization failed"); 
 
 // 2. Apply KNOBS (Overrides) 
 if (dst_terminal != -1) item.addr = dst_terminal; 
 if (src_terminal != -1) item.src = src_terminal; 
 item.mode = (route_mode) ? seq_item::ROW_FIRST : seq_item::COL_FIRST; 
 if (force_broadcast) item.broadcast = 1; 
 
 if (inject_error) begin 
   if ($urandom_range(0,1)) 
       item.msg_error = seq_item::HDR_ERROR; 
   else 
       item.msg_error = seq_item::PAY_ERROR; 
 end else begin 
    item.msg_error = seq_item::NO_ERROR; 
 end 
 
 // 3. FIX: INYECTAR ID UNICO (Usando 'i') 
 item.set_payload_id_for_scb(i); 
 
 finish_item(item); 
 
 // Special Events based on loop count 
 if (reset_mid_tx && i == num_trans/2) 
   `uvm_info("SEQ", "Mid-transfer reset requested", UVM_HIGH) 
 
 if (fifo_stress && (i % 25 == 0)) 
   `uvm_info("SEQ", "FIFO stress event triggered", UVM_LOW) 
end 
 
`uvm_info("SEQ", "Sequence completed", UVM_MEDIUM) 
 

endtask 

endclass 
