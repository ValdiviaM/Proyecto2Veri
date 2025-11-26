class seq_item extends uvm_sequence_item; 

// 1. Enums 
typedef enum logic [0:0] { ROW_FIRST = 1'b1, COL_FIRST = 1'b0 } route_mode_e; 
 
typedef enum logic [1:0] {  
   NO_ERROR  = 2'b00,  
   HDR_ERROR = 2'b01,  
   PAY_ERROR = 2'b10  
} error_type_e; 
    
// 2. Randomized Fields 
rand bit [ADDR_WIDTH-1:0] src;          // Source Port (Input) 
rand bit [ADDR_WIDTH-1:0] addr;         // Dest Port (Logical) 
rand bit [DATA_WIDTH-1:0] data;         // Payload 
rand bit [$clog2(MAX_N_CYCLES)-1:0] cycles_between; 
rand route_mode_e mode; 
rand error_type_e msg_error; 
rand bit broadcast; 
 
// 3. UVM Factory Registration 
`uvm_object_utils_begin(seq_item) 
   `uvm_field_int(src,           UVM_ALL_ON) 
   `uvm_field_int(addr,          UVM_ALL_ON) 
   `uvm_field_int(data,          UVM_ALL_ON | UVM_HEX) 
   `uvm_field_enum(error_type_e, msg_error, UVM_ALL_ON) 
   `uvm_field_int(broadcast,     UVM_ALL_ON) 
`uvm_object_utils_end 
 
// 4. Constructor 
function new (string name = "seq_item"); 
   super.new(name); 
endfunction 
 
// ----------------------------------------------------------------------- 
// NUEVA FUNCION: Inyectar ID para Scoreboard 
// ----------------------------------------------------------------------- 
// Escribe un ID único en los bits data[14:7] que es donde su Scoreboard lee. 
function void set_payload_id_for_scb(int id); 
   data[14:7] = id[7:0];  
endfunction 
 
// 5. Constraints 
 
// Timing 
constraint gap_c { cycles_between inside {[0:15]}; } 
 
// Valid Ports (0 to 15) 
constraint src_valid_c { src inside {[0 : 15]}; } 
constraint dst_valid_c { addr inside {[0 : 15]}; } 
 
// Don't send to yourself unless broadcasting 
constraint src_dst_diff_c {  
   if (!broadcast) src != addr;  
} 
 
// Broadcast Probability (10%) 
constraint broadcast_c { broadcast dist { 1'b0 := 9, 1'b1 := 1}; } 
 
// Error distribution 
constraint error_c {  
   msg_error dist { NO_ERROR := 80, HDR_ERROR := 10, PAY_ERROR := 10 };  
} 
 
// ----------------------------------------------------------------------- 
// HEADER FORMATTING CONSTRAINT (CORREGIDO) 
// ----------------------------------------------------------------------- 
constraint header_valid_c { 
   if (broadcast) { 
       // Force Broadcast ID (FF) in the top byte 
       data[DATA_WIDTH-1 : DATA_WIDTH-8] == 8'hFF; 
   } else { 
       // CORRECCION: Cambiado de [1:4] a [0:3] para que coincida con lógica DUT base-0 
       data[DATA_WIDTH-9  : DATA_WIDTH-12] inside {[0:3]}; // Target Row 
       data[DATA_WIDTH-13 : DATA_WIDTH-16] inside {[0:3]}; // Target Col 
   } 
} 
 

endclass 
