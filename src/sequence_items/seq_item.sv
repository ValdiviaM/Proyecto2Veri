class seq_item extends uvm_sequence_item;

    // Use logic [0:0] to match your knobs
    typedef enum logic [0:0] { ROW_FIRST = 1'b1, COL_FIRST = 1'b0 } route_mode_e;
    
    // Updated Enums to match your sequence
    typedef enum logic [1:0] { 
        NO_ERROR  = 2'b00, 
        HDR_ERROR = 2'b01, 
        PAY_ERROR = 2'b10 
    } error_type_e;
        
    rand bit [ADDR_WIDTH-1:0] src;          // Source Port (Input Terminal)
    rand bit [ADDR_WIDTH-1:0] addr;         // Dest Address (Inside Packet)
    rand bit [DATA_WIDTH-1:0] data;         // Payload
    rand bit [$clog2(MAX_N_CYCLES)-1:0] cycles_between;
    rand route_mode_e mode;
    rand error_type_e msg_error;
    rand bit broadcast;

    `uvm_object_utils_begin(seq_item)
        `uvm_field_int(src,           UVM_ALL_ON)
        `uvm_field_int(addr,          UVM_ALL_ON)
        `uvm_field_int(data,          UVM_ALL_ON | UVM_HEX)
        `uvm_field_enum(error_type_e, msg_error, UVM_ALL_ON)
        `uvm_field_int(broadcast,     UVM_ALL_ON)
    `uvm_object_utils_end

    // Constraints
    constraint gap_c { cycles_between inside {[0:15]}; }
    
    constraint src_valid_c { src inside {[0 : (ROWS*2 + COLUMS*2) - 1]}; }
    constraint dst_valid_c { addr inside {[0 : (ROWS*2 + COLUMS*2) - 1]}; }
    
    // Don't send to yourself unless broadcasting
    constraint src_dst_diff_c { 
        if (!broadcast) src != addr; 
    }

    constraint broadcast_c { broadcast dist { 1'b0 := 9, 1'b1 := 1}; }
    
    // Error distribution (can be overridden by sequence knobs)
    constraint error_c { 
        msg_error dist { NO_ERROR := 80, HDR_ERROR := 10, PAY_ERROR := 10 }; 
    }

    // Packet Header Constraints 
    // (Ensure valid X/Y coords are in the payload based on 'addr')
    // Note: In a real TB, you would calculate data[header_bits] based on 'addr' in post_randomize
    
    function new (string name = "seq_item");
        super.new(name);
    endfunction

endclass
