// Sequence item para router_agent
// Define la transacción que circula entre sequencer, driver y monitor

class seq_item extends uvm_sequence_item;

    // 1. Enums
    typedef enum logic [0:0] { ROW_FIRST = 1'b1, COL_FIRST = 1'b0 } route_mode_e; // Modos de ruteo
    typedef enum logic [1:0] { NO_ERROR=2'b00, HDR_ERROR=2'b01, PAY_ERROR=2'b10 } error_type_e; // Tipos de error
        
    // 2. Campos aleatorizados
    rand bit [ADDR_WIDTH-1:0] src;           // Puerto origen
    rand bit [ADDR_WIDTH-1:0] addr;          // Puerto destino
    rand bit [DATA_WIDTH-1:0] data;          // Payload
    rand bit [$clog2(MAX_N_CYCLES)-1:0] cycles_between; // Ciclos entre envíos
    rand route_mode_e mode;                   // Modo de ruteo
    rand error_type_e msg_error;             // Tipo de error
    rand bit broadcast;                       // Flag broadcast
    rand bit [3:0] target_row;               // Row destino
    rand bit [3:0] target_col;               // Col destino

    // 3. Registro en la UVM Factory
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

    // Helper para inyectar ID en payload (para scoreboard)
    function void set_payload_id_for_scb(int id);
       data[14:7] = id[7:0];  
    endfunction

    // 5. Constraints

    // Tiempo entre transacciones (gap)
    constraint gap_c { cycles_between inside {[2:20]}; }

    // Puertos válidos
    constraint src_valid_c { src inside {[0 : 15]}; }
    constraint dst_valid_c { addr inside {[0 : 15]}; }

    // No enviar a sí mismo salvo broadcast
    constraint src_dst_diff_c { if (!broadcast) src != addr; }

    // Probabilidad de broadcast (10%)
    constraint broadcast_c { broadcast dist { 1'b0 := 9, 1'b1 := 1}; }

    // Distribución de errores
    constraint error_c { msg_error dist { NO_ERROR := 80, HDR_ERROR := 10, PAY_ERROR := 10 }; }

    // HEADER FORMATTING: mapping Row/Col y broadcast
    constraint header_valid_c {
        target_row==data[DATA_WIDTH-9:DATA_WIDTH-12];
        target_col==data[DATA_WIDTH-13:DATA_WIDTH-16];
        if (broadcast) {
            data[DATA_WIDTH-1 : DATA_WIDTH-8] == 8'hFF; // Top byte = broadcast ID
        } else {
            (target_row==0 || target_row==5 || target_col==0 || target_col==5); 
            target_row inside {[0:5]};
            target_col inside {[0:5]};
        }
    }

endclass
