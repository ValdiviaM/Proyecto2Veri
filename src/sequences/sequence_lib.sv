// ----------------------------
// 1. BROADCAST SEQUENCE
// Genera solo paquetes broadcast, usa body() heredado de router_sequence
// ----------------------------
class broadcast_seq extends router_sequence; 
    `uvm_object_utils(broadcast_seq) 

function new(string name="broadcast_seq"); 
    super.new(name); 
    num_trans = 20;       // Cantidad de paquetes a generar
    force_broadcast = 1;  // Obliga a que todos los paquetes sean broadcast
endfunction 
endclass 

// ----------------------------
// 2. FULL MESH SEQUENCE
// Exhaustive sequence: recorre todas las combinaciones source-destination
// Se repite 5 veces para cobertura amplia
// ----------------------------
class full_mesh_seq extends router_sequence;
    `uvm_object_utils(full_mesh_seq)

    function new(string name="full_mesh_seq");
        super.new(name);
    endfunction

    virtual task body();
        `uvm_info("SEQ", "Starting Full Mesh Exhaustive Sequence...", UVM_LOW)
        
        // Repetir la matriz 5 veces
        repeat(5) begin 
            for (int s = 0; s < 16; s++) begin 
                for (int d = 0; d < 16; d++) begin
                    if (s == d) continue; // Evitar envío a sí mismo

                    req = seq_item::type_id::create("req");
                    start_item(req);
                    assert(req.randomize() with {
                        src == s;
                        addr == d;
                        broadcast == 0;
                        msg_error == seq_item::NO_ERROR;
                    });
                    // Inyectar ID único para scoreboard
                    req.set_payload_id_for_scb(s*16 + d); 
                    finish_item(req);
                end
            end
        end
    endtask
endclass

// ----------------------------
// 3. HOTSPOT SEQUENCE
// Concentración de tráfico en un terminal específico para simular congestión
// ----------------------------
class hotspot_seq extends router_sequence; 
    `uvm_object_utils(hotspot_seq) 

function new(string name="hotspot_seq"); 
    super.new(name); 
endfunction 

virtual task body(); 
    int target_dst = 5; 
    `uvm_info("SEQ", "Starting Hotspot Sequence (Contention)...", UVM_LOW) 

    for (int i = 0; i < 40; i++) begin 
        req = seq_item::type_id::create("req"); 
        start_item(req); 
        assert(req.randomize() with { 
            addr == target_dst; 
            src  != target_dst; 
            broadcast == 0; 
        }); 
        
        // Inyectar ID único para scoreboard
        req.set_payload_id_for_scb(i); 
        finish_item(req); 
    end 
endtask 
endclass

// ----------------------------
// 4. DIAGONAL SEQUENCE
// Paquetes entre las esquinas del mesh para patrones diagonales
// ----------------------------
class diagonal_seq extends router_sequence; 
    `uvm_object_utils(diagonal_seq) 

function new(string name="diagonal_seq"); 
    super.new(name); 
endfunction 

virtual task body(); 
    int corners[] = {0, 3, 12, 15}; // Identificadores de las esquinas

    for (int i = 0; i < 30; i++) begin 
        req = seq_item::type_id::create("req"); 
        start_item(req); 
        assert(req.randomize() with { 
            src inside {corners}; 
            addr inside {corners}; 
            src != addr; 
            broadcast == 0; 
        }); 
        
        // Inyectar ID único para scoreboard
        req.set_payload_id_for_scb(i); 
        finish_item(req); 
    end 
endtask 
endclass
