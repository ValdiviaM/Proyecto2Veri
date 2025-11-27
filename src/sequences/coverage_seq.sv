// Secuencia de cobertura especializada, extiende router_sequence
// Diseñada para cubrir todos los caminos: unicast, broadcast y errores

class coverage_seq extends router_sequence; 
`uvm_object_utils(coverage_seq) 

function new(string name = "coverage_seq"); 
    super.new(name); 
endfunction 

virtual task body(); 
    seq_item req_item; 
    int pkt_id_cnt = 0; // Contador local para IDs únicos

// ------------------------------------------------------- 
// LOOP 1: Recorrer la matriz Source x Destination (Unicast)
// Genera un paquete para cada combinación de src!=dst
// ------------------------------------------------------- 
for (int s = 0; s < 16; s++) begin 
    for (int d = 0; d < 16; d++) begin 
        if (s == d) continue; // Evitar enviar a sí mismo

        req_item = seq_item::type_id::create("req_item"); 
        start_item(req_item); 
        
        // Randomizar campos básicos respetando restricciones
        assert(req_item.randomize() with { 
            src == s; 
            addr == d; 
            broadcast == 0; 
            msg_error == seq_item::NO_ERROR;  
            cycles_between inside {[10:20]}; 
        }); 
        
        // Inyectar ID único para scoreboard
        req_item.set_payload_id_for_scb(pkt_id_cnt++); 
        
        finish_item(req_item); 
    end 
end 

// ------------------------------------------------------- 
// LOOP 2: Generar paquetes Broadcast desde cada fuente
// ------------------------------------------------------- 
for (int s = 0; s < 16; s++) begin 
    req_item = seq_item::type_id::create("req_item"); 
    start_item(req_item); 
    assert(req_item.randomize() with { 
        src == s; 
        broadcast == 1; 
    }); 
    
    // Inyectar ID único para scoreboard
    req_item.set_payload_id_for_scb(pkt_id_cnt++); 
    
    finish_item(req_item); 
end 

// ------------------------------------------------------- 
// LOOP 3: Inyección de errores
// Crea 50 paquetes con error aleatorio (HDR o PAY)
// ------------------------------------------------------- 
repeat(50) begin 
    req_item = seq_item::type_id::create("req_item"); 
    start_item(req_item); 
    assert(req_item.randomize() with { 
        msg_error inside {seq_item::HDR_ERROR, seq_item::PAY_ERROR}; 
    }); 
    
    // Inyectar ID único para scoreboard
    req_item.set_payload_id_for_scb(pkt_id_cnt++); 
    
    finish_item(req_item); 
end 

endtask 
endclass
