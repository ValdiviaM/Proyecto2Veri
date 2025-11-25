// ----------------------------------------------------------------------
// ARCHIVO: testbench.sv
// DESCRIPCIÓN: UVM Testbench completo para Mesh Router
// ----------------------------------------------------------------------

`timescale 1ns/1ps
`include "uvm_macros.svh"
import uvm_pkg::*;


// Declaración global de puertos de análisis diferenciados para el Scoreboard
// Deben estar fuera del package para que las macros funcionen globalmente.
`uvm_analysis_imp_decl(_in)
`uvm_analysis_imp_decl(_out)

// ----------------------------------------------------------------------
// INTERFACE
// ----------------------------------------------------------------------
interface mesh_gen_if #(parameter ROWS = 4, parameter COLUMS = 4, parameter pckg_sz = 32) (input logic clk);
    bit reset;

    // ---- Señales que el DUT va a conducir (DUT -> TB) ----
    // Las dejamos como wire porque el DUT las conduce.
    wire pndng [ROWS*2+COLUMS*2];
    wire [pckg_sz-1:0] data_out [ROWS*2+COLUMS*2];
    wire popin [ROWS*2+COLUMS*2];

    // ---- Señales que el TB/driver debe conducir hacia el DUT (TB -> DUT) ----
    // Creamos "driver" interna (logic) y luego asignamos esas lógicas a los wires que ve el DUT.
    logic drv_pop [ROWS*2+COLUMS*2];
    logic [pckg_sz-1:0] drv_data_out_i_in [ROWS*2+COLUMS*2];
    logic drv_pndng_i_in [ROWS*2+COLUMS*2];

    // Nets que conectan al DUT (estas son las mismas names que usabas)
    // Las exponemos como wires para que el DUT las vea como nets.
    wire pop [ROWS*2+COLUMS*2];
    wire [pckg_sz-1:0] data_out_i_in [ROWS*2+COLUMS*2];
    wire pndng_i_in [ROWS*2+COLUMS*2];

    // Continuous assigns: puente entre las señales procedurales y los wires DUT
    genvar gi;
    generate
      for (gi = 0; gi < (ROWS*2+COLUMS*2); gi++) begin : drv_bridge
        assign pop[gi] = drv_pop[gi];
        assign data_out_i_in[gi] = drv_data_out_i_in[gi];
        assign pndng_i_in[gi] = drv_pndng_i_in[gi];
      end
    endgenerate

    // --- Clocking (lo dejamos vacío porque tu simulador no soporta arrays allí) ---
    // No usar para sample/drive arrays en este entorno.

    // --- Modports: exponer lo que necesita cada rol ---
    modport TB (
        input clk, reset,
        output drv_pop, drv_data_out_i_in, drv_pndng_i_in,
        input  popin, data_out, pndng
    );

    modport MON (
        input clk, reset,
        input popin, data_out, pndng,
        input pop, data_out_i_in, pndng_i_in
    );

    modport DUT (
        input clk, reset,
        input pop, data_out_i_in, pndng_i_in,
        output popin, data_out, pndng
    );

    // -----------------------------------------------------------------------
    // CONSUMIDOR DUMMY (CRÍTICO)
    // Lo dejamos igual pero ahora escribe en drv_* si querés forzar ACK desde TB.
    // -----------------------------------------------------------------------
// En mesh_gen_if
        always @(posedge clk) begin
            if (reset) begin
                // Solo reseteamos el consumidor dummy
                for(int k=0; k < (ROWS*2+COLUMS*2); k++) drv_pop[k] <= 0;
            end else begin
                for(int k=0; k < (ROWS*2+COLUMS*2); k++) begin
                    drv_pop[k] <= pndng[k]; // Loopback / Ack automático
                end
            end
        end

endinterface


// ----------------------------------------------------------------------
// PACKAGE: ROUTER_PKG
// Contiene todas las clases UVM
// ----------------------------------------------------------------------

    // Parámetros globales del Testbench (Deben coincidir con el Top)
    parameter ROWS = 4;
    parameter COLUMS = 4;
    parameter ADDR_WIDTH = 32; 
    parameter DATA_WIDTH = 40;
    parameter MAX_N_CYCLES = 16;
    parameter NUM_PORTS = (ROWS*2) + (COLUMS*2);

    // ----------------------------------------------------------------
    // SEQUENCE ITEM        `uvm_object_utils_begin(seq_item)
    // ----------------------------------------------------------------
    class seq_item extends uvm_sequence_item;
    
        // ... (enums y variables rand siguen igual) ...
        typedef enum logic [0:0] { ROW_FIRST = 1'b1, COL_FIRST = 1'b0 } route_mode_e;
        typedef enum logic { NO_ERROR = 1'b0, HAS_ERR  = 1'b1 } error_type_e;
            
        rand bit [ADDR_WIDTH-1:0] addr; 
        rand bit [DATA_WIDTH-1:0] data;
        rand bit [$clog2(MAX_N_CYCLES)-1:0] cycles_between;
        rand route_mode_e mode;
        rand error_type_e msg_error;
        rand bit broadcast;
        bit [DATA_WIDTH-1:0] out_dut; 
    
        `uvm_object_utils_begin(seq_item)
            `uvm_field_int(addr,          UVM_ALL_ON)
            `uvm_field_int(data,          UVM_ALL_ON)
            `uvm_field_int(cycles_between,UVM_ALL_ON)
            `uvm_field_enum(route_mode_e, mode, UVM_ALL_ON)
            `uvm_field_enum(error_type_e, msg_error, UVM_ALL_ON)
            `uvm_field_int(broadcast,     UVM_ALL_ON)
        `uvm_object_utils_end
    
        // Constraints básicos
        constraint gap_c { cycles_between < MAX_N_CYCLES; }
        constraint broadcast_c { broadcast dist { 1'b0 := 9, 1'b1 := 1}; }
        constraint error_c { msg_error dist { NO_ERROR := 9, HAS_ERR := 1 }; }
        
        // -----------------------------------------------------------
        // CONSTRAINT 1: PUERTO DE ORIGEN VÁLIDO (Genérico)
        // -----------------------------------------------------------
        constraint valid_source_port_c { 
            addr inside {[0 : (ROWS*2 + COLUMS*2) - 1]}; 
        }

        // -----------------------------------------------------------
        // CONSTRAINT 2: HEADER DE DESTINO VÁLIDO (Genérico)
        // -----------------------------------------------------------
        // IMPORTANTE: Verifique con el diseñador del DUT si estas posiciones son correctas.
        // Si DATA_WIDTH=32:
        // (32 - 9) -: 4  => Bits [23:20] para la Fila (Row)
        // (32 - 13) -: 4 => Bits [19:16] para la Columna (Col)
        constraint valid_packet_header_c {  
            // Para que el paquete SALGA del DUT, debe dirigirse a una coordenada
            // fuera del rango [1..ROWS, 1..COLUMS].
            // Las coordenadas de "Salida" son: 
            // Fila 0 (Norte), Fila ROWS+1 (Sur), Col 0 (Oeste), Col COLUMS+1 (Este).

            data[(DATA_WIDTH - 9) -: 4] inside {0, [1:ROWS], ROWS+1};     // Row bits
            data[(DATA_WIDTH - 13) -: 4] inside {0, [1:COLUMS], COLUMS+1}; // Col bits

            // REGLA DE ORO: O la fila es externa, O la columna es externa.
            // Si ambas son internas, el paquete se queda atrapado dentro.
            (
                (data[(DATA_WIDTH - 9) -: 4] == 0) || 
                (data[(DATA_WIDTH - 9) -: 4] == ROWS+1) ||
                (data[(DATA_WIDTH - 13) -: 4] == 0) || 
                (data[(DATA_WIDTH - 13) -: 4] == COLUMS+1)
            );
        }

        // -----------------------------------------------------------
        // CONSTRAINT 3: NO LOOPBACK (Nuevo)
        // -----------------------------------------------------------
        // Ayuda a ver salidas. Si origen == destino, el DUT podría no sacar el paquete.
        // Como es difícil calcular XY desde Addr en constraints puros,
        // simplemente forzamos a que el destino NO sea igual a la "dirección" inyectada
        // asumiendo que el ID del paquete tiene alguna correlación, o confiamos en la suerte.
        
        // Una forma simple de ayudar a la aleatorización es evitar que row y col sean idénticos
        // si el puerto de entrada sugiere que estamos en esa diagonal, etc.
        // Por ahora, dejemos que la aleatoriedad fluya, pero si quiere ser estricto:
        
        /* 
        constraint no_dumb_routing_c {
           // Ejemplo: Evitar enviar a coordenadas (0,0) o cosas raras si su malla es 1-based
           data[(DATA_WIDTH - 9) -: 4] != 0;
           data[(DATA_WIDTH - 13) -: 4] != 0;
        }
        */

        function new (string name = "seq_item");
            super.new(name);
        endfunction
    endclass

    // ----------------------------------------------------------------
    // SEQUENCE
    // ----------------------------------------------------------------
    class router_sequence extends uvm_sequence #(seq_item);
        `uvm_object_utils(router_sequence)
    
        function new(string name="sequence");
            super.new(name);
        endfunction
    
        rand int n_items;
        constraint n_items_c { n_items inside {[50:100]}; } // Pocos items para dummy run
    
        virtual task body();
            for (int i = 0; i<n_items; i++) begin
                seq_item i_item = seq_item::type_id::create("i_item");
                start_item(i_item);
                if(!i_item.randomize()) `uvm_error("SEQ", "Randomization failed");
                finish_item(i_item);
                
                if ((i % 10) == 0)
                    `uvm_info("SEQ", $sformatf("Generated item %0d/%0d", i, n_items), UVM_LOW)
            end
            `uvm_info("SEQ", "Generation Done", UVM_LOW)
        endtask
    endclass

    // ----------------------------------------------------------------
    // SEQUENCER
    // ----------------------------------------------------------------
    class router_sequencer extends uvm_sequencer #(seq_item);
        `uvm_component_utils(router_sequencer)
        function new(string name = "router_sequencer", uvm_component parent=null);
            super.new(name, parent);
        endfunction
    endclass

    // ----------------------------------------------------------------
    // DRIVER
    // ----------------------------------------------------------------
    class router_driver extends uvm_driver #(seq_item);
    `uvm_component_utils(router_driver)

    virtual mesh_gen_if #(ROWS, COLUMS, DATA_WIDTH) vif;
    seq_item req;

    function new(string name = "router_driver", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        if (!uvm_config_db#(virtual mesh_gen_if #(ROWS, COLUMS, DATA_WIDTH))::get(this, "", "vif", vif))
        `uvm_fatal("DRV", "Cannot get virtual interface")
        else
        `uvm_info("DRV", $sformatf("Driver got VIF: %p", vif), UVM_LOW);
    endfunction

    task run_phase(uvm_phase phase);
        // 1. INICIALIZACIÓN COMPLETA (CRÍTICO)
        // Antes de hacer nada, ponemos TODOS los puertos en 0 para quitar las X
        // que están matando al DUT.
        for (int i = 0; i < (ROWS*2+COLUMS*2); i++) begin
            vif.drv_pndng_i_in[i] <= 1'b0;
            vif.drv_data_out_i_in[i] <= '0;
        end

        // 2. Esperar al Reset del Top
        // Esperamos que la señal de reset física baje
        wait (vif.reset === 1'b0);
        
        // Un ciclo extra de seguridad para sincronizar
        @(posedge vif.clk);

        // 3. Bucle principal
        forever begin
            seq_item_port.get_next_item(req);
            drive(req);
            seq_item_port.item_done();
        end
    endtask

    task drive(seq_item t);
            // 1. USAR EL PUERTO ALEATORIZADO DEL ITEM
            int unsigned port = t.addr; 
            
            // Protección por si el randomizador falló (opcional pero recomendada)
            if (port >= (ROWS*2 + COLUMS*2)) begin
                `uvm_error("DRV", $sformatf("Port %0d out of bounds! Dropping item.", port))
                return;
            end

            @(posedge vif.clk);

            // 2. DRIVE (Non-blocking)
            vif.drv_data_out_i_in[port] <= t.data;
            vif.drv_pndng_i_in[port]    <= 1'b1;
            
            `uvm_info("DRV", $sformatf("Driving Port %0d Data %h (Waiting ACK...)", port, t.data), UVM_HIGH);

            // 3. ESPERA DE ACK CON TIMEOUT (Watchdog)
            // Usamos fork/join_any para esperar lo que ocurra primero: el ACK o el Timeout
            fork
                begin : wait_for_ack
                    do begin
                        @(posedge vif.clk);
                    end while (vif.popin[port] === 1'b0);
                    `uvm_info("DRV", "ACK received!", UVM_HIGH)
                end

                begin : watchdog_timer
                    repeat(100) @(posedge vif.clk); // Esperar 100 ciclos máx
                    `uvm_error("DRV", $sformatf("Timeout waiting for popin (ACK) on port %0d. DUT ignored packet %h", port, t.data))
                end
            join_any
            disable fork; // Matar el proceso que no terminó (ej. si llegó ACK, matar el timer)

            // 4. BAJAR VALID
            vif.drv_pndng_i_in[port] <= 1'b0;

            // 5. DELAY INTER-PAQUETE
            repeat (t.cycles_between) @(posedge vif.clk);
        endtask

    endclass


    // ----------------------------------------------------------------
    // MONITOR
    // ----------------------------------------------------------------
    class router_monitor extends uvm_monitor;
        `uvm_component_utils(router_monitor)
    
        uvm_analysis_port #(seq_item) ap_in;
        uvm_analysis_port #(seq_item) ap_out;
    
        virtual mesh_gen_if #(ROWS, COLUMS, DATA_WIDTH).MON vif;
    
        function new(string name="monitor", uvm_component parent=null);
            super.new(name, parent);
        endfunction
    
        virtual function void build_phase(uvm_phase phase);
            super.build_phase(phase);
            if (!uvm_config_db#(virtual mesh_gen_if #(ROWS, COLUMS, DATA_WIDTH).MON)::get(this, "", "vif", vif))
                `uvm_fatal("MON", "Could not get vif")
            ap_in  = new("ap_in", this);
            ap_out = new("ap_out", this);
        endfunction
    
        virtual task run_phase(uvm_phase phase);
        forever begin
            @(posedge vif.clk);
            if (!vif.reset) begin
                for (int i = 0; i < NUM_PORTS; i++) begin
                    
                    // ---------------------------------------------------------
                    // CORRECCIÓN 1: Monitor de Entrada (Driver -> DUT)
                    // Valid: pndng_i_in | Ack: popin (Señal que viene del DUT indicando que aceptó)
                    // ---------------------------------------------------------
                    if (vif.pndng_i_in[i] === 1'b1 && vif.popin[i] === 1'b1) begin
                        seq_item item_in = seq_item::type_id::create("item_in");
                        item_in.data = vif.data_out_i_in[i];
                        item_in.addr = i; 
                        ap_in.write(item_in);
                    end

                    // ---------------------------------------------------------
                    // CORRECCIÓN 2: Monitor de Salida (DUT -> TB)
                    // Valid: pndng | Ack: pop (Señal que viene del TB indicando que leyó)
                    // ---------------------------------------------------------
                    if (vif.pndng[i] === 1'b1 && vif.pop[i] === 1'b1) begin
                        seq_item item_out = seq_item::type_id::create("item_out");
                        item_out.data = vif.data_out[i];
                        item_out.addr = i;
                        ap_out.write(item_out);
                    end
                end
            end
        end
        endtask 
    endclass

    // ----------------------------------------------------------------
    // SCOREBOARD
    // ----------------------------------------------------------------
class scoreboard extends uvm_component;
    `uvm_component_utils(scoreboard)

    // Puertos de análisis (Entrada desde Driver, Salida desde DUT)
    uvm_analysis_imp_in#(seq_item, scoreboard) m_analysis_imp_in;
    uvm_analysis_imp_out#(seq_item, scoreboard) m_analysis_imp_out;

    // Estructura para almacenar datos del paquete cuando entra al sistema
    typedef struct {
        real time_in;
        int src_port;
        bit [DATA_WIDTH-1:0] raw_data;
    } pkt_stats_t;

    // Base de datos de paquetes en tránsito (Key = Packet ID)
    pkt_stats_t packet_db [int];

    // Manejo de Archivos
    int fd_csv;
    string filename_csv = "metrics_report.csv";
    string filename_dat = "simulation_summary.dat"; // Datos para Gnuplot

    // --- Variables para Estadísticas por Terminal ---
    // Key: ID de la terminal de destino
    real total_delay_per_term [int];
    real min_delay_per_term   [int];
    real max_delay_per_term   [int];
    int  pkt_count_per_term   [int];
    real total_bits_per_term  [int]; 

    // Tiempos globales de simulación para cálculo de ancho de banda
    real simulation_start_time;
    real simulation_end_time;

    // Constructor
    function new(string name="scoreboard", uvm_component parent=null);
        super.new(name, parent);
        simulation_start_time = 0; 
    endfunction 

    // Build Phase: Inicialización
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);     
        m_analysis_imp_in  = new("m_analysis_imp_in", this);
        m_analysis_imp_out = new("m_analysis_imp_out", this);
        
        // Abrir CSV y escribir encabezados
        fd_csv = $fopen(filename_csv, "w");
        if (fd_csv) begin
            $fwrite(fd_csv, "Send_Time_ns,Source_Term,Dest_Term,Recv_Time_ns,Delay_ns,Packet_ID\n");
        end else begin
            `uvm_error("SCB", "No se pudo abrir el archivo CSV para escritura")
        end
    endfunction

    // ----------------------------------------------------------------------
    // Función Crítica: Extractor de Packet ID
    // Basado en la estructura del DUT para un bus de 40 bits.
    // El ID está en data[33:26] relativo al header, que mapea a [14:7] absolutos.
    // ----------------------------------------------------------------------
    function int get_packet_id(bit [DATA_WIDTH-1:0] data);
        // DATA_WIDTH debe ser 40. 
        // (40 - 26) = 14. Bajamos 8 bits -> Rango [14:7]
        return data[(DATA_WIDTH - 26) -: 8]; 
    endfunction

    // ----------------------------------------------------------------------
    // WRITE_IN: Se llama cuando el Monitor de Entrada detecta un paquete (Driver -> DUT)
    // ----------------------------------------------------------------------
    virtual function void write_in(seq_item item);
        int pid = get_packet_id(item.data);
        pkt_stats_t info;
        
        // Capturar tiempo de inicio real
        if (simulation_start_time == 0) simulation_start_time = $realtime;

        info.time_in  = $realtime;
        info.src_port = item.addr; // Puerto por donde entró
        info.raw_data = item.data;
        
        if (packet_db.exists(pid)) begin
            `uvm_warning("SCB", $sformatf("Packet ID collision or reuse detected: %0d. Overwriting.", pid))
        end
        
        // Guardar en la base de datos
        packet_db[pid] = info;
    endfunction

    // ----------------------------------------------------------------------
    // WRITE_OUT: Se llama cuando el Monitor de Salida detecta un paquete (DUT -> TB)
    // ----------------------------------------------------------------------
    virtual function void write_out(seq_item item);
        int pid = get_packet_id(item.data);
        pkt_stats_t exp_info;
        real current_delay;
        int dst;

        // Verificar si el paquete que salió fue registrado a la entrada
        if (!packet_db.exists(pid)) begin
            `uvm_warning("SCB", $sformatf("Unexpected output packet ID: %0d (Spurious or leftover)", pid))
            return;
        end

        // Recuperar información original
        exp_info = packet_db[pid];
        
        // --- Cálculos ---
        current_delay = $realtime - exp_info.time_in;
        dst = item.addr; // Terminal donde apareció el paquete (Destino Real)

        // --- Escribir fila en CSV (Requerimiento C) ---
        if (fd_csv) begin
            $fwrite(fd_csv, "%0.2f,%0d,%0d,%0.2f,%0.2f,%0d\n", 
                    exp_info.time_in,   // Send Time
                    exp_info.src_port,  // Source
                    dst,                // Dest
                    $realtime,          // Recv Time
                    current_delay,      // Delay
                    pid);               // Packet ID
        end

        // --- Acumular Estadísticas para Reporte Final (Requerimientos A y B) ---
        if (!pkt_count_per_term.exists(dst)) begin
            // Inicializar si es la primera vez que esta terminal recibe algo
            pkt_count_per_term[dst]   = 0;
            total_delay_per_term[dst] = 0;
            total_bits_per_term[dst]  = 0;
            min_delay_per_term[dst]   = current_delay;
            max_delay_per_term[dst]   = current_delay;
        end

        pkt_count_per_term[dst]++;
        total_delay_per_term[dst] += current_delay;
        total_bits_per_term[dst]  += DATA_WIDTH; // Sumar bits recibidos (40 bits)

        // Actualizar Min/Max Delay
        if (current_delay < min_delay_per_term[dst]) min_delay_per_term[dst] = current_delay;
        if (current_delay > max_delay_per_term[dst]) max_delay_per_term[dst] = current_delay;

        // Limpiar base de datos y actualizar tiempo final
        packet_db.delete(pid);
        simulation_end_time = $realtime;
    endfunction

    // ----------------------------------------------------------------------
    // REPORT_PHASE: Generación de resumen, cálculos finales y archivos Gnuplot
    // ----------------------------------------------------------------------
    virtual function void report_phase (uvm_phase phase);
        int fd_dat;
        real avg_delay;
        real bandwidth_gbps; 
        real total_sim_time;
        
        // Variables para encontrar Max/Min del sistema global
        real max_sys_bw = 0;
        real min_sys_bw = 99999999.0;
        int  term_max_bw = -1;
        int  term_min_bw = -1;

        // Cerrar CSV
        if (fd_csv) $fclose(fd_csv);

        // Calcular tiempo total efectivo de transmisión
        total_sim_time = simulation_end_time - simulation_start_time;
        if (total_sim_time <= 0) total_sim_time = 1.0; // Evitar división por cero

        `uvm_info("SCB", "===================================================", UVM_NONE)
        `uvm_info("SCB", "             FINAL METRICS REPORT                  ", UVM_NONE)
        `uvm_info("SCB", "===================================================", UVM_NONE)

        // Abrir archivo de datos para Gnuplot (.dat)
        fd_dat = $fopen(filename_dat, "w");
        $fwrite(fd_dat, "# TermID  AvgDelay(ns)  AvgBW(Gbps)  PacketCount\n");

        // Iterar sobre cada terminal que recibió paquetes
        foreach (pkt_count_per_term[i]) begin
            // (A) Promedio de Retraso
            avg_delay = total_delay_per_term[i] / pkt_count_per_term[i];

            // (B) Ancho de Banda Promedio
            // Formula: (Total Bits / Tiempo Total ns) = Gigabits/sec
            bandwidth_gbps = total_bits_per_term[i] / total_sim_time; 

            // Actualizar Max/Min Global
            if (bandwidth_gbps > max_sys_bw) begin
                max_sys_bw = bandwidth_gbps;
                term_max_bw = i;
            end
            if (bandwidth_gbps < min_sys_bw) begin
                min_sys_bw = bandwidth_gbps;
                term_min_bw = i;
            end

            // Imprimir Log en consola
            `uvm_info("SCB", $sformatf("Term [%02d] -> Pkts: %0d | Avg Delay: %0.2fns | Avg BW: %0.4f Gbps | Range: [%0.2f - %0.2f]ns", 
                                       i, pkt_count_per_term[i], avg_delay, bandwidth_gbps, min_delay_per_term[i], max_delay_per_term[i]), UVM_NONE)

            // Escribir en archivo para Gnuplot
            $fwrite(fd_dat, "%0d  %0.2f  %0.4f  %0d\n", i, avg_delay, bandwidth_gbps, pkt_count_per_term[i]);
        end
        $fclose(fd_dat);

        `uvm_info("SCB", "---------------------------------------------------", UVM_NONE)
        `uvm_info("SCB", $sformatf("System Max Avg BW: Terminal %0d (%0.4f Gbps)", term_max_bw, max_sys_bw), UVM_NONE)
        `uvm_info("SCB", $sformatf("System Min Avg BW: Terminal %0d (%0.4f Gbps)", term_min_bw, min_sys_bw), UVM_NONE)
        `uvm_info("SCB", "===================================================", UVM_NONE)
        
        // (D) Generar scripts de GNUplot
        generate_gnuplot_scripts();
    endfunction

    // ----------------------------------------------------------------------
    // Función Auxiliar: Crear scripts .gp para graficar
    // ----------------------------------------------------------------------
    function void generate_gnuplot_scripts();
        int fd_gp;

        // --- 1. Script para Retraso (Delay) ---
        fd_gp = $fopen("plot_delay.gp", "w");
        $fwrite(fd_gp, "set title 'Average Packet Delay per Terminal'\n");
        $fwrite(fd_gp, "set style data histograms\n");
        $fwrite(fd_gp, "set style fill solid 1.0 border -1\n");
        $fwrite(fd_gp, "set xlabel 'Terminal ID'\n");
        $fwrite(fd_gp, "set ylabel 'Delay (ns)'\n");
        $fwrite(fd_gp, "set grid\n");
        $fwrite(fd_gp, "set boxwidth 0.7\n");
        $fwrite(fd_gp, "set term png size 1024,768\n");
        $fwrite(fd_gp, "set output 'graph_delay.png'\n");
        // Columna 2 = AvgDelay, xtic(1) = Terminal ID
        $fwrite(fd_gp, "plot '%s' using 2:xtic(1) title 'Avg Delay (ns)' linecolor rgb '#3366cc'\n", filename_dat);
        $fclose(fd_gp);

        // --- 2. Script para Ancho de Banda (Bandwidth) ---
        fd_gp = $fopen("plot_bw.gp", "w");
        $fwrite(fd_gp, "set title 'Average Bandwidth per Terminal'\n");
        $fwrite(fd_gp, "set style data histograms\n");
        $fwrite(fd_gp, "set style fill solid 1.0 border -1\n");
        $fwrite(fd_gp, "set xlabel 'Terminal ID'\n");
        $fwrite(fd_gp, "set ylabel 'Bandwidth (Gbps)'\n");
        $fwrite(fd_gp, "set grid\n");
        $fwrite(fd_gp, "set boxwidth 0.7\n");
        $fwrite(fd_gp, "set term png size 1024,768\n");
        $fwrite(fd_gp, "set output 'graph_bandwidth.png'\n");
        // Columna 3 = AvgBW
        $fwrite(fd_gp, "plot '%s' using 3:xtic(1) title 'Avg BW (Gbps)' linecolor rgb '#cc3333'\n", filename_dat);
        $fclose(fd_gp);

        `uvm_info("SCB", "Gnuplot scripts generated: plot_delay.gp, plot_bw.gp", UVM_NONE)
    endfunction

endclass

    // ----------------------------------------------------------------
    // AGENT
    // ----------------------------------------------------------------
    class router_agent extends uvm_agent;
        `uvm_component_utils(router_agent)
        router_sequencer m_sequencer;
        router_driver    m_driver;
        router_monitor   m_monitor; 
        virtual mesh_gen_if #(ROWS, COLUMS, DATA_WIDTH) vif;
    
        function new(string name, uvm_component parent=null);
            super.new(name, parent);
        endfunction
    
        function void build_phase(uvm_phase phase);
            super.build_phase(phase);
            if (!uvm_config_db#(virtual mesh_gen_if #(ROWS, COLUMS, DATA_WIDTH))::get(this, "", "vif", vif))
                `uvm_fatal("AGT", "No vif found")
    
            m_sequencer = router_sequencer::type_id::create("m_sequencer", this);
            m_driver    = router_driver   ::type_id::create("m_driver",    this);
            m_monitor   = router_monitor  ::type_id::create("m_monitor",   this);
    
            uvm_config_db#(virtual mesh_gen_if #(ROWS, COLUMS, DATA_WIDTH))::set(this, "m_driver", "vif", vif);
            uvm_config_db#(virtual mesh_gen_if #(ROWS, COLUMS, DATA_WIDTH).MON)::set(this, "m_monitor", "vif", vif);
        endfunction
    
        function void connect_phase(uvm_phase phase);
            m_driver.seq_item_port.connect(m_sequencer.seq_item_export);
        endfunction
    endclass

    // ----------------------------------------------------------------
    // ENV
    // ----------------------------------------------------------------
    class router_env extends uvm_env;
        `uvm_component_utils(router_env)
        router_agent m_agent;
        scoreboard   m_sb;
    
        function new(string name, uvm_component parent);
            super.new(name, parent);
        endfunction
    
        function void build_phase(uvm_phase phase);
            super.build_phase(phase);
            m_agent = router_agent::type_id::create("m_agent", this);
            m_sb    = scoreboard::type_id::create("m_sb", this);
        endfunction
    
        function void connect_phase(uvm_phase phase);
            m_agent.m_monitor.ap_in.connect(m_sb.m_analysis_imp_in);
            m_agent.m_monitor.ap_out.connect(m_sb.m_analysis_imp_out);
        endfunction
    endclass

    // ----------------------------------------------------------------
    // TEST
    // ----------------------------------------------------------------
    class router_test extends uvm_test;
        `uvm_component_utils(router_test)
        router_env m_env;
    
        function new(string name = "router_test", uvm_component parent=null);
            super.new(name, parent);
        endfunction
    
        function void build_phase(uvm_phase phase);
            super.build_phase(phase);
            m_env = router_env::type_id::create("m_env", this);
        endfunction
    
        // En router_test
        task run_phase(uvm_phase phase);
            router_sequence seq;
            phase.raise_objection(this);
            
            seq = router_sequence::type_id::create("seq");
            
            if(!seq.randomize()) `uvm_fatal("TEST", "Falló la randomización de la secuencia")

            `uvm_info("TEST", "Starting Sequence...", UVM_LOW)
            seq.start(m_env.m_agent.m_sequencer);
            
            `uvm_info("TEST", "Sequence Done. Draining...", UVM_LOW)
            #2000; 
            phase.drop_objection(this);
        endtask
    endclass

// ----------------------------------------------------------------------
// MODULE TOP
// ----------------------------------------------------------------------
module tb_top;

    // Parámetros
    parameter ROWS = 4;
    parameter COLUMS = 4;
    parameter PCK_SZ = 40;

    bit clk;
    
    // Generación de Clock
    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end

    // Instancia de Interfaz
    mesh_gen_if #(ROWS, COLUMS, PCK_SZ) vif(clk);

    // DUT (Device Under Test)
    // Instancia tu módulo mesh_gnrtr aquí. 
    // Asegúrate de usar los mismos parámetros.
    mesh_gnrtr #(
        .ROWS(ROWS), 
        .COLUMS(COLUMS), 
        .pckg_sz(PCK_SZ), 
        .fifo_depth(4), 
        .bdcst({8{1'b1}})
    ) dut (
        .clk(clk),
        .reset(vif.reset),
        .pndng(vif.pndng),
        .data_out(vif.data_out),
        .popin(vif.popin),
        .pop(vif.pop),
        .data_out_i_in(vif.data_out_i_in),
        .pndng_i_in(vif.pndng_i_in)
    );

    initial begin
        // Registrar interfaz en UVM DB
        uvm_config_db#(virtual mesh_gen_if #(ROWS, COLUMS, PCK_SZ))::set(null, "*", "vif", vif);

        run_test("router_test");
    end

    // Configuración Inicial y Arranque de Test
    initial begin
        vif.reset = 1;
        #20 vif.reset = 0;
    end
        
    // Dump waves (Opcional para EDA Playground)
    initial begin
        $dumpfile("dump.vcd");
        $dumpvars(0, tb_top);
    end

endmodule