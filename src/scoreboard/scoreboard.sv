// Scoreboard para router_agent
// Recibe transacciones desde los monitores, calcula métricas y genera reportes

class scoreboard extends uvm_component;
    `uvm_component_utils(scoreboard)

    // Analysis IMPs para conectar monitores
    uvm_analysis_imp_in #(seq_item, scoreboard) m_analysis_imp_in;
    uvm_analysis_imp_out #(seq_item, scoreboard) m_analysis_imp_out;

    // Estructura interna para registrar info de cada paquete
    typedef struct {
        real time_in;
        int src_port;
        bit [DATA_WIDTH-1:0] raw_data;
    } pkt_stats_t;

    pkt_stats_t packet_db [int]; // Base de datos de paquetes
    int fd_csv;                  // Descriptor CSV
    string filename_csv = "metrics_report.csv"; 
    string filename_dat = "simulation_summary.dat";

    // Estadísticas por terminal
    real total_delay_per_term [int];
    real min_delay_per_term   [int];
    real max_delay_per_term   [int];
    int  pkt_count_per_term   [int];
    real total_bits_per_term  [int]; 

    // Tiempos de simulación
    real simulation_start_time;
    real simulation_end_time;

    // Constructor
    function new(string name="scoreboard", uvm_component parent=null);
        super.new(name, parent);
        simulation_start_time = 0; 
    endfunction 

    // Build phase: crear IMPs y abrir archivo CSV
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);     
        m_analysis_imp_in  = new("m_analysis_imp_in", this);
        m_analysis_imp_out = new("m_analysis_imp_out", this);
        
        fd_csv = $fopen(filename_csv, "w");
        if (fd_csv) $fwrite(fd_csv, "Send_Time_ns,Source_Term,Dest_Term,Recv_Time_ns,Delay_ns,Packet_ID\n");
    endfunction

    // Extrae el packet ID del payload
    function int get_packet_id(bit [DATA_WIDTH-1:0] data);
        return data[(DATA_WIDTH - 26) -: 8]; 
    endfunction

    // Registrar paquete de entrada
    virtual function void write_in(seq_item item);
        int pid = get_packet_id(item.data);
        pkt_stats_t info;
        
        if (simulation_start_time == 0) simulation_start_time = $realtime;

        info.time_in  = $realtime;
        info.src_port = item.addr; 
        info.raw_data = item.data;
        
        packet_db[pid] = info;
    endfunction

    // Registrar paquete de salida y calcular métricas
    virtual function void write_out(seq_item item);
        int pid = get_packet_id(item.data);
        pkt_stats_t exp_info;
        real current_delay;
        int dst;
        bit is_broadcast;
        
        if (!packet_db.exists(pid)) begin
            `uvm_warning("SCB", $sformatf("Unexpected output packet ID: %0d", pid))
            return;
        end

        exp_info = packet_db[pid];
        current_delay = $realtime - exp_info.time_in;
        dst = item.addr; 
        is_broadcast = (exp_info.raw_data[DATA_WIDTH-1: DATA_WIDTH-8] == 8'hFF);

        if (fd_csv) $fwrite(fd_csv, "%0.2f,%0d,%0d,%0.2f,%0.2f,%0d\n", 
                             exp_info.time_in, exp_info.src_port, dst, $realtime, current_delay, pid);

        // Inicializar métricas si terminal nuevo
        if (!pkt_count_per_term.exists(dst)) begin
            pkt_count_per_term[dst]   = 0;
            total_delay_per_term[dst] = 0;
            total_bits_per_term[dst]  = 0;
            min_delay_per_term[dst]   = current_delay;
            max_delay_per_term[dst]   = current_delay;
        end

        pkt_count_per_term[dst]++;
        total_delay_per_term[dst] += current_delay;
        total_bits_per_term[dst]  += DATA_WIDTH; 
        if (current_delay < min_delay_per_term[dst]) min_delay_per_term[dst] = current_delay;
        if (current_delay > max_delay_per_term[dst]) max_delay_per_term[dst] = current_delay;

        if(!is_broadcast) packet_db.delete(pid); // Eliminar solo unicast
        simulation_end_time = $realtime;
    endfunction

    // Fase de reporte: calcular métricas finales y generar archivos de salida
    virtual function void report_phase (uvm_phase phase);
        int fd_dat;
        real avg_delay;
        real bandwidth_gbps; 
        real total_sim_time = simulation_end_time - simulation_start_time;
        if (total_sim_time <= 0) total_sim_time = 1.0; 

        if (fd_csv) $fclose(fd_csv);

        `uvm_info("SCB", "=== FINAL METRICS REPORT ===", UVM_NONE)

        fd_dat = $fopen(filename_dat, "w");
        $fwrite(fd_dat, "# TermID  AvgDelay(ns)  AvgBW(Gbps)  PacketCount\n");

        foreach (pkt_count_per_term[i]) begin
            avg_delay = total_delay_per_term[i] / pkt_count_per_term[i];
            bandwidth_gbps = total_bits_per_term[i] / total_sim_time; 
            `uvm_info("SCB", $sformatf("Term [%02d] -> Avg Delay: %0.2f ns | Avg BW: %0.4f Gbps", i, avg_delay, bandwidth_gbps), UVM_NONE)
            $fwrite(fd_dat, "%0d  %0.2f  %0.4f  %0d\n", i, avg_delay, bandwidth_gbps, pkt_count_per_term[i]);
        end
        $fclose(fd_dat);

        // Genera scripts de gnuplot
        generate_gnuplot_scripts();
    endfunction

    // Scripts para graficar delay y bandwidth
    function void generate_gnuplot_scripts();
        int fd_gp;
        fd_gp = $fopen("plot_delay.gp", "w");
        $fwrite(fd_gp, "set title 'Average Packet Delay per Terminal'\nset style data histograms\nset style fill solid 1.0 border -1\nset term png size 800,600\nset output 'graph_delay.png'\nplot '%s' using 2:xtic(1) title 'Avg Delay (ns)'\n", filename_dat);
        $fclose(fd_gp);
        
        fd_gp = $fopen("plot_bw.gp", "w");
        $fwrite(fd_gp, "set title 'Average Bandwidth per Terminal'\nset style data histograms\nset style fill solid 1.0 border -1\nset term png size 800,600\nset output 'graph_bandwidth.png'\nplot '%s' using 3:xtic(1) title 'Avg BW (Gbps)'\n", filename_dat);
        $fclose(fd_gp);
    endfunction

endclass
