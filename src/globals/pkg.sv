//------------------------------------------------------------------------------
// Package: router_pkg
//------------------------------------------------------------------------------
// Centraliza parámetros globales, macros, declaraciones e inclusiones necesarias
// para todo el ambiente de verificación UVM del router.
//------------------------------------------------------------------------------
package router_pkg;

  // Importación del paquete UVM y macros
  import uvm_pkg::*;
  `include "uvm_macros.svh"

  //--------------------------------------------------------------------------
  // 1. Parámetros globales usados en todo el ambiente
  //--------------------------------------------------------------------------
  parameter int ROWS          = 4;                   // Número de filas del router
  parameter int COLUMS        = 4;                   // Número de columnas del router
  parameter int PCKG_SZ       = 40;                  // Tamaño del paquete
  parameter int DATA_WIDTH    = PCKG_SZ;             // Ancho de datos
  parameter int ADDR_WIDTH    = 8;                   // Ancho de dirección
  parameter int MAX_N_CYCLES  = 16;                  // Ciclos máximos para timeout
  
  // Número total de puertos del router según su geometría
  parameter int NUM_PORTS     = (ROWS*2) + (COLUMS*2);

  //--------------------------------------------------------------------------
  // 2. Declaración de macros para análisis del scoreboard
  //    Se generan dos implementaciones: entrada y salida.
  //--------------------------------------------------------------------------
  `uvm_analysis_imp_decl(_in)
  `uvm_analysis_imp_decl(_out)

  //--------------------------------------------------------------------------
  // 3. Inclusión de archivos: sequence items, sequences, agente, scoreboard y tests
  //--------------------------------------------------------------------------
  // Sequence items
  `include "../sequence_items/seq_item.sv"

  // Sequences
  `include "../sequences/base_seq.sv"
  `include "../sequences/sequence_lib.sv"        // Biblioteca de secuencias

  // Componentes del agente del router
  `include "../router_agent/sequencer.sv"
  `include "../router_agent/driver.sv"
  `include "../router_agent/monitor.sv"
  `include "../router_agent/router_agent.sv"

  // Scoreboard y cobertura
  `include "../scoreboard/scoreboard.sv"
  `include "../scoreboard/router_subscriber.sv"

  // Environment
  `include "../env/router_env.sv"

  // Tests
  `include "../tests/base_test.sv"
  `include "../tests/RouteRowFirstTest.sv"
  `include "../tests/test_lib.sv"

endpackage : router_pkg
