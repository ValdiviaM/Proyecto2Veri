// seq_item.sv

class seq_item extends uvm_sequence_item;

  // Enumerations
  typedef enum logic [0:0] {
      ROW_FIRST = 1'b1,
      COL_FIRST = 1'b0
  } route_mode_e;

  typedef enum logic [1:0] {
      NO_ERROR   = 2'b00,
      HDR_ERROR  = 2'b01,
      PAY_ERROR  = 2'b10
  } error_type_e;

  // Randomizable fields
  rand bit [ADDR_WIDTH-1:0] src;   // terminal origen
  rand bit [ADDR_WIDTH-1:0] addr;  // terminal destino
  rand bit [DATA_WIDTH-1:0] data;  // payload
  rand bit [$clog2(MAX_N_CYCLES)-1:0] cycles_between;
  rand route_mode_e mode;

  // Flags
  rand error_type_e msg_error;
  rand bit          broadcast;

  // Observado por el monitor/scoreboard
  bit [DATA_WIDTH-1:0] out_dut;
  bit [ADDR_WIDTH-1:0] out_port;

  `uvm_object_utils_begin(seq_item)
    `uvm_field_int(src,           UVM_ALL_ON)
    `uvm_field_int(addr,          UVM_ALL_ON)
    `uvm_field_int(data,          UVM_ALL_ON)
    `uvm_field_int(cycles_between,UVM_ALL_ON)
    `uvm_field_enum(route_mode_e, mode, UVM_ALL_ON)
    `uvm_field_enum(error_type_e, msg_error, UVM_ALL_ON)
    `uvm_field_int(broadcast,     UVM_ALL_ON)
    `uvm_field_int(out_dut,       UVM_NOPACK)
    `uvm_field_int(out_port,      UVM_NOPACK)
  `uvm_object_utils_end

  // Constraints
  constraint gap_c { cycles_between < MAX_N_CYCLES; }

  constraint broadcast_c {
    broadcast dist { 1'b0 := 9, 1'b1 := 1 };
  }

  constraint error_c {
    msg_error dist { NO_ERROR := 8, HDR_ERROR := 1, PAY_ERROR := 1 };
  }

  constraint bdcst_addr_c {
    solve broadcast before addr;
    if (broadcast)
        addr == {ADDR_WIDTH{1'b1}};
  }

  constraint src_dst_c {
    if (!broadcast)
      src != addr;
  }

  function new(string name="seq_item");
    super.new(name);
  endfunction

endclass

