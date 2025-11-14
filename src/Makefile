# Makefile for Router UVM Verification Environment (VCS)
#Proyecto2Veri

# Root directories
root_dir := $(PWD)
bld_dir  := $(root_dir)/build
src_dir  := $(root_dir)

# File groups
dut_srcs := \
  $(src_dir)/dut/Router_library.sv

# UVM environment (only compile pkg + tests + tb)
uvm_env := \
  $(src_dir)/interface/mesh_gen_if.sv \
  $(src_dir)/globals/pkg.sv \
  $(src_dir)/sequence_items/seq_item.sv \
  $(src_dir)/sequences/base_seq.sv \
  $(src_dir)/router_agent/driver.sv \
  $(src_dir)/router_agent/monitor.sv \
  $(src_dir)/router_agent/sequencer.sv \
  $(src_dir)/scoreboard/scoreboard.sv \
  $(src_dir)/scoreboard/subscriber.sv \
  $(src_dir)/env/agent.sv \
  $(src_dir)/tb.sv \
  $(src_dir)/tests/test.sv \
  $(src_dir)/tests/test_smoke.sv

# switches (macros)
# Example usage: make run TEST=test_router DEBUG=1 GUI=1
TEST ?= test
PATTERN ?=

FSDB_DEF :=
ifeq ($(FSDB),1)
  FSDB_DEF := +define+FSDB
else ifeq ($(FSDB),2)
  FSDB_DEF := +define+FSDB_ALL
endif

DEBUG_DEF :=
ifeq ($(DEBUG),1)
  DEBUG_DEF := +define+DEBUG
endif

GUI_FLAG :=
ifeq ($(GUI),1)
  GUI_FLAG := -gui
endif

# Include directories
INC_DIRS := \
  +incdir+$(src_dir)/globals \
  +incdir+$(src_dir)/interface \
  +incdir+$(src_dir)/sequence_items \
  +incdir+$(src_dir)/sequences \
  +incdir+$(src_dir)/router_agent \
  +incdir+$(src_dir)/scoreboard \
  +incdir+$(src_dir)/env \
  +incdir+$(src_dir)/tests \
  +incdir+$(src_dir)/dut


# Synopsys environment setup
SYNOPSYS_ENV := source /mnt/vol_NFS_rh003/estudiantes/archivos_config/synopsys_tools2.sh

# Build and run targets
$(bld_dir):
	mkdir -p $(bld_dir)

compile: $(bld_dir)
	cd $(bld_dir); \
	$(SYNOPSYS_ENV); \
	vcs -full64 -sverilog -ntb_opts uvm-1.2 \
		+vpi +UVM_NO_RELNOTES \
		$(INC_DIRS) \
		-timescale=1ns/1ps \
		$(src_dir)/interface/mesh_gen_if.sv \
		$(dut_srcs) \
		$(src_dir)/globals/pkg.sv \
		$(src_dir)/tb.sv \
		$(src_dir)/tests/test.sv \
		$(src_dir)/tests/test_smoke.sv \
		+define+UVM_CMDLINE_NO_DPI \
		+define+UVM_REGEX_NO_DPI \
		$(DEBUG_DEF) $(FSDB_DEF) $(PATTERN) \
		-l vcs_compile.log \
		-o simv

run: compile
	cd $(bld_dir); \
	$(SYNOPSYS_ENV); \
	./simv -l vcs_run.log \
		+UVM_VERBOSITY=UVM_MEDIUM \
		+UVM_TESTNAME=$(TEST) \
		+UVM_CONFIG_DB_TRACE \
		$(GUI_FLAG)

clean:
	rm -rf $(bld_dir)

lint:
	$(SYNOPSYS_ENV); \
	vcs -sverilog -lint=TFIPC-L $(dut_srcs) $(uvm_env) $(INC_DIRS)

cov:
	cd $(bld_dir); \
	$(SYNOPSYS_ENV); \
	dve -covdir simv.vdb &

# ============================================================
# Example usage:
#   make run                     -> default test (test)
#   make run TEST=test_router    -> run specific UVM test
#   make run DEBUG=1             -> enable router debug prints
#   make run FSDB=1              -> enable FSDB dump
#   make run GUI=1               -> open DVE GUI debugger
#   make clean                   -> remove build/
#   make lint                    -> lint check
# ============================================================

help:
	@echo "Usage:"
	@echo "  make run                  -> compile & run simulation"
	@echo "  make run TEST=test_name   -> run selected UVM test"
	@echo "  make run DEBUG=1          -> enable router debug prints"
	@echo "  make run FSDB=1           -> enable FSDB waveform dump"
	@echo "  make run GUI=1            -> launch DVE GUI"
	@echo "  make clean                -> clean build/"
	@echo "  make lint                 -> run lint check"
	@echo "  make cov                  -> open coverage"

