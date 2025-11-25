# Makefile for Router UVM Verification Environment (VCS)

# Root directories
root_dir := $(PWD)
bld_dir  := $(root_dir)/build
src_dir  := $(root_dir)

# File groups
# 1. DUT Source
dut_srcs := \
  $(src_dir)/dut/Router_library.sv

# 2. UVM Environment
# NOTICE: We ONLY compile the Interface, the Package, and the Top.
# All class files (driver, monitor, etc.) are compiled because they are 
# `included inside globals/pkg.sv.
uvm_env := \
    $(src_dir)/interface/mesh_gen_if.sv \
    $(src_dir)/globals/pkg.sv \
    $(src_dir)/tb_top.sv

# Test Name Default
TEST ?= base_test

# Debug / GUI Flags
DEBUG_DEF :=
ifeq ($(DEBUG),1)
  DEBUG_DEF := +define+DEBUG
endif

GUI_FLAG :=
ifeq ($(GUI),1)
  GUI_FLAG := -gui
endif

# Include Directories
# VCS needs these to find files referenced by `include inside the package
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

# Synopsys Setup (Adjust if necessary)
SYNOPSYS_ENV := source /mnt/vol_NFS_rh003/estudiantes/archivos_config/synopsys_tools2.sh

#Define the flags for coverage 
COV_OPTS := -cm line+tgl+cond+fsm+branch+assert

# Targets
$(bld_dir):
	mkdir -p $(bld_dir)

compile: $(bld_dir)
	cd $(bld_dir); \
	$(SYNOPSYS_ENV); \
	vcs -full64 -sverilog -ntb_opts uvm-1.2 \
		+vpi +UVM_NO_RELNOTES \
		$(INC_DIRS) \
		-timescale=1ns/1ps \
		$(dut_srcs) \
		$(uvm_env) \
		+define+UVM_CMDLINE_NO_DPI \
		+define+UVM_REGEX_NO_DPI \
		$(DEBUG_DEF) \
                $(COV_OPTS) \
		-l vcs_compile.log \
		-o simv

run: compile
	cd $(bld_dir); \
	$(SYNOPSYS_ENV); \
	./simv -l vcs_run.log \
		+UVM_VERBOSITY=UVM_MEDIUM \
		+UVM_TESTNAME=$(TEST) \
		+UVM_CONFIG_DB_TRACE \
		$(GUI_FLAG)\
                $(COV_OPTS)
clean:
	rm -rf $(bld_dir) *.log *.vcd *.key

lint:
	$(SYNOPSYS_ENV); \
	vcs -sverilog -lint=TFIPC-L $(dut_srcs) $(uvm_env) $(INC_DIRS)

#Add a target to view the report
report:
	cd $(bld_dir); \
	$(SYNOPSYS_ENV); \
	urg -dir simv.vdb -format text; \
	cat urgReport/dashboard.txt
