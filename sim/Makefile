SHELL=/bin/bash -o pipefail
.SHELLFLAGS += -e

PKG_SRCS  := $(PWD)/../pkg/types.sv
HDL_SRCS  := $(shell find $(PWD)/../hdl -name '*.sv')
HVL_SRCS  := $(shell find $(PWD)/../hvl -name '*.sv' -o -name '*.v' -o -name '*.o' -o -name '*.so')
VCS_SRCS  := $(PKG_SRCS) $(HDL_SRCS) $(HVL_SRCS)

TIMEOUT   ?= 1000000000

export VCS_ARCH_OVERRIDE=linux
VCS_FLAGS    = +incdir+$(PWD)/../hvl/vcs -licqueue -full64 -lca -sverilog -timescale=1ps/1ps -debug_acc+all -kdb -suppress=LCA_FEATURES_ENABLED -msg_config=../vcs_warn.config -assert svaext

vcs/top_tb: $(VCS_SRCS)
	mkdir -p vcs
	cd vcs && vcs $(VCS_SRCS) $(VCS_FLAGS) -l compile.log -top top_tb -o top_tb
	# bash check_compile_error.sh

.PHONY: gen_inputs
gen_inputs: ../bin/get_mesi_inputs.py
	cd .. && python3 bin/get_mesi_inputs.py && cd sim

.PHONY: run_vcs_top_tb
run_vcs_top_tb: vcs/top_tb 
	rm -f vcs/dump.fsdb
	python3 $(PWD)/../bin/get_options.py clock
	cp ../inputs_* vcs/
	cd vcs && ./top_tb -l simulation.log -exitstatus -suppress=ASLR_DETECTED_INFO \
		+TIMEOUT_ECE511=$(TIMEOUT) \
		+CLOCK_PERIOD_PS_ECE511=$(shell python3 $(PWD)/../bin/get_options.py clock)

.PHONY: covrep
covrep: vcs/top_tb.vdb
	cd vcs && urg -dir top_tb.vdb

.PHONY: verdi
verdi:
	mkdir -p verdi
	cd verdi && timeout $(ECE411_GUI_TIMEOUT) $(VERDI_HOME)/bin/verdi -ssf $(PWD)/vcs/dump.fsdb

.PHONY: clean
clean:
	rm -rf bin vcs verdi
