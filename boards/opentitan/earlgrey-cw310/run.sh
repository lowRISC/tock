#!/bin/bash

BUILD_DIR="verilator_build/"

if [[ "${VERILATOR}" == "yes" ]]; then
		if [ -d "$BUILD_DIR" ]; then
			# Cleanup before we build again
			printf "\n[CW-130: Verilator Tests]: Cleaning up verilator_build...\n\n"
			rm -R "$BUILD_DIR"/*
		else
			printf "\n[CW-130: Verilator Tests]: Setting up verilator_build...\n\n"
			mkdir "$BUILD_DIR"
		fi
	# Copy in and covert from cargo test output to binary
	${OBJCOPY} ${1} "$BUILD_DIR"/earlgrey-cw310-tests.elf
	${OBJCOPY} --output-target=binary "$BUILD_DIR"/earlgrey-cw310-tests.elf "$BUILD_DIR"/earlgrey-cw310-tests.bin
	# Create VMEM file from test binary
	srec_cat "$BUILD_DIR"/earlgrey-cw310-tests.bin\
		--binary --offset 0 --byte-swap 8 --fill 0xff \
		-within "$BUILD_DIR"/earlgrey-cw310-tests.bin\
		-binary -range-pad 8 --output "$BUILD_DIR"/binary.64.vmem --vmem 64
	${OPENTITAN_TREE}/bazel-out/k8-fastbuild/bin/hw/build.verilator_real/sim-verilator/Vchip_sim_tb \
		--meminit=rom,${OPENTITAN_TREE}/bazel-out/k8-fastbuild-ST-97f470ee3b14/bin/sw/device/lib/testing/test_rom/test_rom_sim_verilator.scr.39.vmem \
		--meminit=flash,./"$BUILD_DIR"/binary.64.vmem \
		--meminit=otp,${OPENTITAN_TREE}/bazel-out/k8-fastbuild/bin/sw/device/tests/otp_ctrl_smoketest_sim_verilator.runfiles/lowrisc_opentitan/hw/ip/otp_ctrl/data/img_rma.vmem
elif [[ "${OPENTITAN_TREE}" != "" ]]; then
	riscv64-linux-gnu-objcopy --update-section .apps=${APP} ${1} bundle.elf
	riscv64-linux-gnu-objcopy --output-target=binary bundle.elf binary

	${OPENTITAN_TREE}/build-out/sw/host/rom_ext_signer \
	rom_ext \
	binary \
	${OPENTITAN_TREE}/sw/device/silicon_creator/mask_rom/keys/test_key_0_rsa_3072_exp_f4.der \
	bundle.elf \
	binary.signed

	${OPENTITAN_TREE}/util/fpga/cw310_loader.py --firmware binary.signed
else
	../../../tools/qemu/build/qemu-system-riscv32 -M opentitan -bios ../../../tools/qemu-runner/opentitan-boot-rom.elf -nographic -serial stdio -monitor none -semihosting -kernel "${1}"
fi
