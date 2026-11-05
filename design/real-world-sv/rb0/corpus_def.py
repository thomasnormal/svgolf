#!/usr/bin/env python3
"""Defines the WP-RB0 corpus; writes corpus.json (blocks) next to this script's parent (W)."""
import json, os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
exec(open(os.path.join(HERE, "pins.py")).read())

REPO = {v[0]: (k, v[1]) for k, v in PINS.items()}

IBEX_PRIM = "vendor/lowrisc_ip/ip/prim/rtl"
IBEX_INC = [IBEX_PRIM, "vendor/lowrisc_ip/dv/sv/dv_utils"]
IBEX_DEPS_SUPPORT = [IBEX_PRIM + "/prim_assert.sv"]  # not compiled (macros only), fetched for -I
CV40P_PKGS = ["rtl/include/cv32e40p_pkg.sv", "rtl/include/cv32e40p_apu_core_pkg.sv", "rtl/include/cv32e40p_fpu_pkg.sv"]
OT_INC = ["hw/ip/prim/rtl", "hw/dv/sv/dv_utils"]
HZ3_INC = ["hdl", "hdl/arith"]
MOR_INC = ["rtl/verilog"]
BIR_INC = ["core/riscv"]
CVA6_PKGS = ["core/include/config_pkg.sv", "core/include/riscv_pkg.sv", "core/include/cv32a6_imac_sv32_config_pkg.sv",
             "core/include/build_config_pkg.sv", "core/include/ariane_pkg.sv"]
CVA6_INC = ["core/include", "vendor/pulp-platform/common_cells/include"]
E40X = "rtl/"

B = []
def blk(id, project, category, kind, top, files, inc=(), note="", params=None, defines=None, skip_base=False):
    repo, commit = REPO[project]
    B.append(dict(id=id, project=project, repo=repo, commit=commit, category=category, kind=kind, top=top,
                  files=list(files), incdirs=list(inc), note=note, params=params or {}, defines=defines or [], skip_base=skip_base))

# --- ibex
blk("ibex_alu", "ibex", "alu", "comb", "ibex_alu", ["rtl/ibex_pkg.sv", "rtl/ibex_alu.sv"], IBEX_INC)
blk("ibex_compressed_decoder", "ibex", "decoder", "comb", "ibex_compressed_decoder",
    ["rtl/ibex_pkg.sv", "rtl/ibex_compressed_decoder.sv"], IBEX_INC, note="RVC expander")
blk("ibex_decoder", "ibex", "decoder", "comb", "ibex_decoder", ["rtl/ibex_pkg.sv", "rtl/ibex_cheriot_pkg.sv", "rtl/ibex_decoder.sv"], IBEX_INC,
    note="main instruction decoder incl. immediate generation")
blk("ibex_branch_predict", "ibex", "branch", "comb", "ibex_branch_predict", ["rtl/ibex_pkg.sv", "rtl/ibex_branch_predict.sv"], IBEX_INC)
blk("ibex_multdiv_slow", "ibex", "mult-div", "seq", "ibex_multdiv_slow", ["rtl/ibex_pkg.sv", "rtl/ibex_multdiv_slow.sv"], IBEX_INC)
blk("ibex_multdiv_fast", "ibex", "mult-div", "seq", "ibex_multdiv_fast", ["rtl/ibex_pkg.sv", "rtl/ibex_multdiv_fast.sv"], IBEX_INC)
blk("ibex_register_file_ff", "ibex", "regfile", "seq", "ibex_register_file_ff", ["rtl/ibex_pkg.sv", "rtl/ibex_cheriot_pkg.sv", "rtl/ibex_register_file_ff.sv"], IBEX_INC)
blk("ibex_ex_block", "ibex", "pipeline-stage", "hier", "ibex_ex_block",
    ["rtl/ibex_pkg.sv", "rtl/ibex_cheriot_pkg.sv", "rtl/ibex_alu.sv", "rtl/ibex_multdiv_slow.sv", "rtl/ibex_multdiv_fast.sv", "rtl/ibex_ex_block.sv"], IBEX_INC,
    note="ALU + multiplier/divider wrapper")
blk("ibex_wb_stage", "ibex", "pipeline-stage", "seq", "ibex_wb_stage", ["rtl/ibex_pkg.sv", "rtl/ibex_cheriot_pkg.sv", "rtl/ibex_wb_stage.sv"], IBEX_INC)
blk("ibex_csr", "ibex", "csr", "seq", "ibex_csr", ["rtl/ibex_pkg.sv", "rtl/ibex_csr.sv"], IBEX_INC)
blk("ibex_counter", "ibex", "csr", "seq", "ibex_counter", ["rtl/ibex_pkg.sv", "rtl/ibex_counter.sv"], IBEX_INC)
# --- cv32e40p
blk("cv32e40p_alu", "cv32e40p", "alu", "hier", "cv32e40p_alu",
    CV40P_PKGS + ["rtl/cv32e40p_popcnt.sv", "rtl/cv32e40p_ff_one.sv", "rtl/cv32e40p_alu_div.sv", "rtl/cv32e40p_alu.sv"], note="ALU with popcount, ff1, serial divider")
blk("cv32e40p_alu_div", "cv32e40p", "mult-div", "seq", "cv32e40p_alu_div", CV40P_PKGS + ["rtl/cv32e40p_alu_div.sv"], note="serial divider (already ingested by Examples/system-verilog/alu_div)")
blk("cv32e40p_popcnt", "cv32e40p", "popcount", "comb", "cv32e40p_popcnt", CV40P_PKGS + ["rtl/cv32e40p_popcnt.sv"])
blk("cv32e40p_ff_one", "cv32e40p", "ff1", "comb", "cv32e40p_ff_one", CV40P_PKGS + ["rtl/cv32e40p_ff_one.sv"])
blk("cv32e40p_compressed_decoder", "cv32e40p", "decoder", "comb", "cv32e40p_compressed_decoder", CV40P_PKGS + ["rtl/cv32e40p_compressed_decoder.sv"])
blk("cv32e40p_decoder", "cv32e40p", "decoder", "comb", "cv32e40p_decoder", CV40P_PKGS + ["rtl/cv32e40p_decoder.sv"], note="main decoder, 131 KB")
blk("cv32e40p_mult", "cv32e40p", "mult-div", "seq", "cv32e40p_mult", CV40P_PKGS + ["rtl/cv32e40p_mult.sv"])
blk("cv32e40p_register_file_ff", "cv32e40p", "regfile", "seq", "cv32e40p_register_file", CV40P_PKGS + ["rtl/cv32e40p_register_file_ff.sv"])
blk("cv32e40p_int_controller", "cv32e40p", "csr", "seq", "cv32e40p_int_controller", CV40P_PKGS + ["rtl/cv32e40p_int_controller.sv"], note="interrupt priority")
blk("ibex_cs_registers", "ibex", "csr", "seq", "ibex_cs_registers", ["rtl/ibex_pkg.sv", "rtl/ibex_cheriot_pkg.sv", "rtl/ibex_csr.sv", "rtl/ibex_counter.sv", "rtl/ibex_cs_registers.sv"], IBEX_INC, note="CSR file incl. address decode")
# --- cv32e40x
blk("cv32e40x_alu_b_cpop", "cv32e40x", "popcount", "comb", "cv32e40x_alu_b_cpop", ["rtl/include/cv32e40x_pkg.sv", "rtl/cv32e40x_alu_b_cpop.sv"])
blk("cv32e40x_popcnt", "cv32e40x", "popcount", "comb", "cv32e40x_popcnt", ["rtl/include/cv32e40x_pkg.sv", "rtl/cv32e40x_popcnt.sv"])
blk("cv32e40x_ff_one", "cv32e40x", "ff1", "comb", "cv32e40x_ff_one", ["rtl/include/cv32e40x_pkg.sv", "rtl/cv32e40x_ff_one.sv"])
blk("cv32e40x_alu", "cv32e40x", "alu", "hier", "cv32e40x_alu", ["rtl/include/cv32e40x_pkg.sv", "rtl/cv32e40x_ff_one.sv", "rtl/cv32e40x_alu_b_cpop.sv", "rtl/cv32e40x_popcnt.sv", "rtl/cv32e40x_alu.sv"])
blk("cv32e40x_pc_target", "cv32e40x", "branch", "comb", "cv32e40x_pc_target", ["rtl/include/cv32e40x_pkg.sv", "rtl/cv32e40x_pc_target.sv"], note="jump/branch target")
blk("cv32e40x_i_decoder", "cv32e40x", "decoder", "comb", "cv32e40x_i_decoder", ["rtl/include/cv32e40x_pkg.sv", "rtl/cv32e40x_i_decoder.sv"])
blk("cv32e40x_b_decoder", "cv32e40x", "decoder", "comb", "cv32e40x_b_decoder", ["rtl/include/cv32e40x_pkg.sv", "rtl/cv32e40x_b_decoder.sv"], note="Zb* decoder")
blk("cv32e40x_compressed_decoder", "cv32e40x", "decoder", "comb", "cv32e40x_compressed_decoder", ["rtl/include/cv32e40x_pkg.sv", "rtl/cv32e40x_compressed_decoder.sv"])
# --- cva6
blk("cva6_alu", "cva6", "alu", "comb", "alu", CVA6_PKGS + ["core/alu.sv"], CVA6_INC, note="struct parameter CVA6Cfg and type parameter fu_data_t")
blk("cva6_branch_unit", "cva6", "branch", "comb", "branch_unit", CVA6_PKGS + ["core/branch_unit.sv"], CVA6_INC)
blk("cva6_multiplier", "cva6", "mult-div", "seq", "multiplier", CVA6_PKGS + ["core/multiplier.sv"], CVA6_INC)
blk("cva6_serdiv", "cva6", "mult-div", "seq", "serdiv", CVA6_PKGS + ["vendor/pulp-platform/common_cells/src/cf_math_pkg.sv", "vendor/pulp-platform/common_cells/src/lzc.sv", "core/serdiv.sv"], CVA6_INC)
blk("cva6_compressed_decoder", "cva6", "decoder", "comb", "compressed_decoder", CVA6_PKGS + ["core/compressed_decoder.sv"], CVA6_INC)
blk("cva6_lzc", "cva6", "ff1", "comb", "lzc", ["vendor/pulp-platform/common_cells/src/cf_math_pkg.sv", "vendor/pulp-platform/common_cells/src/lzc.sv"], CVA6_INC, note="PULP common_cells leading-zero counter (the cell cva6 and cv32e40p share)")
blk("cva6_popcount", "cva6", "popcount", "comb", "popcount", ["vendor/pulp-platform/common_cells/src/cf_math_pkg.sv", "vendor/pulp-platform/common_cells/src/lzc.sv", "vendor/pulp-platform/common_cells/src/popcount.sv"], CVA6_INC, note="recursive instantiation (popcount builds its adder tree from popcount)")
# --- picorv32 (one file, many modules; the tops are instantiated inside the same file)
PV = ["picorv32.v"]
blk("picorv32_pcpi_mul", "picorv32", "mult-div", "seq", "picorv32_pcpi_mul", PV)
blk("picorv32_pcpi_fast_mul", "picorv32", "mult-div", "seq", "picorv32_pcpi_fast_mul", PV)
blk("picorv32_pcpi_div", "picorv32", "mult-div", "seq", "picorv32_pcpi_div", PV)
blk("picorv32_regs", "picorv32", "regfile", "seq", "picorv32_regs", PV)
blk("picorv32_axi_adapter", "picorv32", "pipeline-stage", "seq", "picorv32_axi_adapter", PV)
blk("picorv32_core", "picorv32", "core", "seq", "picorv32", PV, note="the whole 2100-line core")
# --- serv
SV = "rtl/"
blk("serv_alu", "serv", "alu", "seq", "serv_alu", [SV+"serv_alu.v"], note="bit-serial ALU")
blk("serv_immdec", "serv", "imm-gen", "seq", "serv_immdec", [SV+"serv_immdec.v"])
blk("serv_decode", "serv", "decoder", "comb", "serv_decode", [SV+"serv_decode.v"])
blk("serv_compdec", "serv", "decoder", "comb", "serv_compdec", [SV+"serv_compdec.v"], note="RVC decompressor")
blk("serv_csr", "serv", "csr", "seq", "serv_csr", [SV+"serv_csr.v"])
blk("serv_bufreg", "serv", "pipeline-stage", "seq", "serv_bufreg", [SV+"serv_bufreg.v"])
# --- hazard3
HZ = "hdl/"
blk("hazard3_alu", "hazard3", "alu", "comb", "hazard3_alu", [HZ+"arith/hazard3_alu.v", HZ+"arith/hazard3_shift_barrel.v", HZ+"arith/hazard3_priority_encode.v", HZ+"arith/hazard3_onehot_encode.v"], HZ3_INC)
blk("hazard3_branchcmp", "hazard3", "branch", "comb", "hazard3_branchcmp", [HZ+"arith/hazard3_branchcmp.v"], HZ3_INC)
blk("hazard3_shift_barrel", "hazard3", "shifter", "comb", "hazard3_shift_barrel", [HZ+"arith/hazard3_shift_barrel.v"], HZ3_INC)
blk("hazard3_priority_encode", "hazard3", "ff1", "comb", "hazard3_priority_encode", [HZ+"arith/hazard3_onehot_priority.v", HZ+"arith/hazard3_onehot_encode.v", HZ+"arith/hazard3_priority_encode.v"], HZ3_INC)
blk("hazard3_onehot_priority", "hazard3", "ff1", "comb", "hazard3_onehot_priority", [HZ+"arith/hazard3_onehot_priority.v"], HZ3_INC)
blk("hazard3_instr_decompress", "hazard3", "decoder", "comb", "hazard3_instr_decompress", [HZ+"hazard3_instr_decompress.v"], HZ3_INC, note="RVC expander")
blk("hazard3_regfile_1w2r", "hazard3", "regfile", "seq", "hazard3_regfile_1w2r", [HZ+"hazard3_regfile_1w2r.v"], HZ3_INC)
blk("hazard3_mul_fast", "hazard3", "mult-div", "seq", "hazard3_mul_fast", [HZ+"arith/hazard3_mul_fast.v"], HZ3_INC)
# --- mor1kx
MK = "rtl/verilog/"
blk("mor1kx_execute_alu", "mor1kx", "alu", "seq", "mor1kx_execute_alu", [MK+"mor1kx_execute_alu.v"], MOR_INC)
blk("mor1kx_decode", "mor1kx", "decoder", "comb", "mor1kx_decode", [MK+"mor1kx_decode.v"], MOR_INC)
blk("mor1kx_rf_cappuccino", "mor1kx", "regfile", "seq", "mor1kx_rf_cappuccino", [MK+"mor1kx_simple_dpram_sclk.v", MK+"mor1kx_rf_cappuccino.v"], MOR_INC)
blk("mor1kx_wb_mux_cappuccino", "mor1kx", "forwarding-mux", "comb", "mor1kx_wb_mux_cappuccino", [MK+"mor1kx_wb_mux_cappuccino.v"], MOR_INC)
# --- biriscv (ultraembedded/riscv)
BR = "core/riscv/"
blk("biriscv_alu", "biriscv", "alu", "comb", "riscv_alu", [BR+"riscv_alu.v"], BIR_INC)
blk("biriscv_decoder", "biriscv", "decoder", "comb", "riscv_decoder", [BR+"riscv_decoder.v"], BIR_INC)
blk("biriscv_multiplier", "biriscv", "mult-div", "seq", "riscv_multiplier", [BR+"riscv_multiplier.v"], BIR_INC)
blk("biriscv_divider", "biriscv", "mult-div", "seq", "riscv_divider", [BR+"riscv_divider.v"], BIR_INC)
blk("biriscv_regfile", "biriscv", "regfile", "seq", "riscv_regfile", [BR+"riscv_regfile.v"], BIR_INC)
blk("hazard3_csr", "hazard3", "csr", "seq", "hazard3_csr", ["hdl/hazard3_csr.v"], ["hdl"], note="CSR file incl. address decode (uses hazard3_csr_addr.vh)")
# --- opentitan prim
OT = "hw/ip/prim/rtl/"
blk("ot_prim_secded_inv_39_32_enc", "opentitan", "ecc", "comb", "prim_secded_inv_39_32_enc", [OT+"prim_secded_inv_39_32_enc.sv"], OT_INC)
blk("ot_prim_secded_inv_39_32_dec", "opentitan", "ecc", "comb", "prim_secded_inv_39_32_dec", [OT+"prim_secded_inv_39_32_dec.sv"], OT_INC)
blk("ot_prim_secded_39_32_enc", "opentitan", "ecc", "comb", "prim_secded_39_32_enc", [OT+"prim_secded_39_32_enc.sv"], OT_INC)
blk("ot_prim_leading_one_ppc", "opentitan", "ff1", "comb", "prim_leading_one_ppc", [OT+"prim_util_pkg.sv", OT+"prim_leading_one_ppc.sv"], OT_INC)
blk("ot_prim_arbiter_ppc", "opentitan", "forwarding-mux", "comb", "prim_arbiter_ppc", [OT+"prim_util_pkg.sv", OT+"prim_leading_one_ppc.sv", OT+"prim_arbiter_ppc.sv"], OT_INC, note="parallel-prefix priority arbiter")
blk("ot_prim_onehot_mux", "opentitan", "forwarding-mux", "comb", "prim_onehot_mux", ["hw/ip/prim_generic/rtl/prim_and2.sv", OT+"prim_onehot_mux.sv"], OT_INC)
blk("ot_prim_max_tree", "opentitan", "comparator", "comb", "prim_max_tree", [OT+"prim_util_pkg.sv", OT+"prim_max_tree.sv"], OT_INC)
blk("biriscv_issue", "biriscv", "forwarding-mux", "seq", "riscv_issue", [BR+"riscv_issue.v"], BIR_INC, note="issue stage with operand forwarding / scoreboard")
blk("biriscv_exec", "biriscv", "pipeline-stage", "seq", "riscv_exec", [BR+"riscv_alu.v", BR+"riscv_exec.v"], BIR_INC, note="execute stage: ALU + branch resolution")
blk("ot_prim_secded_inv_72_64_dec", "opentitan", "ecc", "comb", "prim_secded_inv_72_64_dec", [OT+"prim_secded_inv_72_64_dec.sv"], OT_INC)
# --- veer el2
EL = "design/"
blk("el2_exu_alu_ctl", "veer_el2", "alu", "comb", "el2_exu_alu_ctl", [EL+"include/el2_def.sv", EL+"lib/beh_lib.sv", EL+"exu/el2_exu_alu_ctl.sv"], [EL+"include", EL+"lib"], note="needs the generated el2_param.vh / el2_pdef.vh (absent from the repository)")
blk("el2_ifu_compress_ctl", "veer_el2", "decoder", "comb", "el2_ifu_compress_ctl", [EL+"include/el2_def.sv", EL+"ifu/el2_ifu_compress_ctl.sv"], [EL+"include", EL+"lib"], note="same generated-config dependency")
blk("el2_dec_gpr_ctl", "veer_el2", "regfile", "seq", "el2_dec_gpr_ctl", [EL+"include/el2_def.sv", EL+"lib/beh_lib.sv", EL+"dec/el2_dec_gpr_ctl.sv"], [EL+"include", EL+"lib"])
blk("vexriscv_min_streamfifo", "vexriscv", "pipeline-stage", "seq", "StreamFifo", ["pythondata_cpu_vexriscv/verilog/VexRiscv_Min.v"], note="a generated FIFO module of the same file")
# --- vexriscv generated
blk("vexriscv_min_core", "vexriscv", "core", "seq", "VexRiscv", ["pythondata_cpu_vexriscv/verilog/VexRiscv_Min.v"], note="SpinalHDL-generated Verilog")

# --- rocket-chip generated Verilog (Chisel/FIRRTL output, 259 modules, 9.5 MB in ONE file)
ROCKET = ["pythondata_cpu_rocket/verilog/generated-src/freechips.rocketchip.system.LitexConfig_linux_1_1.v"]
blk("rocket_alu", "rocket", "alu", "comb", "ALU", ROCKET, note="Chisel-generated ALU module of the 9.5 MB LitexConfig_linux_1_1.v")
blk("rocket_rvc_expander", "rocket", "decoder", "comb", "RVCExpander", ROCKET, note="Chisel-generated RVC expander", skip_base=True)
blk("rocket_muldiv", "rocket", "mult-div", "seq", "MulDiv", ROCKET, note="Chisel-generated multiplier/divider", skip_base=True)
blk("rocket_breakpoint_unit", "rocket", "comparator", "comb", "BreakpointUnit", ROCKET, note="Chisel-generated trigger comparator", skip_base=True)
# --- workarounds (variants run as <id>@wa): the first blocker removed by a deterministic transformation
def wa(id, **kw):
    for b in B:
        if b["id"] == id:
            b["wa"] = kw
            return
    raise KeyError(id)
def edits(id, **kw):
    for b in B:
        if b["id"] == id:
            b["wa3_edits"] = kw
            return
    raise KeyError(id)
# hazard3_branchcmp: replace the two config includes (50+ parameters, one of which the loader refuses) by the one parameter the block uses
edits("hazard3_branchcmp", **{"hazard3_branchcmp.v": [
    (r'`include "hazard3_config.vh"\n,\n`include "hazard3_width_const.vh"', "parameter W_DATA = 32"),
    (r'`include "hazard3_ops.vh"\n', "")]})
for m in ["picorv32_pcpi_mul", "picorv32_pcpi_fast_mul", "picorv32_pcpi_div", "picorv32_axi_adapter"]:
    wa(m, slice={"file": "picorv32.v", "modules": [b["top"] for b in B if b["id"] == m]},
       note="the top is instantiated by another module of the same file: the module text alone is compiled")
wa("picorv32_core", slice={"file": "picorv32.v", "modules": ["picorv32", "picorv32_pcpi_mul", "picorv32_pcpi_fast_mul", "picorv32_pcpi_div"]},
   note="the top is instantiated by picorv32_axi/picorv32_wb of the same file: the core and its coprocessors alone are compiled")
for m, mod in [("rocket_alu", "ALU"), ("rocket_rvc_expander", "RVCExpander"), ("rocket_muldiv", "MulDiv"), ("rocket_breakpoint_unit", "BreakpointUnit")]:
    wa(m, slice={"file": ROCKET[0], "modules": [mod]},
       note="the top is instantiated by another module of the same file: the module text alone is compiled")
wa("cva6_popcount", note="NO workaround attempted: popcount instantiates itself (recursive generate)")

out = os.path.join(HERE, "corpus.json")
json.dump(B, open(out, "w"), indent=1)
print(len(B), "blocks,", len({b['project'] for b in B}), "projects ->", out)
