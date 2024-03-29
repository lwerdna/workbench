#!/usr/bin/env python

# test on the instruction class and instruction form names from the A64 specification

import sys
import random
import algorithm

inputs = [
    'addsub_carry', 'addsub_ext', 'addsub_imm', 'addsub_immtags', 'addsub_shift',
    'asimdall', 'asimddiff', 'asimdelem', 'asimdext', 'asimdimm', 'asimdins',
    'asimdmisc', 'asimdmiscfp16', 'asimdperm', 'asimdsame', 'asimdsame2',
    'asimdsamefp16', 'asimdshf', 'asimdtbl', 'asisddiff', 'asisdelem', 'asisdlse',
    'asisdlsep', 'asisdlso', 'asisdlsop', 'asisdmisc', 'asisdmiscfp16', 'asisdone',
    'asisdpair', 'asisdsame', 'asisdsame2', 'asisdsamefp16', 'asisdshf',
    'barriers', 'bitfield', 'branch_imm', 'branch_reg', 'compbranch', 'comswap',
    'comswappr', 'condbranch', 'condcmp_imm', 'condcmp_reg', 'condsel', 'control',
    'crypto3_imm2', 'crypto3_imm6', 'crypto4', 'cryptoaes', 'cryptosha2',
    'cryptosha3', 'cryptosha512_2', 'cryptosha512_3', 'dp_1src', 'dp_2src',
    'dp_3src', 'dpimm', 'dpreg', 'exception', 'extract', 'float2fix', 'float2int',
    'floatccmp', 'floatcmp', 'floatdp1', 'floatdp2', 'floatdp3', 'floatimm',
    'floatsel', 'hints', 'ldapstl_unscaled', 'ldst', 'ldst_immpost', 'ldst_immpre',
    'ldst_pac', 'ldst_pos', 'ldst_regoff', 'ldst_unpriv', 'ldst_unscaled',
    'ldstexclp', 'ldstexclr', 'ldstnapair_offs', 'ldstord', 'ldstpair_off',
    'ldstpair_post', 'ldstpair_pre', 'ldsttags', 'loadlit', 'log_imm', 'log_shift',
    'memop', 'mortlach_32bit_prod', 'mortlach_64bit_prod', 'mortlach_addhv',
    'mortlach_b16f32_prod', 'mortlach_contig_load', 'mortlach_contig_qload',
    'mortlach_contig_qstore', 'mortlach_contig_store', 'mortlach_ctxt_ldst',
    'mortlach_ext', 'mortlach_extract_pred', 'mortlach_f16f32_prod',
    'mortlach_f32f32_prod', 'mortlach_f64f64_prod', 'mortlach_hvadd',
    'mortlach_i16i64_prod', 'mortlach_i8i32_prod', 'mortlach_ins',
    'mortlach_insert_pred', 'mortlach_mem', 'mortlach_misc', 'mortlach_zero',
    'movewide', 'pcreladdr', 'perm_undef', 'pstate', 'reserved', 'rmif', 'root',
    'setf', 'simd_dp', 'sme', 'sve', 'sve_alloca', 'sve_cmpgpr', 'sve_cmpvec',
    'sve_countelt', 'sve_crypto_binary_const', 'sve_crypto_binary_dest',
    'sve_crypto_unary', 'sve_fp_2op_i_p_zds', 'sve_fp_2op_p_pd', 'sve_fp_2op_p_vd',
    'sve_fp_2op_p_zd_a', 'sve_fp_2op_p_zd_b_0', 'sve_fp_2op_p_zd_b_1',
    'sve_fp_2op_p_zd_c', 'sve_fp_2op_p_zd_d', 'sve_fp_2op_p_zds',
    'sve_fp_2op_u_zd', 'sve_fp_3op_p_pd', 'sve_fp_3op_p_zds_a',
    'sve_fp_3op_p_zds_b', 'sve_fp_3op_u_zd', 'sve_fp_cmpzero', 'sve_fp_fast_red',
    'sve_fp_fcadd', 'sve_fp_fcmla', 'sve_fp_fcmla_by_indexed_elem', 'sve_fp_fcvt2',
    'sve_fp_fdot', 'sve_fp_fdot_by_indexed_elem', 'sve_fp_fma',
    'sve_fp_fma_by_indexed_elem', 'sve_fp_fma_long',
    'sve_fp_fma_long_by_indexed_elem', 'sve_fp_fma_w',
    'sve_fp_fma_w_by_indexed_elem', 'sve_fp_fmmla', 'sve_fp_fmul_by_indexed_elem',
    'sve_fp_ftmad', 'sve_fp_pairwise', 'sve_fp_pred', 'sve_fp_slowreduce',
    'sve_fp_unary', 'sve_fp_unary_unpred', 'sve_index', 'sve_int_arith_imm0',
    'sve_int_arith_imm1', 'sve_int_arith_imm2', 'sve_int_arith_vl',
    'sve_int_bin_cons_arit_0', 'sve_int_bin_cons_log', 'sve_int_bin_cons_misc_0_a',
    'sve_int_bin_cons_misc_0_b', 'sve_int_bin_cons_misc_0_c',
    'sve_int_bin_cons_misc_0_d', 'sve_int_bin_cons_shift_a',
    'sve_int_bin_cons_shift_b', 'sve_int_bin_pred_arit_0',
    'sve_int_bin_pred_arit_1', 'sve_int_bin_pred_arit_2', 'sve_int_bin_pred_div',
    'sve_int_bin_pred_log', 'sve_int_bin_pred_shift_0', 'sve_int_bin_pred_shift_1',
    'sve_int_bin_pred_shift_2', 'sve_int_break', 'sve_int_brkn', 'sve_int_brkp',
    'sve_int_cmp_0', 'sve_int_cmp_1', 'sve_int_count', 'sve_int_count_r',
    'sve_int_count_r_sat', 'sve_int_count_v', 'sve_int_count_v_sat',
    'sve_int_countvlv0', 'sve_int_countvlv1', 'sve_int_cterm', 'sve_int_dup_fpimm',
    'sve_int_dup_fpimm_pred', 'sve_int_dup_imm', 'sve_int_dup_imm_pred',
    'sve_int_dup_mask_imm', 'sve_int_index_ii', 'sve_int_index_ir',
    'sve_int_index_ri', 'sve_int_index_rr', 'sve_int_log_imm',
    'sve_int_mladdsub_vvv_pred', 'sve_int_mlas_vvv_pred', 'sve_int_movprfx_pred',
    'sve_int_mul_b', 'sve_int_muladd_pred', 'sve_int_pcount_pred',
    'sve_int_perm_bin_long_perm_zz', 'sve_int_perm_bin_perm_pp',
    'sve_int_perm_bin_perm_zz', 'sve_int_perm_clast_rz', 'sve_int_perm_clast_vz',
    'sve_int_perm_clast_zz', 'sve_int_perm_compact', 'sve_int_perm_cpy_r',
    'sve_int_perm_cpy_v', 'sve_int_perm_dup_i', 'sve_int_perm_dup_r',
    'sve_int_perm_extract_i', 'sve_int_perm_insrs', 'sve_int_perm_insrv',
    'sve_int_perm_last_r', 'sve_int_perm_last_v', 'sve_int_perm_punpk',
    'sve_int_perm_rev', 'sve_int_perm_revd', 'sve_int_perm_reverse_p',
    'sve_int_perm_reverse_z', 'sve_int_perm_splice', 'sve_int_perm_tbl',
    'sve_int_perm_tbl_3src', 'sve_int_perm_unpk', 'sve_int_pfalse',
    'sve_int_pfirst', 'sve_int_pnext', 'sve_int_pred_bin', 'sve_int_pred_dup',
    'sve_int_pred_log', 'sve_int_pred_pattern_a', 'sve_int_pred_pattern_b',
    'sve_int_pred_red', 'sve_int_pred_shift', 'sve_int_pred_un', 'sve_int_ptest',
    'sve_int_ptrue', 'sve_int_rdffr', 'sve_int_rdffr_2', 'sve_int_read_vl_a',
    'sve_int_reduce_0', 'sve_int_reduce_1', 'sve_int_reduce_2',
    'sve_int_rotate_imm', 'sve_int_scmp_vi', 'sve_int_sel_vvv', 'sve_int_setffr',
    'sve_int_sqdmulh', 'sve_int_tern_log', 'sve_int_ucmp_vi',
    'sve_int_un_pred_arit_0', 'sve_int_un_pred_arit_1', 'sve_int_unpred_arit_b',
    'sve_int_unpred_logical', 'sve_int_unpred_misc', 'sve_int_unpred_shift',
    'sve_int_while_rr', 'sve_int_whilenc', 'sve_int_wrffr', 'sve_intx_aba',
    'sve_intx_aba_long', 'sve_intx_acc', 'sve_intx_accumulate_long_pairs',
    'sve_intx_adc_long', 'sve_intx_arith_binary_pairs', 'sve_intx_arith_narrow',
    'sve_intx_bin_pred_shift_sat_round', 'sve_intx_by_indexed_elem',
    'sve_intx_cadd', 'sve_intx_cdot', 'sve_intx_cdot_by_indexed_elem',
    'sve_intx_clamp', 'sve_intx_clong', 'sve_intx_cmla',
    'sve_intx_cmla_by_indexed_elem', 'sve_intx_cons_arith_long',
    'sve_intx_cons_arith_wide', 'sve_intx_cons_mul_long', 'sve_intx_cons_widening',
    'sve_intx_constructive', 'sve_intx_crypto', 'sve_intx_dot',
    'sve_intx_dot_by_indexed_elem', 'sve_intx_eorx', 'sve_intx_extract_narrow',
    'sve_intx_histcnt', 'sve_intx_histseg', 'sve_intx_match', 'sve_intx_mixed_dot',
    'sve_intx_mixed_dot_by_indexed_elem', 'sve_intx_mla_by_indexed_elem',
    'sve_intx_mla_long_by_indexed_elem', 'sve_intx_mlal_long', 'sve_intx_mmla',
    'sve_intx_mul_by_indexed_elem', 'sve_intx_mul_long_by_indexed_elem',
    'sve_intx_muladd_unpred', 'sve_intx_narrowing', 'sve_intx_perm_bit',
    'sve_intx_perm_extract_i', 'sve_intx_perm_splice',
    'sve_intx_pred_arith_binary', 'sve_intx_pred_arith_binary_sat',
    'sve_intx_pred_arith_unary', 'sve_intx_predicated',
    'sve_intx_qdmla_long_by_indexed_elem', 'sve_intx_qdmlal_long',
    'sve_intx_qdmlalbt', 'sve_intx_qdmul_long_by_indexed_elem',
    'sve_intx_qdmulh_by_indexed_elem', 'sve_intx_qrdcmla_by_indexed_elem',
    'sve_intx_qrdmlah', 'sve_intx_qrdmlah_by_indexed_elem',
    'sve_intx_shift_insert', 'sve_intx_shift_long', 'sve_intx_shift_narrow',
    'sve_intx_sra', 'sve_maskimm', 'sve_mem32', 'sve_mem64', 'sve_mem_32b_fill',
    'sve_mem_32b_gld_sv_a', 'sve_mem_32b_gld_sv_b', 'sve_mem_32b_gld_vi',
    'sve_mem_32b_gld_vs', 'sve_mem_32b_gldnt_vs', 'sve_mem_32b_pfill',
    'sve_mem_32b_prfm_sv', 'sve_mem_32b_prfm_vi', 'sve_mem_64b_gld_sv',
    'sve_mem_64b_gld_sv2', 'sve_mem_64b_gld_vi', 'sve_mem_64b_gld_vs',
    'sve_mem_64b_gld_vs2', 'sve_mem_64b_gldnt_vs', 'sve_mem_64b_prfm_sv',
    'sve_mem_64b_prfm_sv2', 'sve_mem_64b_prfm_vi', 'sve_mem_cld_si',
    'sve_mem_cld_ss', 'sve_mem_cldff_ss', 'sve_mem_cldnf_si', 'sve_mem_cldnt_si',
    'sve_mem_cldnt_ss', 'sve_mem_cst_si', 'sve_mem_cst_ss', 'sve_mem_cstnt_si',
    'sve_mem_cstnt_ss', 'sve_mem_eld_si', 'sve_mem_eld_ss', 'sve_mem_est_si',
    'sve_mem_est_ss', 'sve_mem_ld_dup', 'sve_mem_ldqr_si', 'sve_mem_ldqr_ss',
    'sve_mem_prfm_si', 'sve_mem_prfm_ss', 'sve_mem_pspill', 'sve_mem_spill',
    'sve_mem_sst_sv2', 'sve_mem_sst_sv_a', 'sve_mem_sst_sv_b', 'sve_mem_sst_vi_a',
    'sve_mem_sst_vi_b', 'sve_mem_sst_vs2', 'sve_mem_sst_vs_a', 'sve_mem_sst_vs_b',
    'sve_mem_sstnt_32b_vs', 'sve_mem_sstnt_64b_vs', 'sve_memcld', 'sve_memst_cs',
    'sve_memst_nt', 'sve_memst_si', 'sve_memst_ss', 'sve_memst_ss2',
    'sve_perm_extract', 'sve_perm_pred', 'sve_perm_predicates',
    'sve_perm_unpred_d', 'sve_pred_count_a', 'sve_pred_count_b', 'sve_pred_gen_b',
    'sve_pred_gen_c', 'sve_pred_gen_d', 'sve_pred_wrffr', 'sve_wideimm_pred',
    'sve_wideimm_unpred', 'systeminstrs', 'systeminstrswithreg', 'systemmove',
    'systemresult', 'testbranch'
]

if __name__ == '__main__':
    root = algorithm.hierarchy(inputs, lambda a,b: b.startswith(a))
    print(root)
