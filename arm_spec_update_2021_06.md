Notes upgrading from 2021-03 to 2021-06.

adds new feature identifiers:

```
FEAT_F32MM
FEAT_F64MM
FEAT_SME
FEAT_SME_F64F64
FEAT_SME_I16I64
FEAT_SVE_AES
FEAT_SVE_BitPerm
FEAT_SVE_SHA3
FEAT_SVE_SM4
```

new feature checking functions:

```
HaveSME
HaveSMEF64F64
HaveSMEI16I64
```

removed encodings:

```
MOVS_and_p_p_pp
MOVS_orr_p_p_pp
NOTS_eor_p_p_pp
```

added encodings:

```
MOV_mova_z_p_rza_b
MOV_mova_z_p_rza_d
MOV_mova_z_p_rza_h
MOV_mova_z_p_rza_q
MOV_mova_z_p_rza_w
MOV_mova_za_p_rz_b
MOV_mova_za_p_rz_d
MOV_mova_za_p_rz_h
MOV_mova_za_p_rz_q
MOV_mova_za_p_rz_w
SMSTART_MSR_SI_pstate
SMSTOP_MSR_SI_pstate
addha_za_pp_z_32
addha_za_pp_z_64
addva_za_pp_z_32
addva_za_pp_z_64
bfmopa_za32_pp_zz_
bfmops_za32_pp_zz_
dup_p_p_pi_
fmopa_za32_pp_zz_16
fmopa_za_pp_zz_32
fmopa_za_pp_zz_64
fmops_za32_pp_zz_16
fmops_za_pp_zz_32
fmops_za_pp_zz_64
ld1b_za_p_rrr_
ld1d_za_p_rrr_
ld1h_za_p_rrr_
ld1q_za_p_rrr_
ld1w_za_p_rrr_
ldr_za_ri_
mova_z_p_rza_b
mova_z_p_rza_d
mova_z_p_rza_h
mova_z_p_rza_q
mova_z_p_rza_w
mova_za_p_rz_b
mova_za_p_rz_d
mova_za_p_rz_h
mova_za_p_rz_q
mova_za_p_rz_w
revd_z_p_z_
sclamp_z_zz_
smopa_za_pp_zz_32
smopa_za_pp_zz_64
smops_za_pp_zz_32
smops_za_pp_zz_64
st1b_za_p_rrr_
st1d_za_p_rrr_
st1h_za_p_rrr_
st1q_za_p_rrr_
st1w_za_p_rrr_
str_za_ri_
sumopa_za_pp_zz_32
sumopa_za_pp_zz_64
sumops_za_pp_zz_32
sumops_za_pp_zz_64
uclamp_z_zz_
umopa_za_pp_zz_32
umopa_za_pp_zz_64
umops_za_pp_zz_32
umops_za_pp_zz_64
usmopa_za_pp_zz_32
usmopa_za_pp_zz_64
usmops_za_pp_zz_32
usmops_za_pp_zz_64
zero_za_i_
```

pcode changes:

new datatype DSBAlias with values: {DSBAlias_DSB, DSBAlias_SSBB, DSBAlias_PSSBB}
new values for existing datatype PSTATEField: {PSTATEField_SVCRZA, PSTATEField_SVCRSM, PSTATEField_SVCRSMZA}

The spec is still inconsistent in its named partial bitfields. For example in encoding `and_z_p_zz` it uses angle brackets:

```
00000100|size=xx|011|opc<2:1>=01|opc<0>=0|000|Pg=xxx|Zm=xxxxx|Zdn=xxxxx
```

But in encoding `iclass_3reg_diff` it uses square brackets:

```
0|Q=x|U=0|01110|size=xx|1|Rm=xxxxx|opcode[3:2]=01|o1=0|opcode[0]=0|00|Rn=xxxxx|Rd=xxxxx
```


