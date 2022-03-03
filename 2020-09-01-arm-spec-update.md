---
TITLE: ArmV8.6A 2020-03 to ARMv8.7A 2020-09
---

The following changes were observed upgrading the disassembler from `ArmV8.6A 2020-03` to `ArmV8.7A 2020-09`:

The new version removes the old encodings:

```
FMMLA_Z_ZZZ_S, UMMLA_Z_ZZZ_, LD1ROH_Z_P_BR_CONTIGUOUS, LD1ROD_Z_P_BR_CONTIGUOUS, UZP2_Z_ZZ_Q, USDOT_Z_ZZZI_S, LD1ROB_Z_P_BR_CONTIGUOUS, LD1ROH_Z_P_BI_U16, TRN1_Z_ZZ_Q, UZP1_Z_ZZ_Q, LD1ROD_Z_P_BI_U64, BFMLALB_Z_ZZZ_, USMMLA_Z_ZZZ_, BFMLALB_Z_ZZZI_, USDOT_Z_ZZZ_S, BFMLALT_Z_ZZZI_, BFDOT_Z_ZZZ_, SMMLA_Z_ZZZ_, SUDOT_Z_ZZZI_S, TRN2_Z_ZZ_Q, FMMLA_Z_ZZZ_D, ZIP1_Z_ZZ_Q, BFMLALT_Z_ZZZ_, ZIP2_Z_ZZ_Q, LD1ROW_Z_P_BR_CONTIGUOUS, BFDOT_Z_ZZZI_, BFCVTNT_Z_P_Z_S2BF, LD1ROW_Z_P_BI_U32, LD1ROB_Z_P_BI_U8, BFCVT_Z_P_Z_S2BF, BFMMLA_Z_ZZZ_
```

And adds these encodings:

```
WFET_ONLY_SYSTEMINSTRSWITHREG, ST64BV_64_MEMOP, ST64BV0_64_MEMOP, ST64B_64L_MEMOP, WFIT_ONLY_SYSTEMINSTRSWITHREG, DSB_BON_BARRIERS, LD64B_64L_MEMOP
```

Overall the encodings decreased from 2336 to 2312.

There are a few new pcode constructs: an `assert` statement and a new variable type Constraint. There's used in this common chunk of code appearing many times in many instructions:

```
c = ConstrainUnpredictable(Unpredictable_WBOVERLAPLD);
assert c IN {Constraint_WBSUPPRESS, Constraint_UNKNOWN, Constraint_UNDEF, Constraint_NOP};
case c of
when Constraint_WBSUPPRESS wback = FALSE;       // writeback is suppressed
when Constraint_UNKNOWN    wb_unknown = TRUE;   // writeback is UNKNOWN
when Constraint_UNDEF      UNDEFINED;
when Constraint_NOP        EndOfInstruction();
```

It appears completely worthless for disassembly, and I prune it from the tree before generating code.

Many features were renamed from ArmVX-YYY to FEAT_YYYY, like `ARMv8.4-LRCPC2` is now `FEAT_LRCPC2`. FPCR is now called FPCR[] for some reason.

This is a sample list of instructions from the new encodings:

```
// LD64B_64L_memop 1111100000111111110100xxxxxxxxxx
F83FD290 ld64b x16, [x20]
F83FD104 ld64b x4, [x8]
F83FD18A ld64b x10, [x12]
F83FD240 ld64b x0, [x18]
F83FD084 ld64b x4, [x4]
F83FD128 ld64b x8, [x9]
F83FD172 ld64b x18, [x11]
F83FD132 ld64b x18, [x9]
// ST64B_64L_memop 1111100000111111100100xxxxxxxxxx
F83F9104 st64b x4, [x8]
F83F9344 st64b x4, [x26]
F83F9220 st64b x0, [x17]
F83F90A4 st64b x4, [x5]
F83F90CE st64b x14, [x6]
F83F9240 st64b x0, [x18]
F83F926A st64b x10, [x19]
F83F90D6 st64b x22, [x6]
// ST64BV_64_memop 11111000001xxxxx101100xxxxxxxxxx
F833B24A st64bv x19, x10, [x18]
F830B226 st64bv x16, x6, [x17]
F820B06C st64bv x0, x12, [x3]
F83FB3E2 st64bv xzr, x2, [sp]
F82CB0C4 st64bv x12, x4, [x6]
F82FB076 st64bv x15, x22, [x3]
F827B10E st64bv x7, x14, [x8]
F83BB160 st64bv x27, x0, [x11]
// ST64BV0_64_memop 11111000001xxxxx101000xxxxxxxxxx
F832A2F6 st64bv0 x18, x22, [x23]
F820A0E8 st64bv0 x0, x8, [x7]
F820A194 st64bv0 x0, x20, [x12]
F823A236 st64bv0 x3, x22, [x17]
F831A3A0 st64bv0 x17, x0, [x29]
F83CA194 st64bv0 x28, x20, [x12]
F821A2A0 st64bv0 x1, x0, [x21]
F839A14A st64bv0 x25, x10, [x10]
// DSB_BOn_barriers 11010101000000110011xx1000111111
D5033E3F dsb synxs
D503363F dsb nshnxs
D503323F dsb oshnxs
D5033A3F dsb ishnxs
// WFET_only_systeminstrswithreg 110101010000001100010000000xxxxx
D503100F wfet x15
D5031004 wfet x4
D5031007 wfet x7
D5031001 wfet x1
D503100E wfet x14
D5031008 wfet x8
D5031014 wfet x20
D5031006 wfet x6
// WFIT_only_systeminstrswithreg 110101010000001100010000001xxxxx
D503103E wfit x30
D5031036 wfit x22
D503103C wfit x28
D503103A wfit x26
D5031027 wfit x7
D503102F wfit x15
D503102B wfit x11
D5031030 wfit x16
```

relevant links:

https://developer.arm.com/architectures/cpu-architecture/a-profile/exploration-tools

