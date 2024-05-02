For a certain guest, to avoid illegal instruction, we had to add in tlib/arch/arm/helper.c:
case ARM_CPUID_CORTEXA9:
    ...
    set_feature(env, ARM_FEATURE_ARM_DIV // this

We can't do that for precompiled renode .deb, workaround?
Idea: test how guest detects this feature, intercept the instruction, and lie.

cp15 has ID regs like ID_PFR0, ID_PFR1, ID_ISAR1, ID_ISAR2, ...
Sample and compare them for good/bad renode, see ./sample/*

sysbus LoadBinary @/tmp/sample.bin 0x40008000
start
pause

BAD ONE:
dump 0x40009000 0x28
0x40009000 | 90 C0 0F 41 31 10 00 00 11 00 00 00 00 00 00 00 | ...A1...........
0x40009010 | 00 00 00 00 11 11 10 00 11 21 11 13 41 20 23 21 | .........!..A #!
0x40009020 | 31 21 11 11 42 11 11 00 00 00 00 00 00 00 00 00 | 1!..B...........

GOOD ONE:
dump 0x40009000 0x28
0x40009000 | 90 C0 0F 41 31 10 00 00 11 00 00 00 00 00 00 00 | ...A1...........
0x40009010 | 00 00 00 00 11 11 10 00 11 21 11 13 41 20 23 21 | .........!..A #!
0x40009020 | 31 21 11 11 42 11 11 00 00 00 00 00 00 00 00 00 | 1!..B...........

No difference!

These features are not advertised to the guest. They are renode/tlib internal:

    case 3:
        /* SDIV, UDIV */
        if (!arm_feature(env, ARM_FEATURE_ARM_DIV)) {
            goto illegal_op;
        }

