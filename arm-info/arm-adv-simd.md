History of ARM Advanced SIMD

In architecture **Armv6** it is called **SIMD extension**:

* operates on 32-bit general purpose ARM registers
* 8-bit/16-bit integer
* *2x16-bit/4x8-bit operations per instruction

In architecture Armv7-A it is called **NEON**:

* separate register bank, 32x64-bit NEON registers
* 8/16/32/64-bit integer
* single precision floating point
* Up to 16x8-bit operations per instruction

In architecture **Armv8-A**, AArch64 execution state, it is called **NEON** and grows to:

* separate register bank, 32x128-bit NEON registers (vs. 64-bit)
* 8/16/32/64-bit integer
* single precision floating point
* double precision floating point, both of them are IEEE compliant
* up to 16x8-bit operations per instruction