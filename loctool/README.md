NOTE: this project has been superseded by https://github.com/lwerdna/disassembler_arena/

## loctool: (libopcode tool) programmatically call the same disassembler objdump uses
* depends: libiberty, libbfd, libopcodes all from binutils

## setup
* get [binutils 2.30](https://ftp.gnu.org/gnu/binutils/binutils-2.30.tar.gz) and decompress.
* enter the libiberty directory, `./configure` `CFLAGS=-O3 make` then `cp libiberty.a /usr/local/lib`
* enter the bfd directory, edit configure and set all_targets=true then `./configure` `CFLAGS=-O3 make` `make install`
* enter the opcodes directory, edit configure and set all_targets=true then `./configure` `CFLAGS=-O3 make` `make install`

## compile/link
* `gcc loctool.c -o loctool -lopcodes -lbfd -liberty -lz`

## notes

from binutils-2.30/bfd/bfd.h there is bfd_arch_powerpc, etc.

or bfd_arch_XXX where XXX is:

m68k, vax, i960, or1k, sparc, spu, mips, i386, l1om, k1om, iamcu, we32k, tahoe,
i860, i370, romp, convex, m88k, m98k, pyramid, h8300, pdp11, plugin, powerpc,
rs6000, hppa, d10v, d30v, dlx, m68hc11, m68hc12, m9s12x, m9s12xg, z8k, h8500,
sh, alpha, arm, nds32, ns32k, w65, tic30, tic4x, tic54x, tic6x, tic80, v850,
v850_rh850, arc, m32r, mn10200, mn10300, fr30, frv, moxie, ft32, mcore, mep,
metag, ia64, ip2k, epiphany, mt, pj, avr, bfin, cr16, cr16c, crx, cris, riscv,
rl78, rx, s390, score, mmix, xstormy16, msp430, xc16x, xgate, xtensa, z80,
lm32, microblaze, tilepro, tilegx, aarch64, nios2, visium, wasm32, pru, last
