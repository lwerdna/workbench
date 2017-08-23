#!/bin/bash

set -x # echo commands out
set -e # exit on error

TOOLCHAIN=$NDK/toolchains/aarch64-linux-android-4.9/prebuilt/darwin-x86_64/bin/aarch64-linux-android-

AS=${TOOLCHAIN}as
LD=${TOOLCHAIN}ld
CC=${TOOLCHAIN}gcc
OBJDUMP=${TOOLCHAIN}objdump

CFLAGS=--sysroot=$NDK/platforms/android-26/arch-arm64/

$CC $CFLAGS hello.c -o hello

$OBJDUMP --disassemble hello

