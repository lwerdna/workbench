#!/bin/bash

set -x

# 36 bytes
# 288 bits
# 160 + 128 bits (SHA1 + MD5?)
# 04105fe2082bb1ec544102f3044b2ded700020e1 and 4e47d08b6917679070245fb53f5252e1
# 04105fe2082bb1ec544102f3044b2ded and 700020e14e47d08b6917679070245fb53f5252e1
 
cstool x16 04105fe2082bb1ec544102f3044b2ded700020e14e47d08b6917679070245fb53f5252e1
cstool x32 04105fe2082bb1ec544102f3044b2ded700020e14e47d08b6917679070245fb53f5252e1
cstool x64 04105fe2082bb1ec544102f3044b2ded700020e14e47d08b6917679070245fb53f5252e1
cstool arm 04105fe2082bb1ec544102f3044b2ded700020e14e47d08b6917679070245fb53f5252e1
cstool armbe 04105fe2082bb1ec544102f3044b2ded700020e14e47d08b6917679070245fb53f5252e1
cstool thumb 04105fe2082bb1ec544102f3044b2ded700020e14e47d08b6917679070245fb53f5252e1
cstool thumbbe 04105fe2082bb1ec544102f3044b2ded700020e14e47d08b6917679070245fb53f5252e1
cstool armv8 04105fe2082bb1ec544102f3044b2ded700020e14e47d08b6917679070245fb53f5252e1
cstool arm64 04105fe2082bb1ec544102f3044b2ded700020e14e47d08b6917679070245fb53f5252e1
cstool mips 04105fe2082bb1ec544102f3044b2ded700020e14e47d08b6917679070245fb53f5252e1
cstool ppc32 04105fe2082bb1ec544102f3044b2ded700020e14e47d08b6917679070245fb53f5252e1
cstool ppc32be 04105fe2082bb1ec544102f3044b2ded700020e14e47d08b6917679070245fb53f5252e1
cstool ppc64 04105fe2082bb1ec544102f3044b2ded700020e14e47d08b6917679070245fb53f5252e1
cstool ppc64be 04105fe2082bb1ec544102f3044b2ded700020e14e47d08b6917679070245fb53f5252e1
