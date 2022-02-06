#!/bin/bash

CRC_START=00000000 CRC_END=07FFFFFF gp --quiet ./search.gp &
CRC_START=08000000 CRC_END=0FFFFFFF gp --quiet ./search.gp &

CRC_START=10000000 CRC_END=17FFFFFF gp --quiet ./search.gp &
CRC_START=18000000 CRC_END=1FFFFFFF gp --quiet ./search.gp &

CRC_START=20000000 CRC_END=27FFFFFF gp --quiet ./search.gp &
CRC_START=28000000 CRC_END=2FFFFFFF gp --quiet ./search.gp &

CRC_START=30000000 CRC_END=37FFFFFF gp --quiet ./search.gp &
CRC_START=38000000 CRC_END=3FFFFFFF gp --quiet ./search.gp &

CRC_START=40000000 CRC_END=47FFFFFF gp --quiet ./search.gp &
CRC_START=48000000 CRC_END=4FFFFFFF gp --quiet ./search.gp &

CRC_START=50000000 CRC_END=57FFFFFF gp --quiet ./search.gp &
CRC_START=58000000 CRC_END=5FFFFFFF gp --quiet ./search.gp &

CRC_START=60000000 CRC_END=67FFFFFF gp --quiet ./search.gp &
CRC_START=68000000 CRC_END=6FFFFFFF gp --quiet ./search.gp &

CRC_START=70000000 CRC_END=77FFFFFF gp --quiet ./search.gp &
CRC_START=78000000 CRC_END=7FFFFFFF gp --quiet ./search.gp &

CRC_START=80000000 CRC_END=87FFFFFF gp --quiet ./search.gp &
CRC_START=88000000 CRC_END=8FFFFFFF gp --quiet ./search.gp &

CRC_START=90000000 CRC_END=97FFFFFF gp --quiet ./search.gp &
CRC_START=98000000 CRC_END=9FFFFFFF gp --quiet ./search.gp &

CRC_START=A0000000 CRC_END=A7FFFFFF gp --quiet ./search.gp &
CRC_START=A8000000 CRC_END=AFFFFFFF gp --quiet ./search.gp &

CRC_START=B0000000 CRC_END=B7FFFFFF gp --quiet ./search.gp &
CRC_START=B8000000 CRC_END=BFFFFFFF gp --quiet ./search.gp &

CRC_START=C0000000 CRC_END=C7FFFFFF gp --quiet ./search.gp &
CRC_START=C8000000 CRC_END=CFFFFFFF gp --quiet ./search.gp &

CRC_START=D0000000 CRC_END=D7FFFFFF gp --quiet ./search.gp &
CRC_START=D8000000 CRC_END=DFFFFFFF gp --quiet ./search.gp &

CRC_START=E0000000 CRC_END=E7FFFFFF gp --quiet ./search.gp &
CRC_START=E8000000 CRC_END=EFFFFFFF gp --quiet ./search.gp &

CRC_START=F0000000 CRC_END=F7FFFFFF gp --quiet ./search.gp &
CRC_START=F8000000 CRC_END=FFFFFFFF gp --quiet ./search.gp &

wait
