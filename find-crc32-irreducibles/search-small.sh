#!/bin/bash

CRC_START=100000 CRC_END=1FFFFF gp ./search.gp &
CRC_START=200000 CRC_END=2FFFFF gp ./search.gp &
CRC_START=300000 CRC_END=3FFFFF gp ./search.gp &
CRC_START=400000 CRC_END=4FFFFF gp ./search.gp &
CRC_START=500000 CRC_END=5FFFFF gp ./search.gp &
CRC_START=600000 CRC_END=6FFFFF gp ./search.gp &
wait
