#!/bin/bash

ffmpeg -ss 00:00:00 -i 440_sine.wav -t 00:00:00.25 -c copy 440_sine_trimmed.wav
ffmpeg -ss 00:00:00 -i 440_square.wav -t 00:00:00.25 -c copy 440_square_trimmed.wav
ffmpeg -ss 00:00:00 -i 440_triangle.wav -t 00:00:00.25 -c copy 440_triangle_trimmed.wav
ffmpeg -ss 00:00:00 -i 440_sawtooth.wav -t 00:00:00.25 -c copy 440_sawtooth_trimmed.wav
