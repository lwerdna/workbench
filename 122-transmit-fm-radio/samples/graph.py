#!/usr/bin/env python

# READ WAV FILE, GRAPH SAMPLES OF FIRST CHANNEL

import os
import sys
from struct import unpack

import matplotlib.pyplot as plt

def get_wav_ch1_samples(fpath):
    t = 0
    with open(sys.argv[1], 'rb') as fp:
        # consume riff chunk descriptor
        fp.read(12)
        #
        while True:
            # consume subchunk id
            id_ = fp.read(4)
            # act on the two critical subchunks
            if id_ == b'fmt ':
                _, _, n_ch, sample_rate, _, _, bits_per_sample = \
                    unpack('<IHHIIHH', fp.read(20))
                bytes_per_sample = bits_per_sample//8
                t_per_sample = 1/sample_rate
                assert bits_per_sample in [8, 16]
            elif id_ == b'data':
                size, = unpack('<I', fp.read(4))
                while size:
                    if bytes_per_sample == 1:
                        yield (t, fp.read(1))
                        fp.read(1)
                    elif bytes_per_sample == 2:
                        yield (t, unpack('<h', fp.read(2))[0])
                        fp.read(2)
                    size -= n_ch * bytes_per_sample
                    t += t_per_sample
                return
            else:
                size, = unpack('<I', fp.read(4))
                fp.read(size)

if __name__ == '__main__':
    xs = []
    ys = []
    for t, v in get_wav_ch1_samples(sys.argv[1]):
        xs.append(t)
        ys.append(v)

    plt.plot(xs, ys)
    plt.xlabel('Time (s)')
    plt.ylabel('Amplitude')
    plt.title('Waveform')
    plt.grid(True)
    plt.show()
