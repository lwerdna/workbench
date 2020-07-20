#!/usr/bin/env python

import sys
import time
import simpleaudio as sa

def gen_square(freq):
	samples = 8000 # record in 1/8000 second increments
	data = [0]*samples

	t_cycle = 1/freq
	t_half = t_cycle/2
	t_step = 1/samples
	t = 0
	for sidx in range(samples):
		if t < t_half:
			data[sidx] = 0xff	# high
		else:
			data[sidx] = 0x0	# low

		t += t_step
		if t > t_cycle:
			t -= t_cycle
	
	#print('\n'.join([str(x) for x in data]))

	return bytes(data)

#import simpleaudio.functionchecks as fc
#fc.LeftRightCheck.run()
#sys.exit(-1)

audio_data = gen_square(440)
num_channels = 1
bytes_per_sample = 1
# supports 8000, 11025, 16000, 22050, 24000, 32000, 44100, 48000, 88200, 96000, 192000
sample_rate = 8000

play_obj = sa.play_buffer(audio_data, num_channels, bytes_per_sample, sample_rate)

print('start')
if 0:
	play_obj.wait_done()
else:
	time.sleep(3)
print('stop')
	

