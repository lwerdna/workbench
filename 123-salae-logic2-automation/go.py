#!/usr/bin/env python

import os
import sys
import struct
import pathlib

from saleae import automation

def parse_bins(*bins):
    fps = []
    states = []
    maximums = []

    for i,fpath in enumerate(bins):
        fp = open(fpath, 'rb')

        assert fp.read(8) == b'<SALEAE>' # identifier
        assert fp.read(4) == b'\x00\x00\x00\x00' # version
        assert fp.read(4) == b'\x00\x00\x00\x00' # type TYPE_DIGITAL
        state, = struct.unpack('<I', fp.read(4))
        assert state in [0, 1]
        begin_time, = struct.unpack('<d', fp.read(8))
        end_time, = struct.unpack('<d', fp.read(8))
        num_transitions, = struct.unpack('<Q', fp.read(8))
        assert num_transitions > 0

        print(f'channel {i} starts at {begin_time} in state {state}')

        fps.append(fp)
        states.append(state)

    # load the transition times
    transitions = []
    for fp in fps:
        transitions.append(struct.unpack('<d', fp.read(8))[0])

    running = True
    while running:
        # find next (earliest) transition
        t = min(transitions)
        chans = [i for i in range(len(transitions)) if transitions[i]==t]

        # for every channel that contains this transition time, toggle and advance it
        for chan in chans:
            # toggle that channel's state
            states[chan] = 0 if states[chan] else 1

        # yield all states
        yield [t] + states

        # seek next transition from those channels
        for chan in chans:
            data = fps[chan].read(8)
            if data == b'':
                running = False
            else:
                transitions[chan], = struct.unpack('<d', data)

    for fp in fps:
        fp.close()

def capture():
    script_dir = str(pathlib.Path(__file__).parent.resolve())

    with automation.Manager.connect(port=10430) as manager:
        device_configuration = automation.LogicDeviceConfiguration(
            enabled_digital_channels=[0, 1, 2, 3, 4, 5],
            digital_sample_rate=500_000_000,
            digital_threshold_volts=1.8,
            glitch_filters=[    automation.GlitchFilterEntry(0, .000000004),
                                automation.GlitchFilterEntry(1, .000000004),
                                automation.GlitchFilterEntry(2, .000000004),
                                automation.GlitchFilterEntry(3, .000000004),
                                automation.GlitchFilterEntry(4, .000000004),
                                automation.GlitchFilterEntry(5, .000000004) ]
        )

        if 0:
            # use timed capture
            capture_configuration = automation.CaptureConfiguration(
                capture_mode=automation.TimedCaptureMode(duration_seconds=5.0)
            )
        else:
            # use triggered capture
            capture_configuration = automation.CaptureConfiguration(
                capture_mode=automation.DigitalTriggerCaptureMode(
                    trigger_type=automation.DigitalTriggerType.RISING,
                    trigger_channel_index=0,
                    after_trigger_seconds=5
                )
            )

        # use device_id='F4241' for the demo device or omit it to use first real device
        with manager.start_capture(
                device_id='F4241',
                device_configuration=device_configuration,
                capture_configuration=capture_configuration) as capture:

            # Wait until the capture has finished
            # This will take about 5 seconds because we are using a timed capture mode
            capture.wait()
    
            # Finally, save the capture to a file
            fpath = os.path.join(script_dir, 'capture.sal')
            print(f'writing {fpath}')
            capture.save_capture(filepath=fpath)

            print(f'exporting raw data binaries to {script_dir}')
            capture.export_raw_data_binary(script_dir, digital_channels=[0,1,2,3,4,5])

    # end of "with" block... automatically does manager.close()

    fpath = 'capture.sal'
    print(f'opening {fpath}')

if __name__ == '__main__':
    if sys.argv[1:] and sys.argv[1] == 'capture':
        capture()
    elif sys.argv[1:] and sys.argv[1] == 'parse':
        fpaths = [f'digital_{i}.bin' for i in range(6)]

        for i, entry in enumerate(parse_bins(*fpaths)):
            print(f't={entry[0]:f} {entry[1:]}')

