import serial # pip install pyserial

def open_modem_send_command(fpath, command, **kwargs):

    readsize = kwargs.get('readsize', 1024)
    timeout = kwargs.get('timeout', 1.0)

    try:
        ser = serial.Serial(port=fpath, baudrate=115200, bytesize=serial.EIGHTBITS, parity=serial.PARITY_NONE, stopbits=serial.STOPBITS_ONE, timeout=timeout, write_timeout=5.0, rtscts=False, dsrdtr=False, xonxoff=False)

        ser.reset_input_buffer()
        ser.reset_output_buffer()

        ser.write(command.encode('ascii'))
        ser.flush()

        return ser.read(readsize).decode('ascii').strip()

    except Exception as e:
        print(e)

