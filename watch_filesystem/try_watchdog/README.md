EDIT! It does work, you just can't point it at a file like I thought. Instead, you point it at the directory containing the file, and filter the path contained in the event. See monitor_file.py.

Watchdog doesn't fucking work (at least on macOS 11.4 x64).

# Failure #1
If you try to monitor a file without recursive (see ./watchdog\_sample\_nore.py) , NOTHING shows up:

```
$ ./watchdog_sample_nore.py /tmp/tmp.png
```

Then, from a different terminal:

```
touch /tmp/tmp.png
echo 'hi' > /tmp/tmp.png
cp /path/to/another.png /tmp/tmp.png
```

# Failure #2
Forced to use recursive, monitoring a file will report directory deletion:

```
$ ./watchdog_sample.py /tmp/tmp.png
```

Same commands now, or open in an image editor and make a change, and watchdog reports:

```
2021-12-09 11:36:34 - Modified file: /private/tmp/tmp.png
2021-12-09 11:36:42 - Modified file: /private/tmp/tmp.png
2021-12-09 11:37:19 - Modified file: /private/tmp/tmp.png
2021-12-09 11:37:29 - Modified file: /private/tmp/tmp.png
2021-12-09 11:37:29 - Modified file: /private/tmp/tmp.png
2021-12-09 11:37:30 - Modified file: /private/tmp/tmp.png
2021-12-09 11:37:50 - Deleted directory: /tmp/tmp.pn
```

What!?

