#!/usr/bin/env python

# split file path, monitor the directory, filter files that are not the filepath
#
# eg: /tmp/tmp.png
# monitor /tmp
# filter all events that are not file with path 'tmp.png'

import os
import sys
import time
import logging
from watchdog.observers import Observer
from watchdog.events import FileSystemEventHandler

class MyEventHandler(FileSystemEventHandler):
    def __init__(self, fname):
        self.fname = fname
    def on_any_event(self, event):
        #print('on_any_event()')
        pass
    def on_created(self, event):
        #print('on_created()')
        pass
    def on_deleted(self, event):
        #print('on_deleted()')
        pass
    def on_modified(self, event):
        #print('on_modified()')
        if not event.is_directory and event.src_path.endswith(fname):
            print('%s modified!' % self.fname)
    def on_moved(self, event):
        #print('on_moved()')
        pass

if __name__ == "__main__":
    fpath = sys.argv[1] if len(sys.argv) > 1 else '.'
    (dpath, fname) = os.path.split(fpath)

    event_handler = MyEventHandler(fname)
    observer = Observer()

    observer.schedule(event_handler, dpath)
    observer.start()
    try:
        while True:
            time.sleep(1)
    finally:
        observer.stop()
        observer.join()
