#!/usr/bin/env python

import sys
import time
import logging
from watchdog.observers import Observer
from watchdog.events import LoggingEventHandler, FileSystemEventHandler

# globals
fpath = None
observer = None

def monitor_teardown():
    global observer
    if observer != None:
        observer.stop()
        #observer.join()
        observer = None

def monitor_setup():
    global fpath
    global observer

    monitor_teardown()

    event_handler = None
    if 1:
        event_handler = MyEventHandler()
    else:
        logging.basicConfig(level=logging.INFO,
                        format='%(asctime)s - %(message)s',
                        datefmt='%Y-%m-%d %H:%M:%S')

        event_handler = LoggingEventHandler()

    observer = Observer()
    observer.schedule(event_handler, fpath, recursive=True)
    observer.start()

class MyEventHandler(FileSystemEventHandler):
    def dispatch(self, event):
        breakpoint()

    def on_any_event(self, event):
        print('on_any_event()')
    def on_created(self, event):
        print('on_created()')
    def on_deleted(self, event):
        print('on_deleted()')
        # no further events will come in after this, so start a new watchdog to catch creation, etc.
        print('starting new monitor')
        monitor_teardown()
        monitor_setup()
    def on_modified(self, event):
        print('on_modified()')
    def on_moved(self, event):
        print('on_moved()')

if __name__ == "__main__":
    fpath = sys.argv[1]
    print('monitoring: -%s-' % fpath)

    monitor_setup()

    try:
        while True:
            time.sleep(1)
    except KeyboardInterrupt:
        pass

    monitor_teardown()

