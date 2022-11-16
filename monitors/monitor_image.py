#!/usr/bin/env python

import os, sys, re, pprint, time
import logging

import watchdog
import watchdog.events
import watchdog.observers

from PyQt5 import QtCore
from PyQt5.QtWidgets import QApplication, QWidget, QLabel
from PyQt5.QtGui import QIcon, QPixmap

# globals
fpath = None
main_window = None

class MyEventHandler(watchdog.events.FileSystemEventHandler):
    def on_any_event(self, event):
        #global main_window
        print('on_any_event()')
        main_window.reload_image()

class MainWindow(QWidget):
    def __init__(self):
        super().__init__()
        self.title = 'PyQt5 image - pythonspot.com'
        self.left = 10
        self.top = 10
        self.width = 640
        self.height = 480
        self.initUI()
    
    def initUI(self):
        self.setWindowTitle(self.title)
        self.setGeometry(self.left, self.top, self.width, self.height)
    
        # Create widget
        self.label = QLabel(self)
        #pixmap = QPixmap('image.jpeg')
        #self.label.setPixmap(pixmap)
        self.show()

    def reload_image(self):
        global fpath
        pixmap = QPixmap(fpath)
        self.label.setPixmap(pixmap)
        self.label.resize(pixmap.width(), pixmap.height())
        self.label.show()

if __name__ == '__main__':
    fpath = '/tmp/tmp.png'
    if sys.argv[1:]:
        fpath = sys.argv[1]
    print('monitoring %s' % fpath)

    handler = MyEventHandler()
    observer = watchdog.observers.Observer()
    observer.schedule(handler, fpath, recursive=True)
    observer.start()

    app = QApplication(sys.argv)
    main_window = MainWindow()
    rc = app.exec_()

    observer.stop()
    observer.join()

    sys.exit(rc)
