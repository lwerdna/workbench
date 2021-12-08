#!/usr/bin/env python

import os, sys, re, pprint, time
import logging

import watchdog
import watchdog.events
import watchdog.observers

from PyQt5 import QtCore, QtWidgets
from PyQt5.QtWidgets import QMainWindow, QWidget, QLabel, QLineEdit
from PyQt5.QtWidgets import QPushButton
from PyQt5.QtCore import QSize  

# globals
fpath = None
main_window = None

class MyEventHandler(watchdog.events.FileSystemEventHandler):
    def on_any_event(self, event):
        global fpath
        global main_window
        print('on_any_event()')
        with open(fpath) as fp:
            first_line = fp.readlines()[0]
            main_window.line.setText(first_line)

class MainWindow(QMainWindow):
    def __init__(self):
        QMainWindow.__init__(self)

        self.setMinimumSize(QSize(320, 140))    
        self.setWindowTitle("PyQt Line Edit example (textfield) - pythonprogramminglanguage.com") 

        self.nameLabel = QLabel(self)
        self.nameLabel.setText('Name:')
        self.line = QLineEdit(self)

        self.line.move(80, 20)
        self.line.resize(200, 32)
        self.nameLabel.move(20, 20)

        pybutton = QPushButton('OK', self)
        pybutton.clicked.connect(self.clickMethod)
        pybutton.resize(200,32)
        pybutton.move(80, 60)        

    def clickMethod(self):
        print('Your name: ' + self.line.text())

if __name__ == '__main__':
    fpath = '/tmp/tmp.png'
    if sys.argv[1:]:
        fpath = sys.argv[1]
    print('monitoring %s' % fpath)

    handler = None
    handler = MyEventHandler()

    observer = watchdog.observers.Observer()
    observer.schedule(handler, fpath, recursive=True)
    observer.start()

    # run GUI
    app = QtWidgets.QApplication(sys.argv)
    main_window = MainWindow()
    main_window.show()
    qt_rc = app.exec_()

    observer.stop()
    observer.join()

