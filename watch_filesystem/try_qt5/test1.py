#!/usr/bin/env python

# adapted from https://stackoverflow.com/questions/13518985/why-does-qfilesystemwatcher-work-for-directories-but-not-files-in-python

import sys
from PyQt5 import QtCore, QtWidgets

def directory_changed(path):
    print('Directory Changed: %s' % path)

def file_changed(path):
    print('File Changed: %s' % path)

app = QtWidgets.QApplication(sys.argv)

paths = [
    '/tmp/tmp.png',
    ]

fs_watcher = QtCore.QFileSystemWatcher(paths)
fs_watcher.directoryChanged.connect(directory_changed)
fs_watcher.fileChanged.connect(file_changed)

win = QtWidgets.QWidget()
win.resize(640, 480)
win.show()

sys.exit(app.exec_())
