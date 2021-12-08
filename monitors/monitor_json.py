#!/usr/bin/env python

# use Qt5 QScintilla to display syntax highlighted JSON
#
# https://stackoverflow.com/questions/57215171/syntax-highlighting-editor-with-pyqt5

# pip install PyQt5
# pip install QScintilla

import sys, os

import watchdog
import watchdog.events
import watchdog.observers

import PyQt5
from PyQt5 import QtWidgets, Qsci

JSON = """
"""

# globals
fpath = None
main_window = None
json_editor = None

class MyEventHandler(watchdog.events.FileSystemEventHandler):
    def on_any_event(self, event):
        global fpath
        global main_window
        print('on_any_event()')
        with open(fpath) as fp:
            json_editor.setText(fp.read())

class JSONEditor(Qsci.QsciScintilla):
    def __init__(self, parent=None):
        super().__init__(parent)
        self.setLexer(Qsci.QsciLexerJSON(self))
        self.setText(JSON)

if __name__ == "__main__":
    # filesystem watchdog
    fpath = '/tmp/tmp.json'
    if sys.argv[1:]:
        fpath = sys.argv[1]

    handler = MyEventHandler()
    observer = watchdog.observers.Observer()
    observer.schedule(handler, fpath, recursive=True)
    observer.start()

    # qt application
    app = QtWidgets.QApplication(sys.argv)
    w = QtWidgets.QWidget()
    layout = QtWidgets.QHBoxLayout(w)
    json_editor = JSONEditor()
    layout.addWidget(json_editor)
    w.resize(640, 480)
    w.show()
    qt_return_code = app.exec_()

    #
    observer.stop()
    observer.join()

    sys.exit(qt_return_code)

