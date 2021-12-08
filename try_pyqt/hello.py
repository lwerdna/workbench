#!/usr/bin/env python
# https://build-system.fman.io/pyqt5-tutorial

from PyQt5.QtWidgets import QApplication, QLabel

args = []
app = QApplication(args)
label = QLabel('Hello, World!')
label.show()
app.exec_()
