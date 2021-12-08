#!/usr/bin/env python

from PyQt5.QtWidgets import QApplication, QWidget, QPushButton, QFormLayout
app = QApplication([])
window = QWidget()
layout = QFormLayout()
layout.addRow('ButtonTop:', QPushButton('Top'))
layout.addRow('ButtonBottom:', QPushButton('Bottom'))
window.setLayout(layout)
window.show()
app.exec()
