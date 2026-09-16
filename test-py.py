import sys
print("start")
sys.stdout.flush()

from PyQt5.QtWidgets import QApplication
from PyQt5.uic import loadUi
print("imports OK")
sys.stdout.flush()

import boon
from boon import BooN
import netgraph
import matplotlib
from PyQt5.QtWebEngineWidgets import QWebEngineView
print("all imports OK")
sys.stdout.flush()

app = QApplication(sys.argv)
print("QApplication OK")
sys.stdout.flush()

import boonify
print("boonify OK")
sys.stdout.flush()

window = boonify.Boonify()
print("Boonify() OK")
sys.stdout.flush()

window.show()
print("show OK")
sys.stdout.flush()

sys.exit(app.exec_())