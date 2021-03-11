# python stuff
import codecs

# binja stuff
from binaryninja import binaryview, BinaryDataNotification
from binaryninjaui import View, ViewType, ViewFrame, HexEditor

# binja UI stuff
from PySide2.QtCore import Qt
from PySide2.QtWidgets import QScrollArea

class Rot13Notification(BinaryDataNotification):
	def __init__(self, viewY):
		self.viewY = viewY

	def data_written(self, view, offset, length):
		#print("data_written(offset=0x%X, length=0x%X)" % (offset, length))
		self.write_through(view, offset, length)

	def data_inserted(self, view, offset, length):
		#print("data_inserted(offset=0x%X, length=0x%X)" % (offset, length))
		self.write_through(view, offset, length)

	def write_through(self, view, offset, length):
		X = view.read(offset, length)
		Y = codecs.encode(X.decode('utf-8'), 'rot_13').encode('utf-8')
		self.viewY.write(offset, Y)

class Rot13View(QScrollArea, View):
	def __init__(self, parent, binaryView):
		QScrollArea.__init__(self, parent)

		View.__init__(self)
		View.setBinaryDataNavigable(self, True)
		self.setupView(self)

		# input and output, Y = ROT13(X)
		X = binaryView.read(0, len(binaryView))
		Y = codecs.encode(X.decode('utf-8'), 'rot_13').encode('utf-8')

		# store original binary view (X) and our translated binary view (Y)
		self.binaryViewX = binaryView
		self.binaryViewY = binaryview.BinaryView.new(Y)

		self.setWidgetResizable(True)
		self.hexWidget = HexEditor(self.binaryViewY, ViewFrame.viewFrameForWidget(self), 0)
		self.setWidget(self.hexWidget)

		# capture writes to translated binary view
		notification = Rot13Notification(self.binaryViewX)
		self.binaryViewY.register_notification(notification)

	# binja callbacks
	def getData(self):
		#print("getData()")
		return self.binaryViewY

	# filled in status bar "Selection: 0xd3 to 0xe4 (0x11 bytes)"
	def getCurrentOffset(self):
		return self.hexWidget.getCurrentOffset()
	def getSelectionOffsets(self):
		return self.hexWidget.getSelectionOffsets()
	def setCurrentOffset(self, offset):
		return self.hexWidget.setCurrentOffset()

	# navigate() called when feature map clicked
	def navigate(self, addr):
		return self.hexWidget.navigate(addr)

class Rot13ViewType(ViewType):
	def __init__(self):
		super(Rot13ViewType, self).__init__("Rot13", "Rot13")

	def getPriority(self, binaryView, filename):
		return 100 if filename.endswith('.rot13') else 1

	def create(self, binaryView, view_frame):
		return Rot13View(view_frame, binaryView)

ViewType.registerViewType(Rot13ViewType())
