# Graphical interface for BooN design and analysis
# Author: Franck Delaplace
# Creation date: February 2024
# Co-author: Boomika SELVARADJOU -  New graphical interface
# Modification date: April 2026

#In comments:
#DEF means definition which is a code part gathering functions related to a process or an object definition,
#STEP means main steps
#WARNING is a warning.
#These terms can be used to color comments in PyCharm or else.

# Standard library imports
import sys
import os
import math
import re
import copy
import keyword
import numpy as np

# Third-party imports: import functions only used
import matplotlib as mpl
mpl.use("Qt5Agg")                                                                           #Select the Qt backend before pyplot is imported
import matplotlib.pyplot as plt
import networkx as nx

from sympy import SOPform, symbols
from sympy.core.symbol import Symbol
from sympy.logic.boolalg import is_cnf, is_dnf, is_nnf, to_dnf
from sympy.logic.boolalg import And, Not
from sympy.parsing.sympy_parser import parse_expr
from pulp import PULP_CBC_CMD

# PyQt5
from PyQt5 import QtCore, QtGui, QtWidgets
from PyQt5.QtWidgets import (QApplication, QMainWindow, QDialog, QWidget, QMenu, QWidgetAction, QFrame,
                             QGridLayout, QVBoxLayout, QHBoxLayout, QPushButton, QLabel, QLineEdit, QSlider,
                             QComboBox, QTableWidgetItem, QHeaderView, QMessageBox, QColorDialog,
                             QFileDialog, QInputDialog)
from PyQt5.QtGui import QIcon, QStandardItemModel, QStandardItem, QColor, QCursor
from PyQt5.QtCore import Qt, QSize, QUrl, QTimer
from PyQt5.QtCore import QObject, QThread, pyqtSignal, pyqtSlot
from PyQt5.QtWebEngineWidgets import QWebEngineView
from PyQt5.uic import loadUi

from matplotlib.patches import Rectangle, PathPatch, FancyArrowPatch
from matplotlib.path import Path
from tabulate import tabulate

# Local 
import boon
from boon import BooN, SIGNCOLOR, BOONSEP, PYTHONSKIP, PYTHONHEADER
import boon.logic as logic
from boon.logic import LOGICAL, SYMPY, MATHEMATICA, JAVA, BOOLNET

import BooNGui.booneries_rc  # noqa: F401 - registers the Qt resources (icons)

from matplotlib.backends.backend_qt5agg import FigureCanvasQTAgg as FigureCanvas
from matplotlib.figure import Figure

# Parameters
HSIZE: int = 10                                                                             #Size of the history
STYLE: dict = {"Logical": LOGICAL, "Java": JAVA, "Python": SYMPY, "Mathematica": MATHEMATICA, "BoolNet": BOOLNET}
ICON01: dict = {None: ":/icon/resources/none.svg", True: ":/icon/resources/true.svg", False: ":/icon/resources/false.svg"}  #True/False icons
MODELBOUND: int = 8                                                                         #Size bound of the dynamics model in terms of variables.
LPSOLVER = PULP_CBC_CMD                                                                     #LP-Solver related to the controllability resolution. (destify)

FORMULA_NAMES: set = {"True", "False", "And", "Or", "Not", "Xor", "Nand", "Nor",           #Non-variable names admitted in a formula typed in the View
                      "Implies", "Equivalent", "ITE", "true", "false"}
INTPAT: str = r"\s*-?[0-9]+\s*"                                                           #Integer regular expression
BASIC_FAMILY_COLOR : tuple[int, int, int ] = (1 ,1 ,1 )                                     #White: default/basic family color

TRACEGUI: bool = False                                                                         #Trace flag for debugging purposes. If True, prints the actions to the console.
def trace_gui(msg: str):
    """
    Prints a trace message to the console if the TRACEGUI flag is set to True.

    :param msg: The message to be printed.
    :type msg: str
    :return: None
    """
    if TRACEGUI:
        print(msg)


def is_valid_variable_name(name: str) -> bool:
    """
    Checks whether a string can be used as a BooN variable name.
    The name must be a Python identifier that is not a keyword, so that it can be converted into a single
    sympy Symbol and parsed back from a formula.

    :param name: The candidate name.
    :type name: str
    :return: True if the name is valid.
    :rtype: bool
    """
    return name.isidentifier() and not keyword.iskeyword(name)



class Boonify(QMainWindow):
    """
    Represents the main application window for managing and designing BooNs (Boolean Networks).
    Provides a GUI with a comprehensive set of functionalities. This class is primarily responsible for initializing
    and connecting GUI widgets, setting up callbacks, and constructing an editable graph
    for network interaction design.

    :ivar boon: The current Boolean Network object being managed or displayed.
    :type boon: BooN

    :ivar filename: The name of the file associated with the current BooN (empty if no file is loaded or saved).
    :type filename: str

    :ivar history: Maintains a history list of BooN objects for undo/redo functionalities.
    :type history: list

    :ivar hindex: The index of the last BooN added to the history.
    :type hindex: int

    :ivar hupdate: Flag indicating whether the history should be updated.
    :type hupdate: bool

    :ivar saved: Flag indicating if the current BooN has been saved.
    :type saved: bool

    :ivar QView: Widget for displaying BooN visualization.
    :type QView: QWidget | None

    :ivar QStableStates: Widget for displaying stable states of BooNs.
    :type QStableStates: QWidget | None

    :ivar QModel: Widget for displaying the dynamic model of the BooN.
    :type QModel: QWidget | None

    :ivar QControllability: Widget for displaying BooN controllability analysis.
    :type QControllability: QWidget | None

    :ivar editgraph: Editable graphical representation of the BooN's interaction graph.
    :type editgraph: EditableGraph | None

    :ivar disablecallback: Flag indicating whether design callbacks are disabled.
    :type disablecallback: bool

    :ivar designsize: Scaling factor related to graphics elements in the EditableGraph.
    :type designsize: float

    :ivar worker: Background thread for processing long-running BooN operations.
    :type worker: Threader

    :ivar canvas: Matplotlib canvas for rendering the network design figure in the GUI.
    :type canvas: FigureCanvas
    """

    #DEF: Main Window Initialization
    def __init__(self):
        super(Boonify, self).__init__()

        #STEP: Load Qt interface
        ui_path = os.path.join(os.path.dirname(__file__), 'BooNGui', 'boonify.ui')
        loadUi(ui_path, self)
        self.setGeometry(600, 100, 800, 800)

        #STEP: Configure main application window
        self.setMinimumSize(0, 0)
        self.setContextMenuPolicy(QtCore.Qt.PreventContextMenu)                             #Disable default Qt toolbar context menu (show/hide toolbars)

        #STEP: Initialize the Gui state
        self.boon = BooN()                                                                  #Current BooN
        self.network = Network()                                                            #Network conversion/management helper     
        self.filename = ""                                                                  #Current filename

        #STEP: Initialize undo/redo history             
        self.history = [None] * HSIZE                                                       #History of BooN snapshots
        self.color_history = [None] * HSIZE                                                 #History of edge_family_colors snapshots (parallel to history)
        self.hindex = 0                                                                     #Index of the last BooN added in the history.
        self.undo_depth = 0                                                                 #Number of steps currently undone (0 = at tip; max HSIZE-1)

        self.hupdate = False                                                                #Flag determining whether the history is updated.
        self.saved = True                                                                   #Flag determining whether the current BooN is saved.

        #STEP: Initialize widgets               
        self.QView = None                                                                   #View BooN
        self.QStableStates = None                                                           #Stable states
        self.QModel = None                                                                  #Dynamics model
        self.QControllability = None                                                        #Controllability

        #STEP: Initialize graph editor configuration                
        self.disablecallback = True                                                         #Temporarily disable graph callbacks during initialization
        self.designsize = 2.                                                                #Reference size used for graph rendering and scaling
        self.zoom_factor = 1.0                                                              #Current canvas zoom factor

        self.edge_source = None                                                             #Source node selected when creating an edge
        self.edge_family_colors = {}                                                        #Mapping from edge (u, v) to its family RGB color
        self.default_edge_sign = 1                                                          #Default edge sign (1 = green/activation, -1 = red/inhibition)
        self.edge_preview_target = None                                                     #Temporary target node used during edge creation preview

        #STEP: Connect internal callbacks               
        self.setup_callbacks()              

        self.display_saved_flag()                                                           #Show the save-state indicator in the status bar

        #STEP: Connect callback functions to Menu actions
        #File Management
        self.ActionOpen.triggered.connect(self.open)
        self.ActionSave.triggered.connect(self.save)
        self.ActionSaveAs.triggered.connect(self.saveas)
        self.ActionImport.triggered.connect(self.importation)
        self.ActionExport.triggered.connect(self.exportation)
        self.ActionQuit.triggered.connect(self.quit)

        #Help and History
        self.ActionHelp.triggered.connect(self.help)
        self.ActionUndo.triggered.connect(self.undo)
        self.ActionRedo.triggered.connect(self.redo)

        #Network Analysis
        self.ActionView.triggered.connect(self.view)
        self.ActionModel.triggered.connect(self.model)
        self.ActionStableStates.triggered.connect(self.stablestates)
        self.ActionControllability.triggered.connect(self.controllability)

        #STEP: Initialize the background worker thread
        self.worker = Threader()

        #STEP: Initialize the Matplotlib Canvas for network design
        fig = plt.figure()
        manager = fig.canvas.manager                                                        #Figure manager required by the graph editor(plt)

        self.canvas = FigureCanvas(fig)
        self.canvas.axes = self.canvas.figure.add_subplot(111)
        
        self.canvas.figure.subplots_adjust(left=0, bottom=0, right=1, top=1)                #Adjust the window for drawing area to fully occupy the canvas
        self.canvas.figure.canvas.manager = manager                                         #Assign the manager in the canvas to be accessible by EditGraph

        #STEP: Create graph editor attached to the canvas
        self.graph_editor = Graph(self.canvas)
        self.graph_editor._boonify_parent = self                                            #Back-reference for history callbacks

        self.graph_editor.graph_changed.connect(self.on_graph_changed)                      #Notify application whenever the graph structure changes

        #STEP: Insert canvas into GUI layout
        self.DesignCanvas.addWidget(self.canvas)

        #STEP: Initialize the graph editor from the current BooN
        self.graph_editor.setup_design(self.boon)

        self.disablecallback = False                                                        #Enable callbacks after initialization is complete

        #STEP: Enable key_press_event on canvas
        self.canvas.setFocusPolicy(QtCore.Qt.ClickFocus)
        self.canvas.setFocus()
        
        #STEP: Connect mouse and keyboard events
        self.canvas.mpl_connect('button_press_event', self.graph_editor.on_canvas_press)
        self.canvas.mpl_connect('button_release_event', self.graph_editor.on_canvas_release)
        self.canvas.mpl_connect('motion_notify_event', self.graph_editor.on_canvas_motion)
        self.canvas.mpl_connect('key_press_event', self.graph_editor.on_key_press)

        #STEP: Graph editing actions
        self.actionRenameNode.triggered.connect(self.graph_editor.rename_node)
        self.actionDelete.triggered.connect(self.graph_editor.delete_selection)
        self.actionZoomIn.triggered.connect(self.graph_editor.zoom_in)
        self.actionZoomOut.triggered.connect(self.graph_editor.zoom_out)

        #STEP: Edge Sign selection actions
        self.actionEdgePlus.triggered.connect(lambda: self.graph_editor.set_default_edge_sign(1))
        self.actionEdgeMinus.triggered.connect(lambda: self.graph_editor.set_default_edge_sign(-1))

        #STEP: Initialize the edge family color menu
        self.graph_editor.setup_color_menu(self)        
        self.actionFamilyColor.triggered.connect(self.graph_editor.open_color_palette)      #Open color palette for family color assignment

        #STEP: Initialize node resize menu
        self.graph_editor.setup_resize_menu(self)
        self.actionResizeNode.triggered.connect(self.graph_editor.open_resize_menu)         #Open node resize menu for adjusting node sizes


    def on_graph_changed(self):
        """
        Update the BooN model after a graph editor modification.

        Converts the current graph representation into a BooN object, records the change in the history,
        and refreshes all open views.

        :return: None
        """
        if self.disablecallback:                                                            #Ignore graph_changed signals fired during undo/redo or history updates
            return

        self.boon = self.network.graph_to_boon(
            self.graph_editor,
            current_boon=self.boon
        )
        self.graph_editor.boon = self.boon                                                  #Keep the editor bound to the current BooN (positions and meta are written into it)
        self.graph_editor._sync_node_sizes_to_boon()                                        #Complete boon.meta (family colors) before the snapshot is recorded

        #STEP: Record the modification in the undo/redo history
        self.add_history()

        #STEP: Refresh all visible views and analysis windows
        self.refresh()

    def update_from_formulas(self):
        """
        Propagates a modification of the BooN formulas made outside the graph editor (View, DNF conversion,
        control actions): records the change in the history, rebuilds the graph editor and refreshes all views.

        :return: None
        """
        self.disablecallback = True                                                         #setup_design must not trigger a graph -> BooN conversion
        try:
            self.graph_editor.setup_design(self.boon)                                       #Rebuild the graph from the new formulas
            self.graph_editor._sync_node_sizes_to_boon()                                    #Keep boon.meta consistent with the rebuilt editor
            self.add_history()
        finally:
            self.disablecallback = False
        self.refresh()

    def setup_callbacks(self):
        """
        Connect internal application signals to their corresponding handlers.
        If the graph editor has already been created, connect its `graph_changed` signal to the synchronization callback.

        :return: None
        """
        #STEP: Connect graph editor notifications to the BooN synchronization handler
        if hasattr(self, "graph_editor"):
            self.graph_editor.graph_changed.connect(self.on_graph_changed)

    #DEF: File management
    def open(self):
        """
        Opens a file using a file dialog, loads its contents, and updates the application state.
        Presents a file dialog filtered to .boon files. After a successful selection, loads the BooN,
        refreshes all open views, reinitializes the graph editor, and resets the undo/redo history.

        :return: None
        """
        filename, _ = QFileDialog.getOpenFileName(self, "Open file", "", "Boon Files (*.boon);; All Files (*);;")
        if not filename:                                                                    #Dialog cancelled
            return

        try:
            boon_loaded = BooN.load(filename)                                               #Load the BooN from selected file
        except Exception as e:
            QMessageBox.critical(self, "Open error", f"The file cannot be loaded:\n{e}")
            return

        self.filename = filename
        self.set_boon(boon_loaded)

    def set_boon(self, new_boon):
        """
        Installs a new BooN (after opening or importing a file): refreshes the views, rebuilds the graph editor
        and resets the undo/redo history.

        :param new_boon: The BooN to install.
        :type new_boon: BooN
        :return: None
        """
        self.boon = new_boon
        self.graph_editor.edge_family_colors = {}                                           #Clear previous file's colors so setup_design restores from the new boon.meta
        self.graph_editor.setup_design(self.boon)                                           #Rebuild the graph editor from the new BooN
        self.refresh()                                                                      #Refresh all open analysis views
        self.history_raz()                                                                  #Reset undo/redo history to the new state

    def save(self):
        """
        Saves the current BooN to the existing file, or delegates to saveas() if no file is set.
        If self.filename is already defined, the BooN is saved in place and the saved-state indicator is updated. 
        If no filename exists yet (e.g. new unsaved network), the Save As dialog is opened.

        :return: None
        """
        if self.filename:
            self.graph_editor._sync_node_sizes_to_boon()                                   #Flush node_sizes, node_label_top, and edge_family_colors into boon.meta before writing
            try:
                self.boon.save(self.filename)
            except OSError as e:
                QMessageBox.critical(self, "Save error", f"The file cannot be saved:\n{e}")
                return
            self.display_saved_flag()                                                       #Mark the BooN as saved in the status bar
        else:
            self.saveas()                                                                   #No filename yet: delegate to Save As dialog

    def saveas(self):
        """
        Opens a Save As dialog and saves the current BooN to the chosen file.
        Updates self.filename with the selected path and refreshes the saved-state indicator.
        Does nothing if the dialog is cancelled.

        :return: None
        """
        filename, _ = QFileDialog.getSaveFileName(self, "Save", "", "Boon Files (*.boon);; All Files (*);;")
        if not filename:                                                                    #Dialog cancelled
            return
        self.filename = filename
        self.save()

    def importation(self):
        """
        Imports a BooN from an external file format and updates the application state.
        Supported formats are BoolNet (.bnet), Python/SymPy (.txt), and SBML (.sbml, .xml).
        After a successful import, self.filename is cleared because the BooN is not stored in the native .boon format. 
        All open views are refreshed and the history is reset. An error dialog is shown if the file extension isn't recognised.

        :return: None
        """
        filename, _ = QFileDialog.getOpenFileName(self, "Import from files", "", "Text or SBML Files (*.bnet *.txt *.xml *.sbml);; All Files (*);;")
        if not filename:                                                                    #Dialog cancelled
            return

        extension = os.path.splitext(filename)[1].lower()
        try:
            #STEP: Dispatch to the appropriate import function based on file extension
            match extension:
                case ".bnet":                                                               #BoolNet format
                    imported = BooN.from_textfile(filename)
                case ".txt":                                                                #Python format
                    imported = BooN.from_textfile(filename, sep=BOONSEP, assign='=', ops=SYMPY, skipline=PYTHONSKIP)
                case ".sbml" | ".xml":                                                      #SBML format
                    imported = BooN.from_sbmlfile(filename)
                case _:                                                                     #Unknown extension: show error and keep the current BooN
                    QMessageBox.critical(self, "File extension error", f"The extension is unknown. \nFound {extension}\nAdmitted extension: .txt, .bnet, .sbml, .xml")
                    return
        except Exception as e:
            QMessageBox.critical(self, "Import error", f"The file cannot be imported:\n{e}")
            return

        self.filename = ""                                                                  #No file name since the BooN is not saved in the internal format.
        self.set_boon(imported)

    def exportation(self):
        """
        Exports the current BooN to an external file format via a Save dialog.
        Supported formats are BoolNet (.bnet) and Python/SymPy (.txt). 
        The export format is determined automatically from the chosen file extension.

        An error dialog is shown if the extension is unsupported or if writing fails.

        :return: None
        """
        filename, _ = QFileDialog.getSaveFileName(self, "Export to BoolNet or Python format.", "", "Text Files (*.bnet *.txt);;")
        if not filename:                                                                    #Dialog cancelled
            return

        extension = os.path.splitext(filename)[1].lower()
        try:
            #STEP: Dispatch to the appropriate writer based on file extension.
            match extension:
                case ".bnet":                                                               #BoolNet format
                    self.boon.to_textfile(filename)
                case ".txt":                                                                #Python/SymPy format
                    self.boon.to_textfile(filename, sep=BOONSEP, assign='=', ops=SYMPY, header=PYTHONHEADER)
                case _:                                                                     #Unknown extension: show error
                    QMessageBox.critical(self, "File extension error", f"Unsupported file extension: {extension}\nAdmitted extension: .bnet, .txt")
        except Exception as e:
            QMessageBox.critical(self, "Export error", f"The file cannot be exported:\n{e}")

    def confirm_quit(self) -> bool:
        """
        Asks the user what to do with unsaved changes before quitting.
        If the BooN is already saved, quitting is accepted immediately. Otherwise a dialog
        offers three choices: Save then quit, Quit without saving, or Cancel.
        Choosing Save but cancelling the Save As dialog aborts the quit, so no work is lost.

        :return: True if the application may quit.
        :rtype: bool
        """
        #STEP: Exit directly if there are no unsaved changes.
        if self.saved:
            return True

        #STEP: Ask the user what to do with the unsaved BooN.
        reply = QMessageBox.question(
            self,
            "Quit",
            "Are you sure you want to quit? \nThe BooN is not saved.",
            QMessageBox.Save | QMessageBox.Close | QMessageBox.Cancel,
            QMessageBox.Save)
        match reply:
            case QMessageBox.Save:                                                          #Save the BooN before quitting
                self.save()
                return self.saved                                                           #False if the save was cancelled or failed
            case QMessageBox.Close:                                                         #Quit without saving the BooN
                return True
            case _:                                                                         #Cancel (or dialog closed): return to application
                return False

    def quit(self):
        """
        Terminates the application after confirmation (see confirm_quit).

        :return: None
        """
        self.close()                                                                        #closeEvent performs the confirmation

    #noinspection PyMethodOverriding
    def closeEvent(self, event):
        """
        Handles the close event for the application window (menu Quit or window close button).
        The event is accepted only if the user confirms; the background worker thread is then stopped.

        :param event: The Qt close event triggered when the user closes the window.
        :type event: QCloseEvent

        :return: None
        """
        if self.confirm_quit():
            self.worker.quit()                                                              #Stop the worker thread cleanly
            event.accept()
            QApplication.instance().quit()                                                  #Also close the auxiliary windows
        else:
            event.ignore()

    #DEF: History management
    def history_raz(self):
        """
        Resets both BooN history and color history, then records the current state as the first entry.
        Called after loading or importing a file to start a fresh undo/redo stack from the new state.
        Resets ``history``, ``color_history``, ``hindex``, and ``hupdate`` to their initial values.

        :return: None
        """
        self.history = [None] * HSIZE                                                       #Clear all BooN snapshots from history
        self.color_history = [None] * HSIZE                                                 #Clear all edge_family_colors snapshots from color history
        self.hindex = 0                                                                     #Reset history index to 0   
        self.undo_depth = 0                                                                 #Reset undo depth after history clear
        self.add_history()                                                                  #Record the current state as the initial history entry
        self.hupdate = False                                                                #Reset the history update flag after recording the initial state
        self.display_saved_flag()                                                           #Update the saved-state in the status bar    

    def undo(self):
        """
        Restores the previous BooN and edge family colors from the parallel history stacks.
        Moves the history cursor one step back. Edge colors are restored before setup_design so the graph redraw 
        immediately uses the correct color state.
        Stops at the oldest recorded state (up to HSIZE-1 steps back) and never wraps around.

        :return: None
        """
        if self.undo_depth >= HSIZE - 1:                                                    #Already at the oldest possible state: cannot go further back
            return
        hindex = (self.hindex - 1) % HSIZE                                                  #Compute the previous history index
        
        if self.history[hindex] is None:                                                    #Slot is empty: beginning of history reached
            return
        
        self.disablecallback = True                                                         #Prevent graph callbacks from triggering during restore
        self.boon = self.history[hindex].copy()
        self.boon.meta = copy.deepcopy(getattr(self.history[hindex], "meta", None) or {})   #Force deep-copy meta from snapshot: boon.copy() may drop monkey-patched attrs
        self.graph_editor.edge_family_colors = dict(self.color_history[hindex] or {})       #Restore edge family colors before redrawing
        self.hindex = hindex                                                                #Move history index back to the restored state
        self.undo_depth += 1                                                                #Track how many steps back we are from the tip
        self.refresh()                                                                      #Refresh all open views to reflect the restored state
        self.graph_editor.setup_design(self.boon)
        self.graph_editor.refresh_next_node_id()
        self.disablecallback = False                                                        #Re-enable graph callbacks after restore is complete

    def redo(self):
        """
        Restores the next BooN and edge family colors from the parallel history stacks.
        Moves the history cursor one step forward. Edge colors are restored before setup_design
        so the graph redraw immediately uses the correct color state.
        Stops at the most recent state and never wraps around.

        :return: None
        """
        if self.undo_depth <= 0:                                                            #Already at the most recent state: nothing to redo
            return
        hindex = (self.hindex + 1) % HSIZE                                                  #Compute the next history index

        if self.history[hindex] is None:                                                    #Slot is empty: no future state recorded
            return
        
        self.disablecallback = True                                                         #Prevent graph callbacks from triggering during restore
        self.boon = self.history[hindex].copy()
        self.boon.meta = copy.deepcopy(getattr(self.history[hindex], "meta", None) or {})   #Force deep-copy meta from snapshot: boon.copy() may drop monkey-patched attrs
        self.graph_editor.edge_family_colors = dict(self.color_history[hindex] or {})       #Restore edge family colors before redrawing
        self.hindex = hindex                                                                #Move history index forward to the restored state
        self.undo_depth -= 1                                                                #One step closer to the tip
        self.refresh()                                                                      #Refresh all open views to reflect the restored state
        self.graph_editor.setup_design(self.boon)
        self.graph_editor.refresh_next_node_id()
        self.disablecallback = False                                                        #Re-enable graph callbacks after restore is complete

    def add_history(self):
        """
        Records the current BooN and edge_family_colors into the parallel history stacks if the BooN descriptor 
        has changed since the last recorded entry.

        Both self.history (BooN snapshots) and self.color_history (edge_family_colors snapshots) are always 
        advanced together so their indices stay in sync.
        .. warning::

            BooN equality is based on descriptors only (see ``BooN.__eq__``).
            Color-only changes do NOT create a new entry here: use add_color_history() for those.

        :return: None
        """
        hindex = self.hindex

        #STEP: Record only if the BooN has changed
        if self.boon != self.history[hindex]:
            self.disablecallback = True                                                     #Prevent graph callbacks from triggering during history update   
            self.hupdate = True                                                             #Signal to indicate a new entry was recorded    
            hindex = (hindex + 1) % HSIZE                                                   #Move history index to next slot
            self.history[hindex] = self.boon.copy()                                         #Record a copy of the current BooN in the history
            self.history[hindex].meta = copy.deepcopy(getattr(self.boon, "meta", None) or {})  #Force deep-copy meta: boon.copy() may drop monkey-patched attrs
            _efc = getattr(self.graph_editor, "edge_family_colors", {})
            _nl  = getattr(self.graph_editor, "node_labels", {})
            self.color_history[hindex] = {                                                  #Store colors keyed by (label, label) strings — stable across setup_design ID reassignment
                (_nl.get(u, u), _nl.get(v, v)): c for (u, v), c in _efc.items()
            }
            self.undo_depth = 0                                                             #New action recorded: reset undo depth so redo is no longer available
            self.hindex = hindex
            if self.history[hindex] and self.history[hindex].desc:
                self.display_saved_flag(False)                                              #Mark the BooN as unsaved after structural change
            self.disablecallback = False
        else:
            self.hupdate = False                                                            #No change: leave history entry unchanged

    def add_color_history(self, boon_snapshot=None):
        """
        Records a color-only change into both parallel history stacks.
        Called by set_edge_color_from_palette, set_family_color, and node-resize operations after
        updating edge_family_colors / node_sizes / node_label_top, when the BooN descriptor itself
        has not changed.
        A new slot is created only if something actually differs from the last recorded snapshot,
        so making the same change twice produces only one history entry.

        :return: None
        """
        _efc = getattr(self.graph_editor, "edge_family_colors", {})
        _nl  = getattr(self.graph_editor, "node_labels", {})
        current_colors = {                                                                  #Store colors keyed by (label, label) strings — stable across setup_design ID reassignment
            (_nl.get(u, u), _nl.get(v, v)): c for (u, v), c in _efc.items()
        }
        current_pos = dict(getattr(self.boon, "pos", {}) or {})
        hindex = self.hindex

        last_pos = dict(getattr(self.history[hindex], "pos", {}) or {}) if self.history[hindex] else {}

        #STEP: Also compare node_sizes and node_label_top stored in boon.meta
        current_meta = getattr(self.boon, "meta", None) or {}
        last_meta = getattr(self.history[hindex], "meta", None) or {} if self.history[hindex] else {}
        current_sizes = current_meta.get("node_sizes", {})
        last_sizes = last_meta.get("node_sizes", {})
        current_label_top = current_meta.get("node_label_top", False)
        last_label_top = last_meta.get("node_label_top", False)

        unchanged = (
            current_colors == self.color_history[hindex]
            and current_pos == last_pos
            and current_sizes == last_sizes
            and current_label_top == last_label_top
        )
        if unchanged:                                                                        #Nothing changed: no new entry recorded
            return 
        
        self.disablecallback = True                                                         #Prevent graph callbacks from triggering during history update      
        hindex = (hindex + 1) % HSIZE                                                       #Move history index to next slot
        _src_boon = boon_snapshot or self.boon
        self.history[hindex] = _src_boon.copy()
        self.history[hindex].meta = copy.deepcopy(getattr(_src_boon, "meta", None) or {})   #Force deep-copy meta: boon.copy() may drop monkey-patched attrs
        self.color_history[hindex] = current_colors                                         #Record the new color snapshot in the parallel color history
        self.hindex = hindex
        self.undo_depth = 0                                                                 #New action recorded: reset undo depth so redo is no longer available
        self.display_saved_flag(False)                                                      #Mark the BooN as unsaved after color change
        self.disablecallback = False

    def show_history(self):
        """
        Displays the entire history of changes, showing each entry formatted according to its identifier 
        and rendering logic using a tabulated structure. The current history index is highlighted, and 
        associated data details are presented using a plain tabular format. If a history entry lacks data,
        it displays a placeholder.

        :return: None
        """
        view = []
        for i, theboon in enumerate(self.history):
            label = [i] if i == self.hindex else i                                          #Wrap current index to highlight it in the table
            content = (tabulate([(var, logic.prettyform(eq, theboon.style)) for var, eq in theboon.desc.items()], tablefmt='plain')
                       if theboon is not None else '-')                                     #Show equations or placeholder if no BooN in this slot
            view.append((label, content))
        os.system('cls' if os.name == 'nt' else 'clear')                                    #Clear console before printing the history view
        print(tabulate(view, tablefmt='grid'))

    def refresh(self):
        """
        Refreshes all visible components, such as BooN View, Stable States View, Model View, and Controllability
        View. Each visible component is reinitialized or updated via its relevant function. This ensures that 
        all active components reflect the most current state.

        :return: None
        """
        if self.QView and self.QView.isVisible():                                           #Refresh the BooN View if opened.
            self.QView.initialize_view()
        if self.QStableStates and self.QStableStates.isVisible():                           #Refresh the stable states View if opened.
            self.QStableStates.stablestates()
        if self.QModel and self.QModel.isVisible():                                         #Refresh the Model view if opened.
            if len(self.boon.variables) > MODELBOUND:                                       #Model too large: close the view instead of computing it
                self.QModel.close()
                QMessageBox.warning(self, "No Model", f"The number of variables exceeds {MODELBOUND}.\nThe model view is closed.")
            else:
                self.QModel.modeling()
        if self.QControllability and self.QControllability.isVisible():                     #Refresh the Controllability View if opened.
            self.QControllability.initialize_controllability()

    #DEF: Widgets opening
    def help(self):
        """
        Provides functionality to call and display help using an external Help object.

        :return: None
        """
        thehelp = Help(self)
        thehelp.show()

    def view(self):
        """
        Opens the BooN View window, which displays the Boolean equations of the current network.
        The instance is stored in self.QView so that refresh() can update it while it is open.

        :return: None
        """
        self.QView = View(self)
        self.QView.show()

    def stablestates(self):
        """
        Opens the Stable States window, which computes and displays the stable states of the current BooN.
        The instance is stored in self.QStableStates so that refresh() can update it while it is open.

        :return: None
        """
        self.QStableStates = StableStates(self)
        self.QStableStates.show()

    def model(self):
        """
        Opens the Dynamical Model window, which draws the state-transition graph of the current BooN.
        Refused if the number of variables exceeds MODELBOUND, since the state space grows as 2^n
        and the graph would be too large to render.

        :return: None
        """
        if len(self.boon.variables) > MODELBOUND:
            QMessageBox.critical(self, "No Model", f"The number of variables exceeds {MODELBOUND}.\nThe model cannot be drawn.")
            return
        self.QModel = Model(self)
        self.QModel.show()

    def controllability(self):
        """
        Opens the Controllability window, which computes control actions to drive the BooN toward a target marking profile.
        The instance is stored in self.QControllability so that refresh() can update it while it is open.

        :return: None
        """
        if self.QControllability is None:                                                   #Created once: its signals are connected to the shared worker
            self.QControllability = Controllability(self)
        else:
            self.QControllability.initialize_controllability()
        self.QControllability.show()
        self.QControllability.raise_()

    def display_saved_flag(self, val: bool = True):
        """
        Displays a flag in the status bar indicating whether the data has been saved. 
        A large empty circle (○) means the BooN is saved; a large filled circle (⬤) means it has unsaved changes. 
        Also updates self.saved so that quit() can check the state consistently.

        :param val: True if the BooN is saved, False if it has unsaved changes. Defaults to True.
        :type val: bool

        :return: None
        """
        NOTSAVED: str = '\u2B24'                                                            #Large black/filled circle: unsaved changes
        SAVED: str = '\u25CB'                                                               #Large empty circle: saved 
        self.saved = val
        if self.saved:
            self.statusBar().showMessage(SAVED)
        else:
            self.statusBar().showMessage(NOTSAVED)



class Graph(QObject):
    """
    Interactive graph editor managing the visual and logical representation of a BooN interaction graph on 
    a Matplotlib canvas embedded in the PyQt5 GUI.
    Handles node/edge creation, deletion, renaming, selection, dragging, zooming, edge sign toggling, 
    family color assignment, and self-loop rendering.

    :ivar canvas: The Matplotlib canvas used for rendering the graph.
    :type canvas: FigureCanvas

    :ivar axes: The Matplotlib axes used for drawing.
    :type axes: matplotlib.axes.Axes

    :ivar graph: The directed graph storing nodes and edges.
    :type graph: networkx.DiGraph

    :ivar node_positions: Dictionary mapping node IDs to (x, y) coordinates.
    :type node_positions: dict

    :ivar node_labels: Dictionary mapping node IDs to their display labels.
    :type node_labels: dict

    :ivar next_node_id: Counter for assigning unique integer IDs to new nodes.
    :type next_node_id: int

    :ivar edge_colors: Mapping from edge (u, v) to RGB display color.
    :type edge_colors: dict

    :ivar edge_labels: Mapping from edge (u, v) to its display label.
    :type edge_labels: dict

    :ivar edge_modules: Mapping from edge (u, v) to its BooN module set.
    :type edge_modules: dict

    :ivar default_edge_sign: Default sign for newly created edges (+1 or -1).
    :type default_edge_sign: int

    :ivar selected_nodes: Set of currently selected node IDs.
    :type selected_nodes: set

    :ivar selected_edge: Currently selected edge as (src, tgt), or None.
    :type selected_edge: tuple or None

    :ivar zoom_factor: Current zoom level multiplier.
    :type zoom_factor: float

    :ivar edge_family_colors: Mapping from edge (u, v) to its family RGB color.
    :type edge_family_colors: dict

    :ivar show_family_colors: Whether to render family color markers on edges.
    :type show_family_colors: bool

    :ivar graph_changed: Qt signal emitted whenever the graph topology changes.
    :type graph_changed: pyqtSignal

    :ivar NODE_SIZE_DEFAULT: Default (and minimum) node size in Matplotlib units.
    :type NODE_SIZE_DEFAULT: int

    :ivar NODE_SIZE_MAX: Maximum allowed node size.
    :type NODE_SIZE_MAX: int

    :ivar NODE_SIZE_STEP: Size increment/decrement step.
    :type NODE_SIZE_STEP: int

    :ivar node_sizes: Per-node size overrides; absent key falls back to NODE_SIZE_DEFAULT.
    :type node_sizes: dict
    """

    graph_changed = pyqtSignal()

    def __init__(self, canvas):
        """
        Initializes the Graph editor and attaches it to a Matplotlib canvas.

        :param canvas: The Matplotlib FigureCanvas used for rendering.
        :type canvas: FigureCanvas
        """
        super().__init__()
        self.canvas = canvas
        self.axes = canvas.axes
        self.graph = nx.DiGraph()                                                           #Initialize an empty directed graph to store the interaction structure
        
        #STEP: Initialize graph state variables for nodes, edges, selection, and visual styling.
        self.node_positions = {}
        self.node_labels = {}
        self.next_node_id = 1                                                               #Counter to assign unique IDs for new nodes: increments for each new node created
        self.edge_colors = {}                                                               #Edge sign color: positive/activation = green, negative/inhibition = red
        self.edge_labels = {}                                                               #Edge label: shows the modules associated with the edge, if any
        self.edge_modules = {}                                                              #Edge modules: stores the set of BooN modules associated with each edge, used to generate edge labels
        self.default_edge_sign = 1                                                          #Default sign for new edges: +1 = activation (green)
        self.selected_nodes = set()
        self.selected_edge = None
        self.zoom_factor = 1.0
        self.edge_family_colors = {}                                                        #Edge family color: to visually group edges by families, regardless of their sign
        self.show_family_colors = True

        #STEP: Initialize interaction state variables for edge creation, node dragging, selection rectangle, and double-click detection.
        self.double_click_node = None
        self.edge_preview = None
        self.edge_source = None
        self.tracked_positions = {}
        self.drag_start_pos = None
        self.selection_rect_start = None
        self.selection_rect_patch = None
        self.dragging_nodes = False
        self.is_dragging = False

        #STEP: Initialize node size state
        self.NODE_SIZE_DEFAULT: int = 600                                                   #Default minimal node size
        self.NODE_SIZE_MAX: int = 1800                                                      #Fixed maximum node size      
        self.NODE_SIZE_STEP: int = 200
        self.node_sizes: dict = {}                                                          #Per-node size overrides: stores specific sizes of nodes, uses default size if not specified

        #STEP: Initialize node label position state
        self.node_label_top: bool = False                                                   #If True, labels are shifted above nodes; if False, labels are centered on nodes

    #DEF: Graph Model/Logic
    def setup_design(self, boon):
        """
        Builds the internal graph structure from a BooN model and prepares the canvas for rendering.
        Node IDs are assigned as integers in sorted symbol order. Node positions are taken from boon.pos if 
        available, otherwise computed with a spring layout. Edge signs and colors are read from the interaction 
        graph and stored for later rendering.

        :param boon: The Boolean Network model to visualise.
        :type boon: BooN
        ``SIGNCOLOR`` is also stored as an instance attribute for use by the rendering methods.

        :return: None
        """
        self.boon = boon                                                                    #Reference BooN model for synchronization with the graph editor
        self.canvas.axes.clear()
        self.SIGNCOLOR = SIGNCOLOR                                                          #Instance variable to assign colors for edge signs: +1=green, -1=red, 0=gray

        #STEP: Convert int-keyed family colors to label keys using the CURRENT labels, before IDs are reassigned
        #WARNING: IDs are reassigned below in sorted-label order, which may differ from the IDs of the editing session.
        old_labels = self.node_labels
        self.edge_family_colors = {
            ((old_labels.get(u, u) if isinstance(u, int) else u),
             (old_labels.get(v, v) if isinstance(v, int) else v)): c
            for (u, v), c in self.edge_family_colors.items()
        }
        self.selected_nodes = set()                                                         #Former IDs are meaningless after the rebuild
        self.selected_edge = None
        self.edge_source = None
        self.edge_preview = None

        #STEP: Build a fresh DiGraph from the BooN interaction graph
        #WARNING: To prevent its inclusion in the BooN, the variable names are strings while the other nodes are integers or symbols.
        ig = boon.interaction_graph
        self.graph = nx.DiGraph()

        #STEP: Assign int ID to each symbol node, create graph nodes, and store labels
        symbol_to_id = {}
        for idx, sym_node in enumerate(sorted(ig.nodes(), key=str), start=1):               #Sorted for deterministic ID assignment
            symbol_to_id[sym_node] = idx                                                    #Each symbol node get unique int ID, stored in symbol_to_id
            self.graph.add_node(idx)                                                        #Add node to graph

        self.node_labels = {symbol_to_id[sym]: str(sym) for sym in ig.nodes()}              #Store node labels for display, using the original symbol names from the BooN

        #STEP: Remap edge_family_colors from label-string keys to the new int-ID keys.
        #      color_history and the conversion above use (label, label) pairs as stable keys.
        label_to_id = {str(sym): nid for sym, nid in symbol_to_id.items()}                 #label string -> new int ID for this session
        remapped = {}
        for (u_key, v_key), color in self.edge_family_colors.items():
            u_new = label_to_id.get(u_key)
            v_new = label_to_id.get(v_key)
            if u_new is not None and v_new is not None:                                     #Colors of vanished nodes are dropped
                remapped[(u_new, v_new)] = color
        self.edge_family_colors = remapped

        #STEP: Assign node positions from boon.pos; nodes without a stored position are placed by a spring layout
        pos = getattr(boon, "pos", None) or {}
        self.node_positions = {symbol_to_id[sym]: tuple(coord) for sym, coord in pos.items() if sym in symbol_to_id}
        missing = [sym for sym in ig.nodes() if symbol_to_id[sym] not in self.node_positions]
        if missing:
            fixed = [sym for sym in ig.nodes() if symbol_to_id[sym] in self.node_positions]
            init = {sym: np.array(pos[sym], dtype=float) for sym in fixed}
            sym_layout = nx.spring_layout(ig, pos=init or None, fixed=fixed or None,        #Keep the stored positions, place only the missing nodes
                                          center=(0.5, 0.5) if not fixed else None,
                                          scale=0.4 if not fixed else 1, seed=0)
            for sym in missing:
                self.node_positions[symbol_to_id[sym]] = tuple(sym_layout[sym])

        #STEP: Restore per-node sizes from boon.meta if available
        self.node_sizes = {}
        meta = getattr(boon, "meta", None) or {}
        saved_sizes = meta.get("node_sizes", {})
        for node_id, label in self.node_labels.items():
            if label in saved_sizes:
                self.node_sizes[node_id] = saved_sizes[label]                               #Re-map from symbol string back to int node ID

        #STEP: Restore node_label_top from boon.meta if available
        self.node_label_top = meta.get("node_label_top", False)

        #STEP: Restore edge_family_colors from boon.meta on fresh load (when not already set by undo/redo)
        if not getattr(self, "edge_family_colors", {}):                                   #Empty: this is a fresh open/import, not an undo/redo restore
            efc_by_label = meta.get("edge_family_colors", {})
            label_to_id = {str(sym): symbol_to_id[sym] for sym in ig.nodes()}
            restored_efc = {}
            for key, color in efc_by_label.items():
                parts = key.split("\t", 1)
                if len(parts) == 2:
                    u_id = label_to_id.get(parts[0])
                    v_id = label_to_id.get(parts[1])
                    if u_id is not None and v_id is not None:
                        restored_efc[(u_id, v_id)] = tuple(color)
            if restored_efc:
                self.edge_family_colors = restored_efc

        #STEP: Add edges to the graph, with their signs and display color
        self.edge_colors = {}
        for u_sym, v_sym, data in ig.edges(data=True):
            u_id = symbol_to_id[u_sym]
            v_id = symbol_to_id[v_sym]
            sign = data.get("sign", 1)                                                      #Default edge sign: +1 = activation
            self.graph.add_edge(u_id, v_id, sign=sign)                                      #Assign edge sign
            self.edge_colors[(u_id, v_id)] = self.SIGNCOLOR[sign]                           #Store edge display color based on its sign, with SIGNCOLOR mapping
        self.redraw_graph()

        #STEP: Set next_node_id above the highest existing integer ID to avoid collisions
        existing_ids = [n for n in self.graph.nodes() if isinstance(n, int)]
        if existing_ids:
            self.next_node_id = max(existing_ids) + 1
        else:
            self.next_node_id = 1

    def _track_node_positions(self, dx, dy):
        """
        Tracks node position updates during dragging without committing changes.
        Updates the internal node position dictionary for all selected nodes based on the drag
        delta and refreshes the visualization.

        :param dx: Horizontal movement delta.
        :type dx: float

        :param dy: Vertical movement delta.
        :type dy: float

        :return: None
        """
        #STEP: Shift the positions of all selected nodes by the drag delta (dx, dy) and redraw
        for node in self.selected_nodes:
            if node in self.node_positions:
                x, y = self.node_positions[node]
                self.node_positions[node] = (x + dx, y + dy)
        self.redraw_graph()

    def _commit_tracked_positions(self):
        """
        Persists the final dragged positions of selected nodes into the BooN model.
        Called once on mouse release after a node drag. Writes the current node_positions
        values back to boon.pos so that saving the file preserves the layout.

        :return: None
        """
        #STEP: Build reverse map from int node ID to sympy symbol
        id_to_symbol = {
            node_id: symbols(label)
            for node_id, label in self.node_labels.items()
            if isinstance(label, str) and label.strip()
        }

        #STEP: Write each dragged node's final position into boon.pos under its Symbol key
        for node in self.selected_nodes:
            if node in self.node_positions:
                sym = id_to_symbol.get(node)
                if sym is not None:
                    self.boon.pos[sym] = self.node_positions[node]                          #Symbol key position
        self.redraw_graph()

        #STEP: Record position change in history (layout-only change: the descriptor is unchanged, so add_history would ignore it)
        if hasattr(self, "_boonify_parent"):
            self._boonify_parent.add_color_history()


    def _apply_edge_color(self, rgb):
        """
        Applies a visual color to the currently selected edge.
        Updates the edge color mapping for the selected edge in both directions (if bidirectional) 
        and refreshes the graph display.

        :param rgb: RGB color tuple withvalues in [0, 1].
        :type rgb: tuple[float, float, float]

        :return: None
        """
        if not self.selected_edge:
            return
        u, v = self.selected_edge
        #If bidirectional edge: apply to both directions
        self.edge_colors[(u,v)] = rgb                                                       #Apply color to the selected edge (forward direction)
        self.edge_colors[(v,u)] = rgb                                                       #Apply color to the reverse direction (for bidirectional edges)
        self.redraw_graph()

    def change_edge_sign(self, sign):
        """
        Changes the sign and display color of the currently selected edge.
        Updates both the logical sign stored in the graph and the visual color mapping, then emits a graph 
        update (graph_changed) signal after modification to notify the BooN model.

        :param sign: New sign value for the edge(+1 for activation, -1 for inhibition).
        :type sign: int

        :raises QMessageBox.warning: If no edge is currently selected.
        :return: None
        """
        if not self.selected_edge:                                                          #Show error: if no edge selected
            QMessageBox.warning(None, "No edge selected", "Please click an edge first.")
            return
        
        u, v = self.selected_edge
        self.edge_colors[(u, v)] = self.SIGNCOLOR[sign]                                     #Update edge display color to its sign
        if self.graph.has_edge(u, v):
            self.graph[u][v]["sign"] = sign                                                 #Update edge logical sign in graph data structure

        self.redraw_graph()
        self.graph_changed.emit()

    def set_default_edge_sign(self, sign):
        """
        Sets the default sign used for newly created edges.

        :param sign: Edge sign (+1 for activation, -1 for inhibition).
        :type sign: int

        :return: None
        """
        self.default_edge_sign = sign

    def _add_new_node(self, x, y):
        """
        Add a new node at the specified position in the graph.
        Assigns the next available integer ID, generates a default label (e.g., "x3"), stores position and label, 
        redraws the graph, and emits the ``graph_changed`` signal.

        :param x: X coordinate in data (axes) space.
        :type x: float

        :param y: Y coordinate in data (axes) space.
        :type y: float

        :return: None
        """
        new_id = self.next_node_id                                                          #Assign next available int ID to new node
        self.next_node_id += 1                                                              #Increment counter for unique node IDs

        new_label = self.next_default_label()                                               #Generate default label (ex: x1)

        self.graph.add_node(new_id)                                                         #Add new node to graph with ID
        self.node_positions[new_id]=(x,y)                                                   #Store positions
        self.node_labels[new_id]= new_label                                                 #Store display label shown on canvas

        self.redraw_graph()
        self.graph_changed.emit()

    def refresh_next_node_id(self):
        """
        Recomputes the next available integer node ID.
        Must be called after undo/redo or any external graph modification that may have changed which integer IDs are in use.

        :return: None
        """
        int_nodes = [n for n in self.graph.nodes if isinstance(n, int)]

        if int_nodes:
            self.next_node_id = max(int_nodes) + 1                                          #Set next_node_id above the highest existing int ID
        else:
            self.next_node_id = 1
    
    def next_default_label(self):
        """
        Generates the next available default node label.
        Only labels matching the pattern "x<number>" are considered. Custom renamed nodes are 
        ignored when computing the next index.

        :return: Next generated label (e.g., "x3").
        :rtype: str
        Example::

            x1, x2 -> x3
            tom, x2, x3 -> x4
        """
        max_index = 0
        for label in self.node_labels.values():
            if not isinstance(label, str):
                continue
            
            match = re.fullmatch(r"x(\d+)", label.strip())
            if match:
                number = int(match.group(1))
                if number > max_index:
                    max_index = number
        return f"x{max_index + 1}"

    def _create_edge(self, source, target):
        """
        Creates a directed edge between two nodes with the current default sign.
        Assigns the default family color (white) and the sign-matching display color, clears the selection state,
        redraws the graph, and emits graph_changed. Does nothing if the edge already exists.

        :param source: Source node identifier.

        :param target: Target node identifier.
        :type source: any
        :type target: any

        :return: None
        """
        self._clear_edge_preview()                                                          #Clear the drag preview line before committing the edge

        if source not in self.graph or target not in self.graph:                            #Invalid (or deleted) source or target: abort edge creation
            return

        if self.graph.has_edge(source, target):                                             #Skip duplicate edges
            return
        
        #STEP: Register the new edge with its sign, family color, and display color
        self.graph.add_edge(source, target, sign=self.default_edge_sign)                    #Add edge to graph with the default sign
        self.edge_family_colors[(source, target)] = (1.0, 1.0, 1.0)                         #Assign default family color (white) to the new edge
        self.edge_colors[(source, target)] = (self.SIGNCOLOR[self.default_edge_sign])       #Assign edge display color from its sign

        #STEP: Clear selection state leftover from edge creation and redraw 
        self.selected_nodes.clear()
        self.selected_edge = None
        self.double_click_node = None

        self.redraw_graph()
        self.graph_changed.emit()

    def _compute_self_loop_angle(self, node):
        """
        Computes the optimal placement angle for a self-loop edge on the given node.
        Finds the largest angular gap between neighboring nodes around the target node, then places the loop at the midpoint of 
        that gap to minimise visual overlap. Falls back to a straight-up angle (π/2) when the node has no neighbors.

        :param node: Node identifier.
        :type node: any

        :return: Angle in radians for self-loop placement, measured from the positive x-axis.
        :rtype: float
        """
        #STEP: Collect all neighboring nodes
        neighbors = set(self.graph.predecessors(node)) | set(self.graph.successors(node))
        neighbors.discard(node)                                                             #Remove to exclude self-loop itself

        x0, y0 = self.node_positions[node]

        if not neighbors:
            return np.pi / 2                                                                #No neighbors: default upward loop

        #STEP: Compute angle from node to each neighbor and sort to find angular gaps
        occupied_angles = []
        for nbr in neighbors:
            x1, y1 = self.node_positions[nbr]
            dx = x1 - x0
            dy = y1 - y0
            angle = math.atan2(dy, dx)
            occupied_angles.append(angle)
        occupied_angles.sort()

        #STEP: Find the largest angular gap using a circular extension of the angle list
        extended = occupied_angles + [occupied_angles[0] + 2 * np.pi]                       #Append first angle + 2π lets last angle warp around to the first for gap calculation

        largest_gap = -1
        best_angle = 0
        for a1, a2 in zip(occupied_angles, extended[1:]):
            gap = a2 - a1
            if gap > largest_gap:
                largest_gap = gap
                best_angle = a1 + gap / 2                                                   #Place the loop at the midpoint of the largest gap
        return best_angle

    SELF_LOOP_RADIUS: float = 0.05                                                          #Fixed arc radius of a self-loop

    def _self_loop_geometry(self, node):
        """
        Computes the geometry of the self-loop of a node, shared by drawing, family markers and hit-testing.
        The anchor radius scales with node size so the arc always clears the node border,
        while the arc radius stays fixed so the loop itself does not grow with the node.

        :param node: Node identifier.
        :return: (cx, cy, xr, yr) where (cx, cy) is the arc center and xr, yr are the arc sample coordinates.
        :rtype: tuple
        """
        x, y = self.node_positions[node]
        angle = self._compute_self_loop_angle(node)                                         #Loop orientation avoiding the neighbors

        size_scale = (self.node_sizes.get(node, self.NODE_SIZE_DEFAULT) / self.NODE_SIZE_DEFAULT) ** 0.25
        radius = 0.07 * size_scale                                                          #Distance from node center to arc center: scale to node size
        R = self.SELF_LOOP_RADIUS

        cx = x + radius * math.cos(angle)
        cy = y + radius * math.sin(angle)

        #STEP: Build a circular arc whose opening faces the node
        thetas = np.linspace(0.14 * np.pi, 1.9 * np.pi, 60) + angle + np.pi
        xr = cx + R * np.cos(thetas)
        yr = cy + R * np.sin(thetas)
        return cx, cy, xr, yr

    #DEF: Graph View
    def _draw_nodes(self):
        """
        Renders all nodes on the canvas with per-node sizing.
        Node sizes are looked up individually from node_sizes, falling back to NODE_SIZE_DEFAULT.

        :return: None
        """
        nodes = list(self.graph.nodes())
        sizes = [self.node_sizes.get(n, self.NODE_SIZE_DEFAULT) for n in nodes]
        nx.draw_networkx_nodes(
            self.graph, 
            self.node_positions,
            nodelist=nodes,
            node_color='antiquewhite', 
            edgecolors='black', 
            node_size=sizes, 
            ax=self.canvas.axes
            )
        
    def _draw_labels(self):
        """
        Renders node labels on the canvas, applying optional vertical offset and line wrapping.
        When node_label_top is True, LABEL_VERTICAL_OFFSET = 0.04 shifts all labels just above the node
        center. All nodes are at default size in this mode so the fixed offset is consistent everywhere.
        When node_label_top is False, LABEL_VERTICAL_OFFSET = 0 centers the label on the node.
        Labels containing separators are wrapped by _wrap_node_label before display.

        :return: None
        """
        #STEP: Choose vertical offset based on label-position mode
        if getattr(self, "node_label_top", False):
            LABEL_VERTICAL_OFFSET = 0.04                                                    #Shift labels just above node center; nodes are at default size so offset is uniform
        else:
            LABEL_VERTICAL_OFFSET = 0                                                       #Center labels on nodes

        #STEP: Apply vertical offset to all node positions for label placement
        shifted_positions = {
            node: (x, y + LABEL_VERTICAL_OFFSET)
            for node, (x, y) in self.node_positions.items()
        }

        #STEP: Apply wrapping to long labels that contain separators
        wrapped_labels = {
            node: self._wrap_node_label(label)
            for node, label in self.node_labels.items()
        }

        text_items = nx.draw_networkx_labels(
            self.graph,
            shifted_positions,
            labels=wrapped_labels,
            font_size=10,
            font_weight='bold',
            ax=self.canvas.axes
        )

        for text in text_items.values():
            text.set_zorder(25)                                                             #Draw labels/node name above all to be visible
        
    def _draw_edges(self):
        """
        Draws all non-self-loop edges, dispatching to the appropriate drawing function.
        Bidirectional pairs are drawn once together by _draw_bidirectional_edges; each unidirectional edge 
        is drawn individually by _draw_normal_edge. Self-loops are handled separately by _draw_self_loops.

        :return: None
        """
        drawn_pairs = set()
        for u, v in self.graph.edges():
            #Self loop
            if u == v:
                continue

            #Bi-directional edge 
            if self.graph.has_edge(v, u):
                #Avoid drawing twice
                if (v, u) in drawn_pairs:
                    continue
                self._draw_bidirectional_edges(u, v)
                drawn_pairs.add((u, v))
                drawn_pairs.add((v, u))

            #Normal edge    
            else:
                self._draw_normal_edge(u, v)

    def _draw_normal_edge(self, u, v):
        """
        Draws a single directed edge from u to v.
        The full node size list is passed to networkx so it can offset the arrowhead correctly away from the target node border.

        :param u: Source node identifier.

        :param v: Target node identifier.
        :type u: any
        :type v: any

        :return: None
        """
        #WARNING: node_size must list sizes in the order of ALL nodes so networkx can correctly offset the arrowhead away from the target node border.
        nodes = list(self.graph.nodes())
        sizes = [self.node_sizes.get(n, self.NODE_SIZE_DEFAULT) for n in nodes]
        nx.draw_networkx_edges(
            self.graph,
            self.node_positions,
            edgelist=[(u, v)],
            edge_color=[self.edge_colors.get((u, v), self.SIGNCOLOR[0])],
            arrows=True,
            width=4,
            arrowsize=15,
            node_size=sizes,
            ax=self.canvas.axes,
            )
            
    def _draw_bidirectional_edges(self, u, v):
        """
        Draws two visually separated edges for a bidirectional connection.
        Applies a perpendicular offset so that u→v and v→u edges are both visible without overlap. 
        The offset direction is derived from the canonical (sorted-name) ordering of u and v, which must stay consistent with _get_nearest_edge 
        and _draw_family_circles to ensure hit-testing and marker placement align with the rendered lines.

        :param u: First node.

        :param v: Second node.

        :return: None
        """
        x1, y1 = self.node_positions[u]
        x2, y2 = self.node_positions[v]

        #STEP: Compute the perpendicular offset vector from the canonical (sorted) direction
        if str(u) <= str(v):
            can_x1, can_y1 = x1, y1
            can_x2, can_y2 = x2, y2
        else:
            can_x1, can_y1 = x2, y2
            can_x2, can_y2 = x1, y1

        cdx = can_x2 - can_x1
        cdy = can_y2 - can_y1
        length = math.hypot(cdx, cdy)
        if length == 0:
            return

        #Perpendicular unit vector (canonical frame: canonical_u -> canonical_v)
        px = -cdy / length
        py = cdx / length
        offset = 0.02

        #If u is the canonical-first node, dir_uv = +1, otherwise -1
        dir_uv = 1 if str(u) <= str(v) else -1
        dir_vu = -dir_uv

        nodes = list(self.graph.nodes())
        sizes = [self.node_sizes.get(n, self.NODE_SIZE_DEFAULT) for n in nodes]

        #STEP: Draw edge u -> v, shifted by +offset in the canonical direction
        pos1 = dict(self.node_positions)
        pos1[u] = (x1 + px * offset * dir_uv, y1 + py * offset * dir_uv)
        pos1[v] = (x2 + px * offset * dir_uv, y2 + py * offset * dir_uv)
        nx.draw_networkx_edges(
            self.graph,
            pos1,
            edgelist=[(u, v)],
            edge_color=[self.edge_colors.get((u, v), self.SIGNCOLOR[0])],
            arrows=True,
            width=4,
            arrowsize=15,
            node_size=sizes,
            ax=self.canvas.axes,
        )

        #STEP: Draw edge v -> u, shifted by -offset (opposite side)
        pos2 = dict(self.node_positions)
        pos2[v] = (x2 + px * offset * dir_vu, y2 + py * offset * dir_vu)
        pos2[u] = (x1 + px * offset * dir_vu, y1 + py * offset * dir_vu)
        nx.draw_networkx_edges(
            self.graph,
            pos2,
            edgelist=[(v, u)],
            edge_color=[self.edge_colors.get((v, u), self.SIGNCOLOR[0])],
            arrows=True,
            width=4,
            arrowsize=15,
            node_size=sizes,
            ax=self.canvas.axes,
        )

    def _draw_self_loops(self):
        """
        Draws self-loop edges as curved arcs with an arrowhead for nodes connected to themselves.
        The loop orientation is chosen by _compute_self_loop_angle to avoid neighboring nodes.
        The anchor radius scales with node size so the arc always clears the node border,
        while the arc size R stays fixed so the loop itself does not grow with the node.

        :return: None
        """
        for u, v in self.graph.edges():
            if u != v:
                continue

            _, _, xr, yr = self._self_loop_geometry(u)

            #STEP: Place arrowhead at tip of self-loop arc
            verts = np.column_stack([xr, yr])
            arrow_backoff = 4                                                               #Points shortend in curve for arrowhead to sits exactly at end
            curve_verts = verts[:-arrow_backoff]

            #STEP: Build Matplotlib path
            codes = [Path.MOVETO] + [Path.LINETO] * (len(curve_verts) - 1)
            path = Path(curve_verts, codes)
            patch = PathPatch(
                path,
                facecolor="none",
                edgecolor=self.edge_colors.get((u, u), "black"),
                linewidth=3,
                capstyle='round',
                joinstyle='round',
                zorder=3
            )
            self.axes.add_patch(patch)

            #STEP: Attach arrowhead to end of loop by using last segment direction
            p0 = verts[-arrow_backoff - 1]
            p1 = verts[-1]
            arrow = FancyArrowPatch(
                p0,
                p1,
                arrowstyle='-|>',
                mutation_scale=20,
                color=self.edge_colors.get((u, u), "black"),
                linewidth=3,
                shrinkA=0,
                shrinkB=0,
                connectionstyle="arc3",
                zorder=3
            )
            self.axes.add_patch(arrow)

    def _draw_family_circles(self):
        """
        Draws a small colored circle at the midpoint of each edge that has a non-default family color.
        Markers are placed on self-loops, normal edges, and bidirectional edges using the same geometry as their respective draw 
        functions to ensure visual alignment. Edges with BASIC_FAMILY_COLOR (white) are skipped — white means no family assigned.

        :return: None
        """
        if not self.show_family_colors or not self.edge_family_colors:
            return

        for edge, color in self.edge_family_colors.items():
            if edge not in self.graph.edges():
                continue
            if tuple(color) == BASIC_FAMILY_COLOR:                                          #If family color by default (white): no family color circle drawn
                continue

            u, v = edge

            #STEP: Draw family circles for self-loop
            if u == v:
                _, _, xr, yr = self._self_loop_geometry(u)                                  #Same geometry as _draw_self_loops

                mid_idx = len(xr) // 2                                                      #Place family circle halfway along loop
                mx, my = xr[mid_idx], yr[mid_idx]

                self.axes.add_patch(
                    plt.Circle(
                        (mx, my),
                        0.012,
                        color=color,
                        zorder=20
                    )
                )
                continue

            #STEP: Draw family color circle for normal/bidirectional edge
            x1, y1 = self.node_positions[u]
            x2, y2 = self.node_positions[v]

            dx = x2 - x1
            dy = y2 - y1
            norm = math.hypot(dx, dy)
            if norm == 0:
                continue

            #place family circle at midpoint of edge
            mx = (x1 + x2) / 2
            my = (y1 + y2) / 2

            #default = centered circle
            ox = 0
            oy = 0

            #STEP: Family color for double association/ bi-directional edges
            if self.graph.has_edge(v, u):
                offset = 0.02

                #Derive px/py and sign from the CANONICAL (sorted) ordering, matching _draw_bidirectional_edges and _get_nearest_edge exactly.
                if str(u) <= str(v):
                    can_x1, can_y1 = x1, y1
                    can_x2, can_y2 = x2, y2
                else:
                    can_x1, can_y1 = x2, y2
                    can_x2, can_y2 = x1, y1

                cdx = can_x2 - can_x1
                cdy = can_y2 - can_y1
                px = -cdy / norm
                py = cdx / norm

                direction = 1 if str(u) <= str(v) else -1                                   #Sign matches the +/- convention in _draw_bidirectional_edges

                sx = px * offset * direction
                sy = py * offset * direction

                mx = ((x1 + sx) + (x2 + sx)) / 2                                            #Midpoint of the shifted (offset) edge
                my = ((y1 + sy) + (y2 + sy)) / 2

            self.axes.add_patch(
                plt.Circle(
                    (mx + ox, my + oy),
                    0.012,
                    color=color,
                    zorder=20
                )
            )
    
    def _apply_zoom(self):
        """
        Adjusts the axis limits to implement the current zoom level.
        Zooming is centered on (0.5, 0.5) in data space. A higher zoom_factor narrows the visible range, magnifying the graph.

        :return: None
        """
        ax = self.canvas.axes
        center_x = 0.5
        center_y = 0.5
        base_width = 1.0                                                                    #Unzoomed visible width in data space
        base_height = 1.0                                                                   #Unzoomed visible height in data space
        width = base_width / self.zoom_factor                                               #Visible width shrinks as zoom increases
        height = base_height / self.zoom_factor
        ax.set_xlim(center_x - width / 2, center_x + width / 2)
        ax.set_ylim(center_y - height / 2, center_y + height / 2)

    def _draw_edge_preview(self, x1, y1, x2, y2):
        """
        Draws a temporary preview line for edge creation.
        Used during interactive edge creation to show a dashed line between source node and current mouse position.

        :param x1: Start X coordinate in data space.
        :type x1: float

        :param y1: Start Y coordinate in data space.
        :type y1: float

        :param x2: End X coordinate in data space (current mouse position).
        :type x2: float

        :param y2: End Y coordinate in data space (current mouse position).
        :type y2: float

        :return: None
        """
        #STEP: Remove the previous preview line before drawing the updated one
        if self.edge_preview is not None:
            try:
                self.edge_preview.remove()
            except Exception:
                pass
            self.edge_preview = None

        #STEP: Draw the new preview line and force an immediate canvas refresh
        (self.edge_preview,) = self.axes.plot(
            [x1, x2],
            [y1, y2],
            linestyle="dashed",
            linewidth=2,
            color="gray",
            alpha=0.8,
            zorder=1000,
        )
        self.canvas.draw()                                                                  #Force immediate render (not draw_idle) so preview tracks mouse
    
    def _clear_edge_preview(self):
        """
        Removes the current edge preview from the canvas.
        Clears temporary visualization used during interactive edge creation.

        :return: None
        """
        if self.edge_preview is not None:
            try:
                self.edge_preview.remove()
            except Exception:
                pass
            self.edge_preview = None
            self.canvas.draw_idle()

    def toggle_family_colors(self):
        """
        Toggles visibility of edge family color circles and redraws the graph.
        Enables or disables rendering of additional edge grouping markers and refreshes the graph display.

        :return: None
        """
        self.show_family_colors = not self.show_family_colors
        self.redraw_graph()

    def toggle_edge_sign(self, edge):
        """
        Toggles the sign of an edge between activation (+1) and inhibition (-1).
        Updates both the logical sign stored in the graph and the display color,
        then emits graph_changed to notify the BooN model.

        :param edge: Edge to toggle as a (src, tgt) tuple.
        :type edge: tuple

        :return: None
        """
        src, tgt = edge
        current_sign = self.graph[src][tgt].get("sign", 1)
        new_sign = -1 if current_sign == 1 else 1
        self.graph[src][tgt]["sign"] = new_sign                                             #Update logical sign in graph data
        self.edge_colors[(src, tgt)] = self.SIGNCOLOR[new_sign]                             #Update dispaly edge color to its sign
        self.redraw_graph()
        self.graph_changed.emit()

    def redraw_graph(self):
        """
        Clears and fully reconstructs the graph canvas.
        Draws nodes, labels, edges, self-loops, family color markers, and applies the current zoom.
        If an edge preview is active when this is called (e.g. mid-drag), its endpoints are saved and the preview line 
        is recreated after the redraw so it is not lost.

        :return: None
        """
        #STEP: Store the active edge preview endpoints before clearing the axes
        preview = self.edge_preview
        preview_data = None
        if preview is not None:
            try:
                xdata = preview.get_xdata()
                ydata = preview.get_ydata()
                preview_data = (xdata, ydata)
            except Exception:
                preview_data = None

        #STEP: Clear the axes and reset display settings
        self.axes.clear()
        self.axes.set_aspect('equal', adjustable='box')
        self.axes.set_frame_on(False)
        self.axes.axis('off')
        self.selection_rect_patch=None

        #STEP: Rebuild the full graph visualization
        self._draw_nodes()
        self._draw_labels()
        self._draw_edges()
        self._draw_self_loops()
        self._draw_family_circles()
        self._apply_zoom()

        #STEP: Restore the edge preview properly
        if preview_data is not None:
            self.edge_preview = self.axes.plot(
                preview_data[0],
                preview_data[1],
                linestyle="dashed",
                linewidth=2,
                color="gray",
                alpha=0.7,
                zorder=1000
            )[0]
        else:
            self.edge_preview = None
        self.canvas.draw()
        
    
    #DEF: Graph Controller (Events)
    def on_canvas_press(self, event):
        """
        Handles mouse button press events on the canvas. Dispatches to the appropriate action based on button and position.
            - Right-click on empty space while creating an edge: cancels edge creation.
            - Right-click on node: starts or completes edge creation (first click sets source, second click creates the edge).
            - Right-click on edge: toggles the edge sign and selects the edge.
            - Left-click on edge (no node nearby): selects the edge.
            - Left-click on node: selects the node for dragging (Shift adds to selection).
            - Left-double-click on node: selects the node and opens the rename dialog.
            - Left-click on empty space: begins a rubber-band selection rectangle or prepares a node creation on release.

        :param event: The Matplotlib mouse event carrying button, position, and modifier data.
        :type event: matplotlib.backend_bases.MouseEvent

        :return: None
        """
        outside = event.xdata is None or event.ydata is None
        nearest_node = None if outside else self._get_nearest_node(event.xdata, event.ydata)

        #STEP: Cancel edge creation on right-click on empty space (or outside the axes)
        if event.button == 3 and self.edge_source is not None and nearest_node is None:
            self._cancel_edge_creation()
            return

        if outside:
            return

        nearest_edge = self._get_nearest_edge(event.xdata, event.ydata)

        #STEP: Right click
        if event.button == 3:
            #STEP: First right-click on a node sets the edge source; second creates the edge
            if nearest_node is not None:
                if self.edge_source is None:
                    self.edge_source = nearest_node
                else:
                    source = self.edge_source
                    target = nearest_node
                    self._create_edge(source, target)
                    trace_gui(f"Created edge: {source} -> {target}")
                    self.edge_source = None                                                 #Reset edge creation mode
                return
            
            #STEP: Right-click on edge: toggle sign or select edge
            if nearest_edge is not None:
                self.toggle_edge_sign(nearest_edge)
                self.selected_edge = nearest_edge
                self.selected_nodes.clear()
                return
            
        #STEP: Left-click on an edge to select the edge
        if event.button == 1 and nearest_edge is not None and nearest_node is None:
            self.selected_edge = nearest_edge
            self.selected_nodes.clear()
            trace_gui(f"Selected edge: {nearest_edge}")
            return
        
        #STEP: Left click on node to select for dragging (or double-click to rename)
        if event.button == 1 and nearest_node is not None:
            shift_pressed = event.key is not None and 'shift' in event.key.lower()
            self._select_node(nearest_node, shift_pressed)
            self.selected_edge = None

            #STEP: Left double-click on a node triggers rename
            if getattr(event, 'dblclick', False):
                self.rename_node()
                return

            # Set up for dragging
            self.drag_start_pos = (event.xdata, event.ydata)
            self.selection_rect_start = None
            self.dragging_nodes = True
            self.is_dragging = False
            return
        
        #STEP: Left click on empty space to start selection rectangle or to create node
        if event.button == 1:
            if nearest_node is None and nearest_edge is None:
                self.selection_rect_start = (event.xdata, event.ydata)
                self.selected_nodes.clear()
                self.selected_edge = None
                self.dragging_nodes = False
                self._cancel_edge_creation()
                return

    def _cancel_edge_creation(self):
        """
        Leaves the edge creation mode and removes the preview line.

        :return: None
        """
        self.edge_source = None
        self._clear_edge_preview()
            
    def on_canvas_release(self, event):
        """
        Handles mouse button release events on the canvas.
        On left-button release:

        - If nodes were being dragged, commits their new positions.
        - If a selection rectangle was drawn, selects all nodes within it.
        - If the release is a short click on empty space, creates a new node there.

        Resets all drag and selection rectangle state after processing.

        :param event: The Matplotlib mouse event carrying button and position data.
        :type event: matplotlib.backend_bases.MouseEvent

        :return: None
        """
        if event.button == 1:                                                               #If left mouse click released
            if self.is_dragging:                                                            #If dragged, take the new positions
                self._commit_tracked_positions()
                self.tracked_positions.clear()

            xdata = event.xdata
            ydata = event.ydata
            if self.selection_rect_start is not None and xdata is not None and ydata is not None:
                #Calculate distance to check if it was a click or drag
                dx = xdata - self.selection_rect_start[0]
                dy = ydata - self.selection_rect_start[1]
                distance = math.sqrt(dx**2 + dy**2)

                #STEP: Short click on empty space to create a new node
                if distance < 0.03 and not self.selected_nodes:
                    self._add_new_node(self.selection_rect_start[0], self.selection_rect_start[1])
                else:
                    #STEP: Dragged click : do a selection rectangle
                    self._select_nodes_in_rectangle(
                        self.selection_rect_start[0], self.selection_rect_start[1],
                        xdata, ydata
                    )

            #STEP: Remove selection rectangle visualization
            if self.selection_rect_patch is not None:
                self.selection_rect_patch.remove()
                self.selection_rect_patch = None
                self.canvas.draw_idle()

            #STEP: Reset all drag and selection state
            self.selection_rect_start = None
            self.drag_start_pos = None
            self.dragging_nodes = False
            self.is_dragging = False

    def on_canvas_motion(self, event):
        """
        Handles mouse motion events on the canvas.
        Priority order:

        1. Edge preview: if an edge source is set, draws a dashed preview line.
        2. Selection rectangle: if dragging on empty space, draws a dashed rectangle.
        3. Node dragging: if nodes are selected and being dragged, updates their positions.

        :param event: The Matplotlib mouse event carrying position data.
        :type event: matplotlib.backend_bases.MouseEvent

        :return: None
        """
        if event.xdata is None or event.ydata is None:
            return

        #STEP: Edge preview (highest priority)
        if self.edge_source is not None:
            if self.edge_source not in self.node_positions:                                 #Source node deleted meanwhile
                self._cancel_edge_creation()
                return
            x1, y1 = self.node_positions[self.edge_source]
            x2, y2 = event.xdata, event.ydata

            self._draw_edge_preview(x1, y1, x2, y2)                                         #Already redraws the canvas
            return
        
        #STEP: Selection rectangle preview
        if self.selection_rect_start is not None and not self.dragging_nodes:
            x0, y0 = self.selection_rect_start
            x1, y1 = event.xdata, event.ydata
        
            if self.selection_rect_patch is not None:
                self.selection_rect_patch.remove()                                          #Remove old rectangle
        
            self.selection_rect_patch = Rectangle(                                          #Create dashed rectangle
                (min(x0, x1), min(y0, y1)),
                abs(x1 - x0),
                abs(y1 - y0),
                linewidth=1.5,
                edgecolor='black',
                facecolor='lightblue',
                alpha=0.2,
                linestyle='dashed',
                zorder=999,
            )
        
            self.axes.add_patch(self.selection_rect_patch)
            self.canvas.draw_idle()

        #STEP: Node dragging
        if self.drag_start_pos and self.dragging_nodes and self.selected_nodes:

            dx = event.xdata - self.drag_start_pos[0]
            dy = event.ydata - self.drag_start_pos[1]

            if abs(dx) > 0.01 or abs(dy) > 0.01:
                self.is_dragging = True
                self._track_node_positions(dx, dy)
                self.drag_start_pos = (event.xdata, event.ydata)

    def on_key_press(self, event):
        """
        Handles keyboard press events on the canvas.
        Supported keys:

        - Delete: Deletes the currently selected node(s) or edge.
        - Escape: Cancels active edge creation and clears the edge preview.

        :param event: The Matplotlib key event.
        :type event: matplotlib.backend_bases.KeyEvent

        :return: None
        """
        if event.key == 'delete':
            self.delete_selection()
        elif event.key == 'escape':
            self._cancel_edge_creation()

    def _handle_double_click(self, node):
        """
        Handles a double-click on a node to create an edge via two successive double-clicks.
        The first double-click stores the source node; the second creates the edge to the target.
        Self-loops are allowed (double-clicking the same node twice).

        :param node: The node that was double-clicked.

        :return: None
        """
        if node is None:
            return
        if self.double_click_node is None:
            self.double_click_node = node                                                               
        else:
            source = self.double_click_node                                                 #Store first/source node selected
            target = node                                                                   #Store second/target node selected: to create an edge
            self._create_edge(source, target)
            self.double_click_node = None                                                   #Reset after edge creation

    #DEF: UI helpers/color tools
    def _select_node(self, node, shift_pressed=False):
        """
        Selects or deselects a node, with optional multi-select via Shift.
        Without Shift, replaces the entire selection with this node alone. With Shift, toggles the node in or out of the current selection.

        :param node: The node identifier to select or deselect.

        :param shift_pressed: True to toggle (multi-select), False to replace selection.
        :type shift_pressed: bool

        :return: None
        """
        if shift_pressed:
            if node in self.selected_nodes:
                self.selected_nodes.remove(node)                                            #Deselect if already in selection
            else:
                self.selected_nodes.add(node)                                               #Add to existing selection
        else:
            self.selected_nodes = {node}                                                    #Replace selection with this node only
        trace_gui(f"Selected nodes: {self.selected_nodes}")

    def _select_nodes_in_rectangle(self, x1, y1, x2, y2):
        """
        Selects all graph nodes whose positions fall within the specified rectangle.
        Only user-created nodes (integer or Symbol IDs) are considered;
        internal pattern nodes are ignored. The rectangle is axis-aligned and defined by any two opposite corners.

        :param x1: X coordinate of the first corner.
        :type x1: float

        :param y1: Y coordinate of the first corner.
        :type y1: float

        :param x2: X coordinate of the opposite corner.
        :type x2: float

        :param y2: Y coordinate of the opposite corner.
        :type y2: float

        :return: None
        """
        if self.graph is None:
            return
        
        #STEP: Normalize rectangle coordinates
        min_x, max_x = min(x1, x2), max(x1, x2)
        min_y, max_y = min(y1, y2), max(y1, y2)
        positions = self.node_positions

        for node, pos in positions.items():
            if isinstance(node, int) or isinstance(node, Symbol):                           #Only user nodes, not pattern nodes
                if min_x <= pos[0] <= max_x and min_y <= pos[1] <= max_y:
                    self.selected_nodes.add(node)
        trace_gui(f"Selected nodes (rectangle): {self.selected_nodes}")

    def delete_selection(self):
        """
        Deletes the currently selected nodes or edge from the graph.
        Priority:

        - If nodes are selected, removes them and all their connected edges.
        - If only an edge is selected, removes that edge.
        - If nothing is selected, displays a warning dialog.

        :return: None
        """
        if self.selected_nodes:                                                             #If node selected
            trace_gui(f"Deleted nodes: {self.selected_nodes}")
            self.selected_edge = None                                                       #Clear edge selection when nodes deleted
            self._delete_selected_nodes()                                                   #Delete node and associated edges
            return
        if self.selected_edge:                                                              #If edge selected
            trace_gui(f"Deleted edge: {self.selected_edge}")
            self._delete_selected_edge()                                                    #Delete edge and clear the edge selection
            return
        QMessageBox.warning(None, "No selection", "Please select a node or edge to delete") #Show error: if button pressed without selection
    
    def _delete_selected_nodes(self):
        """
        Deletes all currently selected nodes and all their connected edges.
        Removes each node from the graph, purges its position and label entries, and clears any edge color or family 
        color records that reference the deleted nodes. Redraws the graph and emits graph_changed.

        :return: None
        """
        if not self.selected_nodes:
            return
        
        for node in list(self.selected_nodes):
            if node in self.graph:
                self.graph.remove_node(node)
            self.node_positions.pop(node, None)
            self.node_labels.pop(node, None)
            self.edge_colors = {e: c for e, c in self.edge_colors.items() if node not in e}  #Remove edge colors involving deleted node
            if hasattr(self, "edge_family_colors"):
                self.edge_family_colors = {
                    e: c for e, c in self.edge_family_colors.items()
                    if node not in e
                }
        self.selected_nodes.clear()
        self.redraw_graph()  
        self.graph_changed.emit()
    
    def _delete_selected_edge(self):
        """
        Deletes the currently selected edge and clears its visual metadata.
        Removes the edge from the graph and purges its entries from edge_colors and edge_family_colors. 
        Redraws the graph and emits graph_changed.

        :return: None
        """
        if not self.selected_edge:
            return
        if self.graph.has_edge(*self.selected_edge):
            self.graph.remove_edge(*self.selected_edge)
        self.edge_colors.pop(self.selected_edge, None)
        if hasattr(self, 'edge_family_colors'):
            self.edge_family_colors.pop(self.selected_edge, None)                           #Remove family color of deleted edge

        self.selected_edge= None
        self.redraw_graph()
        self.graph_changed.emit()
    
    def _get_nearest_node(self, x, y, threshold=0.05):
        """
        Finds the graph node closest to the given data-space coordinates.

        :param x: X coordinate to test.
        :type x: float

        :param y: Y coordinate to test.
        :type y: float

        :param threshold: Maximum Euclidean distance to consider as a hit.
        :type threshold: float

        :return: The nearest node identifier, or None if no node is within threshold.
        """
        min_dist = float('inf')
        nearest = None
        for node, pos in self.node_positions.items():
            dx= pos[0] - x
            dy= pos[1] - y
            dist = math.sqrt(dx * dx + dy * dy)
            if dist < threshold and dist < min_dist:
                nearest = node
                min_dist = dist
        return nearest
    
    def _get_nearest_edge(self, x, y, threshold=0.045):
        """
        Finds the graph edge closest to the given data-space coordinates.
        Handles normal edges, bidirectional pairs (with perpendicular offset matching the draw convention), 
        and self-loops (sampled as circular arcs).

        :param x: X coordinate to test.
        :type x: float

        :param y: Y coordinate to test.
        :type y: float

        :param threshold: Maximum distance to consider as a hit.
        :type threshold: float

        :return: The nearest edge as a (src, tgt) tuple, or None if none is within threshold.
        :rtype: tuple or None
        """
        candidates = []

        for src, tgt in self.graph.edges():
            #STEP: Self-loop handling
            if src == tgt:
                cx, cy, _, _ = self._self_loop_geometry(src)                                #Same geometry as _draw_self_loops
                dist = abs(math.hypot(x - cx, y - cy) - self.SELF_LOOP_RADIUS)              #Distance to the loop circle
                if dist < threshold:
                    candidates.append((dist, (src, tgt)))
                continue

            #STEP: Normal/bi-directional edge handling
            x1, y1 = self.node_positions[src]
            x2, y2 = self.node_positions[tgt]

            dx = x2 - x1
            dy = y2 - y1
            length = math.hypot(dx, dy)

            if length == 0:
                continue

            #Unit perpendicular vector for offset of bidirectional edges
            px = -dy / length
            py = dx / length

            #IMPORTANT: offset and direction match _draw_bidirectional_edges.
            if self.graph.has_edge(tgt, src):
                #STEP: Bidirectional edge
                offset = 0.02                                                               #Distance between parallel bidirectional edges

                if str(src) <= str(tgt):
                    can_x1, can_y1 = x1, y1
                    can_x2, can_y2 = x2, y2
                else:
                    can_x1, can_y1 = x2, y2
                    can_x2, can_y2 = x1, y1

                cdx = can_x2 - can_x1
                cdy = can_y2 - can_y1

                px = -cdy / length
                py = cdx / length

                direction = 1 if str(src) <= str(tgt) else -1                               #Src gets +offset if it is the canonical (smaller) node, else -offset
                hit_threshold = threshold

            else:
                offset = 0.0
                direction = 1
                hit_threshold = threshold

            ox = px * offset * direction
            oy = py * offset * direction

            x1o, y1o = x1 + ox, y1 + oy
            x2o, y2o = x2 + ox, y2 + oy

            dist = self._point_to_segment_distance(x, y, x1o, y1o, x2o, y2o)                #Compute shortest disatnce from click to closest edge
            if dist < hit_threshold:
                candidates.append((dist, (src, tgt)))

        if not candidates:
            return None
        candidates.sort(key=lambda x: x[0])
        return candidates[0][1]
    
    def _canonical_edge(self, u, v):
        """
        Returns a stable canonical ordering for a bidirectional edge pair.
        For a pair (u, v) where both (u, v) and (v, u) exist in the graph, returns the sorted tuple so 
        that the canonical form is consistent regardless of which direction is queried first.

        :param u: First node.

        :param v: Second node.

        :return: Canonically ordered edge tuple (smaller, larger), or (u, v) if not bidirectional.
        :rtype: tuple
        """
        #STEP: Check if edge exists in both directions (bidirectional)
        if (u, v) in self.graph.edges() and (v, u) in self.graph.edges():
            return tuple(sorted((u, v)))                                                    #Return tuple of bidirectional edges
        return (u, v)                                                                       #Return original direction if edge is not bidirectional
    
    def _get_event_xy(self, event):
        """
        Extracts data-space coordinates from a Matplotlib mouse event.
        Falls back to inverse-transform of widget coordinates if ``xdata``/``ydata``
        are not available directly (e.g., when the cursor is outside the axes).

        :param event: The Matplotlib mouse event.
        :type event: matplotlib.backend_bases.MouseEvent

        :return: Tuple (x, y) in data coordinates, or (None, None) if unavailable.
        :rtype: tuple[float | None, float | None]
        """
        #STEP: Use direct data coordinates if available (cursor is inside axes)
        if event.xdata is not None and event.ydata is not None:
            return event.xdata, event.ydata
        
        #STEP: Fallback: inverse-transform widget pixel coordinates to data space
        if event.inaxes is not None:
            return event.inaxes.transData.inverted().transform((event.x, event.y))
        return None, None                                                                   #Cursor is fully outside the axes; no coordinates available
    
    def _move_selected_nodes(self, dx, dy):
        """
        Moves all selected nodes by the given delta and persists positions to the BooN model.
        Updates both the internal ``node_positions`` dictionary and the BooN's own position store (``boon.pos``) for symbolic and integer nodes.

        :param dx: Horizontal displacement in data-space units.
        :type dx: float

        :param dy: Vertical displacement in data-space units.
        :type dy: float

        :return: None
        """
        #STEP: Abort if nothing is selected or graph is not initialised
        if not self.selected_nodes or self.graph is None:
            return
        
        #STEP: Apply shift to all selected nodes, then mirror the positions in the BooN model
        self._track_node_positions(dx, dy)                                                  #Shift node positions and redraw
        self._commit_tracked_positions()                                                    #Write the positions into boon.pos and record history
    
    def rename_node(self):
        """
        Opens a dialog to rename the currently selected node.
        """
        #STEP: Ensure valid selection
        if not self.selected_nodes:                                                         #Show error: if no node selected for renaming
            QMessageBox.warning(None, "No Selection", "Please select a node to rename.")
            return
        if len(self.selected_nodes) > 1:                                                    #Show error: if multiple nodes selected for renaming
            QMessageBox.warning(None, "Multiple Selection", "Please select only one node to rename.")
            return
        node = list(self.selected_nodes)[0]                                                 #Get the selected node
        old_name = self.node_labels.get(node, str(node))                                    #Get current label from node_labels

        #STEP: Show input dialog
        new_name, ok = QInputDialog.getText(
            None,
            "Rename Node",
            f"Enter new name for node '{old_name}':",
            text=old_name
        )

        #STEP: Validate the new name
        new_name = new_name.strip()
        if not ok or not new_name or new_name == old_name:                                  #Cancelled or unchanged
            return
        if not is_valid_variable_name(new_name):                                            #The name must be convertible into a single symbol
            QMessageBox.warning(None, "Invalid name",
                                f"'{new_name}' is not a valid variable name.\nUse letters, digits and '_' (not starting with a digit).")
            return
        if new_name in (str(lbl) for n, lbl in self.node_labels.items() if n != node):     #Duplicate names would merge two variables
            QMessageBox.warning(None, "Duplicate name", f"A node named '{new_name}' already exists.")
            return

        #STEP: Apply rename (family colors are keyed by node IDs, node sizes are re-serialized from IDs: both follow the rename)
        self.node_labels[node] = new_name                                                   #Update the node label
        self.redraw_graph()                                                                 #Redraw graph with new node name
        self.graph_changed.emit()                                                           #Update graph with changes
    
    def _point_to_segment_distance(self, px, py, x1, y1, x2, y2):
        """
        Computes the minimum Euclidean distance from a point to a line segment.
        If the segment has zero length, returns the distance from the point to the segment's endpoint.

        :param px: X coordinate of the test point.
        :type px: float

        :param py: Y coordinate of the test point.
        :type py: float

        :param x1: X coordinate of the segment start.
        :type x1: float

        :param y1: Y coordinate of the segment start.
        :type y1: float

        :param x2: X coordinate of the segment end.
        :type x2: float

        :param y2: Y coordinate of the segment end.
        :type y2: float

        :return: Perpendicular (or endpoint) distance from the point to the segment.
        :rtype: float
        """
        #STEP: Compute direction vector of segment
        dx = x2 - x1
        dy = y2 - y1

        if dx == 0 and dy == 0:                                                             #Case if no segment: only a single point
            return math.hypot(px - x1, py - y1)
        
        t = max(0, min(1, ((px - x1) * dx + (py - y1) * dy) / (dx * dx + dy * dy)))         #Parameter t for projection of point onto line

        #STEP: Compute closest point on segment from parameter t
        closest_x = x1 + t * dx
        closest_y = y1 + t * dy

        return math.hypot(px - closest_x, py - closest_y)                                   #Euclidean distance to nearest point on segment
    
    #DEF: Zoom controls
    def zoom_in(self):
        """
        Increase the zoom level of the graph view.
        Multiplies the current zoom factor by 1.2 and redraws the graph.
        """
        self.zoom_factor *= 1.2
        self.redraw_graph()
    
    def zoom_out(self):
        """
        Decrease the zoom level of the graph view.
        Divides the current zoom factor by 1.2 and redraws the graph.
        """
        self.zoom_factor /= 1.2
        self.redraw_graph()
    
    def reset_zoom(self):
        """
        Reset the zoom level to the default value.
        Sets zoom factor back to 1.0 and redraws the graph.
        """
        self.zoom_factor = 1.0
        self.redraw_graph()
    
    #DEF: Edge color management
    def pick_edge_color(self):
        """
        Open a color picker to set the color of the selected edge.
        If no edge is selected, a warning is shown. 
        Otherwise, the user selects a color which is applied to the edge.
        """
        if not self.selected_edge:                                                          #Edge must be selected before assigning a family color
            QMessageBox.warning(None, "No edge selected", "Select an edge first.")
            return
        
        #STEP: Open system color dialog and extract normalised RGB components
        color = QColorDialog.getColor()
        if not color.isValid():
            return
        rgb = (color.redF(), color.greenF(), color.blueF())

        self._apply_edge_color(rgb)                                                         #Color application delegated to helper

    def set_edge_color_from_palette(self, color_name):
        """
        Set the color of the selected edge using a predefined palette color.
        Stores the RGB color in edge_family_colors, redraws, then records a color-only history snapshot via 
        add_color_history so that each individual color assignment is independently undoable/redoable.
        """
        if not self.selected_edge:                                                          #Edge must be selected before assigning a family color
            QMessageBox.warning(None, "No edge selected", "Select an edge first.")
            return
        
        #STEP: Convert named color string to a normalised RGB tuple
        color = QColor(color_name)
        rgb = (color.redF(), color.greenF(), color.blueF())
        if not hasattr(self, "edge_family_colors"):
            self.edge_family_colors = {}

        #STEP: Store new family color
        edge = self.selected_edge
        u, v = edge
        self.edge_family_colors[(u, v)] = rgb                                               #Map edge key to its RBG color

        self.redraw_graph()

        #STEP: Rebuild the BooN so formula is updated with family pairing (also persists the colors into boon.meta)
        self.graph_changed.emit()

        #STEP: Store a color-only history snapshot for redo/undo (when the formulas are unchanged)
        self._sync_node_sizes_to_boon()
        if hasattr(self, "_boonify_parent"):
            self._boonify_parent.add_color_history()

    #DEF: Color palette menu
    def setup_color_menu(self, parent):
        """
        Initialize the edge color palette menu.
            Defines available colors, sets initial visibility count, creates the
            QMenu container, and builds the initial palette UI.
        """
        #STEP: Define list of colors for family assignment
        self.color_palette = [
            ("Pastel pink", "#FFC0E7"),
            ("Pastel green", "#CAFDCB"),
            ("Pastel blue", "#CDE9FF"),
            ("Pastel yellow", "#FAF9A3"),
            ("Purple", "#ECCFFF"),
            ("Magenta", "#FF528C"),
            ("Apple Green", "#72D31C"),
            ("Teal", "#02B5C1"),
            ("Golden", "#F0CE37"),
            ("Purple", "#B66DFF"),
            ("Red", "#C6002E"),
            ("Forest green", "#095A22"),
            ("Indigo", "#0D60DD"),
            ("Orange", "#FF8400"),
            ("Violet", "#6B0E97"),
            ("Neon Pink", "#FF00F2"),
            ("Neon Green", "#4DFF00"),
            ("Cyan", "#00FFEA"),
            ("Neon Yellow", "#E5FF00"),
            ("White/None", "#FFFFFF")
            ]
        self.visible_colors = 5                                                             #Show 5 colors only initially
        self._boonify_parent = parent                                                       #Keep reference to Boonify window for menu actions
        self.color_menu = QMenu(parent)
        self.build_color_palette()

    def open_color_palette(self):
        """
        Opens the edge family color palette menu at the current mouse cursor position.
        Rebuilds the palette UI before displaying so that the icon states (show/hide family colors) 
        always reflect the current application state.

        :return: None
        """
        if not hasattr(self, "color_menu"):                                                 #Menu must be set-up before opened
            return

        #STEP: Rebuild to refresh icon states and display at cursor position
        self.build_color_palette()
        self.color_menu.popup(QCursor().pos())

    def build_color_palette(self):
        """
        Build the color palette UI inside the menu.
        """
        self.color_menu.clear()

        palette_widget = QWidget()
        main_layout = QVBoxLayout()
        grid_layout = QGridLayout()
        grid_layout.setSpacing(5)

        #STEP: Color buttons in palette
        for i, (name, hex_color) in enumerate(self.color_palette[:self.visible_colors]):
            button = QPushButton()
            button.setFixedSize(32, 32)
            button.setStyleSheet(f"""QPushButton {{background-color: {hex_color};border: 1px solid black;border-radius: 16px;}}""")
            button.clicked.connect(lambda _, c=hex_color:self.set_edge_color_from_palette(c))
            row = i // 5
            col = i % 5
            grid_layout.addWidget(button, row, col)
        main_layout.addLayout(grid_layout)

        #STEP: Build bottom controls row
        controls_layout = QHBoxLayout()
        left_controls = QHBoxLayout()                                                       #Bottom-left: expand/collapse palette

        #Show + button only when colors remain hidden
        if self.visible_colors < len(self.color_palette):
            plus_button = QPushButton("+")
            plus_button.setFixedSize(32, 32)
            plus_button.setStyleSheet("""QPushButton {font-size: 18px;font-weight: bold;}""")
            plus_button.clicked.connect(self.show_more_colors)
            left_controls.addWidget(plus_button)

        #Show - button when more than 5 colors are shown
        if self.visible_colors > 5:
            minus_button = QPushButton("-")
            minus_button.setFixedSize(32, 32)
            minus_button.setStyleSheet("""QPushButton {font-size: 18px;font-weight: bold;}""")
            minus_button.clicked.connect(self.show_less_colors)
            left_controls.addWidget(minus_button)

        controls_layout.addLayout(left_controls)
        controls_layout.addStretch()
        toggle_button = QPushButton()                                                       #Bottom-right: hide family-color toogle button
        toggle_button.setFixedSize(32, 32)

        #STEP: Match icons to show_family_colors
        if self.show_family_colors:
            icon = QIcon(":/icon/resources/family_color_sign.svg")
            if icon.isNull():                                                               #Fallback: plain text label
                toggle_button.setText("👁")
        else:
            icon = QIcon(":/icon/resources/no_family_color_sign.svg")
            if icon.isNull():                                                               #Fallback: plain text label
                toggle_button.setText("🚫")

        if not icon.isNull():
            toggle_button.setIcon(icon)
            toggle_button.setIconSize(QSize(20, 20))
        toggle_button.setToolTip("Show / Hide family colors")

        # STEP: Wire toggle button
        def _on_toggle():
            self.toggle_family_colors()
            if hasattr(self, "_boonify_parent") and hasattr(self._boonify_parent, "actionHideFamilyColor"):
                action = self._boonify_parent.actionHideFamilyColor
                action.blockSignals(True)                                                   #Block signals to avoid double-toggle
                action.setChecked(not self.show_family_colors)
                action.blockSignals(False)                                                  #Sync the checked state

            self.build_color_palette()                                                      #Rebuild palette so the icon reflects the new state
            self.color_menu.popup(self.color_menu.pos())

        toggle_button.clicked.connect(_on_toggle)
        controls_layout.addWidget(toggle_button)

        #STEP: Add controls row to main layout
        main_layout.addLayout(controls_layout)
        palette_widget.setLayout(main_layout)
        widget_action = QWidgetAction(self.color_menu)
        widget_action.setDefaultWidget(palette_widget)
        self.color_menu.addAction(widget_action)

    def show_more_colors(self):
        """
        Increase the number of visible colors in the palette.
        Expands visible color count and rebuilds the palette UI.
        """
        self.visible_colors+=5                                                              #Reveal next group of 5 colors
        self.build_color_palette()
        self.color_menu.popup(self.color_menu.pos())

    def show_less_colors(self):
        """
        Decrease the number of visible colors in the palette.
        Reduces visible color count (minimum 5) and rebuilds the palette UI.
        """
        self.visible_colors = max(5, self.visible_colors - 5)                               #Hide a group of colors but never below 5 visible colors
        self.build_color_palette()
        self.color_menu.popup(self.color_menu.pos())

    #DEF: Node-size menu
    def setup_resize_menu(self, parent):
        """
        Initialize the node-size adjustment menu.
        Creates a QMenu container and builds the initial resize UI.
        """
        self._boonify_parent = getattr(self, "_boonify_parent", parent)                     #Preserve existing refrenece if already set
        self.resize_menu = QMenu(parent)
        self.build_resize_palette()

    def open_resize_menu(self):
        """
        Opens the node-size adjustment panel at the current mouse cursor position.
        The panel can be opened even without a selection because the 'All' mode operates on every node.
        A warning is shown only when the panel is actually used in 'Selected' mode with no node chosen.

        :return: None
        """
        if not hasattr(self, "resize_menu"):                                                #Verify menu exists
            return

        #STEP: Rebuild and display the resize panel at cursor position
        self.build_resize_palette()
        self.resize_menu.popup(QCursor().pos())

    def build_resize_palette(self):
        """
        Build the node-size adjustment UI inside the resize menu popup.
                The panel contains:

                - A horizontal slider to set the size of the target node(s) continuously.
                - A toggle switch (Selected / All) to apply the size to the selected node(s) or
                    uniformly to all nodes in the graph.
                - A label-position icon button that switches the node name between Center and Top.
                    Switching to Top immediately resets all node sizes back to NODE_SIZE_DEFAULT so
                    that the label offset is consistent across the graph.

                :return: None
        """
        self.resize_menu.clear()

        container = QWidget()
        layout = QVBoxLayout()
        layout.setContentsMargins(10, 8, 10, 8)
        layout.setSpacing(6)

        #STEP: Create panel title
        title_label = QLabel("Node Size")
        title_label.setAlignment(Qt.AlignCenter)
        title_label.setStyleSheet("font-weight: bold; font-size: 12px;")
        layout.addWidget(title_label)

        #STEP: Determine initial slider value from selected nodes
        if self.selected_nodes:
            ref_size = int(sum(self.node_sizes.get(n, self.NODE_SIZE_DEFAULT)
                               for n in self.selected_nodes) / len(self.selected_nodes))
        else:
            ref_size = self.NODE_SIZE_DEFAULT

        #STEP: Create node-size slider
        slider = QSlider(Qt.Horizontal)
        slider.setMinimum(self.NODE_SIZE_DEFAULT)
        slider.setMaximum(self.NODE_SIZE_MAX)
        slider.setSingleStep(self.NODE_SIZE_STEP)
        slider.setPageStep(self.NODE_SIZE_STEP)
        slider.setValue(ref_size)
        slider.setFixedWidth(180)
        slider.setToolTip("Drag to adjust node size")

        #STEP: Create current size display label
        size_value_label = QLabel(str(ref_size))
        size_value_label.setFixedWidth(36)
        size_value_label.setAlignment(Qt.AlignLeft | Qt.AlignVCenter)
        size_value_label.setStyleSheet("font-size: 10px; color: #555555;")

        #STEP: Disable controls when label position is set to Top
        _in_top_mode = getattr(self, "node_label_top", False)
        slider.setEnabled(not _in_top_mode)
        size_value_label.setEnabled(not _in_top_mode)

        #STEP: Assemble slider row
        slider_row = QHBoxLayout()
        slider_row.setSpacing(6)
        slider_row.addWidget(slider)
        slider_row.addWidget(size_value_label)
        layout.addLayout(slider_row)

        #STEP: Create Selected/All application mode controls
        toggle_row = QHBoxLayout()
        toggle_row.setSpacing(6)

        toggle_lbl = QLabel("Apply to:")
        toggle_lbl.setStyleSheet("font-size: 10px;")
        toggle_row.addWidget(toggle_lbl)

        btn_selected = QPushButton("Selected")
        btn_all = QPushButton("All")
        for btn in (btn_selected, btn_all):
            btn.setCheckable(True)
            btn.setFixedHeight(24)
            btn.setStyleSheet(
                "QPushButton { font-size: 10px; border: 1px solid #aaa; border-radius: 3px; padding: 0 6px; }"
                "QPushButton:checked { background-color: #4A90D9; color: white; border-color: #2E6DAD; }"
            )

        #STEP: Restore previously selected resize mode
        _all_mode = getattr(self, "_resize_all_mode", False)
        btn_selected.setChecked(not _all_mode)
        btn_all.setChecked(_all_mode)

        #STEP: Define resize mode handlers
        def _set_mode_selected():
            self._resize_all_mode = False
            btn_selected.setChecked(True)
            btn_all.setChecked(False)

        def _set_mode_all():
            self._resize_all_mode = True
            btn_selected.setChecked(False)
            btn_all.setChecked(True)

        #STEP: Connect resize mode buttons
        btn_selected.clicked.connect(_set_mode_selected)
        btn_all.clicked.connect(_set_mode_all)

        toggle_row.addWidget(btn_selected)
        toggle_row.addWidget(btn_all)
        toggle_row.addStretch()
        layout.addLayout(toggle_row)

        #STEP: Handle slider value changes
        def _on_slider_changed(value):
            """Apply the slider value to the target nodes and redraw."""
            size_value_label.setText(str(value))
            if getattr(self, "_resize_all_mode", False):
                #Apply uniformly to every node in the graph
                for node in self.graph.nodes():
                    self.node_sizes[node] = value
            else:
                #Apply only to selected nodes; show error if none are selected
                if not self.selected_nodes:
                    QMessageBox.warning(None, "No Selection", "Please select a node to resize.")
                    return
                for node in self.selected_nodes:
                    self.node_sizes[node] = value
            self.redraw_graph()

            #STEP: Persist node_sizes into boon.meta immediately so save() captures the latest sizes
            self._sync_node_sizes_to_boon()

            #STEP: Record resize in undo/redo history, once per user gesture (not at every intermediate value while dragging)
            if not slider.isSliderDown():
                _record_resize()

        def _record_resize():
            if hasattr(self, "_boonify_parent"):
                self._boonify_parent.add_color_history()

        slider.valueChanged.connect(_on_slider_changed)
        slider.sliderReleased.connect(_record_resize)

        #STEP: Add separator between resize and label settings
        sep = QFrame()
        sep.setFrameShape(QFrame.HLine)
        sep.setFrameShadow(QFrame.Sunken)
        sep.setStyleSheet("color: #cccccc;")
        layout.addWidget(sep)

        #STEP: Create label-position controls
        label_pos_row = QHBoxLayout()
        label_pos_row.setSpacing(8)

        label_pos_title = QLabel("Label position:")
        label_pos_title.setStyleSheet("font-size: 10px;")
        label_pos_row.addWidget(label_pos_title)

        #STEP: Read current label-position state
        _label_top = getattr(self, "node_label_top", False)

        #STEP: Create label-position toggle button
        label_pos_btn = QPushButton()
        label_pos_btn.setFixedSize(80, 28)
        label_pos_btn.setCheckable(True)
        label_pos_btn.setChecked(_label_top)

        #STEP: Define label-position icons
        ICON_LABEL_CENTER = ":/icon/resources/center_name.svg"
        ICON_LABEL_TOP    = ":/icon/resources/top_name.svg"

        #STEP: Update label-position button appearance
        def _update_label_pos_btn(is_top):
            """Refresh button icon/text and style to reflect the current label-position mode."""
            if is_top:
                icon = QIcon(ICON_LABEL_TOP)
                if not icon.isNull():
                    label_pos_btn.setIcon(icon)
                    label_pos_btn.setIconSize(QSize(16, 16))
                    label_pos_btn.setText(" Top")
                else:
                    label_pos_btn.setIcon(QIcon())
                    label_pos_btn.setText("⬆ Top")
                label_pos_btn.setStyleSheet(
                    "QPushButton { font-size: 10px; border: 1px solid #aaa; border-radius: 3px; "
                    "background-color: #4A90D9; color: white; border-color: #2E6DAD; }"
                )
            else:
                icon = QIcon(ICON_LABEL_CENTER)
                if not icon.isNull():
                    label_pos_btn.setIcon(icon)
                    label_pos_btn.setIconSize(QSize(16, 16))
                    label_pos_btn.setText(" Center")
                else:
                    label_pos_btn.setIcon(QIcon())
                    label_pos_btn.setText("⬤ Center")
                label_pos_btn.setStyleSheet(
                    "QPushButton { font-size: 10px; border: 1px solid #aaa; border-radius: 3px; "
                    "background-color: #f0f0f0; color: #333; }"
                )
        _update_label_pos_btn(_label_top)

        #STEP: Handle label-position changes
        def _toggle_label_position(checked):
            """
            Switch node label position between Center and Top.
            When switching TO Top: reset all node sizes to NODE_SIZE_DEFAULT for uniform appearance,
            and disable the slider since the fixed offset only works at default size.
            When switching TO Center: re-enable the slider so the user can resize freely.
            """
            self.node_label_top = checked
            if checked:
                #Reset all node sizes to default so the fixed offset is uniform across all nodes
                self.node_sizes.clear()
                slider.blockSignals(True)                                                   #Visual update only: avoid the resize handler (and its warning)
                slider.setValue(self.NODE_SIZE_DEFAULT)
                slider.blockSignals(False)
                size_value_label.setText(str(self.NODE_SIZE_DEFAULT))
            slider.setEnabled(not checked)
            size_value_label.setEnabled(not checked)
            _update_label_pos_btn(checked)
            self.redraw_graph()

            #STEP: Persist node_label_top and cleared node_sizes into boon.meta immediately
            self._sync_node_sizes_to_boon()

            #STEP: Record label-position change in undo/redo history
            if hasattr(self, "_boonify_parent"):
                self._boonify_parent.add_color_history()

        label_pos_btn.toggled.connect(_toggle_label_position)
        label_pos_row.addWidget(label_pos_btn)
        label_pos_row.addStretch()
        layout.addLayout(label_pos_row)

        #STEP: Add informational hint
        hint = QLabel("(Top resets all sizes to default)")
        hint.setStyleSheet("font-size: 9px; color: #999999; font-style: italic;")
        hint.setAlignment(Qt.AlignCenter)
        layout.addWidget(hint)

        #STEP: Attach panel widget to resize menu
        container.setLayout(layout)
        widget_action = QWidgetAction(self.resize_menu)
        widget_action.setDefaultWidget(container)
        self.resize_menu.addAction(widget_action)

    def _resize_increase(self):
        """
        Increases the display size of all currently selected nodes by one step.
        Node sizes cannot exceed NODE_SIZE_MAX.
        Redraws the graph and refreshes the resize palette to reflect the updated state.

        :return: None
        """
        if not self.selected_nodes:
            QMessageBox.warning(None, "No Selection", "Please select a node to resize.")
            return

        #STEP: Increment each selected node's size, capped at NODE_SIZE_MAX
        for node in self.selected_nodes:
            current = self.node_sizes.get(node, self.NODE_SIZE_DEFAULT)
            self.node_sizes[node] = min(self.NODE_SIZE_MAX, current + self.NODE_SIZE_STEP)

        self.redraw_graph()
        self.build_resize_palette()
        self.resize_menu.popup(self.resize_menu.pos())

        #STEP: Persist and record in history
        self._sync_node_sizes_to_boon()
        if hasattr(self, "_boonify_parent"):
            self._boonify_parent.add_color_history()

    def _resize_decrease(self):
        """
        Decreases the display size of all currently selected nodes by one step.
        Size is floored at NODE_SIZE_DEFAULT.
        Redraws the graph and refreshes the resize palette to reflect the updated state.

        :return: None
        """
        if not self.selected_nodes:
            QMessageBox.warning(None, "No Selection", "Please select a node to resize.")
            return

        #STEP: Decrement each selected node's size, floored at NODE_SIZE_DEFAULT
        for node in self.selected_nodes:
            current = self.node_sizes.get(node, self.NODE_SIZE_DEFAULT)
            self.node_sizes[node] = max(self.NODE_SIZE_DEFAULT, current - self.NODE_SIZE_STEP)

        self.redraw_graph()
        self.build_resize_palette()
        self.resize_menu.popup(self.resize_menu.pos())

        #STEP: Persist and record in history
        self._sync_node_sizes_to_boon()
        if hasattr(self, "_boonify_parent"):
            self._boonify_parent.add_color_history()

    def _sync_node_sizes_to_boon(self):
        """
        Writes the current node_sizes and node_label_top into boon.meta so that save() always
        captures the latest resize/label-position state, even when the BooN descriptor itself
        has not changed (i.e. graph_to_boon() was not called).

        :return: None
        """
        if not hasattr(self, "boon") or self.boon is None:
            return

        #STEP: Ensure boon.meta exists
        if not hasattr(self.boon, "meta") or self.boon.meta is None:
            self.boon.meta = {}

        #STEP: Build reverse map from int node ID to symbol string
        id_to_symbol = {
            node_id: symbols(label)
            for node_id, label in self.node_labels.items()
            if isinstance(label, str) and label.strip()
        }

        #STEP: Serialize node_sizes under string keys (JSON-safe)
        node_sizes_by_symbol = {}
        for node_id, size in self.node_sizes.items():
            if node_id in id_to_symbol:
                node_sizes_by_symbol[str(id_to_symbol[node_id])] = size
        self.boon.meta["node_sizes"] = node_sizes_by_symbol

        #STEP: Persist node_label_top so it survives save/load
        self.boon.meta["node_label_top"] = getattr(self, "node_label_top", False)

        #STEP: Serialize edge_family_colors under (label, label) string keys so save/load preserves family color assignments
        efc = getattr(self, "edge_family_colors", {})
        efc_by_label = {}
        for (u_id, v_id), color in efc.items():
            u_lbl = self.node_labels.get(u_id) if isinstance(u_id, int) else u_id        #Already a label string if not int
            v_lbl = self.node_labels.get(v_id) if isinstance(v_id, int) else v_id
            if u_lbl is not None and v_lbl is not None:
                efc_by_label[f"{u_lbl}\t{v_lbl}"] = list(color)                          #Tab-separated label pair as dict key (JSON-safe); color as list
        self.boon.meta["edge_family_colors"] = efc_by_label

        #STEP: Also mirror these serialized meta entries into the parent Boonify.boon.meta
        parent = getattr(self, "_boonify_parent", None)
        try:
            if parent is not None and hasattr(parent, "boon") and parent.boon is not None:
                if not hasattr(parent.boon, "meta") or parent.boon.meta is None:
                    parent.boon.meta = {}
                parent.boon.meta["node_sizes"] = node_sizes_by_symbol
                parent.boon.meta["node_label_top"] = getattr(self, "node_label_top", False)
                parent.boon.meta["edge_family_colors"] = efc_by_label
        except Exception:
            pass

    def set_family_color(self, color_value):
        """
        Set a family color for the selected edge.
        Stores the RGB color in edge_family_colors, redraws, then records a color-only history snapshot 
        via add_color_history so that each individual color assignment is independently undoable/redoable. 
        Requires an edge to be selected.
        """
        if not self.selected_edge:                                                          #Show error: if no edge selected
            QMessageBox.warning(None, "No edge selected", "Select an edge first.")
            return
        
        #STEP: Convert color value to normalised RGB and store it
        color = QColor(color_value)
        rgb = (color.redF(), color.greenF(), color.blueF())
        if not hasattr(self, "edge_family_colors"):
            self.edge_family_colors = {}

        edge = self.selected_edge
        self.edge_family_colors[edge] = rgb                                                 #Map selected edge to its family color

        self.redraw_graph()
        self.graph_changed.emit()                                                           #Family colors define the clauses: rebuild the formulas
        self._sync_node_sizes_to_boon()                                                     #Persist family color assignment into boon.meta so Save/Load captures it
        if hasattr(self, "_boonify_parent"):                                                #Store a color-only history for undo/redo
            self._boonify_parent.add_color_history()

    def _wrap_node_label(self, label, max_length=7):
        """
        Wraps a node label at natural separators: _, -, /, :
        Only wraps if the label exceeds max_length characters. Each segment becomes a new line.

        :param label: Original node label string.

        :param max_length: Character threshold above which wrapping is applied.
        :rtype: str
        """
        if len(label) <= max_length:                                                        #No wrap for short labels
            return label

        separators = {'_', '-', '/', ':'}
        lines = []
        current = ""
        last_break_index = -1

        #STEP: Scan characters to track last break point
        for i, ch in enumerate(label):
            current += ch
            if ch in separators:
                last_break_index = len(current)                                             #Store position of last separator

            #STEP: Wrap when label exceed max_length
            if len(current) > max_length:
                if last_break_index != -1:                                                  #Break at last separator
                    lines.append(current[:last_break_index])
                    current = current[last_break_index:]
                    last_break_index = -1
                else:                                                                       #No separator found: force break
                    lines.append(current)
                    current = ""
        if current:
            lines.append(current)                                                           #Append remaining text as last line
        return "\n".join(lines)



#DEF: Network conversion layer
class Network:
    """
    Conversion layer between Graph and BooN.
    Handles transformation between GUI graph representation and BooN model.
    """

    def __init__(self):
        """
        Initializes the Network conversion layer with an empty BooN model.
        """
        self.boon = BooN()

    def graph_to_boon(self, graph_editor, current_boon=None):
        """
        Converts GUI graph into BooN using BooN.from_ig() (correct logical semantics).

        Family color semantics (clause grouping):
        Edges that share the same family color AND point to the same target node belong to the SAME AND-clause
        (same module index). Edges with different family colors each form their own separate clause,
        joined by OR in the final DNF formula (alternative regulation).

        White / BASIC_FAMILY_COLOR edges pointing to the same target all share the SAME clause index
        (cooperative regulation: all white edges are AND'd together into one clause).
        Only when non-white family colors are present does OR-separation (alternative regulation) apply.

        Module sign follows edge sign exactly (from_ig convention):
          positive sign  ->  positive module index (+k)  ->  literal = src
          negative sign  ->  negative module index (-k)  ->  literal = Not(src)

        Example::

          x1->x2  pink   sign+1  -> module +1
          x3->x2  pink   sign-1  -> module -1  (same clause 1, negated literal)
          x4->x2  yellow sign+1  -> module +2  (separate clause 2)
          => x2 = (x1 & ~x3) | x4
        """
        graph = graph_editor.graph

        #STEP: Build symbol mapping (node integer ID -> sympy Symbol)
        id_to_symbol = {}
        for node_id, label in graph_editor.node_labels.items():
            if isinstance(label, str):
                label = label.strip()
            if not label:
                label = f"x{node_id}"                                                       #Fallback label if empty
            id_to_symbol[node_id] = symbols(label)

        #STEP: Assign module indices driven by family color grouping
        incoming = {}                                                                       #target_id -> list of (src_id, family_color_tuple)
        for u, v in graph.edges():
            if u not in id_to_symbol or v not in id_to_symbol:
                continue
            fc = tuple(graph_editor.edge_family_colors.get((u, v), BASIC_FAMILY_COLOR))
            incoming.setdefault(v, []).append((u, fc))

        edge_module_index = {}                                                              #(src_id, tgt_id) -> signed int
        white = tuple(BASIC_FAMILY_COLOR)
        for tgt, edges_in in incoming.items():
            color_to_clause = {}                                                            #Color tuple -> clause index (unsigned)
            next_idx = [1]                                                                  #Mutable 1-based counter shared across this target

            for src, fc in edges_in:
                if fc == white:                                                             #White (no family assigned): all white edges share a single clause (cooperative AND)
                    if white not in color_to_clause:                                        #Allocate a fresh clause index for the white group on first encounter
                        color_to_clause[white] = next_idx[0]
                        next_idx[0] += 1
                    clause_idx = color_to_clause[white]
                else:                                                                       #Non-white color: each distinct color is its own OR-clause (alternative regulation)
                    key = tuple(round(c, 6) for c in fc)
                    if key not in color_to_clause:
                        color_to_clause[key] = next_idx[0]
                        next_idx[0] += 1
                    clause_idx = color_to_clause[key]

                sign = graph[src][tgt].get("sign", 1)
                edge_module_index[(src, tgt)] = clause_idx if sign >= 0 else -clause_idx    #Positive sign -> +clause_idx  (literal = source symbol)
                                                                                            #Negative sign -> -clause_idx  (literal = Not(source symbol))

        #STEP: Build the interaction graph with correctly signed module sets
        ig = nx.DiGraph()
        for symbol in id_to_symbol.values():
            ig.add_node(symbol)
        for u, v in graph.edges():
            if u not in id_to_symbol or v not in id_to_symbol:
                continue

            src_symbol = id_to_symbol[u]
            tgt_symbol = id_to_symbol[v]
            sign = graph[u][v].get("sign", 1)
            mod_idx = edge_module_index.get((u, v), 1 if sign >= 0 else -1)                 #Module is a singleton set {+k} or {-k}
            module = {mod_idx}
            edge_label = graph_editor.edge_labels.get((u, v), "")
            edge_color  = graph_editor.edge_colors.get((u, v), (0, 0, 0))
            ig.add_edge(
                src_symbol,
                tgt_symbol,
                sign=sign,
                module=module,
                label=edge_label,
                color=edge_color
            )

        #STEP: Let BooN.from_ig() do the logical construction (DNF from modules)
        try:
            boon = BooN.from_ig(ig)

        except Exception:                                                                   #Fallback: preserve the current BooN if conversion fails
            if current_boon is not None:
                boon = current_boon.copy()
            else:
                boon = BooN()

        #STEP: Store node positions
        boon.pos = {}

        for node_id, position in graph_editor.node_positions.items():
            if node_id in id_to_symbol:
                boon.pos[id_to_symbol[node_id]] = position                                  #Map symbol to its canvas position

        #STEP: Serialize node_sizes into boon.meta so they are saved with the file
        if not hasattr(boon, "meta") or boon.meta is None:
            boon.meta = {}
        node_sizes_by_symbol = {}
        for node_id, size in graph_editor.node_sizes.items():
            if node_id in id_to_symbol:
                node_sizes_by_symbol[str(id_to_symbol[node_id])] = size                     #Store under string key for JSON-safe serialization
        boon.meta["node_sizes"] = node_sizes_by_symbol

        #STEP: Persist node_label_top so it survives save/load
        boon.meta["node_label_top"] = getattr(graph_editor, "node_label_top", False)

        return boon
    
    def boon_to_graph(self, boon, graph_editor):
        """
        Converts a BooN logical model back into a GUI graph representation.
        This method rebuilds nodes, edges, positions, labels, and visual properties from the BooN interaction 
        graph and updates the graph editor accordingly.

        :param boon: BooN model to convert.

        :param graph_editor: Target GUI graph editor to populate.

        :return: None
        """
        ig = boon.interaction_graph

        #STEP: Clear existing graph editor state before rebuilding
        graph_editor.graph.clear()
        graph_editor.node_positions.clear()
        graph_editor.node_labels.clear()
        graph_editor.edge_colors.clear()

        symbol_to_id = {}

        #STEP: Rebuild nodes
        for index, node in enumerate(ig.nodes(), start=1):
            symbol_to_id[node] = index
            graph_editor.graph.add_node(index)
            graph_editor.node_labels[index] = str(node)                                     #Display label from symbol name
            if hasattr(boon, "pos") and node in boon.pos:
                graph_editor.node_positions[index] = boon.pos[node]                         #Use stored BooN position
            else:
                graph_editor.node_positions[index] = (0.0, 0.0)                             #Fallback to origin: if no position stored

        #STEP: Rebuild edges
        for src, tgt, data in ig.edges(data=True):
            src_id = symbol_to_id[src]
            tgt_id = symbol_to_id[tgt]
            sign = data.get("sign", 1)
            graph_editor.graph.add_edge(src_id, tgt_id, sign=sign)
            graph_editor.edge_colors[(src_id, tgt_id)] = graph_editor.SIGNCOLOR.get(sign, "black")  #Sign-based display color
            graph_editor.edge_modules[(src_id, tgt_id)]= data.get("module", {1})            #Module set for BooN logic
            graph_editor.edge_labels[(src_id, tgt_id)]= data.get("label", "")               #Edge display label
        graph_editor.redraw_graph()                                                         #Refresh canvas with newly built graph



#DEF: Widget classes
class Help(QMainWindow):
    """
    Defines the Help class, a window in the application providing a user interface for
    displaying help documentation.
    This class inherits from QMainWindow and is used to load and display an HTML-based
    help file using QWebEngineView. It provides a 'Close' button to dismiss the window.
    The layout and UI components are loaded from a .ui file.

    :ivar CloseButton: The button widget used to close the help window.
    :type CloseButton: QPushButton

    :ivar web: A web engine view widget used to render and display the help HTML content.
    :type web: QWebEngineView

    :ivar WebContainer: The container widget to hold the QWebEngineView displaying the help content.
    :type WebContainer: QWidget
    """
    def __init__(self, parent=None):
        super(Help, self).__init__(parent)                                                  #Initialize the parent class (QMainWindow)
        help_ui = os.path.join(os.path.dirname(__file__), 'BooNGui', 'help.ui')
        loadUi(help_ui, self)                                                               #Load Qt designer .ui file for layout and widgets
        self.setMinimumSize(QSize(600, 600))                                                #Min size of help window
        self.CloseButton.clicked.connect(lambda _: self.close())                            #Close button from .ui file
        self.web = QWebEngineView(self)                                                     #Web browser like widget
        self.WebContainer.addWidget(self.web)                      
        help_html = os.path.join(os.path.dirname(__file__), 'BooNGui', 'Help.html')
        with open(help_html, 'r', encoding='utf-8') as f:                                   #Open local html file
            html = f.read()
        self.web.setHtml(html, QUrl.fromLocalFile(help_html))                               #Load html into web view; base URL resolves relative resources



class View(QDialog):
    """
    Dialog showing Boolean formulas in a table, allowing editing, validation and conversions.

    Integrates with a parent `Boonify` instance to obtain formulas and variables for display.

    :ivar style: Style of the formulas displayed in the view.
    :type style: str

    :ivar parent: Reference to the parent `Boonify` instance.
    :type parent: object

    :ivar formulas: List of formula input fields linked to variables.
    :type formulas: list[QLineEdit]
    """
    def __init__(self, parent=None):
        """
        Initializes the View dialog, loads the UI layout, sets up signal connections, and populates the formula 
        table for the current BooN.

        :param parent: The parent Boonify instance providing BooN data.
        :type parent: Boonify or None
        """
        super(View, self).__init__(parent)                                                  #Initialize parent class (QDialog)
        view_ui = os.path.join(os.path.dirname(__file__), 'BooNGui', 'view.ui')
        loadUi(view_ui, self)
        self.setGeometry(300, 300, 750, 500)                                                #Set size and position of view window
        self.style = LOGICAL                                                                #Style of the formulas, by default: logical
        self.parent = parent                                                                #Parent = Boonify class
        self.formulas = None                                                                #Store input: formulas of BooN

        #STEP: Set the functions related to signals             
        self.CloseButton.clicked.connect(lambda _: self.close())                            #Button to close view
        self.DnfButton.clicked.connect(self.convertdnf)                                     #Button to convert formulas into DNF

        #STEP: Combox Box of style             
        self.Style.activated.connect(self.cb_styling)                                       #Change display style

        #STEP: Forbid the edition of BooNContent
        self.BooNContent.setEditTriggers(QtWidgets.QTableWidget.NoEditTriggers)             #Make table read-only but formulas are editable

        #STEP: Resize columns of the table to content
        self.BooNContent.setColumnWidth(1, 500)

        #STEP: Fix size of the formula columns
        header = self.BooNContent.horizontalHeader()
        header.setSectionResizeMode(QHeaderView.Stretch)
        header.setSectionResizeMode(0, QHeaderView.ResizeToContents)                        #Col 0 -> small, formula type
        header.setSectionResizeMode(1, QHeaderView.ResizeToContents)                        #Col 1 -> variable name
        header.setStretchLastSection(True)              
        header.setSectionResizeMode(2, QHeaderView.Interactive)                             #Col 2 -> formula (resizable width)

        self.initialize_view()                                                              #Build the formula table

    def initialize_view(self):
        """
        Initializes and populates the view with formula fields and their respective descriptions and
        attributes. This method configures a table to display rows of formulas, sets the required
        text and style for each formula, and identifies and specifies the type of logical formulation.
        """
        theboon = self.parent.boon

        #STEP: Initialize the formula fields
        nbrow = len(theboon.desc)
        self.BooNContent.setRowCount(nbrow)                                                 #Set one row per variable 
        self.formulas = [QLineEdit() for _ in range(nbrow)]
        for row, f in enumerate(self.formulas):
            f.editingFinished.connect(lambda r=row: self.change_formula(r))                 #Update formula when editing is done; the row is bound (currentRow() does not follow cell widgets)
            f.setFrame(False)

        #STEP: Fill the table each row
        for row, var in enumerate(theboon.desc):
            item = QTableWidgetItem(str(var)) 
            item.setTextAlignment(Qt.AlignCenter) 
            self.BooNContent.setItem(row, 1, item)                                          #Variable name 
            self.formulas[row].setText(logic.prettyform(theboon.desc[var], style=self.style))
            self.BooNContent.setCellWidget(row, 2, self.formulas[row])                      #Converts formula
            #STEP: Detect and label formula form
            if is_dnf(theboon.desc[var]):                                                   #Disjunctive Normal Form
                form = "DNF"                
            elif is_cnf(theboon.desc[var]):                                                 #Conjunctive Normal Form
                form = "CNF"                
            elif is_nnf(theboon.desc[var]):                                                 #Negation Normal Form
                form = "NNF"                
            else:                                                                           #General formula
                form = "ALL"
            item = QTableWidgetItem(form)
            item.setTextAlignment(Qt.AlignHCenter)
            self.BooNContent.setItem(row, 0, item)                                          #Formula type label

    def change_formula(self, row: int):
        """
        Update the BooN formula based on user input and refresh-related components.
        This method processes the formula input provided through the GUI, verifies its syntax and the validity of the
        variables involved, and updates the associated BooN data structure if the formula passes all checks.
        It also records the change in the history and refreshes related components to reflect the changes.
        In case of errors, appropriate error messages are displayed to the user.

        :param row: The row of the edited formula.
        :type row: int
        :return: None
        """
        theboon = self.parent.boon
        if row >= len(theboon.desc):                                                        #Stale widget (the BooN changed meanwhile)
            return
        variable = list(theboon.desc.keys())[row]                                           #Variable of the modified formula
        text = self.formulas[row].text()                                                    #Get the text of the line edit formula

        #STEP: Check the names before parsing (otherwise names such as S or E are silently taken as sympy objects)
        known = {str(v) for v in theboon.variables} | FORMULA_NAMES
        unknown = set(re.findall(r"[A-Za-z_]\w*", text)) - known
        if unknown:
            QMessageBox.critical(self, "VARIABLES ERROR", f"The following variables do not exist:\n{', '.join(sorted(unknown))}\nThe formula is not changed.")
            return

        try:
            #The BooN variables are given explicitly so that names such as S, E, I or Q are not taken as sympy objects.
            formula = parse_expr(text, local_dict={str(v): v for v in theboon.variables})   #Converts input/string into symbolic expression(formula)
        except Exception:                                                                   #Show error: if invalid expression (SyntaxError, TokenError, TypeError...)
            QMessageBox.critical(self, "SYNTAX ERROR", "Syntax Error.\nThe formula is not changed.\nTIP: please select the Python output form. ")
            return

        if isinstance(formula, bool):                                                       #Bool constant: no variables
            variables = set()
        elif hasattr(formula, "free_symbols"):                                              #Get the variables used in the formula
            variables = formula.free_symbols
        else:                                                                               #Not a Boolean expression (e.g. a number)
            QMessageBox.critical(self, "SYNTAX ERROR", f"'{text}' is not a Boolean formula.\nThe formula is not changed.")
            return
        diff = variables.difference(theboon.variables)
        if diff:                                                                            #Show error: unknown variables
            QMessageBox.critical(self, "VARIABLES ERROR", f"The following variables do not exist:\n{diff}\nThe formula is not changed.")
            return

        if not logic.is_and_or_not(formula):                                                #Xor, Implies, Equivalent... are excluded from the BooN formulas: convert to DNF
            formula = to_dnf(formula, simplify=True, force=True)

        if formula == theboon.desc[variable]:                                               #Unchanged (editingFinished is also emitted on focus loss)
            return

        #STEP: Apply the formula, record it in the history and refresh UI
        theboon.desc[variable] = formula                                                    #Update formulas
        QTimer.singleShot(0, self.parent.update_from_formulas)                              #Deferred: the refresh replaces the line edit emitting this signal

    def cb_styling(self):
        """
        Updates the current styling for the component based on the selected style and refreshes the view.

        :return: None
        """
        self.style = STYLE[self.Style.currentText()]                                        #Apply new selected display style
        self.initialize_view()                                                              #Refresh the view with new style applied

    def convertdnf(self):
        """
        Converts the current BooNn into Disjunctive Normal Form (DNF)
        and refreshes the view accordingly.

        :return: None
        """
        try:
            #STEP: Pre-parse any string formulas to ensure they are symbolic expressions
            if hasattr(self.parent.boon, "desc"):
                for k, v in self.parent.boon.desc.items():
                    if isinstance(v, str):
                        self.parent.boon.desc[k] = parse_expr(v)
            self.parent.boon.dnf()                                                          #Convert all BooN formulas into DNF
            self.parent.update_from_formulas()                                              #Record the change and refresh all views (including this one)
        except Exception as e:
            QMessageBox.critical(
                self,
                "DNF ERROR",
                f"DNF conversion failed:\n{str(e)}"
                )



class StableStates(QDialog):
    """
    A dialog for displaying and managing stable states in a computational model. 
    This class represents a graphical interface for visualizing stable states of a Boolean network model. 
    It allows users to switch between different display styles, such as icons or textual representation, 
    for better interpretation of the stable states.

    :ivar parent: Reference to the parent widget or application component.
    :type parent: QWidget

    :ivar style: The display style for representing stable states (e.g., 'Icon Boolean').
    :type style: str

    :ivar datamodel: The data model used for organizing and displaying stable states.
    :type datamodel: QStandardItemModel
    """
    def __init__(self, parent=None):

        #STEP: initialize parent class (QDialog)
        super(StableStates, self).__init__(parent)
        stables_ui = os.path.join(os.path.dirname(__file__), 'BooNGui', 'stablestates.ui')
        loadUi(stables_ui, self)
        self.setGeometry(300, 300, 500, 700)
        self.parent = parent
        self.style = 'Icon Boolean'                                                         #Default display style
        self.datamodel = None                                                               #Store the data model for stable states
        
        #STEP: Connect button and combo box signals
        self.CloseButton.clicked.connect(lambda _: self.close())
        self.Style.activated.connect(self.cb_styling)
        Hheader = self.StableStatesPanel.horizontalHeader()
        Hheader.setSectionResizeMode(QHeaderView.ResizeToContents)

        self.stablestates()                                                                 #Build the stable states table

    def cb_styling(self):
        """
        Updates the formula display style and refreshes the view.
        This method changes how formulas are rendered (logical, Python, etc.) based on user selection.

        :return: None
        """
        self.style = self.Style.currentText()                                               #Change the display style
        self.stablestates()                                                                 #Update stable states view with applied style

    def stablestates(self):
        """
        Generates and sets up a data model to visualize stable states of a system. 
        This method processes the stable states of a parent object's model and organizes them into a table-like 
        structure using a Qt `QStandardItemModel`. Each row represents a variable, and each column corresponds 
        to a stable state. The presentation style of the data (e.g., icons, boolean values, or integers) is
        determined by the specified `style` attribute of the object.

        :return: None
        """
        theboon = self.parent.boon                                                          #Get current BooN of parent
        variables = sorted(theboon.variables, key=str)                                      #List of variables names in the model (deterministic order)
        stablestates = theboon.stable_states                                                #List of stable_states (dict: var name -> bool value)

        #STEP: Define a model of data to store stable states
        self.datamodel = QStandardItemModel()                                               #Initialize data model for stable states
        self.datamodel.setRowCount(len(variables))                                          #Set nb of rows = nb variables
        self.datamodel.setVerticalHeaderLabels([str(var) for var in variables])             #Set var names as row headers

        #STEP: Fill the table: each stable state becomes a column
        for stable in stablestates:                                                         #Each stable = 1 column
            column = []             
            for var in variables:                                                           #Each var = 1 row
                val = stable.get(var, stable.get(str(var), None))
                val01 = "-" if val is None else str(int(bool(val)))                         #0/1 form (undefined value shown as -)
                icon = QIcon()
                icon.addPixmap(QtGui.QPixmap(ICON01[val]), QtGui.QIcon.Normal, QtGui.QIcon.Off) #Icon for True/False/None
                icon.pixmap(QSize(64, 64))

                #STEP: Build table cell item according to selected display style
                match self.style:
                    case 'Icon':                                                            #Icon only
                        item = QStandardItem(icon, "")              
                    case 'Icon Boolean':                                                    #Icon + True/False 
                        item = QStandardItem(icon, str(val))                
                    case 'Icon 0-1':                                                        #Icon + 0/1
                        item = QStandardItem(icon, val01)
                    case 'Boolean':                                                         #True/False only
                        item = QStandardItem(str(val))              
                    case '0-1':                                                             #0/1 only
                        item = QStandardItem(val01)
                    case _:                                                                 #Show error: if unknown style -> set default style
                        item = QStandardItem("None")
                item.setTextAlignment(Qt.AlignCenter)
                column.append(item)
            self.datamodel.appendColumn(column)
        self.StableStatesPanel.setModel(self.datamodel)



class Model(QMainWindow):
    """
    A Model class for managing and visualizing network dynamics using a GUI interface.

    :ivar parent: Reference to the parent window or application.
    :type parent: Any

    :ivar mode: Represents the selected mode of dynamics (asynchronous or synchronous).
    :type mode: Enum or equivalent

    :ivar layout_function: Defines the network layout function to be used for visualization.
    :type layout: Callable

    :ivar canvas: Matplotlib widget for rendering the network visualization.
    :type canvas: matplotlib.backends.backend_qt5agg.FigureCanvas
    """
    def __init__(self, parent=None):
        """
        Initializes the Model window, loads the UI layout, connects radio buttons and the layout combo box, 
        and renders the initial dynamics model.

        :param parent: The parent Boonify instance providing BooN data.
        :type parent: Boonify or None
        """
        super(Model, self).__init__(parent)
        model_ui = os.path.join(os.path.dirname(__file__), 'BooNGui', 'model.ui')
        loadUi(model_ui, self)
        self.setGeometry(300, 300, 600, 600)
        self.CloseButton.clicked.connect(lambda _: self.close())

        #STEP: Initialize attributes
        self.parent = parent
        self.mode = boon.asynchronous                                                       #Default dynamics mode: asynchronous
        self.layout_function = boon.hypercube_layout                                        #Default graph layout: hypercube (named so as not to shadow QMainWindow.layout())

        #STEP: Connect Matplotlib canvas to GUI layout
        self.canvas = FigureCanvas(Figure())
        self.ModelCanvas.addWidget(self.canvas)
        self.canvas.axes = self.canvas.figure.add_subplot(111)

        #STEP: Connect mode radio buttons and layout combo box to their handlers
        self.AsynchronousButton.clicked.connect(self.rb_mode)
        self.SynchronousButton.clicked.connect(self.rb_mode)
        self.NetworkLayout.activated.connect(self.cb_network_layout)

        #STEP: Render the initial model on the canvas
        self.modeling()

    def rb_mode(self):
        """
        Determine and set the mode of operation based on user selection from the interface. This function checks the state
        of radio buttons to assign either an asynchronous or synchronous mode. The established mode is then used for
        further modeling via a further call to the `modeling` method.

        :return: None
        """
        #STEP: Read the selected radio button and update the dynamics mode
        if self.AsynchronousButton.isChecked():
            self.mode = boon.asynchronous                                                   #Asynchronous mode selected
        elif self.SynchronousButton.isChecked():
            self.mode = boon.synchronous                                                    #Synchronous mode selected
        else:
            pass
        self.modeling()                                                                     #Recompute and redraw the model with the new mode

    def cb_network_layout(self):
        """
        Adjusts the network layout based on the selected option and applies the corresponding layout algorithm to the network. 
        The method retrieves the currently selected network layout from a user interface component, maps it to an appropriate algorithm, and configures 
        the network's visualization layout accordingly. It also invokes an update via the `modeling` method to apply and reflect the changes.

        :return: None
        """
        #STEP: Map the selected layout name to its corresponding NetworkX/BooN function
        layout = self.NetworkLayout.currentText()
        match layout:
            case "Hypercube":
                self.layout_function = boon.hypercube_layout
            case "Circular":
                self.layout_function = nx.circular_layout
            case "Spring":
                self.layout_function = nx.spring_layout
            case "Kamada Kawai":
                self.layout_function = nx.kamada_kawai_layout
            case "Random":
                self.layout_function = nx.random_layout
            case _:                                                                         #Show error: unknown layout
                logic.errmsg("Internal Error - Unknown layout - Please contact the development team", "cb_network_layout")
        self.modeling()                                                                     #Recompute and redraw the model with the new mode

    def modeling(self):
        """
        Compute the model of dynamics.

        :return: None
        """
        #STEP: Clear the axes and compute the dynamics model
        self.canvas.axes.clear()
        self.canvas.axes.axis('off')

        model = self.parent.boon.model(mode=self.mode)
        if model.number_of_nodes() == 0:                                                    #Empty datamodel = empty BooN, nothing to draw
            self.canvas.draw_idle()                                                         #Still clear the previous drawing
            return

        #STEP: Apply chosen layout and render model on canvas
        layout = self.layout_function(model)
        self.parent.boon.draw_model(model, pos=layout, ax=self.canvas.axes)
        self.canvas.draw_idle()



class Controllability(QMainWindow):
    """
    Controllability class for managing user interactions with the controllability widget of the GUI application.
    This class is responsible for initializing the controllability user interface, handling the interactions 
    between destiny and observers tables, computing control actions based on user selections, and managing the 
    graphical representation of these actions.

    :ivar parent: Parent window instance for the controllability widget.
    :type parent: QWidget

    :ivar actions: Stores the calculated control actions, if any.
    :type actions: list or None

    :ivar row: Index of the currently selected solution in control actions, if applicable.
    :type row: int or None
    """
    def __init__(self, parent=None):
        super(Controllability, self).__init__(parent)
        controllability_ui = os.path.join(os.path.dirname(__file__), 'BooNGui', 'controllability.ui')
        loadUi(controllability_ui, self)
        self.setGeometry(900, 300, 800, 600)
        self.parent = parent
        self.actions = None                                                                 #Current control actions
        self.error = None                                                                   #Error raised by the last computation, if any
        self.row = None                                                                     #Index of the selected solution row
        self.variables = []                                                                 #Variables in table row order

        #STEP: Define signals (connected once: initialize_controllability is called again at each refresh)
        self.parent.worker.finished.connect(self.display_controllability)                  #Queued to the main thread for Qt model building
        self.Observers.itemChanged.connect(self.observers_to_destiny)
        self.ControlButton.clicked.connect(self.start_controllability)
        self.ControlActions.clicked.connect(self.select_action)
        self.ActButton.clicked.connect(self.actupon)

        header = self.ControlActions.header()
        header.setSectionResizeMode(QHeaderView.ResizeToContents)
        header.setStretchLastSection(True)

        self.initialize_controllability()

    def initialize_controllability(self):
        """
        Initialize the controllability tables (Destiny and Observers) from the current BooN.

        :return: None
        """
        theboon = self.parent.boon
        self.variables = sorted(theboon.variables, key=str)                                 #Deterministic row order shared by both tables
        nbrow = len(self.variables)
        self.actions = None
        self.row = None
        self.ControlActions.setModel(QStandardItemModel())                                  #Former solutions refer to the former BooN

        #STEP: Initialize Destiny page
        self.Destiny.setRowCount(nbrow)
        self.Destiny.resizeColumnToContents(0)                                              #Fit size to content
        self.Destiny.horizontalHeader().setStretchLastSection(True)

        for row, var in enumerate(self.variables):
            item = QTableWidgetItem(str(var))                                               #Add variable name
            item.setTextAlignment(Qt.AlignCenter)
            self.Destiny.setItem(row, 0, item)

            #Add a status combo box for each variable (None / True / False)
            statusbox = QComboBox(self)
            statusbox.addItems(["None", "True", "False"])
            statusbox.setItemIcon(0, QIcon(ICON01[None]))                                   #Icon for None
            statusbox.setItemIcon(1, QIcon(ICON01[True]))                                   #Icon for True
            statusbox.setItemIcon(2, QIcon(ICON01[False]))                                  #Icon for False

            self.Destiny.setCellWidget(row, 1, statusbox)                                   #Insert the status box in the table and connect it
            statusbox.currentTextChanged.connect(lambda label, r=row: self.destiny_to_observers(r, label))

        #STEP: Initialize the observer page
        self.Observers.blockSignals(True)                                                   #Filling the table must not trigger observers_to_destiny
        self.Observers.setRowCount(nbrow)
        self.Observers.horizontalHeader().setStretchLastSection(True)

        for row, var in enumerate(self.variables):
            obschkbox = QTableWidgetItem(str(var))                                          #Add checkbox
            obschkbox.setFlags(Qt.ItemIsUserCheckable | Qt.ItemIsEnabled)
            obschkbox.setCheckState(Qt.Unchecked)
            self.Observers.setItem(row, 0, obschkbox)
        self.Observers.blockSignals(False)

        #STEP: Set the destiny page as default
        self.ControlPanel.setCurrentIndex(0)

        #STEP: Set size of columns
        for i in range(self.ControlPanel.count()):
            self.ControlPanel.widget(i).adjustSize()

    def destiny_to_observers(self, row: int, label: str):
        """
        Updates the check state of the item in the `Observers` table corresponding to the modified row
        of the `Destiny` table.

        :param row: Row of the modified status box.
        :type row: int
        :param label: If "None", the item is unchecked; otherwise it is checked.
        :type label: str

        :return: None
        """
        item = self.Observers.item(row, 0)
        if item is None:
            return

        #STEP: Sync observer checkbox with destiny status selection
        if label == "None":
            item.setCheckState(Qt.Unchecked)                                                #No target: unmark observer
        else:
            item.setCheckState(Qt.Checked)                                                  #Target set: mark as observed

    def observers_to_destiny(self, chkitem):
        """
        Synchronizes the Destiny table when an observer checkbox is unchecked.
        When a variable is unchecked in the Observers table, its corresponding entry in the Destiny table is reset to "None".

        :param chkitem: The table item whose check state changed.
        :type chkitem: QTableWidgetItem

        :return: None
        """
        row = chkitem.row()

        #STEP: Reset the Destiny status to "None" when the corresponding observer is unchecked
        if chkitem.checkState() == Qt.Unchecked:
            combobox = self.Destiny.cellWidget(row, 1)
            if combobox is not None:
                combobox.setCurrentText("None")                                             #Clear target status when observer is unselected

    def start_controllability(self):
        """
        Reads the query from the widgets (main thread) and starts the computation of the control actions
        in the background worker thread.

        :return: None
        """
        #STEP: Get the observers: unobserved variables are controllable
        controlledvars = set()
        for row, var in enumerate(self.variables):
            if self.Observers.item(row, 0).checkState() != Qt.Checked:
                controlledvars.add(var)

        #STEP: Build the goal query from Destiny table selections
        query = {}
        for row, var in enumerate(self.variables):
            match self.Destiny.cellWidget(row, 1).currentText():
                case "True":
                    query[var] = True
                case "False":
                    query[var] = False

        if not query:
            QMessageBox.warning(self, "No destiny", "Please set the Boolean value of at least one variable in the Destiny page.")
            return

        querytype = self.QueryType.currentText()
        possibility = self.Possibility.isChecked()
        necessity = self.Necessity.isChecked()
        theboon = self.parent.boon.copy()                                                   #Snapshot: the BooN may be edited during the computation

        #STEP: Run the computation in the worker thread (no Qt widget access there)
        self.ControlButton.setEnabled(False)
        self.statusBar().showMessage("Computing control actions...")
        self.parent.worker.start(lambda: self.controllability(theboon, controlledvars, query, querytype, possibility, necessity))

    def controllability(self, theboon, controlledvars, query, querytype, possibility, necessity):
        """
        The method calculates control actions required to achieve or avoid a defined goal (or state) in a system represented
        by the BooN model. The method determines the applicable control actions by analyzing a user-specified query defining
        the desired or undesired state, along with the possible variables that can be controlled.
        The result is stored in self.actions (or the error in self.error).

        #WARNING: No Qt widget calls here - this runs in a background thread.
        display_controllability() handles all Qt updates on the main thread via the finished signal.

        :param theboon: The BooN to control.
        :param controlledvars: The controllable variables.
        :param query: The target marking profile {variable: bool}.
        :param querytype: "Reach" or "Avoid".
        :param possibility: True if the possibility modality is required.
        :param necessity: True if the necessity modality is required.
        :return: None
        """
        self.actions = None
        self.error = None
        try:
            #STEP: Convert the query state profiles into minterm formula
            formula = SOPform(list(query.keys()), [query])

            #STEP: Check whether the query must be reached or avoided
            if querytype == "Avoid":
                formula = Not(formula)                                                      #Negate for avoidance

            #STEP: Create a controlled copy of the BooN for analysis
            boonctrl = theboon.copy()
            boonctrl.control(controlledvars, controlledvars)

            #STEP: Evaluate possibility and/or necessity modalities
            possible = boonctrl.possibly(formula) if possibility else True
            necessary = boonctrl.necessary(formula, trace=False) if necessity else True
            destiny = And(possible, necessary)                                              #Combine modalities into final destiny formula

            #STEP: Compute control actions from the destiny formula
            core = boonctrl.destify(destiny, trace=False, solver=LPSOLVER)
            self.actions = boon.core2actions(core)
        except Exception as e:
            self.error = e

    def display_controllability(self):
        """
        Build the Qt tree model from self.actions and update ControlActions.
        Connected to Threader.finished so it always runs on the main thread.

        :return: None
        """
        self.ControlButton.setEnabled(True)
        self.statusBar().clearMessage()
        self.row = None

        if self.error is not None:
            QMessageBox.critical(self, "Controllability error", f"The computation of the control actions failed:\n{self.error}")
            return
        if self.actions is None:                                                            #Nothing computed
            return

        #STEP: Rebuild the tree model from self.actions on the main thread
        treemodel = QStandardItemModel(0, 2)                                                #Add 2 columns: Variable + Boolean value
        treemodel.setHeaderData(0, Qt.Horizontal, "Variable")
        treemodel.setHeaderData(1, Qt.Horizontal, "Boolean value")

        root = treemodel.invisibleRootItem()
        match self.actions:
            case []:
                item = QStandardItem("No action found.")
                root.appendRow(item)
            case [[]]:                                                                      #Target profile already obtained
                item = QStandardItem("The marking profile already exists.")
                root.appendRow(item)
            case _:                                                                         #One or more control solutions found
                for i, actions in enumerate(self.actions, 1):
                    rootactions = QStandardItem("Solution {:2d}".format(i))                 #Root node for each solution

                    #Add each control action: variable + Boolean icon + Boolean value
                    for variable, value in actions:
                        value_item = QStandardItem(QIcon(ICON01[value]), str(value))
                        rootactions.appendRow([QStandardItem(str(variable)), value_item])
                    root.appendRow(rootactions)                                             #Append the solution to the tree model
        self.ControlActions.setModel(treemodel)                                             #Set the data model to tree widget enabling its display
        self.ControlActions.expandAll()

    def select_action(self, arg):
        """
        Keep the selection solution

        :return: None
        """
        #STEP: Record the selected solution index (parent row for child items, own row for root items)
        self.row = arg.parent().row() if arg.parent().row() > -1 else arg.row()

    def actupon(self):
        """
        Apply the selection actions on the BooN.

        :return: None
        """
        #STEP: Apply each control action of the selected solution to the BooN descriptor
        if self.row is None or not self.actions or self.row >= len(self.actions) or not self.actions[self.row]:
            QMessageBox.warning(self, "No solution selected", "Please select a solution to apply.")
            return

        for variable, value in self.actions[self.row]:
            self.parent.boon.desc[variable] = value                                         #Override variable formula with the control value

        #STEP: Record change in history, rebuild graph, refresh views and close dialog
        self.close()
        self.parent.update_from_formulas()



#DEF: Threading utility
class Threader(QObject):
    """
    Threader class for managing application execution within a separate thread.

    This class is designed to separate the execution of a provided application
    function into its own thread using PyQt's threading mechanism. The class
    provides functionality to start, switch, and terminate the application
    running within the thread effectively.

    :ivar finished: Signal emitted when the thread's application completes execution.
    :ivar app: The callable application to be executed within the thread.
    :type app: Callable

    :ivar qthread: The QThread instance used to run the application in a separate thread.
    :type qthread: QThread
    """
    finished = pyqtSignal()
    requested = pyqtSignal()                                                                #Internal: queued request to run the callable in the worker thread

    def __init__(self, app=lambda: None):
        """
        Represents a custom asynchronous functionality encapsulated in a QThread.
        This class initializes with a callable app function, assigns it to an internal
        property, and starts a new thread for its execution.

        :param app: A callable function that serves as the application's main function.
            Defaults to a no-op lambda function.
        :type app: Callable[[], Any]
        """
        super().__init__()
        self.app = app

        #STEP: Create the thread (named qthread so as not to shadow QObject.thread())
        self.qthread = QThread()
        self.moveToThread(self.qthread)
        self.requested.connect(self.run)                                                    #Queued connection: run() executes in the worker thread
        self.qthread.start()

    @pyqtSlot()
    def run(self):
        """
        Executes the application callable and signals completion.
        Must be triggered through start() to run in the worker thread; a direct call runs in the caller's thread.
        """
        #STEP: Execute the app callable and always emit finished, even on error
        try:
            self.app()                                                                      #Run the application
        finally:
            self.finished.emit()                                                            #Emit the end signal

    def apply(self, app):
        """
        Sets the callable executed by the worker.

        :param app: The callable to be executed.

        :return: None
        """
        self.app = app                                                                      #Replace current callable with new one

    def start(self, app=None):
        """
        Runs a callable in the worker thread (asynchronously). The finished signal is emitted at the end.

        :param app: The callable to execute; if None, the current callable is used.

        :return: None
        """
        if app is not None:
            self.app = app
        self.requested.emit()

    def quit(self):
        """
        Terminates the thread execution in an orderly manner: the event loop is stopped once the
        current computation, if any, is finished.

        :return: None
        """
        #STEP: Signal the thread to stop and block until it finishes
        self.qthread.quit()
        self.qthread.wait()                                                                 #Block until thread has fully stopped



#DEF: Main
if __name__ == "__main__":
    app = QApplication(sys.argv)
    boonify = Boonify()
    boonify.show()
    sys.exit(app.exec_())