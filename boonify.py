# Graphical interface for BooN design and analysis
# Author: Franck Delaplace
# Creation date: February 2024
import sys
import os
from tabulate import tabulate
import BooNGui.booneries_rc  # resources

import boon
from boon import BooN, SIGNCOLOR, COLORSIGN, core2actions
import logic
from logic import LOGICAL, SYMPY, MATHEMATICA, JAVA

from sympy.logic.boolalg import is_cnf, is_dnf, is_nnf
from sympy.core.symbol import Symbol
from sympy.logic.boolalg import And, Not
from sympy import SOPform, symbols
from sympy.parsing.sympy_parser import parse_expr

from netgraph import EditableGraph
import networkx as nx

from PyQt5.QtWidgets import *

from PyQt5.uic import loadUi
from PyQt5.QtGui import QIcon, QStandardItemModel, QStandardItem
from PyQt5.QtCore import Qt, QSize
from PyQt5.QtCore import QObject, QThread, pyqtSignal
from PyQt5 import QtCore, QtGui, QtWidgets
from PyQt5.QtWebEngineWidgets import QWebEngineView

import matplotlib as mpl
import matplotlib.pyplot as plt
from matplotlib.backends.backend_qt5agg import FigureCanvasQTAgg as FigureCanvas
from matplotlib.figure import Figure

mpl.use("Qt5Agg")

HSIZE: int = 10  # size of the history
STYLE: dict = {"Logical": LOGICAL, "Java": JAVA, "Python": SYMPY, "Mathematica": MATHEMATICA}
ICON01: dict = {None: ":/icon/resources/none.svg", True: ":/icon/resources/true.svg", False: ":/icon/resources/false.svg"}  # True/False icons
MODELBOUND: int = 8  # Size  bound of the dynamics model in terms of variables.

# Node names for the pattern network
REG: str = '\u03b1'  # lambda
POS: str = '\u03b2'  # alpha
NEG: str = '\u03bb'  # beta


class Boonify(QMainWindow):
    """Main Class of the GUI"""

    def __init__(self):
        super(Boonify, self).__init__()
        loadUi('BooNGui/boonify.ui', self)
        self.setGeometry(600, 100, 800, 800)

        # STEP: initialize the Gui state
        self.boon = BooN()  # Current BooN
        self.filename = ""  # Last filename
        self.history = [None] * HSIZE  # History
        self.hindex = 0  # Index of the last BooN added in the  history
        self.hupdate = False  # Flag determining whether the history is updated
        self.saved = True  # Flag determining whether a BooN is saved.
        self.QView = None  # Widget of the View
        self.QStableStates = None  # Widget of the stable states
        self.QModel = None  # Widget of the dynamics model
        self.QControllability = None  # Widget of the controllability
        self.editgraph = None  # Graph for edition
        self.disablecallback = True  # Flag indicating whether the BooN design callback function is enabled, initially disabled because the editgraph is not set up.

        # STEP:  File menu connected to callback functions
        # File
        self.ActionOpen.triggered.connect(self.open)
        self.ActionSave.triggered.connect(self.save)
        self.ActionSaveAs.triggered.connect(self.saveas)
        self.ActionImport.triggered.connect(self.importation)
        self.ActionExport.triggered.connect(self.exportation)
        self.ActionQuit.triggered.connect(self.quit)
        # Help
        self.ActionHelp.triggered.connect(self.help)
        self.ActionUndo.triggered.connect(self.undo)
        self.ActionRedo.triggered.connect(self.redo)
        # Network
        self.ActionView.triggered.connect(self.view)
        self.ActionModel.triggered.connect(self.model)
        self.ActionStableStates.triggered.connect(self.stablestates)
        self.ActionControllability.triggered.connect(self.controllability)

        # STEP: initialization of a thread for long run application --> controllability
        # the thread will be created and started.
        self.worker = Threader()

        # STEP: Initialize the Canvas for network design
        fig = plt.figure()  # plt.figure is used to create a manager
        manager = fig.canvas.manager
        self.canvas = FigureCanvas(fig)
        self.canvas.axes = self.canvas.figure.add_subplot(111)
        self.canvas.figure.subplots_adjust(left=0, bottom=0, right=1, top=1)  # adjust the window
        self.canvas.figure.canvas.manager = manager  # assign the manager in the canvas to be accessible by EditGraph.

        # STEP: Enable key_press_event events for using EditGraph:
        self.canvas.setFocusPolicy(QtCore.Qt.ClickFocus)
        self.canvas.setFocus()

        # STEP: Insert the network design figure in the main window.
        self.DesignCanvas.addWidget(self.canvas)

        # STEP: set up network design
        self.setup_design()

    # DEF: NETWORK DESIGN
    def setup_design(self):
        """Set up of the editable graph."""
        self.disablecallback = True  # Disable the design callback during the set-up.

        # STEP: Creation of the style network used for edge styling.
        # To prevent its inclusion in the BooN, the variable names are string while the other nodes are integers or symbols.
        g = nx.DiGraph([(REG, NEG), (REG, POS), (POS, POS), (NEG, NEG)])
        edge_color = {(REG, NEG): SIGNCOLOR[-1], (REG, POS): SIGNCOLOR[1], (POS, POS): SIGNCOLOR[1], (NEG, NEG): SIGNCOLOR[-1]}
        positions = {NEG: (0.25, 0.045), REG: (0.5, 0.045), POS: (0.75, 0.045)}

        # STEP: Extend this network by adding the interaction graph of the current BooN.
        ig = self.boon.interaction_graph  # Get the IG.
        for node in ig.nodes():  # Copy the nodes in the Editable graph
            g.add_node(node)
        for edge in ig.edges():  # Copy the edges in the Editable graph
            g.add_edge(edge[0], edge[1])

        # STEP: find the edge color from signs.
        signs = nx.get_edge_attributes(ig, 'sign')
        edge_color.update({edge: SIGNCOLOR[signs[edge]] for edge in signs})  # Define edge colors of editable graph from the IG.
        positions.update(self.boon.pos)  # Complete the position.

        # STEP: transfer the module ids and convert them to string labels.
        modules = nx.get_edge_attributes(ig, 'module')
        modules = {edge: " ".join([str(abs(module)) for module in modules[edge]]) for edge in modules}

        # STEP: Define the editgraph.
        self.canvas.axes.clear()
        self.editgraph = EditableGraph(g,
                                       node_labels=True,
                                       node_color='antiquewhite',
                                       node_edge_color='black',
                                       node_size=2.5,
                                       node_label_fontdict=dict(family='sans-serif', color='black', weight='semibold', size=11),
                                       node_layout=positions,
                                       arrows=True,
                                       edge_labels=modules,
                                       edge_width=1.2,
                                       node_label_offset=(0., 0.05),
                                       edge_label_position=0.75,
                                       edge_label_fontdict=dict(family='sans-serif', fontweight='bold', fontsize=8, color='royalblue'),
                                       edge_color=edge_color,
                                       ax=self.canvas.axes)
        self.disablecallback = False  # Enable the callback.

    def design(self):
        """interaction graph design callback."""

        if self.disablecallback:  # Check whether the callback is enabled otherwise return.
            return

        # STEP: Find consistent nodes corresponding to the variables in the BooN.
        # The type of consistent nodes is symbol or integer with a label.
        # WARNING: As nodes of the pattern network are strings, they are never selected as consistent nodes.
        # Dictionary of consistent nodes id:symbol, where the symbol is defined from the node label.

        idvar = {idt: symbols(text.get_text()) for idt, text in self.editgraph.node_label_artists.items() if isinstance(idt, int | Symbol)}

        # Function setting edges in symbolic form where nodes are all symbols.
        def symbolic(edge):
            return idvar[edge[0]], idvar[edge[1]]

        # STEP: Find the edges having consistent nodes.
        edges = {(src, tgt) for src, tgt in self.editgraph.edge_artists.keys() if src in idvar and tgt in idvar}

        # STEP: Get the positions.
        edit_pos = self.editgraph.node_positions
        pos = {idvar[idt]: edit_pos[idt] for idt in idvar}

        # STEP: Interpret the colors to signs. WARNING: The face color is (r,g,b,a) while the sign colors are (r,g,b).
        edge_attributes = self.editgraph.edge_artists
        signs = {edge: COLORSIGN[edge_attributes[edge].get_facecolor()[0:3]] for edge in edges}

        # STEP: Determination of the modules from edge label.
        edge_labels = self.editgraph.edge_label_artists
        modules = {}
        for edge in edges:
            try:
                label = edge_labels[edge].get_text()
                modularity = {signs[edge] * int(module) for module in list(label.split(" ")) if module.isdigit()}
                if modularity:
                    modules.update({symbolic(edge): modularity})
                else:
                    modules.update({symbolic(edge): {signs[edge]}})
            except KeyError:  # No edge labels
                modules.update({symbolic(edge): {signs[edge]}})

        # STEP: Convert the edges symbolically for signs.
        # WARNING: as signs dict is previously used for determining the modules with string as keys, the conversion can only be achieved here.
        signs = {symbolic(edge): signs[edge] for edge in signs}

        # STEP: Generate the ig from the editable graph.
        ig = nx.DiGraph()
        ig.add_nodes_from(idvar.values())  # add nodes
        for edge in signs:  # add edges
            ig.add_edge(edge[0], edge[1], sign=signs[edge], module=modules[edge])

        # STEP: Finally convert the ig to BooN.
        try:
            self.boon.from_ig(ig)  # Find the BooN from the ig.
        except ValueError:  # To prevent the transient error due to edge labeling.
            pass

        # STEP:  Store positions.
        self.boon.pos = pos

        # STEP: Update the history and refresh the open windows.
        self.add_history()
        if self.hupdate:
            self.refresh()

    # DEF: FILE MANAGEMENT
    def open(self):
        """Open file dialog."""
        filename = QFileDialog.getOpenFileName(self, "Open file", "", "Boon Files (*.boon);; All Files (*);;")
        if filename:
            self.filename = filename[0]
            self.boon.load(filename[0])

            self.refresh()
            self.setup_design()
            self.history_raz()
            self.add_history()

    def save(self):
        """Save file dialog."""
        if self.filename:
            self.boon.save(self.filename)
            self.saved = True
        else:
            self.saveas()

    def saveas(self):
        """Save as file as dialog."""
        filename = QFileDialog.getSaveFileName(self, "Save", "", "Boon Files (*.boon);; All Files (*);;")
        if filename:
            self.filename = filename[0]
            self.boon.save(self.filename)
            self.saved = True

    def importation(self):
        """Import file dialog."""
        filename = QFileDialog.getOpenFileName(self, "Import from files", "", "Text Files (*.txt);; All Files (*);;")
        if filename:
            self.boon.from_textfile(filename[0])
            self.refresh()
            self.setup_design()
            self.history_raz()
            self.add_history()

    def exportation(self):
        """Export file dialog."""
        filename = QFileDialog.getSaveFileName(self, "", "Export to text file.", "Text Files (*.txt);; All Files (*);;")
        if filename:
            self.boon.to_textfile(filename[0])

    def quit(self):
        """Quit application."""
        # check if the BooN is saved

        if self.saved:
            quitting = True
        else:  # Otherwise ask whether it must be saved.
            reply = QMessageBox.question(
                self,
                "Quit",
                "Are you sure you want to quit? the BooN is not saved.",
                QMessageBox.Save | QMessageBox.Close | QMessageBox.Cancel,
                QMessageBox.Save)
            match reply:
                case QMessageBox.Save:
                    self.save()
                    quitting = True
                case QMessageBox.Close:
                    quitting = True
                case QMessageBox.Cancel:
                    quitting = False
                case _:
                    quitting = False
        if quitting:
            app.quit()

        return quitting

    # noinspection PyMethodOverriding
    def closeEvent(self, event):
        """Close window"""
        quitting = self.quit()
        if not quitting:
            event.ignore()

    # DEF: HISTORY MANAGEMENT
    def history_raz(self):
        """Clear the history and initialize self.saved flag."""
        self.history = [None] * HSIZE  # History
        self.hindex = 0  # Index of the last BooN added in the  history
        self.hupdate = False  # Flag determining whether the history is updated
        self.saved = True  # Flag determining whether a BooN is saved.

    def undo(self):
        """Undo operation."""
        hindex = (self.hindex - 1) % HSIZE
        if self.history[hindex]:
            self.disablecallback = True  # Prevent disruptive updates by disabling callback.
            self.boon = self.history[hindex]  # restore the previous BooN
            self.hindex = hindex  # update the history index
            self.refresh()
            self.setup_design()

    def redo(self):
        """Redo operation."""
        hindex = (self.hindex + 1) % HSIZE
        if self.history[hindex]:
            self.disablecallback = True  # Prevent disruptive updates by disabling callback.
            self.boon = self.history[hindex].copy()  # copy the current Boon
            self.hindex = hindex
            self.refresh()
            self.setup_design()

    def add_history(self):
        """Add current BooN to the history."""
        hindex = self.hindex
        if self.boon != self.history[hindex]:  # WARNING: The BooN comparison operates on descriptors only.

            self.disablecallback = True  # Prevent disruptive updates by disabling callback.
            self.hupdate = True  # Descriptor is changed.

            if self.history[hindex] and self.history[hindex].desc:  # The current descriptor is not empty.
                self.saved = False

            self.disablecallback = False  # Enable the design callback

            hindex = (hindex + 1) % HSIZE  # Update the history
            self.history[hindex] = self.boon.copy()
            self.hindex = hindex

        else:
            self.hupdate = False  # No changes.

        # PRINT THE HISTORY
        # for i,h in enumerate(self.history):
        #    if i == self.hindex:
        #        print(f"*{i}:",end="")
        #    else:
        #        print(f" {i}:",end="")
        #    if h:
        #        print(f'[{h}]')
        #    else:
        #        print("[NONE]")

    def show_history(self):
        """Show the history."""
        view = [([i] if i == self.hindex else i,
                 tabulate([(var, logic.prettyform(eq, theboon.style)) for var, eq in theboon.desc.items()], tablefmt='plain')
                 if theboon else '-') for i, theboon in enumerate(self.history)]

        os.system('cls')
        print(tabulate(view, tablefmt='grid'))

    def refresh(self):
        """Refresh the opened widgets."""
        if self.QView and self.QView.isVisible():  # Refresh the BooN View if opened.
            self.QView.initialize_view()
        if self.QStableStates and self.QStableStates.isVisible():  # Refresh the stable states View if opened.
            self.QStableStates.stablestates()
        if self.QModel and self.QModel.isVisible():  # Refresh the Model view if opened.
            self.QModel.modeling()
        if self.QControllability and self.QControllability.isVisible():  # Refresh the Controllabilitt View if opened.
            self.QControllability.initialize_controllability()

    # DEF: WIDGETS OPENING
    def help(self):
        """Help View"""
        thehelp = Help(self)
        thehelp.show()

    def view(self):
        """BooN View"""
        self.QView = View(self)
        self.QView.show()

    def stablestates(self):
        """Stable States View"""
        self.QStableStates = StableStates(self)
        self.QStableStates.show()

    def model(self):
        """Model View"""
        if len(self.boon.variables) > MODELBOUND:
            QMessageBox.critical(self, "NOP", f"The number of variables exceeds {MODELBOUND}. The model cannot be computed.")
            return

        self.QModel = Model(self)
        self.QModel.show()

    def controllability(self):
        """Controllability View"""
        self.QControllability = Controllability(self)
        self.QControllability.show()


# DEF:  WIDGET CLASSES

class Help(QMainWindow):
    """Help Class used for showing help."""

    def __init__(self, parent=None):
        super(Help, self).__init__(parent)
        loadUi('BooNGui/help.ui', self)
        self.setMinimumSize(QSize(600, 600))
        self.CloseButton.clicked.connect(lambda _: self.close())
        self.web = QWebEngineView(self)
        self.WebContainer.addWidget(self.web)
        with open('BooNGui/Help.html', 'r') as f:
            html = f.read()
            self.web.setHtml(html)


class View(QDialog):
    """View Class used for showing the BooN in a table."""

    def __init__(self, parent=None):
        super(View, self).__init__(parent)
        loadUi('BooNGui/view.ui', self)
        self.setGeometry(300, 300, 750, 500)
        self.style = LOGICAL  # Style of the formulas
        self.parent = parent  # parent = Boonify class
        self.formulas = None  # formulas of BooN

        # STEP: Set the functions related to signals
        self.CloseButton.clicked.connect(lambda _: self.close())
        self.DnfButton.clicked.connect(self.convertdnf)

        # STEP: Combox Box of style.
        self.Style.activated.connect(self.cb_styling)

        # STEP: Block the edition of BooNContent.
        self.BooNContent.setEditTriggers(QtWidgets.QTableWidget.NoEditTriggers)

        # STEP: Resize columns of the table to content.
        self.BooNContent.setColumnWidth(1, 500)
        self.BooNContent.resizeColumnToContents(0)
        self.BooNContent.resizeColumnToContents(2)

        # STEP: Stretch the formula columns.
        header = self.BooNContent.horizontalHeader()
        header.setSectionResizeMode(QHeaderView.Stretch)
        header.setSectionResizeMode(1, QHeaderView.Interactive)

        self.initialize_view()

    def initialize_view(self):
        """Fill the table."""
        theboon = self.parent.boon

        # Initialize the formula fields.
        nbrow = len(theboon.desc)
        self.BooNContent.setRowCount(nbrow)
        self.formulas = [QLineEdit() for _ in range(nbrow)]
        for f in self.formulas:
            f.editingFinished.connect(self.change_formula)
            f.setFrame(False)

        # Fill the table
        for row, var in enumerate(theboon.desc):
            item = QTableWidgetItem(str(var))
            item.setTextAlignment(Qt.AlignCenter)
            self.BooNContent.setItem(row, 0, item)  # variable

            self.formulas[row].setText(logic.prettyform(theboon.desc[var], style=self.style))
            self.BooNContent.setCellWidget(row, 1, self.formulas[row])  # formula

            if is_dnf(theboon.desc[var]):  # type of the formula
                form = "DNF"
            elif is_cnf(theboon.desc[var]):
                form = "CNF"
            elif is_nnf(theboon.desc[var]):
                form = "NNF"
            else:
                form = "General"
            item = QTableWidgetItem(form)
            item.setTextAlignment(Qt.AlignHCenter)
            self.BooNContent.setItem(row, 2, item)

    def change_formula(self):
        """ Update the BooN from a formula change."""
        row = self.BooNContent.currentRow()  # get the current modified row
        text = self.formulas[row].text()  # get the text of the lineedit formula

        try:
            formula = parse_expr(text)  # parse the input
        except SyntaxError:
            QMessageBox.critical(self, "SYNTAX ERROR", "Syntax Error.\nThe formula is not changed.")
            self.parent.refresh()
            return

        if isinstance(formula, bool):  # Determine whether a new variable is used.
            variables = set()
        else:
            variables = formula.free_symbols

        diff = variables.difference(self.parent.boon.variables)
        if diff:
            QMessageBox.critical(self, "VARIABLES ERROR", "The following variables do not exist: {}.\nThe formula is not changed.".format(diff))
            self.parent.refresh()
            return

        variable = list(self.parent.boon.desc.keys())[row]
        self.parent.boon.desc[variable] = formula  # update the BooN

        # Refresh open widgets and editgraph.
        self.parent.setup_design()
        self.parent.refresh()

    def cb_styling(self):
        """Style from combo box selection"""
        self.style = STYLE[self.Style.currentText()]
        self.initialize_view()  # Refresh the view.

    def convertdnf(self):
        """ Convert the BooN into DNF."""
        self.parent.boon.dnf()
        self.initialize_view()  # Refresh the view.


class StableStates(QDialog):
    """Class to handle stable states computation."""

    def __init__(self, parent=None):
        super(StableStates, self).__init__(parent)
        loadUi('BooNGui/stablestates.ui', self)
        self.setGeometry(300, 300, 500, 700)
        self.parent = parent
        self.style = 'Icon Boolean'
        self.datamodel = None
        # Button and Combo Box
        self.CloseButton.clicked.connect(lambda _: self.close())
        self.Style.activated.connect(self.cb_styling)

        # shrink the header to size
        Hheader = self.StableStatesPanel.horizontalHeader()
        Hheader.setSectionResizeMode(QHeaderView.ResizeToContents)

        self.stablestates()

    def cb_styling(self):
        """Style from combo box selection"""
        self.style = self.Style.currentText()
        self.stablestates()  # Refresh the stable states view.

    def stablestates(self):
        """Compute stable states and arrange the view."""
        theboon = self.parent.boon
        variables = theboon.variables
        stablestates = theboon.stable_states

        # Define a model of data to store stable states.
        self.datamodel = QStandardItemModel()
        self.datamodel.setRowCount(len(variables))
        self.datamodel.setVerticalHeaderLabels([str(var) for var in variables])

        # Fill the table.
        for stable in stablestates:
            column = []
            for var in variables:
                icon = QIcon()
                icon.addPixmap(QtGui.QPixmap(ICON01[stable[var]]), QtGui.QIcon.Normal, QtGui.QIcon.Off)
                icon.pixmap(QSize(64, 64))

                match self.style:  # define the view from the style
                    case 'Icon':
                        item = QStandardItem(icon, "")
                    case 'Icon Boolean':
                        item = QStandardItem(icon, str(stable[var]))
                    case 'Icon 0-1':
                        item = QStandardItem(icon, str(int(stable[var])))
                    case 'Boolean':
                        item = QStandardItem(str(stable[var]))
                    case '0-1':
                        item = QStandardItem(str(int(stable[var])))
                    case _:
                        item = QStandardItem("None")

                item.setTextAlignment(Qt.AlignCenter)
                column.append(item)

            self.datamodel.appendColumn(column)
        self.StableStatesPanel.setModel(self.datamodel)


class Model(QMainWindow):
    """Class to handle model of dynamics."""

    def __init__(self, parent=None):
        super(Model, self).__init__(parent)
        loadUi('BooNGui/model.ui', self)
        self.setGeometry(300, 300, 600, 600)
        self.CloseButton.clicked.connect(lambda _: self.close())
        # STEP: initialize attributes
        self.parent = parent
        self.mode = boon.asynchronous
        self.layout = boon.hypercube_layout

        # STEP: Connect Matplotlib widget
        self.canvas = FigureCanvas(Figure())
        self.ModelCanvas.addWidget(self.canvas)
        self.canvas.axes = self.canvas.figure.add_subplot(111)

        # STEP: connect functions to signals.
        # Radio Button to select the mode
        self.AsynchronousButton.clicked.connect(self.rb_mode)
        self.SynchronousButton.clicked.connect(self.rb_mode)
        # Network layout Combo box
        self.NetworkLayout.activated.connect(self.cb_network_layout)

        # STEP: Modéling
        self.modeling()

    def rb_mode(self):
        """Mode selection from radio button box."""
        if self.AsynchronousButton.isChecked():
            self.mode = boon.asynchronous
        elif self.SynchronousButton.isChecked():
            self.mode = boon.synchronous
        else:
            pass
        self.modeling()

    def cb_network_layout(self):
        """ Determine the layout of the network model from combo box."""
        layout = self.NetworkLayout.currentText()
        match layout:
            case "Hypercube":
                self.layout = boon.hypercube_layout
            case "Circular":
                self.layout = nx.circular_layout
            case "Spring":
                self.layout = nx.spring_layout
            case "Kamada Kawai":
                self.layout = nx.kamada_kawai_layout
            case "Random":
                self.layout = nx.random_layout
            case _:
                logic.errmsg("Internal Error - Unknown layout", "cb_network_layout")
        self.modeling()

    def modeling(self):
        """Compute the model of dynamics."""
        self.canvas.axes.clear()
        self.canvas.axes.axis('off')

        model = self.parent.boon.model(mode=self.mode)
        if model.number_of_nodes() == 0:  # Empty datamodel = empty BooN
            return

        layout = self.layout(model)
        self.parent.boon.draw_model(model, pos=layout, ax=self.canvas.axes)
        self.canvas.draw_idle()


class Controllability(QMainWindow):
    """Controllability class"""

    def __init__(self, parent=None):
        super(Controllability, self).__init__(parent)
        loadUi('BooNGui/controllability.ui', self)
        self.setGeometry(900, 300, 800, 600)

        self.parent = parent
        self.actions = None  # current control actions
        self.row = None  # row number corresponding to the selected solutions
        self.initialize_controllability()

    def initialize_controllability(self):
        """Initialize the controllability widget."""
        theboon = self.parent.boon
        variables = theboon.variables
        nbrow = len(theboon.desc)

        # STEP : set the controllability as the function of the thread
        self.parent.worker.apply(self.controllability)

        # STEP: Initialize Destiny page
        self.Destiny.setRowCount(nbrow)
        self.Destiny.resizeColumnToContents(0)
        self.Destiny.horizontalHeader().setStretchLastSection(True)

        # fill the destiny table
        for row, var in enumerate(variables):
            # Add variable name
            item = QTableWidgetItem(str(var))
            item.setTextAlignment(Qt.AlignCenter)
            self.Destiny.setItem(row, 0, item)

            # Add a status for each variable
            statusbox = QComboBox(self)
            # item of the status box
            statusbox.addItems(["None", "True", "False"])  # possible status

            # insert icons for each status
            icon = QIcon(ICON01[None])  # icon for None
            icon.pixmap(QSize(64, 64))
            statusbox.setItemIcon(0, icon)
            icon = QIcon(ICON01[True])  # icon for True
            icon.pixmap(QSize(64, 64))
            statusbox.setItemIcon(1, icon)
            icon = QIcon(ICON01[False])  # icon for False
            icon.pixmap(QSize(64, 64))
            statusbox.setItemIcon(2, icon)

            # insert the status box in the table and connect it
            self.Destiny.setCellWidget(row, 1, statusbox)
            statusbox.currentTextChanged.connect(self.destiny_change)

        # STEP: Initialize the observer page
        self.Observers.setRowCount(nbrow)
        self.Observers.horizontalHeader().setStretchLastSection(True)

        # fill the observer table
        for row, var in enumerate(variables):
            obschkbox = QTableWidgetItem(str(var))  # add checkbox
            obschkbox.setText(str(var))
            obschkbox.setFlags(Qt.ItemIsUserCheckable | Qt.ItemIsEnabled)
            obschkbox.setCheckState(Qt.Unchecked)
            self.Observers.setItem(row, 0, obschkbox)

        # STEP: Define signals
        self.Observers.itemClicked.connect(self.observer_change)
        self.ControlButton.clicked.connect(self.parent.worker.run)
        self.ControlActions.clicked.connect(self.select_action)
        self.ActButton.clicked.connect(self.actupon)

        # STEP: Set the destiny page as default
        self.ControlPanel.setCurrentIndex(0)

        # STEP: Set size of columns
        # fit to content for ControlPanel
        for i in range(self.ControlPanel.count()):
            self.ControlPanel.widget(i).adjustSize()

        # fit to content for ControlActions
        header = self.ControlActions.header()
        header.setSectionResizeMode(QHeaderView.ResizeToContents)
        header.setStretchLastSection(True)

    def destiny_change(self, label: str):
        """Modify the observer w.r.t. the destiny change."""
        row = self.Destiny.currentRow()
        item = self.Observers.item(row, 0)

        if label == "None":
            item.setCheckState(Qt.Unchecked)
        else:
            item.setCheckState(Qt.Checked)

    def observer_change(self, chkitem):
        """ Modify the destiny w.r.t. the observer change"""
        row = chkitem.row()
        if chkitem.checkState() == Qt.Unchecked:
            combobox = self.Destiny.cellWidget(row, 1)
            combobox.setCurrentText("None")

    def controllability(self):
        """Compute the control actions based on the destiny and the observers."""
        self.row = None
        theboon = self.parent.boon
        variables = list(theboon.variables)

        # get the observers
        controlledvars = set()
        for row in range(self.Observers.rowCount()):
            item = self.Observers.item(row, 0)
            if item.checkState() == Qt.Checked:
                pass
            else:
                controlledvars.add(variables[row])

        # Get the query formula
        query = {}
        for row in range(self.Destiny.rowCount()):
            combobox = self.Destiny.cellWidget(row, 1)
            match combobox.currentText():
                case "None":
                    pass
                case "True":
                    query.update({variables[row]: True})
                case "False":
                    query.update({variables[row]: False})

        # convert the state profiles into minterm
        formula = SOPform(query.keys(), [query])
        # Check whether the query must be reached or avoid.
        match self.QueryType.currentText():
            case "Reach":
                pass
            case "Avoid":
                formula = Not(formula)

        boonctrl = theboon.copy()
        boonctrl.control(controlledvars, controlledvars)

        if self.Possibility.isChecked():
            possibility = boonctrl.possibly(formula)
        else:
            possibility = True

        if self.Necessity.isChecked():
            necessity = boonctrl.necessary(formula, trace=self.Trace)
        else:
            necessity = True
        destiny = And(possibility, necessity)

        # Destify the controlled BooN and transform the solutions into control actions (var, Boolean Value)
        core = BooN.destify(destiny, trace=self.Trace)
        self.actions = core2actions(core)
        # print("actions>",self.actions)

        # Define tree model to show the actions.
        treemodel = QStandardItemModel(0, 2)  # Add 2 columns
        treemodel.setHeaderData(0, Qt.Horizontal, "Variable")
        treemodel.setHeaderData(1, Qt.Horizontal, "Boolean value")

        root = treemodel.invisibleRootItem()
        match self.actions:
            case []:  # No actions
                item = QStandardItem("No action found.")
                root.appendRow(item)
            case [[]]:  # The destiny profile is already obtained
                item = QStandardItem("The profile already exists.")
                root.appendRow(item)
            case _:  # Compute the control actions.
                for i, actions in enumerate(self.actions, 1):
                    # create the root solution
                    rootactions = QStandardItem("Solution {:2d}".format(i))
                    # add the control actions of this solution
                    for action in actions:
                        # a control action is shown by : variable + Boolean icon + a value
                        variable = QStandardItem(str(action[0]))
                        icon = QIcon(ICON01[action[1]])
                        icon.pixmap(QSize(64, 64))
                        value = QStandardItem(icon, str(action[1]))
                        rootactions.appendRow([variable, value])
                    # append the solution to the tree model
                    root.appendRow(rootactions)

        self.ControlActions.setModel(treemodel)
        self.ControlActions.expandAll()

    def select_action(self, arg):
        """Keep the selection solution"""
        self.row = arg.parent().row() if arg.parent().row() > -1 else arg.row()

    def actupon(self):
        """Apply the selection actions on the BooN."""
        if self.row is not None and self.actions:
            for action in self.actions[self.row]:
                (variable, value) = action
                self.parent.boon.desc[variable] = value

            self.parent.setup_design()
            self.parent.refresh()
            self.close()
            # print("Boon:")
            # print(self.parent.boon)


class Threader(QObject):
    """Class running an application in a thread."""
    finished = pyqtSignal()

    def __init__(self, app=None):
        super().__init__()
        if app:
            self.app = app
        else:
            self.app = lambda: None  # null application

        # Create the thread
        self.thread = QThread()
        self.moveToThread(self.thread)
        self.thread.start()

    def run(self):
        """run the application"""
        self.app()  # run the application
        self.finished.emit()  # Emit the end signal

    def apply(self, app):
        self.app = app

    def quit(self):
        """terminate the thread"""
        self.thread.quit()


# DEF:  MAIN
if __name__ == "__main__":
    app = QApplication(sys.argv)
    boonify = Boonify()
    callback = boonify.canvas.mpl_connect('draw_event', lambda _: boonify.design())
    boonify.show()
    sys.exit(app.exec_())
