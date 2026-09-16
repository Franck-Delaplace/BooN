class StableStates(QDialog):
    """
    A dialog for displaying and managing stable states in a computational model.

    This class represents a graphical interface for visualizing stable states
    of a Boolean network model. It allows users to switch between different
    display styles, such as icons or textual representation, for better
    interpretation of the stable states.

    :ivar parent: Reference to the parent widget or application component.
    :type parent: QWidget
    :ivar style: The display style for representing stable states (e.g., 'Icon Boolean').
    :type style: str
    :ivar datamodel: The data model used for organizing and displaying stable states.
    :type datamodel: QStandardItemModel
    """

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
        """
        Updates the current style setting from the user interface and refreshes the stable states view.

        :return: None.
        """
        self.style = self.Style.currentText()
        self.stablestates()  # Refresh the stable states view.

    def stablestates(self):
        """
        Generates and sets up a data model to visualize stable states of a system.

        This method processes the stable states of a parent object's model and organizes
        them into a table-like structure using a Qt `QStandardItemModel`. Each row
        represents a variable, and each column corresponds to a stable state. The
        presentation style of the data (e.g., icons, boolean values, or integers) is
        determined by the specified `style` attribute of the object.

        :return: None
        """
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





    def stablestates(self):
        """
        Generates and sets up a data model to visualize stable states of a system.

        This method processes the stable states of a parent object's model and organizes
        them into a table-like structure using a Qt `QStandardItemModel`. Each row
        represents a variable, and each column corresponds to a stable state. The
        presentation style of the data (e.g., icons, boolean values, or integers) is
        determined by the specified `style` attribute of the object.

        :return: None
        """
        print("STABLE STATE -  0")
        theboon = self.parent.boon
        variables = theboon.variables
        stablestates = theboon.stable_states

        print("STABLE STATE -  1")
        # Define a model of data to store stable states.
        self.datamodel = QStandardItemModel()
        self.datamodel.setRowCount(len(variables))
        self.datamodel.setVerticalHeaderLabels([str(var) for var in variables])
        print("STABLE STATE -  2")
        # Fill the table.
        # Fill the table.
        for i, stable in enumerate(stablestates):
            print(f"  Traitement état stable #{i}")
            sys.stdout.flush()
            column = []
            for var in variables:
                print(f"    var={var} val={stable[var]}")
                sys.stdout.flush()

                icon = QIcon()
                print(f"    QIcon OK")
                sys.stdout.flush()

                icon.addPixmap(QtGui.QPixmap(ICON01[stable[var]]), QtGui.QIcon.Normal, QtGui.QIcon.Off)
                print(f"    addPixmap OK")
                sys.stdout.flush()

                icon.pixmap(QSize(64, 64))
                print(f"    pixmap OK")
                sys.stdout.flush()

                match self.style:
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

                print(f"    QStandardItem OK")
                sys.stdout.flush()

                item.setTextAlignment(Qt.AlignCenter)
                print(f"    setTextAlignment OK")
                sys.stdout.flush()

                column.append(item)
                print(f"    append OK")
                sys.stdout.flush()

        print("STABLE STATE -  3")
        self.StableStatesPanel.setModel(self.datamodel)
