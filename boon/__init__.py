# Boolean Network analysis module
# Author: Franck Delaplace
# Creation date: January 2024

# In comments :
# DEF means definition which is a code part gathering functions related to a process or an object definition.
# STEP means main steps.
# WARNING is a warning.
# The first terms can be used to color comments in PyCharm or else.

from __future__ import annotations

import random
import re
import copy
import pickle
import sys
from typing import Dict, Any
from datetime import datetime
from functools import reduce

import z3
import math
from collections.abc import Callable
from itertools import product

from pulp import PULP_CBC_CMD

import netgraph as ng
import networkx as nx

from matplotlib.colors import to_rgb

from sympy import symbols
from sympy.core.symbol import Symbol
from sympy.logic.boolalg import And, Or, Not, Implies, Equivalent
from sympy.logic.boolalg import to_cnf, to_dnf, is_dnf, simplify_logic
from sympy.parsing.sympy_parser import parse_expr

from boon.logic import LOGICAL, SYMPY, BOOLNET, errmsg, firstsymbol
import boon.logic as logic

from tqdm import tqdm

import libsbml

# CONSTANTS
SIGNCOLOR: dict = {-1: 'crimson', 0: 'steelblue', 1: 'forestgreen'}  # colors of edges in the interaction graph w.r.t. to signs.
COLORSIGN = {to_rgb(color): sign for sign, color in SIGNCOLOR.items()}
EXTBOON: str = ".boon"  # file extension for BooN format.
EXTXT: str = ".txt"  # file extension of Python format for an imported file.
EXTBOOLNET: str = ".bnet"  # file extension of BOOLNET format for an imported file.
EXTSBML: str = ".sbml"  # file extension of SBML file for an imported file.

CONTROL: str = "_u"  # prefix name of the controllers (control parameters).
CTRLPRFXLEN: int = len(CONTROL)  # length of the control prefix.

BIN2BOOL: dict = {'0': False, '1': True}  # convert string 0-1 value to Boolean.
BOOL2BIN: dict = {False: '0', True: '1', 0: '0', 1: '1'}  # convert Boolean to string.

BOONSEP: str = "\n"  # separator between the equations of a BooN.
VARPREFIX: str = "x"  # Prefix of the generated variables (random)

# palette of colors for graph drawing
COLOR: list[str] = ['tomato', 'gold', 'yellowgreen', 'plum', 'mediumaquamarine', 'darkorange',
                    'darkkhaki', 'forestgreen', 'salmon', 'lightcoral', 'cornflowerblue', 'orange',
                    'paleviolet', 'coral', 'dodgerblue', 'yellowgreen', 'orangered', 'pink', 'blueviolet', 'crimson']

BOOLNETSKIP: str = r'(targets\s*,\s*factors)|(#.*)'  # regexp describing the line to skip in a boolnet format.
PYTHONSKIP: str = r'#.*'  # regexp describing python comment to skip.
PYTHONHEADER: str = '# BooN saved on ' + datetime.now().strftime("%d-%m-%Y")  # header for basic save (.txt)
BOOLNETHEADER: str = PYTHONHEADER + '\ntargets, factors'  # header for boolnet format


def is_controlled(formula) -> bool:
    """Check whether a formula is controlled.

    :param formula: The input formula.
    :type formula: Sympy formula.
    :return: True if the formula is controlled otherwise False
    :rtype: bool
    """
    try:
        return any(map(lambda var: var.name.startswith(CONTROL), formula.free_symbols))
    except AttributeError:  # Boolean True, False not controlled.
        return False


def isctrl(lit) -> bool:
    """
     Determines if a literal contains a controller.
     :param lit: The literal to be validated.
     :type lit: Literal
     :return: True if the literal is a negative control, False otherwise.
     :rtype: Bool
     """

    return firstsymbol(lit).name.startswith(CONTROL)


def isnegctrl(lit) -> bool:
    """
     Determines if a given literal is a negative control.
     :param lit: The literal to be validated.
     :type lit: Literal
     :return: True if the literal is a negative control, False otherwise.
     :rtype: Bool
     """
    return isinstance(lit, Not) and isctrl(lit)


def controls2actions(controls: frozenset) -> list[tuple]:
    """Convert a set of controls into a list of actions where an action is a pair (symbol, boolean value).
    :param controls: The set of control parameters.
    :type controls: frozenset[Sympy symbols]
    :return: A list of actions.
    :rtype: list[tuple[Sympy symbol, bool]]
    """
    return [(symbols(str(ctrl)[CTRLPRFXLEN + 1:]), BIN2BOOL[str(ctrl)[CTRLPRFXLEN]]) for ctrl in controls]


def core2actions(core: frozenset) -> list:
    """Convert the core to a list of actions where an action is a list of (variable, Boolean).
    The actions are sorted by length, meaning that the more parsimonious actions are at first.

    :param core: The core.
    :type core: Frozenset[Frozenset[Sympy symbol]].
    :return: A list of combined actions where an action is defined as:[(variable, bool) ...]
    :rtype: List[list[tuple]]
    """

    actions = [controls2actions(primes) for primes in core]
    # Sort the actions by length.
    return sorted(actions, key=len, reverse=False)


def asynchronous(variables: list | set) -> frozenset:
    """Asynchronous or sequential mode. One variable is updated per transition.

    :param variables: List of variables.
    :type variables: List or set
    :return:  of sets: {{x1},...,{xi},...,{xn}} representing the asynchronous mode.
    :rtype: frozenset[frozenset[Symbol]]
    """
    return frozenset({frozenset({x}) for x in variables})


def synchronous(variables: list | set) -> frozenset:
    """synchronous or parallel mode. All the variables are updated jointly per transition.

        :param variables: list of variables.
        :type variables: list or set
        :return:  of sets: {{x1,...,xi,...,xn}} representing the synchronous mode.
        :rtype: frozenset[frozenset[Symbol]]
        """
    return frozenset({frozenset({*variables})})


def state2int(state: dict | tuple, variables: set | list | None = None) -> int:
    """Convert a set of states to an integer the binary profile of which corresponds to the state of the variables.

    :param state: State of the variables.
    :param variables: List of variables.
    :type state: Dict or tuple
    :type variables: list or set
    :return: an integer such that its binary profile represents the state.
    :rtype: Int
    """

    if variables:
        order = variables
        bin_profile = "".join([BOOL2BIN[state[var]] for var in order])
    elif isinstance(state, dict):
        order = state.keys()
        bin_profile = "".join([BOOL2BIN[state[var]] for var in order])
    elif isinstance(state, tuple):
        bin_profile = "".join([BOOL2BIN[elt] for elt in state])
    else:
        bin_profile = str(state)

    return int(bin_profile, 2)


def int2state(int_state: int, variables: list | set) -> dict:
    """ Convert an integer state to a dictionary state.

    :param int_state: The state coded into integer.
    :param variables: List of variables.
    :type int_state: Int
    :type variables: list or set
    :return: a dictionary representing the state {variable: boolean state…}.
    :rtype: Dict
    """
    bin_state = format(int_state, 'b').zfill(len(variables))
    return dict(zip(variables, [BIN2BOOL[state] for state in bin_state]))


def hypercube_layout(arg: int | nx.Digraph) -> dict:
    """Compute the hypercube layout of a graph.

    :param arg: The dimension of the hypercube or the network to which the layout is applied.
    :type arg: Int or networkx Digraph
    :return: a dictionary {int:position} where int is the integer code of the hypercube labels.
    :rtype: Dict
    """
    dim = 0  # dim gives the dimension of the hypercube, captured from arg.
    if isinstance(arg, int):
        dim = arg
    elif isinstance(arg, nx.DiGraph):
        dim = int(math.log2(arg.number_of_nodes()))

    H = nx.hypercube_graph(dim)
    pos = nx.spring_layout(H)
    return {state2int(node): pos[node] for node in pos}


# noinspection PyMethodFirstArgAssignment
class BooN:
    """Boolean Network Class.

    :param  desc:  Boolean network descriptor { variable: formula, ...}.
    :param  style: Output form of the BooN: LOGICAL, SYMPY, MATHEMATICA, JAVA, BOOLNET, ...,
    :param  pos: the positions of the nodes in the interaction graph. {node:position, ...}.
    :type  desc: Dict
    :type  style: dict
    :type  pos: dict
    """
    desc: dict = {}
    style: dict = {}
    pos: dict = {}

    def __init__(self, descriptor=None, style=LOGICAL, pos: dict = {}):
        """Initialize the BooN object.

        :param descriptor: The descriptor of a Boolean Network {variable: formula, ...}
        (Default None).
        :param style: The output style of formulas (Default: LOGICAL).
        :param pos: Positions of the variable in the interaction graph drawing.
        If empty, the positions are generated during the drawing (Default: {})
        """

        if descriptor:
            self.desc = descriptor
        else:
            self.desc = {}
        self.style = style
        self.pos = pos
        return

    def __copy__(self) -> BooN:
        return BooN(self.desc, self.style, self.pos)

    def __deepcopy__(self, memo) -> BooN:
        return BooN(copy.deepcopy(self.desc, memo), self.style, copy.deepcopy(self.pos, memo))

    def __str__(self, sep: str = BOONSEP, assign: str = "=") -> str:
        return sep.join([f"{str(var)} {assign} {logic.prettyform(self.desc[var], self.style, 0)}" for var in self.variables])

    def str(self, sep: str = BOONSEP, assign: str = "=") -> str:
        """Return a string representing the BooN. The output format can be parameterized (see style argument of BooN)

        :param sep: The separator between formulas (default BOONSEP constant)
        :param assign: the operator defining the assignment of a formula to a variable (e.g., a = f(...) → assign is '='). (Default: '=')
        :type sep: str
        :type assign: str
        """
        return self.__str__(sep, assign)

    def __eq__(self, other: BooN) -> bool:
        """ The equality between BooNs is based on the descriptor only, and not on the style or the nodes position."""
        if not isinstance(other, BooN):
            return NotImplemented
        return self.desc == other.desc

    # DEF: BASIC OPERATIONS

    @property
    def variables(self) -> set:
        """Return the set of variables.
        (property)
        :return: Variables
        :rtype: set[Symbol]
        """
        return set(self.desc.keys())

    def delete(self, variable) -> BooN:
        """Delete a variable in a BooN. The formulas must all be in DNF to properly delete the variable.

        :param  variable: The variable to delete.
        :type variable: Symbol
        :return: self
        :rtype: BooN
        """

        def delete(formula, val: bool = False) -> BooN:  # subfunction deleting a variable by substituting it appropriately.
            if isinstance(formula, bool):
                return formula
            elif isinstance(formula, Symbol):
                if formula == variable:
                    return val
                else:
                    return formula
            elif isinstance(formula, Not):
                if formula.args[0] == variable:
                    return val
                else:
                    return formula
            elif isinstance(formula, And):
                return And(*map(lambda f: delete(f, True), formula.args))
            elif isinstance(formula, Or):
                return Or(*map(lambda f: delete(f, False), formula.args))
            else:
                errmsg("a piece of the formula is not recognized", formula)
                return symbols("__failed__")

        try:
            self.desc.pop(variable)
        except KeyError:
            errmsg("the variable to delete does not exist", variable)

        # Convert BooN in DNF if needed
        if not all(map(is_dnf, self.desc.values())):
            self.dnf()

        for var in self.desc:
            self.desc[var] = delete(self.desc[var])

        return self

    def rename(self, source: Symbol, target: Symbol) -> BooN:
        """Rename a variable.

        :param  source:  The variable to rename.
        :param  target:  The variable renaming the source.
        :type source: Symbol
        :type target: Symbol
        """

        variables = self.variables

        if source not in variables:
            errmsg("the variable to rename does not exist", source)
        if target in variables:
            errmsg("the renamed variable cannot be in BooN variables", target)

        for var in variables:
            if not isinstance(self.desc[var], bool):
                self.desc[var] = self.desc[var].subs(source, target)

        self.desc[target] = self.desc.pop(source)
        return self

    def copy(self) -> BooN:
        """Perform a deep copy of the Boolean network."""
        return copy.deepcopy(self)

    @classmethod
    def random(cls, n: int, p_link: float, p_pos: float = 0.5, topology: str = 'Erdos-Reny', min_clauses: int = 1, max_clauses: int = 5, prefix: str = VARPREFIX) -> BooN:
        """ Generate a random BooN where the formulas are in DNF.
        The method is a class method.

        :param n: The number of variables.
        :type n: Int
        :param p_link: probability related to interaction between variables, the use depends on the topology class.
        :param p_pos: The probability of defining a variable as a positive term (default 0.5).
        :type  p_pos: Float
        :param topology: the topology class of the interaction graph: 'Erdos-Reny', 'Scale-Free', 'Small-World' (default 'Erdos-Reny')
        :type topology: str
        :param min_clauses: the minimum number of clauses required to define a formula (default 1).
        :type  min_clauses: Int
        :param max_clauses: the minimum number of clauses required to define a formula (default 5).
        :type  max_clauses: Int
        :param prefix: the prefix of the variable name, the variables are of the form <prefix> <int> (default 'x').
        :type prefix: Str
        :return: a random BooN
        :rtype: BooN
        """
        assert 0 < n
        assert 0 <= p_link <= 1
        assert 0 <= p_pos <= 1
        assert 0 < min_clauses <= max_clauses

        # Generate a Digraph corresponding to the interaction graph w.r.t a topology class.
        match topology:
            case 'Erdos-Reny':
                ig = nx.fast_gnp_random_graph(n, p_link, directed=True)  # Erdös-Reny
            case 'Scale-Free':
                ig = nx.scale_free_graph(n, alpha=p_link, beta=1 - p_link - 0.05, gamma=0.05, delta_in=0.2)  # Scale-Free
            case 'Small-World':
                ig0 = nx.newman_watts_strogatz_graph(n, min(n, 4), p_link)  # Small World
                ig = nx.DiGraph()  # direct the graph.
                for edge in ig0.edges():
                    i = random.choice([0, 1])
                    ig.add_edge(edge[i], edge[1 - i])
            case _:
                ig = nx.fast_gnp_random_graph(n, p_link, directed=True)  # Erdös Reny by default

        # Associate to each node an integer variable name.
        variables = {node: symbols("{prefix}{counter:d}".format(prefix=prefix, counter=node)) for node in ig.nodes}

        boon = cls()
        # Generate a formula for each node w.r.t. its predecessors.
        for node in ig.nodes:
            # Get the predecessors of a node.
            pred = list(ig.predecessors(node))
            # Define the number of cubes.
            nbclauses = random.randint(min_clauses, min(len(pred), max_clauses)) if len(pred) > 1 else 1

            # Generate the formula.
            if len(pred) == 0:
                boon.desc[variables[node]] = random.choice([True, False])
            else:
                # Form a list of list of predecessors of size nbclauses.
                predlst = [random.choices(pred, k=random.randint(1, len(pred) // 2) if len(pred) > 3 else 1) for _ in range(nbclauses)]
                # Translate it into a DNF formula where each sub list is a cube.
                boon.desc[variables[node]] = simplify_logic(Or(*[And(*[variables[node] if random.random() < p_pos
                                                                       else Not(variables[node]) for node in c
                                                                       ]) for c in predlst]))

        return boon

    # DEF: FILE
    def save(self, filename: str = "BooN" + datetime.now().strftime("%d-%b-%y-%H") + EXTBOON) -> None:
        """Save the Boolean Network to file.
        If the extension is freestates, then .boon is added.

        :param filename:  The name of the file to save the network (Default: BooN+date+hour.boon)
        :type  filename: str
        :return: None
        :rtype: None
        """

        fullfilename = filename if "." in filename else filename + EXTBOON
        with open(fullfilename, 'wb') as f:
            pickle.dump(self, f)
            f.close()

    @classmethod
    def load(cls, filename: str) -> BooN:
        """Load the Boolean Network from a file.
        If the extension is freestates, then .boon is added.
        The method is a class method

        :param filename: The name of the file to load the network.
        :type  filename: Str
        :return: self
        :rtype: BooN
        """
        boon = cls()  # create an empty object

        fullfilename = filename if "." in filename else filename + EXTBOON
        try:
            with open(fullfilename, 'rb') as f:
                boon = pickle.load(f)
                f.close()
        except FileNotFoundError:
            errmsg("No such file or directory", fullfilename, "WARNING")
        return boon

    def to_textfile(self, filename: str, sep: str = BOONSEP, assign: str = ',', ops: dict = BOOLNET, header: str = BOOLNETHEADER) -> BooN:
        """
        Export the Boolean network in a text file.
        If the file extension is freestates, then .txt is added.
        The default format is BOOLNET.

        :param filename: The file name to export the Boolean network.
        :param sep: The separator between formulas (default BOONSEP constant)
        :param assign: the operator defining the formula for a variable, e.g., a = f(...) → assign is '=' (Default: ',' Boolnet Format).
        :param ops: A dictionary stipulating how the operators And, Or, Not are syntactically written (Default: BOOLNET).
        :param header: Header text inserted at the beginning of the saved file.
        :type  filename: Str
        :type sep: str
        :type assign: str
        :type ops: dict
        :type header: str
        :return: self
        :rtype: BooN
        """

        fullfilename = filename if "." in filename else filename + EXTBOOLNET
        with open(fullfilename, 'w') as f:
            tmp = self.style
            self.style = ops  # assign ops to style
            text = header + "\n" + self.str(sep, assign)  # convert to string with regard to sep and assign
            f.write(text)
            self.style = tmp
            f.close()
        return self

    @classmethod
    def from_textfile(cls, filename: str, sep: str = BOONSEP, assign: str = ',', ops: dict = BOOLNET, skipline: str = BOOLNETSKIP) -> BooN:
        """Import the Boolean network from a text file, the syntax of which depends on the ops' descriptor.
        The formulas must be in normal form containing OR, AND, NOT operators only.
        The nodes are circularly mapped.
        The default format is the Bool Net format (see ops and assign defaults).
        The method is a class method.

        :param filename: The file name to import the Boolean network. If the file extension is freestates, then .bnet is added.
        :param sep: The separator between definitions (default BOONSEP constant)
        :param assign: the operator defining the formula for a variable, e.g., a = f(...) → assign is '=' (Default: ',').
        :param ops: A dictionary stipulating how the operators And, Or, Not are syntactically written (Default: BOOLNET).
        :param skipline: Regular expression describing which lines must be skipped and not analyzed.
        :type filename: Str
        :type sep: str
        :type assign: str
        :type ops: dict
        :type skipline: str (regexp)
        :return: BooN
        :rtype: BooN
        """
        # the parsing follows a meta grammar <variable> <assign> <formula>.
        boon = cls()  # create an empty object
        fullfilename = filename if "." in filename else filename + EXTBOOLNET

        try:
            with open(fullfilename, 'r') as f:
                text = " ".join(f.readlines())  # Join all the lines in 1 string.
                text = map(lambda s: s.strip(), text.split(sep))  # And next separate the string w.r.t. the separator sep.

                desc = {}
                for i, line in enumerate(text, 1):  # Parse the network description.
                    if re.fullmatch(skipline, line.strip()):  # Skip line that must be skipped.
                        pass
                    elif line == '':  # Skip empty line.
                        pass
                    else:
                        try:  # Find the position of the assignment.
                            assign_pos = line.index(assign)
                        except ValueError:
                            errmsg(f"Syntax error, the assignment (sign:{assign}) is freestates, line {i} in file", fullfilename, "READ ERROR")
                            return boon
                        try:  # Set the variable to Symbol.
                            var = symbols(line[:assign_pos].strip())
                        except ValueError:
                            errmsg(f"Syntax error, wrong variable name, line {i} in file", fullfilename, "READ ERROR")
                            return boon

                        try:  # Parse formula.
                            # STEP:  rewrite the operators to Python/Sympy operators
                            formula = line[assign_pos + 1:].strip()
                            formula = formula.replace(ops[And], '&')  # Convert And
                            formula = formula.replace(ops[Or], '|')  # Convert Or
                            formula = formula.replace(ops[Not], '~')  # Convert Not

                            # For constant True, False the code can be also a part of the variable name (e.g., True = 0, False = 1 and X101 as variable).
                            # Therefore, the replacement occurs iff it is located after a space, a logical operator or at the start of the formula.
                            formula = re.sub(r'((?<=\||&|~|\s|\()|^)' + ops[False], 'False', formula)  # Convert False
                            formula = re.sub(r'((?<=\||&|~|\s|\()|^)' + ops[True], 'True', formula)  # Convert True

                            # STEP: Now the formula is a string rewritten in Python/Sympy syntax then parse it.
                            trueformula = parse_expr(formula)
                        except SyntaxError:
                            errmsg(f"Syntax error, wrong formula parsing, line {i} in file", fullfilename, "READ ERROR")
                            return boon
                        desc.update({var: trueformula})  # Finally, update the descriptor with the parsed formula.

                boon.desc = desc  # update the descriptor when all lines are filled.
                f.close()
        except FileNotFoundError:
            errmsg("No such file or directory, no changes are made", fullfilename, "WARNING")
            return boon

        ig = boon.interaction_graph
        circular_positions = ng.get_circular_layout([(str(src), str(tgt)) for src, tgt in ig.edges()]
                                                    , origin=(0.1, 0.15)
                                                    , scale=(0.8, 0.8)
                                                    , reduce_edge_crossings=False)
        boon.pos = {symbols(var): pos for var, pos in circular_positions.items()}
        return boon

    @classmethod
    def from_sbmlfile(cls, filename: str) -> BooN:
        """
        Import the Boolean network from a sbml file.
        The method is a class method.

        :param filename: The name of the file, if the extension is freestates, then .sbml is added.
        :type filename: Str
        :return: BooN
        :rtype: BooN
        """

        boon = cls()  # create an empty object
        sbml_file = filename if "." in filename else filename + EXTSBML

        # STEP: Open the SBML file and get the qualitative_model model
        reader = libsbml.SBMLReader()
        document = reader.readSBML(sbml_file)

        if document.getNumErrors() > 0:  # Check if there are no errors while reading the SBML files.
            errmsg("Error reading SBML file", document.getErrorLog().toString(), kind="WARNING")
            return boon

        model = document.getModel()  # Check whether a model exists.
        if model is None:
            errmsg("No model are present in SBML file.", kind="WARNING")
            return boon

        qualitative_model = model.getPlugin("qual")  # Get the qualitative_model part of the model.
        if qualitative_model is None:  # Check whether a Qual model exists.
            errmsg("The model does not have the Qual plugin", kind="WARNING")
            return boon

        # Create a dictionary associating the string name of a variable to its corresponding Symbol.
        vars_dic = {}
        for species in qualitative_model.getListOfQualitativeSpecies():
            species_name = species.getName() if species.isSetName() else species.getId()
            vars_dic[species_name] = symbols(species_name)

        # STEP: read the formulas from transitions and convert them to sympy format.
        desc = {}
        for transition in qualitative_model.getListOfTransitions():  # Scan all the transitions.
            # Get the output variable
            output = transition.getListOfOutputs()
            if len(output) > 1:  # check whether there is a single output
                errmsg("Multiple variables assigned. List of variables", output, kind="WARNING")
                return boon
            else:
                variable = symbols(output[0].getQualitativeSpecies())

            # Get the formula
            logic_terms = transition.getListOfFunctionTerms()

            if len(logic_terms) == 0:  # Empty transition in SBML file, skip it.
                continue

            if len(logic_terms) > 1:  # check whether there exists a single formula only, error otherwise
                errmsg("Multiple logic terms present. Number of terms", len(logic_terms), kind="WARNING")
                return boon
            else:  # Get the SBML QUAL formula
                formula = libsbml.formulaToL3String(logic_terms[0].getMath())

            # Convert the SBML QUAL formula into sympy syntax before parsing it.
            normal_formula = re.sub(r'\|\|', '|', formula)  # convert || to |
            normal_formula = re.sub(r'&&', '&', normal_formula)  # convert && to &
            normal_formula = re.sub(r'\b(\w+)\s*==\s*1\b', r'\1', normal_formula)  # convert <var> == 1 to <var>
            normal_formula = re.sub(r'\b(\w+)\s*==\s*0\b', r'~\1', normal_formula)  # convert <var> == 0 to ~ <var>
            # Parse the formula to get a sympy formula and complete desc
            try:
                sympy_formula = parse_expr(normal_formula, vars_dic)
            except SyntaxError:
                errmsg("Syntax error in the following formula", normal_formula, "SYNTAX ERROR")
                return boon

            desc[variable] = sympy_formula

        # STEP: define the BooN with a circular layout for nodes
        boon.desc = desc
        ig = boon.interaction_graph
        circular_positions = ng.get_circular_layout([(str(src), str(tgt)) for src, tgt in ig.edges()]
                                                    , origin=(0.1, 0.15)
                                                    , scale=(0.8, 0.8)
                                                    , reduce_edge_crossings=False)
        boon.pos = {symbols(var): pos for var, pos in circular_positions.items()}
        return boon

    # DEF: NORMAL FORM CONVERSION
    def cnf(self, variable: Symbol | None = None, simplify: bool = True, force: bool = True) -> BooN:
        """Convert the formulas of the Boolean network to CNF.Convert the formulas of the Boolean network to CNF.

        :param variable: The variable where the formula is to be converted in CNF (Default None).  If variable is None, then all the formulas are converted to CNF.
        :param simplify:  Boolean flag determining whether the formula should be simplified (Default True).
        :param force: Boolean flag forcing the complete simplification of the resulting CNF (Default True).
        :type variable: Symbol
        :type simplify: bool
        :type force: bool
        :return: self
        :rtype: BooN
        """

        if variable:
            try:
                self.desc[variable] = to_cnf(self.desc[variable], simplify=simplify, force=force)
            except KeyError:
                errmsg("The variable is not found", variable)
        else:
            for var in self.desc:
                self.desc[var] = to_cnf(self.desc[var], simplify=simplify, force=force)
        return self

    def dnf(self, variable: Symbol | None = None, simplify: bool = True, force: bool = True) -> BooN:
        """Convert formula(s) of the Boolean network to DNF.

        :param variable:  The variable where the formula is to be converted in DNF (Default: None).
            If variable is None, then all the formulas are converted to DNF.
        :type  variable: Symbol
        :param simplify: Boolean flag determining whether the formula should be simplified (Default: True).
        :type  simplify: bool
        :param force:  Boolean flag forcing the complete simplification (Default: True).
        :type  force: bool
        :return: modified BooN
        :rtype: BooN
        """

        if variable:
            try:
                self.desc[variable] = to_dnf(self.desc[variable], simplify=simplify, force=force)
            except KeyError:
                errmsg("The variable is not found", variable)
        else:
            for var in self.desc:
                self.desc[var] = to_dnf(self.desc[var], simplify=simplify, force=force)
        return self

    # DEF: INTERACTION GRAPH
    @property
    def interaction_graph(self) -> nx.DiGraph:
        """Build the interaction graph.

        :return: The interaction graph.
        :rtype: Networkx DiGraph
        """
        all_dnf = all(map(is_dnf, self.desc.values()))  # Check whether all the formulas are in DNF.
        if all_dnf:
            net = self
        else:  # if some formulas are not in DNF, then convert them into DNF.
            net = self.copy()
            net.dnf()

        variables = net.variables
        ig = nx.DiGraph()

        for var in variables:
            clauses = net.desc[var].args if isinstance(net.desc[var], Or) else (net.desc[var],)

            # get literals_formula clause of the dnf associated to the variable.
            literals_formula = set()  # set of all literals in the dnf
            all_literals_clauses = []  # list of literals per clauses
            for clause in clauses:
                literals_clause = logic.clause2literals(clause)
                literals_formula = literals_formula.union(literals_clause)
                all_literals_clauses.append(literals_clause)

            # Find positive variables.
            posvariables = {lit for lit in literals_formula if isinstance(lit, Symbol)}
            # Find negative variables.
            negvariables = {firstsymbol(lit) for lit in literals_formula if isinstance(lit, Not)}
            # critical variables occur positively and negatively in the formula.
            critical_variables = posvariables & negvariables
            # remove critical variables from positive and negative variables to get pure sets.
            negvariables.difference(critical_variables)
            posvariables.difference(critical_variables)

            for src in posvariables:  # Define interaction for pure positive variables.
                module = set()
                for i, lits in enumerate(all_literals_clauses, 1):
                    if src in lits:
                        module.add(i)
                ig.add_edge(src, var, sign=1, module=module)

            for src in negvariables:  # Define interaction for pure negative variables.
                module = set()
                for i, lits in enumerate(all_literals_clauses, 1):
                    if Not(src) in lits:
                        module.add(-i)
                ig.add_edge(src, var, sign=-1, module=module)

            for src in critical_variables:  # Define interaction for positive and negative variables.
                module = set()
                for i, lits in enumerate(all_literals_clauses, 1):  # find the appropriate modules w.r.t. to literals
                    if src in lits:
                        module.add(i)
                    elif Not(src) in lits:
                        module.add(-i)
                    else:
                        pass
                ig.add_edge(src, var, sign=0, module=module)

        ig.add_nodes_from(variables)
        return ig

    def draw_IG(self, IG: nx.DiGraph | None = None, modular: bool = False, **kwargs) -> nx.DiGraph:
        """Draw the interaction graph.

        :param IG: The interaction graph or None. If None, the interaction graph is generated from BooN (Default: None).
        :param modular: Boolean indicating whether the modular structure of interactions is displayed if True (Default: False)
        :param kwargs: additional keyword arguments to pass to the interaction graph drawing
        :type   IG: networkx DiGraph
        :type   modular: bool
        :type   kwargs: dict
        :return: interaction graph
        :rtype: Networkx DiGraph
        """

        ig = copy.deepcopy(IG) if IG else self.interaction_graph

        if not ig.nodes():
            errmsg("The interaction graph has no nodes", "", "WARNING")
            return ig  # The Graph must have nodes to be drawn.

        signs = nx.get_edge_attributes(ig, 'sign')
        sign_color = {edge: SIGNCOLOR[signs[edge]] for edge in signs}
        if modular:  # add module specification in edges.
            modules = {edge: module.pop() if len(module) == 1 else module
                       for edge, module in nx.get_edge_attributes(ig, 'module').items()}
            module_args = dict(
                edge_labels=modules,
                edge_label_position=0.8,
                edge_label_fontdict=dict(fontweight='bold', fontsize=8, color='darkgray')
            )
        else:
            module_args = dict()

        ng.Graph(ig,
                 node_layout=self.pos,
                 node_color='antiquewhite',
                 node_labels=True,
                 node_size=6,
                 node_label_fontdict=dict(family='sans-serif', color='black', weight='semibold'),
                 arrows=True,
                 edge_width=1,
                 edge_color=sign_color,
                 **module_args,
                 **kwargs)
        return ig

    @classmethod
    def from_ig(cls, IG: nx.DiGraph) -> Boon:
        """
        Define the descriptor of a BooN from an interaction graph.
        The method is a class method.

        :param  IG:  Interaction graph.
        :return: BooN
        :rtype: BooN
        """

        # Find the maximal number of modules for each targetvariable.
        max_nb_modules = {node: 0 for node in IG.nodes()}
        modules = nx.get_edge_attributes(IG, 'module')
        for source, target in modules:
            max_nb_modules[target] = max(max_nb_modules[target], max(map(abs, modules[(source, target)])))

        # define the structure of the DNF as a list of sets where each set stands for a clause.
        nodes = {node: [set() for _ in range(max_nb_modules[node])] for node in IG.nodes()}
        # Place the literal in clauses appropriately.
        for node in nodes:
            for target in IG[node]:
                for module in IG[node][target]['module']:
                    if module > 0:
                        lit = node
                    elif module < 0:
                        lit = Not(node)
                    else:
                        lit = None
                        errmsg("Null module is not admitted - possible origin : non-monotone network", [node, target, module])
                    nodes[target][abs(module) - 1].add(lit)

        # convert into formula
        return cls({node: Or(*(And(*clause) for clause in nodes[node])) for node in nodes})

    # DEF: DYNAMICS
    def model(self, mode: Callable = asynchronous, self_loop: bool = False, trace: bool = False) -> nx.DiGraph:
        """ Compute the dynamical model of the BooN with respect to a mode.

        :param  mode: Determines the mode policy applied to the model (Default: asynchronous).
        :param  self_loop: Determines whether the boon loops are included in the model (Default: False).
        :param trace: Define whether the trace of the execution is enabled (Default: False (disabled)).
        :type self_loop: Bool
        :type mode:  function
        :type trace: bool
        :return: a Digraph representing the complete state-based dynamics.
        :rtype: Networkx Digraph
        """

        def next_state(state, change):  # update a state from changes.
            target = state.copy()
            target.update(change)
            return target

        if trace: print("\rBooN model >> Generate all states        ", end="")

        variables = self.variables
        modalities = mode(variables)
        allstates = [dict(zip(variables, state)) for state in product([False, True], repeat=len(variables))]

        # transitions are state pairs.
        if trace:
            current_transition = 0
            total_transitions = len(allstates) * len(modalities)
            transitions = []
            for state in allstates:
                for modality in modalities:
                    current_transition += 1
                    print("\rBooN model >> Transition [%6d/%6d]      " % (current_transition, total_transitions), end="")
                    transitions.append(
                        (state,
                         next_state(state,
                                    {var: self.desc[var].subs(state) if not isinstance(self.desc[var], bool) else self.desc[var]
                                     for var in modality})
                         ))
        else:
            # Compute the state transition w.r.t. the network.
            transitions = [
                (state,
                 next_state(state,
                            {var: self.desc[var].subs(state) if not isinstance(self.desc[var], bool) else self.desc[var]
                             for var in modality})
                 )
                for state in allstates for modality in modalities]

        # remove boon loop if requested.
        if not self_loop:
            if trace: print("\rBooN model >> self loops removal                          ", end="")
            transitions = filter(lambda edge: edge[0] != edge[1], transitions)

        # Conversion of the states to integral nodes
        if trace: print("\rBooN model >> state to integer conversion                      ", end="")
        nodes = set(map(lambda state: state2int(state, variables), allstates))
        edges = set(map(lambda trans: (state2int(trans[0], variables), state2int(trans[1], variables)), transitions))

        # Graph creation with nodes as integers coding the states.
        if trace: print("\rBooN model >> Graph model design                                ", end="")
        G = nx.DiGraph()
        try:
            G.add_nodes_from(nodes)
        except ValueError:
            pass
        G.add_edges_from(edges)
        return G

    def draw_model(self, model: nx.DiGraph | None = None, mode: Callable = asynchronous, color: list[str] = COLOR, **kwargs) -> None:
        """Draw the graph representing the model of dynamics.

        :param model: Input graph model of the BooN or None (Default: None). If it is None, the asynchronous model computed from the BooN.
        :param mode:  Function characterizing the mode of the model (Default: asynchronous)
        :param color: list of colors for highlighting the equlibria (Default: COLOR)
        :param kwargs: extra parameters of nx.draw_networkx.
        :type model: Networkx DiGraph
        :type mode: function
        :type color: list
        :type kwargs: dict
        :return: None
        :rtype: None
        """

        themodel = model if model else self.model(mode)
        eqs = self.equilibria(themodel)
        if len(eqs) > len(color):
            errmsg(f"the number of colors is insufficient to highlight the equilibria, length of color: {len(color)}, number of attractors", len(eqs))
        variables = self.variables

        def colorize(node) -> str:  # Return the color associated to the attractor in which the node is located otherwise -1
            for i, eq in enumerate(eqs):
                if int2state(node, variables) in eq:
                    return color[i]
            return 'oldlace'

        def is_eq(node) -> bool:
            for eq in eqs:
                if int2state(node, variables) in eq:
                    return True
            return False

        nx.draw_networkx(themodel,
                         labels={node: format(node, 'b').zfill(len(self.variables)) for node in themodel.nodes()},
                         with_labels=True,
                         font_size=11,
                         font_family='fantasy',
                         node_shape='s',
                         node_size=[200 * math.log(len(themodel.nodes()), 2) if is_eq(node) else 200 for node in themodel.nodes()],
                         node_color=[colorize(node) for node in themodel.nodes()],
                         bbox=dict(facecolor='oldlace', edgecolor='black', boxstyle='round,pad=0.1', lw=1.5),
                         width=2,
                         arrowsize=15,
                         arrowstyle='-|>',
                         **kwargs
                         )
        return None

    def equilibria(self, model: nx.DiGraph | None = None, mode: Callable = asynchronous, trace: bool = False) -> list[list]:
        """
        Calculate equilibria for the network based on the model of dynamics.
        The method examines an exponential number of states, and thus it is restricted to networks with a small number of variables (max. ~10).

        :param model: Data model from which the equilibria are calculated (Default: None)
        :param mode: Updating mode function, used if the model is None (Default: asynchronous).
        :param trace: Define whether the trace of execution is enabled (Default: False (disabled)).
        :type model: Networkx DiGraph
        :type mode: function
        :type trace: bool
        :return: Equilibria structure as a list of lists where each sublist is an attractor.
        :rtype: List[list]
        """

        #  Quotient graph.
        #  The function is more than 10 times faster than the networkx method.
        #  The partitions must be frozenset.
        def quotient_graph(graph: nx.DiGraph, partition: list[frozenset]) -> nx.DiGraph:
            # Initialize the quotient graph
            quotient_graph = nx.DiGraph()
            quotient_graph.add_nodes_from(partition)
            # Add edges between groups based on connections in the original graph
            for group1 in partition:
                # Collect all neighbors of a group in the original graph.
                all_neighbors = reduce(set.union, map(lambda node: set(graph.neighbors(node)), group1))
                # Check whether group2 has members in the neighborhood of group1 to define edges.
                for group2 in partition:
                    if group1 != group2 and not group2.isdisjoint(all_neighbors):
                        quotient_graph.add_edge(group1, group2)
            return quotient_graph

        # Possibly compute the model of the BooN.
        themodel = model if model else self.model(mode=mode, trace=trace)

        # Compute the Strongly Connected Components.
        if trace: print("\r BooN equilibria >> SCC                      ", end="")
        scc = list(map(frozenset, nx.strongly_connected_components(themodel)))

        # Deduce the quotient graph of the SCCs.
        if trace: print("\r BooN equilibria >> Quotient graph           ", end="")
        quotient_model = quotient_graph(model, scc)

        # Determine equilibria as the sink in the quotient graph, i.e. terminal SCC.
        if trace: print("\r BooN equilibria >> Equilibria computation    ", end="")
        equilibria = filter(lambda node: quotient_model.out_degree(node) == 0, quotient_model.nodes)

        # Encode the equilibria by transforming the integers into Boolean states.
        if trace: print("\r BooN equilibria >> Encoding                  ", end="")
        eqs_encoded = [[int2state(state, self.variables) for state in attractor] for attractor in equilibria]  # Encode the equilibria.

        if trace: print("\r BooN equilibria >> Completed                 ", end="")
        return eqs_encoded

    def stability_constraints(self):
        """Define the stability constraints for a BooN."""
        return And(*map(lambda var: Equivalent(var, self.desc[var]), self.variables))

    @property
    def stable_states(self) -> list[dict]:
        """Compute all the stable states of a BooN. The algorithm is based on SAT solver.

        :return: List of stable states.
        :rtype: List[dict]
        """

        solver = z3.Solver()  # initialize z3 solver
        solver.add(logic.sympy2z3(self.stability_constraints()))  # add stability constraints translated in z3.

        # Enumerate all models
        models = []
        while solver.check() == z3.sat:
            model = solver.model()
            models.append(model)
            # Block the current model to enable the finding of another model.
            block = [sol() != model[sol] for sol in model]
            solver.add(z3.Or(block))

        # convert the solution to a list of states.
        return list(map(lambda model: {symbols(str(sol())): bool(model[sol]) for sol in model}, models))

    # DEF CONTROLLABILITY

    def control(self, frozenfalse: set | list | frozenset, frozentrue: set | list | frozenset) -> None:
        """Set control on the BooN.
        The controlled variables are divided in two classes:
        the variables frozen to false and the variables frozen to true.
        A variable can belong to both classes.

        :param frozenfalse: List, set or sequence of variables that should be frozen to false by control.
        :param frozentrue: List, set or sequence of variables that should be frozen to true by control.
        :type frozenfalse: Iterable object (list, set, tuple)
        :type frozentrue: iterable object (list, set, tuple)
        :return: self
        :rtype: BooN
        """

        variables = self.variables
        for var in frozenfalse:
            if var in variables:
                u0 = symbols(f"{CONTROL}0{str(var)}")
                self.desc[var] = And(self.desc[var], u0)
            else:
                errmsg("The variable is not found, skipped", var, "WARNING")
        for var in frozentrue:
            if var in variables:
                u1 = symbols(f"{CONTROL}1{str(var)}")
                self.desc[var] = Or(self.desc[var], Not(u1))
            else:
                errmsg("The variable is not found, skipped", var, "WARNING")
        return self

    def possibly(self, query):
        """Compute the possibility constraint.

        :param query: A formula characterizing the query, objective or goal.
        :type query: Sympy formula
        :return: a formula specifying the possibility.
        :rtype: Sympy formula
        """
        return And(self.stability_constraints(), query)

    def necessary(self, query, trace: bool = False):
        """Compute the necessary constraints.
        The computation may take time because the query is converted to CNF that may contain a lot of terms.

        :param query: A formula characterizing the query, objective or goal.
        :param trace: Boolean flag determining whether the trace is activated (Default value = False).
        :type query: Sympy formula
        :type trace: bool
        :return: CNF specifying the necessity.
        :rtype: Sympy formula
        """

        if not self.desc:
            return True

        # Specification of the necessity.
        stability = self.stability_constraints()  # stable stables specification
        necessity = logic.supercnf(Implies(stability, query), trace)  # Necessary conversion into CNF of the query.
        necessary = And(*map(lambda clause:
                             Or(*[lit for lit in logic.clause2literals(clause) if firstsymbol(lit).name.startswith(CONTROL)]),
                             logic.cnf2clauses(necessity)))  # Keep the control variables only.
        return necessary

    def destify(self, query, max_solutions: int = sys.maxsize, trace: bool = False, solver=PULP_CBC_CMD):
        """Compute the core which is the minimal set of controls under the inclusion to satisfy the query at stable state.
        Destify is a neologism that refers to the deliberate and purposeful act of shaping destiny by
        influencing or directing the course of events or outcomes towards an expected goal.

        :param query: The query defining the expected destiny or goal as propositional formula.
        :type query: Sympy formula

        :param max_solutions: Maximal number of solutions (Default the largest integer = sys.maxsize)
        :type max_solutions: int

        :param trace: Boolean flag determining whether the trace is activated (Default: False).
        :type trace: Bool

        :param solver: The PulpSolver used for solving the problem (Default: PULP_CBC_CMD).
        :type solver: Pulp function

        :return: The core of control
        :rtype: frozenset[Sympy symbol]
        """

        # Check if the query contains control variables.
        if not is_controlled(query):
            errmsg("The query has no controls of prefix", CONTROL, kind="WARNING")
            return frozenset(set())

        # Compute the prime implicants filtered by the negative controls.
        allprimes = logic.prime_implicants(query, isnegctrl, max_solutions=max_solutions, trace=trace, solver=solver)

        # The result is of the form ~ _u0X or ~_u1X. We thus need to get the control variable i.e. _u0X, _u1X
        ctrlprimes = {frozenset({firstsymbol(prime) for prime in primes}) for primes in allprimes}

        # Define the core composed of prime implicant sets that are minimal under the inclusion.
        core = {primeset for primeset in ctrlprimes if
                all(map(lambda otherprimeset: not (otherprimeset < primeset), ctrlprimes))}
        return frozenset(core)

    def filter_necessary(self, query, core: frozenset, trace: bool = False) -> frozenset:
        """
        Filter necessary controls in the network such that the query is satisfied for all stable states.
        This method must be applied to a non-controlled network to correctly functioning.

        This function filters controls from the given core based on the condition
        that they satisfy the query for all stable states of the controlled network.

        :param query: The Boolean query to be satisfied across all stable states of the controlled network.
        :type query: Sympy expression
        :param core: A set of prime implicants (controls) that will be filtered.
        :param trace: Determines whether to display progress information during filtering, (Defaults: False).
        :type trace: bool
        :return: A subset of the given `core` containing only the necessary controls.
        :rtype: frozenset
        """

        def all_stable_states_valid(controls: frozenset) -> bool:
            """
            Check whether the application of the control to the network leads to the satisfaction of the query for all stable states.

            :param controls: Prime implicants control
            :type controls: frozenset[Sympy symbol]

            :return: True if all stable states satisfy the query; otherwise, False.
            :rtype: Bool
            """

            # Convert prime controls into a list of actions: (variable, value)
            actions = controls2actions(controls)

            # Create a modified BooN descriptor with given variable assignments
            controlled_desc = self.desc.copy()
            for var, bool_value in actions:
                controlled_desc[var] = bool_value

            # Instantiate a controlled Boolean Network (BooN)
            controlled_boon = BooN(controlled_desc)

            stable_states = controlled_boon.stable_states

            # Validate the query against all stable states of the controlled network
            all_valid = all(query.subs(state) for state in stable_states)
            return all_valid

        # Check whether the network is not controlled.
        if any(map(is_controlled, self.desc.values())):
            errmsg("The network must not be controlled to correctly functioning", "empty set is returned.", kind="WARNING")
            return frozenset(set())

        # Filter the core for prime controls that satisfy the query for all stable states
        if trace:
            filtered_core = frozenset(ctrlprime for ctrlprime in tqdm(core,
                                                                      file=sys.stdout,
                                                                      ascii=False,
                                                                      desc='BooN >> DSTFY NECESSARY ',
                                                                      ncols=80,
                                                                      bar_format='{desc}: {percentage:3.0f}% |{bar}[{n_fmt:5s} - {elapsed} - {rate_fmt}]')
                                      if all_stable_states_valid(ctrlprime))
        else:
            filtered_core = frozenset(filter(all_stable_states_valid, core))

        return filtered_core
