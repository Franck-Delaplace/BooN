# Boolean Network analysis module
# Author: Franck Delaplace
# Creation date: January 2024
from __future__ import annotations

import copy
import datetime
import pickle
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
from sympy.logic.boolalg import to_cnf, to_dnf, is_dnf
from sympy.parsing.sympy_parser import parse_expr
import logic
from logic import LOGICAL, SYMPY, errmsg, firstsymbol

SIGNCOLOR: dict = {-1: 'crimson', 0: 'steelblue', 1: 'forestgreen'}  # colors of edges in the interaction graph w.r.t. to signs.
COLORSIGN = {to_rgb(color): sign for sign, color in SIGNCOLOR.items()}
EXTBOON: str = ".boon"  # file extension for save and load.
EXTXT: str = ".txt"  # file extension for to_textfile and from_textfile.
CONTROL: str = "_u"  # prefix name of the controllers.
BOONSEP: str = "\n"  # separator between the equations of a BooN.
# color list for graph drawing
COLOR: list[str] = ['gold', 'tomato', 'yellowgreen', 'plum', 'mediumaquamarine', 'darkorange',
                    'darkkhaki', 'forestgreen', 'salmon', 'lightcoral', 'cornflowerblue', 'orange',
                    'paleviolet', 'coral', 'dodgerblue', 'yellowgreen', 'orangered', 'pink', 'blueviolet', 'crimson']


def is_controlled(formula) -> bool:
    """Check whether a formula is controlled.
        :param formula: the input formula.
        :return: True if the formula is controlled otherwise False."""
    try:
        return any(map(lambda var: var.name.startswith(CONTROL), formula.free_symbols))
    except AttributeError:  # Boolean True, False not controlled.
        return False


def core2actions(core: frozenset) -> list:
    """Convert the core to a list of actions where an action is a list of (variable, Boolean).
    The actions are sorted by length meaning that the more parsimonious actions are at first.
    :param core: the core.
    :return: A list of combined actions."""
    ACTION: dict = {"0": False, "1": True}
    lctrl = len(CONTROL)
    actions = [[(symbols(str(ctrl)[lctrl + 1:]), ACTION[str(ctrl)[lctrl]]) for ctrl in primes] for primes in core]
    # Sort the actions by length.
    actions = sorted(actions, key=len, reverse=False)
    return actions


def asynchronous(variables: list | set) -> frozenset:
    """Asynchronous or sequential mode. One variable is updated per transition.
    :param: variables: list of variables.
    :return: set of sets: {{x1},...,{xi},...,{xn}} representing the asynchronous mode."""
    return frozenset({frozenset({x}) for x in variables})


def synchronous(variables: list | set) -> frozenset:
    """synchronous or parallel mode. All the variables are updated jointly per transition.
        :param: variables: list of variables.
        :return: set of sets: {{x1,...,xi,...,xn}} representing the synchronous mode."""
    return frozenset({frozenset({*variables})})


def state2int(state: dict | tuple, variables: set | list | None = None) -> int:
    """Convert a set of states to an integer.
    :param state: state of the variables.
    :param variables: list of variables. If the list is empty then the encoding order corresponds to the variable occur. (Defaults [])
    :return: an integer such that its binary profile represents the state.
    """
    BOOL2BIN: dict = {False: '0', True: '1', 0: '0', 1: '1'}
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
    :param: int_state: the state coded into integer.
    :param: variables: list of variables.
    :return: a dictionary state. """
    BIN2BOOL: dict = {'0': False, '1': True}
    bin_state = format(int_state, 'b').zfill(len(variables))
    return dict(zip(variables, [BIN2BOOL[state] for state in bin_state]))


def hypercube_layout(arg: int | nx.Digraph) -> dict:
    """Compute the hypercube layout of a graph.
    :param: arg: the dimension of the hypercube or the network to which the layout is applied.
    :return: a dictionary {int:position} where int is the integer code of the hypercube labels."""
    dim = 0
    if isinstance(arg, int):
        dim = arg
    elif isinstance(arg, nx.DiGraph):
        dim = int(math.log2(arg.number_of_nodes()))

    H = nx.hypercube_graph(dim)
    pos = nx.spring_layout(H)
    return {state2int(node): pos[node] for node in pos}


# noinspection PyMethodFirstArgAssignment
class BooN:
    """Boolean Network Class."""
    desc: dict = {}  # Boolean network descriptor.
    style: dict = {}  # output form of the BooN (str).
    pos: dict = {}  # graph position of the variables.

    def __init__(self, descriptor=None, style=LOGICAL, pos: dict = {}) -> None:
        """Initialize the BooN object.
        :param: descriptor, dict: the descriptor of a Boolean Network.
        :param: style, the output style of formulas  (Default: LOGICAL).
        :param: pos, positions of the variable in the interaction graph drawing.
                If empty, the pos are generated during the drawing (Default: {}). """
        if descriptor:
            self.desc = descriptor
        else:
            self.desc = {}
        self.style = style
        self.pos = pos

    def __copy__(self):
        return BooN(self.desc, self.style, self.pos)

    def __deepcopy__(self, memo):
        return BooN(copy.deepcopy(self.desc, memo), self.style, copy.deepcopy(self.pos, memo))

    def __str__(self) -> str:
        return BOONSEP.join([f"{str(var)} = {logic.prettyform(self.desc[var], self.style, 0)}" for var in self.variables])

    def __eq__(self, other: BooN) -> bool:
        if not isinstance(other, BooN):
            return NotImplemented
        return self.desc == other.desc

    @property
    def variables(self) -> set:
        """Return the set of variables."""
        return set(self.desc.keys())

    def delete(self, variable) -> None:
        """Delete a variable in a BooN. The formulas must all be in DNF to properly delete the variable.
        :param variable: the variable to delete."""

        def delete(formula, val):  # sub function deleting a variable in a formula.
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
            self.desc[var] = delete(self.desc[var], False)

    def rename(self, source: Symbol, target: Symbol) -> None:
        """Rename a variable.
        :param: source, Symbol: the variable to rename.
        :param: target, Symbol: the variable renaming the source."""
        variables = self.variables

        if source not in variables:
            errmsg("the variable to rename does not exist", source)
        if target in variables:
            errmsg("the renamed variable cannot be in BooN variables", target)

        for var in variables:
            if not isinstance(self.desc[var], bool):
                self.desc[var] = self.desc[var].subs(source, target)

        self.desc[target] = self.desc.pop(source)

    def copy(self) -> BooN:
        """Perform a deep copy of the Boolean network."""
        return copy.deepcopy(self)

    # || FILE
    def save(self, filename: str = "BooN" + datetime.datetime.now().strftime("%d-%b-%y-%H") + EXTBOON) -> None:
        """Save the Boolean Network to file.  If the extension is missing then .boon is added.
        :param:filename, str: the name of the file to save the network (Default: BooN+date+hour.boon)"""

        fullfilename = filename if "." in filename else filename + EXTBOON
        with open(fullfilename, 'wb') as f:
            pickle.dump(self, f)
            f.close()

    def load(self, filename: str) -> None:
        """Load the Boolean Network from file. If the extension is missing then .boon is added.
        :param:filename, str: the name of the file to load the network.
        """
        fullfilename = filename if "." in filename else filename + EXTBOON
        try:
            with open(fullfilename, 'rb') as f:
                boon = pickle.load(f)
                self.desc = boon.desc
                self.style = boon.style
                self.pos = boon.pos
                f.close()
        except FileNotFoundError:
            errmsg("No such file or directory, no changes", fullfilename, "WARNING")

    def to_textfile(self, filename: str) -> None:
        """Export the Boolean network in a text file. If the extension is missing then .txt is added.
        The separator of formulas is defined by BOONSEP variable.
        :param:filename: the file name."""
        fullfilename = filename if "." in filename else filename + EXTXT
        with open(fullfilename, 'w') as f:
            tmp = self.style
            self.style = SYMPY
            f.write(str(self))
            self.style = tmp
            f.close()

    def from_textfile(self, filename: str) -> None:
        """Import the Boolean network from a text file. If the extension is missing then .txt is added.
        The separator of formulas is defined by BOONSEP variable.
        :param:filename: the file name to import the Boolean network.
        :return BooN: the Boolean network where the nodes are circularly mapped."""
        fullfilename = filename if "." in filename else filename + EXTXT
        desc = {}
        try:
            with open(fullfilename, 'r') as f:
                text = " ".join(f.readlines())  # Join all the lines in 1 string.
                text = map(lambda s: s.strip(), text.split(BOONSEP))  # And next separate the string w.r.t. the separator BOONSEP
                for i, line in enumerate(text, 1):  # Parse the network description. A line is of the form: <var> = <formula>, comment line start with '#'
                    if line.startswith('#'):  # Skip comment.
                        pass
                    elif line == '':  # Skip empty line.
                        pass
                    else:
                        try:  # Find = sign.
                            equal = line.index("=")
                        except ValueError:
                            errmsg(f"Syntax error, = is missing, line {i} in file", fullfilename, "READ ERROR")
                            return
                        try:  # Set the variable to symbol.
                            var = symbols(line[:equal].strip())
                        except ValueError:
                            errmsg(f"Syntax error, wrong variable name, line {i} in file", fullfilename, "READ ERROR")
                            return
                        try:  # Parse formula.
                            formula = parse_expr(line[equal + 1:].strip())
                        except SyntaxError:
                            errmsg(f"Syntax error, wrong formula parsing, line {i} in file", fullfilename, "READ ERROR")
                            return
                        desc.update({var: formula})
                f.close()
        except FileNotFoundError:
            errmsg("No such file or directory, no changes", fullfilename, "WARNING")
            return

        self.desc = desc
        ig = self.interaction_graph
        circular_positions = ig.get_circular_layout([(str(src), str(tgt)) for src, tgt in ig.edges()], origin=(0.1, 0.15), scale=(0.8, 0.8))
        self.pos = {symbols(var): pos for var, pos in circular_positions.items()}

    # || NORMAL FORM CONVERSION
    def cnf(self, variable: Symbol | None = None, simplify: bool = True, force: bool = True) -> None:
        """Convert the formulas of the Boolean network to CNF.
        :param: variable: the variable where the formula  is to be converted in CNF (Default None).
                          If variable is None then all the formulas are converted to CNF.
        :param: simplify: Boolean flag determining whether the formula should be simplified (Default True).
        :param: force: Boolean flag forcing the complete simplification (Default True)."""

        if variable:
            try:
                self.desc[variable] = to_cnf(self.desc[variable], simplify=simplify, force=force)
            except KeyError:
                errmsg("The variable is not found", variable)
        else:
            for var in self.desc:
                self.desc[var] = to_cnf(self.desc[var], simplify=simplify, force=force)

    def dnf(self, variable: Symbol | None = None, simplify: bool = True, force: bool = True) -> None:
        """Convert formula(s) of the Boolean network to DNF.
        :param: variable: the variable where the formula is to be converted in DNF (Default: None).
                          If variable is None then all the formulas are converted to DNF.
        :param: simplify: Boolean flag determining whether the formula should be simplified (Default: True).
        :param: force: Boolean flag forcing the complete simplification (Default: True)."""

        if variable:
            try:
                self.desc[variable] = to_dnf(self.desc[variable], simplify=simplify, force=force)
            except KeyError:
                errmsg("The variable is not found", variable)
        else:
            for var in self.desc:
                self.desc[var] = to_dnf(self.desc[var], simplify=simplify, force=force)

    # || INTERACTION GRAPH
    @property
    def interaction_graph(self) -> nx.DiGraph:
        """Build the interaction graph.
        :return: the interaction graph."""
        all_dnf = all(map(is_dnf, self.desc.values()))  # Trace whether the formulas are in DNF.
        if all_dnf:
            net = self
        else:  # if the network formulas are not in DNF then convert them into DNF.
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
                for i, lits in enumerate(all_literals_clauses, 1):
                    if src in lits:
                        module.add(i)
                    elif Not(src) in lits:
                        module.add(-i)
                    else:
                        pass
                ig.add_edge(src, var, sign=0, module=module)

        ig.add_nodes_from(variables)
        return ig

    def draw_IG(self, IG: nx.DiGraph | None = None, modular: bool = False, **kwargs):
        """Draw the interaction graph.
        :param IG: the interaction graph or None. If None, the interaction graph is generated from BooN (Default: None).
        :param modular: Boolean indicating whether the modular structure of interactions is displayed if True (Default: False)
        :param kwargs: additional keyword arguments to pass to the interaction graph drawing"""

        ig = copy.deepcopy(IG) if IG else self.interaction_graph

        if not ig.nodes():
            errmsg("The interaction graph has no nodes", "", "WARNING")
            return  # Graph must have nodes to be drawn.

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
                 node_color='antiquewhite',
                 node_labels=True,
                 node_size=6,
                 node_label_fontdict=dict(family='sans-serif', color='black', weight='semibold'),
                 arrows=True,
                 edge_width=1,
                 edge_color=sign_color,
                 pos=self.pos,
                 **module_args,
                 **kwargs)
        return ig

    def from_ig(self, IG: nx.DiGraph):
        """Define the descriptor of a BooN from an interaction graph.
        :param IG:  interaction graph."""
        # Find the maximal number of modules for each source variable.
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
                        errmsg("Internal error module coding - Please call the Software Development Team. ", [node, target, module])
                    nodes[target][abs(module) - 1].add(lit)

        # convert into formula
        self.desc = {node: Or(*(And(*clause) for clause in nodes[node])) for node in nodes}

    # || DYNAMICS
    def model(self, mode: Callable = asynchronous, self_loop: bool = False) -> nx.DiGraph:
        """Compute the dynamical datamodel of the BooN w.r.t. a mode.
        :param: self_loop Boolean: determines whether the boon loops are included in the datamodel (Default: False).
        :param: mode function: determines the mode policy applied to the datamodel (Default: asynchronous).
        :return: a Digraph representing the complete state based dynamics."""

        def next_state(state, change):  # update a state from changes.
            target = state.copy()
            target.update(change)
            return target

        variables = self.variables
        modalities = mode(variables)
        allstates = [dict(zip(variables, state)) for state in product([False, True], repeat=len(variables))]
        # Compute the state transition w.r.t. the network.
        transition = [
            (state,
             next_state(state,
                        {var: self.desc[var].subs(state) if not isinstance(self.desc[var], bool) else self.desc[var]
                         for var in modality})
             )
            for state in allstates for modality in modalities]
        # remove duplicated transitions.
        transition = [edge for i, edge in enumerate(transition) if edge not in transition[:i]]
        # remove boon loop if requested.
        if not self_loop:
            transition = filter(lambda edge: edge[0] != edge[1], transition)
        # Graph creation with nodes as integers coding the states.
        G = nx.DiGraph()
        try:
            G.add_nodes_from([state2int(state, variables) for state in allstates])
        except ValueError:
            pass
        G.add_edges_from([(state2int(src, variables), state2int(tgt, variables)) for src, tgt in transition])
        return G

    def draw_model(self, model: nx.DiGraph | None = None, mode: Callable = asynchronous, color: list[str] = COLOR, **kwargs) -> None:
        """Draw the graph representing the datamodel of dynamics.
        :param: datamodel, Digraph: input datamodel of the BooN or None (Default: None).
        if it is None the asynchronous datamodel computed from the BooN.
        :param: mode function: function characterizing the mode of the datamodel (Default: asynchronous)
        :param: color, list of colors for highlighting the equlibria (Default: COLOR)
        :param: **kwargs: extra parameters of nx.draw_networkx."""

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

    def equilibria(self, model: nx.DiGraph | None, mode: Callable = asynchronous) -> list[list]:
        """Calculate equilibria for the network based on datamodel dynamics.
         The method examines an exponential number of states, and thus it is restricted to networks with a small number of variable (max. ~10).
        :param: datamodel: datamodel from which the  equilibria are calculated.
                       If the datamodel is None, then the datamodel will be calculated from BooN. (Default: None)
        :param: mode, function: updating mode function, used if the datamodel is None  (Default: asynchronous).
        :return: Equilibria structure as a list of lists where each sublist is an attractor."""

        themodel = model if model else self.model(mode=mode)

        scc = list(nx.strongly_connected_components(themodel))  # Compute the Strongly Connected Components.
        quotient_model = nx.quotient_graph(model, scc)  # Deduce the quotient graph of the SCCs.
        equilibria = [node for node in quotient_model.nodes if quotient_model.out_degree(node) == 0]  # Determine equilibria as the sink in the quotient graph, i.e. terminal SCC.
        return [[int2state(state, self.variables) for state in attractor] for attractor in equilibria]  # Encode the equilibria.

    def stability_constraints(self):
        """Define the stability constraints for a BooN."""
        return And(*map(lambda var: Equivalent(var, self.desc[var]), self.variables))

    @property
    def stable_states(self) -> list[dict]:
        """Compute all the stable states of a BooN.
        The algorithm is based on SAT solver."""

        solver = z3.Solver()  # initialize z3 solver
        solver.add(logic.sympy2z3(self.stability_constraints()))  # add stability constraints translated in z3.

        # Enumerate all models
        models = []
        while solver.check() == z3.sat:
            model = solver.model()
            models.append(model)
            # Block the current datamodel to enable the finding of another datamodel.
            block = [sol() != model[sol] for sol in model]
            solver.add(z3.Or(block))

        # convert the solution to a list of states.
        return list(map(lambda model: {symbols(str(sol())): bool(model[sol]) for sol in model}, models))

    # || CONTROLLABILITY

    def control(self, frozenfalse: set | list | frozenset, frozentrue: set | list | frozenset) -> None:
        """Set control on the BooN. The  controlled variables are divided in two classes:
        the variables frozen to false and the variables frozen to true. A variable can be in both classes.
        :param frozenfalse: list, set or sequence of variables that should be frozen to false by control.
        :param frozentrue: list, set or sequence  of variables that should be frozen to true by control. """
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

    def possibly(self, query):
        """Compute the possibility constraint.
        :param query: a formula characterizing the query, objective or goal.
        :return: a formula specifying the possibility."""
        return And(self.stability_constraints(), query)

    def necessary(self, query, trace: bool = False):
        """Compute the necessary constraints.
        :param query: a formula characterizing the query, objective or goal.
        :param trace: Boolean flag determining whether the trace is activated (Default value = False).
        :return: CNF specifying the necessity."""

        if not self.desc:
            return True

        # specification of the necessity.
        stability = self.stability_constraints()
        necessity = logic.supercnf(Implies(stability, query), trace)
        necessary = And(*map(lambda clause:
                             Or(*[lit for lit in logic.clause2literals(clause) if firstsymbol(lit).name.startswith(CONTROL)]),
                             logic.cnf2clauses(necessity)))
        return necessary

    @staticmethod
    def destify(query, trace: bool = False, solver=PULP_CBC_CMD):
        """Compute the core which is the minimal set of controls under the inclusion to satisfy the query.
        Destify is a neologism that refers to the deliberate and purposeful act of shaping destiny by
        influencing or directing the course of events or outcomes towards an expected goal.
        :param query: the query defining the expected destiny or goal as propositional formula.
        :param trace: Boolean flag determining whether the trace is activated (Default: False).
        :param solver: the PulpSolver used for solving the problem (Default: PULP_CBC_CMD)."""

        # predicate selecting the negative control.
        def isnegctrl(lit) -> bool:
            return firstsymbol(lit).name.startswith(CONTROL) and isinstance(lit, Not)

        if not is_controlled(query):
            errmsg("The query has no controls of prefix", CONTROL, kind="WARNING")
            return frozenset(set())

        allprimes = logic.prime_implicants(query, isnegctrl, trace=trace, solver=solver)
        # The result is of the form ~ _u0X; we need to get the control i.e. u0X
        ctrlprimes = {frozenset({firstsymbol(prime) for prime in primes}) for primes in allprimes}

        # Define the core composed of prime implicant sets that are minimal under the inclusion.
        core = {primeset for primeset in ctrlprimes if
                all(map(lambda otherprimeset: not (otherprimeset < primeset), allprimes))}
        return frozenset(core)
