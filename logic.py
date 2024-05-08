# Boolean Network analysis module
# Author: Franck Delaplace
# Creation date: January 2024

import inspect
import pulp
import sys
import z3
from pulp import PULP_CBC_CMD
from sympy import symbols
from collections.abc import Callable
from sympy.core.symbol import Symbol
from sympy.logic.boolalg import And, Or, Not, Implies, Equivalent, Xor, Xnor, Boolean, BooleanTrue, BooleanFalse
from sympy.logic.boolalg import is_cnf
from tqdm import tqdm

# Dictionary defining the output style of the formula, see prettyform
LOGICAL: dict = {'type': 'infix', And: '\u2227', Or: '\u2228', Implies: '\u21D2', Equivalent: '\u21D4', Xor: '\u22BB', Not: '\u00AC', False: 'false', True: 'true'}
MATHEMATICA: dict = {'type': 'prefix', '(': "[", ')': "]",
                     And: '&&', Or: '||', Xor: 'Xor', Xnor: 'Xnor', Implies: 'Implies', Equivalent: 'Equivalent', Not: '!', False: 'False', True: 'True'}
SYMPY: dict = {'type': 'prefix', '(': "(", ')': ")",
               And: '&', Or: '|', Implies: 'Implies', Xor: 'Xor', Xnor: 'Xnor', Equivalent: 'Equivalent', Not: '~', False: 'False', True: 'True'}
JAVA: dict = {'type': 'normal form', And: "&&", Or: "||", Not: "!", False: 'false', True: 'true'}
C: dict = {'type': 'normal form', And: "&&", Or: "DEF:", Not: "!", False: '0', True: '1'}

SOLVER = PULP_CBC_CMD  # Default PULP solver
PATHSEP: str = "\\"  # Separator in the file path.

prime_implicants_problem = None  # Global variable storing the last prime implicants problem specification.
trc_clauses = 0  # global variables counting the number of CNF clauses in supercnf function
trc_cnf = 0 # global variables counting the number of clauses converted to CNF in supercnf function
trc_implicants = 0 # global variables counting the number of prime implicants in prime_implicants
# DEF: Basic functions
def errmsg(msg: str, arg="", kind: str = "ERROR") -> None:
    """Display an error message and exit in case of error (keyword ERROR).
    :param msg: the error message.
    :param arg: the argument of the error message (Default: "" no args).
    :param kind: type of error (Default: ERROR)."""
    print(f"** {kind}: {inspect.stack()[1].filename.split(PATHSEP)[-1]} - {inspect.stack()[1].function}: {msg}: {arg}")
    if kind == "ERROR": exit()


def firstsymbol(formula):
    """ Extract the first symbol from the set of symbols of a dnf.
    :param formula: the input dnf.
    :return: the first symbol."""
    if isinstance(formula, bool | BooleanFalse | BooleanTrue):  # The formula is reduced to a Boolean value, no symbols.
        return None
    else:  # The formula has at least 1 symbol.
        return next(iter(formula.free_symbols))


# DEF: Functions decomposing a formula.
def cnf2clauses(cnf):
    """ Decomposition of a CNF into a sequence of clauses.
    :param cnf: CNF formula
    :return: sequence of clauses."""
    if isinstance(cnf, And):  # The cnf is  plain (And of Or-clauses).
        clauses = cnf.args
    elif isinstance(cnf, bool | BooleanFalse | BooleanTrue):  # The cnf is reduced to a boolean value.
        clauses = ()
    else:
        clauses = (cnf,)  # Otherwise the cnf is reduced to a single clause.
    return clauses


def clause2literals(clause) -> set:
    """" Convert a clause or a cube into of a sequence of literals.
    :param: clause: the clause or cube.
    :return: set of literals."""
    if isinstance(clause, Symbol | Not):  # clause reduced to a single literal.
        literals_clause = {clause}
    elif isinstance(clause, bool | BooleanFalse | BooleanTrue):  # clause reduced to Boolean value.
        literals_clause = set()
    else:  # plain clause.
        literals_clause = set(clause.args)
    return literals_clause


# DEF: Functions converting the formula into another style.
def prettyform(formula, style: dict = LOGICAL, depth=0):
    """Return a string of a formula in nice form.
    :param formula: the input formula.
    :param style: the style style of the logical operators (Default: LOGICAL)
    :param depth: the current depth of the formula for setting parentheses (Default: 0)"""
    if isinstance(formula, bool | BooleanFalse | BooleanTrue):
        return style[formula]
    elif isinstance(formula, Symbol):
        return str(formula)
    elif isinstance(formula, Not):
        return style[Not] + prettyform(formula.args[0], style, depth + 1)
    elif isinstance(formula, And | Or):
        new_formula = " {} ".format(style[type(formula)]).join(map(lambda f: prettyform(f, style, depth + 1), formula.args))
        return new_formula if depth == 0 else "(" + new_formula + ")"
    else:  # other operators than Or, And
        try:
            match style['type']:
                case 'infix':
                    new_formula = " {} ".format(style[type(formula)]).join(map(lambda f: prettyform(f, style, depth + 1), formula.args))
                    return new_formula if depth == 0 else "(" + new_formula + ")"
                case 'prefix':
                    return style[type(formula)] + style["("] + ", ".join(map(lambda f: prettyform(f, style, 0), formula.args)) + style[")"]
                case 'normal form':
                    errmsg("Normal form formula only", formula)
                case _:
                    errmsg("Internal program error on style", style['type'])
        except KeyError:
            errmsg(f"Unknown operator of type {type(formula)}", formula)


def sympy2z3(formula):
    """Convert a sympy formula to z3 formula.
    :param formula: the formula to convert.
    :return: the equivalent z3 formula."""
    if isinstance(formula, bool):
        return formula
    elif isinstance(formula, BooleanTrue):
        return True
    elif isinstance(formula, BooleanFalse):
        return False
    elif isinstance(formula, Symbol):
        return z3.Bool(formula.name)
    elif isinstance(formula, Not):
        return z3.Not(sympy2z3(formula.args[0]))
    elif isinstance(formula, Or):
        return z3.Or([*map(sympy2z3, formula.args)])
    elif isinstance(formula, And):
        return z3.And([*map(sympy2z3, formula.args)])
    elif isinstance(formula, Implies):
        return z3.Implies(sympy2z3(formula.args[0]), sympy2z3(formula.args[1]))
    elif isinstance(formula, Equivalent):
        return sympy2z3(formula.args[0]) == sympy2z3(formula.args[1])
    else:
        errmsg("a piece of the formula is not recognized", formula)


# DEF: Advanced functionalities: fast CNF conversion, prime implicants computation.
TEITSIN: str = "_t6n"  # prefix of the new variables introduced in Teitsin conversion
_varcounter = 0  # counter1 used in newvar.


def newvar(initialize: int | None = None):
    """Create a new sympy symbol of the form <prefix><number>.
       The prefix is given by TSEITIN constant.
     :param initialize: initialize the counter1 if the value is an integer
     or let the counter1 increment by 1 if it is set to None (Default value = None)
     :return: a Sympy symbol."""
    global _varcounter
    if initialize is not None:
        _varcounter = initialize
    else:
        _varcounter = _varcounter + 1
    return symbols("{prefix}{counter:d}".format(prefix=TEITSIN, counter=_varcounter))


def tseitin(formula):
    """ Characterize the Tseitin form of a formula. The additional variables are prefixed by {}
    :param formula: the formula.
    :return: a pair: Tseitin variable, Tseitin CNF.""".format(TEITSIN)
    if isinstance(formula, bool | BooleanFalse | BooleanTrue):
        return formula, True
    elif isinstance(formula, Symbol):
        return formula, True
    elif isinstance(formula, Not):
        # (¬ p ∨ ¬ p1) ∧ (p ∨ p1) ∧ c1
        p = newvar()
        p1, c1 = tseitin(formula.args[0])
        return p, And(Or(Not(p), Not(p1)), Or(p, p1), c1)
    elif isinstance(formula, Or):
        #  p, (¬p ∨ p1 ∨ p2) ∧ (p ∨ ¬p1) ∧ (p ∨ ¬p2) ∧ c1 ∧ c2)
        p = newvar()
        p1, c1 = tseitin(formula.args[0])
        p2, c2 = tseitin(Or(*formula.args[1:]))
        return p, And(Or(Not(p), p1, p2), Or(p, Not(p1)), Or(p, Not(p2)), c1, c2)
    elif isinstance(formula, And):
        # p, (p ∨ ¬p1 ∨ ¬p2) ∧ (¬p ∨ p1) ∧ (¬p ∨ p2) ∧ c1∧ c2
        p = newvar()
        p1, c1 = tseitin(formula.args[0])
        p2, c2 = tseitin(And(*formula.args[1:]))
        return p, And(Or(p, Not(p1), Not(p2)), Or(Not(p), p1), Or(Not(p), p2), c1, c2)
    elif isinstance(formula, Implies):
        # p , (¬p ∨ ¬p1∨ p2) ∧ (p ∨ p1) ∧ (p ∨ ¬p2) ∧ c1∧ c2
        p = newvar()
        p1, c1 = tseitin(formula.args[0])
        p2, c2 = tseitin(formula.args[1])
        return p, And(Or(Not(p), Not(p1), p2), Or(p, p1), Or(p, Not(p2)), c1, c2)
    elif isinstance(formula, Equivalent):
        # p, (¬p ∨¬p1 ∨ p2)∧(¬p ∨ p1 ∨ ¬p2)∧(p ∨ ¬p1 ∨ ¬p2)∧(p ∨ p1 ∨ p2) ∧ c1 ∧ c2)
        p = newvar()
        p1, c1 = tseitin(formula.args[0])
        p2, c2 = tseitin(formula.args[1])
        return p, And(Or(Not(p), Not(p1), p2), Or(Not(p), p1, Not(p2)),
                      Or(p, Not(p1), Not(p2)), Or(p, p1, p2), c1, c2)
    else:
        errmsg("a piece of the formula is not recognized:", formula)
        return symbols("__failed__"), False


def tseitin_cnf(formula):
    """Convert a formula to CNF using Tseitin method.
    :param formula: the formula to be converted.
    :return: CNF formula."""
    newvar(0)  # initialize the counter1
    p, f = tseitin(formula)
    return And(p, f)


def supercnf(formula, trace: bool = False):
    """ Convert the formula to CNF. The method is adapted to large formula.
    :param formula: the formula to convert.
     :param trace: Boolean flag if True trace the computational steps  (Default value = False)
     :return: CNF formula
    """
    # Most of the classical methods cannot perform the CNF conversion on large formula in acceptable time (cf. to_cnf sympy, pyeda)
    # To overcome this disabling limitation, we design another method based on SAT solver.
    # Basically, let f be a formula, we define the CNF as ¬(SAT(¬f)) as ¬¬f = f, namely the negation of the satisfiable models of ¬f.
    # Let f be a formula, we compute all the models for ¬f. For each datamodel if x = True then return ~x and x if x=False.
    # The SAT solver must necessarily admit non CNF formula and be efficient. We use z3 solver which answers to these requirements.
    # This was really challenging to find an efficient method to convert very large formula in CNF, Yep ! I did it :-)
    global trc_clauses
    global trc_cnf
    solver = z3.Solver()  # initialize Z3 solver
    solver.add(sympy2z3(Not(formula)))  # add the negation of the formula.

    # Enumerate all models
    models = []
    trc_clauses = 0
    while solver.check() == z3.sat:
        model = solver.model()
        trc_clauses = trc_clauses + 1
        if trace:
            tqdm.write(f'\rBooN >> # models:[{trc_clauses:5d}]', end='')
        models.append(model)
        # Block the current datamodel to enable the finding of another datamodel.
        block = [sol() != model[sol] for sol in model]
        solver.add(z3.Or(block))  # if x=True, y=False then add x != True or y != False as constraint disabling the selection of the datamodel.

    # Convert the models into a CNF by negating the datamodel: x=True -> ~x, x=False -> x
    if trace:
        tqdm.write('')
        cnf = And(*[Or(*map(lambda sol: Not(symbols(str(sol))) if models[trc_cnf][sol] else symbols(str(sol)), models[trc_cnf]))
                    for trc_cnf in tqdm(range(len(models)), file=sys.stdout, ascii=False, desc='BooN >> CNF formatting', ncols=80,
                                      bar_format='{desc}: {percentage:3.0f}% |{bar}[{n_fmt:5s} - {elapsed} - {rate_fmt}]')])
    else:
        cnf = And(*[Or(*map(lambda sol: Not(symbols(str(sol))) if models[trc_cnf][sol] else symbols(str(sol)), models[trc_cnf]))
                    for trc_cnf in range(len(models))])
    return cnf


def prime_implicants(formula, kept: Callable = lambda lit: not firstsymbol(lit).name.startswith(TEITSIN), trace: bool = False, solver: type = SOLVER) -> frozenset:
    """Compute all the prime implicants of a propositional formula where the literals are filtered by kept function.
    :param formula: the input formula. The formula does not need to be in CNF.
    :param kept: predicate selecting the literals that are kept in the solutions (Default: function discarding the Tseitin working variables)
    :param trace: Boolean flag determining whether the trace showing the resolution is activated (Default: False).
    :param solver: the solver to use (Default: Pulp solver).
    :return: all the prime implicants in the form of a set of sets where each subset represent one prime implicant filtered by kept."""
    global prime_implicants_problem
    global trc_implicants
    cnf = formula if is_cnf(formula) else tseitin_cnf(formula)  # Convert the dnf into CNF by the Tseitin method if needed.

    #  Gather all literals from CNF
    literals = {lit for clause in cnf2clauses(cnf) for lit in clause2literals(clause)}

    # Find the critical variables where a literal and its négation both occur in the CNF formula.
    negvars = {lit for lit in literals if isinstance(lit, Not)}
    posvars = literals - negvars
    negvars = set(map(firstsymbol, negvars))  # Extract the variables from the negative literals.
    criticalvars = posvars & negvars  # Critical variables occurring positively and negatively in the formula.

    # Create a dictionary associating the literals to their Boolean pulp variable of the same name.
    # This dictionary is used to convert the literals into pulp variables (vlit[lit])
    vlit = {lit: pulp.LpVariable(str(lit), lowBound=0, upBound=1, cat=pulp.LpInteger) for lit in literals}

    if trace: tqdm.write("BooN >> Initialize prime implicants solving.", end="")
    # Initialize the prime implicants problem in pulp.
    primes = pulp.LpProblem("Prime_Implicants", pulp.LpMinimize)

    # Objective function = sum of all literals selected by kept function.
    objective_function = pulp.lpSum([vlit[lit] for lit in literals if kept(lit)])
    primes += objective_function

    # Get the sequence of clauses of the CNF.
    clauses = cnf2clauses(cnf)

    # Define the clauses as constraints  x |~y | z  --> x + ~y + z >= 1
    for i, clause in enumerate(clauses):  # Extract the literals of the current clause.
        literals_clause = clause2literals(clause)
        # Transform the current clause into constraints
        primes += pulp.lpSum([vlit[literal] for literal in literals_clause]) >= 1, "CLAUSE_" + str(i)

    # Define the exclusive choice  constraint between a variable and its negation, i.e. x + ~x <= 1
    for var in criticalvars:
        primes += vlit[var] + vlit[Not(var)] <= 1, "EXCLUSION_" + var.name.strip()

    # Find all the solutions until no solutions are found.
    solutions = set()
    status = pulp.LpStatusOptimal
    trc_implicants = 0
    while status == pulp.LpStatusOptimal:   # while a solution is found
        primes.solve(solver(msg=0))  # Quiet solving
        status = primes.status
        if status == pulp.LpStatusOptimal:
            trc_implicants = trc_implicants + 1
            if trace: tqdm.write(f'\rBooN >> # solutions:[{trc_implicants:3d}]     ', end='')
            solution = frozenset({lit for lit in literals if kept(lit) and vlit[lit].varValue == 1.})
            solutions.add(solution)

            # Add the constraint discarding the found solution, e.g.  s = {x, ~y, z} --> x+~y+z <= 2 s.t. len(s)-1 = 2.
            discard_solution = pulp.lpSum(map(lambda lit: vlit[lit], solution)) <= len(solution) - 1, "OUT_" + str(trc_implicants)
            primes += discard_solution
    prime_implicants_problem = primes  # keep the specification of the problem in a global variable.
    if trace: tqdm.write('')
    return frozenset(solutions)
