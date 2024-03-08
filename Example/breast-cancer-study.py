import time
import matplotlib.pyplot as plt
from sympy import SOPform, simplify_logic
from tabulate import tabulate
from boon import *

# The program analyzes the cause of breath cancer from a Boolean network datamodel,
# namely which genes should be mutated to cause cancer and are they oncogenes (True) or tumor suppressors (False).
# Next, the program found the potential therapeutic targets and the actions on them for a cancer caused by a BRCA1 mutation.

# Read the Boolean network from a text file.
bcn = BooN()
bcn.from_textfile("breast-cancer")

# Show the Boolean network
print(" - Boolean Network - ")
print(bcn)

# print all the genes.
print("\n", "List of genes: ", bcn.variables)

# Compute the stable states.
print("\n" * 2, " - Stable States -")
stable_states = bcn.stable_states

print(tabulate(stable_states, headers='keys', tablefmt='plain'))

# *** Controllability analysis

# Define the biomarkers
CycD1, Bax = symbols("CycD1 Bax")
biomarkers = {CycD1, Bax}

# Characterize a marking corresponding to the apoptosis
marking = {CycD1: False, Bax: True}
print("Apoptosis biomarkers")
print(tabulate([marking], headers='keys', tablefmt='plain'))

# convert the marking into a formula
apoptosis_marking = SOPform(biomarkers, [marking])

# Set the marking formula of cancer forbidding the apoptosis, that is the negation of apoptosis query, A cell therefore cannot dies.
kquery = simplify_logic(~apoptosis_marking, force=True)

print("Disease query, apoptosis forbidden: ", kquery)

# Define the variables where a control can be applied to force the variable to True (1) or False (0).
# A variable can have both controls.
# The biomarkers are always excluded from the control since they are observers.

frozenvars0 = frozenvars1 = bcn.variables - biomarkers
print("Frozen variables")
print(tabulate([frozenvars0, frozenvars1], tablefmt='grid'))

# Copy the network and fix the control on it.
bcc = bcn.copy()
bcc.control(frozenvars0, frozenvars1)

print("\nControlled Network")
print(bcc)

# Specification of the query that the biological network necessary reach whatever the stable state.
# The necessity stipulates that all the stable stables must meet the query.

print("\nQuery: Necessary avoid the apoptosis.")
start_time = time.time()
destiny = bcc.necessary(kquery, trace=True)  # activate the trace to see the evolution of the computation.
print("Runtime..: {:5.2f}".format(time.time() - start_time))
print("# clauses: {}".format(len(destiny.args)))
print("# symbols: {}".format(destiny.count(Symbol)))

print("\nCore")
# Compute the core.
start_time = time.time()
core = BooN.destify(destiny, trace=True)
print("Runtime: {:5.2f}".format(time.time() - start_time))

print("\nActions")  # Transform the core into actions.
actions = core2actions(core)
print(tabulate(actions))

# We define a situation of cancer with BRCA1 mutation.
print("\n" * 2, " - Mutate BRCA1  -")
BRCA1 = symbols("BRCA1")
bcn.desc[BRCA1] = False

print("Mutated network.")
print(bcn)

# copy the network and apply control
# Remove the mutated gene from the controlled variable since no modifications is possible.
frozenvars0 = frozenvars1 = frozenvars0 - {BRCA1}
bndrug = bcn.copy()  # fix control on a new instance of bcn.
bndrug.control(frozenvars0, frozenvars1)

# The issue is now to possibly find the actions inducing the apoptosis to deduce the therapeutic targets.
# The possibility stipulates that at least a stable stable fulfills the query property.
# the possibility operation is faster to generate than the necessity.
print("\nQuery : Possibly lead to apoptosis.")

start_time = time.time()
destiny = bndrug.possibly(apoptosis_marking)
print("Runtime..: {:5.2f}".format(time.time() - start_time))
print("# clauses: {}".format(len(destiny.args)))
print("# symbols: {}".format(destiny.count(Symbol)))

print("\nCore")
start_time = time.time()
core = BooN.destify(destiny)
print("Runtime: {:5.2f}".format(time.time() - start_time))

print("\nActions")  # Transform the core into actions.
actions = core2actions(core)
print(tabulate(actions))

# interaction graph
bcn.draw_IG()
plt.show()  # Show the interaction graph
