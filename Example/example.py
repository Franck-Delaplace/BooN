import matplotlib.pyplot as plt
import networkx as nx
from sympy.abc import w, x, y, z, v
from tabulate import tabulate
from boon import *
from logic import *

# The program illustrates the basic features of BooN

# Define the initial Boolean network
n = BooN({x: y, y: x & z, z: w | ~x & v | y, w: x & y | ~x & z & ~w & ~v, v: ~v & w})

# Get the variables
print("Variables of BooN: ", n.variables)

# Show BooN with different styles.
print("- SHOW NETWORK -")
print("Logical")
print(n)
print("Sympy")
n.style = SYMPY
print(n)
print("Mathematica")
n.style = MATHEMATICA
print(n)

# Default style is LOGICAL
n.style = LOGICAL

# Delete variable v
print("- DELETE v -")
n.delete(v)
print(n)

print("- RENAME w to v -")
n.rename(w, v)
print(n)

# compute the stable states
print("- STABLE STATES -")
stable = n.stable_states
print(tabulate(stable, headers='keys', tablefmt='dpsl'))

print("\nStability constraints in logic:", prettyform(n.stability_constraints()))

# initialize figures
_, ax1 = plt.subplots()
_, ax2 = plt.subplots()
_, ax3 = plt.subplots()

# Define the datamodel of dynamics
print("- MODEL ASYNCHRONOUS-")
M = n.model()
ax2.axis('off')
n.draw_model(M, pos=hypercube_layout(4), ax=ax2)

# Compute the datamodel based equilibria
print("- EQUILIBRIA -")
eqs = n.equilibria(model=M)
for eq in eqs:
    print(tabulate(eq, headers='keys'))

# Synchronous datamodel
print("- MODEL SYNCHRONOUS-")
MS = n.model(mode=synchronous, self_loop=True)
ax3.axis('off')
n.draw_model(MS, pos=nx.shell_layout(MS), ax=ax3)

print("- EQUILIBRIA -")
eqs = n.equilibria(model=MS)
for eq in eqs:
    print(tabulate(eq, headers='keys'))

# Build the interaction graph
IG = n.interaction_graph

n.pos = nx.circular_layout(IG)
ax1.axis('off')
n.draw_IG(IG, modular=True, ax=ax1)

# retrieve BooN from the interaction graph
print("- FROM INTERACTION GRAPH -")
n.from_ig(IG)
print(n)

# save and re-load in a new BooN m
n.save("bn")
m = BooN()
m.load("bn")  # load is a static method of BooN

print("- CNF Conversion -")
m.cnf()
print(m)

print(" - DNF conversion -")
m.dnf()
print(m)

# exportation and import from  text file
print("- EXPORT & IMPORT -")
m.to_textfile('boolnet')
m.from_textfile('boolnet.txt')  # static method of BooN
print(m)

# show the models and the interaction graph
plt.show()
