# The program illustrates the basic features of BooN.
import matplotlib.pyplot as plt
import networkx as nx
from sympy.abc import w, x, y, z, v
from tabulate import tabulate
from boon import *
from boon.logic import *
#%%
# Define the initial Boolean network
boon = BooN({x: y, y: x & z, z: w | ~x & v | y, w: x & y | ~x & z & ~w & ~v, v: ~v & w})
#%%
# Get the variables
print("Variables of BooN: ", boon.variables)
#%%
# Show BooN with different styles.
print("- SHOW NETWORK -")
print("Logical")
print(boon)
#%%
print("Sympy")
boon.style = SYMPY
print(boon)
#%%
print("Mathematica")
boon.style = MATHEMATICA
print(boon)
#%%
# Default style is LOGICAL
boon.style = LOGICAL
#%%
print("- DELETE v -")
boon.delete(v)
print(boon)
#%%
print("- RENAME w to v -")
boon.rename(w, v)
print(boon)
#%%
# compute the stable states
print("- STABLE STATES -")
stable = boon.stable_states
print(tabulate(stable, headers='keys', tablefmt='dpsl'))

print("\nStability constraints in logic:", prettyform(boon.stability_constraints()))
#%%
# initialize figures
_, ax2 = plt.subplots()
# Define the datamodel of dynamics
print("- MODEL ASYNCHRONOUS-")
M = boon.model()
ax2.axis('off')
boon.draw_model(M, pos=hypercube_layout(4), ax=ax2)
#%%
# Synchronous datamodel
print("- MODEL SYNCHRONOUS-")
MS = boon.model(mode=synchronous, self_loop=True)
_, ax3 = plt.subplots()
ax3.axis('off')
boon.draw_model(MS, pos=nx.shell_layout(MS), ax=ax3)
#%%
print("- EQUILIBRIA -")
eqs = boon.equilibria(model=MS)
for eq in eqs:
    print(tabulate(eq, headers='keys'))
#%%
# Build the interaction graph
IG = boon.interaction_graph

boon.pos = nx.circular_layout(IG)
_, ax1 = plt.subplots()
ax1.axis('off')
boon.draw_IG(IG, modular=True, ax=ax1)
#%%
# retrieve BooN from the interaction graph
print("- FROM INTERACTION GRAPH -")
boon2= BooN.from_ig(IG)
print(boon2)
#%%
# save and re-load in a new BooN boon2
print("SAVE and LOAD")
boon.save("bn")
print("BooN saved in bn.boon - next re loaded.")

boon2 = BooN.load("bn") # load is a static method of BooN
print(boon2)
#%%
print("- CNF Conversion -")
boon2.cnf()
print(boon2)
#%%
print(" - DNF conversion -")
boon2.dnf()
print(boon2)
#%%
# exportation and import from BoolNet file
print("- EXPORT & IMPORT -")
boon2.to_textfile('bn')
print("BooN exported as Bool Net format in bn.bnet - next imported. ")
boon2 = BooN.from_textfile('bn.bnet')
print(boon2)