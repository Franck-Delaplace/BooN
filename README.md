<h1> BooN  </h1>
The BooN project provides a complete set of functionalities for Boolean network analysis. 
It was originally designed to explore the modeling of genetic networks by Boolean networks. 
The project includes:
    <ul>
    <li> the definition of a Boolean network with the possibility to load and save it; </li>
    <li> the computation of the model of dynamics with respect to a <b>mode</b> policy;  </li>
    <li> the definition of the <b>interaction graph</b> including a modular decomposition of the interaction;  </li>
    <li> the  computation of all equilibria based on dynamics model;  </li>
    <li> the efficient symbolic computation of stable states based on SAT solver;  </li>
    <li> the <b>controllability</b> analysis predicting which variables must be frozen 
         to reach the expected goal at stable states based on possibility and necessity query;</li>
   <li>also different basic functionalities are included as: variable renaming, delete variable,
     update formula and importing/exporting to a text file the Boolean network. </li>
    </ul>

The BooN project comprises 3 modules:
<ul>
<li> <B>boon</B> module is related to the manipulation of Boolean network named BooN which is an object.</li>
<li>  <B>logic</B> module includes basic functions on propositional formula,
as well as more advanced features like CNF conversion for large formulas, CNF conversion using Tseitin's method, 
and prime implicant calculation. These functions are used in the BooN module. </li>
<li> <B>boonify</B> module is the graphical interface including all the functionalities of BooN:
computation of dynamical model for synchronous and asynchronous mode, the computation ot the stable states, and 
the controllability analysis.</li>
</ul>

The distribution includes examples to illustrate the different functionalities (c.f. <b> example.py</b>).
It also contains a real case study on breast cancer (<b>breast-cancer-study.py</b> and <b>breast-cancer.boon</b> for the network)
to identify the causes of the cancer and to predict the therapeutic targets of cancer.


<H3> To cite this work</H3>
<a href="https://pubmed.ncbi.nlm.nih.gov/30582550/"> Causal Reasoning on Boolean Control Networks Based on Abduction: Theory and Application to Cancer Drug Discovery</a>
<br/>
<i> Celia Biane, Franck Delaplace</i>
<br>
IEEE/ACM Trans Comput Biol Bioinform
. 2019 Sep-Oct;16(5):1574-1585. 
<br>
PMID: 30582550 - DOI: 10.1109/TCBB.2018.2889102
<H3>Used Python modules </H3> pulp, z3-solver, sympy tqdm, pickle, netgraph, networkx.