
<h1 style="text-align:center">BooN</h1>
<p style="text-align:justify">The BooN project provides a complete set of functionalities for Boolean network analysis. 
It was originally designed to explore the modeling of genetic networks by Boolean networks. 
The project includes:</p>
 <ul>
 <li> the definition of a <b>Boolean network</b> with the possibility to load and save it; </li>
 <li> the computation of the <b>model of dynamics</b> with respect to a <b>mode</b> policy; </li>
 <li> the definition of the <b>interaction graph</b> including a modular decomposition of the interaction; </li>
 <li> the computation of <b> equilibria</b> based on dynamics model; </li>
 <li> the efficient symbolic computation of <b>stable states</b> based on SAT solver; </li>
 <li> the <b>controllability</b> analysis predicting which variables must be frozen 
  to reach the expected goal at stable states based on possibility and necessity query;</li>
 <li>also different basic functionalities are included as: variable renaming, delete variable,
 update formula and importing/exporting to a text file the Boolean network. </li>
 </ul>
<h3> BooN functionnalities </h3>
<p>The BooN project comprises 3 modules:</p>
<ul>
<li> <code>boon</code> module is related to the manipulation of Boolean network named BooN which is an object.</li>
<li> <code>logic</code> module includes basic functions on propositional formula,
as well as more advanced features like CNF conversion for large formulas, CNF conversion using Tseitin's method, 
and prime implicant calculation. These functions are used in the BooN modules. </li>
<li> The <code>boonify</code> module is the graphical interface for accessing project functions in BooN:
computation of dynamical model for synchronous and asynchronous mode, the computation ot the stable states, and 
the controllability analysis.</li>
</ul>

<p style="text-align:justify">
<code>example.py</code> illustrates the different functionalities of BooN.
A real case study on breast cancer (<code>breast-cancer-study.py</code> and <code>breast-cancer.boon</code> for the network)
is also available. This example aims to identify the causes of the cancer and to predict the therapeutic targets of cancer.
For exploring BooN interactively run <code>boonify.py</code></p>

<H3>BooN installation</H3>
Go in the directory of BooN and type: 
<ul>
<li> <code>pip install .</code>  </li>
<li> or,  <code> python -m pip install .</code></li>
</ul>

<H3> To cite this work</H3>
If you wish to cite this work, please use the following citation:<br>
<a href="https://pubmed.ncbi.nlm.nih.gov/30582550/"> Causal Reasoning on Boolean Control Networks Based on Abduction: Theory and Application to Cancer Drug Discovery</a>
<br/>
<i> Celia Biane, Franck Delaplace</i>
<br>
IEEE/ACM Trans Comput Biol Bioinform
. 2019 Sep-Oct;16(5):1574-1585. 
<br>
PMID: 30582550 - DOI: 10.1109/TCBB.2018.2889102

