
<h1 style="text-align:center">BooN</h1>
<p style="text-align:justify">The BooN project provides a complete set of functionalities for Boolean Network (BooN) analysis. 
It was originally designed to explore the modeling of genetic networks by Boolean networks.
The documentation related to the functions can be found here: <a href="https://franck-delaplace.github.io/BooN/"> 
https://franck-delaplace.github.io/BooN/</a>. 
 <b> To compute BooN using the Graphical Interface, please run <code>boonify</code>.</b>


The project includes:</p>
 <ul>
 <li> the definition of a <b>Boolean network</b> with the possibility to load and save it; </li>
 <li> the computation of the <b>model of dynamics</b> with respect to a <b>mode</b> policy; </li>
 <li> the definition of the <b>interaction graph</b> including a modular decomposition of the interaction; </li>
 <li> the computation of <b> equilibria</b> based on a dynamics model; </li>
 <li> the efficient symbolic computation of <b>stable states</b> based on SAT solver; </li>
 <li> the <b>controllability</b> analysis predicting which variables must be frozen 
  to reach the expected goal at stable states based on the possibility and necessity query;</li>
 <li>also, different basic functionalities are included as: update formula and importing/exporting to a text file the Boolean network. </li>
 </ul>
<h3> BooN functionalities </h3>
<p>The BooN project comprises 3 modules:</p>
<ul>
<li> <code>boon</code> module is related to the manipulation of Boolean network named BooN, which is an object.</li>
<li> <code>logic</code> module includes basic functions on propositional formula,
as well as more advanced features like fast CNF conversion for large formulas, CNF conversion using Tseitin's method, 
and prime implicant calculation. These functions are used in the BooN modules. </li>
<li> The <code>boonify</code> module is the graphical interface manipulating BooN:
computation of a dynamical model for synchronous and asynchronous mode, the computation ot the stable states, and 
the controllability analysis. For exploring BooN interactively run <code>boonify.py</code></li>
</ul>

<p style="text-align:justify">
<code>example.py</code> illustrates the different functionalities of BooN.

<h3> Real case study </h3>
A real case study on breast cancer is available.
<code>breast-cancer-study.py</code>  is a python program defining all the steps of the analysis using <code>boon.py</code> library.
 This example aims to identify the causes of breast cancer and to predict the therapeutic targets.
<code>breast-cancer.boon</code> contains the Boolean network related to breast cancer study that can be used interactively with <code>boonify.py</code>.
The analysis is decomposed in two phases: first, we will consider the prediction of mutations causing breast cancer, 
and then the prediction of therapeutic actions by cancer type to cure <b>BRCA1</b> cancer.
In this section, we will detail the operations to apply with <code>boonify.py</code> in order to achieve these predictions. 
Following and testing this scenario will contribute to a deeper understanding of the potentiality of BooN for regulatory network analysis and its philosophy.
<h4> Start the analysis </h4>
<ul>
<li> first open <code>breast-cancer.boon</code> file. The model depicts a regulatory network in normal cell conditions.</li>
<li> Compute the stable stables. Two possible stable states are shown which respectively correspond to the apoptosis and the cellular division initiation.
Recall that each stable state is presumably associated to a characteristic phenotype. </li>
</ul>

<h4> Predicting mutations causing breast cancer</h4>
<ul>
<li> A cancerous situation corresponds here to a particular hallmark of cancer which is the loss of apoptosis. 
Cell division thus becomes the only phenotype describing the development of metastases.</li>
<li> The biomarkers are CyC1 and Bax. When <code>CycD1=False, Bax=True</code> at stable state, such a situation corresponds to apoptosis. 
By contrast, when <code>CycD1=True, Bax=False</code> the stable state represents the cell division. 
Please check these bio-marking at stable states 
for the initial normal cell condition.</li>
<li>The onset of cancer is thus linked to the inhibition of apoptosis,
which is indicated by the absence of its respective marking at stable state, namely:<code>CycD1=False, Bax=True</code>.
<li> To describe cancerous conditions, open the <b>Controllability</b> window and set Cyc1 to False and Bax to True in the <b>Destiny</b> sheet. </li>
<li> Then, select <b>[Avoid]</b> and <b>[Necessity]</b>. The programmed query is thus: 
<i>"There is never a stable state where <code>Cyc1=False, Bax=True</code>."</i>
  "</li>
<li> Execute this query. 3469 Models are produced and nine solutions are found. 
Note that a large number of models may require significant computational time.</li>
<li> The solutions describe the mutations required to trigger breast cancer. 
Please check the validity of these predictions in literature.  Some correspond to a single mutation (Solution 1 to  </li>
</ul>

<h4>Predicting therapeutic actions</h4>
<ul>
<li> Among the solutions describing mutation causing cancer, we do focus on BRCA1 mutation. 
Hence, select BRCA1=False (Solution 4) and apply it. Normally, the <b>Controllability</b> window closes.  </li>
<li> You can check that the modification is applied by opening the <b>BooN View</b> window, and you can also verify that the stable states have changed.
 <code>Cyc1=False,Bax=True</code> has disappeared.</li>
<li> Now, we examine the conditions for curing BRCA1-cancer. Open the <b>Controllability</b> window again. </li>
<li> The therapeutic actions thus must recover the apoptosis.</li>
<li> Again, fix Cyc1 to False and Bax to True. </li>
<li> Moreover, open the <b>observer</b> sheet and also check BRCA1 for excluding it to the potential targets since the mutation definitively freezes its state. </li>
<li> Select <b>[Reach]</b> and <b>[Possibility]</b>. The programmed query is thus: <i>'There exists a stable state having <code>Cyc1=False, Bax=True</code>'</i>.</li>
<li> Execute this query. Notice that the Possibility is always faster than the necessity. Three solutions are available. Please check their validity in literature.</li>
<li> Note that among the solutions, the controllability discovers that inhibiting PARP1 is a potential therapeutic target. Actually, PARP1 is the lethal partner of BRCA1 
enabling targeted cancerous therapy, and the lethal partners are hard to discover. </li>
</ul>

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
IEEE/ACM Trans Computer Biology & Bioinformatics
. 2019 Sep-Oct;16(5):1574-1585. 
<br>
PMID: 30582550 - DOI: 10.1109/TCBB.2018.2889102

