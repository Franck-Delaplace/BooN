(* ::Package:: *)

(* ::Title:: *)
(*BOONED*)
(*Boolean Networks Dynamic Package*)


(* ::Subtitle:: *)
(* Franck Delaplace 2013 - 2014 - 2015 - *)
(*2021 - inclusion of the multi-valued*)
(*2022 - conversion of Boolean network to ODE*)
(*2024 - Conversion to TikZ-network*)


(* ::Text:: *)
(*Reference: Analysis of Modular Organisation of Interaction Networks Based on Asymptotic Dynamics - CMSB 2012*)


(* ::Text:: *)
(*A collection of functions for boolean Network and multivalued analysis.*)


(* ::Section:: *)
(*Package Declaration*)


(* ::Input::Initialization:: *)
BeginPackage["Booned`",{"GraphUtilities`"}];


(* ::Input::Initialization:: *)
BoonType::usage="Type of Boolean network.";


MultiValuedType::usage="Type of multivalued network";


(* ::Subsection:: *)
(*Graph*)


(* ::Input::Initialization:: *)
ReflexiveReduce::usage="Compute the reflexive reduction of a graph.";


(* ::Input::Initialization:: *)
QuotientGraph::usage="QuotientGraph[graph,partition], defines the quotient graph according to a partition of vertices. An edge exists in between two parts if and only if there is an edge between two vertices respectively belonging to each part.";


ShowQuotient::usage="ShowQuotient[\!\(\*
StyleBox[\"ig\",\nFontSlant->\"Italic\"]\)] show the quotient graph of ig. the Option is ImageSize"


(* ::Subsection:: *)
(*States*)


Booned::appsize="The size of the state is different to the number of variables - Abort."


(* ::Input::Initialization:: *)
BoonCompose::usage="Compose symbolically either two Boolean Networks, BooNCompose[F1,F2] or a n-iterated composition BooNCompose[F,n]." 


(* ::Input::Initialization:: *)
StateToString::usage="StateToString[\!\(\*
StyleBox[\"state\",\nFontSlant->\"Italic\"]\)] converts a boolean \!\(\*
StyleBox[\"state\",\nFontSlant->\"Italic\"]\) to a binary string profile (eg. {a \[Rule] True, b \[Rule] False} gives \"10\").";


(* ::Input::Initialization:: *)
StateToInteger::usage="StateToString[state] converts a boolean state an integer whose binary profile corresponds to the agent state values.";


(* ::Input::Initialization:: *)
Observers::usage="Option of AttractorToTable to specify the list of the observers."


(* ::Input::Initialization:: *)
AttractorToTable::usage="AttractorToTable[attractor, OPTIONS], Shows an attractor as a graphic table of equilibria. The function has two options:
\[FilledSquare] 'ColorRules' defines the colors for False and True (Default False \[Rule] Red, True \[Rule] Green)
\[FilledSquare] 'Observers' defines the list of the observers (Default All)"


(* ::Input::Initialization:: *)
NiceEqs::usage="Draws the equilibria in graphical form, used for large set of equilibria.";


(* ::Input::Initialization:: *)
NiceStableStates::usage="compute using symbolic method and show the stable states in a table. 
Parameters:
\[FilledSquare] Boolean Network
\[FilledSquare] height of the table
\[FilledSquare] function  applied to stable states (Default \[FilledSquare])
\[FilledSquare] label of the values (Default \[FilledSquare])
Options
\[FilledSquare] ColorRules: rules attributing colors for True and False (Default {True \[Rule] Green, False \[Rule] Red}) 
\[FilledSquare] Background: color of the background (Default LightYellow)"


(* ::Subsection:: *)
(*Interaction graph*)


(* ::Input::Initialization:: *)
NiceIG::usage="NiceIG[\!\(\*
StyleBox[\"interaction\",\nFontSlant->\"Italic\"]\)\!\(\*
StyleBox[\" \",\nFontSlant->\"Italic\"]\)\!\(\*
StyleBox[\"graph\",\nFontSlant->\"Italic\"]\)] sets the interaction graph in a nice form." ;


Regulators::usage="Regulators[\!\(\*
StyleBox[\"ig\",\nFontSlant->\"Italic\"]\)\!\(\*
StyleBox[\",\",\nFontSlant->\"Italic\"]\)\!\(\*
StyleBox[\"v\",\nFontSlant->\"Italic\"]\)\!\(\*
StyleBox[\",\",\nFontSlant->\"Italic\"]\)\!\(\*
StyleBox[\"signs\",\nFontSlant->\"Italic\"]\)] finds the regulators of \!\(\*
StyleBox[\"v\",\nFontSlant->\"Italic\"]\) in the interaction graph \!\(\*
StyleBox[\"ig\",\nFontSlant->\"Italic\"]\), such that the sign belongs to the list \!\(\*
StyleBox[\"signs\",\nFontSlant->\"Italic\"]\).
\!\(\*
StyleBox[\"v\",\nFontSlant->\"Italic\"]\) is either a variable or a list of variables.
Parameters
\[FilledSquare] ig: interaction graph or Boolean network;
\[FilledSquare] v: vertex;
\[FilledSquare] signs: list of the signs that are -1,0 or 1. ex. {-1,1} correspond to the inhibitors (-1) and the activators (1). Default {-1,0,1}.";


(* ::Input::Initialization:: *)
InteractionGraphSimple::usage="InteractionGraphSimple[\!\(\*
StyleBox[\"f\",\nFontSlant->\"Italic\"]\)] defines a basic interaction graph  from a BooN \!\(\*
StyleBox[\"f\",\nFontSlant->\"Italic\"]\) which is a directed graph with weights -1 ,0 or 1.";


(* ::Input::Initialization:: *)
InteractionGraph::usage="Compute the interaction graph from a BooN. \[WarningSign] The formulas are set in DNF before extracting the arcs."; 


(* ::Input::Initialization:: *)
NiceIG3D::usage="NiceIG3D[\!\(\*
StyleBox[\"ig\",\nFontSlant->\"Italic\"]\)] 3D representation of an interaction graph. 
Parameters
\[FilledSquare] ig: an interaction graph
Options:
\[FilledSquare] ImageSize: size of image (Default Large);
\[FilledSquare] FontSize: size of the characters (Default Automatic - automatic adaptation to the image size);
\[FilledSquare] FontColor: colors of the font;
\[FilledSquare] Background: background (Default Dark gray); 
\[FilledSquare] VertexStyle: Style of Vertices (Default Yellow);
\[FilledSquare] GraphLayout: Layout of Graph (Automatic);
\[FilledSquare] ViewPoint:  gives the point in space from which three\[Hyphen]dimensional graph is to be viewed." ;


(* ::Input::Initialization:: *)
Sequential::usage="Sequential mode, one agent is updated per transition.";


(* ::Input::Initialization:: *)
Parallel::usage="Parallel mode, all the agents are updated per transition.";


(* ::Input::Initialization:: *)
SccOrganisation::usage="Defines a modular organisation based on strongly connected components of the interaction graph";


(* ::Subsection:: *)
(*Model*)


(* ::Input::Initialization:: *)
ModelOf::usage="Compute the state graph.The parameters are: 
\[FilledSquare] a BooN ModelOf[\[Eta]]. In this case the mode is Sequential/Asynchrone;
\[FilledSquare] a BooN and a mode function - ModelOf[\[Eta],Sequential];
\[FilledSquare] a BooN and a list defining the mode  - ModelOf[\[Eta], {{a1,a2},{a2,a3}} ];
\[FilledSquare] a BooN, a list and a list of agents  - ModelOf[\[Eta], {{a1,a2},{a2,a3}}, {a1,a2}]. In this  case, the state graph is restricted to the concerned agents. Notice that the states of the regulators are also added.";


(* ::Input::Initialization:: *)
StateGraph::usage="Synonym of ModelOf.";


(* ::Input::Initialization:: *)
NiceModel::usage="A nice view of a model. 
Options:
\[FilledSquare] EdgeLabels is an option with the following values: None, Automatic,All  or a list (Default None).  The result is a label on edges. The list specifies which agents must be considered for the labeling. Automatic = all the agents, All = all the agents with the sign of the evolution according to a lexicographic order. 
\[FilledSquare] VertexLabels whose values are Booleans or Integer, specifying how the states are represented (Default Boolean);
\[FilledSquare] ImageSize (Default Automatic);
\[FilledSquare] GraphLayout.";
NiceBM::usage="Synonym of NiceModel for version compatibility."


(* ::Input::Initialization:: *)
ModularEquilibria::usage="ModularEquilibria[\[Eta], morganisation] determines the equilibria according to a modular organisation of a BooN for Sequential mode. 'morganisation' is a modular organisation of variable." ;


(* ::Input::Initialization:: *)
FindEquilibria::usage="FindEquilibria[ model of dynamics ] Determines the equilibria from a stategraph. The result is a set of attractors.";


(* ::Input::Initialization:: *)
StableStates::usage="StableStates[boon, number of solutions] Computes the steady states for the sequential mode with a symbolic algorithm based on satisfiability of formulas. The function is efficient for large networks. The parameter is the number of results (All by default)"


BooNDistance::unvars="The variables of the two networks are different or in different orders, conflictuous variables `1` \[LongDash] Aborted.";
BooNDistance::usage="BooNDistanceMean[F1,F2] computes the distance between two networks with the unsigned same interaction graphs.
Option \[LongDash] Method:
\[FilledSmallSquare] Automatic, Mean: Mean matching dissimilarity distance of the output Boolean vectors of the Boolean tables of each formula.
\[FilledSmallSquare] All: Matching dissimilarity distance of two Boolean vectors formed by the assembly of the outputs of the Boolean tables of each formula."


b2o::nnarg="Syntax error formula not recognized aborted: `1`  ";
BooleanToODE::usage="BooleanToODE[F,v, \[Kappa],\[Gamma],\[Theta], var0, fstep] converts a Boolean network into ODE system. The structures are associations the keys of which are variables of the network.
PARAMETERS:
\[FilledSmallSquare] F : Boolean network.
\[FilledSmallSquare] v : variable of the system, default t.
\[FilledSmallSquare] \[Kappa] : Expression rate (Association var \[Rule] Real).
\[FilledSmallSquare] \[Gamma] : Decay rate (Association var \[Rule] Real).
\[FilledSmallSquare] \[Theta] : Threshold of expression (Association var \[Rule] Real).
\[FilledSmallSquare] var0: initial condition (Association). 
\[FilledSmallSquare] fstep: pair of step functions {function inhibition, function activation}
"


(* ::Subsection:: *)
(*Graphical Interface*)


(* ::Input::Initialization:: *)
WindowView::usage="WindowView[title,content, size] Show a list of process in a window. The parameters are: 
\[FilledSquare] title: title of the windows 
\[FilledSquare] content: list of treatment, 
\[FilledSquare] size: size  of the window (default Automatic)."


(* ::Input::Initialization:: *)
IBooned::usage=" IBooned[a , boon variable, extra, filename]. A graphical interface to generate BooNs. See the Help documentation for detail of the use. All the parameters can be omitted (i.e. IBooned[]). The global variable IBOONED$ keeps the internal structure of the interaction graph (see ?IBOONEDS$).
The parameters are:
\[FilledSquare] 'a':  is a string corresponding to the prefix of the symbol, and \"a\" is the default. 
\[FilledSquare] boon variable: is the variable storing the BooN in order to connect the interface to other programs. 
\[FilledSquare] extra: a list of add-on buttons for the right hand side button bar. 
\[FilledSquare] filename:  is a string containing the name of the IG database (default: BoonedIGSamples.nb).
";


(* ::Input::Initialization:: *)
IBOONED$::usage="global variable used in IBooned containig {nodes coordinates, operators, names, arcs} dynamically updated.";


(* ::Subsection:: *)
(*Conversion Multivalued to Boolean network*)


(* ::Subsubsection:: *)
(*Integer Coding*)


SupportSeparator::usage = "Separator of the support which is \[LetterSpace] by Default. A Boolean variable of the Boolean support is of the form x\[LetterSpace]n where is the supported multivalued variable."


VanHam::usage="VanHam[n] gives the Van Ham Code for integers from 0 to \!\(\*
StyleBox[\"n\",\nFontSlant->\"Italic\"]\)\!\(\*
StyleBox[\".\",\nFontSlant->\"Italic\"]\)\!\(\*
StyleBox[\" \",\nFontSlant->\"Italic\"]\)The result is an association i \[Rule] code of i. A code is a list of Boolean list, where each Boolean list represents on possible coding of an integer 0 \[LessEqual] i \[LessEqual]n."


SummingCode::usage="SummingCode[n] gives the Summing Code for integers from 0 to \!\(\*
StyleBox[\"n\",\nFontSlant->\"Italic\"]\)\!\(\*
StyleBox[\".\",\nFontSlant->\"Italic\"]\)\!\(\*
StyleBox[\" \",\nFontSlant->\"Italic\"]\)The result is an association i \[Rule] code of i. A code is a list of Boolean list, where each Boolean list represents on possible coding of an integer 0 \[LessEqual] i \[LessEqual]n."


GrayCode::usage=" GrayCode[n] gives the Gray Code for integers from 0 to \!\(\*
StyleBox[\"n\",\nFontSlant->\"Italic\"]\)\!\(\*
StyleBox[\".\",\nFontSlant->\"Italic\"]\)\!\(\*
StyleBox[\" \",\nFontSlant->\"Italic\"]\)The result is an association i \[Rule] code of i. A code is a list of Boolean list, where each Boolean list represents on possible coding of an integer 0 \[LessEqual] i \[LessEqual]n.."


IntSumming::usage="IntSumming[boolean state] computes the integer state from the boolean state according to the Summing Code. This state is either a Boolean list or a state following the protocol of the Booleanization." 


IntGray::usage="IntGray[boolean state] computes the integer state from the boolean state according to the Gray Code. This state is either a Boolean list or  a state following the protocol of the Booleanization."


(* ::Subsubsection:: *)
(*Conversion*)


MaxLevels::usage="MaxLevels[p] extract the maximal reachable levels of the variables from a transition form equation. The parameter p can be either:
\[FilledSmallSquare] an equation of the form: v \[Rule] Piecewise function
\[FilledSmallSquare] a system of equations: list of equations."


GetMode::usage="GetMode[\!\(\*
StyleBox[\"f\",\nFontSlant->\"Italic\"]\)\!\(\*
StyleBox[\",\",\nFontSlant->\"Italic\"]\)\!\(\*
StyleBox[\"encoding\",\nFontSlant->\"Italic\"]\)\!\(\*
StyleBox[\",\",\nFontSlant->\"Italic\"]\)\!\(\*
StyleBox[\"size\",\nFontSlant->\"Italic\"]\)] defines a mode for each Boolean variable support. The result is an association: <| var \[Rule] mode description ...|>.
PARAMETER
\[FilledSmallSquare] f: multivalued network;
\[FilledSmallSquare] encoding: Boolean coding rule of the variables
\[FilledSmallSquare] size: number of joined updated variables per modality."


MultiValuedToBoon::usage="MultiValuedToBoon[\!\(\*
StyleBox[\"g\",\nFontSlant->\"Italic\"]\)\!\(\*
StyleBox[\",\",\nFontSlant->\"Italic\"]\)\!\(\*
StyleBox[\"coding\",\nFontSlant->\"Italic\"]\)\!\(\*
StyleBox[\",\",\nFontSlant->\"Italic\"]\)\!\(\*
StyleBox[\"booleanmode\",\nFontSlant->\"Italic\"]\)\!\(\*
StyleBox[\",\",\nFontSlant->\"Italic\"]\)\!\(\*
StyleBox[\"logicalform\",\nFontSlant->\"Italic\"]\)] converts a Multi-valued network into a Boolean network.
PARAMETERS
\[FilledSmallSquare] g: multi-valued network.
\[FilledSmallSquare] coding: name of the function used to encode integer into Boolean (VanHam, SummingCode, GrayCode)
\[FilledSmallSquare] booleanmode: association keeping the Boolean mode used to implement the conversion for each variable (optional, default: Sequential for all variables). 
\[FilledSmallSquare] logicalform: parameter determining the form of the resulting Boolean expressions (optional, default: \"CNF\")."


VertexFontSize::usage="Option of TikzNetwork. Node Label Font Size: Tiny, Script, FootNote, Small, Medium, Large";
EdgeFontSize::usage="Option of TikzNetwork. Edge Label Font Size: Tiny, Script, FootNote, Small, Medium, Large";
VertexLabelFunction::usage="Option of TikzNetwork. Function defining a label from the vertex ID";
EdgeLabelFunction::usage="Option of TikzNetwork. Function defining a label from EdgeWeight.";
ScaleDistance::usage="Option of TikzNetwork. Scaling distance";
MathMode::usage="Option of TikzNetwork. Switch to mathematical mode for vertex label(Boolean)";

FootNote::usage="Option of TikzNetwork. Footnote size"
Script::usage="Option of TikzNetwork. Script size"

TikzNetwork::usage="TikzNetwork[G] generates a LateX code of graph G using Tikz Network package (\\usepackage{tikz-network}). The options are:
\[FilledSquare] Scale: the tikz picture scale (Default 1).
\[FilledSquare] VertexShape: Shape of the vertices which is either: Automatic, classical shapes e.g. Circle, None (Default Automatic), if the option is Automatic then the shape is interpreted from VertexShapeFunction;
\[FilledSquare] VertexFontSize: Font size of the vertex label which is either: Tiny, Script, FootNote, Small, Medium, Large (Default Medium);
\[FilledSquare] EdgeFontSize: Font size of the edge label which is either: Tiny, Script, FootNote, Small, Medium, Large (Default Large);
\[FilledSquare] ScaleDistance: Scale distance (Default 3);
\[FilledSquare] MathMode: Set the vertex and edge label in Math Mode - Boolean value (Default False);
\[FilledSquare] VertexLabelFunction: Function defining a label from the vertex ID (Default Identity);
\[FilledSquare] Function defining a label from EdgeWeight (Default translate  $Failed and Automatic to {} otherwise the EdgeWeight value).
"


(* ::Subsection:: *)
(*Random Graph Generation*)


Monotone::usage="Parameter of RandomBooleanNetwork function."


RandomBooleanNetwork::usage="RandomBooleanNetwork[\!\(\*
StyleBox[\"number\",\nFontSlant->\"Italic\"]\)\!\(\*
StyleBox[\" \",\nFontSlant->\"Italic\"]\)\!\(\*
StyleBox[\"of\",\nFontSlant->\"Italic\"]\)\!\(\*
StyleBox[\" \",\nFontSlant->\"Italic\"]\)\!\(\*
StyleBox[\"agents\",\nFontSlant->\"Italic\"]\)\!\(\*
StyleBox[\",\",\nFontSlant->\"Italic\"]\)\!\(\*
StyleBox[\" \",\nFontSlant->\"Italic\"]\)\!\(\*
StyleBox[\"dist\",\nFontSlant->\"Italic\"]\)\!\(\*
StyleBox[\".\",\nFontSlant->\"Italic\"]\)\!\(\*
StyleBox[\" \",\nFontSlant->\"Italic\"]\)\!\(\*
StyleBox[\"parameter\",\nFontSlant->\"Italic\"]\)\!\(\*
StyleBox[\",\",\nFontSlant->\"Italic\"]\)\!\(\*
StyleBox[\"  \",\nFontSlant->\"Italic\"]\)\!\(\*
StyleBox[\"prob\",\nFontSlant->\"Italic\"]\)\!\(\*
StyleBox[\" \",\nFontSlant->\"Italic\"]\)\!\(\*
StyleBox[\"of\",\nFontSlant->\"Italic\"]\)\!\(\*
StyleBox[\" \",\nFontSlant->\"Italic\"]\)\!\(\*
StyleBox[\"self\",\nFontSlant->\"Italic\"]\)\!\(\*
StyleBox[\",\",\nFontSlant->\"Italic\"]\)\!\(\*
StyleBox[\" \",\nFontSlant->\"Italic\"]\)\!\(\*
StyleBox[\"prob\",\nFontSlant->\"Italic\"]\)\!\(\*
StyleBox[\".\",\nFontSlant->\"Italic\"]\)\!\(\*
StyleBox[\" \",\nFontSlant->\"Italic\"]\)\!\(\*
StyleBox[\"pos\",\nFontSlant->\"Italic\"]\)\!\(\*
StyleBox[\",\",\nFontSlant->\"Italic\"]\)\!\(\*
StyleBox[\" \",\nFontSlant->\"Italic\"]\)\!\(\*
StyleBox[\"prefix\",\nFontSlant->\"Italic\"]\)] generate a random Boolean network. 
The parameters are:
\[FilledSquare] number of agents.
\[FilledSquare] list of parameters for the  chosen distribution governing random graph generation (see help in random graph distribution)
\[FilledSquare] probability of self loop (Default 0.)
\[FilledSquare] probability of generating a positive regulation (default 0.5)
\[FilledSquare] String defining the prefix name of the node. The name of the node/variable is <prefix><integer> (Default \"$x\")
The options are:
\[FilledSquare] Method: distribution method to generate the random graph (see help for graph distribution). The distribution function must have two parameters: number of agent and a parameter depending on the distribution policy (default distribution BarabasiAlbertGraphDistribution). 
\[FilledSquare] Monotone (Boolean): the option determines whether the generated Boolean functions are necessary monotone (True) or not (False) (Default True).
"


(* ::Section::Initialization:: *)
(*Private Section*)


(* ::Input::Initialization:: *)
 Begin["`Private`"]


(* ::Section:: *)
(*Miscalleneous functions on graph*)


(* ::Text:: *)
(*Default color Data *)


(* ::Input::Initialization:: *)
BoonedColorData = 113;


(* ::Input::Initialization:: *)
BoonType={ (_Symbol -> _) ...};


MultiValuedType={(_Symbol->( _Piecewise|_Integer))...};


BoolStateType={(_Symbol-> (True|False))...};


(* ::Subsection:: *)
(*Basic functions*)


(* ::Input::Initialization:: *)
ReflexiveReduce[graph_Graph]:=GraphDifference[graph,Graph[Function[vertex, vertex \[DirectedEdge] vertex]/@VertexList[graph]]]


(* ::Input::Initialization:: *)
QuotientGraph[ graph_Graph,partition_List]:=ReflexiveReduce@AdjacencyGraph[partition,Outer[Function[{p1,p2},Boole@MemberQ[Outer[Function[{s1,s2},EdgeQ[graph,s1 \[DirectedEdge] s2]],p1,p2,1],True,Infinity]],partition,partition,1], DirectedEdges->True]


Options[ShowQuotient]={ImageSize-> Automatic};
ShowQuotient[g_Graph, OptionsPattern[]]:=With[{qg=QuotientGraph[g,SccOrganisation[g]]},
SetProperty[qg,{
 EdgeShapeFunction->GraphElementData[{"FilledArrow","ArrowSize"->Medium}],
EdgeStyle->GrayLevel[0.2],
VertexLabels->Null,
VertexShapeFunction->Function[{coord,arcs,size},
With[{thearcs=TableForm[Partition[arcs,UpTo[1+Round[Length[arcs]/10]]]],color=Which[
VertexOutDegree[qg,arcs]===0,LightRed,
VertexInDegree[qg,arcs]===0,RGBColor[0.96, 0.96, 0.96],
True,LightYellow]},
{Black ,Inset[Framed[thearcs,Background-> color],coord,Center]}]]
,GraphLayout->"LayeredDigraphEmbedding" (* this layout causes error sometimes *)
,ImageSize-> OptionValue[ImageSize]
}]]


(* ::Input::Initialization:: *)
BoonCompose[F:BoonType,n_Integer]:=  FixedPoint[Function[boon,Function[ eq, Keys[eq]->BooleanMinimize[Values[eq]/.F]]/@boon],Thread[Keys[F]-> Keys[F]],n]
BoonCompose[F1:BoonType,F2:BoonType]:= Function[ r, First[r]-> BooleanConvert[(Last[r]/.F2),"DNF"]]/@F1


Options[BooNDistance]={Method-> Automatic};
BooNDistance[F1:BoonType,F2:BoonType, OptionsPattern[]]:= If[Keys[F1]=!= Keys[F2],Message[BooNDistance::unvars, Complement[Keys[F1],Keys[F2]] \[Union] Complement[Keys[F2],Keys[F1]]]; Abort[],
Switch[OptionValue[Method]
,Automatic|Mean,Mean@MapThread[Function[{f1,f2},MatchingDissimilarity[BooleanTable[f1],BooleanTable[f2]]],{Values[F1],Values[F2]}]
,All, MatchingDissimilarity[Flatten[BooleanTable/@Values[F1]],Flatten[BooleanTable/@Values[F2]]]]]


(* ::Subsection:: *)
(*Views*)


(* ::Input::Initialization:: *)
Options[StateToString]={Full-> False};
StateToString[state:{(_-> (False|True))..},OptionsPattern[]]:= With[{basis=2},
With[{str= IntegerString[FromDigits[Boole@Values[state],basis ],basis,Length[state]]},
If[OptionValue[Full],Tooltip[str,state],str]]]
StateToString[state:{(_-> _Integer)..},OptionsPattern[]]:= With[{basis=10},
With[{str= IntegerString[FromDigits[Values[state],basis ],basis,Length[state]]},
If[OptionValue[Full],Tooltip[str,state],str]]]


(* ::Input::Initialization:: *)
StateToInteger[s:{(_-> (False|True))..}]:=  FromDigits[Boole@Values[s],2]
StateToInteger[s:{(_-> _Integer)..}]:= FromDigits[Values[s],10]


(* ::Input::Initialization:: *)
Options[AttractorToTable]={ColorRules->{False-> Darker[Red,0.4],True-> Darker[Green,0.6],_->Black}, Observers-> All};
AttractorToTable[attractors_,OptionsPattern[]]:= With[{vars=If[OptionValue[Observers]===All,  Keys@First[attractors],OptionValue[Observers]]},
Grid[
Join[{vars}, 
Function[eq,
vars/.eq/.{False->Graphics3D[{Specularity[Yellow,20],(False/.OptionValue[ColorRules]),Sphere[]},ImageSize->30,Boxed-> False,Background->None],
True-> Graphics3D[{Specularity[Yellow,20],(True/.OptionValue[ColorRules]),Sphere[]},ImageSize->30,Boxed-> False,Background->None]}]
/@attractors
](*end join*)
,Alignment->{Left,Center},ItemStyle->Directive[Black,FontFamily->"Helvetica",FontSize->11,Bold]
,Spacings->{1,0.5}
,Frame->{All,1->True}
,FrameStyle->Directive[Thick,GrayLevel[0.5]]
,Background->{None,1->LightYellow}
]]


(* ::Input::Initialization:: *)
WhichUpdated[ e1_ \[DirectedEdge] e2_ ]:= DeleteDuplicates[Complement[e1,e2]/.(v$_ -> _) -> v$] 
WhichOrderUpdated[edge:( e1_ \[DirectedEdge] e2_) ]:= With[{e= WhichUpdated[edge] }, Append[e,Switch [Order[e/. e1 ,e/.e2], -1, "-", 0,"=",1,"+",_,"?"]]]


(* ::Input::Initialization:: *)
Options[NiceModel]={EdgeLabels-> None, VertexLabels ->  Labeled,ImageSize->Automatic, GraphLayout-> Automatic};
NiceModel[stategraph_Graph, OptionsPattern[]]:= 
With[{newvertices = StateToInteger/@VertexList[stategraph], newedges = EdgeList[stategraph]/. v1$_ \[DirectedEdge] v2$_ :> StateToInteger[v1$] \[DirectedEdge] StateToInteger[v2$]},
Graph[newvertices, newedges
, EdgeLabels  -> Switch[OptionValue[EdgeLabels]
,None, {}
,Automatic,Function[e,(StateToInteger[First[e]] \[DirectedEdge]  StateToInteger[Last[e]])->   Placed[Row@WhichUpdated[e],{1/2,{0,0}}]]/@EdgeList[stategraph]
,_List, Function[e,(StateToInteger[First[e]] \[DirectedEdge]  StateToInteger[Last[e]])->   Placed[Row@(WhichUpdated[e] \[Intersection] OptionValue[EdgeLabels]),{1/2,{0,0}}]]/@EdgeList[stategraph]
, All, Function[e,StateToInteger[First[e]] \[DirectedEdge]  StateToInteger[Last[e]] ->   Placed[Row@WhichOrderUpdated[e],{1/2,{0,0}}]]/@EdgeList[stategraph]
,_, {}]
,EdgeWeight->Switch[OptionValue[EdgeLabels]
,None, {}
,Automatic,Function[e,(StateToInteger[First[e]] \[DirectedEdge]  StateToInteger[Last[e]])->   First@WhichUpdated[e]]/@EdgeList[stategraph]
,_List, Function[e,(StateToInteger[First[e]] \[DirectedEdge]  StateToInteger[Last[e]])->   First@(WhichUpdated[e] \[Intersection] OptionValue[EdgeLabels])]/@EdgeList[stategraph]
, All, Function[e,StateToInteger[First[e]] \[DirectedEdge]  StateToInteger[Last[e]] ->  First@ WhichOrderUpdated[e],{1/2,{0,0}}]/@EdgeList[stategraph]
,_, {}]
,EdgeStyle -> Black
,VertexStyle->LightGray
,VertexSize ->0.15
,VertexShapeFunction->"Circle"
,VertexLabelStyle-> Directive[Bold,"Times",11]
,EdgeLabelStyle -> Directive[Italic,"Times",11]
,VertexLabels->  
Switch[OptionValue[VertexLabels]
,Labeled,Function[state,StateToInteger[state]->Placed[StateToString[state, Full-> True],Automatic]]/@VertexList[stategraph]
,Integer, "Name"
,_,{}]
, GraphLayout->OptionValue[GraphLayout]
,ImagePadding -> 25
,ImageSize-> OptionValue[ImageSize]
]]
NiceBM=NiceModel


(* ::Input::Initialization:: *)
NiceEqs[{}]:= Graphics[{},ImageSize->Full]
NiceEqs[{Null}]:=Graphics[{},ImageSize->Full]
NiceEqs[eqs_]:= With[{vars =   Keys@First@First[eqs]},
With[ { l = Boole[vars/.eqs],size=Length[vars], len = Length/@eqs, eqcolor=Orange},
With[
{ geol=First@MinimalBy[#,Norm]&/@Map[ Function[{v},FromDigits[#,2]&/@
{v[[1;;Round[size/3]]], v[[Round[size/3]+1;; Round[2/3 size]]],v[[ Round[2/3 size]+1;;size]]}],l,{2}]},
BubbleChart3D[List/@
MapThread[Function[{xy,s, eq},
Tooltip[
Labeled[Append[xy,s],Style[s,14,"Helvetica"]] 
,Grid[Join[{vars}, vars/.eq/.{False->Graphics[{Opacity[0],EdgeForm[{Thin,Dotted,eqcolor}],Disk[]},ImageSize->32],True->Graphics[{eqcolor,Disk[]},ImageSize->32]}]
,Alignment->{Left,Center},ItemStyle->Directive[Black,FontFamily->"Helvetica",FontSize->14,Bold],Spacings->{1,0.5},Frame->All,FrameStyle->Directive[Thick,Orange]]]

],{geol,len, eqs},1]
,ChartStyle->BoonedColorData 
,Axes-> False
,Ticks->None
,FaceGrids-> None
,Boxed->False
,ImageSize->Full
]]]]


(* ::Input::Initialization:: *)
Options[NiceStableStates]={ColorRules->{False-> Darker[Red,0.4],True-> Darker[Green,0.6],_->Black}, Background-> LightYellow};
NiceStableStates[f_,sizey_:Automatic,funstable_:("\[FilledSquare]"&),label_:"\[FilledSquare]", OptionsPattern[]]:= With[{stablestates=StableStates[f], agents=  Keys[f]},
Pane[
If[stablestates!= {},
If[Length[stablestates]<200,
Grid[Join[{ Prepend[Range@Length[stablestates]," "]},
MapIndexed[ (Prepend[#1,agents[[First[#2]]]]&),
Transpose[Function[eq,
agents/.First[eq]/.{False->Graphics3D[{Specularity[Yellow,20],(False/.OptionValue[ColorRules]),Sphere[]},ImageSize->30,Boxed-> False,Background->None],
True-> Graphics3D[{Specularity[Yellow,20],(True/.OptionValue[ColorRules]),Sphere[]},ImageSize->30,Boxed-> False,Background->None]}]
/@stablestates]]
,{Prepend[(funstable@First[#]&)/@stablestates, label]}
]
,Background->{{1-> OptionValue[Background]},{1->  OptionValue[Background]}}
, Frame->{All,{1->True,-1-> True}}
,Spacings->{1,0.5}
,Alignment->Center
,FrameStyle->Directive[Thick,GrayLevel[0.5]]
,ItemStyle->Directive[Black,FontFamily->"Helvetica",FontSize->12,Bold]
],
Framed[Style["Cannot represent the "<>ToString[Length[stablestates]]<>" stable states.",Black,FontFamily->"Helvetica",FontSize->12,Bold],Background->LightYellow]]
,
Framed[Style["NO STABLE STATES",Black,FontFamily->"Helvetica",FontSize->12,Bold],Background->LightYellow]]
,ImageSize->{Automatic,sizey}, ImageSizeAction->"ShrinkToFit"]]


(* ::Subsubsection:: *)
(*Graphical interface for formula generation from interaction graph*)


(* ::Text:: *)
(*Icons are found in inconsdb http://www.iconsdb.com/*)


(* ::Input::Initialization:: *)
GenForm[a_String,arrows_,operators_, names_,maxfamily_]:= With[{convertrules= {Or-> And,And-> Or},opsign= {1 -> Identity,-1 -> Not},
nb=Length[operators]},
Table[  Symbol@names[[jvar]]-> 
 (operators[[jvar]]/.convertrules)@@DeleteCases[Table[ 
operators[[jvar]]@@Cases[arrows,{ivar$_,jvar,sign$_,ifamily}:>  sign$ [Symbol@names[[ivar$]]],1]
,{ifamily,0,maxfamily-1}],operators[[jvar]][]]
,{jvar,nb}]/.opsign];
GenForm::usage="generate a formula from the interaction graph specification."


(* ::Input::Initialization:: *)
BOONEDSAMPLES$ ="BoonedIGSamples.nb"


(* ::Input::Initialization:: *)
ClosestMouse[ l_List, dist_]:= If[l==={},0,With[{pos=MousePosition["Graphics"]},With[{v=Function[coord,Norm[(coord-pos)]]/@l},If[Min[v] > dist,0,First@First@Position[v,Min[v]]]]]]
ClosesMouse::usage= "Give the position of the closest element whose distance is below dist, otherwise 0." 


(* ::Input::Initialization:: *)
LogoTxt::usage="Convert an image into string and can be treated as a string."
LogoTxt[image_Image,size_:24]:="\!\(\*"<>ToString[ToBoxes@Deploy@ImageResize[image,size],InputForm]<>"\)"


(* ::Input::Initialization:: *)
ScrollSelector[ labels_,action_, actionbutton_, label0_:"",overcolor_:Gray,color_:LightGray,sizey_:150, sizex_:100]:= 
With[{height=15},
DynamicModule[{field=label0},
Column[{
Pane[Grid[ 
Function[label,
{Button[Mouseover[Panel[ Pane[Style[label],Alignment->Center,ImageSizeAction->"ShrinkToFit",  FrameMargins->Tiny,ImageMargins->0 , ImageSize-> {sizex,height}]
, Background->color,  FrameMargins-> 0,  ImageMargins->0 ](*panel*)
,Panel[ Pane[Style[label,Bold,color],ImageSizeAction->"ShrinkToFit",Alignment->Center, FrameMargins->Tiny,ImageMargins->0 , ImageSize-> {sizex,height}], Background->overcolor, FrameMargins-> 0,  ImageMargins->0 ](*panel*)
](* mouseover *)
,(field=label;action[field])
, Method-> "Queued",Appearance->"Palette", Background->White, FrameMargins->0]}
]/@labels,Spacings->{0,0.1}]
,ImageSize->{sizex+18,sizey}, Scrollbars-> {False,True}],
Grid[{{InputField[Dynamic[field],String,Alignment->Left, FrameMargins->Tiny,ImageMargins->0 , ImageSize-> {sizex,height+5}], Button[ Graphics[{overcolor,Polygon[{{1,0},{0,-Sqrt[3]},{-1,0}}]},ImageSize->{10,10}], actionbutton[field], Method->"Queued"]}}, Spacings->0, Alignment->Top]
}, Spacings->0.1, Alignment->Left]
]]


(* ::Input::Initialization:: *)
Angle[{x1_,y1_},{x2_,y2_}]:= If[x2==x1,Sign[y2-y1]\[Pi]/2,ArcTan[ (y2-y1)/(x2-x1)]];
(*calcul du point othogonal au milieu d'un arc d'une distance D*)
MidPoint[{x1_,y1_},{x2_,y2_},factor_:1, D_:5]:=
With[{dist= If[x1^2-2 x1 x2+x2^2+y1^2-2 y1 y2+y2^2==0,D,(D (y1-y2))/Sqrt[x1^2-2 x1 x2+x2^2+y1^2-2 y1 y2+y2^2]]},{(factor dist)+(x1+x2)/2, (y1+y2)/2+ If[(y1-y2)==0,factor*Sign[x2-x1]*D,(factor dist)(x2-x1)/(y1-y2)]}]
TaggedArrow[{x1_,y1_}, {x2_,y2_},color_,diskr_, dist_,D_:10]:= 
With[ {\[Alpha]=Angle[{x1,y1},{x2,y2}], sign= If[Sign[(x1-x2)]==0,-1,Sign[x1-x2]]},
{Arrowheads[Medium],
If[{x1,y1}== {x2,y2},
{Mouseover[{Opacity[0],Disk[{x1,y1}+2{ x1 >= 0,y1 >= 0}/. {False-> -1,True ->1},1]},{Opacity[0.25],Disk[{x1,y1}+2{x1 >= 0,y1>= 0}/. {False-> -1,True ->1},1]}],
Translate[Arrow[BSplineCurve[5{{0,0},{x1 >= 0,0},{x1 >= 0,y1>= 0},{0,y1>= 0},{0,0}}/. {False-> -1,True ->1}],1],{x1,y1}]
,color,Translate[Disk[{x1>=0,y1>=0 }/. {False-> -3.75,True ->3.75} ,diskr],{x1,y1}]},
(* D\[EAcute]termination d'un point perpendiculaire \[AGrave] une distance fixe D = 10 - midcoord est la coordonn\[EAcute]e en consid\[EAcute]rant {x1,y1} est l'origine.*)
With[{middisk=Disk[MidPoint[{x1,y1},{x2,y2},0.5,D],3]}, 
 {Mouseover[{Opacity[0],middisk},{ Opacity[0.25],middisk}],
{ Arrow[BezierCurve[{{x1,y1},MidPoint[{x1,y1},{x2,y2},1,D],{x2,y2}}],1]}
,color,Translate[Disk[{0,0},diskr],{x2+sign Cos[\[Alpha]]dist,y2+sign Sin[\[Alpha]]dist}]
}]]}]


(* ::Input::Initialization:: *)
WindowView[title_,content_, imagesize_:Automatic]:= CreateWindow[DocumentNotebook[Map[ ExpressionCell,content]],ShowCellBracket->False, WindowSize->imagesize, WindowFloating->True, Saveable->False, WindowTitle->title, Selectable->True, Editable->False,Deletable->False, WindowElements->{"MagnificationPopUp","StatusArea","VerticalScrollBar"}]


(* ::Input::Initialization:: *)
SetAttributes[IBooned,HoldRest]
IBooned[a_String:"a", fvar_Symbol:FDUMMYVAR$, extra_:{}, filename_String:"BoonedIGSamples.nb"]:=
(** param\[EGrave]tres de l'application - fixe *)
With[ {maxrange =40, iconsize=32, delay=0.5, maxdo=5
(* param\[EGrave]tres des couleurs *) 
,signcolor={1 -> Darker[Green,.5],-1 -> Darker[Red,.3] }, opcolor= {And-> Black,Or-> Gray},guicolor =RGBColor[4/5,1/5,0],familycolor=Join[{ 0 -> Opacity[0]} , Table[ i -> ColorData[85][i],{i,10}]]
,helpicon= Image[CompressedData["
1:eJztmzFoU0EYx0MtJYhIhiKlQ4mbk4h0kNLh6SC4lahFOtliLEqI0hbFIoJ0
khKcSggiIk4OTiVIcChODlKCiIMUyYE4ODiIlCBS9Pt4V3hc7i6X9767e/J6
8Cs0fb3v/793ubvv3r3jC7dK14dyudxyHn6U5u+eXVqav3exAL9cri7fWKyW
r12orpQXy0tnFg7BhwFnOHdQDoqfwoKRPFDg5H3rsVXA2xgwC9SAFrAD7AJ/
BXb531r8WvyfMd/64xTQPQGsAtvAnsSrKXu8DqxrwrevfgU0BsBmQs+6tsC6
A98+xQKaJoEtC55VYKzJFPg+CtQt3W+T/tBADZ68TwEdD75FUMO0Y+8V4E8K
vO+DWioOfA8Bj1PgVwVqG7LovZECj/1o2GiDlN/3nn5A7L2SAk+DQjIesHCc
px7rsL6PQBN4xcI173vgJ3GMqYTecX7vEGrCtewcU8zZLBxjcC1VI2qLjiqW
of864b3A75DxuATXjvK+kTR2PaZ3vA9U67o5Sf3ngUcsHFevMkkODJ8hSecc
9DDwWpnRredfSuq+LbnuHdCzJQWfjQAfEmrYGtB7QOQdOSep/7Pi2ksKPSUC
HcEA/jcJ/Y9L6v+huLam0IN7RbI9k0FoGnrHvQvKfO6UJMY3xbXPNbq2E+pA
T0UD/6uE3pG6UP9JTfs+0+h6Q6Bl1cB/0naW8QS4Aqwxdd9X9n+u6y2BjnYf
72Oae+OCmxptX4hi9IxHkRizHr0jpx3cl1mN/5pH7x1ApUu2XoiL7jvW8uj/
jkIT5iCq+SIOLY3/HU/evwJHJHqQF8SxdjT+k64x4lJS6HlgIVZXESvvybss
P0DWLMaU5VoFD95xLTAq6BgGnlqOW0iJ/4qgAcc6inVeHP+u+/8v4HAkPs7x
SfNcU6TP25nb8a8ZiYs5vo11twzp+Md1uJz/NiJxKfJ7U3Tzn8v1Ty0St+ow
rm7943L922Xh+I+4/N7p1r++8x8X6PIf3/mvC5T5L28DV+OwD7T7H9w/9f6X
DOxjr4GHwDpzN++b7H9R73+K4Hg3LcTE51625wCj/U+uh3L/W2RGE3fDYlyj
/W+ug/L5RxTM83VxT1j0H5j651q2LGjQPodiYe5nw/tAz7+4Fsrnn/t86hNz
3IL3WM8/uR4b5316ngdF4q1YiNeI453roT7/gOC5j2OSWHjOhHodjNoTnY+E
/59m9OdfvgP3WXgGYIb3s9/EMVAzyblIluHzT5E2yOz5N+4/0+cfI22Q5n5g
7fyr0A6ZPP8stEFmz79H2iCz7z8I7ZDJ91/EwsK8sWmpP+zxugPfPvsV0Fhk
4T5Sm8B3m9dV9O0rTmFhTie+/9iV+Oyy3vcftXuV/3NhGXn/9aCku/wDFmco
Zw==
"], "Byte", ColorSpace -> "RGB", Interleaving -> True], trashicon=Image[CompressedData["
1:eJztmzFqAkEUhpdEJIXIFiJWQhoPYCGpxDRCgpUhjZ0SI2kMqCTkCBYWOUAQ
j+AZxEJSWqUzhUgIksJKUiRvcAWRtzqrM+4k/A8+QXkz/N/gLrMDe1q6z98e
WZZVP6GPfPHxvFYrPl3Z9OW6Wr+rVMs3F9VGuVKunZWO6ceMQ8DSV6NM0CYa
xCsxJ348MnfGijlsjVGVF+VNEe87OLsh5kr57SVTlDNOfCp0XyLmjPvtt60o
Y0eD+5KO336bivKFdrzWvdwTQn57uhVlS7tkvnTuh0FJbGcMt5Zpvz3dirIV
mLyDPeYbMPMVVGaWyJAknokXCfpM3rHkWI4xM19fcqzInFTgrvN61s3c6xpQ
f4BIOLQNcNiX9orP1i0f9UQMyKyLCPzhD/+N/mLv0f+n/KnnSJQZNVo80/r9
3/WKsmfl0WLv4Pe9yysJ+MMf/vCH/8H8xTn1+jlEj+kbMn1Dpq/H9Mmeq/vh
32XGlpi+JtPXZPpKTF8X/vCHP/zhD3/4wx/+8Ic//OEPf/jDH/7whz/84Q9/
+MMf/vCHP/wP4D8j3taYMH1Tpm/K9E2YvpnB/iYBf3X+UQN8vBJV6C/g3kUx
FZFVlf5yDVoGeMnSUiq/8I8RXwa4bUNkjKn2d9YgR3wb4OiGyJbT4b6yBlni
wwDXdUSmrE73lTUIEw+jxfuJsvsRHcycDCJLeBeXX7DqBFE=
"], "Byte", ColorSpace -> "RGB", Interleaving -> True], neticon =Image[CompressedData["
1:eJztW11oXEUUDjGUIBKCBAl5CLUUKUVKkSJ9kLCKDxqkhFgX6UOxIWlrCSts
Q6whFEREgoiUUkIQCVJKkBJEpJQ8lBJKKVLEBylSRHpERIpICSVIkaLnc2Zx
9uydv3vn2k3jwhfI7sz5znfvnZlzzsx9cuyt0cOdHR0dx7v5z+iht5+v1w+9
82ov//Na7fibR2oT4y/XpiaOTNT3jj3CX1Y0ujr+/5T5ocoWoPMB+9DF6GcM
Mvrg03/A+QxjibHG+Itxj/ELY4GxtXQHlA99mu+u9qEB+FHHdSmJ9yjjT8Fp
Yp0xUga34cN2xk8OH4BLjO7EvE95tDeA52GOMVsSfNobOJlY/1Qgb7vgemL9
822gKQZXE2p/kVrnGht+Yxxk7M/ASAT2MV7JwJeBfkwl0g4//gjkvMF4OgWv
xResdd8G+HGeUXgxZBtVUvNZw+5txjDjsuD7mdTaUNoCTGr+/dHgXMu4FhcY
Q1QwDiAV27xBzfM9uLfr35cE7wdJRNr92aOvvTnG9mgfTT+OJuACJhn3Dbu4
zv1GG6l/tiivw58X6N9Yq/Gs7dS/VVPq19qnhc0rjF7RTuqfKcLr8Kcq5h48
g9uM3/en0q+1vyfsXWQ8mtFW6j+Rl9fhyzHxDH7HGBDtRlLo536djI+Frc9t
81mG/uk8vBbbwLvC/nVGX0bbwvq19gVhB/9bc4iy9JPK52SctcrosbQvpF/z
nRM2PiRPXluGfrbRTWrd9o4/o09u/ZrvC6MvxtoMBaydqfVjfiWVs5k2l8mT
w+XVj2vKWBHaJyP8TaafVEz3jbC36Bp/Rt9o/fparxp9EOMcjPQ5iX5SufwP
wtYZ3/gz+gfp5++3kcrJcZ3XhfbRHH7n0s/tHiOVS42TyuV/FXbmQrVre079
pNaSGrnzl+g8KVY/qTUGc8uaw4+5kLknUv/rDj5z7A+VrH8mwI/lEvSvBvAC
yFvnIyDH7DVHW8QS9zz8DexOrP/7QN52wbHE+uVz2u44kFj/QMAzgLrWAcZe
UnPzsLY7Siq/qmbgqrBxitS+QAPPGniOVO7i046cvtemNY9+3QZrDvIJudZg
TC5Sjj2LjOfKN/89Qe661e+MSg4/guMffR3MtvOxfIat6PWfVMyJtfiO6Is8
s9/X32IzRv8W0fZ0Hk5tK3f8R62xblTsKWxtRP1fb3L91za5frl2bDb9Vx5C
/agZtdTnLH03rH5SNSPEEll5HHLpj8hfO0uin/vtpNaaEcbWLkt7qf9MJF9X
Bl8WnDUYat07i9ZPKgZdt/DjPqC24NMfFf+Q2tP1aQcQ3+wgFfNlQc5/k462
WcAecEg+eUL4X1T/2UD97YKbm1z/rcT6K4G8qLVhH23aQN2ArJ0sid8lprQN
1JDeJ3XGK8SPlcT6gVMeTuRxL3nsXBZ9YmvPu0nlyi4/cI0HE+vP2isC7ms+
1C8HAuwU1Y/6wm2Lbjx7qLk9ntEvt35S6/6y0Ix5G/WVHoqoWxbRT61nAVBX
wXqAGssusuwT6r5S/yeBnMjbLxj9ovdLhL1c+knVosw6PvLIoJhT94/WT6pm
YsY84I/eLxE2o/Vzm8PUfBbnkuteW2xE6Se1T2bGKoi3nHNboB/B+knNubPU
fA7iK3LsCTtsSf2fOtrifLFZp0FMF7VH4rAdpJ/UnpFcbzD/5jrcpcexaWvR
0m6Amuu1/5y1ysNpse/Vr++VXGuwj5L7vH2Ifv5uK+Om0QaxRtLzjD79es65
KNpE7YtaeKX+s+J35Czm2epbpM/7pfy49OtxJ+tjQWcyAnhl/fuc8RtiKjOm
wDMw6LJXwI9M/aTe4bhhfI85r5ZCu7bfK3jP6++HqLkmj7Gfqx4f6EeLflK1
DPPZw1o3lkq75u0XvIhpUD8y6wiY84Njihw+ZO1JL1BzPI/cvpqYF3P6acF7
l5pjCoy7qP23SB9wj1eEDxKIr/Yl5h0n/9l93PeoeCrSh5D3B3AvhhPzVqg5
drIB976nJODZs+VrJuDnjsT6PwvgNfnLQqgPSc9RU3POuhGwkFj/eBtoikHw
GcxA/cghsmo2EidJnUUsA3hvJeSdJdSQks/B+hogxpBnUDDfIr9F/SQ1rfQB
tTPEsfLsA4CaIWKA0mIu7UMjBsQ9wXnQpO+HBvqAvA7v7WBdGtK+PNB3qB/m
z99Nr9jj
"], "Byte", ColorSpace -> "RGB", Interleaving -> True], plusminusicon =Image[CompressedData["
1:eJztmrFKw1AYRkMs4hj6AKUuPoM4SN0UOlUE6SA2mFaXCKkgPoFDH6kUh9IH
EIciXS6IY2cHEf0u9EKW2Cvk5lfvd+AU0kDynamBdDu+7vTDIAiGW/jo9G4P
sqx3dxzh4CQdXg3S5OIovUkGSbYbb+DL1spaQAghhBBCXKNam3W4U2Bdep9L
0HcO3+FngfrcmfROV6Dt6Zt246P0TlegbWHR/yy90xXsZz/72c/+/9eP3U24
v8ZXi/4Xi+s0pXvzYE8Xfli0laW+V1e624AtDxW2GyfS3QZsmQn0T6W7Dexn
P/u97p963j8S6B9JdxuwpQb78H6NS4uupcV1LvU9pbt/irJ7/l9I73QF+9nP
fvaz39v+uUX/XHqnK5Tdc+Kvea4rG7SF8BDGBepzofROQgghxBb8bjXgXkU2
pHvzYM+p8vv916TCdqPv779m0t0G9nvfPxboH0t3G7ClDd8qbNf3akt358Ge
SBX/r7lsI+leQgghhJC/yhebKEmu
"], "Byte", ColorSpace -> "RGB", Interleaving -> True], familyicon = Image[CompressedData["
1:eJztms9LVFEUxwcTGSJCxJWEWMv+AnE1LRNXE20FpUkTmeI5kLkL/wIZBhFx
IS7CRUi4cOUqRFy5CnERHBcS0ioiIiLqe7hv6CENzbv33HfPwD3wGdDNnM+Z
9+4998fd2efVp32lUmmpjI/qzMsHSTLz6tEg/nhcX3o2V689eVhv1OZqyfjs
DfyzktJfihEjRowYMfwGVQZGwBRogCZ4A/ZSdsE6WAZVMBY6X9eAQx+ogBb4
CH7n5BJsgUnQM1M1cr0FEkvnTnwCr8FwaL9OgdwGwAvwWdD7Ol/BKtc4tG82
kM84+ODR+zoX/F4o8OZ3fAX8LNA9C4+jA4Hcy+BtIO8s78FQwe630+8N7d6G
372RgtzLytzbnJHn+YHM+67hme/EEf8+Hv1XFDj+j01P7jzHhRrn81IVdufe
psj53ZUrEpwTyPR1oZ3ysibkzv28z57WFz/AqIB/osDFlqajO893kuu4ouH1
kvVaicz6PbSDK9MO/i0F+buy7+Dfy89+m29ksUYks18XOncpJiz8pxTkLcWi
hX9DQd5StCz8mwryliL3GEhmfz503lIcW/jvKchbitPon9t/V0HeUpxY+K8r
yFuKAwv/ZQV5S7Fh4V9VkLcUiYX/mIK8pajk9U9rcKkgd1d4H+impf+Wgvxd
ObRxT/0nFeTvyoKDfz+ZuwehHWz5To5nYmTuXYT2sGXbxT31HyazjxjaJS+/
wH1X/7QGqwp88rIj4Z768xnIhQKnbvkC7kj5pzXopblgXtI9U4Ne2BN6B3zo
t8+BNd79aHMOBr3I/63BEOk8C+de/Z5P90wN+GzgTIFz1l1krstRA+4LjhS4
nxf1u/+jBnwXbDOgO491Xt/3LuvAeyVXBXrz/D5PnsZ5myAzLq6RWW/78uae
doeEexvJQG6jZPoEyTUDr+O2qeAxziXI9MzTYJ/MGXReZ36ODsECKb73302Q
6ZsmwCKZOxVck2NwmnICDsAGmftGfO/Eas8qRowYMWLE6Cb+AKto+v0=
"], "Byte", ColorSpace -> "RGB", Interleaving -> True],delicon= Image[CompressedData["
1:eJztmTFLw1AQx0MUcfQruPgJHEqnOtpJKu42NBaXCGlBBXER534Av1wWZ3F0
kHoP8+ARQkhe7u7dg/vDv9AOufv9pnA9zR4Wd2mSJJtj+FgsHy/Kcvl8fQJf
borN/brIV5fFNl/n5SQ7gB9ndQ8TjUaj0Wg0Gs3QVLOjM+g2wNxb6Dn33MYO
hv0Tuoe+Mc5dQX+hX6EcNNj3XA4cdjvTOJhQz23s0MZO7qCF3fYbOqWa29ih
i53MQQc7m4Oe7OgOerCTOxjIjuZgADuZA0/20Q482EkcwLMKT3ZvByPYbXdY
/PU+L1wOENg/oCkmP5cDqewcDqSzUzqIhZ3CQWzsmA5iZUd0MKZB2QM7EMFu
w+xAFLsNkwOR7DbEDkSz2xA5iILdBtlBVOw2SA6iZDepxr/bmL6H5vAJErst
220dI8jsUTkgYo/CATG7aAdM7CIdMLOLchCIXYQDBHbzbsN2VxbIntbPisoB
JrvzzCgcULDH4oCSXboDDnapDuB5GRc7ooNXRP5p9f+fMgs7goMf6ByLf4SD
0bcLDwfo7M4uQxyg3W0GODDsVxgzO3bp4wD9ZtXDATm7s0uXA7J7XYcDNnZn
lzYH5LfKFgfs7M4urgO2O63jIBi7s4txsONid+Y+hWbXaDQajUajiTF/vRaX
cQ==
"], "Byte", ColorSpace -> "RGB", Interleaving -> True],resizeupicon = Image[CompressedData["
1:eJztm89LG0EUx4NKCCIhBw+lePGfCD3aY6FIsBZyChqaqpe0JIXqnyAeJPTc
Qw/Fg3+BiAcPIiLiqYdSAnP3ICKepNj3yEiXuLM7v97szLoPvoGEmffm893N
/prZ+fanpY8TpVKpX4GPpdWvr3u91a13NfjyvtvfWOt2PrzpfumsdXqv2pPw
4wLXVKmIIuKDLZTLoMqYyHYZzB1Tz1Q642iBhqCHGP0GvbTI/FjvAnQvqGmi
O9ARqCHjBbRZkchpxQPO/p2AWaQ93KdTxiTa7tY9gP7rDtmjHojGU1bMZeQB
9P2TAT+qIRhPRSOXlgfQZzYjdtSRRX4tD7B9hvx4TLTJr+wBtJ0A3WToQcUy
v44H33LGr+QBtKuBfuWMX9UDPA7ug/4Gxj8ANRNUl+GP1J4DLabkxOuFW0/4
myp8psFG/5Vzj7a/M34C9mD4idiD4Cdk956fmN1rfgfs3vIbsqucG73jN2TH
firPE7zit8CO/Zsh8huyn2J/nic4fkP2E1A1kisofpvsofHbZg+Jn4I9FH4q
9hD4Kdl5/reSuXCe6ck8HiU/G83tHVOx8xovmNxzpDNBf0r+TU32Yxn2SJ0f
EjmXXfJD22nQtSb7jGwdXgv/Y5cJOQcJfan4l12wR+rNgHbHPMe5tjZLmAMm
5N9xxT5WF+dYcJ5pVrI9Ff9P1+w64QF/Zux8nFT8276z83FS8Td8Z+fjpOLH
vFeCPIegaUou2aDi57k/C9ifXIdnFcT8eC468JUdg5Kf56+y0bU8CTvkrDOz
9Ugu7n+rVNudje5/tddkueCnDPb//l93TVZe+LU8yBm/sgc55FfyIKf80h7k
mF/KA0X+tPVPWWiQMuZEDxT5Q5XQg2fC/+iB6fPv0EW5/jMEFfwF/zi/6vsv
ISt2IoDJv/8UsoYJ1wAtD8ZHrZaIP+JBHveDYRp7zPHA9vuoWUn9RdginkX8
A/X6Wn8=
"], "Byte", ColorSpace -> "RGB", Interleaving -> True],resizedownicon=Image[CompressedData["
1:eJzt289LVFEUB/DBQmbhwkWIiMTUwlVICxchEbYzFy2MxFWkOFkRE4yRKP0D
ES1FXLRqFRGtWrRy1cpFSLQU7kYiokWESEjY9zBXkEnfnPvr3XPfvAtfnRln
DudzcHgw986F+cfT93oqlcpSFT+m55avN5tzK7f6ced2Y+nBYqO+cKPxpL5Y
b16ZP4MHJ3TOVspVruIuNdHbtf/isM8gX5Gh2L3kvbT9ADlEtpE+yzpVpL8t
Vd/9+lzob/aY/ShrhjVGkU/I37Y6lB3kfKj+XRb6unNKzwfcnvG8QeTnCTVE
zyDDfpQms87TDnZxM2DYKW+YtdaZfhEzYNopm8x6Jv6oMzCwUz4ya5r6WTPA
33uQa8h93ffFHO2UjYD+zBng8UvIl7bnU++vlMX11MJOmQnsP3EGuF9DfmS8
5j1iYr9rYd/lztnR/98McPst4zU3mb0tWNgpswbz5frJ+fmUvEP6kF5kn1Hr
dUD7c67d0D/JqDXMrJV5bXKwv1AG760A/pqrP0+7NH/edkn+GHYp/lh2CX7c
fhjLHtuP348s3N7sMf0S7BH9vyXYI/pF2BPyB7En4g9mT8Af1C7cH9wu2J+L
Xfcszb+nWp8RZYV6nvIxI4F+k3xQlnt9BfFTWPscBfZTRoX4z0XyN4T4KVmf
fYfKMwl+XW8tgp+115GTfwD5lqP9u3K4Bvj265pjuq/Q9j/IlK09lF/XHVKt
/b69QPYt5KqLPaT/WH3aExpBLnsKndUZcHXn5Ze+UvSr1v66lzMYifonladz
KAn7D33MIHG/8wwK4HeaQUH81jMokN9qBgXzG8/AwE/nyjeFZLtDr+wZGPhT
C2sGBfZTXna5f730l/7Sn+lfFdBnqKwy/HRm9ZeAXn2HTMOd/HoG46r13cHY
PfsKWcY59rY50HfBaoln0NRdru5Z/wCKPVtH
"], "Byte", ColorSpace -> "RGB", Interleaving -> True], gridicon=Image[CompressedData["
1:eJztm79Kw1AYR4MWcfQVhD6EdKqja8UHaDG2LhFSqfggeZAMfYLgI2R365Ah
U4YORW8hEZEP+tsi+U7hFFp6wj1JyB/Se714mT2dRVG0vgxvs/nbbZrO3++v
woeHZP28TOLHu+Q1XsbpzeI8fDltGQU+pxfjwEfgEPhywqFt7tr7Hk9feNvu
1n7Q9xj+G8d1UgnUhrsX3cZwG9HdG24tusr2riLhFX43MdxcdDeGuxHd3HAn
olvRTz/99NNPP/30G9Rt2ylWhluIbma4megWhrsSXeuaFQCg43h/mQtYx6Gd
6JaGW4ruznAL0bXunf/i/fxHv7Ys+umnn3766R9Sf9OO7xTWPWwpulvD3Yqu
de2Yia713AUAoMP78c/7+Y9+bVn0008//fTTP6R+788/AMAv3v//4v38R7+2
LPrpp59++ukfUr/3+W/e8LxOunnQfY+jL37PAfe0H/zMf/8GAAl/Ig==
"], "Byte", ColorSpace -> "RGB", Interleaving -> True],graygrid=Image[CompressedData["
1:eJztmz9Kw2AYh4M6OHoFwUNIJx1dKx6gxdi6REil0i2XyEEy9ATBI+QMHTJk
ytCh6FdIROSF/rZI3qfwFFr6hO9JQv6Qftfzt+nLWRRFq8vwNp193KfpbPN4
FT48JavXRRI/PyTv8SJOb+fn4cu7jotAlmU3gc/AIfDlhEPX3LcPPZ6h8Lbd
rf1g6DH8N47rpBZoDHcvuq3htqK7N9xGdJXtXUfCK/xuYriF6K4Ndy26heFO
RLemn3766aeffvrpN2i6tlMsDbcU3dxwc9EtDXcputY1KwBAz/H+shCwjkM7
0a0MtxLdneGWomvdO//F+/mPfm1Z9NNPP/300z+m/rYb3ymse9hKdLeGuxVd
69oxF13ruQsAQI/345/38x/92rLop59++umnf0z93p9/AIBfvP//xfv5j35t
WfTTTz/99NM/pn7v89+84Xmd9POghx7HUPyeA+5pP/iZ//4NvcxXvg==
"], "Byte", ColorSpace -> "RGB", Interleaving -> True],showsampleicon= Image[CompressedData["
1:eJztm01oE0EUx0OUEKQUKaUUKaIiRYqH4kFKCaWKiF5EqkIRLw1tqiJR0qK1
h4J4KD0UEfEgRcSzJxER6SGHIp48FBEREZ6IiIQiRYpIKfU9ZgLp9u3OZGc3
u2tm4N/Qzczs+83Hmzeb2f3560OFdCqVmsjin6GRW8dKpZHb53bjPxeKE1fG
i2Ojp4uTY+Njpb78Drw4KLUztTXBYCaLKqDKqF+ozQRqFbWEKqJaUpoJ8/ai
PsXA/iD1FZXTZF+Ngb1h6A9qwIM9+x/2u1PfUa0u/IUY2NcITbvwl2NgWyO0
7MKfVD9frzZQGYY/arsaqbYm52/X4F8HsR4kXX998lc4P5G0BPyabvm357P8
lt/yW37Lb/ktv4Ifvz+KOuMQF1cfZ/IFKc/nOiHyP2fK9GveP0i9sfyW3/I3
nP8a6rFDB5l8s0y+IDUVBX9SkuW3/JY/FP83hLrpUBeTb5TJF6QuRsTf7Ouf
5bf8zczf1P4vKcnyZw6g7qPWmpG/mpCnE7UA4vfvpuOvJuTqA+Y8mA//F/T+
dw61S5NhL4hnf3S2bQY1Jf0ssWX1W8OIP8j1b5mYNJjvoj4q6lqTtp1FOY82
xpG/DC5nsmR58l9PQZxHqDc2+IK6hErHlL/sNuap71DTIM7tGcdIqJ6Y8b8D
l3OpeL1L2mzK7ZwXowHym/7+0eFR7w8FC61hi3J8zNbZDg+B8Qv18oeRZFv9
Vtj/GtVdU6bfx1h4Bo4zcFHz4/1ysDVG4/QAHL7MJ3+1DdI19UTGT/2JWtHo
921+3ICfdC9qfhDnrt9rzPdul/Im/KThiPnnNGxc9Ch/xJCfzv3uiYIfxDrH
nU90asajDooTPhi2wSPm2koD+C9r2ue6bst6aG83DyImcUq1npBWYft7HzTn
OkPmH9Tkv2FwD1UsQaJYa4m5/gqYmCaohHWnXO7r1BOf9Xdotu9JEHtJ7juK
vz9DMGeRTzE29oA6xq+Aj30tlrmq27b42QLiPSkTP6IS9TVnZ16jrOfv3Eyd
xPNNUSetuy01ZXIafWGq8y72zivK0Trh+v6Wo640iPjOqz56F2ofU3ZAfhcW
P/kjbp9ENi8oypIvH+bGUE09bcDvTWv1E3XYo45WEHsrei6zEUIbvAQ+lk1r
jANSWbYDxS1ULgMiDqLnQxVFWZrjh3TGkbQpI9u0PWC5PpMB8S6eTly0WWf/
kP9h991xS7I/TeO6qtbl2NB+HhiHJMcezUOTd3JprvRGzWKS5Pyj59yq9ax2
TrxAnQAPX5m0BMI/0n73Dggfvyz9GcVnb0GsH3k/c/wfOtLeoA==
"], "Byte", ColorSpace -> "RGB", Interleaving -> True], addsampleicon=Image[CompressedData["
1:eJztmz1IHEEUgA8T5AoREQuRIARC6hQiEg4xYmHCEeRCOgs9/AuEi2i4JHKt
BLGwCCFVipSSQlJJqivEOohYSBBfCosgR7AIEoIk7zF7oLtvd2dvZ3Znkxn4
Allnd963N/dmdub2ZvlZaa4tl8st5/Gf0vSLe0tL068edeF/HleWn8xXZmfu
V57Pzs8uDZWv4cERh+u5qwVG2vPIHFJHfiB/MsgZsoNUkI6cZMG6d5BDA+JX
yTekIOl+ZkC8OjhHhgPc8//g5+7mBOn08Z8zIL4kWPHxrxsQWxLs+fhnNc9H
5QJpZ/zTjitJuv9z/x4J/98gxoOs86tF/1MuT2StAD+mW39vPetv/a2/9bf+
1t/6h/jj3weRhy64efUoU08lges6Gv0/MefclWxfJbvW3/pb/8T9nyLvXdxi
6r1m6qnkZRr+WSnW3/pbfy35r4RUXdxg6s0w9VRBe5ueMSch/7TGvz1kBcT8
2711zcU5gWyC2P/Lqj/tWWwhQ0iYsl+8XU6f+Z4x/y9hfTzifegEuf0fE/zX
uFh1lBb8dee/BxIxt4PIA5PIonPeAjKO9On0T6tgXG0gnvspH/wM6T8HSA3p
lbiu8f4Y0xiy38L3iHL/OgT8DshkfxC/TXkbI480OUIGfNow0h9Evq4rcG9C
35ki007U/Kf6+ZdbO8wrdm9Ce8KjMf1Vjn9bPm2o6PN+NJB+Q/yHmPPGJD3O
wbvnfyJ57mdw5pMp+u+Da04LYoyTzfOe9S8Q46NsPyim7F+LGX9c/50W/VXt
f3jmJiDmNkn5E7ej+usqIOa0YfM61f6LBvkPBsRJuW7XxTvmGgWm3teA6340
yH8yIM7DGNctB1yXy7Vp+XN9Ubc/N16m5V9Nwf/UIP+FFPyPmWMNlV4R4hwP
6aeh+/94rJep9ybgunXwvvdBa46h6wYa/PsC4tQ1/m2AeFfIfXwbmDlNAvfg
IGH/Ioi9BO5vNObS2Knr98kTTPy1BP0p99GcqwPEe1JR7psKNpn4e+HqfoVO
/9VL5xUitKsKaq+LcViXPJ/6ZtlFUK67DK0B9LjaHQb552dVVBl/6o9Hmtud
crfrtE1rbrTHRnttFwn4056U5700PDYA0Z6FovABJPbSQOSGbuonmmGDAZGb
uXc44rDt156JBcRaWEPh554Z92bBmPtBrNe16k33b0qmz5taKHbn+8DN1fyg
8X0VmD3vLBcQa1b0rExrF/T8fuK4HoOYz28490rqA/8LlJBUrw==
"], "Byte", ColorSpace -> "RGB", Interleaving -> True],delsampleicon=Image[CompressedData["
1:eJztm09IF0EUx39YyO8gIuJBJIREOncQkRAx8WAhIkY3Dyr+C+SXaFiJV4mQ
8CAdO3SUDtJJOv0OEh1DpEOE+CI8hEh4iIgQe6/ZX/zcfbMzu+7sztYMfAV3
Z3fe5/1m3ryd2b06cX9kuqZQKCwW8c/I+MObCwvjj+804D93S4v3ZkpTk7dK
D6Zmpha6Ji7hwV5PlwvnC/TWFlHTqDLqG+oshzpB7aBKqLqCZsG611EfLbA/
SX1GdWuyn1hgrwn9QPWEsBf/wd/dr0NUvYR/2gL70tCyhL9sgW1paFfCn9c4
H1WnqFqGP2u70lTjf87fpMH/C8R8kHf9jMl/xMWJvBXg53THH6zn+B2/43f8
jt/xO34FP57vRA35xOXVfUy9JBW6rmOQ/zVzzQ3N9pPUW8fv+B1/6vxzqBc+
tTP1njD1ktSjLPjzUhy/43f8RuLfCGrJpytMvUmmXlKivc3AnJMSf1bz3y5q
GUT+7d+65uwcRm2C2P/LKz/tWWyhulAqZJm9DV6f+Zoz/veqPh7RD/Wgt/9j
A/9TzlYTJQa/6fh3W8PmWhBxYBQ17103ixpAtZjkz6qgXTUgnvspHnxX9J8P
qBVUs8Z9redHm/pRezHGEcX+NQh5D8hmfhDvpjy/QBypaB/VIWnDSn4Q8bqc
AHtFNGYGmXaixr+kn3+5tcNiwuwV0Z5w3wX5k5z/tiRtyPr8FxDvtOmwvpMc
P0a1WsLfxVzXH8LejmrT8AHlyXSvDcn5N+Dlkxny74EvpwUxx3Fx/g97Vb0w
HyxX1QvzwWDG/CvMNUMqdoUPAu+4hfhgJyZ/UvsfgdwERG7jt4cY2yS2VPtA
9n4f6ZnkN7gWld9UAZHTyvI6lQ/mJOfC2EnzFvF3KsaL1AeS+6nYSa8s4h9V
2KrtA499XeN+XKzNip/ri5F9EIGddGgR/5KmzWey8e7dpwn0c6Qji/hnNW1m
47zvXjo5EumAOXacBi9j80AS7FX30/FBGYLffdCao3LdIOmCbbbEYffGe2Bd
0zun8gHFiR3m+DYwOY3pAmLdJir7OujnSH4NgthL4M7R2sknMPd+8jBj6wpj
Bz3HhbEr5wUQewFc7KOcq05jnJjQJmNnM5zfr6hoo9oHIM9tAj4A8W3XMVN3
tapOt6Rdk6L2GhgfrEnqb3jcqrzurw9C2OlYk6/dHuDzAZNaYvipP+6H+ECV
01Z8MCxhJ41JxgmtudHaAe21nabAT3tSge/S8FgHqNe44+olaOylgYgNjSDy
KZNijQERm7lvOC6ibVl7NhYQa2GyPhznd88Ne6Wgza0g1uvicpP/xnT6vK0F
RMyn8cDlajLR/L4KktwwrwXEmhU9K9PaBT2/H3qsByDy+XXPV1o/+G/MKg5k

"], "Byte", ColorSpace -> "RGB", Interleaving -> True],  asynchroneicon=Image[CompressedData["
1:eJzlm89rE0EYhpdaShAp0oMHkaIiRfwDpAeReqs9eIjoQTzYYFoFiZIGfyEF
kSIiRYqIeBIPUkRERIqIeMihBxEPEkS8jYgHEZEcRERE34+daIi7s2nwm3dw
X3jaNFu63zO7mZ2d2W4qHS9O9UVRNFPAl+LkqV3V6uSZvWvxw77KzNHpSvnw
7kqtPF2ujpZW4c0xS3+kGzM20AeqoA6WwSzQ3m0wgWsN/OzgArsuH4Gn8C7B
/6OcF+z6tAPHkQT3FiPs+rQDxz0O/wl2fdqB4xGHf4ldn3ZsX5/mf4Jdn3bg
eMXhf45dn3bgeN3hf55dn3bgeNPhP8euTztwvO3wv8iuTzsZ/nk//v/9GDjD
Pw/9n8t/ll2fduC4mPPrv8v/LLs+7WT4n2bXp50M/5Ps+rQDxzsO/xq7Pu1k
+Of9+OfdPw/9n8s/D9e/u92Mf/G6HwwB19/yUvO/TIb/vP2dCfDJvvdBPhft
rnhdBK/Ad9AAozShFSbD/wZYbZ0T+wZ83w9+dGxrgs1st26COu85/B+AQynb
voEF8DVl+1MTr6sJB+04S+ZaC2zn9qCe+w7/L+CzY3sWS+BFQrsE01HYY9yr
X68EM6+AWh4S/OW8Wsd2l9hz1Le/EMTYAnU8Ivk32O4S1PGY5C8MB+D/hOh/
IAD/OtF/nuxeMH/GtQyWyP4LRHfhNclbxqSudW9fNAnug4Yz5kvD21gY+9oA
Xgbg3I6XcSD2MwzeBuDbifoYwMRzN88DcE1iiwf/tHv4EPDhzxrjd8NGD/5v
AvBMY70H/0YAnmms8eB/KwDPJGS+WFtf/McDcE3ivbp89PsZ9xCvf898+Ns2
2G7+nqdns+jL37bBpQCc2/E6B4j9Dcg5F4B3i3Gf/rYN5D4gaT3LN9L3D/r2
t22w0+6f6V9nuLe1QYXsf4zsn/Xsuyay/jPE9LdtIP0hY/77Ktu9FRPPh/m8
P5Bjr37Ps5KYeF7M19zQZbZvUlDXNqO/FtAM4XOfFtS2w8TPdWj5X2M7ZgU1
Tin6B///pCa+Li4r+W/tta5fst4l8Q==
"], "Byte", ColorSpace -> "RGB", Interleaving -> True], parallelicon=Image[CompressedData["
1:eJzlm29EX1EYx9MmSZJMkkkjk0xm9iJ7kZZMy2SaTSaz8mvZzG+p7E8yshdJ
Jsn0Ikkv9iIzM0mvksxMZmYmyaSTycxkkslk2nm658fT6Zzn3Nvvd8+5dPhG
na97n8855557znNPp1oeNNxJT0tL68zkPxqaH13s6Gh+ci2X/3I93nm3Ld4a
uxzvam1r7ahoOcb/WCV0PM1tYVUZjVyzXAtcg1wZjkOyVjhrJdeupF7Xcdkq
nHVCwb+m8Z7ninM1cWXbjjWMwjkWFfygfMlXzvUX1X+K8nPCYwPVc42KPm6B
vyl8fzT81ZJvVOGJWQMKWHhs9xXx3pM8GRp20C3Ju6rwzNql8ldE368r4v0m
+U4Q/I+RL1vjgbHj+vV1oPCYCgmu0z59A8h3hvCVKu4P7VrFlWeLWbp/KRFv
E/IVEL5R5KsmfHXSvWGe3BJ1Sy7Gh6G/cL9S/JPId5XwxaR7v5bq982jNgq/
ZxER7xTy5RO+aeS7Sfi6kC8d9f2BecQifxYR7yLy5RC+OeRrIny9yKd67sZt
84tYNjTxbkM/CQ/1/vuArnWL8PUh3yVF/Ywj/i9EzEXCA/qn8Xz2yY/nk9uK
+o+O+OV5CKsK+eTnNaFlA1dCQ8gXV9QvWUZPxDJAxBxDPtU6CbSOPFT/DyPf
Q0X9d9vsIpY7RMz9yLek8WwiDzX/vUC+HkX9T9vsIhZqzfIG+d5rPDAvJDzU
+Mf8zxT1Gw7wTWsA/A6cInxZwkONJczfr6jfcsQPa5FtTcw7XJnCN06wFQiP
ai+p4h+KCr+IR5fbAJ0Tnj7CUy483YRnBN1P1Zabuvgs8FNjOyY87YSnRnhU
4zohvE96GzF+1XjcFzfzcr86T6PwqHI/CU2g+y0o6n855Kf6dkl4qPdEu/BQ
4wi/S74r6td18Vngryfi3pvfmLdf19UPiutQa+lZ4YG9hGotveKQn2IDQU6U
ygFBv8N7RJcjBS2Ke+lyDoumOEPkzzPwzzB6D7zmow33coBMv0ZccMhP5bd3
xXitM/C9M9SD4LuIbo6cM0caaht8M8Su2/8G0VeuTd0z5Jh/LgV8yWjSHGWo
/JOO+ccc84845h82Rxkq/3PH/H3mKEPlp9buNtR9xPnjR5y/5YjzNx5x/iuO
+akcgA3VJBF74swR7NMa2CG+pzM6v2dDlYdkP8e8M0b4WnD+aIyrOMB1Zhzz
VxyC/QKj922Q14XnOtfHtZYd858NyA55lBWf1/7N9ZSJPLXiWpDf2XHMXxaQ
37QfVwkYZ0VbQD4T5gr4Fmfa+9pQSUD+hgjEnEoVB+TP5JqPQNypUmEQftEG
kHOsZd67OwpjOBnlBOWX2gJUwfWSuZ/LggriTQZfbosSrlcR4PKrHymD398O
cLbyawT4TAot9828dUIfi/YzEXruk3lzw2oEWFXqCZtftAF855mOAK+sWhv8
og3gndkbAeaE4Lk07k9CaIcbTH/uxabmbbOjNoD9o+78qy3dd8Uv2qCM6c82
hi3Yuzv53wepDWC9tOaA3+k3H1x4LMXM7vsR+j7wnifMwryzkH5zKslqwByR
/cLjOsnCz4XBGYATrll1hXn5sDD3DSPmKNwW0QZh5RScfuvwW5h3pikV515k
HfhfQL/lP1CLou8=
"], "Byte", ColorSpace -> "RGB", Interleaving -> True], renameicon=Image[CompressedData["
1:eJztW01IVFEUHiYRkZBBXLiIqBBxIRESIiJiEYOJhEwU4iJ08K+IScboR6JN
REsRF60kWrSIaBEtRFqEiISIi5AQEeGKRIsIkYiIkDqHdweOZ+59P+PzzRvf
PfDJOPOdn+/d++679773TqfvpIbjsVhsvAL+pAbuX8hmBx5eTcA/1zLjN0cy
Q4OXM3eHRoayLelj8GWHRFnMmDFjxvJNdJSXA6oBNSUO1FDuUnMVYALwGbAH
+HdEsCc1obYqjfZ2wNcQ1HrYQI3tTHsb4HcIagsKqLVNaj8O2ApBTUFjS2rP
hKCWYgG1L4SgjmIBte+GoI5iIcraDQwMDDh2AK1HFDsu9H8/+OoxnIbajH6j
3+g3+o3+g+sHbj0gLdF2mLWzvJdI3hMe/HzTD7w4YJn4dRWuyJtBrn6Sdxbg
1s9P/YPEZ9VtDX6YsPam6V5lt0s/X/TLtt8kPhkXPri3nATcEta+C35W3oIT
1r7UGGBGcvN48N1Tkn8pYP1Jwse95VobbgowB/ijyIV70icZvxbwhfGmFHEb
GedcgPpfEP6KDa9G6l4T+j3Wxdy5g+2MbangbCtiI7YJ51kQ+mXeb4T/3IaL
fT5B/EY1Oc9KzhPN76ua+G9pXwpI/xnGH3XKS3wRy4qc9wBNgL+amoY18R6z
81B5b8dn/Z2M7+m6B/ysIucHYY0FHwF9gJeAT8IaN67bxOpncZoC0D/I+M0e
9Z/S5F13aj9FrG4W44oD3w/9Y4zf6KVmGWNNkdfVNZzFuchi9Dnw/dDP7xcV
on9akTdbQByuv9eB74f+NOOfL6Bu3m8R7wuI01WE/s/Hv2QBdU8q8v4CVHiM
c4PFCGL8q2P8tA0Xr/84nuOcF+eMlbL/4P3nbUVuT2MA8B8QX7z+JQLQH2dx
JjW8BrF/npRrY6wTn8OYUuSe8aj/FfFdc8H3a/77mvAXNZx3mvgrwlq/9Sh+
23VqQ5Zjg/hOB6g/Rfg4Z6tWcDYVsbH9G+TvuMb7qeDMy3OlRZ43dZoa+HnY
GqB+XKfQ9cxtBWeOxcV+38s4Ew61/MDjpKmBrhVw7uhUtt/7H8PEJ2//Q7bP
kuwfuJ7tUcSIyTamfQXHjDd4rITmeiCPP93/yIsdgP4yqTvn16nhuQmHPLw2
VLrk0nn/vIccfu9/dhC/Bbd+BzFhXX9y82fsW67nn37rlzFxLrMoUe9dkTeD
HM0k3yOPvmb/3+g3+o1+2zlHses8LBPWfIrr5c8A2u7nl6oJ674Cf6Yftaue
f8V7anlz+lI1Yb0DMavQidp1zz/jGh3XV+sljg2hf7YftUf6+XfZPyL7/gM5
RyL7/gs5BpF9/0lxLCL3/psxY8aiZf8BQw7jTw==
"], "Byte", ColorSpace -> "RGB", Interleaving -> True] ,nameicon=Image[CompressedData["
1:eJztm09IVFEUhwcLkZBoIa0kCAZpERHRQlrECyIqXCm2apHiaEVMMQpRhCAh
LaNluBAREYkQFy1aiQtXEi3ERYvgRIRIhMgQERH2O9z7FsrIu3PfvHeuzTnw
+Q/nzPnevHn3zr3vnB582DvcUigURtvwpXfg8ZVKZeBJ3wn80l8evTdSLg3d
KI+VRkqV7sEj+GNkOVqQC4pa28AL8BX8AVWwCT6At2AcXOX/c8zXCiLwFLwB
azZf1ebnn1+B41m7OdTKLIFdB3bADDh/QK4z4DX44ZhvBbTk7byv5kuOte6H
X9dOm6MDTIO/Hnl6hP0fePrv2te5DL6lyDEh7H8rRe2N4L6w/zEy1yMJ921w
UtLfHoOL4EvO7lsgknaPg8wYeB0Mg0fgOZgDn1J6fgbzYNLm5fw3+byTdnYN
1FokM17/dnTmcWAKnJWuvZFBZqzcSXD/xeeRdK1ZBZnxLtjxLOuA37kE/0i6
xiyD39MJ/pela8wy1F/91T8bfzJzcZ4nLYPVAHjn4b9e53OsWGd2n0nInTff
Pfx9mSUzd5J2lvKvBuAr6R8i0v68PtAlSNHD/7Zj7m2f4y8dDv5O4x+7qb/6
q3/d19+ifWzDOST+XQ6P80L91V/91V/91V/9g/Vv6vmPdKi/+qt/bv7Nvv4l
jfT6pzR5+4e2B5CnP+/9zAbgLOXPe3/x/ifvCUrvfea1/7lsnQ/F/XAO/rr/
/x+H+qt/k/s3+/2PdxL8x6RrzCrsub+V4M/3R3dL19rIgM8pO0f5meAew/fJ
v6Qanx9DDTI9e9fAEJl7vLn/gefjG+TX1xXD/RNztLf/oSek+R7J9L9shnCt
RA3tlK5/LQ18regQ9pfuf7sr7J+m/5HXKyYo3VrWuLC/b//re7LXd3zvJNMn
7ZNHuv+VWXSslce/BT5mB+S6QGYdI6lHKobXOSRb3+O6a/W/8zznoz02PBZy
b2B7Hfm4X/6ZPS+4j75W//uefP8AW2lwQw==
"], "Byte", ColorSpace -> "RGB", Interleaving -> True] , switchicon=Image[CompressedData["
1:eJztm01IVFEUxwcTkRYSEiISYiLRSiREXERMLqRCXFiJhATK+JHEFFOURQQu
WrSIEImIFi4kXEiIRLiQGFxERAuJiBYRHpAQiQgJiQip/+HeR7fHG9885368
oTnwE2aQd87/vvtx7rl3Dg5e6hkuSyQSVyrxp2fg+vFMZuDG6X34cDZ95cJI
eih1Mn11aGQo0z64B18mJeWJ4jFKVjwCDa7jcGHQXQV+giXgOhzrBs294Lck
5Toe2wbNTxT9m6DedUy2DFrLwTdFP7P4v4wD6OzwafcYdB2bDYPOyRz6uU8c
cB2fSeM+DlZz6GeeF9M4QKzVoBNcBlNgTq5pWfACPAPT4A73b9C/g3aP8651
7WSI7zCYACtgOw89UfkK6lzrVE3221PyverWG8RCXMYB4mgFLy3pVjnnWHcF
uGeoj+c7Dmodaa8DrxzpVpl3oL0ZrMdAu0efRe2tst+51qzyBdRY0H5I+nKt
N4g5w9o5j/kUIZ4N8JrEvoXXKs7blsFHEvt6E21wxpD2Mhn/Tr7XwAPQHdYX
SezveA65SCIX1LV+cJvvN6A/ncPfLzALktxGBTy/WZP+bd19AM9rBFs+P9x/
H5KmmgSJvLEQ3Vuy7zXpiMcX24LP16JuP5R7v5tPf79los/LuJKKL17ve8hA
zo1nfoiom/8/BSq1B/NvXFnpb95gG9dH0M3rR3chc02EuI7I+S1j4p0rflJ5
zGlcM2gzFkRwXPdBpwU/cyFzWqPpGHLEVWXBB+cV/lya57TbpsZbnAwa2xXd
q2AM7HUdly2Ta9c7EjW/Yjqa1GLQXGtjLi9ZyUpWMldmI5eIm5E4DzlG4nxr
0XU8tkzmdLxPVGvj11zHZdp4LwpGSdT3/Ll8iwX/rs5BqmUet5FjH7NuOseR
+eO4SR8BPhtInGf7a2N+ZgzGwHVUPn/jepyV82BZF5iVtYF8ahb9huJoVOaY
aRM+FF/MCRL3FaLWY7WOSzm/8j5xk/7WYrXXPaWvCjm23kbU7bGiOZ428Mbn
Y1KnD+mH715y3Wttl7o97mqKpwU8DXg+x6c1t6Lw+0dR4Ds9uyoeklhPe0PG
XJdO7YrvYU36GT4vfQz6SJyfBtY5pF5+z6PyXW+GPFd7v1diYZY0toEKrxuf
SdTwufbzXn6OcgaY3W2/itAGvL5/N9QGhcDtVm1Su9IGozHQ69du7d4bibU2
6ppvCr5LYD3Hj8k4mCHDZ30hbTDmSDefjXD+5Uq6p5/HQdaibs5p+ewrNmdA
FHwPwsT75v1cLH/rQbnvwahEWcf5f3lO57skXWR4TS/U5DhYDtHEc0UNOEoi
f+U7TuMkzjRvys/8Pe9liq4uipibQsZBLPuuTiPxW4Yg7Vr3u3E1OQ6C7rtP
uI7NlpHYy/nHQavruGwaiRqJp51rEa5DsmpyHHg1yCnX8bgwEr91+gE6XMfi
yqjI7q/8AaKKH18=
"], "Byte", ColorSpace -> "RGB", Interleaving -> True],delnodeicon=Image[CompressedData["
1:eJztms9LFVEUxx8mj0eIiLiSCGvRolVLcfVaJq5eBK0EJdNELJ5C5i78C+Tx
EBEX4kJchISEtHAVIq1chbgQjotHSKuQiIioc7wzNf4Y3z3nnjszwRz4CCXP
M5/vm5l778y9Nfy88rSlUChMlfBHZejl/Wp16NXDDvzHo8mpZ6OTI08eTE6P
jI5Ue4ev4X+WA1oLeeWVV1555eW3oFzsRgaQaaSGrCEbAevIAjKDVJCetI/X
tdChBSkjdeQQ+c2kgSwj/ch/M1TjsbYhVaFzHJ+R10hX2n5xhcdWRF4gXxS9
z3OCzFHGaftGC4+nF/nk0fs8R3RdZMCbrvFZ5GeC7lHoPlpMyb2EvEnJO8oH
pDNh9/agb9ruIXTtdSfkXsqYe8g+eB4fwFzvWTjn49ih78ej/2wGHJux5Mmd
xjjOff5E0Yn7tyrK7jS34YzvdB52Ie8U3Gk+dQ/MusH2M8egOCaAmddx3Nsj
ublkcOoeOQ5OBvNK7m1gP6f96x75vDSDM+6CDH4gNxX8q1J3hwwudRdkUHN0
p/HOZh23G+cuyOBKd2YGdN8Ur5XArN9tcj60OdcsMrB1p+9lyfLYBh3864xz
1jUDH+7EpoM/9xmGNANf7sQ3EKwRwTyv4/SRZuDTPaRP4D8g7MXN4I5nd2JC
4M+Za4gzSMCdqAv61hx7Omeg5E6w74Fgns+79hVnoOhO7Ar6byj1Zmeg7E7s
CfzfKvYnPiK2vceVe0v81xX7W41xkd6u68YL2Qv8F9Jw95TBlqD/TFruHjJY
FPSupOmunEFV0LfHtzuY+3zTZ9YKGZS5/kHfhmd3GuO01s5x0HOg60L/Zc/u
4ed8ZrAtcQ/69Sfg7juDcQf/VjB7D3y7+8rgOzi+EwOz76JZn/fQ5BmDhTs3
g0GLv7Xi4h70ofcYNu9fNuIyYLhbZYC/ewzN30X9Qu66+gf95iyP+0IGAvcr
M7B0J1Y13IOe9A7kiJuBg/ulGTDcvyI3tPyD3pyx4DQDR/czGTDciTFN90gG
nGdCtueLDQ2GO63bfeiH404W936EHCAdXuT/ZdAJye5145wjt326RzKgdwP7
GXAOoTmayljHyIDmBTsZcD9I6nu/JAPaC6b5nJIL3eu8Xu+WOdCzkuMEvWl8
HwNP93lJgbkvzoNZb/vypjntKijPbTQLzFyF5gma+79oHbcCCd/jXArMnJnW
aJtg3kFznek82gbzLiCz+/5tCsy8qQ+ZALOngjKhPTN7AfRuZAtZBLPfiPad
iJ5Z5ZVXXnnllZdN/QEwWK8r
"], "Byte", ColorSpace -> "RGB", Interleaving -> True], undoicon= Image[CompressedData["
1:eJztmk1IVUEUxx8m8ggJEYmQEHuLkBYtQ1zEC1qURIsXtWghKX4lYvGUMolA
XEi0EBEREQlxIS1CwoVISEiISIiLEHERHRci4iIiRCSizmHmxuV138zcmbkf
wT3wE7zMu3P+c+fjzJm50PIo116SSqV60/gn1/z0Wj7f/OxOBf5zt6f3YUdP
W+vNnr62jrZ8fcspfJjllKYSSyyxxBJLLFiDbFk1cgvpQ8aQOWSe8waZQPqR
HFIbtb+mhhpKkCwyjnxBfvtkD5lGGpH/ZqlGX8uRvKbmYuwjg0hV1PqKGfpW
hjxGDi3qLuQHMkRtHLVet6E/9chWgLoL2aVxEQPdNMYHkJ8handD82hZRNrT
yNuIdLv5iFSGrP0Mrzdq7Q409qpD0p6OmXaHbQh4fQA23uPQ54uxSt8nQP0D
MdAoYyog7bTGRTXP+yVnWTvFNrbWd2rDDWCx7XOkC+kEFjOOIEvIN8M6DsDi
mgAsrjPx5xfXdR+pUKivFLmKTAKL+XTqHLWkneJ53ZiWdNM+r86g/krkJXLs
s+4TpMaC/rykntUizz8jDab1u/y4iKz7bIMxwzppvZPt46qQlcJ6IYB1CNg8
NOVDP40d7b0SsP27rI40HyMrvM812dTs4VOKjwfVNtD2B1juQqqfly232d8l
fqV89IMFg3pUchiBxVsS32gsfFLw7wg09ojA8nUq7autH39bR/0TWBwwjLxA
HiCXae5R/P2Jgo+++yWwXKV1/Vj+NLB4YkfyXsp5vULOS943ouBjt4b+Ptv6
gcU0XxXf63DM+4VnDhSfn1PoA+Ma+sds6sdyLWC2f6D1xTOmBZY/tzoHAovb
rOjHMteBxYK62h1o3/DPeo7P7kl+t6ahf96ific+MNVPzHm8/6zkN5sa+t9Z
7v822+CGx/v3LOuXjSlf+i23warHu9cE5dc19E8o+kJ6PvhAJWZRIVPg75Kg
7KKG/n5LfgZFa4G/on41qaE/FwONIkYK/N0WlM1r6K+NgUYRr12+0l5AFANl
/ern7xXNqVEz7fLziqActctpTf3TMdBZjGGXn4OCcss62vl7G2OgsxhN3EdZ
jqrLQD/lYfdjoNWLDPfxtqAM7Z2MzsQkfSsqtlzffkNQbsZEO6+D8pu6Ofig
eMJ9axeUof3WJVP9vJ6hGGh2OOLfJIN8F5SbtaGd66e4fTcG2gnKCVEOSdTv
qV2EeSONNojDWnDIv71sb95pU7urDVRzQkFBOaQZSRnatwch34kzo7r78V7h
u1NOVXq+atgGdB4Z5l03gvKGsrMIitUzcgVW2oDOBkT7rbChGM3KWuejDWge
Knb2GyY7YX13jzags08/57G2obku0PGu2A6UKzkIUTet73RnJmrpfw3YvDgK
audxulBMOwuWYxubhr7VAIsTbO4ZaB9H636oc5yJAYuZ6Wx3AVjM7lcz9aNl
YPfDYnvvX8WAxU0NSDewOxXUJpSv3+TQvZ5FYPe96L4R3TvRylklllhiiSWW
mIr9AXDmWNo=
"], "Byte", ColorSpace -> "RGB", Interleaving -> True],plusicon=Image[CompressedData["
1:eJztmjFIHEEUQD8mRTgsJBwiKYQclpJKQrCQi9hEUhkiKVKcklPTbOQMCRGx
sUohFlct1hYh1REkpJArUoTUIiksUocUYpEiiCT/3+yhMbt3O7N/ZnaW+ccT
tHDmzc3u/v3zby++mFsaAIC1G/hjbuH1/UZj4c2jIfzlcbD2fDmoP3sQvKwv
1xv3Fq/hH6sR18GHDx8+fPjwYTRCfPyGMIxUkDFkFBm0PS0tIVynkE3kA/Id
OUP+xHCCfEXo8xQZsT195QhhAmkiPxNc03COtJGaM/sjhJlozqrOSdA6biBD
thVjQ1zL+xq849aB9sOAbeVOhB1WkF8G3C9zgNyy7F5C3hn2vswPZNqSexn5
YtG9y2/kiQX3oxy4d6HnRM2Qeykn3/tVKKd4qNmdsHm994PuweMa/Vdy4NiP
o84e5XevAM8z7hhpJfCRaQ12NPhz5TZve4xRZhqD7gV3GN1nGPenCX/iE6N/
20F/4i6D+wTznEz6v2fwbzrsT7nhzQzuVLvI8v5u259YyuA/pWE+pv33M/hv
FsD/FFRrBaJe57o/oZYTi1pl2jGOO279me0xXinl/9iT9J9XcKd7X1KdNo6W
0hqrRAiTkv6vFMYYlhwjz/7bCmNUCuQfKowxViD/XYUxRgvk31QYY7BA/luK
45xIjEG1i3IKkmszlKek+x+zkv5qObA4i5QZJw028p+qon9YAH+qjau9A4oz
aNf9D5XcxXxGovVz2V8+9/l3Tm3H/bPVwMRZs6v+30A+87s6J8oDOGtAJv2D
jPbdeW046E9n4zznQNRzwrcHTPmvsrhfzI3rPkC1i8kEZPO6JA4hZG5xF7np
AeP3o4uzzlrqCOq3EdeVbcderGtxv1iDaRDnCrY942iBib4w6rfhzwuz8hl0
nPsnr0EN5Oqjut3N90VSv435vr+4PW/ue/9/DcbBTi8Y7b11yEMfqDi32DF4
PdDzXc8zLktQzwn1XejzpmfvKnDnNtxB75zUe8D3nKT3uMDqda4SVHei2qPo
nTqV8D2P9vh2tJbuh8if6V45D3QeJ9zoswuix2QrWqsqZOnZ8OHDhw8ffeMv
bm/lLw==
"], "Byte", ColorSpace -> "RGB", Interleaving -> True],minusicon=Image[CompressedData["
1:eJztmz9IW0Ecx0PaoQSHIEXEQWhwDE4ixUFScWlxslQcOkRpol1SicVSERen
DuKQKTg7FKdQpDiUDB1K4bdJ6dDBuXQQhw6lSPs97qU85MX0fvfuT8L94CPo
kN/v88t77+7dnfdWXyxWs5lMZvMOfiyuvHpQr6+8fpzHL09qm8/XapVnD2sv
K2uV+v3VW/hjKeJ2JkSIECFChAhhMwjDLxgBBTABxsGQ67pMROQ6C3bBO3AO
foM/CVyAz6AJnoJR1/VzA7VPgQb40cX1f7gCbVDul+sDdc5HNXOduyH6uAPy
rh2TIrqXTwx4J/VBXA9Z184iSLIOflpwj/MBjDl2z4G3lr3jfAdzjtzvgk8O
3Tv8AssO3L944N5BjBNlS+45T77364g5xYJhd4HL+70X4hlcNOi/7oFjL8R9
mTPgXiD7YxyXAwP+NuY2aSGeBZMpus974KTKaYr+bQ98OEyn4D7lgQeX4xT8
Gx54cBFzw2ENd7F2ofP+7gNVDf9ZD+rX5UTDf9eD+nW5JOZaAcn1Otf1p0GR
6X+ukOMbeGOJI0X/JYa7ePZ1W6dNosXpMSeQa0bRf4uRY0Qxh8/++4wchQHy
bzJyTAyQ/yEjx/gA+TcYOYYGyH+PmedCIcd7kuuiNnik6M+aA5Pci1TJ4ysl
pn/Tg9p1EWvjrHdAknvQruvX5YzjHvmPRv1z7aCD8tznWg/aHjjooLUGRnKv
2bUDl6+kI5/5Nw/o1zWgmqZ+pwc7HrioIvbGU9kHwufk+/Aa2EjDPdaDfnoO
nFHKR9zxeVmSZ05cu/VCrNnMpOke68EYyfvKteNNbJtwj/VgjuS+gmvPJFpk
4VwYciyTf/PCj2Rg3/+GHpRJbX3UtLv1c5HIuUDuz0S0bH7vCT0okpuzYOLa
2yYPzoGSPBN2YPF+EOO7kTFOJ1DTJDg16C3G3g3y/N/3UN80OKb0xknxHldz
eZ9zAvUOgyrJs1OXCr5X0TW+H/Wy74Pk/Fk8K5fAVuQm1hcPSZ4x2Yt6VSKN
MxshQoQIEaJ3/AV+LEYy
"], "Byte", ColorSpace -> "RGB", Interleaving -> True]},
With[{helptext="
\!\(\*
StyleBox[\"Node\",\nFontSize->14,\nFontColor->RGBColor[1, 0.5, 0]]\)\!\(\*
StyleBox[\" \",\nFontSize->14,\nFontColor->RGBColor[1, 0.5, 0]]\)\!\(\*
StyleBox[\"[\",\nFontSize->14,\nFontColor->RGBColor[1, 0.5, 0]]\)\!\(\*
StyleBox[\"Right\",\nFontSize->14,\nFontColor->RGBColor[1, 0.5, 0]]\)\!\(\*
StyleBox[\" \",\nFontSize->14,\nFontColor->RGBColor[1, 0.5, 0]]\)\!\(\*
StyleBox[\"Button\",\nFontSize->14,\nFontColor->RGBColor[1, 0.5, 0]]\)\!\(\*
StyleBox[\"]\",\nFontSize->14,\nFontColor->RGBColor[1, 0.5, 0]]\)
\[SelectionPlaceholder] \!\(\*
StyleBox[\"Create\",\nFontVariations->{\"Underline\"->True}]\): select the logical operator associated to a node, then right click any where.
\[SelectionPlaceholder] \!\(\*
StyleBox[\"Move\",\nFontVariations->{\"Underline\"->True}]\): right click on the node and drag it to the chosen place.
\[SelectionPlaceholder] \!\(\*
StyleBox[\"Delete\",\nFontVariations->{\"Underline\"->True}]\): move the node out of the work space or select "<>LogoTxt[delnodeicon]<>"and right click on a node.
\[SelectionPlaceholder] \!\(\*
StyleBox[\"Rename\",\nFontVariations->{\"Underline\"->True}]\): select "<>LogoTxt[nameicon]<>" and right click on a node. The name must compliy to the regexp: [a-Z]([a-Z] | [0-9])*
\[SelectionPlaceholder] "<>LogoTxt[renameicon]<>" Globally renames the labels of all nodes.
\[SelectionPlaceholder] Operator change: select "<>LogoTxt[switchicon]<>" then right click on a node.

\!\(\*
StyleBox[\"Arc\",\nFontSize->14,\nFontColor->RGBColor[1, 0.5, 0]]\)\!\(\*
StyleBox[\" \",\nFontSize->14,\nFontColor->RGBColor[1, 0.5, 0]]\)\!\(\*
StyleBox[\"[\",\nFontSize->14,\nFontColor->RGBColor[1, 0.5, 0]]\)\!\(\*
StyleBox[\"Left\",\nFontSize->14,\nFontColor->RGBColor[1, 0.5, 0]]\)\!\(\*
StyleBox[\" \",\nFontSize->14,\nFontColor->RGBColor[1, 0.5, 0]]\)\!\(\*
StyleBox[\"Button\",\nFontSize->14,\nFontColor->RGBColor[1, 0.5, 0]]\)\!\(\*
StyleBox[\"]\",\nFontSize->14,\nFontColor->RGBColor[1, 0.5, 0]]\)
\[SelectionPlaceholder] \!\(\*
StyleBox[\"Create\",\nFontVariations->{\"Underline\"->True}]\): select "<>LogoTxt[plusicon]<>" or "<>LogoTxt[minusicon]<>" then left click on the source and drag the arc to the target. For self loop double left click on the node.
\[SelectionPlaceholder] \!\(\*
StyleBox[\"Delete\",\nFontVariations->{\"Underline\"->True}]\): select "<>LogoTxt[delicon]<>" then left click near the middle of the arc. For self loop left click at the center of the loop.
\[SelectionPlaceholder] \!\(\*
StyleBox[\"Sign\",\nFontVariations->{\"Underline\"->True}]\)\!\(\*
StyleBox[\" \",\nFontVariations->{\"Underline\"->True}]\)\!\(\*
StyleBox[\"change\",\nFontVariations->{\"Underline\"->True}]\): select "<>LogoTxt[plusminusicon]<>" then left click near the middle of the arc. For self loop left click at the center of the loop.
\[SelectionPlaceholder] \!\(\*
StyleBox[\"Family\",\nFontVariations->{\"Underline\"->True}]\)\!\(\*
StyleBox[\" \",\nFontVariations->{\"Underline\"->True}]\)\!\(\*
StyleBox[\"change\",\nFontVariations->{\"Underline\"->True}]\): select "<>LogoTxt[familyicon]<>" then select the family and left click near the middle of the arc. For self loop left click at the center of the loop. Each family corresponds to a clause, either in DNF (And) or CNF (Or) form.

\!\(\*
StyleBox[\"Graph\",\nFontSize->14,\nFontColor->RGBColor[1, 0.5, 0]]\)\!\(\*
StyleBox[\",\",\nFontSize->14,\nFontColor->RGBColor[1, 0.5, 0]]\)\!\(\*
StyleBox[\" \",\nFontSize->14,\nFontColor->RGBColor[1, 0.5, 0]]\)\!\(\*
StyleBox[\"Formula\",\nFontSize->14,\nFontColor->RGBColor[1, 0.5, 0]]\)\!\(\*
StyleBox[\" \",\nFontSize->14,\nFontColor->RGBColor[1, 0.5, 0]]\)\!\(\*
StyleBox[\"&\",\nFontSize->14,\nFontColor->RGBColor[1, 0.5, 0]]\)\!\(\*
StyleBox[\" \",\nFontSize->14,\nFontColor->RGBColor[1, 0.5, 0]]\)\!\(\*
StyleBox[\"Equilibria\",\nFontSize->14,\nFontColor->RGBColor[1, 0.5, 0]]\)
\[SelectionPlaceholder] "<>LogoTxt[trashicon]<>" Delete the graph.
\[SelectionPlaceholder] "<>LogoTxt[neticon]<>"Compute model and equilibria. Three methods are proposed ordered by efficiency of computation. 
\[SelectionPlaceholder] "<>LogoTxt[undoicon]<>"Undo the last command.

\!\(\*
StyleBox[\"Network\",\nFontSize->14,\nFontColor->RGBColor[1, 0.5, 0]]\)\!\(\*
StyleBox[\" \",\nFontSize->14,\nFontColor->RGBColor[1, 0.5, 0]]\)\!\(\*
StyleBox[\"management\",\nFontSize->14,\nFontColor->RGBColor[1, 0.5, 0]]\)
\[SelectionPlaceholder] "<>LogoTxt[showsampleicon]<>" Show, save or modify network. 
  To save a network, enter a name then click on the button at right of the field. The modification can be saved by clicking on the button at right of the field. 
\[SelectionPlaceholder] "<>LogoTxt[delsampleicon]<>" Delete network. 
  To delete a network, first select the network then validate by clicking the button at right of the field.

\!\(\*
StyleBox[\"Workspace\",\nFontSize->14,\nFontColor->RGBColor[1, 0.5, 0]]\)
\[SelectionPlaceholder] "<>LogoTxt[gridicon]<>" activate or deactivate the grid alignment mode. The scale can be changed by clicking on the resize button. 
\[SelectionPlaceholder] "<>LogoTxt[resizedownicon]<>"and "<>LogoTxt[resizeupicon]<>" either resize the workspace (down or up) or modify the scale of the grid if the grid alignment mode is activated.
"},
DynamicModule[ {
dbsamples= If[FileExistsQ[filename], Get[filename],{}] (* variables contenant la liste d'exemples *),
 boon={},(* BooN *)
imagesize=600, (* taille courante de la zone de dessin *)
grid=False,(* indicateur d'activation de la grille *)
gridscale=2,(* taille de la grille *)
nodes={},operators={},names={}, arrows={}, (* listes decrivant le r\[EAcute]seau *)
tmpdraw= {},(* zone temporaire de dessin *)
src=0,(* index du noeud source d'un arc, 0 si aucun *)
inode=0, (* index du noeud courant, 0 si aucun *) 
(* param\[EGrave]tres d'\[EAcute]tats *) 
 dragged=False,(* indicateur de mouvement d'un noeud *)
openform=False,(* indicateur d'ouverture de la zome du BooN *)
mode=Sequential,(* mode courant *)
netname="", (* nom du dernier exemple *)
tmpname="" ,(*champ pour le nom du noeud *)
lastnet=Table[{{},{},{},{}},{maxdo}],
ido=1
},
Manipulate[
EventHandler[
(** Zone graphique repr\[EAcute]sentant le r\[EAcute]seau. **)
Dynamic[ 
IBOONED$ = {nodes,operators,names,arrows};
Graphics[{
(* affichage des arcs *)
Map[
Function[arc,{
arc[[3]]/.signcolor,
TaggedArrow[nodes[[arc[[1]]]],nodes[[arc[[2]]]], arc[[4]]/.familycolor,0.6,5,dist]}
],arrows],
(* affichage des sommets *)
MapIndexed[Function[{pos,index}, {operators[[First[index]]]/.opcolor, Mouseover[Disk[pos],{EdgeForm[{Thick,guicolor}],Disk[pos]}]
,Text[Style[ names[[First[index]]],FontSize->14],pos+2 {pos[[1]] <0 , pos[[2]]<0} /. {False-> 1,True ->- 1}]}],nodes],
(* zone de dessin temporaire *)
 tmpdraw
},PlotRange->maxrange,ImageSize->imagesize]
] (*Graphics*)
(** Gestion d'\[EAcute]v\[EAcute]nements de la souris *)

(*** \[EAcute]v\[EAcute]nement sur les arcs - click gauche *)
, {"MouseDown",1} :> (  src= ClosestMouse[nodes,2]; tmpdraw={}; action=Show;
lastnet[[ ido=Mod[ido+1,maxdo,1]]]= {nodes,operators,names,arrows}) 
,{"MouseDragged",1} :>  If[src != 0,  tmpdraw={sign/.signcolor,Arrowheads[Medium],Arrow[{nodes[[src]],MousePosition["Graphics"]}]}] (*arc temporaire *)
,{"MouseUp",1} :> (* action sur arc *)
With[{ closestnode= ClosestMouse[nodes,2]} ,
tmpdraw={};
Which[
(*creation d'un arc *)  src != 0 && closestnode != 0, arrows = DeleteDuplicates@Append[arrows, {src, closestnode,sign, family}],
(*action sur arc*)  src  == 0, With[{closestmid= ClosestMouse[Function[arc,MidPoint[nodes[[arc[[1]] ]],nodes[[arc[[2]]]],0.5,dist]]/@arrows,3]},
If[closestmid!= 0,
Switch[command
,Together, arrows[[closestmid,4]]= family
,Sign, arrows[[closestmid,3]]=-arrows[[closestmid,3]]
,Delete,  arrows=Delete[arrows,closestmid]]
]]]]

(*** \[EAcute]venement sur les sommets - click droit *)
,{"MouseDown",2} :> (inode =ClosestMouse[nodes,2];  tmpdraw={}; action=Show ;lastnet[[ ido=Mod[ido+1,maxdo,1]]]= {nodes,operators,names,arrows})
,{"MouseDragged",2} :>  If[inode!= 0,dragged=True; nodes[[inode]]= If[grid,Floor[MousePosition["Graphics"],gridscale],MousePosition["Graphics"]]]
,{"MouseUp",2} :> With[{mousepos= MousePosition["Graphics"]}, 
Which[
(*cr\[EAcute]ation*)  inode ==  0 && Abs@mousepos[[1]]<=  maxrange  &&  Abs@mousepos[[2]]<=  maxrange,AppendTo[nodes,If[grid,Floor[mousepos,gridscale],mousepos]];AppendTo[operators,operator];
With[{iname=Max@ToExpression@Flatten[StringCases[#,a~~val$:DigitCharacter..->val$]&/@Append[names,a<>"0"]]},AppendTo[names,a <> ToString[iname+1]]],

(*d\[EAcute]letion*) inode !=0 && ((Abs@mousepos[[1]]> maxrange || Abs@mousepos[[2]]> maxrange) || (!dragged && actionnode === Delete)),
nodes=Delete[nodes,inode];operators=Delete[operators,inode];names=Delete[names,inode];arrows=DeleteCases[arrows,{inode,_,_,_}| {_,inode,_,_}];Do[ If[arrows[[i,1]]>inode,arrows[[i,1]]--]; If[arrows[[i,2]]>inode,arrows[[i,2]]--];,{i,1,Length[arrows]}];,

(*switch operateur*) inode !=0 && !dragged && actionnode  === Switch,
operators[[inode]] = operators[[inode]] /.{And->Or,Or-> And},

(*renommage *) inode !=0  && !dragged &&  actionnode=== Names,
tmpdraw={ guicolor,Disk[nodes[[inode]]]};tmpname=names[[inode]];
With[{pos=MousePosition["ScreenAbsolute"]},CreateDialog[{TextCell["Enter a name: "],InputField[Dynamic[tmpname],String, ImageSize->{150,All}],
Row[{DefaultButton[DialogReturn[tmpdraw={};If[StringMatchQ[tmpname,LetterCharacter..~~(WordCharacter)...] && !MemberQ[names,tmpname],names[[inode]]=tmpname,Beep[]]],ImageSize->{70,30}] ,CancelButton[DialogReturn[tmpdraw={}],ImageSize->{70,30}]}]}, WindowTitle->"Rename", WindowFloating->True,WindowMargins->{{pos[[1]],pos[[1]]}+20,{pos[[2]],pos[[2]]}-134}]],

(*mouvement*) inode != 0,nodes[[inode]]= If[grid,Floor[mousepos,gridscale],mousepos]
]; dragged=False]
] (* Handler *)

(** Menu *)
(***  Barre de boutons de commande de droite *)
,ButtonBar[
Join[
{
(* Help*)
Tooltip[Image[helpicon,ImageSize->iconsize],"Help.",TooltipDelay->delay]:> MessageDialog[
Panel[Pane[Style[helptext, FontSize->12, FontFamily->"Helvetica"],ImageSize->{400,500},Scrollbars->{False,True}] ,Background->White], 
WindowTitle->"Help",WindowSize->{430,600}],
(* Undo *)
Tooltip[Image[undoicon,ImageSize->iconsize],"Undo !",TooltipDelay->delay] :> 
({nodes,operators,names,arrows}=lastnet[[ido]]; ido=Mod[ido-1,maxdo,1]; tmpdraw={}),
(* Delete Graph*)
Tooltip[Image[trashicon,ImageSize->iconsize],"Delete the graph.",TooltipDelay->delay] :> ({tmpdraw,nodes,operators,names,arrows}={{},{},{},{},{}}),
(*renommage*)
Tooltip[Image[renameicon,ImageSize->iconsize],"Global renaming.",TooltipDelay->delay] :> (names=Table[ a<>ToString[i],{i,Length[names]}])
} (* Fin bouton int\[EAcute]gr\[EAcute] *)
, Function[ r,Tooltip[Image[r[[1]],ImageSize->iconsize],r[[2,2]],TooltipDelay->delay]:>  r[[2,1]]]/@extra  (* extra bouton *)
](* Join*)
(* param\[EGrave]tres de la barre de boutons de droite *)
,FrameMargins->2.5, Alignment->Center,Appearance->"Vertical", Method-> "Queued"]
(***  Barre de Gauche *)
(* Calcul d'\[EAcute]quilibre *)
,ActionMenu[Tooltip[Image[neticon,ImageSize->iconsize],"Dynamics and equilibria computation.",TooltipDelay->delay] ,
{
(* brute force *)
"Dynamics & Equilibria (Brute Force)" :> 
WindowView["Dynamics & Equilibria",
{ SetterBar[Dynamic[mode],{Sequential-> Tooltip[Image[asynchroneicon,ImageSize->iconsize],"Asynchronous mode.",TooltipDelay->delay],
Parallel-> Tooltip[Image[parallelicon,ImageSize->iconsize],"Parallel mode.",TooltipDelay->delay]}],
Dynamic@With[{sg=ReflexiveReduce@ModelOf[boon,mode]},HighlightGraph[NiceBM[sg, ImageSize->Full],Map[StateToInteger,FindEquilibria[sg],{2}]]]
}, imagesize],
"Sequential steady states (Symbolic)":> WindowView["Sequential steady states",
{ Dynamic@NiceEqs@StableStates[boon]}, imagesize]
}]
, Delimiter
(*** Param\[EGrave]tres et actions sur les noeuds  *)
(* Menu de commande *)
,{{actionnode,Names,""},{
Names ->  Tooltip[Image[nameicon,ImageSize-> iconsize],"Node renaming",TooltipDelay->delay],
Switch-> Tooltip[ Image[switchicon,ImageSize-> iconsize],"Operator switching",TooltipDelay->delay],
Delete -> Tooltip[ Image[delnodeicon,ImageSize-> iconsize],"Node deletion",TooltipDelay->delay]}}
(* op\[EAcute]rateur des clauses associ\[EAcute] au noeud *)
,{{operator,And,""},{And,Or},ControlType-> RadioButton}
,Delimiter

(*** Param\[EGrave]tres et actions sur les arcs*)
(* menu de commande *)
,{{command,Sign,""} ,{
Sign->Tooltip[Image[plusminusicon,ImageSize->iconsize], "Sign inversion",TooltipDelay->delay],
Together->Tooltip[Image[familyicon,ImageSize->iconsize], "Assign a family to arc",TooltipDelay->delay],
 Delete->Tooltip[Image[delicon,ImageSize->iconsize], "Delete arc",TooltipDelay->delay]}
, ControlType->SetterBar}
(* signe *)
,{{sign,1,""} ,{
1 -> Image[plusicon,ImageSize-> iconsize], 
-1->  Image[minusicon,ImageSize-> iconsize]}}
(* famille *)
,{{family,0,""}, 
Table[  i-> Graphics[{ EdgeForm[{Thin,GrayLevel[0.6]}],i/. familycolor,Disk[]},ImageSize->{iconsize,iconsize}/1.2],{i,0,Length[familycolor]-1}]}
,{{dist,5,"\[Cup]"},0,10,1, Appearance-> Small,ImageSize-> Small}
,Delimiter

(*** Gestion des r\[EAcute]seaux sauvegard\[EAcute]s *)
,Dynamic@
ScrollSelector[ First/@dbsamples,
Switch[action (* action  des items *)
,Show, Function[label,tmpdraw={}; {nodes,operators,names,arrows}= label/.dbsamples; netname=label]
, Delete,Function[label, {nodes,operators,names,arrows}= label/.dbsamples; netname=label;tmpdraw=Inset[Image[delsampleicon,ImageSize->64]]]
],
Switch[action (* action du boutton \[AGrave] droite du champ du nom*)
,Show, Function[label, If[(label/.dbsamples) === label,dbsamples=SortBy[Append[dbsamples,label-> {nodes,operators,names,arrows}],First], 
dbsamples= SortBy[Append[ DeleteCases[dbsamples,label -> _], label-> {nodes,operators,names,arrows}],First]];Put[ dbsamples,filename]; netname=label]
, Delete,Function[label,{nodes,operators,names,arrows}={{},{},{},{}}; dbsamples=DeleteCases[dbsamples,label-> _]; tmpdraw={}; Put[ dbsamples,filename];netname=""]
],
"",guicolor, Lighter[Orange,0.75],imagesize/2.5, 105]

(** Menu de gestion des r\[EAcute]seaux sauvegard\[EAcute]s *)
,{{action,Show,""} 
,{
  Show-> Tooltip[Image[showsampleicon,ImageSize->iconsize], "Show, Save or modify  the selected network",TooltipDelay->delay]
, Delete->Tooltip[Image[delsampleicon,ImageSize->iconsize], "Delete the selected network",TooltipDelay->delay]}
, ControlType->SetterBar}
,Delimiter

(*** Gestion du Workspace *)
,ButtonBar[{
Tooltip[Image[resizeupicon,ImageSize->iconsize],"Resize the work space or the grid scale.",TooltipDelay->delay]:>  If[grid, gridscale = Min[maxrange,gridscale+1],imagesize = imagesize+200], (* resize up *)
Tooltip[Image[resizedownicon,ImageSize->iconsize],"Resize the work space or the grid scale.",TooltipDelay->delay]:> 
If[grid,gridscale=Max[1,gridscale-1],imagesize= Max[imagesize-200,300]], (* resize down *)
Tooltip[Dynamic@Image[grid/.{False-> gridicon,True-> graygrid},ImageSize->iconsize],"Turn on/off the grid alignment.",TooltipDelay->delay]:> (grid=!grid)} (* mode grille *)
,FrameMargins->2.5, Alignment->Center]

(*** champ de la formule *)
,Row[{ Spacer[130],Tooltip[Opener[Dynamic[openform]],"Open/Close the formula field",TooltipDelay->delay],
Dynamic@(fvar=boon = GenForm[a,arrows,operators,names,9];
openform/.
{True -> InputField[TraditionalForm[boon],ImageSize->Dynamic[imagesize]],
False -> Style["BooN",12,Bold,guicolor]})}]

(** param\[EGrave]tres de manipulate *)
,ControlPlacement->{Right,Left,Left,Left,Left,Left,Left,Left,Left,Left,Left,Bottom}
,Deployed-> True
, LabelStyle->Directive[FontFamily-> "Helvetica",Medium]
]]]]


(* ::Section:: *)
(*Interaction Network*)


(* ::Text:: *)
(*A network \[Eta] is defined as a symbolic state of the form { a -> f ,...} where f is a boolean formula.*)


Regulators[ig_Graph,v_List, kinds:{(-1|0|1)..}:{-1,0,1}]:= DeleteDuplicates@Flatten[Regulators[ig,#, kinds]&/@v] 
Regulators[ig_Graph,v_, kinds:{(-1|0|1)..}:{-1,0,1}]:= With[{edges= EdgeList[ig,_\[DirectedEdge] v]},
First/@Select[edges,Function[edge, MemberQ[kinds,PropertyValue[{ig,edge}, EdgeWeight]]]]]
Regulators[f:BoonType, v_ , kinds:{(-1|0|1)..}:{-1,0,1}]:= Regulators[InteractionGraphSimple[f],v,kinds]


(* ::Input::Initialization:: *)
FindRegulators[\[Eta]_,a_]:= BooleanVariables[a/.\[Eta]]


(* ::Subsection:: *)
(*Interaction graph drawing*)


(* ::Input::Initialization:: *)
InteractionGraphSimple[\[Eta]_]:= With [{edges= Sort@Flatten[Function[agent,Function[regulator,regulator \[DirectedEdge] agent]/@FindRegulators[\[Eta],agent]]/@  Keys[\[Eta]],1], vertices= Sort@  Keys[\[Eta]]},
With[{sign= Function[e, With[{ src=First[e], trgt = Last[e]}, 
Switch[With[{dnf=BooleanConvert[trgt/.\[Eta]]},{Count[{dnf},(!src),Infinity],Count[{dnf},src,Infinity]}]
,{0,_},1(* No negation \[Rule] activation *)
,{x$_,x$_},-1 (* Only negation *)
,_,0]] (* Otherwise *)
]/@edges},
Graph[vertices,edges
,EdgeWeight->  sign
,VertexLabels-> "Name"
, EdgeLabels-> "EdgeWeight"
, ImagePadding->25 ]]]


(* ::Input::Initialization:: *)
interactioncolor={-1 ->RGBColor[Rational[2, 3], 0, 0],1-> RGBColor[0, 0.5700000000000001, 0],0-> RGBColor[0.20392156862745098`, 0.28627450980392155`, 0.3686274509803922],_-> RGBColor[0.8274509803921568, 0.32941176470588235`, 0.]};
Options[NiceIG]={ ImageSize->Automatic};
NiceIG[ig_Graph, palette_List:interactioncolor,OptionsPattern[]]:=
With[{ color=GrayLevel[0.7],
arrowsize={Tiny-> 0.2, Small->0.09, Medium-> 0.05, Large->0.03, $size_Integer->15/$size,{$sizex_Integer,_}-> 15/$sizex, _-> 0.07}
},
Annotate[ig,
{VertexLabels-> "Name"
,VertexStyle-> Directive[EdgeForm[{Darker[color]}],color]
,VertexLabelStyle->Directive[FontFamily->"Yu Gothic UI",10]
,VertexShapeFunction ->"Circle"
,EdgeShapeFunction-> GraphElementData[{"Arrow","ArrowSize"->(OptionValue[ImageSize]/.arrowsize)}]
,EdgeStyle ->Function[edge,edge-> Directive[PropertyValue[{ig,edge},EdgeWeight]/.palette,Thick]]/@EdgeList[ig]
,EdgeLabelStyle->Automatic
,EdgeLabels->None
,ImageMargins->All
,ImagePadding->25
,ImageSize->OptionValue[ImageSize]
}]]


(* ::Input::Initialization:: *)
Options[InteractionGraph]={ ImageSize->Automatic};
InteractionGraph[\[Eta]_,OptionsPattern[]]:=  NiceIG[ InteractionGraphSimple[\[Eta]],ImageSize ->  OptionValue[ImageSize]]


(* ::Input::Initialization:: *)
Options[NiceIG3D]={ ImageSize->Large, Background-> GrayLevel[0.25], FontSize-> Automatic, FontColor -> White,
ViewPoint-> Above, VertexStyle->Directive[{Specularity[White,30],Yellow}],FontColor-> White, GraphLayout-> Automatic};
NiceIG3D[ig_Graph,OptionsPattern[]]:= With[{fontsizefactor=0.020},
 With[{signcolor = {1 -> Darker[Green,.5],-1 -> Darker[Red,.3] ,0-> Darker[Blue,.2]},
fontsize = If[OptionValue[FontSize]===Automatic,
 Switch[OptionValue[ImageSize]
,Full,18
,Large,14
,Medium,12
,Small,10
,_Integer,Max[ 10,Floor[OptionValue[ImageSize]*fontsizefactor]]
,{_Integer,_Integer}, Max[10,Floor[Mean@OptionValue[ImageSize]*fontsizefactor]]
,_,16]
,OptionValue[FontSize]]
},
Graph3D[ VertexList[ig],EdgeList[ig]
,VertexLabels-> "Name",VertexSize->{"Scaled",0.03}
,VertexStyle->OptionValue[VertexStyle]
,VertexLabelStyle->Directive["Helvetica",fontsize,OptionValue[FontColor],Bold]
,EdgeStyle->  If[EdgeList[ig]!= {},MapThread[ Function[{e,c},e-> {c}],{EdgeList[ig], PropertyValue[ig,EdgeWeight]/.signcolor}],None]
,EdgeLabelStyle->None
,EdgeLabels-> None
,ImagePadding->25
,GraphLayout->OptionValue[GraphLayout]
,Background->OptionValue[Background]
,ImageSize->OptionValue[ImageSize]
]]]


(* ::Subsection:: *)
(*Modular organisation from SCCs*)


(* ::Input::Initialization:: *)
SccOrganisation[reg_Graph]:= 
With[{sccs=ConnectedComponents[reg]}, If[ Length[sccs]==1,sccs,TopologicalSort@QuotientGraph[reg,sccs]]]
SccOrganisation[\[Eta]_]:= SccOrganisation@ InteractionGraphSimple[\[Eta]]


(* ::Section:: *)
(*States *)


(* ::Subsection::Initialization:: *)
(*Updating modes*)


(* ::Text::Initialization:: *)
(*The updating mode codifies the state update.  This corresponds to a list of variable lists. States of variables belonging to the same list are updated at the same time. No specific constraint has been set on the variable list but they must occur in the state definition. Usually, the variable lists are mutually disjoint.*)


(* ::Input::Initialization:: *)
Sequential[v_List]:= List/@v
Sequential[v_Symbol]:={{v}}
Sequential[f:BoonType]:= Sequential@Keys[f]


(* ::Input::Initialization:: *)
Parallel[v_List]:={v}
Parallel[v_Symbol]:={{v}}
Parallel[f:BoonType]:= Parallel@Keys[f]


(* ::Subsection::Initialization:: *)
(*State graph computation*)


(* ::Input::Initialization:: *)
GenerateBoolStates[vars_List]:=Sort@Thread[Rule[ vars,#]]&/@Tuples[{False,True},Length[vars]]
GenerateBoolStates::usage="GenerateBoolStates[vars_List] generates a state set with regards to  list of variables, vars. A state is of the form: {v1 \[Rule] (False|True),...,vn \[Rule] (False|True)}."


(* ::Input::Initialization:: *)
EmptySingleAttractor={{{Null}}};
EmptySingleAttractor::usage= "definition of an empty set of attractors."


(* ::Input::Initialization:: *)
StateCompletion::usage="StateCompletion[states_List,vars_List] defines the completion of states by extending the states with 'vars' states while preserving the initial structure of state sets.
Whatever the order of the variables, a state is set in normal form corresponding to a lexicographic order of the variables."
StateCompletion[vars_List]:=GenerateBoolStates[vars]
StateCompletion[EmptySingleAttractor,vars_List]:=List/@GenerateBoolStates[vars]
StateCompletion[states_,{}]:= states
StateCompletion[states_,vars_List]:= 
Flatten[Outer[ #1 \[Union] #2&,GenerateBoolStates[vars], states,1,Max[Depth[states]-3,1]],1]


(* ::Subsubsection:: *)
(*State updating function from a component of a modality.*)


(* ::Input::Initialization:: *)
StateUpdate[\[Eta]_,amodality_, astate_]:= astate/.(Function[var,(var -> _) ->(var -> (( var/.\[Eta])/.astate))]/@ amodality)


(* ::Subsubsection:: *)
(*State graph computation *)


(* ::Input::Initialization:: *)
ModelOf[f_,mode_List]:= ModelOf[f,mode,Union@@mode]
ModelOf[f_, funmode_:Sequential]:= ModelOf[f,funmode@Keys[f], Keys [f]]
ModelOf[f:BoonType,mode_List,agents_List]:= Graph@Union@Flatten[Outer[ Function[{astate,amode}, astate \[DirectedEdge] StateUpdate[f,amode, astate]],Thread[Rule[agents,#]]&/@Tuples[{False,True},Length[agents]],mode,1,1],1]
ModelOf[f:MultiValuedType, mode_List,agents_List]:= 
Graph@Union@Flatten[Outer[ Function[{astate,amode}, astate \[DirectedEdge] StateUpdate[f,amode, astate]],
Thread[Rule[agents,#]]&/@Tuples[  Range[0,#]&/@(agents/.MaxLevels[f])]
,mode,1,1],1]


(* ::Input::Initialization:: *)
CoreStateGraph[\[Eta]_, mode_List,attractors_]:=
Module[{outtrans,trans,att,instates},
att  = attractors;
(* Computation of the transition for each equilibrium *)
trans=outtrans=Union@Flatten[Outer[ Function[{astate,amode}, astate \[DirectedEdge] StateUpdate[\[Eta],amode, astate]], Flatten[attractors,1],mode,1,1],1];
While[outtrans =!= {},
	(* Identify the transitions reaching a state outside the attractors *)
	outtrans= Cases[trans,( _ \[DirectedEdge]e$_)/;\[Not]MemberQ[ Flatten[att,1],e$]];
	(*remove these transition*)
	trans=Complement[trans,outtrans] ;
	(*Source states of these transitions*)
	 instates= outtrans/. (e$_ \[DirectedEdge] _ )-> e$;
	(*remove the attractors having such elements in input *)
	att= DeleteCases[att, a$_/;(a$ \[Intersection] instates =!= {})]
];
(* return a pair composed with the new stategraph and the curated set of attractors. *)
{Graph[trans],att}]
CoreStateGraph::usage="CoreStateGraph[\[Eta],mode,attractors] computes the core state graph of the set with respect to the mode from the attractors. The result is a pair {core state graph, attractors} where the attractors are curated to keep the attractors that does not reach an element outside the attractors."


(* ::Section:: *)
(*Equilibria Computation*)


(* ::Subsubsection:: *)
(*Classical equilibria computation*)


(* ::Text:: *)
(*The equilibria of the state graph corresponds to the sinks (terminal strongly connected components) of the quotient graph of the SCCs.*)


(* ::Input::Initialization:: *)
FindEquilibria[g0_Graph]:= 
With[{integervertexconversion = Association@ MapIndexed[ Function[{val,index},val-> index[[1]]],VertexList[g0]]},
With[{g=Graph[VertexList[g0]/.integervertexconversion,EdgeList[g0]/.integervertexconversion]}, (* Conversion of the vertices to integer to avoid problems with ConnectedComponents*)
With[{sccs=ConnectedComponents[g]}, (* find terminal strongly connected components *)
With[{quotientgraph = QuotientGraph[g,sccs]},
Pick[sccs, Function[{scc},VertexOutDegree[quotientgraph ,scc ]==0]/@sccs]/.AssociationMap[Reverse,integervertexconversion] (* reverse conversion to obtain the original vertices *)
]]]]


(* ::Subsubsection:: *)
(*Modular computation of Equilibria*)


(* ::Text:: *)
(*The computation of the modular equilibria follows the order given by the modular organisation. The states are incrementally generated.*)


(* ::Input::Initialization:: *)
ModularEquilibria[\[Eta]:BoonType]:= ModularEquilibria[\[Eta],SccOrganisation[\[Eta]]]
ModularEquilibria[\[Eta]:BoonType, morganisation_List,funmode_:Sequential]:=Fold[
Function[{attractors,vars},
(* Identification of  the variables whose equilibria have been already fixed. *)
With[{alreadyfixedvars=  Keys[First@First[attractors]]},
(*  Extension of the current set of attractors by adding the new variables and the regulators that have not been treated yet. *)
With[{attractorscompletion=StateCompletion[attractors,Complement[ vars \[Union] FindRegulators[\[Eta],vars],alreadyfixedvars]]},
(* Definition of the state graph according to the state set corresponding to the attractors. *)
With[{stgraphandattractors = CoreStateGraph[\[Eta], funmode[vars],attractorscompletion]},
(* Definition of the quotient graph of attractors *)
With[{attractorstategraph=QuotientGraph[stgraphandattractors[[1]],stgraphandattractors[[2]]]},
(* Flat each attractor corresponding to an attractor of the quotient graph where each vertice is also an attractor to provide a classical structure of attractor. *)
Function[attractorofattractors,Flatten[attractorofattractors,1]]/@FindEquilibria[attractorstategraph] 
]]]]]
(*Initial condition - A single attractor corresponding to an empty state  *)
,EmptySingleAttractor,morganisation]


(* ::Subsubsection:: *)
(*Symbolic computation for sequential mode of steady states.*)


(* ::Input::Initialization:: *)
StableStates[{}, n_:All]:= {}
StableStates[f:BoonType, n_:All]:=With[{eqn= BooleanMinimize[And@@Map[ Function[rule,Equivalent@@ rule],f]]},
With[{boolvars=Keys[f] \[Union]BooleanVariables@Values[f]},
Function[val,{Thread[boolvars -> val]}]/@SatisfiabilityInstances[eqn, boolvars,n ]]];
StableStates[f:MultiValuedType,n_:100]:=  With[{eqn= And@@Function[rule, Keys[rule] == Values[rule]]/@f  \[And] And@@( MaxLevels[f]/.($x_ -> $i_ )->  0 <= $x <= $i)
},Solve[eqn,Keys[f],Integers]]


(* ::Section:: *)
(*Conversion  of a multi-valued to Boolean network*)


(* ::Text:: *)
(*Transform a multi-valued system into a Boolean network. A multi-valued system is a multivalued system of the form { var -> { level -> condtion, ...},...} associating for each level the required condition. level -> True is the default condition if none of the other conditions are satisfied.*)


(* ::Subsection:: *)
(*Functions *)


Clear[MaxLevels]
SetAttributes[MaxLevels,Listable]
MaxLevels[ HoldPattern[var_Symbol-> Piecewise[ which_List,defaultvalue_Integer]]]:=var ->Max@Append[which[[;;,1]],defaultvalue]
MaxLevels[ var_Symbol-> i_Integer]:= var ->i
MaxLevels[i_Integer]:=i
MaxLevels[_]:= Nothing


(* ::Input:: *)
(**)


Clear[GetMode]
GetMode[f_,encoding_,size_]:=With[{ maxlevel=MaxLevels[f]},AssociationMap[Partition[Range@Length@First@encoding[#/.maxlevel][0],UpTo[size]]&,Keys[f]]]


Clear[GetVariables]
GetVariables::usage="GetVariables[\!\(\*
StyleBox[\"expression\",\nFontSlant->\"Italic\"]\)] collect variables of an expression. A variable is an unprotected symbol."
GetVariables[ var_Symbol/;\[Not]MemberQ[Attributes[var],Protected]]:= {var}
GetVariables[_Symbol[exp__]]:=DeleteDuplicates@Flatten@ Map[GetVariables,{exp}]
GetVariables[_]:={}


SupportSeparator="\[LetterSpace]";
Clear[SupportVar];
SupportVar::usage="SupportVar[var,i] define the ith support Boolean variable for encoding a state of the integer variable \!\(\*
StyleBox[\"var\",\nFontSlant->\"Italic\"]\)\!\(\*
StyleBox[\" \",\nFontSlant->\"Italic\"]\)or a list of variables."
SupportVar[var_Symbol, 1]:=var
SupportVar[var_Symbol, i_Integer/;i>1]:= Symbol[ToString[var]<>SupportSeparator<>ToString[i]]
SupportVar[var_,range_List]:= SupportVar[var,#]&/@range


Clear[BoolSingleSwitch]
BoolSingleSwitch::usage="BoolSingleSwitch[\!\(\*
StyleBox[SubscriptBox[\"l\", \"1\"],\nFontSlant->\"Italic\"]\)\!\(\*
StyleBox[\",\",\nFontSlant->\"Italic\"]\)\!\(\*
StyleBox[SubscriptBox[\"l\", \"2\"],\nFontSlant->\"Italic\"]\)\!\(\*
StyleBox[\",\",\nFontSlant->\"Italic\"]\)\!\(\*
StyleBox[\"i\",\nFontSlant->\"Italic\"]\)\!\(\*
StyleBox[\",\",\nFontSlant->\"Italic\"]\)\!\(\*
StyleBox[\"inval\",\nFontSlant->\"Italic\"]\)\!\(\*
StyleBox[\",\",\nFontSlant->\"Italic\"]\)\!\(\*
StyleBox[\"outval\",\nFontSlant->\"Italic\"]\)\!\(\*
StyleBox[\",\",\nFontSlant->\"Italic\"]\)\!\(\*
StyleBox[\"coding\",\nFontSlant->\"Italic\"]\)] select the codes of level \!\(\*SubscriptBox[\(l\), \(1\)]\) such that the \!\(\*SuperscriptBox[\(i\), \(th\)]\) value is inval and the change of this value by outval corresponds to a code of level \!\(\*SubscriptBox[\(l\), \(2\)]\).
PARAMETERS:
\[FilledSmallSquare] \!\(\*SubscriptBox[\(l\), \(1\)]\) : a level (Integer);
\[FilledSmallSquare] \!\(\*SubscriptBox[\(l\), \(2\)]\) : a level (Integer);
\[FilledSmallSquare] i : a position in the binary code profile (Integer);
\[FilledSmallSquare] inval : the initial value;
\[FilledSmallSquare] outval: the modified value (Boolean);
\[FilledSmallSquare] coding: Assocation table associating for each level, its binary representations.
"
BoolSingleSwitch[l1_Integer, l2_Integer,i_Integer,inval:(True|False),outval:(True|False),localencoding_]:= 
With[{b1=Select[localencoding[l1],#[[i]]==inval&],b2=localencoding[l2]},
Select[b1,MemberQ[b2,ReplacePart[#,i-> outval]]&] ]


BoolSingleMatch::usage="BoolSingleSwitch[\!\(\*
StyleBox[SubscriptBox[\"l\", \"1\"],\nFontSlant->\"Italic\"]\)\!\(\*
StyleBox[\",\",\nFontSlant->\"Italic\"]\)\!\(\*
StyleBox[SubscriptBox[\"l\", \"2\"],\nFontSlant->\"Italic\"]\)\!\(\*
StyleBox[\",\",\nFontSlant->\"Italic\"]\)\!\(\*
StyleBox[\"i\",\nFontSlant->\"Italic\"]\)\!\(\*
StyleBox[\",\",\nFontSlant->\"Italic\"]\)\!\(\*
StyleBox[\"inval\",\nFontSlant->\"Italic\"]\)\!\(\*
StyleBox[\",\",\nFontSlant->\"Italic\"]\)\!\(\*
StyleBox[\"outval\",\nFontSlant->\"Italic\"]\)\!\(\*
StyleBox[\",\",\nFontSlant->\"Italic\"]\)\!\(\*
StyleBox[\"coding\",\nFontSlant->\"Italic\"]\)] selects the codes of level l1 such that the \!\(\*SuperscriptBox[\(i\), \(th\)]\) value is \!\(\*
StyleBox[\"inval\",\nFontSlant->\"Italic\"]\) and this value is also \!\(\*
StyleBox[\"outval\",\nFontSlant->\"Italic\"]\) for one code of level l2 at least.
PARAMETERS:
\[FilledSmallSquare] \!\(\*SubscriptBox[\(l\), \(1\)]\) : a level (Integer);
\[FilledSmallSquare] \!\(\*SubscriptBox[\(l\), \(2\)]\) : a level (Integer);
\[FilledSmallSquare] i : a position in the binary code profile (Integer);
\[FilledSmallSquare] inval: the initial expected value;
\[FilledSmallSquare] outval: the modified value (Boolean);
\[FilledSmallSquare] coding: assocation table associating the possible binary representations for each level.
"
BoolSingleMatch[l1_Integer, l2_Integer,i_Integer,inval:(True|False),outval:(True|False),localencoding_]:= 
With[{b1=localencoding[l1],b2=localencoding[l2]},
Select[b1,#[[i]]==inval&& AnyTrue[b2,Function[c,c[[i]]==outval]]&]]


Clear[FilterCodeByMode]
FilterCodeByMode::usage="FilterCodeByMode[coding,mode] filter the coding with regard to a mode by selecting some codes reachable from neighboring levels. 
PARAMETERS:
\[FilledSmallSquare] coding: the code for each variable of the form { <var> \[Rule] <| \!\(\*SubscriptBox[\(code\), \(1\)]\),\[Ellipsis],\!\(\*SubscriptBox[\(code\), \(n\)]\)|>, ...}
\[FilledSmallSquare] mode : description of the mode. The description is based on the position of the variable. For example a Parallel mode on 3 variables is {{1,2,3}} and the Sequential mode is {{1},{2},{3}}."
FilterCodeByMode[code_Association,mode_List]:= 
Module[{currentcode, filteredcodes,previouscode,assoccode},
currentcode=code[0];
assoccode=<| 0-> currentcode|>;
previouscode= currentcode;
Do[
currentcode=ReverseSort[code[level]];
filteredcodes=Function[m,SelectFirst[currentcode,Function[acode,AnyTrue[ m,Function[i,acode[[i]] \[And] MemberQ[ previouscode, ReplacePart[acode,i-> False]]]]],First[currentcode]]]/@mode;
AppendTo[assoccode,level-> Union@filteredcodes ];
previouscode=code[level];
,{level,1, Max@Keys[code]}];
assoccode]


(* ::Subsection:: *)
(*Conversion*)


Clear[Booleanize]
Booleanize::usage="Booleanize[\!\(\*
StyleBox[\"equation\",\nFontSlant->\"Italic\"]\)\!\(\*
StyleBox[\",\",\nFontSlant->\"Italic\"]\)\!\(\*
StyleBox[\"levels\",\nFontSlant->\"Italic\"]\)\!\(\*
StyleBox[\",\",\nFontSlant->\"Italic\"]\)\!\(\*
StyleBox[\"srcencoding\",\nFontSlant->\"Italic\"]\)\!\(\*
StyleBox[\",\",\nFontSlant->\"Italic\"]\)\!\(\*
StyleBox[\"mode\",\nFontSlant->\"Italic\"]\)\!\(\*
StyleBox[\",\",\nFontSlant->\"Italic\"]\)\!\(\*
StyleBox[\"logicalform\",\nFontSlant->\"Italic\"]\)] convert an equation into a set of Boolean equations. 
PARAMETERS
\[FilledSmallSquare] equation: a transition form equation 
\[FilledSmallSquare] levels: a list of all the maximal level including the variables involved in the equation (<| v \[Rule] i ...|>)
\[FilledSmallSquare] srcencoding: the source encoding rule defining how an integer states is encoded.
\[FilledSmallSquare] mode: the mode of the Boolean network,
\[FilledSmallSquare] logicalform: specifies the logical form of the Boolean condition (\"DNF\",\"CNF\",...)"
Booleanize[ varsrc_Symbol->which_,levels_List,allcodes_Association,mode_Association,logicalform_String]:= 
With[{
vars=GetVariables[which], (* variables occuring in the levels conditions *)
 maxlevel= varsrc/.levels, (* maximal level of the source variable *)
allcodessize=Length[allcodes[varsrc][0][[1]]]},(* size of the support for the source variable *)

Module[ {
support=Function[var,SupportVar[var,Range@Length[allcodes[var][0][[1]]]]]/@vars , (* support of all variables occuring in the level conditions *)
varsrcsupport=SupportVar[varsrc,Range[allcodessize]], (* list of Boolean variables that are the support of the assigned variable *)
regstatespace= Tuples[ Range[0,#]&/@(vars/.levels)], (* integer state space of the regulators of the target variable *)
formulas=ConstantArray[False,allcodessize], (* formulas for each support variable *)
tuple\[DoubleStruckCapitalB],(*Boolean code of levels for tuples *)
guard\[DoubleStruckCapitalB], (* Boolean guard *)
trueguardstates,(* integer states leading to activate the current level *)
sourcelevels, (* level of the source {l-1, l, l+1} *)
\[CapitalPsi]01,\[CapitalPsi]10,\[CapitalPsi]11,\[CapitalPsi]\[FivePointedStar]1},
Do[ (* scan of levels for the output variable *)

(* Allowed potential source levels to reach the target level for 1-step multivalued transition where the accessible levels are l-1, l, l+1 *)
sourcelevels=Select[{level-1,level,level+1},0<= # <= maxlevel&];

(* Integer states leading to activate the current level. The guard of the level is true with these states *)
trueguardstates=Select[regstatespace,Function[tuple,(which/.Thread[vars-> tuple]) ==level]];

guard\[DoubleStruckCapitalB]=False;
(* 1) CONVERSION OF STATES SATISFYING THE GUARD CONDITION FOR THE CURRENT LEVEL ----------------------- *)
Do[ (* Scan the states of regulators satisfying the current level condition of the target *)

(* Retrieve the binary code of the state for all regulators. *)
tuple\[DoubleStruckCapitalB]= MapThread[Function[{var,alevel}, allcodes[var][alevel]],{vars,astate}]; 

(* Integrate the new state condition for the current true-tuple in to a formula *)
guard\[DoubleStruckCapitalB] = guard\[DoubleStruckCapitalB] \[Or] And@@MapThread[BooleanMinterms,{tuple\[DoubleStruckCapitalB],support}];

(* The formula is equivalent to the Boolean codes of the levels satifying the guard. if l is encoded by 3 codes Subscript[c, 1],Subscript[c, 2],Subscript[c, 3], the formula is :
 BooleanMinterms(Subscript[c, 1]) \[Or] BooleanMinterms(Subscript[c, 2]) \[Or] BooleanMinterms(Subscript[c, 3]). *)
,{astate,trueguardstates}];

(* 2) ADMISSIBLE INITIAL LEVEL CODES LEADING TO 1 FOR THE TARGET LEVEL ------------------------------- *)
Do[ (* scan of support *)

(* Select the admissible codes of the source levels for the support variable i w.r.t. 3 cases of transitions to reach a code encoding the target level *)

(* CASE 1: 0 \[Rule] 1 *)
\[CapitalPsi]01 =Flatten[BoolSingleSwitch[ #,level,i,False,True, allcodes[varsrc]]&/@sourcelevels,1];

(* CASE 2: 1 \[Rule] 0 *)
\[CapitalPsi]10 = Flatten[ BoolSingleSwitch[#,level,i,True,False, allcodes[varsrc]]&/@sourcelevels,1];

(* CASE 3: 1 \[Rule] 1 *)
\[CapitalPsi]11= Flatten[BoolSingleMatch[#,level,i,True,True, allcodes[varsrc]]&/@sourcelevels,1]; 

(* Define the set of admissible codes *)
\[CapitalPsi]\[FivePointedStar]1=\[CapitalPsi]01 \[Union] Complement[\[CapitalPsi]11,\[CapitalPsi]10];

(* The formula for a support variable is of the form : (condition Subscript[C, l] to reach the level l) \[And] (minterms of admissible codes of source level for the support variable Subscript[y, i]) *)
formulas[[i]]=formulas[[i]] \[Or] (guard\[DoubleStruckCapitalB] \[And]BooleanMinterms[ \[CapitalPsi]\[FivePointedStar]1,varsrcsupport])
,{i,allcodessize}]
,{level,maxlevel}];

(* Boolean network assembly with formulas simplification.*) 
Thread[varsrcsupport-> (BooleanMinimize[#,logicalform]&/@formulas)]
]]


Clear[MultiValuedToBoon]
MultiValuedToBoon[system_List,encoding_Symbol,booleanmode_Association,logicalform_String:"CNF"]:=
With[{levels=MaxLevels[system]},
With[{modebyvars= (* mode of the Noolean network *)
Association@Map[
Function[varlevel,
Keys[varlevel]-> With[{code=encoding[Max[Values[varlevel],1]]},
Switch[booleanmode[Keys[varlevel]]
,Sequential, List/@Range@Length@First@First[code]
,Parallel,{Range@Length@First@First[code]}
,_,booleanmode[Keys[varlevel]]]]], levels],
 onlysequential= AllTrue[booleanmode, MatchQ[#,Sequential | {{_}..}]&]},
With[{allcodes=Association@Map[ Function[{varlevel}, Keys[varlevel]-> 
If[onlysequential
,encoding[Max[Values[varlevel],1]]
,FilterCodeByMode[encoding[Max[Values[varlevel],1]],modebyvars[Keys[varlevel]]]]]
,levels]}, (* codes for each integer variable w.r.t. the mode. If the mode is sequential the complete code is taken *)
$MN2BNCODES=allcodes;
$MN2BNMODE=modebyvars;
Flatten[Function[eq,Booleanize[eq,levels,allcodes,modebyvars,logicalform]]/@system]]]]
MultiValuedToBoon[system_List,encoding_Symbol,logicalform_String:"CNF"]:= MultiValuedToBoon[system,encoding, AssociationMap[ Sequential&,Keys[system]],logicalform]


(* ::Subsection:: *)
(*Integer Coding in Boolean*)


VanHam[n_Integer]:=
Association@Table[ i ->{ Join[ConstantArray[True,i],ConstantArray[False,n-i]]},{i,0,n}]


SummingCode[n_Integer]:=With[{codes=Tuples[{False,True},n]}, Association@Table[i-> Select[codes,Count[#,True]==i&],{i,0,n}]]


(* ::Text:: *)
(*Pour le code de gray, le bit de gauche, ie. 1^er de la liste qui joue le r\[OHat]le du bit de poids fort Subscript[b, 0] dans l'algorithme de calcul du code de Gray. il correspond \[AGrave] la variable \!\(\*OverscriptBox[*)
(*SubscriptBox[\(y\), \(1\)], \(^\)]\) qui correspond a la premi\[EGrave]re de la liste des variables de supports.*)


GrayCode[n_Integer]:= With[{size=Ceiling@Log2[n+1]},
Association@Table[ 
With[{binary=IntegerDigits[i,2,size]/.{0-> False,1-> True}},
 i->{ Prepend[ Table[ binary[[j-1]] \[Xor] binary[[j]],{j,2,size}],binary[[1]]]}],{i,0,n}]]


IntSumming[bprofile:{(True|False)...}]:= Total@Boole[bprofile]
IntSumming[bprofile:{(_Symbol-> (True|False))...}]:=IntSumming/@Values@SplitBy[bprofile,First@StringCases[ToString[#], multivaluedvariable:RegularExpression["[^"<>SupportSeparator<>"]+"]~~___-> multivaluedvariable]&]


IntGray[gcode:{(True|False)...}]:=FromDigits[Boole@FoldList[Function[{bin,gray}, gray \[Xor] bin],gcode],2]
IntGray[gcode:{(_Symbol-> (True|False))...}]:=IntGray/@Values@SplitBy[gcode,First@StringCases[ToString[#], multivaluedvariable:RegularExpression["[^"<>SupportSeparator<>"]+"]~~___-> multivaluedvariable]&]


(* ::Section:: *)
(*Conversion of Boolean Network to ODE*)


BooleanToODE[F_ ,v_Symbol, \[Kappa]_Association,\[Gamma]_Association,\[Theta]_Association, var0_Association, fstep:{_Symbol,_Symbol}]:=Module[{B2O, fneg=fstep[[1]],fpos=fstep[[2]]},
B2O[ network_List]:= Flatten[B2O/@network];
       B2O [x_Symbol->f_]:= {(x'[v]== \[Kappa][x]*B2O[f] -  \[Gamma][x]*x[v]), x[0]==var0[x]};
      B2O[ var_Symbol] :=fpos[var[v],\[Theta][var]];
B2O[\[Not] var_Symbol]:= fneg[var[v], \[Theta][var]];
      B2O[ f1_ \[And] f2_] := B2O[f1]*B2O[f2];
      B2O[f1_ \[Or] f2_]:= B2O[f1]+B2O[f2];
B2O[True]:= 1;
B2O[False]:= 0;
B2O[x_]:=(Message[b2o::nnarg,x];Abort[]);
B2O[F]]


(* ::Section:: *)
(*Conversion to Tikz-Network*)


(* ::Text:: *)
(*Conversion of a network to latex using Tikz-Network*)


Protect[VertexFontSize,EdgeFontSize,ScaleDistance,VertexLabelFunction, EdgeLabelFunction, MathMode];


Clear[TikzNetwork]
Options[TikzNetwork]={Scale->1, VertexShape->Automatic, VertexFontSize->Medium, EdgeFontSize-> Large, ScaleDistance->3.0,MathMode-> False,VertexLabelFunction->Identity,EdgeLabelFunction-> (#/.{Automatic->{},$Failed->{}}&) };
TikzNetwork[G0_Graph, OptionsPattern[]]:= 
Module[{definecolor=<||>,icolor=1, InterpretColor,EdgeStyling, G=G0},
(* Transfer graph highlight style to VertexStyle and EdgeStyle *)
Which[
 MatchQ[AnnotationValue[G,GraphHighlightStyle],{__}],
Scan[Function[annotation, G=Annotate[{G,Keys[annotation]},Values[annotation]]],AnnotationValue[G,GraphHighlightStyle]],
(* Special case where all the vertices are of the same color. In this case GraphHighlightStyle is not filled, but the highlighted vertices are listed in GraphHiglight *)
AnnotationValue[G,GraphHighlightStyle]== Automatic &&  MatchQ[AnnotationValue[G,GraphHighlight],{__}],
G=Annotate[{G,AnnotationValue[G,GraphHighlight]},VertexStyle->Directive[RGBColor[0.79, 0.16, 0],EdgeForm[{RGBColor[0.79, 0.16, 0],Opacity[1]}]]],
True, Null ];
(* Color interpreter *)
InterpretColor[xcolor_]:= 
Switch[xcolor
,_RGBColor,Lookup[definecolor,xcolor, AssociateTo[definecolor,xcolor->"color"<>ToString[icolor++]];definecolor[xcolor]]
,_GrayLevel,Lookup[definecolor,xcolor, AssociateTo[definecolor,xcolor->"color"<>ToString[icolor++]];definecolor[xcolor]]
, _Hue,InterpretColor@ColorConvert[xcolor,"rgb"]
,Directive[___,_GrayLevel,___],InterpretColor@FirstCase[xcolor,_GrayLevel]
,Directive[___,_RGBColor,___],InterpretColor@FirstCase[xcolor,_RGBColor]
,Directive[___,_Hue,___],InterpretColor@FirstCase[xcolor,_Hue]
,_,"{}"
];
EdgeStyling[Automatic]:=1.; (* Interpret the style of the edges - limited to Edge Thickness *)
EdgeStyling[{___,Thickness[value_Real],___}]:=250*value;
EdgeStyling[{___,Thickness[value_Symbol],___}]:= <| Tiny-> 0.25,Small->0.5,Medium-> 1.,Large->2.|>[value];
EdgeStyling[{Directive[___,Thickness[value_Real],___]}]:=250*value;
EdgeStyling[{Directive[___,Thickness[value_Symbol],___]}]:= <| Tiny-> 0.25,Small->0.5,Medium-> 1.,Large->2.|>[value];
EdgeStyling[_]:= 1.;
With[{
header=ToString@StringForm["\\begin{tikzpicture}[scale=`1`]\n",OptionValue[Scale]],
closer="\\end{tikzpicture}",
  boolsymbol=<|True->"true",False->"false"|>,
  fontsize=<|Tiny->"\\tiny", Script-> "\\scriptsize",FootNote->"\\footnotesize",Small->"\\small", Medium->"\\normalsize", Large->"\\large"|>,
shape=<|Circle->"circle",Rectangle->"rectangle",Triangle->"triangle",Diamond->"diamond",Star->"star", None->"rectangle, LineColor=white",{"Circle"}->"circle",{"Rectangle"}->"rectangle",{"Square"}->"rectangle",{"Triangle"}->"triangle",{"Diamond"}->"diamond",{"Star"}->"star",Automatic->"circle"|>,
colortype=<|RGBColor->"rgb",GrayLevel->"gray"|>,
coordinates=AssociationThread[VertexList[G]->First@Values@AbsoluteOptions[G,VertexCoordinates]]
},
(* Get vertex information Format: {"id","label","color","x","y","Math Mode"} *)
With[{contentvert=
Function[v,{v, 
(* math mode label *)
OptionValue[VertexLabelFunction][v],
(* coordinates *)
NumberForm[Chop[coordinates[v][[1]],10^-2],{6,2}],NumberForm[Chop[coordinates[v][[2]],10^-2],{6,2}],
(* node color *)
InterpretColor[AnnotationValue[{G,v},VertexStyle]],
(* is math mode enabled *)
 boolsymbol[OptionValue[MathMode]]
 }]/@VertexList[G],
(* Get edge information Format: {"u","v","label","color", "bend","Direct"}*)
contentedges= 
Function[e,
{
(*edges*)
e[[1]],e[[2]],
(* label*)
OptionValue[EdgeLabelFunction][AnnotationValue[{G,e},EdgeWeight]],
(* color *)
InterpretColor[AnnotationValue[{G,e},EdgeStyle]],
(*bending*)
If[MemberQ[EdgeList[G],e[[2]]\[DirectedEdge]e[[1]]],30,0], 
(* oriented or not *)
boolsymbol[MatchQ[e,_DirectedEdge]],
(* math mode*)
boolsymbol[OptionValue[MathMode]]
}]/@EdgeList[G]},
(* Assembly*)
header
<> (* Color definition *)
StringJoin[KeyValueMap[Function[{color,name},"\\definecolor{"<>name<>"}{"<>colortype[color[[0]]]<>"}"<>ToString[List@@N[color]]<>"\n"],definecolor]]
<> (* Vertex style *)
ToString@StringForm["\\SetVertexStyle[FillColor=white,MinSize=0.8cm,LineWidth=1.25pt, Shape=`1`, TextFont=`2`]\n",
  If[MatchQ[OptionValue[VertexShape],Automatic],AnnotationValue[G,VertexShapeFunction],OptionValue[VertexShape]]/.shape,
  fontsize[OptionValue[VertexFontSize]]]
<> (* Edge style *)
ToString@StringForm["\\SetEdgeStyle[TextFont=`1`,LineWidth=`2`] \\SetDistanceScale{`3`}\n",
fontsize[OptionValue[EdgeFontSize]],EdgeStyling[AnnotationValue[G,EdgeStyle]],OptionValue[ScaleDistance]]
<> (* Vertices *)
"%% Vertices ------\n"<>
StringJoin[Function[vertspec,ToString@StringForm[ "\\Vertex[x=`3`, y=`4`, color=`5`, Math=`6`, label=`2`]{`1`}\n",Sequence@@vertspec]]/@contentvert]
<> (* Edges *)
"%% Edges ---------\n"<>
StringJoin[Function[edgespec,ToString@StringForm[ "\\Edge[label=`3`, color=`4`, bend=`5`, Direct=`6`, Math=`7`](`1`)(`2`)\n",Sequence@@edgespec]]/@contentedges]
<>closer 
]]]


(* ::Section:: *)
(*Random Boolean Network*)


MonotoneDNF::usage="MonotoneDNF[f, probtrue:0.5] transform a DNF boolean formula f into a monotone Boolean formula. probtrue is the probability that the variable occurs positively."
MonotoneDNF[f_, probtrue_:0.5]:= (f/.\[Not]$x_-> $x)/.
Function[v,RandomChoice[ConstantArray[v-> v,Round[10 probtrue]] ~Join~ ConstantArray[ v->!v,10 - Round[10 probtrue]]]]/@BooleanVariables[f]


SetAttributes[IntegerToSymbol,Listable]
IntegerToSymbol::usage="IntegerToSymbol[number,string] Generate a symbol of the form <string><number>. Default string \"a$\"." 
IntegerToSymbol[i_,symbol_String:"a$"]:= Symbol[symbol<>ToString[i]]


Options[RandomBooleanNetwork]={ Method->BarabasiAlbertGraphDistribution, Monotone -> True};
RandomBooleanNetwork[nagents_Integer,k_List, self_Real:0.,probtrue_Real:0.5, prefix_String:"x",OptionsPattern[]]:= 
With[{
interactiongraph=Graph[Function[edge,
RandomChoice[{edge[[1]] \[DirectedEdge] edge[[2]],edge[[2]]\[DirectedEdge]edge[[1]]}]] (* fix the edge orientation randomly *)
/@EdgeList@RandomGraph[OptionValue[Method][nagents, Sequence@@k]]]}, (* Generation of an undirected random graph *)
 Sort@Function[v, (* convert the interaction graph into a random Boolean network *)
With[{neighbors=If[RandomReal[]< self,Identity,DeleteCases[#,v]&]@VertexInComponent[interactiongraph,{v},1]},
With[{f=BooleanFunction[ RandomInteger[{0,2^2^Length[neighbors]-1}],IntegerToSymbol[neighbors,prefix]]},
IntegerToSymbol[v,prefix]->If[OptionValue[Monotone], MonotoneDNF[f,probtrue],f]]]]/@VertexList[interactiongraph]]


(* ::Section:: *)
(*End of the package*)


(* ::Input::Initialization:: *)
End[];


(* ::Input::Initialization:: *)
EndPackage[]
