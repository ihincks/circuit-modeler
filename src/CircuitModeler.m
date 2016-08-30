(* ::Package:: *)

BeginPackage["CircuitModeler`",{"SystemsOfEquations`"}];


(* ::Section::Closed:: *)
(*Circuit Elements*)


(* ::Subsection:: *)
(*Usage Declarations*)


Circuit::usage = "Circuit[element1, element2, ...] is a container to hold a sequence of elements like Resistor and Capacitor.";


(* ::Text:: *)
(*Note that only 2-node elements are allowed at this time.*)


Resistor::usage = "Resistor[node1, node2, symbol, R] represents a resistor from node1 to node2 of resistance R. Nodes can be basically anything, but it is recommended that you use numbers or undefined symbols.";
Capacitor::usage = "Capacitor[node1, node2, symbol, C] represents a capacitor from node1 to node2 of capacitance C. Nodes can be basically anything, but it is recommended that you use numbers or undefined symbols.";
Inductor::usage = "Resistor[node1, node2, symbol, L] represents an inductor from node1 to node2 of inductance L. Nodes can be basically anything, but it is recommended that you use numbers or undefined symbols.";


Source::usage = "Source[node1, node2, symbol] represents a source from node1 to node2. A source essentially adds one independent variable to your system of equations. More precisely, it adds two variables, current and voltage, and one equation. Nodes can be basically anything, but it is recommended that you use numbers or undefined symbols.";


CNode::usage = "CNode[element, n_] returns the n'th node of the given element.";
CNodes::usage = "CNodes[element] returns a list of all nodes of the given element.";
CSign::usage = "CSign[element, node] returns 1 if node is the first node of the element, -1 if it is the second, and fails otherwise.";
CSymbol::usage = "CSymbol[element] returns the symbol of the given element.";
CValue::usage = "CValue[element] returns the value of the given element.";


ConstitutiveEquation::usage = "ConstitutiveEquation[element, i, v, t]";
LaplaceConstitutiveEquation::usage = "LaplaceConstitutiveEquation[element, i, v, s]";


(* ::Subsection:: *)
(*Implementations*)


Begin["`Private`"];


CNode[element_, n_]:=element[[n]];
CNodes[element_]:=List@@element[[{1,2}]]
CSign[element_,node_]:=Which[CNode[element,1]===node,1,CNode[element,2]===node,-1,True,$Failed[element,node]]
CSymbol[element_]:=element[[3]]
CValue[element_]:=element[[4]]


ConstitutiveEquation[element_Resistor,i_Symbol,v_Symbol,t_Symbol]:=v[CSymbol@element,t]==CValue[element]*i[CSymbol@element,t]
ConstitutiveEquation[element_Capacitor,i_Symbol,v_Symbol,t_Symbol]:=D[CValue[element]*v[CSymbol@element,t],t]==i[CSymbol@element,t]
ConstitutiveEquation[element_Inductor,i_Symbol,v_Symbol,t_Symbol]:=v[CSymbol@element,t]==D[CValue[element]*i[CSymbol@element,t],t]


ConstitutiveEquation[element_Source,i_Symbol,v_Symbol,t_Symbol]:={};


LaplaceConstitutiveEquation[element_Resistor,i_Symbol,v_Symbol,s_Symbol]:=v[CSymbol@element,s]==CValue[element]*i[CSymbol@element,s]
LaplaceConstitutiveEquation[element_Capacitor,i_Symbol,v_Symbol,s_Symbol]:=v[CSymbol@element,s]==(1/(s*CValue[element]))*i[CSymbol@element,s]
LaplaceConstitutiveEquation[element_Inductor,i_Symbol,v_Symbol,s_Symbol]:=v[CSymbol@element,s]==s*CValue[element]*i[CSymbol@element,s]


LaplaceConstitutiveEquation[element_Source,i_Symbol,v_Symbol,s_Symbol]:={};


End[];


(* ::Section::Closed:: *)
(*Utility Functions*)


(* ::Subsection:: *)
(*Usage Declarations*)


AllCycles::usage = "AllCycles[vertexPairs_] returns a list of all simple cycles in the graph defined by the given list of vertex pairs.";


DifferentiateIfIntegral::usage = "DifferentiateIfIntegral[left\[Equal]right,t] differentiates both sides differentiates both sides by t until the resulting expression no longer contains an integral. Warning -- no infinite recursion protection.";


GetNodeElements::usage = "GetNodeElements[circuit_Circuit, node(s)] returns all elements of the circuit connected to the given node, or all nodes in the given list of nodes.";


(* ::Subsection:: *)
(*Implementations*)


Begin["`Private`"];


(* ::Text:: *)
(*Brute force simple cycle finder by Mr.Wizard (http://mathematica.stackexchange.com/questions/9434/finding-elementary-cycles-of-directed-graphs).*)
(*Still not convinced there's no built in thing that does this, but I can't find it.*)
(*If speed becomes an issue, we can think about that later.*)


AllCycles[el_]:=Module[
	{f,edges=Join[Rule@@@el,Rule@@@(Reverse/@el)]//Dispatch,allperms,out},
	(* We exploit pattern matching along with ReplaceList in a clever way *)
	f[x_,b___,x_]:={{x,b,x}};
	f[___,x_,___,x_]={};
	f[c___,v_]:=Join@@(f[c,v,#]&/@ReplaceList[v,edges]);
	allperms=Join@@f/@Union@@el;
	(* Now we just need to decide which cycles are equal *)
	out=DeleteDuplicates[RotateLeft[#,Ordering[#,1]-1]&/@Most/@#]&[allperms];
	out=DeleteDuplicates[out,((Length[#1]==Length[#2])&&(Length[#1]==Length[Union[#1,#2]]))&];
	out
]


DifferentiateIfIntegral[left_==right_,t_]:=If[Not[FreeQ[{left,right},Integrate]],DifferentiateIfIntegral[D[left,t]==D[right,t],t],left==right]


GetNodeElements[circuit_Circuit,nodes_List]:=With[
	{hasAllNodes=Function[{element}, And@@(MemberQ[CNodes[element],#]&/@nodes)]},
	Cases[circuit, _?hasAllNodes]
]
GetNodeElements[circuit_, node_]:=GetNodeElements[circuit, {node}]


End[];


(* ::Section:: *)
(*Drawing Functions*)


(* ::Subsection:: *)
(*Usage Declarations*)


CircuitGraph::usage = "CircuitGraph[circuit] displays a circuit as a graph. This is useful mainly for reminding onesself of node labels, as the graph produced is not a proper-looking electrical network.";


NicePrint::usage = "NicePrint[expr]";


SParamsPlot::usage = "SParamsPlot[S_,reps_,s_,{fmin_,fmax_},fun_:Abs,grid_:False,opts:OptionsPattern[Plot]] plots the S Parameters S with independent variable s, after relpacing S with reps, on the frequency range fmin to fmax. The argument fun lets you run a function on the S parameters before plotting, like Abs, or Log10[Abs[#]]&.";


(* ::Subsection:: *)
(*Implementations*)


Begin["`Private`"];


CircuitGraph[circuit_Circuit]:=Module[
	{edges, uniqueEdges, repr},
	edges=List@@(Labeled[DirectedEdge@@CNodes[#],CSymbol[#]]&/@circuit);
	uniqueEdges=Labeled[#[[1,1]],repr@#[[All,2]]]&/@GatherBy[edges, First@#&];
	repr[symbols_]:=StringDrop[StringJoin[ToString[#]<>", "&/@symbols],{-2,-1}];
	Graph[uniqueEdges,VertexLabels->"Name"]
]


CircuitGraph[circuit_Circuit]:=Module[
	{edges, repr},
	repr[symbols_]:=StringDrop[StringJoin[ToString[#]<>", "&/@symbols],{-2,-1}];
	edges=List@@({Rule@@CNodes[#],ToString@CSymbol[#]}&/@circuit);
	edges=GatherBy[edges, First@#&];
	(* There is a bug in GraphPlot; it seems that only one multiedge can be labeled *)
	(* This workaround combines the labels from all multiedges between the same two vertices *)
	edges=If[Length@#==1,
		#[[1]],
		Sequence@@RotateLeft[{{#[[1,1]],repr@#[[All,2]]},Sequence@@#[[2;;-1,1]]},Round[Length@#/2]]
	]&/@edges;
	
	GraphPlot[edges,VertexLabeling->True,DirectedEdges->True,MultiedgeStyle->1/2]
]


NicePrint[expr_]:=TraditionalForm[
	expr/.{
		v_?(MemberQ[{i,v},#]&)[s_,n_,t_]:>If[n>0,Derivative[n][Subscript[v,s]][t],Subscript[v,s][t]],
		v_?(MemberQ[{i,v},#]&)[s_,t_]:>Subscript[v,s][t]
	}
];


SParamsPlot[S_,reps_,s_,{fmin_,fmax_},fun_:Abs,grid_:False,opts:OptionsPattern[Plot]]:=Module[
	{labels},
	labels=Table[Subscript["S",ToString[i]<>ToString[j]],{i,Length@S},{j,Length@S}];
	If[grid,
		Grid[Table[		
			Plot[Evaluate[fun@S[[i,j]]/.Append[reps,s->I*f*2*\[Pi]]],{f,fmin,fmax},PlotLabel->labels[[i,j]],opts],
			{i,Length@S},{j,Length@S}
		]],
		labels=Flatten@Table[Subscript["S",ToString[i]<>ToString[j]],{i,Length@S},{j,Length@S}];
		Plot[Evaluate[fun@Flatten@S/.Append[reps,s->I*f*2*\[Pi]]],{f,fmin,fmax},PlotLegends->Flatten@labels,opts]
	]
]


End[];


(* ::Section::Closed:: *)
(*Modeler*)


(* ::Subsection:: *)
(*Usage Declarations*)


CVerbose::usage = "An option for modeler functions which when set to True enables verbocity.";


KirchhoffsLaws::usage = "KirchhoffsLaws[circuit_Circuit, i_Symbol, v_Symbol] returns {voltageEquations, currentEquations} where voltageEquations and currentEquations are lists of equations that the voltages, v, and the currents, i, have to satisfy according to Kirchhoff's two circuit laws.";


CircuitEquation::usage = "CircuitEquation[circuit_Circuit, termOfInterest, i, v, t, order] attempts to find a system of differential equations relating the given term of interest. Order is sort of a nuisance argument; it should be an integer specifying how many times to differentiate all the starting equations before trying to reduce to the final differential equation. For a resistor network this is 0, for an RLC circuit, this is 1, for an RLC with matching capacitor, it is 2, etc.";


LaplaceCircuitEquation::usage = "LaplaceCircuitEquationcircuit_Circuit, solveFor_, inTermsOf_, i_, v_, s_] attempts to find a system of equations relating the given term of interest.";


(* ::Subsection:: *)
(*Options*)


Options[CircuitEquation]={CVerbose->False};


Options[LaplaceCircuitEquation]={CVerbose->False,EliminationOrder->\[Infinity],Simplify->True};


(* ::Subsection:: *)
(*Implementations*)


Begin["`Private`"];


KirchhoffsLaws[circuit_Circuit,i_Symbol,v_Symbol]:=Module[
	{edges,nodes,cycles,KCL,KVL,voltageSum,currents,voltages},

	(* Find the circuit's graph properties *)
	edges=List@@(CNodes/@circuit);
	nodes=Union@@edges;
	cycles=AllCycles[edges];

	(* First apply KCL at each node *)
	KCL=Table[
		Sum[CSign[element,node]*Subscript[i,CSymbol[element]], {element,GetNodeElements[circuit, node]}]==0,
		{node,nodes}
	];

	(* Now apply KVL, a bit more complicated *)
	voltageSum[signedElements__]:=Sum[
		With[{node=First@selem,elem=Last@selem},
			CSign[elem,node]*Subscript[v,CSymbol[elem]]
		],
		{selem,{signedElements}}
	]==0;
	KVL=Flatten@Table[
		(* Some node pairs will match multiple elements; we need to use KLV 
		on all possible combinations of such occurences, hence Outer. *)
		Outer[voltageSum,##,1]&@@Table[
			(* Need to store the first element of the node pair in the 
			current cycle since it will determine the sign of the voltage 
			drop across the corresponding element *)
			{First@nodePair,#}&/@GetNodeElements[circuit,nodePair],
			{nodePair,Thread[{cycle,RotateLeft[cycle,1]}]}
		],
		{cycle,cycles}
	];

	(* Mathematica Magic *)
	(* Reduce away redundant equations, combine equations, etc. *)
	(* This always seems to result in Length[circuit] total equations...probably not a coincidence. *)
	currents=List@@(Subscript[i,#]&/@CSymbol/@circuit);
	voltages=List@@(Subscript[v,#]&/@CSymbol/@circuit);
	KCL=Reduce[KCL, currents];
	KVL=Reduce[KVL, voltages];

	(* Join all equations into one big list *)
	KCL=If[Head[KCL]===And, List@@KCL, {KCL}];
	KVL=If[Head[KVL]===And, List@@KVL, {KVL}];
	{KCL, KVL}
]


CircuitEquation[circuit_Circuit,termsOfInterest_,i_,v_,t_,order_,OptionsPattern[]]:=Module[
	{VPrint,currentEqns,voltageEqns,constitutiveEqns,raiseOrder,eqns,variables,toiList,elimList},
	
	VPrint = If[OptionValue[CVerbose],Print[#]]&;

	VPrint["Analysing circuit with "<>ToString[Length@circuit]<>" elements..."];

	(* Get all of the equations from Kirchhoff's two circuit laws *)
	(* We are using the notation i[symb,n,t] to refer to the n'th time derivative *)
	{currentEqns,voltageEqns}=KirchhoffsLaws[circuit,i,v]/.{Subscript[var_,symb_]:>var[symb,t]};
	VPrint["# Kirchhoff equations: "<>ToString[Length[currentEqns~Join~voltageEqns]]];

	(* Make a list of the constitutive equations *)
	constitutiveEqns=Flatten[List@@(ConstitutiveEquation[#,i,v,t]&/@circuit)];
	VPrint["# Constitutive equations: "<>ToString[Length[constitutiveEqns]]];

	(* All equations together *)
	eqns=Join[currentEqns,voltageEqns,constitutiveEqns];

	(* Just differentiate both sides... *)
	raiseOrder[left_==right_]:=(D[left,t]==D[right,t]);
	raiseOrder[eqnList_List]:=raiseOrder/@eqnList;

	(* Loop through and make sure there are no integrals *)
	Table[
		eqns[[n]]=DifferentiateIfIntegral[eqns[[n]],t],
		{n,Length@eqns}
	];

	(* Differentiate all equations order times. *)
	eqns=Flatten[NestList[raiseOrder,eqns,order]];
	VPrint["# augmented equations: "<>ToString[Length[eqns]]];

	(* The Eliminate function doesn't work well with derivatives, so replace by symbols *)
	eqns=eqns/.{
		Derivative[0,n_][i][s_,t]:>i[s,n,t],
		Derivative[0,n_][v][s_,t]:>v[s,n,t],
		i[s_,t]:>i[s,0,t],
		v[s_,t]:>v[s,0,t]
	};

	(**)
	variables=DeleteDuplicates@Cases[eqns,Alternatives[i[__],v[__]],Infinity];
	toiList=DeleteDuplicates@Cases[eqns,Alternatives@@termsOfInterest,Infinity];
	elimList=SetDifference[variables,toiList];
	VPrint["# augmented variables: "<>ToString[Length[variables]]];
	VPrint["# variables to keep: "<>ToString[Length@toiList]];
	VPrint["# variables to eliminate: "<>ToString[Length@elimList]];

	EliminateIfPossible[eqns,toiList,elimList,Simplify->True]
]


LaplaceCircuitEquation[circuit_Circuit,solveFor_,inTermsOf_,i_,v_,s_,OptionsPattern[]]:=Module[
	{VPrint,currentEqns,voltageEqns,variables,constitutiveEqns,elimList,eqns,soln,elimOrder,Simp},
	
	VPrint = If[OptionValue[CVerbose],Print[#]]&;

	(* Get all of the equations from Kirchhoff's two circuit laws *)
	(* We are using the notation i[symb,n,t] to refer to the n'th time derivative *)
	{currentEqns,voltageEqns}=KirchhoffsLaws[circuit,i,v]/.{Subscript[var_,symb_]:>var[symb,s]};
	variables=Flatten[{i[CSymbol@#,s],v[CSymbol@#,s]}&/@(List@@circuit)];
	VPrint["Kirchhoff: "<>ToString[Length[currentEqns~Join~voltageEqns]]<>" equations"];
	VPrint["Kirchhoff: "<>ToString[Length[variables]]<>" unknowns"];

	(* Make a list of the constitutive equations *)
	constitutiveEqns=Flatten[List@@(LaplaceConstitutiveEquation[#,i,v,s]&/@circuit)];
	VPrint["Constitutive: "<>ToString[Length[constitutiveEqns]]<>" equations"];

	(* All equations together *)
	eqns=Join[currentEqns,voltageEqns,constitutiveEqns];

	(* Things we want to eliminate from the equations *)
	elimList=SetDifference[variables,Join[EquationListForm@solveFor,EquationListForm@inTermsOf]];

	(* Partition elimList into chunks of size EliminationOrder *)
	elimOrder=Min[OptionValue[EliminationOrder],Length@elimList];
	elimList=With[{part=Partition[elimList,elimOrder]},
		Select[Append[part,elimList[[Length@Flatten@part-Length@elimList;;-1]]],Length@#>0&]
	];

	Simp=If[OptionValue[Simplify],Simplify,Identity];

	(* Eliminate and solve *)
	eqns=Fold[Simp@Eliminate[#1,#2]&,eqns,elimList];
	soln=Solve[eqns,solveFor];
	If[Length[soln]>0,
		First@soln,
		$Failed
	]
]


End[];


(* ::Section:: *)
(*Scattering Parameters*)


(* ::Subsection:: *)
(*Usage Declarations*)


ScatteringParameters::usage = "ScatteringParameters[circuit_Circuit,ports,Z0,s] finds the scattering parameters of the given linear circuit assuming that the impedance, Z0, is the same for all ports. As a usage note, *don't* include the impedances or sources in the input circuit. The input ports should be a list of tuples specifying the nodes you want to use for a given port.";
SolveForExtraElements::usage = "Option to ScatteringParameters. If specified, ScatteringParameters will return a list whose first element is the S-parameter matrix and whose second element is a matrix of lists of replacement rules for the given circuit elements.";


(* ::Subsection:: *)
(*Options*)


Options[ScatteringParameters] = Union[Options[LaplaceCircuitEquation], {
	SolveForExtraElements -> None,
	VoltageSymbol -> V,
	CurrentSymbol -> J,
	PortSymbol -> Port
}];


(* ::Subsection:: *)
(*Implementations*)


Begin["`Private`"];


ScatteringParameters[circuit_Circuit,ports_,Z0_,s_,opt:OptionsPattern[ScatteringParameters]]:=Module[
	{
		augmentedCircuit,
		P,nodej,Rj,eqns,reps, (* Port symbol, circuit equations, and solution replacements *)
		J,V, (* Current, Voltage and Laplace domain variable. *)
		Vj,Jj,Vi,Ji,
		S,
		extraSolutions,
		extraEqn, lceOpts,
		eJ, eV, eP
	},
	(* When we pass options to LaplaceCircuitEquation, we must strip out options that functio ndoes not recognize. *)
	lceOpts = Sequence @@ FilterRules[{opt}, Options[LaplaceCircuitEquation]];
	
	(* Scattering matrix *)
	S=ConstantArray[0,{Length@ports,Length@ports}];

	(* Make something to hold extra solutions. *)
	extraSolutions = ConstantArray[{}, {Length @ ports}];
	eJ = OptionValue[CurrentSymbol];
	eV = OptionValue[VoltageSymbol];
	eP = OptionValue[PortSymbol];

	(* Calculate one column at a time, because they have the same circuit in common. *)
	Table[
		(* Put source in series with a Z0 resistor on port j, and a Z0 resistor on every other port *)
		augmentedCircuit=Join[
			circuit,
			Circuit@@Flatten@Table[
				If[j==i,
					(*{Resistor[nodej, ports[[i,1]],Rj,Z0], Source[ports[[i,2]], nodej, P[i]]},*)
					Source[Sequence@@ports[[i]],P[i]],
					Resistor[Sequence@@ports[[i]],P[i],Z0]
				],
				{i,Length@ports}
			]
		];

		(* We will find all of Vj, Jj, Vi, Vj in terms of Jj so that Jj will cancel out in the defn of Sij *)
		(*Vj=(Z0*J[P[j],s]-V[P[j],s])/.LaplaceCircuitEquation[augmentedCircuit,V[P[j],s],J[P[j],s],J,V,s, lceOpts];*)
		Vj=(V[P[j],s])/.LaplaceCircuitEquation[augmentedCircuit,V[P[j],s],J[P[j],s],J,V,s, lceOpts];
		Jj=J[P[j],s];

		Table[
			If[i!=j,
				Vi=V[P[i],s]/.LaplaceCircuitEquation[augmentedCircuit,V[P[i],s],J[P[j],s],J,V,s,lceOpts];
				Ji=J[P[i],s]/.LaplaceCircuitEquation[augmentedCircuit,J[P[i],s],J[P[j],s],J,V,s,lceOpts];
				S[[i,j]] = (Vi+Z0*Ji)/(Vj-Z0*Jj);
			];,
			{i,Length@ports}
		];
	
		If[OptionValue[SolveForExtraElements] =!= None,
			extraSolutions[[j]] = Flatten @ Table[
				{
					LaplaceCircuitEquation[augmentedCircuit, eV[elem, s], eJ[P[j], s], eJ, eV, s, lceOpts],
					LaplaceCircuitEquation[augmentedCircuit, eJ[elem, s], eJ[P[j], s], eJ, eV, s, lceOpts]
				},
				{elem, OptionValue[SolveForExtraElements]}
			]
		];		
		S[[j,j]] = (Vj+Z0*Jj)/(Vj-Z0*Jj);	
		,
		{j,Length@ports}
	];

	If[OptionValue[SolveForExtraElements] =!= None,
		{Simplify @ S, Simplify @ (extraSolutions /. P -> eP)},
		Simplify@S
	]

]


End[];


(* ::Section::Closed:: *)
(*Nonlinear Scattering Parameters*)


(* ::Subsection:: *)
(*Usage Declarations*)


SingleParameterThresholdStoppingCriteria::usage = "SingleParameterThresholdStoppingCriteria[\[Epsilon]] returns a function which takes arguments [{thisSymb->thisVal},{prevSymb->prevVal} and returns True iff Abs[thisVal-prevVal]<\[Epsilon].";
NormParameterThresholdStoppingCriteria::usage = "NormParameterThresholdStoppingCriteria[\[Epsilon]] returns a function which takes arguments [{thisSymb1->thisVal1,...},{prevSymb1->prevVal1,...} and returns True iff Norm[{thisVal1-prevVal1,...}]<\[Epsilon].";
ScaledNormParameterThresholdStoppingCriteria::usage = "ScaledNormParameterThresholdStoppingCriteria[\[Epsilon],symb1->scale1,...] returns a function which takes arguments [{symb1->thisVal1,...},{symb1->prevVal1,...} and returns True iff Norm[{(thisVal1-prevVal1)/(scale1),...}]<\[Epsilon].";


DragIterationTransformation::usage = "DragIterationTransformation[drag] returns a function ";


SelfConsistentSParams::usage = "";


(* ::Subsection:: *)
(*Options*)


MinIterations::usage = "An option for non-linear modeler functions specifying the minimum number of iterations to use.";
PostIterationTransformation::usage = "An option for non-linear modeler functions specifying a transformation to apply after each iteration step. Consider using #1& (default), or DragIterationTransformation.";


Options[SelfConsistentSParams]={
	MinIterations->1,
	MaxIterations->10000,
	PostIterationTransformation->(#1&)
};


(* ::Subsection:: *)
(*Messages*)


SelfConsistentSParams::notnum="Not all symbols replaced by replacements. Something is very likely wrong.";


(* ::Subsection:: *)
(*Implementations*)


Begin["`Private`"];


SingleParameterThresholdStoppingCriteria[\[Epsilon]_][{_->prev_},{_->this_}]:=Abs[this-prev]<\[Epsilon];


NormParameterThresholdStoppingCriteria[\[Epsilon]_][{thisRules__},{prevRules__}]:=With[{syms={thisRules}[[All,1]]},Norm[(syms/.{thisRules})-(syms/.{prevRules})]<\[Epsilon]];


ScaledNormParameterThresholdStoppingCriteria[\[Epsilon]_,scales__][{thisRules__},{prevRules__}]:=With[{syms={thisRules}[[All,1]]},
	Norm[Table[
		((sym/.{thisRules})-(sym/.{prevRules}))/(sym/.{scales}),
		{sym,syms}
	]]<\[Epsilon]
];


SelfConsistentSParams[
	circuit_Circuit,ports_,RL_,inputPower$dBm_,replacements_,J_,V_,s_,{ss__},
	nonlinearSymbols_,dependentElements_,iterationExpression_,stoppingCriteria_,
	opts:OptionsPattern[]]:=Module[
		{prev,prog,this,S,Sequations,extraEqns,Port,idx$j,idx$s,Siter,iterCount,power$W,portCurrent,cur$s},
		prog="...";
		Print@Dynamic@prog;

		(* Calculate the power on each port and translate that into a current. *)
		power$W = 10^((inputPower$dBm/10)-3);
		portCurrent=Sqrt[power$W/RL];

		(* Get the analytic form of the linear S-parameters along with the current and potential for the dependent circuit elements. *)
		prog="Calculating analytic form of S for linear case...";
		{Sequations,extraEqns}=ScatteringParameters[circuit,ports,RL,s,SolveForExtraElements->dependentElements,CurrentSymbol->J,VoltageSymbol->V,PortSymbol->Port];

		(* Make somewhere to hold an array for S. We want there to be a different S matrix for each value of the Laplace-domain parameter s. *)
		S=ConstantArray[0,{Length @ {ss},Length @ ports, Length@ports}];

		(*
			Now we loop over values of the Laplace-domain parameter s and input ports j.
			At each s and j, we iteratively update dependent circuit elements.
		*)
		Table[
			iterCount=0;
			prev = None;
			this =nonlinearSymbols;
			cur$s={ss}[[idx$s]];
			While[prev === None || iterCount <OptionValue[MinIterations]||(\[Not]stoppingCriteria[prev,this]&&iterCount<OptionValue[MaxIterations]),
				iterCount++;
				prog="idx$s == " <> ToString@N[idx$s] <> ", j == " <> ToString[idx$j] <>", Iteration " <> ToString[iterCount]<>"...\nCurrent state: "<>ToString[this];
				prev =this;
				this=(iterationExpression/.extraEqns[[idx$j]]) ;
				this[[All,2]]=this[[All,2]]/.J[Port[idx$j],s]->portCurrent;
				this[[All,2]]=this[[All,2]]/.prev/.replacements;
				this[[All,2]]=this[[All,2]]/.s->cur$s;
				this=OptionValue[PostIterationTransformation][this,prev];
				If[
					\[Not]And@@NumericQ/@this[[All,2]],
					Print[(extraEqns[[idx$j]]/.J[Port[idx$j],s]->portCurrent)];
					Message[SelfConsistentSParams::notnum]
				];
			];
			Sow[{idx$s,iterCount},"iterCount"];
			(* Update S using the latest value of this. *)
			S[[idx$s,All,idx$j]]=(Sequations[[All,idx$j]]/.this/.(s->cur$s))/.replacements;,
			{idx$s,Length@{ss}},{idx$j, Length @ ports}
		];

		S
	];


End[];


(* ::Section::Closed:: *)
(*X, Y and ABCD Parameters*)


(* ::Subsection:: *)
(*Usage Declarations*)


ZParameters::usage = "ZParameters[circuit_Circuit,ports,s] finds the Z (impedance) parameters of the given linear circuit. As a usage note, *don't* include sources in the input circuit. The input ports should be a list of tuples specifying the nodes you want to use for a given port.";


YParameters::usage = "YParameters[circuit_Circuit,ports,s] finds the Y (admittance) parameters of the given linear circuit. As a usage note, *don't* include sources in the input circuit. The input ports should be a list of tuples specifying the nodes you want to use for a given port.";


ABCDParameters::usage = "ABCDParameters[circuit_Circuit,port1,port2,s] finds the ABCD (chain, cascade, or transmission line) parameters of the given linear circuit. The convention used is {{V2},{I2}}={{A,B},{C,D}}.{{V1},{I1}}. As a usage note, *don't* include sources in the input circuit. NThe input ports should be tuples specifying the nodes you want to use for the given port.";


(* ::Subsection:: *)
(*Options*)


Options[ZParameters] = Union[Options[LaplaceCircuitEquation],{}];


Options[YParameters] = Union[Options[LaplaceCircuitEquation],{}];


Options[ABCDParameters] = Union[Options[LaplaceCircuitEquation],{}];


(* ::Subsection:: *)
(*Implementations*)


Begin["`Private`"];


ZParameters[circuit_Circuit,ports_,s_,opt:OptionsPattern[]]:=Module[
	{
		augmentedCircuit,
		P,Rj,eqns,reps, (* Port symbol, circuit equations, and solution replacements *)
		J,V, (* Current, Voltage and Laplace domain variable. *)
		Vj,Jj,Vi,Ji,
		Z, 
		Z0, (* Limiting impedance to use to create effective short *)
		lceOpts
	},
	(* When we pass options to LaplaceCircuitEquation, we must strip out options that functio ndoes not recognize. *)
	lceOpts = Sequence @@ FilterRules[{opt}, Options[LaplaceCircuitEquation]];
	
	(* Z matrix *)
	Z=ConstantArray[0,{Length@ports,Length@ports}];

	(* Calculate one column at a time, because they have the same circuit in common. *)
	Table[
		(* Put source on port j, and a Z0 impedance on every other port *)
		augmentedCircuit=Join[
			circuit,
			Circuit@@Flatten@Table[
				If[j==i,
					Source[Sequence@@ports[[i]], P[i]],
					Resistor[Sequence@@ports[[i]],P[i],Z0]
				],
				{i,Length@ports}
			]
		];

		(* Find V on port i in terms of J on port j, then do the division, and J[P[j],s] should cancel*)
		Table[
			Vi=V[P[i],s]/.LaplaceCircuitEquation[augmentedCircuit,V[P[i],s],J[P[j],s],J,V,s,lceOpts];
			Z[[i,j]] = Vi/J[P[j],s];,
			{i,Length@ports}
		];
		,
		{j,Length@ports}
	];

	Limit[Z,Z0->\[Infinity]]
]


YParameters[circuit_Circuit,ports_,s_,opt:OptionsPattern[]]:=Module[
	{
		augmentedCircuit,
		P,Rj,eqns,reps, (* Port symbol, circuit equations, and solution replacements *)
		J,V, (* Current, Voltage and Laplace domain variable. *)
		Vj,Jj,Vi,Ji,
		Y, 
		Z0, (* Limiting impedance to use to create effective short *)
		lceOpts
	},
	(* When we pass options to LaplaceCircuitEquation, we must strip out options that functio ndoes not recognize. *)
	lceOpts = Sequence @@ FilterRules[{opt}, Options[LaplaceCircuitEquation]];
	
	(* Z matrix *)
	Y=ConstantArray[0,{Length@ports,Length@ports}];
	Z0=0;

	(* Calculate one column at a time, because they have the same circuit in common. *)
	Table[
		
		(* Any self looped elements will be useless, so remove them. *)
		augmentedCircuit=circuit;
		Table[
			If[i!=j,augmentedCircuit=Select[augmentedCircuit,(Length@DeleteDuplicates[Join[List@@#[[{1,2}]],ports[[i]]]]>2)&]];,
			{i,Length@ports}
		];

		(* Put source on port j, and a Z0 impedance on every other port *)
		augmentedCircuit=Join[
			augmentedCircuit,
			Circuit@@Flatten@Table[
				If[j==i,
					Source[Sequence@@ports[[i]], P[i]],
					Resistor[Sequence@@ports[[i]],P[i],Z0]
				],
				{i,Length@ports}
			]
		];

		Table[
			(* Find V on port i in terms of J on port j, then do the division, and J[P[j],s] should cancel*)
			Ji=J[P[i],s]/.LaplaceCircuitEquation[augmentedCircuit,J[P[i],s],V[P[j],s],J,V,s,lceOpts];
			Y[[i,j]] = Ji/V[P[j],s];
			,
			{i,Length@ports}
		];
		,
		{j,Length@ports}
	];

	Y
]


ABCDParameters[circuit_Circuit,port1_,port2_,s_,opt:OptionsPattern[]]:=Module[
	{
		augmentedCircuit,
		P1,P2,Rj,eqns,reps, (* Port symbol, circuit equations, and solution replacements *)
		J,V, (* Current, Voltage and Laplace domain variable. *)
		Vj,Jj,Vi,Ji,
		ABCD, 
		Z0, (* Limiting impedance to use to create effective short *)
		lceOpts
	},
	(* When we pass options to LaplaceCircuitEquation, we must strip out options that functio ndoes not recognize. *)
	lceOpts = Sequence @@ FilterRules[{opt}, Options[LaplaceCircuitEquation]];
	
	(* Z matrix *)
	ABCD=ConstantArray[0,{2,2}];

	augmentedCircuit=Join[
			circuit,
			Circuit[Source[Sequence@@port2,P2],Resistor[Sequence@@port1,P1,Z0]]
		];
	
	ABCD[[1,1]] = (V[P2,s]/V[P1,s])/.LaplaceCircuitEquation[augmentedCircuit,V[P2,s],V[P1,s],J,V,s,lceOpts];
	ABCD[[2,1]] = (J[P2,s]/V[P1,s])/.LaplaceCircuitEquation[augmentedCircuit,J[P2,s],V[P1,s],J,V,s,lceOpts];

	augmentedCircuit=Join[
			circuit,
			Circuit[Source[Sequence@@port1,P1],Resistor[Sequence@@port2,P2,0]]
		];
	
	ABCD[[1,2]] = (V[P2,s]/J[P1,s])/.LaplaceCircuitEquation[augmentedCircuit,V[P2,s],J[P1,s],J,V,s,lceOpts];
	ABCD[[2,2]] = (J[P2,s]/J[P1,s])/.LaplaceCircuitEquation[augmentedCircuit,J[P2,s],J[P1,s],J,V,s,lceOpts];

	Limit[ABCD,Z0->\[Infinity]]
]


End[];


(* ::Section::Closed:: *)
(*Epilogue*)


EndPackage[];
