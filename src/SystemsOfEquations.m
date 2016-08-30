(* ::Package:: *)

BeginPackage["SystemsOfEquations`"];


(* ::Section::Closed:: *)
(*Operations and Relations on Sets*)


(* ::Subsection:: *)
(*Usage Declarations*)


SetDifference::usage = "SetDifference[a, b] returns a list of all elements of a that are not also elements of b.";


(* ::Subsection:: *)
(*Implementations*)


Begin["`Private`"];


Subset[a_,b_] := And @@ (MemberQ[b, #]& /@ a);


SetDifference[a_, b_] := Select[a, Not[MemberQ[b, #]]&];


End[];


(* ::Section::Closed:: *)
(*Elimination of Extraneous Equations and Symbols*)


(* ::Subsection:: *)
(*Usage Declarations*)


EquationListForm::usage = "EquationListForm[eqns] returns eqns as a list of equations. For example, left1==right1&&left2=right2 and {left1==right1,left2=right2} both return {left1==right1,left2=right2}, and left==right returns {left==right}.";


ConnectedEquations::usage = "ConnectedEquations[eqns, symbols, allSymbols] returns a list {connEqns, connSymbols} of those equations and symbols in eqns that are connected to one or more of symbols, where allSymbols is a list of all expressions to treat as atomic symbols.";
EliminateIfPossible::usage = "EliminateIfPossible[eqns, goodSymbols, badSymbols] returns a list of eqns with as many of badSymbols eliminated as possible under the guarantee that all goodSymbols remain in the system of equations. goodSymbols and badSymbols can contain patterns, effectively adding all symbols that match the given patterns to the respective lists. The option Simplify can be set to True (default) or False; when True, a simplification will be called following every call to the builtin Eliminate.";


(* ::Subsection:: *)
(*Options*)


Options[EliminateIfPossible]={Simplify->True};


(* ::Subsection:: *)
(*Implementations*)


Begin["`Private`"];


EquationListForm[eqns_]:=Which[Head[eqns]===And,List@@eqns,Head[eqns]===List,eqns,True,{eqns}]


ConnectedEquations[eqns_, symbols_, allSymbols_] := Module[
	{containingEqns, connectedSymbols, symbolsList, allSymbolsList, eqnsList},

	(* Convert to a standard form *)
	eqnsList = EquationListForm@eqns;
	symbolsList = EquationListForm@symbols;
	allSymbolsList = EquationListForm@allSymbols;

	(* Make a list of all equations containing one or more of the known symbols. *)
	containingEqns = Union @@ Table[
		Select[eqnsList, Not[FreeQ[#,symbol]]&],
		{symbol, symbolsList}
	];

	(* Find all symbols in those equations to make the new set of symbols connected to the initial set. *)
	connectedSymbols= Union @@ Table[
		Cases[eqn,Alternatives@@allSymbolsList,Infinity],
		{eqn, containingEqns}
	];

	(* Check if we got any new symbols this iteration, and stop the recursion if we did not. *)
	If[connectedSymbols \[Subset] symbolsList,
		(* We're done, as the symbol set did not expand. *)
		{containingEqns,connectedSymbols},
		ConnectedEquations[eqnsList,connectedSymbols,allSymbolsList]
	]
];


(* Base case: there is no bathwater. *)
EliminateIfPossible[eqns_, goodSymbols_, {}, OptionsPattern[]] := eqns;

(* Recursive step: throw out a bit of bathwater, checking for the babies. *)
EliminateIfPossible[eqns_, goodSymbols_, badSymbols_,opt:OptionsPattern[]] := Module[
	{firstBad,eliminationTrialEqns,eqnsList,goodSymbolsList,badSymbolsList,Simp},

	Simp=If[OptionValue[Simplify],Simplify,Identity];

	eqnsList=EquationListForm@eqns;
	goodSymbolsList=DeleteDuplicates@Cases[eqns,Alternatives@@EquationListForm@goodSymbols,Infinity];
	badSymbolsList=DeleteDuplicates@Cases[eqns,Alternatives@@EquationListForm@badSymbols,Infinity];

	firstBad=First@badSymbolsList;
	eliminationTrialEqns=EquationListForm@Simp@Eliminate[eqnsList,firstBad];
	If[
		(* Check if we eliminated the baby. *)
		Or@@(FreeQ[eliminationTrialEqns,#]&/@goodSymbolsList),
		(* Put the baby back, try the next variable. *)
		EliminateIfPossible[eqnsList,goodSymbolsList,Rest@badSymbolsList,opt],
		(* We have a bit less bathwater. *)
		EliminateIfPossible[eliminationTrialEqns,goodSymbolsList,Rest@badSymbolsList,opt]
	]
];


End[];


(* ::Section::Closed:: *)
(*Drawing Functions*)


(* ::Subsection:: *)
(*Usage Declarations*)


EquationGraph::usage = "EquationGraph[equations,variables] displays a graph where the given equations are vertices, and two vertices are connected by an edge iff they share a common variable. The variables input is allowed to contain patterns to identify variables.";


EquationVariableGraph::usage = "EquationVariableGraph[equations,variables] displays a graph where the variables are vertices, and two vertices are connected by an edge iff there exists an equation both of them belong to. The variables input is allowed to contain patterns to identify variables.";


(* ::Subsection:: *)
(*Implementations*)


Begin["`Private`"];


EquationGraph[equations_,variables_]:=Module[
	{symbols,edges,r},
	(* Find all symbols *)
	symbols=Cases[equations,Alternatives@@variables,Infinity];

	edges=Flatten@Table[
		With[
			{eqnList=Select[equations,Not@FreeQ[#,symbol]&]},
			r@@@Tuples[eqnList,2]
		],
		{symbol,symbols}
	];
	(* a\[Rule]b === b\[Rule]a *)
	edges=DeleteDuplicates[edges,#1===#2||Reverse[#1]===#2&];
	(* Get rid of self edges *)
	edges=Select[edges/.(r[x_,x_]:>None),#=!=None&]/.r->Rule;
	GraphPlot[edges,VertexLabeling->True]
]


EquationVariableGraph[equations_,variables_]:=Module[
	{edges,r},
	(* Find all edges *)
	edges=Flatten@Table[
		With[{eqnSymbols=Cases[eqn,Alternatives@@variables,Infinity]},
			Outer[r,eqnSymbols,eqnSymbols]
		],
		{eqn,equations}
	];
	(* a\[Rule]b === b\[Rule]a *)
	edges=DeleteDuplicates[edges,#1===#2||Reverse[#1]===#2&];
	(* Get rid of self edges *)
	edges=Select[edges/.(r[x_,x_]:>None),#=!=None&]/.r->Rule;
	GraphPlot[edges,VertexLabeling->True]
]


End[];


(* ::Section::Closed:: *)
(*Partial Solver*)


(* ::Subsection:: *)
(*Usage Declarations*)


PartialSolve::usage = "PartialSolve[eqns, symbols, allSymbols] returns the solution to eqns for all variables symbols, disregarding all variables unconnected to symbols, or that are completely determined by symbols. Optional argument Method is called on the reduced equations, the default value is Solve; consider also using Reduce.";


(* ::Subsection:: *)
(*Options*)


Options[PartialSolve]={Method->Solve};


(* ::Subsection:: *)
(*Implementations*)


Begin["`Private`"];


PartialSolve[eqns_, symbols_, allSymbols_,OptionsPattern[]] := Module[
	{connectedEqns, connectedSymbols, badSymbols, reducedEqns, solution},

	{connectedEqns, connectedSymbols} = ConnectedEquations[eqns,symbols,allSymbols];
	badSymbols = SetDifference[connectedSymbols, symbols];
	reducedEqns = EliminateIfPossible[connectedEqns, symbols, badSymbols];
	OptionValue[Method][reducedEqns, symbols]
]


End[];


(* ::Section:: *)
(*Epilogue*)


EndPackage[];
