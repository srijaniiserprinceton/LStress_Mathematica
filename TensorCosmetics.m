(* ::Package:: *)

(* ::Input::Initialization:: *)
BeginPackage["TensorCosmetics`"];
Unprotect@@Names["TensorCosmetics`*"];
ClearAll@@Names["TensorCosmetics`*"];
GenInd::usage=
"GenInd[x_] is a GSH index generator that returns the index or a sequence of concatenated indices corresponding to the arguments x = 1 or 2 or 3 or a list of these numbers, for 3D geometry.";
GenerateTensor::usage=
"GenerateTensor[x_] is a tensor index generator that returns the elements of tensor x in tensorial form subscripted by -,0 or + depending upon its location in the tensor";
Symmetrise::usage=
"Symmetrise[h_] symmetrises a given second order tensor.";

Begin["`Private`"];

GenInd[i_]:=Module[{},
If[Length[i]==0,Switch[i,1,"-",2,"0",3,"+"],
Module[{k,temp},
temp="";
For[k=1,k<=Length[i],k++,temp=temp<>GenInd[i[[k]]]];
Return[temp];
]
]
]

GenerateTensor[T_]:=
Module[{i,j},Return[Table[Subscript[Symbol[T], GenInd[{i,j}]],{i,1,3},{j,1,3}]]];

Symmetrise[h_]:=Module[{i,j},
ret=Evaluate[h];
For[i=1,i<=3,i++,
For[j=i+1,j<=3,j++,
ret[[i]][[j]]=h[[j]][[i]];
];
];
Return[ret];
];

End[];
Protect@@Names["TensorCosmetics`*"];
EndPackage[];


(* ::Input:: *)
(*NotebookClose[TensorCosmetics];*)
