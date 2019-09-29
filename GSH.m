(* ::Package:: *)

(* ::Input::Initialization:: *)
BeginPackage["GSH`"];
Unprotect@@Names["GSH`*"];
ClearAll@@Names["GSH`*"];
GSHUnitVector::usage=
"GSHUnitVector[] returns the unit vectors \!\(\*SubscriptBox[\(e\), \(-\)]\),\!\(\*SubscriptBox[\(e\), \(\(0\)\(,\)\)]\)\!\(\*SubscriptBox[\(e\), \(+\)]\) as three entries of a rank 2 tensor.
It does not admit any argument.";
UnitTensor::usage = 
"UnitTensor[A_] returns tensor with 1 in slot A and 0 everywhere else. Rank = Length[A]. Dim = 3.\[IndentingNewLine]Rank = 1 if Length[A] = 0 i.e. A is an integer";
SpheInt::usage=
"SpheInt[l1_,l2_,l3_,m1_,m2_,m3_,n1_,n2_,n3_,simp_:False] is used to retrieve the symbolic form of the corresponding GSH integral with the first GSH being conjugated. The results is in terms of 3J symbols. If (optional) simp is true, 3J symbols will appear decomposed s.t lower rows are either 0,0,0 or -1,0,1. simp is False by default. Integral lack a prefactor of \!\(\*SqrtBox[FractionBox[\(\((2  l1 + 1)\) \((2  l2 + 1)\) \((2  l3 + 1)\)\), \(4  \[Pi]\)]]\)";
ThreeJ::usage=
"ThreeJ[l1_,l2_,l3_,m1_,m2_,m3_] is used to retrieve the symbolic form of a Wigner-3j";
ThreeJStd::usage="Standard form of ThreeJ";
Shift::usage=
"Shift[T_,q_,r_] returns tensor T wirh entries shifted by q places in r'th index, putting 0's for emergent entries."; 
GradGSH::usage=
"GradGSH[T_,l_] returns gradient of tensor T with harmonic order l. rank[gradient] = rank[T]+1";
Om::usage=
"Om[l_,m_] finds the value \!\(\*SqrtBox[\(\*FractionBox[\(1\), \(2\)] \((l \[PlusMinus] N)\) \((\(l \[MinusPlus] N\) + 1)\)\)]\) " ;
Gam::usage="Gam[l_] returns \!\(\*SubscriptBox[\(\[Gamma]\), \(l\)]\) and stands for the value \!\(\*SqrtBox[FractionBox[\(2  l + 1\), \(4  \[Pi]\)]]\)";
r::usage="r";

Begin["`Private`"];

GSHUnitVector[] := {1/Sqrt[2] {0,1,-I},{1,0,0},1/Sqrt[2] {0,-1,-I}};
UnitTensor[A_]:=Module[{ret,i},
(
If[Max[A]>3||Max[A]<0,Return[0]];
If[Length[A]==0,ret=Array[KroneckerDelta[#,A]&,3],
(
ret=1;
For[i=1,i<=Length[A],i++,
ret=TensorProduct[ret,UnitTensor[A[[i]]]];
];
)
];
Return[ret];
)
]
SpheInt[l1_,l2_,l3_,m1_,m2_,m3_,n1_,n2_,n3_,simp_:False]:=
(-1)^(m1+n1) ThreeJ[l1,l2,l3,-m1,m2,m3]If[simp,ThreeJStd[l1,l2,l3,-n1,n2,n3],ThreeJ[l1,l2,l3,-n1,n2,n3]];

ThreeJ[l1_,l2_,l3_,m1_,m2_,m3_]:=Module[{ret},
If[m1+m2+m3!=0,Return[0]];
ret=MatrixForm[{{l1,l2,l3},{m1,m2,m3}}];
Return[ret];
]

ThreeJStd[l1_,l2_,l3_,m1_,m2_,m3_]:=Module[{ret,sign,up,lo,maxi,mini,medi,tempmed,tempmin,a,b,c,d,e,f,s},
If[m1+m2+m3!=0,Return[0]];
ret=ThreeJ[l1,l2,l3,m1,m2,m3];
sign=(-1)^(l1+l2+l3);
If[m1==0&&m2==0&&m3==0&&sign==-1,Return[0]];
up={l1,l2,l3};(*upper row*)
lo={m1,m2,m3};(*lower row*)
{mini,medi,maxi}=Ordering[Abs[lo]];
(*Indices of succesively absolutely increasing m's*)
If[Abs[lo[[maxi]]]>1,
(
s=Sign[lo[[maxi]]];(*sign of abs biggest m*)
tempmed={{l1,l2,l3},{m1,m2,m3}};
tempmin={{l1,l2,l3},{m1,m2,m3}};
tempmed[[2]][[medi]]+=s;tempmed[[2]][[maxi]]-=s;
tempmin[[2]][[mini]]+=s;tempmin[[2]][[maxi]]-=s;
{a,b,c,d,e,f}=Flatten[tempmed];
ret=-Om[up[[medi]],-s lo[[medi]]]ThreeJStd[a,b,c,d,e,f];
{a,b,c,d,e,f}=Flatten[tempmin];
ret-=Om[up[[mini]],-s lo[[mini]]]ThreeJStd[a,b,c,d,e,f];
ret/=Om[up[[maxi]],-s lo[[maxi]]+1];
),
If[m2!=0,
(
{mini,medi,maxi}={1,3,2};
s=Sign[lo[[maxi]]];(*sign of abs biggest m*)
tempmed={{l1,l2,l3},{m1,m2,m3}};
tempmin={{l1,l2,l3},{m1,m2,m3}};
tempmed[[2]][[medi]]+=s;tempmed[[2]][[maxi]]-=s;
tempmin[[2]][[mini]]+=s;tempmin[[2]][[maxi]]-=s;
{a,b,c,d,e,f}=Flatten[tempmed];
ret=-Om[up[[medi]],-s lo[[medi]]]ThreeJStd[a,b,c,d,e,f];
{a,b,c,d,e,f}=Flatten[tempmin];
ret-=Om[up[[mini]],-s lo[[mini]]]ThreeJStd[a,b,c,d,e,f];
ret/=Om[up[[maxi]],-s lo[[maxi]]+1];
)
,
If[m1>0,ret=sign*ThreeJ[l1,l2,l3,-m1,-m2,-m3]]
]
];
Return[Simplify[ret]];
]

Om[l_,m_]:=
If[m<0||m==1,Om[l,-m+1],Subscript[Global`\[CapitalOmega], ToString[l]<>ToString[m]]];
Shift[T_,q_,r_]:=Module[{i,dim,rank,len,ind,Tf,Tnew,shape,m},
shape=Dimensions[T];
dim=shape[[1]];
rank=Length[shape];
If[r>rank,Return["r exceeds rank of tensor"]];
If[Total[shape]-dim*rank!=0,Return["input array has nonuniform dimensionality"]];
Tf=Flatten[T];
len=Length[Tf];
Tnew=Array[0&,len];
For[m=1,m<=len,m++,
ind=IntegerDigits[m-1,dim,rank]+1;
i=ind[[r]];
If[i-q<=0||i-q>dim,Tnew[[m]]=0,Tnew[[m]]=Tf[[m-q*dim^(rank-r)]]];
];
Return[ArrayReshape[Tnew,shape]];
]

$Assumptions=r>0;
GradGSH[T_,l_]:=Module[{a,rad,ang,rank,omega1,omega2},
(*Returns gradient of tensor T with harmonic order l. rank[gradient] = rank[T]+1*)
rank=Length[Dimensions[T]];
rad=TensorProduct[UnitTensor[2],D[T,r]];(*radial part of gradient*)
omega1=Array[Om[l,Total[{##}]-2*rank]&,Dimensions[T]];
omega2=Array[Om[l,-(Total[{##}]-2*rank)]&,Dimensions[T]];
ang=TensorProduct[UnitTensor[1],omega1*T];(*angular part of gradient*)
ang+=TensorProduct[UnitTensor[3],omega2*T];
For[a=1,a<=rank,a++,
ang-=TensorProduct[UnitTensor[1],Shift[T,1,a]];
ang-=TensorProduct[UnitTensor[3],Shift[T,-1,a]];
];
Return[rad+ang/r];
]
Gam[l_]:=Subscript[Global`\[Gamma], ToString[l]];

End[];
Protect@@Names["GSH`*"];
EndPackage[];


(* ::Input:: *)
(*NotebookClose[GSH];*)
