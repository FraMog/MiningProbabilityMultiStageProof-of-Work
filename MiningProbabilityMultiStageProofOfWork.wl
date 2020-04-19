(* ::Package:: *)

(*
This package provided the functionalities to compute the mining probability of a miner, in a context which comprises M>=2 miners and k>=1 sequential hash-puzzles. 
It implements the expression 3 obtained in the paper "On multi-stage Proof-of-Work blockchain protocols: issues and challenges" (D'Arco, Ebadi Ansarodi, Mogavero). 
*)

BeginPackage[ "MiningProbabilityMultiStageProofOfWork`"]
Needs["GeneralUtilities`"]

ComputeMiningProbability::usage = "ComputeMiningProbability[ { {\!\(\*SubscriptBox[\(\[Lambda]\), \(1, 0\)]\), \ 
..., \!\(\*SubscriptBox[\(\[Lambda]\), \(1, k - 1\)]\)}, ..., {\!\(\*SubscriptBox[\(\[Lambda]\), \(M, 0\)]\), ..., \
 \!\(\*SubscriptBox[\(\[Lambda]\), \(M, k - 1\)]\)} }] \
computes the mining probability of the first of M miners. Each one of the M miners is identified by a list of k \
positive real \[Lambda]-parameters. The function implicitly determines the values of M and k by parsing the input. \
It must hold that M>=2 and k>=1.";
ComputeMiningProbability::atLeastTwoMinersMessage="Expecting at least two miners instead of `1`.";
ComputeMiningProbability::samenStagesForEveryMinerMessage="Every miner must have the same number of stages to resolve.";
ComputeMiningProbability::atLeastOneStageMessage="The number of stage should be at least 1 instead of `1`.";
ComputeMiningProbability::No3DListMessage="Too many dimensions for the input list.";
ComputeMiningProbability::positiveRealValuesMessage="Every input parameter must be a positive real value.";


Begin["Private`"]
ComputeMiningProbability[args___] :=
{
 {Module[{input, z, nStages, nMiners, listsLambdaParameters, minerZLambdaParameters, couples, minerZCouples,
  BminerZ,BValues, aZ, aValues , summationsResult, currentParameters, miningProbability},
  
  (* Verify that the number of input args is 1. If the condition is not respected, it throws an error message and the computation stops with an empty output. *)
  input=System`Private`Arguments[ComputeMiningProbability[args],1];
  If[input == {}, Return[{},ComputeMiningProbability];];
  
  (* Check other syntax errors using the function CheckInputErrors  written below. If CheckInputErrors throws a Failure, the computation stops with an empty output*)
  If [FailureQ[wrongNumberOfArgs=CheckInputErrors@@input], Return[{},ComputeMiningProbability];];
  
  
 
  listsLambdaParameters = args;
  nMiners = Length[listsLambdaParameters];
  nStages = Length[listsLambdaParameters[[1]]];
  
  couples  = {};
  BValues = {};
  aValues = {};
  currentParameters= {};
  
  
  (* Work disjointly for every distinct miner z *)
  For [z = 1, z <= nMiners, z++,
    (* Get {Subscript[\[Lambda], 1,0], ..., Subscript[\[Lambda], z,k-1]}*) 
    minerZLambdaParameters = listsLambdaParameters[[z]];
  
    (* Retrieve \[LeftAssociation]Subscript[\[Beta], z,1 ]\[Rule]Subscript[r, z,1 ],..., Subscript[\[Beta], z,Subscript[a, z]]Subscript[r, z,Subscript[a, z]]\[RightAssociation] *) 
    minerZCouples = GroupEqualLambdas[minerZLambdaParameters,nStages];
    AppendTo[couples, minerZCouples];
  
    (* Retrieve  BminerZ = Subscript[\[Beta], z,1 ]^(Subscript[r, z,1 ])\[CenterDot]...\[CenterDot] Subscript[\[Beta], z,Subscript[a, z]]^(Subscript[r, z,Subscript[a, z]])*) 
  
  (* Get Subscript[a, z] as the number of distinct \[Beta]-parameters relative to miner z. *) 
    aZ = Length[Keys[minerZCouples]];
    AppendTo[aValues, aZ];
    
    BminerZ = B[minerZCouples, aZ];
    AppendTo[BValues, BminerZ];
  ];
  
  (* Retrieve  summationsResult as the result of the k^M nested summations of expression 3 in the paper.*) 
  summationsResult = ComputeSummationRecursive[1,currentParameters, nMiners,  couples, aValues,null];
  miningProbability  = summationsResult;
  
  For [z = 1, z <= nMiners, z++,
     miningProbability *= BValues[[z]];
  ];
  
  Return[miningProbability, ComputeMiningProbability ];
  ]}
 
 
}





CheckInputErrors[input_,opts_]:=CatchFailureAsMessage[ComputeMiningProbability,
 Module[{nStages, nMiners, listsLambdaParameters},
 
  listsLambdaParameters = input[[1]];
  nMiners = Length[listsLambdaParameters];

  argumentTest["AtLeastTwoMiners","atLeastTwoMinersMessage"][nMiners];
  argumentTest["samenStagesForEveryMiner","samenStagesForEveryMinerMessage"][listsLambdaParameters];

  nStages = Length[listsLambdaParameters[[1]]];

  argumentTest["AtLeastOneStage","atLeastOneStageMessage"][nStages];
  (* Checks that the input list has just two dimensions *)
  argumentTest["No3DList","No3DListMessage"][listsLambdaParameters];
  argumentTest["PositiveRealValues", "positiveRealValuesMessage"][listsLambdaParameters];
  
]]


argumentTest["AtLeastTwoMiners",message_]:=
Function[
  If[# >=2,#, ThrowFailure[message,#]
]]

argumentTest["samenStagesForEveryMiner",message_]:=
Function[
  If[ArrayQ[#],#, ThrowFailure[message,#]
]]

argumentTest["AtLeastOneStage", message_]:=Function[
  If[#>= 1,#,ThrowFailure[message,#]
]]

argumentTest["No3DList", message_]:=Function[
  If[ArrayDepth[#]==   2,#,ThrowFailure[message,#]
]]
 
argumentTest["PositiveRealValues", message_]:=Function[
 Module[{flattenedList},
  flattenedList = Flatten[#];
  flattenedList=Select[flattenedList,NumericQ];
  If[Min@flattenedList >0,#,ThrowFailure[message,#]
  Return[{},Module];
]]]


ComputeSummationRecursive [par1_, par2_, par3_,par4_, par5_, par6_] :=

Module[{z,currentParameters, nMiners,  couples, minerZCouples, aValues, aZ,betaValuesMinerZ,qZ, betaZqZ , rZqZ,  lZ, multinomialNumerator,
multonomialDenominator, multinomialCoefficient, iteratecurrentParameters, currentParametersMinerZ, iterationDenominator,
iterationDenominatorBasis, iterationDenominatorExp, thetaPrimeResult, recursiveResult, thetaCumulativeResult, output},

  z = par1;
  currentParameters= par2;
  nMiners = par3;
  couples=par4;
  aValues=par5;

  output=0;
  minerZCouples = couples[[z]];
  betaValuesMinerZ = Keys[minerZCouples];
  aZ = aValues [[z]];
  
  AppendTo[currentParameters, {1,1, betaValuesMinerZ[[1]]}];



  For[qZ = 1,qZ <= aZ,qZ++,
    betaZqZ = betaValuesMinerZ[[qZ]];
    rZqZ = minerZCouples[betaZqZ];

    For [lZ= 1, lZ<= rZqZ, lZ++,
      thetaCumulativeResult = par6;
      currentParameters[[z]] = {rZqZ,lZ,betaZqZ};

	   (* case 1: z \[Equal] 1 *)
       If[z == 1,
         (* The value of thetaPrimeResult is obtained through the PhiPrime function below. *)
         thetaPrimeResult = PhiPrime[qZ ,lZ, - betaZqZ, aZ, minerZCouples] ;
         thetaCumulativeResult = thetaPrimeResult;
         recursiveResult= ComputeSummationRecursive[2,currentParameters, nMiners,  couples, aValues,thetaCumulativeResult];
         output += recursiveResult;
       ,

		(* Else statement: z > 1 *)
		 (* The value of thetaPrimeResult is obtained through the PsiPrime function below. *)
         thetaPrimeResult = PsiPrime[qZ ,lZ, - betaZqZ, aZ, minerZCouples] ; 
         thetaCumulativeResult *= thetaPrimeResult;

		  (* case 2: 2 \[LessEqual] z \[LessEqual] M-1 *)	
          If[z < nMiners,
             recursiveResult= ComputeSummationRecursive[z +1 ,currentParameters, nMiners,  couples, aValues,thetaCumulativeResult]; 
             output += recursiveResult;
          ,

		    (* Else statement: case 3: z \[Equal] M *)
            multinomialNumerator = 0;
            multonomialDenominator = 1;
            iterationDenominatorBasis =0;

            For[iteratecurrentParameters= 1, iteratecurrentParameters<= nMiners,iteratecurrentParameters++,
                currentParametersMinerZ = currentParameters[[iteratecurrentParameters]];
               multinomialNumerator +=  currentParametersMinerZ[[1]] - currentParametersMinerZ[[2]];
                 multonomialDenominator *=  (currentParametersMinerZ[[1]] - currentParametersMinerZ[[2]])!;
                 iterationDenominatorBasis += currentParametersMinerZ[[3]];
            ];

             iterationDenominatorExp = (multinomialNumerator + 1);
             iterationDenominator = (iterationDenominatorBasis)^(iterationDenominatorExp);
               multinomialNumerator = multinomialNumerator!;
               multinomialCoefficient = multinomialNumerator/multonomialDenominator;
               output  += thetaCumulativeResult  * multinomialCoefficient/iterationDenominator;
           ];
        ];
      ];
    ];


Return[output, Module];

]


GroupEqualLambdas[par1_, par2_] := 
Module[{lambdaListMinerZ, i, lambdaStageI, nStages, minerZCouples},

  lambdaListMinerZ = par1;
  nStages = par2;
  minerZCouples = Association[];

  For[i=1,i<=nStages,i++,
    lambdaStageI = lambdaListMinerZ[[i]];
    If [KeyExistsQ[minerZCouples, lambdaStageI], minerZCouples[lambdaStageI] =  minerZCouples[lambdaStageI] +1; ,  minerZCouples[lambdaStageI] = 1;];
  ];

  Return[minerZCouples,Module];
]


B[par1_, par2_] :=
Module[{minerZCouples, i, betaValuesMinerZ, aZ,firstBeta, BMinerZ, BetaNoi},

  minerZCouples = par1;
  aZ = par2;

  betaValuesMinerZ = Keys[minerZCouples];
  
  firstBeta = betaValuesMinerZ[[1]];
  BMinerZ =firstBeta^ (minerZCouples[firstBeta]);


  For[i=2,i<=aZ,i++,
    BetaNoi = betaValuesMinerZ[[i]];
    BMinerZ *= BetaNoi^ minerZCouples[BetaNoi];
  ];

  Return[BMinerZ,Module];
]

(* This function computes Subscript[Derivative[1][\[CapitalPhi]], 1,Subscript[l, 1] Subscript[q, 1]] (t) *)




PhiPrime[par1_, par2_, par3_, par4_, par5_] :=
Module[{q1,l1, t,a1, miner1Couples,arraySize,array,summationResultPhi, result},

  q1 = par1;
  l1 = par2;
  t = par3;
  a1 = par4;

  arraySize = a1-1;
  array = 0;
  summationResultPhi =0;
   (* the length of miner1Couples is arraySize + 1 (i.e.: it is: a1) *)
  miner1Couples = par5;

  If[arraySize == 0,
    If[l1-1 ==0, result =1, result =0];
      Return[result, Module];
   ];

  array = Array[0&,{arraySize}];
  summationResultPhi = RecursivelyComputeSumPhiPrimeWithArray[1,l1-1, array, q1, t, arraySize, miner1Couples, a1];
  result =   (-1)^(l1-1)  * summationResultPhi;

  Return[result, Module];
]


RecursivelyComputeSumPhiPrimeWithArray[par1_, par2_, par3_, par4_, par5_, par6_, par7_, par8_] :=
Module[{v,amountToAssign, array,q1, t, arraySize, miner1Couples, phiValueRecursiveResult,c,idx, a1, result},

  v = par1;
  amountToAssign = par2;
  array = par3;
  q1 = par4;
  t = par5;
  arraySize = par6;
  miner1Couples = par7;
  a1 = par8;

  result =0;
  phiValueRecursiveResult =0;
  c=0;

  (* Case 1) v = arraySize *)
  If[v == arraySize, 
    array[[v]] = amountToAssign;
    result= PhiProduct[array, q1, t , miner1Couples, arraySize, a1];

  Return[result, Module];
  ];

  (* Case 3) 1<=v <= arraySize  and amountToAssign > 0 *)
  For[c =0, c <= (amountToAssign-1), c++,
    array[[v]]=c;
    phiValueRecursiveResult = RecursivelyComputeSumPhiPrimeWithArray[v+1, (amountToAssign-c) , array, q1, t, arraySize, miner1Couples, a1];
    result += phiValueRecursiveResult;
  ];


  array[[v]] = amountToAssign;
  (* Case 2)  amountToAssign =  0 *)
  For [idx = (v +1), idx <= arraySize, idx++,
    array[[idx]]=0;
  ];


  phiValueRecursiveResult= PhiProduct[array, q1, t , miner1Couples, arraySize, a1];
  result +=   phiValueRecursiveResult ;

  Return[result, Module];
]


PhiProduct[par1_, par2_, par3_ , par4_,par5_, par6_] :=
Module[{array, q1, t , miner1Couples,arraySize,v,j1, ij1, beta1j1,rj1, upperIndexBinomialCoefficient,distinctBetaValuesMiner1, tauj1, a1, result},

  array = par1;
  q1 = par2;
  t = par3;
  miner1Couples = par4;
  arraySize = par5;
  a1 = par6;

  v=0;
  j1 = 0;
  ij1=0;
  beta1j1 = 0;
  rj1 =0;
  upperIndexBinomialCoefficient =0;
  distinctBetaValuesMiner1 =0;
  tauj1 =0;
  result = 1;



  For[j1= 1, j1 <= a1, j1++,
    If[j1 != q1, 
      If[j1<q1, v = j1 ,  v = j1 - 1];
        distinctBetaValuesMiner1 = Keys[miner1Couples];
        beta1j1 = distinctBetaValuesMiner1[[j1]];
        rj1 = miner1Couples[beta1j1];
        ij1 = array[[v]];
        upperIndexBinomialCoefficient =  ij1 + rj1 -1;
        tauj1 = (beta1j1 + t)^(- (rj1 + ij1) );
        result *= Binomial[upperIndexBinomialCoefficient, ij1] * tauj1;
     ];
   ];

  Return[result, Module];

]


PsiPrime[par1_, par2_, par3_, par4_, par5_] :=
Module[{qZ,lZ, t,aZ, minerZCouples,arraySize,array,summationResultPsi, result},
  qZ = par1;
  lZ = par2;
  t = par3;
  aZ = par4;
  minerZCouples = par5;

  arraySize = aZ;
  array = 0;
  summationResultPsi =0;
  result = 0;


  (* the length of minerZCouples is arraySize + 1 (i.e.: it is: aZ + 1), *)
  minerZCouples=Insert[minerZCouples,0->1,-(Length[minerZCouples]+1)];
  array = Array[0&,{arraySize}];
  summationResultPsi = RecursivelyComputeSumPsiPrimeWithArray[1,lZ-1, array, qZ, t, arraySize, minerZCouples, aZ];
  result = - (-1)^(lZ-1 ) *  summationResultPsi;


  Return[result, Module];
]


RecursivelyComputeSumPsiPrimeWithArray[par1_, par2_, par3_, par4_, par5_, par6_, par7_, par8_] :=
Module[{v,amountToAssign, array,qZ, t, arraySize, minerZCouples, psiValueRecursiveResult,c,idx, aZ, result},

  v = par1;
  amountToAssign = par2;
  array = par3;
  qZ = par4;
  t = par5;
  arraySize = par6;
  minerZCouples = par7;
  aZ = par8;

  result =0;
  psiValueRecursiveResult =0;
  c=0;


  (* Case 1) v = arraySize *)
  If[v == arraySize, 
    array[[v]] = amountToAssign;
    result = PsiProduct[array, qZ, t , minerZCouples,arraySize,aZ];
    Return[result, Module];
  ];

  (* Case 3) 1<=v <= arraySize  and amountToAssign > 0 *)
  For[c =0, c <= (amountToAssign-1), c++,
    array[[v]]=c;
    psiValueRecursiveResult= RecursivelyComputeSumPsiPrimeWithArray[v+1, (amountToAssign-c) , array, qZ, t, arraySize, minerZCouples, aZ];
    result  +=psiValueRecursiveResult;
  ];

  array[[v]] = amountToAssign;
  (* Case 2)  amountToAssign =  0 *)
  For [idx = (v +1), idx <= arraySize, idx++,
    array[[idx]]=0;
  ];

  psiValueRecursiveResult= PsiProduct[array, qZ, t , minerZCouples,arraySize, aZ];
  result+=psiValueRecursiveResult;

  Return[result, Module];
]


PsiProduct[par1_, par2_, par3_ , par4_,par5_, par6_] :=
Module[{array, qZ, t , minerZCouples,arraySize,v,jZ, ijZ, betaZjZ,rjZ, upperIndexBinomialCoefficient,distinctBetaValuesMinerZ, taujZ, aZ, result},

  array = par1;
  qZ = par2;
  t = par3;
  minerZCouples = par4;
  arraySize = par5;
  aZ = par6;

  v=0;
  jZ = 0;
  ijZ=0;
  betaZjZ = 0;
  rjZ =0;
  upperIndexBinomialCoefficient =0;
  distinctBetaValuesMinerZ =0;
  taujZ =0;
  result = 1;



  For[jZ= 0, jZ <= aZ, jZ++,
    If[jZ != qZ, 
      If[jZ<qZ, v = jZ + 1 ,  v = jZ];
        distinctBetaValuesMinerZ = Keys[minerZCouples];
        
        (* Since the first index is 1, then betaZjZ is in position jZ+1 of the list of distinctBetaValuesMinerZ, for every value of jZ*)
        betaZjZ = distinctBetaValuesMinerZ[[jZ + 1]];
     
        rjZ = minerZCouples[betaZjZ];
        ijZ = array[[v]];
        upperIndexBinomialCoefficient =  ijZ + rjZ -1;
        taujZ = (betaZjZ + t)^(- (rjZ + ijZ) );
        result *= Binomial[upperIndexBinomialCoefficient, ijZ] * taujZ;
     ];
   ];

  Return[result, Module];

]


End[]
EndPackage[]
