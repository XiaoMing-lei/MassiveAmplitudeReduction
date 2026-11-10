(* Native Wolfram Language application of frozen v3.2 contextual replacements.
   Offline context preparation is separate. No Python is called by this package.
   See USAGE.txt for scope, conventions and reproducible preparation. *)
BeginPackage["MassiveTensorReduction`"];
Angle::usage = "Angle[i,j] is the angle bracket with physically symmetrized free little-group slots.";
(* The short name is explicitly requested. Create only this package symbol
   under Quiet; do not change System`Square or disable syntax highlighting. *)
Quiet[Symbol["MassiveTensorReduction`Square"]];
MassiveTensorReduction`Square::usage = "Square[i,j] is the square spinor bracket in this package, distinct from System`Square.";
ab::usage = "ab[i,j] is the short form of Angle[i,j].";
sb::usage = "sb[i,j] is the short form of this package's Square[i,j].";
m::usage = "m[i] is the short form of Mass[i], displayed as a subscripted mass.";
s::usage = "s[i,j] = 2 p_i.p_j in the adopted convention; it is not (p_i+p_j)^2 for massive legs.";
AmplitudeForm::usage = "AmplitudeForm[expr] displays readable notation; more than three tensor monomials are shown as a signed-coefficient / monomial table.";
ReductionCacheInformation::usage = "ReductionCacheInformation[] reports prepared lookup data, reference examples and runtime cache counts separately.";
BenchmarkAmplitude::usage = "BenchmarkAmplitude[expr,repeats] measures one first measured query and repeated queries with trace disabled. FirstQuerySeconds is only reported when no previous query has run after loading.";
$ReductionQueryCount::usage = "$ReductionQueryCount counts reducer calls since default-catalog loading; it is not a result cache.";
MassiveTensorReduction`SquareBracket::usage = "SquareBracket[i,j] is the square bracket with physically symmetrized free little-group slots. This is distinct from System`Square.";
SpinorChain::usage = "SpinorChain[{i,k,...,j},start] infers alternating contractions; start=1 for angle, 0 for square. Explicit color lists remain supported.";
TensorTrace::usage = "TensorTrace[labels,start] infers alternating contractions around an even-length trace; start=1 for angle, 0 for square. Display uses tr_a or tr_s. The existing signed convention is unchanged: TensorTrace[{i,j},0]=-2 p_i.p_j. Explicit color lists remain supported.";
ScalarProduct::usage = "ScalarProduct[i,j] denotes s_ij=2 p_i.p_j, with all momenta outgoing.";
Mass::usage = "Mass[i] denotes the generic mass coefficient m_i. Specialize masses after reduction and check returned nonzero conditions.";
TensorUnit::usage = "TensorUnit[d,kind,labels,colors] is the exact contraction representation: kind 0=open chain, 1=closed trace. Prefer the public constructors.";
PrepareTensorExpression::usage = "PrepareTensorExpression[expr] applies determinants and signed canonicalization only; no implicit repeated-trace identities.";
LoadPreparedCatalog::usage = "LoadPreparedCatalog[file] validates and indexes an offline prepared JSON application catalog.";
PreparedCatalog::usage = "PreparedCatalog[data] validates and indexes an imported RawJSON association.";
ReduceAmplitude::usage = "ReduceAmplitude[expr,catalog] applies group 1 then group 2 at each descending bracket degree. Returns an association or Failure on missing coverage or a stage gap.";
AmplitudeReduce::usage = "AmplitudeReduce[expr] returns the reduced expression using the available prepared replacements, with tracing disabled. Coefficients are interpreted at generic masses; ReduceAmplitude provides detailed conditions and provenance.";
$LastAmplitudeReduction::usage = "$LastAmplitudeReduction contains the last AmplitudeReduce result, elapsed seconds and actual rule-application counts, including native descendant preparation. ReductionTrace->True also records its steps.";
ReductionSteps::usage = "ReductionSteps[] displays a Manipulate for the last traced AmplitudeReduce call. ReductionSteps[report] displays a saved $LastAmplitudeReduction report.";
AutoSavePreparedData::usage = "AutoSavePreparedData is an AmplitudeReduce option. True merges new contextual applications into the single PreparedApplications.json file after successful reduction.";
UsePreparedData::usage = "UsePreparedData is an option for AmplitudeReduce. True reuses prepared data; False starts with the frozen parent rules and empty contextual caches, preparing descendants in Mathematica.";
CatalogExample::usage = "CatalogExample[catalog,name] returns Input and Expected for a saved example.";
CatalogInformation::usage = "CatalogInformation[catalog] returns finite coverage and preparation metadata.";
ExportPreparationRequest::usage = "ExportPreparationRequest[file,<|name->expr,...|>,n] writes exact polynomial-mass inputs for the separate Python offline preparer.";
RunCatalogTests::usage = "RunCatalogTests[catalog,names] compares native reductions with saved reference results; All tests every saved example.";
ReductionTrace::usage = "ReductionTrace->True makes AmplitudeReduce record equivalent input-amplitude rewrites for ReductionSteps. The default is False; step counts are automatic.";
MaximumReductionSteps::usage = "MaximumReductionSteps is a safety bound, not a completeness assertion.";
$DefaultCatalog::usage = "$DefaultCatalog is the bundled application catalog, or Missing when the package was loaded with $LoadPreparedTable=False.";
$LoadPreparedTable::usage = "$LoadPreparedTable controls package loading: True (default) loads parents and the prepared application table; False loads only parents. Set it before Get, preferably inside Block.";
If[!ValueQ[$LoadPreparedTable],$LoadPreparedTable=True];
$CatalogLoadingSeconds::usage = "$CatalogLoadingSeconds records the most recent default data loading and validation time.";
LoadDefaultCatalog::usage = "LoadDefaultCatalog[] reloads the bundled catalog relative to the package file.";
LoadRuleCatalog::usage="LoadRuleCatalog[file] loads a native n-point identity catalog and clears catalog-specific caches. Compatible bundled preparations are loaded by default; UsePreparedData->False disables loading them.";
SyntaxInformation[LoadRuleCatalog]={"ArgumentsPattern"->{_,OptionsPattern[]}};
Begin["`Private`"];
$packageDirectory = DirectoryName[$InputFileName];

(* Python tuple ordering, explicitly reproduced rather than using Wolfram's
   canonical expression order, which has different list-order semantics. *)
lexLess[a_List,b_List] := Module[{j=1,n=Min[Length[a],Length[b]]},
  While[j<=n && SameQ[a[[j]],b[[j]]],j++];
  If[j>n,Length[a]<Length[b],lexLess[a[[j]],b[[j]]]]
];
lexLess[a_Integer,b_Integer] := a<b;
lexSort[x_List] := Sort[x,lexLess];
monKey[m_List] := ToString[m,InputForm];
monDegree[m_List] := Total[If[m==={}, {}, m[[All,1]]]];
edges[u_List] := Table[With[{p=Sort[{u[[3,j]],u[[3,Mod[j,Length[u[[3]]]]+1]]}],c=u[[4,j]]},
  Prepend[If[c==1,p,-p],c]],{j,u[[1]]}];
unbolded[m_List] := lexSort[Flatten[edges /@ m,1]];
unitOrder[u_List] := {u[[1]],1-u[[2]],lexSort[edges[u]],
  If[u[[2]]==1 && u[[1]]<=4,{},u[[3]]],If[u[[2]]==1 && u[[1]]<=4,{},u[[4]]]};
orderKey[m_List,bound_Integer] := {monDegree[m],unbolded[m],
  Table[Count[m,u_/;u[[1]]==d],{d,bound,1,-1}],
  Table[-Count[m,u_/;u[[1]]==d && u[[2]]==1],{d,bound,1,-1}],
  Table[lexSort[unitOrder /@ Select[m,#[[1]]==d&]],{d,bound,1,-1}]};

validUnit[k_,ll_,cc_] := MemberQ[{0,1},k] && ListQ[ll] && ListQ[cc] &&
  Length[cc]>0 && Length[ll]==Length[cc]+1-k &&
  AllTrue[ll,IntegerQ[#] && #>0&] && AllTrue[cc,MemberQ[{0,1},#]&];
normalizeUnit[k_,ll_,cc_] := Catch[Module[{d=Length[cc],j,rev,variants={},l,col},
  If[!validUnit[k,ll,cc],Throw[Failure["InvalidTensorUnit",<|"Kind"->k,"Labels"->ll,"Colors"->cc|>],"TensorReduction"]];
  Do[If[ll[[j]]==ll[[Mod[j,Length[ll]]+1]],
    If[d==1,Throw[If[k==0,0,2 Mass[ll[[j]]]],"UnitResult"]];
    Throw[-Mass[ll[[j]]] normalizeUnit[k,Delete[ll,j],Delete[cc,j]],"UnitResult"]],{j,d}];
  Do[If[cc[[Mod[j-2,d]+1]]==cc[[j]],
    Throw[-Mass[ll[[j]]] normalizeUnit[k,Delete[ll,j],Delete[cc,j]],"UnitResult"]],{j,If[k==1,1,2],d}];
  If[k==0,
    rev={Reverse[ll],Reverse[cc]};
    If[SameQ[{ll,cc},rev],Throw[0,"UnitResult"]];
    Throw[If[lexLess[rev,{ll,cc}],-TensorUnit[d,0,rev[[1]],rev[[2]]],TensorUnit[d,0,ll,cc]],"UnitResult"]
  ];
  Do[l=RotateLeft[ll,j];col=RotateLeft[cc,j];
    AppendTo[variants,{l,col}];AppendTo[variants,{Prepend[Reverse[Rest[l]],First[l]],Reverse[col]}],{j,0,d-1}];
  {l,col}=First[lexSort[variants]];
  TensorUnit[d,1,l,col]
],"UnitResult"];
SpinorChain[ll_List,cc_List] := Catch[normalizeUnit[0,ll,cc],"TensorReduction"];
TensorTrace[ll_List,cc_List] := Catch[normalizeUnit[1,ll,cc],"TensorReduction"];
SpinorChain[ll_List,start:(0|1)] := If[Length[ll]>=2,
  SpinorChain[ll,Mod[start+Range[0,Length[ll]-2],2]],Failure["InvalidChainLength",<||>]];
TensorTrace[ll_List,start:(0|1)] := If[Length[ll]>=2 && EvenQ[Length[ll]],
  TensorTrace[ll,Mod[start+Range[0,Length[ll]-1],2]],
  Failure["InvalidAlternatingTraceLength",<|"MessageTemplate"->"A closed alternating trace needs an even number of labels, at least two."|>]];
Angle[i_Integer,j_Integer] := SpinorChain[{i,j},{1}];
SquareBracket[i_Integer,j_Integer] := SpinorChain[{i,j},{0}];
MassiveTensorReduction`Square[i_Integer,j_Integer] := SpinorChain[{i,j},{0}];
ab[i_Integer,j_Integer] := Angle[i,j];
sb[i_Integer,j_Integer] := MassiveTensorReduction`Square[i,j];
m[i_Integer] := Mass[i];
s[i_Integer,j_Integer] := ScalarProduct[i,j];
SyntaxInformation[MassiveTensorReduction`Square] = {"ArgumentsPattern" -> {_,_}};
SyntaxInformation[ab] = {"ArgumentsPattern" -> {_,_}};
SyntaxInformation[sb] = {"ArgumentsPattern" -> {_,_}};
SyntaxInformation[m] = {"ArgumentsPattern" -> {_}};
SyntaxInformation[s] = {"ArgumentsPattern" -> {_,_}};
SyntaxInformation[SquareBracket] = {"ArgumentsPattern" -> {_,_}};
SyntaxInformation[Angle] = {"ArgumentsPattern" -> {_,_}};
SyntaxInformation[SpinorChain] = {"ArgumentsPattern" -> {_,_}};
SyntaxInformation[TensorTrace] = {"ArgumentsPattern" -> {_,_}};
ScalarProduct[i_Integer,j_Integer] := If[i==j,2 Mass[i]^2,-TensorTrace[{i,j},{0,1}]];

(* Display only: InterpretationBox retains the exact internal expression.
   InputForm remains available for deliberate inspection/debugging. *)
labelBox[i_,form_] := MakeBoxes[i,form];
scalarBox[i_,j_,form_] := SubscriptBox["s",RowBox[{labelBox[i,form],",",labelBox[j,form]}]];
unitBoxes[{d_,kind_,ll_,cc_},form_] := Module[{left,right,momenta},
  If[kind==1,
    If[d==2,Return[RowBox[{"(","-",scalarBox[ll[[1]],ll[[2]],form],")"}]]];
    Return[RowBox[{SubscriptBox[StyleBox["tr",FontSlant->"Plain"],If[First[cc]==1,"a","s"]],
      "(",RowBox[Riffle[labelBox[#,form]& /@ ll,","]],")"}]]];
  left=If[First[cc]==1,"\[LeftAngleBracket]","["];
  right=If[Last[cc]==1,"\[RightAngleBracket]","]"];
  If[d==1,Return[RowBox[{left,labelBox[First[ll],form],"\[ThinSpace]",labelBox[Last[ll],form],right}]]];
  momenta=RowBox[Riffle[SubscriptBox["p",labelBox[#,form]]& /@ Rest[Most[ll]],"\[ThinSpace]"]];
  RowBox[{left,labelBox[First[ll],form],"|",momenta,"|",labelBox[Last[ll],form],right}]
];
Mass /: MakeBoxes[t:Mass[i_Integer],form:(StandardForm|TraditionalForm)] :=
  With[{boxes=SubscriptBox["m",labelBox[i,form]]},InterpretationBox[boxes,t,Editable->False]];
TensorUnit /: MakeBoxes[t:TensorUnit[d_Integer,k_Integer,ll_List,cc_List],form:(StandardForm|TraditionalForm)] :=
  With[{boxes=unitBoxes[{d,k,ll,cc},form]},InterpretationBox[boxes,t,Editable->False]];
displayScalar /: MakeBoxes[displayScalar[i_,j_],form:(StandardForm|TraditionalForm)] := scalarBox[i,j,form];
readableScalars[expr_] := expr /. TensorUnit[2,1,labels_List,colors_List] :> -displayScalar[labels[[1]],labels[[2]]];
(* Count tensor monomials, keeping mass polynomials together as coefficients.
   Convert two-leg traces before splitting, so their minus signs belong to
   the coefficient column. The enclosing interpretation preserves expr. *)
amplitudeDisplayRows[expr_] := Module[{shown=readableScalars[expr],vars,rules},
  vars=DeleteDuplicates[Cases[shown,_TensorUnit|_displayScalar,Infinity]];
  If[vars==={} || !PolynomialQ[shown,vars],Return[{}]];
  rules=CoefficientRules[shown,vars];
  ({Last[#],Times@@MapThread[Power,{vars,First[#]}]}& /@ rules)
];
signedCoefficientBoxes[c_,form_] := Module[{negative,magnitude,boxes},
  negative=TrueQ[If[Head[c]===Times,First[c],c]<0];
  magnitude=If[negative,-c,c];
  boxes=With[{value=magnitude},MakeBoxes[value,form]];
  If[Head[magnitude]===Plus,boxes=RowBox[{"(",boxes,")"}]];
  RowBox[{If[negative,"-","+"],boxes}]
];
amplitudeDisplayBoxes[expr_,form_] := Module[{rows=amplitudeDisplayRows[expr],boxes},
  If[Length[rows]<=3,Return[With[{shown=readableScalars[expr]},MakeBoxes[shown,form]]]];
  boxes=({signedCoefficientBoxes[#[[1]],form],With[{monomial=#[[2]]},MakeBoxes[monomial,form]]}& /@ rows);
  GridBox[Prepend[boxes,{StyleBox["Coefficient",FontWeight->"Bold"],StyleBox["Monomial",FontWeight->"Bold"]}],
    GridBoxAlignment->{"Columns"->{Right,Left}},
    GridBoxSpacings->{"Columns"->{{2}},"Rows"->{{0.7}}},
    GridBoxDividers->{"Columns"->{False,True,False},"Rows"->{False,True}}]
];
AmplitudeForm /: MakeBoxes[AmplitudeForm[expr_],form:(StandardForm|TraditionalForm)] :=
  With[{boxes=amplitudeDisplayBoxes[expr,form]},InterpretationBox[boxes,expr,Editable->False]];
PrepareTensorExpression[expr_] := Catch[Expand[expr /. TensorUnit[d_,k_,ll_,cc_] :>
  If[d==Length[cc],normalizeUnit[k,ll,cc],Throw[Failure["InvalidDegree",<||>],"TensorReduction"]]],"TensorReduction"];

massPolynomial[terms_List,n_Integer] := Total[Map[Function[t,
  If[Length[t[[1]]]!=n,Throw[Failure["MassDimension",<||>],"TensorReduction"]];
  t[[2]] Times@@MapThread[Power,{Array[Mass,n],t[[1]]}]],terms]];
massPolynomial[terms_Association,n_Integer] /; Length[terms]==0 := 0;
rowAdd[row_Association,m_List,c_] := Module[{r=row,k=monKey[m],v},
  v=Together[c+If[KeyExistsQ[r,k],r[k][[2]],0]];
  If[TrueQ[v==0],KeyDropFrom[r,k],AssociateTo[r,k->{m,v}]];r
];
readRow[raw_List,n_Integer] := Fold[rowAdd[#1,#2[[1]],massPolynomial[#2[[2]],n]/If[Length[#2]>=3,massPolynomial[#2[[3]],n],1]]&,<||>,raw];
readRow[raw_Association,n_Integer] /; Length[raw]==0 := <||>;
rowExpression[row_Association] := Total[(#[[2]] Times@@(Apply[TensorUnit,#]& /@ #[[1]]))& /@ Values[row]];
expressionRow[expr_,n_Integer] := Module[{e=PrepareTensorExpression[expr],vars,cr,r=<||>,m},
  If[FailureQ[e],Throw[e,"TensorReduction"]];
  vars=DeleteDuplicates[Cases[e,_TensorUnit,{0,Infinity}]];
  If[AnyTrue[vars,AnyTrue[#[[3]],#>n&]&],Throw[Failure["ParticleRange",<|"Particles"->n|>],"TensorReduction"]];
  If[vars==={},Return[If[TrueQ[e==0],<||>,<|monKey[{}]->{{},e}|>]]];
  If[!PolynomialQ[e,vars],Throw[Failure["NonPolynomialTensorInput",<|"Input"->e|>],"TensorReduction"]];
  cr=CoefficientRules[e,vars];
  Do[m=lexSort[Flatten[MapThread[ConstantArray,{List@@@vars,First[t]}],1]];
    r=rowAdd[r,m,Last[t]],{t,cr}];r
];
sameRows[a_Association,b_Association] := AllTrue[Union[Keys[a],Keys[b]],
  TrueQ[Together[If[KeyExistsQ[a,#],a[#][[2]],0]-If[KeyExistsQ[b,#],b[#][[2]],0]]==0]&];
scaleRow[r_Association,c_] := Map[{#[[1]],Together[c #[[2]]]}&,r];
rowGroup[r_Association] := Module[{d=Max[monDegree[#[[1]]]& /@ Values[r]]},
  If[Length[DeleteDuplicates[unbolded[#[[1]]]& /@ Select[Values[r],monDegree[#[[1]]]==d&]]]==1,2,1]];

LoadPreparedCatalog[file_String] := Module[{data=Quiet[Check[Import[file,"RawJSON"],$Failed]]},
  If[AssociationQ[data],PreparedCatalog[data],Failure["CatalogRead",<|"File"->file|>]]];
PreparedCatalog[data_Association] := Catch[Module[{index=<||>,n,bound,m,k,acts,row,head,base,ex},
  If[Lookup[data,"format",""]!="MassiveTensorPrepared-1",Throw[Failure["CatalogFormat",<||>],"TensorReduction"]];
  n=data["particles"];bound=data["order_bound"];
  Do[m=entry["monomial"];k=monKey[m];
    If[monDegree[m]>bound || KeyExistsQ[index,k],Throw[Failure["InvalidContext",<|"Monomial"->m|>],"TensorReduction"]];
    If[!sameRows[expressionRow[Times@@(Apply[TensorUnit,#]& /@ m),n],<|k->{m,1}|>],
      Throw[Failure["NonCanonicalContext",<|"Monomial"->m|>],"TensorReduction"]];
    acts=Table[row=readRow[a["identity"],n];
      If[!KeyExistsQ[row,k],Throw[Failure["MissingHead",<||>],"TensorReduction"]];
      head=row[k][[2]];
      If[!AllTrue[Values[KeyDrop[row,k]],lexLess[orderKey[#[[1]],bound],orderKey[m,bound]]&],
        Throw[Failure["NonDecreasingReplacement",<|"Monomial"->m|>],"TensorReduction"]];
      If[rowGroup[row]!=a["group"],Throw[Failure["WrongGroup",<||>],"TensorReduction"]];
      <|"Group"->a["group"],"Identity"->row,"HeadCoefficient"->head,"Source"->a["source"]|> ~Join~
        If[KeyExistsQ[a,"original_identity"],<|"OriginalIdentity"->readRow[a["original_identity"],n]|>,<||>] ~Join~
        If[KeyExistsQ[a,"preparation_proof"],<|"PreparationProof"->
          (<|"Monomial"->#["monomial"],"Identity"->readRow[#["identity"],n],"Source"->#["source"]|>& /@ a["preparation_proof"])|>,<||>],{a,entry["actions"]}];
    If[Length[acts]>1,base=scaleRow[acts[[1]]["Identity"],1/acts[[1]]["HeadCoefficient"]];
      If[!AllTrue[Rest[acts],sameRows[base,scaleRow[#["Identity"],1/#["HeadCoefficient"]]]&],
        Throw[Failure["AmbiguousReplacements",<|"Monomial"->m|>],"TensorReduction"]]];
    AssociateTo[index,k-><|"Monomial"->m,"Actions"->acts|>],{entry,data["entries"]}];
  Do[Do[If[!AllTrue[Keys[a["Identity"]],KeyExistsQ[index,#]&],
    Throw[Failure["MissingRHSCoverage",<||>],"TensorReduction"]],{a,entry["Actions"]}],{entry,Values[index]}];
  ex=Association[Map[(#["name"]->#)&,data["examples"]]];
  <|"Index"->index,"Examples"->ex,"Particles"->n,"OrderBound"->bound,
    "Information"->Join[KeyDrop[data,{"entries","examples"}],<|"ContextCount"->Length[index],"ExampleCount"->Length[ex]|>]|>
],"TensorReduction"];
CatalogInformation[cat_Association] := cat["Information"];
CatalogExample[cat_Association,name_String] := Catch[Module[{e=Lookup[cat["Examples"],name,Missing["UnknownExample"]],n=cat["Particles"]},
  If[MissingQ[e],Return[e]];
  <|"Input"->rowExpression[readRow[e["input"],n]],
    "Expected"->rowExpression[readRow[e["output"],n]]/massPolynomial[e["denominator"],n]|>
],"TensorReduction"];

Options[AmplitudeReduce]={AutoSavePreparedData->True,UsePreparedData->True,MaximumReductionSteps->200000,ReductionTrace->False};
SyntaxInformation[AmplitudeReduce]={"ArgumentsPattern"->{_,OptionsPattern[]}};
AmplitudeReduce[expr_,OptionsPattern[]] := Block[{$nativeTraceEnabled=TrueQ[OptionValue[ReductionTrace]]},Module[{answer,freshActions,freshPrepared,freshGraphs,freshProofs,freshSources,saveResult,saveSeconds=0,reductionSeconds,start=AbsoluteTime[]},
  $LastAmplitudeReduction=Missing["CallNotCompleted"];
  If[!ListQ[$nativeParents],Return[Failure["ParentDataUnavailable",<||>]]];
  If[!MemberQ[{True,False},OptionValue[UsePreparedData]],Return[Failure["InvalidOption",<||>]]];
  $ReductionQueryCount++;
  If[TrueQ[OptionValue[UsePreparedData]],answer=nativeAmplitudeReduce[expr,True,OptionValue[MaximumReductionSteps]],
  answer=Block[{$nativeActions=<||>,$nativePrepared=<||>,$nativeGraphs=<||>,$nativeDerivationProofs=<||>,$nativeActionSources=<||>},
    With[{value=nativeAmplitudeReduce[expr,False,OptionValue[MaximumReductionSteps]]},
      freshActions=$nativeActions;freshPrepared=$nativePrepared;freshGraphs=$nativeGraphs;freshProofs=$nativeDerivationProofs;freshSources=$nativeActionSources;value]];
  If[!FailureQ[answer],$nativeActions=Join[$nativeActions,freshActions];
    $nativePrepared=Join[$nativePrepared,freshPrepared];$nativeGraphs=Join[$nativeGraphs,freshGraphs];
    $nativeDerivationProofs=Join[$nativeDerivationProofs,freshProofs];$nativeActionSources=Join[$nativeActionSources,freshSources]]];
  reductionSeconds=AbsoluteTime[]-start;
  If[!FailureQ[answer] && TrueQ[OptionValue[AutoSavePreparedData]],
    {saveSeconds,saveResult}=AbsoluteTiming[saveNativePrepared[]];
    If[FailureQ[saveResult],Message[AmplitudeReduce::save,saveResult]]];
  $LastAmplitudeReduction=Join[$nativeRunSummary,<|"Expression"->answer,"Seconds"->reductionSeconds,
    "CacheSaveSeconds"->saveSeconds,"CacheSaveResult"->If[ValueQ[saveResult],saveResult,Missing["Disabled"]],
    "Particles"->$nativeParticles,"Completed"->!FailureQ[answer],"HistoricalCachedPreparationCounted"->False|>];
  answer
]];
Options[ReduceAmplitude]={ReductionTrace->True,MaximumReductionSteps->200000};
ReduceAmplitude[expr_,opts:OptionsPattern[]] := If[AssociationQ[$DefaultCatalog],
  ReduceAmplitude[expr,$DefaultCatalog,opts],
  Failure["DefaultCatalogUnavailable",<|"MessageTemplate"->"The bundled catalog did not load. Inspect $DefaultCatalog, then call LoadDefaultCatalog[]."|>]];
ReduceAmplitude[expr_,cat_Association,OptionsPattern[]] := Catch[Module[
  {pending=expressionRow[expr,cat["Particles"]],out=<||>,untouched,degree,keys,k,m,actions,a,
   coefficient,head,steps={},count=0,conditions={},bound=cat["OrderBound"],missing,stages={}},
  $ReductionQueryCount++;
  missing=Select[Values[pending],!KeyExistsQ[cat["Index"],monKey[#[[1]]]]&];
  If[missing=!={},Throw[Failure["CoverageGap",<|"UncoveredMonomials"->missing[[All,1]],
    "MessageTemplate"->"Prepare these complete contraction contexts offline; absence of a match does not prove irreducibility."|>],"TensorReduction"]];
  While[Length[pending]>0,
    degree=Max[monDegree[#[[1]]]& /@ Values[pending]];
    Do[untouched=<||>;
      While[Length[keys=Select[Keys[pending],monDegree[pending[#][[1]]]==degree&]]>0,
        k=Last[Sort[keys,lexLess[orderKey[pending[#1][[1]],bound],orderKey[pending[#2][[1]],bound]]&]];
        {m,coefficient}=pending[k];
        actions=Select[cat["Index"][k]["Actions"],#["Group"]==group&];
        If[actions==={},AssociateTo[untouched,k->pending[k]];KeyDropFrom[pending,k];Continue[]];
        a=First[actions];head=a["HeadCoefficient"];
        If[!AllTrue[Values[KeyDrop[a["Identity"],k]],lexLess[orderKey[#[[1]],bound],orderKey[m,bound]]&],
          Throw[Failure["NonDecreasingReplacement",<||>],"TensorReduction"]];
        If[!NumberQ[head],AppendTo[conditions,head!=0]];
        count++;If[count>OptionValue[MaximumReductionSteps],Throw[Failure["StepLimit",<|"Steps"->count-1|>],"TensorReduction"]];
        If[TrueQ[OptionValue[ReductionTrace]],AppendTo[steps,<|"InputMonomial"->m,"Coefficient"->coefficient,
          "Degree"->degree,"Group"->group,"Source"->a["Source"],"Identity"->rowExpression[a["Identity"]]|>]];
        Do[pending=rowAdd[pending,t[[1]],-coefficient t[[2]]/head],{t,Values[a["Identity"]]}]
      ];
      Do[pending=rowAdd[pending,t[[1]],t[[2]]],{t,Values[untouched]}];
      AppendTo[stages,{degree,group,count}],{group,{1,2}}];
    keys=Select[Keys[pending],monDegree[pending[#][[1]]]==degree&];
    If[AnyTrue[keys,AnyTrue[cat["Index"][#]["Actions"],#["Group"]==1&]&],
      Throw[Failure["StageCoverageGap",<|"Degree"->degree,"PartialExpression"->rowExpression[pending]+rowExpression[out]|>],"TensorReduction"]];
    Do[AssociateTo[out,k->pending[k]];KeyDropFrom[pending,k],{k,keys}]
  ];
  <|"Expression"->rowExpression[out],"Status"->"ReducedExpression",
    "UniquenessEstablished"->False,"Coverage"->"Listed full contraction contexts; frozen catalog",
    "Applications"->count,"NonzeroConditions"->DeleteDuplicates[conditions],"Trace"->steps,"Stages"->stages|>
],"TensorReduction"];

RunCatalogTests[cat_Association,names_:All] := Module[{ns=If[names===All,Keys[cat["Examples"]],names],e,r},
  TestReport[Table[e=CatalogExample[cat,name];r=ReduceAmplitude[e["Input"],cat,ReductionTrace->False];
    With[{ok=If[FailureQ[r],False,sameRows[expressionRow[r["Expression"],cat["Particles"]],expressionRow[e["Expected"],cat["Particles"]]]],id=name},
      VerificationTest[ok,True,TestID->id]],{name,ns}]]
];
ExportPreparationRequest[file_String,inputs_Association,n_Integer:4] := Catch[Module[{raw,masses=Array[Mass,n]},
  raw=Map[Function[e,Map[Function[t,
    If[!PolynomialQ[t[[2]],masses],Throw[Failure["PolynomialMassCoefficientsRequired",<||>],"TensorReduction"]];
    {t[[1]],Map[Function[rule,
      If[!IntegerQ[Last[rule]],Throw[Failure["IntegerCoefficientsRequired",<|"MessageTemplate"->"Clear a common rational denominator before exporting, then divide the final answer by it."|>],"TensorReduction"]];
      {First[rule],Last[rule]}],CoefficientRules[t[[2]],masses]]}],Values[expressionRow[e,n]]]],inputs];
  Export[file,raw,"RawJSON"]
],"TensorReduction"];
LoadDefaultCatalog[] := Module[{path=preparedDataPath[]},
  {$CatalogLoadingSeconds,$DefaultCatalog}=AbsoluteTiming[LoadPreparedCatalog[path]];
  If[FailureQ[$DefaultCatalog],Message[LoadDefaultCatalog::data,path]];
  $ReductionQueryCount=0;
  $DefaultCatalog
];
ReductionCacheInformation[] := Module[{cat=$DefaultCatalog,entries,actions},
  If[!AssociationQ[cat],Return[<|"PreparedTableLoaded"->False,"PreparedContexts"->0,
    "PreparedApplicationRecords"->0,"NativeParentRules"->Length[$nativeParents],
    "NativeRawContextCacheEntries"->Length[$nativeActions],
    "NativePreparedContextCacheEntries"->Length[$nativePrepared],
    "NativeGraphCacheEntries"->Length[$nativeGraphs],
    "PreparationProofsLoaded"->ListQ[$traceBundledProofs],
    "NativeDerivationProofCacheEntries"->Length[$nativeDerivationProofs],
    "NativeParentLoadingSeconds"->$nativeParentLoadingSeconds,
    "RuntimeAmplitudeResultCacheEntries"->0,"QueriesSinceLoad"->$ReductionQueryCount|>]];
  entries=Values[cat["Index"]];actions=Flatten[Lookup[entries,"Actions"],1];
  <|"PreparedTableLoaded"->True,"NativeParentRules"->Length[$nativeParents],
    "PreparedContexts"->Length[entries],"PreparedApplicationRecords"->Length[actions],
    "ContextsWithReplacements"->Count[entries,e_/;Length[e["Actions"]]>0],
    "RecordedNoMatchContexts"->Count[entries,e_/;Length[e["Actions"]]==0],
    "ReferenceExamplesNotUsedByReducer"->Length[cat["Examples"]],
    "RuntimeAmplitudeResultCacheEntries"->0,"RuntimeMemoizedFunctionEntries"->0,
    "NativeRawContextCacheEntries"->Length[$nativeActions],
    "NativePreparedContextCacheEntries"->Length[$nativePrepared],
    "NativeGraphCacheEntries"->Length[$nativeGraphs],
    "NativeParentLoadingSeconds"->$nativeParentLoadingSeconds,
    "QueriesSinceLoad"->$ReductionQueryCount,"CatalogBytes"->ByteCount[cat],
    "PreparedDataFileBytes"->FileByteCount[preparedDataPath[]],
    "PreparationProofsLoaded"->ListQ[$traceBundledProofs],"NativeDerivationProofCacheEntries"->Length[$nativeDerivationProofs],
    "ParentConstructionIncludedInQuery"->False|>
];
BenchmarkAmplitude[expr_,repeats_Integer:9] := Module[{before=$ReductionQueryCount,t,answer,warm,check},
  If[repeats<1,Return[Failure["InvalidRepetitions",<||>]]];
  {t,answer}=AbsoluteTiming[ReduceAmplitude[expr,ReductionTrace->False]];
  If[FailureQ[answer],Return[answer]];
  warm=Table[First[AbsoluteTiming[check=ReduceAmplitude[expr,ReductionTrace->False]]],{repeats}];
  If[FailureQ[check] || !SameQ[check["Expression"],answer["Expression"]],Return[Failure["BenchmarkResultMismatch",<||>]]];
  <|"FirstQuerySeconds"->If[before==0,t,Missing["PriorQueriesExist"]],
    "FirstMeasuredQuerySeconds"->t,"PriorQueryCount"->before,"WarmMedianSeconds"->Median[warm],
    "WarmTimesSeconds"->warm,"TraceEnabled"->False,"LoadingSeconds"->$CatalogLoadingSeconds,
    "Result"->answer,"RuntimeResultMemoization"->False|>
];
LoadDefaultCatalog::data = "The bundled catalog could not be loaded from `1`. Keep sample_data_n4 beside MassiveTensorReduction.m.";
Options[LoadRuleCatalog]={UsePreparedData->True};
LoadRuleCatalog[file_String,OptionsPattern[]] := Module[{raw,status,path,prepared=Missing["NotLoaded"],data},
 raw=Quiet[Check[Import[file,"RawJSON"],$Failed]];
 If[!AssociationQ[raw] || Lookup[raw,"format",""]=!="MassiveTensorParents-1" || !IntegerQ[Lookup[raw,"particles",None]],Return[Failure["InvalidRuleCatalog",<||>]]];
 If[!MemberQ[{True,False},OptionValue[UsePreparedData]],Return[Failure["InvalidOption",<||>]]];
 path=FileNameJoin[{DirectoryName[ExpandFileName[file]],"sample_data_n"<>ToString[raw["particles"]],"PreparedApplications.json"}];
 If[TrueQ[OptionValue[UsePreparedData]] && FileExistsQ[path],
 data=Import[path,"RawJSON"];
 If[Lookup[data,"particles",None]=!=raw["particles"] || Lookup[data,"parent_sha256",""]=!=IntegerString[FileHash[file,"SHA256"],16,64],Return[Failure["PreparedParentMismatch",<|"Stored"->Lookup[data,"parent_sha256",""],"Actual"->IntegerString[FileHash[file,"SHA256"],16,64],"N"->Lookup[data,"particles",None],"ExpectedN"->raw["particles"]|>]]];
 prepared=PreparedCatalog[data];If[FailureQ[prepared],Return[prepared]]];
 $nativeParentPath=ExpandFileName[file];$nativePreparedPath=path;status=loadNativeParents[];
 $nativeGraphs=<||>;$nativeActions=<||>;$nativePrepared=<||>;$nativePreparedMonomials=<||>;$nativeActionSources=<||>;$nativeDerivationProofs=<||>;$persistedNativeKeys={};$traceBundledProofs=.;$DefaultCatalog=prepared;
 <|"Particles"->$nativeParticles,"Rules"->status,"PreparedDataLoaded"->AssociationQ[prepared]|>
];
Get[FileNameJoin[{$packageDirectory,"ParentPreparation.m"}]];
Get[FileNameJoin[{$packageDirectory,"ReductionSteps.m"}]];
Get[FileNameJoin[{$packageDirectory,"PersistentPreparedData.m"}]];
$LastAmplitudeReduction=Missing["NoReductionYet"];
{$nativeParentLoadingSeconds,$nativeParentLoadStatus}=AbsoluteTiming[loadNativeParents[]];
If[TrueQ[$LoadPreparedTable],
  LoadDefaultCatalog[],
  $DefaultCatalog=Missing["PreparedTableNotLoaded"];
  $CatalogLoadingSeconds=0;
  $ReductionQueryCount=0
];
End[];
(* Deliberate package-local Square shadows the System name; its definitions
   and syntax metadata remain untouched. Silence only this expected notice. *)
Quiet[EndPackage[],{MassiveTensorReduction`Square::shdw,System`Square::shdw,General::shdw}];

