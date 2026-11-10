$nativePreparedPath=FileNameJoin[{$packageDirectory,"sample_data_n4","PreparedApplications.json"}];
$nativeParticles=4; $nativeParentPath=FileNameJoin[{$packageDirectory,"NativeRules_n4.json"}];
(* Loaded inside MassiveTensorReduction`Private`. Native contextual matching
   and RHS preparation. NativeRules_n4.json contains no contextual descendants. *)
$nativePreparedMonomials=<||>; $nativeGraphs=<||>; $nativeActions=<||>; $nativePrepared=<||>; $nativeActionSources=<||>;
nativeHead[row_Association] := Last[Sort[Values[row][[All,1]],lexLess[orderKey[#1,16],orderKey[#2,16]]&]];
nativeGraph[mon_List] := Module[{key=monKey[mon],ll={},bb={},ee={},first,a},
 If[KeyExistsQ[$nativeGraphs,key],Return[$nativeGraphs[key]]];
 Do[first=Length[ll]+1;
   Do[a=Length[ll]+1;ll=Join[ll,{u[[3,j]],u[[3,Mod[j,Length[u[[3]]]]+1]]}];
     AppendTo[bb,{a,a+1,u[[4,j]]}];If[j>1,AppendTo[ee,{a-1,a}]],{j,u[[1]]}];
   If[u[[2]]==1,AppendTo[ee,{first,Length[ll]}]],{u,mon}];
 AssociateTo[$nativeGraphs,key->{ll,bb,ee}];{ll,bb,ee}
];
nativeNormalize[{ll_,bb_,ee_}] := Module[{ba=<||>,ea=<||>,remaining,ends,start,v,w,c,sgn,labels,colors,kind,result=1,pair},
 Do[AssociateTo[ba,{e[[1]]->{e[[2]],e[[3]],1},e[[2]]->{e[[1]],e[[3]],-1}}],{e,bb}];
 Do[AssociateTo[ea,{e[[1]]->{e[[2]],1},e[[2]]->{e[[1]],-1}}],{e,ee}];
 remaining=Sort[Keys[ba]];
 While[remaining=!={},ends=Complement[remaining,Keys[ea]];
   kind=If[ends==={},1,0];start=First[If[ends==={},remaining,ends]];
   labels={ll[[start]]};colors={};sgn=1;v=start;
   While[True,{w,c,pair}=ba[v];sgn*=pair;
     remaining=Complement[remaining,{v,w}];AppendTo[colors,c];
     If[!KeyExistsQ[ea,w],AppendTo[labels,ll[[w]]];Break[]];
     {v,pair}=ea[w];sgn*=pair;If[v==start,sgn*=-1;Break[]];AppendTo[labels,ll[[w]]]];
   result*=sgn normalizeUnit[kind,labels,colors];If[result===0,Break[]]];
 result
];
nativeQuotient[mon_List,factors_List] := Module[{rest=mon,pos},
 Do[pos=FirstPosition[rest,u,Missing["Absent"],{1}];
   If[MissingQ[pos],Return[$Failed]];rest=Delete[rest,pos],{u,factors}];rest
];
nativeMultiply[row_Association,rest_List] := Module[{out=<||>},
 Do[out=rowAdd[out,lexSort[Join[t[[1]],rest]],t[[2]]],{t,Values[row]}];out
];
nativeGraphSignature[{ll_,bb_,ee_}] := Sort[({#[[3]],Sort[ll[[#[[1;;2]]]]]}& /@ bb)];
nativeSignatureContains[input_,needed_] := AllTrue[Tally[needed],Count[input,#[[1]]]>=#[[2]]&];
nativeMatches[pattern_,host_] := Module[{pl,pb,pe,ll,bb,ee,poss,seq,visit,found={},ea=<||>},
 {pl,pb,pe}=pattern;{ll,bb,ee}=host;
 poss=Table[Select[Range[Length[bb]],bb[[#,3]]==e[[3]] && Sort[ll[[bb[[#,1;;2]]]]]==Sort[pl[[e[[1;;2]]]]]&],{e,pb}];
 If[MemberQ[poss,{}],Return[{}]];seq=Ordering[Length /@ poss];
 Do[AssociateTo[ea,{e[[1]]->e[[2]],e[[2]]->e[[1]]}],{e,ee}];
 visit[k_,used_,mapping_] := Module[{a,z,c,x,y,map},
   If[k>Length[seq],AppendTo[found,{Sort[used],mapping}];Return[]];
   {a,z,c}=pb[[seq[[k]]]];
   Do[If[MemberQ[used,j],Continue[]];{x,y}=bb[[j,1;;2]];
     If[pl[[a]]!=ll[[x]],{x,y}={y,x}];map=Join[mapping,<|a->x,z->y|>];
     If[AllTrue[pe,!KeyExistsQ[map,#[[1]]] || !KeyExistsQ[map,#[[2]]] || Lookup[ea,map[#[[1]]],0]==map[#[[2]]]&],
       visit[k+1,Append[used,j],map]],{j,poss[[seq[[k]]]]}]];
 visit[1,{},<||>];DeleteDuplicates[found]
];
nativeEmbed[row_,pattern_,host_,selected_,mapping_] := Module[
 {ll,bb,ee,internal,remaining,ports,context,holes,external,extmap,extlabels,extbb,groups,labels,off,
  tl,tb,te,free,choices,sub,eps,brackets,result=0},
 {ll,bb,ee}=host;internal=Sort /@ ((Lookup[mapping,#]&) /@ pattern[[3]]);
 remaining=Delete[bb,List /@ selected];ports=Flatten[bb[[selected,1;;2]]];
 context=Select[ee,!MemberQ[internal,Sort[#]]&];
 If[AnyTrue[context,AllTrue[#,MemberQ[ports,#]&]&],Return[<||>]];
 holes=Intersection[Flatten[context],ports];external=Union[Flatten[remaining[[All,1;;2]]]];
 extmap=AssociationThread[external,Range[Length[external]]];extlabels=ll[[external]];off=Length[external];
 extbb=({extmap[#[[1]]],extmap[#[[2]]],#[[3]]}& /@ remaining);
 labels=Union[ll[[holes]]];groups=Table[Select[holes,ll[[#]]==label&],{label,labels}];
 Do[{tl,tb,te}=nativeGraph[t[[1]]];free=Complement[Range[Length[tl]],Flatten[te]];
   choices=MapThread[Function[{label,hs},Permutations[Select[free,tl[[#]]==label&],{Length[hs]}]],{labels,groups}];
   Do[sub=extmap;
     Do[AssociateTo[sub,Thread[groups[[j]]->(off+assign[[j]])]],{j,Length[groups]}];
     eps=Join[(#+off)& /@ te,(Lookup[sub,#]&) /@ context];
     brackets=Join[extbb,({#[[1]]+off,#[[2]]+off,#[[3]]}& /@ tb)];
     result+=t[[2]] nativeNormalize[{Join[extlabels,tl],brackets,eps}],{assign,Tuples[choices]}],{t,Values[row]}];
 expressionRow[Expand[result],$nativeParticles]
];
loadNativeParents[] := Module[{raw,parents},
 raw=Import[$nativeParentPath,"RawJSON"];
 If[!AssociationQ[raw] || Lookup[raw,"format",""]=!="MassiveTensorParents-1",
   Return[Failure["ParentDataUnavailable",<||>]]];
 $nativeParticles=Lookup[raw,"particles",4];
 parents=Map[Function[p,Join[p,<|"Row"->readRow[p["row"],$nativeParticles],
   "Patterns"->Map[Function[g,<|"Graph"->g["graph"],"Signature"->nativeGraphSignature[g["graph"]]|>],p["patterns"]]|>]],raw["parents"]];
 parents=Map[Join[#,<|"Head"->If[Length[#["Row"]]>0,nativeHead[#["Row"]],{}]|>]&,parents];
 $nativeParents=parents;$nativeDerived=Select[parents,!TrueQ[#["original"]]&];
 $parentSerialByID=AssociationThread[Lookup[parents,"id"],Range[Length[parents]]];
 $parentFamilyByID=AssociationThread[Lookup[parents,"id"],Lookup[parents,"family"]];
 $parentLabelsByID=AssociationThread[Lookup[parents,"id"],Lookup[parents,"labels"]];
 $nativeOriginal=Association[(ToString[{#["family"],#["labels"]},InputForm]->#)& /@ Select[parents,TrueQ[#["original"]]&]];
 Length[parents]
];
nativeOriginalRow[ll_,bb_,ee_,kind_,place_] := Module[{a,z,x,y,color,copy,expr=0,endpoints,leading,parent,key,selectedSig,allowed},
 If[kind==="M",
   {x,y}=place;
   endpoints=Reverse[Sort[Table[With[{edge=SelectFirst[bb,MemberQ[#[[1;;2]],v]&]},
     {edge[[3]],ll[[First[DeleteCases[edge[[1;;2]],v]]]]}],{v,{x,y}}]]];
   leading=First[Complement[Range[$nativeParticles],endpoints[[All,2]]]];
   If[ll[[x]]!=leading,Return[<||>]];
   Do[copy=ll;copy[[x]]=k;copy[[y]]=k;expr+=nativeNormalize[{copy,bb,ee}],{k,$nativeParticles}],
   {a,z,color}=bb[[place[[1]]]];{x,y}=bb[[place[[2]],1;;2]];
   key=ToString[{"S",Prepend[Sort[ll[[{a,z,x,y}]]],color]},InputForm];
   If[!KeyExistsQ[$nativeOriginal,key],Return[<||>]];
   parent=$nativeOriginal[key];
   If[Length[DeleteDuplicates[ll[[{a,z,x,y}]]]]==4,
     selectedSig=nativeGraphSignature[{ll,bb[[place]],{}}];
     allowed=Lookup[parent["Patterns"],"Signature"];
     If[!MemberQ[allowed,selectedSig],Return[<||>]]];
   expr=nativeNormalize[{ll,bb,ee}];copy=bb;
   copy[[place]]={{a,x,color},{z,y,color}};expr-=nativeNormalize[{ll,copy,ee}];
   copy[[place]]={{a,y,color},{z,x,color}};expr+=nativeNormalize[{ll,copy,ee}]];
 expressionRow[Expand[expr],$nativeParticles]
];
nativeOriginalSource[ll_,bb_,kind_,place_] := Module[{labels,endpoints,parent},
 If[kind==="M",
   endpoints=Reverse[Sort[Table[With[{edge=SelectFirst[bb,MemberQ[#[[1;;2]],v]&]},
     {edge[[3]],ll[[First[DeleteCases[edge[[1;;2]],v]]]]}],{v,place}]]];labels=endpoints[[All,2]],
   labels=Prepend[Sort[ll[[Flatten[bb[[place,1;;2]]]]]],bb[[First[place],3]]]
 ];
 parent=Lookup[$nativeOriginal,ToString[{kind,labels},InputForm],Missing["UnknownParent"]];
 If[MissingQ[parent],<||>,<|"parent"->parent["id"],"kind"->kind,"placement"->place|>]
];
nativeRawActions[mon_List] := Module[{key=monKey[mon],actions={},sources={},seen=<||>,accept,host,ll,bb,ee,edgeof=<||>,row,rest,signature},
 If[KeyExistsQ[$nativeActions,key],Return[$nativeActions[key]]];
 accept[r_,source_] := Module[{normalized,code,h},
   If[Length[r]==0 || nativeHead[r]=!=mon,Return[]];
   h=r[key][[2]];normalized=Map[{#[[1]],Together[#[[2]]/h]}&,r];
   code=ToString[Sort[Values[normalized]],InputForm];
   If[!KeyExistsQ[seen,code],AssociateTo[seen,code->True];AppendTo[actions,normalized];AppendTo[sources,source]]];
 (* Untouched products of derived parent LMs precede contextual matches. *)
 Do[rest=nativeQuotient[mon,parent["Head"]];
   If[rest=!=$Failed,accept[nativeMultiply[parent["Row"],rest],<|"parent"->parent["id"],"kind"->"derived-product"|>]],{parent,$nativeDerived}];
 host=nativeGraph[mon];{ll,bb,ee}=host;
 Do[AssociateTo[edgeof,{bb[[j,1]]->j,bb[[j,2]]->j}],{j,Length[bb]}];
 Do[If[bb[[edgeof[e[[1]]],3]]!=bb[[edgeof[e[[2]]],3]],accept[nativeOriginalRow[ll,bb,ee,"M",e],nativeOriginalSource[ll,bb,"M",e]]],{e,ee}];
 Do[If[bb[[pair[[1]],3]]==bb[[pair[[2]],3]] && Max[Last /@ Tally[ll[[Flatten[bb[[pair,1;;2]]]]]]]<=2,
   accept[nativeOriginalRow[ll,bb,ee,"S",pair],nativeOriginalSource[ll,bb,"S",pair]]],{pair,Subsets[Range[Length[bb]],{2}]}];
 signature=nativeGraphSignature[host];
 Do[Do[If[Length[pat["Graph"][[2]]]>=Length[bb] || !nativeSignatureContains[signature,pat["Signature"]],Continue[]];
   Do[accept[nativeEmbed[parent["Row"],pat["Graph"],host,match[[1]],match[[2]]],
     <|"parent"->parent["id"],"kind"->"derived-context","selected_edges"->match[[1]],"port_map"->match[[2]]|>],
     {match,nativeMatches[pat["Graph"],host]}],{pat,parent["Patterns"]}],{parent,$nativeDerived}];
 AssociateTo[$nativeActions,key->actions];AssociateTo[$nativeActionSources,key->sources];actions
];
nativeNeutral[row_Association] := Module[{pending=row,out=<||>,mon,key,actions,co},
 While[Length[pending]>0,mon=nativeHead[pending];key=monKey[mon];actions=nativeRawActions[mon];
   If[actions==={},AssociateTo[out,key->pending[key]];KeyDropFrom[pending,key];Continue[]];
   If[$nativeStepCount>=$nativeStepLimit,Throw[Failure["StepLimit",<||>],"TensorReduction"]];$nativeStepCount++;
   $nativePreparationStepCount++;
   co=pending[key][[2]];
   Do[pending=rowAdd[pending,t[[1]],-co t[[2]]],{t,Values[First[actions]]}];
   If[$nativeTraceEnabled,AppendTo[$nativeProofSteps,<|"Monomial"->mon,"Identity"->First[actions],"Source"->First[$nativeActionSources[key]]|>]]];
 out
];
nativePreparedActions[mon_List] := Module[{key=monKey[mon],prepared={},tail,r,top,group,proof,raw,source},
 If[KeyExistsQ[$nativePrepared,key],Return[$nativePrepared[key]]];
 Do[{raw,source}=pair;tail=KeyDrop[raw,key];
   If[$nativeTraceEnabled,proof=Block[{$nativeProofSteps={}},r=nativeNeutral[tail];$nativeProofSteps],r=nativeNeutral[tail]];
   r=rowAdd[r,mon,1];
   top=Select[Values[r],monDegree[#[[1]]]==monDegree[mon]&];
   group=If[Length[DeleteDuplicates[unbolded[#[[1]]]& /@ top]]==1,2,1];
   AppendTo[prepared,Join[<|"Group"->group,"Identity"->r,"HeadCoefficient"->1,"OriginalIdentity"->raw,"Source"->source|>,
     If[$nativeTraceEnabled,<|"PreparationProof"->proof|>,<||>]]],{pair,Transpose[{nativeRawActions[mon],$nativeActionSources[key]}]}];
 AssociateTo[$nativePreparedMonomials,key->mon];AssociateTo[$nativePrepared,key->prepared];prepared
];
nativeAvailableActions[mon_,usePrepared_] := Module[{key=monKey[mon]},
 If[TrueQ[usePrepared] && AssociationQ[$DefaultCatalog] && $DefaultCatalog["Particles"]==$nativeParticles && KeyExistsQ[$DefaultCatalog["Index"],key],
   $DefaultCatalog["Index"][key]["Actions"],nativePreparedActions[mon]]
];
nativeAmplitudeReduce[expr_,usePrepared_,limit_] := Block[
 {$nativeStepCount=0,$nativeStepLimit=limit,$nativePreparationStepCount=0,
  $nativeEvents={},$nativeInitialRow=<||>},Module[{value},
 value=Catch[Module[
 {pending=expressionRow[expr,$nativeParticles],out=<||>,degree,keys,key,mon,co,actions,untouched,before},
 If[$nativeTraceEnabled,$nativeInitialRow=pending];
 If[AnyTrue[Values[pending],monDegree[#[[1]]]>16&],Throw[Failure["OrderBoundExceeded",<|"OrderBound"->16|>],"TensorReduction"]];
 While[Length[pending]>0,degree=Max[monDegree[#[[1]]]& /@ Values[pending]];
   Do[untouched=<||>;
     While[Length[keys=Select[Keys[pending],monDegree[pending[#][[1]]]==degree&]]>0,
       key=Last[Sort[keys,lexLess[orderKey[pending[#1][[1]],16],orderKey[pending[#2][[1]],16]]&]];
       {mon,co}=pending[key];
       actions=Select[nativeAvailableActions[mon,usePrepared],#["Group"]==group&];
       If[actions==={},AssociateTo[untouched,key->pending[key]];KeyDropFrom[pending,key];Continue[]];
       If[!AllTrue[Values[KeyDrop[First[actions]["Identity"],key]],lexLess[orderKey[#[[1]],16],orderKey[mon,16]]&],
         Throw[Failure["NonDecreasingReplacement",<||>],"TensorReduction"]];
       If[$nativeStepCount>=limit,Throw[Failure["StepLimit",<||>],"TensorReduction"]];$nativeStepCount++;
       If[$nativeTraceEnabled,before=nativeMergeRows[pending,out,untouched]];
       Do[pending=rowAdd[pending,t[[1]],-co t[[2]]/First[actions]["HeadCoefficient"]],{t,Values[First[actions]["Identity"]]}];
       If[$nativeTraceEnabled,nativeExpandApplication[First[actions],mon,co,before,nativeMergeRows[pending,out,untouched]]]];
     Do[pending=rowAdd[pending,t[[1]],t[[2]]],{t,Values[untouched]}],{group,{1,2}}];
   keys=Select[Keys[pending],monDegree[pending[#][[1]]]==degree&];
   Do[If[AnyTrue[nativeAvailableActions[pending[key][[1]],usePrepared],#["Group"]==1&],
       Throw[Failure["StageCoverageGap",<||>],"TensorReduction"]];
     AssociateTo[out,key->pending[key]];KeyDropFrom[pending,key],{key,keys}]];
 rowExpression[out]
],"TensorReduction"];
 $nativeRunSummary=<|"RuleApplications"->$nativeStepCount,
   "AmplitudeApplications"->$nativeStepCount-$nativePreparationStepCount,
   "PreparationApplications"->$nativePreparationStepCount,
   "TraceRecorded"->$nativeTraceEnabled|>;
 If[$nativeTraceEnabled,AssociateTo[$nativeRunSummary,
   {"InitialRow"->$nativeInitialRow,"Events"->$nativeEvents,"DisplayedSteps"->Length[$nativeEvents]}]];
 value
]];
