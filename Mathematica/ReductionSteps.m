(* Executed inside Private. A prepared replacement's proof is lifted back
   into the input amplitude; preparation itself is never shown as a timeline. *)
$traceBundledProofs=.;$nativeDerivationProofs=<||>;
nativeMergeRows[rows__Association] := Fold[rowAdd[#1,#2[[1]],#2[[2]]]&,<||>,Flatten[Values /@ {rows},1]];
nativeSelectedProof[action_,mon_] := Module[{id,record,raw,proof,key,tail},
 If[KeyExistsQ[action,"OriginalIdentity"],
   raw=action["OriginalIdentity"];
   If[KeyExistsQ[action,"PreparationProof"],Return[{raw,action["PreparationProof"]}]];
   key=ToString[Sort[Values[raw]],InputForm];
   If[KeyExistsQ[$nativeDerivationProofs,key],Return[{raw,$nativeDerivationProofs[key]}]];
   tail=KeyDrop[raw,monKey[mon]];
   proof=Block[{$nativeProofSteps={}},nativeNeutral[tail];$nativeProofSteps];
   AssociateTo[$nativeDerivationProofs,key->proof];Return[{raw,proof}]];
 id=Lookup[Lookup[action,"Source",<||>],"requested_preparation",Missing["NoProof"]];
 If[!IntegerQ[id],Throw[Failure["DerivationUnavailable",<||>],"TensorReduction"]];
 If[!ListQ[$traceBundledProofs],$traceBundledProofs=Import[
   FileNameJoin[{DirectoryName[$nativePreparedPath],"PreparationProofs.json"}],"RawJSON"]];
 If[!ListQ[$traceBundledProofs] || id<0 || id>=Length[$traceBundledProofs],
   Throw[Failure["DerivationUnavailable",<||>],"TensorReduction"]];
 record=$traceBundledProofs[[id+1]];
 If[record["id"]!=id || record["input"]=!=mon,Throw[Failure["DerivationMismatch",<||>],"TensorReduction"]];
 {readRow[record["original_identity"],$nativeParticles],
   (<|"Monomial"->#["input"],"Identity"->readRow[#["identity"],$nativeParticles],"Source"->#["source"]|>& /@ record["rhs_reduction_steps"])}
];
traceApply[row_,mon_,co_,identity_] := Module[{result=row,key=monKey[mon],head},
 If[!KeyExistsQ[identity,key] || nativeHead[identity]=!=mon,
   Throw[Failure["TraceRuleNotLeading",<||>],"TensorReduction"]];
 head=identity[key][[2]];
 Do[result=rowAdd[result,t[[1]],-co t[[2]]/head],{t,Values[identity]}];result
];
traceUsedParentIDs[source_Association] := DeleteDuplicates[Join[
 If[IntegerQ[Lookup[source,"parent",None]],{source["parent"]},{}],
 Flatten[traceUsedParentIDs[Lookup[#,"source",<||>]]& /@ Lookup[source,"momentum_steps",{}]]]];
traceParentMetadata[source_] := Module[{id=Lookup[source,"parent",Missing["Unavailable"]],ids},
 ids=traceUsedParentIDs[source];
 <|"ParentCatalogID"->id,"ParentRuleSerial"->Lookup[$parentSerialByID,id,Missing["Unavailable"]],
   "UsedParentCatalogIDs"->ids,"UsedParentRuleSerials"->Lookup[$parentSerialByID,ids,Missing["Unavailable"]],
   "CombinedApplication"->(TrueQ[Lookup[source,"momentum_reduced",False]] || Length[Lookup[source,"momentum_steps",{}]]>0)|>
];
traceParentName[id_] := Module[{family=Lookup[$parentFamilyByID,id,"unknown"],labels=Lookup[$parentLabelsByID,id,{}],notation,number},
 number="parent rule #"<>ToString[Lookup[$parentSerialByID,id,"?"]];
 notation=Switch[family,
   "M",DisplayForm[SubscriptBox[StyleBox["M",FontFamily->"Arial",FontSlant->"Plain"],RowBox[ToString /@ labels]]],
   "S",DisplayForm[SubsuperscriptBox[StyleBox["S",FontFamily->"Arial",FontSlant->"Plain"],
       RowBox[ToString /@ Rest[labels]],If[First[labels]==1,"a","s"]]],
   _,"Generated parent"];
 Row[{notation,"  —  ",number}]
];
traceParentLabel[event_] := Module[{source=Lookup[event,"Source",<||>],meta,labels},
 meta=traceParentMetadata[source];
 If[meta["UsedParentCatalogIDs"]==={},Return[Style["Parent provenance unavailable in this older trace; rerun with ReductionTrace -> True.",Darker[Orange]]]];
 labels=traceParentName /@ meta["UsedParentCatalogIDs"];
 Style[Row[Join[If[meta["CombinedApplication"],{"Combined application: "},{}],Riffle[labels," + "]]],Bold]
];
nativeExpandApplication[action_,mon_,co_,before_,expected_] := Module[
 {raw,proof,state=before,next,tail,key=monKey[mon],factor,submon,subco,identity,append},
 {raw,proof}=nativeSelectedProof[action,mon];factor=-co/raw[key][[2]];
 append[m_,c_,rule_,source_] := (
   next=traceApply[state,m,c,rule];
   AppendTo[$nativeEvents,Join[<|"Step"->Length[$nativeEvents]+1,"Monomial"->m,
     "Coefficient"->c,"Identity"->rule,"Source"->source,"Before"->state,"After"->next|>,traceParentMetadata[source]]];state=next);
 append[mon,co,raw,Lookup[action,"Source",<||>]];
 tail=KeyDrop[raw,key];
 Do[submon=step["Monomial"];identity=step["Identity"];
   subco=traceCoefficient[tail,monKey[submon]];
   If[TrueQ[subco==0],Throw[Failure["TraceProofMismatch",<||>],"TensorReduction"]];
   append[submon,Together[factor subco],identity,Lookup[step,"Source",<||>]];
   tail=traceApply[tail,submon,subco,identity],{step,proof}];
 If[!sameRows[state,expected],Throw[Failure["TraceEndpointMismatch",<||>],"TensorReduction"]];
 state
];
traceCoefficient[row_,key_] := If[KeyExistsQ[row,key],row[key][[2]],0];
traceMonomialDisplay[mon_] := Module[{expr=Times@@(Apply[TensorUnit,#]& /@ mon),rows},
 rows=amplitudeDisplayRows[expr];
 If[Length[rows]==1,First[rows],{1,expr}]
];
traceHighlightParts[event_] := Module[{row=event["Identity"],mon=event["Monomial"],shared={},count,reduced=<||>,q,key,head,a,b,c,
  source=Lookup[event,"Source",<||>],id,parent,plain=False},
 Do[count=Min[Count[#[[1]],u]& /@ Values[row]];
   shared=Join[shared,ConstantArray[u,count]],{u,DeleteDuplicates[mon]}];
 Do[q=nativeQuotient[t[[1]],shared];
   If[q===$Failed,Return[Failure["HighlightFactorMismatch",<||>]]];
   reduced=rowAdd[reduced,q,t[[2]]],{t,Values[row]}];
 If[!sameRows[nativeMultiply[reduced,shared],row],Return[Failure["HighlightFactorMismatch",<||>]]];
 q=nativeQuotient[mon,shared];key=monKey[q];head=reduced[key][[2]];
 a=Times@@(Apply[TensorUnit,#]& /@ shared);b=Times@@(Apply[TensorUnit,#]& /@ q);
 c=-rowExpression[KeyDrop[reduced,key]]/head;
 id=Lookup[source,"parent",Missing["Unavailable"]];
 If[KeyExistsQ[$parentSerialByID,id] && !TrueQ[traceParentMetadata[source]["CombinedApplication"]],
   parent=$nativeParents[[$parentSerialByID[id]]]["Row"];
   If[KeyExistsQ[parent,key],plain=sameRows[scaleRow[reduced,1/head],scaleRow[parent,1/parent[key][[2]]]]]];
 <|"Spectator"->a,"LeftBlock"->b,"RightBlock"->c,"SpectatorMonomial"->shared,
   "ExactParentFactorization"->plain,"CombinedApplication"->TrueQ[traceParentMetadata[source]["CombinedApplication"]]|>
];
traceViewData[report_Association] := Module[{seen=<||>,visit,final,keys,front,back,display},
 visit[row_] := Do[If[!KeyExistsQ[seen,k],AssociateTo[seen,k->row[k][[1]]]],{k,Keys[row]}];
 visit[report["InitialRow"]];
 Do[visit[e["Before"]];visit[e["Identity"]];visit[e["After"]],{e,report["Events"]}];
 final=expressionRow[report["Expression"],Lookup[report,"Particles",$nativeParticles]];visit[final];keys=Keys[seen];
 front=Select[keys,KeyExistsQ[final,#]&];back=Select[keys,!KeyExistsQ[final,#]&];keys=Join[front,back];
 display=Association[(#->traceMonomialDisplay[seen[#]])& /@ keys];
 <|"Report"->report,"Keys"->keys,"Monomials"->seen,"Display"->display,
   "FinalKeys"->front,"OtherKeys"->back,"RuleHighlights"->(traceHighlightParts /@ report["Events"])|>
];
traceSignedCoefficient[c_] := If[TrueQ[c==0],0,DisplayForm[signedCoefficientBoxes[c,StandardForm]]];
traceHighlightedProduct[a_,block_] := Row[{
 If[a===1,Nothing,Row[{AmplitudeForm[a]," \[Times] "}]],
 Style[If[Head[block]===Plus,Row[{"(",AmplitudeForm[block],")"}],AmplitudeForm[block]],
   RGBColor[0.08,0.28,0.72],Background->RGBColor[0.93,0.96,1],Bold]}];
traceRule[event_,parts_] := Module[{key=monKey[event["Monomial"]]},
 Column[{traceParentLabel[event],
   Row[{traceHighlightedProduct[parts["Spectator"],parts["LeftBlock"]],"  \[LongRightArrow]  ",
     traceHighlightedProduct[parts["Spectator"],parts["RightBlock"]]}],
   Style[Which[TrueQ[parts["CombinedApplication"]],"Blue: changed block of the combined application; unchanged tensor factors are unhighlighted.",
     TrueQ[parts["ExactParentFactorization"]],"Blue: parent B and C. Unhighlighted: the same spectator A on both sides.",
     True,"Blue: the contracted replacement block, including attached contractions; unchanged tensor factors are unhighlighted."],Small],
   Row[{"Applied coefficient: ",AmplitudeForm[event["Coefficient"]],
     If[TrueQ[Together[traceCoefficient[event["Before"],key]-event["Coefficient"]]==0],"",
       " (a portion of the collected coefficient)"]}]},Spacings->0.5]
];
traceFrame[data_,step_Integer] := Module[{report=data["Report"],event,main,rows,headers,rule,colors,display,k},
 If[step==0,main=report["InitialRow"];rule=Style["Initial amplitude (no rule applied)",Bold],
   event=report["Events"][[step]];main=event["After"];rule=traceRule[event,data["RuleHighlights"][[step]]]];
 headers={"Coefficient","Monomial"};
 rows=Table[display=data["Display"][k];
   {traceSignedCoefficient[display[[1]] traceCoefficient[main,k]],
     With[{mon=display[[2]]},DisplayForm[MakeBoxes[mon,StandardForm]]]}, {k,data["Keys"]}];
 colors=Prepend[Table[If[MemberQ[data["FinalKeys"],k],RGBColor[0.92,0.97,0.92],White],{k,data["Keys"]}],LightGray];
 Column[{Row[{"Step ",step," / ",Length[report["Events"]]}],Pane[rule,{Automatic,UpTo[230]},Scrollbars->Automatic],
   Row[{"Final support: ",Length[data["FinalKeys"]]," monomials first; all other rows are retained with zero coefficients at the end."}],
   Pane[Grid[Prepend[rows,Style[#,Bold]& /@ headers],
     Alignment->{{Right,Left},Center},
     Background->{None,colors},Dividers->{All,{False,True}},Spacings->{2,0.7}],
     {Automatic,UpTo[550]},Scrollbars->Automatic]},Spacings->1]
];
ReductionSteps[] := ReductionSteps[$LastAmplitudeReduction];
ReductionSteps[report_Association] := Module[{data},
 If[!TrueQ[Lookup[report,"Completed",False]],Return[Failure["IncompleteReduction",<||>]]];
 If[!TrueQ[Lookup[report,"TraceRecorded",False]],Return[Failure["TraceNotRecorded",<|
   "MessageTemplate"->"Run AmplitudeReduce[amp, ReductionTrace -> True] first, then call ReductionSteps[]."|>]]];
 data=traceViewData[report];
 With[{snapshot=data,n=Length[report["Events"]]},
   Manipulate[traceFrame[snapshot,step],
     {{step,0,"Reduction step"},0,n,1,Appearance->"Labeled",Enabled->(n>0)},
     TrackedSymbols:>{step},SaveDefinitions->True]]
];
ReductionSteps[_] := Failure["NoRecordedReduction",<||>];
SyntaxInformation[ReductionSteps]={"ArgumentsPattern"->{_.}};
