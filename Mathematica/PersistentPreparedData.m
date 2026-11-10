(* One mutable application table for bundled and newly prepared contexts. *)
$persistedNativeKeys={};
preparedDataPath[]:=$nativePreparedPath;
preparedParentHash[]:=IntegerString[FileHash[$nativeParentPath,"SHA256"],16,64];
AmplitudeReduce::save="Reduction completed, but prepared data could not be saved: `1`.";
preparedPolynomial[p_]:=({First[#],Last[#]}& /@ CoefficientRules[Expand[p],Array[Mass,$nativeParticles]]);
preparedWriteRow[row_Association]:=Map[Function[t,With[{c=Together[t[[2]]]},
 {t[[1]],preparedPolynomial[Numerator[c]],preparedPolynomial[Denominator[c]]}]],Values[row]];
preparedWriteAction[a_Association]:=Join[
 <|"group"->a["Group"],"identity"->preparedWriteRow[a["Identity"]],"source"->a["Source"]|>,
 If[KeyExistsQ[a,"OriginalIdentity"],<|"original_identity"->preparedWriteRow[a["OriginalIdentity"]]|>,<||>],
 If[KeyExistsQ[a,"PreparationProof"],<|"preparation_proof"->
  (<|"monomial"->#["Monomial"],"identity"->preparedWriteRow[#["Identity"]],"source"->#["Source"]|>& /@ a["PreparationProof"])|>,<||>]];
saveNativePrepared[]:=If[!FileExistsQ[preparedDataPath[]],<|"AddedContexts"->0,"DiskSaving"->"NoPreparedFile"|>,saveNativePreparedFour[]];
saveNativePreparedFour[]:=Module[{keys=Complement[Keys[$nativePrepared],$persistedNativeKeys],path=preparedDataPath[],raw,index,hash,tmp,result,new=0,mon},
 If[keys==={},Return[<|"AddedContexts"->0|>]];
 hash=FileHash[path,"SHA256"];
 raw=Quiet[Check[Import[path,"RawJSON"],$Failed]];
 If[!AssociationQ[raw] || Lookup[raw,"format",""]=!="MassiveTensorPrepared-1",Return[Failure["PreparedDataRead",<|"File"->path|>]]];
 If[Lookup[raw,"parent_sha256",preparedParentHash[]]=!=preparedParentHash[],Return[Failure["PreparedParentMismatch",<||>]]];
 index=Association[(monKey[#["monomial"]]->#)& /@ raw["entries"]];
 Do[If[!KeyExistsQ[index,key],
   mon=Lookup[$nativePreparedMonomials,key,Missing["NoMonomial"]];
   If[MissingQ[mon],Continue[]];
   AssociateTo[index,key-><|"monomial"->mon,"actions"->(preparedWriteAction /@ $nativePrepared[key])|>];new++],{key,keys}];
 If[new==0,$persistedNativeKeys=Union[$persistedNativeKeys,keys];Return[<|"AddedContexts"->0|>]];
 AssociateTo[raw,{"entries"->Values[index],"parent_sha256"->preparedParentHash[],"runtime_encoding"->"rational-mass-rows-1"}];
 tmp=path<>"."<>CreateUUID[]<>".tmp";
 result=Quiet[Check[Export[tmp,raw,"RawJSON"],$Failed]];
 If[result===$Failed,Return[Failure["PreparedDataWrite",<|"File"->path|>]]];
 If[FileHash[path,"SHA256"]=!=hash,DeleteFile[tmp];Return[Failure["PreparedDataChangedDuringSave",<|"File"->path|>]]];
 result=Quiet[Check[RenameFile[tmp,path,OverwriteTarget->True],$Failed]];
 If[result===$Failed,Return[Failure["PreparedDataReplace",<|"File"->path,"TemporaryFile"->tmp|>]]];
 $persistedNativeKeys=Union[$persistedNativeKeys,keys];
 <|"AddedContexts"->new,"File"->path|>
];
