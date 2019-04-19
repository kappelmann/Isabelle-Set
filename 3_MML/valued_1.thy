theory valued_1
  imports xxreal_2 square_1 funct_4 finseq_3 fraenkel recdef_1 nat_d
   "../mizar_extension/E_number"
begin
(*begin*)
mlemma valued_1_lm_1:
" for f be FinSequenceFINSEQ-1M1 holds  for h be FunctionFUNCT-1M1 holds domRELAT-1K1 h =XBOOLE-0R4 domFINSEQ-1K5 f implies h be FinSequenceFINSEQ-1M1"
sorry

mlemma valued_1_lm_2:
" for f be FinSequenceFINSEQ-1M1 holds  for g be FinSequenceFINSEQ-1M1 holds  for h be FunctionFUNCT-1M1 holds domRELAT-1K1 h =XBOOLE-0R4 domFINSEQ-1K5 f /\\SUBSET-1K9\<^bsub>(omegaORDINAL1K4)\<^esub> domFINSEQ-1K5 g implies h be FinSequenceFINSEQ-1M1"
sorry

mtheorem valued_1_cl_1:
"cluster complex-valuedVALUED-0V5 for FinSequenceFINSEQ-1M1"
proof
(*existence*)
  show " ex it be FinSequenceFINSEQ-1M1 st it be complex-valuedVALUED-0V5"
sorry
qed "sorry"

mtheorem valued_1_cl_2:
  mlet "r be RationalRAT-1M1"
"cluster |.COMPLEX1K10 r.| as-term-is rationalRAT-1V1"
proof
(*coherence*)
  show "|.COMPLEX1K10 r.| be rationalRAT-1V1"
sorry
qed "sorry"

mdef valued_1_def_1 (" _ +VALUED-1K1  _ " [132,132]132 ) where
  mlet "f1 be complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1", "f2 be complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1"
"func f1 +VALUED-1K1 f2 \<rightarrow> FunctionFUNCT-1M1 means
  \<lambda>it. domRELAT-1K1 it =XBOOLE-0R4 domRELAT-1K1 f1 /\\XBOOLE-0K3 domRELAT-1K1 f2 & ( for c be objectHIDDENM1 holds c inHIDDENR3 domRELAT-1K1 it implies it .FUNCT-1K1 c =XBOOLE-0R4 f1 .FUNCT-1K1 c +XCMPLX-0K2 f2 .FUNCT-1K1 c)"
proof-
  (*existence*)
    show " ex it be FunctionFUNCT-1M1 st domRELAT-1K1 it =XBOOLE-0R4 domRELAT-1K1 f1 /\\XBOOLE-0K3 domRELAT-1K1 f2 & ( for c be objectHIDDENM1 holds c inHIDDENR3 domRELAT-1K1 it implies it .FUNCT-1K1 c =XBOOLE-0R4 f1 .FUNCT-1K1 c +XCMPLX-0K2 f2 .FUNCT-1K1 c)"
sorry
  (*uniqueness*)
    show " for it1 be FunctionFUNCT-1M1 holds  for it2 be FunctionFUNCT-1M1 holds (domRELAT-1K1 it1 =XBOOLE-0R4 domRELAT-1K1 f1 /\\XBOOLE-0K3 domRELAT-1K1 f2 & ( for c be objectHIDDENM1 holds c inHIDDENR3 domRELAT-1K1 it1 implies it1 .FUNCT-1K1 c =XBOOLE-0R4 f1 .FUNCT-1K1 c +XCMPLX-0K2 f2 .FUNCT-1K1 c)) & (domRELAT-1K1 it2 =XBOOLE-0R4 domRELAT-1K1 f1 /\\XBOOLE-0K3 domRELAT-1K1 f2 & ( for c be objectHIDDENM1 holds c inHIDDENR3 domRELAT-1K1 it2 implies it2 .FUNCT-1K1 c =XBOOLE-0R4 f1 .FUNCT-1K1 c +XCMPLX-0K2 f2 .FUNCT-1K1 c)) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mtheorem VALUED_1K1_commutativity:
" for f1 be complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1 holds  for f2 be complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1 holds f1 +VALUED-1K1 f2 =HIDDENR1 f2 +VALUED-1K1 f1"
sorry

mtheorem valued_1_cl_3:
  mlet "f1 be complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1", "f2 be complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1"
"cluster f1 +VALUED-1K1 f2 as-term-is complex-valuedVALUED-0V5"
proof
(*coherence*)
  show "f1 +VALUED-1K1 f2 be complex-valuedVALUED-0V5"
sorry
qed "sorry"

mtheorem valued_1_cl_4:
  mlet "f1 be real-valuedVALUED-0V7\<bar>FunctionFUNCT-1M1", "f2 be real-valuedVALUED-0V7\<bar>FunctionFUNCT-1M1"
"cluster f1 +VALUED-1K1 f2 as-term-is real-valuedVALUED-0V7"
proof
(*coherence*)
  show "f1 +VALUED-1K1 f2 be real-valuedVALUED-0V7"
sorry
qed "sorry"

mtheorem valued_1_cl_5:
  mlet "f1 be RATRAT-1K1 -valuedRELAT-1V5\<bar>FunctionFUNCT-1M1", "f2 be RATRAT-1K1 -valuedRELAT-1V5\<bar>FunctionFUNCT-1M1"
"cluster f1 +VALUED-1K1 f2 as-term-is RATRAT-1K1 -valuedRELAT-1V5"
proof
(*coherence*)
  show "f1 +VALUED-1K1 f2 be RATRAT-1K1 -valuedRELAT-1V5"
sorry
qed "sorry"

mtheorem valued_1_cl_6:
  mlet "f1 be INTINT-1K1 -valuedRELAT-1V5\<bar>FunctionFUNCT-1M1", "f2 be INTINT-1K1 -valuedRELAT-1V5\<bar>FunctionFUNCT-1M1"
"cluster f1 +VALUED-1K1 f2 as-term-is INTINT-1K1 -valuedRELAT-1V5"
proof
(*coherence*)
  show "f1 +VALUED-1K1 f2 be INTINT-1K1 -valuedRELAT-1V5"
sorry
qed "sorry"

mtheorem valued_1_cl_7:
  mlet "f1 be natural-valuedVALUED-0V8\<bar>FunctionFUNCT-1M1", "f2 be natural-valuedVALUED-0V8\<bar>FunctionFUNCT-1M1"
"cluster f1 +VALUED-1K1 f2 as-term-is natural-valuedVALUED-0V8"
proof
(*coherence*)
  show "f1 +VALUED-1K1 f2 be natural-valuedVALUED-0V8"
sorry
qed "sorry"

syntax VALUED_1K2 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ +VALUED-1K2\<^bsub>'( _ , _ , _ ')\<^esub>  _ " [132,0,0,0,132]132)
translations "f1 +VALUED-1K2\<^bsub>(C,D1,D2)\<^esub> f2" \<rightharpoonup> "f1 +VALUED-1K1 f2"

mtheorem valued_1_add_1:
  mlet "C be setHIDDENM2", "D1 be complex-memberedMEMBEREDV1\<bar>setHIDDENM2", "D2 be complex-memberedMEMBEREDV1\<bar>setHIDDENM2", "f1 be PartFuncPARTFUN1M1-of(C,D1)", "f2 be PartFuncPARTFUN1M1-of(C,D2)"
"cluster f1 +VALUED-1K1 f2 as-term-is PartFuncPARTFUN1M1-of(C,COMPLEXNUMBERSK3)"
proof
(*coherence*)
  show "f1 +VALUED-1K1 f2 be PartFuncPARTFUN1M1-of(C,COMPLEXNUMBERSK3)"
sorry
qed "sorry"

syntax VALUED_1K3 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ +VALUED-1K3\<^bsub>'( _ , _ , _ ')\<^esub>  _ " [132,0,0,0,132]132)
translations "f1 +VALUED-1K3\<^bsub>(C,D1,D2)\<^esub> f2" \<rightharpoonup> "f1 +VALUED-1K1 f2"

mtheorem valued_1_add_2:
  mlet "C be setHIDDENM2", "D1 be real-memberedMEMBEREDV3\<bar>setHIDDENM2", "D2 be real-memberedMEMBEREDV3\<bar>setHIDDENM2", "f1 be PartFuncPARTFUN1M1-of(C,D1)", "f2 be PartFuncPARTFUN1M1-of(C,D2)"
"cluster f1 +VALUED-1K1 f2 as-term-is PartFuncPARTFUN1M1-of(C,REALNUMBERSK2)"
proof
(*coherence*)
  show "f1 +VALUED-1K1 f2 be PartFuncPARTFUN1M1-of(C,REALNUMBERSK2)"
sorry
qed "sorry"

syntax VALUED_1K4 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ +VALUED-1K4\<^bsub>'( _ , _ , _ ')\<^esub>  _ " [132,0,0,0,132]132)
translations "f1 +VALUED-1K4\<^bsub>(C,D1,D2)\<^esub> f2" \<rightharpoonup> "f1 +VALUED-1K1 f2"

mtheorem valued_1_add_3:
  mlet "C be setHIDDENM2", "D1 be rational-memberedMEMBEREDV4\<bar>setHIDDENM2", "D2 be rational-memberedMEMBEREDV4\<bar>setHIDDENM2", "f1 be PartFuncPARTFUN1M1-of(C,D1)", "f2 be PartFuncPARTFUN1M1-of(C,D2)"
"cluster f1 +VALUED-1K1 f2 as-term-is PartFuncPARTFUN1M1-of(C,RATRAT-1K1)"
proof
(*coherence*)
  show "f1 +VALUED-1K1 f2 be PartFuncPARTFUN1M1-of(C,RATRAT-1K1)"
sorry
qed "sorry"

syntax VALUED_1K5 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ +VALUED-1K5\<^bsub>'( _ , _ , _ ')\<^esub>  _ " [132,0,0,0,132]132)
translations "f1 +VALUED-1K5\<^bsub>(C,D1,D2)\<^esub> f2" \<rightharpoonup> "f1 +VALUED-1K1 f2"

mtheorem valued_1_add_4:
  mlet "C be setHIDDENM2", "D1 be integer-memberedMEMBEREDV5\<bar>setHIDDENM2", "D2 be integer-memberedMEMBEREDV5\<bar>setHIDDENM2", "f1 be PartFuncPARTFUN1M1-of(C,D1)", "f2 be PartFuncPARTFUN1M1-of(C,D2)"
"cluster f1 +VALUED-1K1 f2 as-term-is PartFuncPARTFUN1M1-of(C,INTINT-1K1)"
proof
(*coherence*)
  show "f1 +VALUED-1K1 f2 be PartFuncPARTFUN1M1-of(C,INTINT-1K1)"
sorry
qed "sorry"

syntax VALUED_1K6 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ +VALUED-1K6\<^bsub>'( _ , _ , _ ')\<^esub>  _ " [132,0,0,0,132]132)
translations "f1 +VALUED-1K6\<^bsub>(C,D1,D2)\<^esub> f2" \<rightharpoonup> "f1 +VALUED-1K1 f2"

mtheorem valued_1_add_5:
  mlet "C be setHIDDENM2", "D1 be natural-memberedMEMBEREDV6\<bar>setHIDDENM2", "D2 be natural-memberedMEMBEREDV6\<bar>setHIDDENM2", "f1 be PartFuncPARTFUN1M1-of(C,D1)", "f2 be PartFuncPARTFUN1M1-of(C,D2)"
"cluster f1 +VALUED-1K1 f2 as-term-is PartFuncPARTFUN1M1-of(C,NATNUMBERSK1)"
proof
(*coherence*)
  show "f1 +VALUED-1K1 f2 be PartFuncPARTFUN1M1-of(C,NATNUMBERSK1)"
sorry
qed "sorry"

mtheorem valued_1_cl_8:
  mlet "C be setHIDDENM2", "D1 be complex-memberedMEMBEREDV1\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2", "D2 be complex-memberedMEMBEREDV1\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2", "f1 be FunctionFUNCT-2M1-of(C,D1)", "f2 be FunctionFUNCT-2M1-of(C,D2)"
"cluster f1 +VALUED-1K2\<^bsub>(C,D1,D2)\<^esub> f2 as-term-is totalPARTFUN1V1\<^bsub>(C)\<^esub> for PartFuncPARTFUN1M1-of(C,COMPLEXNUMBERSK3)"
proof
(*coherence*)
  show " for it be PartFuncPARTFUN1M1-of(C,COMPLEXNUMBERSK3) holds it =HIDDENR1 f1 +VALUED-1K2\<^bsub>(C,D1,D2)\<^esub> f2 implies it be totalPARTFUN1V1\<^bsub>(C)\<^esub>"
sorry
qed "sorry"

mtheorem valued_1_cl_9:
  mlet "C be setHIDDENM2", "D1 be real-memberedMEMBEREDV3\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2", "D2 be real-memberedMEMBEREDV3\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2", "f1 be FunctionFUNCT-2M1-of(C,D1)", "f2 be FunctionFUNCT-2M1-of(C,D2)"
"cluster f1 +VALUED-1K3\<^bsub>(C,D1,D2)\<^esub> f2 as-term-is totalPARTFUN1V1\<^bsub>(C)\<^esub> for PartFuncPARTFUN1M1-of(C,REALNUMBERSK2)"
proof
(*coherence*)
  show " for it be PartFuncPARTFUN1M1-of(C,REALNUMBERSK2) holds it =HIDDENR1 f1 +VALUED-1K3\<^bsub>(C,D1,D2)\<^esub> f2 implies it be totalPARTFUN1V1\<^bsub>(C)\<^esub>"
sorry
qed "sorry"

mtheorem valued_1_cl_10:
  mlet "C be setHIDDENM2", "D1 be rational-memberedMEMBEREDV4\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2", "D2 be rational-memberedMEMBEREDV4\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2", "f1 be FunctionFUNCT-2M1-of(C,D1)", "f2 be FunctionFUNCT-2M1-of(C,D2)"
"cluster f1 +VALUED-1K4\<^bsub>(C,D1,D2)\<^esub> f2 as-term-is totalPARTFUN1V1\<^bsub>(C)\<^esub> for PartFuncPARTFUN1M1-of(C,RATRAT-1K1)"
proof
(*coherence*)
  show " for it be PartFuncPARTFUN1M1-of(C,RATRAT-1K1) holds it =HIDDENR1 f1 +VALUED-1K4\<^bsub>(C,D1,D2)\<^esub> f2 implies it be totalPARTFUN1V1\<^bsub>(C)\<^esub>"
sorry
qed "sorry"

mtheorem valued_1_cl_11:
  mlet "C be setHIDDENM2", "D1 be integer-memberedMEMBEREDV5\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2", "D2 be integer-memberedMEMBEREDV5\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2", "f1 be FunctionFUNCT-2M1-of(C,D1)", "f2 be FunctionFUNCT-2M1-of(C,D2)"
"cluster f1 +VALUED-1K5\<^bsub>(C,D1,D2)\<^esub> f2 as-term-is totalPARTFUN1V1\<^bsub>(C)\<^esub> for PartFuncPARTFUN1M1-of(C,INTINT-1K1)"
proof
(*coherence*)
  show " for it be PartFuncPARTFUN1M1-of(C,INTINT-1K1) holds it =HIDDENR1 f1 +VALUED-1K5\<^bsub>(C,D1,D2)\<^esub> f2 implies it be totalPARTFUN1V1\<^bsub>(C)\<^esub>"
sorry
qed "sorry"

mtheorem valued_1_cl_12:
  mlet "C be setHIDDENM2", "D1 be natural-memberedMEMBEREDV6\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2", "D2 be natural-memberedMEMBEREDV6\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2", "f1 be FunctionFUNCT-2M1-of(C,D1)", "f2 be FunctionFUNCT-2M1-of(C,D2)"
"cluster f1 +VALUED-1K6\<^bsub>(C,D1,D2)\<^esub> f2 as-term-is totalPARTFUN1V1\<^bsub>(C)\<^esub> for PartFuncPARTFUN1M1-of(C,NATNUMBERSK1)"
proof
(*coherence*)
  show " for it be PartFuncPARTFUN1M1-of(C,NATNUMBERSK1) holds it =HIDDENR1 f1 +VALUED-1K6\<^bsub>(C,D1,D2)\<^esub> f2 implies it be totalPARTFUN1V1\<^bsub>(C)\<^esub>"
sorry
qed "sorry"

mtheorem valued_1_th_1:
" for C be setHIDDENM2 holds  for D1 be complex-memberedMEMBEREDV1\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D2 be complex-memberedMEMBEREDV1\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for f1 be FunctionFUNCT-2M1-of(C,D1) holds  for f2 be FunctionFUNCT-2M1-of(C,D2) holds  for c be ElementSUBSET-1M1-of C holds (f1 +VALUED-1K2\<^bsub>(C,D1,D2)\<^esub> f2).FUNCT-1K1 c =XBOOLE-0R4 f1 .FUNCT-1K1 c +XCMPLX-0K2 f2 .FUNCT-1K1 c"
sorry

mtheorem valued_1_cl_13:
  mlet "f1 be complex-valuedVALUED-0V5\<bar>FinSequenceFINSEQ-1M1", "f2 be complex-valuedVALUED-0V5\<bar>FinSequenceFINSEQ-1M1"
"cluster f1 +VALUED-1K1 f2 as-term-is FinSequence-likeFINSEQ-1V1"
proof
(*coherence*)
  show "f1 +VALUED-1K1 f2 be FinSequence-likeFINSEQ-1V1"
sorry
qed "sorry"

(*begin*)
mdef valued_1_def_2 (" _ +VALUED-1K7  _ " [132,132]132 ) where
  mlet "f be complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1", "r be ComplexXCMPLX-0M1"
"func r +VALUED-1K7 f \<rightarrow> FunctionFUNCT-1M1 means
  \<lambda>it. domRELAT-1K1 it =XBOOLE-0R4 domRELAT-1K1 f & ( for c be objectHIDDENM1 holds c inHIDDENR3 domRELAT-1K1 it implies it .FUNCT-1K1 c =XBOOLE-0R4 r +XCMPLX-0K2 f .FUNCT-1K1 c)"
proof-
  (*existence*)
    show " ex it be FunctionFUNCT-1M1 st domRELAT-1K1 it =XBOOLE-0R4 domRELAT-1K1 f & ( for c be objectHIDDENM1 holds c inHIDDENR3 domRELAT-1K1 it implies it .FUNCT-1K1 c =XBOOLE-0R4 r +XCMPLX-0K2 f .FUNCT-1K1 c)"
sorry
  (*uniqueness*)
    show " for it1 be FunctionFUNCT-1M1 holds  for it2 be FunctionFUNCT-1M1 holds (domRELAT-1K1 it1 =XBOOLE-0R4 domRELAT-1K1 f & ( for c be objectHIDDENM1 holds c inHIDDENR3 domRELAT-1K1 it1 implies it1 .FUNCT-1K1 c =XBOOLE-0R4 r +XCMPLX-0K2 f .FUNCT-1K1 c)) & (domRELAT-1K1 it2 =XBOOLE-0R4 domRELAT-1K1 f & ( for c be objectHIDDENM1 holds c inHIDDENR3 domRELAT-1K1 it2 implies it2 .FUNCT-1K1 c =XBOOLE-0R4 r +XCMPLX-0K2 f .FUNCT-1K1 c)) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

abbreviation(input) VALUED_1K8(" _ +VALUED-1K8  _ " [132,132]132) where
  "f +VALUED-1K8 r \<equiv> r +VALUED-1K7 f"

mtheorem valued_1_cl_14:
  mlet "f be complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1", "r be ComplexXCMPLX-0M1"
"cluster r +VALUED-1K7 f as-term-is complex-valuedVALUED-0V5"
proof
(*coherence*)
  show "r +VALUED-1K7 f be complex-valuedVALUED-0V5"
sorry
qed "sorry"

mtheorem valued_1_cl_15:
  mlet "f be real-valuedVALUED-0V7\<bar>FunctionFUNCT-1M1", "r be RealXREAL-0M1"
"cluster r +VALUED-1K7 f as-term-is real-valuedVALUED-0V7"
proof
(*coherence*)
  show "r +VALUED-1K7 f be real-valuedVALUED-0V7"
sorry
qed "sorry"

mtheorem valued_1_cl_16:
  mlet "f be RATRAT-1K1 -valuedRELAT-1V5\<bar>FunctionFUNCT-1M1", "r be RationalRAT-1M1"
"cluster r +VALUED-1K7 f as-term-is RATRAT-1K1 -valuedRELAT-1V5"
proof
(*coherence*)
  show "r +VALUED-1K7 f be RATRAT-1K1 -valuedRELAT-1V5"
sorry
qed "sorry"

mtheorem valued_1_cl_17:
  mlet "f be INTINT-1K1 -valuedRELAT-1V5\<bar>FunctionFUNCT-1M1", "r be IntegerINT-1M1"
"cluster r +VALUED-1K7 f as-term-is INTINT-1K1 -valuedRELAT-1V5"
proof
(*coherence*)
  show "r +VALUED-1K7 f be INTINT-1K1 -valuedRELAT-1V5"
sorry
qed "sorry"

mtheorem valued_1_cl_18:
  mlet "f be natural-valuedVALUED-0V8\<bar>FunctionFUNCT-1M1", "r be NatNAT-1M1"
"cluster r +VALUED-1K7 f as-term-is natural-valuedVALUED-0V8"
proof
(*coherence*)
  show "r +VALUED-1K7 f be natural-valuedVALUED-0V8"
sorry
qed "sorry"

syntax VALUED_1K9 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ +VALUED-1K9\<^bsub>'( _ , _ ')\<^esub>  _ " [132,0,0,132]132)
translations "r +VALUED-1K9\<^bsub>(C,D)\<^esub> f" \<rightharpoonup> "r +VALUED-1K7 f"

mtheorem valued_1_add_6:
  mlet "C be setHIDDENM2", "D be complex-memberedMEMBEREDV1\<bar>setHIDDENM2", "f be PartFuncPARTFUN1M1-of(C,D)", "r be ComplexXCMPLX-0M1"
"cluster r +VALUED-1K7 f as-term-is PartFuncPARTFUN1M1-of(C,COMPLEXNUMBERSK3)"
proof
(*coherence*)
  show "r +VALUED-1K7 f be PartFuncPARTFUN1M1-of(C,COMPLEXNUMBERSK3)"
sorry
qed "sorry"

syntax VALUED_1K10 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ +VALUED-1K10\<^bsub>'( _ , _ ')\<^esub>  _ " [132,0,0,132]132)
translations "r +VALUED-1K10\<^bsub>(C,D)\<^esub> f" \<rightharpoonup> "r +VALUED-1K7 f"

mtheorem valued_1_add_7:
  mlet "C be setHIDDENM2", "D be real-memberedMEMBEREDV3\<bar>setHIDDENM2", "f be PartFuncPARTFUN1M1-of(C,D)", "r be RealXREAL-0M1"
"cluster r +VALUED-1K7 f as-term-is PartFuncPARTFUN1M1-of(C,REALNUMBERSK2)"
proof
(*coherence*)
  show "r +VALUED-1K7 f be PartFuncPARTFUN1M1-of(C,REALNUMBERSK2)"
sorry
qed "sorry"

syntax VALUED_1K11 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ +VALUED-1K11\<^bsub>'( _ , _ ')\<^esub>  _ " [132,0,0,132]132)
translations "r +VALUED-1K11\<^bsub>(C,D)\<^esub> f" \<rightharpoonup> "r +VALUED-1K7 f"

mtheorem valued_1_add_8:
  mlet "C be setHIDDENM2", "D be rational-memberedMEMBEREDV4\<bar>setHIDDENM2", "f be PartFuncPARTFUN1M1-of(C,D)", "r be RationalRAT-1M1"
"cluster r +VALUED-1K7 f as-term-is PartFuncPARTFUN1M1-of(C,RATRAT-1K1)"
proof
(*coherence*)
  show "r +VALUED-1K7 f be PartFuncPARTFUN1M1-of(C,RATRAT-1K1)"
sorry
qed "sorry"

syntax VALUED_1K12 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ +VALUED-1K12\<^bsub>'( _ , _ ')\<^esub>  _ " [132,0,0,132]132)
translations "r +VALUED-1K12\<^bsub>(C,D)\<^esub> f" \<rightharpoonup> "r +VALUED-1K7 f"

mtheorem valued_1_add_9:
  mlet "C be setHIDDENM2", "D be integer-memberedMEMBEREDV5\<bar>setHIDDENM2", "f be PartFuncPARTFUN1M1-of(C,D)", "r be IntegerINT-1M1"
"cluster r +VALUED-1K7 f as-term-is PartFuncPARTFUN1M1-of(C,INTINT-1K1)"
proof
(*coherence*)
  show "r +VALUED-1K7 f be PartFuncPARTFUN1M1-of(C,INTINT-1K1)"
sorry
qed "sorry"

syntax VALUED_1K13 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ +VALUED-1K13\<^bsub>'( _ , _ ')\<^esub>  _ " [132,0,0,132]132)
translations "r +VALUED-1K13\<^bsub>(C,D)\<^esub> f" \<rightharpoonup> "r +VALUED-1K7 f"

mtheorem valued_1_add_10:
  mlet "C be setHIDDENM2", "D be natural-memberedMEMBEREDV6\<bar>setHIDDENM2", "f be PartFuncPARTFUN1M1-of(C,D)", "r be NatNAT-1M1"
"cluster r +VALUED-1K7 f as-term-is PartFuncPARTFUN1M1-of(C,NATNUMBERSK1)"
proof
(*coherence*)
  show "r +VALUED-1K7 f be PartFuncPARTFUN1M1-of(C,NATNUMBERSK1)"
sorry
qed "sorry"

mtheorem valued_1_cl_19:
  mlet "C be setHIDDENM2", "D be complex-memberedMEMBEREDV1\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2", "f be FunctionFUNCT-2M1-of(C,D)", "r be ComplexXCMPLX-0M1"
"cluster r +VALUED-1K9\<^bsub>(C,D)\<^esub> f as-term-is totalPARTFUN1V1\<^bsub>(C)\<^esub> for PartFuncPARTFUN1M1-of(C,COMPLEXNUMBERSK3)"
proof
(*coherence*)
  show " for it be PartFuncPARTFUN1M1-of(C,COMPLEXNUMBERSK3) holds it =HIDDENR1 r +VALUED-1K9\<^bsub>(C,D)\<^esub> f implies it be totalPARTFUN1V1\<^bsub>(C)\<^esub>"
sorry
qed "sorry"

mtheorem valued_1_cl_20:
  mlet "C be setHIDDENM2", "D be real-memberedMEMBEREDV3\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2", "f be FunctionFUNCT-2M1-of(C,D)", "r be RealXREAL-0M1"
"cluster r +VALUED-1K10\<^bsub>(C,D)\<^esub> f as-term-is totalPARTFUN1V1\<^bsub>(C)\<^esub> for PartFuncPARTFUN1M1-of(C,REALNUMBERSK2)"
proof
(*coherence*)
  show " for it be PartFuncPARTFUN1M1-of(C,REALNUMBERSK2) holds it =HIDDENR1 r +VALUED-1K10\<^bsub>(C,D)\<^esub> f implies it be totalPARTFUN1V1\<^bsub>(C)\<^esub>"
sorry
qed "sorry"

mtheorem valued_1_cl_21:
  mlet "C be setHIDDENM2", "D be rational-memberedMEMBEREDV4\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2", "f be FunctionFUNCT-2M1-of(C,D)", "r be RationalRAT-1M1"
"cluster r +VALUED-1K11\<^bsub>(C,D)\<^esub> f as-term-is totalPARTFUN1V1\<^bsub>(C)\<^esub> for PartFuncPARTFUN1M1-of(C,RATRAT-1K1)"
proof
(*coherence*)
  show " for it be PartFuncPARTFUN1M1-of(C,RATRAT-1K1) holds it =HIDDENR1 r +VALUED-1K11\<^bsub>(C,D)\<^esub> f implies it be totalPARTFUN1V1\<^bsub>(C)\<^esub>"
sorry
qed "sorry"

mtheorem valued_1_cl_22:
  mlet "C be setHIDDENM2", "D be integer-memberedMEMBEREDV5\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2", "f be FunctionFUNCT-2M1-of(C,D)", "r be IntegerINT-1M1"
"cluster r +VALUED-1K12\<^bsub>(C,D)\<^esub> f as-term-is totalPARTFUN1V1\<^bsub>(C)\<^esub> for PartFuncPARTFUN1M1-of(C,INTINT-1K1)"
proof
(*coherence*)
  show " for it be PartFuncPARTFUN1M1-of(C,INTINT-1K1) holds it =HIDDENR1 r +VALUED-1K12\<^bsub>(C,D)\<^esub> f implies it be totalPARTFUN1V1\<^bsub>(C)\<^esub>"
sorry
qed "sorry"

mtheorem valued_1_cl_23:
  mlet "C be setHIDDENM2", "D be natural-memberedMEMBEREDV6\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2", "f be FunctionFUNCT-2M1-of(C,D)", "r be NatNAT-1M1"
"cluster r +VALUED-1K13\<^bsub>(C,D)\<^esub> f as-term-is totalPARTFUN1V1\<^bsub>(C)\<^esub> for PartFuncPARTFUN1M1-of(C,NATNUMBERSK1)"
proof
(*coherence*)
  show " for it be PartFuncPARTFUN1M1-of(C,NATNUMBERSK1) holds it =HIDDENR1 r +VALUED-1K13\<^bsub>(C,D)\<^esub> f implies it be totalPARTFUN1V1\<^bsub>(C)\<^esub>"
sorry
qed "sorry"

mtheorem valued_1_th_2:
" for C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D be complex-memberedMEMBEREDV1\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(C,D) holds  for r be ComplexXCMPLX-0M1 holds  for c be ElementSUBSET-1M1-of C holds (r +VALUED-1K9\<^bsub>(C,D)\<^esub> f).FUNCT-2K3\<^bsub>(C,COMPLEXNUMBERSK3)\<^esub> c =XBOOLE-0R4 r +XCMPLX-0K2 f .FUNCT-2K3\<^bsub>(C,D)\<^esub> c"
sorry

mtheorem valued_1_cl_24:
  mlet "f be complex-valuedVALUED-0V5\<bar>FinSequenceFINSEQ-1M1", "r be ComplexXCMPLX-0M1"
"cluster r +VALUED-1K7 f as-term-is FinSequence-likeFINSEQ-1V1"
proof
(*coherence*)
  show "r +VALUED-1K7 f be FinSequence-likeFINSEQ-1V1"
sorry
qed "sorry"

(*begin*)
mdef valued_1_def_3 (" _ -VALUED-1K14  _ " [132,132]132 ) where
  mlet "f be complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1", "r be ComplexXCMPLX-0M1"
"func f -VALUED-1K14 r \<rightarrow> FunctionFUNCT-1M1 equals
  (-XCMPLX-0K4 r)+VALUED-1K7 f"
proof-
  (*coherence*)
    show "(-XCMPLX-0K4 r)+VALUED-1K7 f be FunctionFUNCT-1M1"
       sorry
qed "sorry"

mtheorem valued_1_th_3:
" for f be complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1 holds  for r be ComplexXCMPLX-0M1 holds domRELAT-1K1 (f -VALUED-1K14 r) =XBOOLE-0R4 domRELAT-1K1 f & ( for c be objectHIDDENM1 holds c inHIDDENR3 domRELAT-1K1 f implies (f -VALUED-1K14 r).FUNCT-1K1 c =XBOOLE-0R4 f .FUNCT-1K1 c -XCMPLX-0K6 r)"
sorry

mtheorem valued_1_cl_25:
  mlet "f be complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1", "r be ComplexXCMPLX-0M1"
"cluster f -VALUED-1K14 r as-term-is complex-valuedVALUED-0V5"
proof
(*coherence*)
  show "f -VALUED-1K14 r be complex-valuedVALUED-0V5"
     sorry
qed "sorry"

mtheorem valued_1_cl_26:
  mlet "f be real-valuedVALUED-0V7\<bar>FunctionFUNCT-1M1", "r be RealXREAL-0M1"
"cluster f -VALUED-1K14 r as-term-is real-valuedVALUED-0V7"
proof
(*coherence*)
  show "f -VALUED-1K14 r be real-valuedVALUED-0V7"
     sorry
qed "sorry"

mtheorem valued_1_cl_27:
  mlet "f be RATRAT-1K1 -valuedRELAT-1V5\<bar>FunctionFUNCT-1M1", "r be RationalRAT-1M1"
"cluster f -VALUED-1K14 r as-term-is RATRAT-1K1 -valuedRELAT-1V5"
proof
(*coherence*)
  show "f -VALUED-1K14 r be RATRAT-1K1 -valuedRELAT-1V5"
     sorry
qed "sorry"

mtheorem valued_1_cl_28:
  mlet "f be INTINT-1K1 -valuedRELAT-1V5\<bar>FunctionFUNCT-1M1", "r be IntegerINT-1M1"
"cluster f -VALUED-1K14 r as-term-is INTINT-1K1 -valuedRELAT-1V5"
proof
(*coherence*)
  show "f -VALUED-1K14 r be INTINT-1K1 -valuedRELAT-1V5"
     sorry
qed "sorry"

syntax VALUED_1K15 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ -VALUED-1K15\<^bsub>'( _ , _ ')\<^esub>  _ " [132,0,0,132]132)
translations "f -VALUED-1K15\<^bsub>(C,D)\<^esub> r" \<rightharpoonup> "f -VALUED-1K14 r"

mtheorem valued_1_add_11:
  mlet "C be setHIDDENM2", "D be complex-memberedMEMBEREDV1\<bar>setHIDDENM2", "f be PartFuncPARTFUN1M1-of(C,D)", "r be ComplexXCMPLX-0M1"
"cluster f -VALUED-1K14 r as-term-is PartFuncPARTFUN1M1-of(C,COMPLEXNUMBERSK3)"
proof
(*coherence*)
  show "f -VALUED-1K14 r be PartFuncPARTFUN1M1-of(C,COMPLEXNUMBERSK3)"
sorry
qed "sorry"

syntax VALUED_1K16 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ -VALUED-1K16\<^bsub>'( _ , _ ')\<^esub>  _ " [132,0,0,132]132)
translations "f -VALUED-1K16\<^bsub>(C,D)\<^esub> r" \<rightharpoonup> "f -VALUED-1K14 r"

mtheorem valued_1_add_12:
  mlet "C be setHIDDENM2", "D be real-memberedMEMBEREDV3\<bar>setHIDDENM2", "f be PartFuncPARTFUN1M1-of(C,D)", "r be RealXREAL-0M1"
"cluster f -VALUED-1K14 r as-term-is PartFuncPARTFUN1M1-of(C,REALNUMBERSK2)"
proof
(*coherence*)
  show "f -VALUED-1K14 r be PartFuncPARTFUN1M1-of(C,REALNUMBERSK2)"
sorry
qed "sorry"

syntax VALUED_1K17 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ -VALUED-1K17\<^bsub>'( _ , _ ')\<^esub>  _ " [132,0,0,132]132)
translations "f -VALUED-1K17\<^bsub>(C,D)\<^esub> r" \<rightharpoonup> "f -VALUED-1K14 r"

mtheorem valued_1_add_13:
  mlet "C be setHIDDENM2", "D be rational-memberedMEMBEREDV4\<bar>setHIDDENM2", "f be PartFuncPARTFUN1M1-of(C,D)", "r be RationalRAT-1M1"
"cluster f -VALUED-1K14 r as-term-is PartFuncPARTFUN1M1-of(C,RATRAT-1K1)"
proof
(*coherence*)
  show "f -VALUED-1K14 r be PartFuncPARTFUN1M1-of(C,RATRAT-1K1)"
sorry
qed "sorry"

syntax VALUED_1K18 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ -VALUED-1K18\<^bsub>'( _ , _ ')\<^esub>  _ " [132,0,0,132]132)
translations "f -VALUED-1K18\<^bsub>(C,D)\<^esub> r" \<rightharpoonup> "f -VALUED-1K14 r"

mtheorem valued_1_add_14:
  mlet "C be setHIDDENM2", "D be integer-memberedMEMBEREDV5\<bar>setHIDDENM2", "f be PartFuncPARTFUN1M1-of(C,D)", "r be IntegerINT-1M1"
"cluster f -VALUED-1K14 r as-term-is PartFuncPARTFUN1M1-of(C,INTINT-1K1)"
proof
(*coherence*)
  show "f -VALUED-1K14 r be PartFuncPARTFUN1M1-of(C,INTINT-1K1)"
sorry
qed "sorry"

mtheorem valued_1_cl_29:
  mlet "C be setHIDDENM2", "D be complex-memberedMEMBEREDV1\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2", "f be FunctionFUNCT-2M1-of(C,D)", "r be ComplexXCMPLX-0M1"
"cluster f -VALUED-1K15\<^bsub>(C,D)\<^esub> r as-term-is totalPARTFUN1V1\<^bsub>(C)\<^esub> for PartFuncPARTFUN1M1-of(C,COMPLEXNUMBERSK3)"
proof
(*coherence*)
  show " for it be PartFuncPARTFUN1M1-of(C,COMPLEXNUMBERSK3) holds it =HIDDENR1 f -VALUED-1K15\<^bsub>(C,D)\<^esub> r implies it be totalPARTFUN1V1\<^bsub>(C)\<^esub>"
     sorry
qed "sorry"

mtheorem valued_1_cl_30:
  mlet "C be setHIDDENM2", "D be real-memberedMEMBEREDV3\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2", "f be FunctionFUNCT-2M1-of(C,D)", "r be RealXREAL-0M1"
"cluster f -VALUED-1K16\<^bsub>(C,D)\<^esub> r as-term-is totalPARTFUN1V1\<^bsub>(C)\<^esub> for PartFuncPARTFUN1M1-of(C,REALNUMBERSK2)"
proof
(*coherence*)
  show " for it be PartFuncPARTFUN1M1-of(C,REALNUMBERSK2) holds it =HIDDENR1 f -VALUED-1K16\<^bsub>(C,D)\<^esub> r implies it be totalPARTFUN1V1\<^bsub>(C)\<^esub>"
     sorry
qed "sorry"

mtheorem valued_1_cl_31:
  mlet "C be setHIDDENM2", "D be rational-memberedMEMBEREDV4\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2", "f be FunctionFUNCT-2M1-of(C,D)", "r be RationalRAT-1M1"
"cluster f -VALUED-1K17\<^bsub>(C,D)\<^esub> r as-term-is totalPARTFUN1V1\<^bsub>(C)\<^esub> for PartFuncPARTFUN1M1-of(C,RATRAT-1K1)"
proof
(*coherence*)
  show " for it be PartFuncPARTFUN1M1-of(C,RATRAT-1K1) holds it =HIDDENR1 f -VALUED-1K17\<^bsub>(C,D)\<^esub> r implies it be totalPARTFUN1V1\<^bsub>(C)\<^esub>"
     sorry
qed "sorry"

mtheorem valued_1_cl_32:
  mlet "C be setHIDDENM2", "D be integer-memberedMEMBEREDV5\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2", "f be FunctionFUNCT-2M1-of(C,D)", "r be IntegerINT-1M1"
"cluster f -VALUED-1K18\<^bsub>(C,D)\<^esub> r as-term-is totalPARTFUN1V1\<^bsub>(C)\<^esub> for PartFuncPARTFUN1M1-of(C,INTINT-1K1)"
proof
(*coherence*)
  show " for it be PartFuncPARTFUN1M1-of(C,INTINT-1K1) holds it =HIDDENR1 f -VALUED-1K18\<^bsub>(C,D)\<^esub> r implies it be totalPARTFUN1V1\<^bsub>(C)\<^esub>"
     sorry
qed "sorry"

mtheorem valued_1_th_4:
" for C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D be complex-memberedMEMBEREDV1\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(C,D) holds  for r be ComplexXCMPLX-0M1 holds  for c be ElementSUBSET-1M1-of C holds (f -VALUED-1K15\<^bsub>(C,D)\<^esub> r).FUNCT-2K3\<^bsub>(C,COMPLEXNUMBERSK3)\<^esub> c =XBOOLE-0R4 f .FUNCT-2K3\<^bsub>(C,D)\<^esub> c -XCMPLX-0K6 r"
sorry

mtheorem valued_1_cl_33:
  mlet "f be complex-valuedVALUED-0V5\<bar>FinSequenceFINSEQ-1M1", "r be ComplexXCMPLX-0M1"
"cluster f -VALUED-1K14 r as-term-is FinSequence-likeFINSEQ-1V1"
proof
(*coherence*)
  show "f -VALUED-1K14 r be FinSequence-likeFINSEQ-1V1"
     sorry
qed "sorry"

(*begin*)
mdef valued_1_def_4 (" _ '(#')VALUED-1K19  _ " [164,164]164 ) where
  mlet "f1 be complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1", "f2 be complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1"
"func f1 (#)VALUED-1K19 f2 \<rightarrow> FunctionFUNCT-1M1 means
  \<lambda>it. domRELAT-1K1 it =XBOOLE-0R4 domRELAT-1K1 f1 /\\XBOOLE-0K3 domRELAT-1K1 f2 & ( for c be objectHIDDENM1 holds c inHIDDENR3 domRELAT-1K1 it implies it .FUNCT-1K1 c =XBOOLE-0R4 f1 .FUNCT-1K1 c *XCMPLX-0K3 f2 .FUNCT-1K1 c)"
proof-
  (*existence*)
    show " ex it be FunctionFUNCT-1M1 st domRELAT-1K1 it =XBOOLE-0R4 domRELAT-1K1 f1 /\\XBOOLE-0K3 domRELAT-1K1 f2 & ( for c be objectHIDDENM1 holds c inHIDDENR3 domRELAT-1K1 it implies it .FUNCT-1K1 c =XBOOLE-0R4 f1 .FUNCT-1K1 c *XCMPLX-0K3 f2 .FUNCT-1K1 c)"
sorry
  (*uniqueness*)
    show " for it1 be FunctionFUNCT-1M1 holds  for it2 be FunctionFUNCT-1M1 holds (domRELAT-1K1 it1 =XBOOLE-0R4 domRELAT-1K1 f1 /\\XBOOLE-0K3 domRELAT-1K1 f2 & ( for c be objectHIDDENM1 holds c inHIDDENR3 domRELAT-1K1 it1 implies it1 .FUNCT-1K1 c =XBOOLE-0R4 f1 .FUNCT-1K1 c *XCMPLX-0K3 f2 .FUNCT-1K1 c)) & (domRELAT-1K1 it2 =XBOOLE-0R4 domRELAT-1K1 f1 /\\XBOOLE-0K3 domRELAT-1K1 f2 & ( for c be objectHIDDENM1 holds c inHIDDENR3 domRELAT-1K1 it2 implies it2 .FUNCT-1K1 c =XBOOLE-0R4 f1 .FUNCT-1K1 c *XCMPLX-0K3 f2 .FUNCT-1K1 c)) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mtheorem VALUED_1K19_commutativity:
" for f1 be complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1 holds  for f2 be complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1 holds f1 (#)VALUED-1K19 f2 =HIDDENR1 f2 (#)VALUED-1K19 f1"
sorry

mtheorem valued_1_th_5:
" for f1 be complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1 holds  for f2 be complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1 holds  for c be objectHIDDENM1 holds (f1 (#)VALUED-1K19 f2).FUNCT-1K1 c =XBOOLE-0R4 f1 .FUNCT-1K1 c *XCMPLX-0K3 f2 .FUNCT-1K1 c"
sorry

mtheorem valued_1_cl_34:
  mlet "f1 be complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1", "f2 be complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1"
"cluster f1 (#)VALUED-1K19 f2 as-term-is complex-valuedVALUED-0V5"
proof
(*coherence*)
  show "f1 (#)VALUED-1K19 f2 be complex-valuedVALUED-0V5"
sorry
qed "sorry"

mtheorem valued_1_cl_35:
  mlet "f1 be real-valuedVALUED-0V7\<bar>FunctionFUNCT-1M1", "f2 be real-valuedVALUED-0V7\<bar>FunctionFUNCT-1M1"
"cluster f1 (#)VALUED-1K19 f2 as-term-is real-valuedVALUED-0V7"
proof
(*coherence*)
  show "f1 (#)VALUED-1K19 f2 be real-valuedVALUED-0V7"
sorry
qed "sorry"

mtheorem valued_1_cl_36:
  mlet "f1 be RATRAT-1K1 -valuedRELAT-1V5\<bar>FunctionFUNCT-1M1", "f2 be RATRAT-1K1 -valuedRELAT-1V5\<bar>FunctionFUNCT-1M1"
"cluster f1 (#)VALUED-1K19 f2 as-term-is RATRAT-1K1 -valuedRELAT-1V5"
proof
(*coherence*)
  show "f1 (#)VALUED-1K19 f2 be RATRAT-1K1 -valuedRELAT-1V5"
sorry
qed "sorry"

mtheorem valued_1_cl_37:
  mlet "f1 be INTINT-1K1 -valuedRELAT-1V5\<bar>FunctionFUNCT-1M1", "f2 be INTINT-1K1 -valuedRELAT-1V5\<bar>FunctionFUNCT-1M1"
"cluster f1 (#)VALUED-1K19 f2 as-term-is INTINT-1K1 -valuedRELAT-1V5"
proof
(*coherence*)
  show "f1 (#)VALUED-1K19 f2 be INTINT-1K1 -valuedRELAT-1V5"
sorry
qed "sorry"

mtheorem valued_1_cl_38:
  mlet "f1 be natural-valuedVALUED-0V8\<bar>FunctionFUNCT-1M1", "f2 be natural-valuedVALUED-0V8\<bar>FunctionFUNCT-1M1"
"cluster f1 (#)VALUED-1K19 f2 as-term-is natural-valuedVALUED-0V8"
proof
(*coherence*)
  show "f1 (#)VALUED-1K19 f2 be natural-valuedVALUED-0V8"
sorry
qed "sorry"

syntax VALUED_1K20 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ '(#')VALUED-1K20\<^bsub>'( _ , _ , _ ')\<^esub>  _ " [164,0,0,0,164]164)
translations "f1 (#)VALUED-1K20\<^bsub>(C,D1,D2)\<^esub> f2" \<rightharpoonup> "f1 (#)VALUED-1K19 f2"

mtheorem valued_1_add_15:
  mlet "C be setHIDDENM2", "D1 be complex-memberedMEMBEREDV1\<bar>setHIDDENM2", "D2 be complex-memberedMEMBEREDV1\<bar>setHIDDENM2", "f1 be PartFuncPARTFUN1M1-of(C,D1)", "f2 be PartFuncPARTFUN1M1-of(C,D2)"
"cluster f1 (#)VALUED-1K19 f2 as-term-is PartFuncPARTFUN1M1-of(C,COMPLEXNUMBERSK3)"
proof
(*coherence*)
  show "f1 (#)VALUED-1K19 f2 be PartFuncPARTFUN1M1-of(C,COMPLEXNUMBERSK3)"
sorry
qed "sorry"

syntax VALUED_1K21 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ '(#')VALUED-1K21\<^bsub>'( _ , _ , _ ')\<^esub>  _ " [164,0,0,0,164]164)
translations "f1 (#)VALUED-1K21\<^bsub>(C,D1,D2)\<^esub> f2" \<rightharpoonup> "f1 (#)VALUED-1K19 f2"

mtheorem valued_1_add_16:
  mlet "C be setHIDDENM2", "D1 be real-memberedMEMBEREDV3\<bar>setHIDDENM2", "D2 be real-memberedMEMBEREDV3\<bar>setHIDDENM2", "f1 be PartFuncPARTFUN1M1-of(C,D1)", "f2 be PartFuncPARTFUN1M1-of(C,D2)"
"cluster f1 (#)VALUED-1K19 f2 as-term-is PartFuncPARTFUN1M1-of(C,REALNUMBERSK2)"
proof
(*coherence*)
  show "f1 (#)VALUED-1K19 f2 be PartFuncPARTFUN1M1-of(C,REALNUMBERSK2)"
sorry
qed "sorry"

syntax VALUED_1K22 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ '(#')VALUED-1K22\<^bsub>'( _ , _ , _ ')\<^esub>  _ " [164,0,0,0,164]164)
translations "f1 (#)VALUED-1K22\<^bsub>(C,D1,D2)\<^esub> f2" \<rightharpoonup> "f1 (#)VALUED-1K19 f2"

mtheorem valued_1_add_17:
  mlet "C be setHIDDENM2", "D1 be rational-memberedMEMBEREDV4\<bar>setHIDDENM2", "D2 be rational-memberedMEMBEREDV4\<bar>setHIDDENM2", "f1 be PartFuncPARTFUN1M1-of(C,D1)", "f2 be PartFuncPARTFUN1M1-of(C,D2)"
"cluster f1 (#)VALUED-1K19 f2 as-term-is PartFuncPARTFUN1M1-of(C,RATRAT-1K1)"
proof
(*coherence*)
  show "f1 (#)VALUED-1K19 f2 be PartFuncPARTFUN1M1-of(C,RATRAT-1K1)"
sorry
qed "sorry"

syntax VALUED_1K23 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ '(#')VALUED-1K23\<^bsub>'( _ , _ , _ ')\<^esub>  _ " [164,0,0,0,164]164)
translations "f1 (#)VALUED-1K23\<^bsub>(C,D1,D2)\<^esub> f2" \<rightharpoonup> "f1 (#)VALUED-1K19 f2"

mtheorem valued_1_add_18:
  mlet "C be setHIDDENM2", "D1 be integer-memberedMEMBEREDV5\<bar>setHIDDENM2", "D2 be integer-memberedMEMBEREDV5\<bar>setHIDDENM2", "f1 be PartFuncPARTFUN1M1-of(C,D1)", "f2 be PartFuncPARTFUN1M1-of(C,D2)"
"cluster f1 (#)VALUED-1K19 f2 as-term-is PartFuncPARTFUN1M1-of(C,INTINT-1K1)"
proof
(*coherence*)
  show "f1 (#)VALUED-1K19 f2 be PartFuncPARTFUN1M1-of(C,INTINT-1K1)"
sorry
qed "sorry"

syntax VALUED_1K24 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ '(#')VALUED-1K24\<^bsub>'( _ , _ , _ ')\<^esub>  _ " [164,0,0,0,164]164)
translations "f1 (#)VALUED-1K24\<^bsub>(C,D1,D2)\<^esub> f2" \<rightharpoonup> "f1 (#)VALUED-1K19 f2"

mtheorem valued_1_add_19:
  mlet "C be setHIDDENM2", "D1 be natural-memberedMEMBEREDV6\<bar>setHIDDENM2", "D2 be natural-memberedMEMBEREDV6\<bar>setHIDDENM2", "f1 be PartFuncPARTFUN1M1-of(C,D1)", "f2 be PartFuncPARTFUN1M1-of(C,D2)"
"cluster f1 (#)VALUED-1K19 f2 as-term-is PartFuncPARTFUN1M1-of(C,NATNUMBERSK1)"
proof
(*coherence*)
  show "f1 (#)VALUED-1K19 f2 be PartFuncPARTFUN1M1-of(C,NATNUMBERSK1)"
sorry
qed "sorry"

mtheorem valued_1_cl_39:
  mlet "C be setHIDDENM2", "D1 be complex-memberedMEMBEREDV1\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2", "D2 be complex-memberedMEMBEREDV1\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2", "f1 be FunctionFUNCT-2M1-of(C,D1)", "f2 be FunctionFUNCT-2M1-of(C,D2)"
"cluster f1 (#)VALUED-1K20\<^bsub>(C,D1,D2)\<^esub> f2 as-term-is totalPARTFUN1V1\<^bsub>(C)\<^esub> for PartFuncPARTFUN1M1-of(C,COMPLEXNUMBERSK3)"
proof
(*coherence*)
  show " for it be PartFuncPARTFUN1M1-of(C,COMPLEXNUMBERSK3) holds it =HIDDENR1 f1 (#)VALUED-1K20\<^bsub>(C,D1,D2)\<^esub> f2 implies it be totalPARTFUN1V1\<^bsub>(C)\<^esub>"
sorry
qed "sorry"

mtheorem valued_1_cl_40:
  mlet "C be setHIDDENM2", "D1 be real-memberedMEMBEREDV3\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2", "D2 be real-memberedMEMBEREDV3\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2", "f1 be FunctionFUNCT-2M1-of(C,D1)", "f2 be FunctionFUNCT-2M1-of(C,D2)"
"cluster f1 (#)VALUED-1K21\<^bsub>(C,D1,D2)\<^esub> f2 as-term-is totalPARTFUN1V1\<^bsub>(C)\<^esub> for PartFuncPARTFUN1M1-of(C,REALNUMBERSK2)"
proof
(*coherence*)
  show " for it be PartFuncPARTFUN1M1-of(C,REALNUMBERSK2) holds it =HIDDENR1 f1 (#)VALUED-1K21\<^bsub>(C,D1,D2)\<^esub> f2 implies it be totalPARTFUN1V1\<^bsub>(C)\<^esub>"
sorry
qed "sorry"

mtheorem valued_1_cl_41:
  mlet "C be setHIDDENM2", "D1 be rational-memberedMEMBEREDV4\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2", "D2 be rational-memberedMEMBEREDV4\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2", "f1 be FunctionFUNCT-2M1-of(C,D1)", "f2 be FunctionFUNCT-2M1-of(C,D2)"
"cluster f1 (#)VALUED-1K22\<^bsub>(C,D1,D2)\<^esub> f2 as-term-is totalPARTFUN1V1\<^bsub>(C)\<^esub> for PartFuncPARTFUN1M1-of(C,RATRAT-1K1)"
proof
(*coherence*)
  show " for it be PartFuncPARTFUN1M1-of(C,RATRAT-1K1) holds it =HIDDENR1 f1 (#)VALUED-1K22\<^bsub>(C,D1,D2)\<^esub> f2 implies it be totalPARTFUN1V1\<^bsub>(C)\<^esub>"
sorry
qed "sorry"

mtheorem valued_1_cl_42:
  mlet "C be setHIDDENM2", "D1 be integer-memberedMEMBEREDV5\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2", "D2 be integer-memberedMEMBEREDV5\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2", "f1 be FunctionFUNCT-2M1-of(C,D1)", "f2 be FunctionFUNCT-2M1-of(C,D2)"
"cluster f1 (#)VALUED-1K23\<^bsub>(C,D1,D2)\<^esub> f2 as-term-is totalPARTFUN1V1\<^bsub>(C)\<^esub> for PartFuncPARTFUN1M1-of(C,INTINT-1K1)"
proof
(*coherence*)
  show " for it be PartFuncPARTFUN1M1-of(C,INTINT-1K1) holds it =HIDDENR1 f1 (#)VALUED-1K23\<^bsub>(C,D1,D2)\<^esub> f2 implies it be totalPARTFUN1V1\<^bsub>(C)\<^esub>"
sorry
qed "sorry"

mtheorem valued_1_cl_43:
  mlet "C be setHIDDENM2", "D1 be natural-memberedMEMBEREDV6\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2", "D2 be natural-memberedMEMBEREDV6\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2", "f1 be FunctionFUNCT-2M1-of(C,D1)", "f2 be FunctionFUNCT-2M1-of(C,D2)"
"cluster f1 (#)VALUED-1K24\<^bsub>(C,D1,D2)\<^esub> f2 as-term-is totalPARTFUN1V1\<^bsub>(C)\<^esub> for PartFuncPARTFUN1M1-of(C,NATNUMBERSK1)"
proof
(*coherence*)
  show " for it be PartFuncPARTFUN1M1-of(C,NATNUMBERSK1) holds it =HIDDENR1 f1 (#)VALUED-1K24\<^bsub>(C,D1,D2)\<^esub> f2 implies it be totalPARTFUN1V1\<^bsub>(C)\<^esub>"
sorry
qed "sorry"

mtheorem valued_1_cl_44:
  mlet "f1 be complex-valuedVALUED-0V5\<bar>FinSequenceFINSEQ-1M1", "f2 be complex-valuedVALUED-0V5\<bar>FinSequenceFINSEQ-1M1"
"cluster f1 (#)VALUED-1K19 f2 as-term-is FinSequence-likeFINSEQ-1V1"
proof
(*coherence*)
  show "f1 (#)VALUED-1K19 f2 be FinSequence-likeFINSEQ-1V1"
sorry
qed "sorry"

(*begin*)
mdef valued_1_def_5 (" _ '(#')VALUED-1K25  _ " [164,164]164 ) where
  mlet "f be complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1", "r be ComplexXCMPLX-0M1"
"func r (#)VALUED-1K25 f \<rightarrow> FunctionFUNCT-1M1 means
  \<lambda>it. domRELAT-1K1 it =XBOOLE-0R4 domRELAT-1K1 f & ( for c be objectHIDDENM1 holds c inHIDDENR3 domRELAT-1K1 it implies it .FUNCT-1K1 c =XBOOLE-0R4 r *XCMPLX-0K3 f .FUNCT-1K1 c)"
proof-
  (*existence*)
    show " ex it be FunctionFUNCT-1M1 st domRELAT-1K1 it =XBOOLE-0R4 domRELAT-1K1 f & ( for c be objectHIDDENM1 holds c inHIDDENR3 domRELAT-1K1 it implies it .FUNCT-1K1 c =XBOOLE-0R4 r *XCMPLX-0K3 f .FUNCT-1K1 c)"
sorry
  (*uniqueness*)
    show " for it1 be FunctionFUNCT-1M1 holds  for it2 be FunctionFUNCT-1M1 holds (domRELAT-1K1 it1 =XBOOLE-0R4 domRELAT-1K1 f & ( for c be objectHIDDENM1 holds c inHIDDENR3 domRELAT-1K1 it1 implies it1 .FUNCT-1K1 c =XBOOLE-0R4 r *XCMPLX-0K3 f .FUNCT-1K1 c)) & (domRELAT-1K1 it2 =XBOOLE-0R4 domRELAT-1K1 f & ( for c be objectHIDDENM1 holds c inHIDDENR3 domRELAT-1K1 it2 implies it2 .FUNCT-1K1 c =XBOOLE-0R4 r *XCMPLX-0K3 f .FUNCT-1K1 c)) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

abbreviation(input) VALUED_1K26(" _ '(#')VALUED-1K26  _ " [164,164]164) where
  "f (#)VALUED-1K26 r \<equiv> r (#)VALUED-1K25 f"

mtheorem valued_1_th_6:
" for f be complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1 holds  for r be ComplexXCMPLX-0M1 holds  for c be objectHIDDENM1 holds (r (#)VALUED-1K25 f).FUNCT-1K1 c =XBOOLE-0R4 r *XCMPLX-0K3 f .FUNCT-1K1 c"
sorry

mtheorem valued_1_cl_45:
  mlet "f be complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1", "r be ComplexXCMPLX-0M1"
"cluster r (#)VALUED-1K25 f as-term-is complex-valuedVALUED-0V5"
proof
(*coherence*)
  show "r (#)VALUED-1K25 f be complex-valuedVALUED-0V5"
sorry
qed "sorry"

mtheorem valued_1_cl_46:
  mlet "f be real-valuedVALUED-0V7\<bar>FunctionFUNCT-1M1", "r be RealXREAL-0M1"
"cluster r (#)VALUED-1K25 f as-term-is real-valuedVALUED-0V7"
proof
(*coherence*)
  show "r (#)VALUED-1K25 f be real-valuedVALUED-0V7"
sorry
qed "sorry"

mtheorem valued_1_cl_47:
  mlet "f be RATRAT-1K1 -valuedRELAT-1V5\<bar>FunctionFUNCT-1M1", "r be RationalRAT-1M1"
"cluster r (#)VALUED-1K25 f as-term-is RATRAT-1K1 -valuedRELAT-1V5"
proof
(*coherence*)
  show "r (#)VALUED-1K25 f be RATRAT-1K1 -valuedRELAT-1V5"
sorry
qed "sorry"

mtheorem valued_1_cl_48:
  mlet "f be INTINT-1K1 -valuedRELAT-1V5\<bar>FunctionFUNCT-1M1", "r be IntegerINT-1M1"
"cluster r (#)VALUED-1K25 f as-term-is INTINT-1K1 -valuedRELAT-1V5"
proof
(*coherence*)
  show "r (#)VALUED-1K25 f be INTINT-1K1 -valuedRELAT-1V5"
sorry
qed "sorry"

mtheorem valued_1_cl_49:
  mlet "f be natural-valuedVALUED-0V8\<bar>FunctionFUNCT-1M1", "r be NatNAT-1M1"
"cluster r (#)VALUED-1K25 f as-term-is natural-valuedVALUED-0V8"
proof
(*coherence*)
  show "r (#)VALUED-1K25 f be natural-valuedVALUED-0V8"
sorry
qed "sorry"

syntax VALUED_1K27 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ '(#')VALUED-1K27\<^bsub>'( _ , _ ')\<^esub>  _ " [164,0,0,164]164)
translations "r (#)VALUED-1K27\<^bsub>(C,D)\<^esub> f" \<rightharpoonup> "r (#)VALUED-1K25 f"

mtheorem valued_1_add_20:
  mlet "C be setHIDDENM2", "D be complex-memberedMEMBEREDV1\<bar>setHIDDENM2", "f be PartFuncPARTFUN1M1-of(C,D)", "r be ComplexXCMPLX-0M1"
"cluster r (#)VALUED-1K25 f as-term-is PartFuncPARTFUN1M1-of(C,COMPLEXNUMBERSK3)"
proof
(*coherence*)
  show "r (#)VALUED-1K25 f be PartFuncPARTFUN1M1-of(C,COMPLEXNUMBERSK3)"
sorry
qed "sorry"

syntax VALUED_1K28 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ '(#')VALUED-1K28\<^bsub>'( _ , _ ')\<^esub>  _ " [164,0,0,164]164)
translations "r (#)VALUED-1K28\<^bsub>(C,D)\<^esub> f" \<rightharpoonup> "r (#)VALUED-1K25 f"

mtheorem valued_1_add_21:
  mlet "C be setHIDDENM2", "D be real-memberedMEMBEREDV3\<bar>setHIDDENM2", "f be PartFuncPARTFUN1M1-of(C,D)", "r be RealXREAL-0M1"
"cluster r (#)VALUED-1K25 f as-term-is PartFuncPARTFUN1M1-of(C,REALNUMBERSK2)"
proof
(*coherence*)
  show "r (#)VALUED-1K25 f be PartFuncPARTFUN1M1-of(C,REALNUMBERSK2)"
sorry
qed "sorry"

syntax VALUED_1K29 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ '(#')VALUED-1K29\<^bsub>'( _ , _ ')\<^esub>  _ " [164,0,0,164]164)
translations "r (#)VALUED-1K29\<^bsub>(C,D)\<^esub> f" \<rightharpoonup> "r (#)VALUED-1K25 f"

mtheorem valued_1_add_22:
  mlet "C be setHIDDENM2", "D be rational-memberedMEMBEREDV4\<bar>setHIDDENM2", "f be PartFuncPARTFUN1M1-of(C,D)", "r be RationalRAT-1M1"
"cluster r (#)VALUED-1K25 f as-term-is PartFuncPARTFUN1M1-of(C,RATRAT-1K1)"
proof
(*coherence*)
  show "r (#)VALUED-1K25 f be PartFuncPARTFUN1M1-of(C,RATRAT-1K1)"
sorry
qed "sorry"

syntax VALUED_1K30 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ '(#')VALUED-1K30\<^bsub>'( _ , _ ')\<^esub>  _ " [164,0,0,164]164)
translations "r (#)VALUED-1K30\<^bsub>(C,D)\<^esub> f" \<rightharpoonup> "r (#)VALUED-1K25 f"

mtheorem valued_1_add_23:
  mlet "C be setHIDDENM2", "D be integer-memberedMEMBEREDV5\<bar>setHIDDENM2", "f be PartFuncPARTFUN1M1-of(C,D)", "r be IntegerINT-1M1"
"cluster r (#)VALUED-1K25 f as-term-is PartFuncPARTFUN1M1-of(C,INTINT-1K1)"
proof
(*coherence*)
  show "r (#)VALUED-1K25 f be PartFuncPARTFUN1M1-of(C,INTINT-1K1)"
sorry
qed "sorry"

syntax VALUED_1K31 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ '(#')VALUED-1K31\<^bsub>'( _ , _ ')\<^esub>  _ " [164,0,0,164]164)
translations "r (#)VALUED-1K31\<^bsub>(C,D)\<^esub> f" \<rightharpoonup> "r (#)VALUED-1K25 f"

mtheorem valued_1_add_24:
  mlet "C be setHIDDENM2", "D be natural-memberedMEMBEREDV6\<bar>setHIDDENM2", "f be PartFuncPARTFUN1M1-of(C,D)", "r be NatNAT-1M1"
"cluster r (#)VALUED-1K25 f as-term-is PartFuncPARTFUN1M1-of(C,NATNUMBERSK1)"
proof
(*coherence*)
  show "r (#)VALUED-1K25 f be PartFuncPARTFUN1M1-of(C,NATNUMBERSK1)"
sorry
qed "sorry"

mtheorem valued_1_cl_50:
  mlet "C be setHIDDENM2", "D be complex-memberedMEMBEREDV1\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2", "f be FunctionFUNCT-2M1-of(C,D)", "r be ComplexXCMPLX-0M1"
"cluster r (#)VALUED-1K27\<^bsub>(C,D)\<^esub> f as-term-is totalPARTFUN1V1\<^bsub>(C)\<^esub> for PartFuncPARTFUN1M1-of(C,COMPLEXNUMBERSK3)"
proof
(*coherence*)
  show " for it be PartFuncPARTFUN1M1-of(C,COMPLEXNUMBERSK3) holds it =HIDDENR1 r (#)VALUED-1K27\<^bsub>(C,D)\<^esub> f implies it be totalPARTFUN1V1\<^bsub>(C)\<^esub>"
sorry
qed "sorry"

mtheorem valued_1_cl_51:
  mlet "C be setHIDDENM2", "D be real-memberedMEMBEREDV3\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2", "f be FunctionFUNCT-2M1-of(C,D)", "r be RealXREAL-0M1"
"cluster r (#)VALUED-1K28\<^bsub>(C,D)\<^esub> f as-term-is totalPARTFUN1V1\<^bsub>(C)\<^esub> for PartFuncPARTFUN1M1-of(C,REALNUMBERSK2)"
proof
(*coherence*)
  show " for it be PartFuncPARTFUN1M1-of(C,REALNUMBERSK2) holds it =HIDDENR1 r (#)VALUED-1K28\<^bsub>(C,D)\<^esub> f implies it be totalPARTFUN1V1\<^bsub>(C)\<^esub>"
sorry
qed "sorry"

mtheorem valued_1_cl_52:
  mlet "C be setHIDDENM2", "D be rational-memberedMEMBEREDV4\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2", "f be FunctionFUNCT-2M1-of(C,D)", "r be RationalRAT-1M1"
"cluster r (#)VALUED-1K29\<^bsub>(C,D)\<^esub> f as-term-is totalPARTFUN1V1\<^bsub>(C)\<^esub> for PartFuncPARTFUN1M1-of(C,RATRAT-1K1)"
proof
(*coherence*)
  show " for it be PartFuncPARTFUN1M1-of(C,RATRAT-1K1) holds it =HIDDENR1 r (#)VALUED-1K29\<^bsub>(C,D)\<^esub> f implies it be totalPARTFUN1V1\<^bsub>(C)\<^esub>"
sorry
qed "sorry"

mtheorem valued_1_cl_53:
  mlet "C be setHIDDENM2", "D be integer-memberedMEMBEREDV5\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2", "f be FunctionFUNCT-2M1-of(C,D)", "r be IntegerINT-1M1"
"cluster r (#)VALUED-1K30\<^bsub>(C,D)\<^esub> f as-term-is totalPARTFUN1V1\<^bsub>(C)\<^esub> for PartFuncPARTFUN1M1-of(C,INTINT-1K1)"
proof
(*coherence*)
  show " for it be PartFuncPARTFUN1M1-of(C,INTINT-1K1) holds it =HIDDENR1 r (#)VALUED-1K30\<^bsub>(C,D)\<^esub> f implies it be totalPARTFUN1V1\<^bsub>(C)\<^esub>"
sorry
qed "sorry"

mtheorem valued_1_cl_54:
  mlet "C be setHIDDENM2", "D be natural-memberedMEMBEREDV6\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2", "f be FunctionFUNCT-2M1-of(C,D)", "r be NatNAT-1M1"
"cluster r (#)VALUED-1K31\<^bsub>(C,D)\<^esub> f as-term-is totalPARTFUN1V1\<^bsub>(C)\<^esub> for PartFuncPARTFUN1M1-of(C,NATNUMBERSK1)"
proof
(*coherence*)
  show " for it be PartFuncPARTFUN1M1-of(C,NATNUMBERSK1) holds it =HIDDENR1 r (#)VALUED-1K31\<^bsub>(C,D)\<^esub> f implies it be totalPARTFUN1V1\<^bsub>(C)\<^esub>"
sorry
qed "sorry"

mtheorem valued_1_th_7:
" for C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D be complex-memberedMEMBEREDV1\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(C,D) holds  for r be ComplexXCMPLX-0M1 holds  for g be FunctionFUNCT-2M1-of(C,COMPLEXNUMBERSK3) holds ( for c be ElementSUBSET-1M1-of C holds g .FUNCT-2K3\<^bsub>(C,COMPLEXNUMBERSK3)\<^esub> c =XBOOLE-0R4 r *XCMPLX-0K3 f .FUNCT-2K3\<^bsub>(C,D)\<^esub> c) implies g =FUNCT-2R2\<^bsub>(C,COMPLEXNUMBERSK3)\<^esub> r (#)VALUED-1K27\<^bsub>(C,D)\<^esub> f"
sorry

mtheorem valued_1_cl_55:
  mlet "f be complex-valuedVALUED-0V5\<bar>FinSequenceFINSEQ-1M1", "r be ComplexXCMPLX-0M1"
"cluster r (#)VALUED-1K25 f as-term-is FinSequence-likeFINSEQ-1V1"
proof
(*coherence*)
  show "r (#)VALUED-1K25 f be FinSequence-likeFINSEQ-1V1"
sorry
qed "sorry"

(*begin*)
mdef valued_1_def_6 ("-VALUED-1K32  _ " [132]132 ) where
  mlet "f be complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1"
"func -VALUED-1K32 f \<rightarrow> complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1 equals
  (-XCMPLX-0K4 \<one>\<^sub>M)(#)VALUED-1K25 f"
proof-
  (*coherence*)
    show "(-XCMPLX-0K4 \<one>\<^sub>M)(#)VALUED-1K25 f be complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1"
       sorry
qed "sorry"

mtheorem VALUED_1K32_involutiveness:
" for f be complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1 holds -VALUED-1K32 (-VALUED-1K32 f) =HIDDENR1 f"
sorry

mtheorem valued_1_th_8:
" for f be complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1 holds domRELAT-1K1 (-VALUED-1K32 f) =XBOOLE-0R4 domRELAT-1K1 f & ( for c be objectHIDDENM1 holds (-VALUED-1K32 f).FUNCT-1K1 c =COMPLEX1R1 -XCMPLX-0K4 f .FUNCT-1K1 c)"
sorry

mtheorem valued_1_th_9:
" for f be complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds domRELAT-1K1 f =XBOOLE-0R4 domRELAT-1K1 g & ( for c be objectHIDDENM1 holds c inHIDDENR3 domRELAT-1K1 f implies g .FUNCT-1K1 c =HIDDENR1 -XCMPLX-0K4 f .FUNCT-1K1 c) implies g =FUNCT-1R1 -VALUED-1K32 f"
sorry

mtheorem valued_1_cl_56:
  mlet "f be complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1"
"cluster -VALUED-1K32 f as-term-is complex-valuedVALUED-0V5"
proof
(*coherence*)
  show "-VALUED-1K32 f be complex-valuedVALUED-0V5"
     sorry
qed "sorry"

mtheorem valued_1_cl_57:
  mlet "f be real-valuedVALUED-0V7\<bar>FunctionFUNCT-1M1"
"cluster -VALUED-1K32 f as-term-is real-valuedVALUED-0V7"
proof
(*coherence*)
  show "-VALUED-1K32 f be real-valuedVALUED-0V7"
     sorry
qed "sorry"

mtheorem valued_1_cl_58:
  mlet "f be RATRAT-1K1 -valuedRELAT-1V5\<bar>FunctionFUNCT-1M1"
"cluster -VALUED-1K32 f as-term-is RATRAT-1K1 -valuedRELAT-1V5"
proof
(*coherence*)
  show "-VALUED-1K32 f be RATRAT-1K1 -valuedRELAT-1V5"
     sorry
qed "sorry"

mtheorem valued_1_cl_59:
  mlet "f be INTINT-1K1 -valuedRELAT-1V5\<bar>FunctionFUNCT-1M1"
"cluster -VALUED-1K32 f as-term-is INTINT-1K1 -valuedRELAT-1V5"
proof
(*coherence*)
  show "-VALUED-1K32 f be INTINT-1K1 -valuedRELAT-1V5"
     sorry
qed "sorry"

syntax VALUED_1K33 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" ("-VALUED-1K33\<^bsub>'( _ , _ ')\<^esub>  _ " [0,0,132]132)
translations "-VALUED-1K33\<^bsub>(C,D)\<^esub> f" \<rightharpoonup> "-VALUED-1K32 f"

mtheorem valued_1_add_25:
  mlet "C be setHIDDENM2", "D be complex-memberedMEMBEREDV1\<bar>setHIDDENM2", "f be PartFuncPARTFUN1M1-of(C,D)"
"cluster -VALUED-1K32 f as-term-is PartFuncPARTFUN1M1-of(C,COMPLEXNUMBERSK3)"
proof
(*coherence*)
  show "-VALUED-1K32 f be PartFuncPARTFUN1M1-of(C,COMPLEXNUMBERSK3)"
sorry
qed "sorry"

syntax VALUED_1K34 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" ("-VALUED-1K34\<^bsub>'( _ , _ ')\<^esub>  _ " [0,0,132]132)
translations "-VALUED-1K34\<^bsub>(C,D)\<^esub> f" \<rightharpoonup> "-VALUED-1K32 f"

mtheorem valued_1_add_26:
  mlet "C be setHIDDENM2", "D be real-memberedMEMBEREDV3\<bar>setHIDDENM2", "f be PartFuncPARTFUN1M1-of(C,D)"
"cluster -VALUED-1K32 f as-term-is PartFuncPARTFUN1M1-of(C,REALNUMBERSK2)"
proof
(*coherence*)
  show "-VALUED-1K32 f be PartFuncPARTFUN1M1-of(C,REALNUMBERSK2)"
sorry
qed "sorry"

syntax VALUED_1K35 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" ("-VALUED-1K35\<^bsub>'( _ , _ ')\<^esub>  _ " [0,0,132]132)
translations "-VALUED-1K35\<^bsub>(C,D)\<^esub> f" \<rightharpoonup> "-VALUED-1K32 f"

mtheorem valued_1_add_27:
  mlet "C be setHIDDENM2", "D be rational-memberedMEMBEREDV4\<bar>setHIDDENM2", "f be PartFuncPARTFUN1M1-of(C,D)"
"cluster -VALUED-1K32 f as-term-is PartFuncPARTFUN1M1-of(C,RATRAT-1K1)"
proof
(*coherence*)
  show "-VALUED-1K32 f be PartFuncPARTFUN1M1-of(C,RATRAT-1K1)"
sorry
qed "sorry"

syntax VALUED_1K36 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" ("-VALUED-1K36\<^bsub>'( _ , _ ')\<^esub>  _ " [0,0,132]132)
translations "-VALUED-1K36\<^bsub>(C,D)\<^esub> f" \<rightharpoonup> "-VALUED-1K32 f"

mtheorem valued_1_add_28:
  mlet "C be setHIDDENM2", "D be integer-memberedMEMBEREDV5\<bar>setHIDDENM2", "f be PartFuncPARTFUN1M1-of(C,D)"
"cluster -VALUED-1K32 f as-term-is PartFuncPARTFUN1M1-of(C,INTINT-1K1)"
proof
(*coherence*)
  show "-VALUED-1K32 f be PartFuncPARTFUN1M1-of(C,INTINT-1K1)"
sorry
qed "sorry"

mtheorem valued_1_cl_60:
  mlet "C be setHIDDENM2", "D be complex-memberedMEMBEREDV1\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2", "f be FunctionFUNCT-2M1-of(C,D)"
"cluster -VALUED-1K33\<^bsub>(C,D)\<^esub> f as-term-is totalPARTFUN1V1\<^bsub>(C)\<^esub> for PartFuncPARTFUN1M1-of(C,COMPLEXNUMBERSK3)"
proof
(*coherence*)
  show " for it be PartFuncPARTFUN1M1-of(C,COMPLEXNUMBERSK3) holds it =HIDDENR1 -VALUED-1K33\<^bsub>(C,D)\<^esub> f implies it be totalPARTFUN1V1\<^bsub>(C)\<^esub>"
     sorry
qed "sorry"

mtheorem valued_1_cl_61:
  mlet "C be setHIDDENM2", "D be real-memberedMEMBEREDV3\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2", "f be FunctionFUNCT-2M1-of(C,D)"
"cluster -VALUED-1K34\<^bsub>(C,D)\<^esub> f as-term-is totalPARTFUN1V1\<^bsub>(C)\<^esub> for PartFuncPARTFUN1M1-of(C,REALNUMBERSK2)"
proof
(*coherence*)
  show " for it be PartFuncPARTFUN1M1-of(C,REALNUMBERSK2) holds it =HIDDENR1 -VALUED-1K34\<^bsub>(C,D)\<^esub> f implies it be totalPARTFUN1V1\<^bsub>(C)\<^esub>"
     sorry
qed "sorry"

mtheorem valued_1_cl_62:
  mlet "C be setHIDDENM2", "D be rational-memberedMEMBEREDV4\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2", "f be FunctionFUNCT-2M1-of(C,D)"
"cluster -VALUED-1K35\<^bsub>(C,D)\<^esub> f as-term-is totalPARTFUN1V1\<^bsub>(C)\<^esub> for PartFuncPARTFUN1M1-of(C,RATRAT-1K1)"
proof
(*coherence*)
  show " for it be PartFuncPARTFUN1M1-of(C,RATRAT-1K1) holds it =HIDDENR1 -VALUED-1K35\<^bsub>(C,D)\<^esub> f implies it be totalPARTFUN1V1\<^bsub>(C)\<^esub>"
     sorry
qed "sorry"

mtheorem valued_1_cl_63:
  mlet "C be setHIDDENM2", "D be integer-memberedMEMBEREDV5\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2", "f be FunctionFUNCT-2M1-of(C,D)"
"cluster -VALUED-1K36\<^bsub>(C,D)\<^esub> f as-term-is totalPARTFUN1V1\<^bsub>(C)\<^esub> for PartFuncPARTFUN1M1-of(C,INTINT-1K1)"
proof
(*coherence*)
  show " for it be PartFuncPARTFUN1M1-of(C,INTINT-1K1) holds it =HIDDENR1 -VALUED-1K36\<^bsub>(C,D)\<^esub> f implies it be totalPARTFUN1V1\<^bsub>(C)\<^esub>"
     sorry
qed "sorry"

mtheorem valued_1_cl_64:
  mlet "f be complex-valuedVALUED-0V5\<bar>FinSequenceFINSEQ-1M1"
"cluster -VALUED-1K32 f as-term-is FinSequence-likeFINSEQ-1V1"
proof
(*coherence*)
  show "-VALUED-1K32 f be FinSequence-likeFINSEQ-1V1"
     sorry
qed "sorry"

(*begin*)
mdef valued_1_def_7 (" _ \<inverse>VALUED-1K37" [228]228 ) where
  mlet "f be complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1"
"func f \<inverse>VALUED-1K37 \<rightarrow> complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1 means
  \<lambda>it. domRELAT-1K1 it =XBOOLE-0R4 domRELAT-1K1 f & ( for c be objectHIDDENM1 holds c inHIDDENR3 domRELAT-1K1 it implies it .FUNCT-1K1 c =COMPLEX1R1 (f .FUNCT-1K1 c)\<inverse>XCMPLX-0K5)"
proof-
  (*existence*)
    show " ex it be complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1 st domRELAT-1K1 it =XBOOLE-0R4 domRELAT-1K1 f & ( for c be objectHIDDENM1 holds c inHIDDENR3 domRELAT-1K1 it implies it .FUNCT-1K1 c =COMPLEX1R1 (f .FUNCT-1K1 c)\<inverse>XCMPLX-0K5)"
sorry
  (*uniqueness*)
    show " for it1 be complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1 holds  for it2 be complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1 holds (domRELAT-1K1 it1 =XBOOLE-0R4 domRELAT-1K1 f & ( for c be objectHIDDENM1 holds c inHIDDENR3 domRELAT-1K1 it1 implies it1 .FUNCT-1K1 c =COMPLEX1R1 (f .FUNCT-1K1 c)\<inverse>XCMPLX-0K5)) & (domRELAT-1K1 it2 =XBOOLE-0R4 domRELAT-1K1 f & ( for c be objectHIDDENM1 holds c inHIDDENR3 domRELAT-1K1 it2 implies it2 .FUNCT-1K1 c =COMPLEX1R1 (f .FUNCT-1K1 c)\<inverse>XCMPLX-0K5)) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mtheorem VALUED_1K37_involutiveness:
" for f be complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1 holds (f \<inverse>VALUED-1K37)\<inverse>VALUED-1K37 =HIDDENR1 f"
sorry

mtheorem valued_1_th_10:
" for f be complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1 holds  for c be objectHIDDENM1 holds f \<inverse>VALUED-1K37 .FUNCT-1K1 c =COMPLEX1R1 (f .FUNCT-1K1 c)\<inverse>XCMPLX-0K5"
sorry

mtheorem valued_1_cl_65:
  mlet "f be real-valuedVALUED-0V7\<bar>FunctionFUNCT-1M1"
"cluster f \<inverse>VALUED-1K37 as-term-is real-valuedVALUED-0V7"
proof
(*coherence*)
  show "f \<inverse>VALUED-1K37 be real-valuedVALUED-0V7"
sorry
qed "sorry"

mtheorem valued_1_cl_66:
  mlet "f be RATRAT-1K1 -valuedRELAT-1V5\<bar>FunctionFUNCT-1M1"
"cluster f \<inverse>VALUED-1K37 as-term-is RATRAT-1K1 -valuedRELAT-1V5"
proof
(*coherence*)
  show "f \<inverse>VALUED-1K37 be RATRAT-1K1 -valuedRELAT-1V5"
sorry
qed "sorry"

syntax VALUED_1K38 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ \<inverse>VALUED-1K38\<^bsub>'( _ , _ ')\<^esub>" [228,0,0]228)
translations "f \<inverse>VALUED-1K38\<^bsub>(C,D)\<^esub>" \<rightharpoonup> "f \<inverse>VALUED-1K37"

mtheorem valued_1_add_29:
  mlet "C be setHIDDENM2", "D be complex-memberedMEMBEREDV1\<bar>setHIDDENM2", "f be PartFuncPARTFUN1M1-of(C,D)"
"cluster f \<inverse>VALUED-1K37 as-term-is PartFuncPARTFUN1M1-of(C,COMPLEXNUMBERSK3)"
proof
(*coherence*)
  show "f \<inverse>VALUED-1K37 be PartFuncPARTFUN1M1-of(C,COMPLEXNUMBERSK3)"
sorry
qed "sorry"

syntax VALUED_1K39 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ \<inverse>VALUED-1K39\<^bsub>'( _ , _ ')\<^esub>" [228,0,0]228)
translations "f \<inverse>VALUED-1K39\<^bsub>(C,D)\<^esub>" \<rightharpoonup> "f \<inverse>VALUED-1K37"

mtheorem valued_1_add_30:
  mlet "C be setHIDDENM2", "D be real-memberedMEMBEREDV3\<bar>setHIDDENM2", "f be PartFuncPARTFUN1M1-of(C,D)"
"cluster f \<inverse>VALUED-1K37 as-term-is PartFuncPARTFUN1M1-of(C,REALNUMBERSK2)"
proof
(*coherence*)
  show "f \<inverse>VALUED-1K37 be PartFuncPARTFUN1M1-of(C,REALNUMBERSK2)"
sorry
qed "sorry"

syntax VALUED_1K40 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ \<inverse>VALUED-1K40\<^bsub>'( _ , _ ')\<^esub>" [228,0,0]228)
translations "f \<inverse>VALUED-1K40\<^bsub>(C,D)\<^esub>" \<rightharpoonup> "f \<inverse>VALUED-1K37"

mtheorem valued_1_add_31:
  mlet "C be setHIDDENM2", "D be rational-memberedMEMBEREDV4\<bar>setHIDDENM2", "f be PartFuncPARTFUN1M1-of(C,D)"
"cluster f \<inverse>VALUED-1K37 as-term-is PartFuncPARTFUN1M1-of(C,RATRAT-1K1)"
proof
(*coherence*)
  show "f \<inverse>VALUED-1K37 be PartFuncPARTFUN1M1-of(C,RATRAT-1K1)"
sorry
qed "sorry"

mtheorem valued_1_cl_67:
  mlet "C be setHIDDENM2", "D be complex-memberedMEMBEREDV1\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2", "f be FunctionFUNCT-2M1-of(C,D)"
"cluster f \<inverse>VALUED-1K38\<^bsub>(C,D)\<^esub> as-term-is totalPARTFUN1V1\<^bsub>(C)\<^esub> for PartFuncPARTFUN1M1-of(C,COMPLEXNUMBERSK3)"
proof
(*coherence*)
  show " for it be PartFuncPARTFUN1M1-of(C,COMPLEXNUMBERSK3) holds it =HIDDENR1 f \<inverse>VALUED-1K38\<^bsub>(C,D)\<^esub> implies it be totalPARTFUN1V1\<^bsub>(C)\<^esub>"
sorry
qed "sorry"

mtheorem valued_1_cl_68:
  mlet "C be setHIDDENM2", "D be real-memberedMEMBEREDV3\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2", "f be FunctionFUNCT-2M1-of(C,D)"
"cluster f \<inverse>VALUED-1K39\<^bsub>(C,D)\<^esub> as-term-is totalPARTFUN1V1\<^bsub>(C)\<^esub> for PartFuncPARTFUN1M1-of(C,REALNUMBERSK2)"
proof
(*coherence*)
  show " for it be PartFuncPARTFUN1M1-of(C,REALNUMBERSK2) holds it =HIDDENR1 f \<inverse>VALUED-1K39\<^bsub>(C,D)\<^esub> implies it be totalPARTFUN1V1\<^bsub>(C)\<^esub>"
sorry
qed "sorry"

mtheorem valued_1_cl_69:
  mlet "C be setHIDDENM2", "D be rational-memberedMEMBEREDV4\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2", "f be FunctionFUNCT-2M1-of(C,D)"
"cluster f \<inverse>VALUED-1K40\<^bsub>(C,D)\<^esub> as-term-is totalPARTFUN1V1\<^bsub>(C)\<^esub> for PartFuncPARTFUN1M1-of(C,RATRAT-1K1)"
proof
(*coherence*)
  show " for it be PartFuncPARTFUN1M1-of(C,RATRAT-1K1) holds it =HIDDENR1 f \<inverse>VALUED-1K40\<^bsub>(C,D)\<^esub> implies it be totalPARTFUN1V1\<^bsub>(C)\<^esub>"
sorry
qed "sorry"

mtheorem valued_1_cl_70:
  mlet "f be complex-valuedVALUED-0V5\<bar>FinSequenceFINSEQ-1M1"
"cluster f \<inverse>VALUED-1K37 as-term-is FinSequence-likeFINSEQ-1V1"
proof
(*coherence*)
  show "f \<inverse>VALUED-1K37 be FinSequence-likeFINSEQ-1V1"
sorry
qed "sorry"

(*begin*)
mdef valued_1_def_8 (" _ ^2VALUED-1K41" [354]354 ) where
  mlet "f be complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1"
"func f ^2VALUED-1K41 \<rightarrow> FunctionFUNCT-1M1 equals
  f (#)VALUED-1K19 f"
proof-
  (*coherence*)
    show "f (#)VALUED-1K19 f be FunctionFUNCT-1M1"
       sorry
qed "sorry"

mtheorem valued_1_th_11:
" for f be complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1 holds domRELAT-1K1 f ^2VALUED-1K41 =XBOOLE-0R4 domRELAT-1K1 f & ( for c be objectHIDDENM1 holds f ^2VALUED-1K41 .FUNCT-1K1 c =XBOOLE-0R4 (f .FUNCT-1K1 c)^2SQUARE-1K1)"
sorry

mtheorem valued_1_cl_71:
  mlet "f be complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1"
"cluster f ^2VALUED-1K41 as-term-is complex-valuedVALUED-0V5"
proof
(*coherence*)
  show "f ^2VALUED-1K41 be complex-valuedVALUED-0V5"
     sorry
qed "sorry"

mtheorem valued_1_cl_72:
  mlet "f be real-valuedVALUED-0V7\<bar>FunctionFUNCT-1M1"
"cluster f ^2VALUED-1K41 as-term-is real-valuedVALUED-0V7"
proof
(*coherence*)
  show "f ^2VALUED-1K41 be real-valuedVALUED-0V7"
     sorry
qed "sorry"

mtheorem valued_1_cl_73:
  mlet "f be RATRAT-1K1 -valuedRELAT-1V5\<bar>FunctionFUNCT-1M1"
"cluster f ^2VALUED-1K41 as-term-is RATRAT-1K1 -valuedRELAT-1V5"
proof
(*coherence*)
  show "f ^2VALUED-1K41 be RATRAT-1K1 -valuedRELAT-1V5"
     sorry
qed "sorry"

mtheorem valued_1_cl_74:
  mlet "f be INTINT-1K1 -valuedRELAT-1V5\<bar>FunctionFUNCT-1M1"
"cluster f ^2VALUED-1K41 as-term-is INTINT-1K1 -valuedRELAT-1V5"
proof
(*coherence*)
  show "f ^2VALUED-1K41 be INTINT-1K1 -valuedRELAT-1V5"
     sorry
qed "sorry"

mtheorem valued_1_cl_75:
  mlet "f be natural-valuedVALUED-0V8\<bar>FunctionFUNCT-1M1"
"cluster f ^2VALUED-1K41 as-term-is natural-valuedVALUED-0V8"
proof
(*coherence*)
  show "f ^2VALUED-1K41 be natural-valuedVALUED-0V8"
     sorry
qed "sorry"

syntax VALUED_1K42 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ ^2VALUED-1K42\<^bsub>'( _ , _ ')\<^esub>" [354,0,0]354)
translations "f ^2VALUED-1K42\<^bsub>(C,D)\<^esub>" \<rightharpoonup> "f ^2VALUED-1K41"

mtheorem valued_1_add_32:
  mlet "C be setHIDDENM2", "D be complex-memberedMEMBEREDV1\<bar>setHIDDENM2", "f be PartFuncPARTFUN1M1-of(C,D)"
"cluster f ^2VALUED-1K41 as-term-is PartFuncPARTFUN1M1-of(C,COMPLEXNUMBERSK3)"
proof
(*coherence*)
  show "f ^2VALUED-1K41 be PartFuncPARTFUN1M1-of(C,COMPLEXNUMBERSK3)"
sorry
qed "sorry"

syntax VALUED_1K43 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ ^2VALUED-1K43\<^bsub>'( _ , _ ')\<^esub>" [354,0,0]354)
translations "f ^2VALUED-1K43\<^bsub>(C,D)\<^esub>" \<rightharpoonup> "f ^2VALUED-1K41"

mtheorem valued_1_add_33:
  mlet "C be setHIDDENM2", "D be real-memberedMEMBEREDV3\<bar>setHIDDENM2", "f be PartFuncPARTFUN1M1-of(C,D)"
"cluster f ^2VALUED-1K41 as-term-is PartFuncPARTFUN1M1-of(C,REALNUMBERSK2)"
proof
(*coherence*)
  show "f ^2VALUED-1K41 be PartFuncPARTFUN1M1-of(C,REALNUMBERSK2)"
sorry
qed "sorry"

syntax VALUED_1K44 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ ^2VALUED-1K44\<^bsub>'( _ , _ ')\<^esub>" [354,0,0]354)
translations "f ^2VALUED-1K44\<^bsub>(C,D)\<^esub>" \<rightharpoonup> "f ^2VALUED-1K41"

mtheorem valued_1_add_34:
  mlet "C be setHIDDENM2", "D be rational-memberedMEMBEREDV4\<bar>setHIDDENM2", "f be PartFuncPARTFUN1M1-of(C,D)"
"cluster f ^2VALUED-1K41 as-term-is PartFuncPARTFUN1M1-of(C,RATRAT-1K1)"
proof
(*coherence*)
  show "f ^2VALUED-1K41 be PartFuncPARTFUN1M1-of(C,RATRAT-1K1)"
sorry
qed "sorry"

syntax VALUED_1K45 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ ^2VALUED-1K45\<^bsub>'( _ , _ ')\<^esub>" [354,0,0]354)
translations "f ^2VALUED-1K45\<^bsub>(C,D)\<^esub>" \<rightharpoonup> "f ^2VALUED-1K41"

mtheorem valued_1_add_35:
  mlet "C be setHIDDENM2", "D be integer-memberedMEMBEREDV5\<bar>setHIDDENM2", "f be PartFuncPARTFUN1M1-of(C,D)"
"cluster f ^2VALUED-1K41 as-term-is PartFuncPARTFUN1M1-of(C,INTINT-1K1)"
proof
(*coherence*)
  show "f ^2VALUED-1K41 be PartFuncPARTFUN1M1-of(C,INTINT-1K1)"
sorry
qed "sorry"

syntax VALUED_1K46 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ ^2VALUED-1K46\<^bsub>'( _ , _ ')\<^esub>" [354,0,0]354)
translations "f ^2VALUED-1K46\<^bsub>(C,D)\<^esub>" \<rightharpoonup> "f ^2VALUED-1K41"

mtheorem valued_1_add_36:
  mlet "C be setHIDDENM2", "D be natural-memberedMEMBEREDV6\<bar>setHIDDENM2", "f be PartFuncPARTFUN1M1-of(C,D)"
"cluster f ^2VALUED-1K41 as-term-is PartFuncPARTFUN1M1-of(C,NATNUMBERSK1)"
proof
(*coherence*)
  show "f ^2VALUED-1K41 be PartFuncPARTFUN1M1-of(C,NATNUMBERSK1)"
sorry
qed "sorry"

mtheorem valued_1_cl_76:
  mlet "C be setHIDDENM2", "D be complex-memberedMEMBEREDV1\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2", "f be FunctionFUNCT-2M1-of(C,D)"
"cluster f ^2VALUED-1K42\<^bsub>(C,D)\<^esub> as-term-is totalPARTFUN1V1\<^bsub>(C)\<^esub> for PartFuncPARTFUN1M1-of(C,COMPLEXNUMBERSK3)"
proof
(*coherence*)
  show " for it be PartFuncPARTFUN1M1-of(C,COMPLEXNUMBERSK3) holds it =HIDDENR1 f ^2VALUED-1K42\<^bsub>(C,D)\<^esub> implies it be totalPARTFUN1V1\<^bsub>(C)\<^esub>"
     sorry
qed "sorry"

mtheorem valued_1_cl_77:
  mlet "C be setHIDDENM2", "D be real-memberedMEMBEREDV3\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2", "f be FunctionFUNCT-2M1-of(C,D)"
"cluster f ^2VALUED-1K43\<^bsub>(C,D)\<^esub> as-term-is totalPARTFUN1V1\<^bsub>(C)\<^esub> for PartFuncPARTFUN1M1-of(C,REALNUMBERSK2)"
proof
(*coherence*)
  show " for it be PartFuncPARTFUN1M1-of(C,REALNUMBERSK2) holds it =HIDDENR1 f ^2VALUED-1K43\<^bsub>(C,D)\<^esub> implies it be totalPARTFUN1V1\<^bsub>(C)\<^esub>"
     sorry
qed "sorry"

mtheorem valued_1_cl_78:
  mlet "C be setHIDDENM2", "D be rational-memberedMEMBEREDV4\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2", "f be FunctionFUNCT-2M1-of(C,D)"
"cluster f ^2VALUED-1K44\<^bsub>(C,D)\<^esub> as-term-is totalPARTFUN1V1\<^bsub>(C)\<^esub> for PartFuncPARTFUN1M1-of(C,RATRAT-1K1)"
proof
(*coherence*)
  show " for it be PartFuncPARTFUN1M1-of(C,RATRAT-1K1) holds it =HIDDENR1 f ^2VALUED-1K44\<^bsub>(C,D)\<^esub> implies it be totalPARTFUN1V1\<^bsub>(C)\<^esub>"
     sorry
qed "sorry"

mtheorem valued_1_cl_79:
  mlet "C be setHIDDENM2", "D be integer-memberedMEMBEREDV5\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2", "f be FunctionFUNCT-2M1-of(C,D)"
"cluster f ^2VALUED-1K45\<^bsub>(C,D)\<^esub> as-term-is totalPARTFUN1V1\<^bsub>(C)\<^esub> for PartFuncPARTFUN1M1-of(C,INTINT-1K1)"
proof
(*coherence*)
  show " for it be PartFuncPARTFUN1M1-of(C,INTINT-1K1) holds it =HIDDENR1 f ^2VALUED-1K45\<^bsub>(C,D)\<^esub> implies it be totalPARTFUN1V1\<^bsub>(C)\<^esub>"
     sorry
qed "sorry"

mtheorem valued_1_cl_80:
  mlet "C be setHIDDENM2", "D be natural-memberedMEMBEREDV6\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2", "f be FunctionFUNCT-2M1-of(C,D)"
"cluster f ^2VALUED-1K46\<^bsub>(C,D)\<^esub> as-term-is totalPARTFUN1V1\<^bsub>(C)\<^esub> for PartFuncPARTFUN1M1-of(C,NATNUMBERSK1)"
proof
(*coherence*)
  show " for it be PartFuncPARTFUN1M1-of(C,NATNUMBERSK1) holds it =HIDDENR1 f ^2VALUED-1K46\<^bsub>(C,D)\<^esub> implies it be totalPARTFUN1V1\<^bsub>(C)\<^esub>"
     sorry
qed "sorry"

mtheorem valued_1_cl_81:
  mlet "f be complex-valuedVALUED-0V5\<bar>FinSequenceFINSEQ-1M1"
"cluster f ^2VALUED-1K41 as-term-is FinSequence-likeFINSEQ-1V1"
proof
(*coherence*)
  show "f ^2VALUED-1K41 be FinSequence-likeFINSEQ-1V1"
     sorry
qed "sorry"

(*begin*)
mdef valued_1_def_9 (" _ -VALUED-1K47  _ " [132,132]132 ) where
  mlet "f1 be complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1", "f2 be complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1"
"func f1 -VALUED-1K47 f2 \<rightarrow> FunctionFUNCT-1M1 equals
  f1 +VALUED-1K1 (-VALUED-1K32 f2)"
proof-
  (*coherence*)
    show "f1 +VALUED-1K1 (-VALUED-1K32 f2) be FunctionFUNCT-1M1"
       sorry
qed "sorry"

mtheorem valued_1_cl_82:
  mlet "f1 be complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1", "f2 be complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1"
"cluster f1 -VALUED-1K47 f2 as-term-is complex-valuedVALUED-0V5"
proof
(*coherence*)
  show "f1 -VALUED-1K47 f2 be complex-valuedVALUED-0V5"
     sorry
qed "sorry"

mtheorem valued_1_cl_83:
  mlet "f1 be real-valuedVALUED-0V7\<bar>FunctionFUNCT-1M1", "f2 be real-valuedVALUED-0V7\<bar>FunctionFUNCT-1M1"
"cluster f1 -VALUED-1K47 f2 as-term-is real-valuedVALUED-0V7"
proof
(*coherence*)
  show "f1 -VALUED-1K47 f2 be real-valuedVALUED-0V7"
     sorry
qed "sorry"

mtheorem valued_1_cl_84:
  mlet "f1 be RATRAT-1K1 -valuedRELAT-1V5\<bar>FunctionFUNCT-1M1", "f2 be RATRAT-1K1 -valuedRELAT-1V5\<bar>FunctionFUNCT-1M1"
"cluster f1 -VALUED-1K47 f2 as-term-is RATRAT-1K1 -valuedRELAT-1V5"
proof
(*coherence*)
  show "f1 -VALUED-1K47 f2 be RATRAT-1K1 -valuedRELAT-1V5"
     sorry
qed "sorry"

mtheorem valued_1_cl_85:
  mlet "f1 be INTINT-1K1 -valuedRELAT-1V5\<bar>FunctionFUNCT-1M1", "f2 be INTINT-1K1 -valuedRELAT-1V5\<bar>FunctionFUNCT-1M1"
"cluster f1 -VALUED-1K47 f2 as-term-is INTINT-1K1 -valuedRELAT-1V5"
proof
(*coherence*)
  show "f1 -VALUED-1K47 f2 be INTINT-1K1 -valuedRELAT-1V5"
     sorry
qed "sorry"

mtheorem valued_1_th_12:
" for f1 be complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1 holds  for f2 be complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1 holds domRELAT-1K1 (f1 -VALUED-1K47 f2) =XBOOLE-0R4 domRELAT-1K1 f1 /\\XBOOLE-0K3 domRELAT-1K1 f2"
sorry

mtheorem valued_1_th_13:
" for f1 be complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1 holds  for f2 be complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1 holds  for c be objectHIDDENM1 holds c inHIDDENR3 domRELAT-1K1 (f1 -VALUED-1K47 f2) implies (f1 -VALUED-1K47 f2).FUNCT-1K1 c =XBOOLE-0R4 f1 .FUNCT-1K1 c -XCMPLX-0K6 f2 .FUNCT-1K1 c"
sorry

mtheorem valued_1_th_14:
" for f1 be complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1 holds  for f2 be complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1 holds  for f be FunctionFUNCT-1M1 holds domRELAT-1K1 f =XBOOLE-0R4 domRELAT-1K1 (f1 -VALUED-1K47 f2) & ( for c be objectHIDDENM1 holds c inHIDDENR3 domRELAT-1K1 f implies f .FUNCT-1K1 c =XBOOLE-0R4 f1 .FUNCT-1K1 c -XCMPLX-0K6 f2 .FUNCT-1K1 c) implies f =FUNCT-1R1 f1 -VALUED-1K47 f2"
sorry

syntax VALUED_1K48 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ -VALUED-1K48\<^bsub>'( _ , _ , _ ')\<^esub>  _ " [132,0,0,0,132]132)
translations "f1 -VALUED-1K48\<^bsub>(C,D1,D2)\<^esub> f2" \<rightharpoonup> "f1 -VALUED-1K47 f2"

mtheorem valued_1_add_37:
  mlet "C be setHIDDENM2", "D1 be complex-memberedMEMBEREDV1\<bar>setHIDDENM2", "D2 be complex-memberedMEMBEREDV1\<bar>setHIDDENM2", "f1 be PartFuncPARTFUN1M1-of(C,D1)", "f2 be PartFuncPARTFUN1M1-of(C,D2)"
"cluster f1 -VALUED-1K47 f2 as-term-is PartFuncPARTFUN1M1-of(C,COMPLEXNUMBERSK3)"
proof
(*coherence*)
  show "f1 -VALUED-1K47 f2 be PartFuncPARTFUN1M1-of(C,COMPLEXNUMBERSK3)"
sorry
qed "sorry"

syntax VALUED_1K49 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ -VALUED-1K49\<^bsub>'( _ , _ , _ ')\<^esub>  _ " [132,0,0,0,132]132)
translations "f1 -VALUED-1K49\<^bsub>(C,D1,D2)\<^esub> f2" \<rightharpoonup> "f1 -VALUED-1K47 f2"

mtheorem valued_1_add_38:
  mlet "C be setHIDDENM2", "D1 be real-memberedMEMBEREDV3\<bar>setHIDDENM2", "D2 be real-memberedMEMBEREDV3\<bar>setHIDDENM2", "f1 be PartFuncPARTFUN1M1-of(C,D1)", "f2 be PartFuncPARTFUN1M1-of(C,D2)"
"cluster f1 -VALUED-1K47 f2 as-term-is PartFuncPARTFUN1M1-of(C,REALNUMBERSK2)"
proof
(*coherence*)
  show "f1 -VALUED-1K47 f2 be PartFuncPARTFUN1M1-of(C,REALNUMBERSK2)"
sorry
qed "sorry"

syntax VALUED_1K50 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ -VALUED-1K50\<^bsub>'( _ , _ , _ ')\<^esub>  _ " [132,0,0,0,132]132)
translations "f1 -VALUED-1K50\<^bsub>(C,D1,D2)\<^esub> f2" \<rightharpoonup> "f1 -VALUED-1K47 f2"

mtheorem valued_1_add_39:
  mlet "C be setHIDDENM2", "D1 be rational-memberedMEMBEREDV4\<bar>setHIDDENM2", "D2 be rational-memberedMEMBEREDV4\<bar>setHIDDENM2", "f1 be PartFuncPARTFUN1M1-of(C,D1)", "f2 be PartFuncPARTFUN1M1-of(C,D2)"
"cluster f1 -VALUED-1K47 f2 as-term-is PartFuncPARTFUN1M1-of(C,RATRAT-1K1)"
proof
(*coherence*)
  show "f1 -VALUED-1K47 f2 be PartFuncPARTFUN1M1-of(C,RATRAT-1K1)"
sorry
qed "sorry"

syntax VALUED_1K51 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ -VALUED-1K51\<^bsub>'( _ , _ , _ ')\<^esub>  _ " [132,0,0,0,132]132)
translations "f1 -VALUED-1K51\<^bsub>(C,D1,D2)\<^esub> f2" \<rightharpoonup> "f1 -VALUED-1K47 f2"

mtheorem valued_1_add_40:
  mlet "C be setHIDDENM2", "D1 be integer-memberedMEMBEREDV5\<bar>setHIDDENM2", "D2 be integer-memberedMEMBEREDV5\<bar>setHIDDENM2", "f1 be PartFuncPARTFUN1M1-of(C,D1)", "f2 be PartFuncPARTFUN1M1-of(C,D2)"
"cluster f1 -VALUED-1K47 f2 as-term-is PartFuncPARTFUN1M1-of(C,INTINT-1K1)"
proof
(*coherence*)
  show "f1 -VALUED-1K47 f2 be PartFuncPARTFUN1M1-of(C,INTINT-1K1)"
sorry
qed "sorry"

mlemma valued_1_lm_3:
" for C be setHIDDENM2 holds  for D1 be complex-memberedMEMBEREDV1\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D2 be complex-memberedMEMBEREDV1\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for f1 be FunctionFUNCT-2M1-of(C,D1) holds  for f2 be FunctionFUNCT-2M1-of(C,D2) holds domRELSET-1K1\<^bsub>(C)\<^esub> (f1 -VALUED-1K48\<^bsub>(C,D1,D2)\<^esub> f2) =XBOOLE-0R4 C"
sorry

mtheorem valued_1_cl_86:
  mlet "C be setHIDDENM2", "D1 be complex-memberedMEMBEREDV1\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2", "D2 be complex-memberedMEMBEREDV1\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2", "f1 be FunctionFUNCT-2M1-of(C,D1)", "f2 be FunctionFUNCT-2M1-of(C,D2)"
"cluster f1 -VALUED-1K48\<^bsub>(C,D1,D2)\<^esub> f2 as-term-is totalPARTFUN1V1\<^bsub>(C)\<^esub> for PartFuncPARTFUN1M1-of(C,COMPLEXNUMBERSK3)"
proof
(*coherence*)
  show " for it be PartFuncPARTFUN1M1-of(C,COMPLEXNUMBERSK3) holds it =HIDDENR1 f1 -VALUED-1K48\<^bsub>(C,D1,D2)\<^esub> f2 implies it be totalPARTFUN1V1\<^bsub>(C)\<^esub>"
    using valued_1_lm_3 partfun1_def_2 sorry
qed "sorry"

mtheorem valued_1_cl_87:
  mlet "C be setHIDDENM2", "D1 be real-memberedMEMBEREDV3\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2", "D2 be real-memberedMEMBEREDV3\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2", "f1 be FunctionFUNCT-2M1-of(C,D1)", "f2 be FunctionFUNCT-2M1-of(C,D2)"
"cluster f1 -VALUED-1K49\<^bsub>(C,D1,D2)\<^esub> f2 as-term-is totalPARTFUN1V1\<^bsub>(C)\<^esub> for PartFuncPARTFUN1M1-of(C,REALNUMBERSK2)"
proof
(*coherence*)
  show " for it be PartFuncPARTFUN1M1-of(C,REALNUMBERSK2) holds it =HIDDENR1 f1 -VALUED-1K49\<^bsub>(C,D1,D2)\<^esub> f2 implies it be totalPARTFUN1V1\<^bsub>(C)\<^esub>"
    using valued_1_lm_3 partfun1_def_2 sorry
qed "sorry"

mtheorem valued_1_cl_88:
  mlet "C be setHIDDENM2", "D1 be rational-memberedMEMBEREDV4\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2", "D2 be rational-memberedMEMBEREDV4\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2", "f1 be FunctionFUNCT-2M1-of(C,D1)", "f2 be FunctionFUNCT-2M1-of(C,D2)"
"cluster f1 -VALUED-1K50\<^bsub>(C,D1,D2)\<^esub> f2 as-term-is totalPARTFUN1V1\<^bsub>(C)\<^esub> for PartFuncPARTFUN1M1-of(C,RATRAT-1K1)"
proof
(*coherence*)
  show " for it be PartFuncPARTFUN1M1-of(C,RATRAT-1K1) holds it =HIDDENR1 f1 -VALUED-1K50\<^bsub>(C,D1,D2)\<^esub> f2 implies it be totalPARTFUN1V1\<^bsub>(C)\<^esub>"
    using valued_1_lm_3 partfun1_def_2 sorry
qed "sorry"

mtheorem valued_1_cl_89:
  mlet "C be setHIDDENM2", "D1 be integer-memberedMEMBEREDV5\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2", "D2 be integer-memberedMEMBEREDV5\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2", "f1 be FunctionFUNCT-2M1-of(C,D1)", "f2 be FunctionFUNCT-2M1-of(C,D2)"
"cluster f1 -VALUED-1K51\<^bsub>(C,D1,D2)\<^esub> f2 as-term-is totalPARTFUN1V1\<^bsub>(C)\<^esub> for PartFuncPARTFUN1M1-of(C,INTINT-1K1)"
proof
(*coherence*)
  show " for it be PartFuncPARTFUN1M1-of(C,INTINT-1K1) holds it =HIDDENR1 f1 -VALUED-1K51\<^bsub>(C,D1,D2)\<^esub> f2 implies it be totalPARTFUN1V1\<^bsub>(C)\<^esub>"
    using valued_1_lm_3 partfun1_def_2 sorry
qed "sorry"

mtheorem valued_1_th_15:
" for C be setHIDDENM2 holds  for D1 be complex-memberedMEMBEREDV1\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D2 be complex-memberedMEMBEREDV1\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for f1 be FunctionFUNCT-2M1-of(C,D1) holds  for f2 be FunctionFUNCT-2M1-of(C,D2) holds  for c be ElementSUBSET-1M1-of C holds (f1 -VALUED-1K48\<^bsub>(C,D1,D2)\<^esub> f2).FUNCT-1K1 c =XBOOLE-0R4 f1 .FUNCT-1K1 c -XCMPLX-0K6 f2 .FUNCT-1K1 c"
sorry

mtheorem valued_1_cl_90:
  mlet "f1 be complex-valuedVALUED-0V5\<bar>FinSequenceFINSEQ-1M1", "f2 be complex-valuedVALUED-0V5\<bar>FinSequenceFINSEQ-1M1"
"cluster f1 -VALUED-1K47 f2 as-term-is FinSequence-likeFINSEQ-1V1"
proof
(*coherence*)
  show "f1 -VALUED-1K47 f2 be FinSequence-likeFINSEQ-1V1"
     sorry
qed "sorry"

(*begin*)
mdef valued_1_def_10 (" _ '/\<inverse>VALUED-1K52  _ " [164,164]164 ) where
  mlet "f1 be complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1", "f2 be complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1"
"func f1 /\<inverse>VALUED-1K52 f2 \<rightarrow> FunctionFUNCT-1M1 equals
  f1 (#)VALUED-1K19 f2 \<inverse>VALUED-1K37"
proof-
  (*coherence*)
    show "f1 (#)VALUED-1K19 f2 \<inverse>VALUED-1K37 be FunctionFUNCT-1M1"
       sorry
qed "sorry"

mtheorem valued_1_th_16:
" for f1 be complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1 holds  for f2 be complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1 holds domRELAT-1K1 (f1 /\<inverse>VALUED-1K52 f2) =XBOOLE-0R4 domRELAT-1K1 f1 /\\XBOOLE-0K3 domRELAT-1K1 f2"
sorry

mtheorem valued_1_th_17:
" for f1 be complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1 holds  for f2 be complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1 holds  for c be objectHIDDENM1 holds (f1 /\<inverse>VALUED-1K52 f2).FUNCT-1K1 c =XBOOLE-0R4 f1 .FUNCT-1K1 c /XCMPLX-0K7 f2 .FUNCT-1K1 c"
sorry

mtheorem valued_1_cl_91:
  mlet "f1 be complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1", "f2 be complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1"
"cluster f1 /\<inverse>VALUED-1K52 f2 as-term-is complex-valuedVALUED-0V5"
proof
(*coherence*)
  show "f1 /\<inverse>VALUED-1K52 f2 be complex-valuedVALUED-0V5"
     sorry
qed "sorry"

mtheorem valued_1_cl_92:
  mlet "f1 be real-valuedVALUED-0V7\<bar>FunctionFUNCT-1M1", "f2 be real-valuedVALUED-0V7\<bar>FunctionFUNCT-1M1"
"cluster f1 /\<inverse>VALUED-1K52 f2 as-term-is real-valuedVALUED-0V7"
proof
(*coherence*)
  show "f1 /\<inverse>VALUED-1K52 f2 be real-valuedVALUED-0V7"
     sorry
qed "sorry"

mtheorem valued_1_cl_93:
  mlet "f1 be RATRAT-1K1 -valuedRELAT-1V5\<bar>FunctionFUNCT-1M1", "f2 be RATRAT-1K1 -valuedRELAT-1V5\<bar>FunctionFUNCT-1M1"
"cluster f1 /\<inverse>VALUED-1K52 f2 as-term-is RATRAT-1K1 -valuedRELAT-1V5"
proof
(*coherence*)
  show "f1 /\<inverse>VALUED-1K52 f2 be RATRAT-1K1 -valuedRELAT-1V5"
     sorry
qed "sorry"

syntax VALUED_1K53 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ '/\<inverse>VALUED-1K53\<^bsub>'( _ , _ , _ ')\<^esub>  _ " [164,0,0,0,164]164)
translations "f1 /\<inverse>VALUED-1K53\<^bsub>(C,D1,D2)\<^esub> f2" \<rightharpoonup> "f1 /\<inverse>VALUED-1K52 f2"

mtheorem valued_1_add_41:
  mlet "C be setHIDDENM2", "D1 be complex-memberedMEMBEREDV1\<bar>setHIDDENM2", "D2 be complex-memberedMEMBEREDV1\<bar>setHIDDENM2", "f1 be PartFuncPARTFUN1M1-of(C,D1)", "f2 be PartFuncPARTFUN1M1-of(C,D2)"
"cluster f1 /\<inverse>VALUED-1K52 f2 as-term-is PartFuncPARTFUN1M1-of(C,COMPLEXNUMBERSK3)"
proof
(*coherence*)
  show "f1 /\<inverse>VALUED-1K52 f2 be PartFuncPARTFUN1M1-of(C,COMPLEXNUMBERSK3)"
sorry
qed "sorry"

syntax VALUED_1K54 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ '/\<inverse>VALUED-1K54\<^bsub>'( _ , _ , _ ')\<^esub>  _ " [164,0,0,0,164]164)
translations "f1 /\<inverse>VALUED-1K54\<^bsub>(C,D1,D2)\<^esub> f2" \<rightharpoonup> "f1 /\<inverse>VALUED-1K52 f2"

mtheorem valued_1_add_42:
  mlet "C be setHIDDENM2", "D1 be real-memberedMEMBEREDV3\<bar>setHIDDENM2", "D2 be real-memberedMEMBEREDV3\<bar>setHIDDENM2", "f1 be PartFuncPARTFUN1M1-of(C,D1)", "f2 be PartFuncPARTFUN1M1-of(C,D2)"
"cluster f1 /\<inverse>VALUED-1K52 f2 as-term-is PartFuncPARTFUN1M1-of(C,REALNUMBERSK2)"
proof
(*coherence*)
  show "f1 /\<inverse>VALUED-1K52 f2 be PartFuncPARTFUN1M1-of(C,REALNUMBERSK2)"
sorry
qed "sorry"

syntax VALUED_1K55 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ '/\<inverse>VALUED-1K55\<^bsub>'( _ , _ , _ ')\<^esub>  _ " [164,0,0,0,164]164)
translations "f1 /\<inverse>VALUED-1K55\<^bsub>(C,D1,D2)\<^esub> f2" \<rightharpoonup> "f1 /\<inverse>VALUED-1K52 f2"

mtheorem valued_1_add_43:
  mlet "C be setHIDDENM2", "D1 be rational-memberedMEMBEREDV4\<bar>setHIDDENM2", "D2 be rational-memberedMEMBEREDV4\<bar>setHIDDENM2", "f1 be PartFuncPARTFUN1M1-of(C,D1)", "f2 be PartFuncPARTFUN1M1-of(C,D2)"
"cluster f1 /\<inverse>VALUED-1K52 f2 as-term-is PartFuncPARTFUN1M1-of(C,RATRAT-1K1)"
proof
(*coherence*)
  show "f1 /\<inverse>VALUED-1K52 f2 be PartFuncPARTFUN1M1-of(C,RATRAT-1K1)"
sorry
qed "sorry"

mlemma valued_1_lm_4:
" for C be setHIDDENM2 holds  for D1 be complex-memberedMEMBEREDV1\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D2 be complex-memberedMEMBEREDV1\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for f1 be FunctionFUNCT-2M1-of(C,D1) holds  for f2 be FunctionFUNCT-2M1-of(C,D2) holds domRELSET-1K1\<^bsub>(C)\<^esub> (f1 /\<inverse>VALUED-1K53\<^bsub>(C,D1,D2)\<^esub> f2) =XBOOLE-0R4 C"
sorry

mtheorem valued_1_cl_94:
  mlet "C be setHIDDENM2", "D1 be complex-memberedMEMBEREDV1\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2", "D2 be complex-memberedMEMBEREDV1\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2", "f1 be FunctionFUNCT-2M1-of(C,D1)", "f2 be FunctionFUNCT-2M1-of(C,D2)"
"cluster f1 /\<inverse>VALUED-1K53\<^bsub>(C,D1,D2)\<^esub> f2 as-term-is totalPARTFUN1V1\<^bsub>(C)\<^esub> for PartFuncPARTFUN1M1-of(C,COMPLEXNUMBERSK3)"
proof
(*coherence*)
  show " for it be PartFuncPARTFUN1M1-of(C,COMPLEXNUMBERSK3) holds it =HIDDENR1 f1 /\<inverse>VALUED-1K53\<^bsub>(C,D1,D2)\<^esub> f2 implies it be totalPARTFUN1V1\<^bsub>(C)\<^esub>"
    using valued_1_lm_4 partfun1_def_2 sorry
qed "sorry"

mtheorem valued_1_cl_95:
  mlet "C be setHIDDENM2", "D1 be real-memberedMEMBEREDV3\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2", "D2 be real-memberedMEMBEREDV3\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2", "f1 be FunctionFUNCT-2M1-of(C,D1)", "f2 be FunctionFUNCT-2M1-of(C,D2)"
"cluster f1 /\<inverse>VALUED-1K54\<^bsub>(C,D1,D2)\<^esub> f2 as-term-is totalPARTFUN1V1\<^bsub>(C)\<^esub> for PartFuncPARTFUN1M1-of(C,REALNUMBERSK2)"
proof
(*coherence*)
  show " for it be PartFuncPARTFUN1M1-of(C,REALNUMBERSK2) holds it =HIDDENR1 f1 /\<inverse>VALUED-1K54\<^bsub>(C,D1,D2)\<^esub> f2 implies it be totalPARTFUN1V1\<^bsub>(C)\<^esub>"
    using valued_1_lm_4 partfun1_def_2 sorry
qed "sorry"

mtheorem valued_1_cl_96:
  mlet "C be setHIDDENM2", "D1 be rational-memberedMEMBEREDV4\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2", "D2 be rational-memberedMEMBEREDV4\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2", "f1 be FunctionFUNCT-2M1-of(C,D1)", "f2 be FunctionFUNCT-2M1-of(C,D2)"
"cluster f1 /\<inverse>VALUED-1K55\<^bsub>(C,D1,D2)\<^esub> f2 as-term-is totalPARTFUN1V1\<^bsub>(C)\<^esub> for PartFuncPARTFUN1M1-of(C,RATRAT-1K1)"
proof
(*coherence*)
  show " for it be PartFuncPARTFUN1M1-of(C,RATRAT-1K1) holds it =HIDDENR1 f1 /\<inverse>VALUED-1K55\<^bsub>(C,D1,D2)\<^esub> f2 implies it be totalPARTFUN1V1\<^bsub>(C)\<^esub>"
    using valued_1_lm_4 partfun1_def_2 sorry
qed "sorry"

mtheorem valued_1_cl_97:
  mlet "f1 be complex-valuedVALUED-0V5\<bar>FinSequenceFINSEQ-1M1", "f2 be complex-valuedVALUED-0V5\<bar>FinSequenceFINSEQ-1M1"
"cluster f1 /\<inverse>VALUED-1K52 f2 as-term-is FinSequence-likeFINSEQ-1V1"
proof
(*coherence*)
  show "f1 /\<inverse>VALUED-1K52 f2 be FinSequence-likeFINSEQ-1V1"
     sorry
qed "sorry"

(*begin*)
mdef valued_1_def_11 ("|.VALUED-1K56  _ .|" [0]164 ) where
  mlet "f be complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1"
"func |.VALUED-1K56 f.| \<rightarrow> real-valuedVALUED-0V7\<bar>FunctionFUNCT-1M1 means
  \<lambda>it. domRELAT-1K1 it =XBOOLE-0R4 domRELAT-1K1 f & ( for c be objectHIDDENM1 holds c inHIDDENR3 domRELAT-1K1 it implies it .FUNCT-1K1 c =COMPLEX1R1 |.COMPLEX1K10 f .FUNCT-1K1 c.|)"
proof-
  (*existence*)
    show " ex it be real-valuedVALUED-0V7\<bar>FunctionFUNCT-1M1 st domRELAT-1K1 it =XBOOLE-0R4 domRELAT-1K1 f & ( for c be objectHIDDENM1 holds c inHIDDENR3 domRELAT-1K1 it implies it .FUNCT-1K1 c =COMPLEX1R1 |.COMPLEX1K10 f .FUNCT-1K1 c.|)"
sorry
  (*uniqueness*)
    show " for it1 be real-valuedVALUED-0V7\<bar>FunctionFUNCT-1M1 holds  for it2 be real-valuedVALUED-0V7\<bar>FunctionFUNCT-1M1 holds (domRELAT-1K1 it1 =XBOOLE-0R4 domRELAT-1K1 f & ( for c be objectHIDDENM1 holds c inHIDDENR3 domRELAT-1K1 it1 implies it1 .FUNCT-1K1 c =COMPLEX1R1 |.COMPLEX1K10 f .FUNCT-1K1 c.|)) & (domRELAT-1K1 it2 =XBOOLE-0R4 domRELAT-1K1 f & ( for c be objectHIDDENM1 holds c inHIDDENR3 domRELAT-1K1 it2 implies it2 .FUNCT-1K1 c =COMPLEX1R1 |.COMPLEX1K10 f .FUNCT-1K1 c.|)) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mtheorem VALUED_1K56_projectivity:
" for f be complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1 holds |.VALUED-1K56 |.VALUED-1K56 f.| .| =HIDDENR1 |.VALUED-1K56 f.|"
sorry

abbreviation(input) VALUED_1K57("absVALUED-1K57  _ " [250]250) where
  "absVALUED-1K57 f \<equiv> |.VALUED-1K56 f.|"

mtheorem valued_1_th_18:
" for f be complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1 holds  for c be objectHIDDENM1 holds (|.VALUED-1K56 f.|).FUNCT-1K1 c =COMPLEX1R1 |.COMPLEX1K10 f .FUNCT-1K1 c.|"
sorry

mtheorem valued_1_cl_98:
  mlet "f be RATRAT-1K1 -valuedRELAT-1V5\<bar>FunctionFUNCT-1M1"
"cluster |.VALUED-1K56 f.| as-term-is RATRAT-1K1 -valuedRELAT-1V5"
proof
(*coherence*)
  show "|.VALUED-1K56 f.| be RATRAT-1K1 -valuedRELAT-1V5"
sorry
qed "sorry"

mtheorem valued_1_cl_99:
  mlet "f be INTINT-1K1 -valuedRELAT-1V5\<bar>FunctionFUNCT-1M1"
"cluster |.VALUED-1K56 f.| as-term-is natural-valuedVALUED-0V8"
proof
(*coherence*)
  show "|.VALUED-1K56 f.| be natural-valuedVALUED-0V8"
sorry
qed "sorry"

syntax VALUED_1K58 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" ("|.VALUED-1K58\<^bsub>'( _ , _ ')\<^esub>  _ .|" [0,0,0]164)
translations "|.VALUED-1K58\<^bsub>(C,D)\<^esub> f.|" \<rightharpoonup> "|.VALUED-1K56 f.|"

mtheorem valued_1_add_44:
  mlet "C be setHIDDENM2", "D be complex-memberedMEMBEREDV1\<bar>setHIDDENM2", "f be PartFuncPARTFUN1M1-of(C,D)"
"cluster |.VALUED-1K56 f.| as-term-is PartFuncPARTFUN1M1-of(C,REALNUMBERSK2)"
proof
(*coherence*)
  show "|.VALUED-1K56 f.| be PartFuncPARTFUN1M1-of(C,REALNUMBERSK2)"
sorry
qed "sorry"

syntax VALUED_1K59 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" ("absVALUED-1K59\<^bsub>'( _ , _ ')\<^esub>  _ " [0,0,250]250)
translations "absVALUED-1K59\<^bsub>(C,D)\<^esub> f" \<rightharpoonup> "|.VALUED-1K56 f.|"

mtheorem valued_1_add_45:
  mlet "C be setHIDDENM2", "D be complex-memberedMEMBEREDV1\<bar>setHIDDENM2", "f be PartFuncPARTFUN1M1-of(C,D)"
"cluster |.VALUED-1K56 f.| as-term-is PartFuncPARTFUN1M1-of(C,REALNUMBERSK2)"
proof
(*coherence*)
  show "|.VALUED-1K56 f.| be PartFuncPARTFUN1M1-of(C,REALNUMBERSK2)"
sorry
qed "sorry"

syntax VALUED_1K60 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" ("|.VALUED-1K60\<^bsub>'( _ , _ ')\<^esub>  _ .|" [0,0,0]164)
translations "|.VALUED-1K60\<^bsub>(C,D)\<^esub> f.|" \<rightharpoonup> "|.VALUED-1K56 f.|"

mtheorem valued_1_add_46:
  mlet "C be setHIDDENM2", "D be rational-memberedMEMBEREDV4\<bar>setHIDDENM2", "f be PartFuncPARTFUN1M1-of(C,D)"
"cluster |.VALUED-1K56 f.| as-term-is PartFuncPARTFUN1M1-of(C,RATRAT-1K1)"
proof
(*coherence*)
  show "|.VALUED-1K56 f.| be PartFuncPARTFUN1M1-of(C,RATRAT-1K1)"
sorry
qed "sorry"

syntax VALUED_1K61 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" ("absVALUED-1K61\<^bsub>'( _ , _ ')\<^esub>  _ " [0,0,250]250)
translations "absVALUED-1K61\<^bsub>(C,D)\<^esub> f" \<rightharpoonup> "|.VALUED-1K56 f.|"

mtheorem valued_1_add_47:
  mlet "C be setHIDDENM2", "D be rational-memberedMEMBEREDV4\<bar>setHIDDENM2", "f be PartFuncPARTFUN1M1-of(C,D)"
"cluster |.VALUED-1K56 f.| as-term-is PartFuncPARTFUN1M1-of(C,RATRAT-1K1)"
proof
(*coherence*)
  show "|.VALUED-1K56 f.| be PartFuncPARTFUN1M1-of(C,RATRAT-1K1)"
sorry
qed "sorry"

syntax VALUED_1K62 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" ("|.VALUED-1K62\<^bsub>'( _ , _ ')\<^esub>  _ .|" [0,0,0]164)
translations "|.VALUED-1K62\<^bsub>(C,D)\<^esub> f.|" \<rightharpoonup> "|.VALUED-1K56 f.|"

mtheorem valued_1_add_48:
  mlet "C be setHIDDENM2", "D be integer-memberedMEMBEREDV5\<bar>setHIDDENM2", "f be PartFuncPARTFUN1M1-of(C,D)"
"cluster |.VALUED-1K56 f.| as-term-is PartFuncPARTFUN1M1-of(C,NATNUMBERSK1)"
proof
(*coherence*)
  show "|.VALUED-1K56 f.| be PartFuncPARTFUN1M1-of(C,NATNUMBERSK1)"
sorry
qed "sorry"

syntax VALUED_1K63 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" ("absVALUED-1K63\<^bsub>'( _ , _ ')\<^esub>  _ " [0,0,250]250)
translations "absVALUED-1K63\<^bsub>(C,D)\<^esub> f" \<rightharpoonup> "|.VALUED-1K56 f.|"

mtheorem valued_1_add_49:
  mlet "C be setHIDDENM2", "D be integer-memberedMEMBEREDV5\<bar>setHIDDENM2", "f be PartFuncPARTFUN1M1-of(C,D)"
"cluster |.VALUED-1K56 f.| as-term-is PartFuncPARTFUN1M1-of(C,NATNUMBERSK1)"
proof
(*coherence*)
  show "|.VALUED-1K56 f.| be PartFuncPARTFUN1M1-of(C,NATNUMBERSK1)"
sorry
qed "sorry"

mtheorem valued_1_cl_100:
  mlet "C be setHIDDENM2", "D be complex-memberedMEMBEREDV1\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2", "f be FunctionFUNCT-2M1-of(C,D)"
"cluster |.VALUED-1K58\<^bsub>(C,D)\<^esub> f.| as-term-is totalPARTFUN1V1\<^bsub>(C)\<^esub> for PartFuncPARTFUN1M1-of(C,REALNUMBERSK2)"
proof
(*coherence*)
  show " for it be PartFuncPARTFUN1M1-of(C,REALNUMBERSK2) holds it =HIDDENR1 |.VALUED-1K58\<^bsub>(C,D)\<^esub> f.| implies it be totalPARTFUN1V1\<^bsub>(C)\<^esub>"
sorry
qed "sorry"

mtheorem valued_1_cl_101:
  mlet "C be setHIDDENM2", "D be rational-memberedMEMBEREDV4\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2", "f be FunctionFUNCT-2M1-of(C,D)"
"cluster |.VALUED-1K60\<^bsub>(C,D)\<^esub> f.| as-term-is totalPARTFUN1V1\<^bsub>(C)\<^esub> for PartFuncPARTFUN1M1-of(C,RATRAT-1K1)"
proof
(*coherence*)
  show " for it be PartFuncPARTFUN1M1-of(C,RATRAT-1K1) holds it =HIDDENR1 |.VALUED-1K60\<^bsub>(C,D)\<^esub> f.| implies it be totalPARTFUN1V1\<^bsub>(C)\<^esub>"
sorry
qed "sorry"

mtheorem valued_1_cl_102:
  mlet "C be setHIDDENM2", "D be integer-memberedMEMBEREDV5\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2", "f be FunctionFUNCT-2M1-of(C,D)"
"cluster |.VALUED-1K62\<^bsub>(C,D)\<^esub> f.| as-term-is totalPARTFUN1V1\<^bsub>(C)\<^esub> for PartFuncPARTFUN1M1-of(C,NATNUMBERSK1)"
proof
(*coherence*)
  show " for it be PartFuncPARTFUN1M1-of(C,NATNUMBERSK1) holds it =HIDDENR1 |.VALUED-1K62\<^bsub>(C,D)\<^esub> f.| implies it be totalPARTFUN1V1\<^bsub>(C)\<^esub>"
sorry
qed "sorry"

mtheorem valued_1_cl_103:
  mlet "f be complex-valuedVALUED-0V5\<bar>FinSequenceFINSEQ-1M1"
"cluster |.VALUED-1K56 f.| as-term-is FinSequence-likeFINSEQ-1V1"
proof
(*coherence*)
  show "|.VALUED-1K56 f.| be FinSequence-likeFINSEQ-1V1"
sorry
qed "sorry"

mtheorem valued_1_th_19:
" for f be FinSequenceFINSEQ-1M1 holds  for g be FinSequenceFINSEQ-1M1 holds  for h be FunctionFUNCT-1M1 holds domRELAT-1K1 h =XBOOLE-0R4 domFINSEQ-1K5 f /\\SUBSET-1K9\<^bsub>(omegaORDINAL1K4)\<^esub> domFINSEQ-1K5 g implies h be FinSequenceFINSEQ-1M1"
  using valued_1_lm_2 sorry

(*begin*)
reserve m, j, p, q, n, l for "ElementSUBSET-1M1-of NATNUMBERSK1"
mdef valued_1_def_12 ("ShiftVALUED-1K64'( _ , _ ')" [0,0]164 ) where
  mlet "p be FunctionFUNCT-1M1", "k be NatNAT-1M1"
"func ShiftVALUED-1K64(p,k) \<rightarrow> FunctionFUNCT-1M1 means
  \<lambda>it. domRELAT-1K1 it =XBOOLE-0R4 {m +XCMPLX-0K2 k where m be NatNAT-1M1 : m inTARSKIR2 domRELAT-1K1 p } & ( for m be NatNAT-1M1 holds m inTARSKIR2 domRELAT-1K1 p implies it .FUNCT-1K1 (m +XCMPLX-0K2 k) =XBOOLE-0R4 p .FUNCT-1K1 m)"
proof-
  (*existence*)
    show " ex it be FunctionFUNCT-1M1 st domRELAT-1K1 it =XBOOLE-0R4 {m +XCMPLX-0K2 k where m be NatNAT-1M1 : m inTARSKIR2 domRELAT-1K1 p } & ( for m be NatNAT-1M1 holds m inTARSKIR2 domRELAT-1K1 p implies it .FUNCT-1K1 (m +XCMPLX-0K2 k) =XBOOLE-0R4 p .FUNCT-1K1 m)"
sorry
  (*uniqueness*)
    show " for it1 be FunctionFUNCT-1M1 holds  for it2 be FunctionFUNCT-1M1 holds (domRELAT-1K1 it1 =XBOOLE-0R4 {m +XCMPLX-0K2 k where m be NatNAT-1M1 : m inTARSKIR2 domRELAT-1K1 p } & ( for m be NatNAT-1M1 holds m inTARSKIR2 domRELAT-1K1 p implies it1 .FUNCT-1K1 (m +XCMPLX-0K2 k) =XBOOLE-0R4 p .FUNCT-1K1 m)) & (domRELAT-1K1 it2 =XBOOLE-0R4 {m +XCMPLX-0K2 k where m be NatNAT-1M1 : m inTARSKIR2 domRELAT-1K1 p } & ( for m be NatNAT-1M1 holds m inTARSKIR2 domRELAT-1K1 p implies it2 .FUNCT-1K1 (m +XCMPLX-0K2 k) =XBOOLE-0R4 p .FUNCT-1K1 m)) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mtheorem valued_1_cl_104:
  mlet "p be FunctionFUNCT-1M1", "k be NatNAT-1M1"
"cluster ShiftVALUED-1K64(p,k) as-term-is NATNUMBERSK1 -definedRELAT-1V4"
proof
(*coherence*)
  show "ShiftVALUED-1K64(p,k) be NATNUMBERSK1 -definedRELAT-1V4"
sorry
qed "sorry"

mtheorem valued_1_th_20:
" for P be FunctionFUNCT-1M1 holds  for Q be FunctionFUNCT-1M1 holds  for k be NatNAT-1M1 holds P c=RELAT-1R2 Q implies ShiftVALUED-1K64(P,k) c=RELAT-1R2 ShiftVALUED-1K64(Q,k)"
sorry

mtheorem valued_1_th_21:
" for n be NatNAT-1M1 holds  for m be NatNAT-1M1 holds  for I be FunctionFUNCT-1M1 holds ShiftVALUED-1K64(ShiftVALUED-1K64(I,m),n) =FUNCT-1R1 ShiftVALUED-1K64(I,m +XCMPLX-0K2 n)"
sorry

mtheorem valued_1_th_22:
" for s be FunctionFUNCT-1M1 holds  for f be FunctionFUNCT-1M1 holds  for n be NatNAT-1M1 holds ShiftVALUED-1K64(f *FUNCT-1K3 s,n) =FUNCT-1R1 f *FUNCT-1K3 (ShiftVALUED-1K64(s,n))"
sorry

mtheorem valued_1_th_23:
" for I be FunctionFUNCT-1M1 holds  for J be FunctionFUNCT-1M1 holds  for n be NatNAT-1M1 holds ShiftVALUED-1K64(I +*FUNCT-4K1 J,n) =FUNCT-1R1 (ShiftVALUED-1K64(I,n))+*FUNCT-4K1 (ShiftVALUED-1K64(J,n))"
sorry

mtheorem valued_1_th_24:
" for p be FunctionFUNCT-1M1 holds  for k be NatNAT-1M1 holds  for il be NatNAT-1M1 holds il inTARSKIR2 domRELAT-1K1 p implies il +XCMPLX-0K2 k inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> (ShiftVALUED-1K64(p,k))"
sorry

mtheorem valued_1_th_25:
" for p be FunctionFUNCT-1M1 holds  for k be NatNAT-1M1 holds rngFUNCT-1K2 (ShiftVALUED-1K64(p,k)) c=TARSKIR1 rngFUNCT-1K2 p"
sorry

mtheorem valued_1_th_26:
" for p be FunctionFUNCT-1M1 holds domRELAT-1K1 p c=TARSKIR1 NATNUMBERSK1 implies ( for k be NatNAT-1M1 holds rngFUNCT-1K2 (ShiftVALUED-1K64(p,k)) =XBOOLE-0R4 rngFUNCT-1K2 p)"
sorry

mtheorem valued_1_cl_105:
  mlet "p be finiteFINSET-1V1\<bar>FunctionFUNCT-1M1", "k be NatNAT-1M1"
"cluster ShiftVALUED-1K64(p,k) as-term-is finiteFINSET-1V1"
proof
(*coherence*)
  show "ShiftVALUED-1K64(p,k) be finiteFINSET-1V1"
sorry
qed "sorry"

reserve e1, e2 for "ExtRealXXREAL-0M1"
syntax VALUED_1V1 :: " Set \<Rightarrow> Ty" ("increasingVALUED-1V1\<^bsub>'( _ ')\<^esub>" [0]70)
translations "increasingVALUED-1V1\<^bsub>(X)\<^esub>" \<rightharpoonup> "increasingVALUED-0V9"

mtheorem valued_1_def_13:
  mlet "X be  non emptyXBOOLE-0V1\<bar>ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2", "s be sequenceNAT-1M2-of X"
"redefine attr increasingVALUED-1V1\<^bsub>(X)\<^esub> for sequenceNAT-1M2-of X means
  (\<lambda>s.  for n be NatNAT-1M1 holds s .NAT-1K8\<^bsub>(X)\<^esub> n <XXREAL-0R3 s .NAT-1K8\<^bsub>(X)\<^esub> (n +NAT-1K1 \<one>\<^sub>M))"
proof
(*compatibility*)
  show " for s be sequenceNAT-1M2-of X holds s be increasingVALUED-1V1\<^bsub>(X)\<^esub> iff ( for n be NatNAT-1M1 holds s .NAT-1K8\<^bsub>(X)\<^esub> n <XXREAL-0R3 s .NAT-1K8\<^bsub>(X)\<^esub> (n +NAT-1K1 \<one>\<^sub>M))"
sorry
qed "sorry"

syntax VALUED_1V2 :: " Set \<Rightarrow> Ty" ("decreasingVALUED-1V2\<^bsub>'( _ ')\<^esub>" [0]70)
translations "decreasingVALUED-1V2\<^bsub>(X)\<^esub>" \<rightharpoonup> "decreasingVALUED-0V10"

mtheorem valued_1_def_14:
  mlet "X be  non emptyXBOOLE-0V1\<bar>ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2", "s be sequenceNAT-1M2-of X"
"redefine attr decreasingVALUED-1V2\<^bsub>(X)\<^esub> for sequenceNAT-1M2-of X means
  (\<lambda>s.  for n be NatNAT-1M1 holds s .NAT-1K8\<^bsub>(X)\<^esub> n >XXREAL-0R4 s .NAT-1K8\<^bsub>(X)\<^esub> (n +NAT-1K1 \<one>\<^sub>M))"
proof
(*compatibility*)
  show " for s be sequenceNAT-1M2-of X holds s be decreasingVALUED-1V2\<^bsub>(X)\<^esub> iff ( for n be NatNAT-1M1 holds s .NAT-1K8\<^bsub>(X)\<^esub> n >XXREAL-0R4 s .NAT-1K8\<^bsub>(X)\<^esub> (n +NAT-1K1 \<one>\<^sub>M))"
sorry
qed "sorry"

syntax VALUED_1V3 :: " Set \<Rightarrow> Ty" ("non-decreasingVALUED-1V3\<^bsub>'( _ ')\<^esub>" [0]70)
translations "non-decreasingVALUED-1V3\<^bsub>(X)\<^esub>" \<rightharpoonup> "non-decreasingVALUED-0V11"

mtheorem valued_1_def_15:
  mlet "X be  non emptyXBOOLE-0V1\<bar>ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2", "s be sequenceNAT-1M2-of X"
"redefine attr non-decreasingVALUED-1V3\<^bsub>(X)\<^esub> for sequenceNAT-1M2-of X means
  (\<lambda>s.  for n be NatNAT-1M1 holds s .NAT-1K8\<^bsub>(X)\<^esub> n <=XXREAL-0R1 s .NAT-1K8\<^bsub>(X)\<^esub> (n +NAT-1K1 \<one>\<^sub>M))"
proof
(*compatibility*)
  show " for s be sequenceNAT-1M2-of X holds s be non-decreasingVALUED-1V3\<^bsub>(X)\<^esub> iff ( for n be NatNAT-1M1 holds s .NAT-1K8\<^bsub>(X)\<^esub> n <=XXREAL-0R1 s .NAT-1K8\<^bsub>(X)\<^esub> (n +NAT-1K1 \<one>\<^sub>M))"
sorry
qed "sorry"

syntax VALUED_1V4 :: " Set \<Rightarrow> Ty" ("non-increasingVALUED-1V4\<^bsub>'( _ ')\<^esub>" [0]70)
translations "non-increasingVALUED-1V4\<^bsub>(X)\<^esub>" \<rightharpoonup> "non-increasingVALUED-0V12"

mtheorem valued_1_def_16:
  mlet "X be  non emptyXBOOLE-0V1\<bar>ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2", "s be sequenceNAT-1M2-of X"
"redefine attr non-increasingVALUED-1V4\<^bsub>(X)\<^esub> for sequenceNAT-1M2-of X means
  (\<lambda>s.  for n be NatNAT-1M1 holds s .NAT-1K8\<^bsub>(X)\<^esub> n >=XXREAL-0R2 s .NAT-1K8\<^bsub>(X)\<^esub> (n +NAT-1K1 \<one>\<^sub>M))"
proof
(*compatibility*)
  show " for s be sequenceNAT-1M2-of X holds s be non-increasingVALUED-1V4\<^bsub>(X)\<^esub> iff ( for n be NatNAT-1M1 holds s .NAT-1K8\<^bsub>(X)\<^esub> n >=XXREAL-0R2 s .NAT-1K8\<^bsub>(X)\<^esub> (n +NAT-1K1 \<one>\<^sub>M))"
sorry
qed "sorry"

theorem valued_1_sch_1:
  fixes Xf0 Sf0 Pp1 
  assumes
[ty]: "Xf0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
  [ty]: "Sf0 be sequenceNAT-1M2-of Xf0" and
   A1: " for n be ElementSUBSET-1M1-of NATNUMBERSK1 holds  ex m be ElementSUBSET-1M1-of NATNUMBERSK1 st n <=XXREAL-0R1 m & Pp1(Sf0 .NAT-1K8\<^bsub>(Xf0)\<^esub> m)"
  shows " ex S1 be subsequenceVALUED-0M2\<^bsub>(Xf0)\<^esub>-of Sf0 st  for n be ElementSUBSET-1M1-of NATNUMBERSK1 holds Pp1(S1 .NAT-1K8\<^bsub>(Xf0)\<^esub> n)"
sorry

mtheorem valued_1_th_27:
" for k be NatNAT-1M1 holds  for F be NATNUMBERSK1 -definedRELAT-1V4\<bar>FunctionFUNCT-1M1 holds (domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> F,domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> (ShiftVALUED-1K64(F,k)))are-equipotentTARSKIR3"
sorry

mtheorem valued_1_reduce_1:
  mlet "F be NATNUMBERSK1 -definedRELAT-1V4\<bar>FunctionFUNCT-1M1"
"reduce ShiftVALUED-1K64(F,0NUMBERSK6) to F"
proof
(*reducibility*)
  show "ShiftVALUED-1K64(F,0NUMBERSK6) =HIDDENR1 F"
sorry
qed "sorry"

mtheorem valued_1_cl_106:
  mlet "X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "F be X -valuedRELAT-1V5\<bar>FunctionFUNCT-1M1", "k be NatNAT-1M1"
"cluster ShiftVALUED-1K64(F,k) as-term-is X -valuedRELAT-1V5"
proof
(*coherence*)
  show "ShiftVALUED-1K64(F,k) be X -valuedRELAT-1V5"
sorry
qed "sorry"

mtheorem valued_1_cl_107:
"cluster  non emptyXBOOLE-0V1\<bar>NATNUMBERSK1 -definedRELAT-1V4 for FunctionFUNCT-1M1"
proof
(*existence*)
  show " ex it be FunctionFUNCT-1M1 st it be  non emptyXBOOLE-0V1\<bar>NATNUMBERSK1 -definedRELAT-1V4"
sorry
qed "sorry"

mtheorem valued_1_cl_108:
  mlet "F be emptyXBOOLE-0V1\<bar>FunctionFUNCT-1M1", "k be NatNAT-1M1"
"cluster ShiftVALUED-1K64(F,k) as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "ShiftVALUED-1K64(F,k) be emptyXBOOLE-0V1"
sorry
qed "sorry"

mtheorem valued_1_cl_109:
  mlet "F be  non emptyXBOOLE-0V1\<bar>NATNUMBERSK1 -definedRELAT-1V4\<bar>FunctionFUNCT-1M1", "k be NatNAT-1M1"
"cluster ShiftVALUED-1K64(F,k) as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "ShiftVALUED-1K64(F,k) be  non emptyXBOOLE-0V1"
sorry
qed "sorry"

(*\$CT*)
mtheorem valued_1_th_29:
" for F be FunctionFUNCT-1M1 holds  for k be NatNAT-1M1 holds k >XXREAL-0R4 0NUMBERSK6 implies  not 0NUMBERSK6 inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> (ShiftVALUED-1K64(F,k))"
sorry

mtheorem valued_1_cl_110:
"cluster NATNUMBERSK1 -definedRELAT-1V4\<bar>finiteFINSET-1V1\<bar> non emptyXBOOLE-0V1 for FunctionFUNCT-1M1"
proof
(*existence*)
  show " ex it be FunctionFUNCT-1M1 st it be NATNUMBERSK1 -definedRELAT-1V4\<bar>finiteFINSET-1V1\<bar> non emptyXBOOLE-0V1"
sorry
qed "sorry"

mtheorem valued_1_cl_111:
  mlet "F be NATNUMBERSK1 -definedRELAT-1V4\<bar>RelationRELAT-1M1"
"cluster domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> F as-term-is natural-memberedMEMBEREDV6"
proof
(*coherence*)
  show "domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> F be natural-memberedMEMBEREDV6"
     sorry
qed "sorry"

mdef valued_1_def_17 ("LastLocVALUED-1K65  _ " [164]164 ) where
  mlet "F be  non emptyXBOOLE-0V1\<bar>NATNUMBERSK1 -definedRELAT-1V4\<bar>finiteFINSET-1V1\<bar>FunctionFUNCT-1M1"
"func LastLocVALUED-1K65 F \<rightarrow> ElementSUBSET-1M1-of NATNUMBERSK1 equals
  maxXXREAL-2K6 (domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> F)"
proof-
  (*coherence*)
    show "maxXXREAL-2K6 (domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> F) be ElementSUBSET-1M1-of NATNUMBERSK1"
      using ordinal1_def_12 sorry
qed "sorry"

mdef valued_1_def_18 ("CutLastLocVALUED-1K66  _ " [164]164 ) where
  mlet "F be  non emptyXBOOLE-0V1\<bar>NATNUMBERSK1 -definedRELAT-1V4\<bar>finiteFINSET-1V1\<bar>FunctionFUNCT-1M1"
"func CutLastLocVALUED-1K66 F \<rightarrow> FunctionFUNCT-1M1 equals
  F \\SUBSET-1K6 (LastLocVALUED-1K65 F).-->FUNCOP-1K17 F .FUNCT-1K1 (LastLocVALUED-1K65 F)"
proof-
  (*coherence*)
    show "F \\SUBSET-1K6 (LastLocVALUED-1K65 F).-->FUNCOP-1K17 F .FUNCT-1K1 (LastLocVALUED-1K65 F) be FunctionFUNCT-1M1"
       sorry
qed "sorry"

mtheorem valued_1_cl_112:
  mlet "F be  non emptyXBOOLE-0V1\<bar>NATNUMBERSK1 -definedRELAT-1V4\<bar>finiteFINSET-1V1\<bar>FunctionFUNCT-1M1"
"cluster CutLastLocVALUED-1K66 F as-term-is NATNUMBERSK1 -definedRELAT-1V4\<bar>finiteFINSET-1V1"
proof
(*coherence*)
  show "CutLastLocVALUED-1K66 F be NATNUMBERSK1 -definedRELAT-1V4\<bar>finiteFINSET-1V1"
     sorry
qed "sorry"

mtheorem valued_1_th_30:
" for F be  non emptyXBOOLE-0V1\<bar>NATNUMBERSK1 -definedRELAT-1V4\<bar>finiteFINSET-1V1\<bar>FunctionFUNCT-1M1 holds LastLocVALUED-1K65 F inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> F"
  using xxreal_2_def_8 sorry

mtheorem valued_1_th_31:
" for F be  non emptyXBOOLE-0V1\<bar>NATNUMBERSK1 -definedRELAT-1V4\<bar>finiteFINSET-1V1\<bar>FunctionFUNCT-1M1 holds  for G be  non emptyXBOOLE-0V1\<bar>NATNUMBERSK1 -definedRELAT-1V4\<bar>finiteFINSET-1V1\<bar>FunctionFUNCT-1M1 holds F c=RELAT-1R2 G implies LastLocVALUED-1K65 F <=XXREAL-0R1 LastLocVALUED-1K65 G"
  using relat_1_th_11 xxreal_2_th_59 sorry

mtheorem valued_1_th_32:
" for F be  non emptyXBOOLE-0V1\<bar>NATNUMBERSK1 -definedRELAT-1V4\<bar>finiteFINSET-1V1\<bar>FunctionFUNCT-1M1 holds  for l be ElementSUBSET-1M1-of NATNUMBERSK1 holds l inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> F implies l <=XXREAL-0R1 LastLocVALUED-1K65 F"
  using xxreal_2_def_8 sorry

mdef valued_1_def_19 ("FirstLocVALUED-1K67  _ " [164]164 ) where
  mlet "F be  non emptyXBOOLE-0V1\<bar>NATNUMBERSK1 -definedRELAT-1V4\<bar>FunctionFUNCT-1M1"
"func FirstLocVALUED-1K67 F \<rightarrow> ElementSUBSET-1M1-of NATNUMBERSK1 equals
  minXXREAL-2K5 (domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> F)"
proof-
  (*coherence*)
    show "minXXREAL-2K5 (domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> F) be ElementSUBSET-1M1-of NATNUMBERSK1"
      using ordinal1_def_12 sorry
qed "sorry"

mtheorem valued_1_th_33:
" for F be  non emptyXBOOLE-0V1\<bar>NATNUMBERSK1 -definedRELAT-1V4\<bar>finiteFINSET-1V1\<bar>FunctionFUNCT-1M1 holds FirstLocVALUED-1K67 F inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> F"
  using xxreal_2_def_7 sorry

mtheorem valued_1_th_34:
" for F be  non emptyXBOOLE-0V1\<bar>NATNUMBERSK1 -definedRELAT-1V4\<bar>finiteFINSET-1V1\<bar>FunctionFUNCT-1M1 holds  for G be  non emptyXBOOLE-0V1\<bar>NATNUMBERSK1 -definedRELAT-1V4\<bar>finiteFINSET-1V1\<bar>FunctionFUNCT-1M1 holds F c=RELAT-1R2 G implies FirstLocVALUED-1K67 G <=XXREAL-0R1 FirstLocVALUED-1K67 F"
  using relat_1_th_11 xxreal_2_th_60 sorry

mtheorem valued_1_th_35:
" for l1 be ElementSUBSET-1M1-of NATNUMBERSK1 holds  for F be  non emptyXBOOLE-0V1\<bar>NATNUMBERSK1 -definedRELAT-1V4\<bar>finiteFINSET-1V1\<bar>FunctionFUNCT-1M1 holds l1 inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> F implies FirstLocVALUED-1K67 F <=XXREAL-0R1 l1"
  using xxreal_2_def_7 sorry

mtheorem valued_1_th_36:
" for F be  non emptyXBOOLE-0V1\<bar>NATNUMBERSK1 -definedRELAT-1V4\<bar>finiteFINSET-1V1\<bar>FunctionFUNCT-1M1 holds domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> (CutLastLocVALUED-1K66 F) =MEMBEREDR12 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> F \\SUBSET-1K7\<^bsub>(NATNUMBERSK1)\<^esub> {TARSKIK1 LastLocVALUED-1K65 F }"
sorry

mtheorem valued_1_th_37:
" for F be  non emptyXBOOLE-0V1\<bar>NATNUMBERSK1 -definedRELAT-1V4\<bar>finiteFINSET-1V1\<bar>FunctionFUNCT-1M1 holds domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> F =MEMBEREDR12 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> (CutLastLocVALUED-1K66 F) \\/XBOOLE-0K2 {TARSKIK1 LastLocVALUED-1K65 F }"
sorry

mtheorem valued_1_cl_113:
"cluster \<one>\<^sub>M -elementCARD-1V3\<bar>NATNUMBERSK1 -definedRELAT-1V4\<bar>finiteFINSET-1V1 for FunctionFUNCT-1M1"
proof
(*existence*)
  show " ex it be FunctionFUNCT-1M1 st it be \<one>\<^sub>M -elementCARD-1V3\<bar>NATNUMBERSK1 -definedRELAT-1V4\<bar>finiteFINSET-1V1"
sorry
qed "sorry"

mtheorem valued_1_cl_114:
  mlet "F be \<one>\<^sub>M -elementCARD-1V3\<bar>NATNUMBERSK1 -definedRELAT-1V4\<bar>finiteFINSET-1V1\<bar>FunctionFUNCT-1M1"
"cluster CutLastLocVALUED-1K66 F as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "CutLastLocVALUED-1K66 F be emptyXBOOLE-0V1"
sorry
qed "sorry"

mtheorem valued_1_th_38:
" for F be  non emptyXBOOLE-0V1\<bar>NATNUMBERSK1 -definedRELAT-1V4\<bar>finiteFINSET-1V1\<bar>FunctionFUNCT-1M1 holds cardCARD-1K4 (CutLastLocVALUED-1K66 F) =COMPLEX1R1 cardCARD-1K4 F -XCMPLX-0K6 \<one>\<^sub>M"
sorry

(*begin*)
mtheorem valued_1_cl_115:
  mlet "X be setHIDDENM2", "f be X -definedRELAT-1V4\<bar>complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1"
"cluster -VALUED-1K32 f as-term-is X -definedRELAT-1V4"
proof
(*coherence*)
  show "-VALUED-1K32 f be X -definedRELAT-1V4"
sorry
qed "sorry"

mtheorem valued_1_cl_116:
  mlet "X be setHIDDENM2", "f be X -definedRELAT-1V4\<bar>complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1"
"cluster f \<inverse>VALUED-1K37 as-term-is X -definedRELAT-1V4"
proof
(*coherence*)
  show "f \<inverse>VALUED-1K37 be X -definedRELAT-1V4"
sorry
qed "sorry"

mtheorem valued_1_cl_117:
  mlet "X be setHIDDENM2", "f be X -definedRELAT-1V4\<bar>complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1"
"cluster f ^2VALUED-1K41 as-term-is X -definedRELAT-1V4"
proof
(*coherence*)
  show "f ^2VALUED-1K41 be X -definedRELAT-1V4"
sorry
qed "sorry"

mtheorem valued_1_cl_118:
  mlet "X be setHIDDENM2", "f be X -definedRELAT-1V4\<bar>complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1"
"cluster |.VALUED-1K56 f.| as-term-is X -definedRELAT-1V4"
proof
(*coherence*)
  show "|.VALUED-1K56 f.| be X -definedRELAT-1V4"
sorry
qed "sorry"

mtheorem valued_1_cl_119:
  mlet "X be setHIDDENM2"
"cluster totalPARTFUN1V1\<^bsub>(X)\<^esub> for X -definedRELAT-1V4\<bar>natural-valuedVALUED-0V8\<bar>FunctionFUNCT-1M1"
proof
(*existence*)
  show " ex it be X -definedRELAT-1V4\<bar>natural-valuedVALUED-0V8\<bar>FunctionFUNCT-1M1 st it be totalPARTFUN1V1\<^bsub>(X)\<^esub>"
sorry
qed "sorry"

mtheorem valued_1_cl_120:
  mlet "X be setHIDDENM2", "f be totalPARTFUN1V1\<^bsub>(X)\<^esub>\<bar>X -definedRELAT-1V4\<bar>complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1"
"cluster -VALUED-1K32 f as-term-is totalPARTFUN1V1\<^bsub>(X)\<^esub>"
proof
(*coherence*)
  show "-VALUED-1K32 f be totalPARTFUN1V1\<^bsub>(X)\<^esub>"
sorry
qed "sorry"

mtheorem valued_1_cl_121:
  mlet "X be setHIDDENM2", "f be totalPARTFUN1V1\<^bsub>(X)\<^esub>\<bar>X -definedRELAT-1V4\<bar>complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1"
"cluster f \<inverse>VALUED-1K37 as-term-is totalPARTFUN1V1\<^bsub>(X)\<^esub>"
proof
(*coherence*)
  show "f \<inverse>VALUED-1K37 be totalPARTFUN1V1\<^bsub>(X)\<^esub>"
sorry
qed "sorry"

mtheorem valued_1_cl_122:
  mlet "X be setHIDDENM2", "f be totalPARTFUN1V1\<^bsub>(X)\<^esub>\<bar>X -definedRELAT-1V4\<bar>complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1"
"cluster f ^2VALUED-1K41 as-term-is totalPARTFUN1V1\<^bsub>(X)\<^esub>"
proof
(*coherence*)
  show "f ^2VALUED-1K41 be totalPARTFUN1V1\<^bsub>(X)\<^esub>"
sorry
qed "sorry"

mtheorem valued_1_cl_123:
  mlet "X be setHIDDENM2", "f be totalPARTFUN1V1\<^bsub>(X)\<^esub>\<bar>X -definedRELAT-1V4\<bar>complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1"
"cluster |.VALUED-1K56 f.| as-term-is totalPARTFUN1V1\<^bsub>(X)\<^esub>"
proof
(*coherence*)
  show "|.VALUED-1K56 f.| be totalPARTFUN1V1\<^bsub>(X)\<^esub>"
sorry
qed "sorry"

mtheorem valued_1_cl_124:
  mlet "X be setHIDDENM2", "f be X -definedRELAT-1V4\<bar>complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1", "r be ComplexXCMPLX-0M1"
"cluster r +VALUED-1K7 f as-term-is X -definedRELAT-1V4"
proof
(*coherence*)
  show "r +VALUED-1K7 f be X -definedRELAT-1V4"
sorry
qed "sorry"

mtheorem valued_1_cl_125:
  mlet "X be setHIDDENM2", "f be X -definedRELAT-1V4\<bar>complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1", "r be ComplexXCMPLX-0M1"
"cluster f -VALUED-1K14 r as-term-is X -definedRELAT-1V4"
proof
(*coherence*)
  show "f -VALUED-1K14 r be X -definedRELAT-1V4"
     sorry
qed "sorry"

mtheorem valued_1_cl_126:
  mlet "X be setHIDDENM2", "f be X -definedRELAT-1V4\<bar>complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1", "r be ComplexXCMPLX-0M1"
"cluster r (#)VALUED-1K25 f as-term-is X -definedRELAT-1V4"
proof
(*coherence*)
  show "r (#)VALUED-1K25 f be X -definedRELAT-1V4"
sorry
qed "sorry"

mtheorem valued_1_cl_127:
  mlet "X be setHIDDENM2", "f be totalPARTFUN1V1\<^bsub>(X)\<^esub>\<bar>X -definedRELAT-1V4\<bar>complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1", "r be ComplexXCMPLX-0M1"
"cluster r +VALUED-1K7 f as-term-is totalPARTFUN1V1\<^bsub>(X)\<^esub>"
proof
(*coherence*)
  show "r +VALUED-1K7 f be totalPARTFUN1V1\<^bsub>(X)\<^esub>"
sorry
qed "sorry"

mtheorem valued_1_cl_128:
  mlet "X be setHIDDENM2", "f be totalPARTFUN1V1\<^bsub>(X)\<^esub>\<bar>X -definedRELAT-1V4\<bar>complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1", "r be ComplexXCMPLX-0M1"
"cluster f -VALUED-1K14 r as-term-is totalPARTFUN1V1\<^bsub>(X)\<^esub>"
proof
(*coherence*)
  show "f -VALUED-1K14 r be totalPARTFUN1V1\<^bsub>(X)\<^esub>"
     sorry
qed "sorry"

mtheorem valued_1_cl_129:
  mlet "X be setHIDDENM2", "f be totalPARTFUN1V1\<^bsub>(X)\<^esub>\<bar>X -definedRELAT-1V4\<bar>complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1", "r be ComplexXCMPLX-0M1"
"cluster r (#)VALUED-1K25 f as-term-is totalPARTFUN1V1\<^bsub>(X)\<^esub>"
proof
(*coherence*)
  show "r (#)VALUED-1K25 f be totalPARTFUN1V1\<^bsub>(X)\<^esub>"
sorry
qed "sorry"

mtheorem valued_1_cl_130:
  mlet "X be setHIDDENM2", "f1 be complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1", "f2 be X -definedRELAT-1V4\<bar>complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1"
"cluster f1 +VALUED-1K1 f2 as-term-is X -definedRELAT-1V4"
proof
(*coherence*)
  show "f1 +VALUED-1K1 f2 be X -definedRELAT-1V4"
sorry
qed "sorry"

mtheorem valued_1_cl_131:
  mlet "X be setHIDDENM2", "f1 be complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1", "f2 be X -definedRELAT-1V4\<bar>complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1"
"cluster f1 -VALUED-1K47 f2 as-term-is X -definedRELAT-1V4"
proof
(*coherence*)
  show "f1 -VALUED-1K47 f2 be X -definedRELAT-1V4"
     sorry
qed "sorry"

mtheorem valued_1_cl_132:
  mlet "X be setHIDDENM2", "f1 be complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1", "f2 be X -definedRELAT-1V4\<bar>complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1"
"cluster f1 (#)VALUED-1K19 f2 as-term-is X -definedRELAT-1V4"
proof
(*coherence*)
  show "f1 (#)VALUED-1K19 f2 be X -definedRELAT-1V4"
sorry
qed "sorry"

mtheorem valued_1_cl_133:
  mlet "X be setHIDDENM2", "f1 be complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1", "f2 be X -definedRELAT-1V4\<bar>complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1"
"cluster f1 /\<inverse>VALUED-1K52 f2 as-term-is X -definedRELAT-1V4"
proof
(*coherence*)
  show "f1 /\<inverse>VALUED-1K52 f2 be X -definedRELAT-1V4"
     sorry
qed "sorry"

mtheorem valued_1_cl_134:
  mlet "X be setHIDDENM2", "f1 be totalPARTFUN1V1\<^bsub>(X)\<^esub>\<bar>X -definedRELAT-1V4\<bar>complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1", "f2 be totalPARTFUN1V1\<^bsub>(X)\<^esub>\<bar>X -definedRELAT-1V4\<bar>complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1"
"cluster f1 +VALUED-1K1 f2 as-term-is totalPARTFUN1V1\<^bsub>(X)\<^esub>"
proof
(*coherence*)
  show "f1 +VALUED-1K1 f2 be totalPARTFUN1V1\<^bsub>(X)\<^esub>"
sorry
qed "sorry"

mtheorem valued_1_cl_135:
  mlet "X be setHIDDENM2", "f1 be totalPARTFUN1V1\<^bsub>(X)\<^esub>\<bar>X -definedRELAT-1V4\<bar>complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1", "f2 be totalPARTFUN1V1\<^bsub>(X)\<^esub>\<bar>X -definedRELAT-1V4\<bar>complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1"
"cluster f1 -VALUED-1K47 f2 as-term-is totalPARTFUN1V1\<^bsub>(X)\<^esub>"
proof
(*coherence*)
  show "f1 -VALUED-1K47 f2 be totalPARTFUN1V1\<^bsub>(X)\<^esub>"
     sorry
qed "sorry"

mtheorem valued_1_cl_136:
  mlet "X be setHIDDENM2", "f1 be totalPARTFUN1V1\<^bsub>(X)\<^esub>\<bar>X -definedRELAT-1V4\<bar>complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1", "f2 be totalPARTFUN1V1\<^bsub>(X)\<^esub>\<bar>X -definedRELAT-1V4\<bar>complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1"
"cluster f1 (#)VALUED-1K19 f2 as-term-is totalPARTFUN1V1\<^bsub>(X)\<^esub>"
proof
(*coherence*)
  show "f1 (#)VALUED-1K19 f2 be totalPARTFUN1V1\<^bsub>(X)\<^esub>"
sorry
qed "sorry"

mtheorem valued_1_cl_137:
  mlet "X be setHIDDENM2", "f1 be totalPARTFUN1V1\<^bsub>(X)\<^esub>\<bar>X -definedRELAT-1V4\<bar>complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1", "f2 be totalPARTFUN1V1\<^bsub>(X)\<^esub>\<bar>X -definedRELAT-1V4\<bar>complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1"
"cluster f1 /\<inverse>VALUED-1K52 f2 as-term-is totalPARTFUN1V1\<^bsub>(X)\<^esub>"
proof
(*coherence*)
  show "f1 /\<inverse>VALUED-1K52 f2 be totalPARTFUN1V1\<^bsub>(X)\<^esub>"
     sorry
qed "sorry"

mtheorem valued_1_cl_138:
  mlet "X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "F be X -valuedRELAT-1V5\<bar> non emptyXBOOLE-0V1\<bar>NATNUMBERSK1 -definedRELAT-1V4\<bar>finiteFINSET-1V1\<bar>FunctionFUNCT-1M1"
"cluster CutLastLocVALUED-1K66 F as-term-is X -valuedRELAT-1V5"
proof
(*coherence*)
  show "CutLastLocVALUED-1K66 F be X -valuedRELAT-1V5"
     sorry
qed "sorry"

mtheorem valued_1_th_39:
" for f be FunctionFUNCT-1M1 holds  for i be NatNAT-1M1 holds  for n be NatNAT-1M1 holds i inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> (ShiftVALUED-1K64(f,n)) implies ( ex j be NatNAT-1M1 st j inTARSKIR2 domRELAT-1K1 f & i =COMPLEX1R1 j +XCMPLX-0K2 n)"
sorry

mtheorem valued_1_cl_139:
  mlet "p be FinSubsequenceFINSEQ-1M4", "i be NatNAT-1M1"
"cluster ShiftVALUED-1K64(p,i) as-term-is FinSubsequence-likeFINSEQ-1V2"
proof
(*coherence*)
  show "ShiftVALUED-1K64(p,i) be FinSubsequence-likeFINSEQ-1V2"
sorry
qed "sorry"

reserve i for "NatNAT-1M1"
reserve k, k1, k2, j1 for "ElementSUBSET-1M1-of NATNUMBERSK1"
reserve x, x1, x2, y for "setHIDDENM2"
mtheorem valued_1_th_40:
" for i be NatNAT-1M1 holds  for p be FinSequenceFINSEQ-1M1 holds domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> (ShiftVALUED-1K64(p,i)) =XBOOLE-0R4 {j1 where j1 be NatNAT-1M1 : i +NAT-1K1 \<one>\<^sub>M <=XXREAL-0R1 j1 & j1 <=XXREAL-0R1 i +NAT-1K1 lenFINSEQ-1K4 p }"
sorry

mtheorem valued_1_th_41:
" for i be NatNAT-1M1 holds  for q be FinSubsequenceFINSEQ-1M4 holds  ex ss be FinSubsequenceFINSEQ-1M4 st ((domRELSET-1K1\<^bsub>(omegaORDINAL1K4)\<^esub> ss =MEMBEREDR12 domRELSET-1K1\<^bsub>(omegaORDINAL1K4)\<^esub> q & rngFUNCT-1K2 ss =XBOOLE-0R4 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> (ShiftVALUED-1K64(q,i))) & ( for k be ElementSUBSET-1M1-of NATNUMBERSK1 holds k inTARSKIR2 domRELSET-1K1\<^bsub>(omegaORDINAL1K4)\<^esub> q implies ss .FUNCT-1K1 k =XBOOLE-0R4 i +NAT-1K1 k)) & ss be one-to-oneFUNCT-1V2"
sorry

mlemma valued_1_lm_5:
" for i be NatNAT-1M1 holds  for p be FinSequenceFINSEQ-1M1 holds  ex fs be FinSequenceFINSEQ-1M1 st ((domFINSEQ-1K5 fs =MEMBEREDR12 domFINSEQ-1K5 p & rngFUNCT-1K2 fs =XBOOLE-0R4 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> (ShiftVALUED-1K64(p,i))) & ( for k be ElementSUBSET-1M1-of NATNUMBERSK1 holds k inTARSKIR2 domFINSEQ-1K5 p implies fs .FUNCT-1K1 k =XBOOLE-0R4 i +NAT-1K1 k)) & fs be one-to-oneFUNCT-1V2"
sorry

mtheorem valued_1_th_42:
" for i be NatNAT-1M1 holds  for q be FinSubsequenceFINSEQ-1M4 holds cardCARD-1K4 q =COMPLEX1R1 cardCARD-1K4 (ShiftVALUED-1K64(q,i))"
sorry

mtheorem valued_1_th_43:
" for i be NatNAT-1M1 holds  for p be FinSequenceFINSEQ-1M1 holds domFINSEQ-1K5 p =MEMBEREDR12 domFINSEQ-1K5 (SeqFINSEQ-1K16 (ShiftVALUED-1K64(p,i)))"
sorry

mtheorem valued_1_th_44:
" for i be NatNAT-1M1 holds  for k be ElementSUBSET-1M1-of NATNUMBERSK1 holds  for p be FinSequenceFINSEQ-1M1 holds k inTARSKIR2 domFINSEQ-1K5 p implies SgmFINSEQ-1K15 (domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> (ShiftVALUED-1K64(p,i))) .FUNCT-1K1 k =COMPLEX1R1 i +NAT-1K1 k"
sorry

mtheorem valued_1_th_45:
" for i be NatNAT-1M1 holds  for k be ElementSUBSET-1M1-of NATNUMBERSK1 holds  for p be FinSequenceFINSEQ-1M1 holds k inTARSKIR2 domFINSEQ-1K5 p implies SeqFINSEQ-1K16 (ShiftVALUED-1K64(p,i)) .FUNCT-1K1 k =XBOOLE-0R4 p .FUNCT-1K1 k"
sorry

mtheorem valued_1_th_46:
" for i be NatNAT-1M1 holds  for p be FinSequenceFINSEQ-1M1 holds SeqFINSEQ-1K16 (ShiftVALUED-1K64(p,i)) =FINSEQ-1R1 p"
sorry

reserve p1, p2 for "FinSequenceFINSEQ-1M1"
mlemma valued_1_lm_6:
" for j be NatNAT-1M1 holds  for k be NatNAT-1M1 holds  for l be NatNAT-1M1 holds \<one>\<^sub>M <=XXREAL-0R1 j & j <=XXREAL-0R1 l or l +NAT-1K1 \<one>\<^sub>M <=XXREAL-0R1 j & j <=XXREAL-0R1 l +XCMPLX-0K2 k implies \<one>\<^sub>M <=XXREAL-0R1 j & j <=XXREAL-0R1 l +XCMPLX-0K2 k"
sorry

mtheorem valued_1_th_47:
" for p1 be FinSequenceFINSEQ-1M1 holds  for p2 be FinSequenceFINSEQ-1M1 holds domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> (p1 \\/XBOOLE-0K2 ShiftVALUED-1K64(p2,lenFINSEQ-1K4 p1)) =MEMBEREDR12 SegFINSEQ-1K2 (lenFINSEQ-1K4 p1 +NAT-1K1 lenFINSEQ-1K4 p2)"
sorry

mtheorem valued_1_th_48:
" for i be NatNAT-1M1 holds  for p1 be FinSequenceFINSEQ-1M1 holds  for p2 be FinSubsequenceFINSEQ-1M4 holds lenFINSEQ-1K4 p1 <=XXREAL-0R1 i implies domFINSEQ-1K5 p1 missesMEMBEREDR18 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> (ShiftVALUED-1K64(p2,i))"
sorry

mtheorem valued_1_th_49:
" for p1 be FinSequenceFINSEQ-1M1 holds  for p2 be FinSequenceFINSEQ-1M1 holds p1 ^FINSEQ-1K8 p2 =RELAT-1R1 p1 \\/XBOOLE-0K2 ShiftVALUED-1K64(p2,lenFINSEQ-1K4 p1)"
sorry

mtheorem valued_1_th_50:
" for i be NatNAT-1M1 holds  for p1 be FinSequenceFINSEQ-1M1 holds  for p2 be FinSubsequenceFINSEQ-1M4 holds i >=XXREAL-0R2 lenFINSEQ-1K4 p1 implies p1 missesXBOOLE-0R1 ShiftVALUED-1K64(p2,i)"
sorry

mtheorem valued_1_th_51:
" for F be totalPARTFUN1V1\<^bsub>(NATNUMBERSK1)\<^esub>\<bar>NATNUMBERSK1 -definedRELAT-1V4\<bar>FunctionFUNCT-1M1 holds  for p be NATNUMBERSK1 -definedRELAT-1V4\<bar>FunctionFUNCT-1M1 holds  for n be ElementSUBSET-1M1-of NATNUMBERSK1 holds ShiftVALUED-1K64(p,n) c=RELAT-1R2 F implies ( for i be ElementSUBSET-1M1-of NATNUMBERSK1 holds i inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> p implies F .FUNCT-1K1 (n +NAT-1K1 i) =XBOOLE-0R4 p .FUNCT-1K1 i)"
sorry

mtheorem valued_1_th_52:
" for i be NatNAT-1M1 holds  for p be FinSubsequenceFINSEQ-1M4 holds  for q be FinSubsequenceFINSEQ-1M4 holds q c=RELAT-1R2 p implies ShiftVALUED-1K64(q,i) c=RELAT-1R2 ShiftVALUED-1K64(p,i)"
sorry

mtheorem valued_1_th_53:
" for p1 be FinSequenceFINSEQ-1M1 holds  for p2 be FinSequenceFINSEQ-1M1 holds ShiftVALUED-1K64(p2,lenFINSEQ-1K4 p1) c=RELAT-1R2 p1 ^FINSEQ-1K8 p2"
sorry

reserve q, q1, q2, q3, q4 for "FinSubsequenceFINSEQ-1M4"
mtheorem valued_1_th_54:
" for i be NatNAT-1M1 holds  for q1 be FinSubsequenceFINSEQ-1M4 holds  for q2 be FinSubsequenceFINSEQ-1M4 holds domRELSET-1K1\<^bsub>(omegaORDINAL1K4)\<^esub> q1 missesMEMBEREDR18 domRELSET-1K1\<^bsub>(omegaORDINAL1K4)\<^esub> q2 implies domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> (ShiftVALUED-1K64(q1,i)) missesMEMBEREDR18 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> (ShiftVALUED-1K64(q2,i))"
sorry

mtheorem valued_1_th_55:
" for i be NatNAT-1M1 holds  for q be FinSubsequenceFINSEQ-1M4 holds  for q1 be FinSubsequenceFINSEQ-1M4 holds  for q2 be FinSubsequenceFINSEQ-1M4 holds q =RELAT-1R1 q1 \\/XBOOLE-0K2 q2 & q1 missesXBOOLE-0R1 q2 implies ShiftVALUED-1K64(q1,i) \\/XBOOLE-0K2 ShiftVALUED-1K64(q2,i) =RELAT-1R1 ShiftVALUED-1K64(q,i)"
sorry

mtheorem valued_1_th_56:
" for i be NatNAT-1M1 holds  for q be FinSubsequenceFINSEQ-1M4 holds domFINSEQ-1K5 (SeqFINSEQ-1K16 q) =MEMBEREDR12 domFINSEQ-1K5 (SeqFINSEQ-1K16 (ShiftVALUED-1K64(q,i)))"
sorry

reserve l1 for "NatNAT-1M1"
mtheorem valued_1_th_57:
" for i be NatNAT-1M1 holds  for k be ElementSUBSET-1M1-of NATNUMBERSK1 holds  for q be FinSubsequenceFINSEQ-1M4 holds k inTARSKIR2 domFINSEQ-1K5 (SeqFINSEQ-1K16 q) implies ( ex j be ElementSUBSET-1M1-of NATNUMBERSK1 st j =COMPLEX1R1 SgmFINSEQ-1K15 (domRELSET-1K1\<^bsub>(omegaORDINAL1K4)\<^esub> q) .FUNCT-1K1 k & SgmFINSEQ-1K15 (domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> (ShiftVALUED-1K64(q,i))) .FUNCT-1K1 k =COMPLEX1R1 i +NAT-1K1 j)"
sorry

mtheorem valued_1_th_58:
" for i be NatNAT-1M1 holds  for k be ElementSUBSET-1M1-of NATNUMBERSK1 holds  for q be FinSubsequenceFINSEQ-1M4 holds k inTARSKIR2 domFINSEQ-1K5 (SeqFINSEQ-1K16 q) implies SeqFINSEQ-1K16 (ShiftVALUED-1K64(q,i)) .FUNCT-1K1 k =XBOOLE-0R4 SeqFINSEQ-1K16 q .FUNCT-1K1 k"
sorry

mtheorem valued_1_th_59:
" for i be NatNAT-1M1 holds  for q be FinSubsequenceFINSEQ-1M4 holds SeqFINSEQ-1K16 q =FINSEQ-1R1 SeqFINSEQ-1K16 (ShiftVALUED-1K64(q,i))"
sorry

mtheorem valued_1_th_60:
" for i be NatNAT-1M1 holds  for k be ElementSUBSET-1M1-of NATNUMBERSK1 holds  for q be FinSubsequenceFINSEQ-1M4 holds domRELSET-1K1\<^bsub>(omegaORDINAL1K4)\<^esub> q c=MEMBEREDR6 SegFINSEQ-1K2 k implies domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> (ShiftVALUED-1K64(q,i)) c=MEMBEREDR6 SegFINSEQ-1K2 (i +NAT-1K1 k)"
sorry

mtheorem valued_1_th_61:
" for p be FinSequenceFINSEQ-1M1 holds  for q1 be FinSubsequenceFINSEQ-1M4 holds  for q2 be FinSubsequenceFINSEQ-1M4 holds q1 c=RELAT-1R2 p implies ( ex ss be FinSubsequenceFINSEQ-1M4 st ss =RELAT-1R1 q1 \\/XBOOLE-0K2 ShiftVALUED-1K64(q2,lenFINSEQ-1K4 p))"
sorry

mlemma valued_1_lm_7:
" for i be NatNAT-1M1 holds  for p be FinSubsequenceFINSEQ-1M4 holds  for q be FinSubsequenceFINSEQ-1M4 holds q c=RELAT-1R2 p implies domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> (ShiftVALUED-1K64(q,i)) c=MEMBEREDR6 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> (ShiftVALUED-1K64(p,i))"
sorry

mlemma valued_1_lm_8:
" for p1 be FinSequenceFINSEQ-1M1 holds  for p2 be FinSequenceFINSEQ-1M1 holds  for q1 be FinSubsequenceFINSEQ-1M4 holds  for q2 be FinSubsequenceFINSEQ-1M4 holds q1 c=RELAT-1R2 p1 & q2 c=RELAT-1R2 p2 implies SgmFINSEQ-1K15 (domRELSET-1K1\<^bsub>(omegaORDINAL1K4)\<^esub> q1 \\/SUBSET-1K4\<^bsub>(NATNUMBERSK1)\<^esub> domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> (ShiftVALUED-1K64(q2,lenFINSEQ-1K4 p1))) =FINSEQ-1R1 SgmFINSEQ-1K15 (domRELSET-1K1\<^bsub>(omegaORDINAL1K4)\<^esub> q1) ^FINSEQ-1K9\<^bsub>(omegaORDINAL1K4)\<^esub> SgmFINSEQ-1K15 (domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> (ShiftVALUED-1K64(q2,lenFINSEQ-1K4 p1)))"
sorry

mtheorem valued_1_th_62:
" for p1 be FinSequenceFINSEQ-1M1 holds  for p2 be FinSequenceFINSEQ-1M1 holds  for q1 be FinSubsequenceFINSEQ-1M4 holds  for q2 be FinSubsequenceFINSEQ-1M4 holds q1 c=RELAT-1R2 p1 & q2 c=RELAT-1R2 p2 implies ( ex ss be FinSubsequenceFINSEQ-1M4 st ss =RELAT-1R1 q1 \\/XBOOLE-0K2 ShiftVALUED-1K64(q2,lenFINSEQ-1K4 p1) & domFINSEQ-1K5 (SeqFINSEQ-1K16 ss) =MEMBEREDR12 SegFINSEQ-1K2 (lenFINSEQ-1K4 (SeqFINSEQ-1K16 q1) +NAT-1K1 lenFINSEQ-1K4 (SeqFINSEQ-1K16 q2)))"
sorry

mtheorem valued_1_th_63:
" for p1 be FinSequenceFINSEQ-1M1 holds  for p2 be FinSequenceFINSEQ-1M1 holds  for q1 be FinSubsequenceFINSEQ-1M4 holds  for q2 be FinSubsequenceFINSEQ-1M4 holds q1 c=RELAT-1R2 p1 & q2 c=RELAT-1R2 p2 implies ( ex ss be FinSubsequenceFINSEQ-1M4 st (ss =RELAT-1R1 q1 \\/XBOOLE-0K2 ShiftVALUED-1K64(q2,lenFINSEQ-1K4 p1) & domFINSEQ-1K5 (SeqFINSEQ-1K16 ss) =MEMBEREDR12 SegFINSEQ-1K2 (lenFINSEQ-1K4 (SeqFINSEQ-1K16 q1) +NAT-1K1 lenFINSEQ-1K4 (SeqFINSEQ-1K16 q2))) & SeqFINSEQ-1K16 ss =RELAT-1R1 SeqFINSEQ-1K16 q1 \\/XBOOLE-0K2 ShiftVALUED-1K64(SeqFINSEQ-1K16 q2,lenFINSEQ-1K4 (SeqFINSEQ-1K16 q1)))"
sorry

mtheorem valued_1_th_64:
" for p1 be FinSequenceFINSEQ-1M1 holds  for p2 be FinSequenceFINSEQ-1M1 holds  for q1 be FinSubsequenceFINSEQ-1M4 holds  for q2 be FinSubsequenceFINSEQ-1M4 holds q1 c=RELAT-1R2 p1 & q2 c=RELAT-1R2 p2 implies ( ex ss be FinSubsequenceFINSEQ-1M4 st ss =RELAT-1R1 q1 \\/XBOOLE-0K2 ShiftVALUED-1K64(q2,lenFINSEQ-1K4 p1) & SeqFINSEQ-1K16 q1 ^FINSEQ-1K8 SeqFINSEQ-1K16 q2 =FINSEQ-1R1 SeqFINSEQ-1K16 ss)"
sorry

mtheorem valued_1_th_65:
" for F be  non emptyXBOOLE-0V1\<bar>NATNUMBERSK1 -definedRELAT-1V4\<bar>finiteFINSET-1V1\<bar>FunctionFUNCT-1M1 holds cardCARD-1K4 (CutLastLocVALUED-1K66 F) =COMPLEX1R1 cardCARD-1K4 F -'XREAL-0K1 \<one>\<^sub>M"
sorry

mtheorem valued_1_th_66:
" for F be  non emptyXBOOLE-0V1\<bar>NATNUMBERSK1 -definedRELAT-1V4\<bar>finiteFINSET-1V1\<bar>FunctionFUNCT-1M1 holds  for G be  non emptyXBOOLE-0V1\<bar>NATNUMBERSK1 -definedRELAT-1V4\<bar>finiteFINSET-1V1\<bar>FunctionFUNCT-1M1 holds domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> F =MEMBEREDR12 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> G implies LastLocVALUED-1K65 F =COMPLEX1R1 LastLocVALUED-1K65 G"
   sorry

mtheorem valued_1_th_67:
" for i be NatNAT-1M1 holds  for x be setHIDDENM2 holds  for y be setHIDDENM2 holds  for f be  non emptyXBOOLE-0V1\<bar>NATNUMBERSK1 -definedRELAT-1V4\<bar>finiteFINSET-1V1\<bar>FunctionFUNCT-1M1 holds ShiftVALUED-1K64(f +~FUNCT-4K8(x,y),i) =FUNCT-1R1 (ShiftVALUED-1K64(f,i))+~FUNCT-4K8(x,y)"
sorry

mtheorem valued_1_th_68:
" for F be  non emptyXBOOLE-0V1\<bar>NATNUMBERSK1 -definedRELAT-1V4\<bar>finiteFINSET-1V1\<bar>FunctionFUNCT-1M1 holds  for G be  non emptyXBOOLE-0V1\<bar>NATNUMBERSK1 -definedRELAT-1V4\<bar>finiteFINSET-1V1\<bar>FunctionFUNCT-1M1 holds domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> F c=MEMBEREDR6 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> G implies LastLocVALUED-1K65 F <=XXREAL-0R1 LastLocVALUED-1K65 G"
  using xxreal_2_th_59 sorry

end
