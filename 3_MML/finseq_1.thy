theory finseq_1
  imports valued_0 axioms card_2
   "../mizar_extension/E_number"
begin
(*begin*)
reserve a for "naturalORDINAL1V7\<bar>NumberORDINAL1M1"
reserve k, l, m, n, k1, b, c, i for "NatNAT-1M1"
reserve x, y, z, y1, y2 for "objectHIDDENM1"
reserve X, Y for "setHIDDENM2"
reserve f, g for "FunctionFUNCT-1M1"
mdef finseq_1_def_1 ("SegFINSEQ-1K1  _ " [228]228 ) where
  mlet "n be naturalORDINAL1V7\<bar>NumberORDINAL1M1"
"func SegFINSEQ-1K1 n \<rightarrow> setHIDDENM2 equals
  {k where k be NatNAT-1M1 : \<one>\<^sub>M <=XXREAL-0R1 k & k <=XXREAL-0R1 n }"
proof-
  (*coherence*)
    show "{k where k be NatNAT-1M1 : \<one>\<^sub>M <=XXREAL-0R1 k & k <=XXREAL-0R1 n } be setHIDDENM2"
       sorry
qed "sorry"

abbreviation(input) FINSEQ_1K2("SegFINSEQ-1K2  _ " [228]228) where
  "SegFINSEQ-1K2 n \<equiv> SegFINSEQ-1K1 n"

mtheorem finseq_1_add_1:
  mlet "n be NatNAT-1M1"
"cluster SegFINSEQ-1K1 n as-term-is SubsetSUBSET-1M2-of NATNUMBERSK1"
proof
(*coherence*)
  show "SegFINSEQ-1K1 n be SubsetSUBSET-1M2-of NATNUMBERSK1"
sorry
qed "sorry"

mtheorem finseq_1_th_1:
" for a be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for b be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds a inHIDDENR3 SegFINSEQ-1K1 b iff \<one>\<^sub>M <=XXREAL-0R1 a & a <=XXREAL-0R1 b"
sorry

mtheorem finseq_1_cl_1:
  mlet "n be zeroORDINAL1V8\<bar>naturalORDINAL1V7\<bar>NumberORDINAL1M1"
"cluster SegFINSEQ-1K1 n as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "SegFINSEQ-1K1 n be emptyXBOOLE-0V1"
sorry
qed "sorry"

mtheorem finseq_1_th_2:
"SegFINSEQ-1K2 \<one>\<^sub>M =XBOOLE-0R4 {TARSKIK1 \<one>\<^sub>M} & SegFINSEQ-1K2 \<two>\<^sub>M =XBOOLE-0R4 {TARSKIK2 \<one>\<^sub>M,\<two>\<^sub>M }"
sorry

mtheorem finseq_1_th_3:
" for a be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds a =HIDDENR1 0NUMBERSK6 or a inHIDDENR3 SegFINSEQ-1K1 a"
sorry

mtheorem finseq_1_cl_2:
  mlet "n be  non zeroORDINAL1V8\<bar>naturalORDINAL1V7\<bar>NumberORDINAL1M1"
"cluster SegFINSEQ-1K1 n as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "SegFINSEQ-1K1 n be  non emptyXBOOLE-0V1"
    using finseq_1_th_3 sorry
qed "sorry"

mtheorem finseq_1_th_4:
" for a be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds a +NAT-1K1 \<one>\<^sub>M inTARSKIR2 SegFINSEQ-1K2 (a +NAT-1K1 \<one>\<^sub>M)"
  using finseq_1_th_3 sorry

mtheorem finseq_1_th_5:
" for a be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for b be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds a <=XXREAL-0R1 b iff SegFINSEQ-1K1 a c=TARSKIR1 SegFINSEQ-1K1 b"
sorry

mtheorem finseq_1_th_6:
" for a be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for b be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds SegFINSEQ-1K1 a =XBOOLE-0R4 SegFINSEQ-1K1 b implies a =HIDDENR1 b"
sorry

mtheorem finseq_1_th_7:
" for a be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for b be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for c be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds c <=XXREAL-0R1 a implies SegFINSEQ-1K1 c =XBOOLE-0R4 SegFINSEQ-1K1 a /\\XBOOLE-0K3 SegFINSEQ-1K1 c"
  using finseq_1_th_5 xboole_1_th_28 sorry

mtheorem finseq_1_th_8:
" for a be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for c be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds SegFINSEQ-1K1 c =XBOOLE-0R4 SegFINSEQ-1K1 c /\\XBOOLE-0K3 SegFINSEQ-1K1 a implies c <=XXREAL-0R1 a"
  using finseq_1_th_6 finseq_1_th_7 sorry

mtheorem finseq_1_th_9:
" for a be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds SegFINSEQ-1K1 a \\/XBOOLE-0K2 {TARSKIK1 a +NAT-1K1 \<one>\<^sub>M } =XBOOLE-0R4 SegFINSEQ-1K2 (a +NAT-1K1 \<one>\<^sub>M)"
sorry

mtheorem finseq_1_th_10:
" for k be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds SegFINSEQ-1K1 k =XBOOLE-0R4 SegFINSEQ-1K2 (k +NAT-1K1 \<one>\<^sub>M) \\SUBSET-1K7\<^bsub>(NATNUMBERSK1)\<^esub> {TARSKIK1 k +NAT-1K1 \<one>\<^sub>M }"
sorry

mdef finseq_1_def_2 ("FinSequence-likeFINSEQ-1V1" 70 ) where
"attr FinSequence-likeFINSEQ-1V1 for RelationRELAT-1M1 means
  (\<lambda>IT.  ex n be NatNAT-1M1 st domRELAT-1K1 IT =XBOOLE-0R4 SegFINSEQ-1K2 n)"..

mtheorem finseq_1_cl_3:
"cluster emptyXBOOLE-0V1 also-is FinSequence-likeFINSEQ-1V1 for RelationRELAT-1M1"
proof
(*coherence*)
  show " for it be RelationRELAT-1M1 holds it be emptyXBOOLE-0V1 implies it be FinSequence-likeFINSEQ-1V1"
sorry
qed "sorry"

syntax FINSEQ_1M1 :: "Ty" ("FinSequenceFINSEQ-1M1" 70)
translations "FinSequenceFINSEQ-1M1" \<rightharpoonup> "FinSequence-likeFINSEQ-1V1\<bar>FunctionFUNCT-1M1"

reserve p, q, r, s, t for "FinSequenceFINSEQ-1M1"
mtheorem finseq_1_cl_4:
  mlet "n be naturalORDINAL1V7\<bar>NumberORDINAL1M1"
"cluster SegFINSEQ-1K1 n as-term-is finiteFINSET-1V1"
proof
(*coherence*)
  show "SegFINSEQ-1K1 n be finiteFINSET-1V1"
sorry
qed "sorry"

mtheorem finseq_1_cl_5:
"cluster FinSequence-likeFINSEQ-1V1 also-is finiteFINSET-1V1 for FunctionFUNCT-1M1"
proof
(*coherence*)
  show " for it be FunctionFUNCT-1M1 holds it be FinSequence-likeFINSEQ-1V1 implies it be finiteFINSET-1V1"
sorry
qed "sorry"

mlemma finseq_1_lm_1:
" for n be NatNAT-1M1 holds (SegFINSEQ-1K2 n,n)are-equipotentWELLORD2R2"
sorry

mtheorem finseq_1_cl_6:
  mlet "n be naturalORDINAL1V7\<bar>NumberORDINAL1M1"
"cluster SegFINSEQ-1K1 n as-term-is n -elementCARD-1V3"
proof
(*coherence*)
  show "SegFINSEQ-1K1 n be n -elementCARD-1V3"
sorry
qed "sorry"

abbreviation(input) FINSEQ_1K3("lenFINSEQ-1K3  _ " [228]228) where
  "lenFINSEQ-1K3 p \<equiv> cardCARD-1K1 p"

abbreviation(input) FINSEQ_1K4("lenFINSEQ-1K4  _ " [228]228) where
  "lenFINSEQ-1K4 p \<equiv> cardCARD-1K1 p"

mtheorem finseq_1_def_3:
  mlet "p be FinSequenceFINSEQ-1M1"
"redefine func lenFINSEQ-1K4 p \<rightarrow> ElementSUBSET-1M1-of NATNUMBERSK1 means
  \<lambda>it. SegFINSEQ-1K2 it =XBOOLE-0R4 domRELAT-1K1 p"
proof
(*compatibility*)
  show " for it be ElementSUBSET-1M1-of NATNUMBERSK1 holds it =HIDDENR1 lenFINSEQ-1K4 p iff SegFINSEQ-1K2 it =XBOOLE-0R4 domRELAT-1K1 p"
sorry
qed "sorry"

mtheorem finseq_1_add_2:
  mlet "p be FinSequenceFINSEQ-1M1"
"cluster cardCARD-1K1 p as-term-is ElementSUBSET-1M1-of NATNUMBERSK1"
proof
(*coherence*)
  show "cardCARD-1K1 p be ElementSUBSET-1M1-of NATNUMBERSK1"
sorry
qed "sorry"

abbreviation(input) FINSEQ_1K5("domFINSEQ-1K5  _ " [228]228) where
  "domFINSEQ-1K5 p \<equiv> domRELAT-1K1 p"

mtheorem finseq_1_add_3:
  mlet "p be FinSequenceFINSEQ-1M1"
"cluster domRELAT-1K1 p as-term-is SubsetSUBSET-1M2-of NATNUMBERSK1"
proof
(*coherence*)
  show "domRELAT-1K1 p be SubsetSUBSET-1M2-of NATNUMBERSK1"
sorry
qed "sorry"

mtheorem finseq_1_th_11:
" for f be FunctionFUNCT-1M1 holds ( ex k be NatNAT-1M1 st domRELAT-1K1 f c=TARSKIR1 SegFINSEQ-1K2 k) implies ( ex p be FinSequenceFINSEQ-1M1 st f c=RELAT-1R2 p)"
sorry

theorem finseq_1_sch_1:
  fixes Af0 Pp2 
  assumes
[ty]: "Af0 be NatNAT-1M1" and
   A1: " for k be NatNAT-1M1 holds k inTARSKIR2 SegFINSEQ-1K2 Af0 implies ( ex x be objectHIDDENM1 st Pp2(k,x))"
  shows " ex p be FinSequenceFINSEQ-1M1 st domFINSEQ-1K5 p =XBOOLE-0R4 SegFINSEQ-1K2 Af0 & ( for k be NatNAT-1M1 holds k inTARSKIR2 SegFINSEQ-1K2 Af0 implies Pp2(k,p .FUNCT-1K1 k))"
sorry

theorem finseq_1_sch_2:
  fixes Af0 Ff1 
  assumes
[ty]: "Af0 be NatNAT-1M1" and
  [ty_func]: "\<And> x1. x1 be objectHIDDENM1 \<Longrightarrow> Ff1(x1) be objectHIDDENM1"
  shows " ex p be FinSequenceFINSEQ-1M1 st lenFINSEQ-1K4 p =XBOOLE-0R4 Af0 & ( for k be NatNAT-1M1 holds k inTARSKIR2 domFINSEQ-1K5 p implies p .FUNCT-1K1 k =HIDDENR1 Ff1(k))"
sorry

mtheorem finseq_1_th_12:
" for z be objectHIDDENM1 holds  for p be FinSequenceFINSEQ-1M1 holds z inHIDDENR3 p implies ( ex k be NatNAT-1M1 st k inTARSKIR2 domFINSEQ-1K5 p & z =HIDDENR1 [TARSKIK4 k,p .FUNCT-1K1 k ])"
sorry

mtheorem finseq_1_th_13:
" for p be FinSequenceFINSEQ-1M1 holds  for q be FinSequenceFINSEQ-1M1 holds domFINSEQ-1K5 p =XBOOLE-0R4 domFINSEQ-1K5 q & ( for k be NatNAT-1M1 holds k inTARSKIR2 domFINSEQ-1K5 p implies p .FUNCT-1K1 k =XBOOLE-0R4 q .FUNCT-1K1 k) implies p =FUNCT-1R1 q"
   sorry

mtheorem finseq_1_th_14:
" for p be FinSequenceFINSEQ-1M1 holds  for q be FinSequenceFINSEQ-1M1 holds lenFINSEQ-1K4 p =XBOOLE-0R4 lenFINSEQ-1K4 q & ( for k be NatNAT-1M1 holds \<one>\<^sub>M <=XXREAL-0R1 k & k <=XXREAL-0R1 lenFINSEQ-1K4 p implies p .FUNCT-1K1 k =XBOOLE-0R4 q .FUNCT-1K1 k) implies p =FUNCT-1R1 q"
sorry

mtheorem finseq_1_th_15:
" for a be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for p be FinSequenceFINSEQ-1M1 holds p |RELAT-1K8 SegFINSEQ-1K1 a be FinSequenceFINSEQ-1M1"
sorry

mtheorem finseq_1_th_16:
" for f be FunctionFUNCT-1M1 holds  for p be FinSequenceFINSEQ-1M1 holds rngFUNCT-1K2 p c=TARSKIR1 domRELAT-1K1 f implies f *FUNCT-1K3 p be FinSequenceFINSEQ-1M1"
sorry

mtheorem finseq_1_th_17:
" for a be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for p be FinSequenceFINSEQ-1M1 holds  for q be FinSequenceFINSEQ-1M1 holds a <=XXREAL-0R1 lenFINSEQ-1K4 p & q =FUNCT-1R1 p |RELAT-1K8 SegFINSEQ-1K1 a implies lenFINSEQ-1K4 q =HIDDENR1 a & domFINSEQ-1K5 q =XBOOLE-0R4 SegFINSEQ-1K1 a"
sorry

mdef finseq_1_def_4 ("FinSequenceFINSEQ-1M2-of  _ " [70]70 ) where
  mlet "D be setHIDDENM2"
"mode FinSequenceFINSEQ-1M2-of D \<rightarrow> FinSequenceFINSEQ-1M1 means
  (\<lambda>it. rngFUNCT-1K2 it c=TARSKIR1 D)"
proof-
  (*existence*)
    show " ex it be FinSequenceFINSEQ-1M1 st rngFUNCT-1K2 it c=TARSKIR1 D"
sorry
qed "sorry"

mtheorem finseq_1_cl_7:
  mlet "D be setHIDDENM2"
"cluster note-that D -valuedRELAT-1V5 for FinSequenceFINSEQ-1M2-of D"
proof
(*coherence*)
  show " for it be FinSequenceFINSEQ-1M2-of D holds it be D -valuedRELAT-1V5"
sorry
qed "sorry"

mlemma finseq_1_lm_2:
" for D be setHIDDENM2 holds  for f be FinSequenceFINSEQ-1M2-of D holds f be PartFuncPARTFUN1M1-of(NATNUMBERSK1,D)"
sorry

mtheorem finseq_1_cl_8:
"cluster emptyXBOOLE-0V1 also-is FinSequence-likeFINSEQ-1V1 for RelationRELAT-1M1"
proof
(*coherence*)
  show " for it be RelationRELAT-1M1 holds it be emptyXBOOLE-0V1 implies it be FinSequence-likeFINSEQ-1V1"
     sorry
qed "sorry"

mtheorem finseq_1_cl_9:
  mlet "D be setHIDDENM2"
"cluster FinSequence-likeFINSEQ-1V1 for PartFuncPARTFUN1M1-of(NATNUMBERSK1,D)"
proof
(*existence*)
  show " ex it be PartFuncPARTFUN1M1-of(NATNUMBERSK1,D) st it be FinSequence-likeFINSEQ-1V1"
sorry
qed "sorry"

abbreviation(input) FINSEQ_1M3("FinSequenceFINSEQ-1M3-of  _ " [70]70) where
  "FinSequenceFINSEQ-1M3-of D \<equiv> FinSequenceFINSEQ-1M2-of D"

mtheorem finseq_1_add_4:
  mlet "D be setHIDDENM2"
"cluster note-that FinSequence-likeFINSEQ-1V1\<bar>PartFuncPARTFUN1M1-of(NATNUMBERSK1,D) for FinSequenceFINSEQ-1M2-of D"
proof
(*coherence*)
  show " for it be FinSequenceFINSEQ-1M2-of D holds it be FinSequence-likeFINSEQ-1V1\<bar>PartFuncPARTFUN1M1-of(NATNUMBERSK1,D)"
    using finseq_1_lm_2 sorry
qed "sorry"

reserve D for "setHIDDENM2"
mtheorem finseq_1_th_18:
" for a be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for D be setHIDDENM2 holds  for p be FinSequenceFINSEQ-1M3-of D holds p |PARTFUN1K2\<^bsub>(NATNUMBERSK1,D)\<^esub> SegFINSEQ-1K1 a be FinSequenceFINSEQ-1M3-of D"
sorry

mtheorem finseq_1_th_19:
" for a be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  ex p be FinSequenceFINSEQ-1M3-of D st lenFINSEQ-1K4 p =HIDDENR1 a"
sorry

mlemma finseq_1_lm_3:
" for q be FinSequenceFINSEQ-1M1 holds q =FUNCT-1R1 {}XBOOLE-0K1 iff lenFINSEQ-1K4 q =XBOOLE-0R4 0NUMBERSK6"
   sorry

mtheorem finseq_1_th_20:
" for p be FinSequenceFINSEQ-1M1 holds p <>HIDDENR2 {}XBOOLE-0K1 iff lenFINSEQ-1K4 p >=XXREAL-0R2 \<one>\<^sub>M"
sorry

mdef finseq_1_def_5 ("<*FINSEQ-1K6  _ *>" [0]164 ) where
  mlet "x be objectHIDDENM1"
"func <*FINSEQ-1K6 x*> \<rightarrow> setHIDDENM2 equals
  {TARSKIK1 [TARSKIK4 \<one>\<^sub>M,x ] }"
proof-
  (*coherence*)
    show "{TARSKIK1 [TARSKIK4 \<one>\<^sub>M,x ] } be setHIDDENM2"
       sorry
qed "sorry"

mdef finseq_1_def_6 ("<*>FINSEQ-1K7  _ " [354]354 ) where
  mlet "D be setHIDDENM2"
"func <*>FINSEQ-1K7 D \<rightarrow> FinSequenceFINSEQ-1M3-of D equals
  {}XBOOLE-0K1"
proof-
  (*coherence*)
    show "{}XBOOLE-0K1 be FinSequenceFINSEQ-1M3-of D"
sorry
qed "sorry"

mtheorem finseq_1_cl_10:
  mlet "D be setHIDDENM2"
"cluster <*>FINSEQ-1K7 D as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "<*>FINSEQ-1K7 D be emptyXBOOLE-0V1"
     sorry
qed "sorry"

mtheorem finseq_1_cl_11:
  mlet "D be setHIDDENM2"
"cluster emptyXBOOLE-0V1 for FinSequenceFINSEQ-1M3-of D"
proof
(*existence*)
  show " ex it be FinSequenceFINSEQ-1M3-of D st it be emptyXBOOLE-0V1"
sorry
qed "sorry"

mdef finseq_1_def_7 (" _ ^FINSEQ-1K8  _ " [164,164]164 ) where
  mlet "p be FinSequenceFINSEQ-1M1", "q be FinSequenceFINSEQ-1M1"
"func p ^FINSEQ-1K8 q \<rightarrow> FinSequenceFINSEQ-1M1 means
  \<lambda>it. (domFINSEQ-1K5 it =XBOOLE-0R4 SegFINSEQ-1K2 (lenFINSEQ-1K4 p +NAT-1K1 lenFINSEQ-1K4 q) & ( for k be NatNAT-1M1 holds k inTARSKIR2 domFINSEQ-1K5 p implies it .FUNCT-1K1 k =XBOOLE-0R4 p .FUNCT-1K1 k)) & ( for k be NatNAT-1M1 holds k inTARSKIR2 domFINSEQ-1K5 q implies it .FUNCT-1K1 (lenFINSEQ-1K4 p +XCMPLX-0K2 k) =XBOOLE-0R4 q .FUNCT-1K1 k)"
proof-
  (*existence*)
    show " ex it be FinSequenceFINSEQ-1M1 st (domFINSEQ-1K5 it =XBOOLE-0R4 SegFINSEQ-1K2 (lenFINSEQ-1K4 p +NAT-1K1 lenFINSEQ-1K4 q) & ( for k be NatNAT-1M1 holds k inTARSKIR2 domFINSEQ-1K5 p implies it .FUNCT-1K1 k =XBOOLE-0R4 p .FUNCT-1K1 k)) & ( for k be NatNAT-1M1 holds k inTARSKIR2 domFINSEQ-1K5 q implies it .FUNCT-1K1 (lenFINSEQ-1K4 p +XCMPLX-0K2 k) =XBOOLE-0R4 q .FUNCT-1K1 k)"
sorry
  (*uniqueness*)
    show " for it1 be FinSequenceFINSEQ-1M1 holds  for it2 be FinSequenceFINSEQ-1M1 holds ((domFINSEQ-1K5 it1 =XBOOLE-0R4 SegFINSEQ-1K2 (lenFINSEQ-1K4 p +NAT-1K1 lenFINSEQ-1K4 q) & ( for k be NatNAT-1M1 holds k inTARSKIR2 domFINSEQ-1K5 p implies it1 .FUNCT-1K1 k =XBOOLE-0R4 p .FUNCT-1K1 k)) & ( for k be NatNAT-1M1 holds k inTARSKIR2 domFINSEQ-1K5 q implies it1 .FUNCT-1K1 (lenFINSEQ-1K4 p +XCMPLX-0K2 k) =XBOOLE-0R4 q .FUNCT-1K1 k)) & ((domFINSEQ-1K5 it2 =XBOOLE-0R4 SegFINSEQ-1K2 (lenFINSEQ-1K4 p +NAT-1K1 lenFINSEQ-1K4 q) & ( for k be NatNAT-1M1 holds k inTARSKIR2 domFINSEQ-1K5 p implies it2 .FUNCT-1K1 k =XBOOLE-0R4 p .FUNCT-1K1 k)) & ( for k be NatNAT-1M1 holds k inTARSKIR2 domFINSEQ-1K5 q implies it2 .FUNCT-1K1 (lenFINSEQ-1K4 p +XCMPLX-0K2 k) =XBOOLE-0R4 q .FUNCT-1K1 k)) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mtheorem finseq_1_th_21:
" for p be FinSequenceFINSEQ-1M1 holds  for q be FinSequenceFINSEQ-1M1 holds p =FUNCT-1R1 (p ^FINSEQ-1K8 q)|RELAT-1K8 domFINSEQ-1K5 p"
sorry

mtheorem finseq_1_th_22:
" for p be FinSequenceFINSEQ-1M1 holds  for q be FinSequenceFINSEQ-1M1 holds lenFINSEQ-1K4 (p ^FINSEQ-1K8 q) =XBOOLE-0R4 lenFINSEQ-1K4 p +NAT-1K1 lenFINSEQ-1K4 q"
sorry

mtheorem finseq_1_th_23:
" for p be FinSequenceFINSEQ-1M1 holds  for q be FinSequenceFINSEQ-1M1 holds  for k be NatNAT-1M1 holds lenFINSEQ-1K4 p +NAT-1K1 \<one>\<^sub>M <=XXREAL-0R1 k & k <=XXREAL-0R1 lenFINSEQ-1K4 p +NAT-1K1 lenFINSEQ-1K4 q implies (p ^FINSEQ-1K8 q).FUNCT-1K1 k =XBOOLE-0R4 q .FUNCT-1K1 (k -XCMPLX-0K6 lenFINSEQ-1K4 p)"
sorry

mtheorem finseq_1_th_24:
" for p be FinSequenceFINSEQ-1M1 holds  for q be FinSequenceFINSEQ-1M1 holds  for k be NatNAT-1M1 holds lenFINSEQ-1K4 p <XXREAL-0R3 k & k <=XXREAL-0R1 lenFINSEQ-1K4 (p ^FINSEQ-1K8 q) implies (p ^FINSEQ-1K8 q).FUNCT-1K1 k =XBOOLE-0R4 q .FUNCT-1K1 (k -XCMPLX-0K6 lenFINSEQ-1K4 p)"
sorry

mtheorem finseq_1_th_25:
" for p be FinSequenceFINSEQ-1M1 holds  for q be FinSequenceFINSEQ-1M1 holds  for k be NatNAT-1M1 holds k inTARSKIR2 domFINSEQ-1K5 (p ^FINSEQ-1K8 q) implies k inTARSKIR2 domFINSEQ-1K5 p or ( ex n be NatNAT-1M1 st n inTARSKIR2 domFINSEQ-1K5 q & k =XBOOLE-0R4 lenFINSEQ-1K4 p +XCMPLX-0K2 n)"
sorry

mtheorem finseq_1_th_26:
" for p be FinSequenceFINSEQ-1M1 holds  for q be FinSequenceFINSEQ-1M1 holds domFINSEQ-1K5 p c=TARSKIR1 domFINSEQ-1K5 (p ^FINSEQ-1K8 q)"
sorry

mtheorem finseq_1_th_27:
" for x be objectHIDDENM1 holds  for p be FinSequenceFINSEQ-1M1 holds  for q be FinSequenceFINSEQ-1M1 holds x inHIDDENR3 domFINSEQ-1K5 q implies ( ex k be NatNAT-1M1 st k =HIDDENR1 x & lenFINSEQ-1K4 p +XCMPLX-0K2 k inTARSKIR2 domFINSEQ-1K5 (p ^FINSEQ-1K8 q))"
sorry

mtheorem finseq_1_th_28:
" for k be NatNAT-1M1 holds  for p be FinSequenceFINSEQ-1M1 holds  for q be FinSequenceFINSEQ-1M1 holds k inTARSKIR2 domFINSEQ-1K5 q implies lenFINSEQ-1K4 p +XCMPLX-0K2 k inTARSKIR2 domFINSEQ-1K5 (p ^FINSEQ-1K8 q)"
sorry

mtheorem finseq_1_th_29:
" for p be FinSequenceFINSEQ-1M1 holds  for q be FinSequenceFINSEQ-1M1 holds rngFUNCT-1K2 p c=TARSKIR1 rngFUNCT-1K2 (p ^FINSEQ-1K8 q)"
sorry

mtheorem finseq_1_th_30:
" for p be FinSequenceFINSEQ-1M1 holds  for q be FinSequenceFINSEQ-1M1 holds rngFUNCT-1K2 q c=TARSKIR1 rngFUNCT-1K2 (p ^FINSEQ-1K8 q)"
sorry

mtheorem finseq_1_th_31:
" for p be FinSequenceFINSEQ-1M1 holds  for q be FinSequenceFINSEQ-1M1 holds rngFUNCT-1K2 (p ^FINSEQ-1K8 q) =XBOOLE-0R4 rngFUNCT-1K2 p \\/XBOOLE-0K2 rngFUNCT-1K2 q"
sorry

mtheorem finseq_1_th_32:
" for p be FinSequenceFINSEQ-1M1 holds  for q be FinSequenceFINSEQ-1M1 holds  for r be FinSequenceFINSEQ-1M1 holds (p ^FINSEQ-1K8 q)^FINSEQ-1K8 r =FUNCT-1R1 p ^FINSEQ-1K8 (q ^FINSEQ-1K8 r)"
sorry

mtheorem finseq_1_th_33:
" for p be FinSequenceFINSEQ-1M1 holds  for q be FinSequenceFINSEQ-1M1 holds  for r be FinSequenceFINSEQ-1M1 holds p ^FINSEQ-1K8 r =FUNCT-1R1 q ^FINSEQ-1K8 r or r ^FINSEQ-1K8 p =FUNCT-1R1 r ^FINSEQ-1K8 q implies p =FUNCT-1R1 q"
sorry

mtheorem finseq_1_th_34:
" for p be FinSequenceFINSEQ-1M1 holds p ^FINSEQ-1K8 {}XBOOLE-0K1 =FUNCT-1R1 p & {}XBOOLE-0K1 ^FINSEQ-1K8 p =FUNCT-1R1 p"
sorry

mtheorem finseq_1_th_35:
" for p be FinSequenceFINSEQ-1M1 holds  for q be FinSequenceFINSEQ-1M1 holds p ^FINSEQ-1K8 q =FUNCT-1R1 {}XBOOLE-0K1 implies p =FUNCT-1R1 {}XBOOLE-0K1 & q =FUNCT-1R1 {}XBOOLE-0K1"
sorry

syntax FINSEQ_1K9 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ ^FINSEQ-1K9\<^bsub>'( _ ')\<^esub>  _ " [164,0,164]164)
translations "p ^FINSEQ-1K9\<^bsub>(D)\<^esub> q" \<rightharpoonup> "p ^FINSEQ-1K8 q"

mtheorem finseq_1_add_5:
  mlet "D be setHIDDENM2", "p be FinSequenceFINSEQ-1M3-of D", "q be FinSequenceFINSEQ-1M3-of D"
"cluster p ^FINSEQ-1K8 q as-term-is FinSequenceFINSEQ-1M3-of D"
proof
(*coherence*)
  show "p ^FINSEQ-1K8 q be FinSequenceFINSEQ-1M3-of D"
sorry
qed "sorry"

mlemma finseq_1_lm_4:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for x1 be objectHIDDENM1 holds  for y1 be objectHIDDENM1 holds [TARSKIK4 x,y ] inHIDDENR3 {TARSKIK1 [TARSKIK4 x1,y1 ] } implies x =HIDDENR1 x1 & y =HIDDENR1 y1"
sorry

abbreviation(input) FINSEQ_1K10("<*FINSEQ-1K10  _ *>" [0]164) where
  "<*FINSEQ-1K10 x*> \<equiv> <*FINSEQ-1K6 x*>"

mtheorem finseq_1_def_8:
  mlet "x be objectHIDDENM1"
"redefine func <*FINSEQ-1K10 x*> \<rightarrow> FunctionFUNCT-1M1 means
  \<lambda>it. domRELAT-1K1 it =XBOOLE-0R4 SegFINSEQ-1K2 \<one>\<^sub>M & it .FUNCT-1K1 \<one>\<^sub>M =HIDDENR1 x"
proof
(*compatibility*)
  show " for it be FunctionFUNCT-1M1 holds it =HIDDENR1 <*FINSEQ-1K10 x*> iff domRELAT-1K1 it =XBOOLE-0R4 SegFINSEQ-1K2 \<one>\<^sub>M & it .FUNCT-1K1 \<one>\<^sub>M =HIDDENR1 x"
sorry
qed "sorry"

mtheorem finseq_1_add_6:
  mlet "x be objectHIDDENM1"
"cluster <*FINSEQ-1K6 x*> as-term-is FunctionFUNCT-1M1"
proof
(*coherence*)
  show "<*FINSEQ-1K6 x*> be FunctionFUNCT-1M1"
     sorry
qed "sorry"

mtheorem finseq_1_cl_12:
  mlet "x be objectHIDDENM1"
"cluster <*FINSEQ-1K10 x*> as-term-is Function-likeFUNCT-1V1\<bar>Relation-likeRELAT-1V1"
proof
(*coherence*)
  show "<*FINSEQ-1K10 x*> be Function-likeFUNCT-1V1\<bar>Relation-likeRELAT-1V1"
     sorry
qed "sorry"

mtheorem finseq_1_cl_13:
  mlet "x be objectHIDDENM1"
"cluster <*FINSEQ-1K10 x*> as-term-is FinSequence-likeFINSEQ-1V1"
proof
(*coherence*)
  show "<*FINSEQ-1K10 x*> be FinSequence-likeFINSEQ-1V1"
    using finseq_1_def_8 sorry
qed "sorry"

mtheorem finseq_1_th_36:
" for p be FinSequenceFINSEQ-1M1 holds  for q be FinSequenceFINSEQ-1M1 holds  for D be setHIDDENM2 holds p ^FINSEQ-1K8 q be FinSequenceFINSEQ-1M3-of D implies p be FinSequenceFINSEQ-1M3-of D & q be FinSequenceFINSEQ-1M3-of D"
sorry

mdef finseq_1_def_9 ("<*FINSEQ-1K11 _ , _ *>" [0,0]164 ) where
  mlet "x be objectHIDDENM1", "y be objectHIDDENM1"
"func <*FINSEQ-1K11 x,y *> \<rightarrow> setHIDDENM2 equals
  (<*FINSEQ-1K10 x*>)^FINSEQ-1K8 (<*FINSEQ-1K10 y*>)"
proof-
  (*coherence*)
    show "(<*FINSEQ-1K10 x*>)^FINSEQ-1K8 (<*FINSEQ-1K10 y*>) be setHIDDENM2"
       sorry
qed "sorry"

mdef finseq_1_def_10 ("<*FINSEQ-1K12 _ , _ , _ *>" [0,0,0]164 ) where
  mlet "x be objectHIDDENM1", "y be objectHIDDENM1", "z be objectHIDDENM1"
"func <*FINSEQ-1K12 x,y,z *> \<rightarrow> setHIDDENM2 equals
  ((<*FINSEQ-1K10 x*>)^FINSEQ-1K8 (<*FINSEQ-1K10 y*>))^FINSEQ-1K8 (<*FINSEQ-1K10 z*>)"
proof-
  (*coherence*)
    show "((<*FINSEQ-1K10 x*>)^FINSEQ-1K8 (<*FINSEQ-1K10 y*>))^FINSEQ-1K8 (<*FINSEQ-1K10 z*>) be setHIDDENM2"
       sorry
qed "sorry"

mtheorem finseq_1_cl_14:
  mlet "x be objectHIDDENM1", "y be objectHIDDENM1"
"cluster <*FINSEQ-1K11 x,y *> as-term-is Function-likeFUNCT-1V1\<bar>Relation-likeRELAT-1V1"
proof
(*coherence*)
  show "<*FINSEQ-1K11 x,y *> be Function-likeFUNCT-1V1\<bar>Relation-likeRELAT-1V1"
     sorry
qed "sorry"

mtheorem finseq_1_cl_15:
  mlet "x be objectHIDDENM1", "y be objectHIDDENM1", "z be objectHIDDENM1"
"cluster <*FINSEQ-1K12 x,y,z *> as-term-is Function-likeFUNCT-1V1\<bar>Relation-likeRELAT-1V1"
proof
(*coherence*)
  show "<*FINSEQ-1K12 x,y,z *> be Function-likeFUNCT-1V1\<bar>Relation-likeRELAT-1V1"
     sorry
qed "sorry"

mtheorem finseq_1_cl_16:
  mlet "x be objectHIDDENM1", "y be objectHIDDENM1"
"cluster <*FINSEQ-1K11 x,y *> as-term-is FinSequence-likeFINSEQ-1V1"
proof
(*coherence*)
  show "<*FINSEQ-1K11 x,y *> be FinSequence-likeFINSEQ-1V1"
     sorry
qed "sorry"

mtheorem finseq_1_cl_17:
  mlet "x be objectHIDDENM1", "y be objectHIDDENM1", "z be objectHIDDENM1"
"cluster <*FINSEQ-1K12 x,y,z *> as-term-is FinSequence-likeFINSEQ-1V1"
proof
(*coherence*)
  show "<*FINSEQ-1K12 x,y,z *> be FinSequence-likeFINSEQ-1V1"
     sorry
qed "sorry"

mtheorem finseq_1_th_37:
" for x be objectHIDDENM1 holds <*FINSEQ-1K10 x*> =FUNCT-1R1 {TARSKIK1 [TARSKIK4 \<one>\<^sub>M,x ] }"
   sorry

mtheorem finseq_1_th_38:
" for p be FinSequenceFINSEQ-1M1 holds  for x be objectHIDDENM1 holds p =FUNCT-1R1 <*FINSEQ-1K10 x*> iff domFINSEQ-1K5 p =XBOOLE-0R4 SegFINSEQ-1K2 \<one>\<^sub>M & rngFUNCT-1K2 p =XBOOLE-0R4 {TARSKIK1 x}"
sorry

mtheorem finseq_1_th_39:
" for p be FinSequenceFINSEQ-1M1 holds  for x be objectHIDDENM1 holds p =FUNCT-1R1 <*FINSEQ-1K10 x*> iff lenFINSEQ-1K4 p =XBOOLE-0R4 \<one>\<^sub>M & rngFUNCT-1K2 p =XBOOLE-0R4 {TARSKIK1 x}"
sorry

mtheorem finseq_1_th_40:
" for p be FinSequenceFINSEQ-1M1 holds  for x be objectHIDDENM1 holds p =FUNCT-1R1 <*FINSEQ-1K10 x*> iff lenFINSEQ-1K4 p =XBOOLE-0R4 \<one>\<^sub>M & p .FUNCT-1K1 \<one>\<^sub>M =HIDDENR1 x"
sorry

mtheorem finseq_1_th_41:
" for p be FinSequenceFINSEQ-1M1 holds  for x be objectHIDDENM1 holds ((<*FINSEQ-1K10 x*>)^FINSEQ-1K8 p).FUNCT-1K1 \<one>\<^sub>M =HIDDENR1 x"
sorry

mtheorem finseq_1_th_42:
" for p be FinSequenceFINSEQ-1M1 holds  for x be objectHIDDENM1 holds (p ^FINSEQ-1K8 (<*FINSEQ-1K10 x*>)).FUNCT-1K1 (lenFINSEQ-1K4 p +NAT-1K1 \<one>\<^sub>M) =HIDDENR1 x"
sorry

mtheorem finseq_1_th_43:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for z be objectHIDDENM1 holds <*FINSEQ-1K12 x,y,z *> =FUNCT-1R1 (<*FINSEQ-1K10 x*>)^FINSEQ-1K8 (<*FINSEQ-1K11 y,z *>) & <*FINSEQ-1K12 x,y,z *> =FUNCT-1R1 (<*FINSEQ-1K11 x,y *>)^FINSEQ-1K8 (<*FINSEQ-1K10 z*>)"
  using finseq_1_th_32 sorry

mtheorem finseq_1_th_44:
" for p be FinSequenceFINSEQ-1M1 holds  for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds p =FUNCT-1R1 <*FINSEQ-1K11 x,y *> iff (lenFINSEQ-1K4 p =XBOOLE-0R4 \<two>\<^sub>M & p .FUNCT-1K1 \<one>\<^sub>M =HIDDENR1 x) & p .FUNCT-1K1 \<two>\<^sub>M =HIDDENR1 y"
sorry

mtheorem finseq_1_th_45:
" for p be FinSequenceFINSEQ-1M1 holds  for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for z be objectHIDDENM1 holds p =FUNCT-1R1 <*FINSEQ-1K12 x,y,z *> iff ((lenFINSEQ-1K4 p =XBOOLE-0R4 \<three>\<^sub>M & p .FUNCT-1K1 \<one>\<^sub>M =HIDDENR1 x) & p .FUNCT-1K1 \<two>\<^sub>M =HIDDENR1 y) & p .FUNCT-1K1 \<three>\<^sub>M =HIDDENR1 z"
sorry

mtheorem finseq_1_th_46:
" for p be FinSequenceFINSEQ-1M1 holds  for x be objectHIDDENM1 holds p <>HIDDENR2 {}XBOOLE-0K1 implies ( ex q be FinSequenceFINSEQ-1M1 st  ex x be objectHIDDENM1 st p =FUNCT-1R1 q ^FINSEQ-1K8 (<*FINSEQ-1K10 x*>))"
sorry

syntax FINSEQ_1K13 :: " Set \<Rightarrow>  Set \<Rightarrow> Set" ("<*FINSEQ-1K13\<^bsub>'( _ ')\<^esub>  _ *>" [0,0]164)
translations "<*FINSEQ-1K13\<^bsub>(D)\<^esub> x*>" \<rightharpoonup> "<*FINSEQ-1K6 x*>"

mtheorem finseq_1_add_7:
  mlet "D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "x be ElementSUBSET-1M1-of D"
"cluster <*FINSEQ-1K6 x*> as-term-is FinSequenceFINSEQ-1M3-of D"
proof
(*coherence*)
  show "<*FINSEQ-1K6 x*> be FinSequenceFINSEQ-1M3-of D"
sorry
qed "sorry"

theorem finseq_1_sch_3:
  fixes Pp1 
  assumes
    A1: "Pp1({}XBOOLE-0K1)" and
   A2: " for p be FinSequenceFINSEQ-1M1 holds  for x be objectHIDDENM1 holds Pp1(p) implies Pp1(p ^FINSEQ-1K8 (<*FINSEQ-1K10 x*>))"
  shows " for p be FinSequenceFINSEQ-1M1 holds Pp1(p)"
sorry

mtheorem finseq_1_th_47:
" for p be FinSequenceFINSEQ-1M1 holds  for q be FinSequenceFINSEQ-1M1 holds  for r be FinSequenceFINSEQ-1M1 holds  for s be FinSequenceFINSEQ-1M1 holds p ^FINSEQ-1K8 q =FUNCT-1R1 r ^FINSEQ-1K8 s & lenFINSEQ-1K4 p <=XXREAL-0R1 lenFINSEQ-1K4 r implies ( ex t be FinSequenceFINSEQ-1M1 st p ^FINSEQ-1K8 t =FUNCT-1R1 r)"
sorry

mtheorem finseq_1_cl_18:
"cluster note-that NATNUMBERSK1 -definedRELAT-1V4 for FinSequenceFINSEQ-1M1"
proof
(*coherence*)
  show " for it be FinSequenceFINSEQ-1M1 holds it be NATNUMBERSK1 -definedRELAT-1V4"
sorry
qed "sorry"

mdef finseq_1_def_11 (" _ * FINSEQ-1K14" [164]164 ) where
  mlet "D be setHIDDENM2"
"func D * FINSEQ-1K14 \<rightarrow> setHIDDENM2 means
  \<lambda>it.  for x be objectHIDDENM1 holds x inHIDDENR3 it iff x be FinSequenceFINSEQ-1M3-of D"
proof-
  (*existence*)
    show " ex it be setHIDDENM2 st  for x be objectHIDDENM1 holds x inHIDDENR3 it iff x be FinSequenceFINSEQ-1M3-of D"
sorry
  (*uniqueness*)
    show " for it1 be setHIDDENM2 holds  for it2 be setHIDDENM2 holds ( for x be objectHIDDENM1 holds x inHIDDENR3 it1 iff x be FinSequenceFINSEQ-1M3-of D) & ( for x be objectHIDDENM1 holds x inHIDDENR3 it2 iff x be FinSequenceFINSEQ-1M3-of D) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mtheorem finseq_1_cl_19:
  mlet "D be setHIDDENM2"
"cluster D * FINSEQ-1K14 as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "D * FINSEQ-1K14 be  non emptyXBOOLE-0V1"
sorry
qed "sorry"

mtheorem finseq_1_th_48:
" for p be FinSequenceFINSEQ-1M1 holds  for q be FinSequenceFINSEQ-1M1 holds (rngFUNCT-1K2 p =XBOOLE-0R4 rngFUNCT-1K2 q & p be one-to-oneFUNCT-1V2) & q be one-to-oneFUNCT-1V2 implies lenFINSEQ-1K4 p =XBOOLE-0R4 lenFINSEQ-1K4 q"
sorry

mtheorem finseq_1_th_49:
" for D be setHIDDENM2 holds {}XBOOLE-0K1 inTARSKIR2 D * FINSEQ-1K14"
sorry

theorem finseq_1_sch_4:
  fixes Df0 Pp1 
  assumes
[ty]: "Df0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
  shows " ex X be setHIDDENM2 st  for x be objectHIDDENM1 holds x inHIDDENR3 X iff ( ex p be FinSequenceFINSEQ-1M1 st (p inTARSKIR2 Df0 * FINSEQ-1K14 & Pp1(p)) & x =HIDDENR1 p)"
sorry

mdef finseq_1_def_12 ("FinSubsequence-likeFINSEQ-1V2" 70 ) where
"attr FinSubsequence-likeFINSEQ-1V2 for FunctionFUNCT-1M1 means
  (\<lambda>IT.  ex k be NatNAT-1M1 st domRELAT-1K1 IT c=TARSKIR1 SegFINSEQ-1K2 k)"..

mtheorem finseq_1_cl_20:
"cluster FinSubsequence-likeFINSEQ-1V2 for FunctionFUNCT-1M1"
proof
(*existence*)
  show " ex it be FunctionFUNCT-1M1 st it be FinSubsequence-likeFINSEQ-1V2"
sorry
qed "sorry"

syntax FINSEQ_1M4 :: "Ty" ("FinSubsequenceFINSEQ-1M4" 70)
translations "FinSubsequenceFINSEQ-1M4" \<rightharpoonup> "FinSubsequence-likeFINSEQ-1V2\<bar>FunctionFUNCT-1M1"

mtheorem finseq_1_cl_21:
"cluster FinSequence-likeFINSEQ-1V1 also-is FinSubsequence-likeFINSEQ-1V2 for FunctionFUNCT-1M1"
proof
(*coherence*)
  show " for it be FunctionFUNCT-1M1 holds it be FinSequence-likeFINSEQ-1V1 implies it be FinSubsequence-likeFINSEQ-1V2"
     sorry
qed "sorry"

mtheorem finseq_1_cl_22:
  mlet "p be FinSubsequenceFINSEQ-1M4", "X be setHIDDENM2"
"cluster p |RELAT-1K8 X as-term-is FinSubsequence-likeFINSEQ-1V2"
proof
(*coherence*)
  show "p |RELAT-1K8 X be FinSubsequence-likeFINSEQ-1V2"
sorry
qed "sorry"

mtheorem finseq_1_cl_23:
  mlet "p be FinSubsequenceFINSEQ-1M4", "X be setHIDDENM2"
"cluster X |`RELAT-1K9 p as-term-is FinSubsequence-likeFINSEQ-1V2"
proof
(*coherence*)
  show "X |`RELAT-1K9 p be FinSubsequence-likeFINSEQ-1V2"
sorry
qed "sorry"

mtheorem finseq_1_cl_24:
"cluster note-that NATNUMBERSK1 -definedRELAT-1V4 for FinSubsequenceFINSEQ-1M4"
proof
(*coherence*)
  show " for it be FinSubsequenceFINSEQ-1M4 holds it be NATNUMBERSK1 -definedRELAT-1V4"
sorry
qed "sorry"

reserve p9 for "FinSubsequenceFINSEQ-1M4"
mdef finseq_1_def_13 ("SgmFINSEQ-1K15  _ " [228]228 ) where
  mlet "X be setHIDDENM2"
"assume  ex k be NatNAT-1M1 st X c=TARSKIR1 SegFINSEQ-1K2 k func SgmFINSEQ-1K15 X \<rightarrow> FinSequenceFINSEQ-1M3-of NATNUMBERSK1 means
  \<lambda>it. rngFUNCT-1K2 it =XBOOLE-0R4 X & ( for l be NatNAT-1M1 holds  for m be NatNAT-1M1 holds  for k1 be NatNAT-1M1 holds  for k2 be NatNAT-1M1 holds (((\<one>\<^sub>M <=XXREAL-0R1 l & l <XXREAL-0R3 m) & m <=XXREAL-0R1 lenFINSEQ-1K4 it) & k1 =XBOOLE-0R4 it .FUNCT-1K1 l) & k2 =XBOOLE-0R4 it .FUNCT-1K1 m implies k1 <XXREAL-0R3 k2)"
proof-
  (*existence*)
    show "( ex k be NatNAT-1M1 st X c=TARSKIR1 SegFINSEQ-1K2 k) implies ( ex it be FinSequenceFINSEQ-1M3-of NATNUMBERSK1 st rngFUNCT-1K2 it =XBOOLE-0R4 X & ( for l be NatNAT-1M1 holds  for m be NatNAT-1M1 holds  for k1 be NatNAT-1M1 holds  for k2 be NatNAT-1M1 holds (((\<one>\<^sub>M <=XXREAL-0R1 l & l <XXREAL-0R3 m) & m <=XXREAL-0R1 lenFINSEQ-1K4 it) & k1 =XBOOLE-0R4 it .FUNCT-1K1 l) & k2 =XBOOLE-0R4 it .FUNCT-1K1 m implies k1 <XXREAL-0R3 k2))"
sorry
  (*uniqueness*)
    show "( ex k be NatNAT-1M1 st X c=TARSKIR1 SegFINSEQ-1K2 k) implies ( for it1 be FinSequenceFINSEQ-1M3-of NATNUMBERSK1 holds  for it2 be FinSequenceFINSEQ-1M3-of NATNUMBERSK1 holds (rngFUNCT-1K2 it1 =XBOOLE-0R4 X & ( for l be NatNAT-1M1 holds  for m be NatNAT-1M1 holds  for k1 be NatNAT-1M1 holds  for k2 be NatNAT-1M1 holds (((\<one>\<^sub>M <=XXREAL-0R1 l & l <XXREAL-0R3 m) & m <=XXREAL-0R1 lenFINSEQ-1K4 it1) & k1 =XBOOLE-0R4 it1 .FUNCT-1K1 l) & k2 =XBOOLE-0R4 it1 .FUNCT-1K1 m implies k1 <XXREAL-0R3 k2)) & (rngFUNCT-1K2 it2 =XBOOLE-0R4 X & ( for l be NatNAT-1M1 holds  for m be NatNAT-1M1 holds  for k1 be NatNAT-1M1 holds  for k2 be NatNAT-1M1 holds (((\<one>\<^sub>M <=XXREAL-0R1 l & l <XXREAL-0R3 m) & m <=XXREAL-0R1 lenFINSEQ-1K4 it2) & k1 =XBOOLE-0R4 it2 .FUNCT-1K1 l) & k2 =XBOOLE-0R4 it2 .FUNCT-1K1 m implies k1 <XXREAL-0R3 k2)) implies it1 =HIDDENR1 it2)"
sorry
qed "sorry"

mtheorem finseq_1_th_50:
" for p9 be FinSubsequenceFINSEQ-1M4 holds rngFUNCT-1K2 (SgmFINSEQ-1K15 (domRELAT-1K1 p9)) =XBOOLE-0R4 domRELAT-1K1 p9"
sorry

mdef finseq_1_def_14 ("SeqFINSEQ-1K16  _ " [228]228 ) where
  mlet "p9 be FinSubsequenceFINSEQ-1M4"
"func SeqFINSEQ-1K16 p9 \<rightarrow> FunctionFUNCT-1M1 equals
  p9 *FUNCT-1K3 SgmFINSEQ-1K15 (domRELAT-1K1 p9)"
proof-
  (*coherence*)
    show "p9 *FUNCT-1K3 SgmFINSEQ-1K15 (domRELAT-1K1 p9) be FunctionFUNCT-1M1"
       sorry
qed "sorry"

mtheorem finseq_1_cl_25:
  mlet "p9 be FinSubsequenceFINSEQ-1M4"
"cluster SeqFINSEQ-1K16 p9 as-term-is FinSequence-likeFINSEQ-1V1"
proof
(*coherence*)
  show "SeqFINSEQ-1K16 p9 be FinSequence-likeFINSEQ-1V1"
sorry
qed "sorry"

mtheorem finseq_1_th_51:
" for X be setHIDDENM2 holds ( ex k be NatNAT-1M1 st X c=TARSKIR1 SegFINSEQ-1K2 k) implies (SgmFINSEQ-1K15 X =FUNCT-1R1 {}XBOOLE-0K1 iff X =XBOOLE-0R4 {}XBOOLE-0K1)"
sorry

(*begin*)
mtheorem finseq_1_th_52:
" for D be setHIDDENM2 holds D be finiteFINSET-1V1 iff ( ex p be FinSequenceFINSEQ-1M1 st D =XBOOLE-0R4 rngFUNCT-1K2 p)"
sorry

(*begin*)
mtheorem finseq_1_th_53:
" for m be NatNAT-1M1 holds  for n be NatNAT-1M1 holds (SegFINSEQ-1K2 n,SegFINSEQ-1K2 m)are-equipotentWELLORD2R2 implies n =XBOOLE-0R4 m"
sorry

mtheorem finseq_1_th_54:
" for n be NatNAT-1M1 holds (SegFINSEQ-1K2 n,n)are-equipotentWELLORD2R2"
  using finseq_1_lm_1 sorry

mtheorem finseq_1_th_55:
" for n be NatNAT-1M1 holds cardCARD-1K4 (SegFINSEQ-1K2 n) =XBOOLE-0R4 cardCARD-1K4 n"
  using finseq_1_lm_1 card_1_th_5 sorry

mtheorem finseq_1_th_56:
" for X be setHIDDENM2 holds X be finiteFINSET-1V1 implies ( ex n be NatNAT-1M1 st (X,SegFINSEQ-1K2 n)are-equipotentWELLORD2R2)"
sorry

mtheorem finseq_1_th_57:
" for n be NatNAT-1M1 holds cardCARD-1K4 (SegFINSEQ-1K2 n) =XBOOLE-0R4 n"
  using finseq_1_lm_1 card_1_def_2 sorry

(*begin*)
mtheorem finseq_1_cl_26:
  mlet "x be objectHIDDENM1"
"cluster <*FINSEQ-1K10 x*> as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "<*FINSEQ-1K10 x*> be  non emptyXBOOLE-0V1"
     sorry
qed "sorry"

mtheorem finseq_1_cl_27:
"cluster  non emptyXBOOLE-0V1 for FinSequenceFINSEQ-1M1"
proof
(*existence*)
  show " ex it be FinSequenceFINSEQ-1M1 st it be  non emptyXBOOLE-0V1"
sorry
qed "sorry"

mtheorem finseq_1_cl_28:
  mlet "f1 be FinSequenceFINSEQ-1M1", "f2 be  non emptyXBOOLE-0V1\<bar>FinSequenceFINSEQ-1M1"
"cluster f1 ^FINSEQ-1K8 f2 as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "f1 ^FINSEQ-1K8 f2 be  non emptyXBOOLE-0V1"
    using finseq_1_th_35 sorry
qed "sorry"

mtheorem finseq_1_cl_29:
  mlet "f1 be FinSequenceFINSEQ-1M1", "f2 be  non emptyXBOOLE-0V1\<bar>FinSequenceFINSEQ-1M1"
"cluster f2 ^FINSEQ-1K8 f1 as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "f2 ^FINSEQ-1K8 f1 be  non emptyXBOOLE-0V1"
    using finseq_1_th_35 sorry
qed "sorry"

mtheorem finseq_1_cl_30:
  mlet "x be objectHIDDENM1", "y be objectHIDDENM1"
"cluster <*FINSEQ-1K11 x,y *> as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "<*FINSEQ-1K11 x,y *> be  non emptyXBOOLE-0V1"
     sorry
qed "sorry"

mtheorem finseq_1_cl_31:
  mlet "x be objectHIDDENM1", "y be objectHIDDENM1", "z be objectHIDDENM1"
"cluster <*FINSEQ-1K12 x,y,z *> as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "<*FINSEQ-1K12 x,y,z *> be  non emptyXBOOLE-0V1"
     sorry
qed "sorry"

theorem finseq_1_sch_5:
  fixes Df0 Af0 Pp2 
  assumes
[ty]: "Df0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
  [ty]: "Af0 be NatNAT-1M1" and
   A1: " for k be NatNAT-1M1 holds k inTARSKIR2 SegFINSEQ-1K2 Af0 implies ( ex x be ElementSUBSET-1M1-of Df0 st Pp2(k,x))"
  shows " ex p be FinSequenceFINSEQ-1M3-of Df0 st domFINSEQ-1K5 p =XBOOLE-0R4 SegFINSEQ-1K2 Af0 & ( for k be NatNAT-1M1 holds k inTARSKIR2 SegFINSEQ-1K2 Af0 implies Pp2(k,p .FUNCT-1K1 k))"
sorry

reserve D for "setHIDDENM2"
reserve p for "FinSequenceFINSEQ-1M3-of D"
reserve m for "NatNAT-1M1"
mdef finseq_1_def_15 (" _ |FINSEQ-1K17  _ " [200,200]200 ) where
  mlet "m be NatNAT-1M1", "p be FinSequenceFINSEQ-1M1"
"func p |FINSEQ-1K17 m \<rightarrow> FinSequenceFINSEQ-1M1 equals
  p |RELAT-1K8 SegFINSEQ-1K2 m"
proof-
  (*coherence*)
    show "p |RELAT-1K8 SegFINSEQ-1K2 m be FinSequenceFINSEQ-1M1"
      using finseq_1_th_15 sorry
qed "sorry"

syntax FINSEQ_1K18 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ |FINSEQ-1K18\<^bsub>'( _ ')\<^esub>  _ " [200,0,200]200)
translations "p |FINSEQ-1K18\<^bsub>(D)\<^esub> m" \<rightharpoonup> "p |FINSEQ-1K17 m"

mtheorem finseq_1_add_8:
  mlet "D be setHIDDENM2", "m be NatNAT-1M1", "p be FinSequenceFINSEQ-1M3-of D"
"cluster p |FINSEQ-1K17 m as-term-is FinSequenceFINSEQ-1M3-of D"
proof
(*coherence*)
  show "p |FINSEQ-1K17 m be FinSequenceFINSEQ-1M3-of D"
    using finseq_1_th_18 sorry
qed "sorry"

mtheorem finseq_1_cl_32:
  mlet "f be FinSequenceFINSEQ-1M1"
"cluster f |FINSEQ-1K17 (0NUMBERSK6) as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "f |FINSEQ-1K17 (0NUMBERSK6) be emptyXBOOLE-0V1"
     sorry
qed "sorry"

mtheorem finseq_1_th_58:
" for i be NatNAT-1M1 holds  for q be FinSequenceFINSEQ-1M1 holds lenFINSEQ-1K4 q <=XXREAL-0R1 i implies q |FINSEQ-1K17 i =FUNCT-1R1 q"
sorry

mtheorem finseq_1_th_59:
" for i be NatNAT-1M1 holds  for q be FinSequenceFINSEQ-1M1 holds i <=XXREAL-0R1 lenFINSEQ-1K4 q implies lenFINSEQ-1K4 (q |FINSEQ-1K17 i) =XBOOLE-0R4 i"
sorry

mtheorem finseq_1_th_60:
" for n be NatNAT-1M1 holds  for i be NatNAT-1M1 holds  for m be NatNAT-1M1 holds i inTARSKIR2 SegFINSEQ-1K2 n implies i +XCMPLX-0K2 m inTARSKIR2 SegFINSEQ-1K2 (n +XCMPLX-0K2 m)"
sorry

mtheorem finseq_1_th_61:
" for n be NatNAT-1M1 holds  for i be NatNAT-1M1 holds  for m be NatNAT-1M1 holds i >XXREAL-0R4 0NUMBERSK6 & i +XCMPLX-0K2 m inTARSKIR2 SegFINSEQ-1K2 (n +XCMPLX-0K2 m) implies i inTARSKIR2 SegFINSEQ-1K2 n & i inTARSKIR2 SegFINSEQ-1K2 (n +XCMPLX-0K2 m)"
sorry

mdef finseq_1_def_16 (" _ [*]FINSEQ-1K19" [164]164 ) where
  mlet "R be RelationRELAT-1M1"
"func R [*]FINSEQ-1K19 \<rightarrow> RelationRELAT-1M1 means
  \<lambda>it.  for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds [TARSKIK4 x,y ] inHIDDENR3 it iff (x inHIDDENR3 fieldRELAT-1K3 R & y inHIDDENR3 fieldRELAT-1K3 R) & ( ex p be FinSequenceFINSEQ-1M1 st ((lenFINSEQ-1K4 p >=XXREAL-0R2 \<one>\<^sub>M & p .FUNCT-1K1 \<one>\<^sub>M =HIDDENR1 x) & p .FUNCT-1K1 lenFINSEQ-1K4 p =HIDDENR1 y) & ( for i be NatNAT-1M1 holds i >=XXREAL-0R2 \<one>\<^sub>M & i <XXREAL-0R3 lenFINSEQ-1K4 p implies [TARSKIK4 p .FUNCT-1K1 i,p .FUNCT-1K1 (i +NAT-1K1 \<one>\<^sub>M) ] inHIDDENR3 R))"
proof-
  (*existence*)
    show " ex it be RelationRELAT-1M1 st  for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds [TARSKIK4 x,y ] inHIDDENR3 it iff (x inHIDDENR3 fieldRELAT-1K3 R & y inHIDDENR3 fieldRELAT-1K3 R) & ( ex p be FinSequenceFINSEQ-1M1 st ((lenFINSEQ-1K4 p >=XXREAL-0R2 \<one>\<^sub>M & p .FUNCT-1K1 \<one>\<^sub>M =HIDDENR1 x) & p .FUNCT-1K1 lenFINSEQ-1K4 p =HIDDENR1 y) & ( for i be NatNAT-1M1 holds i >=XXREAL-0R2 \<one>\<^sub>M & i <XXREAL-0R3 lenFINSEQ-1K4 p implies [TARSKIK4 p .FUNCT-1K1 i,p .FUNCT-1K1 (i +NAT-1K1 \<one>\<^sub>M) ] inHIDDENR3 R))"
sorry
  (*uniqueness*)
    show " for it1 be RelationRELAT-1M1 holds  for it2 be RelationRELAT-1M1 holds ( for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds [TARSKIK4 x,y ] inHIDDENR3 it1 iff (x inHIDDENR3 fieldRELAT-1K3 R & y inHIDDENR3 fieldRELAT-1K3 R) & ( ex p be FinSequenceFINSEQ-1M1 st ((lenFINSEQ-1K4 p >=XXREAL-0R2 \<one>\<^sub>M & p .FUNCT-1K1 \<one>\<^sub>M =HIDDENR1 x) & p .FUNCT-1K1 lenFINSEQ-1K4 p =HIDDENR1 y) & ( for i be NatNAT-1M1 holds i >=XXREAL-0R2 \<one>\<^sub>M & i <XXREAL-0R3 lenFINSEQ-1K4 p implies [TARSKIK4 p .FUNCT-1K1 i,p .FUNCT-1K1 (i +NAT-1K1 \<one>\<^sub>M) ] inHIDDENR3 R))) & ( for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds [TARSKIK4 x,y ] inHIDDENR3 it2 iff (x inHIDDENR3 fieldRELAT-1K3 R & y inHIDDENR3 fieldRELAT-1K3 R) & ( ex p be FinSequenceFINSEQ-1M1 st ((lenFINSEQ-1K4 p >=XXREAL-0R2 \<one>\<^sub>M & p .FUNCT-1K1 \<one>\<^sub>M =HIDDENR1 x) & p .FUNCT-1K1 lenFINSEQ-1K4 p =HIDDENR1 y) & ( for i be NatNAT-1M1 holds i >=XXREAL-0R2 \<one>\<^sub>M & i <XXREAL-0R3 lenFINSEQ-1K4 p implies [TARSKIK4 p .FUNCT-1K1 i,p .FUNCT-1K1 (i +NAT-1K1 \<one>\<^sub>M) ] inHIDDENR3 R))) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mtheorem finseq_1_th_62:
" for D1 be setHIDDENM2 holds  for D2 be setHIDDENM2 holds D1 c=TARSKIR1 D2 implies D1 * FINSEQ-1K14 c=TARSKIR1 D2 * FINSEQ-1K14"
sorry

mtheorem finseq_1_cl_33:
  mlet "D be setHIDDENM2"
"cluster D * FINSEQ-1K14 as-term-is functionalFUNCT-1V6"
proof
(*coherence*)
  show "D * FINSEQ-1K14 be functionalFUNCT-1V6"
    using finseq_1_def_11 sorry
qed "sorry"

mtheorem finseq_1_th_63:
" for p be FinSequenceFINSEQ-1M1 holds  for q be FinSequenceFINSEQ-1M1 holds p c=RELAT-1R2 q implies lenFINSEQ-1K4 p <=XXREAL-0R1 lenFINSEQ-1K4 q"
sorry

mtheorem finseq_1_th_64:
" for p be FinSequenceFINSEQ-1M1 holds  for q be FinSequenceFINSEQ-1M1 holds  for i be NatNAT-1M1 holds \<one>\<^sub>M <=XXREAL-0R1 i & i <=XXREAL-0R1 lenFINSEQ-1K4 p implies (p ^FINSEQ-1K8 q).FUNCT-1K1 i =XBOOLE-0R4 p .FUNCT-1K1 i"
sorry

mtheorem finseq_1_th_65:
" for p be FinSequenceFINSEQ-1M1 holds  for q be FinSequenceFINSEQ-1M1 holds  for i be NatNAT-1M1 holds \<one>\<^sub>M <=XXREAL-0R1 i & i <=XXREAL-0R1 lenFINSEQ-1K4 q implies (p ^FINSEQ-1K8 q).FUNCT-1K1 (lenFINSEQ-1K4 p +XCMPLX-0K2 i) =XBOOLE-0R4 q .FUNCT-1K1 i"
sorry

theorem finseq_1_sch_6:
  fixes nf0 Ff1 Pp1 
  assumes
[ty]: "nf0 be NatNAT-1M1" and
  [ty_func]: "\<And> x1. x1 be setHIDDENM2 \<Longrightarrow> Ff1(x1) be setHIDDENM2"
  shows "{Ff1(i) where i be NatNAT-1M1 : i <=XXREAL-0R1 nf0 & Pp1(i) } be finiteFINSET-1V1"
sorry

mlemma finseq_1_lm_5:
" for n be NatNAT-1M1 holds  for x be objectHIDDENM1 holds x inHIDDENR3 SegFINSEQ-1K2 n implies ( ex VarFor3 be setHIDDENM2 st (\<one>\<^sub>M <=XXREAL-0R1 VarFor3 & VarFor3 <=XXREAL-0R1 n) & x =HIDDENR1 VarFor3)"
sorry

mtheorem finseq_1_th_66:
" for x1 be setHIDDENM2 holds  for x2 be setHIDDENM2 holds  for x3 be setHIDDENM2 holds  for x4 be setHIDDENM2 holds  for p be FinSequenceFINSEQ-1M1 holds p =FUNCT-1R1 (((<*FINSEQ-1K10 x1*>)^FINSEQ-1K8 (<*FINSEQ-1K10 x2*>))^FINSEQ-1K8 (<*FINSEQ-1K10 x3*>))^FINSEQ-1K8 (<*FINSEQ-1K10 x4*>) implies (((lenFINSEQ-1K4 p =XBOOLE-0R4 \<four>\<^sub>M & p .FUNCT-1K1 \<one>\<^sub>M =XBOOLE-0R4 x1) & p .FUNCT-1K1 \<two>\<^sub>M =XBOOLE-0R4 x2) & p .FUNCT-1K1 \<three>\<^sub>M =XBOOLE-0R4 x3) & p .FUNCT-1K1 \<four>\<^sub>M =XBOOLE-0R4 x4"
sorry

mtheorem finseq_1_th_67:
" for x1 be setHIDDENM2 holds  for x2 be setHIDDENM2 holds  for x3 be setHIDDENM2 holds  for x4 be setHIDDENM2 holds  for x5 be setHIDDENM2 holds  for p be FinSequenceFINSEQ-1M1 holds p =FUNCT-1R1 ((((<*FINSEQ-1K10 x1*>)^FINSEQ-1K8 (<*FINSEQ-1K10 x2*>))^FINSEQ-1K8 (<*FINSEQ-1K10 x3*>))^FINSEQ-1K8 (<*FINSEQ-1K10 x4*>))^FINSEQ-1K8 (<*FINSEQ-1K10 x5*>) implies ((((lenFINSEQ-1K4 p =XBOOLE-0R4 \<five>\<^sub>M & p .FUNCT-1K1 \<one>\<^sub>M =XBOOLE-0R4 x1) & p .FUNCT-1K1 \<two>\<^sub>M =XBOOLE-0R4 x2) & p .FUNCT-1K1 \<three>\<^sub>M =XBOOLE-0R4 x3) & p .FUNCT-1K1 \<four>\<^sub>M =XBOOLE-0R4 x4) & p .FUNCT-1K1 \<five>\<^sub>M =XBOOLE-0R4 x5"
sorry

mtheorem finseq_1_th_68:
" for x1 be setHIDDENM2 holds  for x2 be setHIDDENM2 holds  for x3 be setHIDDENM2 holds  for x4 be setHIDDENM2 holds  for x5 be setHIDDENM2 holds  for x6 be setHIDDENM2 holds  for p be FinSequenceFINSEQ-1M1 holds p =FUNCT-1R1 (((((<*FINSEQ-1K10 x1*>)^FINSEQ-1K8 (<*FINSEQ-1K10 x2*>))^FINSEQ-1K8 (<*FINSEQ-1K10 x3*>))^FINSEQ-1K8 (<*FINSEQ-1K10 x4*>))^FINSEQ-1K8 (<*FINSEQ-1K10 x5*>))^FINSEQ-1K8 (<*FINSEQ-1K10 x6*>) implies (((((lenFINSEQ-1K4 p =XBOOLE-0R4 \<six>\<^sub>M & p .FUNCT-1K1 \<one>\<^sub>M =XBOOLE-0R4 x1) & p .FUNCT-1K1 \<two>\<^sub>M =XBOOLE-0R4 x2) & p .FUNCT-1K1 \<three>\<^sub>M =XBOOLE-0R4 x3) & p .FUNCT-1K1 \<four>\<^sub>M =XBOOLE-0R4 x4) & p .FUNCT-1K1 \<five>\<^sub>M =XBOOLE-0R4 x5) & p .FUNCT-1K1 \<six>\<^sub>M =XBOOLE-0R4 x6"
sorry

mtheorem finseq_1_th_69:
" for x1 be setHIDDENM2 holds  for x2 be setHIDDENM2 holds  for x3 be setHIDDENM2 holds  for x4 be setHIDDENM2 holds  for x5 be setHIDDENM2 holds  for x6 be setHIDDENM2 holds  for x7 be setHIDDENM2 holds  for p be FinSequenceFINSEQ-1M1 holds p =FUNCT-1R1 ((((((<*FINSEQ-1K10 x1*>)^FINSEQ-1K8 (<*FINSEQ-1K10 x2*>))^FINSEQ-1K8 (<*FINSEQ-1K10 x3*>))^FINSEQ-1K8 (<*FINSEQ-1K10 x4*>))^FINSEQ-1K8 (<*FINSEQ-1K10 x5*>))^FINSEQ-1K8 (<*FINSEQ-1K10 x6*>))^FINSEQ-1K8 (<*FINSEQ-1K10 x7*>) implies ((((((lenFINSEQ-1K4 p =XBOOLE-0R4 \<seven>\<^sub>M & p .FUNCT-1K1 \<one>\<^sub>M =XBOOLE-0R4 x1) & p .FUNCT-1K1 \<two>\<^sub>M =XBOOLE-0R4 x2) & p .FUNCT-1K1 \<three>\<^sub>M =XBOOLE-0R4 x3) & p .FUNCT-1K1 \<four>\<^sub>M =XBOOLE-0R4 x4) & p .FUNCT-1K1 \<five>\<^sub>M =XBOOLE-0R4 x5) & p .FUNCT-1K1 \<six>\<^sub>M =XBOOLE-0R4 x6) & p .FUNCT-1K1 \<seven>\<^sub>M =XBOOLE-0R4 x7"
sorry

mtheorem finseq_1_th_70:
" for x1 be setHIDDENM2 holds  for x2 be setHIDDENM2 holds  for x3 be setHIDDENM2 holds  for x4 be setHIDDENM2 holds  for x5 be setHIDDENM2 holds  for x6 be setHIDDENM2 holds  for x7 be setHIDDENM2 holds  for x8 be setHIDDENM2 holds  for p be FinSequenceFINSEQ-1M1 holds p =FUNCT-1R1 (((((((<*FINSEQ-1K10 x1*>)^FINSEQ-1K8 (<*FINSEQ-1K10 x2*>))^FINSEQ-1K8 (<*FINSEQ-1K10 x3*>))^FINSEQ-1K8 (<*FINSEQ-1K10 x4*>))^FINSEQ-1K8 (<*FINSEQ-1K10 x5*>))^FINSEQ-1K8 (<*FINSEQ-1K10 x6*>))^FINSEQ-1K8 (<*FINSEQ-1K10 x7*>))^FINSEQ-1K8 (<*FINSEQ-1K10 x8*>) implies (((((((lenFINSEQ-1K4 p =XBOOLE-0R4 \<eight>\<^sub>M & p .FUNCT-1K1 \<one>\<^sub>M =XBOOLE-0R4 x1) & p .FUNCT-1K1 \<two>\<^sub>M =XBOOLE-0R4 x2) & p .FUNCT-1K1 \<three>\<^sub>M =XBOOLE-0R4 x3) & p .FUNCT-1K1 \<four>\<^sub>M =XBOOLE-0R4 x4) & p .FUNCT-1K1 \<five>\<^sub>M =XBOOLE-0R4 x5) & p .FUNCT-1K1 \<six>\<^sub>M =XBOOLE-0R4 x6) & p .FUNCT-1K1 \<seven>\<^sub>M =XBOOLE-0R4 x7) & p .FUNCT-1K1 \<eight>\<^sub>M =XBOOLE-0R4 x8"
sorry

mtheorem finseq_1_th_71:
" for x1 be setHIDDENM2 holds  for x2 be setHIDDENM2 holds  for x3 be setHIDDENM2 holds  for x4 be setHIDDENM2 holds  for x5 be setHIDDENM2 holds  for x6 be setHIDDENM2 holds  for x7 be setHIDDENM2 holds  for x8 be setHIDDENM2 holds  for x9 be setHIDDENM2 holds  for p be FinSequenceFINSEQ-1M1 holds p =FUNCT-1R1 ((((((((<*FINSEQ-1K10 x1*>)^FINSEQ-1K8 (<*FINSEQ-1K10 x2*>))^FINSEQ-1K8 (<*FINSEQ-1K10 x3*>))^FINSEQ-1K8 (<*FINSEQ-1K10 x4*>))^FINSEQ-1K8 (<*FINSEQ-1K10 x5*>))^FINSEQ-1K8 (<*FINSEQ-1K10 x6*>))^FINSEQ-1K8 (<*FINSEQ-1K10 x7*>))^FINSEQ-1K8 (<*FINSEQ-1K10 x8*>))^FINSEQ-1K8 (<*FINSEQ-1K10 x9*>) implies ((((((((lenFINSEQ-1K4 p =XBOOLE-0R4 \<nine>\<^sub>M & p .FUNCT-1K1 \<one>\<^sub>M =XBOOLE-0R4 x1) & p .FUNCT-1K1 \<two>\<^sub>M =XBOOLE-0R4 x2) & p .FUNCT-1K1 \<three>\<^sub>M =XBOOLE-0R4 x3) & p .FUNCT-1K1 \<four>\<^sub>M =XBOOLE-0R4 x4) & p .FUNCT-1K1 \<five>\<^sub>M =XBOOLE-0R4 x5) & p .FUNCT-1K1 \<six>\<^sub>M =XBOOLE-0R4 x6) & p .FUNCT-1K1 \<seven>\<^sub>M =XBOOLE-0R4 x7) & p .FUNCT-1K1 \<eight>\<^sub>M =XBOOLE-0R4 x8) & p .FUNCT-1K1 \<nine>\<^sub>M =XBOOLE-0R4 x9"
sorry

mtheorem finseq_1_th_72:
" for p be FinSequenceFINSEQ-1M1 holds p |FINSEQ-1K17 SegFINSEQ-1K2 (0NUMBERSK6) =FUNCT-1R1 {}XBOOLE-0K1"
   sorry

mtheorem finseq_1_th_73:
" for f be FinSequenceFINSEQ-1M1 holds  for g be FinSequenceFINSEQ-1M1 holds f |FINSEQ-1K17 SegFINSEQ-1K2 (0NUMBERSK6) =FUNCT-1R1 g |FINSEQ-1K17 SegFINSEQ-1K2 (0NUMBERSK6)"
   sorry

mtheorem finseq_1_th_74:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for x be ElementSUBSET-1M1-of D holds <*FINSEQ-1K13\<^bsub>(D)\<^esub> x*> be FinSequenceFINSEQ-1M3-of D"
   sorry

mtheorem finseq_1_th_75:
" for D be setHIDDENM2 holds  for p be FinSequenceFINSEQ-1M3-of D holds  for q be FinSequenceFINSEQ-1M3-of D holds p ^FINSEQ-1K9\<^bsub>(D)\<^esub> q be FinSequenceFINSEQ-1M3-of D"
   sorry

reserve a, b, c, d, e, f for "objectHIDDENM1"
mtheorem finseq_1_th_76:
" for a be objectHIDDENM1 holds  for b be objectHIDDENM1 holds <*FINSEQ-1K10 a*> =FUNCT-1R1 <*FINSEQ-1K10 b*> implies a =HIDDENR1 b"
sorry

mtheorem finseq_1_th_77:
" for a be objectHIDDENM1 holds  for b be objectHIDDENM1 holds  for c be objectHIDDENM1 holds  for d be objectHIDDENM1 holds <*FINSEQ-1K11 a,b *> =FUNCT-1R1 <*FINSEQ-1K11 c,d *> implies a =HIDDENR1 c & b =HIDDENR1 d"
sorry

mtheorem finseq_1_th_78:
" for a be objectHIDDENM1 holds  for b be objectHIDDENM1 holds  for c be objectHIDDENM1 holds  for d be objectHIDDENM1 holds  for e be objectHIDDENM1 holds  for f be objectHIDDENM1 holds <*FINSEQ-1K12 a,b,c *> =FUNCT-1R1 <*FINSEQ-1K12 d,e,f *> implies (a =HIDDENR1 d & b =HIDDENR1 e) & c =HIDDENR1 f"
sorry

mtheorem finseq_1_cl_34:
"cluster  non emptyXBOOLE-0V1\<bar>non-emptyFUNCT-1V4 for FinSequenceFINSEQ-1M1"
proof
(*existence*)
  show " ex it be FinSequenceFINSEQ-1M1 st it be  non emptyXBOOLE-0V1\<bar>non-emptyFUNCT-1V4"
sorry
qed "sorry"

mtheorem finseq_1_th_79:
" for n be NatNAT-1M1 holds  for p be FinSequenceFINSEQ-1M1 holds  for q be FinSequenceFINSEQ-1M1 holds q =FUNCT-1R1 p |RELAT-1K8 SegFINSEQ-1K2 n implies lenFINSEQ-1K4 q <=XXREAL-0R1 lenFINSEQ-1K4 p"
sorry

mtheorem finseq_1_th_80:
" for n be NatNAT-1M1 holds  for p be FinSequenceFINSEQ-1M1 holds  for r be FinSequenceFINSEQ-1M1 holds r =FUNCT-1R1 p |RELAT-1K8 SegFINSEQ-1K2 n implies ( ex q be FinSequenceFINSEQ-1M1 st p =FUNCT-1R1 r ^FINSEQ-1K8 q)"
sorry

mtheorem finseq_1_cl_35:
  mlet "D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster  non emptyXBOOLE-0V1 for FinSequenceFINSEQ-1M3-of D"
proof
(*existence*)
  show " ex it be FinSequenceFINSEQ-1M3-of D st it be  non emptyXBOOLE-0V1"
sorry
qed "sorry"

abbreviation(input) FINSEQ_1R1(" _ =FINSEQ-1R1  _ " [50,50]50) where
  "p =FINSEQ-1R1 q \<equiv> p =HIDDENR1 q"

mtheorem finseq_1_def_17:
  mlet "p be FinSequenceFINSEQ-1M1", "q be FinSequenceFINSEQ-1M1"
"redefine pred p =FINSEQ-1R1 q means
  lenFINSEQ-1K4 p =XBOOLE-0R4 lenFINSEQ-1K4 q & ( for k be NatNAT-1M1 holds \<one>\<^sub>M <=XXREAL-0R1 k & k <=XXREAL-0R1 lenFINSEQ-1K4 p implies p .FUNCT-1K1 k =XBOOLE-0R4 q .FUNCT-1K1 k)"
proof
(*compatibility*)
  show "p =FINSEQ-1R1 q iff lenFINSEQ-1K4 p =XBOOLE-0R4 lenFINSEQ-1K4 q & ( for k be NatNAT-1M1 holds \<one>\<^sub>M <=XXREAL-0R1 k & k <=XXREAL-0R1 lenFINSEQ-1K4 p implies p .FUNCT-1K1 k =XBOOLE-0R4 q .FUNCT-1K1 k)"
    using finseq_1_th_14 sorry
qed "sorry"

mtheorem finseq_1_th_81:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for z be objectHIDDENM1 holds (\<one>\<^sub>M inTARSKIR2 domFINSEQ-1K5 (<*FINSEQ-1K12 x,y,z *>) & \<two>\<^sub>M inTARSKIR2 domFINSEQ-1K5 (<*FINSEQ-1K12 x,y,z *>)) & \<three>\<^sub>M inTARSKIR2 domFINSEQ-1K5 (<*FINSEQ-1K12 x,y,z *>)"
sorry

mtheorem finseq_1_th_82:
" for p be FinSequenceFINSEQ-1M1 holds  for n be NatNAT-1M1 holds  for m be NatNAT-1M1 holds m <=XXREAL-0R1 n implies (p |FINSEQ-1K17 n)|FINSEQ-1K17 m =FINSEQ-1R1 p |FINSEQ-1K17 m"
  using finseq_1_th_5 relat_1_th_74 sorry

reserve m for "NatNAT-1M1"
mtheorem finseq_1_th_83:
" for n be NatNAT-1M1 holds SegFINSEQ-1K2 n =XBOOLE-0R4 (n +NAT-1K1 \<one>\<^sub>M)\\SUBSET-1K6 {TARSKIK1 0NUMBERSK6 }"
sorry

mtheorem finseq_1_cl_36:
  mlet "n be naturalORDINAL1V7\<bar>NumberORDINAL1M1"
"cluster n -elementCARD-1V3 for FinSequenceFINSEQ-1M1"
proof
(*existence*)
  show " ex it be FinSequenceFINSEQ-1M1 st it be n -elementCARD-1V3"
sorry
qed "sorry"

mtheorem finseq_1_cl_37:
  mlet "x be objectHIDDENM1"
"cluster <*FINSEQ-1K10 x*> as-term-is \<one>\<^sub>M -elementCARD-1V3"
proof
(*coherence*)
  show "<*FINSEQ-1K10 x*> be \<one>\<^sub>M -elementCARD-1V3"
     sorry
qed "sorry"

mtheorem finseq_1_cl_38:
  mlet "x be objectHIDDENM1", "y be objectHIDDENM1"
"cluster <*FINSEQ-1K11 x,y *> as-term-is \<two>\<^sub>M -elementCARD-1V3"
proof
(*coherence*)
  show "<*FINSEQ-1K11 x,y *> be \<two>\<^sub>M -elementCARD-1V3"
    using finseq_1_th_44 sorry
qed "sorry"

mtheorem finseq_1_cl_39:
  mlet "x be objectHIDDENM1", "y be objectHIDDENM1", "z be objectHIDDENM1"
"cluster <*FINSEQ-1K12 x,y,z *> as-term-is \<three>\<^sub>M -elementCARD-1V3"
proof
(*coherence*)
  show "<*FINSEQ-1K12 x,y,z *> be \<three>\<^sub>M -elementCARD-1V3"
    using finseq_1_th_45 sorry
qed "sorry"

mdef finseq_1_def_18 ("FinSequence-memberedFINSEQ-1V3" 70 ) where
"attr FinSequence-memberedFINSEQ-1V3 for setHIDDENM2 means
  (\<lambda>X.  for x be objectHIDDENM1 holds x inHIDDENR3 X implies x be FinSequenceFINSEQ-1M1)"..

mtheorem finseq_1_cl_40:
"cluster emptyXBOOLE-0V1 also-is FinSequence-memberedFINSEQ-1V3 for setHIDDENM2"
proof
(*coherence*)
  show " for it be setHIDDENM2 holds it be emptyXBOOLE-0V1 implies it be FinSequence-memberedFINSEQ-1V3"
     sorry
qed "sorry"

mtheorem finseq_1_cl_41:
"cluster  non emptyXBOOLE-0V1\<bar>FinSequence-memberedFINSEQ-1V3 for setHIDDENM2"
proof
(*existence*)
  show " ex it be setHIDDENM2 st it be  non emptyXBOOLE-0V1\<bar>FinSequence-memberedFINSEQ-1V3"
sorry
qed "sorry"

mtheorem finseq_1_cl_42:
  mlet "X be setHIDDENM2"
"cluster X * FINSEQ-1K14 as-term-is FinSequence-memberedFINSEQ-1V3"
proof
(*coherence*)
  show "X * FINSEQ-1K14 be FinSequence-memberedFINSEQ-1V3"
    using finseq_1_def_11 sorry
qed "sorry"

mtheorem finseq_1_th_84:
" for x be objectHIDDENM1 holds  for D be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds f inTARSKIR2 D * FINSEQ-1K14 & x inHIDDENR3 domRELAT-1K1 f implies f .FUNCT-1K1 x inTARSKIR2 D"
sorry

mtheorem finseq_1_cl_43:
"cluster FinSequence-memberedFINSEQ-1V3 also-is functionalFUNCT-1V6 for setHIDDENM2"
proof
(*coherence*)
  show " for it be setHIDDENM2 holds it be FinSequence-memberedFINSEQ-1V3 implies it be functionalFUNCT-1V6"
     sorry
qed "sorry"

mtheorem finseq_1_th_85:
" for X be FinSequence-memberedFINSEQ-1V3\<bar>setHIDDENM2 holds  ex Y be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 st X c=TARSKIR1 Y * FINSEQ-1K14"
sorry

mtheorem finseq_1_cl_44:
  mlet "X be FinSequence-memberedFINSEQ-1V3\<bar>setHIDDENM2"
"cluster note-that FinSequence-likeFINSEQ-1V1 for ElementSUBSET-1M1-of X"
proof
(*coherence*)
  show " for it be ElementSUBSET-1M1-of X holds it be FinSequence-likeFINSEQ-1V1"
sorry
qed "sorry"

mtheorem finseq_1_cl_45:
  mlet "X be FinSequence-memberedFINSEQ-1V3\<bar>setHIDDENM2"
"cluster note-that FinSequence-memberedFINSEQ-1V3 for SubsetSUBSET-1M2-of X"
proof
(*coherence*)
  show " for it be SubsetSUBSET-1M2-of X holds it be FinSequence-memberedFINSEQ-1V3"
     sorry
qed "sorry"

mtheorem finseq_1_th_86:
" for n be NatNAT-1M1 holds  for p be FinSequenceFINSEQ-1M1 holds  for q be FinSequenceFINSEQ-1M1 holds q =FUNCT-1R1 p |RELAT-1K8 SegFINSEQ-1K2 n implies lenFINSEQ-1K4 q <=XXREAL-0R1 n"
sorry

mtheorem finseq_1_th_87:
" for p be FinSequenceFINSEQ-1M1 holds  for q be FinSequenceFINSEQ-1M1 holds p =FINSEQ-1R1 p ^FINSEQ-1K8 q or p =FINSEQ-1R1 q ^FINSEQ-1K8 p implies q =FINSEQ-1R1 {}XBOOLE-0K1"
sorry

mtheorem finseq_1_th_88:
" for x be objectHIDDENM1 holds  for p be FinSequenceFINSEQ-1M1 holds  for q be FinSequenceFINSEQ-1M1 holds p ^FINSEQ-1K8 q =FINSEQ-1R1 <*FINSEQ-1K10 x*> implies p =FINSEQ-1R1 <*FINSEQ-1K10 x*> & q =FINSEQ-1R1 {}XBOOLE-0K1 or p =FINSEQ-1R1 {}XBOOLE-0K1 & q =FINSEQ-1R1 <*FINSEQ-1K10 x*>"
sorry

mtheorem finseq_1_th_89:
" for n be NatNAT-1M1 holds  for f be n -elementCARD-1V3\<bar>FinSequenceFINSEQ-1M1 holds domFINSEQ-1K5 f =XBOOLE-0R4 SegFINSEQ-1K2 n"
sorry

mtheorem finseq_1_cl_46:
  mlet "n be naturalORDINAL1V7\<bar>NumberORDINAL1M1", "m be naturalORDINAL1V7\<bar>NumberORDINAL1M1", "f be n -elementCARD-1V3\<bar>FinSequenceFINSEQ-1M1", "g be m -elementCARD-1V3\<bar>FinSequenceFINSEQ-1M1"
"cluster f ^FINSEQ-1K8 g as-term-is n +XCMPLX-0K2 m -elementCARD-1V3"
proof
(*coherence*)
  show "f ^FINSEQ-1K8 g be n +XCMPLX-0K2 m -elementCARD-1V3"
sorry
qed "sorry"

mtheorem finseq_1_cl_47:
"cluster increasingVALUED-0V9 also-is one-to-oneFUNCT-1V2 for real-valuedVALUED-0V7\<bar>FinSequenceFINSEQ-1M1"
proof
(*coherence*)
  show " for it be real-valuedVALUED-0V7\<bar>FinSequenceFINSEQ-1M1 holds it be increasingVALUED-0V9 implies it be one-to-oneFUNCT-1V2"
sorry
qed "sorry"

mtheorem finseq_1_th_90:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds x inHIDDENR3 domFINSEQ-1K5 (<*FINSEQ-1K10 y*>) implies x =HIDDENR1 \<one>\<^sub>M"
sorry

mtheorem finseq_1_cl_48:
  mlet "X be setHIDDENM2"
"cluster X -valuedRELAT-1V5 for FinSequenceFINSEQ-1M1"
proof
(*existence*)
  show " ex it be FinSequenceFINSEQ-1M1 st it be X -valuedRELAT-1V5"
sorry
qed "sorry"

mtheorem finseq_1_cl_49:
  mlet "D be FinSequence-memberedFINSEQ-1V3\<bar>setHIDDENM2", "f be D -valuedRELAT-1V5\<bar>FunctionFUNCT-1M1", "x be objectHIDDENM1"
"cluster f .FUNCT-1K1 x as-term-is FinSequence-likeFINSEQ-1V1"
proof
(*coherence*)
  show "f .FUNCT-1K1 x be FinSequence-likeFINSEQ-1V1"
sorry
qed "sorry"

mtheorem finseq_1_th_91:
" for n be NatNAT-1M1 holds  for x be objectHIDDENM1 holds x inHIDDENR3 SegFINSEQ-1K2 n implies ( ex VarFor3 be setHIDDENM2 st (\<one>\<^sub>M <=XXREAL-0R1 VarFor3 & VarFor3 <=XXREAL-0R1 n) & x =HIDDENR1 VarFor3)"
  using finseq_1_lm_5 sorry

mtheorem finseq_1_th_92:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds domFINSEQ-1K5 (<*FINSEQ-1K11 x,y *>) =XBOOLE-0R4 {TARSKIK2 \<one>\<^sub>M,\<two>\<^sub>M }"
sorry

(*begin*)
mtheorem finseq_1_cl_50:
  mlet "A be finiteFINSET-1V1\<bar>setHIDDENM2"
"cluster ontoFUNCT-2V2\<^bsub>(A)\<^esub>\<bar>one-to-oneFUNCT-1V2 for FinSequenceFINSEQ-1M3-of A"
proof
(*existence*)
  show " ex it be FinSequenceFINSEQ-1M3-of A st it be ontoFUNCT-2V2\<^bsub>(A)\<^esub>\<bar>one-to-oneFUNCT-1V2"
sorry
qed "sorry"

mdef finseq_1_def_19 ("canFSFINSEQ-1K20  _ " [164]164 ) where
  mlet "A be finiteFINSET-1V1\<bar>setHIDDENM2"
"func canFSFINSEQ-1K20 A \<rightarrow> FinSequenceFINSEQ-1M1 equals
  the one-to-oneFUNCT-1V2\<bar>ontoFUNCT-2V2\<^bsub>(A)\<^esub>\<bar>FinSequenceFINSEQ-1M3-of A"
proof-
  (*coherence*)
    show "the one-to-oneFUNCT-1V2\<bar>ontoFUNCT-2V2\<^bsub>(A)\<^esub>\<bar>FinSequenceFINSEQ-1M3-of A be FinSequenceFINSEQ-1M1"
       sorry
qed "sorry"

abbreviation(input) FINSEQ_1K21("canFSFINSEQ-1K21  _ " [164]164) where
  "canFSFINSEQ-1K21 A \<equiv> canFSFINSEQ-1K20 A"

mtheorem finseq_1_add_9:
  mlet "A be finiteFINSET-1V1\<bar>setHIDDENM2"
"cluster canFSFINSEQ-1K20 A as-term-is FinSequenceFINSEQ-1M3-of A"
proof
(*coherence*)
  show "canFSFINSEQ-1K20 A be FinSequenceFINSEQ-1M3-of A"
     sorry
qed "sorry"

mtheorem finseq_1_cl_51:
  mlet "A be finiteFINSET-1V1\<bar>setHIDDENM2"
"cluster canFSFINSEQ-1K21 A as-term-is one-to-oneFUNCT-1V2\<bar>ontoFUNCT-2V2\<^bsub>(A)\<^esub> for FinSequenceFINSEQ-1M3-of A"
proof
(*coherence*)
  show " for it be FinSequenceFINSEQ-1M3-of A holds it =HIDDENR1 canFSFINSEQ-1K21 A implies it be one-to-oneFUNCT-1V2\<bar>ontoFUNCT-2V2\<^bsub>(A)\<^esub>"
     sorry
qed "sorry"

mtheorem finseq_1_th_93:
" for A be finiteFINSET-1V1\<bar>setHIDDENM2 holds lenFINSEQ-1K4 (canFSFINSEQ-1K21 A) =XBOOLE-0R4 cardCARD-1K4 A"
sorry

mtheorem finseq_1_cl_52:
  mlet "A be finiteFINSET-1V1\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster canFSFINSEQ-1K21 A as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "canFSFINSEQ-1K21 A be  non emptyXBOOLE-0V1"
sorry
qed "sorry"

mtheorem finseq_1_th_94:
" for a be objectHIDDENM1 holds canFSFINSEQ-1K21 {TARSKIK1 a} =FINSEQ-1R1 <*FINSEQ-1K10 a*>"
sorry

mtheorem finseq_1_th_95:
" for A be finiteFINSET-1V1\<bar>setHIDDENM2 holds (canFSFINSEQ-1K21 A)\<inverse>FUNCT-1K4 be FunctionFUNCT-2M1-of(A,SegFINSEQ-1K2 (cardCARD-1K4 A))"
sorry

mtheorem finseq_1_th_96:
" for i be NatNAT-1M1 holds  for x be objectHIDDENM1 holds i >XXREAL-0R4 0NUMBERSK6 implies {TARSKIK1 [TARSKIK4 i,x ] } be FinSubsequenceFINSEQ-1M4"
sorry

mlemma finseq_1_lm_6:
" for p be FinSubsequenceFINSEQ-1M4 holds SeqFINSEQ-1K16 p =FINSEQ-1R1 {}XBOOLE-0K1 implies p =FUNCT-1R1 {}XBOOLE-0K1"
sorry

mtheorem finseq_1_th_97:
" for q be FinSubsequenceFINSEQ-1M4 holds q =FUNCT-1R1 {}XBOOLE-0K1 iff SeqFINSEQ-1K16 q =FINSEQ-1R1 {}XBOOLE-0K1"
  using finseq_1_lm_6 sorry

mtheorem finseq_1_cl_53:
"cluster note-that finiteFINSET-1V1 for FinSubsequenceFINSEQ-1M4"
proof
(*coherence*)
  show " for it be FinSubsequenceFINSEQ-1M4 holds it be finiteFINSET-1V1"
sorry
qed "sorry"

reserve x1, x2, y1, y2 for "setHIDDENM2"
mtheorem finseq_1_th_98:
" for x1 be setHIDDENM2 holds  for x2 be setHIDDENM2 holds  for y1 be setHIDDENM2 holds  for y2 be setHIDDENM2 holds {TARSKIK2 [TARSKIK4 x1,y1 ],[TARSKIK4 x2,y2 ] } be FinSequenceFINSEQ-1M1 implies ((x1 =XBOOLE-0R4 \<one>\<^sub>M & x2 =XBOOLE-0R4 \<one>\<^sub>M) & y1 =XBOOLE-0R4 y2 or x1 =XBOOLE-0R4 \<one>\<^sub>M & x2 =XBOOLE-0R4 \<two>\<^sub>M) or x1 =XBOOLE-0R4 \<two>\<^sub>M & x2 =XBOOLE-0R4 \<one>\<^sub>M"
sorry

mtheorem finseq_1_th_99:
" for x1 be setHIDDENM2 holds  for x2 be setHIDDENM2 holds <*FINSEQ-1K11 x1,x2 *> =RELAT-1R1 {TARSKIK2 [TARSKIK4 \<one>\<^sub>M,x1 ],[TARSKIK4 \<two>\<^sub>M,x2 ] }"
sorry

mtheorem finseq_1_th_100:
" for q be FinSubsequenceFINSEQ-1M4 holds domFINSEQ-1K5 (SeqFINSEQ-1K16 q) =XBOOLE-0R4 domFINSEQ-1K5 (SgmFINSEQ-1K15 (domRELAT-1K1 q))"
sorry

mtheorem finseq_1_th_101:
" for q be FinSubsequenceFINSEQ-1M4 holds rngFUNCT-1K2 q =XBOOLE-0R4 rngFUNCT-1K2 (SeqFINSEQ-1K16 q)"
sorry

mtheorem finseq_1_cl_54:
"cluster one-to-oneFUNCT-1V2 for FinSequenceFINSEQ-1M1"
proof
(*existence*)
  show " ex it be FinSequenceFINSEQ-1M1 st it be one-to-oneFUNCT-1V2"
sorry
qed "sorry"

mtheorem finseq_1_cl_55:
  mlet "D be setHIDDENM2"
"cluster one-to-oneFUNCT-1V2 for FinSequenceFINSEQ-1M3-of D"
proof
(*existence*)
  show " ex it be FinSequenceFINSEQ-1M3-of D st it be one-to-oneFUNCT-1V2"
sorry
qed "sorry"

end
