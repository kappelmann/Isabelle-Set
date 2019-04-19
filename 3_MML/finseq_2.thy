theory finseq_2
  imports funct_3 finseq_1 card_3 fraenkel square_1
   "../mizar_extension/E_number"
begin
(*begin*)
reserve i, j, k, l for "naturalORDINAL1V7\<bar>NumberORDINAL1M1"
reserve A for "setHIDDENM2"
reserve a, b, x, x1, x2, x3 for "objectHIDDENM1"
reserve D, D9, E for " non emptyXBOOLE-0V1\<bar>setHIDDENM2"
reserve d, d1, d2, d3 for "ElementSUBSET-1M1-of D"
reserve d9, d19, d29, d39 for "ElementSUBSET-1M1-of D9"
reserve p, q, r for "FinSequenceFINSEQ-1M1"
(*\$CT*)
mtheorem finseq_2_th_2:
" for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for j be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for l be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds l =HIDDENR1 minXXREAL-0K4(i,j) implies SegFINSEQ-1K1 i /\\XBOOLE-0K3 SegFINSEQ-1K1 j =XBOOLE-0R4 SegFINSEQ-1K1 l"
sorry

mtheorem finseq_2_th_3:
" for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for j be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds i <=XXREAL-0R1 j implies maxXXREAL-0K5(0NUMBERSK6,i -XCMPLX-0K6 j) =HIDDENR1 0NUMBERSK6"
sorry

mtheorem finseq_2_th_4:
" for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for j be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds j <=XXREAL-0R1 i implies maxXXREAL-0K5(0NUMBERSK6,i -XCMPLX-0K6 j) =HIDDENR1 i -XCMPLX-0K6 j"
sorry

mtheorem finseq_2_th_5:
" for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for j be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds maxXXREAL-0K5(0NUMBERSK6,i -XCMPLX-0K6 j) be ElementSUBSET-1M1-of NATNUMBERSK1"
sorry

(*\$CT*)
mtheorem finseq_2_th_7:
" for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for l be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds i inHIDDENR3 SegFINSEQ-1K2 (l +NAT-1K1 \<one>\<^sub>M) implies i inHIDDENR3 SegFINSEQ-1K1 l or i =HIDDENR1 l +NAT-1K1 \<one>\<^sub>M"
sorry

mtheorem finseq_2_th_8:
" for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for j be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for l be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds i inHIDDENR3 SegFINSEQ-1K1 l implies i inHIDDENR3 SegFINSEQ-1K2 (l +XCMPLX-0K2 j)"
sorry

mtheorem finseq_2_th_9:
" for p be FinSequenceFINSEQ-1M1 holds  for q be FinSequenceFINSEQ-1M1 holds lenFINSEQ-1K4 p =XBOOLE-0R4 lenFINSEQ-1K4 q & ( for j be NatNAT-1M1 holds j inTARSKIR2 domFINSEQ-1K5 p implies p .FUNCT-1K1 j =XBOOLE-0R4 q .FUNCT-1K1 j) implies p =FINSEQ-1R1 q"
sorry

mtheorem finseq_2_th_10:
" for b be objectHIDDENM1 holds  for p be FinSequenceFINSEQ-1M1 holds b inHIDDENR3 rngFUNCT-1K2 p implies ( ex i be NatNAT-1M1 st i inTARSKIR2 domFINSEQ-1K5 p & p .FUNCT-1K1 i =HIDDENR1 b)"
sorry

mtheorem finseq_2_th_11:
" for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for D be setHIDDENM2 holds  for p be FinSequenceFINSEQ-1M3-of D holds i inHIDDENR3 domFINSEQ-1K5 p implies p .FUNCT-1K1 i inTARSKIR2 D"
sorry

mtheorem finseq_2_th_12:
" for p be FinSequenceFINSEQ-1M1 holds  for D be setHIDDENM2 holds ( for i be NatNAT-1M1 holds i inTARSKIR2 domFINSEQ-1K5 p implies p .FUNCT-1K1 i inTARSKIR2 D) implies p be FinSequenceFINSEQ-1M3-of D"
sorry

mlemma finseq_2_lm_1:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds rngFUNCT-1K2 (<*FINSEQ-1K11 x1,x2 *>) =XBOOLE-0R4 {TARSKIK2 x1,x2 }"
sorry

mtheorem finseq_2_th_13:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d1 be ElementSUBSET-1M1-of D holds  for d2 be ElementSUBSET-1M1-of D holds <*FINSEQ-1K11 d1,d2 *> be FinSequenceFINSEQ-1M3-of D"
sorry

mlemma finseq_2_lm_2:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds rngFUNCT-1K2 (<*FINSEQ-1K12 x1,x2,x3 *>) =XBOOLE-0R4 {ENUMSET1K1 x1,x2,x3 }"
sorry

mtheorem finseq_2_th_14:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d1 be ElementSUBSET-1M1-of D holds  for d2 be ElementSUBSET-1M1-of D holds  for d3 be ElementSUBSET-1M1-of D holds <*FINSEQ-1K12 d1,d2,d3 *> be FinSequenceFINSEQ-1M3-of D"
sorry

mtheorem finseq_2_th_15:
" for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for p be FinSequenceFINSEQ-1M1 holds  for q be FinSequenceFINSEQ-1M1 holds i inHIDDENR3 domFINSEQ-1K5 p implies i inHIDDENR3 domFINSEQ-1K5 (p ^FINSEQ-1K8 q)"
sorry

mtheorem finseq_2_th_16:
" for a be objectHIDDENM1 holds  for p be FinSequenceFINSEQ-1M1 holds lenFINSEQ-1K4 (p ^FINSEQ-1K8 (<*FINSEQ-1K10 a*>)) =XBOOLE-0R4 lenFINSEQ-1K4 p +NAT-1K1 \<one>\<^sub>M"
sorry

mtheorem finseq_2_th_17:
" for a be objectHIDDENM1 holds  for b be objectHIDDENM1 holds  for p be FinSequenceFINSEQ-1M1 holds  for q be FinSequenceFINSEQ-1M1 holds p ^FINSEQ-1K8 (<*FINSEQ-1K10 a*>) =FINSEQ-1R1 q ^FINSEQ-1K8 (<*FINSEQ-1K10 b*>) implies p =FINSEQ-1R1 q & a =HIDDENR1 b"
sorry

mtheorem finseq_2_th_18:
" for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for p be FinSequenceFINSEQ-1M1 holds lenFINSEQ-1K4 p =XBOOLE-0R4 i +NAT-1K1 \<one>\<^sub>M implies ( ex q be FinSequenceFINSEQ-1M1 st  ex a be objectHIDDENM1 st p =FINSEQ-1R1 q ^FINSEQ-1K8 (<*FINSEQ-1K10 a*>))"
  using card_1_th_27 finseq_1_th_46 sorry

mtheorem finseq_2_th_19:
" for A be setHIDDENM2 holds  for p be FinSequenceFINSEQ-1M3-of A holds lenFINSEQ-1K4 p <>HIDDENR2 0NUMBERSK6 implies ( ex q be FinSequenceFINSEQ-1M3-of A st  ex d be ElementSUBSET-1M1-of A st p =FINSEQ-1R1 q ^FINSEQ-1K8 (<*FINSEQ-1K10 d*>))"
sorry

mtheorem finseq_2_th_20:
" for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for p be FinSequenceFINSEQ-1M1 holds  for q be FinSequenceFINSEQ-1M1 holds q =FUNCT-1R1 p |RELAT-1K8 SegFINSEQ-1K1 i & lenFINSEQ-1K4 p <=XXREAL-0R1 i implies p =FINSEQ-1R1 q"
sorry

mtheorem finseq_2_th_21:
" for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for p be FinSequenceFINSEQ-1M1 holds  for q be FinSequenceFINSEQ-1M1 holds q =FUNCT-1R1 p |RELAT-1K8 SegFINSEQ-1K1 i implies lenFINSEQ-1K4 q =HIDDENR1 minXXREAL-0K4(i,lenFINSEQ-1K4 p)"
sorry

mtheorem finseq_2_th_22:
" for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for j be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for r be FinSequenceFINSEQ-1M1 holds lenFINSEQ-1K4 r =XBOOLE-0R4 i +XCMPLX-0K2 j implies ( ex p be FinSequenceFINSEQ-1M1 st  ex q be FinSequenceFINSEQ-1M1 st (lenFINSEQ-1K4 p =HIDDENR1 i & lenFINSEQ-1K4 q =HIDDENR1 j) & r =FINSEQ-1R1 p ^FINSEQ-1K8 q)"
sorry

mtheorem finseq_2_th_23:
" for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for j be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for r be FinSequenceFINSEQ-1M3-of D holds lenFINSEQ-1K4 r =XBOOLE-0R4 i +XCMPLX-0K2 j implies ( ex p be FinSequenceFINSEQ-1M3-of D st  ex q be FinSequenceFINSEQ-1M3-of D st (lenFINSEQ-1K4 p =HIDDENR1 i & lenFINSEQ-1K4 q =HIDDENR1 j) & r =FINSEQ-1R1 p ^FINSEQ-1K9\<^bsub>(D)\<^esub> q)"
sorry

theorem finseq_2_sch_1:
  fixes if0 Df0 Ff1 
  assumes
[ty]: "if0 be NatNAT-1M1" and
  [ty]: "Df0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
  [ty_func]: "\<And> x1. x1 be setHIDDENM2 \<Longrightarrow> Ff1(x1) be ElementSUBSET-1M1-of Df0"
  shows " ex z be FinSequenceFINSEQ-1M3-of Df0 st lenFINSEQ-1K4 z =XBOOLE-0R4 if0 & ( for j be NatNAT-1M1 holds j inTARSKIR2 domFINSEQ-1K5 z implies z .FUNCT-1K1 j =XBOOLE-0R4 Ff1(j))"
sorry

theorem finseq_2_sch_2:
  fixes Df0 Pp1 
  assumes
[ty]: "Df0 be setHIDDENM2" and
   A1: "Pp1(<*>FINSEQ-1K7 Df0)" and
   A2: " for p be FinSequenceFINSEQ-1M3-of Df0 holds  for x be ElementSUBSET-1M1-of Df0 holds Pp1(p) implies Pp1(p ^FINSEQ-1K8 (<*FINSEQ-1K10 x*>))"
  shows " for p be FinSequenceFINSEQ-1M3-of Df0 holds Pp1(p)"
sorry

mtheorem finseq_2_th_24:
" for D be setHIDDENM2 holds  for D1 be SubsetSUBSET-1M2-of D holds  for p be FinSequenceFINSEQ-1M3-of D1 holds p be FinSequenceFINSEQ-1M3-of D"
sorry

mtheorem finseq_2_th_25:
" for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(SegFINSEQ-1K1 i,D) holds f be FinSequenceFINSEQ-1M3-of D"
sorry

mtheorem finseq_2_th_26:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for p be FinSequenceFINSEQ-1M3-of D holds p be FunctionFUNCT-2M1-of(domFINSEQ-1K5 p,D)"
sorry

mtheorem finseq_2_th_27:
" for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for f be sequenceNAT-1M2-of D holds f |PARTFUN1K2\<^bsub>(omegaORDINAL1K4,D)\<^esub> SegFINSEQ-1K1 i be FinSequenceFINSEQ-1M3-of D"
sorry

mtheorem finseq_2_th_28:
" for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for q be FinSequenceFINSEQ-1M1 holds  for f be sequenceNAT-1M2-of D holds q =FUNCT-1R1 f |PARTFUN1K2\<^bsub>(omegaORDINAL1K4,D)\<^esub> SegFINSEQ-1K1 i implies lenFINSEQ-1K4 q =HIDDENR1 i"
sorry

mtheorem finseq_2_th_29:
" for p be FinSequenceFINSEQ-1M1 holds  for q be FinSequenceFINSEQ-1M1 holds  for f be FunctionFUNCT-1M1 holds rngFUNCT-1K2 p c=TARSKIR1 domRELAT-1K1 f & q =FUNCT-1R1 f *FUNCT-1K3 p implies lenFINSEQ-1K4 q =XBOOLE-0R4 lenFINSEQ-1K4 p"
sorry

mtheorem finseq_2_th_30:
" for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds D =XBOOLE-0R4 SegFINSEQ-1K1 i implies ( for p be FinSequenceFINSEQ-1M1 holds  for q be FinSequenceFINSEQ-1M3-of D holds i <=XXREAL-0R1 lenFINSEQ-1K4 p implies p *FUNCT-1K3 q be FinSequenceFINSEQ-1M1)"
sorry

mtheorem finseq_2_th_31:
" for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D9 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds D =XBOOLE-0R4 SegFINSEQ-1K1 i implies ( for p be FinSequenceFINSEQ-1M3-of D9 holds  for q be FinSequenceFINSEQ-1M3-of D holds i <=XXREAL-0R1 lenFINSEQ-1K4 p implies p *PARTFUN1K1\<^bsub>(omegaORDINAL1K4,D,omegaORDINAL1K4,D9)\<^esub> q be FinSequenceFINSEQ-1M3-of D9)"
sorry

mtheorem finseq_2_th_32:
" for A be setHIDDENM2 holds  for D be setHIDDENM2 holds  for p be FinSequenceFINSEQ-1M3-of A holds  for f be FunctionFUNCT-2M1-of(A,D) holds f *PARTFUN1K1\<^bsub>(omegaORDINAL1K4,A,A,D)\<^esub> p be FinSequenceFINSEQ-1M3-of D"
sorry

mtheorem finseq_2_th_33:
" for A be setHIDDENM2 holds  for D9 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for q be FinSequenceFINSEQ-1M1 holds  for p be FinSequenceFINSEQ-1M3-of A holds  for f be FunctionFUNCT-2M1-of(A,D9) holds q =FUNCT-1R1 f *PARTFUN1K1\<^bsub>(omegaORDINAL1K4,A,A,D9)\<^esub> p implies lenFINSEQ-1K4 q =XBOOLE-0R4 lenFINSEQ-1K4 p"
sorry

mtheorem finseq_2_th_34:
" for x be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds x inTARSKIR2 domRELAT-1K1 f implies f *FUNCT-1K3 (<*FINSEQ-1K10 x*>) =FUNCT-1R1 <*FINSEQ-1K10 f .FUNCT-1K1 x*>"
sorry

mtheorem finseq_2_th_35:
" for x1 be objectHIDDENM1 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D9 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for p be FinSequenceFINSEQ-1M3-of D holds  for f be FunctionFUNCT-2M1-of(D,D9) holds p =FINSEQ-1R1 <*FINSEQ-1K10 x1*> implies f *PARTFUN1K1\<^bsub>(omegaORDINAL1K4,D,D,D9)\<^esub> p =FUNCT-1R1 <*FINSEQ-1K10 f .FUNCT-1K1 x1*>"
sorry

mtheorem finseq_2_th_36:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D9 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for p be FinSequenceFINSEQ-1M3-of D holds  for f be FunctionFUNCT-2M1-of(D,D9) holds p =FINSEQ-1R1 <*FINSEQ-1K11 x1,x2 *> implies f *PARTFUN1K1\<^bsub>(omegaORDINAL1K4,D,D,D9)\<^esub> p =FUNCT-1R1 <*FINSEQ-1K11 f .FUNCT-1K1 x1,f .FUNCT-1K1 x2 *>"
sorry

mtheorem finseq_2_th_37:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D9 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for p be FinSequenceFINSEQ-1M3-of D holds  for f be FunctionFUNCT-2M1-of(D,D9) holds p =FINSEQ-1R1 <*FINSEQ-1K12 x1,x2,x3 *> implies f *PARTFUN1K1\<^bsub>(omegaORDINAL1K4,D,D,D9)\<^esub> p =FUNCT-1R1 <*FINSEQ-1K12 f .FUNCT-1K1 x1,f .FUNCT-1K1 x2,f .FUNCT-1K1 x3 *>"
sorry

mtheorem finseq_2_th_38:
" for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for j be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for p be FinSequenceFINSEQ-1M1 holds  for f be FunctionFUNCT-2M1-of(SegFINSEQ-1K1 i,SegFINSEQ-1K1 j) holds (j =HIDDENR1 0NUMBERSK6 implies i =HIDDENR1 0NUMBERSK6) & j <=XXREAL-0R1 lenFINSEQ-1K4 p implies p *FUNCT-1K3 f be FinSequenceFINSEQ-1M1"
sorry

mtheorem finseq_2_th_39:
" for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for p be FinSequenceFINSEQ-1M1 holds  for f be FunctionFUNCT-2M1-of(SegFINSEQ-1K1 i,SegFINSEQ-1K1 i) holds i <=XXREAL-0R1 lenFINSEQ-1K4 p implies p *FUNCT-1K3 f be FinSequenceFINSEQ-1M1"
  using finseq_2_th_38 sorry

mtheorem finseq_2_th_40:
" for p be FinSequenceFINSEQ-1M1 holds  for f be FunctionFUNCT-2M1-of(domFINSEQ-1K5 p,domFINSEQ-1K5 p) holds p *FUNCT-1K3 f be FinSequenceFINSEQ-1M1"
sorry

mtheorem finseq_2_th_41:
" for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for p be FinSequenceFINSEQ-1M1 holds  for q be FinSequenceFINSEQ-1M1 holds  for f be FunctionFUNCT-2M1-of(SegFINSEQ-1K1 i,SegFINSEQ-1K1 i) holds (rngFUNCT-1K2 f =XBOOLE-0R4 SegFINSEQ-1K1 i & i <=XXREAL-0R1 lenFINSEQ-1K4 p) & q =FUNCT-1R1 p *FUNCT-1K3 f implies lenFINSEQ-1K4 q =HIDDENR1 i"
sorry

mtheorem finseq_2_th_42:
" for p be FinSequenceFINSEQ-1M1 holds  for q be FinSequenceFINSEQ-1M1 holds  for f be FunctionFUNCT-2M1-of(domFINSEQ-1K5 p,domFINSEQ-1K5 p) holds rngFUNCT-1K2 f =XBOOLE-0R4 domFINSEQ-1K5 p & q =FUNCT-1R1 p *FUNCT-1K3 f implies lenFINSEQ-1K4 q =XBOOLE-0R4 lenFINSEQ-1K4 p"
sorry

mtheorem finseq_2_th_43:
" for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for p be FinSequenceFINSEQ-1M1 holds  for q be FinSequenceFINSEQ-1M1 holds  for f be PermutationFUNCT-2M2-of SegFINSEQ-1K1 i holds i <=XXREAL-0R1 lenFINSEQ-1K4 p & q =FUNCT-1R1 p *FUNCT-1K3 f implies lenFINSEQ-1K4 q =HIDDENR1 i"
sorry

mtheorem finseq_2_th_44:
" for p be FinSequenceFINSEQ-1M1 holds  for q be FinSequenceFINSEQ-1M1 holds  for f be PermutationFUNCT-2M2-of domFINSEQ-1K5 p holds q =FUNCT-1R1 p *FUNCT-1K3 f implies lenFINSEQ-1K4 q =XBOOLE-0R4 lenFINSEQ-1K4 p"
sorry

mtheorem finseq_2_th_45:
" for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for j be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for p be FinSequenceFINSEQ-1M3-of D holds  for f be FunctionFUNCT-2M1-of(SegFINSEQ-1K1 i,SegFINSEQ-1K1 j) holds (j =HIDDENR1 0NUMBERSK6 implies i =HIDDENR1 0NUMBERSK6) & j <=XXREAL-0R1 lenFINSEQ-1K4 p implies p *PARTFUN1K1\<^bsub>(SegFINSEQ-1K1 i,SegFINSEQ-1K1 j,omegaORDINAL1K4,D)\<^esub> f be FinSequenceFINSEQ-1M3-of D"
sorry

mtheorem finseq_2_th_46:
" for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for p be FinSequenceFINSEQ-1M3-of D holds  for f be FunctionFUNCT-2M1-of(SegFINSEQ-1K1 i,SegFINSEQ-1K1 i) holds i <=XXREAL-0R1 lenFINSEQ-1K4 p implies p *PARTFUN1K1\<^bsub>(SegFINSEQ-1K1 i,SegFINSEQ-1K1 i,omegaORDINAL1K4,D)\<^esub> f be FinSequenceFINSEQ-1M3-of D"
  using finseq_2_th_45 sorry

mtheorem finseq_2_th_47:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for p be FinSequenceFINSEQ-1M3-of D holds  for f be FunctionFUNCT-2M1-of(domFINSEQ-1K5 p,domFINSEQ-1K5 p) holds p *PARTFUN1K1\<^bsub>(domFINSEQ-1K5 p,domFINSEQ-1K5 p,omegaORDINAL1K4,D)\<^esub> f be FinSequenceFINSEQ-1M3-of D"
sorry

mtheorem finseq_2_th_48:
" for k be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds idPARTFUN1K6 (SegFINSEQ-1K1 k) be FinSequenceFINSEQ-1M3-of NATNUMBERSK1"
sorry

mdef finseq_2_def_1 ("idseqFINSEQ-2K1  _ " [228]228 ) where
  mlet "i be naturalORDINAL1V7\<bar>NumberORDINAL1M1"
"func idseqFINSEQ-2K1 i \<rightarrow> FinSequenceFINSEQ-1M1 equals
  idPARTFUN1K6 (SegFINSEQ-1K1 i)"
proof-
  (*coherence*)
    show "idPARTFUN1K6 (SegFINSEQ-1K1 i) be FinSequenceFINSEQ-1M1"
      using finseq_2_th_48 sorry
qed "sorry"

mtheorem finseq_2_cl_1:
  mlet "k be naturalORDINAL1V7\<bar>NumberORDINAL1M1"
"cluster idseqFINSEQ-2K1 k as-term-is k -elementCARD-1V3"
proof
(*coherence*)
  show "idseqFINSEQ-2K1 k be k -elementCARD-1V3"
sorry
qed "sorry"

mtheorem finseq_2_cl_2:
"cluster idseqFINSEQ-2K1 (0NUMBERSK6) as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "idseqFINSEQ-2K1 (0NUMBERSK6) be emptyXBOOLE-0V1"
     sorry
qed "sorry"

mtheorem finseq_2_th_49:
" for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for k be ElementSUBSET-1M1-of SegFINSEQ-1K1 i holds idseqFINSEQ-2K1 i .FUNCT-1K1 k =XBOOLE-0R4 k"
   sorry

mtheorem finseq_2_th_50:
"idseqFINSEQ-2K1 \<one>\<^sub>M =FINSEQ-1R1 <*FINSEQ-1K13\<^bsub>(omegaORDINAL1K4)\<^esub> \<one>\<^sub>M*>"
sorry

mtheorem finseq_2_th_51:
" for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds idseqFINSEQ-2K1 (i +NAT-1K1 \<one>\<^sub>M) =FINSEQ-1R1 idseqFINSEQ-2K1 i ^FINSEQ-1K8 (<*FINSEQ-1K13\<^bsub>(omegaORDINAL1K4)\<^esub> i +NAT-1K1 \<one>\<^sub>M *>)"
sorry

mtheorem finseq_2_th_52:
"idseqFINSEQ-2K1 \<two>\<^sub>M =FINSEQ-1R1 <*FINSEQ-1K11 \<one>\<^sub>M,\<two>\<^sub>M *>"
  using finseq_2_th_50 finseq_2_th_51 sorry

mtheorem finseq_2_th_53:
"idseqFINSEQ-2K1 \<three>\<^sub>M =FINSEQ-1R1 <*FINSEQ-1K12 \<one>\<^sub>M,\<two>\<^sub>M,\<three>\<^sub>M *>"
  using finseq_2_th_51 finseq_2_th_52 sorry

mtheorem finseq_2_th_54:
" for k be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for p be FinSequenceFINSEQ-1M1 holds lenFINSEQ-1K4 p <=XXREAL-0R1 k implies p *FUNCT-1K3 idseqFINSEQ-2K1 k =FUNCT-1R1 p"
sorry

mtheorem finseq_2_th_55:
" for k be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds idseqFINSEQ-2K1 k be PermutationFUNCT-2M2-of SegFINSEQ-1K1 k"
   sorry

mtheorem finseq_2_th_56:
" for a be objectHIDDENM1 holds  for k be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds SegFINSEQ-1K1 k -->FUNCOP-1K7 a be FinSequenceFINSEQ-1M1"
sorry

mtheorem finseq_2_cl_3:
  mlet "i be naturalORDINAL1V7\<bar>NumberORDINAL1M1", "a be objectHIDDENM1"
"cluster SegFINSEQ-1K1 i -->FUNCOP-1K7 a as-term-is FinSequence-likeFINSEQ-1V1"
proof
(*coherence*)
  show "SegFINSEQ-1K1 i -->FUNCOP-1K7 a be FinSequence-likeFINSEQ-1V1"
    using finseq_2_th_56 sorry
qed "sorry"

mdef finseq_2_def_2 (" _ |->FINSEQ-2K2  _ " [164,164]164 ) where
  mlet "i be naturalORDINAL1V7\<bar>NumberORDINAL1M1", "a be objectHIDDENM1"
"func i |->FINSEQ-2K2 a \<rightarrow> FinSequenceFINSEQ-1M1 equals
  SegFINSEQ-1K1 i -->FUNCOP-1K7 a"
proof-
  (*coherence*)
    show "SegFINSEQ-1K1 i -->FUNCOP-1K7 a be FinSequenceFINSEQ-1M1"
       sorry
qed "sorry"

mtheorem finseq_2_cl_4:
  mlet "k be naturalORDINAL1V7\<bar>NumberORDINAL1M1", "a be objectHIDDENM1"
"cluster k |->FINSEQ-2K2 a as-term-is k -elementCARD-1V3"
proof
(*coherence*)
  show "k |->FINSEQ-2K2 a be k -elementCARD-1V3"
sorry
qed "sorry"

mtheorem finseq_2_th_57:
" for k be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for d be objectHIDDENM1 holds  for w be setHIDDENM2 holds w inTARSKIR2 SegFINSEQ-1K1 k implies (k |->FINSEQ-2K2 d).FUNCT-1K1 w =HIDDENR1 d"
  using funcop_1_th_7 sorry

mtheorem finseq_2_th_58:
" for a be objectHIDDENM1 holds (0NUMBERSK6)|->FINSEQ-2K2 a =FINSEQ-1R1 {}XBOOLE-0K1"
   sorry

mtheorem finseq_2_th_59:
" for a be objectHIDDENM1 holds \<one>\<^sub>M |->FINSEQ-2K2 a =FINSEQ-1R1 <*FINSEQ-1K10 a*>"
sorry

mtheorem finseq_2_th_60:
" for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for a be objectHIDDENM1 holds (i +NAT-1K1 \<one>\<^sub>M)|->FINSEQ-2K2 a =FINSEQ-1R1 (i |->FINSEQ-2K2 a)^FINSEQ-1K8 (<*FINSEQ-1K10 a*>)"
sorry

mtheorem finseq_2_th_61:
" for a be objectHIDDENM1 holds \<two>\<^sub>M |->FINSEQ-2K2 a =FINSEQ-1R1 <*FINSEQ-1K11 a,a *>"
sorry

mtheorem finseq_2_th_62:
" for a be objectHIDDENM1 holds \<three>\<^sub>M |->FINSEQ-2K2 a =FINSEQ-1R1 <*FINSEQ-1K12 a,a,a *>"
sorry

mtheorem finseq_2_th_63:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d be ElementSUBSET-1M1-of D holds  for k be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds k |->FINSEQ-2K2 d be FinSequenceFINSEQ-1M3-of D"
sorry

mlemma finseq_2_lm_3:
" for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for p be FinSequenceFINSEQ-1M1 holds  for q be FinSequenceFINSEQ-1M1 holds  for F be FunctionFUNCT-1M1 holds [:ZFMISC-1K2 rngFUNCT-1K2 p,rngFUNCT-1K2 q :] c=RELAT-1R2 domRELAT-1K1 F & i =HIDDENR1 minXXREAL-0K4(lenFINSEQ-1K4 p,lenFINSEQ-1K4 q) implies domRELAT-1K1 (F .:FUNCOP-1K3(p,q)) =XBOOLE-0R4 SegFINSEQ-1K1 i"
sorry

mtheorem finseq_2_th_64:
" for p be FinSequenceFINSEQ-1M1 holds  for q be FinSequenceFINSEQ-1M1 holds  for F be FunctionFUNCT-1M1 holds [:ZFMISC-1K2 rngFUNCT-1K2 p,rngFUNCT-1K2 q :] c=RELAT-1R2 domRELAT-1K1 F implies F .:FUNCOP-1K3(p,q) be FinSequenceFINSEQ-1M1"
sorry

mtheorem finseq_2_th_65:
" for p be FinSequenceFINSEQ-1M1 holds  for q be FinSequenceFINSEQ-1M1 holds  for r be FinSequenceFINSEQ-1M1 holds  for F be FunctionFUNCT-1M1 holds [:ZFMISC-1K2 rngFUNCT-1K2 p,rngFUNCT-1K2 q :] c=RELAT-1R2 domRELAT-1K1 F & r =FUNCT-1R1 F .:FUNCOP-1K3(p,q) implies lenFINSEQ-1K4 r =HIDDENR1 minXXREAL-0K4(lenFINSEQ-1K4 p,lenFINSEQ-1K4 q)"
sorry

mlemma finseq_2_lm_4:
" for a be objectHIDDENM1 holds  for p be FinSequenceFINSEQ-1M1 holds  for F be FunctionFUNCT-1M1 holds [:ZFMISC-1K2 {TARSKIK1 a},rngFUNCT-1K2 p :] c=RELAT-1R2 domRELAT-1K1 F implies domRELAT-1K1 (F [;]FUNCOP-1K5(a,p)) =XBOOLE-0R4 domFINSEQ-1K5 p"
sorry

mtheorem finseq_2_th_66:
" for a be objectHIDDENM1 holds  for p be FinSequenceFINSEQ-1M1 holds  for F be FunctionFUNCT-1M1 holds [:ZFMISC-1K2 {TARSKIK1 a},rngFUNCT-1K2 p :] c=RELAT-1R2 domRELAT-1K1 F implies F [;]FUNCOP-1K5(a,p) be FinSequenceFINSEQ-1M1"
sorry

mtheorem finseq_2_th_67:
" for a be objectHIDDENM1 holds  for p be FinSequenceFINSEQ-1M1 holds  for r be FinSequenceFINSEQ-1M1 holds  for F be FunctionFUNCT-1M1 holds [:ZFMISC-1K2 {TARSKIK1 a},rngFUNCT-1K2 p :] c=RELAT-1R2 domRELAT-1K1 F & r =FUNCT-1R1 F [;]FUNCOP-1K5(a,p) implies lenFINSEQ-1K4 r =XBOOLE-0R4 lenFINSEQ-1K4 p"
sorry

mlemma finseq_2_lm_5:
" for a be objectHIDDENM1 holds  for p be FinSequenceFINSEQ-1M1 holds  for F be FunctionFUNCT-1M1 holds [:ZFMISC-1K2 rngFUNCT-1K2 p,{TARSKIK1 a} :] c=RELAT-1R2 domRELAT-1K1 F implies domRELAT-1K1 (F [:]FUNCOP-1K4(p,a)) =XBOOLE-0R4 domFINSEQ-1K5 p"
sorry

mtheorem finseq_2_th_68:
" for a be objectHIDDENM1 holds  for p be FinSequenceFINSEQ-1M1 holds  for F be FunctionFUNCT-1M1 holds [:ZFMISC-1K2 rngFUNCT-1K2 p,{TARSKIK1 a} :] c=RELAT-1R2 domRELAT-1K1 F implies F [:]FUNCOP-1K4(p,a) be FinSequenceFINSEQ-1M1"
sorry

mtheorem finseq_2_th_69:
" for a be objectHIDDENM1 holds  for p be FinSequenceFINSEQ-1M1 holds  for r be FinSequenceFINSEQ-1M1 holds  for F be FunctionFUNCT-1M1 holds [:ZFMISC-1K2 rngFUNCT-1K2 p,{TARSKIK1 a} :] c=RELAT-1R2 domRELAT-1K1 F & r =FUNCT-1R1 F [:]FUNCOP-1K4(p,a) implies lenFINSEQ-1K4 r =XBOOLE-0R4 lenFINSEQ-1K4 p"
sorry

mtheorem finseq_2_th_70:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D9 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for E be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for F be FunctionFUNCT-2M1-of([:ZFMISC-1K2 D,D9 :],E) holds  for p be FinSequenceFINSEQ-1M3-of D holds  for q be FinSequenceFINSEQ-1M3-of D9 holds F .:FUNCOP-1K3(p,q) be FinSequenceFINSEQ-1M3-of E"
sorry

mtheorem finseq_2_th_71:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D9 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for E be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for r be FinSequenceFINSEQ-1M1 holds  for F be FunctionFUNCT-2M1-of([:ZFMISC-1K2 D,D9 :],E) holds  for p be FinSequenceFINSEQ-1M3-of D holds  for q be FinSequenceFINSEQ-1M3-of D9 holds r =FUNCT-1R1 F .:FUNCOP-1K3(p,q) implies lenFINSEQ-1K4 r =HIDDENR1 minXXREAL-0K4(lenFINSEQ-1K4 p,lenFINSEQ-1K4 q)"
sorry

mtheorem finseq_2_th_72:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D9 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for E be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for r be FinSequenceFINSEQ-1M1 holds  for F be FunctionFUNCT-2M1-of([:ZFMISC-1K2 D,D9 :],E) holds  for p be FinSequenceFINSEQ-1M3-of D holds  for q be FinSequenceFINSEQ-1M3-of D9 holds lenFINSEQ-1K4 p =XBOOLE-0R4 lenFINSEQ-1K4 q & r =FUNCT-1R1 F .:FUNCOP-1K3(p,q) implies lenFINSEQ-1K4 r =XBOOLE-0R4 lenFINSEQ-1K4 p & lenFINSEQ-1K4 r =XBOOLE-0R4 lenFINSEQ-1K4 q"
sorry

mtheorem finseq_2_th_73:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D9 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for E be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for F be FunctionFUNCT-2M1-of([:ZFMISC-1K2 D,D9 :],E) holds  for p be FinSequenceFINSEQ-1M3-of D holds  for p9 be FinSequenceFINSEQ-1M3-of D9 holds F .:FUNCOP-1K3(<*>FINSEQ-1K7 D,p9) =FUNCT-1R1 <*>FINSEQ-1K7 E & F .:FUNCOP-1K3(p,<*>FINSEQ-1K7 D9) =FUNCT-1R1 <*>FINSEQ-1K7 E"
sorry

mtheorem finseq_2_th_74:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D9 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for E be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d1 be ElementSUBSET-1M1-of D holds  for d19 be ElementSUBSET-1M1-of D9 holds  for F be FunctionFUNCT-2M1-of([:ZFMISC-1K2 D,D9 :],E) holds  for p be FinSequenceFINSEQ-1M3-of D holds  for q be FinSequenceFINSEQ-1M3-of D9 holds p =FINSEQ-1R1 <*FINSEQ-1K13\<^bsub>(D)\<^esub> d1*> & q =FINSEQ-1R1 <*FINSEQ-1K13\<^bsub>(D9)\<^esub> d19*> implies F .:FUNCOP-1K3(p,q) =FUNCT-1R1 <*FINSEQ-1K13\<^bsub>(E)\<^esub> F .BINOP-1K2\<^bsub>(D,D9,E)\<^esub>(d1,d19)*>"
sorry

mtheorem finseq_2_th_75:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D9 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for E be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d1 be ElementSUBSET-1M1-of D holds  for d2 be ElementSUBSET-1M1-of D holds  for d19 be ElementSUBSET-1M1-of D9 holds  for d29 be ElementSUBSET-1M1-of D9 holds  for F be FunctionFUNCT-2M1-of([:ZFMISC-1K2 D,D9 :],E) holds  for p be FinSequenceFINSEQ-1M3-of D holds  for q be FinSequenceFINSEQ-1M3-of D9 holds p =FINSEQ-1R1 <*FINSEQ-1K11 d1,d2 *> & q =FINSEQ-1R1 <*FINSEQ-1K11 d19,d29 *> implies F .:FUNCOP-1K3(p,q) =FUNCT-1R1 <*FINSEQ-1K11 F .BINOP-1K2\<^bsub>(D,D9,E)\<^esub>(d1,d19),F .BINOP-1K2\<^bsub>(D,D9,E)\<^esub>(d2,d29) *>"
sorry

mtheorem finseq_2_th_76:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D9 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for E be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d1 be ElementSUBSET-1M1-of D holds  for d2 be ElementSUBSET-1M1-of D holds  for d3 be ElementSUBSET-1M1-of D holds  for d19 be ElementSUBSET-1M1-of D9 holds  for d29 be ElementSUBSET-1M1-of D9 holds  for d39 be ElementSUBSET-1M1-of D9 holds  for F be FunctionFUNCT-2M1-of([:ZFMISC-1K2 D,D9 :],E) holds  for p be FinSequenceFINSEQ-1M3-of D holds  for q be FinSequenceFINSEQ-1M3-of D9 holds p =FINSEQ-1R1 <*FINSEQ-1K12 d1,d2,d3 *> & q =FINSEQ-1R1 <*FINSEQ-1K12 d19,d29,d39 *> implies F .:FUNCOP-1K3(p,q) =FUNCT-1R1 <*FINSEQ-1K12 F .BINOP-1K2\<^bsub>(D,D9,E)\<^esub>(d1,d19),F .BINOP-1K2\<^bsub>(D,D9,E)\<^esub>(d2,d29),F .BINOP-1K2\<^bsub>(D,D9,E)\<^esub>(d3,d39) *>"
sorry

mtheorem finseq_2_th_77:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D9 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for E be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d be ElementSUBSET-1M1-of D holds  for F be FunctionFUNCT-2M1-of([:ZFMISC-1K2 D,D9 :],E) holds  for p be FinSequenceFINSEQ-1M3-of D9 holds F [;]FUNCOP-1K5(d,p) be FinSequenceFINSEQ-1M3-of E"
sorry

mtheorem finseq_2_th_78:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D9 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for E be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d be ElementSUBSET-1M1-of D holds  for r be FinSequenceFINSEQ-1M1 holds  for F be FunctionFUNCT-2M1-of([:ZFMISC-1K2 D,D9 :],E) holds  for p be FinSequenceFINSEQ-1M3-of D9 holds r =FUNCT-1R1 F [;]FUNCOP-1K5(d,p) implies lenFINSEQ-1K4 r =XBOOLE-0R4 lenFINSEQ-1K4 p"
sorry

mtheorem finseq_2_th_79:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D9 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for E be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d be ElementSUBSET-1M1-of D holds  for F be FunctionFUNCT-2M1-of([:ZFMISC-1K2 D,D9 :],E) holds F [;]FUNCOP-1K5(d,<*>FINSEQ-1K7 D9) =FUNCT-1R1 <*>FINSEQ-1K7 E"
sorry

mtheorem finseq_2_th_80:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D9 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for E be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d be ElementSUBSET-1M1-of D holds  for d19 be ElementSUBSET-1M1-of D9 holds  for F be FunctionFUNCT-2M1-of([:ZFMISC-1K2 D,D9 :],E) holds  for p be FinSequenceFINSEQ-1M3-of D9 holds p =FINSEQ-1R1 <*FINSEQ-1K13\<^bsub>(D9)\<^esub> d19*> implies F [;]FUNCOP-1K5(d,p) =FUNCT-1R1 <*FINSEQ-1K13\<^bsub>(E)\<^esub> F .BINOP-1K2\<^bsub>(D,D9,E)\<^esub>(d,d19)*>"
sorry

mtheorem finseq_2_th_81:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D9 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for E be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d be ElementSUBSET-1M1-of D holds  for d19 be ElementSUBSET-1M1-of D9 holds  for d29 be ElementSUBSET-1M1-of D9 holds  for F be FunctionFUNCT-2M1-of([:ZFMISC-1K2 D,D9 :],E) holds  for p be FinSequenceFINSEQ-1M3-of D9 holds p =FINSEQ-1R1 <*FINSEQ-1K11 d19,d29 *> implies F [;]FUNCOP-1K5(d,p) =FUNCT-1R1 <*FINSEQ-1K11 F .BINOP-1K2\<^bsub>(D,D9,E)\<^esub>(d,d19),F .BINOP-1K2\<^bsub>(D,D9,E)\<^esub>(d,d29) *>"
sorry

mtheorem finseq_2_th_82:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D9 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for E be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d be ElementSUBSET-1M1-of D holds  for d19 be ElementSUBSET-1M1-of D9 holds  for d29 be ElementSUBSET-1M1-of D9 holds  for d39 be ElementSUBSET-1M1-of D9 holds  for F be FunctionFUNCT-2M1-of([:ZFMISC-1K2 D,D9 :],E) holds  for p be FinSequenceFINSEQ-1M3-of D9 holds p =FINSEQ-1R1 <*FINSEQ-1K12 d19,d29,d39 *> implies F [;]FUNCOP-1K5(d,p) =FUNCT-1R1 <*FINSEQ-1K12 F .BINOP-1K2\<^bsub>(D,D9,E)\<^esub>(d,d19),F .BINOP-1K2\<^bsub>(D,D9,E)\<^esub>(d,d29),F .BINOP-1K2\<^bsub>(D,D9,E)\<^esub>(d,d39) *>"
sorry

mtheorem finseq_2_th_83:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D9 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for E be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d9 be ElementSUBSET-1M1-of D9 holds  for F be FunctionFUNCT-2M1-of([:ZFMISC-1K2 D,D9 :],E) holds  for p be FinSequenceFINSEQ-1M3-of D holds F [:]FUNCOP-1K4(p,d9) be FinSequenceFINSEQ-1M3-of E"
sorry

mtheorem finseq_2_th_84:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D9 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for E be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d9 be ElementSUBSET-1M1-of D9 holds  for r be FinSequenceFINSEQ-1M1 holds  for F be FunctionFUNCT-2M1-of([:ZFMISC-1K2 D,D9 :],E) holds  for p be FinSequenceFINSEQ-1M3-of D holds r =FUNCT-1R1 F [:]FUNCOP-1K4(p,d9) implies lenFINSEQ-1K4 r =XBOOLE-0R4 lenFINSEQ-1K4 p"
sorry

mtheorem finseq_2_th_85:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D9 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for E be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d9 be ElementSUBSET-1M1-of D9 holds  for F be FunctionFUNCT-2M1-of([:ZFMISC-1K2 D,D9 :],E) holds F [:]FUNCOP-1K4(<*>FINSEQ-1K7 D,d9) =FUNCT-1R1 <*>FINSEQ-1K7 E"
sorry

mtheorem finseq_2_th_86:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D9 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for E be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d1 be ElementSUBSET-1M1-of D holds  for d9 be ElementSUBSET-1M1-of D9 holds  for F be FunctionFUNCT-2M1-of([:ZFMISC-1K2 D,D9 :],E) holds  for p be FinSequenceFINSEQ-1M3-of D holds p =FINSEQ-1R1 <*FINSEQ-1K13\<^bsub>(D)\<^esub> d1*> implies F [:]FUNCOP-1K4(p,d9) =FUNCT-1R1 <*FINSEQ-1K13\<^bsub>(E)\<^esub> F .BINOP-1K2\<^bsub>(D,D9,E)\<^esub>(d1,d9)*>"
sorry

mtheorem finseq_2_th_87:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D9 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for E be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d1 be ElementSUBSET-1M1-of D holds  for d2 be ElementSUBSET-1M1-of D holds  for d9 be ElementSUBSET-1M1-of D9 holds  for F be FunctionFUNCT-2M1-of([:ZFMISC-1K2 D,D9 :],E) holds  for p be FinSequenceFINSEQ-1M3-of D holds p =FINSEQ-1R1 <*FINSEQ-1K11 d1,d2 *> implies F [:]FUNCOP-1K4(p,d9) =FUNCT-1R1 <*FINSEQ-1K11 F .BINOP-1K2\<^bsub>(D,D9,E)\<^esub>(d1,d9),F .BINOP-1K2\<^bsub>(D,D9,E)\<^esub>(d2,d9) *>"
sorry

mtheorem finseq_2_th_88:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D9 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for E be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d1 be ElementSUBSET-1M1-of D holds  for d2 be ElementSUBSET-1M1-of D holds  for d3 be ElementSUBSET-1M1-of D holds  for d9 be ElementSUBSET-1M1-of D9 holds  for F be FunctionFUNCT-2M1-of([:ZFMISC-1K2 D,D9 :],E) holds  for p be FinSequenceFINSEQ-1M3-of D holds p =FINSEQ-1R1 <*FINSEQ-1K12 d1,d2,d3 *> implies F [:]FUNCOP-1K4(p,d9) =FUNCT-1R1 <*FINSEQ-1K12 F .BINOP-1K2\<^bsub>(D,D9,E)\<^esub>(d1,d9),F .BINOP-1K2\<^bsub>(D,D9,E)\<^esub>(d2,d9),F .BINOP-1K2\<^bsub>(D,D9,E)\<^esub>(d3,d9) *>"
sorry

mdef finseq_2_def_3 ("FinSequenceSetFINSEQ-2M1-of  _ " [70]70 ) where
  mlet "D be setHIDDENM2"
"mode FinSequenceSetFINSEQ-2M1-of D \<rightarrow> setHIDDENM2 means
  (\<lambda>it.  for a be objectHIDDENM1 holds a inHIDDENR3 it implies a be FinSequenceFINSEQ-1M3-of D)"
proof-
  (*existence*)
    show " ex it be setHIDDENM2 st  for a be objectHIDDENM1 holds a inHIDDENR3 it implies a be FinSequenceFINSEQ-1M3-of D"
sorry
qed "sorry"

syntax FINSEQ_2M2 :: " Set \<Rightarrow>  Set \<Rightarrow> Ty" ("ElementFINSEQ-2M2\<^bsub>'( _ ')\<^esub>-of  _ " [0,70]70)
translations "ElementFINSEQ-2M2\<^bsub>(D)\<^esub>-of S" \<rightharpoonup> "ElementSUBSET-1M1-of S"

mtheorem finseq_2_add_1:
  mlet "D be setHIDDENM2", "S be FinSequenceSetFINSEQ-2M1-of D"
"cluster note-that FinSequenceFINSEQ-1M3-of D for ElementSUBSET-1M1-of S"
proof
(*coherence*)
  show " for it be ElementSUBSET-1M1-of S holds it be FinSequenceFINSEQ-1M3-of D"
sorry
qed "sorry"

mtheorem finseq_2_cl_5:
  mlet "D be setHIDDENM2"
"cluster  non emptyXBOOLE-0V1 for FinSequenceSetFINSEQ-2M1-of D"
proof
(*existence*)
  show " ex it be FinSequenceSetFINSEQ-2M1-of D st it be  non emptyXBOOLE-0V1"
sorry
qed "sorry"

mtheorem finseq_2_th_89:
" for D be setHIDDENM2 holds D * FINSEQ-1K14 be FinSequenceSetFINSEQ-2M1-of D"
sorry

abbreviation(input) FINSEQ_2K3(" _ * FINSEQ-2K3" [164]164) where
  "D * FINSEQ-2K3 \<equiv> D * FINSEQ-1K14"

mtheorem finseq_2_add_2:
  mlet "D be setHIDDENM2"
"cluster D * FINSEQ-1K14 as-term-is FinSequenceSetFINSEQ-2M1-of D"
proof
(*coherence*)
  show "D * FINSEQ-1K14 be FinSequenceSetFINSEQ-2M1-of D"
    using finseq_2_th_89 sorry
qed "sorry"

mtheorem finseq_2_th_90:
" for D be setHIDDENM2 holds  for D9 be FinSequenceSetFINSEQ-2M1-of D holds D9 c=TARSKIR1 D * FINSEQ-2K3"
sorry

mtheorem finseq_2_th_91:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D9 be SubsetSUBSET-1M2-of D holds  for S be FinSequenceSetFINSEQ-2M1-of D9 holds S be FinSequenceSetFINSEQ-2M1-of D"
sorry

reserve s for "ElementFINSEQ-2M2\<^bsub>(D)\<^esub>-of D * FINSEQ-2K3"
mtheorem finseq_2_cl_6:
  mlet "i be naturalORDINAL1V7\<bar>NumberORDINAL1M1", "D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster i -elementCARD-1V3 for FinSequenceFINSEQ-1M3-of D"
proof
(*existence*)
  show " ex it be FinSequenceFINSEQ-1M3-of D st it be i -elementCARD-1V3"
sorry
qed "sorry"

abbreviation(input) FINSEQ_2M3("TupleFINSEQ-2M3-of'( _ , _ ')" [0,0]70) where
  "TupleFINSEQ-2M3-of(i,D) \<equiv> i -elementCARD-1V3\<bar>FinSequenceFINSEQ-1M3-of D"

mdef finseq_2_def_4 (" _ -tuples-onFINSEQ-2K4  _ " [228,228]228 ) where
  mlet "i be naturalORDINAL1V7\<bar>NumberORDINAL1M1", "D be setHIDDENM2"
"func i -tuples-onFINSEQ-2K4 D \<rightarrow> FinSequenceSetFINSEQ-2M1-of D equals
  {s where s be ElementFINSEQ-2M2\<^bsub>(D)\<^esub>-of D * FINSEQ-2K3 : lenFINSEQ-1K4 s =HIDDENR1 i }"
proof-
  (*coherence*)
    show "{s where s be ElementFINSEQ-2M2\<^bsub>(D)\<^esub>-of D * FINSEQ-2K3 : lenFINSEQ-1K4 s =HIDDENR1 i } be FinSequenceSetFINSEQ-2M1-of D"
sorry
qed "sorry"

mtheorem finseq_2_cl_7:
  mlet "i be naturalORDINAL1V7\<bar>NumberORDINAL1M1", "D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster i -tuples-onFINSEQ-2K4 D as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "i -tuples-onFINSEQ-2K4 D be  non emptyXBOOLE-0V1"
sorry
qed "sorry"

mtheorem finseq_2_cl_8:
  mlet "D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "i be naturalORDINAL1V7\<bar>NumberORDINAL1M1"
"cluster note-that i -elementCARD-1V3 for ElementFINSEQ-2M2\<^bsub>(D)\<^esub>-of i -tuples-onFINSEQ-2K4 D"
proof
(*coherence*)
  show " for it be ElementFINSEQ-2M2\<^bsub>(D)\<^esub>-of i -tuples-onFINSEQ-2K4 D holds it be i -elementCARD-1V3"
sorry
qed "sorry"

mtheorem finseq_2_th_92:
" for D be setHIDDENM2 holds  for z be FinSequenceFINSEQ-1M3-of D holds z be ElementFINSEQ-2M2\<^bsub>(D)\<^esub>-of (lenFINSEQ-1K4 z)-tuples-onFINSEQ-2K4 D"
sorry

mtheorem finseq_2_th_93:
" for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for D be setHIDDENM2 holds i -tuples-onFINSEQ-2K4 D =XBOOLE-0R4 FuncsFUNCT-2K1(SegFINSEQ-1K1 i,D)"
sorry

mtheorem finseq_2_th_94:
" for D be setHIDDENM2 holds (0NUMBERSK6)-tuples-onFINSEQ-2K4 D =XBOOLE-0R4 {TARSKIK1 <*>FINSEQ-1K7 D }"
sorry

mtheorem finseq_2_th_95:
" for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for z be TupleFINSEQ-2M3-of(0NUMBERSK6,D) holds  for t be TupleFINSEQ-2M3-of(i,D) holds z ^FINSEQ-1K9\<^bsub>(D)\<^esub> t =FINSEQ-1R1 t & t ^FINSEQ-1K9\<^bsub>(D)\<^esub> z =FINSEQ-1R1 t"
  using finseq_1_th_34 sorry

mtheorem finseq_2_th_96:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds \<one>\<^sub>M -tuples-onFINSEQ-2K4 D =XBOOLE-0R4 {<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*> where d be ElementSUBSET-1M1-of D :  True  }"
sorry

mlemma finseq_2_lm_6:
" for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for z be TupleFINSEQ-2M3-of(i,D) holds z inTARSKIR2 i -tuples-onFINSEQ-2K4 D"
sorry

mtheorem finseq_2_th_97:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for z be TupleFINSEQ-2M3-of(\<one>\<^sub>M,D) holds  ex d be ElementSUBSET-1M1-of D st z =FINSEQ-1R1 <*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>"
sorry

mtheorem finseq_2_th_98:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d be ElementSUBSET-1M1-of D holds <*FINSEQ-1K13\<^bsub>(D)\<^esub> d*> inTARSKIR2 \<one>\<^sub>M -tuples-onFINSEQ-2K4 D"
sorry

mtheorem finseq_2_th_99:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds \<two>\<^sub>M -tuples-onFINSEQ-2K4 D =XBOOLE-0R4 {<*FINSEQ-1K11 d1,d2 *> where d1 be ElementSUBSET-1M1-of D, d2 be ElementSUBSET-1M1-of D :  True  }"
sorry

mtheorem finseq_2_th_100:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for z be TupleFINSEQ-2M3-of(\<two>\<^sub>M,D) holds  ex d1 be ElementSUBSET-1M1-of D st  ex d2 be ElementSUBSET-1M1-of D st z =FINSEQ-1R1 <*FINSEQ-1K11 d1,d2 *>"
sorry

mtheorem finseq_2_th_101:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d1 be ElementSUBSET-1M1-of D holds  for d2 be ElementSUBSET-1M1-of D holds <*FINSEQ-1K11 d1,d2 *> inTARSKIR2 \<two>\<^sub>M -tuples-onFINSEQ-2K4 D"
sorry

mtheorem finseq_2_th_102:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds \<three>\<^sub>M -tuples-onFINSEQ-2K4 D =XBOOLE-0R4 {<*FINSEQ-1K12 d1,d2,d3 *> where d1 be ElementSUBSET-1M1-of D, d2 be ElementSUBSET-1M1-of D, d3 be ElementSUBSET-1M1-of D :  True  }"
sorry

mtheorem finseq_2_th_103:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for z be TupleFINSEQ-2M3-of(\<three>\<^sub>M,D) holds  ex d1 be ElementSUBSET-1M1-of D st  ex d2 be ElementSUBSET-1M1-of D st  ex d3 be ElementSUBSET-1M1-of D st z =FINSEQ-1R1 <*FINSEQ-1K12 d1,d2,d3 *>"
sorry

mtheorem finseq_2_th_104:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d1 be ElementSUBSET-1M1-of D holds  for d2 be ElementSUBSET-1M1-of D holds  for d3 be ElementSUBSET-1M1-of D holds <*FINSEQ-1K12 d1,d2,d3 *> inTARSKIR2 \<three>\<^sub>M -tuples-onFINSEQ-2K4 D"
sorry

mtheorem finseq_2_th_105:
" for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for j be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds (i +XCMPLX-0K2 j)-tuples-onFINSEQ-2K4 D =XBOOLE-0R4 {z ^FINSEQ-1K9\<^bsub>(D)\<^esub> t where z be TupleFINSEQ-2M3-of(i,D), t be TupleFINSEQ-2M3-of(j,D) :  True  }"
sorry

mtheorem finseq_2_th_106:
" for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for j be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for s be TupleFINSEQ-2M3-of(i +XCMPLX-0K2 j,D) holds  ex z be ElementFINSEQ-2M2\<^bsub>(D)\<^esub>-of i -tuples-onFINSEQ-2K4 D st  ex t be ElementFINSEQ-2M2\<^bsub>(D)\<^esub>-of j -tuples-onFINSEQ-2K4 D st s =FINSEQ-1R1 z ^FINSEQ-1K9\<^bsub>(D)\<^esub> t"
sorry

mtheorem finseq_2_th_107:
" for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for j be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for z be TupleFINSEQ-2M3-of(i,D) holds  for t be TupleFINSEQ-2M3-of(j,D) holds z ^FINSEQ-1K9\<^bsub>(D)\<^esub> t be TupleFINSEQ-2M3-of(i +XCMPLX-0K2 j,D)"
   sorry

mtheorem finseq_2_th_108:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds D * FINSEQ-2K3 =XBOOLE-0R4 unionTARSKIK3 ({i -tuples-onFINSEQ-2K4 D where i be NatNAT-1M1 :  True  })"
sorry

mtheorem finseq_2_th_109:
" for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D9 be  non emptyXBOOLE-0V1\<bar>SubsetSUBSET-1M2-of D holds  for z be TupleFINSEQ-2M3-of(i,D9) holds z be ElementFINSEQ-2M2\<^bsub>(D)\<^esub>-of i -tuples-onFINSEQ-2K4 D"
sorry

mlemma finseq_2_lm_7:
" for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for A be setHIDDENM2 holds  for x be objectHIDDENM1 holds x inHIDDENR3 i -tuples-onFINSEQ-2K4 A implies x be i -elementCARD-1V3\<bar>FinSequenceFINSEQ-1M1"
sorry

mtheorem finseq_2_th_110:
" for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for j be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for A be setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds i -tuples-onFINSEQ-2K4 D =XBOOLE-0R4 j -tuples-onFINSEQ-2K4 A implies i =HIDDENR1 j"
sorry

mtheorem finseq_2_th_111:
" for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds idseqFINSEQ-2K1 i be ElementFINSEQ-2M2\<^bsub>(NATNUMBERSK1)\<^esub>-of i -tuples-onFINSEQ-2K4 NATNUMBERSK1"
sorry

mtheorem finseq_2_th_112:
" for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d be ElementSUBSET-1M1-of D holds i |->FINSEQ-2K2 d be ElementFINSEQ-2M2\<^bsub>(D)\<^esub>-of i -tuples-onFINSEQ-2K4 D"
sorry

mtheorem finseq_2_th_113:
" for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D9 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for z be TupleFINSEQ-2M3-of(i,D) holds  for f be FunctionFUNCT-2M1-of(D,D9) holds f *PARTFUN1K1\<^bsub>(omegaORDINAL1K4,D,D,D9)\<^esub> z be ElementFINSEQ-2M2\<^bsub>(D9)\<^esub>-of i -tuples-onFINSEQ-2K4 D9"
sorry

mtheorem finseq_2_th_114:
" for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for z be TupleFINSEQ-2M3-of(i,D) holds  for f be FunctionFUNCT-2M1-of(SegFINSEQ-1K1 i,SegFINSEQ-1K1 i) holds rngFUNCT-1K2 f =XBOOLE-0R4 SegFINSEQ-1K1 i implies z *PARTFUN1K1\<^bsub>(SegFINSEQ-1K1 i,SegFINSEQ-1K1 i,omegaORDINAL1K4,D)\<^esub> f be ElementFINSEQ-2M2\<^bsub>(D)\<^esub>-of i -tuples-onFINSEQ-2K4 D"
sorry

mtheorem finseq_2_th_115:
" for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for z be TupleFINSEQ-2M3-of(i,D) holds  for f be PermutationFUNCT-2M2-of SegFINSEQ-1K1 i holds z *PARTFUN1K1\<^bsub>(SegFINSEQ-1K1 i,SegFINSEQ-1K1 i,omegaORDINAL1K4,D)\<^esub> f be TupleFINSEQ-2M3-of(i,D)"
sorry

mtheorem finseq_2_th_116:
" for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for z be TupleFINSEQ-2M3-of(i,D) holds  for d be ElementSUBSET-1M1-of D holds (z ^FINSEQ-1K9\<^bsub>(D)\<^esub> (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>)).FUNCT-1K1 (i +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 d"
sorry

mtheorem finseq_2_th_117:
" for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for z be TupleFINSEQ-2M3-of(i +NAT-1K1 \<one>\<^sub>M,D) holds  ex t be ElementFINSEQ-2M2\<^bsub>(D)\<^esub>-of i -tuples-onFINSEQ-2K4 D st  ex d be ElementSUBSET-1M1-of D st z =FINSEQ-1R1 t ^FINSEQ-1K9\<^bsub>(D)\<^esub> (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>)"
sorry

mtheorem finseq_2_th_118:
" for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for z be TupleFINSEQ-2M3-of(i,D) holds z *FUNCT-1K3 idseqFINSEQ-2K1 i =FUNCT-1R1 z"
sorry

mtheorem finseq_2_th_119:
" for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for z1 be TupleFINSEQ-2M3-of(i,D) holds  for z2 be TupleFINSEQ-2M3-of(i,D) holds ( for j be NatNAT-1M1 holds j inTARSKIR2 SegFINSEQ-1K1 i implies z1 .FUNCT-1K1 j =XBOOLE-0R4 z2 .FUNCT-1K1 j) implies z1 =FINSEQ-1R1 z2"
sorry

mtheorem finseq_2_th_120:
" for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D9 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for E be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for F be FunctionFUNCT-2M1-of([:ZFMISC-1K2 D,D9 :],E) holds  for z1 be TupleFINSEQ-2M3-of(i,D) holds  for z2 be TupleFINSEQ-2M3-of(i,D9) holds F .:FUNCOP-1K3(z1,z2) be ElementFINSEQ-2M2\<^bsub>(E)\<^esub>-of i -tuples-onFINSEQ-2K4 E"
sorry

mtheorem finseq_2_th_121:
" for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D9 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for E be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d be ElementSUBSET-1M1-of D holds  for F be FunctionFUNCT-2M1-of([:ZFMISC-1K2 D,D9 :],E) holds  for z be TupleFINSEQ-2M3-of(i,D9) holds F [;]FUNCOP-1K5(d,z) be ElementFINSEQ-2M2\<^bsub>(E)\<^esub>-of i -tuples-onFINSEQ-2K4 E"
sorry

mtheorem finseq_2_th_122:
" for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D9 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for E be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d9 be ElementSUBSET-1M1-of D9 holds  for F be FunctionFUNCT-2M1-of([:ZFMISC-1K2 D,D9 :],E) holds  for z be TupleFINSEQ-2M3-of(i,D) holds F [:]FUNCOP-1K4(z,d9) be ElementFINSEQ-2M2\<^bsub>(E)\<^esub>-of i -tuples-onFINSEQ-2K4 E"
sorry

mtheorem finseq_2_th_123:
" for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for j be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for x be objectHIDDENM1 holds (i +XCMPLX-0K2 j)|->FINSEQ-2K2 x =FINSEQ-1R1 (i |->FINSEQ-2K2 x)^FINSEQ-1K8 (j |->FINSEQ-2K2 x)"
sorry

mtheorem finseq_2_th_124:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for x be TupleFINSEQ-2M3-of(i,D) holds domFINSEQ-1K5 x =XBOOLE-0R4 SegFINSEQ-1K1 i"
sorry

mtheorem finseq_2_th_125:
" for f be FunctionFUNCT-1M1 holds  for x be setHIDDENM2 holds  for y be setHIDDENM2 holds x inTARSKIR2 domRELAT-1K1 f & y inTARSKIR2 domRELAT-1K1 f implies f *FUNCT-1K3 (<*FINSEQ-1K11 x,y *>) =FUNCT-1R1 <*FINSEQ-1K11 f .FUNCT-1K1 x,f .FUNCT-1K1 y *>"
sorry

mtheorem finseq_2_th_126:
" for f be FunctionFUNCT-1M1 holds  for x be setHIDDENM2 holds  for y be setHIDDENM2 holds  for z be setHIDDENM2 holds (x inTARSKIR2 domRELAT-1K1 f & y inTARSKIR2 domRELAT-1K1 f) & z inTARSKIR2 domRELAT-1K1 f implies f *FUNCT-1K3 (<*FINSEQ-1K12 x,y,z *>) =FUNCT-1R1 <*FINSEQ-1K12 f .FUNCT-1K1 x,f .FUNCT-1K1 y,f .FUNCT-1K1 z *>"
sorry

mtheorem finseq_2_th_127:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds rngFUNCT-1K2 (<*FINSEQ-1K11 x1,x2 *>) =XBOOLE-0R4 {TARSKIK2 x1,x2 }"
  using finseq_2_lm_1 sorry

mtheorem finseq_2_th_128:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds rngFUNCT-1K2 (<*FINSEQ-1K12 x1,x2,x3 *>) =XBOOLE-0R4 {ENUMSET1K1 x1,x2,x3 }"
  using finseq_2_lm_2 sorry

(*begin*)
mtheorem finseq_2_th_129:
" for p1 be FinSequenceFINSEQ-1M1 holds  for p2 be FinSequenceFINSEQ-1M1 holds  for q be FinSequenceFINSEQ-1M1 holds (p1 c=RELAT-1R2 q & p2 c=RELAT-1R2 q) & lenFINSEQ-1K4 p1 =XBOOLE-0R4 lenFINSEQ-1K4 p2 implies p1 =FINSEQ-1R1 p2"
sorry

reserve m, n for "NatNAT-1M1"
mtheorem finseq_2_th_130:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for s be FinSequenceFINSEQ-1M3-of D holds s <>HIDDENR2 {}XBOOLE-0K1 implies ( ex w be FinSequenceFINSEQ-1M3-of D st  ex n be ElementSUBSET-1M1-of D st s =FINSEQ-1R1 (<*FINSEQ-1K13\<^bsub>(D)\<^esub> n*>)^FINSEQ-1K9\<^bsub>(D)\<^esub> w)"
sorry

mtheorem finseq_2_cl_9:
  mlet "D be setHIDDENM2"
"cluster note-that functionalFUNCT-1V6 for FinSequenceSetFINSEQ-2M1-of D"
proof
(*coherence*)
  show " for it be FinSequenceSetFINSEQ-2M1-of D holds it be functionalFUNCT-1V6"
    using finseq_2_def_3 sorry
qed "sorry"

syntax FINSEQ_2K5 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ |->FINSEQ-2K5\<^bsub>'( _ ')\<^esub>  _ " [164,0,164]164)
translations "n |->FINSEQ-2K5\<^bsub>(D)\<^esub> d" \<rightharpoonup> "n |->FINSEQ-2K2 d"

mtheorem finseq_2_add_3:
  mlet "D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "n be naturalORDINAL1V7\<bar>NumberORDINAL1M1", "d be ElementSUBSET-1M1-of D"
"cluster n |->FINSEQ-2K2 d as-term-is ElementFINSEQ-2M2\<^bsub>(D)\<^esub>-of n -tuples-onFINSEQ-2K4 D"
proof
(*coherence*)
  show "n |->FINSEQ-2K2 d be ElementFINSEQ-2M2\<^bsub>(D)\<^esub>-of n -tuples-onFINSEQ-2K4 D"
    using finseq_2_th_112 sorry
qed "sorry"

mtheorem finseq_2_th_131:
" for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for z be setHIDDENM2 holds z be TupleFINSEQ-2M3-of(i,D) iff z inTARSKIR2 i -tuples-onFINSEQ-2K4 D"
sorry

mtheorem finseq_2_th_132:
" for A be setHIDDENM2 holds  for i be ElementSUBSET-1M1-of NATNUMBERSK1 holds  for p be FinSequenceFINSEQ-1M1 holds p inTARSKIR2 i -tuples-onFINSEQ-2K4 A iff lenFINSEQ-1K4 p =XBOOLE-0R4 i & rngFUNCT-1K2 p c=TARSKIR1 A"
sorry

mtheorem finseq_2_th_133:
" for A be setHIDDENM2 holds  for i be ElementSUBSET-1M1-of NATNUMBERSK1 holds  for p be FinSequenceFINSEQ-1M3-of A holds p inTARSKIR2 i -tuples-onFINSEQ-2K4 A iff lenFINSEQ-1K4 p =XBOOLE-0R4 i"
sorry

mtheorem finseq_2_th_134:
" for A be setHIDDENM2 holds  for i be ElementSUBSET-1M1-of NATNUMBERSK1 holds i -tuples-onFINSEQ-2K4 A c=TARSKIR1 A * FINSEQ-2K3"
sorry

mtheorem finseq_2_th_135:
" for A be setHIDDENM2 holds  for x be objectHIDDENM1 holds x inHIDDENR3 \<one>\<^sub>M -tuples-onFINSEQ-2K4 A iff ( ex a be setHIDDENM2 st a inTARSKIR2 A & x =HIDDENR1 <*FINSEQ-1K10 a*>)"
sorry

mtheorem finseq_2_th_136:
" for A be setHIDDENM2 holds  for a be objectHIDDENM1 holds <*FINSEQ-1K10 a*> inTARSKIR2 \<one>\<^sub>M -tuples-onFINSEQ-2K4 A implies a inHIDDENR3 A"
sorry

mtheorem finseq_2_th_137:
" for A be setHIDDENM2 holds  for x be objectHIDDENM1 holds x inHIDDENR3 \<two>\<^sub>M -tuples-onFINSEQ-2K4 A iff ( ex a be objectHIDDENM1 st  ex b be objectHIDDENM1 st (a inHIDDENR3 A & b inHIDDENR3 A) & x =HIDDENR1 <*FINSEQ-1K11 a,b *>)"
sorry

mtheorem finseq_2_th_138:
" for A be setHIDDENM2 holds  for a be objectHIDDENM1 holds  for b be objectHIDDENM1 holds <*FINSEQ-1K11 a,b *> inTARSKIR2 \<two>\<^sub>M -tuples-onFINSEQ-2K4 A implies a inHIDDENR3 A & b inHIDDENR3 A"
sorry

mtheorem finseq_2_th_139:
" for A be setHIDDENM2 holds  for x be objectHIDDENM1 holds x inHIDDENR3 \<three>\<^sub>M -tuples-onFINSEQ-2K4 A iff ( ex a be objectHIDDENM1 st  ex b be objectHIDDENM1 st  ex c be objectHIDDENM1 st ((a inHIDDENR3 A & b inHIDDENR3 A) & c inHIDDENR3 A) & x =HIDDENR1 <*FINSEQ-1K12 a,b,c *>)"
sorry

mtheorem finseq_2_th_140:
" for A be setHIDDENM2 holds  for a be objectHIDDENM1 holds  for b be objectHIDDENM1 holds  for c be objectHIDDENM1 holds <*FINSEQ-1K12 a,b,c *> inTARSKIR2 \<three>\<^sub>M -tuples-onFINSEQ-2K4 A implies (a inHIDDENR3 A & b inHIDDENR3 A) & c inHIDDENR3 A"
sorry

mtheorem finseq_2_th_141:
" for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for A be setHIDDENM2 holds  for x be objectHIDDENM1 holds x inHIDDENR3 i -tuples-onFINSEQ-2K4 A implies x be i -elementCARD-1V3\<bar>FinSequenceFINSEQ-1M1"
  using finseq_2_lm_7 sorry

mtheorem finseq_2_th_142:
" for A be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for n be NatNAT-1M1 holds n -tuples-onFINSEQ-2K4 A c=TARSKIR1 A * FINSEQ-2K3"
sorry

mtheorem finseq_2_th_143:
" for x be objectHIDDENM1 holds  for m be NatNAT-1M1 holds  for n be NatNAT-1M1 holds n |->FINSEQ-2K2 x =FINSEQ-1R1 m |->FINSEQ-2K2 x implies n =XBOOLE-0R4 m"
sorry

reserve n for "NatNAT-1M1"
mdef finseq_2_def_5 (" _ #FINSEQ-2K6\<^bsub>'( _ ')\<^esub>" [164,0]164 ) where
  mlet "I be setHIDDENM2", "M be ManySortedSetPBOOLEM1-of I"
"func M #FINSEQ-2K6\<^bsub>(I)\<^esub> \<rightarrow> ManySortedSetPBOOLEM1-of I * FINSEQ-2K3 means
  \<lambda>it.  for i be ElementFINSEQ-2M2\<^bsub>(I)\<^esub>-of I * FINSEQ-2K3 holds it .FUNCT-1K1 i =XBOOLE-0R4 productCARD-3K4 (M *FUNCT-1K3 i)"
proof-
  (*existence*)
    show " ex it be ManySortedSetPBOOLEM1-of I * FINSEQ-2K3 st  for i be ElementFINSEQ-2M2\<^bsub>(I)\<^esub>-of I * FINSEQ-2K3 holds it .FUNCT-1K1 i =XBOOLE-0R4 productCARD-3K4 (M *FUNCT-1K3 i)"
sorry
  (*uniqueness*)
    show " for it1 be ManySortedSetPBOOLEM1-of I * FINSEQ-2K3 holds  for it2 be ManySortedSetPBOOLEM1-of I * FINSEQ-2K3 holds ( for i be ElementFINSEQ-2M2\<^bsub>(I)\<^esub>-of I * FINSEQ-2K3 holds it1 .FUNCT-1K1 i =XBOOLE-0R4 productCARD-3K4 (M *FUNCT-1K3 i)) & ( for i be ElementFINSEQ-2M2\<^bsub>(I)\<^esub>-of I * FINSEQ-2K3 holds it2 .FUNCT-1K1 i =XBOOLE-0R4 productCARD-3K4 (M *FUNCT-1K3 i)) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mtheorem finseq_2_cl_10:
  mlet "I be setHIDDENM2", "M be non-emptyRELAT-1V2\<bar>ManySortedSetPBOOLEM1-of I"
"cluster M #FINSEQ-2K6\<^bsub>(I)\<^esub> as-term-is non-emptyRELAT-1V2"
proof
(*coherence*)
  show "M #FINSEQ-2K6\<^bsub>(I)\<^esub> be non-emptyRELAT-1V2"
sorry
qed "sorry"

mdef finseq_2_def_6 (" *-->FINSEQ-2K7  _ " [164]164 ) where
  mlet "a be setHIDDENM2"
"func  *-->FINSEQ-2K7 a \<rightarrow> sequenceNAT-1M2-of {TARSKIK1 a} * FINSEQ-2K3 means
  \<lambda>it.  for n be NatNAT-1M1 holds it .FUNCT-1K1 n =FINSEQ-1R1 n |->FINSEQ-2K2 a"
proof-
  (*existence*)
    show " ex it be sequenceNAT-1M2-of {TARSKIK1 a} * FINSEQ-2K3 st  for n be NatNAT-1M1 holds it .FUNCT-1K1 n =FINSEQ-1R1 n |->FINSEQ-2K2 a"
sorry
  (*uniqueness*)
    show " for it1 be sequenceNAT-1M2-of {TARSKIK1 a} * FINSEQ-2K3 holds  for it2 be sequenceNAT-1M2-of {TARSKIK1 a} * FINSEQ-2K3 holds ( for n be NatNAT-1M1 holds it1 .FUNCT-1K1 n =FINSEQ-1R1 n |->FINSEQ-2K2 a) & ( for n be NatNAT-1M1 holds it2 .FUNCT-1K1 n =FINSEQ-1R1 n |->FINSEQ-2K2 a) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mtheorem finseq_2_th_144:
" for n be NatNAT-1M1 holds  for a be setHIDDENM2 holds  for b be setHIDDENM2 holds (a .-->FUNCOP-1K17 b)*FUNCT-1K3 (n |->FINSEQ-2K2 a) =FUNCT-1R1 n |->FINSEQ-2K2 b"
sorry

mtheorem finseq_2_th_145:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for n be NatNAT-1M1 holds  for a be setHIDDENM2 holds  for M be ManySortedSetPBOOLEM1-of {TARSKIK1 a} holds M =FUNCT-1R1 a .-->FUNCOP-1K17 D implies ((M #FINSEQ-2K6\<^bsub>({TARSKIK1 a})\<^esub>)*FUNCT-1K3 ( *-->FINSEQ-2K7 a)).FUNCT-1K1 n =XBOOLE-0R4 FuncsFUNCT-2K9(SegFINSEQ-1K2 n,D)"
sorry

mtheorem finseq_2_cl_11:
  mlet "i be naturalORDINAL1V7\<bar>NumberORDINAL1M1"
"cluster i |->FINSEQ-2K5\<^bsub>(omegaORDINAL1K4)\<^esub> (0NUMBERSK6) as-term-is empty-yieldingFUNCT-1V3"
proof
(*coherence*)
  show "i |->FINSEQ-2K5\<^bsub>(omegaORDINAL1K4)\<^esub> (0NUMBERSK6) be empty-yieldingFUNCT-1V3"
sorry
qed "sorry"

mtheorem finseq_2_cl_12:
  mlet "D be setHIDDENM2"
"cluster note-that FinSequence-memberedFINSEQ-1V3 for FinSequenceSetFINSEQ-2M1-of D"
proof
(*coherence*)
  show " for it be FinSequenceSetFINSEQ-2M1-of D holds it be FinSequence-memberedFINSEQ-1V3"
sorry
qed "sorry"

syntax FINSEQ_2K8 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ .FINSEQ-2K8\<^bsub>'( _ , _ ')\<^esub>  _ " [200,0,0,200]200)
translations "f .FINSEQ-2K8\<^bsub>(D,F)\<^esub> n" \<rightharpoonup> "f .FUNCT-1K1 n"

mtheorem finseq_2_add_4:
  mlet "D be setHIDDENM2", "F be FinSequenceSetFINSEQ-2M1-of D", "f be sequenceNAT-1M2-of F", "n be naturalORDINAL1V7\<bar>NumberORDINAL1M1"
"cluster f .FUNCT-1K1 n as-term-is FinSequenceFINSEQ-1M3-of D"
proof
(*coherence*)
  show "f .FUNCT-1K1 n be FinSequenceFINSEQ-1M3-of D"
sorry
qed "sorry"

end
