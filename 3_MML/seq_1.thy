theory seq_1
  imports valued_1 absvalue
   "../mizar_extension/E_number"
begin
(*begin*)
reserve f for "FunctionFUNCT-1M1"
reserve n, k, n1 for "NatNAT-1M1"
reserve r, p for "RealXREAL-0M1"
reserve x, y, z for "objectHIDDENM1"
syntax SEQ_1M1 :: "Ty" ("Real-SequenceSEQ-1M1" 70)
translations "Real-SequenceSEQ-1M1" \<rightharpoonup> "sequenceNAT-1M2-of REALNUMBERSK2"

reserve seq, seq1, seq2, seq3, seq9, seq19 for "Real-SequenceSEQ-1M1"
mtheorem seq_1_th_1:
" for f be FunctionFUNCT-1M1 holds f be Real-SequenceSEQ-1M1 iff domRELAT-1K1 f =XBOOLE-0R4 NATNUMBERSK1 & ( for x be objectHIDDENM1 holds x inHIDDENR3 NATNUMBERSK1 implies f .FUNCT-1K1 x be realXREAL-0V1)"
sorry

mtheorem seq_1_th_2:
" for f be FunctionFUNCT-1M1 holds f be Real-SequenceSEQ-1M1 iff domRELAT-1K1 f =XBOOLE-0R4 NATNUMBERSK1 & ( for n be NatNAT-1M1 holds f .FUNCT-1K1 n be realXREAL-0V1)"
sorry

mtheorem seq_1_cl_1:
"cluster non-zeroORDINAL1V9 for PartFuncPARTFUN1M1-of(NATNUMBERSK1,REALNUMBERSK2)"
proof
(*existence*)
  show " ex it be PartFuncPARTFUN1M1-of(NATNUMBERSK1,REALNUMBERSK2) st it be non-zeroORDINAL1V9"
sorry
qed "sorry"

mtheorem seq_1_th_3:
" for f be non-zeroORDINAL1V9\<bar>PartFuncPARTFUN1M1-of(NATNUMBERSK1,REALNUMBERSK2) holds rngRELSET-1K2\<^bsub>(REALNUMBERSK2)\<^esub> f c=TARSKIR1 REALNUMBERSK2 \\SUBSET-1K6 {TARSKIK1 0NUMBERSK6 }"
  using ordinal1_def_15 zfmisc_1_th_34 sorry

mtheorem seq_1_th_4:
" for seq be Real-SequenceSEQ-1M1 holds seq be non-zeroORDINAL1V9 iff ( for x be objectHIDDENM1 holds x inHIDDENR3 NATNUMBERSK1 implies seq .FUNCT-1K1 x <>HIDDENR2 0NUMBERSK6)"
sorry

mtheorem seq_1_th_5:
" for seq be Real-SequenceSEQ-1M1 holds seq be non-zeroORDINAL1V9 iff ( for n be NatNAT-1M1 holds seq .NAT-1K8\<^bsub>(REALNUMBERSK2)\<^esub> n <>HIDDENR2 0NUMBERSK6)"
sorry

mtheorem seq_1_th_6:
" for r be RealXREAL-0M1 holds  ex seq be Real-SequenceSEQ-1M1 st rngRELSET-1K2\<^bsub>(REALNUMBERSK2)\<^esub> seq =XBOOLE-0R4 {TARSKIK1 r}"
sorry

theorem seq_1_sch_1:
  fixes Ff1 
  assumes
[ty_func]: "\<And> x1. x1 be objectHIDDENM1 \<Longrightarrow> Ff1(x1) be RealXREAL-0M1"
  shows " ex seq be Real-SequenceSEQ-1M1 st  for n be NatNAT-1M1 holds seq .NAT-1K8\<^bsub>(REALNUMBERSK2)\<^esub> n =COMPLEX1R1 Ff1(n)"
sorry

theorem seq_1_sch_2:
  fixes Df0 Cf0 Pp2 
  assumes
[ty]: "Df0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
  [ty]: "Cf0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
  shows " ex f be PartFuncPARTFUN1M1-of(Df0,Cf0) st ( for d be ElementSUBSET-1M1-of Df0 holds d inTARSKIR2 domRELSET-1K1\<^bsub>(Df0)\<^esub> f iff ( ex c be ElementSUBSET-1M1-of Cf0 st Pp2(d,c))) & ( for d be ElementSUBSET-1M1-of Df0 holds d inTARSKIR2 domRELSET-1K1\<^bsub>(Df0)\<^esub> f implies Pp2(d,f .FUNCT-1K1 d))"
sorry

theorem seq_1_sch_3:
  fixes Df0 Cf0 Ff1 Pp1 
  assumes
[ty]: "Df0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
  [ty]: "Cf0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
  [ty_func]: "\<And> x1. x1 be objectHIDDENM1 \<Longrightarrow> Ff1(x1) be ElementSUBSET-1M1-of Cf0"
  shows " ex f be PartFuncPARTFUN1M1-of(Df0,Cf0) st ( for d be ElementSUBSET-1M1-of Df0 holds d inTARSKIR2 domRELSET-1K1\<^bsub>(Df0)\<^esub> f iff Pp1(d)) & ( for d be ElementSUBSET-1M1-of Df0 holds d inTARSKIR2 domRELSET-1K1\<^bsub>(Df0)\<^esub> f implies f .FUNCT-1K1 d =XBOOLE-0R4 Ff1(d))"
sorry

theorem seq_1_sch_4:
  fixes Cf0 Df0 Xf0 Ff1 
  assumes
[ty]: "Cf0 be setHIDDENM2" and
  [ty]: "Df0 be setHIDDENM2" and
  [ty]: "Xf0 be setHIDDENM2" and
  [ty_func]: "\<And> x1. x1 be objectHIDDENM1 \<Longrightarrow> Ff1(x1) be objectHIDDENM1"
  shows " for f be PartFuncPARTFUN1M1-of(Cf0,Df0) holds  for g be PartFuncPARTFUN1M1-of(Cf0,Df0) holds (domRELSET-1K1\<^bsub>(Cf0)\<^esub> f =XBOOLE-0R4 Xf0 & ( for c be ElementSUBSET-1M1-of Cf0 holds c inTARSKIR2 domRELSET-1K1\<^bsub>(Cf0)\<^esub> f implies f .FUNCT-1K1 c =HIDDENR1 Ff1(c))) & (domRELSET-1K1\<^bsub>(Cf0)\<^esub> g =XBOOLE-0R4 Xf0 & ( for c be ElementSUBSET-1M1-of Cf0 holds c inTARSKIR2 domRELSET-1K1\<^bsub>(Cf0)\<^esub> g implies g .FUNCT-1K1 c =HIDDENR1 Ff1(c))) implies f =RELSET-1R2\<^bsub>(Cf0,Df0)\<^esub> g"
sorry

mtheorem seq_1_th_7:
" for seq be Real-SequenceSEQ-1M1 holds  for seq1 be Real-SequenceSEQ-1M1 holds  for seq2 be Real-SequenceSEQ-1M1 holds seq =FUNCT-2R2\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> seq1 +VALUED-1K3\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq2 iff ( for n be NatNAT-1M1 holds seq .NAT-1K8\<^bsub>(REALNUMBERSK2)\<^esub> n =COMPLEX1R1 seq1 .NAT-1K8\<^bsub>(REALNUMBERSK2)\<^esub> n +REAL-1K3 seq2 .NAT-1K8\<^bsub>(REALNUMBERSK2)\<^esub> n)"
sorry

mtheorem seq_1_th_8:
" for seq be Real-SequenceSEQ-1M1 holds  for seq1 be Real-SequenceSEQ-1M1 holds  for seq2 be Real-SequenceSEQ-1M1 holds seq =FUNCT-2R2\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> seq1 (#)VALUED-1K21\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq2 iff ( for n be NatNAT-1M1 holds seq .NAT-1K8\<^bsub>(REALNUMBERSK2)\<^esub> n =COMPLEX1R1 seq1 .NAT-1K8\<^bsub>(REALNUMBERSK2)\<^esub> n *REAL-1K4 seq2 .NAT-1K8\<^bsub>(REALNUMBERSK2)\<^esub> n)"
sorry

mtheorem seq_1_th_9:
" for r be RealXREAL-0M1 holds  for seq1 be Real-SequenceSEQ-1M1 holds  for seq2 be Real-SequenceSEQ-1M1 holds seq1 =FUNCT-2R2\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> r (#)VALUED-1K28\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> seq2 iff ( for n be NatNAT-1M1 holds seq1 .NAT-1K8\<^bsub>(REALNUMBERSK2)\<^esub> n =COMPLEX1R1 r *XCMPLX-0K3 seq2 .NAT-1K8\<^bsub>(REALNUMBERSK2)\<^esub> n)"
sorry

mtheorem seq_1_th_10:
" for seq1 be Real-SequenceSEQ-1M1 holds  for seq2 be Real-SequenceSEQ-1M1 holds seq1 =FUNCT-2R2\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> -VALUED-1K34\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> seq2 iff ( for n be NatNAT-1M1 holds seq1 .NAT-1K8\<^bsub>(REALNUMBERSK2)\<^esub> n =COMPLEX1R1 -REAL-1K1 seq2 .NAT-1K8\<^bsub>(REALNUMBERSK2)\<^esub> n)"
sorry

mtheorem seq_1_th_11:
" for seq1 be Real-SequenceSEQ-1M1 holds  for seq2 be Real-SequenceSEQ-1M1 holds seq1 -VALUED-1K49\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq2 =FUNCT-2R2\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> seq1 +VALUED-1K3\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> (-VALUED-1K34\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> seq2)"
   sorry

mtheorem seq_1_th_12:
" for seq be Real-SequenceSEQ-1M1 holds  for seq1 be Real-SequenceSEQ-1M1 holds seq1 =FUNCT-2R2\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> absVALUED-1K59\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> seq iff ( for n be NatNAT-1M1 holds seq1 .NAT-1K8\<^bsub>(REALNUMBERSK2)\<^esub> n =COMPLEX1R1 |.COMPLEX1K10 seq .NAT-1K8\<^bsub>(REALNUMBERSK2)\<^esub> n.|)"
sorry

mtheorem seq_1_th_13:
" for seq1 be Real-SequenceSEQ-1M1 holds  for seq2 be Real-SequenceSEQ-1M1 holds  for seq3 be Real-SequenceSEQ-1M1 holds (seq1 +VALUED-1K3\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq2)+VALUED-1K3\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq3 =FUNCT-2R2\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> seq1 +VALUED-1K3\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> (seq2 +VALUED-1K3\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq3)"
sorry

mtheorem seq_1_th_14:
" for seq1 be Real-SequenceSEQ-1M1 holds  for seq2 be Real-SequenceSEQ-1M1 holds  for seq3 be Real-SequenceSEQ-1M1 holds (seq1 (#)VALUED-1K21\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq2)(#)VALUED-1K21\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq3 =FUNCT-2R2\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> seq1 (#)VALUED-1K21\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> (seq2 (#)VALUED-1K21\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq3)"
sorry

mtheorem seq_1_th_15:
" for seq1 be Real-SequenceSEQ-1M1 holds  for seq2 be Real-SequenceSEQ-1M1 holds  for seq3 be Real-SequenceSEQ-1M1 holds (seq1 +VALUED-1K3\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq2)(#)VALUED-1K21\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq3 =FUNCT-2R2\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> seq1 (#)VALUED-1K21\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq3 +VALUED-1K3\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq2 (#)VALUED-1K21\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq3"
sorry

mtheorem seq_1_th_16:
" for seq1 be Real-SequenceSEQ-1M1 holds  for seq2 be Real-SequenceSEQ-1M1 holds  for seq3 be Real-SequenceSEQ-1M1 holds seq3 (#)VALUED-1K21\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> (seq1 +VALUED-1K3\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq2) =FUNCT-2R2\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> seq3 (#)VALUED-1K21\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq1 +VALUED-1K3\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq3 (#)VALUED-1K21\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq2"
  using seq_1_th_15 sorry

mtheorem seq_1_th_17:
" for seq be Real-SequenceSEQ-1M1 holds -VALUED-1K34\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> seq =FUNCT-2R2\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> (-XCMPLX-0K4 \<one>\<^sub>M)(#)VALUED-1K28\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> seq"
   sorry

mtheorem seq_1_th_18:
" for r be RealXREAL-0M1 holds  for seq1 be Real-SequenceSEQ-1M1 holds  for seq2 be Real-SequenceSEQ-1M1 holds r (#)VALUED-1K28\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> (seq1 (#)VALUED-1K21\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq2) =FUNCT-2R2\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> (r (#)VALUED-1K28\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> seq1)(#)VALUED-1K21\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq2"
sorry

mtheorem seq_1_th_19:
" for r be RealXREAL-0M1 holds  for seq1 be Real-SequenceSEQ-1M1 holds  for seq2 be Real-SequenceSEQ-1M1 holds r (#)VALUED-1K28\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> (seq1 (#)VALUED-1K21\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq2) =FUNCT-2R2\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> seq1 (#)VALUED-1K21\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> (r (#)VALUED-1K28\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> seq2)"
sorry

mtheorem seq_1_th_20:
" for seq1 be Real-SequenceSEQ-1M1 holds  for seq2 be Real-SequenceSEQ-1M1 holds  for seq3 be Real-SequenceSEQ-1M1 holds (seq1 -VALUED-1K49\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq2)(#)VALUED-1K21\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq3 =FUNCT-2R2\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> seq1 (#)VALUED-1K21\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq3 -VALUED-1K49\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq2 (#)VALUED-1K21\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq3"
sorry

mtheorem seq_1_th_21:
" for seq1 be Real-SequenceSEQ-1M1 holds  for seq2 be Real-SequenceSEQ-1M1 holds  for seq3 be Real-SequenceSEQ-1M1 holds seq3 (#)VALUED-1K21\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq1 -VALUED-1K49\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq3 (#)VALUED-1K21\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq2 =FUNCT-2R2\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> seq3 (#)VALUED-1K21\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> (seq1 -VALUED-1K49\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq2)"
  using seq_1_th_20 sorry

mtheorem seq_1_th_22:
" for r be RealXREAL-0M1 holds  for seq1 be Real-SequenceSEQ-1M1 holds  for seq2 be Real-SequenceSEQ-1M1 holds r (#)VALUED-1K28\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> (seq1 +VALUED-1K3\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq2) =FUNCT-2R2\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> r (#)VALUED-1K28\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> seq1 +VALUED-1K3\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> r (#)VALUED-1K28\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> seq2"
sorry

mtheorem seq_1_th_23:
" for r be RealXREAL-0M1 holds  for p be RealXREAL-0M1 holds  for seq be Real-SequenceSEQ-1M1 holds (r *XCMPLX-0K3 p)(#)VALUED-1K28\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> seq =FUNCT-2R2\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> r (#)VALUED-1K28\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> (p (#)VALUED-1K28\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> seq)"
sorry

mtheorem seq_1_th_24:
" for r be RealXREAL-0M1 holds  for seq1 be Real-SequenceSEQ-1M1 holds  for seq2 be Real-SequenceSEQ-1M1 holds r (#)VALUED-1K28\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> (seq1 -VALUED-1K49\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq2) =FUNCT-2R2\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> r (#)VALUED-1K28\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> seq1 -VALUED-1K49\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> r (#)VALUED-1K28\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> seq2"
sorry

mtheorem seq_1_th_25:
" for r be RealXREAL-0M1 holds  for seq be Real-SequenceSEQ-1M1 holds  for seq1 be Real-SequenceSEQ-1M1 holds r (#)VALUED-1K28\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> (seq1 /\<inverse>VALUED-1K54\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq) =FUNCT-2R2\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> (r (#)VALUED-1K28\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> seq1)/\<inverse>VALUED-1K54\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq"
sorry

mtheorem seq_1_th_26:
" for seq1 be Real-SequenceSEQ-1M1 holds  for seq2 be Real-SequenceSEQ-1M1 holds  for seq3 be Real-SequenceSEQ-1M1 holds seq1 -VALUED-1K49\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> (seq2 +VALUED-1K3\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq3) =FUNCT-2R2\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> (seq1 -VALUED-1K49\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq2)-VALUED-1K49\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq3"
sorry

mtheorem seq_1_th_27:
" for seq be Real-SequenceSEQ-1M1 holds \<one>\<^sub>M (#)VALUED-1K28\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> seq =FUNCT-2R2\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> seq"
sorry

(*\$CT*)
mtheorem seq_1_th_29:
" for seq1 be Real-SequenceSEQ-1M1 holds  for seq2 be Real-SequenceSEQ-1M1 holds seq1 -VALUED-1K49\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> (-VALUED-1K34\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> seq2) =FUNCT-2R2\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> seq1 +VALUED-1K3\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq2"
   sorry

mtheorem seq_1_th_30:
" for seq1 be Real-SequenceSEQ-1M1 holds  for seq2 be Real-SequenceSEQ-1M1 holds  for seq3 be Real-SequenceSEQ-1M1 holds seq1 -VALUED-1K49\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> (seq2 -VALUED-1K49\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq3) =FUNCT-2R2\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> (seq1 -VALUED-1K49\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq2)+VALUED-1K3\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq3"
sorry

mtheorem seq_1_th_31:
" for seq1 be Real-SequenceSEQ-1M1 holds  for seq2 be Real-SequenceSEQ-1M1 holds  for seq3 be Real-SequenceSEQ-1M1 holds seq1 +VALUED-1K3\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> (seq2 -VALUED-1K49\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq3) =FUNCT-2R2\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> (seq1 +VALUED-1K3\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq2)-VALUED-1K49\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq3"
sorry

mtheorem seq_1_th_32:
" for seq1 be Real-SequenceSEQ-1M1 holds  for seq2 be Real-SequenceSEQ-1M1 holds (-VALUED-1K34\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> seq1)(#)VALUED-1K21\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq2 =FUNCT-2R2\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> -VALUED-1K34\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> seq1 (#)VALUED-1K21\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq2 & seq1 (#)VALUED-1K21\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> (-VALUED-1K34\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> seq2) =FUNCT-2R2\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> -VALUED-1K34\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> seq1 (#)VALUED-1K21\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq2"
  using seq_1_th_18 sorry

mtheorem seq_1_th_33:
" for seq be Real-SequenceSEQ-1M1 holds seq be non-zeroORDINAL1V9 implies seq \<inverse>VALUED-1K39\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> be non-zeroORDINAL1V9"
sorry

(*\$CT*)
mtheorem seq_1_th_35:
" for seq be Real-SequenceSEQ-1M1 holds  for seq1 be Real-SequenceSEQ-1M1 holds seq be non-zeroORDINAL1V9 & seq1 be non-zeroORDINAL1V9 iff seq (#)VALUED-1K21\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq1 be non-zeroORDINAL1V9"
sorry

mtheorem seq_1_th_36:
" for seq be Real-SequenceSEQ-1M1 holds  for seq1 be Real-SequenceSEQ-1M1 holds seq \<inverse>VALUED-1K39\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> (#)VALUED-1K21\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq1 \<inverse>VALUED-1K39\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> =FUNCT-2R2\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> (seq (#)VALUED-1K21\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq1)\<inverse>VALUED-1K39\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub>"
sorry

mtheorem seq_1_th_37:
" for seq be Real-SequenceSEQ-1M1 holds  for seq1 be Real-SequenceSEQ-1M1 holds seq be non-zeroORDINAL1V9 implies (seq1 /\<inverse>VALUED-1K54\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq)(#)VALUED-1K21\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq =FUNCT-2R2\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> seq1"
sorry

mtheorem seq_1_th_38:
" for seq be Real-SequenceSEQ-1M1 holds  for seq1 be Real-SequenceSEQ-1M1 holds  for seq9 be Real-SequenceSEQ-1M1 holds  for seq19 be Real-SequenceSEQ-1M1 holds (seq9 /\<inverse>VALUED-1K54\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq)(#)VALUED-1K21\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> (seq19 /\<inverse>VALUED-1K54\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq1) =FUNCT-2R2\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> (seq9 (#)VALUED-1K21\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq19)/\<inverse>VALUED-1K54\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> (seq (#)VALUED-1K21\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq1)"
sorry

mtheorem seq_1_th_39:
" for seq be Real-SequenceSEQ-1M1 holds  for seq1 be Real-SequenceSEQ-1M1 holds seq be non-zeroORDINAL1V9 & seq1 be non-zeroORDINAL1V9 implies seq /\<inverse>VALUED-1K54\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq1 be non-zeroORDINAL1V9"
sorry

mtheorem seq_1_th_40:
" for seq be Real-SequenceSEQ-1M1 holds  for seq1 be Real-SequenceSEQ-1M1 holds (seq /\<inverse>VALUED-1K54\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq1)\<inverse>VALUED-1K39\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> =FUNCT-2R2\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> seq1 /\<inverse>VALUED-1K54\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq"
sorry

mtheorem seq_1_th_41:
" for seq be Real-SequenceSEQ-1M1 holds  for seq1 be Real-SequenceSEQ-1M1 holds  for seq2 be Real-SequenceSEQ-1M1 holds seq2 (#)VALUED-1K21\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> (seq1 /\<inverse>VALUED-1K54\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq) =FUNCT-2R2\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> (seq2 (#)VALUED-1K21\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq1)/\<inverse>VALUED-1K54\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq"
sorry

mtheorem seq_1_th_42:
" for seq be Real-SequenceSEQ-1M1 holds  for seq1 be Real-SequenceSEQ-1M1 holds  for seq2 be Real-SequenceSEQ-1M1 holds seq2 /\<inverse>VALUED-1K54\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> (seq /\<inverse>VALUED-1K54\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq1) =FUNCT-2R2\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> (seq2 (#)VALUED-1K21\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq1)/\<inverse>VALUED-1K54\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq"
sorry

mtheorem seq_1_th_43:
" for seq be Real-SequenceSEQ-1M1 holds  for seq1 be Real-SequenceSEQ-1M1 holds  for seq2 be Real-SequenceSEQ-1M1 holds seq1 be non-zeroORDINAL1V9 implies seq2 /\<inverse>VALUED-1K54\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq =FUNCT-2R2\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> (seq2 (#)VALUED-1K21\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq1)/\<inverse>VALUED-1K54\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> (seq (#)VALUED-1K21\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq1)"
sorry

mtheorem seq_1_th_44:
" for r be RealXREAL-0M1 holds  for seq be Real-SequenceSEQ-1M1 holds r <>HIDDENR2 0NUMBERSK6 & seq be non-zeroORDINAL1V9 implies r (#)VALUED-1K28\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> seq be non-zeroORDINAL1V9"
sorry

mtheorem seq_1_th_45:
" for seq be Real-SequenceSEQ-1M1 holds seq be non-zeroORDINAL1V9 implies -VALUED-1K34\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> seq be non-zeroORDINAL1V9"
  using seq_1_th_44 sorry

mtheorem seq_1_th_46:
" for r be RealXREAL-0M1 holds  for seq be Real-SequenceSEQ-1M1 holds (r (#)VALUED-1K28\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> seq)\<inverse>VALUED-1K39\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> =FUNCT-2R2\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> r \<inverse>XCMPLX-0K5 (#)VALUED-1K28\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> seq \<inverse>VALUED-1K39\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub>"
sorry

mlemma seq_1_lm_1:
"(-XCMPLX-0K4 \<one>\<^sub>M)\<inverse>XCMPLX-0K5 =COMPLEX1R1 -XCMPLX-0K4 \<one>\<^sub>M"
   sorry

mtheorem seq_1_th_47:
" for seq be Real-SequenceSEQ-1M1 holds (-VALUED-1K34\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> seq)\<inverse>VALUED-1K39\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> =FUNCT-2R2\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> (-XCMPLX-0K4 \<one>\<^sub>M)(#)VALUED-1K28\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> seq \<inverse>VALUED-1K39\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub>"
  using seq_1_lm_1 seq_1_th_46 sorry

mtheorem seq_1_th_48:
" for seq be Real-SequenceSEQ-1M1 holds  for seq1 be Real-SequenceSEQ-1M1 holds -VALUED-1K34\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> seq1 /\<inverse>VALUED-1K54\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq =FUNCT-2R2\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> (-VALUED-1K34\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> seq1)/\<inverse>VALUED-1K54\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq & seq1 /\<inverse>VALUED-1K54\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> (-VALUED-1K34\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> seq) =FUNCT-2R2\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> -VALUED-1K34\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> seq1 /\<inverse>VALUED-1K54\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq"
sorry

mtheorem seq_1_th_49:
" for seq be Real-SequenceSEQ-1M1 holds  for seq1 be Real-SequenceSEQ-1M1 holds  for seq19 be Real-SequenceSEQ-1M1 holds seq1 /\<inverse>VALUED-1K54\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq +VALUED-1K3\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq19 /\<inverse>VALUED-1K54\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq =FUNCT-2R2\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> (seq1 +VALUED-1K3\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq19)/\<inverse>VALUED-1K54\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq & seq1 /\<inverse>VALUED-1K54\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq -VALUED-1K49\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq19 /\<inverse>VALUED-1K54\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq =FUNCT-2R2\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> (seq1 -VALUED-1K49\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq19)/\<inverse>VALUED-1K54\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq"
sorry

mtheorem seq_1_th_50:
" for seq be Real-SequenceSEQ-1M1 holds  for seq1 be Real-SequenceSEQ-1M1 holds  for seq9 be Real-SequenceSEQ-1M1 holds  for seq19 be Real-SequenceSEQ-1M1 holds seq be non-zeroORDINAL1V9 & seq9 be non-zeroORDINAL1V9 implies seq1 /\<inverse>VALUED-1K54\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq +VALUED-1K3\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq19 /\<inverse>VALUED-1K54\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq9 =FUNCT-2R2\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> (seq1 (#)VALUED-1K21\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq9 +VALUED-1K3\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq19 (#)VALUED-1K21\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq)/\<inverse>VALUED-1K54\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> (seq (#)VALUED-1K21\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq9) & seq1 /\<inverse>VALUED-1K54\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq -VALUED-1K49\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq19 /\<inverse>VALUED-1K54\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq9 =FUNCT-2R2\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> (seq1 (#)VALUED-1K21\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq9 -VALUED-1K49\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq19 (#)VALUED-1K21\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq)/\<inverse>VALUED-1K54\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> (seq (#)VALUED-1K21\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq9)"
sorry

mtheorem seq_1_th_51:
" for seq be Real-SequenceSEQ-1M1 holds  for seq1 be Real-SequenceSEQ-1M1 holds  for seq9 be Real-SequenceSEQ-1M1 holds  for seq19 be Real-SequenceSEQ-1M1 holds (seq19 /\<inverse>VALUED-1K54\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq)/\<inverse>VALUED-1K54\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> (seq9 /\<inverse>VALUED-1K54\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq1) =FUNCT-2R2\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> (seq19 (#)VALUED-1K21\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq1)/\<inverse>VALUED-1K54\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> (seq (#)VALUED-1K21\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq9)"
sorry

mtheorem seq_1_th_52:
" for seq be Real-SequenceSEQ-1M1 holds  for seq9 be Real-SequenceSEQ-1M1 holds absVALUED-1K59\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> (seq (#)VALUED-1K21\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq9) =FUNCT-2R2\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> absVALUED-1K59\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> seq (#)VALUED-1K21\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> absVALUED-1K59\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> seq9"
sorry

mtheorem seq_1_th_53:
" for seq be Real-SequenceSEQ-1M1 holds seq be non-zeroORDINAL1V9 implies absVALUED-1K59\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> seq be non-zeroORDINAL1V9"
sorry

mtheorem seq_1_th_54:
" for seq be Real-SequenceSEQ-1M1 holds absVALUED-1K59\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> seq \<inverse>VALUED-1K39\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> =FUNCT-2R2\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> absVALUED-1K59\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> (seq \<inverse>VALUED-1K39\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub>)"
sorry

mtheorem seq_1_th_55:
" for seq be Real-SequenceSEQ-1M1 holds  for seq9 be Real-SequenceSEQ-1M1 holds absVALUED-1K59\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> (seq9 /\<inverse>VALUED-1K54\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq) =FUNCT-2R2\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> absVALUED-1K59\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> seq9 /\<inverse>VALUED-1K54\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> absVALUED-1K59\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> seq"
sorry

mtheorem seq_1_th_56:
" for r be RealXREAL-0M1 holds  for seq be Real-SequenceSEQ-1M1 holds absVALUED-1K59\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> (r (#)VALUED-1K28\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> seq) =FUNCT-2R2\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> (|.COMPLEX1K10 r.|)(#)VALUED-1K28\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> absVALUED-1K59\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> seq"
sorry

mdef seq_1_def_1 ("seq-constSEQ-1K1  _ " [164]164 ) where
  mlet "b be RealXREAL-0M1"
"func seq-constSEQ-1K1 b \<rightarrow> Real-SequenceSEQ-1M1 equals
  NATNUMBERSK1 -->FUNCOP-1K7 b"
proof-
  (*coherence*)
    show "NATNUMBERSK1 -->FUNCOP-1K7 b be Real-SequenceSEQ-1M1"
sorry
qed "sorry"

mtheorem seq_1_cl_2:
  mlet "b be RealXREAL-0M1"
"cluster seq-constSEQ-1K1 b as-term-is constantFUNCT-1V5"
proof
(*coherence*)
  show "seq-constSEQ-1K1 b be constantFUNCT-1V5"
     sorry
qed "sorry"

mtheorem seq_1_cl_3:
  mlet "b be  non zeroORDINAL1V8\<bar>RealXREAL-0M1"
"cluster seq-constSEQ-1K1 b as-term-is non-zeroORDINAL1V9"
proof
(*coherence*)
  show "seq-constSEQ-1K1 b be non-zeroORDINAL1V9"
sorry
qed "sorry"

mtheorem seq_1_cl_4:
"cluster constantFUNCT-1V5 for Real-SequenceSEQ-1M1"
proof
(*existence*)
  show " ex it be Real-SequenceSEQ-1M1 st it be constantFUNCT-1V5"
sorry
qed "sorry"

mtheorem seq_1_th_57:
" for a be RealXREAL-0M1 holds  for k be NatNAT-1M1 holds (seq-constSEQ-1K1 a).NAT-1K8\<^bsub>(REALNUMBERSK2)\<^esub> k =COMPLEX1R1 a"
  using ordinal1_def_12 funcop_1_th_7 sorry

end
