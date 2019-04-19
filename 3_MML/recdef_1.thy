theory recdef_1
  imports ordinal2 finseq_1 binop_1 domain_1 real_1
   "../mizar_extension/E_number"
begin
(*begin*)
reserve n, m, k for "NatNAT-1M1"
reserve D for " non emptyXBOOLE-0V1\<bar>setHIDDENM2"
reserve Z, x, y, z, y1, y2 for "setHIDDENM2"
reserve p, q for "FinSequenceFINSEQ-1M1"
mlemma recdef_1_lm_1:
" for n be NatNAT-1M1 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for p be FinSequenceFINSEQ-1M3-of D holds \<one>\<^sub>M <=XXREAL-0R1 n & n <=XXREAL-0R1 lenFINSEQ-1K4 p implies p .FUNCT-1K1 n be ElementSUBSET-1M1-of D"
sorry

abbreviation(input) RECDEF_1K1(" _ .RECDEF-1K1  _ " [200,200]200) where
  "p .RECDEF-1K1 n \<equiv> p .FUNCT-1K1 n"

mtheorem recdef_1_add_1:
  mlet "p be natural-valuedVALUED-0V8\<bar>FunctionFUNCT-1M1", "n be setHIDDENM2"
"cluster p .FUNCT-1K1 n as-term-is ElementSUBSET-1M1-of NATNUMBERSK1"
proof
(*coherence*)
  show "p .FUNCT-1K1 n be ElementSUBSET-1M1-of NATNUMBERSK1"
    using ordinal1_def_12 sorry
qed "sorry"

theorem recdef_1_sch_1:
  fixes Af0 Pp3 
  assumes
[ty]: "Af0 be objectHIDDENM1" and
   A1: " for n be NatNAT-1M1 holds  for x be setHIDDENM2 holds  ex y be setHIDDENM2 st Pp3(n,x,y)"
  shows " ex f be FunctionFUNCT-1M1 st (domRELAT-1K1 f =XBOOLE-0R4 NATNUMBERSK1 & f .FUNCT-1K1 (0NUMBERSK6) =HIDDENR1 Af0) & ( for n be NatNAT-1M1 holds Pp3(n,f .FUNCT-1K1 n,f .FUNCT-1K1 (n +NAT-1K1 \<one>\<^sub>M)))"
sorry

theorem recdef_1_sch_2:
  fixes Df0 Af0 Pp3 
  assumes
[ty]: "Df0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
  [ty]: "Af0 be ElementSUBSET-1M1-of Df0" and
   A1: " for n be NatNAT-1M1 holds  for x be ElementSUBSET-1M1-of Df0 holds  ex y be ElementSUBSET-1M1-of Df0 st Pp3(n,x,y)"
  shows " ex f be sequenceNAT-1M2-of Df0 st f .FUNCT-2K3\<^bsub>(omegaORDINAL1K4,Df0)\<^esub> (0NUMBERSK6) =XBOOLE-0R4 Af0 & ( for n be NatNAT-1M1 holds Pp3(n,f .FUNCT-1K1 n,f .FUNCT-2K3\<^bsub>(omegaORDINAL1K4,Df0)\<^esub> (n +NAT-1K1 \<one>\<^sub>M)))"
sorry

mlemma recdef_1_lm_2:
"\<one>\<^sub>M inTARSKIR2 REALNUMBERSK2"
  using numbers_th_19 sorry

theorem recdef_1_sch_3:
  fixes Af0 Nf0 Pp3 
  assumes
[ty]: "Af0 be objectHIDDENM1" and
  [ty]: "Nf0 be NatNAT-1M1" and
   A1: " for n be NatNAT-1M1 holds \<one>\<^sub>M <=XXREAL-0R1 n & n <XXREAL-0R3 Nf0 implies ( for x be setHIDDENM2 holds  ex y be setHIDDENM2 st Pp3(n,x,y))"
  shows " ex p be FinSequenceFINSEQ-1M1 st (lenFINSEQ-1K4 p =XBOOLE-0R4 Nf0 & (p .FUNCT-1K1 \<one>\<^sub>M =HIDDENR1 Af0 or Nf0 =XBOOLE-0R4 0NUMBERSK6)) & ( for n be NatNAT-1M1 holds \<one>\<^sub>M <=XXREAL-0R1 n & n <XXREAL-0R3 Nf0 implies Pp3(n,p .FUNCT-1K1 n,p .FUNCT-1K1 (n +NAT-1K1 \<one>\<^sub>M)))"
sorry

theorem recdef_1_sch_4:
  fixes Df0 Af0 Nf0 Pp3 
  assumes
[ty]: "Df0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
  [ty]: "Af0 be ElementSUBSET-1M1-of Df0" and
  [ty]: "Nf0 be NatNAT-1M1" and
   A1: " for n be NatNAT-1M1 holds \<one>\<^sub>M <=XXREAL-0R1 n & n <XXREAL-0R3 Nf0 implies ( for x be ElementSUBSET-1M1-of Df0 holds  ex y be ElementSUBSET-1M1-of Df0 st Pp3(n,x,y))"
  shows " ex p be FinSequenceFINSEQ-1M3-of Df0 st (lenFINSEQ-1K4 p =XBOOLE-0R4 Nf0 & (p .FUNCT-1K1 \<one>\<^sub>M =XBOOLE-0R4 Af0 or Nf0 =XBOOLE-0R4 0NUMBERSK6)) & ( for n be NatNAT-1M1 holds \<one>\<^sub>M <=XXREAL-0R1 n & n <XXREAL-0R3 Nf0 implies Pp3(n,p .FUNCT-1K1 n,p .FUNCT-1K1 (n +NAT-1K1 \<one>\<^sub>M)))"
sorry

theorem recdef_1_sch_5:
  fixes Sf0 Pp3 
  assumes
[ty]: "Sf0 be FinSequenceFINSEQ-1M1" and
   A1: " for k be NatNAT-1M1 holds  for x be setHIDDENM2 holds \<one>\<^sub>M <=XXREAL-0R1 k & k <XXREAL-0R3 lenFINSEQ-1K4 Sf0 implies ( ex y be setHIDDENM2 st Pp3(Sf0 .FUNCT-1K1 (k +NAT-1K1 \<one>\<^sub>M),x,y))"
  shows " ex x be setHIDDENM2 st  ex p be FinSequenceFINSEQ-1M1 st ((x =XBOOLE-0R4 p .FUNCT-1K1 lenFINSEQ-1K4 p & lenFINSEQ-1K4 p =XBOOLE-0R4 lenFINSEQ-1K4 Sf0) & p .FUNCT-1K1 \<one>\<^sub>M =XBOOLE-0R4 Sf0 .FUNCT-1K1 \<one>\<^sub>M) & ( for k be NatNAT-1M1 holds \<one>\<^sub>M <=XXREAL-0R1 k & k <XXREAL-0R3 lenFINSEQ-1K4 Sf0 implies Pp3(Sf0 .FUNCT-1K1 (k +NAT-1K1 \<one>\<^sub>M),p .FUNCT-1K1 k,p .FUNCT-1K1 (k +NAT-1K1 \<one>\<^sub>M)))"
sorry

theorem recdef_1_sch_6:
  fixes Sf0 Ff2 
  assumes
[ty]: "Sf0 be FinSequenceFINSEQ-1M1" and
  [ty_func]: "\<And> x1 x2. x1 be objectHIDDENM1 \<Longrightarrow> x2 be objectHIDDENM1 \<Longrightarrow> Ff2(x1,x2) be setHIDDENM2"
  shows " ex x be setHIDDENM2 st  ex p be FinSequenceFINSEQ-1M1 st ((x =XBOOLE-0R4 p .FUNCT-1K1 lenFINSEQ-1K4 p & lenFINSEQ-1K4 p =XBOOLE-0R4 lenFINSEQ-1K4 Sf0) & p .FUNCT-1K1 \<one>\<^sub>M =XBOOLE-0R4 Sf0 .FUNCT-1K1 \<one>\<^sub>M) & ( for k be NatNAT-1M1 holds \<one>\<^sub>M <=XXREAL-0R1 k & k <XXREAL-0R3 lenFINSEQ-1K4 Sf0 implies p .FUNCT-1K1 (k +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 Ff2(Sf0 .FUNCT-1K1 (k +NAT-1K1 \<one>\<^sub>M),p .FUNCT-1K1 k))"
sorry

theorem recdef_1_sch_7:
  fixes Af0 Nf0 Ff0 Gf0 Pp3 
  assumes
[ty]: "Af0 be objectHIDDENM1" and
  [ty]: "Nf0 be NatNAT-1M1" and
  [ty]: "Ff0 be FinSequenceFINSEQ-1M1" and
  [ty]: "Gf0 be FinSequenceFINSEQ-1M1" and
   A1: " for n be NatNAT-1M1 holds \<one>\<^sub>M <=XXREAL-0R1 n & n <XXREAL-0R3 Nf0 implies ( for x be setHIDDENM2 holds  for y1 be setHIDDENM2 holds  for y2 be setHIDDENM2 holds Pp3(n,x,y1) & Pp3(n,x,y2) implies y1 =XBOOLE-0R4 y2)" and
   A2: "(lenFINSEQ-1K4 Ff0 =XBOOLE-0R4 Nf0 & (Ff0 .FUNCT-1K1 \<one>\<^sub>M =HIDDENR1 Af0 or Nf0 =XBOOLE-0R4 0NUMBERSK6)) & ( for n be NatNAT-1M1 holds \<one>\<^sub>M <=XXREAL-0R1 n & n <XXREAL-0R3 Nf0 implies Pp3(n,Ff0 .FUNCT-1K1 n,Ff0 .FUNCT-1K1 (n +NAT-1K1 \<one>\<^sub>M)))" and
   A3: "(lenFINSEQ-1K4 Gf0 =XBOOLE-0R4 Nf0 & (Gf0 .FUNCT-1K1 \<one>\<^sub>M =HIDDENR1 Af0 or Nf0 =XBOOLE-0R4 0NUMBERSK6)) & ( for n be NatNAT-1M1 holds \<one>\<^sub>M <=XXREAL-0R1 n & n <XXREAL-0R3 Nf0 implies Pp3(n,Gf0 .FUNCT-1K1 n,Gf0 .FUNCT-1K1 (n +NAT-1K1 \<one>\<^sub>M)))"
  shows "Ff0 =FINSEQ-1R1 Gf0"
sorry

theorem recdef_1_sch_8:
  fixes Df0 Af0 Nf0 Ff0 Gf0 Pp3 
  assumes
[ty]: "Df0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
  [ty]: "Af0 be ElementSUBSET-1M1-of Df0" and
  [ty]: "Nf0 be NatNAT-1M1" and
  [ty]: "Ff0 be FinSequenceFINSEQ-1M3-of Df0" and
  [ty]: "Gf0 be FinSequenceFINSEQ-1M3-of Df0" and
   A1: " for n be NatNAT-1M1 holds \<one>\<^sub>M <=XXREAL-0R1 n & n <XXREAL-0R3 Nf0 implies ( for x be ElementSUBSET-1M1-of Df0 holds  for y1 be ElementSUBSET-1M1-of Df0 holds  for y2 be ElementSUBSET-1M1-of Df0 holds Pp3(n,x,y1) & Pp3(n,x,y2) implies y1 =XBOOLE-0R4 y2)" and
   A2: "(lenFINSEQ-1K4 Ff0 =XBOOLE-0R4 Nf0 & (Ff0 .FUNCT-1K1 \<one>\<^sub>M =XBOOLE-0R4 Af0 or Nf0 =XBOOLE-0R4 0NUMBERSK6)) & ( for n be NatNAT-1M1 holds \<one>\<^sub>M <=XXREAL-0R1 n & n <XXREAL-0R3 Nf0 implies Pp3(n,Ff0 .FUNCT-1K1 n,Ff0 .FUNCT-1K1 (n +NAT-1K1 \<one>\<^sub>M)))" and
   A3: "(lenFINSEQ-1K4 Gf0 =XBOOLE-0R4 Nf0 & (Gf0 .FUNCT-1K1 \<one>\<^sub>M =XBOOLE-0R4 Af0 or Nf0 =XBOOLE-0R4 0NUMBERSK6)) & ( for n be NatNAT-1M1 holds \<one>\<^sub>M <=XXREAL-0R1 n & n <XXREAL-0R3 Nf0 implies Pp3(n,Gf0 .FUNCT-1K1 n,Gf0 .FUNCT-1K1 (n +NAT-1K1 \<one>\<^sub>M)))"
  shows "Ff0 =FINSEQ-1R1 Gf0"
sorry

theorem recdef_1_sch_9:
  fixes Sf0 xf0 yf0 Pp3 
  assumes
[ty]: "Sf0 be FinSequenceFINSEQ-1M1" and
  [ty]: "xf0 be objectHIDDENM1" and
  [ty]: "yf0 be objectHIDDENM1" and
   A1: " for k be NatNAT-1M1 holds  for x be setHIDDENM2 holds  for y1 be setHIDDENM2 holds  for y2 be setHIDDENM2 holds  for z be setHIDDENM2 holds (((\<one>\<^sub>M <=XXREAL-0R1 k & k <XXREAL-0R3 lenFINSEQ-1K4 Sf0) & z =XBOOLE-0R4 Sf0 .FUNCT-1K1 (k +NAT-1K1 \<one>\<^sub>M)) & Pp3(z,x,y1)) & Pp3(z,x,y2) implies y1 =XBOOLE-0R4 y2" and
   A2: " ex p be FinSequenceFINSEQ-1M1 st ((xf0 =HIDDENR1 p .FUNCT-1K1 lenFINSEQ-1K4 p & lenFINSEQ-1K4 p =XBOOLE-0R4 lenFINSEQ-1K4 Sf0) & p .FUNCT-1K1 \<one>\<^sub>M =XBOOLE-0R4 Sf0 .FUNCT-1K1 \<one>\<^sub>M) & ( for k be NatNAT-1M1 holds \<one>\<^sub>M <=XXREAL-0R1 k & k <XXREAL-0R3 lenFINSEQ-1K4 Sf0 implies Pp3(Sf0 .FUNCT-1K1 (k +NAT-1K1 \<one>\<^sub>M),p .FUNCT-1K1 k,p .FUNCT-1K1 (k +NAT-1K1 \<one>\<^sub>M)))" and
   A3: " ex p be FinSequenceFINSEQ-1M1 st ((yf0 =HIDDENR1 p .FUNCT-1K1 lenFINSEQ-1K4 p & lenFINSEQ-1K4 p =XBOOLE-0R4 lenFINSEQ-1K4 Sf0) & p .FUNCT-1K1 \<one>\<^sub>M =XBOOLE-0R4 Sf0 .FUNCT-1K1 \<one>\<^sub>M) & ( for k be NatNAT-1M1 holds \<one>\<^sub>M <=XXREAL-0R1 k & k <XXREAL-0R3 lenFINSEQ-1K4 Sf0 implies Pp3(Sf0 .FUNCT-1K1 (k +NAT-1K1 \<one>\<^sub>M),p .FUNCT-1K1 k,p .FUNCT-1K1 (k +NAT-1K1 \<one>\<^sub>M)))"
  shows "xf0 =HIDDENR1 yf0"
sorry

theorem recdef_1_sch_10:
  fixes Sf0 Ff2 xf0 yf0 
  assumes
[ty]: "Sf0 be FinSequenceFINSEQ-1M1" and
  [ty_func]: "\<And> x1 x2. x1 be objectHIDDENM1 \<Longrightarrow> x2 be objectHIDDENM1 \<Longrightarrow> Ff2(x1,x2) be objectHIDDENM1" and
  [ty]: "xf0 be objectHIDDENM1" and
  [ty]: "yf0 be objectHIDDENM1" and
   A1: " ex p be FinSequenceFINSEQ-1M1 st ((xf0 =HIDDENR1 p .FUNCT-1K1 lenFINSEQ-1K4 p & lenFINSEQ-1K4 p =XBOOLE-0R4 lenFINSEQ-1K4 Sf0) & p .FUNCT-1K1 \<one>\<^sub>M =XBOOLE-0R4 Sf0 .FUNCT-1K1 \<one>\<^sub>M) & ( for k be NatNAT-1M1 holds \<one>\<^sub>M <=XXREAL-0R1 k & k <XXREAL-0R3 lenFINSEQ-1K4 Sf0 implies p .FUNCT-1K1 (k +NAT-1K1 \<one>\<^sub>M) =HIDDENR1 Ff2(Sf0 .FUNCT-1K1 (k +NAT-1K1 \<one>\<^sub>M),p .FUNCT-1K1 k))" and
   A2: " ex p be FinSequenceFINSEQ-1M1 st ((yf0 =HIDDENR1 p .FUNCT-1K1 lenFINSEQ-1K4 p & lenFINSEQ-1K4 p =XBOOLE-0R4 lenFINSEQ-1K4 Sf0) & p .FUNCT-1K1 \<one>\<^sub>M =XBOOLE-0R4 Sf0 .FUNCT-1K1 \<one>\<^sub>M) & ( for k be NatNAT-1M1 holds \<one>\<^sub>M <=XXREAL-0R1 k & k <XXREAL-0R3 lenFINSEQ-1K4 Sf0 implies p .FUNCT-1K1 (k +NAT-1K1 \<one>\<^sub>M) =HIDDENR1 Ff2(Sf0 .FUNCT-1K1 (k +NAT-1K1 \<one>\<^sub>M),p .FUNCT-1K1 k))"
  shows "xf0 =HIDDENR1 yf0"
sorry

theorem recdef_1_sch_11:
  fixes Af0 nf0 Pp3 
  assumes
[ty]: "Af0 be objectHIDDENM1" and
  [ty]: "nf0 be NatNAT-1M1" and
   A1: " for n be NatNAT-1M1 holds  for x be setHIDDENM2 holds  ex y be setHIDDENM2 st Pp3(n,x,y)" and
   A2: " for n be NatNAT-1M1 holds  for x be setHIDDENM2 holds  for y1 be setHIDDENM2 holds  for y2 be setHIDDENM2 holds Pp3(n,x,y1) & Pp3(n,x,y2) implies y1 =XBOOLE-0R4 y2"
  shows "( ex y be setHIDDENM2 st  ex f be FunctionFUNCT-1M1 st ((y =XBOOLE-0R4 f .FUNCT-1K1 nf0 & domRELAT-1K1 f =XBOOLE-0R4 NATNUMBERSK1) & f .FUNCT-1K1 (0NUMBERSK6) =HIDDENR1 Af0) & ( for n be NatNAT-1M1 holds Pp3(n,f .FUNCT-1K1 n,f .FUNCT-1K1 (n +NAT-1K1 \<one>\<^sub>M)))) & ( for y1 be setHIDDENM2 holds  for y2 be setHIDDENM2 holds ( ex f be FunctionFUNCT-1M1 st ((y1 =XBOOLE-0R4 f .FUNCT-1K1 nf0 & domRELAT-1K1 f =XBOOLE-0R4 NATNUMBERSK1) & f .FUNCT-1K1 (0NUMBERSK6) =HIDDENR1 Af0) & ( for n be NatNAT-1M1 holds Pp3(n,f .FUNCT-1K1 n,f .FUNCT-1K1 (n +NAT-1K1 \<one>\<^sub>M)))) & ( ex f be FunctionFUNCT-1M1 st ((y2 =XBOOLE-0R4 f .FUNCT-1K1 nf0 & domRELAT-1K1 f =XBOOLE-0R4 NATNUMBERSK1) & f .FUNCT-1K1 (0NUMBERSK6) =HIDDENR1 Af0) & ( for n be NatNAT-1M1 holds Pp3(n,f .FUNCT-1K1 n,f .FUNCT-1K1 (n +NAT-1K1 \<one>\<^sub>M)))) implies y1 =XBOOLE-0R4 y2)"
sorry

theorem recdef_1_sch_12:
  fixes Af0 nf0 RecFunf2 
  assumes
[ty]: "Af0 be objectHIDDENM1" and
  [ty]: "nf0 be NatNAT-1M1" and
  [ty_func]: "\<And> x1 x2. x1 be objectHIDDENM1 \<Longrightarrow> x2 be objectHIDDENM1 \<Longrightarrow> RecFunf2(x1,x2) be setHIDDENM2"
  shows "( ex y be setHIDDENM2 st  ex f be FunctionFUNCT-1M1 st ((y =XBOOLE-0R4 f .FUNCT-1K1 nf0 & domRELAT-1K1 f =XBOOLE-0R4 NATNUMBERSK1) & f .FUNCT-1K1 (0NUMBERSK6) =HIDDENR1 Af0) & ( for n be NatNAT-1M1 holds f .FUNCT-1K1 (n +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 RecFunf2(n,f .FUNCT-1K1 n))) & ( for y1 be setHIDDENM2 holds  for y2 be setHIDDENM2 holds ( ex f be FunctionFUNCT-1M1 st ((y1 =XBOOLE-0R4 f .FUNCT-1K1 nf0 & domRELAT-1K1 f =XBOOLE-0R4 NATNUMBERSK1) & f .FUNCT-1K1 (0NUMBERSK6) =HIDDENR1 Af0) & ( for n be NatNAT-1M1 holds f .FUNCT-1K1 (n +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 RecFunf2(n,f .FUNCT-1K1 n))) & ( ex f be FunctionFUNCT-1M1 st ((y2 =XBOOLE-0R4 f .FUNCT-1K1 nf0 & domRELAT-1K1 f =XBOOLE-0R4 NATNUMBERSK1) & f .FUNCT-1K1 (0NUMBERSK6) =HIDDENR1 Af0) & ( for n be NatNAT-1M1 holds f .FUNCT-1K1 (n +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 RecFunf2(n,f .FUNCT-1K1 n))) implies y1 =XBOOLE-0R4 y2)"
sorry

theorem recdef_1_sch_13:
  fixes Df0 Af0 nf0 Pp3 
  assumes
[ty]: "Df0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
  [ty]: "Af0 be ElementSUBSET-1M1-of Df0" and
  [ty]: "nf0 be NatNAT-1M1" and
   A1: " for n be NatNAT-1M1 holds  for x be ElementSUBSET-1M1-of Df0 holds  ex y be ElementSUBSET-1M1-of Df0 st Pp3(n,x,y)" and
   A2: " for n be NatNAT-1M1 holds  for x be ElementSUBSET-1M1-of Df0 holds  for y1 be ElementSUBSET-1M1-of Df0 holds  for y2 be ElementSUBSET-1M1-of Df0 holds Pp3(n,x,y1) & Pp3(n,x,y2) implies y1 =XBOOLE-0R4 y2"
  shows "( ex y be ElementSUBSET-1M1-of Df0 st  ex f be sequenceNAT-1M2-of Df0 st (y =XBOOLE-0R4 f .FUNCT-1K1 nf0 & f .FUNCT-2K3\<^bsub>(omegaORDINAL1K4,Df0)\<^esub> (0NUMBERSK6) =XBOOLE-0R4 Af0) & ( for n be NatNAT-1M1 holds Pp3(n,f .FUNCT-1K1 n,f .FUNCT-2K3\<^bsub>(omegaORDINAL1K4,Df0)\<^esub> (n +NAT-1K1 \<one>\<^sub>M)))) & ( for y1 be ElementSUBSET-1M1-of Df0 holds  for y2 be ElementSUBSET-1M1-of Df0 holds ( ex f be sequenceNAT-1M2-of Df0 st (y1 =XBOOLE-0R4 f .FUNCT-1K1 nf0 & f .FUNCT-2K3\<^bsub>(omegaORDINAL1K4,Df0)\<^esub> (0NUMBERSK6) =XBOOLE-0R4 Af0) & ( for n be NatNAT-1M1 holds Pp3(n,f .FUNCT-1K1 n,f .FUNCT-2K3\<^bsub>(omegaORDINAL1K4,Df0)\<^esub> (n +NAT-1K1 \<one>\<^sub>M)))) & ( ex f be sequenceNAT-1M2-of Df0 st (y2 =XBOOLE-0R4 f .FUNCT-1K1 nf0 & f .FUNCT-2K3\<^bsub>(omegaORDINAL1K4,Df0)\<^esub> (0NUMBERSK6) =XBOOLE-0R4 Af0) & ( for n be NatNAT-1M1 holds Pp3(n,f .FUNCT-1K1 n,f .FUNCT-2K3\<^bsub>(omegaORDINAL1K4,Df0)\<^esub> (n +NAT-1K1 \<one>\<^sub>M)))) implies y1 =XBOOLE-0R4 y2)"
sorry

theorem recdef_1_sch_14:
  fixes Df0 Af0 nf0 RecFunf2 
  assumes
[ty]: "Df0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
  [ty]: "Af0 be ElementSUBSET-1M1-of Df0" and
  [ty]: "nf0 be NatNAT-1M1" and
  [ty_func]: "\<And> x1 x2. x1 be objectHIDDENM1 \<Longrightarrow> x2 be objectHIDDENM1 \<Longrightarrow> RecFunf2(x1,x2) be ElementSUBSET-1M1-of Df0"
  shows "( ex y be ElementSUBSET-1M1-of Df0 st  ex f be sequenceNAT-1M2-of Df0 st (y =XBOOLE-0R4 f .FUNCT-1K1 nf0 & f .FUNCT-2K3\<^bsub>(omegaORDINAL1K4,Df0)\<^esub> (0NUMBERSK6) =XBOOLE-0R4 Af0) & ( for n be NatNAT-1M1 holds f .FUNCT-2K3\<^bsub>(omegaORDINAL1K4,Df0)\<^esub> (n +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 RecFunf2(n,f .FUNCT-1K1 n))) & ( for y1 be ElementSUBSET-1M1-of Df0 holds  for y2 be ElementSUBSET-1M1-of Df0 holds ( ex f be sequenceNAT-1M2-of Df0 st (y1 =XBOOLE-0R4 f .FUNCT-1K1 nf0 & f .FUNCT-2K3\<^bsub>(omegaORDINAL1K4,Df0)\<^esub> (0NUMBERSK6) =XBOOLE-0R4 Af0) & ( for n be NatNAT-1M1 holds f .FUNCT-2K3\<^bsub>(omegaORDINAL1K4,Df0)\<^esub> (n +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 RecFunf2(n,f .FUNCT-1K1 n))) & ( ex f be sequenceNAT-1M2-of Df0 st (y2 =XBOOLE-0R4 f .FUNCT-1K1 nf0 & f .FUNCT-2K3\<^bsub>(omegaORDINAL1K4,Df0)\<^esub> (0NUMBERSK6) =XBOOLE-0R4 Af0) & ( for n be NatNAT-1M1 holds f .FUNCT-2K3\<^bsub>(omegaORDINAL1K4,Df0)\<^esub> (n +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 RecFunf2(n,f .FUNCT-1K1 n))) implies y1 =XBOOLE-0R4 y2)"
sorry

theorem recdef_1_sch_15:
  fixes Sf0 Pp3 
  assumes
[ty]: "Sf0 be FinSequenceFINSEQ-1M1" and
   A1: " for k be NatNAT-1M1 holds  for y be setHIDDENM2 holds \<one>\<^sub>M <=XXREAL-0R1 k & k <XXREAL-0R3 lenFINSEQ-1K4 Sf0 implies ( ex z be setHIDDENM2 st Pp3(Sf0 .FUNCT-1K1 (k +NAT-1K1 \<one>\<^sub>M),y,z))" and
   A2: " for k be NatNAT-1M1 holds  for x be setHIDDENM2 holds  for y1 be setHIDDENM2 holds  for y2 be setHIDDENM2 holds  for z be setHIDDENM2 holds (((\<one>\<^sub>M <=XXREAL-0R1 k & k <XXREAL-0R3 lenFINSEQ-1K4 Sf0) & z =XBOOLE-0R4 Sf0 .FUNCT-1K1 (k +NAT-1K1 \<one>\<^sub>M)) & Pp3(z,x,y1)) & Pp3(z,x,y2) implies y1 =XBOOLE-0R4 y2"
  shows "( ex x be setHIDDENM2 st  ex p be FinSequenceFINSEQ-1M1 st ((x =XBOOLE-0R4 p .FUNCT-1K1 lenFINSEQ-1K4 p & lenFINSEQ-1K4 p =XBOOLE-0R4 lenFINSEQ-1K4 Sf0) & p .FUNCT-1K1 \<one>\<^sub>M =XBOOLE-0R4 Sf0 .FUNCT-1K1 \<one>\<^sub>M) & ( for k be NatNAT-1M1 holds \<one>\<^sub>M <=XXREAL-0R1 k & k <XXREAL-0R3 lenFINSEQ-1K4 Sf0 implies Pp3(Sf0 .FUNCT-1K1 (k +NAT-1K1 \<one>\<^sub>M),p .FUNCT-1K1 k,p .FUNCT-1K1 (k +NAT-1K1 \<one>\<^sub>M)))) & ( for x be setHIDDENM2 holds  for y be setHIDDENM2 holds ( ex p be FinSequenceFINSEQ-1M1 st ((x =XBOOLE-0R4 p .FUNCT-1K1 lenFINSEQ-1K4 p & lenFINSEQ-1K4 p =XBOOLE-0R4 lenFINSEQ-1K4 Sf0) & p .FUNCT-1K1 \<one>\<^sub>M =XBOOLE-0R4 Sf0 .FUNCT-1K1 \<one>\<^sub>M) & ( for k be NatNAT-1M1 holds \<one>\<^sub>M <=XXREAL-0R1 k & k <XXREAL-0R3 lenFINSEQ-1K4 Sf0 implies Pp3(Sf0 .FUNCT-1K1 (k +NAT-1K1 \<one>\<^sub>M),p .FUNCT-1K1 k,p .FUNCT-1K1 (k +NAT-1K1 \<one>\<^sub>M)))) & ( ex p be FinSequenceFINSEQ-1M1 st ((y =XBOOLE-0R4 p .FUNCT-1K1 lenFINSEQ-1K4 p & lenFINSEQ-1K4 p =XBOOLE-0R4 lenFINSEQ-1K4 Sf0) & p .FUNCT-1K1 \<one>\<^sub>M =XBOOLE-0R4 Sf0 .FUNCT-1K1 \<one>\<^sub>M) & ( for k be NatNAT-1M1 holds \<one>\<^sub>M <=XXREAL-0R1 k & k <XXREAL-0R3 lenFINSEQ-1K4 Sf0 implies Pp3(Sf0 .FUNCT-1K1 (k +NAT-1K1 \<one>\<^sub>M),p .FUNCT-1K1 k,p .FUNCT-1K1 (k +NAT-1K1 \<one>\<^sub>M)))) implies x =XBOOLE-0R4 y)"
sorry

theorem recdef_1_sch_16:
  fixes Sf0 Ff2 
  assumes
[ty]: "Sf0 be FinSequenceFINSEQ-1M1" and
  [ty_func]: "\<And> x1 x2. x1 be objectHIDDENM1 \<Longrightarrow> x2 be objectHIDDENM1 \<Longrightarrow> Ff2(x1,x2) be setHIDDENM2"
  shows "( ex x be setHIDDENM2 st  ex p be FinSequenceFINSEQ-1M1 st ((x =XBOOLE-0R4 p .FUNCT-1K1 lenFINSEQ-1K4 p & lenFINSEQ-1K4 p =XBOOLE-0R4 lenFINSEQ-1K4 Sf0) & p .FUNCT-1K1 \<one>\<^sub>M =XBOOLE-0R4 Sf0 .FUNCT-1K1 \<one>\<^sub>M) & ( for k be NatNAT-1M1 holds \<one>\<^sub>M <=XXREAL-0R1 k & k <XXREAL-0R3 lenFINSEQ-1K4 Sf0 implies p .FUNCT-1K1 (k +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 Ff2(Sf0 .FUNCT-1K1 (k +NAT-1K1 \<one>\<^sub>M),p .FUNCT-1K1 k))) & ( for x be setHIDDENM2 holds  for y be setHIDDENM2 holds ( ex p be FinSequenceFINSEQ-1M1 st ((x =XBOOLE-0R4 p .FUNCT-1K1 lenFINSEQ-1K4 p & lenFINSEQ-1K4 p =XBOOLE-0R4 lenFINSEQ-1K4 Sf0) & p .FUNCT-1K1 \<one>\<^sub>M =XBOOLE-0R4 Sf0 .FUNCT-1K1 \<one>\<^sub>M) & ( for k be NatNAT-1M1 holds \<one>\<^sub>M <=XXREAL-0R1 k & k <XXREAL-0R3 lenFINSEQ-1K4 Sf0 implies p .FUNCT-1K1 (k +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 Ff2(Sf0 .FUNCT-1K1 (k +NAT-1K1 \<one>\<^sub>M),p .FUNCT-1K1 k))) & ( ex p be FinSequenceFINSEQ-1M1 st ((y =XBOOLE-0R4 p .FUNCT-1K1 lenFINSEQ-1K4 p & lenFINSEQ-1K4 p =XBOOLE-0R4 lenFINSEQ-1K4 Sf0) & p .FUNCT-1K1 \<one>\<^sub>M =XBOOLE-0R4 Sf0 .FUNCT-1K1 \<one>\<^sub>M) & ( for k be NatNAT-1M1 holds \<one>\<^sub>M <=XXREAL-0R1 k & k <XXREAL-0R3 lenFINSEQ-1K4 Sf0 implies p .FUNCT-1K1 (k +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 Ff2(Sf0 .FUNCT-1K1 (k +NAT-1K1 \<one>\<^sub>M),p .FUNCT-1K1 k))) implies x =XBOOLE-0R4 y)"
sorry

theorem recdef_1_sch_17:
  fixes Df0 Nf0 Pp2 
  assumes
[ty]: "Df0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
  [ty]: "Nf0 be NatNAT-1M1" and
   A1: " for k be NatNAT-1M1 holds k inTARSKIR2 SegFINSEQ-1K2 Nf0 implies ( ex x be ElementSUBSET-1M1-of Df0 st Pp2(k,x))"
  shows " ex p be FinSequenceFINSEQ-1M3-of Df0 st domFINSEQ-1K5 p =XBOOLE-0R4 SegFINSEQ-1K2 Nf0 & ( for k be NatNAT-1M1 holds k inTARSKIR2 SegFINSEQ-1K2 Nf0 implies Pp2(k,p /.PARTFUN1K7\<^bsub>(Df0)\<^esub> k))"
sorry

theorem recdef_1_sch_18:
  fixes Df0 Af0 Nf0 Pp3 
  assumes
[ty]: "Df0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
  [ty]: "Af0 be ElementSUBSET-1M1-of Df0" and
  [ty]: "Nf0 be ElementSUBSET-1M1-of NATNUMBERSK1" and
   A1: " for n be NatNAT-1M1 holds \<one>\<^sub>M <=XXREAL-0R1 n & n <=XXREAL-0R1 Nf0 -XCMPLX-0K6 \<one>\<^sub>M implies ( for x be ElementSUBSET-1M1-of Df0 holds  ex y be ElementSUBSET-1M1-of Df0 st Pp3(n,x,y))"
  shows " ex p be FinSequenceFINSEQ-1M3-of Df0 st (lenFINSEQ-1K4 p =XBOOLE-0R4 Nf0 & (p /.PARTFUN1K7\<^bsub>(Df0)\<^esub> \<one>\<^sub>M =XBOOLE-0R4 Af0 or Nf0 =XBOOLE-0R4 0NUMBERSK6)) & ( for n be NatNAT-1M1 holds \<one>\<^sub>M <=XXREAL-0R1 n & n <=XXREAL-0R1 Nf0 -XCMPLX-0K6 \<one>\<^sub>M implies Pp3(n,p /.PARTFUN1K7\<^bsub>(Df0)\<^esub> n,p /.PARTFUN1K7\<^bsub>(Df0)\<^esub> (n +NAT-1K1 \<one>\<^sub>M)))"
sorry

end
