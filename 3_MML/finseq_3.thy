theory finseq_3
  imports finseqop card_2 int_1 grfunc_1
   "../mizar_extension/E_number"
begin
(*begin*)
reserve p, q, r for "FinSequenceFINSEQ-1M1"
reserve u, v, x, y, y1, y2, z for "objectHIDDENM1"
reserve A, D, X, Y for "setHIDDENM2"
reserve i, j, k, l, m, n for "NatNAT-1M1"
mtheorem finseq_3_th_1:
"SegFINSEQ-1K2 \<three>\<^sub>M =XBOOLE-0R4 {ENUMSET1K1 \<one>\<^sub>M,\<two>\<^sub>M,\<three>\<^sub>M }"
sorry

mtheorem finseq_3_th_2:
"SegFINSEQ-1K2 \<four>\<^sub>M =XBOOLE-0R4 {ENUMSET1K2 \<one>\<^sub>M,\<two>\<^sub>M,\<three>\<^sub>M,\<four>\<^sub>M }"
sorry

mtheorem finseq_3_th_3:
"SegFINSEQ-1K2 \<five>\<^sub>M =XBOOLE-0R4 {ENUMSET1K3 \<one>\<^sub>M,\<two>\<^sub>M,\<three>\<^sub>M,\<four>\<^sub>M,\<five>\<^sub>M }"
sorry

mtheorem finseq_3_th_4:
"SegFINSEQ-1K2 \<six>\<^sub>M =XBOOLE-0R4 {ENUMSET1K4 \<one>\<^sub>M,\<two>\<^sub>M,\<three>\<^sub>M,\<four>\<^sub>M,\<five>\<^sub>M,\<six>\<^sub>M }"
sorry

mtheorem finseq_3_th_5:
"SegFINSEQ-1K2 \<seven>\<^sub>M =XBOOLE-0R4 {ENUMSET1K5 \<one>\<^sub>M,\<two>\<^sub>M,\<three>\<^sub>M,\<four>\<^sub>M,\<five>\<^sub>M,\<six>\<^sub>M,\<seven>\<^sub>M }"
sorry

mtheorem finseq_3_th_6:
"SegFINSEQ-1K2 \<eight>\<^sub>M =XBOOLE-0R4 {ENUMSET1K6 \<one>\<^sub>M,\<two>\<^sub>M,\<three>\<^sub>M,\<four>\<^sub>M,\<five>\<^sub>M,\<six>\<^sub>M,\<seven>\<^sub>M,\<eight>\<^sub>M }"
sorry

mtheorem finseq_3_th_7:
" for k be NatNAT-1M1 holds SegFINSEQ-1K2 k =XBOOLE-0R4 {}XBOOLE-0K1 iff  not k inTARSKIR2 SegFINSEQ-1K2 k"
sorry

mtheorem finseq_3_th_8:
" for k be NatNAT-1M1 holds  not k +NAT-1K1 \<one>\<^sub>M inTARSKIR2 SegFINSEQ-1K2 k"
sorry

mtheorem finseq_3_th_9:
" for k be NatNAT-1M1 holds  for n be NatNAT-1M1 holds k <>HIDDENR2 0NUMBERSK6 implies k inTARSKIR2 SegFINSEQ-1K2 (k +XCMPLX-0K2 n)"
sorry

mtheorem finseq_3_th_10:
" for k be NatNAT-1M1 holds  for n be NatNAT-1M1 holds k +XCMPLX-0K2 n inTARSKIR2 SegFINSEQ-1K2 k implies n =XBOOLE-0R4 0NUMBERSK6"
sorry

mtheorem finseq_3_th_11:
" for k be NatNAT-1M1 holds  for n be NatNAT-1M1 holds k <XXREAL-0R3 n implies k +NAT-1K1 \<one>\<^sub>M inTARSKIR2 SegFINSEQ-1K2 n"
sorry

mtheorem finseq_3_th_12:
" for k be NatNAT-1M1 holds  for m be NatNAT-1M1 holds  for n be NatNAT-1M1 holds k inTARSKIR2 SegFINSEQ-1K2 n & m <XXREAL-0R3 k implies k -XCMPLX-0K6 m inTARSKIR2 SegFINSEQ-1K2 n"
sorry

mtheorem finseq_3_th_13:
" for k be NatNAT-1M1 holds  for n be NatNAT-1M1 holds k -XCMPLX-0K6 n inTARSKIR2 SegFINSEQ-1K2 k iff n <XXREAL-0R3 k"
sorry

mtheorem finseq_3_th_14:
" for k be NatNAT-1M1 holds SegFINSEQ-1K2 k missesXBOOLE-0R1 {TARSKIK1 k +NAT-1K1 \<one>\<^sub>M }"
sorry

mtheorem finseq_3_th_15:
" for k be NatNAT-1M1 holds SegFINSEQ-1K2 (k +NAT-1K1 \<one>\<^sub>M) \\SUBSET-1K7\<^bsub>(omegaORDINAL1K4)\<^esub> SegFINSEQ-1K2 k =XBOOLE-0R4 {TARSKIK1 k +NAT-1K1 \<one>\<^sub>M }"
sorry

mtheorem finseq_3_th_16:
" for k be NatNAT-1M1 holds SegFINSEQ-1K2 k <>HIDDENR2 SegFINSEQ-1K2 (k +NAT-1K1 \<one>\<^sub>M)"
  using finseq_3_th_8 finseq_1_th_4 sorry

mtheorem finseq_3_th_17:
" for k be NatNAT-1M1 holds  for n be NatNAT-1M1 holds SegFINSEQ-1K2 k =XBOOLE-0R4 SegFINSEQ-1K2 (k +XCMPLX-0K2 n) implies n =XBOOLE-0R4 0NUMBERSK6"
  using finseq_3_th_10 finseq_1_th_3 sorry

mtheorem finseq_3_th_18:
" for k be NatNAT-1M1 holds  for n be NatNAT-1M1 holds SegFINSEQ-1K2 k c=TARSKIR1 SegFINSEQ-1K2 (k +XCMPLX-0K2 n)"
  using finseq_1_th_5 nat_1_th_12 sorry

mtheorem finseq_3_th_19:
" for k be NatNAT-1M1 holds  for n be NatNAT-1M1 holds (SegFINSEQ-1K2 k,SegFINSEQ-1K2 n)are-c=-comparableXBOOLE-0R3"
sorry

mtheorem finseq_3_th_20:
" for k be NatNAT-1M1 holds  for y be objectHIDDENM1 holds SegFINSEQ-1K2 k =XBOOLE-0R4 {TARSKIK1 y} implies k =XBOOLE-0R4 \<one>\<^sub>M & y =HIDDENR1 \<one>\<^sub>M"
sorry

mtheorem finseq_3_th_21:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for k be NatNAT-1M1 holds SegFINSEQ-1K2 k =XBOOLE-0R4 {TARSKIK2 x,y } & x <>HIDDENR2 y implies k =XBOOLE-0R4 \<two>\<^sub>M & {TARSKIK2 x,y } =XBOOLE-0R4 {TARSKIK2 \<one>\<^sub>M,\<two>\<^sub>M }"
sorry

mtheorem finseq_3_th_22:
" for p be FinSequenceFINSEQ-1M1 holds  for q be FinSequenceFINSEQ-1M1 holds  for x be objectHIDDENM1 holds x inHIDDENR3 domRELSET-1K1\<^bsub>(omegaORDINAL1K4)\<^esub> p implies x inHIDDENR3 domRELSET-1K1\<^bsub>(omegaORDINAL1K4)\<^esub> (p ^FINSEQ-1K8 q)"
sorry

mtheorem finseq_3_th_23:
" for p be FinSequenceFINSEQ-1M1 holds  for x be objectHIDDENM1 holds x inHIDDENR3 domRELSET-1K1\<^bsub>(omegaORDINAL1K4)\<^esub> p implies x be ElementSUBSET-1M1-of NATNUMBERSK1"
   sorry

mtheorem finseq_3_th_24:
" for p be FinSequenceFINSEQ-1M1 holds  for x be objectHIDDENM1 holds x inHIDDENR3 domRELSET-1K1\<^bsub>(omegaORDINAL1K4)\<^esub> p implies x <>HIDDENR2 0NUMBERSK6"
sorry

mtheorem finseq_3_th_25:
" for p be FinSequenceFINSEQ-1M1 holds  for n be NatNAT-1M1 holds n inTARSKIR2 domRELSET-1K1\<^bsub>(omegaORDINAL1K4)\<^esub> p iff \<one>\<^sub>M <=XXREAL-0R1 n & n <=XXREAL-0R1 lenFINSEQ-1K4 p"
sorry

mtheorem finseq_3_th_26:
" for p be FinSequenceFINSEQ-1M1 holds  for n be NatNAT-1M1 holds n inTARSKIR2 domRELSET-1K1\<^bsub>(omegaORDINAL1K4)\<^esub> p iff n -XCMPLX-0K6 \<one>\<^sub>M be ElementSUBSET-1M1-of NATNUMBERSK1 & lenFINSEQ-1K4 p -XCMPLX-0K6 n be ElementSUBSET-1M1-of NATNUMBERSK1"
sorry

(*\$CT 2*)
mtheorem finseq_3_th_29:
" for p be FinSequenceFINSEQ-1M1 holds  for q be FinSequenceFINSEQ-1M1 holds lenFINSEQ-1K4 p =XBOOLE-0R4 lenFINSEQ-1K4 q iff domRELSET-1K1\<^bsub>(omegaORDINAL1K4)\<^esub> p =XBOOLE-0R4 domRELSET-1K1\<^bsub>(omegaORDINAL1K4)\<^esub> q"
sorry

mtheorem finseq_3_th_30:
" for p be FinSequenceFINSEQ-1M1 holds  for q be FinSequenceFINSEQ-1M1 holds lenFINSEQ-1K4 p <=XXREAL-0R1 lenFINSEQ-1K4 q iff domRELSET-1K1\<^bsub>(omegaORDINAL1K4)\<^esub> p c=TARSKIR1 domRELSET-1K1\<^bsub>(omegaORDINAL1K4)\<^esub> q"
sorry

mtheorem finseq_3_th_31:
" for p be FinSequenceFINSEQ-1M1 holds  for x be objectHIDDENM1 holds x inHIDDENR3 rngFUNCT-1K2 p implies \<one>\<^sub>M inTARSKIR2 domRELSET-1K1\<^bsub>(omegaORDINAL1K4)\<^esub> p"
sorry

mtheorem finseq_3_th_32:
" for p be FinSequenceFINSEQ-1M1 holds rngFUNCT-1K2 p <>HIDDENR2 {}XBOOLE-0K1 implies \<one>\<^sub>M inTARSKIR2 domRELSET-1K1\<^bsub>(omegaORDINAL1K4)\<^esub> p"
sorry

mtheorem finseq_3_th_33:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds {}XBOOLE-0K1 <>HIDDENR2 <*FINSEQ-1K11 x,y *>"
   sorry

mtheorem finseq_3_th_34:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for z be objectHIDDENM1 holds {}XBOOLE-0K1 <>HIDDENR2 <*FINSEQ-1K12 x,y,z *>"
   sorry

mtheorem finseq_3_th_35:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for z be objectHIDDENM1 holds <*FINSEQ-1K10 x*> <>HIDDENR2 <*FINSEQ-1K11 y,z *>"
sorry

mtheorem finseq_3_th_36:
" for u be objectHIDDENM1 holds  for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for z be objectHIDDENM1 holds <*FINSEQ-1K10 u*> <>HIDDENR2 <*FINSEQ-1K12 x,y,z *>"
sorry

mtheorem finseq_3_th_37:
" for u be objectHIDDENM1 holds  for v be objectHIDDENM1 holds  for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for z be objectHIDDENM1 holds <*FINSEQ-1K11 u,v *> <>HIDDENR2 <*FINSEQ-1K12 x,y,z *>"
sorry

mtheorem finseq_3_th_38:
" for p be FinSequenceFINSEQ-1M1 holds  for q be FinSequenceFINSEQ-1M1 holds  for r be FinSequenceFINSEQ-1M1 holds (lenFINSEQ-1K4 r =XBOOLE-0R4 lenFINSEQ-1K4 p +NAT-1K1 lenFINSEQ-1K4 q & ( for k be NatNAT-1M1 holds k inTARSKIR2 domRELSET-1K1\<^bsub>(omegaORDINAL1K4)\<^esub> p implies r .FUNCT-1K1 k =XBOOLE-0R4 p .FUNCT-1K1 k)) & ( for k be NatNAT-1M1 holds k inTARSKIR2 domRELSET-1K1\<^bsub>(omegaORDINAL1K4)\<^esub> q implies r .FUNCT-1K1 (lenFINSEQ-1K4 p +XCMPLX-0K2 k) =XBOOLE-0R4 q .FUNCT-1K1 k) implies r =FINSEQ-1R1 p ^FINSEQ-1K8 q"
sorry

mlemma finseq_3_lm_1:
" for A be setHIDDENM2 holds  for k be NatNAT-1M1 holds A c=TARSKIR1 SegFINSEQ-1K2 k implies SgmFINSEQ-1K15 A be one-to-oneFUNCT-1V2"
sorry

mtheorem finseq_3_th_39:
" for k be NatNAT-1M1 holds  for A be finiteFINSET-1V1\<bar>setHIDDENM2 holds A c=TARSKIR1 SegFINSEQ-1K2 k implies lenFINSEQ-1K4 (SgmFINSEQ-1K15 A) =XBOOLE-0R4 cardCARD-1K4 A"
sorry

mtheorem finseq_3_th_40:
" for k be NatNAT-1M1 holds  for A be finiteFINSET-1V1\<bar>setHIDDENM2 holds A c=TARSKIR1 SegFINSEQ-1K2 k implies domRELSET-1K1\<^bsub>(omegaORDINAL1K4)\<^esub> (SgmFINSEQ-1K15 A) =XBOOLE-0R4 SegFINSEQ-1K2 (cardCARD-1K4 A)"
sorry

mtheorem finseq_3_th_41:
" for X be setHIDDENM2 holds  for i be NatNAT-1M1 holds  for k be NatNAT-1M1 holds  for l be NatNAT-1M1 holds  for m be NatNAT-1M1 holds  for n be NatNAT-1M1 holds ((((X c=TARSKIR1 SegFINSEQ-1K2 i & k <XXREAL-0R3 l) & \<one>\<^sub>M <=XXREAL-0R1 n) & m <=XXREAL-0R1 lenFINSEQ-1K4 (SgmFINSEQ-1K15 X)) & SgmFINSEQ-1K15 X .FUNCT-1K1 m =XBOOLE-0R4 k) & SgmFINSEQ-1K15 X .FUNCT-1K1 n =XBOOLE-0R4 l implies m <XXREAL-0R3 n"
sorry

mtheorem finseq_3_th_42:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for i be NatNAT-1M1 holds  for j be NatNAT-1M1 holds X c=TARSKIR1 SegFINSEQ-1K2 i & Y c=TARSKIR1 SegFINSEQ-1K2 j implies (( for m be NatNAT-1M1 holds  for n be NatNAT-1M1 holds m inTARSKIR2 X & n inTARSKIR2 Y implies m <XXREAL-0R3 n) iff SgmFINSEQ-1K15 (X \\/XBOOLE-0K2 Y) =RELSET-1R2\<^bsub>(omegaORDINAL1K4,omegaORDINAL1K4)\<^esub> SgmFINSEQ-1K15 X ^FINSEQ-1K9\<^bsub>(omegaORDINAL1K4)\<^esub> SgmFINSEQ-1K15 Y)"
sorry

mtheorem finseq_3_th_43:
"SgmFINSEQ-1K15 ({}XBOOLE-0K1) =FINSEQ-1R1 {}XBOOLE-0K1"
sorry

mtheorem finseq_3_th_44:
" for n be NatNAT-1M1 holds 0NUMBERSK6 <>HIDDENR2 n implies SgmFINSEQ-1K15 {TARSKIK1 n} =FINSEQ-1R1 <*FINSEQ-1K10 n*>"
sorry

mtheorem finseq_3_th_45:
" for m be NatNAT-1M1 holds  for n be NatNAT-1M1 holds 0NUMBERSK6 <XXREAL-0R3 n & n <XXREAL-0R3 m implies SgmFINSEQ-1K15 {TARSKIK2 n,m } =FINSEQ-1R1 <*FINSEQ-1K11 n,m *>"
sorry

mtheorem finseq_3_th_46:
" for k be NatNAT-1M1 holds lenFINSEQ-1K4 (SgmFINSEQ-1K15 (SegFINSEQ-1K2 k)) =XBOOLE-0R4 k"
sorry

mlemma finseq_3_lm_2:
" for k be NatNAT-1M1 holds SgmFINSEQ-1K15 (SegFINSEQ-1K2 (k +NAT-1K1 0NUMBERSK6)) |PARTFUN1K2\<^bsub>(omegaORDINAL1K4,omegaORDINAL1K4)\<^esub> SegFINSEQ-1K2 k =RELSET-1R2\<^bsub>(omegaORDINAL1K4,omegaORDINAL1K4)\<^esub> SgmFINSEQ-1K15 (SegFINSEQ-1K2 k)"
sorry

mlemma finseq_3_lm_3:
" for n be NatNAT-1M1 holds ( for k be NatNAT-1M1 holds SgmFINSEQ-1K15 (SegFINSEQ-1K2 (k +XCMPLX-0K2 n)) |PARTFUN1K2\<^bsub>(omegaORDINAL1K4,omegaORDINAL1K4)\<^esub> SegFINSEQ-1K2 k =RELSET-1R2\<^bsub>(omegaORDINAL1K4,omegaORDINAL1K4)\<^esub> SgmFINSEQ-1K15 (SegFINSEQ-1K2 k)) implies ( for k be NatNAT-1M1 holds SgmFINSEQ-1K15 (SegFINSEQ-1K2 (k +NAT-1K1 (n +NAT-1K1 \<one>\<^sub>M))) |PARTFUN1K2\<^bsub>(omegaORDINAL1K4,omegaORDINAL1K4)\<^esub> SegFINSEQ-1K2 k =RELSET-1R2\<^bsub>(omegaORDINAL1K4,omegaORDINAL1K4)\<^esub> SgmFINSEQ-1K15 (SegFINSEQ-1K2 k))"
sorry

mlemma finseq_3_lm_4:
" for n be NatNAT-1M1 holds  for k be NatNAT-1M1 holds SgmFINSEQ-1K15 (SegFINSEQ-1K2 (k +XCMPLX-0K2 n)) |PARTFUN1K2\<^bsub>(omegaORDINAL1K4,omegaORDINAL1K4)\<^esub> SegFINSEQ-1K2 k =RELSET-1R2\<^bsub>(omegaORDINAL1K4,omegaORDINAL1K4)\<^esub> SgmFINSEQ-1K15 (SegFINSEQ-1K2 k)"
sorry

mtheorem finseq_3_th_47:
" for k be NatNAT-1M1 holds  for n be NatNAT-1M1 holds SgmFINSEQ-1K15 (SegFINSEQ-1K2 (k +XCMPLX-0K2 n)) |PARTFUN1K2\<^bsub>(omegaORDINAL1K4,omegaORDINAL1K4)\<^esub> SegFINSEQ-1K2 k =RELSET-1R2\<^bsub>(omegaORDINAL1K4,omegaORDINAL1K4)\<^esub> SgmFINSEQ-1K15 (SegFINSEQ-1K2 k)"
  using finseq_3_lm_4 sorry

mlemma finseq_3_lm_5:
" for k be NatNAT-1M1 holds SgmFINSEQ-1K15 (SegFINSEQ-1K2 k) =FINSEQ-1R1 idseqFINSEQ-2K1 k implies SgmFINSEQ-1K15 (SegFINSEQ-1K2 (k +NAT-1K1 \<one>\<^sub>M)) =FINSEQ-1R1 idseqFINSEQ-2K1 (k +NAT-1K1 \<one>\<^sub>M)"
sorry

mtheorem finseq_3_th_48:
" for k be NatNAT-1M1 holds SgmFINSEQ-1K15 (SegFINSEQ-1K2 k) =FINSEQ-1R1 idseqFINSEQ-2K1 k"
sorry

mtheorem finseq_3_th_49:
" for p be FinSequenceFINSEQ-1M1 holds  for n be NatNAT-1M1 holds p |RELAT-1K8 SegFINSEQ-1K2 n =FUNCT-1R1 p iff lenFINSEQ-1K4 p <=XXREAL-0R1 n"
sorry

mtheorem finseq_3_th_50:
" for k be NatNAT-1M1 holds  for n be NatNAT-1M1 holds idseqFINSEQ-2K1 (n +XCMPLX-0K2 k) |RELAT-1K8 SegFINSEQ-1K2 n =FUNCT-1R1 idseqFINSEQ-2K1 n"
sorry

mtheorem finseq_3_th_51:
" for m be NatNAT-1M1 holds  for n be NatNAT-1M1 holds idseqFINSEQ-2K1 n |RELAT-1K8 SegFINSEQ-1K2 m =FUNCT-1R1 idseqFINSEQ-2K1 m iff m <=XXREAL-0R1 n"
sorry

mtheorem finseq_3_th_52:
" for m be NatNAT-1M1 holds  for n be NatNAT-1M1 holds idseqFINSEQ-2K1 n |RELAT-1K8 SegFINSEQ-1K2 m =FUNCT-1R1 idseqFINSEQ-2K1 n iff n <=XXREAL-0R1 m"
sorry

mtheorem finseq_3_th_53:
" for p be FinSequenceFINSEQ-1M1 holds  for q be FinSequenceFINSEQ-1M1 holds  for k be NatNAT-1M1 holds  for l be NatNAT-1M1 holds lenFINSEQ-1K4 p =XBOOLE-0R4 k +XCMPLX-0K2 l & q =FUNCT-1R1 p |RELAT-1K8 SegFINSEQ-1K2 k implies lenFINSEQ-1K4 q =XBOOLE-0R4 k"
sorry

mtheorem finseq_3_th_54:
" for p be FinSequenceFINSEQ-1M1 holds  for q be FinSequenceFINSEQ-1M1 holds  for k be NatNAT-1M1 holds  for l be NatNAT-1M1 holds lenFINSEQ-1K4 p =XBOOLE-0R4 k +XCMPLX-0K2 l & q =FUNCT-1R1 p |RELAT-1K8 SegFINSEQ-1K2 k implies domRELSET-1K1\<^bsub>(omegaORDINAL1K4)\<^esub> q =XBOOLE-0R4 SegFINSEQ-1K2 k"
sorry

mtheorem finseq_3_th_55:
" for p be FinSequenceFINSEQ-1M1 holds  for q be FinSequenceFINSEQ-1M1 holds  for k be NatNAT-1M1 holds lenFINSEQ-1K4 p =XBOOLE-0R4 k +NAT-1K1 \<one>\<^sub>M & q =FUNCT-1R1 p |RELAT-1K8 SegFINSEQ-1K2 k implies p =FINSEQ-1R1 q ^FINSEQ-1K8 (<*FINSEQ-1K10 p .FUNCT-1K1 (k +NAT-1K1 \<one>\<^sub>M)*>)"
sorry

mtheorem finseq_3_th_56:
" for p be FinSequenceFINSEQ-1M1 holds  for X be setHIDDENM2 holds p |RELAT-1K8 X be FinSequenceFINSEQ-1M1 iff ( ex k be ElementSUBSET-1M1-of NATNUMBERSK1 st X /\\SUBSET-1K9\<^bsub>(omegaORDINAL1K4)\<^esub> domRELSET-1K1\<^bsub>(omegaORDINAL1K4)\<^esub> p =XBOOLE-0R4 SegFINSEQ-1K2 k)"
sorry

mtheorem finseq_3_th_57:
" for p be FinSequenceFINSEQ-1M1 holds  for q be FinSequenceFINSEQ-1M1 holds  for A be setHIDDENM2 holds cardCARD-1K4 ((p ^FINSEQ-1K8 q)\<inverse>FUNCT-1K6 A) =XBOOLE-0R4 cardCARD-1K4 (p \<inverse>FUNCT-1K6 A) +NAT-1K1 cardCARD-1K4 (q \<inverse>FUNCT-1K6 A)"
sorry

mtheorem finseq_3_th_58:
" for p be FinSequenceFINSEQ-1M1 holds  for q be FinSequenceFINSEQ-1M1 holds  for A be setHIDDENM2 holds p \<inverse>FUNCT-1K6 A c=TARSKIR1 (p ^FINSEQ-1K8 q)\<inverse>FUNCT-1K6 A"
sorry

mdef finseq_3_def_1 (" _ -FINSEQ-3K1  _ " [132,132]132 ) where
  mlet "p be FinSequenceFINSEQ-1M1", "A be setHIDDENM2"
"func p -FINSEQ-3K1 A \<rightarrow> FinSequenceFINSEQ-1M1 equals
  p *FUNCT-1K3 SgmFINSEQ-1K15 (domRELSET-1K1\<^bsub>(omegaORDINAL1K4)\<^esub> p \\SUBSET-1K7\<^bsub>(omegaORDINAL1K4)\<^esub> p \<inverse>FUNCT-1K6 A)"
proof-
  (*coherence*)
    show "p *FUNCT-1K3 SgmFINSEQ-1K15 (domRELSET-1K1\<^bsub>(omegaORDINAL1K4)\<^esub> p \\SUBSET-1K7\<^bsub>(omegaORDINAL1K4)\<^esub> p \<inverse>FUNCT-1K6 A) be FinSequenceFINSEQ-1M1"
sorry
qed "sorry"

mtheorem finseq_3_th_59:
" for p be FinSequenceFINSEQ-1M1 holds  for A be setHIDDENM2 holds lenFINSEQ-1K4 (p -FINSEQ-3K1 A) =XBOOLE-0R4 lenFINSEQ-1K4 p -XCMPLX-0K6 cardCARD-1K4 (p \<inverse>FUNCT-1K6 A)"
sorry

mtheorem finseq_3_th_60:
" for p be FinSequenceFINSEQ-1M1 holds  for A be setHIDDENM2 holds lenFINSEQ-1K4 (p -FINSEQ-3K1 A) <=XXREAL-0R1 lenFINSEQ-1K4 p"
sorry

mtheorem finseq_3_th_61:
" for p be FinSequenceFINSEQ-1M1 holds  for A be setHIDDENM2 holds lenFINSEQ-1K4 (p -FINSEQ-3K1 A) =XBOOLE-0R4 lenFINSEQ-1K4 p implies A missesXBOOLE-0R1 rngFUNCT-1K2 p"
sorry

mtheorem finseq_3_th_62:
" for p be FinSequenceFINSEQ-1M1 holds  for A be setHIDDENM2 holds  for n be NatNAT-1M1 holds n =XBOOLE-0R4 lenFINSEQ-1K4 p -XCMPLX-0K6 cardCARD-1K4 (p \<inverse>FUNCT-1K6 A) implies domRELSET-1K1\<^bsub>(omegaORDINAL1K4)\<^esub> (p -FINSEQ-3K1 A) =XBOOLE-0R4 SegFINSEQ-1K2 n"
sorry

mtheorem finseq_3_th_63:
" for p be FinSequenceFINSEQ-1M1 holds  for A be setHIDDENM2 holds domRELSET-1K1\<^bsub>(omegaORDINAL1K4)\<^esub> (p -FINSEQ-3K1 A) c=TARSKIR1 domRELSET-1K1\<^bsub>(omegaORDINAL1K4)\<^esub> p"
sorry

mtheorem finseq_3_th_64:
" for p be FinSequenceFINSEQ-1M1 holds  for A be setHIDDENM2 holds domRELSET-1K1\<^bsub>(omegaORDINAL1K4)\<^esub> (p -FINSEQ-3K1 A) =XBOOLE-0R4 domRELSET-1K1\<^bsub>(omegaORDINAL1K4)\<^esub> p implies A missesXBOOLE-0R1 rngFUNCT-1K2 p"
sorry

mtheorem finseq_3_th_65:
" for p be FinSequenceFINSEQ-1M1 holds  for A be setHIDDENM2 holds rngFUNCT-1K2 (p -FINSEQ-3K1 A) =XBOOLE-0R4 rngFUNCT-1K2 p \\SUBSET-1K6 A"
sorry

mtheorem finseq_3_th_66:
" for p be FinSequenceFINSEQ-1M1 holds  for A be setHIDDENM2 holds rngFUNCT-1K2 (p -FINSEQ-3K1 A) c=TARSKIR1 rngFUNCT-1K2 p"
sorry

mtheorem finseq_3_th_67:
" for p be FinSequenceFINSEQ-1M1 holds  for A be setHIDDENM2 holds rngFUNCT-1K2 (p -FINSEQ-3K1 A) =XBOOLE-0R4 rngFUNCT-1K2 p implies A missesXBOOLE-0R1 rngFUNCT-1K2 p"
sorry

mtheorem finseq_3_th_68:
" for p be FinSequenceFINSEQ-1M1 holds  for A be setHIDDENM2 holds p -FINSEQ-3K1 A =FINSEQ-1R1 {}XBOOLE-0K1 iff rngFUNCT-1K2 p c=TARSKIR1 A"
sorry

mtheorem finseq_3_th_69:
" for p be FinSequenceFINSEQ-1M1 holds  for A be setHIDDENM2 holds p -FINSEQ-3K1 A =FINSEQ-1R1 p iff A missesXBOOLE-0R1 rngFUNCT-1K2 p"
sorry

mtheorem finseq_3_th_70:
" for p be FinSequenceFINSEQ-1M1 holds  for x be objectHIDDENM1 holds p -FINSEQ-3K1 {TARSKIK1 x} =FINSEQ-1R1 p iff  not x inHIDDENR3 rngFUNCT-1K2 p"
sorry

mtheorem finseq_3_th_71:
" for p be FinSequenceFINSEQ-1M1 holds p -FINSEQ-3K1 {}XBOOLE-0K1 =FINSEQ-1R1 p"
sorry

mtheorem finseq_3_th_72:
" for p be FinSequenceFINSEQ-1M1 holds p -FINSEQ-3K1 rngFUNCT-1K2 p =FINSEQ-1R1 {}XBOOLE-0K1"
  using finseq_3_th_68 sorry

mlemma finseq_3_lm_6:
" for x be objectHIDDENM1 holds  for A be setHIDDENM2 holds <*FINSEQ-1K10 x*> -FINSEQ-3K1 A =FINSEQ-1R1 <*FINSEQ-1K10 x*> iff  not x inHIDDENR3 A"
sorry

mlemma finseq_3_lm_7:
" for x be objectHIDDENM1 holds  for A be setHIDDENM2 holds <*FINSEQ-1K10 x*> -FINSEQ-3K1 A =FINSEQ-1R1 {}XBOOLE-0K1 iff x inHIDDENR3 A"
sorry

mlemma finseq_3_lm_8:
" for p be FinSequenceFINSEQ-1M1 holds  for A be setHIDDENM2 holds p ^FINSEQ-1K8 {}XBOOLE-0K1 -FINSEQ-3K1 A =FINSEQ-1R1 (p -FINSEQ-3K1 A)^FINSEQ-1K8 ({}XBOOLE-0K1 -FINSEQ-3K1 A)"
sorry

mlemma finseq_3_lm_9:
" for p be FinSequenceFINSEQ-1M1 holds  for x be objectHIDDENM1 holds  for A be setHIDDENM2 holds p ^FINSEQ-1K8 (<*FINSEQ-1K10 x*>) -FINSEQ-3K1 A =FINSEQ-1R1 (p -FINSEQ-3K1 A)^FINSEQ-1K8 (<*FINSEQ-1K10 x*> -FINSEQ-3K1 A)"
sorry

mlemma finseq_3_lm_10:
" for q be FinSequenceFINSEQ-1M1 holds  for x be objectHIDDENM1 holds ( for p be FinSequenceFINSEQ-1M1 holds  for A be setHIDDENM2 holds p ^FINSEQ-1K8 q -FINSEQ-3K1 A =FINSEQ-1R1 (p -FINSEQ-3K1 A)^FINSEQ-1K8 (q -FINSEQ-3K1 A)) implies ( for p be FinSequenceFINSEQ-1M1 holds  for A be setHIDDENM2 holds p ^FINSEQ-1K8 (q ^FINSEQ-1K8 (<*FINSEQ-1K10 x*>)) -FINSEQ-3K1 A =HIDDENR1 (p -FINSEQ-3K1 A)^FINSEQ-1K8 (q ^FINSEQ-1K8 (<*FINSEQ-1K10 x*>) -FINSEQ-3K1 A))"
sorry

mlemma finseq_3_lm_11:
" for q be FinSequenceFINSEQ-1M1 holds  for p be FinSequenceFINSEQ-1M1 holds  for A be setHIDDENM2 holds p ^FINSEQ-1K8 q -FINSEQ-3K1 A =FINSEQ-1R1 (p -FINSEQ-3K1 A)^FINSEQ-1K8 (q -FINSEQ-3K1 A)"
sorry

mtheorem finseq_3_th_73:
" for p be FinSequenceFINSEQ-1M1 holds  for q be FinSequenceFINSEQ-1M1 holds  for A be setHIDDENM2 holds p ^FINSEQ-1K8 q -FINSEQ-3K1 A =FINSEQ-1R1 (p -FINSEQ-3K1 A)^FINSEQ-1K8 (q -FINSEQ-3K1 A)"
  using finseq_3_lm_11 sorry

mtheorem finseq_3_th_74:
" for A be setHIDDENM2 holds {}XBOOLE-0K1 -FINSEQ-3K1 A =FINSEQ-1R1 {}XBOOLE-0K1"
   sorry

mtheorem finseq_3_th_75:
" for x be objectHIDDENM1 holds  for A be setHIDDENM2 holds <*FINSEQ-1K10 x*> -FINSEQ-3K1 A =FINSEQ-1R1 <*FINSEQ-1K10 x*> iff  not x inHIDDENR3 A"
  using finseq_3_lm_6 sorry

mtheorem finseq_3_th_76:
" for x be objectHIDDENM1 holds  for A be setHIDDENM2 holds <*FINSEQ-1K10 x*> -FINSEQ-3K1 A =FINSEQ-1R1 {}XBOOLE-0K1 iff x inHIDDENR3 A"
  using finseq_3_lm_7 sorry

mtheorem finseq_3_th_77:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for A be setHIDDENM2 holds <*FINSEQ-1K11 x,y *> -FINSEQ-3K1 A =FINSEQ-1R1 {}XBOOLE-0K1 iff x inHIDDENR3 A & y inHIDDENR3 A"
sorry

mtheorem finseq_3_th_78:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for A be setHIDDENM2 holds x inHIDDENR3 A &  not y inHIDDENR3 A implies <*FINSEQ-1K11 x,y *> -FINSEQ-3K1 A =FINSEQ-1R1 <*FINSEQ-1K10 y*>"
sorry

mtheorem finseq_3_th_79:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for A be setHIDDENM2 holds <*FINSEQ-1K11 x,y *> -FINSEQ-3K1 A =FINSEQ-1R1 <*FINSEQ-1K10 y*> & x <>HIDDENR2 y implies x inHIDDENR3 A &  not y inHIDDENR3 A"
sorry

mtheorem finseq_3_th_80:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for A be setHIDDENM2 holds  not x inHIDDENR3 A & y inHIDDENR3 A implies <*FINSEQ-1K11 x,y *> -FINSEQ-3K1 A =FINSEQ-1R1 <*FINSEQ-1K10 x*>"
sorry

mtheorem finseq_3_th_81:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for A be setHIDDENM2 holds <*FINSEQ-1K11 x,y *> -FINSEQ-3K1 A =FINSEQ-1R1 <*FINSEQ-1K10 x*> & x <>HIDDENR2 y implies  not x inHIDDENR3 A & y inHIDDENR3 A"
sorry

mtheorem finseq_3_th_82:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for A be setHIDDENM2 holds <*FINSEQ-1K11 x,y *> -FINSEQ-3K1 A =FINSEQ-1R1 <*FINSEQ-1K11 x,y *> iff  not x inHIDDENR3 A &  not y inHIDDENR3 A"
sorry

mtheorem finseq_3_th_83:
" for p be FinSequenceFINSEQ-1M1 holds  for q be FinSequenceFINSEQ-1M1 holds  for A be setHIDDENM2 holds  for k be NatNAT-1M1 holds lenFINSEQ-1K4 p =XBOOLE-0R4 k +NAT-1K1 \<one>\<^sub>M & q =FUNCT-1R1 p |RELAT-1K8 SegFINSEQ-1K2 k implies (p .FUNCT-1K1 (k +NAT-1K1 \<one>\<^sub>M) inTARSKIR2 A iff p -FINSEQ-3K1 A =FINSEQ-1R1 q -FINSEQ-3K1 A)"
sorry

mtheorem finseq_3_th_84:
" for p be FinSequenceFINSEQ-1M1 holds  for q be FinSequenceFINSEQ-1M1 holds  for A be setHIDDENM2 holds  for k be NatNAT-1M1 holds lenFINSEQ-1K4 p =XBOOLE-0R4 k +NAT-1K1 \<one>\<^sub>M & q =FUNCT-1R1 p |RELAT-1K8 SegFINSEQ-1K2 k implies ( not p .FUNCT-1K1 (k +NAT-1K1 \<one>\<^sub>M) inTARSKIR2 A iff p -FINSEQ-3K1 A =FINSEQ-1R1 (q -FINSEQ-3K1 A)^FINSEQ-1K8 (<*FINSEQ-1K10 p .FUNCT-1K1 (k +NAT-1K1 \<one>\<^sub>M)*>))"
sorry

mlemma finseq_3_lm_12:
" for l be NatNAT-1M1 holds ( for p be FinSequenceFINSEQ-1M1 holds  for A be setHIDDENM2 holds lenFINSEQ-1K4 p =XBOOLE-0R4 l implies ( for n be NatNAT-1M1 holds n inTARSKIR2 domRELSET-1K1\<^bsub>(omegaORDINAL1K4)\<^esub> p implies ( for B be finiteFINSET-1V1\<bar>setHIDDENM2 holds B =XBOOLE-0R4 {k where k be ElementSUBSET-1M1-of NATNUMBERSK1 : (k inTARSKIR2 domRELSET-1K1\<^bsub>(omegaORDINAL1K4)\<^esub> p & k <=XXREAL-0R1 n) & p .FUNCT-1K1 k inTARSKIR2 A } implies p .FUNCT-1K1 n inTARSKIR2 A or (p -FINSEQ-3K1 A).FUNCT-1K1 (n -XCMPLX-0K6 cardCARD-1K4 B) =XBOOLE-0R4 p .FUNCT-1K1 n))) implies ( for p be FinSequenceFINSEQ-1M1 holds  for A be setHIDDENM2 holds lenFINSEQ-1K4 p =XBOOLE-0R4 l +NAT-1K1 \<one>\<^sub>M implies ( for n be NatNAT-1M1 holds n inTARSKIR2 domRELSET-1K1\<^bsub>(omegaORDINAL1K4)\<^esub> p implies ( for C be finiteFINSET-1V1\<bar>setHIDDENM2 holds C =XBOOLE-0R4 {m where m be ElementSUBSET-1M1-of NATNUMBERSK1 : (m inTARSKIR2 domRELSET-1K1\<^bsub>(omegaORDINAL1K4)\<^esub> p & m <=XXREAL-0R1 n) & p .FUNCT-1K1 m inTARSKIR2 A } implies p .FUNCT-1K1 n inTARSKIR2 A or (p -FINSEQ-3K1 A).FUNCT-1K1 (n -XCMPLX-0K6 cardCARD-1K4 C) =XBOOLE-0R4 p .FUNCT-1K1 n)))"
sorry

mlemma finseq_3_lm_13:
" for l be NatNAT-1M1 holds  for p be FinSequenceFINSEQ-1M1 holds  for A be setHIDDENM2 holds lenFINSEQ-1K4 p =XBOOLE-0R4 l implies ( for n be NatNAT-1M1 holds n inTARSKIR2 domRELSET-1K1\<^bsub>(omegaORDINAL1K4)\<^esub> p implies ( for B be finiteFINSET-1V1\<bar>setHIDDENM2 holds B =XBOOLE-0R4 {k where k be ElementSUBSET-1M1-of NATNUMBERSK1 : (k inTARSKIR2 domRELSET-1K1\<^bsub>(omegaORDINAL1K4)\<^esub> p & k <=XXREAL-0R1 n) & p .FUNCT-1K1 k inTARSKIR2 A } implies p .FUNCT-1K1 n inTARSKIR2 A or (p -FINSEQ-3K1 A).FUNCT-1K1 (n -XCMPLX-0K6 cardCARD-1K4 B) =XBOOLE-0R4 p .FUNCT-1K1 n))"
sorry

mtheorem finseq_3_th_85:
" for p be FinSequenceFINSEQ-1M1 holds  for A be setHIDDENM2 holds  for n be NatNAT-1M1 holds n inTARSKIR2 domRELSET-1K1\<^bsub>(omegaORDINAL1K4)\<^esub> p implies ( for B be finiteFINSET-1V1\<bar>setHIDDENM2 holds B =XBOOLE-0R4 {k where k be ElementSUBSET-1M1-of NATNUMBERSK1 : (k inTARSKIR2 domRELSET-1K1\<^bsub>(omegaORDINAL1K4)\<^esub> p & k <=XXREAL-0R1 n) & p .FUNCT-1K1 k inTARSKIR2 A } implies p .FUNCT-1K1 n inTARSKIR2 A or (p -FINSEQ-3K1 A).FUNCT-1K1 (n -XCMPLX-0K6 cardCARD-1K4 B) =XBOOLE-0R4 p .FUNCT-1K1 n)"
sorry

mtheorem finseq_3_th_86:
" for p be FinSequenceFINSEQ-1M1 holds  for A be setHIDDENM2 holds  for D be setHIDDENM2 holds p be FinSequenceFINSEQ-1M3-of D implies p -FINSEQ-3K1 A be FinSequenceFINSEQ-1M3-of D"
sorry

mtheorem finseq_3_th_87:
" for p be FinSequenceFINSEQ-1M1 holds  for A be setHIDDENM2 holds p be one-to-oneFUNCT-1V2 implies p -FINSEQ-3K1 A be one-to-oneFUNCT-1V2"
sorry

mtheorem finseq_3_th_88:
" for p be FinSequenceFINSEQ-1M1 holds  for A be setHIDDENM2 holds p be one-to-oneFUNCT-1V2 implies lenFINSEQ-1K4 (p -FINSEQ-3K1 A) =XBOOLE-0R4 lenFINSEQ-1K4 p -XCMPLX-0K6 cardCARD-1K4 (A /\\XBOOLE-0K3 rngFUNCT-1K2 p)"
sorry

mtheorem finseq_3_th_89:
" for p be FinSequenceFINSEQ-1M1 holds  for A be finiteFINSET-1V1\<bar>setHIDDENM2 holds p be one-to-oneFUNCT-1V2 & A c=TARSKIR1 rngFUNCT-1K2 p implies lenFINSEQ-1K4 (p -FINSEQ-3K1 A) =XBOOLE-0R4 lenFINSEQ-1K4 p -XCMPLX-0K6 cardCARD-1K4 A"
sorry

mtheorem finseq_3_th_90:
" for p be FinSequenceFINSEQ-1M1 holds  for x be objectHIDDENM1 holds p be one-to-oneFUNCT-1V2 & x inHIDDENR3 rngFUNCT-1K2 p implies lenFINSEQ-1K4 (p -FINSEQ-3K1 {TARSKIK1 x}) =XBOOLE-0R4 lenFINSEQ-1K4 p -XCMPLX-0K6 \<one>\<^sub>M"
sorry

mtheorem finseq_3_th_91:
" for p be FinSequenceFINSEQ-1M1 holds  for q be FinSequenceFINSEQ-1M1 holds (rngFUNCT-1K2 p missesXBOOLE-0R1 rngFUNCT-1K2 q & p be one-to-oneFUNCT-1V2) & q be one-to-oneFUNCT-1V2 iff p ^FINSEQ-1K8 q be one-to-oneFUNCT-1V2"
sorry

mtheorem finseq_3_th_92:
" for A be setHIDDENM2 holds  for k be NatNAT-1M1 holds A c=TARSKIR1 SegFINSEQ-1K2 k implies SgmFINSEQ-1K15 A be one-to-oneFUNCT-1V2"
  using finseq_3_lm_1 sorry

mtheorem finseq_3_th_93:
" for x be objectHIDDENM1 holds <*FINSEQ-1K10 x*> be one-to-oneFUNCT-1V2"
sorry

mtheorem finseq_3_th_94:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds x <>HIDDENR2 y iff <*FINSEQ-1K11 x,y *> be one-to-oneFUNCT-1V2"
sorry

mtheorem finseq_3_th_95:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for z be objectHIDDENM1 holds (x <>HIDDENR2 y & y <>HIDDENR2 z) & z <>HIDDENR2 x iff <*FINSEQ-1K12 x,y,z *> be one-to-oneFUNCT-1V2"
sorry

mtheorem finseq_3_th_96:
" for p be FinSequenceFINSEQ-1M1 holds  for x be objectHIDDENM1 holds p be one-to-oneFUNCT-1V2 & rngFUNCT-1K2 p =XBOOLE-0R4 {TARSKIK1 x} implies lenFINSEQ-1K4 p =XBOOLE-0R4 \<one>\<^sub>M"
sorry

mtheorem finseq_3_th_97:
" for p be FinSequenceFINSEQ-1M1 holds  for x be objectHIDDENM1 holds p be one-to-oneFUNCT-1V2 & rngFUNCT-1K2 p =XBOOLE-0R4 {TARSKIK1 x} implies p =FINSEQ-1R1 <*FINSEQ-1K10 x*>"
sorry

mtheorem finseq_3_th_98:
" for p be FinSequenceFINSEQ-1M1 holds  for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds (p be one-to-oneFUNCT-1V2 & rngFUNCT-1K2 p =XBOOLE-0R4 {TARSKIK2 x,y }) & x <>HIDDENR2 y implies lenFINSEQ-1K4 p =XBOOLE-0R4 \<two>\<^sub>M"
sorry

mtheorem finseq_3_th_99:
" for p be FinSequenceFINSEQ-1M1 holds  for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds (p be one-to-oneFUNCT-1V2 & rngFUNCT-1K2 p =XBOOLE-0R4 {TARSKIK2 x,y }) & x <>HIDDENR2 y implies p =FINSEQ-1R1 <*FINSEQ-1K11 x,y *> or p =FINSEQ-1R1 <*FINSEQ-1K11 y,x *>"
sorry

mtheorem finseq_3_th_100:
" for p be FinSequenceFINSEQ-1M1 holds  for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for z be objectHIDDENM1 holds (p be one-to-oneFUNCT-1V2 & rngFUNCT-1K2 p =XBOOLE-0R4 {ENUMSET1K1 x,y,z }) & <*FINSEQ-1K12 x,y,z *> be one-to-oneFUNCT-1V2 implies lenFINSEQ-1K4 p =XBOOLE-0R4 \<three>\<^sub>M"
sorry

mtheorem finseq_3_th_101:
" for p be FinSequenceFINSEQ-1M1 holds  for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for z be objectHIDDENM1 holds (((p be one-to-oneFUNCT-1V2 & rngFUNCT-1K2 p =XBOOLE-0R4 {ENUMSET1K1 x,y,z }) & x <>HIDDENR2 y) & y <>HIDDENR2 z) & x <>HIDDENR2 z implies lenFINSEQ-1K4 p =XBOOLE-0R4 \<three>\<^sub>M"
sorry

(*begin*)
mtheorem finseq_3_th_102:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for df be FinSequenceFINSEQ-1M3-of D holds df be  non emptyXBOOLE-0V1 implies ( ex d be ElementSUBSET-1M1-of D st  ex df1 be FinSequenceFINSEQ-1M3-of D st d =XBOOLE-0R4 df .FUNCT-1K1 \<one>\<^sub>M & df =RELSET-1R2\<^bsub>(omegaORDINAL1K4,D)\<^esub> (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>)^FINSEQ-1K9\<^bsub>(D)\<^esub> df1)"
sorry

mtheorem finseq_3_th_103:
" for i be NatNAT-1M1 holds  for df be FinSequenceFINSEQ-1M1 holds  for d be objectHIDDENM1 holds i inTARSKIR2 domRELSET-1K1\<^bsub>(omegaORDINAL1K4)\<^esub> df implies ((<*FINSEQ-1K10 d*>)^FINSEQ-1K8 df).FUNCT-1K1 (i +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 df .FUNCT-1K1 i"
sorry

mdef finseq_3_def_2 ("DelFINSEQ-3K2'( _ , _ ')" [0,0]164 ) where
  mlet "i be naturalORDINAL1V7\<bar>NumberORDINAL1M1", "p be FinSequenceFINSEQ-1M1"
"func DelFINSEQ-3K2(p,i) \<rightarrow> FinSequenceFINSEQ-1M1 equals
  p *FUNCT-1K3 SgmFINSEQ-1K15 (domRELSET-1K1\<^bsub>(omegaORDINAL1K4)\<^esub> p \\SUBSET-1K7\<^bsub>(omegaORDINAL1K4)\<^esub> {TARSKIK1 i})"
proof-
  (*coherence*)
    show "p *FUNCT-1K3 SgmFINSEQ-1K15 (domRELSET-1K1\<^bsub>(omegaORDINAL1K4)\<^esub> p \\SUBSET-1K7\<^bsub>(omegaORDINAL1K4)\<^esub> {TARSKIK1 i}) be FinSequenceFINSEQ-1M1"
sorry
qed "sorry"

mtheorem finseq_3_th_104:
" for i be NatNAT-1M1 holds  for p be FinSequenceFINSEQ-1M1 holds (i inTARSKIR2 domRELSET-1K1\<^bsub>(omegaORDINAL1K4)\<^esub> p implies ( ex m be NatNAT-1M1 st lenFINSEQ-1K4 p =XBOOLE-0R4 m +NAT-1K1 \<one>\<^sub>M & lenFINSEQ-1K4 (DelFINSEQ-3K2(p,i)) =XBOOLE-0R4 m)) & ( not i inTARSKIR2 domRELSET-1K1\<^bsub>(omegaORDINAL1K4)\<^esub> p implies DelFINSEQ-3K2(p,i) =FINSEQ-1R1 p)"
sorry

mtheorem finseq_3_th_105:
" for i be NatNAT-1M1 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for p be FinSequenceFINSEQ-1M3-of D holds DelFINSEQ-3K2(p,i) be FinSequenceFINSEQ-1M3-of D"
sorry

mtheorem finseq_3_th_106:
" for i be NatNAT-1M1 holds  for p be FinSequenceFINSEQ-1M1 holds rngFUNCT-1K2 (DelFINSEQ-3K2(p,i)) c=TARSKIR1 rngFUNCT-1K2 p"
  using funct_1_th_14 sorry

mtheorem finseq_3_th_107:
" for i be NatNAT-1M1 holds  for m be NatNAT-1M1 holds  for n be NatNAT-1M1 holds n =XBOOLE-0R4 m +NAT-1K1 \<one>\<^sub>M & i inTARSKIR2 SegFINSEQ-1K2 n implies lenFINSEQ-1K4 (SgmFINSEQ-1K15 (SegFINSEQ-1K2 n \\SUBSET-1K7\<^bsub>(omegaORDINAL1K4)\<^esub> {TARSKIK1 i})) =XBOOLE-0R4 m"
sorry

reserve J for "NatNAT-1M1"
mtheorem finseq_3_th_108:
" for i be NatNAT-1M1 holds  for k be NatNAT-1M1 holds  for m be NatNAT-1M1 holds  for n be NatNAT-1M1 holds (n =XBOOLE-0R4 m +NAT-1K1 \<one>\<^sub>M & k inTARSKIR2 SegFINSEQ-1K2 n) & i inTARSKIR2 SegFINSEQ-1K2 m implies (\<one>\<^sub>M <=XXREAL-0R1 i & i <XXREAL-0R3 k implies SgmFINSEQ-1K15 (SegFINSEQ-1K2 n \\SUBSET-1K7\<^bsub>(omegaORDINAL1K4)\<^esub> {TARSKIK1 k}) .FUNCT-1K1 i =XBOOLE-0R4 i) & (k <=XXREAL-0R1 i & i <=XXREAL-0R1 m implies SgmFINSEQ-1K15 (SegFINSEQ-1K2 n \\SUBSET-1K7\<^bsub>(omegaORDINAL1K4)\<^esub> {TARSKIK1 k}) .FUNCT-1K1 i =XBOOLE-0R4 i +NAT-1K1 \<one>\<^sub>M)"
sorry

mtheorem finseq_3_th_109:
" for m be NatNAT-1M1 holds  for n be NatNAT-1M1 holds  for f be FinSequenceFINSEQ-1M1 holds lenFINSEQ-1K4 f =XBOOLE-0R4 m +NAT-1K1 \<one>\<^sub>M & n inTARSKIR2 domRELSET-1K1\<^bsub>(omegaORDINAL1K4)\<^esub> f implies lenFINSEQ-1K4 (DelFINSEQ-3K2(f,n)) =XBOOLE-0R4 m"
sorry

mtheorem finseq_3_th_110:
" for k be NatNAT-1M1 holds  for n be NatNAT-1M1 holds  for f be FinSequenceFINSEQ-1M1 holds k <XXREAL-0R3 n implies (DelFINSEQ-3K2(f,n)).FUNCT-1K1 k =XBOOLE-0R4 f .FUNCT-1K1 k"
sorry

mtheorem finseq_3_th_111:
" for k be NatNAT-1M1 holds  for m be NatNAT-1M1 holds  for n be NatNAT-1M1 holds  for f be FinSequenceFINSEQ-1M1 holds ((lenFINSEQ-1K4 f =XBOOLE-0R4 m +NAT-1K1 \<one>\<^sub>M & n inTARSKIR2 domRELSET-1K1\<^bsub>(omegaORDINAL1K4)\<^esub> f) & n <=XXREAL-0R1 k) & k <=XXREAL-0R1 m implies (DelFINSEQ-3K2(f,n)).FUNCT-1K1 k =XBOOLE-0R4 f .FUNCT-1K1 (k +NAT-1K1 \<one>\<^sub>M)"
sorry

mtheorem finseq_3_th_112:
" for k be NatNAT-1M1 holds  for n be NatNAT-1M1 holds  for f be FinSequenceFINSEQ-1M1 holds k <=XXREAL-0R1 n implies (f |FINSEQ-1K17 n).FUNCT-1K1 k =XBOOLE-0R4 f .FUNCT-1K1 k"
sorry

mtheorem finseq_3_th_113:
" for p be FinSequenceFINSEQ-1M1 holds  for q be FinSequenceFINSEQ-1M1 holds p c=RELAT-1R2 q implies q |FINSEQ-1K17 lenFINSEQ-1K4 p =FINSEQ-1R1 p"
sorry

mtheorem finseq_3_th_114:
" for A be setHIDDENM2 holds  for F be FinSequenceFINSEQ-1M1 holds SgmFINSEQ-1K15 (F \<inverse>FUNCT-1K6 A) ^FINSEQ-1K9\<^bsub>(omegaORDINAL1K4)\<^esub> SgmFINSEQ-1K15 (F \<inverse>FUNCT-1K6 (rngFUNCT-1K2 F \\SUBSET-1K6 A)) be PermutationFUNCT-2M2-of domRELSET-1K1\<^bsub>(omegaORDINAL1K4)\<^esub> F"
sorry

mtheorem finseq_3_th_115:
" for F be FinSequenceFINSEQ-1M1 holds  for A be SubsetSUBSET-1M2-of rngFUNCT-1K2 F holds  ex p be PermutationFUNCT-2M2-of domRELSET-1K1\<^bsub>(omegaORDINAL1K4)\<^esub> F st (F -FINSEQ-3K1 A `SUBSET-1K3\<^bsub>(rngFUNCT-1K2 F)\<^esub>)^FINSEQ-1K8 (F -FINSEQ-3K1 A) =FUNCT-1R1 F *FUNCT-1K3 p"
sorry

mtheorem finseq_3_th_116:
" for f be FinSubsequenceFINSEQ-1M4 holds f be FinSequenceFINSEQ-1M1 implies SeqFINSEQ-1K16 f =FUNCT-1R1 f"
sorry

mtheorem finseq_3_th_117:
" for t be FinSequenceFINSEQ-1M3-of INTNUMBERSK5 holds t be FinSequenceFINSEQ-1M3-of REALNUMBERSK2"
sorry

mtheorem finseq_3_th_118:
" for p be FinSequenceFINSEQ-1M1 holds  for q be FinSequenceFINSEQ-1M1 holds lenFINSEQ-1K4 p <XXREAL-0R3 lenFINSEQ-1K4 q iff domRELSET-1K1\<^bsub>(omegaORDINAL1K4)\<^esub> p c<XBOOLE-0R2 domRELSET-1K1\<^bsub>(omegaORDINAL1K4)\<^esub> q"
sorry

mtheorem finseq_3_th_119:
" for A be setHIDDENM2 holds  for i be NatNAT-1M1 holds i <>HIDDENR2 0NUMBERSK6 & A =XBOOLE-0R4 {}XBOOLE-0K1 iff i -tuples-onFINSEQ-2K4 A =XBOOLE-0R4 {}XBOOLE-0K1"
sorry

mtheorem finseq_3_cl_1:
  mlet "i be NatNAT-1M1", "D be setHIDDENM2"
"cluster i -tuples-onFINSEQ-2K4 D as-term-is with-common-domainCARD-3V2"
proof
(*coherence*)
  show "i -tuples-onFINSEQ-2K4 D be with-common-domainCARD-3V2"
sorry
qed "sorry"

mtheorem finseq_3_cl_2:
  mlet "i be NatNAT-1M1", "D be setHIDDENM2"
"cluster i -tuples-onFINSEQ-2K4 D as-term-is product-likeCARD-3V3"
proof
(*coherence*)
  show "i -tuples-onFINSEQ-2K4 D be product-likeCARD-3V3"
sorry
qed "sorry"

(*begin*)
reserve n for "NatNAT-1M1"
mtheorem finseq_3_th_120:
" for D1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D2 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for p be FinSequenceFINSEQ-1M3-of D1 holds  for f be FunctionFUNCT-2M1-of(D1,D2) holds (domRELSET-1K1\<^bsub>(omegaORDINAL1K4)\<^esub> (f *FINSEQOPK4\<^bsub>(D1,D2)\<^esub> p) =XBOOLE-0R4 domRELSET-1K1\<^bsub>(omegaORDINAL1K4)\<^esub> p & lenFINSEQ-1K4 (f *FINSEQOPK4\<^bsub>(D1,D2)\<^esub> p) =XBOOLE-0R4 lenFINSEQ-1K4 p) & ( for n be NatNAT-1M1 holds n inTARSKIR2 domRELSET-1K1\<^bsub>(omegaORDINAL1K4)\<^esub> (f *FINSEQOPK4\<^bsub>(D1,D2)\<^esub> p) implies (f *FINSEQOPK4\<^bsub>(D1,D2)\<^esub> p).FUNCT-1K1 n =XBOOLE-0R4 f .FUNCT-1K1 (p .FUNCT-1K1 n))"
sorry

mdef finseq_3_def_3 ("ExtendRelFINSEQ-3K3\<^bsub>'( _ ')\<^esub>  _ " [0,164]164 ) where
  mlet "D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "R be RelationRELSET-1M2-of D"
"func ExtendRelFINSEQ-3K3\<^bsub>(D)\<^esub> R \<rightarrow> RelationRELSET-1M2-of D * FINSEQ-2K3 means
  \<lambda>it.  for x be FinSequenceFINSEQ-1M3-of D holds  for y be FinSequenceFINSEQ-1M3-of D holds [TARSKIK4 x,y ] inHIDDENR3 it iff lenFINSEQ-1K4 x =XBOOLE-0R4 lenFINSEQ-1K4 y & ( for n be NatNAT-1M1 holds n inTARSKIR2 domRELSET-1K1\<^bsub>(omegaORDINAL1K4)\<^esub> x implies [TARSKIK4 x .FUNCT-1K1 n,y .FUNCT-1K1 n ] inHIDDENR3 R)"
proof-
  (*existence*)
    show " ex it be RelationRELSET-1M2-of D * FINSEQ-2K3 st  for x be FinSequenceFINSEQ-1M3-of D holds  for y be FinSequenceFINSEQ-1M3-of D holds [TARSKIK4 x,y ] inHIDDENR3 it iff lenFINSEQ-1K4 x =XBOOLE-0R4 lenFINSEQ-1K4 y & ( for n be NatNAT-1M1 holds n inTARSKIR2 domRELSET-1K1\<^bsub>(omegaORDINAL1K4)\<^esub> x implies [TARSKIK4 x .FUNCT-1K1 n,y .FUNCT-1K1 n ] inHIDDENR3 R)"
sorry
  (*uniqueness*)
    show " for it1 be RelationRELSET-1M2-of D * FINSEQ-2K3 holds  for it2 be RelationRELSET-1M2-of D * FINSEQ-2K3 holds ( for x be FinSequenceFINSEQ-1M3-of D holds  for y be FinSequenceFINSEQ-1M3-of D holds [TARSKIK4 x,y ] inHIDDENR3 it1 iff lenFINSEQ-1K4 x =XBOOLE-0R4 lenFINSEQ-1K4 y & ( for n be NatNAT-1M1 holds n inTARSKIR2 domRELSET-1K1\<^bsub>(omegaORDINAL1K4)\<^esub> x implies [TARSKIK4 x .FUNCT-1K1 n,y .FUNCT-1K1 n ] inHIDDENR3 R)) & ( for x be FinSequenceFINSEQ-1M3-of D holds  for y be FinSequenceFINSEQ-1M3-of D holds [TARSKIK4 x,y ] inHIDDENR3 it2 iff lenFINSEQ-1K4 x =XBOOLE-0R4 lenFINSEQ-1K4 y & ( for n be NatNAT-1M1 holds n inTARSKIR2 domRELSET-1K1\<^bsub>(omegaORDINAL1K4)\<^esub> x implies [TARSKIK4 x .FUNCT-1K1 n,y .FUNCT-1K1 n ] inHIDDENR3 R)) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mtheorem finseq_3_th_121:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds ExtendRelFINSEQ-3K3\<^bsub>(D)\<^esub> idPARTFUN1K6 D =RELSET-1R2\<^bsub>(D * FINSEQ-2K3,D * FINSEQ-2K3)\<^esub> idPARTFUN1K6 (D * FINSEQ-2K3)"
sorry

mdef finseq_3_def_4 (" _ is-representatives-FSFINSEQ-3R1\<^bsub>'( _ , _ ')\<^esub>  _ " [50,0,0,50]50 ) where
  mlet "D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "R be Equivalence-RelationEQREL-1M2-of D", "y be FinSequenceFINSEQ-1M3-of ClassEQREL-1K9\<^bsub>(D)\<^esub> R", "x be FinSequenceFINSEQ-1M3-of D"
"pred x is-representatives-FSFINSEQ-3R1\<^bsub>(D,R)\<^esub> y means
  lenFINSEQ-1K4 x =XBOOLE-0R4 lenFINSEQ-1K4 y & ( for n be NatNAT-1M1 holds n inTARSKIR2 domRELSET-1K1\<^bsub>(omegaORDINAL1K4)\<^esub> x implies ClassEQREL-1K7\<^bsub>(D,D)\<^esub>(R,x .FUNCT-1K1 n) =XBOOLE-0R4 y .FUNCT-1K1 n)"..

mtheorem finseq_3_th_122:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for R be Equivalence-RelationEQREL-1M2-of D holds  for y be FinSequenceFINSEQ-1M3-of ClassEQREL-1K9\<^bsub>(D)\<^esub> R holds  ex x be FinSequenceFINSEQ-1M3-of D st x is-representatives-FSFINSEQ-3R1\<^bsub>(D,R)\<^esub> y"
sorry

reserve x, y, y1, y2, z, a, b for "objectHIDDENM1"
reserve X, Y, Z, V1, V2 for "setHIDDENM2"
reserve f, g, h, h9, f1, f2 for "FunctionFUNCT-1M1"
reserve i for "NatNAT-1M1"
reserve D, D1, D2, D3 for " non emptyXBOOLE-0V1\<bar>setHIDDENM2"
reserve d1 for "ElementSUBSET-1M1-of D1"
reserve d2 for "ElementSUBSET-1M1-of D2"
reserve d3 for "ElementSUBSET-1M1-of D3"
mtheorem finseq_3_th_123:
" for x be objectHIDDENM1 holds  for X be setHIDDENM2 holds x inHIDDENR3 productCARD-3K4 (<*FINSEQ-1K10 X*>) iff ( ex y be objectHIDDENM1 st y inHIDDENR3 X & x =HIDDENR1 <*FINSEQ-1K10 y*>)"
sorry

mtheorem finseq_3_th_124:
" for z be objectHIDDENM1 holds  for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds z inHIDDENR3 productCARD-3K4 (<*FINSEQ-1K11 X,Y *>) iff ( ex x be objectHIDDENM1 st  ex y be objectHIDDENM1 st (x inHIDDENR3 X & y inHIDDENR3 Y) & z =HIDDENR1 <*FINSEQ-1K11 x,y *>)"
sorry

mtheorem finseq_3_th_125:
" for a be objectHIDDENM1 holds  for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds a inHIDDENR3 productCARD-3K4 (<*FINSEQ-1K12 X,Y,Z *>) iff ( ex x be objectHIDDENM1 st  ex y be objectHIDDENM1 st  ex z be objectHIDDENM1 st ((x inHIDDENR3 X & y inHIDDENR3 Y) & z inHIDDENR3 Z) & a =HIDDENR1 <*FINSEQ-1K12 x,y,z *>)"
sorry

mtheorem finseq_3_th_126:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds productCARD-3K4 (<*FINSEQ-1K10 D*>) =XBOOLE-0R4 \<one>\<^sub>M -tuples-onFINSEQ-2K4 D"
sorry

mtheorem finseq_3_th_127:
" for D1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D2 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds productCARD-3K4 (<*FINSEQ-1K11 D1,D2 *>) =XBOOLE-0R4 {<*FINSEQ-1K11 d1,d2 *> where d1 be ElementSUBSET-1M1-of D1, d2 be ElementSUBSET-1M1-of D2 :  True  }"
sorry

mtheorem finseq_3_th_128:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds productCARD-3K4 (<*FINSEQ-1K11 D,D *>) =XBOOLE-0R4 \<two>\<^sub>M -tuples-onFINSEQ-2K4 D"
sorry

mtheorem finseq_3_th_129:
" for D1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D2 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D3 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds productCARD-3K4 (<*FINSEQ-1K12 D1,D2,D3 *>) =XBOOLE-0R4 {<*FINSEQ-1K12 d1,d2,d3 *> where d1 be ElementSUBSET-1M1-of D1, d2 be ElementSUBSET-1M1-of D2, d3 be ElementSUBSET-1M1-of D3 :  True  }"
sorry

mtheorem finseq_3_th_130:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds productCARD-3K4 (<*FINSEQ-1K12 D,D,D *>) =XBOOLE-0R4 \<three>\<^sub>M -tuples-onFINSEQ-2K4 D"
sorry

mtheorem finseq_3_th_131:
" for i be NatNAT-1M1 holds  for D be setHIDDENM2 holds productCARD-3K4 (i |->FINSEQ-2K2 D) =XBOOLE-0R4 i -tuples-onFINSEQ-2K4 D"
sorry

mtheorem finseq_3_cl_3:
  mlet "f be FunctionFUNCT-1M1"
"cluster <*FINSEQ-1K10 f*> as-term-is Function-yieldingFUNCOP-1V1"
proof
(*coherence*)
  show "<*FINSEQ-1K10 f*> be Function-yieldingFUNCOP-1V1"
sorry
qed "sorry"

mtheorem finseq_3_cl_4:
  mlet "f be FunctionFUNCT-1M1", "g be FunctionFUNCT-1M1"
"cluster <*FINSEQ-1K11 f,g *> as-term-is Function-yieldingFUNCOP-1V1"
proof
(*coherence*)
  show "<*FINSEQ-1K11 f,g *> be Function-yieldingFUNCOP-1V1"
sorry
qed "sorry"

mtheorem finseq_3_cl_5:
  mlet "f be FunctionFUNCT-1M1", "g be FunctionFUNCT-1M1", "h be FunctionFUNCT-1M1"
"cluster <*FINSEQ-1K12 f,g,h *> as-term-is Function-yieldingFUNCOP-1V1"
proof
(*coherence*)
  show "<*FINSEQ-1K12 f,g,h *> be Function-yieldingFUNCOP-1V1"
sorry
qed "sorry"

mtheorem finseq_3_th_132:
" for f be FunctionFUNCT-1M1 holds domsFUNCT-6K1 (<*FINSEQ-1K10 f*>) =FUNCT-1R1 <*FINSEQ-1K10 domRELAT-1K1 f*> & rngsFUNCT-6K2 (<*FINSEQ-1K10 f*>) =FUNCT-1R1 <*FINSEQ-1K10 rngFUNCT-1K2 f*>"
sorry

mtheorem finseq_3_th_133:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds domsFUNCT-6K1 (<*FINSEQ-1K11 f,g *>) =FUNCT-1R1 <*FINSEQ-1K11 domRELAT-1K1 f,domRELAT-1K1 g *> & rngsFUNCT-6K2 (<*FINSEQ-1K11 f,g *>) =FUNCT-1R1 <*FINSEQ-1K11 rngFUNCT-1K2 f,rngFUNCT-1K2 g *>"
sorry

mtheorem finseq_3_th_134:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds  for h be FunctionFUNCT-1M1 holds domsFUNCT-6K1 (<*FINSEQ-1K12 f,g,h *>) =FUNCT-1R1 <*FINSEQ-1K12 domRELAT-1K1 f,domRELAT-1K1 g,domRELAT-1K1 h *> & rngsFUNCT-6K2 (<*FINSEQ-1K12 f,g,h *>) =FUNCT-1R1 <*FINSEQ-1K12 rngFUNCT-1K2 f,rngFUNCT-1K2 g,rngFUNCT-1K2 h *>"
sorry

mtheorem finseq_3_th_135:
" for X be setHIDDENM2 holds UnionCARD-3K3 (<*FINSEQ-1K10 X*>) =XBOOLE-0R4 X & meetFUNCT-6K3 (<*FINSEQ-1K10 X*>) =XBOOLE-0R4 X"
sorry

mtheorem finseq_3_th_136:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds UnionCARD-3K3 (<*FINSEQ-1K11 X,Y *>) =XBOOLE-0R4 X \\/XBOOLE-0K2 Y & meetFUNCT-6K3 (<*FINSEQ-1K11 X,Y *>) =XBOOLE-0R4 X /\\XBOOLE-0K3 Y"
sorry

mtheorem finseq_3_th_137:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds UnionCARD-3K3 (<*FINSEQ-1K12 X,Y,Z *>) =XBOOLE-0R4 (X \\/XBOOLE-0K2 Y)\\/XBOOLE-0K2 Z & meetFUNCT-6K3 (<*FINSEQ-1K12 X,Y,Z *>) =XBOOLE-0R4 (X /\\XBOOLE-0K3 Y)/\\XBOOLE-0K3 Z"
sorry

mtheorem finseq_3_th_138:
" for x be objectHIDDENM1 holds  for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds  for h be FunctionFUNCT-1M1 holds x inHIDDENR3 domRELAT-1K1 f implies ((<*FINSEQ-1K10 f*>)..FUNCT-6K4(\<one>\<^sub>M,x) =XBOOLE-0R4 f .FUNCT-1K1 x & (<*FINSEQ-1K11 f,g *>)..FUNCT-6K4(\<one>\<^sub>M,x) =XBOOLE-0R4 f .FUNCT-1K1 x) & (<*FINSEQ-1K12 f,g,h *>)..FUNCT-6K4(\<one>\<^sub>M,x) =XBOOLE-0R4 f .FUNCT-1K1 x"
sorry

mtheorem finseq_3_th_139:
" for x be objectHIDDENM1 holds  for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds  for h be FunctionFUNCT-1M1 holds x inHIDDENR3 domRELAT-1K1 g implies (<*FINSEQ-1K11 f,g *>)..FUNCT-6K4(\<two>\<^sub>M,x) =XBOOLE-0R4 g .FUNCT-1K1 x & (<*FINSEQ-1K12 f,g,h *>)..FUNCT-6K4(\<two>\<^sub>M,x) =XBOOLE-0R4 g .FUNCT-1K1 x"
sorry

mtheorem finseq_3_th_140:
" for x be objectHIDDENM1 holds  for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds  for h be FunctionFUNCT-1M1 holds x inHIDDENR3 domRELAT-1K1 h implies (<*FINSEQ-1K12 f,g,h *>)..FUNCT-6K4(\<three>\<^sub>M,x) =XBOOLE-0R4 h .FUNCT-1K1 x"
sorry

mtheorem finseq_3_th_141:
" for h be FunctionFUNCT-1M1 holds domRELAT-1K1 (<:FUNCT-6K5 <*FINSEQ-1K10 h*> :>) =XBOOLE-0R4 domRELAT-1K1 h & ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 h implies (<:FUNCT-6K5 <*FINSEQ-1K10 h*> :>).FUNCT-1K1 x =XBOOLE-0R4 <*FINSEQ-1K10 h .FUNCT-1K1 x*>)"
sorry

mtheorem finseq_3_th_142:
" for f1 be FunctionFUNCT-1M1 holds  for f2 be FunctionFUNCT-1M1 holds domRELAT-1K1 (<:FUNCT-6K5 <*FINSEQ-1K11 f1,f2 *> :>) =XBOOLE-0R4 domRELAT-1K1 f1 /\\XBOOLE-0K3 domRELAT-1K1 f2 & ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 f1 /\\XBOOLE-0K3 domRELAT-1K1 f2 implies (<:FUNCT-6K5 <*FINSEQ-1K11 f1,f2 *> :>).FUNCT-1K1 x =XBOOLE-0R4 <*FINSEQ-1K11 f1 .FUNCT-1K1 x,f2 .FUNCT-1K1 x *>)"
sorry

mtheorem finseq_3_th_143:
" for h be FunctionFUNCT-1M1 holds (domRELAT-1K1 (FregeFUNCT-6K6 (<*FINSEQ-1K10 h*>)) =XBOOLE-0R4 productCARD-3K4 (<*FINSEQ-1K10 domRELAT-1K1 h*>) & rngFUNCT-1K2 (FregeFUNCT-6K6 (<*FINSEQ-1K10 h*>)) =XBOOLE-0R4 productCARD-3K4 (<*FINSEQ-1K10 rngFUNCT-1K2 h*>)) & ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 h implies (FregeFUNCT-6K6 (<*FINSEQ-1K10 h*>)).FUNCT-1K1 (<*FINSEQ-1K10 x*>) =XBOOLE-0R4 <*FINSEQ-1K10 h .FUNCT-1K1 x*>)"
sorry

mtheorem finseq_3_th_144:
" for f1 be FunctionFUNCT-1M1 holds  for f2 be FunctionFUNCT-1M1 holds (domRELAT-1K1 (FregeFUNCT-6K6 (<*FINSEQ-1K11 f1,f2 *>)) =XBOOLE-0R4 productCARD-3K4 (<*FINSEQ-1K11 domRELAT-1K1 f1,domRELAT-1K1 f2 *>) & rngFUNCT-1K2 (FregeFUNCT-6K6 (<*FINSEQ-1K11 f1,f2 *>)) =XBOOLE-0R4 productCARD-3K4 (<*FINSEQ-1K11 rngFUNCT-1K2 f1,rngFUNCT-1K2 f2 *>)) & ( for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 f1 & y inHIDDENR3 domRELAT-1K1 f2 implies (FregeFUNCT-6K6 (<*FINSEQ-1K11 f1,f2 *>)).FUNCT-1K1 (<*FINSEQ-1K11 x,y *>) =XBOOLE-0R4 <*FINSEQ-1K11 f1 .FUNCT-1K1 x,f2 .FUNCT-1K1 y *>)"
sorry

mtheorem finseq_3_th_145:
" for x be objectHIDDENM1 holds  for f1 be FunctionFUNCT-1M1 holds  for f2 be FunctionFUNCT-1M1 holds x inHIDDENR3 domRELAT-1K1 f1 & x inHIDDENR3 domRELAT-1K1 f2 implies ( for y1 be objectHIDDENM1 holds  for y2 be objectHIDDENM1 holds (<:FUNCT-3K14 f1,f2 :>).FUNCT-1K1 x =HIDDENR1 [TARSKIK4 y1,y2 ] iff (<:FUNCT-6K5 <*FINSEQ-1K11 f1,f2 *> :>).FUNCT-1K1 x =XBOOLE-0R4 <*FINSEQ-1K11 y1,y2 *>)"
sorry

mtheorem finseq_3_th_146:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for f1 be FunctionFUNCT-1M1 holds  for f2 be FunctionFUNCT-1M1 holds x inHIDDENR3 domRELAT-1K1 f1 & y inHIDDENR3 domRELAT-1K1 f2 implies ( for y1 be objectHIDDENM1 holds  for y2 be objectHIDDENM1 holds ([:FUNCT-3K16 f1,f2 :]).BINOP-1K1(x,y) =HIDDENR1 [TARSKIK4 y1,y2 ] iff (FregeFUNCT-6K6 (<*FINSEQ-1K11 f1,f2 *>)).FUNCT-1K1 (<*FINSEQ-1K11 x,y *>) =XBOOLE-0R4 <*FINSEQ-1K11 y1,y2 *>)"
sorry

mtheorem finseq_3_th_147:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds FuncsFUNCT-6K7(<*FINSEQ-1K10 X*>,Y) =FUNCT-1R1 <*FINSEQ-1K10 FuncsFUNCT-2K1(X,Y)*>"
sorry

mtheorem finseq_3_th_148:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds FuncsFUNCT-6K7(<*FINSEQ-1K11 X,Y *>,Z) =FUNCT-1R1 <*FINSEQ-1K11 FuncsFUNCT-2K1(X,Z),FuncsFUNCT-2K1(Y,Z) *>"
sorry

mtheorem finseq_3_th_149:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds FuncsFUNCT-6K8(X,<*FINSEQ-1K10 Y*>) =FUNCT-1R1 <*FINSEQ-1K10 FuncsFUNCT-2K1(X,Y)*>"
sorry

mtheorem finseq_3_th_150:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds FuncsFUNCT-6K8(X,<*FINSEQ-1K11 Y,Z *>) =FUNCT-1R1 <*FINSEQ-1K11 FuncsFUNCT-2K1(X,Y),FuncsFUNCT-2K1(X,Z) *>"
sorry

mtheorem finseq_3_th_151:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for f be FinSequenceFINSEQ-1M1 holds rngFUNCT-1K2 f =XBOOLE-0R4 {TARSKIK2 x,y } & lenFINSEQ-1K4 f =XBOOLE-0R4 \<two>\<^sub>M implies f .FUNCT-1K1 \<one>\<^sub>M =HIDDENR1 x & f .FUNCT-1K1 \<two>\<^sub>M =HIDDENR1 y or f .FUNCT-1K1 \<one>\<^sub>M =HIDDENR1 y & f .FUNCT-1K1 \<two>\<^sub>M =HIDDENR1 x"
sorry

mtheorem finseq_3_th_152:
" for X be setHIDDENM2 holds  for k be ElementSUBSET-1M1-of NATNUMBERSK1 holds X c=TARSKIR1 SegFINSEQ-1K2 k implies ( for m be ElementSUBSET-1M1-of NATNUMBERSK1 holds  for n be ElementSUBSET-1M1-of NATNUMBERSK1 holds m inTARSKIR2 domRELSET-1K1\<^bsub>(omegaORDINAL1K4)\<^esub> (SgmFINSEQ-1K15 X) & n =XBOOLE-0R4 SgmFINSEQ-1K15 X .FUNCT-1K1 m implies m <=XXREAL-0R1 n)"
sorry

mtheorem finseq_3_cl_6:
  mlet "i be NatNAT-1M1", "D be finiteFINSET-1V1\<bar>setHIDDENM2"
"cluster i -tuples-onFINSEQ-2K4 D as-term-is finiteFINSET-1V1"
proof
(*coherence*)
  show "i -tuples-onFINSEQ-2K4 D be finiteFINSET-1V1"
sorry
qed "sorry"

mtheorem finseq_3_th_153:
" for m be NatNAT-1M1 holds  for p be m -elementCARD-1V3\<bar>FinSequenceFINSEQ-1M1 holds lenFINSEQ-1K4 p =XBOOLE-0R4 m"
  using card_1_def_7 sorry

mtheorem finseq_3_th_154:
" for n be NatNAT-1M1 holds  for p be n -elementCARD-1V3\<bar>FinSequenceFINSEQ-1M1 holds  for q be FinSequenceFINSEQ-1M1 holds  for VarFor4 be setHIDDENM2 holds \<one>\<^sub>M <=XXREAL-0R1 VarFor4 & VarFor4 <=XXREAL-0R1 n implies  not (p ^FINSEQ-1K8 q).FUNCT-1K1 VarFor4 =XBOOLE-0R4 p .FUNCT-1K1 VarFor4"
sorry

reserve n for "NatNAT-1M1"
mtheorem finseq_3_th_155:
" for m be NatNAT-1M1 holds  for n be NatNAT-1M1 holds  for p be n -elementCARD-1V3\<bar>FinSequenceFINSEQ-1M1 holds  for q be m -elementCARD-1V3\<bar>FinSequenceFINSEQ-1M1 holds  for VarFor5 be setHIDDENM2 holds \<one>\<^sub>M <=XXREAL-0R1 VarFor5 & VarFor5 <=XXREAL-0R1 m implies  not (p ^FINSEQ-1K8 q).FUNCT-1K1 (n +XCMPLX-0K2 VarFor5) =XBOOLE-0R4 q .FUNCT-1K1 VarFor5"
sorry

mtheorem finseq_3_th_156:
" for p be FinSequenceFINSEQ-1M1 holds  for k be NatNAT-1M1 holds k inTARSKIR2 domRELSET-1K1\<^bsub>(omegaORDINAL1K4)\<^esub> p implies ( for i be NatNAT-1M1 holds \<one>\<^sub>M <=XXREAL-0R1 i & i <=XXREAL-0R1 k implies i inTARSKIR2 domRELSET-1K1\<^bsub>(omegaORDINAL1K4)\<^esub> p)"
sorry

mtheorem finseq_3_th_157:
" for x be objectHIDDENM1 holds  for i be NatNAT-1M1 holds  for q be FinSubsequenceFINSEQ-1M4 holds q =FUNCT-1R1 {TARSKIK1 [TARSKIK4 i,x ] } implies SeqFINSEQ-1K16 q =FINSEQ-1R1 <*FINSEQ-1K10 x*>"
sorry

mtheorem finseq_3_th_158:
" for p be FinSubsequenceFINSEQ-1M4 holds cardCARD-1K4 p =XBOOLE-0R4 lenFINSEQ-1K4 (SeqFINSEQ-1K16 p)"
sorry

mtheorem finseq_3_th_159:
" for x be objectHIDDENM1 holds  for q be FinSubsequenceFINSEQ-1M4 holds SeqFINSEQ-1K16 q =FINSEQ-1R1 <*FINSEQ-1K10 x*> implies ( ex i be ElementSUBSET-1M1-of NATNUMBERSK1 st q =FUNCT-1R1 {TARSKIK1 [TARSKIK4 i,x ] })"
sorry

end
