theory xxreal_1
  imports membered xreal_1
begin
(*begin*)
reserve x for "setHIDDENM2"
reserve p, q, r, s, t, u for "ExtRealXXREAL-0M1"
reserve g for "RealXREAL-0M1"
reserve a for "ElementSUBSET-1M1-of ExtREALXXREAL-0K3"
theorem xxreal_1_sch_1:
  fixes Pp1 Qp1 
  assumes
    A1: " for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds Pp1(r) & Qp1(s) implies r <=XXREAL-0R1 s"
  shows " ex s be ExtRealXXREAL-0M1 st ( for r be ExtRealXXREAL-0M1 holds Pp1(r) implies r <=XXREAL-0R1 s) & ( for r be ExtRealXXREAL-0M1 holds Qp1(r) implies s <=XXREAL-0R1 r)"
sorry

(*begin*)
mdef xxreal_1_def_1 ("[.XXREAL-1K1 _ , _ .]" [0,0]164 ) where
  mlet "r be ExtRealXXREAL-0M1", "s be ExtRealXXREAL-0M1"
"func [.XXREAL-1K1 r,s .] \<rightarrow> setHIDDENM2 equals
  {a where a be ElementSUBSET-1M1-of ExtREALXXREAL-0K3 : r <=XXREAL-0R1 a & a <=XXREAL-0R1 s }"
proof-
  (*coherence*)
    show "{a where a be ElementSUBSET-1M1-of ExtREALXXREAL-0K3 : r <=XXREAL-0R1 a & a <=XXREAL-0R1 s } be setHIDDENM2"
       sorry
qed "sorry"

mdef xxreal_1_def_2 ("[.XXREAL-1K2 _ , _ .[" [0,0]164 ) where
  mlet "r be ExtRealXXREAL-0M1", "s be ExtRealXXREAL-0M1"
"func [.XXREAL-1K2 r,s .[ \<rightarrow> setHIDDENM2 equals
  {a where a be ElementSUBSET-1M1-of ExtREALXXREAL-0K3 : r <=XXREAL-0R1 a & a <XXREAL-0R3 s }"
proof-
  (*coherence*)
    show "{a where a be ElementSUBSET-1M1-of ExtREALXXREAL-0K3 : r <=XXREAL-0R1 a & a <XXREAL-0R3 s } be setHIDDENM2"
       sorry
qed "sorry"

mdef xxreal_1_def_3 ("].XXREAL-1K3 _ , _ .]" [0,0]164 ) where
  mlet "r be ExtRealXXREAL-0M1", "s be ExtRealXXREAL-0M1"
"func ].XXREAL-1K3 r,s .] \<rightarrow> setHIDDENM2 equals
  {a where a be ElementSUBSET-1M1-of ExtREALXXREAL-0K3 : r <XXREAL-0R3 a & a <=XXREAL-0R1 s }"
proof-
  (*coherence*)
    show "{a where a be ElementSUBSET-1M1-of ExtREALXXREAL-0K3 : r <XXREAL-0R3 a & a <=XXREAL-0R1 s } be setHIDDENM2"
       sorry
qed "sorry"

mdef xxreal_1_def_4 ("].XXREAL-1K4 _ , _ .[" [0,0]164 ) where
  mlet "r be ExtRealXXREAL-0M1", "s be ExtRealXXREAL-0M1"
"func ].XXREAL-1K4 r,s .[ \<rightarrow> setHIDDENM2 equals
  {a where a be ElementSUBSET-1M1-of ExtREALXXREAL-0K3 : r <XXREAL-0R3 a & a <XXREAL-0R3 s }"
proof-
  (*coherence*)
    show "{a where a be ElementSUBSET-1M1-of ExtREALXXREAL-0K3 : r <XXREAL-0R3 a & a <XXREAL-0R3 s } be setHIDDENM2"
       sorry
qed "sorry"

mtheorem xxreal_1_th_1:
" for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds  for t be ExtRealXXREAL-0M1 holds t inHIDDENR3 [.XXREAL-1K1 r,s .] iff r <=XXREAL-0R1 t & t <=XXREAL-0R1 s"
sorry

mtheorem xxreal_1_th_2:
" for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds  for t be ExtRealXXREAL-0M1 holds t inHIDDENR3 ].XXREAL-1K3 r,s .] iff r <XXREAL-0R3 t & t <=XXREAL-0R1 s"
sorry

mtheorem xxreal_1_th_3:
" for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds  for t be ExtRealXXREAL-0M1 holds t inHIDDENR3 [.XXREAL-1K2 r,s .[ iff r <=XXREAL-0R1 t & t <XXREAL-0R3 s"
sorry

mtheorem xxreal_1_th_4:
" for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds  for t be ExtRealXXREAL-0M1 holds t inHIDDENR3 ].XXREAL-1K4 r,s .[ iff r <XXREAL-0R3 t & t <XXREAL-0R3 s"
sorry

mtheorem xxreal_1_cl_1:
  mlet "r be ExtRealXXREAL-0M1", "s be ExtRealXXREAL-0M1"
"cluster [.XXREAL-1K1 r,s .] as-term-is ext-real-memberedMEMBEREDV2"
proof
(*coherence*)
  show "[.XXREAL-1K1 r,s .] be ext-real-memberedMEMBEREDV2"
sorry
qed "sorry"

mtheorem xxreal_1_cl_2:
  mlet "r be ExtRealXXREAL-0M1", "s be ExtRealXXREAL-0M1"
"cluster [.XXREAL-1K2 r,s .[ as-term-is ext-real-memberedMEMBEREDV2"
proof
(*coherence*)
  show "[.XXREAL-1K2 r,s .[ be ext-real-memberedMEMBEREDV2"
sorry
qed "sorry"

mtheorem xxreal_1_cl_3:
  mlet "r be ExtRealXXREAL-0M1", "s be ExtRealXXREAL-0M1"
"cluster ].XXREAL-1K3 r,s .] as-term-is ext-real-memberedMEMBEREDV2"
proof
(*coherence*)
  show "].XXREAL-1K3 r,s .] be ext-real-memberedMEMBEREDV2"
sorry
qed "sorry"

mtheorem xxreal_1_cl_4:
  mlet "r be ExtRealXXREAL-0M1", "s be ExtRealXXREAL-0M1"
"cluster ].XXREAL-1K4 r,s .[ as-term-is ext-real-memberedMEMBEREDV2"
proof
(*coherence*)
  show "].XXREAL-1K4 r,s .[ be ext-real-memberedMEMBEREDV2"
sorry
qed "sorry"

mtheorem xxreal_1_th_5:
" for x be setHIDDENM2 holds  for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds x inTARSKIR2 [.XXREAL-1K1 p,q .] implies (x inTARSKIR2 ].XXREAL-1K4 p,q .[ or x =HIDDENR1 p) or x =HIDDENR1 q"
sorry

mtheorem xxreal_1_th_6:
" for x be setHIDDENM2 holds  for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds x inTARSKIR2 [.XXREAL-1K1 p,q .] implies x inTARSKIR2 ].XXREAL-1K3 p,q .] or x =HIDDENR1 p"
sorry

mtheorem xxreal_1_th_7:
" for x be setHIDDENM2 holds  for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds x inTARSKIR2 [.XXREAL-1K1 p,q .] implies x inTARSKIR2 [.XXREAL-1K2 p,q .[ or x =HIDDENR1 q"
sorry

mtheorem xxreal_1_th_8:
" for x be setHIDDENM2 holds  for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds x inTARSKIR2 [.XXREAL-1K2 p,q .[ implies x inTARSKIR2 ].XXREAL-1K4 p,q .[ or x =HIDDENR1 p"
sorry

mtheorem xxreal_1_th_9:
" for x be setHIDDENM2 holds  for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds x inTARSKIR2 ].XXREAL-1K3 p,q .] implies x inTARSKIR2 ].XXREAL-1K4 p,q .[ or x =HIDDENR1 q"
sorry

mtheorem xxreal_1_th_10:
" for x be setHIDDENM2 holds  for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds x inTARSKIR2 [.XXREAL-1K2 p,q .[ implies x inTARSKIR2 ].XXREAL-1K3 p,q .] & x <>HIDDENR2 q or x =HIDDENR1 p"
sorry

mtheorem xxreal_1_th_11:
" for x be setHIDDENM2 holds  for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds x inTARSKIR2 ].XXREAL-1K3 p,q .] implies x inTARSKIR2 [.XXREAL-1K2 p,q .[ & x <>HIDDENR2 p or x =HIDDENR1 q"
sorry

mtheorem xxreal_1_th_12:
" for x be setHIDDENM2 holds  for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds x inTARSKIR2 ].XXREAL-1K3 p,q .] implies x inTARSKIR2 [.XXREAL-1K1 p,q .] & x <>HIDDENR2 p"
sorry

mtheorem xxreal_1_th_13:
" for x be setHIDDENM2 holds  for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds x inTARSKIR2 [.XXREAL-1K2 p,q .[ implies x inTARSKIR2 [.XXREAL-1K1 p,q .] & x <>HIDDENR2 q"
sorry

mtheorem xxreal_1_th_14:
" for x be setHIDDENM2 holds  for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds x inTARSKIR2 ].XXREAL-1K4 p,q .[ implies x inTARSKIR2 [.XXREAL-1K2 p,q .[ & x <>HIDDENR2 p"
sorry

mtheorem xxreal_1_th_15:
" for x be setHIDDENM2 holds  for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds x inTARSKIR2 ].XXREAL-1K4 p,q .[ implies x inTARSKIR2 ].XXREAL-1K3 p,q .] & x <>HIDDENR2 q"
sorry

mtheorem xxreal_1_th_16:
" for x be setHIDDENM2 holds  for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds x inTARSKIR2 ].XXREAL-1K4 p,q .[ implies (x inTARSKIR2 [.XXREAL-1K1 p,q .] & x <>HIDDENR2 p) & x <>HIDDENR2 q"
sorry

mtheorem xxreal_1_th_17:
" for r be ExtRealXXREAL-0M1 holds [.XXREAL-1K1 r,r .] =MEMBEREDR8 {TARSKIK1 r}"
sorry

mtheorem xxreal_1_th_18:
" for r be ExtRealXXREAL-0M1 holds [.XXREAL-1K2 r,r .[ =MEMBEREDR8 {}XBOOLE-0K1"
sorry

mtheorem xxreal_1_th_19:
" for r be ExtRealXXREAL-0M1 holds ].XXREAL-1K3 r,r .] =MEMBEREDR8 {}XBOOLE-0K1"
sorry

mtheorem xxreal_1_th_20:
" for r be ExtRealXXREAL-0M1 holds ].XXREAL-1K4 r,r .[ =MEMBEREDR8 {}XBOOLE-0K1"
sorry

mtheorem xxreal_1_cl_5:
  mlet "r be ExtRealXXREAL-0M1"
"cluster [.XXREAL-1K1 r,r .] as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "[.XXREAL-1K1 r,r .] be  non emptyXBOOLE-0V1"
sorry
qed "sorry"

mtheorem xxreal_1_cl_6:
  mlet "r be ExtRealXXREAL-0M1"
"cluster [.XXREAL-1K2 r,r .[ as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "[.XXREAL-1K2 r,r .[ be emptyXBOOLE-0V1"
    using xxreal_1_th_18 sorry
qed "sorry"

mtheorem xxreal_1_cl_7:
  mlet "r be ExtRealXXREAL-0M1"
"cluster ].XXREAL-1K3 r,r .] as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "].XXREAL-1K3 r,r .] be emptyXBOOLE-0V1"
    using xxreal_1_th_19 sorry
qed "sorry"

mtheorem xxreal_1_cl_8:
  mlet "r be ExtRealXXREAL-0M1"
"cluster ].XXREAL-1K4 r,r .[ as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "].XXREAL-1K4 r,r .[ be emptyXBOOLE-0V1"
    using xxreal_1_th_20 sorry
qed "sorry"

mtheorem xxreal_1_th_21:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds ].XXREAL-1K4 p,q .[ c=MEMBEREDR2 ].XXREAL-1K3 p,q .]"
sorry

mtheorem xxreal_1_th_22:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds ].XXREAL-1K4 p,q .[ c=MEMBEREDR2 [.XXREAL-1K2 p,q .["
sorry

mtheorem xxreal_1_th_23:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds ].XXREAL-1K3 p,q .] c=MEMBEREDR2 [.XXREAL-1K1 p,q .]"
sorry

mtheorem xxreal_1_th_24:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds [.XXREAL-1K2 p,q .[ c=MEMBEREDR2 [.XXREAL-1K1 p,q .]"
sorry

mtheorem xxreal_1_th_25:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds ].XXREAL-1K4 p,q .[ c=MEMBEREDR2 [.XXREAL-1K1 p,q .]"
sorry

mtheorem xxreal_1_th_26:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds p <=XXREAL-0R1 q implies ].XXREAL-1K3 q,p .] =MEMBEREDR8 {}XBOOLE-0K1"
sorry

mtheorem xxreal_1_th_27:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds p <=XXREAL-0R1 q implies [.XXREAL-1K2 q,p .[ =MEMBEREDR8 {}XBOOLE-0K1"
sorry

mtheorem xxreal_1_th_28:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds p <=XXREAL-0R1 q implies ].XXREAL-1K4 q,p .[ =MEMBEREDR8 {}XBOOLE-0K1"
sorry

mtheorem xxreal_1_th_29:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds p <XXREAL-0R3 q implies [.XXREAL-1K1 q,p .] =MEMBEREDR8 {}XBOOLE-0K1"
sorry

mtheorem xxreal_1_th_30:
" for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <=XXREAL-0R1 s implies [.XXREAL-1K1 r,s .] be  non emptyXBOOLE-0V1"
  using xxreal_1_th_1 sorry

mtheorem xxreal_1_th_31:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds p <XXREAL-0R3 q implies [.XXREAL-1K2 p,q .[ be  non emptyXBOOLE-0V1"
  using xxreal_1_th_3 sorry

mtheorem xxreal_1_th_32:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds p <XXREAL-0R3 q implies ].XXREAL-1K3 p,q .] be  non emptyXBOOLE-0V1"
  using xxreal_1_th_2 sorry

mtheorem xxreal_1_th_33:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds p <XXREAL-0R3 q implies ].XXREAL-1K4 p,q .[ be  non emptyXBOOLE-0V1"
sorry

mtheorem xxreal_1_th_34:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds p <=XXREAL-0R1 r & s <=XXREAL-0R1 q implies [.XXREAL-1K1 r,s .] c=MEMBEREDR2 [.XXREAL-1K1 p,q .]"
sorry

mtheorem xxreal_1_th_35:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds p <=XXREAL-0R1 r & s <=XXREAL-0R1 q implies [.XXREAL-1K2 r,s .[ c=MEMBEREDR2 [.XXREAL-1K1 p,q .]"
sorry

mtheorem xxreal_1_th_36:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds p <=XXREAL-0R1 r & s <=XXREAL-0R1 q implies ].XXREAL-1K3 r,s .] c=MEMBEREDR2 [.XXREAL-1K1 p,q .]"
sorry

mtheorem xxreal_1_th_37:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds p <=XXREAL-0R1 r & s <=XXREAL-0R1 q implies ].XXREAL-1K4 r,s .[ c=MEMBEREDR2 [.XXREAL-1K1 p,q .]"
sorry

mtheorem xxreal_1_th_38:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds p <=XXREAL-0R1 r & s <=XXREAL-0R1 q implies [.XXREAL-1K2 r,s .[ c=MEMBEREDR2 [.XXREAL-1K2 p,q .["
sorry

mtheorem xxreal_1_th_39:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds p <XXREAL-0R3 r & s <=XXREAL-0R1 q implies [.XXREAL-1K1 r,s .] c=MEMBEREDR2 ].XXREAL-1K3 p,q .]"
sorry

mtheorem xxreal_1_th_40:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds p <XXREAL-0R3 r & s <=XXREAL-0R1 q implies [.XXREAL-1K2 r,s .[ c=MEMBEREDR2 ].XXREAL-1K3 p,q .]"
sorry

mtheorem xxreal_1_th_41:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds p <=XXREAL-0R1 r & s <=XXREAL-0R1 q implies ].XXREAL-1K4 r,s .[ c=MEMBEREDR2 ].XXREAL-1K3 p,q .]"
sorry

mtheorem xxreal_1_th_42:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds p <=XXREAL-0R1 r & s <=XXREAL-0R1 q implies ].XXREAL-1K3 r,s .] c=MEMBEREDR2 ].XXREAL-1K3 p,q .]"
sorry

mtheorem xxreal_1_th_43:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds p <=XXREAL-0R1 r & s <XXREAL-0R3 q implies [.XXREAL-1K1 r,s .] c=MEMBEREDR2 [.XXREAL-1K2 p,q .["
sorry

mtheorem xxreal_1_th_44:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds p <=XXREAL-0R1 r & s <XXREAL-0R3 q implies ].XXREAL-1K3 r,s .] c=MEMBEREDR2 [.XXREAL-1K2 p,q .["
sorry

mtheorem xxreal_1_th_45:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds p <=XXREAL-0R1 r & s <=XXREAL-0R1 q implies ].XXREAL-1K4 r,s .[ c=MEMBEREDR2 [.XXREAL-1K2 p,q .["
sorry

mtheorem xxreal_1_th_46:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds p <=XXREAL-0R1 r & s <=XXREAL-0R1 q implies ].XXREAL-1K4 r,s .[ c=MEMBEREDR2 ].XXREAL-1K4 p,q .["
sorry

mtheorem xxreal_1_th_47:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds p <XXREAL-0R3 r & s <XXREAL-0R3 q implies [.XXREAL-1K1 r,s .] c=MEMBEREDR2 ].XXREAL-1K4 p,q .["
sorry

mtheorem xxreal_1_th_48:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds p <XXREAL-0R3 r & s <=XXREAL-0R1 q implies [.XXREAL-1K2 r,s .[ c=MEMBEREDR2 ].XXREAL-1K4 p,q .["
sorry

mtheorem xxreal_1_th_49:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds p <=XXREAL-0R1 r & s <XXREAL-0R3 q implies ].XXREAL-1K3 r,s .] c=MEMBEREDR2 ].XXREAL-1K4 p,q .["
sorry

mtheorem xxreal_1_th_50:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <=XXREAL-0R1 s & [.XXREAL-1K1 r,s .] c=MEMBEREDR2 [.XXREAL-1K1 p,q .] implies p <=XXREAL-0R1 r & s <=XXREAL-0R1 q"
sorry

mtheorem xxreal_1_th_51:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <XXREAL-0R3 s & ].XXREAL-1K4 r,s .[ c=MEMBEREDR2 [.XXREAL-1K1 p,q .] implies p <=XXREAL-0R1 r & s <=XXREAL-0R1 q"
sorry

mtheorem xxreal_1_th_52:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <XXREAL-0R3 s & [.XXREAL-1K2 r,s .[ c=MEMBEREDR2 [.XXREAL-1K1 p,q .] implies p <=XXREAL-0R1 r & s <=XXREAL-0R1 q"
sorry

mtheorem xxreal_1_th_53:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <XXREAL-0R3 s & ].XXREAL-1K3 r,s .] c=MEMBEREDR2 [.XXREAL-1K1 p,q .] implies p <=XXREAL-0R1 r & s <=XXREAL-0R1 q"
sorry

mtheorem xxreal_1_th_54:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <=XXREAL-0R1 s & [.XXREAL-1K1 r,s .] c=MEMBEREDR2 [.XXREAL-1K2 p,q .[ implies p <=XXREAL-0R1 r & s <XXREAL-0R3 q"
sorry

mtheorem xxreal_1_th_55:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <XXREAL-0R3 s & [.XXREAL-1K2 r,s .[ c=MEMBEREDR2 [.XXREAL-1K2 p,q .[ implies p <=XXREAL-0R1 r & s <=XXREAL-0R1 q"
sorry

mtheorem xxreal_1_th_56:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <XXREAL-0R3 s & ].XXREAL-1K4 r,s .[ c=MEMBEREDR2 [.XXREAL-1K2 p,q .[ implies p <=XXREAL-0R1 r & s <=XXREAL-0R1 q"
sorry

mtheorem xxreal_1_th_57:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <XXREAL-0R3 s & ].XXREAL-1K3 r,s .] c=MEMBEREDR2 [.XXREAL-1K2 p,q .[ implies p <=XXREAL-0R1 r & s <XXREAL-0R3 q"
sorry

mtheorem xxreal_1_th_58:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <=XXREAL-0R1 s & [.XXREAL-1K1 r,s .] c=MEMBEREDR2 ].XXREAL-1K3 p,q .] implies p <XXREAL-0R3 r & s <=XXREAL-0R1 q"
sorry

mtheorem xxreal_1_th_59:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <XXREAL-0R3 s & ].XXREAL-1K4 r,s .[ c=MEMBEREDR2 ].XXREAL-1K3 p,q .] implies p <=XXREAL-0R1 r & s <=XXREAL-0R1 q"
sorry

mtheorem xxreal_1_th_60:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <XXREAL-0R3 s & [.XXREAL-1K2 r,s .[ c=MEMBEREDR2 ].XXREAL-1K3 p,q .] implies p <XXREAL-0R3 r & s <=XXREAL-0R1 q"
sorry

mtheorem xxreal_1_th_61:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <XXREAL-0R3 s & ].XXREAL-1K3 r,s .] c=MEMBEREDR2 ].XXREAL-1K3 p,q .] implies p <=XXREAL-0R1 r & s <=XXREAL-0R1 q"
sorry

mtheorem xxreal_1_th_62:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <=XXREAL-0R1 s & [.XXREAL-1K1 r,s .] c=MEMBEREDR2 ].XXREAL-1K4 p,q .[ implies p <XXREAL-0R3 r & s <XXREAL-0R3 q"
sorry

mtheorem xxreal_1_th_63:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <XXREAL-0R3 s & ].XXREAL-1K4 r,s .[ c=MEMBEREDR2 ].XXREAL-1K4 p,q .[ implies p <=XXREAL-0R1 r & s <=XXREAL-0R1 q"
sorry

mtheorem xxreal_1_th_64:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <XXREAL-0R3 s & [.XXREAL-1K2 r,s .[ c=MEMBEREDR2 ].XXREAL-1K4 p,q .[ implies p <XXREAL-0R3 r & s <=XXREAL-0R1 q"
sorry

mtheorem xxreal_1_th_65:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <XXREAL-0R3 s & ].XXREAL-1K3 r,s .] c=MEMBEREDR2 ].XXREAL-1K4 p,q .[ implies p <=XXREAL-0R1 r & s <XXREAL-0R3 q"
sorry

mtheorem xxreal_1_th_66:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds p <=XXREAL-0R1 q & [.XXREAL-1K1 p,q .] =MEMBEREDR8 [.XXREAL-1K1 r,s .] implies p =HIDDENR1 r & q =HIDDENR1 s"
sorry

mtheorem xxreal_1_th_67:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds p <XXREAL-0R3 q & ].XXREAL-1K4 p,q .[ =MEMBEREDR8 ].XXREAL-1K4 r,s .[ implies p =HIDDENR1 r & q =HIDDENR1 s"
sorry

mtheorem xxreal_1_th_68:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds p <XXREAL-0R3 q & ].XXREAL-1K3 p,q .] =MEMBEREDR8 ].XXREAL-1K3 r,s .] implies p =HIDDENR1 r & q =HIDDENR1 s"
sorry

mtheorem xxreal_1_th_69:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds p <XXREAL-0R3 q & [.XXREAL-1K2 p,q .[ =MEMBEREDR8 [.XXREAL-1K2 r,s .[ implies p =HIDDENR1 r & q =HIDDENR1 s"
sorry

mtheorem xxreal_1_th_70:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <=XXREAL-0R1 s implies [.XXREAL-1K1 r,s .] <>HIDDENR2 ].XXREAL-1K3 p,q .]"
sorry

mtheorem xxreal_1_th_71:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <=XXREAL-0R1 s implies [.XXREAL-1K1 r,s .] <>HIDDENR2 [.XXREAL-1K2 p,q .["
sorry

mtheorem xxreal_1_th_72:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <=XXREAL-0R1 s implies [.XXREAL-1K1 r,s .] <>HIDDENR2 ].XXREAL-1K4 p,q .["
sorry

mtheorem xxreal_1_th_73:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <XXREAL-0R3 s implies [.XXREAL-1K2 r,s .[ <>HIDDENR2 [.XXREAL-1K1 p,q .]"
sorry

mtheorem xxreal_1_th_74:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <XXREAL-0R3 s implies [.XXREAL-1K2 r,s .[ <>HIDDENR2 ].XXREAL-1K3 p,q .]"
sorry

mtheorem xxreal_1_th_75:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <XXREAL-0R3 s implies [.XXREAL-1K2 r,s .[ <>HIDDENR2 ].XXREAL-1K4 p,q .["
sorry

mtheorem xxreal_1_th_76:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <XXREAL-0R3 s implies ].XXREAL-1K3 r,s .] <>HIDDENR2 [.XXREAL-1K1 p,q .]"
sorry

mtheorem xxreal_1_th_77:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <XXREAL-0R3 s implies ].XXREAL-1K3 r,s .] <>HIDDENR2 [.XXREAL-1K2 p,q .["
sorry

mtheorem xxreal_1_th_78:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <XXREAL-0R3 s implies ].XXREAL-1K3 r,s .] <>HIDDENR2 ].XXREAL-1K4 p,q .["
sorry

mtheorem xxreal_1_th_79:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <XXREAL-0R3 s implies ].XXREAL-1K4 r,s .[ <>HIDDENR2 [.XXREAL-1K1 p,q .]"
sorry

mtheorem xxreal_1_th_80:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <XXREAL-0R3 s implies ].XXREAL-1K4 r,s .[ <>HIDDENR2 ].XXREAL-1K3 p,q .]"
sorry

mtheorem xxreal_1_th_81:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <XXREAL-0R3 s implies ].XXREAL-1K4 r,s .[ <>HIDDENR2 [.XXREAL-1K2 p,q .["
sorry

mtheorem xxreal_1_th_82:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <=XXREAL-0R1 s & [.XXREAL-1K1 r,s .] c<XBOOLE-0R2 [.XXREAL-1K1 p,q .] implies p <XXREAL-0R3 r or s <XXREAL-0R3 q"
sorry

mtheorem xxreal_1_th_83:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <XXREAL-0R3 s & ].XXREAL-1K4 r,s .[ c=MEMBEREDR2 [.XXREAL-1K1 p,q .] implies [.XXREAL-1K1 r,s .] c=MEMBEREDR2 [.XXREAL-1K1 p,q .]"
sorry

mtheorem xxreal_1_th_84:
" for p be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <XXREAL-0R3 s implies [.XXREAL-1K2 s,p .[ c=MEMBEREDR2 ].XXREAL-1K4 r,p .["
sorry

mtheorem xxreal_1_th_85:
" for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds s <=XXREAL-0R1 r implies [.XXREAL-1K1 r,s .] c=MEMBEREDR2 {TARSKIK1 r} & [.XXREAL-1K1 r,s .] c=MEMBEREDR2 {TARSKIK1 s}"
sorry

mtheorem xxreal_1_th_86:
" for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds ].XXREAL-1K4 r,s .[ missesMEMBEREDR14 {TARSKIK2 r,s }"
sorry

mtheorem xxreal_1_th_87:
" for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds [.XXREAL-1K2 r,s .[ missesMEMBEREDR14 {TARSKIK1 s}"
sorry

mtheorem xxreal_1_th_88:
" for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds ].XXREAL-1K3 r,s .] missesMEMBEREDR14 {TARSKIK1 r}"
sorry

mtheorem xxreal_1_th_89:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds s <=XXREAL-0R1 p implies [.XXREAL-1K1 r,s .] missesMEMBEREDR14 ].XXREAL-1K4 p,q .["
sorry

mtheorem xxreal_1_th_90:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds s <=XXREAL-0R1 p implies [.XXREAL-1K1 r,s .] missesMEMBEREDR14 ].XXREAL-1K3 p,q .]"
sorry

mtheorem xxreal_1_th_91:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds s <=XXREAL-0R1 p implies ].XXREAL-1K3 r,s .] missesMEMBEREDR14 ].XXREAL-1K4 p,q .["
sorry

mtheorem xxreal_1_th_92:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds s <=XXREAL-0R1 p implies ].XXREAL-1K3 r,s .] missesMEMBEREDR14 ].XXREAL-1K3 p,q .]"
sorry

mtheorem xxreal_1_th_93:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds s <=XXREAL-0R1 p implies ].XXREAL-1K4 r,s .[ missesMEMBEREDR14 [.XXREAL-1K1 p,q .]"
sorry

mtheorem xxreal_1_th_94:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds s <=XXREAL-0R1 p implies ].XXREAL-1K4 r,s .[ missesMEMBEREDR14 [.XXREAL-1K2 p,q .["
sorry

mtheorem xxreal_1_th_95:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds s <=XXREAL-0R1 p implies [.XXREAL-1K2 r,s .[ missesMEMBEREDR14 [.XXREAL-1K1 p,q .]"
sorry

mtheorem xxreal_1_th_96:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds s <=XXREAL-0R1 p implies [.XXREAL-1K2 r,s .[ missesMEMBEREDR14 [.XXREAL-1K2 p,q .["
sorry

mtheorem xxreal_1_th_97:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <XXREAL-0R3 p & r <XXREAL-0R3 s implies  not ].XXREAL-1K4 r,s .[ c=MEMBEREDR2 [.XXREAL-1K1 p,q .]"
sorry

mtheorem xxreal_1_th_98:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <XXREAL-0R3 p & r <XXREAL-0R3 s implies  not [.XXREAL-1K2 r,s .[ c=MEMBEREDR2 [.XXREAL-1K1 p,q .]"
sorry

mtheorem xxreal_1_th_99:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <XXREAL-0R3 p & r <XXREAL-0R3 s implies  not ].XXREAL-1K3 r,s .] c=MEMBEREDR2 [.XXREAL-1K1 p,q .]"
sorry

mtheorem xxreal_1_th_100:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <XXREAL-0R3 p & r <=XXREAL-0R1 s implies  not [.XXREAL-1K1 r,s .] c=MEMBEREDR2 [.XXREAL-1K1 p,q .]"
sorry

mtheorem xxreal_1_th_101:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <XXREAL-0R3 p & r <XXREAL-0R3 s implies  not ].XXREAL-1K4 r,s .[ c=MEMBEREDR2 [.XXREAL-1K2 p,q .["
sorry

mtheorem xxreal_1_th_102:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <XXREAL-0R3 p & r <XXREAL-0R3 s implies  not ].XXREAL-1K3 r,s .] c=MEMBEREDR2 [.XXREAL-1K2 p,q .["
sorry

mtheorem xxreal_1_th_103:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <XXREAL-0R3 p & r <XXREAL-0R3 s implies  not [.XXREAL-1K2 r,s .[ c=MEMBEREDR2 [.XXREAL-1K2 p,q .["
sorry

mtheorem xxreal_1_th_104:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <XXREAL-0R3 p & r <=XXREAL-0R1 s implies  not [.XXREAL-1K1 r,s .] c=MEMBEREDR2 [.XXREAL-1K2 p,q .["
sorry

mtheorem xxreal_1_th_105:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <XXREAL-0R3 p & r <XXREAL-0R3 s implies  not ].XXREAL-1K4 r,s .[ c=MEMBEREDR2 ].XXREAL-1K3 p,q .]"
sorry

mtheorem xxreal_1_th_106:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <=XXREAL-0R1 p & r <XXREAL-0R3 s implies  not [.XXREAL-1K2 r,s .[ c=MEMBEREDR2 ].XXREAL-1K3 p,q .]"
sorry

mtheorem xxreal_1_th_107:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <XXREAL-0R3 p & r <XXREAL-0R3 s implies  not ].XXREAL-1K3 r,s .] c=MEMBEREDR2 ].XXREAL-1K3 p,q .]"
sorry

mtheorem xxreal_1_th_108:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <=XXREAL-0R1 p & r <=XXREAL-0R1 s implies  not [.XXREAL-1K1 r,s .] c=MEMBEREDR2 ].XXREAL-1K3 p,q .]"
sorry

mtheorem xxreal_1_th_109:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <=XXREAL-0R1 p & r <=XXREAL-0R1 s implies  not [.XXREAL-1K1 r,s .] c=MEMBEREDR2 ].XXREAL-1K4 p,q .["
sorry

mtheorem xxreal_1_th_110:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <=XXREAL-0R1 p & r <XXREAL-0R3 s implies  not [.XXREAL-1K2 r,s .[ c=MEMBEREDR2 ].XXREAL-1K4 p,q .["
sorry

mtheorem xxreal_1_th_111:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <XXREAL-0R3 p & r <XXREAL-0R3 s implies  not ].XXREAL-1K3 r,s .] c=MEMBEREDR2 ].XXREAL-1K4 p,q .["
sorry

mtheorem xxreal_1_th_112:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <XXREAL-0R3 p & r <XXREAL-0R3 s implies  not ].XXREAL-1K4 r,s .[ c=MEMBEREDR2 ].XXREAL-1K4 p,q .["
sorry

mtheorem xxreal_1_th_113:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds q <XXREAL-0R3 s & r <XXREAL-0R3 s implies  not ].XXREAL-1K4 r,s .[ c=MEMBEREDR2 [.XXREAL-1K1 p,q .]"
sorry

mtheorem xxreal_1_th_114:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds q <XXREAL-0R3 s & r <XXREAL-0R3 s implies  not [.XXREAL-1K2 r,s .[ c=MEMBEREDR2 [.XXREAL-1K1 p,q .]"
sorry

mtheorem xxreal_1_th_115:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds q <XXREAL-0R3 s & r <XXREAL-0R3 s implies  not ].XXREAL-1K3 r,s .] c=MEMBEREDR2 [.XXREAL-1K1 p,q .]"
sorry

mtheorem xxreal_1_th_116:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds q <XXREAL-0R3 s & r <=XXREAL-0R1 s implies  not [.XXREAL-1K1 r,s .] c=MEMBEREDR2 [.XXREAL-1K1 p,q .]"
sorry

mtheorem xxreal_1_th_117:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds q <XXREAL-0R3 s & r <XXREAL-0R3 s implies  not ].XXREAL-1K4 r,s .[ c=MEMBEREDR2 [.XXREAL-1K2 p,q .["
sorry

mtheorem xxreal_1_th_118:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds q <=XXREAL-0R1 s & r <XXREAL-0R3 s implies  not ].XXREAL-1K3 r,s .] c=MEMBEREDR2 [.XXREAL-1K2 p,q .["
sorry

mtheorem xxreal_1_th_119:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds q <XXREAL-0R3 s & r <XXREAL-0R3 s implies  not [.XXREAL-1K2 r,s .[ c=MEMBEREDR2 [.XXREAL-1K2 p,q .["
sorry

mtheorem xxreal_1_th_120:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds q <XXREAL-0R3 s & r <XXREAL-0R3 s implies  not ].XXREAL-1K4 r,s .[ c=MEMBEREDR2 ].XXREAL-1K3 p,q .]"
sorry

mtheorem xxreal_1_th_121:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds q <XXREAL-0R3 s & r <=XXREAL-0R1 s implies  not [.XXREAL-1K1 r,s .] c=MEMBEREDR2 ].XXREAL-1K3 p,q .]"
sorry

mtheorem xxreal_1_th_122:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds q <XXREAL-0R3 s & r <XXREAL-0R3 s implies  not [.XXREAL-1K2 r,s .[ c=MEMBEREDR2 ].XXREAL-1K3 p,q .]"
sorry

mtheorem xxreal_1_th_123:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds q <XXREAL-0R3 s & r <XXREAL-0R3 s implies  not ].XXREAL-1K3 r,s .] c=MEMBEREDR2 ].XXREAL-1K3 p,q .]"
sorry

mtheorem xxreal_1_th_124:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds q <=XXREAL-0R1 s & r <=XXREAL-0R1 s implies  not [.XXREAL-1K1 r,s .] c=MEMBEREDR2 ].XXREAL-1K4 p,q .["
sorry

mtheorem xxreal_1_th_125:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds q <XXREAL-0R3 s & r <XXREAL-0R3 s implies  not [.XXREAL-1K2 r,s .[ c=MEMBEREDR2 ].XXREAL-1K4 p,q .["
sorry

mtheorem xxreal_1_th_126:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds q <=XXREAL-0R1 s & r <XXREAL-0R3 s implies  not ].XXREAL-1K3 r,s .] c=MEMBEREDR2 ].XXREAL-1K4 p,q .["
sorry

mtheorem xxreal_1_th_127:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds q <XXREAL-0R3 s & r <XXREAL-0R3 s implies  not ].XXREAL-1K4 r,s .[ c=MEMBEREDR2 ].XXREAL-1K4 p,q .["
sorry

(*begin*)
mtheorem xxreal_1_th_128:
" for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <=XXREAL-0R1 s implies [.XXREAL-1K1 r,s .] =MEMBEREDR8 ].XXREAL-1K4 r,s .[ \\/XBOOLE-0K2 {TARSKIK2 r,s }"
sorry

mtheorem xxreal_1_th_129:
" for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <=XXREAL-0R1 s implies [.XXREAL-1K1 r,s .] =MEMBEREDR8 [.XXREAL-1K2 r,s .[ \\/XBOOLE-0K2 {TARSKIK1 s}"
sorry

mtheorem xxreal_1_th_130:
" for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <=XXREAL-0R1 s implies [.XXREAL-1K1 r,s .] =MEMBEREDR8 {TARSKIK1 r} \\/XBOOLE-0K2 ].XXREAL-1K3 r,s .]"
sorry

mtheorem xxreal_1_th_131:
" for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <XXREAL-0R3 s implies [.XXREAL-1K2 r,s .[ =MEMBEREDR8 {TARSKIK1 r} \\/XBOOLE-0K2 ].XXREAL-1K4 r,s .["
sorry

mtheorem xxreal_1_th_132:
" for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <XXREAL-0R3 s implies ].XXREAL-1K3 r,s .] =MEMBEREDR8 ].XXREAL-1K4 r,s .[ \\/XBOOLE-0K2 {TARSKIK1 s}"
sorry

mtheorem xxreal_1_th_133:
" for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <=XXREAL-0R1 s implies [.XXREAL-1K1 r,s .] \\SUBSET-1K6 {TARSKIK2 r,s } =MEMBEREDR8 ].XXREAL-1K4 r,s .["
sorry

mtheorem xxreal_1_th_134:
" for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <=XXREAL-0R1 s implies [.XXREAL-1K1 r,s .] \\SUBSET-1K6 {TARSKIK1 r} =MEMBEREDR8 ].XXREAL-1K3 r,s .]"
sorry

mtheorem xxreal_1_th_135:
" for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <=XXREAL-0R1 s implies [.XXREAL-1K1 r,s .] \\SUBSET-1K6 {TARSKIK1 s} =MEMBEREDR8 [.XXREAL-1K2 r,s .["
sorry

mtheorem xxreal_1_th_136:
" for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <XXREAL-0R3 s implies [.XXREAL-1K2 r,s .[ \\SUBSET-1K6 {TARSKIK1 r} =MEMBEREDR8 ].XXREAL-1K4 r,s .["
sorry

mtheorem xxreal_1_th_137:
" for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <XXREAL-0R3 s implies ].XXREAL-1K3 r,s .] \\SUBSET-1K6 {TARSKIK1 s} =MEMBEREDR8 ].XXREAL-1K4 r,s .["
sorry

mtheorem xxreal_1_th_138:
" for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds  for t be ExtRealXXREAL-0M1 holds r <XXREAL-0R3 s & s <XXREAL-0R3 t implies (].XXREAL-1K3 r,s .])/\\XBOOLE-0K3 ([.XXREAL-1K2 s,t .[) =MEMBEREDR8 {TARSKIK1 s}"
sorry

mtheorem xxreal_1_th_139:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds ([.XXREAL-1K2 r,s .[)/\\XBOOLE-0K3 ([.XXREAL-1K2 p,q .[) =MEMBEREDR8 [.XXREAL-1K2 maxXXREAL-0K5(r,p),minXXREAL-0K4(s,q) .["
sorry

mtheorem xxreal_1_th_140:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds ([.XXREAL-1K1 r,s .])/\\XBOOLE-0K3 ([.XXREAL-1K1 p,q .]) =MEMBEREDR8 [.XXREAL-1K1 maxXXREAL-0K5(r,p),minXXREAL-0K4(s,q) .]"
sorry

mtheorem xxreal_1_th_141:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds (].XXREAL-1K3 r,s .])/\\XBOOLE-0K3 (].XXREAL-1K3 p,q .]) =MEMBEREDR8 ].XXREAL-1K3 maxXXREAL-0K5(r,p),minXXREAL-0K4(s,q) .]"
sorry

mtheorem xxreal_1_th_142:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds (].XXREAL-1K4 r,s .[)/\\XBOOLE-0K3 (].XXREAL-1K4 p,q .[) =MEMBEREDR8 ].XXREAL-1K4 maxXXREAL-0K5(r,p),minXXREAL-0K4(s,q) .["
sorry

mtheorem xxreal_1_th_143:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <=XXREAL-0R1 p & s <=XXREAL-0R1 q implies ([.XXREAL-1K1 r,s .])/\\XBOOLE-0K3 ([.XXREAL-1K1 p,q .]) =MEMBEREDR8 [.XXREAL-1K1 p,s .]"
sorry

mtheorem xxreal_1_th_144:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <=XXREAL-0R1 p & s <=XXREAL-0R1 q implies ([.XXREAL-1K2 r,s .[)/\\XBOOLE-0K3 ([.XXREAL-1K1 p,q .]) =MEMBEREDR8 [.XXREAL-1K2 p,s .["
sorry

mtheorem xxreal_1_th_145:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r >=XXREAL-0R2 p & s >XXREAL-0R4 q implies ([.XXREAL-1K2 r,s .[)/\\XBOOLE-0K3 ([.XXREAL-1K1 p,q .]) =MEMBEREDR8 [.XXREAL-1K1 r,q .]"
sorry

mtheorem xxreal_1_th_146:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <XXREAL-0R3 p & s <=XXREAL-0R1 q implies (].XXREAL-1K3 r,s .])/\\XBOOLE-0K3 ([.XXREAL-1K1 p,q .]) =MEMBEREDR8 [.XXREAL-1K1 p,s .]"
sorry

mtheorem xxreal_1_th_147:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r >=XXREAL-0R2 p & s >=XXREAL-0R2 q implies (].XXREAL-1K3 r,s .])/\\XBOOLE-0K3 ([.XXREAL-1K1 p,q .]) =MEMBEREDR8 ].XXREAL-1K3 r,q .]"
sorry

mtheorem xxreal_1_th_148:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <XXREAL-0R3 p & s <=XXREAL-0R1 q implies (].XXREAL-1K4 r,s .[)/\\XBOOLE-0K3 ([.XXREAL-1K1 p,q .]) =MEMBEREDR8 [.XXREAL-1K2 p,s .["
sorry

mtheorem xxreal_1_th_149:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r >=XXREAL-0R2 p & s >XXREAL-0R4 q implies (].XXREAL-1K4 r,s .[)/\\XBOOLE-0K3 ([.XXREAL-1K1 p,q .]) =MEMBEREDR8 ].XXREAL-1K3 r,q .]"
sorry

mtheorem xxreal_1_th_150:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <=XXREAL-0R1 p & s <=XXREAL-0R1 q implies ([.XXREAL-1K2 r,s .[)/\\XBOOLE-0K3 ([.XXREAL-1K2 p,q .[) =MEMBEREDR8 [.XXREAL-1K2 p,s .["
sorry

mtheorem xxreal_1_th_151:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r >=XXREAL-0R2 p & s >=XXREAL-0R2 q implies ([.XXREAL-1K2 r,s .[)/\\XBOOLE-0K3 ([.XXREAL-1K2 p,q .[) =MEMBEREDR8 [.XXREAL-1K2 r,q .["
sorry

mtheorem xxreal_1_th_152:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <XXREAL-0R3 p & s <XXREAL-0R3 q implies (].XXREAL-1K3 r,s .])/\\XBOOLE-0K3 ([.XXREAL-1K2 p,q .[) =MEMBEREDR8 [.XXREAL-1K1 p,s .]"
sorry

mtheorem xxreal_1_th_153:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r >=XXREAL-0R2 p & s >=XXREAL-0R2 q implies (].XXREAL-1K3 r,s .])/\\XBOOLE-0K3 ([.XXREAL-1K2 p,q .[) =MEMBEREDR8 ].XXREAL-1K4 r,q .["
sorry

mtheorem xxreal_1_th_154:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <XXREAL-0R3 p & s <=XXREAL-0R1 q implies (].XXREAL-1K4 r,s .[)/\\XBOOLE-0K3 ([.XXREAL-1K2 p,q .[) =MEMBEREDR8 [.XXREAL-1K2 p,s .["
sorry

mtheorem xxreal_1_th_155:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r >=XXREAL-0R2 p & s >=XXREAL-0R2 q implies (].XXREAL-1K4 r,s .[)/\\XBOOLE-0K3 ([.XXREAL-1K2 p,q .[) =MEMBEREDR8 ].XXREAL-1K4 r,q .["
sorry

mtheorem xxreal_1_th_156:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <=XXREAL-0R1 p & s <=XXREAL-0R1 q implies (].XXREAL-1K3 r,s .])/\\XBOOLE-0K3 (].XXREAL-1K3 p,q .]) =MEMBEREDR8 ].XXREAL-1K3 p,s .]"
sorry

mtheorem xxreal_1_th_157:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r >=XXREAL-0R2 p & s >=XXREAL-0R2 q implies (].XXREAL-1K3 r,s .])/\\XBOOLE-0K3 (].XXREAL-1K3 p,q .]) =MEMBEREDR8 ].XXREAL-1K3 r,q .]"
sorry

mtheorem xxreal_1_th_158:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <=XXREAL-0R1 p & s <=XXREAL-0R1 q implies (].XXREAL-1K4 r,s .[)/\\XBOOLE-0K3 (].XXREAL-1K3 p,q .]) =MEMBEREDR8 ].XXREAL-1K4 p,s .["
sorry

mtheorem xxreal_1_th_159:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r >=XXREAL-0R2 p & s >XXREAL-0R4 q implies (].XXREAL-1K4 r,s .[)/\\XBOOLE-0K3 (].XXREAL-1K3 p,q .]) =MEMBEREDR8 ].XXREAL-1K3 r,q .]"
sorry

mtheorem xxreal_1_th_160:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <=XXREAL-0R1 p & s <=XXREAL-0R1 q implies (].XXREAL-1K4 r,s .[)/\\XBOOLE-0K3 (].XXREAL-1K4 p,q .[) =MEMBEREDR8 ].XXREAL-1K4 p,s .["
sorry

mtheorem xxreal_1_th_161:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds [.XXREAL-1K2 r,s .[ \\/XBOOLE-0K2 [.XXREAL-1K2 p,q .[ c=MEMBEREDR2 [.XXREAL-1K2 minXXREAL-0K4(r,p),maxXXREAL-0K5(s,q) .["
sorry

mtheorem xxreal_1_th_162:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds [.XXREAL-1K2 r,s .[ meetsXBOOLE-0R5 [.XXREAL-1K2 p,q .[ implies [.XXREAL-1K2 r,s .[ \\/XBOOLE-0K2 [.XXREAL-1K2 p,q .[ =MEMBEREDR8 [.XXREAL-1K2 minXXREAL-0K4(r,p),maxXXREAL-0K5(s,q) .["
sorry

mtheorem xxreal_1_th_163:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds ].XXREAL-1K3 r,s .] \\/XBOOLE-0K2 ].XXREAL-1K3 p,q .] c=MEMBEREDR2 ].XXREAL-1K3 minXXREAL-0K4(r,p),maxXXREAL-0K5(s,q) .]"
sorry

mtheorem xxreal_1_th_164:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds ].XXREAL-1K3 r,s .] meetsXBOOLE-0R5 ].XXREAL-1K3 p,q .] implies ].XXREAL-1K3 r,s .] \\/XBOOLE-0K2 ].XXREAL-1K3 p,q .] =MEMBEREDR8 ].XXREAL-1K3 minXXREAL-0K4(r,p),maxXXREAL-0K5(s,q) .]"
sorry

mtheorem xxreal_1_th_165:
" for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds  for t be ExtRealXXREAL-0M1 holds r <=XXREAL-0R1 s & s <=XXREAL-0R1 t implies [.XXREAL-1K1 r,s .] \\/XBOOLE-0K2 [.XXREAL-1K1 s,t .] =MEMBEREDR8 [.XXREAL-1K1 r,t .]"
sorry

mtheorem xxreal_1_th_166:
" for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds  for t be ExtRealXXREAL-0M1 holds r <=XXREAL-0R1 s & s <=XXREAL-0R1 t implies [.XXREAL-1K2 r,s .[ \\/XBOOLE-0K2 [.XXREAL-1K1 s,t .] =MEMBEREDR8 [.XXREAL-1K1 r,t .]"
sorry

mtheorem xxreal_1_th_167:
" for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds  for t be ExtRealXXREAL-0M1 holds r <=XXREAL-0R1 s & s <=XXREAL-0R1 t implies [.XXREAL-1K1 r,s .] \\/XBOOLE-0K2 ].XXREAL-1K3 s,t .] =MEMBEREDR8 [.XXREAL-1K1 r,t .]"
sorry

mtheorem xxreal_1_th_168:
" for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds  for t be ExtRealXXREAL-0M1 holds r <=XXREAL-0R1 s & s <=XXREAL-0R1 t implies [.XXREAL-1K2 r,s .[ \\/XBOOLE-0K2 [.XXREAL-1K2 s,t .[ =MEMBEREDR8 [.XXREAL-1K2 r,t .["
sorry

mtheorem xxreal_1_th_169:
" for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds  for t be ExtRealXXREAL-0M1 holds r <=XXREAL-0R1 s & s <XXREAL-0R3 t implies [.XXREAL-1K1 r,s .] \\/XBOOLE-0K2 ].XXREAL-1K4 s,t .[ =MEMBEREDR8 [.XXREAL-1K2 r,t .["
sorry

mtheorem xxreal_1_th_170:
" for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds  for t be ExtRealXXREAL-0M1 holds r <=XXREAL-0R1 s & s <=XXREAL-0R1 t implies ].XXREAL-1K3 r,s .] \\/XBOOLE-0K2 ].XXREAL-1K3 s,t .] =MEMBEREDR8 ].XXREAL-1K3 r,t .]"
sorry

mtheorem xxreal_1_th_171:
" for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds  for t be ExtRealXXREAL-0M1 holds r <=XXREAL-0R1 s & s <XXREAL-0R3 t implies ].XXREAL-1K3 r,s .] \\/XBOOLE-0K2 ].XXREAL-1K4 s,t .[ =MEMBEREDR8 ].XXREAL-1K4 r,t .["
sorry

mtheorem xxreal_1_th_172:
" for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds  for t be ExtRealXXREAL-0M1 holds r <XXREAL-0R3 s & s <XXREAL-0R3 t implies ].XXREAL-1K3 r,s .] \\/XBOOLE-0K2 [.XXREAL-1K2 s,t .[ =MEMBEREDR8 ].XXREAL-1K4 r,t .["
sorry

mtheorem xxreal_1_th_173:
" for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds  for t be ExtRealXXREAL-0M1 holds r <XXREAL-0R3 s & s <XXREAL-0R3 t implies ].XXREAL-1K4 r,s .[ \\/XBOOLE-0K2 [.XXREAL-1K2 s,t .[ =MEMBEREDR8 ].XXREAL-1K4 r,t .["
sorry

mtheorem xxreal_1_th_174:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds (p <=XXREAL-0R1 s & r <=XXREAL-0R1 q) & s <=XXREAL-0R1 r implies [.XXREAL-1K1 p,r .] \\/XBOOLE-0K2 [.XXREAL-1K1 s,q .] =MEMBEREDR8 [.XXREAL-1K1 p,q .]"
sorry

mtheorem xxreal_1_th_175:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds (p <=XXREAL-0R1 s & r <=XXREAL-0R1 q) & s <XXREAL-0R3 r implies [.XXREAL-1K2 p,r .[ \\/XBOOLE-0K2 ].XXREAL-1K3 s,q .] =MEMBEREDR8 [.XXREAL-1K1 p,q .]"
sorry

mtheorem xxreal_1_th_176:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds (p <=XXREAL-0R1 s & s <=XXREAL-0R1 r) & r <XXREAL-0R3 q implies [.XXREAL-1K1 p,r .] \\/XBOOLE-0K2 [.XXREAL-1K2 s,q .[ =MEMBEREDR8 [.XXREAL-1K2 p,q .["
sorry

mtheorem xxreal_1_th_177:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds (p <XXREAL-0R3 s & r <=XXREAL-0R1 q) & s <=XXREAL-0R1 r implies ].XXREAL-1K3 p,r .] \\/XBOOLE-0K2 [.XXREAL-1K1 s,q .] =MEMBEREDR8 ].XXREAL-1K3 p,q .]"
sorry

mtheorem xxreal_1_th_178:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds (p <XXREAL-0R3 s & r <XXREAL-0R3 q) & s <=XXREAL-0R1 r implies ].XXREAL-1K3 p,r .] \\/XBOOLE-0K2 [.XXREAL-1K2 s,q .[ =MEMBEREDR8 ].XXREAL-1K4 p,q .["
sorry

mtheorem xxreal_1_th_179:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds ((p <=XXREAL-0R1 r & p <=XXREAL-0R1 s) & r <=XXREAL-0R1 q) & s <=XXREAL-0R1 q implies ([.XXREAL-1K2 p,r .[ \\/XBOOLE-0K2 [.XXREAL-1K1 r,s .])\\/XBOOLE-0K2 ].XXREAL-1K3 s,q .] =MEMBEREDR8 [.XXREAL-1K1 p,q .]"
sorry

mtheorem xxreal_1_th_180:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds ((p <XXREAL-0R3 r & p <XXREAL-0R3 s) & r <XXREAL-0R3 q) & s <XXREAL-0R3 q implies (].XXREAL-1K3 p,r .] \\/XBOOLE-0K2 ].XXREAL-1K4 r,s .[)\\/XBOOLE-0K2 [.XXREAL-1K2 s,q .[ =MEMBEREDR8 ].XXREAL-1K4 p,q .["
sorry

mtheorem xxreal_1_th_181:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds (p <=XXREAL-0R1 r & r <=XXREAL-0R1 s) & s <=XXREAL-0R1 q implies ([.XXREAL-1K1 p,r .] \\/XBOOLE-0K2 ].XXREAL-1K4 r,s .[)\\/XBOOLE-0K2 [.XXREAL-1K1 s,q .] =MEMBEREDR8 [.XXREAL-1K1 p,q .]"
sorry

mtheorem xxreal_1_th_182:
" for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds  for t be ExtRealXXREAL-0M1 holds r <=XXREAL-0R1 s implies [.XXREAL-1K1 r,t .] \\SUBSET-1K6 [.XXREAL-1K1 r,s .] =MEMBEREDR8 ].XXREAL-1K3 s,t .]"
sorry

mtheorem xxreal_1_th_183:
" for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds  for t be ExtRealXXREAL-0M1 holds r <=XXREAL-0R1 s implies [.XXREAL-1K2 r,t .[ \\SUBSET-1K6 [.XXREAL-1K1 r,s .] =MEMBEREDR8 ].XXREAL-1K4 s,t .["
sorry

mtheorem xxreal_1_th_184:
" for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds  for t be ExtRealXXREAL-0M1 holds r <XXREAL-0R3 s implies [.XXREAL-1K1 r,t .] \\SUBSET-1K6 [.XXREAL-1K2 r,s .[ =MEMBEREDR8 [.XXREAL-1K1 s,t .]"
sorry

mtheorem xxreal_1_th_185:
" for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds  for t be ExtRealXXREAL-0M1 holds r <XXREAL-0R3 s implies [.XXREAL-1K2 r,t .[ \\SUBSET-1K6 [.XXREAL-1K2 r,s .[ =MEMBEREDR8 [.XXREAL-1K2 s,t .["
sorry

mtheorem xxreal_1_th_186:
" for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds  for t be ExtRealXXREAL-0M1 holds r <=XXREAL-0R1 s implies [.XXREAL-1K1 r,t .] \\SUBSET-1K6 [.XXREAL-1K1 r,s .] =MEMBEREDR8 ].XXREAL-1K3 s,t .]"
sorry

mtheorem xxreal_1_th_187:
" for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds  for t be ExtRealXXREAL-0M1 holds r <XXREAL-0R3 s implies ].XXREAL-1K4 r,t .[ \\SUBSET-1K6 ].XXREAL-1K3 r,s .] =MEMBEREDR8 ].XXREAL-1K4 s,t .["
sorry

mtheorem xxreal_1_th_188:
" for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds  for t be ExtRealXXREAL-0M1 holds r <XXREAL-0R3 s implies ].XXREAL-1K3 r,t .] \\SUBSET-1K6 ].XXREAL-1K4 r,s .[ =MEMBEREDR8 [.XXREAL-1K1 s,t .]"
sorry

mtheorem xxreal_1_th_189:
" for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds  for t be ExtRealXXREAL-0M1 holds r <XXREAL-0R3 s implies ].XXREAL-1K4 r,t .[ \\SUBSET-1K6 ].XXREAL-1K4 r,s .[ =MEMBEREDR8 [.XXREAL-1K2 s,t .["
sorry

mtheorem xxreal_1_th_190:
" for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds  for t be ExtRealXXREAL-0M1 holds s <=XXREAL-0R1 t implies [.XXREAL-1K1 r,t .] \\SUBSET-1K6 [.XXREAL-1K1 s,t .] =MEMBEREDR8 [.XXREAL-1K2 r,s .["
sorry

mtheorem xxreal_1_th_191:
" for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds  for t be ExtRealXXREAL-0M1 holds s <=XXREAL-0R1 t implies ].XXREAL-1K3 r,t .] \\SUBSET-1K6 [.XXREAL-1K1 s,t .] =MEMBEREDR8 ].XXREAL-1K4 r,s .["
sorry

mtheorem xxreal_1_th_192:
" for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds  for t be ExtRealXXREAL-0M1 holds s <XXREAL-0R3 t implies [.XXREAL-1K1 r,t .] \\SUBSET-1K6 ].XXREAL-1K3 s,t .] =MEMBEREDR8 [.XXREAL-1K1 r,s .]"
sorry

mtheorem xxreal_1_th_193:
" for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds  for t be ExtRealXXREAL-0M1 holds s <XXREAL-0R3 t implies ].XXREAL-1K3 r,t .] \\SUBSET-1K6 ].XXREAL-1K3 s,t .] =MEMBEREDR8 ].XXREAL-1K3 r,s .]"
sorry

mtheorem xxreal_1_th_194:
" for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds  for t be ExtRealXXREAL-0M1 holds s <XXREAL-0R3 t implies [.XXREAL-1K2 r,t .[ \\SUBSET-1K6 [.XXREAL-1K2 s,t .[ =MEMBEREDR8 [.XXREAL-1K2 r,s .["
sorry

mtheorem xxreal_1_th_195:
" for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds  for t be ExtRealXXREAL-0M1 holds s <XXREAL-0R3 t implies ].XXREAL-1K4 r,t .[ \\SUBSET-1K6 [.XXREAL-1K2 s,t .[ =MEMBEREDR8 ].XXREAL-1K4 r,s .["
sorry

mtheorem xxreal_1_th_196:
" for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds  for t be ExtRealXXREAL-0M1 holds s <XXREAL-0R3 t implies [.XXREAL-1K2 r,t .[ \\SUBSET-1K6 ].XXREAL-1K4 s,t .[ =MEMBEREDR8 [.XXREAL-1K1 r,s .]"
sorry

mtheorem xxreal_1_th_197:
" for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds  for t be ExtRealXXREAL-0M1 holds s <XXREAL-0R3 t implies ].XXREAL-1K4 r,t .[ \\SUBSET-1K6 ].XXREAL-1K4 s,t .[ =MEMBEREDR8 ].XXREAL-1K3 r,s .]"
sorry

mtheorem xxreal_1_th_198:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds [.XXREAL-1K2 p,q .[ meetsXBOOLE-0R5 [.XXREAL-1K2 r,s .[ implies [.XXREAL-1K2 p,q .[ \\SUBSET-1K6 [.XXREAL-1K2 r,s .[ =MEMBEREDR8 [.XXREAL-1K2 p,r .[ \\/XBOOLE-0K2 [.XXREAL-1K2 s,q .["
sorry

mtheorem xxreal_1_th_199:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds ].XXREAL-1K3 p,q .] meetsXBOOLE-0R5 ].XXREAL-1K3 r,s .] implies ].XXREAL-1K3 p,q .] \\SUBSET-1K6 ].XXREAL-1K3 r,s .] =MEMBEREDR8 ].XXREAL-1K3 p,r .] \\/XBOOLE-0K2 ].XXREAL-1K3 s,q .]"
sorry

mtheorem xxreal_1_th_200:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds p <=XXREAL-0R1 r & s <=XXREAL-0R1 q implies [.XXREAL-1K1 p,q .] \\SUBSET-1K6 ([.XXREAL-1K1 p,r .] \\/XBOOLE-0K2 [.XXREAL-1K1 s,q .]) =MEMBEREDR8 ].XXREAL-1K4 r,s .["
sorry

mtheorem xxreal_1_th_201:
" for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds  for t be ExtRealXXREAL-0M1 holds r <=XXREAL-0R1 s & s <=XXREAL-0R1 t implies [.XXREAL-1K1 r,t .] \\SUBSET-1K6 {TARSKIK1 s} =MEMBEREDR8 [.XXREAL-1K2 r,s .[ \\/XBOOLE-0K2 ].XXREAL-1K3 s,t .]"
sorry

mtheorem xxreal_1_th_202:
" for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds  for t be ExtRealXXREAL-0M1 holds r <=XXREAL-0R1 s & s <XXREAL-0R3 t implies [.XXREAL-1K2 r,t .[ \\SUBSET-1K6 {TARSKIK1 s} =MEMBEREDR8 [.XXREAL-1K2 r,s .[ \\/XBOOLE-0K2 ].XXREAL-1K4 s,t .["
sorry

mtheorem xxreal_1_th_203:
" for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds  for t be ExtRealXXREAL-0M1 holds r <XXREAL-0R3 s & s <=XXREAL-0R1 t implies ].XXREAL-1K3 r,t .] \\SUBSET-1K6 {TARSKIK1 s} =MEMBEREDR8 ].XXREAL-1K4 r,s .[ \\/XBOOLE-0K2 ].XXREAL-1K3 s,t .]"
sorry

mtheorem xxreal_1_th_204:
" for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds  for t be ExtRealXXREAL-0M1 holds r <XXREAL-0R3 s & s <XXREAL-0R3 t implies ].XXREAL-1K4 r,t .[ \\SUBSET-1K6 {TARSKIK1 s} =MEMBEREDR8 ].XXREAL-1K4 r,s .[ \\/XBOOLE-0K2 ].XXREAL-1K4 s,t .["
sorry

mtheorem xxreal_1_th_205:
" for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds  for t be ExtRealXXREAL-0M1 holds  not s inHIDDENR3 ].XXREAL-1K4 r,s .[ \\/XBOOLE-0K2 ].XXREAL-1K4 s,t .["
sorry

mtheorem xxreal_1_th_206:
" for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds  for t be ExtRealXXREAL-0M1 holds  not s inHIDDENR3 [.XXREAL-1K2 r,s .[ \\/XBOOLE-0K2 ].XXREAL-1K4 s,t .["
sorry

mtheorem xxreal_1_th_207:
" for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds  for t be ExtRealXXREAL-0M1 holds  not s inHIDDENR3 ].XXREAL-1K4 r,s .[ \\/XBOOLE-0K2 ].XXREAL-1K3 s,t .]"
sorry

mtheorem xxreal_1_th_208:
" for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds  for t be ExtRealXXREAL-0M1 holds  not s inHIDDENR3 [.XXREAL-1K2 r,s .[ \\/XBOOLE-0K2 ].XXREAL-1K3 s,t .]"
sorry

(*begin*)
mtheorem xxreal_1_th_209:
"[.XXREAL-1K1 -inftyXXREAL-0K2,+inftyXXREAL-0K1 .] =MEMBEREDR8 ExtREALXXREAL-0K3"
sorry

mtheorem xxreal_1_th_210:
" for p be ExtRealXXREAL-0M1 holds ].XXREAL-1K4 p,-inftyXXREAL-0K2 .[ =MEMBEREDR8 {}XBOOLE-0K1"
sorry

mtheorem xxreal_1_th_211:
" for p be ExtRealXXREAL-0M1 holds [.XXREAL-1K2 p,-inftyXXREAL-0K2 .[ =MEMBEREDR8 {}XBOOLE-0K1"
sorry

mtheorem xxreal_1_th_212:
" for p be ExtRealXXREAL-0M1 holds ].XXREAL-1K3 p,-inftyXXREAL-0K2 .] =MEMBEREDR8 {}XBOOLE-0K1"
sorry

mtheorem xxreal_1_th_213:
" for p be ExtRealXXREAL-0M1 holds p <>HIDDENR2 -inftyXXREAL-0K2 implies [.XXREAL-1K1 p,-inftyXXREAL-0K2 .] =MEMBEREDR8 {}XBOOLE-0K1"
sorry

mtheorem xxreal_1_th_214:
" for p be ExtRealXXREAL-0M1 holds ].XXREAL-1K4 +inftyXXREAL-0K1,p .[ =MEMBEREDR8 {}XBOOLE-0K1"
sorry

mtheorem xxreal_1_th_215:
" for p be ExtRealXXREAL-0M1 holds [.XXREAL-1K2 +inftyXXREAL-0K1,p .[ =MEMBEREDR8 {}XBOOLE-0K1"
sorry

mtheorem xxreal_1_th_216:
" for p be ExtRealXXREAL-0M1 holds ].XXREAL-1K3 +inftyXXREAL-0K1,p .] =MEMBEREDR8 {}XBOOLE-0K1"
sorry

mtheorem xxreal_1_th_217:
" for p be ExtRealXXREAL-0M1 holds p <>HIDDENR2 +inftyXXREAL-0K1 implies [.XXREAL-1K1 +inftyXXREAL-0K1,p .] =MEMBEREDR8 {}XBOOLE-0K1"
sorry

mtheorem xxreal_1_th_218:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds p >XXREAL-0R4 q implies p inHIDDENR3 ].XXREAL-1K3 q,+inftyXXREAL-0K1 .]"
  using xxreal_0_th_3 xxreal_1_th_2 sorry

mtheorem xxreal_1_th_219:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds q <=XXREAL-0R1 p implies p inHIDDENR3 [.XXREAL-1K1 q,+inftyXXREAL-0K1 .]"
sorry

mtheorem xxreal_1_th_220:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds p <=XXREAL-0R1 q implies p inHIDDENR3 [.XXREAL-1K1 -inftyXXREAL-0K2,q .]"
sorry

mtheorem xxreal_1_th_221:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds p <XXREAL-0R3 q implies p inHIDDENR3 [.XXREAL-1K2 -inftyXXREAL-0K2,q .["
  using xxreal_0_th_5 xxreal_1_th_3 sorry

(*begin*)
mtheorem xxreal_1_th_222:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds p <=XXREAL-0R1 q implies [.XXREAL-1K1 p,q .] =MEMBEREDR8 [.XXREAL-1K1 p,q .] \\/XBOOLE-0K2 [.XXREAL-1K1 q,p .]"
sorry

mtheorem xxreal_1_th_223:
" for p be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds  for t be ExtRealXXREAL-0M1 holds r <=XXREAL-0R1 s & s <=XXREAL-0R1 t implies  not r inHIDDENR3 ].XXREAL-1K4 s,t .[ \\/XBOOLE-0K2 ].XXREAL-1K4 t,p .["
sorry

mtheorem xxreal_1_th_224:
"REALNUMBERSK2 =MEMBEREDR8 ].XXREAL-1K4 -inftyXXREAL-0K2,+inftyXXREAL-0K1 .["
sorry

mtheorem xxreal_1_th_225:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds ].XXREAL-1K4 p,q .[ c=MEMBEREDR2 REALNUMBERSK2"
sorry

mtheorem xxreal_1_th_226:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds p inHIDDENR3 REALNUMBERSK2 implies [.XXREAL-1K2 p,q .[ c=MEMBEREDR2 REALNUMBERSK2"
sorry

mtheorem xxreal_1_th_227:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds q inHIDDENR3 REALNUMBERSK2 implies ].XXREAL-1K3 p,q .] c=MEMBEREDR2 REALNUMBERSK2"
sorry

mtheorem xxreal_1_th_228:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds p inHIDDENR3 REALNUMBERSK2 & q inHIDDENR3 REALNUMBERSK2 implies [.XXREAL-1K1 p,q .] c=MEMBEREDR2 REALNUMBERSK2"
sorry

mtheorem xxreal_1_cl_9:
  mlet "p be ExtRealXXREAL-0M1", "q be ExtRealXXREAL-0M1"
"cluster ].XXREAL-1K4 p,q .[ as-term-is real-memberedMEMBEREDV3"
proof
(*coherence*)
  show "].XXREAL-1K4 p,q .[ be real-memberedMEMBEREDV3"
    using xxreal_1_th_225 membered_th_21 sorry
qed "sorry"

mtheorem xxreal_1_cl_10:
  mlet "p be RealXREAL-0M1", "q be ExtRealXXREAL-0M1"
"cluster [.XXREAL-1K2 p,q .[ as-term-is real-memberedMEMBEREDV3"
proof
(*coherence*)
  show "[.XXREAL-1K2 p,q .[ be real-memberedMEMBEREDV3"
sorry
qed "sorry"

mtheorem xxreal_1_cl_11:
  mlet "q be RealXREAL-0M1", "p be ExtRealXXREAL-0M1"
"cluster ].XXREAL-1K3 p,q .] as-term-is real-memberedMEMBEREDV3"
proof
(*coherence*)
  show "].XXREAL-1K3 p,q .] be real-memberedMEMBEREDV3"
sorry
qed "sorry"

mtheorem xxreal_1_cl_12:
  mlet "p be RealXREAL-0M1", "q be RealXREAL-0M1"
"cluster [.XXREAL-1K1 p,q .] as-term-is real-memberedMEMBEREDV3"
proof
(*coherence*)
  show "[.XXREAL-1K1 p,q .] be real-memberedMEMBEREDV3"
sorry
qed "sorry"

mtheorem xxreal_1_th_229:
" for s be ExtRealXXREAL-0M1 holds ].XXREAL-1K4 -inftyXXREAL-0K2,s .[ =XBOOLE-0R4 {g where g be RealXREAL-0M1 : g <XXREAL-0R3 s }"
sorry

mtheorem xxreal_1_th_230:
" for s be ExtRealXXREAL-0M1 holds ].XXREAL-1K4 s,+inftyXXREAL-0K1 .[ =XBOOLE-0R4 {g where g be RealXREAL-0M1 : s <XXREAL-0R3 g }"
sorry

mtheorem xxreal_1_th_231:
" for s be RealXREAL-0M1 holds ].XXREAL-1K3 -inftyXXREAL-0K2,s .] =XBOOLE-0R4 {g where g be RealXREAL-0M1 : g <=XXREAL-0R1 s }"
sorry

mtheorem xxreal_1_th_232:
" for s be RealXREAL-0M1 holds [.XXREAL-1K2 s,+inftyXXREAL-0K1 .[ =XBOOLE-0R4 {g where g be RealXREAL-0M1 : s <=XXREAL-0R1 g }"
sorry

mtheorem xxreal_1_th_233:
" for u be ExtRealXXREAL-0M1 holds  for x be RealXREAL-0M1 holds x inHIDDENR3 ].XXREAL-1K4 -inftyXXREAL-0K2,u .[ iff x <XXREAL-0R3 u"
sorry

mtheorem xxreal_1_th_234:
" for u be ExtRealXXREAL-0M1 holds  for x be RealXREAL-0M1 holds x inHIDDENR3 ].XXREAL-1K3 -inftyXXREAL-0K2,u .] iff x <=XXREAL-0R1 u"
sorry

mtheorem xxreal_1_th_235:
" for u be ExtRealXXREAL-0M1 holds  for x be RealXREAL-0M1 holds x inHIDDENR3 ].XXREAL-1K4 u,+inftyXXREAL-0K1 .[ iff u <XXREAL-0R3 x"
sorry

mtheorem xxreal_1_th_236:
" for u be ExtRealXXREAL-0M1 holds  for x be RealXREAL-0M1 holds x inHIDDENR3 [.XXREAL-1K2 u,+inftyXXREAL-0K1 .[ iff u <=XXREAL-0R1 x"
sorry

mtheorem xxreal_1_th_237:
" for p be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds p <=XXREAL-0R1 r implies [.XXREAL-1K1 r,s .] c=MEMBEREDR2 [.XXREAL-1K1 p,+inftyXXREAL-0K1 .]"
sorry

mtheorem xxreal_1_th_238:
" for p be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds p <=XXREAL-0R1 r implies [.XXREAL-1K2 r,s .[ c=MEMBEREDR2 [.XXREAL-1K1 p,+inftyXXREAL-0K1 .]"
sorry

mtheorem xxreal_1_th_239:
" for p be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds p <=XXREAL-0R1 r implies ].XXREAL-1K3 r,s .] c=MEMBEREDR2 [.XXREAL-1K1 p,+inftyXXREAL-0K1 .]"
sorry

mtheorem xxreal_1_th_240:
" for p be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds p <=XXREAL-0R1 r implies ].XXREAL-1K4 r,s .[ c=MEMBEREDR3 [.XXREAL-1K1 p,+inftyXXREAL-0K1 .]"
sorry

mtheorem xxreal_1_th_241:
" for p be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds p <=XXREAL-0R1 r implies [.XXREAL-1K2 r,s .[ c=MEMBEREDR2 [.XXREAL-1K2 p,+inftyXXREAL-0K1 .["
sorry

mtheorem xxreal_1_th_242:
" for p be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds p <XXREAL-0R3 r implies [.XXREAL-1K1 r,s .] c=MEMBEREDR2 ].XXREAL-1K3 p,+inftyXXREAL-0K1 .]"
  using xxreal_1_th_39 xxreal_0_th_3 sorry

mtheorem xxreal_1_th_243:
" for p be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds p <XXREAL-0R3 r implies [.XXREAL-1K2 r,s .[ c=MEMBEREDR2 ].XXREAL-1K3 p,+inftyXXREAL-0K1 .]"
  using xxreal_1_th_40 xxreal_0_th_3 sorry

mtheorem xxreal_1_th_244:
" for p be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds p <=XXREAL-0R1 r implies ].XXREAL-1K4 r,s .[ c=MEMBEREDR3 ].XXREAL-1K3 p,+inftyXXREAL-0K1 .]"
sorry

mtheorem xxreal_1_th_245:
" for p be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds p <=XXREAL-0R1 r implies ].XXREAL-1K3 r,s .] c=MEMBEREDR2 ].XXREAL-1K3 p,+inftyXXREAL-0K1 .]"
sorry

mtheorem xxreal_1_th_246:
" for p be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds p <=XXREAL-0R1 r implies ].XXREAL-1K4 r,s .[ c=MEMBEREDR3 [.XXREAL-1K2 p,+inftyXXREAL-0K1 .["
sorry

mtheorem xxreal_1_th_247:
" for p be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds p <=XXREAL-0R1 r implies ].XXREAL-1K4 r,s .[ c=MEMBEREDR3 ].XXREAL-1K4 p,+inftyXXREAL-0K1 .["
sorry

mtheorem xxreal_1_th_248:
" for p be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds p <XXREAL-0R3 r implies [.XXREAL-1K2 r,s .[ c=MEMBEREDR2 ].XXREAL-1K4 p,+inftyXXREAL-0K1 .["
  using xxreal_1_th_48 xxreal_0_th_3 sorry

mtheorem xxreal_1_th_249:
" for p be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be RealXREAL-0M1 holds p <XXREAL-0R3 r implies [.XXREAL-1K1 r,s .] c=MEMBEREDR2 ].XXREAL-1K4 p,+inftyXXREAL-0K1 .["
sorry

mtheorem xxreal_1_th_250:
" for p be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be RealXREAL-0M1 holds p <=XXREAL-0R1 r implies ].XXREAL-1K3 r,s .] c=MEMBEREDR3 ].XXREAL-1K4 p,+inftyXXREAL-0K1 .["
sorry

mtheorem xxreal_1_th_251:
" for p be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be RealXREAL-0M1 holds p <=XXREAL-0R1 r implies [.XXREAL-1K1 r,s .] c=MEMBEREDR2 [.XXREAL-1K2 p,+inftyXXREAL-0K1 .["
sorry

mtheorem xxreal_1_th_252:
" for p be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be RealXREAL-0M1 holds p <=XXREAL-0R1 r implies ].XXREAL-1K3 r,s .] c=MEMBEREDR3 [.XXREAL-1K2 p,+inftyXXREAL-0K1 .["
sorry

mtheorem xxreal_1_th_253:
" for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds s <=XXREAL-0R1 q implies [.XXREAL-1K1 r,s .] c=MEMBEREDR2 [.XXREAL-1K1 -inftyXXREAL-0K2,q .]"
sorry

mtheorem xxreal_1_th_254:
" for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds s <=XXREAL-0R1 q implies [.XXREAL-1K2 r,s .[ c=MEMBEREDR2 [.XXREAL-1K1 -inftyXXREAL-0K2,q .]"
sorry

mtheorem xxreal_1_th_255:
" for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds s <=XXREAL-0R1 q implies ].XXREAL-1K3 r,s .] c=MEMBEREDR2 [.XXREAL-1K1 -inftyXXREAL-0K2,q .]"
sorry

mtheorem xxreal_1_th_256:
" for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds s <=XXREAL-0R1 q implies ].XXREAL-1K4 r,s .[ c=MEMBEREDR3 [.XXREAL-1K1 -inftyXXREAL-0K2,q .]"
sorry

mtheorem xxreal_1_th_257:
" for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds s <=XXREAL-0R1 q implies [.XXREAL-1K2 r,s .[ c=MEMBEREDR2 [.XXREAL-1K2 -inftyXXREAL-0K2,q .["
sorry

mtheorem xxreal_1_th_258:
" for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds s <=XXREAL-0R1 q implies ].XXREAL-1K4 r,s .[ c=MEMBEREDR3 ].XXREAL-1K3 -inftyXXREAL-0K2,q .]"
sorry

mtheorem xxreal_1_th_259:
" for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds s <=XXREAL-0R1 q implies ].XXREAL-1K3 r,s .] c=MEMBEREDR2 ].XXREAL-1K3 -inftyXXREAL-0K2,q .]"
sorry

mtheorem xxreal_1_th_260:
" for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds s <XXREAL-0R3 q implies [.XXREAL-1K1 r,s .] c=MEMBEREDR2 [.XXREAL-1K2 -inftyXXREAL-0K2,q .["
  using xxreal_1_th_43 xxreal_0_th_5 sorry

mtheorem xxreal_1_th_261:
" for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds s <XXREAL-0R3 q implies ].XXREAL-1K3 r,s .] c=MEMBEREDR2 [.XXREAL-1K2 -inftyXXREAL-0K2,q .["
  using xxreal_1_th_44 xxreal_0_th_5 sorry

mtheorem xxreal_1_th_262:
" for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds s <=XXREAL-0R1 q implies ].XXREAL-1K4 r,s .[ c=MEMBEREDR3 [.XXREAL-1K2 -inftyXXREAL-0K2,q .["
sorry

mtheorem xxreal_1_th_263:
" for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds s <=XXREAL-0R1 q implies ].XXREAL-1K4 r,s .[ c=MEMBEREDR3 ].XXREAL-1K4 -inftyXXREAL-0K2,q .["
sorry

mtheorem xxreal_1_th_264:
" for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds s <XXREAL-0R3 q implies ].XXREAL-1K3 r,s .] c=MEMBEREDR2 ].XXREAL-1K4 -inftyXXREAL-0K2,q .["
  using xxreal_1_th_49 xxreal_0_th_5 sorry

mtheorem xxreal_1_th_265:
" for q be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds  for r be RealXREAL-0M1 holds s <=XXREAL-0R1 q implies [.XXREAL-1K1 r,s .] c=MEMBEREDR2 ].XXREAL-1K3 -inftyXXREAL-0K2,q .]"
sorry

mtheorem xxreal_1_th_266:
" for q be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds  for r be RealXREAL-0M1 holds s <=XXREAL-0R1 q implies [.XXREAL-1K2 r,s .[ c=MEMBEREDR3 ].XXREAL-1K3 -inftyXXREAL-0K2,q .]"
sorry

mtheorem xxreal_1_th_267:
" for q be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds  for r be RealXREAL-0M1 holds s <XXREAL-0R3 q implies [.XXREAL-1K1 r,s .] c=MEMBEREDR2 ].XXREAL-1K4 -inftyXXREAL-0K2,q .["
sorry

mtheorem xxreal_1_th_268:
" for q be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds  for r be RealXREAL-0M1 holds s <=XXREAL-0R1 q implies [.XXREAL-1K2 r,s .[ c=MEMBEREDR3 ].XXREAL-1K4 -inftyXXREAL-0K2,q .["
sorry

mtheorem xxreal_1_th_269:
" for a be ExtRealXXREAL-0M1 holds  for b be ExtRealXXREAL-0M1 holds (].XXREAL-1K4 -inftyXXREAL-0K2,b .[)/\\XBOOLE-0K3 (].XXREAL-1K4 a,+inftyXXREAL-0K1 .[) =MEMBEREDR9 ].XXREAL-1K4 a,b .["
sorry

mtheorem xxreal_1_th_270:
" for p be ExtRealXXREAL-0M1 holds  for b be RealXREAL-0M1 holds (].XXREAL-1K3 -inftyXXREAL-0K2,b .])/\\XBOOLE-0K3 (].XXREAL-1K4 p,+inftyXXREAL-0K1 .[) =MEMBEREDR9 ].XXREAL-1K3 p,b .]"
sorry

mtheorem xxreal_1_th_271:
" for p be ExtRealXXREAL-0M1 holds  for a be RealXREAL-0M1 holds (].XXREAL-1K4 -inftyXXREAL-0K2,p .[)/\\XBOOLE-0K3 ([.XXREAL-1K2 a,+inftyXXREAL-0K1 .[) =MEMBEREDR9 [.XXREAL-1K2 a,p .["
sorry

mtheorem xxreal_1_th_272:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds (].XXREAL-1K3 -inftyXXREAL-0K2,a .])/\\XBOOLE-0K3 ([.XXREAL-1K2 b,+inftyXXREAL-0K1 .[) =MEMBEREDR9 [.XXREAL-1K1 b,a .]"
sorry

mtheorem xxreal_1_th_273:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds s <=XXREAL-0R1 p implies [.XXREAL-1K2 r,s .[ missesMEMBEREDR14 ].XXREAL-1K4 p,q .["
sorry

mtheorem xxreal_1_th_274:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds s <=XXREAL-0R1 p implies [.XXREAL-1K2 r,s .[ missesMEMBEREDR14 ].XXREAL-1K3 p,q .]"
sorry

mtheorem xxreal_1_th_275:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds s <=XXREAL-0R1 p implies ].XXREAL-1K4 r,s .[ missesMEMBEREDR15 ].XXREAL-1K4 p,q .["
sorry

mtheorem xxreal_1_th_276:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds s <=XXREAL-0R1 p implies ].XXREAL-1K4 r,s .[ missesMEMBEREDR14 ].XXREAL-1K3 p,q .]"
sorry

mtheorem xxreal_1_th_277:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds s <XXREAL-0R3 p implies [.XXREAL-1K1 r,s .] missesMEMBEREDR14 [.XXREAL-1K2 p,q .["
sorry

mtheorem xxreal_1_th_278:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds s <XXREAL-0R3 p implies [.XXREAL-1K1 r,s .] missesMEMBEREDR14 [.XXREAL-1K1 p,q .]"
sorry

mtheorem xxreal_1_th_279:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds s <XXREAL-0R3 p implies ].XXREAL-1K3 r,s .] missesMEMBEREDR14 [.XXREAL-1K2 p,q .["
sorry

mtheorem xxreal_1_th_280:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds s <XXREAL-0R3 p implies ].XXREAL-1K3 r,s .] missesMEMBEREDR14 [.XXREAL-1K1 p,q .]"
sorry

mtheorem xxreal_1_th_281:
" for s be ExtRealXXREAL-0M1 holds  for t be ExtRealXXREAL-0M1 holds [.XXREAL-1K1 -inftyXXREAL-0K2,t .] \\SUBSET-1K6 [.XXREAL-1K1 -inftyXXREAL-0K2,s .] =MEMBEREDR8 ].XXREAL-1K3 s,t .]"
  using xxreal_1_th_182 xxreal_0_th_5 sorry

mtheorem xxreal_1_th_282:
" for s be ExtRealXXREAL-0M1 holds  for t be ExtRealXXREAL-0M1 holds [.XXREAL-1K2 -inftyXXREAL-0K2,t .[ \\SUBSET-1K6 [.XXREAL-1K1 -inftyXXREAL-0K2,s .] =MEMBEREDR8 ].XXREAL-1K4 s,t .["
  using xxreal_1_th_183 xxreal_0_th_5 sorry

mtheorem xxreal_1_th_283:
" for s be ExtRealXXREAL-0M1 holds  for t be ExtRealXXREAL-0M1 holds [.XXREAL-1K1 -inftyXXREAL-0K2,t .] \\SUBSET-1K6 [.XXREAL-1K1 -inftyXXREAL-0K2,s .] =MEMBEREDR8 ].XXREAL-1K3 s,t .]"
  using xxreal_1_th_186 xxreal_0_th_5 sorry

mtheorem xxreal_1_th_284:
" for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds [.XXREAL-1K1 r,+inftyXXREAL-0K1 .] \\SUBSET-1K6 [.XXREAL-1K1 s,+inftyXXREAL-0K1 .] =MEMBEREDR8 [.XXREAL-1K2 r,s .["
  using xxreal_1_th_190 xxreal_0_th_3 sorry

mtheorem xxreal_1_th_285:
" for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds ].XXREAL-1K3 r,+inftyXXREAL-0K1 .] \\SUBSET-1K6 [.XXREAL-1K1 s,+inftyXXREAL-0K1 .] =MEMBEREDR8 ].XXREAL-1K4 r,s .["
  using xxreal_1_th_191 xxreal_0_th_3 sorry

mtheorem xxreal_1_th_286:
" for t be ExtRealXXREAL-0M1 holds  for s be RealXREAL-0M1 holds [.XXREAL-1K1 -inftyXXREAL-0K2,t .] \\SUBSET-1K6 [.XXREAL-1K2 -inftyXXREAL-0K2,s .[ =MEMBEREDR8 [.XXREAL-1K1 s,t .]"
sorry

mtheorem xxreal_1_th_287:
" for t be ExtRealXXREAL-0M1 holds  for s be RealXREAL-0M1 holds [.XXREAL-1K2 -inftyXXREAL-0K2,t .[ \\SUBSET-1K6 [.XXREAL-1K2 -inftyXXREAL-0K2,s .[ =MEMBEREDR8 [.XXREAL-1K2 s,t .["
sorry

mtheorem xxreal_1_th_288:
" for t be ExtRealXXREAL-0M1 holds  for s be RealXREAL-0M1 holds ].XXREAL-1K4 -inftyXXREAL-0K2,t .[ \\SUBSET-1K6 ].XXREAL-1K3 -inftyXXREAL-0K2,s .] =MEMBEREDR9 ].XXREAL-1K4 s,t .["
sorry

mtheorem xxreal_1_th_289:
" for t be ExtRealXXREAL-0M1 holds  for s be RealXREAL-0M1 holds ].XXREAL-1K3 -inftyXXREAL-0K2,t .] \\SUBSET-1K6 ].XXREAL-1K4 -inftyXXREAL-0K2,s .[ =MEMBEREDR8 [.XXREAL-1K1 s,t .]"
sorry

mtheorem xxreal_1_th_290:
" for t be ExtRealXXREAL-0M1 holds  for s be RealXREAL-0M1 holds ].XXREAL-1K4 -inftyXXREAL-0K2,t .[ \\SUBSET-1K6 ].XXREAL-1K4 -inftyXXREAL-0K2,s .[ =MEMBEREDR9 [.XXREAL-1K2 s,t .["
sorry

mtheorem xxreal_1_th_291:
" for r be ExtRealXXREAL-0M1 holds  for s be RealXREAL-0M1 holds [.XXREAL-1K1 r,+inftyXXREAL-0K1 .] \\SUBSET-1K6 ].XXREAL-1K3 s,+inftyXXREAL-0K1 .] =MEMBEREDR8 [.XXREAL-1K1 r,s .]"
sorry

mtheorem xxreal_1_th_292:
" for r be ExtRealXXREAL-0M1 holds  for s be RealXREAL-0M1 holds ].XXREAL-1K3 r,+inftyXXREAL-0K1 .] \\SUBSET-1K6 ].XXREAL-1K3 s,+inftyXXREAL-0K1 .] =MEMBEREDR8 ].XXREAL-1K3 r,s .]"
sorry

mtheorem xxreal_1_th_293:
" for r be ExtRealXXREAL-0M1 holds  for s be RealXREAL-0M1 holds [.XXREAL-1K2 r,+inftyXXREAL-0K1 .[ \\SUBSET-1K6 [.XXREAL-1K2 s,+inftyXXREAL-0K1 .[ =MEMBEREDR8 [.XXREAL-1K2 r,s .["
sorry

mtheorem xxreal_1_th_294:
" for r be ExtRealXXREAL-0M1 holds  for s be RealXREAL-0M1 holds ].XXREAL-1K4 r,+inftyXXREAL-0K1 .[ \\SUBSET-1K6 [.XXREAL-1K2 s,+inftyXXREAL-0K1 .[ =MEMBEREDR9 ].XXREAL-1K4 r,s .["
sorry

mtheorem xxreal_1_th_295:
" for r be ExtRealXXREAL-0M1 holds  for s be RealXREAL-0M1 holds [.XXREAL-1K2 r,+inftyXXREAL-0K1 .[ \\SUBSET-1K6 ].XXREAL-1K4 s,+inftyXXREAL-0K1 .[ =MEMBEREDR8 [.XXREAL-1K1 r,s .]"
sorry

mtheorem xxreal_1_th_296:
" for r be ExtRealXXREAL-0M1 holds  for s be RealXREAL-0M1 holds ].XXREAL-1K4 r,+inftyXXREAL-0K1 .[ \\SUBSET-1K6 ].XXREAL-1K4 s,+inftyXXREAL-0K1 .[ =MEMBEREDR9 ].XXREAL-1K3 r,s .]"
sorry

mtheorem xxreal_1_th_297:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <XXREAL-0R3 s & p <XXREAL-0R3 q implies ].XXREAL-1K4 r,q .[ \\SUBSET-1K6 ].XXREAL-1K4 p,s .[ =MEMBEREDR8 ].XXREAL-1K3 r,p .] \\/XBOOLE-0K2 [.XXREAL-1K2 s,q .["
sorry

mtheorem xxreal_1_th_298:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <=XXREAL-0R1 s & p <XXREAL-0R3 q implies [.XXREAL-1K2 r,q .[ \\SUBSET-1K6 ].XXREAL-1K4 p,s .[ =MEMBEREDR8 [.XXREAL-1K1 r,p .] \\/XBOOLE-0K2 [.XXREAL-1K2 s,q .["
sorry

mtheorem xxreal_1_th_299:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <XXREAL-0R3 s & p <=XXREAL-0R1 q implies ].XXREAL-1K3 r,q .] \\SUBSET-1K6 ].XXREAL-1K4 p,s .[ =MEMBEREDR8 ].XXREAL-1K3 r,p .] \\/XBOOLE-0K2 [.XXREAL-1K1 s,q .]"
sorry

mtheorem xxreal_1_th_300:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <=XXREAL-0R1 s & p <=XXREAL-0R1 q implies [.XXREAL-1K1 r,q .] \\SUBSET-1K6 ].XXREAL-1K4 p,s .[ =MEMBEREDR8 [.XXREAL-1K1 r,p .] \\/XBOOLE-0K2 [.XXREAL-1K1 s,q .]"
sorry

mtheorem xxreal_1_th_301:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <XXREAL-0R3 s & p <=XXREAL-0R1 q implies ].XXREAL-1K4 r,q .[ \\SUBSET-1K6 [.XXREAL-1K2 p,s .[ =MEMBEREDR8 ].XXREAL-1K4 r,p .[ \\/XBOOLE-0K2 [.XXREAL-1K2 s,q .["
sorry

mtheorem xxreal_1_th_302:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <=XXREAL-0R1 s & p <=XXREAL-0R1 q implies [.XXREAL-1K2 r,q .[ \\SUBSET-1K6 [.XXREAL-1K2 p,s .[ =MEMBEREDR8 [.XXREAL-1K2 r,p .[ \\/XBOOLE-0K2 [.XXREAL-1K2 s,q .["
sorry

mtheorem xxreal_1_th_303:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <XXREAL-0R3 s & p <=XXREAL-0R1 q implies ].XXREAL-1K3 r,q .] \\SUBSET-1K6 [.XXREAL-1K2 p,s .[ =MEMBEREDR8 ].XXREAL-1K4 r,p .[ \\/XBOOLE-0K2 [.XXREAL-1K1 s,q .]"
sorry

mtheorem xxreal_1_th_304:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <=XXREAL-0R1 s & p <=XXREAL-0R1 q implies [.XXREAL-1K1 r,q .] \\SUBSET-1K6 [.XXREAL-1K2 p,s .[ =MEMBEREDR8 [.XXREAL-1K2 r,p .[ \\/XBOOLE-0K2 [.XXREAL-1K1 s,q .]"
sorry

mtheorem xxreal_1_th_305:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <XXREAL-0R3 s & p <XXREAL-0R3 q implies ].XXREAL-1K4 r,q .[ \\SUBSET-1K6 ].XXREAL-1K3 p,s .] =MEMBEREDR8 ].XXREAL-1K3 r,p .] \\/XBOOLE-0K2 ].XXREAL-1K4 s,q .["
sorry

mtheorem xxreal_1_th_306:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <=XXREAL-0R1 s & p <XXREAL-0R3 q implies [.XXREAL-1K2 r,q .[ \\SUBSET-1K6 ].XXREAL-1K3 p,s .] =MEMBEREDR8 [.XXREAL-1K1 r,p .] \\/XBOOLE-0K2 ].XXREAL-1K4 s,q .["
sorry

mtheorem xxreal_1_th_307:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <XXREAL-0R3 s & p <=XXREAL-0R1 q implies ].XXREAL-1K3 r,q .] \\SUBSET-1K6 ].XXREAL-1K3 p,s .] =MEMBEREDR8 ].XXREAL-1K3 r,p .] \\/XBOOLE-0K2 ].XXREAL-1K3 s,q .]"
sorry

mtheorem xxreal_1_th_308:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <=XXREAL-0R1 s & p <=XXREAL-0R1 q implies [.XXREAL-1K1 r,q .] \\SUBSET-1K6 ].XXREAL-1K3 p,s .] =MEMBEREDR8 [.XXREAL-1K1 r,p .] \\/XBOOLE-0K2 ].XXREAL-1K3 s,q .]"
sorry

mtheorem xxreal_1_th_309:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <=XXREAL-0R1 s & p <=XXREAL-0R1 q implies ].XXREAL-1K4 r,q .[ \\SUBSET-1K6 [.XXREAL-1K1 p,s .] =MEMBEREDR9 ].XXREAL-1K4 r,p .[ \\/XBOOLE-0K2 ].XXREAL-1K4 s,q .["
sorry

mtheorem xxreal_1_th_310:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <=XXREAL-0R1 s & p <=XXREAL-0R1 q implies [.XXREAL-1K2 r,q .[ \\SUBSET-1K6 [.XXREAL-1K1 p,s .] =MEMBEREDR8 [.XXREAL-1K2 r,p .[ \\/XBOOLE-0K2 ].XXREAL-1K4 s,q .["
sorry

mtheorem xxreal_1_th_311:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <XXREAL-0R3 s & p <=XXREAL-0R1 q implies ].XXREAL-1K3 r,q .] \\SUBSET-1K6 [.XXREAL-1K1 p,s .] =MEMBEREDR8 ].XXREAL-1K4 r,p .[ \\/XBOOLE-0K2 ].XXREAL-1K3 s,q .]"
sorry

mtheorem xxreal_1_th_312:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <=XXREAL-0R1 s & p <=XXREAL-0R1 q implies [.XXREAL-1K1 r,q .] \\SUBSET-1K6 [.XXREAL-1K1 p,s .] =MEMBEREDR8 [.XXREAL-1K2 r,p .[ \\/XBOOLE-0K2 ].XXREAL-1K3 s,q .]"
sorry

mtheorem xxreal_1_th_313:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds r <=XXREAL-0R1 p & p <=XXREAL-0R1 q implies ].XXREAL-1K4 r,q .[ \\SUBSET-1K6 {TARSKIK1 p} =MEMBEREDR9 ].XXREAL-1K4 r,p .[ \\/XBOOLE-0K2 ].XXREAL-1K4 p,q .["
sorry

mtheorem xxreal_1_th_314:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds r <=XXREAL-0R1 p & p <=XXREAL-0R1 q implies [.XXREAL-1K2 r,q .[ \\SUBSET-1K6 {TARSKIK1 p} =MEMBEREDR8 [.XXREAL-1K2 r,p .[ \\/XBOOLE-0K2 ].XXREAL-1K4 p,q .["
sorry

mtheorem xxreal_1_th_315:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds r <XXREAL-0R3 p & p <=XXREAL-0R1 q implies ].XXREAL-1K3 r,q .] \\SUBSET-1K6 {TARSKIK1 p} =MEMBEREDR8 ].XXREAL-1K4 r,p .[ \\/XBOOLE-0K2 ].XXREAL-1K3 p,q .]"
sorry

mtheorem xxreal_1_th_316:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds r <=XXREAL-0R1 p & p <=XXREAL-0R1 q implies [.XXREAL-1K1 r,q .] \\SUBSET-1K6 {TARSKIK1 p} =MEMBEREDR8 [.XXREAL-1K2 r,p .[ \\/XBOOLE-0K2 ].XXREAL-1K3 p,q .]"
sorry

mtheorem xxreal_1_th_317:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds r <XXREAL-0R3 q & p <=XXREAL-0R1 q implies ].XXREAL-1K3 r,q .] \\SUBSET-1K6 ].XXREAL-1K4 p,q .[ =MEMBEREDR8 ].XXREAL-1K3 r,p .] \\/XBOOLE-0K2 {TARSKIK1 q}"
sorry

mtheorem xxreal_1_th_318:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds r <=XXREAL-0R1 q & p <=XXREAL-0R1 q implies [.XXREAL-1K1 r,q .] \\SUBSET-1K6 ].XXREAL-1K4 p,q .[ =MEMBEREDR8 [.XXREAL-1K1 r,p .] \\/XBOOLE-0K2 {TARSKIK1 q}"
sorry

mtheorem xxreal_1_th_319:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds r <XXREAL-0R3 q & p <=XXREAL-0R1 q implies ].XXREAL-1K3 r,q .] \\SUBSET-1K6 [.XXREAL-1K2 p,q .[ =MEMBEREDR8 ].XXREAL-1K4 r,p .[ \\/XBOOLE-0K2 {TARSKIK1 q}"
sorry

mtheorem xxreal_1_th_320:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds r <=XXREAL-0R1 q & p <=XXREAL-0R1 q implies [.XXREAL-1K1 r,q .] \\SUBSET-1K6 [.XXREAL-1K2 p,q .[ =MEMBEREDR8 [.XXREAL-1K2 r,p .[ \\/XBOOLE-0K2 {TARSKIK1 q}"
sorry

mtheorem xxreal_1_th_321:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds p <=XXREAL-0R1 s & p <XXREAL-0R3 q implies [.XXREAL-1K2 p,q .[ \\SUBSET-1K6 ].XXREAL-1K4 p,s .[ =MEMBEREDR8 {TARSKIK1 p} \\/XBOOLE-0K2 [.XXREAL-1K2 s,q .["
sorry

mtheorem xxreal_1_th_322:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds p <=XXREAL-0R1 s & p <=XXREAL-0R1 q implies [.XXREAL-1K1 p,q .] \\SUBSET-1K6 ].XXREAL-1K4 p,s .[ =MEMBEREDR8 {TARSKIK1 p} \\/XBOOLE-0K2 [.XXREAL-1K1 s,q .]"
sorry

mtheorem xxreal_1_th_323:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds p <=XXREAL-0R1 s & p <XXREAL-0R3 q implies [.XXREAL-1K2 p,q .[ \\SUBSET-1K6 ].XXREAL-1K3 p,s .] =MEMBEREDR8 {TARSKIK1 p} \\/XBOOLE-0K2 ].XXREAL-1K4 s,q .["
sorry

mtheorem xxreal_1_th_324:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds p <=XXREAL-0R1 s & p <=XXREAL-0R1 q implies [.XXREAL-1K1 p,q .] \\SUBSET-1K6 ].XXREAL-1K3 p,s .] =MEMBEREDR8 {TARSKIK1 p} \\/XBOOLE-0K2 ].XXREAL-1K3 s,q .]"
sorry

mtheorem xxreal_1_th_325:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds p <XXREAL-0R3 q implies [.XXREAL-1K2 -inftyXXREAL-0K2,q .[ \\SUBSET-1K6 ].XXREAL-1K4 p,s .[ =MEMBEREDR8 [.XXREAL-1K1 -inftyXXREAL-0K2,p .] \\/XBOOLE-0K2 [.XXREAL-1K2 s,q .["
  using xxreal_1_th_298 xxreal_0_th_5 sorry

mtheorem xxreal_1_th_326:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds p <=XXREAL-0R1 q implies [.XXREAL-1K1 -inftyXXREAL-0K2,q .] \\SUBSET-1K6 ].XXREAL-1K4 p,s .[ =MEMBEREDR8 [.XXREAL-1K1 -inftyXXREAL-0K2,p .] \\/XBOOLE-0K2 [.XXREAL-1K1 s,q .]"
sorry

mtheorem xxreal_1_th_327:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds p <=XXREAL-0R1 q implies [.XXREAL-1K2 -inftyXXREAL-0K2,q .[ \\SUBSET-1K6 [.XXREAL-1K2 p,s .[ =MEMBEREDR8 [.XXREAL-1K2 -inftyXXREAL-0K2,p .[ \\/XBOOLE-0K2 [.XXREAL-1K2 s,q .["
sorry

mtheorem xxreal_1_th_328:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds p <=XXREAL-0R1 q implies [.XXREAL-1K1 -inftyXXREAL-0K2,q .] \\SUBSET-1K6 [.XXREAL-1K2 p,s .[ =MEMBEREDR8 [.XXREAL-1K2 -inftyXXREAL-0K2,p .[ \\/XBOOLE-0K2 [.XXREAL-1K1 s,q .]"
sorry

mtheorem xxreal_1_th_329:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds p <XXREAL-0R3 q implies [.XXREAL-1K2 -inftyXXREAL-0K2,q .[ \\SUBSET-1K6 ].XXREAL-1K3 p,s .] =MEMBEREDR8 [.XXREAL-1K1 -inftyXXREAL-0K2,p .] \\/XBOOLE-0K2 ].XXREAL-1K4 s,q .["
  using xxreal_1_th_306 xxreal_0_th_5 sorry

mtheorem xxreal_1_th_330:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds p <=XXREAL-0R1 q implies [.XXREAL-1K1 -inftyXXREAL-0K2,q .] \\SUBSET-1K6 ].XXREAL-1K3 p,s .] =MEMBEREDR8 [.XXREAL-1K1 -inftyXXREAL-0K2,p .] \\/XBOOLE-0K2 ].XXREAL-1K3 s,q .]"
sorry

mtheorem xxreal_1_th_331:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds p <=XXREAL-0R1 q implies [.XXREAL-1K2 -inftyXXREAL-0K2,q .[ \\SUBSET-1K6 [.XXREAL-1K1 p,s .] =MEMBEREDR8 [.XXREAL-1K2 -inftyXXREAL-0K2,p .[ \\/XBOOLE-0K2 ].XXREAL-1K4 s,q .["
sorry

mtheorem xxreal_1_th_332:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds p <=XXREAL-0R1 q implies [.XXREAL-1K1 -inftyXXREAL-0K2,q .] \\SUBSET-1K6 [.XXREAL-1K1 p,s .] =MEMBEREDR8 [.XXREAL-1K2 -inftyXXREAL-0K2,p .[ \\/XBOOLE-0K2 ].XXREAL-1K3 s,q .]"
sorry

mtheorem xxreal_1_th_333:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for s be RealXREAL-0M1 holds p <XXREAL-0R3 q implies ].XXREAL-1K4 -inftyXXREAL-0K2,q .[ \\SUBSET-1K6 ].XXREAL-1K4 p,s .[ =MEMBEREDR8 ].XXREAL-1K3 -inftyXXREAL-0K2,p .] \\/XBOOLE-0K2 [.XXREAL-1K2 s,q .["
sorry

mtheorem xxreal_1_th_334:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for s be RealXREAL-0M1 holds p <=XXREAL-0R1 q implies ].XXREAL-1K3 -inftyXXREAL-0K2,q .] \\SUBSET-1K6 ].XXREAL-1K4 p,s .[ =MEMBEREDR8 ].XXREAL-1K3 -inftyXXREAL-0K2,p .] \\/XBOOLE-0K2 [.XXREAL-1K1 s,q .]"
sorry

mtheorem xxreal_1_th_335:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for s be RealXREAL-0M1 holds p <=XXREAL-0R1 q implies ].XXREAL-1K4 -inftyXXREAL-0K2,q .[ \\SUBSET-1K6 [.XXREAL-1K2 p,s .[ =MEMBEREDR9 ].XXREAL-1K4 -inftyXXREAL-0K2,p .[ \\/XBOOLE-0K2 [.XXREAL-1K2 s,q .["
sorry

mtheorem xxreal_1_th_336:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for s be RealXREAL-0M1 holds p <=XXREAL-0R1 q implies ].XXREAL-1K3 -inftyXXREAL-0K2,q .] \\SUBSET-1K6 [.XXREAL-1K2 p,s .[ =MEMBEREDR8 ].XXREAL-1K4 -inftyXXREAL-0K2,p .[ \\/XBOOLE-0K2 [.XXREAL-1K1 s,q .]"
sorry

mtheorem xxreal_1_th_337:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for s be RealXREAL-0M1 holds p <XXREAL-0R3 q implies ].XXREAL-1K4 -inftyXXREAL-0K2,q .[ \\SUBSET-1K6 ].XXREAL-1K3 p,s .] =MEMBEREDR8 ].XXREAL-1K3 -inftyXXREAL-0K2,p .] \\/XBOOLE-0K2 ].XXREAL-1K4 s,q .["
sorry

mtheorem xxreal_1_th_338:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for s be RealXREAL-0M1 holds p <=XXREAL-0R1 q implies ].XXREAL-1K3 -inftyXXREAL-0K2,q .] \\SUBSET-1K6 ].XXREAL-1K3 p,s .] =MEMBEREDR8 ].XXREAL-1K3 -inftyXXREAL-0K2,p .] \\/XBOOLE-0K2 ].XXREAL-1K3 s,q .]"
sorry

mtheorem xxreal_1_th_339:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds p <=XXREAL-0R1 q implies ].XXREAL-1K4 -inftyXXREAL-0K2,q .[ \\SUBSET-1K6 [.XXREAL-1K1 p,s .] =MEMBEREDR9 ].XXREAL-1K4 -inftyXXREAL-0K2,p .[ \\/XBOOLE-0K2 ].XXREAL-1K4 s,q .["
sorry

mtheorem xxreal_1_th_340:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds  for s be RealXREAL-0M1 holds p <=XXREAL-0R1 q implies ].XXREAL-1K3 -inftyXXREAL-0K2,q .] \\SUBSET-1K6 [.XXREAL-1K1 p,s .] =MEMBEREDR8 ].XXREAL-1K4 -inftyXXREAL-0K2,p .[ \\/XBOOLE-0K2 ].XXREAL-1K3 s,q .]"
sorry

mtheorem xxreal_1_th_341:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds p <=XXREAL-0R1 q implies [.XXREAL-1K2 -inftyXXREAL-0K2,q .[ \\SUBSET-1K6 {TARSKIK1 p} =MEMBEREDR8 [.XXREAL-1K2 -inftyXXREAL-0K2,p .[ \\/XBOOLE-0K2 ].XXREAL-1K4 p,q .["
sorry

mtheorem xxreal_1_th_342:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds p <=XXREAL-0R1 q implies [.XXREAL-1K1 -inftyXXREAL-0K2,q .] \\SUBSET-1K6 {TARSKIK1 p} =MEMBEREDR8 [.XXREAL-1K2 -inftyXXREAL-0K2,p .[ \\/XBOOLE-0K2 ].XXREAL-1K3 p,q .]"
sorry

mtheorem xxreal_1_th_343:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds p <=XXREAL-0R1 q implies [.XXREAL-1K1 -inftyXXREAL-0K2,q .] \\SUBSET-1K6 ].XXREAL-1K4 p,q .[ =MEMBEREDR8 [.XXREAL-1K1 -inftyXXREAL-0K2,p .] \\/XBOOLE-0K2 {TARSKIK1 q}"
sorry

mtheorem xxreal_1_th_344:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds p <=XXREAL-0R1 q implies [.XXREAL-1K1 -inftyXXREAL-0K2,q .] \\SUBSET-1K6 [.XXREAL-1K2 p,q .[ =MEMBEREDR8 [.XXREAL-1K2 -inftyXXREAL-0K2,p .[ \\/XBOOLE-0K2 {TARSKIK1 q}"
sorry

mtheorem xxreal_1_th_345:
" for q be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds [.XXREAL-1K1 -inftyXXREAL-0K2,q .] \\SUBSET-1K6 ].XXREAL-1K4 -inftyXXREAL-0K2,s .[ =MEMBEREDR8 {TARSKIK1 -inftyXXREAL-0K2 } \\/XBOOLE-0K2 [.XXREAL-1K1 s,q .]"
sorry

mtheorem xxreal_1_th_346:
" for q be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds [.XXREAL-1K1 -inftyXXREAL-0K2,q .] \\SUBSET-1K6 ].XXREAL-1K3 -inftyXXREAL-0K2,s .] =MEMBEREDR8 {TARSKIK1 -inftyXXREAL-0K2 } \\/XBOOLE-0K2 ].XXREAL-1K3 s,q .]"
sorry

mtheorem xxreal_1_th_347:
" for s be ExtRealXXREAL-0M1 holds  for q be RealXREAL-0M1 holds [.XXREAL-1K2 -inftyXXREAL-0K2,q .[ \\SUBSET-1K6 ].XXREAL-1K4 -inftyXXREAL-0K2,s .[ =MEMBEREDR8 {TARSKIK1 -inftyXXREAL-0K2 } \\/XBOOLE-0K2 [.XXREAL-1K2 s,q .["
sorry

mtheorem xxreal_1_th_348:
" for s be ExtRealXXREAL-0M1 holds  for q be RealXREAL-0M1 holds [.XXREAL-1K2 -inftyXXREAL-0K2,q .[ \\SUBSET-1K6 ].XXREAL-1K3 -inftyXXREAL-0K2,s .] =MEMBEREDR8 {TARSKIK1 -inftyXXREAL-0K2 } \\/XBOOLE-0K2 ].XXREAL-1K4 s,q .["
sorry

mtheorem xxreal_1_th_349:
" for p be ExtRealXXREAL-0M1 holds  for q be ExtRealXXREAL-0M1 holds p <=XXREAL-0R1 q implies ].XXREAL-1K4 -inftyXXREAL-0K2,q .[ \\SUBSET-1K6 {TARSKIK1 p} =MEMBEREDR9 ].XXREAL-1K4 -inftyXXREAL-0K2,p .[ \\/XBOOLE-0K2 ].XXREAL-1K4 p,q .["
sorry

mtheorem xxreal_1_th_350:
" for q be ExtRealXXREAL-0M1 holds  for p be RealXREAL-0M1 holds p <=XXREAL-0R1 q implies ].XXREAL-1K3 -inftyXXREAL-0K2,q .] \\SUBSET-1K6 {TARSKIK1 p} =MEMBEREDR8 ].XXREAL-1K4 -inftyXXREAL-0K2,p .[ \\/XBOOLE-0K2 ].XXREAL-1K3 p,q .]"
sorry

mtheorem xxreal_1_th_351:
" for p be ExtRealXXREAL-0M1 holds  for q be RealXREAL-0M1 holds p <=XXREAL-0R1 q implies ].XXREAL-1K3 -inftyXXREAL-0K2,q .] \\SUBSET-1K6 ].XXREAL-1K4 p,q .[ =MEMBEREDR8 ].XXREAL-1K3 -inftyXXREAL-0K2,p .] \\/XBOOLE-0K2 {TARSKIK1 q}"
sorry

mtheorem xxreal_1_th_352:
" for p be ExtRealXXREAL-0M1 holds  for q be RealXREAL-0M1 holds p <=XXREAL-0R1 q implies ].XXREAL-1K3 -inftyXXREAL-0K2,q .] \\SUBSET-1K6 [.XXREAL-1K2 p,q .[ =MEMBEREDR9 ].XXREAL-1K4 -inftyXXREAL-0K2,p .[ \\/XBOOLE-0K2 {TARSKIK1 q}"
sorry

mtheorem xxreal_1_th_353:
" for p be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <XXREAL-0R3 s implies ].XXREAL-1K3 r,+inftyXXREAL-0K1 .] \\SUBSET-1K6 ].XXREAL-1K4 p,s .[ =MEMBEREDR8 ].XXREAL-1K3 r,p .] \\/XBOOLE-0K2 [.XXREAL-1K1 s,+inftyXXREAL-0K1 .]"
  using xxreal_1_th_299 xxreal_0_th_3 sorry

mtheorem xxreal_1_th_354:
" for p be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <=XXREAL-0R1 s implies [.XXREAL-1K1 r,+inftyXXREAL-0K1 .] \\SUBSET-1K6 ].XXREAL-1K4 p,s .[ =MEMBEREDR8 [.XXREAL-1K1 r,p .] \\/XBOOLE-0K2 [.XXREAL-1K1 s,+inftyXXREAL-0K1 .]"
sorry

mtheorem xxreal_1_th_355:
" for p be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <XXREAL-0R3 s implies ].XXREAL-1K4 r,+inftyXXREAL-0K1 .[ \\SUBSET-1K6 [.XXREAL-1K2 p,s .[ =MEMBEREDR8 ].XXREAL-1K4 r,p .[ \\/XBOOLE-0K2 [.XXREAL-1K2 s,+inftyXXREAL-0K1 .["
  using xxreal_1_th_301 xxreal_0_th_3 sorry

mtheorem xxreal_1_th_356:
" for p be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <=XXREAL-0R1 s implies [.XXREAL-1K2 r,+inftyXXREAL-0K1 .[ \\SUBSET-1K6 [.XXREAL-1K2 p,s .[ =MEMBEREDR8 [.XXREAL-1K2 r,p .[ \\/XBOOLE-0K2 [.XXREAL-1K2 s,+inftyXXREAL-0K1 .["
sorry

mtheorem xxreal_1_th_357:
" for p be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <XXREAL-0R3 s implies ].XXREAL-1K3 r,+inftyXXREAL-0K1 .] \\SUBSET-1K6 [.XXREAL-1K2 p,s .[ =MEMBEREDR8 ].XXREAL-1K4 r,p .[ \\/XBOOLE-0K2 [.XXREAL-1K1 s,+inftyXXREAL-0K1 .]"
  using xxreal_1_th_303 xxreal_0_th_3 sorry

mtheorem xxreal_1_th_358:
" for p be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <=XXREAL-0R1 s implies [.XXREAL-1K1 r,+inftyXXREAL-0K1 .] \\SUBSET-1K6 [.XXREAL-1K2 p,s .[ =MEMBEREDR8 [.XXREAL-1K2 r,p .[ \\/XBOOLE-0K2 [.XXREAL-1K1 s,+inftyXXREAL-0K1 .]"
sorry

mtheorem xxreal_1_th_359:
" for p be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <XXREAL-0R3 s implies ].XXREAL-1K3 r,+inftyXXREAL-0K1 .] \\SUBSET-1K6 ].XXREAL-1K3 p,s .] =MEMBEREDR8 ].XXREAL-1K3 r,p .] \\/XBOOLE-0K2 ].XXREAL-1K3 s,+inftyXXREAL-0K1 .]"
  using xxreal_1_th_307 xxreal_0_th_3 sorry

mtheorem xxreal_1_th_360:
" for p be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <=XXREAL-0R1 s implies [.XXREAL-1K1 r,+inftyXXREAL-0K1 .] \\SUBSET-1K6 ].XXREAL-1K3 p,s .] =MEMBEREDR8 [.XXREAL-1K1 r,p .] \\/XBOOLE-0K2 ].XXREAL-1K3 s,+inftyXXREAL-0K1 .]"
sorry

mtheorem xxreal_1_th_361:
" for p be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <=XXREAL-0R1 s implies ].XXREAL-1K4 r,+inftyXXREAL-0K1 .[ \\SUBSET-1K6 [.XXREAL-1K1 p,s .] =MEMBEREDR9 ].XXREAL-1K4 r,p .[ \\/XBOOLE-0K2 ].XXREAL-1K4 s,+inftyXXREAL-0K1 .["
sorry

mtheorem xxreal_1_th_362:
" for p be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <=XXREAL-0R1 s implies [.XXREAL-1K2 r,+inftyXXREAL-0K1 .[ \\SUBSET-1K6 [.XXREAL-1K1 p,s .] =MEMBEREDR8 [.XXREAL-1K2 r,p .[ \\/XBOOLE-0K2 ].XXREAL-1K4 s,+inftyXXREAL-0K1 .["
sorry

mtheorem xxreal_1_th_363:
" for p be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <XXREAL-0R3 s implies ].XXREAL-1K3 r,+inftyXXREAL-0K1 .] \\SUBSET-1K6 [.XXREAL-1K1 p,s .] =MEMBEREDR8 ].XXREAL-1K4 r,p .[ \\/XBOOLE-0K2 ].XXREAL-1K3 s,+inftyXXREAL-0K1 .]"
  using xxreal_1_th_311 xxreal_0_th_3 sorry

mtheorem xxreal_1_th_364:
" for p be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <=XXREAL-0R1 s implies [.XXREAL-1K1 r,+inftyXXREAL-0K1 .] \\SUBSET-1K6 [.XXREAL-1K1 p,s .] =MEMBEREDR8 [.XXREAL-1K2 r,p .[ \\/XBOOLE-0K2 ].XXREAL-1K3 s,+inftyXXREAL-0K1 .]"
sorry

mtheorem xxreal_1_th_365:
" for p be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds r <=XXREAL-0R1 p implies ].XXREAL-1K4 r,+inftyXXREAL-0K1 .[ \\SUBSET-1K6 {TARSKIK1 p} =MEMBEREDR9 ].XXREAL-1K4 r,p .[ \\/XBOOLE-0K2 ].XXREAL-1K4 p,+inftyXXREAL-0K1 .["
sorry

mtheorem xxreal_1_th_366:
" for p be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds r <=XXREAL-0R1 p implies [.XXREAL-1K2 r,+inftyXXREAL-0K1 .[ \\SUBSET-1K6 {TARSKIK1 p} =MEMBEREDR8 [.XXREAL-1K2 r,p .[ \\/XBOOLE-0K2 ].XXREAL-1K4 p,+inftyXXREAL-0K1 .["
sorry

mtheorem xxreal_1_th_367:
" for p be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds r <XXREAL-0R3 p implies ].XXREAL-1K3 r,+inftyXXREAL-0K1 .] \\SUBSET-1K6 {TARSKIK1 p} =MEMBEREDR8 ].XXREAL-1K4 r,p .[ \\/XBOOLE-0K2 ].XXREAL-1K3 p,+inftyXXREAL-0K1 .]"
  using xxreal_1_th_315 xxreal_0_th_3 sorry

mtheorem xxreal_1_th_368:
" for p be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds r <=XXREAL-0R1 p implies [.XXREAL-1K1 r,+inftyXXREAL-0K1 .] \\SUBSET-1K6 {TARSKIK1 p} =MEMBEREDR8 [.XXREAL-1K2 r,p .[ \\/XBOOLE-0K2 ].XXREAL-1K3 p,+inftyXXREAL-0K1 .]"
sorry

mtheorem xxreal_1_th_369:
" for p be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds [.XXREAL-1K1 r,+inftyXXREAL-0K1 .] \\SUBSET-1K6 ].XXREAL-1K4 p,+inftyXXREAL-0K1 .[ =MEMBEREDR8 [.XXREAL-1K1 r,p .] \\/XBOOLE-0K2 {TARSKIK1 +inftyXXREAL-0K1 }"
sorry

mtheorem xxreal_1_th_370:
" for p be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds [.XXREAL-1K1 r,+inftyXXREAL-0K1 .] \\SUBSET-1K6 [.XXREAL-1K2 p,+inftyXXREAL-0K1 .[ =MEMBEREDR8 [.XXREAL-1K2 r,p .[ \\/XBOOLE-0K2 {TARSKIK1 +inftyXXREAL-0K1 }"
sorry

mtheorem xxreal_1_th_371:
" for p be ExtRealXXREAL-0M1 holds  for r be RealXREAL-0M1 holds ].XXREAL-1K3 r,+inftyXXREAL-0K1 .] \\SUBSET-1K6 ].XXREAL-1K4 p,+inftyXXREAL-0K1 .[ =MEMBEREDR8 ].XXREAL-1K3 r,p .] \\/XBOOLE-0K2 {TARSKIK1 +inftyXXREAL-0K1 }"
sorry

mtheorem xxreal_1_th_372:
" for p be ExtRealXXREAL-0M1 holds  for r be RealXREAL-0M1 holds ].XXREAL-1K3 r,+inftyXXREAL-0K1 .] \\SUBSET-1K6 [.XXREAL-1K2 p,+inftyXXREAL-0K1 .[ =MEMBEREDR8 ].XXREAL-1K4 r,p .[ \\/XBOOLE-0K2 {TARSKIK1 +inftyXXREAL-0K1 }"
sorry

mtheorem xxreal_1_th_373:
" for p be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds p <=XXREAL-0R1 s implies [.XXREAL-1K1 p,+inftyXXREAL-0K1 .] \\SUBSET-1K6 ].XXREAL-1K4 p,s .[ =MEMBEREDR8 {TARSKIK1 p} \\/XBOOLE-0K2 [.XXREAL-1K1 s,+inftyXXREAL-0K1 .]"
sorry

mtheorem xxreal_1_th_374:
" for p be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds p <=XXREAL-0R1 s implies [.XXREAL-1K1 p,+inftyXXREAL-0K1 .] \\SUBSET-1K6 ].XXREAL-1K3 p,s .] =MEMBEREDR8 {TARSKIK1 p} \\/XBOOLE-0K2 ].XXREAL-1K3 s,+inftyXXREAL-0K1 .]"
sorry

mtheorem xxreal_1_th_375:
" for p be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds [.XXREAL-1K1 -inftyXXREAL-0K2,+inftyXXREAL-0K1 .] \\SUBSET-1K6 ].XXREAL-1K4 p,s .[ =MEMBEREDR8 [.XXREAL-1K1 -inftyXXREAL-0K2,p .] \\/XBOOLE-0K2 [.XXREAL-1K1 s,+inftyXXREAL-0K1 .]"
  using xxreal_1_th_326 xxreal_0_th_3 sorry

mtheorem xxreal_1_th_376:
" for p be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds [.XXREAL-1K2 -inftyXXREAL-0K2,+inftyXXREAL-0K1 .[ \\SUBSET-1K6 [.XXREAL-1K2 p,s .[ =MEMBEREDR8 [.XXREAL-1K2 -inftyXXREAL-0K2,p .[ \\/XBOOLE-0K2 [.XXREAL-1K2 s,+inftyXXREAL-0K1 .["
  using xxreal_1_th_327 xxreal_0_th_3 sorry

mtheorem xxreal_1_th_377:
" for p be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds [.XXREAL-1K1 -inftyXXREAL-0K2,+inftyXXREAL-0K1 .] \\SUBSET-1K6 [.XXREAL-1K2 p,s .[ =MEMBEREDR8 [.XXREAL-1K2 -inftyXXREAL-0K2,p .[ \\/XBOOLE-0K2 [.XXREAL-1K1 s,+inftyXXREAL-0K1 .]"
  using xxreal_1_th_328 xxreal_0_th_3 sorry

mtheorem xxreal_1_th_378:
" for p be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds [.XXREAL-1K1 -inftyXXREAL-0K2,+inftyXXREAL-0K1 .] \\SUBSET-1K6 ].XXREAL-1K3 p,s .] =MEMBEREDR8 [.XXREAL-1K1 -inftyXXREAL-0K2,p .] \\/XBOOLE-0K2 ].XXREAL-1K3 s,+inftyXXREAL-0K1 .]"
  using xxreal_1_th_330 xxreal_0_th_3 sorry

mtheorem xxreal_1_th_379:
" for p be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds [.XXREAL-1K2 -inftyXXREAL-0K2,+inftyXXREAL-0K1 .[ \\SUBSET-1K6 [.XXREAL-1K1 p,s .] =MEMBEREDR8 [.XXREAL-1K2 -inftyXXREAL-0K2,p .[ \\/XBOOLE-0K2 ].XXREAL-1K4 s,+inftyXXREAL-0K1 .["
  using xxreal_1_th_331 xxreal_0_th_3 sorry

mtheorem xxreal_1_th_380:
" for p be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds [.XXREAL-1K1 -inftyXXREAL-0K2,+inftyXXREAL-0K1 .] \\SUBSET-1K6 [.XXREAL-1K1 p,s .] =MEMBEREDR8 [.XXREAL-1K2 -inftyXXREAL-0K2,p .[ \\/XBOOLE-0K2 ].XXREAL-1K3 s,+inftyXXREAL-0K1 .]"
  using xxreal_1_th_332 xxreal_0_th_3 sorry

mtheorem xxreal_1_th_381:
" for p be ExtRealXXREAL-0M1 holds  for s be RealXREAL-0M1 holds ].XXREAL-1K3 -inftyXXREAL-0K2,+inftyXXREAL-0K1 .] \\SUBSET-1K6 ].XXREAL-1K4 p,s .[ =MEMBEREDR8 ].XXREAL-1K3 -inftyXXREAL-0K2,p .] \\/XBOOLE-0K2 [.XXREAL-1K1 s,+inftyXXREAL-0K1 .]"
  using xxreal_1_th_334 xxreal_0_th_3 sorry

mtheorem xxreal_1_th_382:
" for p be ExtRealXXREAL-0M1 holds  for s be RealXREAL-0M1 holds REALNUMBERSK2 \\SUBSET-1K6 [.XXREAL-1K2 p,s .[ =MEMBEREDR9 ].XXREAL-1K4 -inftyXXREAL-0K2,p .[ \\/XBOOLE-0K2 [.XXREAL-1K2 s,+inftyXXREAL-0K1 .["
  using xxreal_1_th_224 xxreal_1_th_335 xxreal_0_th_3 sorry

mtheorem xxreal_1_th_383:
" for p be ExtRealXXREAL-0M1 holds  for s be RealXREAL-0M1 holds ].XXREAL-1K3 -inftyXXREAL-0K2,+inftyXXREAL-0K1 .] \\SUBSET-1K6 [.XXREAL-1K2 p,s .[ =MEMBEREDR8 ].XXREAL-1K4 -inftyXXREAL-0K2,p .[ \\/XBOOLE-0K2 [.XXREAL-1K1 s,+inftyXXREAL-0K1 .]"
  using xxreal_1_th_336 xxreal_0_th_3 sorry

mtheorem xxreal_1_th_384:
" for p be ExtRealXXREAL-0M1 holds  for s be RealXREAL-0M1 holds ].XXREAL-1K3 -inftyXXREAL-0K2,+inftyXXREAL-0K1 .] \\SUBSET-1K6 ].XXREAL-1K3 p,s .] =MEMBEREDR8 ].XXREAL-1K3 -inftyXXREAL-0K2,p .] \\/XBOOLE-0K2 ].XXREAL-1K3 s,+inftyXXREAL-0K1 .]"
  using xxreal_1_th_338 xxreal_0_th_3 sorry

mtheorem xxreal_1_th_385:
" for p be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds REALNUMBERSK2 \\SUBSET-1K6 [.XXREAL-1K1 p,s .] =MEMBEREDR9 ].XXREAL-1K4 -inftyXXREAL-0K2,p .[ \\/XBOOLE-0K2 ].XXREAL-1K4 s,+inftyXXREAL-0K1 .["
  using xxreal_1_th_224 xxreal_1_th_339 xxreal_0_th_3 sorry

mtheorem xxreal_1_th_386:
" for p be ExtRealXXREAL-0M1 holds  for s be RealXREAL-0M1 holds ].XXREAL-1K3 -inftyXXREAL-0K2,+inftyXXREAL-0K1 .] \\SUBSET-1K6 [.XXREAL-1K1 p,s .] =MEMBEREDR8 ].XXREAL-1K4 -inftyXXREAL-0K2,p .[ \\/XBOOLE-0K2 ].XXREAL-1K3 s,+inftyXXREAL-0K1 .]"
  using xxreal_1_th_340 xxreal_0_th_3 sorry

mtheorem xxreal_1_th_387:
" for p be ExtRealXXREAL-0M1 holds [.XXREAL-1K2 -inftyXXREAL-0K2,+inftyXXREAL-0K1 .[ \\SUBSET-1K6 {TARSKIK1 p} =MEMBEREDR8 [.XXREAL-1K2 -inftyXXREAL-0K2,p .[ \\/XBOOLE-0K2 ].XXREAL-1K4 p,+inftyXXREAL-0K1 .["
  using xxreal_1_th_341 xxreal_0_th_3 sorry

mtheorem xxreal_1_th_388:
" for p be ExtRealXXREAL-0M1 holds [.XXREAL-1K1 -inftyXXREAL-0K2,+inftyXXREAL-0K1 .] \\SUBSET-1K6 {TARSKIK1 p} =MEMBEREDR8 [.XXREAL-1K2 -inftyXXREAL-0K2,p .[ \\/XBOOLE-0K2 ].XXREAL-1K3 p,+inftyXXREAL-0K1 .]"
  using xxreal_1_th_342 xxreal_0_th_3 sorry

mtheorem xxreal_1_th_389:
" for p be ExtRealXXREAL-0M1 holds REALNUMBERSK2 \\SUBSET-1K6 {TARSKIK1 p} =MEMBEREDR9 ].XXREAL-1K4 -inftyXXREAL-0K2,p .[ \\/XBOOLE-0K2 ].XXREAL-1K4 p,+inftyXXREAL-0K1 .["
  using xxreal_1_th_224 xxreal_1_th_349 xxreal_0_th_3 sorry

mtheorem xxreal_1_th_390:
" for p be RealXREAL-0M1 holds ].XXREAL-1K3 -inftyXXREAL-0K2,+inftyXXREAL-0K1 .] \\SUBSET-1K6 {TARSKIK1 p} =MEMBEREDR8 ].XXREAL-1K4 -inftyXXREAL-0K2,p .[ \\/XBOOLE-0K2 ].XXREAL-1K3 p,+inftyXXREAL-0K1 .]"
  using xxreal_1_th_350 xxreal_0_th_3 sorry

mtheorem xxreal_1_th_391:
" for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds  for p be RealXREAL-0M1 holds r <XXREAL-0R3 s implies ].XXREAL-1K4 r,+inftyXXREAL-0K1 .[ \\SUBSET-1K6 ].XXREAL-1K4 p,s .[ =MEMBEREDR8 ].XXREAL-1K3 r,p .] \\/XBOOLE-0K2 [.XXREAL-1K2 s,+inftyXXREAL-0K1 .["
sorry

mtheorem xxreal_1_th_392:
" for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds  for p be RealXREAL-0M1 holds r <=XXREAL-0R1 s implies [.XXREAL-1K2 r,+inftyXXREAL-0K1 .[ \\SUBSET-1K6 ].XXREAL-1K4 p,s .[ =MEMBEREDR8 [.XXREAL-1K1 r,p .] \\/XBOOLE-0K2 [.XXREAL-1K2 s,+inftyXXREAL-0K1 .["
sorry

mtheorem xxreal_1_th_393:
" for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds  for p be RealXREAL-0M1 holds r <XXREAL-0R3 s implies ].XXREAL-1K4 r,+inftyXXREAL-0K1 .[ \\SUBSET-1K6 ].XXREAL-1K3 p,s .] =MEMBEREDR9 ].XXREAL-1K3 r,p .] \\/XBOOLE-0K2 ].XXREAL-1K4 s,+inftyXXREAL-0K1 .["
sorry

mtheorem xxreal_1_th_394:
" for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds  for p be RealXREAL-0M1 holds r <=XXREAL-0R1 s implies [.XXREAL-1K2 r,+inftyXXREAL-0K1 .[ \\SUBSET-1K6 ].XXREAL-1K3 p,s .] =MEMBEREDR8 [.XXREAL-1K1 r,p .] \\/XBOOLE-0K2 ].XXREAL-1K4 s,+inftyXXREAL-0K1 .["
sorry

mtheorem xxreal_1_th_395:
" for s be ExtRealXXREAL-0M1 holds  for p be RealXREAL-0M1 holds p <=XXREAL-0R1 s implies [.XXREAL-1K2 p,+inftyXXREAL-0K1 .[ \\SUBSET-1K6 ].XXREAL-1K3 p,s .] =MEMBEREDR9 {TARSKIK1 p} \\/XBOOLE-0K2 ].XXREAL-1K4 s,+inftyXXREAL-0K1 .["
sorry

mtheorem xxreal_1_th_396:
" for s be ExtRealXXREAL-0M1 holds  for p be RealXREAL-0M1 holds [.XXREAL-1K2 -inftyXXREAL-0K2,+inftyXXREAL-0K1 .[ \\SUBSET-1K6 ].XXREAL-1K4 p,s .[ =MEMBEREDR8 [.XXREAL-1K1 -inftyXXREAL-0K2,p .] \\/XBOOLE-0K2 [.XXREAL-1K2 s,+inftyXXREAL-0K1 .["
sorry

mtheorem xxreal_1_th_397:
" for s be ExtRealXXREAL-0M1 holds  for p be RealXREAL-0M1 holds [.XXREAL-1K2 -inftyXXREAL-0K2,+inftyXXREAL-0K1 .[ \\SUBSET-1K6 ].XXREAL-1K3 p,s .] =MEMBEREDR8 [.XXREAL-1K1 -inftyXXREAL-0K2,p .] \\/XBOOLE-0K2 ].XXREAL-1K4 s,+inftyXXREAL-0K1 .["
sorry

mtheorem xxreal_1_th_398:
" for s be RealXREAL-0M1 holds  for p be RealXREAL-0M1 holds REALNUMBERSK2 \\SUBSET-1K6 ].XXREAL-1K4 p,s .[ =MEMBEREDR9 ].XXREAL-1K3 -inftyXXREAL-0K2,p .] \\/XBOOLE-0K2 [.XXREAL-1K2 s,+inftyXXREAL-0K1 .["
sorry

mtheorem xxreal_1_th_399:
" for s be RealXREAL-0M1 holds  for p be RealXREAL-0M1 holds REALNUMBERSK2 \\SUBSET-1K6 ].XXREAL-1K3 p,s .] =MEMBEREDR9 ].XXREAL-1K3 -inftyXXREAL-0K2,p .] \\/XBOOLE-0K2 ].XXREAL-1K4 s,+inftyXXREAL-0K1 .["
sorry

mtheorem xxreal_1_th_400:
" for s be ExtRealXXREAL-0M1 holds  for p be RealXREAL-0M1 holds p <=XXREAL-0R1 s implies [.XXREAL-1K2 p,+inftyXXREAL-0K1 .[ \\SUBSET-1K6 ].XXREAL-1K4 p,s .[ =MEMBEREDR8 {TARSKIK1 p} \\/XBOOLE-0K2 [.XXREAL-1K2 s,+inftyXXREAL-0K1 .["
sorry

mtheorem xxreal_1_th_401:
" for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <XXREAL-0R3 s implies [.XXREAL-1K1 r,s .] \\SUBSET-1K6 [.XXREAL-1K2 r,s .[ =MEMBEREDR8 {TARSKIK1 s}"
sorry

mtheorem xxreal_1_th_402:
" for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r <XXREAL-0R3 s implies ].XXREAL-1K3 r,s .] \\SUBSET-1K6 ].XXREAL-1K4 r,s .[ =MEMBEREDR8 {TARSKIK1 s}"
sorry

mtheorem xxreal_1_th_403:
" for r be ExtRealXXREAL-0M1 holds  for t be ExtRealXXREAL-0M1 holds r <XXREAL-0R3 t implies [.XXREAL-1K1 r,t .] \\SUBSET-1K6 ].XXREAL-1K3 r,t .] =MEMBEREDR8 {TARSKIK1 r}"
sorry

mtheorem xxreal_1_th_404:
" for r be ExtRealXXREAL-0M1 holds  for t be ExtRealXXREAL-0M1 holds r <XXREAL-0R3 t implies [.XXREAL-1K2 r,t .[ \\SUBSET-1K6 ].XXREAL-1K4 r,t .[ =MEMBEREDR8 {TARSKIK1 r}"
sorry

mtheorem xxreal_1_th_405:
" for s be RealXREAL-0M1 holds [.XXREAL-1K1 -inftyXXREAL-0K2,s .] \\SUBSET-1K6 [.XXREAL-1K2 -inftyXXREAL-0K2,s .[ =MEMBEREDR8 {TARSKIK1 s}"
sorry

mtheorem xxreal_1_th_406:
" for s be RealXREAL-0M1 holds ].XXREAL-1K3 -inftyXXREAL-0K2,s .] \\SUBSET-1K6 ].XXREAL-1K4 -inftyXXREAL-0K2,s .[ =MEMBEREDR9 {TARSKIK1 s}"
sorry

mtheorem xxreal_1_th_407:
" for s be RealXREAL-0M1 holds [.XXREAL-1K1 -inftyXXREAL-0K2,s .] \\SUBSET-1K6 ].XXREAL-1K3 -inftyXXREAL-0K2,s .] =MEMBEREDR8 {TARSKIK1 -inftyXXREAL-0K2 }"
sorry

mtheorem xxreal_1_th_408:
" for s be RealXREAL-0M1 holds [.XXREAL-1K2 -inftyXXREAL-0K2,s .[ \\SUBSET-1K6 ].XXREAL-1K4 -inftyXXREAL-0K2,s .[ =MEMBEREDR8 {TARSKIK1 -inftyXXREAL-0K2 }"
sorry

mtheorem xxreal_1_th_409:
" for s be RealXREAL-0M1 holds [.XXREAL-1K1 s,+inftyXXREAL-0K1 .] \\SUBSET-1K6 [.XXREAL-1K2 s,+inftyXXREAL-0K1 .[ =MEMBEREDR8 {TARSKIK1 +inftyXXREAL-0K1 }"
sorry

mtheorem xxreal_1_th_410:
" for s be RealXREAL-0M1 holds ].XXREAL-1K3 s,+inftyXXREAL-0K1 .] \\SUBSET-1K6 ].XXREAL-1K4 s,+inftyXXREAL-0K1 .[ =MEMBEREDR8 {TARSKIK1 +inftyXXREAL-0K1 }"
sorry

mtheorem xxreal_1_th_411:
" for s be RealXREAL-0M1 holds [.XXREAL-1K1 s,+inftyXXREAL-0K1 .] \\SUBSET-1K6 ].XXREAL-1K3 s,+inftyXXREAL-0K1 .] =MEMBEREDR8 {TARSKIK1 s}"
sorry

mtheorem xxreal_1_th_412:
" for s be RealXREAL-0M1 holds [.XXREAL-1K2 s,+inftyXXREAL-0K1 .[ \\SUBSET-1K6 ].XXREAL-1K4 s,+inftyXXREAL-0K1 .[ =MEMBEREDR9 {TARSKIK1 s}"
sorry

mtheorem xxreal_1_th_413:
" for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds  for t be ExtRealXXREAL-0M1 holds r <=XXREAL-0R1 s & s <XXREAL-0R3 t implies [.XXREAL-1K1 r,s .] \\/XBOOLE-0K2 [.XXREAL-1K2 s,t .[ =MEMBEREDR8 [.XXREAL-1K2 r,t .["
sorry

mtheorem xxreal_1_th_414:
" for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds  for t be ExtRealXXREAL-0M1 holds r <XXREAL-0R3 s & s <=XXREAL-0R1 t implies ].XXREAL-1K3 r,s .] \\/XBOOLE-0K2 [.XXREAL-1K1 s,t .] =MEMBEREDR8 ].XXREAL-1K3 r,t .]"
sorry

mtheorem xxreal_1_th_415:
" for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds  for t be ExtRealXXREAL-0M1 holds r <XXREAL-0R3 s & s <XXREAL-0R3 t implies ].XXREAL-1K3 r,s .] \\/XBOOLE-0K2 [.XXREAL-1K2 s,t .[ =MEMBEREDR8 ].XXREAL-1K4 r,t .["
sorry

mtheorem xxreal_1_th_416:
" for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds  for t be ExtRealXXREAL-0M1 holds r <=XXREAL-0R1 s & s <XXREAL-0R3 t implies ([.XXREAL-1K1 r,s .])/\\XBOOLE-0K3 ([.XXREAL-1K2 s,t .[) =MEMBEREDR8 {TARSKIK1 s}"
sorry

mtheorem xxreal_1_th_417:
" for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds  for t be ExtRealXXREAL-0M1 holds r <XXREAL-0R3 s & s <=XXREAL-0R1 t implies (].XXREAL-1K3 r,s .])/\\XBOOLE-0K3 ([.XXREAL-1K1 s,t .]) =MEMBEREDR8 {TARSKIK1 s}"
sorry

mtheorem xxreal_1_th_418:
" for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds  for t be ExtRealXXREAL-0M1 holds r <=XXREAL-0R1 s & s <=XXREAL-0R1 t implies ([.XXREAL-1K1 r,s .])/\\XBOOLE-0K3 ([.XXREAL-1K1 s,t .]) =MEMBEREDR8 {TARSKIK1 s}"
sorry

mtheorem xxreal_1_th_419:
" for s be ExtRealXXREAL-0M1 holds [.XXREAL-1K1 -inftyXXREAL-0K2,s .] =MEMBEREDR8 ].XXREAL-1K4 -inftyXXREAL-0K2,s .[ \\/XBOOLE-0K2 {TARSKIK2 -inftyXXREAL-0K2,s }"
  using xxreal_1_th_128 xxreal_0_th_5 sorry

mtheorem xxreal_1_th_420:
" for s be ExtRealXXREAL-0M1 holds [.XXREAL-1K1 -inftyXXREAL-0K2,s .] =MEMBEREDR8 [.XXREAL-1K2 -inftyXXREAL-0K2,s .[ \\/XBOOLE-0K2 {TARSKIK1 s}"
  using xxreal_1_th_129 xxreal_0_th_5 sorry

mtheorem xxreal_1_th_421:
" for s be ExtRealXXREAL-0M1 holds [.XXREAL-1K1 -inftyXXREAL-0K2,s .] =MEMBEREDR8 {TARSKIK1 -inftyXXREAL-0K2 } \\/XBOOLE-0K2 ].XXREAL-1K3 -inftyXXREAL-0K2,s .]"
  using xxreal_1_th_130 xxreal_0_th_5 sorry

mtheorem xxreal_1_th_422:
" for s be RealXREAL-0M1 holds [.XXREAL-1K2 -inftyXXREAL-0K2,s .[ =MEMBEREDR8 {TARSKIK1 -inftyXXREAL-0K2 } \\/XBOOLE-0K2 ].XXREAL-1K4 -inftyXXREAL-0K2,s .["
sorry

mtheorem xxreal_1_th_423:
" for s be RealXREAL-0M1 holds ].XXREAL-1K3 -inftyXXREAL-0K2,s .] =MEMBEREDR9 ].XXREAL-1K4 -inftyXXREAL-0K2,s .[ \\/XBOOLE-0K2 {TARSKIK1 s}"
sorry

mtheorem xxreal_1_th_424:
" for r be ExtRealXXREAL-0M1 holds [.XXREAL-1K1 r,+inftyXXREAL-0K1 .] =MEMBEREDR8 ].XXREAL-1K4 r,+inftyXXREAL-0K1 .[ \\/XBOOLE-0K2 {TARSKIK2 r,+inftyXXREAL-0K1 }"
  using xxreal_1_th_128 xxreal_0_th_3 sorry

mtheorem xxreal_1_th_425:
" for r be ExtRealXXREAL-0M1 holds [.XXREAL-1K1 r,+inftyXXREAL-0K1 .] =MEMBEREDR8 [.XXREAL-1K2 r,+inftyXXREAL-0K1 .[ \\/XBOOLE-0K2 {TARSKIK1 +inftyXXREAL-0K1 }"
  using xxreal_1_th_129 xxreal_0_th_3 sorry

mtheorem xxreal_1_th_426:
" for r be ExtRealXXREAL-0M1 holds [.XXREAL-1K1 r,+inftyXXREAL-0K1 .] =MEMBEREDR8 {TARSKIK1 r} \\/XBOOLE-0K2 ].XXREAL-1K3 r,+inftyXXREAL-0K1 .]"
  using xxreal_1_th_130 xxreal_0_th_3 sorry

mtheorem xxreal_1_th_427:
" for r be RealXREAL-0M1 holds [.XXREAL-1K2 r,+inftyXXREAL-0K1 .[ =MEMBEREDR9 {TARSKIK1 r} \\/XBOOLE-0K2 ].XXREAL-1K4 r,+inftyXXREAL-0K1 .["
sorry

mtheorem xxreal_1_th_428:
" for r be RealXREAL-0M1 holds ].XXREAL-1K3 r,+inftyXXREAL-0K1 .] =MEMBEREDR8 ].XXREAL-1K4 r,+inftyXXREAL-0K1 .[ \\/XBOOLE-0K2 {TARSKIK1 +inftyXXREAL-0K1 }"
sorry

end
