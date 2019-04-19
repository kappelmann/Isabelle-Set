theory membered
  imports rat_1
begin
(*begin*)
reserve x for "objectHIDDENM1"
reserve X, F for "setHIDDENM2"
mdef membered_def_1 ("complex-memberedMEMBEREDV1" 70 ) where
"attr complex-memberedMEMBEREDV1 for setHIDDENM2 means
  (\<lambda>X.  for x be objectHIDDENM1 holds x inHIDDENR3 X implies x be complexXCMPLX-0V1)"..

mdef membered_def_2 ("ext-real-memberedMEMBEREDV2" 70 ) where
"attr ext-real-memberedMEMBEREDV2 for setHIDDENM2 means
  (\<lambda>X.  for x be objectHIDDENM1 holds x inHIDDENR3 X implies x be ext-realXXREAL-0V1)"..

mdef membered_def_3 ("real-memberedMEMBEREDV3" 70 ) where
"attr real-memberedMEMBEREDV3 for setHIDDENM2 means
  (\<lambda>X.  for x be objectHIDDENM1 holds x inHIDDENR3 X implies x be realXREAL-0V1)"..

mdef membered_def_4 ("rational-memberedMEMBEREDV4" 70 ) where
"attr rational-memberedMEMBEREDV4 for setHIDDENM2 means
  (\<lambda>X.  for x be objectHIDDENM1 holds x inHIDDENR3 X implies x be rationalRAT-1V1)"..

mdef membered_def_5 ("integer-memberedMEMBEREDV5" 70 ) where
"attr integer-memberedMEMBEREDV5 for setHIDDENM2 means
  (\<lambda>X.  for x be objectHIDDENM1 holds x inHIDDENR3 X implies x be integerINT-1V1)"..

mdef membered_def_6 ("natural-memberedMEMBEREDV6" 70 ) where
"attr natural-memberedMEMBEREDV6 for setHIDDENM2 means
  (\<lambda>X.  for x be objectHIDDENM1 holds x inHIDDENR3 X implies x be naturalORDINAL1V7)"..

mtheorem membered_cl_1:
"cluster natural-memberedMEMBEREDV6 also-is integer-memberedMEMBEREDV5 for setHIDDENM2"
proof
(*coherence*)
  show " for it be setHIDDENM2 holds it be natural-memberedMEMBEREDV6 implies it be integer-memberedMEMBEREDV5"
sorry
qed "sorry"

mtheorem membered_cl_2:
"cluster integer-memberedMEMBEREDV5 also-is rational-memberedMEMBEREDV4 for setHIDDENM2"
proof
(*coherence*)
  show " for it be setHIDDENM2 holds it be integer-memberedMEMBEREDV5 implies it be rational-memberedMEMBEREDV4"
sorry
qed "sorry"

mtheorem membered_cl_3:
"cluster rational-memberedMEMBEREDV4 also-is real-memberedMEMBEREDV3 for setHIDDENM2"
proof
(*coherence*)
  show " for it be setHIDDENM2 holds it be rational-memberedMEMBEREDV4 implies it be real-memberedMEMBEREDV3"
sorry
qed "sorry"

mtheorem membered_cl_4:
"cluster real-memberedMEMBEREDV3 also-is ext-real-memberedMEMBEREDV2 for setHIDDENM2"
proof
(*coherence*)
  show " for it be setHIDDENM2 holds it be real-memberedMEMBEREDV3 implies it be ext-real-memberedMEMBEREDV2"
sorry
qed "sorry"

mtheorem membered_cl_5:
"cluster real-memberedMEMBEREDV3 also-is complex-memberedMEMBEREDV1 for setHIDDENM2"
proof
(*coherence*)
  show " for it be setHIDDENM2 holds it be real-memberedMEMBEREDV3 implies it be complex-memberedMEMBEREDV1"
sorry
qed "sorry"

mtheorem membered_cl_6:
"cluster  non emptyXBOOLE-0V1\<bar>natural-memberedMEMBEREDV6 for setHIDDENM2"
proof
(*existence*)
  show " ex it be setHIDDENM2 st it be  non emptyXBOOLE-0V1\<bar>natural-memberedMEMBEREDV6"
sorry
qed "sorry"

mtheorem membered_cl_7:
"cluster COMPLEXNUMBERSK3 as-term-is complex-memberedMEMBEREDV1"
proof
(*coherence*)
  show "COMPLEXNUMBERSK3 be complex-memberedMEMBEREDV1"
     sorry
qed "sorry"

mtheorem membered_cl_8:
"cluster ExtREALXXREAL-0K3 as-term-is ext-real-memberedMEMBEREDV2"
proof
(*coherence*)
  show "ExtREALXXREAL-0K3 be ext-real-memberedMEMBEREDV2"
sorry
qed "sorry"

mtheorem membered_cl_9:
"cluster REALNUMBERSK2 as-term-is real-memberedMEMBEREDV3"
proof
(*coherence*)
  show "REALNUMBERSK2 be real-memberedMEMBEREDV3"
     sorry
qed "sorry"

mtheorem membered_cl_10:
"cluster RATRAT-1K1 as-term-is rational-memberedMEMBEREDV4"
proof
(*coherence*)
  show "RATRAT-1K1 be rational-memberedMEMBEREDV4"
sorry
qed "sorry"

mtheorem membered_cl_11:
"cluster INTINT-1K1 as-term-is integer-memberedMEMBEREDV5"
proof
(*coherence*)
  show "INTINT-1K1 be integer-memberedMEMBEREDV5"
     sorry
qed "sorry"

mtheorem membered_cl_12:
"cluster NATNUMBERSK1 as-term-is natural-memberedMEMBEREDV6"
proof
(*coherence*)
  show "NATNUMBERSK1 be natural-memberedMEMBEREDV6"
     sorry
qed "sorry"

mtheorem membered_th_1:
" for X be setHIDDENM2 holds X be complex-memberedMEMBEREDV1 implies X c=TARSKIR1 COMPLEXNUMBERSK3"
sorry

mtheorem membered_th_2:
" for X be setHIDDENM2 holds X be ext-real-memberedMEMBEREDV2 implies X c=TARSKIR1 ExtREALXXREAL-0K3"
sorry

mtheorem membered_th_3:
" for X be setHIDDENM2 holds X be real-memberedMEMBEREDV3 implies X c=TARSKIR1 REALNUMBERSK2"
sorry

mtheorem membered_th_4:
" for X be setHIDDENM2 holds X be rational-memberedMEMBEREDV4 implies X c=TARSKIR1 RATRAT-1K1"
sorry

mtheorem membered_th_5:
" for X be setHIDDENM2 holds X be integer-memberedMEMBEREDV5 implies X c=TARSKIR1 INTINT-1K1"
sorry

mtheorem membered_th_6:
" for X be setHIDDENM2 holds X be natural-memberedMEMBEREDV6 implies X c=TARSKIR1 NATNUMBERSK1"
  using ordinal1_def_12 sorry

mtheorem membered_cl_13:
  mlet "X be complex-memberedMEMBEREDV1\<bar>setHIDDENM2"
"cluster note-that complexXCMPLX-0V1 for ElementSUBSET-1M1-of X"
proof
(*coherence*)
  show " for it be ElementSUBSET-1M1-of X holds it be complexXCMPLX-0V1"
sorry
qed "sorry"

mtheorem membered_cl_14:
  mlet "X be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2"
"cluster note-that ext-realXXREAL-0V1 for ElementSUBSET-1M1-of X"
proof
(*coherence*)
  show " for it be ElementSUBSET-1M1-of X holds it be ext-realXXREAL-0V1"
sorry
qed "sorry"

mtheorem membered_cl_15:
  mlet "X be real-memberedMEMBEREDV3\<bar>setHIDDENM2"
"cluster note-that realXREAL-0V1 for ElementSUBSET-1M1-of X"
proof
(*coherence*)
  show " for it be ElementSUBSET-1M1-of X holds it be realXREAL-0V1"
sorry
qed "sorry"

mtheorem membered_cl_16:
  mlet "X be rational-memberedMEMBEREDV4\<bar>setHIDDENM2"
"cluster note-that rationalRAT-1V1 for ElementSUBSET-1M1-of X"
proof
(*coherence*)
  show " for it be ElementSUBSET-1M1-of X holds it be rationalRAT-1V1"
sorry
qed "sorry"

mtheorem membered_cl_17:
  mlet "X be integer-memberedMEMBEREDV5\<bar>setHIDDENM2"
"cluster note-that integerINT-1V1 for ElementSUBSET-1M1-of X"
proof
(*coherence*)
  show " for it be ElementSUBSET-1M1-of X holds it be integerINT-1V1"
sorry
qed "sorry"

mtheorem membered_cl_18:
  mlet "X be natural-memberedMEMBEREDV6\<bar>setHIDDENM2"
"cluster note-that naturalORDINAL1V7 for ElementSUBSET-1M1-of X"
proof
(*coherence*)
  show " for it be ElementSUBSET-1M1-of X holds it be naturalORDINAL1V7"
sorry
qed "sorry"

reserve c, c1, c2, c3 for "ComplexXCMPLX-0M1"
reserve e, e1, e2, e3 for "ExtRealXXREAL-0M1"
reserve r, r1, r2, r3 for "RealXREAL-0M1"
reserve w, w1, w2, w3 for "RationalRAT-1M1"
reserve i, i1, i2, i3 for "IntegerINT-1M1"
reserve n, n1, n2, n3 for "NatNAT-1M1"
mtheorem membered_th_7:
" for X be  non emptyXBOOLE-0V1\<bar>complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  ex c be ComplexXCMPLX-0M1 st c inHIDDENR3 X"
sorry

mtheorem membered_th_8:
" for X be  non emptyXBOOLE-0V1\<bar>ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  ex e be ExtRealXXREAL-0M1 st e inHIDDENR3 X"
sorry

mtheorem membered_th_9:
" for X be  non emptyXBOOLE-0V1\<bar>real-memberedMEMBEREDV3\<bar>setHIDDENM2 holds  ex r be RealXREAL-0M1 st r inHIDDENR3 X"
sorry

mtheorem membered_th_10:
" for X be  non emptyXBOOLE-0V1\<bar>rational-memberedMEMBEREDV4\<bar>setHIDDENM2 holds  ex w be RationalRAT-1M1 st w inHIDDENR3 X"
sorry

mtheorem membered_th_11:
" for X be  non emptyXBOOLE-0V1\<bar>integer-memberedMEMBEREDV5\<bar>setHIDDENM2 holds  ex i be IntegerINT-1M1 st i inHIDDENR3 X"
sorry

mtheorem membered_th_12:
" for X be  non emptyXBOOLE-0V1\<bar>natural-memberedMEMBEREDV6\<bar>setHIDDENM2 holds  ex n be NatNAT-1M1 st n inTARSKIR2 X"
sorry

mtheorem membered_th_13:
" for X be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds ( for c be ComplexXCMPLX-0M1 holds c inHIDDENR3 X) implies X =XBOOLE-0R4 COMPLEXNUMBERSK3"
sorry

mtheorem membered_th_14:
" for X be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds ( for e be ExtRealXXREAL-0M1 holds e inHIDDENR3 X) implies X =XBOOLE-0R4 ExtREALXXREAL-0K3"
sorry

mtheorem membered_th_15:
" for X be real-memberedMEMBEREDV3\<bar>setHIDDENM2 holds ( for r be RealXREAL-0M1 holds r inHIDDENR3 X) implies X =XBOOLE-0R4 REALNUMBERSK2"
sorry

mtheorem membered_th_16:
" for X be rational-memberedMEMBEREDV4\<bar>setHIDDENM2 holds ( for w be RationalRAT-1M1 holds w inHIDDENR3 X) implies X =XBOOLE-0R4 RATRAT-1K1"
sorry

mtheorem membered_th_17:
" for X be integer-memberedMEMBEREDV5\<bar>setHIDDENM2 holds ( for i be IntegerINT-1M1 holds i inHIDDENR3 X) implies X =XBOOLE-0R4 INTINT-1K1"
sorry

mtheorem membered_th_18:
" for X be natural-memberedMEMBEREDV6\<bar>setHIDDENM2 holds ( for n be NatNAT-1M1 holds n inTARSKIR2 X) implies X =XBOOLE-0R4 NATNUMBERSK1"
sorry

mtheorem membered_th_19:
" for X be setHIDDENM2 holds  for Y be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds X c=TARSKIR1 Y implies X be complex-memberedMEMBEREDV1"
   sorry

mtheorem membered_th_20:
" for X be setHIDDENM2 holds  for Y be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds X c=TARSKIR1 Y implies X be ext-real-memberedMEMBEREDV2"
   sorry

mtheorem membered_th_21:
" for X be setHIDDENM2 holds  for Y be real-memberedMEMBEREDV3\<bar>setHIDDENM2 holds X c=TARSKIR1 Y implies X be real-memberedMEMBEREDV3"
   sorry

mtheorem membered_th_22:
" for X be setHIDDENM2 holds  for Y be rational-memberedMEMBEREDV4\<bar>setHIDDENM2 holds X c=TARSKIR1 Y implies X be rational-memberedMEMBEREDV4"
   sorry

mtheorem membered_th_23:
" for X be setHIDDENM2 holds  for Y be integer-memberedMEMBEREDV5\<bar>setHIDDENM2 holds X c=TARSKIR1 Y implies X be integer-memberedMEMBEREDV5"
   sorry

mtheorem membered_th_24:
" for X be setHIDDENM2 holds  for Y be natural-memberedMEMBEREDV6\<bar>setHIDDENM2 holds X c=TARSKIR1 Y implies X be natural-memberedMEMBEREDV6"
   sorry

mtheorem membered_cl_19:
"cluster emptyXBOOLE-0V1 also-is natural-memberedMEMBEREDV6 for setHIDDENM2"
proof
(*coherence*)
  show " for it be setHIDDENM2 holds it be emptyXBOOLE-0V1 implies it be natural-memberedMEMBEREDV6"
     sorry
qed "sorry"

mtheorem membered_cl_20:
  mlet "c be ComplexXCMPLX-0M1"
"cluster {TARSKIK1 c} as-term-is complex-memberedMEMBEREDV1"
proof
(*coherence*)
  show "{TARSKIK1 c} be complex-memberedMEMBEREDV1"
    using tarski_def_1 sorry
qed "sorry"

mtheorem membered_cl_21:
  mlet "e be ExtRealXXREAL-0M1"
"cluster {TARSKIK1 e} as-term-is ext-real-memberedMEMBEREDV2"
proof
(*coherence*)
  show "{TARSKIK1 e} be ext-real-memberedMEMBEREDV2"
    using tarski_def_1 sorry
qed "sorry"

mtheorem membered_cl_22:
  mlet "r be RealXREAL-0M1"
"cluster {TARSKIK1 r} as-term-is real-memberedMEMBEREDV3"
proof
(*coherence*)
  show "{TARSKIK1 r} be real-memberedMEMBEREDV3"
    using tarski_def_1 sorry
qed "sorry"

mtheorem membered_cl_23:
  mlet "w be RationalRAT-1M1"
"cluster {TARSKIK1 w} as-term-is rational-memberedMEMBEREDV4"
proof
(*coherence*)
  show "{TARSKIK1 w} be rational-memberedMEMBEREDV4"
    using tarski_def_1 sorry
qed "sorry"

mtheorem membered_cl_24:
  mlet "i be IntegerINT-1M1"
"cluster {TARSKIK1 i} as-term-is integer-memberedMEMBEREDV5"
proof
(*coherence*)
  show "{TARSKIK1 i} be integer-memberedMEMBEREDV5"
    using tarski_def_1 sorry
qed "sorry"

mtheorem membered_cl_25:
  mlet "n be NatNAT-1M1"
"cluster {TARSKIK1 n} as-term-is natural-memberedMEMBEREDV6"
proof
(*coherence*)
  show "{TARSKIK1 n} be natural-memberedMEMBEREDV6"
    using tarski_def_1 sorry
qed "sorry"

mtheorem membered_cl_26:
  mlet "c1 be ComplexXCMPLX-0M1", "c2 be ComplexXCMPLX-0M1"
"cluster {TARSKIK2 c1,c2 } as-term-is complex-memberedMEMBEREDV1"
proof
(*coherence*)
  show "{TARSKIK2 c1,c2 } be complex-memberedMEMBEREDV1"
    using tarski_def_2 sorry
qed "sorry"

mtheorem membered_cl_27:
  mlet "e1 be ExtRealXXREAL-0M1", "e2 be ExtRealXXREAL-0M1"
"cluster {TARSKIK2 e1,e2 } as-term-is ext-real-memberedMEMBEREDV2"
proof
(*coherence*)
  show "{TARSKIK2 e1,e2 } be ext-real-memberedMEMBEREDV2"
    using tarski_def_2 sorry
qed "sorry"

mtheorem membered_cl_28:
  mlet "r1 be RealXREAL-0M1", "r2 be RealXREAL-0M1"
"cluster {TARSKIK2 r1,r2 } as-term-is real-memberedMEMBEREDV3"
proof
(*coherence*)
  show "{TARSKIK2 r1,r2 } be real-memberedMEMBEREDV3"
    using tarski_def_2 sorry
qed "sorry"

mtheorem membered_cl_29:
  mlet "w1 be RationalRAT-1M1", "w2 be RationalRAT-1M1"
"cluster {TARSKIK2 w1,w2 } as-term-is rational-memberedMEMBEREDV4"
proof
(*coherence*)
  show "{TARSKIK2 w1,w2 } be rational-memberedMEMBEREDV4"
    using tarski_def_2 sorry
qed "sorry"

mtheorem membered_cl_30:
  mlet "i1 be IntegerINT-1M1", "i2 be IntegerINT-1M1"
"cluster {TARSKIK2 i1,i2 } as-term-is integer-memberedMEMBEREDV5"
proof
(*coherence*)
  show "{TARSKIK2 i1,i2 } be integer-memberedMEMBEREDV5"
    using tarski_def_2 sorry
qed "sorry"

mtheorem membered_cl_31:
  mlet "n1 be NatNAT-1M1", "n2 be NatNAT-1M1"
"cluster {TARSKIK2 n1,n2 } as-term-is natural-memberedMEMBEREDV6"
proof
(*coherence*)
  show "{TARSKIK2 n1,n2 } be natural-memberedMEMBEREDV6"
    using tarski_def_2 sorry
qed "sorry"

mtheorem membered_cl_32:
  mlet "c1 be ComplexXCMPLX-0M1", "c2 be ComplexXCMPLX-0M1", "c3 be ComplexXCMPLX-0M1"
"cluster {ENUMSET1K1 c1,c2,c3 } as-term-is complex-memberedMEMBEREDV1"
proof
(*coherence*)
  show "{ENUMSET1K1 c1,c2,c3 } be complex-memberedMEMBEREDV1"
    using enumset1_def_1 sorry
qed "sorry"

mtheorem membered_cl_33:
  mlet "e1 be ExtRealXXREAL-0M1", "e2 be ExtRealXXREAL-0M1", "e3 be ExtRealXXREAL-0M1"
"cluster {ENUMSET1K1 e1,e2,e3 } as-term-is ext-real-memberedMEMBEREDV2"
proof
(*coherence*)
  show "{ENUMSET1K1 e1,e2,e3 } be ext-real-memberedMEMBEREDV2"
    using enumset1_def_1 sorry
qed "sorry"

mtheorem membered_cl_34:
  mlet "r1 be RealXREAL-0M1", "r2 be RealXREAL-0M1", "r3 be RealXREAL-0M1"
"cluster {ENUMSET1K1 r1,r2,r3 } as-term-is real-memberedMEMBEREDV3"
proof
(*coherence*)
  show "{ENUMSET1K1 r1,r2,r3 } be real-memberedMEMBEREDV3"
    using enumset1_def_1 sorry
qed "sorry"

mtheorem membered_cl_35:
  mlet "w1 be RationalRAT-1M1", "w2 be RationalRAT-1M1", "w3 be RationalRAT-1M1"
"cluster {ENUMSET1K1 w1,w2,w3 } as-term-is rational-memberedMEMBEREDV4"
proof
(*coherence*)
  show "{ENUMSET1K1 w1,w2,w3 } be rational-memberedMEMBEREDV4"
    using enumset1_def_1 sorry
qed "sorry"

mtheorem membered_cl_36:
  mlet "i1 be IntegerINT-1M1", "i2 be IntegerINT-1M1", "i3 be IntegerINT-1M1"
"cluster {ENUMSET1K1 i1,i2,i3 } as-term-is integer-memberedMEMBEREDV5"
proof
(*coherence*)
  show "{ENUMSET1K1 i1,i2,i3 } be integer-memberedMEMBEREDV5"
    using enumset1_def_1 sorry
qed "sorry"

mtheorem membered_cl_37:
  mlet "n1 be NatNAT-1M1", "n2 be NatNAT-1M1", "n3 be NatNAT-1M1"
"cluster {ENUMSET1K1 n1,n2,n3 } as-term-is natural-memberedMEMBEREDV6"
proof
(*coherence*)
  show "{ENUMSET1K1 n1,n2,n3 } be natural-memberedMEMBEREDV6"
    using enumset1_def_1 sorry
qed "sorry"

mtheorem membered_cl_38:
  mlet "X be complex-memberedMEMBEREDV1\<bar>setHIDDENM2"
"cluster note-that complex-memberedMEMBEREDV1 for SubsetSUBSET-1M2-of X"
proof
(*coherence*)
  show " for it be SubsetSUBSET-1M2-of X holds it be complex-memberedMEMBEREDV1"
     sorry
qed "sorry"

mtheorem membered_cl_39:
  mlet "X be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2"
"cluster note-that ext-real-memberedMEMBEREDV2 for SubsetSUBSET-1M2-of X"
proof
(*coherence*)
  show " for it be SubsetSUBSET-1M2-of X holds it be ext-real-memberedMEMBEREDV2"
     sorry
qed "sorry"

mtheorem membered_cl_40:
  mlet "X be real-memberedMEMBEREDV3\<bar>setHIDDENM2"
"cluster note-that real-memberedMEMBEREDV3 for SubsetSUBSET-1M2-of X"
proof
(*coherence*)
  show " for it be SubsetSUBSET-1M2-of X holds it be real-memberedMEMBEREDV3"
     sorry
qed "sorry"

mtheorem membered_cl_41:
  mlet "X be rational-memberedMEMBEREDV4\<bar>setHIDDENM2"
"cluster note-that rational-memberedMEMBEREDV4 for SubsetSUBSET-1M2-of X"
proof
(*coherence*)
  show " for it be SubsetSUBSET-1M2-of X holds it be rational-memberedMEMBEREDV4"
     sorry
qed "sorry"

mtheorem membered_cl_42:
  mlet "X be integer-memberedMEMBEREDV5\<bar>setHIDDENM2"
"cluster note-that integer-memberedMEMBEREDV5 for SubsetSUBSET-1M2-of X"
proof
(*coherence*)
  show " for it be SubsetSUBSET-1M2-of X holds it be integer-memberedMEMBEREDV5"
     sorry
qed "sorry"

mtheorem membered_cl_43:
  mlet "X be natural-memberedMEMBEREDV6\<bar>setHIDDENM2"
"cluster note-that natural-memberedMEMBEREDV6 for SubsetSUBSET-1M2-of X"
proof
(*coherence*)
  show " for it be SubsetSUBSET-1M2-of X holds it be natural-memberedMEMBEREDV6"
     sorry
qed "sorry"

mtheorem membered_cl_44:
  mlet "X be complex-memberedMEMBEREDV1\<bar>setHIDDENM2", "Y be complex-memberedMEMBEREDV1\<bar>setHIDDENM2"
"cluster X \\/XBOOLE-0K2 Y as-term-is complex-memberedMEMBEREDV1"
proof
(*coherence*)
  show "X \\/XBOOLE-0K2 Y be complex-memberedMEMBEREDV1"
sorry
qed "sorry"

mtheorem membered_cl_45:
  mlet "X be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2", "Y be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2"
"cluster X \\/XBOOLE-0K2 Y as-term-is ext-real-memberedMEMBEREDV2"
proof
(*coherence*)
  show "X \\/XBOOLE-0K2 Y be ext-real-memberedMEMBEREDV2"
sorry
qed "sorry"

mtheorem membered_cl_46:
  mlet "X be real-memberedMEMBEREDV3\<bar>setHIDDENM2", "Y be real-memberedMEMBEREDV3\<bar>setHIDDENM2"
"cluster X \\/XBOOLE-0K2 Y as-term-is real-memberedMEMBEREDV3"
proof
(*coherence*)
  show "X \\/XBOOLE-0K2 Y be real-memberedMEMBEREDV3"
sorry
qed "sorry"

mtheorem membered_cl_47:
  mlet "X be rational-memberedMEMBEREDV4\<bar>setHIDDENM2", "Y be rational-memberedMEMBEREDV4\<bar>setHIDDENM2"
"cluster X \\/XBOOLE-0K2 Y as-term-is rational-memberedMEMBEREDV4"
proof
(*coherence*)
  show "X \\/XBOOLE-0K2 Y be rational-memberedMEMBEREDV4"
sorry
qed "sorry"

mtheorem membered_cl_48:
  mlet "X be integer-memberedMEMBEREDV5\<bar>setHIDDENM2", "Y be integer-memberedMEMBEREDV5\<bar>setHIDDENM2"
"cluster X \\/XBOOLE-0K2 Y as-term-is integer-memberedMEMBEREDV5"
proof
(*coherence*)
  show "X \\/XBOOLE-0K2 Y be integer-memberedMEMBEREDV5"
sorry
qed "sorry"

mtheorem membered_cl_49:
  mlet "X be natural-memberedMEMBEREDV6\<bar>setHIDDENM2", "Y be natural-memberedMEMBEREDV6\<bar>setHIDDENM2"
"cluster X \\/XBOOLE-0K2 Y as-term-is natural-memberedMEMBEREDV6"
proof
(*coherence*)
  show "X \\/XBOOLE-0K2 Y be natural-memberedMEMBEREDV6"
sorry
qed "sorry"

mtheorem membered_cl_50:
  mlet "X be complex-memberedMEMBEREDV1\<bar>setHIDDENM2", "Y be setHIDDENM2"
"cluster X /\\XBOOLE-0K3 Y as-term-is complex-memberedMEMBEREDV1"
proof
(*coherence*)
  show "X /\\XBOOLE-0K3 Y be complex-memberedMEMBEREDV1"
    using membered_th_19 xboole_1_th_17 sorry
qed "sorry"

mtheorem membered_cl_51:
  mlet "X be complex-memberedMEMBEREDV1\<bar>setHIDDENM2", "Y be setHIDDENM2"
"cluster Y /\\XBOOLE-0K3 X as-term-is complex-memberedMEMBEREDV1"
proof
(*coherence*)
  show "Y /\\XBOOLE-0K3 X be complex-memberedMEMBEREDV1"
     sorry
qed "sorry"

mtheorem membered_cl_52:
  mlet "X be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2", "Y be setHIDDENM2"
"cluster X /\\XBOOLE-0K3 Y as-term-is ext-real-memberedMEMBEREDV2"
proof
(*coherence*)
  show "X /\\XBOOLE-0K3 Y be ext-real-memberedMEMBEREDV2"
    using membered_th_20 xboole_1_th_17 sorry
qed "sorry"

mtheorem membered_cl_53:
  mlet "X be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2", "Y be setHIDDENM2"
"cluster Y /\\XBOOLE-0K3 X as-term-is ext-real-memberedMEMBEREDV2"
proof
(*coherence*)
  show "Y /\\XBOOLE-0K3 X be ext-real-memberedMEMBEREDV2"
     sorry
qed "sorry"

mtheorem membered_cl_54:
  mlet "X be real-memberedMEMBEREDV3\<bar>setHIDDENM2", "Y be setHIDDENM2"
"cluster X /\\XBOOLE-0K3 Y as-term-is real-memberedMEMBEREDV3"
proof
(*coherence*)
  show "X /\\XBOOLE-0K3 Y be real-memberedMEMBEREDV3"
    using membered_th_21 xboole_1_th_17 sorry
qed "sorry"

mtheorem membered_cl_55:
  mlet "X be real-memberedMEMBEREDV3\<bar>setHIDDENM2", "Y be setHIDDENM2"
"cluster Y /\\XBOOLE-0K3 X as-term-is real-memberedMEMBEREDV3"
proof
(*coherence*)
  show "Y /\\XBOOLE-0K3 X be real-memberedMEMBEREDV3"
     sorry
qed "sorry"

mtheorem membered_cl_56:
  mlet "X be rational-memberedMEMBEREDV4\<bar>setHIDDENM2", "Y be setHIDDENM2"
"cluster X /\\XBOOLE-0K3 Y as-term-is rational-memberedMEMBEREDV4"
proof
(*coherence*)
  show "X /\\XBOOLE-0K3 Y be rational-memberedMEMBEREDV4"
    using membered_th_22 xboole_1_th_17 sorry
qed "sorry"

mtheorem membered_cl_57:
  mlet "X be rational-memberedMEMBEREDV4\<bar>setHIDDENM2", "Y be setHIDDENM2"
"cluster Y /\\XBOOLE-0K3 X as-term-is rational-memberedMEMBEREDV4"
proof
(*coherence*)
  show "Y /\\XBOOLE-0K3 X be rational-memberedMEMBEREDV4"
     sorry
qed "sorry"

mtheorem membered_cl_58:
  mlet "X be integer-memberedMEMBEREDV5\<bar>setHIDDENM2", "Y be setHIDDENM2"
"cluster X /\\XBOOLE-0K3 Y as-term-is integer-memberedMEMBEREDV5"
proof
(*coherence*)
  show "X /\\XBOOLE-0K3 Y be integer-memberedMEMBEREDV5"
    using membered_th_23 xboole_1_th_17 sorry
qed "sorry"

mtheorem membered_cl_59:
  mlet "X be integer-memberedMEMBEREDV5\<bar>setHIDDENM2", "Y be setHIDDENM2"
"cluster Y /\\XBOOLE-0K3 X as-term-is integer-memberedMEMBEREDV5"
proof
(*coherence*)
  show "Y /\\XBOOLE-0K3 X be integer-memberedMEMBEREDV5"
     sorry
qed "sorry"

mtheorem membered_cl_60:
  mlet "X be natural-memberedMEMBEREDV6\<bar>setHIDDENM2", "Y be setHIDDENM2"
"cluster X /\\XBOOLE-0K3 Y as-term-is natural-memberedMEMBEREDV6"
proof
(*coherence*)
  show "X /\\XBOOLE-0K3 Y be natural-memberedMEMBEREDV6"
    using membered_th_24 xboole_1_th_17 sorry
qed "sorry"

mtheorem membered_cl_61:
  mlet "X be natural-memberedMEMBEREDV6\<bar>setHIDDENM2", "Y be setHIDDENM2"
"cluster Y /\\XBOOLE-0K3 X as-term-is natural-memberedMEMBEREDV6"
proof
(*coherence*)
  show "Y /\\XBOOLE-0K3 X be natural-memberedMEMBEREDV6"
     sorry
qed "sorry"

mtheorem membered_cl_62:
  mlet "X be complex-memberedMEMBEREDV1\<bar>setHIDDENM2", "Y be setHIDDENM2"
"cluster X \\SUBSET-1K6 Y as-term-is complex-memberedMEMBEREDV1"
proof
(*coherence*)
  show "X \\SUBSET-1K6 Y be complex-memberedMEMBEREDV1"
     sorry
qed "sorry"

mtheorem membered_cl_63:
  mlet "X be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2", "Y be setHIDDENM2"
"cluster X \\SUBSET-1K6 Y as-term-is ext-real-memberedMEMBEREDV2"
proof
(*coherence*)
  show "X \\SUBSET-1K6 Y be ext-real-memberedMEMBEREDV2"
     sorry
qed "sorry"

mtheorem membered_cl_64:
  mlet "X be real-memberedMEMBEREDV3\<bar>setHIDDENM2", "Y be setHIDDENM2"
"cluster X \\SUBSET-1K6 Y as-term-is real-memberedMEMBEREDV3"
proof
(*coherence*)
  show "X \\SUBSET-1K6 Y be real-memberedMEMBEREDV3"
     sorry
qed "sorry"

mtheorem membered_cl_65:
  mlet "X be rational-memberedMEMBEREDV4\<bar>setHIDDENM2", "Y be setHIDDENM2"
"cluster X \\SUBSET-1K6 Y as-term-is rational-memberedMEMBEREDV4"
proof
(*coherence*)
  show "X \\SUBSET-1K6 Y be rational-memberedMEMBEREDV4"
     sorry
qed "sorry"

mtheorem membered_cl_66:
  mlet "X be integer-memberedMEMBEREDV5\<bar>setHIDDENM2", "Y be setHIDDENM2"
"cluster X \\SUBSET-1K6 Y as-term-is integer-memberedMEMBEREDV5"
proof
(*coherence*)
  show "X \\SUBSET-1K6 Y be integer-memberedMEMBEREDV5"
     sorry
qed "sorry"

mtheorem membered_cl_67:
  mlet "X be natural-memberedMEMBEREDV6\<bar>setHIDDENM2", "Y be setHIDDENM2"
"cluster X \\SUBSET-1K6 Y as-term-is natural-memberedMEMBEREDV6"
proof
(*coherence*)
  show "X \\SUBSET-1K6 Y be natural-memberedMEMBEREDV6"
     sorry
qed "sorry"

mtheorem membered_cl_68:
  mlet "X be complex-memberedMEMBEREDV1\<bar>setHIDDENM2", "Y be complex-memberedMEMBEREDV1\<bar>setHIDDENM2"
"cluster X \\+\\XBOOLE-0K5 Y as-term-is complex-memberedMEMBEREDV1"
proof
(*coherence*)
  show "X \\+\\XBOOLE-0K5 Y be complex-memberedMEMBEREDV1"
     sorry
qed "sorry"

mtheorem membered_cl_69:
  mlet "X be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2", "Y be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2"
"cluster X \\+\\XBOOLE-0K5 Y as-term-is ext-real-memberedMEMBEREDV2"
proof
(*coherence*)
  show "X \\+\\XBOOLE-0K5 Y be ext-real-memberedMEMBEREDV2"
     sorry
qed "sorry"

mtheorem membered_cl_70:
  mlet "X be real-memberedMEMBEREDV3\<bar>setHIDDENM2", "Y be real-memberedMEMBEREDV3\<bar>setHIDDENM2"
"cluster X \\+\\XBOOLE-0K5 Y as-term-is real-memberedMEMBEREDV3"
proof
(*coherence*)
  show "X \\+\\XBOOLE-0K5 Y be real-memberedMEMBEREDV3"
     sorry
qed "sorry"

mtheorem membered_cl_71:
  mlet "X be rational-memberedMEMBEREDV4\<bar>setHIDDENM2", "Y be rational-memberedMEMBEREDV4\<bar>setHIDDENM2"
"cluster X \\+\\XBOOLE-0K5 Y as-term-is rational-memberedMEMBEREDV4"
proof
(*coherence*)
  show "X \\+\\XBOOLE-0K5 Y be rational-memberedMEMBEREDV4"
     sorry
qed "sorry"

mtheorem membered_cl_72:
  mlet "X be integer-memberedMEMBEREDV5\<bar>setHIDDENM2", "Y be integer-memberedMEMBEREDV5\<bar>setHIDDENM2"
"cluster X \\+\\XBOOLE-0K5 Y as-term-is integer-memberedMEMBEREDV5"
proof
(*coherence*)
  show "X \\+\\XBOOLE-0K5 Y be integer-memberedMEMBEREDV5"
     sorry
qed "sorry"

mtheorem membered_cl_73:
  mlet "X be natural-memberedMEMBEREDV6\<bar>setHIDDENM2", "Y be natural-memberedMEMBEREDV6\<bar>setHIDDENM2"
"cluster X \\+\\XBOOLE-0K5 Y as-term-is natural-memberedMEMBEREDV6"
proof
(*coherence*)
  show "X \\+\\XBOOLE-0K5 Y be natural-memberedMEMBEREDV6"
     sorry
qed "sorry"

abbreviation(input) MEMBEREDR1(" _ c=MEMBEREDR1  _ " [50,50]50) where
  "X c=MEMBEREDR1 Y \<equiv> X c=TARSKIR1 Y"

mtheorem membered_def_7:
  mlet "X be complex-memberedMEMBEREDV1\<bar>setHIDDENM2", "Y be setHIDDENM2"
"redefine pred X c=MEMBEREDR1 Y means
   for c be ComplexXCMPLX-0M1 holds c inHIDDENR3 X implies c inHIDDENR3 Y"
proof
(*compatibility*)
  show "X c=MEMBEREDR1 Y iff ( for c be ComplexXCMPLX-0M1 holds c inHIDDENR3 X implies c inHIDDENR3 Y)"
     sorry
qed "sorry"

abbreviation(input) MEMBEREDR2(" _ c=MEMBEREDR2  _ " [50,50]50) where
  "X c=MEMBEREDR2 Y \<equiv> X c=TARSKIR1 Y"

mtheorem membered_def_8:
  mlet "X be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2", "Y be setHIDDENM2"
"redefine pred X c=MEMBEREDR2 Y means
   for e be ExtRealXXREAL-0M1 holds e inHIDDENR3 X implies e inHIDDENR3 Y"
proof
(*compatibility*)
  show "X c=MEMBEREDR2 Y iff ( for e be ExtRealXXREAL-0M1 holds e inHIDDENR3 X implies e inHIDDENR3 Y)"
     sorry
qed "sorry"

abbreviation(input) MEMBEREDR3(" _ c=MEMBEREDR3  _ " [50,50]50) where
  "X c=MEMBEREDR3 Y \<equiv> X c=TARSKIR1 Y"

mtheorem membered_def_9:
  mlet "X be real-memberedMEMBEREDV3\<bar>setHIDDENM2", "Y be setHIDDENM2"
"redefine pred X c=MEMBEREDR3 Y means
   for r be RealXREAL-0M1 holds r inHIDDENR3 X implies r inHIDDENR3 Y"
proof
(*compatibility*)
  show "X c=MEMBEREDR3 Y iff ( for r be RealXREAL-0M1 holds r inHIDDENR3 X implies r inHIDDENR3 Y)"
     sorry
qed "sorry"

abbreviation(input) MEMBEREDR4(" _ c=MEMBEREDR4  _ " [50,50]50) where
  "X c=MEMBEREDR4 Y \<equiv> X c=TARSKIR1 Y"

mtheorem membered_def_10:
  mlet "X be rational-memberedMEMBEREDV4\<bar>setHIDDENM2", "Y be setHIDDENM2"
"redefine pred X c=MEMBEREDR4 Y means
   for w be RationalRAT-1M1 holds w inHIDDENR3 X implies w inHIDDENR3 Y"
proof
(*compatibility*)
  show "X c=MEMBEREDR4 Y iff ( for w be RationalRAT-1M1 holds w inHIDDENR3 X implies w inHIDDENR3 Y)"
     sorry
qed "sorry"

abbreviation(input) MEMBEREDR5(" _ c=MEMBEREDR5  _ " [50,50]50) where
  "X c=MEMBEREDR5 Y \<equiv> X c=TARSKIR1 Y"

mtheorem membered_def_11:
  mlet "X be integer-memberedMEMBEREDV5\<bar>setHIDDENM2", "Y be setHIDDENM2"
"redefine pred X c=MEMBEREDR5 Y means
   for i be IntegerINT-1M1 holds i inHIDDENR3 X implies i inHIDDENR3 Y"
proof
(*compatibility*)
  show "X c=MEMBEREDR5 Y iff ( for i be IntegerINT-1M1 holds i inHIDDENR3 X implies i inHIDDENR3 Y)"
     sorry
qed "sorry"

abbreviation(input) MEMBEREDR6(" _ c=MEMBEREDR6  _ " [50,50]50) where
  "X c=MEMBEREDR6 Y \<equiv> X c=TARSKIR1 Y"

mtheorem membered_def_12:
  mlet "X be natural-memberedMEMBEREDV6\<bar>setHIDDENM2", "Y be setHIDDENM2"
"redefine pred X c=MEMBEREDR6 Y means
   for n be NatNAT-1M1 holds n inTARSKIR2 X implies n inTARSKIR2 Y"
proof
(*compatibility*)
  show "X c=MEMBEREDR6 Y iff ( for n be NatNAT-1M1 holds n inTARSKIR2 X implies n inTARSKIR2 Y)"
     sorry
qed "sorry"

abbreviation(input) MEMBEREDR7(" _ =MEMBEREDR7  _ " [50,50]50) where
  "X =MEMBEREDR7 Y \<equiv> X =HIDDENR1 Y"

mtheorem membered_def_13:
  mlet "X be complex-memberedMEMBEREDV1\<bar>setHIDDENM2", "Y be complex-memberedMEMBEREDV1\<bar>setHIDDENM2"
"redefine pred X =MEMBEREDR7 Y means
   for c be ComplexXCMPLX-0M1 holds c inHIDDENR3 X iff c inHIDDENR3 Y"
proof
(*compatibility*)
  show "X =MEMBEREDR7 Y iff ( for c be ComplexXCMPLX-0M1 holds c inHIDDENR3 X iff c inHIDDENR3 Y)"
sorry
qed "sorry"

abbreviation(input) MEMBEREDR8(" _ =MEMBEREDR8  _ " [50,50]50) where
  "X =MEMBEREDR8 Y \<equiv> X =HIDDENR1 Y"

mtheorem membered_def_14:
  mlet "X be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2", "Y be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2"
"redefine pred X =MEMBEREDR8 Y means
   for e be ExtRealXXREAL-0M1 holds e inHIDDENR3 X iff e inHIDDENR3 Y"
proof
(*compatibility*)
  show "X =MEMBEREDR8 Y iff ( for e be ExtRealXXREAL-0M1 holds e inHIDDENR3 X iff e inHIDDENR3 Y)"
sorry
qed "sorry"

abbreviation(input) MEMBEREDR9(" _ =MEMBEREDR9  _ " [50,50]50) where
  "X =MEMBEREDR9 Y \<equiv> X =HIDDENR1 Y"

mtheorem membered_def_15:
  mlet "X be real-memberedMEMBEREDV3\<bar>setHIDDENM2", "Y be real-memberedMEMBEREDV3\<bar>setHIDDENM2"
"redefine pred X =MEMBEREDR9 Y means
   for r be RealXREAL-0M1 holds r inHIDDENR3 X iff r inHIDDENR3 Y"
proof
(*compatibility*)
  show "X =MEMBEREDR9 Y iff ( for r be RealXREAL-0M1 holds r inHIDDENR3 X iff r inHIDDENR3 Y)"
     sorry
qed "sorry"

abbreviation(input) MEMBEREDR10(" _ =MEMBEREDR10  _ " [50,50]50) where
  "X =MEMBEREDR10 Y \<equiv> X =HIDDENR1 Y"

mtheorem membered_def_16:
  mlet "X be rational-memberedMEMBEREDV4\<bar>setHIDDENM2", "Y be rational-memberedMEMBEREDV4\<bar>setHIDDENM2"
"redefine pred X =MEMBEREDR10 Y means
   for w be RationalRAT-1M1 holds w inHIDDENR3 X iff w inHIDDENR3 Y"
proof
(*compatibility*)
  show "X =MEMBEREDR10 Y iff ( for w be RationalRAT-1M1 holds w inHIDDENR3 X iff w inHIDDENR3 Y)"
     sorry
qed "sorry"

abbreviation(input) MEMBEREDR11(" _ =MEMBEREDR11  _ " [50,50]50) where
  "X =MEMBEREDR11 Y \<equiv> X =HIDDENR1 Y"

mtheorem membered_def_17:
  mlet "X be integer-memberedMEMBEREDV5\<bar>setHIDDENM2", "Y be integer-memberedMEMBEREDV5\<bar>setHIDDENM2"
"redefine pred X =MEMBEREDR11 Y means
   for i be IntegerINT-1M1 holds i inHIDDENR3 X iff i inHIDDENR3 Y"
proof
(*compatibility*)
  show "X =MEMBEREDR11 Y iff ( for i be IntegerINT-1M1 holds i inHIDDENR3 X iff i inHIDDENR3 Y)"
     sorry
qed "sorry"

abbreviation(input) MEMBEREDR12(" _ =MEMBEREDR12  _ " [50,50]50) where
  "X =MEMBEREDR12 Y \<equiv> X =HIDDENR1 Y"

mtheorem membered_def_18:
  mlet "X be natural-memberedMEMBEREDV6\<bar>setHIDDENM2", "Y be natural-memberedMEMBEREDV6\<bar>setHIDDENM2"
"redefine pred X =MEMBEREDR12 Y means
   for n be NatNAT-1M1 holds n inTARSKIR2 X iff n inTARSKIR2 Y"
proof
(*compatibility*)
  show "X =MEMBEREDR12 Y iff ( for n be NatNAT-1M1 holds n inTARSKIR2 X iff n inTARSKIR2 Y)"
     sorry
qed "sorry"

abbreviation(input) MEMBEREDR13(" _ missesMEMBEREDR13  _ " [50,50]50) where
  "X missesMEMBEREDR13 Y \<equiv> X missesXBOOLE-0R1 Y"

mtheorem membered_def_19:
  mlet "X be complex-memberedMEMBEREDV1\<bar>setHIDDENM2", "Y be complex-memberedMEMBEREDV1\<bar>setHIDDENM2"
"redefine pred X missesMEMBEREDR13 Y means
   not ( ex c be ComplexXCMPLX-0M1 st c inHIDDENR3 X & c inHIDDENR3 Y)"
proof
(*compatibility*)
  show "X missesMEMBEREDR13 Y iff  not ( ex c be ComplexXCMPLX-0M1 st c inHIDDENR3 X & c inHIDDENR3 Y)"
sorry
qed "sorry"

abbreviation(input) MEMBEREDR14(" _ missesMEMBEREDR14  _ " [50,50]50) where
  "X missesMEMBEREDR14 Y \<equiv> X missesXBOOLE-0R1 Y"

mtheorem membered_def_20:
  mlet "X be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2", "Y be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2"
"redefine pred X missesMEMBEREDR14 Y means
   not ( ex e be ExtRealXXREAL-0M1 st e inHIDDENR3 X & e inHIDDENR3 Y)"
proof
(*compatibility*)
  show "X missesMEMBEREDR14 Y iff  not ( ex e be ExtRealXXREAL-0M1 st e inHIDDENR3 X & e inHIDDENR3 Y)"
sorry
qed "sorry"

abbreviation(input) MEMBEREDR15(" _ missesMEMBEREDR15  _ " [50,50]50) where
  "X missesMEMBEREDR15 Y \<equiv> X missesXBOOLE-0R1 Y"

mtheorem membered_def_21:
  mlet "X be real-memberedMEMBEREDV3\<bar>setHIDDENM2", "Y be real-memberedMEMBEREDV3\<bar>setHIDDENM2"
"redefine pred X missesMEMBEREDR15 Y means
   not ( ex r be RealXREAL-0M1 st r inHIDDENR3 X & r inHIDDENR3 Y)"
proof
(*compatibility*)
  show "X missesMEMBEREDR15 Y iff  not ( ex r be RealXREAL-0M1 st r inHIDDENR3 X & r inHIDDENR3 Y)"
     sorry
qed "sorry"

abbreviation(input) MEMBEREDR16(" _ missesMEMBEREDR16  _ " [50,50]50) where
  "X missesMEMBEREDR16 Y \<equiv> X missesXBOOLE-0R1 Y"

mtheorem membered_def_22:
  mlet "X be rational-memberedMEMBEREDV4\<bar>setHIDDENM2", "Y be rational-memberedMEMBEREDV4\<bar>setHIDDENM2"
"redefine pred X missesMEMBEREDR16 Y means
   not ( ex w be RationalRAT-1M1 st w inHIDDENR3 X & w inHIDDENR3 Y)"
proof
(*compatibility*)
  show "X missesMEMBEREDR16 Y iff  not ( ex w be RationalRAT-1M1 st w inHIDDENR3 X & w inHIDDENR3 Y)"
     sorry
qed "sorry"

abbreviation(input) MEMBEREDR17(" _ missesMEMBEREDR17  _ " [50,50]50) where
  "X missesMEMBEREDR17 Y \<equiv> X missesXBOOLE-0R1 Y"

mtheorem membered_def_23:
  mlet "X be integer-memberedMEMBEREDV5\<bar>setHIDDENM2", "Y be integer-memberedMEMBEREDV5\<bar>setHIDDENM2"
"redefine pred X missesMEMBEREDR17 Y means
   not ( ex i be IntegerINT-1M1 st i inHIDDENR3 X & i inHIDDENR3 Y)"
proof
(*compatibility*)
  show "X missesMEMBEREDR17 Y iff  not ( ex i be IntegerINT-1M1 st i inHIDDENR3 X & i inHIDDENR3 Y)"
     sorry
qed "sorry"

abbreviation(input) MEMBEREDR18(" _ missesMEMBEREDR18  _ " [50,50]50) where
  "X missesMEMBEREDR18 Y \<equiv> X missesXBOOLE-0R1 Y"

mtheorem membered_def_24:
  mlet "X be natural-memberedMEMBEREDV6\<bar>setHIDDENM2", "Y be natural-memberedMEMBEREDV6\<bar>setHIDDENM2"
"redefine pred X missesMEMBEREDR18 Y means
   not ( ex n be NatNAT-1M1 st n inTARSKIR2 X & n inTARSKIR2 Y)"
proof
(*compatibility*)
  show "X missesMEMBEREDR18 Y iff  not ( ex n be NatNAT-1M1 st n inTARSKIR2 X & n inTARSKIR2 Y)"
     sorry
qed "sorry"

mtheorem membered_th_25:
" for F be setHIDDENM2 holds ( for X be setHIDDENM2 holds X inTARSKIR2 F implies X be complex-memberedMEMBEREDV1) implies unionTARSKIK3 F be complex-memberedMEMBEREDV1"
sorry

mtheorem membered_th_26:
" for F be setHIDDENM2 holds ( for X be setHIDDENM2 holds X inTARSKIR2 F implies X be ext-real-memberedMEMBEREDV2) implies unionTARSKIK3 F be ext-real-memberedMEMBEREDV2"
sorry

mtheorem membered_th_27:
" for F be setHIDDENM2 holds ( for X be setHIDDENM2 holds X inTARSKIR2 F implies X be real-memberedMEMBEREDV3) implies unionTARSKIK3 F be real-memberedMEMBEREDV3"
sorry

mtheorem membered_th_28:
" for F be setHIDDENM2 holds ( for X be setHIDDENM2 holds X inTARSKIR2 F implies X be rational-memberedMEMBEREDV4) implies unionTARSKIK3 F be rational-memberedMEMBEREDV4"
sorry

mtheorem membered_th_29:
" for F be setHIDDENM2 holds ( for X be setHIDDENM2 holds X inTARSKIR2 F implies X be integer-memberedMEMBEREDV5) implies unionTARSKIK3 F be integer-memberedMEMBEREDV5"
sorry

mtheorem membered_th_30:
" for F be setHIDDENM2 holds ( for X be setHIDDENM2 holds X inTARSKIR2 F implies X be natural-memberedMEMBEREDV6) implies unionTARSKIK3 F be natural-memberedMEMBEREDV6"
sorry

mtheorem membered_th_31:
" for F be setHIDDENM2 holds  for X be setHIDDENM2 holds X inTARSKIR2 F & X be complex-memberedMEMBEREDV1 implies meetSETFAM-1K1 F be complex-memberedMEMBEREDV1"
  using membered_th_19 setfam_1_th_3 sorry

mtheorem membered_th_32:
" for F be setHIDDENM2 holds  for X be setHIDDENM2 holds X inTARSKIR2 F & X be ext-real-memberedMEMBEREDV2 implies meetSETFAM-1K1 F be ext-real-memberedMEMBEREDV2"
  using membered_th_20 setfam_1_th_3 sorry

mtheorem membered_th_33:
" for F be setHIDDENM2 holds  for X be setHIDDENM2 holds X inTARSKIR2 F & X be real-memberedMEMBEREDV3 implies meetSETFAM-1K1 F be real-memberedMEMBEREDV3"
  using membered_th_21 setfam_1_th_3 sorry

mtheorem membered_th_34:
" for F be setHIDDENM2 holds  for X be setHIDDENM2 holds X inTARSKIR2 F & X be rational-memberedMEMBEREDV4 implies meetSETFAM-1K1 F be rational-memberedMEMBEREDV4"
  using membered_th_22 setfam_1_th_3 sorry

mtheorem membered_th_35:
" for F be setHIDDENM2 holds  for X be setHIDDENM2 holds X inTARSKIR2 F & X be integer-memberedMEMBEREDV5 implies meetSETFAM-1K1 F be integer-memberedMEMBEREDV5"
  using membered_th_23 setfam_1_th_3 sorry

mtheorem membered_th_36:
" for F be setHIDDENM2 holds  for X be setHIDDENM2 holds X inTARSKIR2 F & X be natural-memberedMEMBEREDV6 implies meetSETFAM-1K1 F be natural-memberedMEMBEREDV6"
  using membered_th_24 setfam_1_th_3 sorry

theorem membered_sch_1:
  fixes Pp1 
  shows " ex X be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 st  for c be ComplexXCMPLX-0M1 holds c inHIDDENR3 X iff Pp1(c)"
sorry

theorem membered_sch_2:
  fixes Pp1 
  shows " ex X be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 st  for e be ExtRealXXREAL-0M1 holds e inHIDDENR3 X iff Pp1(e)"
sorry

theorem membered_sch_3:
  fixes Pp1 
  shows " ex X be real-memberedMEMBEREDV3\<bar>setHIDDENM2 st  for r be RealXREAL-0M1 holds r inHIDDENR3 X iff Pp1(r)"
sorry

theorem membered_sch_4:
  fixes Pp1 
  shows " ex X be rational-memberedMEMBEREDV4\<bar>setHIDDENM2 st  for w be RationalRAT-1M1 holds w inHIDDENR3 X iff Pp1(w)"
sorry

theorem membered_sch_5:
  fixes Pp1 
  shows " ex X be integer-memberedMEMBEREDV5\<bar>setHIDDENM2 st  for i be IntegerINT-1M1 holds i inHIDDENR3 X iff Pp1(i)"
sorry

theorem membered_sch_6:
  fixes Pp1 
  shows " ex X be natural-memberedMEMBEREDV6\<bar>setHIDDENM2 st  for n be NatNAT-1M1 holds n inTARSKIR2 X iff Pp1(n)"
sorry

mtheorem membered_cl_74:
"cluster  non emptyXBOOLE-0V1\<bar>natural-memberedMEMBEREDV6 for setHIDDENM2"
proof
(*existence*)
  show " ex it be setHIDDENM2 st it be  non emptyXBOOLE-0V1\<bar>natural-memberedMEMBEREDV6"
sorry
qed "sorry"

reserve a, b, d for "RealXREAL-0M1"
mtheorem membered_th_37:
" for X be real-memberedMEMBEREDV3\<bar>setHIDDENM2 holds  for Y be real-memberedMEMBEREDV3\<bar>setHIDDENM2 holds (X <>HIDDENR2 {}XBOOLE-0K1 & Y <>HIDDENR2 {}XBOOLE-0K1) & ( for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds a inHIDDENR3 X & b inHIDDENR3 Y implies a <=XXREAL-0R1 b) implies ( ex d be RealXREAL-0M1 st ( for a be RealXREAL-0M1 holds a inHIDDENR3 X implies a <=XXREAL-0R1 d) & ( for b be RealXREAL-0M1 holds b inHIDDENR3 Y implies d <=XXREAL-0R1 b))"
sorry

mdef membered_def_25 ("add-closedMEMBEREDV7" 70 ) where
"attr add-closedMEMBEREDV7 for setHIDDENM2 means
  (\<lambda>X.  for x be ComplexXCMPLX-0M1 holds  for y be ComplexXCMPLX-0M1 holds x inHIDDENR3 X & y inHIDDENR3 X implies x +XCMPLX-0K2 y inTARSKIR2 X)"..

mtheorem membered_cl_75:
"cluster emptyXBOOLE-0V1 also-is add-closedMEMBEREDV7 for setHIDDENM2"
proof
(*coherence*)
  show " for it be setHIDDENM2 holds it be emptyXBOOLE-0V1 implies it be add-closedMEMBEREDV7"
     sorry
qed "sorry"

mtheorem membered_cl_76:
"cluster COMPLEXNUMBERSK3 as-term-is add-closedMEMBEREDV7"
proof
(*coherence*)
  show "COMPLEXNUMBERSK3 be add-closedMEMBEREDV7"
    using xcmplx_0_def_2 sorry
qed "sorry"

mtheorem membered_cl_77:
"cluster REALNUMBERSK2 as-term-is add-closedMEMBEREDV7"
proof
(*coherence*)
  show "REALNUMBERSK2 be add-closedMEMBEREDV7"
    using xreal_0_def_1 sorry
qed "sorry"

mtheorem membered_cl_78:
"cluster RATRAT-1K1 as-term-is add-closedMEMBEREDV7"
proof
(*coherence*)
  show "RATRAT-1K1 be add-closedMEMBEREDV7"
    using rat_1_def_2 sorry
qed "sorry"

mtheorem membered_cl_79:
"cluster INTINT-1K1 as-term-is add-closedMEMBEREDV7"
proof
(*coherence*)
  show "INTINT-1K1 be add-closedMEMBEREDV7"
    using int_1_def_2 sorry
qed "sorry"

mtheorem membered_cl_80:
"cluster NATNUMBERSK1 as-term-is add-closedMEMBEREDV7"
proof
(*coherence*)
  show "NATNUMBERSK1 be add-closedMEMBEREDV7"
    using ordinal1_def_12 sorry
qed "sorry"

mtheorem membered_cl_81:
"cluster  non emptyXBOOLE-0V1\<bar>add-closedMEMBEREDV7\<bar>natural-memberedMEMBEREDV6 for setHIDDENM2"
proof
(*existence*)
  show " ex it be setHIDDENM2 st it be  non emptyXBOOLE-0V1\<bar>add-closedMEMBEREDV7\<bar>natural-memberedMEMBEREDV6"
sorry
qed "sorry"

end
