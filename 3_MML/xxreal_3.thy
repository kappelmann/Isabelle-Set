theory xxreal_3
  imports xcmplx_1 xxreal_2
   "../mizar_extension/E_number"
begin
(*begin*)
reserve x, y, z, w for "ExtRealXXREAL-0M1"
reserve r for "RealXREAL-0M1"
abbreviation(input) XXREAL_3R1(" _ <=XXREAL-3R1  _ " [50,50]50) where
  "x <=XXREAL-3R1 y \<equiv> x <=XXREAL-0R1 y"

mtheorem xxreal_3_def_1:
  mlet "x be ExtRealXXREAL-0M1", "y be ExtRealXXREAL-0M1"
"redefine pred x <=XXREAL-3R1 y means
   ex p be ElementSUBSET-1M1-of REALNUMBERSK2 st  ex q be ElementSUBSET-1M1-of REALNUMBERSK2 st (p =HIDDENR1 x & q =HIDDENR1 y) & p <=XXREAL-0R1 q if x inHIDDENR3 REALNUMBERSK2 & y inHIDDENR3 REALNUMBERSK2 otherwise x =HIDDENR1 -inftyXXREAL-0K2 or y =HIDDENR1 +inftyXXREAL-0K1"
proof
(*compatibility*)
  show "(x inHIDDENR3 REALNUMBERSK2 & y inHIDDENR3 REALNUMBERSK2 implies (x <=XXREAL-3R1 y iff ( ex p be ElementSUBSET-1M1-of REALNUMBERSK2 st  ex q be ElementSUBSET-1M1-of REALNUMBERSK2 st (p =HIDDENR1 x & q =HIDDENR1 y) & p <=XXREAL-0R1 q))) & ( not (x inHIDDENR3 REALNUMBERSK2 & y inHIDDENR3 REALNUMBERSK2) implies (x <=XXREAL-3R1 y iff x =HIDDENR1 -inftyXXREAL-0K2 or y =HIDDENR1 +inftyXXREAL-0K1))"
sorry
(*consistency*)
  show " True "
     sorry
qed "sorry"

mtheorem xxreal_3_cl_1:
"cluster  non realXREAL-0V1\<bar>positiveXXREAL-0V2 for ExtRealXXREAL-0M1"
proof
(*existence*)
  show " ex it be ExtRealXXREAL-0M1 st it be  non realXREAL-0V1\<bar>positiveXXREAL-0V2"
sorry
qed "sorry"

mtheorem xxreal_3_cl_2:
"cluster  non realXREAL-0V1\<bar>negativeXXREAL-0V3 for ExtRealXXREAL-0M1"
proof
(*existence*)
  show " ex it be ExtRealXXREAL-0M1 st it be  non realXREAL-0V1\<bar>negativeXXREAL-0V3"
sorry
qed "sorry"

mtheorem xxreal_3_th_1:
" for x be  non realXREAL-0V1\<bar>positiveXXREAL-0V2\<bar>ExtRealXXREAL-0M1 holds x =HIDDENR1 +inftyXXREAL-0K1"
sorry

mtheorem xxreal_3_th_2:
" for x be  non realXREAL-0V1\<bar>negativeXXREAL-0V3\<bar>ExtRealXXREAL-0M1 holds x =HIDDENR1 -inftyXXREAL-0K2"
sorry

mtheorem xxreal_3_cl_3:
"cluster  non realXREAL-0V1\<bar> non negativeXXREAL-0V3 also-is positiveXXREAL-0V2 for ExtRealXXREAL-0M1"
proof
(*coherence*)
  show " for it be ExtRealXXREAL-0M1 holds it be  non realXREAL-0V1\<bar> non negativeXXREAL-0V3 implies it be positiveXXREAL-0V2"
     sorry
qed "sorry"

mtheorem xxreal_3_cl_4:
"cluster  non realXREAL-0V1\<bar> non positiveXXREAL-0V2 also-is negativeXXREAL-0V3 for ExtRealXXREAL-0M1"
proof
(*coherence*)
  show " for it be ExtRealXXREAL-0M1 holds it be  non realXREAL-0V1\<bar> non positiveXXREAL-0V2 implies it be negativeXXREAL-0V3"
     sorry
qed "sorry"

mtheorem xxreal_3_th_3:
" for x be ExtRealXXREAL-0M1 holds  for z be ExtRealXXREAL-0M1 holds x <XXREAL-0R3 z implies ( ex y be RealXREAL-0M1 st x <XXREAL-0R3 y & y <XXREAL-0R3 z)"
sorry

(*begin*)
mdef xxreal_3_def_2 (" _ +XXREAL-3K1  _ " [132,132]132 ) where
  mlet "x be ExtRealXXREAL-0M1", "y be ExtRealXXREAL-0M1"
"func x +XXREAL-3K1 y \<rightarrow> ExtRealXXREAL-0M1 means
  \<lambda>it.  ex a be ComplexXCMPLX-0M1 st  ex b be ComplexXCMPLX-0M1 st (x =HIDDENR1 a & y =HIDDENR1 b) & it =HIDDENR1 a +XCMPLX-0K2 b if x be realXREAL-0V1 & y be realXREAL-0V1,
  \<lambda>it. it =HIDDENR1 +inftyXXREAL-0K1 if x =HIDDENR1 +inftyXXREAL-0K1 & y <>HIDDENR2 -inftyXXREAL-0K2 or y =HIDDENR1 +inftyXXREAL-0K1 & x <>HIDDENR2 -inftyXXREAL-0K2,
  \<lambda>it. it =HIDDENR1 -inftyXXREAL-0K2 if x =HIDDENR1 -inftyXXREAL-0K2 & y <>HIDDENR2 +inftyXXREAL-0K1 or y =HIDDENR1 -inftyXXREAL-0K2 & x <>HIDDENR2 +inftyXXREAL-0K1 otherwise \<lambda>it. it =HIDDENR1 0NUMBERSK6"
proof-
  (*existence*)
    show "(x be realXREAL-0V1 & y be realXREAL-0V1 implies ( ex it be ExtRealXXREAL-0M1 st  ex a be ComplexXCMPLX-0M1 st  ex b be ComplexXCMPLX-0M1 st (x =HIDDENR1 a & y =HIDDENR1 b) & it =HIDDENR1 a +XCMPLX-0K2 b)) & ((x =HIDDENR1 +inftyXXREAL-0K1 & y <>HIDDENR2 -inftyXXREAL-0K2 or y =HIDDENR1 +inftyXXREAL-0K1 & x <>HIDDENR2 -inftyXXREAL-0K2 implies ( ex it be ExtRealXXREAL-0M1 st it =HIDDENR1 +inftyXXREAL-0K1)) & ((x =HIDDENR1 -inftyXXREAL-0K2 & y <>HIDDENR2 +inftyXXREAL-0K1 or y =HIDDENR1 -inftyXXREAL-0K2 & x <>HIDDENR2 +inftyXXREAL-0K1 implies ( ex it be ExtRealXXREAL-0M1 st it =HIDDENR1 -inftyXXREAL-0K2)) & ( not (x be realXREAL-0V1 & y be realXREAL-0V1) & ( not (x =HIDDENR1 +inftyXXREAL-0K1 & y <>HIDDENR2 -inftyXXREAL-0K2 or y =HIDDENR1 +inftyXXREAL-0K1 & x <>HIDDENR2 -inftyXXREAL-0K2) &  not (x =HIDDENR1 -inftyXXREAL-0K2 & y <>HIDDENR2 +inftyXXREAL-0K1 or y =HIDDENR1 -inftyXXREAL-0K2 & x <>HIDDENR2 +inftyXXREAL-0K1)) implies ( ex it be ExtRealXXREAL-0M1 st it =HIDDENR1 0NUMBERSK6))))"
sorry
  (*uniqueness*)
    show " for it1 be ExtRealXXREAL-0M1 holds  for it2 be ExtRealXXREAL-0M1 holds (x be realXREAL-0V1 & y be realXREAL-0V1 implies (( ex a be ComplexXCMPLX-0M1 st  ex b be ComplexXCMPLX-0M1 st (x =HIDDENR1 a & y =HIDDENR1 b) & it1 =HIDDENR1 a +XCMPLX-0K2 b) & ( ex a be ComplexXCMPLX-0M1 st  ex b be ComplexXCMPLX-0M1 st (x =HIDDENR1 a & y =HIDDENR1 b) & it2 =HIDDENR1 a +XCMPLX-0K2 b) implies it1 =HIDDENR1 it2)) & ((x =HIDDENR1 +inftyXXREAL-0K1 & y <>HIDDENR2 -inftyXXREAL-0K2 or y =HIDDENR1 +inftyXXREAL-0K1 & x <>HIDDENR2 -inftyXXREAL-0K2 implies (it1 =HIDDENR1 +inftyXXREAL-0K1 & it2 =HIDDENR1 +inftyXXREAL-0K1 implies it1 =HIDDENR1 it2)) & ((x =HIDDENR1 -inftyXXREAL-0K2 & y <>HIDDENR2 +inftyXXREAL-0K1 or y =HIDDENR1 -inftyXXREAL-0K2 & x <>HIDDENR2 +inftyXXREAL-0K1 implies (it1 =HIDDENR1 -inftyXXREAL-0K2 & it2 =HIDDENR1 -inftyXXREAL-0K2 implies it1 =HIDDENR1 it2)) & ( not (x be realXREAL-0V1 & y be realXREAL-0V1) & ( not (x =HIDDENR1 +inftyXXREAL-0K1 & y <>HIDDENR2 -inftyXXREAL-0K2 or y =HIDDENR1 +inftyXXREAL-0K1 & x <>HIDDENR2 -inftyXXREAL-0K2) &  not (x =HIDDENR1 -inftyXXREAL-0K2 & y <>HIDDENR2 +inftyXXREAL-0K1 or y =HIDDENR1 -inftyXXREAL-0K2 & x <>HIDDENR2 +inftyXXREAL-0K1)) implies (it1 =HIDDENR1 0NUMBERSK6 & it2 =HIDDENR1 0NUMBERSK6 implies it1 =HIDDENR1 it2))))"
       sorry
  (*consistency*)
    show " for it be ExtRealXXREAL-0M1 holds (((x be realXREAL-0V1 & y be realXREAL-0V1) & (x =HIDDENR1 +inftyXXREAL-0K1 & y <>HIDDENR2 -inftyXXREAL-0K2 or y =HIDDENR1 +inftyXXREAL-0K1 & x <>HIDDENR2 -inftyXXREAL-0K2) implies (( ex a be ComplexXCMPLX-0M1 st  ex b be ComplexXCMPLX-0M1 st (x =HIDDENR1 a & y =HIDDENR1 b) & it =HIDDENR1 a +XCMPLX-0K2 b) iff it =HIDDENR1 +inftyXXREAL-0K1)) & ((x be realXREAL-0V1 & y be realXREAL-0V1) & (x =HIDDENR1 -inftyXXREAL-0K2 & y <>HIDDENR2 +inftyXXREAL-0K1 or y =HIDDENR1 -inftyXXREAL-0K2 & x <>HIDDENR2 +inftyXXREAL-0K1) implies (( ex a be ComplexXCMPLX-0M1 st  ex b be ComplexXCMPLX-0M1 st (x =HIDDENR1 a & y =HIDDENR1 b) & it =HIDDENR1 a +XCMPLX-0K2 b) iff it =HIDDENR1 -inftyXXREAL-0K2))) & ((x =HIDDENR1 +inftyXXREAL-0K1 & y <>HIDDENR2 -inftyXXREAL-0K2 or y =HIDDENR1 +inftyXXREAL-0K1 & x <>HIDDENR2 -inftyXXREAL-0K2) & (x =HIDDENR1 -inftyXXREAL-0K2 & y <>HIDDENR2 +inftyXXREAL-0K1 or y =HIDDENR1 -inftyXXREAL-0K2 & x <>HIDDENR2 +inftyXXREAL-0K1) implies (it =HIDDENR1 +inftyXXREAL-0K1 iff it =HIDDENR1 -inftyXXREAL-0K2))"
       sorry
qed "sorry"

mtheorem XXREAL_3K1_commutativity:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds x +XXREAL-3K1 y =HIDDENR1 y +XXREAL-3K1 x"
sorry

mdef xxreal_3_def_3 ("-XXREAL-3K2  _ " [132]132 ) where
  mlet "x be ExtRealXXREAL-0M1"
"func -XXREAL-3K2 x \<rightarrow> ExtRealXXREAL-0M1 means
  \<lambda>it.  ex a be ComplexXCMPLX-0M1 st x =HIDDENR1 a & it =HIDDENR1 -XCMPLX-0K4 a if x be realXREAL-0V1,
  \<lambda>it. it =HIDDENR1 -inftyXXREAL-0K2 if x =HIDDENR1 +inftyXXREAL-0K1 otherwise \<lambda>it. it =HIDDENR1 +inftyXXREAL-0K1"
proof-
  (*existence*)
    show "(x be realXREAL-0V1 implies ( ex it be ExtRealXXREAL-0M1 st  ex a be ComplexXCMPLX-0M1 st x =HIDDENR1 a & it =HIDDENR1 -XCMPLX-0K4 a)) & ((x =HIDDENR1 +inftyXXREAL-0K1 implies ( ex it be ExtRealXXREAL-0M1 st it =HIDDENR1 -inftyXXREAL-0K2)) & ( not x be realXREAL-0V1 &  not x =HIDDENR1 +inftyXXREAL-0K1 implies ( ex it be ExtRealXXREAL-0M1 st it =HIDDENR1 +inftyXXREAL-0K1)))"
sorry
  (*uniqueness*)
    show " for it1 be ExtRealXXREAL-0M1 holds  for it2 be ExtRealXXREAL-0M1 holds (x be realXREAL-0V1 implies (( ex a be ComplexXCMPLX-0M1 st x =HIDDENR1 a & it1 =HIDDENR1 -XCMPLX-0K4 a) & ( ex a be ComplexXCMPLX-0M1 st x =HIDDENR1 a & it2 =HIDDENR1 -XCMPLX-0K4 a) implies it1 =HIDDENR1 it2)) & ((x =HIDDENR1 +inftyXXREAL-0K1 implies (it1 =HIDDENR1 -inftyXXREAL-0K2 & it2 =HIDDENR1 -inftyXXREAL-0K2 implies it1 =HIDDENR1 it2)) & ( not x be realXREAL-0V1 &  not x =HIDDENR1 +inftyXXREAL-0K1 implies (it1 =HIDDENR1 +inftyXXREAL-0K1 & it2 =HIDDENR1 +inftyXXREAL-0K1 implies it1 =HIDDENR1 it2)))"
       sorry
  (*consistency*)
    show " for it be ExtRealXXREAL-0M1 holds x be realXREAL-0V1 & x =HIDDENR1 +inftyXXREAL-0K1 implies (( ex a be ComplexXCMPLX-0M1 st x =HIDDENR1 a & it =HIDDENR1 -XCMPLX-0K4 a) iff it =HIDDENR1 -inftyXXREAL-0K2)"
       sorry
qed "sorry"

mtheorem XXREAL_3K2_involutiveness:
" for x be ExtRealXXREAL-0M1 holds -XXREAL-3K2 (-XXREAL-3K2 x) =HIDDENR1 x"
sorry

mdef xxreal_3_def_4 (" _ -XXREAL-3K3  _ " [132,132]132 ) where
  mlet "x be ExtRealXXREAL-0M1", "y be ExtRealXXREAL-0M1"
"func x -XXREAL-3K3 y \<rightarrow> ExtRealXXREAL-0M1 equals
  x +XXREAL-3K1 (-XXREAL-3K2 y)"
proof-
  (*coherence*)
    show "x +XXREAL-3K1 (-XXREAL-3K2 y) be ExtRealXXREAL-0M1"
       sorry
qed "sorry"

mtheorem xxreal_3_ident_1:
  mlet "x be RealXREAL-0M1", "y be RealXREAL-0M1", "a be ComplexXCMPLX-0M1", "b be ComplexXCMPLX-0M1"
"identify x +XXREAL-3K1 y with a +XCMPLX-0K2 b when x =HIDDENR1 a & y =HIDDENR1 b"
proof
(*compatibility*)
  show "x =HIDDENR1 a & y =HIDDENR1 b implies x +XXREAL-3K1 y =HIDDENR1 a +XCMPLX-0K2 b"
    using xxreal_3_def_2 sorry
qed "sorry"

mtheorem xxreal_3_ident_2:
  mlet "x be RealXREAL-0M1", "a be ComplexXCMPLX-0M1"
"identify -XXREAL-3K2 x with -XCMPLX-0K4 a when x =HIDDENR1 a"
proof
(*compatibility*)
  show "x =HIDDENR1 a implies -XXREAL-3K2 x =HIDDENR1 -XCMPLX-0K4 a"
    using xxreal_3_def_3 sorry
qed "sorry"

mtheorem xxreal_3_cl_5:
  mlet "r be RealXREAL-0M1"
"cluster -XXREAL-3K2 r as-term-is realXREAL-0V1"
proof
(*coherence*)
  show "-XXREAL-3K2 r be realXREAL-0V1"
     sorry
qed "sorry"

mtheorem xxreal_3_cl_6:
  mlet "r be RealXREAL-0M1", "s be RealXREAL-0M1"
"cluster r +XXREAL-3K1 s as-term-is realXREAL-0V1"
proof
(*coherence*)
  show "r +XXREAL-3K1 s be realXREAL-0V1"
     sorry
qed "sorry"

mtheorem xxreal_3_cl_7:
  mlet "r be RealXREAL-0M1", "s be RealXREAL-0M1"
"cluster r -XXREAL-3K3 s as-term-is realXREAL-0V1"
proof
(*coherence*)
  show "r -XXREAL-3K3 s be realXREAL-0V1"
     sorry
qed "sorry"

mtheorem xxreal_3_cl_8:
  mlet "x be RealXREAL-0M1", "y be  non realXREAL-0V1\<bar>ExtRealXXREAL-0M1"
"cluster x +XXREAL-3K1 y as-term-is  non realXREAL-0V1 for objectHIDDENM1"
proof
(*coherence*)
  show " for it be objectHIDDENM1 holds it =HIDDENR1 x +XXREAL-3K1 y implies it be  non realXREAL-0V1"
sorry
qed "sorry"

mtheorem xxreal_3_cl_9:
  mlet "x be  non realXREAL-0V1\<bar>positiveXXREAL-0V2\<bar>ExtRealXXREAL-0M1", "y be  non realXREAL-0V1\<bar>positiveXXREAL-0V2\<bar>ExtRealXXREAL-0M1"
"cluster x +XXREAL-3K1 y as-term-is  non realXREAL-0V1"
proof
(*coherence*)
  show "x +XXREAL-3K1 y be  non realXREAL-0V1"
sorry
qed "sorry"

mtheorem xxreal_3_cl_10:
  mlet "x be  non realXREAL-0V1\<bar>negativeXXREAL-0V3\<bar>ExtRealXXREAL-0M1", "y be  non realXREAL-0V1\<bar>negativeXXREAL-0V3\<bar>ExtRealXXREAL-0M1"
"cluster x +XXREAL-3K1 y as-term-is  non realXREAL-0V1"
proof
(*coherence*)
  show "x +XXREAL-3K1 y be  non realXREAL-0V1"
sorry
qed "sorry"

mtheorem xxreal_3_cl_11:
  mlet "x be  non realXREAL-0V1\<bar>negativeXXREAL-0V3\<bar>ExtRealXXREAL-0M1", "y be  non realXREAL-0V1\<bar>positiveXXREAL-0V2\<bar>ExtRealXXREAL-0M1"
"cluster x +XXREAL-3K1 y as-term-is zeroORDINAL1V8"
proof
(*coherence*)
  show "x +XXREAL-3K1 y be zeroORDINAL1V8"
sorry
qed "sorry"

mtheorem xxreal_3_ident_3:
  mlet "x be RealXREAL-0M1", "y be RealXREAL-0M1", "a be ComplexXCMPLX-0M1", "b be ComplexXCMPLX-0M1"
"identify x -XXREAL-3K3 y with a -XCMPLX-0K6 b when x =HIDDENR1 a & y =HIDDENR1 b"
proof
(*compatibility*)
  show "x =HIDDENR1 a & y =HIDDENR1 b implies x -XXREAL-3K3 y =HIDDENR1 a -XCMPLX-0K6 b"
     sorry
qed "sorry"

mtheorem xxreal_3_th_4:
" for x be ExtRealXXREAL-0M1 holds x +XXREAL-3K1 0NUMBERSK6 =HIDDENR1 x"
sorry

mtheorem xxreal_3_th_5:
"-XXREAL-3K2 -inftyXXREAL-0K2 =HIDDENR1 +inftyXXREAL-0K1"
  using xxreal_3_def_3 sorry

mtheorem xxreal_3_th_6:
"-XXREAL-3K2 +inftyXXREAL-0K1 =HIDDENR1 -inftyXXREAL-0K2"
  using xxreal_3_def_3 sorry

mlemma xxreal_3_lm_1:
"+inftyXXREAL-0K1 +XXREAL-3K1 +inftyXXREAL-0K1 =HIDDENR1 +inftyXXREAL-0K1"
  using xxreal_3_def_2 sorry

mlemma xxreal_3_lm_2:
"-inftyXXREAL-0K2 +XXREAL-3K1 -inftyXXREAL-0K2 =HIDDENR1 -inftyXXREAL-0K2"
  using xxreal_3_def_2 sorry

mtheorem xxreal_3_th_7:
" for x be ExtRealXXREAL-0M1 holds x +XXREAL-3K1 (-XXREAL-3K2 x) =HIDDENR1 0NUMBERSK6"
sorry

mtheorem xxreal_3_th_8:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds x +XXREAL-3K1 y =HIDDENR1 0NUMBERSK6 implies x =HIDDENR1 -XXREAL-3K2 y"
sorry

mlemma xxreal_3_lm_3:
" for x be ExtRealXXREAL-0M1 holds -XXREAL-3K2 x inHIDDENR3 REALNUMBERSK2 iff x inHIDDENR3 REALNUMBERSK2"
sorry

mlemma xxreal_3_lm_4:
"-XXREAL-3K2 (+inftyXXREAL-0K1 +XXREAL-3K1 -inftyXXREAL-0K2) =HIDDENR1 (-XXREAL-3K2 -inftyXXREAL-0K2)-XXREAL-3K3 +inftyXXREAL-0K1"
sorry

mlemma xxreal_3_lm_5:
"-XXREAL-3K2 +inftyXXREAL-0K1 =HIDDENR1 -inftyXXREAL-0K2"
  using xxreal_3_def_3 sorry

mlemma xxreal_3_lm_6:
" for x be ExtRealXXREAL-0M1 holds x inHIDDENR3 REALNUMBERSK2 implies -XXREAL-3K2 (x +XXREAL-3K1 +inftyXXREAL-0K1) =HIDDENR1 (-XXREAL-3K2 +inftyXXREAL-0K1)+XXREAL-3K1 (-XXREAL-3K2 x)"
sorry

mlemma xxreal_3_lm_7:
" for x be ExtRealXXREAL-0M1 holds x inHIDDENR3 REALNUMBERSK2 implies -XXREAL-3K2 (x +XXREAL-3K1 -inftyXXREAL-0K2) =HIDDENR1 (-XXREAL-3K2 -inftyXXREAL-0K2)+XXREAL-3K1 (-XXREAL-3K2 x)"
sorry

mtheorem xxreal_3_th_9:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds -XXREAL-3K2 (x +XXREAL-3K1 y) =HIDDENR1 (-XXREAL-3K2 x)+XXREAL-3K1 (-XXREAL-3K2 y)"
sorry

reserve f, g for "ExtRealXXREAL-0M1"
mtheorem xxreal_3_th_10:
" for f be ExtRealXXREAL-0M1 holds  for g be ExtRealXXREAL-0M1 holds -XXREAL-3K2 f =HIDDENR1 -XXREAL-3K2 g implies f =HIDDENR1 g"
sorry

mlemma xxreal_3_lm_8:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds x +XXREAL-3K1 y =HIDDENR1 +inftyXXREAL-0K1 implies x =HIDDENR1 +inftyXXREAL-0K1 or y =HIDDENR1 +inftyXXREAL-0K1"
sorry

mlemma xxreal_3_lm_9:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds x +XXREAL-3K1 y =HIDDENR1 -inftyXXREAL-0K2 implies x =HIDDENR1 -inftyXXREAL-0K2 or y =HIDDENR1 -inftyXXREAL-0K2"
sorry

mtheorem xxreal_3_th_11:
" for r be RealXREAL-0M1 holds  for f be ExtRealXXREAL-0M1 holds  for g be ExtRealXXREAL-0M1 holds r +XXREAL-3K1 f =HIDDENR1 r +XXREAL-3K1 g implies f =HIDDENR1 g"
sorry

mtheorem xxreal_3_th_12:
" for r be RealXREAL-0M1 holds  for f be ExtRealXXREAL-0M1 holds  for g be ExtRealXXREAL-0M1 holds r -XXREAL-3K3 f =HIDDENR1 r -XXREAL-3K3 g implies f =HIDDENR1 g"
sorry

mtheorem xxreal_3_th_13:
" for x be ExtRealXXREAL-0M1 holds x <>HIDDENR2 +inftyXXREAL-0K1 implies +inftyXXREAL-0K1 -XXREAL-3K3 x =HIDDENR1 +inftyXXREAL-0K1 & x -XXREAL-3K3 +inftyXXREAL-0K1 =HIDDENR1 -inftyXXREAL-0K2"
sorry

mtheorem xxreal_3_th_14:
" for x be ExtRealXXREAL-0M1 holds x <>HIDDENR2 -inftyXXREAL-0K2 implies -inftyXXREAL-0K2 -XXREAL-3K3 x =HIDDENR1 -inftyXXREAL-0K2 & x -XXREAL-3K3 -inftyXXREAL-0K2 =HIDDENR1 +inftyXXREAL-0K1"
sorry

mtheorem xxreal_3_th_15:
" for x be ExtRealXXREAL-0M1 holds x -XXREAL-3K3 0NUMBERSK6 =HIDDENR1 x"
sorry

mtheorem xxreal_3_th_16:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds x +XXREAL-3K1 y =HIDDENR1 +inftyXXREAL-0K1 implies x =HIDDENR1 +inftyXXREAL-0K1 or y =HIDDENR1 +inftyXXREAL-0K1"
  using xxreal_3_lm_8 sorry

mtheorem xxreal_3_th_17:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds x +XXREAL-3K1 y =HIDDENR1 -inftyXXREAL-0K2 implies x =HIDDENR1 -inftyXXREAL-0K2 or y =HIDDENR1 -inftyXXREAL-0K2"
  using xxreal_3_lm_9 sorry

mtheorem xxreal_3_th_18:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds x -XXREAL-3K3 y =HIDDENR1 +inftyXXREAL-0K1 implies x =HIDDENR1 +inftyXXREAL-0K1 or y =HIDDENR1 -inftyXXREAL-0K2"
sorry

mtheorem xxreal_3_th_19:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds x -XXREAL-3K3 y =HIDDENR1 -inftyXXREAL-0K2 implies x =HIDDENR1 -inftyXXREAL-0K2 or y =HIDDENR1 +inftyXXREAL-0K1"
sorry

mtheorem xxreal_3_th_20:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds  not (x =HIDDENR1 +inftyXXREAL-0K1 & y =HIDDENR1 -inftyXXREAL-0K2 or x =HIDDENR1 -inftyXXREAL-0K2 & y =HIDDENR1 +inftyXXREAL-0K1) & x +XXREAL-3K1 y inHIDDENR3 REALNUMBERSK2 implies x inHIDDENR3 REALNUMBERSK2 & y inHIDDENR3 REALNUMBERSK2"
sorry

mtheorem xxreal_3_th_21:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds  not (x =HIDDENR1 +inftyXXREAL-0K1 & y =HIDDENR1 +inftyXXREAL-0K1 or x =HIDDENR1 -inftyXXREAL-0K2 & y =HIDDENR1 -inftyXXREAL-0K2) & x -XXREAL-3K3 y inHIDDENR3 REALNUMBERSK2 implies x inHIDDENR3 REALNUMBERSK2 & y inHIDDENR3 REALNUMBERSK2"
sorry

mtheorem xxreal_3_th_22:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds x be realXREAL-0V1 implies (y -XXREAL-3K3 x)+XXREAL-3K1 x =HIDDENR1 y & (y +XXREAL-3K1 x)-XXREAL-3K3 x =HIDDENR1 y"
sorry

mtheorem xxreal_3_th_23:
" for x be ExtRealXXREAL-0M1 holds (x =HIDDENR1 +inftyXXREAL-0K1 iff -XXREAL-3K2 x =HIDDENR1 -inftyXXREAL-0K2) & (x =HIDDENR1 -inftyXXREAL-0K2 iff -XXREAL-3K2 x =HIDDENR1 +inftyXXREAL-0K1)"
sorry

mtheorem xxreal_3_th_24:
" for x be ExtRealXXREAL-0M1 holds  for z be ExtRealXXREAL-0M1 holds z be realXREAL-0V1 implies x =HIDDENR1 (x +XXREAL-3K1 z)-XXREAL-3K3 z"
sorry

mlemma xxreal_3_lm_10:
"-XXREAL-3K2 +inftyXXREAL-0K1 =HIDDENR1 -inftyXXREAL-0K2"
  using xxreal_3_def_3 sorry

mlemma xxreal_3_lm_11:
" for x be ExtRealXXREAL-0M1 holds x inHIDDENR3 REALNUMBERSK2 implies -XXREAL-3K2 (x +XXREAL-3K1 -inftyXXREAL-0K2) =HIDDENR1 (-XXREAL-3K2 -inftyXXREAL-0K2)+XXREAL-3K1 (-XXREAL-3K2 x)"
sorry

mtheorem xxreal_3_th_25:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds -XXREAL-3K2 (x +XXREAL-3K1 y) =HIDDENR1 (-XXREAL-3K2 y)-XXREAL-3K3 x"
sorry

mtheorem xxreal_3_th_26:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds -XXREAL-3K2 (x -XXREAL-3K3 y) =HIDDENR1 (-XXREAL-3K2 x)+XXREAL-3K1 y & -XXREAL-3K2 (x -XXREAL-3K3 y) =HIDDENR1 y -XXREAL-3K3 x"
sorry

mtheorem xxreal_3_th_27:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds -XXREAL-3K2 ((-XXREAL-3K2 x)+XXREAL-3K1 y) =HIDDENR1 x -XXREAL-3K3 y & -XXREAL-3K2 ((-XXREAL-3K2 x)+XXREAL-3K1 y) =HIDDENR1 x +XXREAL-3K1 (-XXREAL-3K2 y)"
sorry

mtheorem xxreal_3_th_28:
" for y be ExtRealXXREAL-0M1 holds  for z be ExtRealXXREAL-0M1 holds 0NUMBERSK6 <=XXREAL-3R1 y & y <XXREAL-0R3 +inftyXXREAL-0K1 implies z =HIDDENR1 (z +XXREAL-3K1 y)-XXREAL-3K3 y"
sorry

mtheorem xxreal_3_th_29:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds  for z be ExtRealXXREAL-0M1 holds (( not (x =HIDDENR1 +inftyXXREAL-0K1 & y =HIDDENR1 -inftyXXREAL-0K2) &  not (x =HIDDENR1 -inftyXXREAL-0K2 & y =HIDDENR1 +inftyXXREAL-0K1)) &  not (y =HIDDENR1 +inftyXXREAL-0K1 & z =HIDDENR1 -inftyXXREAL-0K2 or y =HIDDENR1 -inftyXXREAL-0K2 & z =HIDDENR1 +inftyXXREAL-0K1)) &  not (x =HIDDENR1 +inftyXXREAL-0K1 & z =HIDDENR1 -inftyXXREAL-0K2 or x =HIDDENR1 -inftyXXREAL-0K2 & z =HIDDENR1 +inftyXXREAL-0K1) implies (x +XXREAL-3K1 y)+XXREAL-3K1 z =HIDDENR1 x +XXREAL-3K1 (y +XXREAL-3K1 z)"
sorry

mtheorem xxreal_3_th_30:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds  for z be ExtRealXXREAL-0M1 holds (((( not (x =HIDDENR1 +inftyXXREAL-0K1 & y =HIDDENR1 -inftyXXREAL-0K2) &  not (x =HIDDENR1 -inftyXXREAL-0K2 & y =HIDDENR1 +inftyXXREAL-0K1)) &  not (y =HIDDENR1 +inftyXXREAL-0K1 & z =HIDDENR1 +inftyXXREAL-0K1)) &  not (y =HIDDENR1 -inftyXXREAL-0K2 & z =HIDDENR1 -inftyXXREAL-0K2)) &  not (x =HIDDENR1 +inftyXXREAL-0K1 & z =HIDDENR1 +inftyXXREAL-0K1)) &  not (x =HIDDENR1 -inftyXXREAL-0K2 & z =HIDDENR1 -inftyXXREAL-0K2) implies (x +XXREAL-3K1 y)-XXREAL-3K3 z =HIDDENR1 x +XXREAL-3K1 (y -XXREAL-3K3 z)"
sorry

mtheorem xxreal_3_th_31:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds  for z be ExtRealXXREAL-0M1 holds (((( not (x =HIDDENR1 +inftyXXREAL-0K1 & y =HIDDENR1 +inftyXXREAL-0K1) &  not (x =HIDDENR1 -inftyXXREAL-0K2 & y =HIDDENR1 -inftyXXREAL-0K2)) &  not (y =HIDDENR1 +inftyXXREAL-0K1 & z =HIDDENR1 -inftyXXREAL-0K2)) &  not (y =HIDDENR1 -inftyXXREAL-0K2 & z =HIDDENR1 +inftyXXREAL-0K1)) &  not (x =HIDDENR1 +inftyXXREAL-0K1 & z =HIDDENR1 +inftyXXREAL-0K1)) &  not (x =HIDDENR1 -inftyXXREAL-0K2 & z =HIDDENR1 -inftyXXREAL-0K2) implies (x -XXREAL-3K3 y)-XXREAL-3K3 z =HIDDENR1 x -XXREAL-3K3 (y +XXREAL-3K1 z)"
sorry

mtheorem xxreal_3_th_32:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds  for z be ExtRealXXREAL-0M1 holds (((( not (x =HIDDENR1 +inftyXXREAL-0K1 & y =HIDDENR1 +inftyXXREAL-0K1) &  not (x =HIDDENR1 -inftyXXREAL-0K2 & y =HIDDENR1 -inftyXXREAL-0K2)) &  not (y =HIDDENR1 +inftyXXREAL-0K1 & z =HIDDENR1 +inftyXXREAL-0K1)) &  not (y =HIDDENR1 -inftyXXREAL-0K2 & z =HIDDENR1 -inftyXXREAL-0K2)) &  not (x =HIDDENR1 +inftyXXREAL-0K1 & z =HIDDENR1 -inftyXXREAL-0K2)) &  not (x =HIDDENR1 -inftyXXREAL-0K2 & z =HIDDENR1 +inftyXXREAL-0K1) implies (x -XXREAL-3K3 y)+XXREAL-3K1 z =HIDDENR1 x -XXREAL-3K3 (y -XXREAL-3K3 z)"
sorry

mtheorem xxreal_3_th_33:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds  for z be ExtRealXXREAL-0M1 holds z be realXREAL-0V1 implies (z +XXREAL-3K1 x)-XXREAL-3K3 (z +XXREAL-3K1 y) =HIDDENR1 x -XXREAL-3K3 y"
sorry

mtheorem xxreal_3_th_34:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds  for z be ExtRealXXREAL-0M1 holds y be realXREAL-0V1 implies (z -XXREAL-3K3 y)+XXREAL-3K1 (y -XXREAL-3K3 x) =HIDDENR1 z -XXREAL-3K3 x"
sorry

(*begin*)
mlemma xxreal_3_lm_12:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds  for z be ExtRealXXREAL-0M1 holds x <=XXREAL-3R1 y implies x +XXREAL-3K1 z <=XXREAL-3R1 y +XXREAL-3K1 z"
sorry

mlemma xxreal_3_lm_13:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds x >=XXREAL-0R2 0NUMBERSK6 & y >XXREAL-0R4 0NUMBERSK6 implies x +XXREAL-3K1 y >XXREAL-0R4 0NUMBERSK6"
sorry

mlemma xxreal_3_lm_14:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds x <=XXREAL-3R1 0NUMBERSK6 & y <XXREAL-0R3 0NUMBERSK6 implies x +XXREAL-3K1 y <XXREAL-0R3 0NUMBERSK6"
sorry

mtheorem xxreal_3_cl_12:
  mlet "x be  non negativeXXREAL-0V3\<bar>ExtRealXXREAL-0M1", "y be  non negativeXXREAL-0V3\<bar>ExtRealXXREAL-0M1"
"cluster x +XXREAL-3K1 y as-term-is  non negativeXXREAL-0V3"
proof
(*coherence*)
  show "x +XXREAL-3K1 y be  non negativeXXREAL-0V3"
sorry
qed "sorry"

mtheorem xxreal_3_cl_13:
  mlet "x be  non positiveXXREAL-0V2\<bar>ExtRealXXREAL-0M1", "y be  non positiveXXREAL-0V2\<bar>ExtRealXXREAL-0M1"
"cluster x +XXREAL-3K1 y as-term-is  non positiveXXREAL-0V2"
proof
(*coherence*)
  show "x +XXREAL-3K1 y be  non positiveXXREAL-0V2"
sorry
qed "sorry"

mtheorem xxreal_3_cl_14:
  mlet "x be positiveXXREAL-0V2\<bar>ExtRealXXREAL-0M1", "y be  non negativeXXREAL-0V3\<bar>ExtRealXXREAL-0M1"
"cluster x +XXREAL-3K1 y as-term-is positiveXXREAL-0V2"
proof
(*coherence*)
  show "x +XXREAL-3K1 y be positiveXXREAL-0V2"
    using xxreal_3_lm_13 sorry
qed "sorry"

mtheorem xxreal_3_cl_15:
  mlet "x be positiveXXREAL-0V2\<bar>ExtRealXXREAL-0M1", "y be  non negativeXXREAL-0V3\<bar>ExtRealXXREAL-0M1"
"cluster y +XXREAL-3K1 x as-term-is positiveXXREAL-0V2"
proof
(*coherence*)
  show "y +XXREAL-3K1 x be positiveXXREAL-0V2"
     sorry
qed "sorry"

mtheorem xxreal_3_cl_16:
  mlet "x be negativeXXREAL-0V3\<bar>ExtRealXXREAL-0M1", "y be  non positiveXXREAL-0V2\<bar>ExtRealXXREAL-0M1"
"cluster x +XXREAL-3K1 y as-term-is negativeXXREAL-0V3"
proof
(*coherence*)
  show "x +XXREAL-3K1 y be negativeXXREAL-0V3"
    using xxreal_3_lm_14 sorry
qed "sorry"

mtheorem xxreal_3_cl_17:
  mlet "x be negativeXXREAL-0V3\<bar>ExtRealXXREAL-0M1", "y be  non positiveXXREAL-0V2\<bar>ExtRealXXREAL-0M1"
"cluster y +XXREAL-3K1 x as-term-is negativeXXREAL-0V3"
proof
(*coherence*)
  show "y +XXREAL-3K1 x be negativeXXREAL-0V3"
     sorry
qed "sorry"

mtheorem xxreal_3_cl_18:
  mlet "x be  non positiveXXREAL-0V2\<bar>ExtRealXXREAL-0M1"
"cluster -XXREAL-3K2 x as-term-is  non negativeXXREAL-0V3"
proof
(*coherence*)
  show "-XXREAL-3K2 x be  non negativeXXREAL-0V3"
sorry
qed "sorry"

mtheorem xxreal_3_cl_19:
  mlet "x be  non negativeXXREAL-0V3\<bar>ExtRealXXREAL-0M1"
"cluster -XXREAL-3K2 x as-term-is  non positiveXXREAL-0V2"
proof
(*coherence*)
  show "-XXREAL-3K2 x be  non positiveXXREAL-0V2"
sorry
qed "sorry"

mtheorem xxreal_3_cl_20:
  mlet "x be positiveXXREAL-0V2\<bar>ExtRealXXREAL-0M1"
"cluster -XXREAL-3K2 x as-term-is negativeXXREAL-0V3"
proof
(*coherence*)
  show "-XXREAL-3K2 x be negativeXXREAL-0V3"
sorry
qed "sorry"

mtheorem xxreal_3_cl_21:
  mlet "x be negativeXXREAL-0V3\<bar>ExtRealXXREAL-0M1"
"cluster -XXREAL-3K2 x as-term-is positiveXXREAL-0V2"
proof
(*coherence*)
  show "-XXREAL-3K2 x be positiveXXREAL-0V2"
sorry
qed "sorry"

mtheorem xxreal_3_cl_22:
  mlet "x be  non negativeXXREAL-0V3\<bar>ExtRealXXREAL-0M1", "y be  non positiveXXREAL-0V2\<bar>ExtRealXXREAL-0M1"
"cluster x -XXREAL-3K3 y as-term-is  non negativeXXREAL-0V3"
proof
(*coherence*)
  show "x -XXREAL-3K3 y be  non negativeXXREAL-0V3"
     sorry
qed "sorry"

mtheorem xxreal_3_cl_23:
  mlet "x be  non negativeXXREAL-0V3\<bar>ExtRealXXREAL-0M1", "y be  non positiveXXREAL-0V2\<bar>ExtRealXXREAL-0M1"
"cluster y -XXREAL-3K3 x as-term-is  non positiveXXREAL-0V2"
proof
(*coherence*)
  show "y -XXREAL-3K3 x be  non positiveXXREAL-0V2"
     sorry
qed "sorry"

mtheorem xxreal_3_cl_24:
  mlet "x be positiveXXREAL-0V2\<bar>ExtRealXXREAL-0M1", "y be  non positiveXXREAL-0V2\<bar>ExtRealXXREAL-0M1"
"cluster x -XXREAL-3K3 y as-term-is positiveXXREAL-0V2"
proof
(*coherence*)
  show "x -XXREAL-3K3 y be positiveXXREAL-0V2"
     sorry
qed "sorry"

mtheorem xxreal_3_cl_25:
  mlet "x be positiveXXREAL-0V2\<bar>ExtRealXXREAL-0M1", "y be  non positiveXXREAL-0V2\<bar>ExtRealXXREAL-0M1"
"cluster y -XXREAL-3K3 x as-term-is negativeXXREAL-0V3"
proof
(*coherence*)
  show "y -XXREAL-3K3 x be negativeXXREAL-0V3"
     sorry
qed "sorry"

mtheorem xxreal_3_cl_26:
  mlet "x be negativeXXREAL-0V3\<bar>ExtRealXXREAL-0M1", "y be  non negativeXXREAL-0V3\<bar>ExtRealXXREAL-0M1"
"cluster x -XXREAL-3K3 y as-term-is negativeXXREAL-0V3"
proof
(*coherence*)
  show "x -XXREAL-3K3 y be negativeXXREAL-0V3"
     sorry
qed "sorry"

mtheorem xxreal_3_cl_27:
  mlet "x be negativeXXREAL-0V3\<bar>ExtRealXXREAL-0M1", "y be  non negativeXXREAL-0V3\<bar>ExtRealXXREAL-0M1"
"cluster y -XXREAL-3K3 x as-term-is positiveXXREAL-0V2"
proof
(*coherence*)
  show "y -XXREAL-3K3 x be positiveXXREAL-0V2"
     sorry
qed "sorry"

mlemma xxreal_3_lm_15:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds x <=XXREAL-3R1 y implies -XXREAL-3K2 y <=XXREAL-3R1 -XXREAL-3K2 x"
sorry

mtheorem xxreal_3_th_35:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds  for z be ExtRealXXREAL-0M1 holds x <=XXREAL-3R1 y implies x +XXREAL-3K1 z <=XXREAL-3R1 y +XXREAL-3K1 z"
  using xxreal_3_lm_12 sorry

mtheorem xxreal_3_th_36:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds  for z be ExtRealXXREAL-0M1 holds  for w be ExtRealXXREAL-0M1 holds x <=XXREAL-3R1 y & z <=XXREAL-3R1 w implies x +XXREAL-3K1 z <=XXREAL-3R1 y +XXREAL-3K1 w"
sorry

mtheorem xxreal_3_th_37:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds  for z be ExtRealXXREAL-0M1 holds  for w be ExtRealXXREAL-0M1 holds x <=XXREAL-3R1 y & z <=XXREAL-3R1 w implies x -XXREAL-3K3 w <=XXREAL-3R1 y -XXREAL-3K3 z"
sorry

mtheorem xxreal_3_th_38:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds x <=XXREAL-3R1 y iff -XXREAL-3K2 y <=XXREAL-3R1 -XXREAL-3K2 x"
sorry

mtheorem xxreal_3_th_39:
" for x be ExtRealXXREAL-0M1 holds  for z be ExtRealXXREAL-0M1 holds 0NUMBERSK6 <=XXREAL-3R1 z implies x <=XXREAL-3R1 x +XXREAL-3K1 z"
sorry

mtheorem xxreal_3_th_40:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds x <=XXREAL-3R1 y implies y -XXREAL-3K3 x >=XXREAL-0R2 0NUMBERSK6"
sorry

mtheorem xxreal_3_th_41:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds  for z be ExtRealXXREAL-0M1 holds (z =HIDDENR1 -inftyXXREAL-0K2 & y =HIDDENR1 +inftyXXREAL-0K1 implies x <=XXREAL-3R1 0NUMBERSK6) & (z =HIDDENR1 +inftyXXREAL-0K1 & y =HIDDENR1 -inftyXXREAL-0K2 implies x <=XXREAL-3R1 0NUMBERSK6) implies (x -XXREAL-3K3 y <=XXREAL-3R1 z implies x <=XXREAL-3R1 z +XXREAL-3K1 y)"
sorry

mtheorem xxreal_3_th_42:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds  for z be ExtRealXXREAL-0M1 holds (x =HIDDENR1 +inftyXXREAL-0K1 & y =HIDDENR1 +inftyXXREAL-0K1 implies 0NUMBERSK6 <=XXREAL-3R1 z) & (x =HIDDENR1 -inftyXXREAL-0K2 & y =HIDDENR1 -inftyXXREAL-0K2 implies 0NUMBERSK6 <=XXREAL-3R1 z) implies (x <=XXREAL-3R1 z +XXREAL-3K1 y implies x -XXREAL-3K3 y <=XXREAL-3R1 z)"
sorry

mtheorem xxreal_3_th_43:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds  for z be ExtRealXXREAL-0M1 holds z inHIDDENR3 REALNUMBERSK2 & x <XXREAL-0R3 y implies x +XXREAL-3K1 z <XXREAL-0R3 y +XXREAL-3K1 z & x -XXREAL-3K3 z <XXREAL-0R3 y -XXREAL-3K3 z"
sorry

mtheorem xxreal_3_th_44:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds  for z be ExtRealXXREAL-0M1 holds (0NUMBERSK6 <=XXREAL-3R1 x & 0NUMBERSK6 <=XXREAL-3R1 y) & 0NUMBERSK6 <=XXREAL-3R1 z implies (x +XXREAL-3K1 y)+XXREAL-3K1 z =HIDDENR1 x +XXREAL-3K1 (y +XXREAL-3K1 z)"
sorry

mtheorem xxreal_3_th_45:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds  for z be ExtRealXXREAL-0M1 holds x be realXREAL-0V1 implies (y +XXREAL-3K1 x <=XXREAL-3R1 z iff y <=XXREAL-3R1 z -XXREAL-3K3 x)"
sorry

mtheorem xxreal_3_th_46:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds 0NUMBERSK6 <XXREAL-0R3 x & x <XXREAL-0R3 y implies 0NUMBERSK6 <XXREAL-0R3 y -XXREAL-3K3 x"
sorry

mlemma xxreal_3_lm_16:
"0NUMBERSK6 inHIDDENR3 REALNUMBERSK2"
  using xreal_0_def_1 sorry

mtheorem xxreal_3_th_47:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds  for z be ExtRealXXREAL-0M1 holds (0NUMBERSK6 <=XXREAL-3R1 x & 0NUMBERSK6 <=XXREAL-3R1 z) & z +XXREAL-3K1 x <XXREAL-0R3 y implies z <XXREAL-0R3 y -XXREAL-3K3 x"
sorry

mtheorem xxreal_3_th_48:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds  for z be ExtRealXXREAL-0M1 holds (0NUMBERSK6 <=XXREAL-3R1 x & 0NUMBERSK6 <=XXREAL-3R1 z) & z +XXREAL-3K1 x <XXREAL-0R3 y implies z <=XXREAL-3R1 y"
sorry

mtheorem xxreal_3_th_49:
" for x be ExtRealXXREAL-0M1 holds  for z be ExtRealXXREAL-0M1 holds 0NUMBERSK6 <=XXREAL-3R1 x & x <XXREAL-0R3 z implies ( ex y be RealXREAL-0M1 st 0NUMBERSK6 <XXREAL-0R3 y & x +XXREAL-3K1 y <XXREAL-0R3 z)"
sorry

mtheorem xxreal_3_th_50:
" for x be ExtRealXXREAL-0M1 holds 0NUMBERSK6 <XXREAL-0R3 x implies ( ex y be RealXREAL-0M1 st 0NUMBERSK6 <XXREAL-0R3 y & y +XXREAL-3K1 y <XXREAL-0R3 x)"
sorry

mtheorem xxreal_3_th_51:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds (x <XXREAL-0R3 y & x <XXREAL-0R3 +inftyXXREAL-0K1) & -inftyXXREAL-0K2 <XXREAL-0R3 y implies 0NUMBERSK6 <XXREAL-0R3 y -XXREAL-3K3 x"
sorry

mtheorem xxreal_3_th_52:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds  for z be ExtRealXXREAL-0M1 holds  not (x =HIDDENR1 +inftyXXREAL-0K1 & y =HIDDENR1 -inftyXXREAL-0K2 or x =HIDDENR1 -inftyXXREAL-0K2 & y =HIDDENR1 +inftyXXREAL-0K1) & x +XXREAL-3K1 y <XXREAL-0R3 z implies ((x <>HIDDENR2 +inftyXXREAL-0K1 & y <>HIDDENR2 +inftyXXREAL-0K1) & z <>HIDDENR2 -inftyXXREAL-0K2) & x <XXREAL-0R3 z -XXREAL-3K3 y"
sorry

mtheorem xxreal_3_th_53:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds  for z be ExtRealXXREAL-0M1 holds  not (z =HIDDENR1 +inftyXXREAL-0K1 & y =HIDDENR1 +inftyXXREAL-0K1 or z =HIDDENR1 -inftyXXREAL-0K2 & y =HIDDENR1 -inftyXXREAL-0K2) & x <XXREAL-0R3 z -XXREAL-3K3 y implies ((x <>HIDDENR2 +inftyXXREAL-0K1 & y <>HIDDENR2 +inftyXXREAL-0K1) & z <>HIDDENR2 -inftyXXREAL-0K2) & x +XXREAL-3K1 y <XXREAL-0R3 z"
sorry

mtheorem xxreal_3_th_54:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds  for z be ExtRealXXREAL-0M1 holds  not (x =HIDDENR1 +inftyXXREAL-0K1 & y =HIDDENR1 +inftyXXREAL-0K1 or x =HIDDENR1 -inftyXXREAL-0K2 & y =HIDDENR1 -inftyXXREAL-0K2) & x -XXREAL-3K3 y <XXREAL-0R3 z implies ((x <>HIDDENR2 +inftyXXREAL-0K1 & y <>HIDDENR2 -inftyXXREAL-0K2) & z <>HIDDENR2 -inftyXXREAL-0K2) & x <XXREAL-0R3 z +XXREAL-3K1 y"
sorry

mtheorem xxreal_3_th_55:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds  for z be ExtRealXXREAL-0M1 holds  not (z =HIDDENR1 +inftyXXREAL-0K1 & y =HIDDENR1 -inftyXXREAL-0K2 or z =HIDDENR1 -inftyXXREAL-0K2 & y =HIDDENR1 +inftyXXREAL-0K1) & x <XXREAL-0R3 z +XXREAL-3K1 y implies ((x <>HIDDENR2 +inftyXXREAL-0K1 & y <>HIDDENR2 -inftyXXREAL-0K2) & z <>HIDDENR2 -inftyXXREAL-0K2) & x -XXREAL-3K3 y <XXREAL-0R3 z"
sorry

mtheorem xxreal_3_th_56:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds  for z be ExtRealXXREAL-0M1 holds  not (((x =HIDDENR1 +inftyXXREAL-0K1 & y =HIDDENR1 -inftyXXREAL-0K2 or x =HIDDENR1 -inftyXXREAL-0K2 & y =HIDDENR1 +inftyXXREAL-0K1) or y =HIDDENR1 +inftyXXREAL-0K1 & z =HIDDENR1 +inftyXXREAL-0K1) or y =HIDDENR1 -inftyXXREAL-0K2 & z =HIDDENR1 -inftyXXREAL-0K2) & x +XXREAL-3K1 y <=XXREAL-3R1 z implies y <>HIDDENR2 +inftyXXREAL-0K1 & x <=XXREAL-3R1 z -XXREAL-3K3 y"
sorry

mtheorem xxreal_3_th_57:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds  for z be ExtRealXXREAL-0M1 holds (( not (x =HIDDENR1 +inftyXXREAL-0K1 & y =HIDDENR1 -inftyXXREAL-0K2) &  not (x =HIDDENR1 -inftyXXREAL-0K2 & y =HIDDENR1 +inftyXXREAL-0K1)) &  not (y =HIDDENR1 +inftyXXREAL-0K1 & z =HIDDENR1 +inftyXXREAL-0K1)) & x <=XXREAL-3R1 z -XXREAL-3K3 y implies y <>HIDDENR2 +inftyXXREAL-0K1 & x +XXREAL-3K1 y <=XXREAL-3R1 z"
sorry

mtheorem xxreal_3_th_58:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds  for z be ExtRealXXREAL-0M1 holds  not (((x =HIDDENR1 +inftyXXREAL-0K1 & y =HIDDENR1 +inftyXXREAL-0K1 or x =HIDDENR1 -inftyXXREAL-0K2 & y =HIDDENR1 -inftyXXREAL-0K2) or y =HIDDENR1 +inftyXXREAL-0K1 & z =HIDDENR1 -inftyXXREAL-0K2) or y =HIDDENR1 -inftyXXREAL-0K2 & z =HIDDENR1 +inftyXXREAL-0K1) & x -XXREAL-3K3 y <=XXREAL-3R1 z implies y <>HIDDENR2 -inftyXXREAL-0K2"
sorry

mtheorem xxreal_3_th_59:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds  for z be ExtRealXXREAL-0M1 holds ( not (x =HIDDENR1 -inftyXXREAL-0K2 & y =HIDDENR1 -inftyXXREAL-0K2) &  not (y =HIDDENR1 -inftyXXREAL-0K2 & z =HIDDENR1 +inftyXXREAL-0K1)) & x <=XXREAL-3R1 z +XXREAL-3K1 y implies y <>HIDDENR2 -inftyXXREAL-0K2"
sorry

mtheorem xxreal_3_th_60:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds (x <=XXREAL-3R1 -XXREAL-3K2 y implies y <=XXREAL-3R1 -XXREAL-3K2 x) & (-XXREAL-3K2 x <=XXREAL-3R1 y implies -XXREAL-3K2 y <=XXREAL-3R1 x)"
sorry

mtheorem xxreal_3_th_61:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds ( for e be RealXREAL-0M1 holds 0NUMBERSK6 <XXREAL-0R3 e implies x <XXREAL-0R3 y +XXREAL-3K1 e) implies x <=XXREAL-3R1 y"
sorry

reserve t for "ExtRealXXREAL-0M1"
mtheorem xxreal_3_th_62:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds  for t be ExtRealXXREAL-0M1 holds (t <>HIDDENR2 -inftyXXREAL-0K2 & t <>HIDDENR2 +inftyXXREAL-0K1) & x <XXREAL-0R3 y implies x +XXREAL-3K1 t <XXREAL-0R3 y +XXREAL-3K1 t"
sorry

mtheorem xxreal_3_th_63:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds  for t be ExtRealXXREAL-0M1 holds (t <>HIDDENR2 -inftyXXREAL-0K2 & t <>HIDDENR2 +inftyXXREAL-0K1) & x <XXREAL-0R3 y implies x -XXREAL-3K3 t <XXREAL-0R3 y -XXREAL-3K3 t"
sorry

mtheorem xxreal_3_th_64:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds  for z be ExtRealXXREAL-0M1 holds  for w be ExtRealXXREAL-0M1 holds x <XXREAL-0R3 y & w <XXREAL-0R3 z implies x +XXREAL-3K1 w <XXREAL-0R3 y +XXREAL-3K1 z"
sorry

mtheorem xxreal_3_th_65:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds  for z be ExtRealXXREAL-0M1 holds 0NUMBERSK6 <=XXREAL-3R1 x & z +XXREAL-3K1 x <=XXREAL-3R1 y implies z <=XXREAL-3R1 y"
sorry

(*begin*)
mdef xxreal_3_def_5 (" _ *XXREAL-3K4  _ " [164,164]164 ) where
  mlet "x be ExtRealXXREAL-0M1", "y be ExtRealXXREAL-0M1"
"func x *XXREAL-3K4 y \<rightarrow> ExtRealXXREAL-0M1 means
  \<lambda>it.  ex a be ComplexXCMPLX-0M1 st  ex b be ComplexXCMPLX-0M1 st (x =HIDDENR1 a & y =HIDDENR1 b) & it =HIDDENR1 a *XCMPLX-0K3 b if x be realXREAL-0V1 & y be realXREAL-0V1,
  \<lambda>it. it =HIDDENR1 +inftyXXREAL-0K1 if ( not x be realXREAL-0V1 or  not y be realXREAL-0V1) & (x be positiveXXREAL-0V2 & y be positiveXXREAL-0V2 or x be negativeXXREAL-0V3 & y be negativeXXREAL-0V3),
  \<lambda>it. it =HIDDENR1 -inftyXXREAL-0K2 if ( not x be realXREAL-0V1 or  not y be realXREAL-0V1) & (x be positiveXXREAL-0V2 & y be negativeXXREAL-0V3 or x be negativeXXREAL-0V3 & y be positiveXXREAL-0V2) otherwise \<lambda>it. it =HIDDENR1 0NUMBERSK6"
proof-
  (*existence*)
    show "(x be realXREAL-0V1 & y be realXREAL-0V1 implies ( ex it be ExtRealXXREAL-0M1 st  ex a be ComplexXCMPLX-0M1 st  ex b be ComplexXCMPLX-0M1 st (x =HIDDENR1 a & y =HIDDENR1 b) & it =HIDDENR1 a *XCMPLX-0K3 b)) & ((( not x be realXREAL-0V1 or  not y be realXREAL-0V1) & (x be positiveXXREAL-0V2 & y be positiveXXREAL-0V2 or x be negativeXXREAL-0V3 & y be negativeXXREAL-0V3) implies ( ex it be ExtRealXXREAL-0M1 st it =HIDDENR1 +inftyXXREAL-0K1)) & ((( not x be realXREAL-0V1 or  not y be realXREAL-0V1) & (x be positiveXXREAL-0V2 & y be negativeXXREAL-0V3 or x be negativeXXREAL-0V3 & y be positiveXXREAL-0V2) implies ( ex it be ExtRealXXREAL-0M1 st it =HIDDENR1 -inftyXXREAL-0K2)) & ( not (x be realXREAL-0V1 & y be realXREAL-0V1) & ( not (( not x be realXREAL-0V1 or  not y be realXREAL-0V1) & (x be positiveXXREAL-0V2 & y be positiveXXREAL-0V2 or x be negativeXXREAL-0V3 & y be negativeXXREAL-0V3)) &  not (( not x be realXREAL-0V1 or  not y be realXREAL-0V1) & (x be positiveXXREAL-0V2 & y be negativeXXREAL-0V3 or x be negativeXXREAL-0V3 & y be positiveXXREAL-0V2))) implies ( ex it be ExtRealXXREAL-0M1 st it =HIDDENR1 0NUMBERSK6))))"
sorry
  (*uniqueness*)
    show " for it1 be ExtRealXXREAL-0M1 holds  for it2 be ExtRealXXREAL-0M1 holds (x be realXREAL-0V1 & y be realXREAL-0V1 implies (( ex a be ComplexXCMPLX-0M1 st  ex b be ComplexXCMPLX-0M1 st (x =HIDDENR1 a & y =HIDDENR1 b) & it1 =HIDDENR1 a *XCMPLX-0K3 b) & ( ex a be ComplexXCMPLX-0M1 st  ex b be ComplexXCMPLX-0M1 st (x =HIDDENR1 a & y =HIDDENR1 b) & it2 =HIDDENR1 a *XCMPLX-0K3 b) implies it1 =HIDDENR1 it2)) & ((( not x be realXREAL-0V1 or  not y be realXREAL-0V1) & (x be positiveXXREAL-0V2 & y be positiveXXREAL-0V2 or x be negativeXXREAL-0V3 & y be negativeXXREAL-0V3) implies (it1 =HIDDENR1 +inftyXXREAL-0K1 & it2 =HIDDENR1 +inftyXXREAL-0K1 implies it1 =HIDDENR1 it2)) & ((( not x be realXREAL-0V1 or  not y be realXREAL-0V1) & (x be positiveXXREAL-0V2 & y be negativeXXREAL-0V3 or x be negativeXXREAL-0V3 & y be positiveXXREAL-0V2) implies (it1 =HIDDENR1 -inftyXXREAL-0K2 & it2 =HIDDENR1 -inftyXXREAL-0K2 implies it1 =HIDDENR1 it2)) & ( not (x be realXREAL-0V1 & y be realXREAL-0V1) & ( not (( not x be realXREAL-0V1 or  not y be realXREAL-0V1) & (x be positiveXXREAL-0V2 & y be positiveXXREAL-0V2 or x be negativeXXREAL-0V3 & y be negativeXXREAL-0V3)) &  not (( not x be realXREAL-0V1 or  not y be realXREAL-0V1) & (x be positiveXXREAL-0V2 & y be negativeXXREAL-0V3 or x be negativeXXREAL-0V3 & y be positiveXXREAL-0V2))) implies (it1 =HIDDENR1 0NUMBERSK6 & it2 =HIDDENR1 0NUMBERSK6 implies it1 =HIDDENR1 it2))))"
       sorry
  (*consistency*)
    show " for it be ExtRealXXREAL-0M1 holds (((x be realXREAL-0V1 & y be realXREAL-0V1) & (( not x be realXREAL-0V1 or  not y be realXREAL-0V1) & (x be positiveXXREAL-0V2 & y be positiveXXREAL-0V2 or x be negativeXXREAL-0V3 & y be negativeXXREAL-0V3)) implies (( ex a be ComplexXCMPLX-0M1 st  ex b be ComplexXCMPLX-0M1 st (x =HIDDENR1 a & y =HIDDENR1 b) & it =HIDDENR1 a *XCMPLX-0K3 b) iff it =HIDDENR1 +inftyXXREAL-0K1)) & ((x be realXREAL-0V1 & y be realXREAL-0V1) & (( not x be realXREAL-0V1 or  not y be realXREAL-0V1) & (x be positiveXXREAL-0V2 & y be negativeXXREAL-0V3 or x be negativeXXREAL-0V3 & y be positiveXXREAL-0V2)) implies (( ex a be ComplexXCMPLX-0M1 st  ex b be ComplexXCMPLX-0M1 st (x =HIDDENR1 a & y =HIDDENR1 b) & it =HIDDENR1 a *XCMPLX-0K3 b) iff it =HIDDENR1 -inftyXXREAL-0K2))) & ((( not x be realXREAL-0V1 or  not y be realXREAL-0V1) & (x be positiveXXREAL-0V2 & y be positiveXXREAL-0V2 or x be negativeXXREAL-0V3 & y be negativeXXREAL-0V3)) & (( not x be realXREAL-0V1 or  not y be realXREAL-0V1) & (x be positiveXXREAL-0V2 & y be negativeXXREAL-0V3 or x be negativeXXREAL-0V3 & y be positiveXXREAL-0V2)) implies (it =HIDDENR1 +inftyXXREAL-0K1 iff it =HIDDENR1 -inftyXXREAL-0K2))"
       sorry
qed "sorry"

mtheorem XXREAL_3K4_commutativity:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds x *XXREAL-3K4 y =HIDDENR1 y *XXREAL-3K4 x"
sorry

mtheorem xxreal_3_ident_4:
  mlet "x be RealXREAL-0M1", "y be RealXREAL-0M1", "a be ComplexXCMPLX-0M1", "b be ComplexXCMPLX-0M1"
"identify x *XXREAL-3K4 y with a *XCMPLX-0K3 b when x =HIDDENR1 a & y =HIDDENR1 b"
proof
(*compatibility*)
  show "x =HIDDENR1 a & y =HIDDENR1 b implies x *XXREAL-3K4 y =HIDDENR1 a *XCMPLX-0K3 b"
    using xxreal_3_def_5 sorry
qed "sorry"

mdef xxreal_3_def_6 (" _ \<inverse>XXREAL-3K5" [228]228 ) where
  mlet "x be ExtRealXXREAL-0M1"
"func x \<inverse>XXREAL-3K5 \<rightarrow> ExtRealXXREAL-0M1 means
  \<lambda>it.  ex a be ComplexXCMPLX-0M1 st x =HIDDENR1 a & it =HIDDENR1 a \<inverse>XCMPLX-0K5 if x be realXREAL-0V1 otherwise \<lambda>it. it =HIDDENR1 0NUMBERSK6"
proof-
  (*existence*)
    show "(x be realXREAL-0V1 implies ( ex it be ExtRealXXREAL-0M1 st  ex a be ComplexXCMPLX-0M1 st x =HIDDENR1 a & it =HIDDENR1 a \<inverse>XCMPLX-0K5)) & ( not x be realXREAL-0V1 implies ( ex it be ExtRealXXREAL-0M1 st it =HIDDENR1 0NUMBERSK6))"
sorry
  (*uniqueness*)
    show " for it1 be ExtRealXXREAL-0M1 holds  for it2 be ExtRealXXREAL-0M1 holds (x be realXREAL-0V1 implies (( ex a be ComplexXCMPLX-0M1 st x =HIDDENR1 a & it1 =HIDDENR1 a \<inverse>XCMPLX-0K5) & ( ex a be ComplexXCMPLX-0M1 st x =HIDDENR1 a & it2 =HIDDENR1 a \<inverse>XCMPLX-0K5) implies it1 =HIDDENR1 it2)) & ( not x be realXREAL-0V1 implies (it1 =HIDDENR1 0NUMBERSK6 & it2 =HIDDENR1 0NUMBERSK6 implies it1 =HIDDENR1 it2))"
       sorry
  (*consistency*)
    show " for it be ExtRealXXREAL-0M1 holds  True "
       sorry
qed "sorry"

mtheorem xxreal_3_ident_5:
  mlet "x be RealXREAL-0M1", "a be ComplexXCMPLX-0M1"
"identify x \<inverse>XXREAL-3K5 with a \<inverse>XCMPLX-0K5 when x =HIDDENR1 a"
proof
(*compatibility*)
  show "x =HIDDENR1 a implies x \<inverse>XXREAL-3K5 =HIDDENR1 a \<inverse>XCMPLX-0K5"
    using xxreal_3_def_6 sorry
qed "sorry"

mdef xxreal_3_def_7 (" _ '/XXREAL-3K6  _ " [164,164]164 ) where
  mlet "x be ExtRealXXREAL-0M1", "y be ExtRealXXREAL-0M1"
"func x /XXREAL-3K6 y \<rightarrow> ExtRealXXREAL-0M1 equals
  x *XXREAL-3K4 y \<inverse>XXREAL-3K5"
proof-
  (*coherence*)
    show "x *XXREAL-3K4 y \<inverse>XXREAL-3K5 be ExtRealXXREAL-0M1"
       sorry
qed "sorry"

mtheorem xxreal_3_ident_6:
  mlet "x be RealXREAL-0M1", "y be RealXREAL-0M1", "a be ComplexXCMPLX-0M1", "b be ComplexXCMPLX-0M1"
"identify x /XXREAL-3K6 y with a /XCMPLX-0K7 b when x =HIDDENR1 a & y =HIDDENR1 b"
proof
(*compatibility*)
  show "x =HIDDENR1 a & y =HIDDENR1 b implies x /XXREAL-3K6 y =HIDDENR1 a /XCMPLX-0K7 b"
sorry
qed "sorry"

mlemma xxreal_3_lm_17:
" for x be ExtRealXXREAL-0M1 holds x *XXREAL-3K4 (0NUMBERSK6) =HIDDENR1 0NUMBERSK6"
sorry

mtheorem xxreal_3_cl_28:
  mlet "x be positiveXXREAL-0V2\<bar>ExtRealXXREAL-0M1", "y be negativeXXREAL-0V3\<bar>ExtRealXXREAL-0M1"
"cluster x *XXREAL-3K4 y as-term-is negativeXXREAL-0V3"
proof
(*coherence*)
  show "x *XXREAL-3K4 y be negativeXXREAL-0V3"
sorry
qed "sorry"

mtheorem xxreal_3_cl_29:
  mlet "x be negativeXXREAL-0V3\<bar>ExtRealXXREAL-0M1", "y be negativeXXREAL-0V3\<bar>ExtRealXXREAL-0M1"
"cluster x *XXREAL-3K4 y as-term-is positiveXXREAL-0V2"
proof
(*coherence*)
  show "x *XXREAL-3K4 y be positiveXXREAL-0V2"
sorry
qed "sorry"

mtheorem xxreal_3_cl_30:
  mlet "x be positiveXXREAL-0V2\<bar>ExtRealXXREAL-0M1", "y be positiveXXREAL-0V2\<bar>ExtRealXXREAL-0M1"
"cluster x *XXREAL-3K4 y as-term-is positiveXXREAL-0V2"
proof
(*coherence*)
  show "x *XXREAL-3K4 y be positiveXXREAL-0V2"
sorry
qed "sorry"

mtheorem xxreal_3_cl_31:
  mlet "x be  non positiveXXREAL-0V2\<bar>ExtRealXXREAL-0M1", "y be  non negativeXXREAL-0V3\<bar>ExtRealXXREAL-0M1"
"cluster x *XXREAL-3K4 y as-term-is  non positiveXXREAL-0V2"
proof
(*coherence*)
  show "x *XXREAL-3K4 y be  non positiveXXREAL-0V2"
sorry
qed "sorry"

mtheorem xxreal_3_cl_32:
  mlet "x be  non positiveXXREAL-0V2\<bar>ExtRealXXREAL-0M1", "y be  non positiveXXREAL-0V2\<bar>ExtRealXXREAL-0M1"
"cluster x *XXREAL-3K4 y as-term-is  non negativeXXREAL-0V3"
proof
(*coherence*)
  show "x *XXREAL-3K4 y be  non negativeXXREAL-0V3"
sorry
qed "sorry"

mtheorem xxreal_3_cl_33:
  mlet "x be  non negativeXXREAL-0V3\<bar>ExtRealXXREAL-0M1", "y be  non negativeXXREAL-0V3\<bar>ExtRealXXREAL-0M1"
"cluster x *XXREAL-3K4 y as-term-is  non negativeXXREAL-0V3"
proof
(*coherence*)
  show "x *XXREAL-3K4 y be  non negativeXXREAL-0V3"
sorry
qed "sorry"

mtheorem xxreal_3_cl_34:
  mlet "x be  non positiveXXREAL-0V2\<bar>ExtRealXXREAL-0M1"
"cluster x \<inverse>XXREAL-3K5 as-term-is  non positiveXXREAL-0V2"
proof
(*coherence*)
  show "x \<inverse>XXREAL-3K5 be  non positiveXXREAL-0V2"
sorry
qed "sorry"

mtheorem xxreal_3_cl_35:
  mlet "x be  non negativeXXREAL-0V3\<bar>ExtRealXXREAL-0M1"
"cluster x \<inverse>XXREAL-3K5 as-term-is  non negativeXXREAL-0V3"
proof
(*coherence*)
  show "x \<inverse>XXREAL-3K5 be  non negativeXXREAL-0V3"
sorry
qed "sorry"

mtheorem xxreal_3_cl_36:
  mlet "x be  non negativeXXREAL-0V3\<bar>ExtRealXXREAL-0M1", "y be  non positiveXXREAL-0V2\<bar>ExtRealXXREAL-0M1"
"cluster x /XXREAL-3K6 y as-term-is  non positiveXXREAL-0V2"
proof
(*coherence*)
  show "x /XXREAL-3K6 y be  non positiveXXREAL-0V2"
     sorry
qed "sorry"

mtheorem xxreal_3_cl_37:
  mlet "x be  non negativeXXREAL-0V3\<bar>ExtRealXXREAL-0M1", "y be  non positiveXXREAL-0V2\<bar>ExtRealXXREAL-0M1"
"cluster y /XXREAL-3K6 x as-term-is  non positiveXXREAL-0V2"
proof
(*coherence*)
  show "y /XXREAL-3K6 x be  non positiveXXREAL-0V2"
     sorry
qed "sorry"

mtheorem xxreal_3_cl_38:
  mlet "x be  non negativeXXREAL-0V3\<bar>ExtRealXXREAL-0M1", "y be  non negativeXXREAL-0V3\<bar>ExtRealXXREAL-0M1"
"cluster x /XXREAL-3K6 y as-term-is  non negativeXXREAL-0V3"
proof
(*coherence*)
  show "x /XXREAL-3K6 y be  non negativeXXREAL-0V3"
     sorry
qed "sorry"

mtheorem xxreal_3_cl_39:
  mlet "x be  non positiveXXREAL-0V2\<bar>ExtRealXXREAL-0M1", "y be  non positiveXXREAL-0V2\<bar>ExtRealXXREAL-0M1"
"cluster x /XXREAL-3K6 y as-term-is  non negativeXXREAL-0V3"
proof
(*coherence*)
  show "x /XXREAL-3K6 y be  non negativeXXREAL-0V3"
     sorry
qed "sorry"

mlemma xxreal_3_lm_18:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds  not x be realXREAL-0V1 & x *XXREAL-3K4 y =HIDDENR1 0NUMBERSK6 implies y =HIDDENR1 0NUMBERSK6"
sorry

mtheorem xxreal_3_cl_40:
  mlet "x be  non zeroORDINAL1V8\<bar>ExtRealXXREAL-0M1", "y be  non zeroORDINAL1V8\<bar>ExtRealXXREAL-0M1"
"cluster x *XXREAL-3K4 y as-term-is  non zeroORDINAL1V8"
proof
(*coherence*)
  show "x *XXREAL-3K4 y be  non zeroORDINAL1V8"
sorry
qed "sorry"

mtheorem xxreal_3_cl_41:
  mlet "x be zeroORDINAL1V8\<bar>ExtRealXXREAL-0M1", "y be ExtRealXXREAL-0M1"
"cluster x *XXREAL-3K4 y as-term-is zeroORDINAL1V8 for ExtRealXXREAL-0M1"
proof
(*coherence*)
  show " for it be ExtRealXXREAL-0M1 holds it =HIDDENR1 x *XXREAL-3K4 y implies it be zeroORDINAL1V8"
    using xxreal_3_lm_17 sorry
qed "sorry"

mlemma xxreal_3_lm_19:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds  for z be ExtRealXXREAL-0M1 holds x =HIDDENR1 0NUMBERSK6 implies x *XXREAL-3K4 (y *XXREAL-3K4 z) =HIDDENR1 (x *XXREAL-3K4 y)*XXREAL-3K4 z"
sorry

mlemma xxreal_3_lm_20:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds  for z be ExtRealXXREAL-0M1 holds y =HIDDENR1 0NUMBERSK6 implies x *XXREAL-3K4 (y *XXREAL-3K4 z) =HIDDENR1 (x *XXREAL-3K4 y)*XXREAL-3K4 z"
sorry

mlemma xxreal_3_lm_21:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds  for z be ExtRealXXREAL-0M1 holds  not y be realXREAL-0V1 implies x *XXREAL-3K4 (y *XXREAL-3K4 z) =HIDDENR1 (x *XXREAL-3K4 y)*XXREAL-3K4 z"
sorry

mlemma xxreal_3_lm_22:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds  for z be ExtRealXXREAL-0M1 holds  not x be realXREAL-0V1 implies x *XXREAL-3K4 (y *XXREAL-3K4 z) =HIDDENR1 (x *XXREAL-3K4 y)*XXREAL-3K4 z"
sorry

mtheorem xxreal_3_th_66:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds  for z be ExtRealXXREAL-0M1 holds x *XXREAL-3K4 (y *XXREAL-3K4 z) =HIDDENR1 (x *XXREAL-3K4 y)*XXREAL-3K4 z"
sorry

mtheorem xxreal_3_cl_42:
  mlet "r be RealXREAL-0M1"
"cluster r \<inverse>XXREAL-3K5 as-term-is realXREAL-0V1"
proof
(*coherence*)
  show "r \<inverse>XXREAL-3K5 be realXREAL-0V1"
     sorry
qed "sorry"

mtheorem xxreal_3_cl_43:
  mlet "r be RealXREAL-0M1", "s be RealXREAL-0M1"
"cluster r *XXREAL-3K4 s as-term-is realXREAL-0V1"
proof
(*coherence*)
  show "r *XXREAL-3K4 s be realXREAL-0V1"
     sorry
qed "sorry"

mtheorem xxreal_3_cl_44:
  mlet "r be RealXREAL-0M1", "s be RealXREAL-0M1"
"cluster r /XXREAL-3K6 s as-term-is realXREAL-0V1"
proof
(*coherence*)
  show "r /XXREAL-3K6 s be realXREAL-0V1"
     sorry
qed "sorry"

mtheorem xxreal_3_cl_45:
"cluster -inftyXXREAL-0K2 \<inverse>XXREAL-3K5 as-term-is zeroORDINAL1V8"
proof
(*coherence*)
  show "-inftyXXREAL-0K2 \<inverse>XXREAL-3K5 be zeroORDINAL1V8"
    using xxreal_3_def_6 sorry
qed "sorry"

mtheorem xxreal_3_cl_46:
"cluster +inftyXXREAL-0K1 \<inverse>XXREAL-3K5 as-term-is zeroORDINAL1V8"
proof
(*coherence*)
  show "+inftyXXREAL-0K1 \<inverse>XXREAL-3K5 be zeroORDINAL1V8"
    using xxreal_3_def_6 sorry
qed "sorry"

mtheorem xxreal_3_th_67:
" for f be ExtRealXXREAL-0M1 holds  for g be ExtRealXXREAL-0M1 holds (f *XXREAL-3K4 g)\<inverse>XXREAL-3K5 =HIDDENR1 f \<inverse>XXREAL-3K5 *XXREAL-3K4 g \<inverse>XXREAL-3K5"
sorry

mtheorem xxreal_3_th_68:
" for r be RealXREAL-0M1 holds  for f be ExtRealXXREAL-0M1 holds  for g be ExtRealXXREAL-0M1 holds r <>HIDDENR2 0NUMBERSK6 & r *XXREAL-3K4 f =HIDDENR1 r *XXREAL-3K4 g implies f =HIDDENR1 g"
sorry

mtheorem xxreal_3_th_69:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds (x <>HIDDENR2 +inftyXXREAL-0K1 & x <>HIDDENR2 -inftyXXREAL-0K2) & x *XXREAL-3K4 y =HIDDENR1 +inftyXXREAL-0K1 implies y =HIDDENR1 +inftyXXREAL-0K1 or y =HIDDENR1 -inftyXXREAL-0K2"
sorry

mtheorem xxreal_3_th_70:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds (x <>HIDDENR2 +inftyXXREAL-0K1 & x <>HIDDENR2 -inftyXXREAL-0K2) & x *XXREAL-3K4 y =HIDDENR1 -inftyXXREAL-0K2 implies y =HIDDENR1 +inftyXXREAL-0K1 or y =HIDDENR1 -inftyXXREAL-0K2"
sorry

mlemma xxreal_3_lm_23:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds x *XXREAL-3K4 y inHIDDENR3 REALNUMBERSK2 implies x inHIDDENR3 REALNUMBERSK2 & y inHIDDENR3 REALNUMBERSK2 or x *XXREAL-3K4 y =HIDDENR1 0NUMBERSK6"
sorry

mtheorem xxreal_3_th_71:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds  for z be ExtRealXXREAL-0M1 holds x <=XXREAL-3R1 y & 0NUMBERSK6 <=XXREAL-3R1 z implies x *XXREAL-3K4 z <=XXREAL-3R1 y *XXREAL-3K4 z"
sorry

mtheorem xxreal_3_th_72:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds  for z be ExtRealXXREAL-0M1 holds (x <XXREAL-0R3 y & 0NUMBERSK6 <XXREAL-0R3 z) & z <>HIDDENR2 +inftyXXREAL-0K1 implies x *XXREAL-3K4 z <XXREAL-0R3 y *XXREAL-3K4 z"
sorry

mtheorem xxreal_3_th_73:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds x *XXREAL-3K4 y inHIDDENR3 REALNUMBERSK2 implies x inHIDDENR3 REALNUMBERSK2 & y inHIDDENR3 REALNUMBERSK2 or x *XXREAL-3K4 y =HIDDENR1 0NUMBERSK6"
  using xxreal_3_lm_23 sorry

mtheorem xxreal_3_th_74:
"+inftyXXREAL-0K1 \<inverse>XXREAL-3K5 =HIDDENR1 0NUMBERSK6"
   sorry

mtheorem xxreal_3_th_75:
"-inftyXXREAL-0K2 \<inverse>XXREAL-3K5 =HIDDENR1 0NUMBERSK6"
   sorry

mtheorem xxreal_3_th_76:
" for x be ExtRealXXREAL-0M1 holds x /XXREAL-3K6 +inftyXXREAL-0K1 =HIDDENR1 0NUMBERSK6"
   sorry

mtheorem xxreal_3_th_77:
" for x be ExtRealXXREAL-0M1 holds x /XXREAL-3K6 -inftyXXREAL-0K2 =HIDDENR1 0NUMBERSK6"
   sorry

mtheorem xxreal_3_th_78:
" for x be ExtRealXXREAL-0M1 holds (x <>HIDDENR2 -inftyXXREAL-0K2 & x <>HIDDENR2 +inftyXXREAL-0K1) & x <>HIDDENR2 0NUMBERSK6 implies x /XXREAL-3K6 x =HIDDENR1 \<one>\<^sub>M"
sorry

mtheorem xxreal_3_th_79:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds  for z be ExtRealXXREAL-0M1 holds x <=XXREAL-3R1 y & 0NUMBERSK6 <XXREAL-0R3 z implies x /XXREAL-3K6 z <=XXREAL-3R1 y /XXREAL-3K6 z"
  using xxreal_3_th_71 sorry

mtheorem xxreal_3_th_80:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds  for z be ExtRealXXREAL-0M1 holds (x <XXREAL-0R3 y & 0NUMBERSK6 <XXREAL-0R3 z) & z <>HIDDENR2 +inftyXXREAL-0K1 implies x /XXREAL-3K6 z <XXREAL-0R3 y /XXREAL-3K6 z"
sorry

mtheorem xxreal_3_th_81:
" for x be ExtRealXXREAL-0M1 holds \<one>\<^sub>M *XXREAL-3K4 x =HIDDENR1 x"
sorry

mtheorem xxreal_3_th_82:
" for y be ExtRealXXREAL-0M1 holds y \<inverse>XXREAL-3K5 =HIDDENR1 0NUMBERSK6 implies (y =HIDDENR1 +inftyXXREAL-0K1 or y =HIDDENR1 -inftyXXREAL-0K2) or y =HIDDENR1 0NUMBERSK6"
sorry

mtheorem xxreal_3_th_83:
" for y be ExtRealXXREAL-0M1 holds 0NUMBERSK6 <XXREAL-0R3 y & y <>HIDDENR2 +inftyXXREAL-0K1 implies +inftyXXREAL-0K1 /XXREAL-3K6 y =HIDDENR1 +inftyXXREAL-0K1"
sorry

mtheorem xxreal_3_th_84:
" for y be ExtRealXXREAL-0M1 holds y <XXREAL-0R3 0NUMBERSK6 & -inftyXXREAL-0K2 <>HIDDENR2 y implies -inftyXXREAL-0K2 /XXREAL-3K6 y =HIDDENR1 +inftyXXREAL-0K1"
sorry

mtheorem xxreal_3_th_85:
" for y be ExtRealXXREAL-0M1 holds y <XXREAL-0R3 0NUMBERSK6 & -inftyXXREAL-0K2 <>HIDDENR2 y implies +inftyXXREAL-0K1 /XXREAL-3K6 y =HIDDENR1 -inftyXXREAL-0K2"
sorry

mtheorem xxreal_3_th_86:
" for y be ExtRealXXREAL-0M1 holds 0NUMBERSK6 <XXREAL-0R3 y & y <>HIDDENR2 +inftyXXREAL-0K1 implies -inftyXXREAL-0K2 /XXREAL-3K6 y =HIDDENR1 -inftyXXREAL-0K2"
sorry

mtheorem xxreal_3_th_87:
" for x be ExtRealXXREAL-0M1 holds (x <>HIDDENR2 +inftyXXREAL-0K1 & x <>HIDDENR2 -inftyXXREAL-0K2) & x <>HIDDENR2 0NUMBERSK6 implies x *XXREAL-3K4 (\<one>\<^sub>M /XXREAL-3K6 x) =HIDDENR1 \<one>\<^sub>M & (\<one>\<^sub>M /XXREAL-3K6 x)*XXREAL-3K4 x =HIDDENR1 \<one>\<^sub>M"
sorry

mtheorem xxreal_3_th_88:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds (-inftyXXREAL-0K2 <>HIDDENR2 y & y <>HIDDENR2 +inftyXXREAL-0K1) & y <>HIDDENR2 0NUMBERSK6 implies (x *XXREAL-3K4 y)/XXREAL-3K6 y =HIDDENR1 x & x *XXREAL-3K4 (y /XXREAL-3K6 y) =HIDDENR1 x"
sorry

mtheorem xxreal_3_th_89:
" for y be ExtRealXXREAL-0M1 holds +inftyXXREAL-0K1 *XXREAL-3K4 y <>HIDDENR2 \<one>\<^sub>M & -inftyXXREAL-0K2 *XXREAL-3K4 y <>HIDDENR2 \<one>\<^sub>M"
sorry

mtheorem xxreal_3_th_90:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds x *XXREAL-3K4 y <>HIDDENR2 +inftyXXREAL-0K1 & x *XXREAL-3K4 y <>HIDDENR2 -inftyXXREAL-0K2 implies x inHIDDENR3 REALNUMBERSK2 or y inHIDDENR3 REALNUMBERSK2"
sorry

(*begin*)
mtheorem xxreal_3_th_91:
" for x be ExtRealXXREAL-0M1 holds (-XXREAL-3K2 \<one>\<^sub>M)*XXREAL-3K4 x =HIDDENR1 -XXREAL-3K2 x"
sorry

mtheorem xxreal_3_th_92:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds -XXREAL-3K2 x *XXREAL-3K4 y =HIDDENR1 (-XXREAL-3K2 x)*XXREAL-3K4 y"
sorry

mtheorem xxreal_3_th_93:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds  for z be ExtRealXXREAL-0M1 holds y =HIDDENR1 -XXREAL-3K2 z implies x *XXREAL-3K4 (y +XXREAL-3K1 z) =HIDDENR1 x *XXREAL-3K4 y +XXREAL-3K1 x *XXREAL-3K4 z"
sorry

mtheorem xxreal_3_th_94:
" for x be ExtRealXXREAL-0M1 holds \<two>\<^sub>M *XXREAL-3K4 x =HIDDENR1 x +XXREAL-3K1 x"
sorry

mlemma xxreal_3_lm_24:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds x *XXREAL-3K4 (y +XXREAL-3K1 y) =HIDDENR1 x *XXREAL-3K4 y +XXREAL-3K1 x *XXREAL-3K4 y"
sorry

mlemma xxreal_3_lm_25:
" for x be ExtRealXXREAL-0M1 holds  for z be ExtRealXXREAL-0M1 holds x *XXREAL-3K4 (0NUMBERSK6 +XXREAL-3K1 z) =HIDDENR1 x *XXREAL-3K4 (0NUMBERSK6) +XXREAL-3K1 x *XXREAL-3K4 z"
sorry

mlemma xxreal_3_lm_26:
" for y be ExtRealXXREAL-0M1 holds  for z be ExtRealXXREAL-0M1 holds (0NUMBERSK6)*XXREAL-3K4 (y +XXREAL-3K1 z) =HIDDENR1 (0NUMBERSK6)*XXREAL-3K4 y +XXREAL-3K1 (0NUMBERSK6)*XXREAL-3K4 z"
   sorry

mlemma xxreal_3_lm_27:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds  for z be ExtRealXXREAL-0M1 holds x be realXREAL-0V1 & y be realXREAL-0V1 implies x *XXREAL-3K4 (y +XXREAL-3K1 z) =HIDDENR1 x *XXREAL-3K4 y +XXREAL-3K1 x *XXREAL-3K4 z"
sorry

mlemma xxreal_3_lm_28:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds  for z be ExtRealXXREAL-0M1 holds x be realXREAL-0V1 &  not y be realXREAL-0V1 implies x *XXREAL-3K4 (y +XXREAL-3K1 z) =HIDDENR1 x *XXREAL-3K4 y +XXREAL-3K1 x *XXREAL-3K4 z"
sorry

mtheorem xxreal_3_th_95:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds  for z be ExtRealXXREAL-0M1 holds x be realXREAL-0V1 implies x *XXREAL-3K4 (y +XXREAL-3K1 z) =HIDDENR1 x *XXREAL-3K4 y +XXREAL-3K1 x *XXREAL-3K4 z"
sorry

mtheorem xxreal_3_th_96:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds  for z be ExtRealXXREAL-0M1 holds y >=XXREAL-0R2 0NUMBERSK6 & z >=XXREAL-0R2 0NUMBERSK6 implies x *XXREAL-3K4 (y +XXREAL-3K1 z) =HIDDENR1 x *XXREAL-3K4 y +XXREAL-3K1 x *XXREAL-3K4 z"
sorry

mtheorem xxreal_3_th_97:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds  for z be ExtRealXXREAL-0M1 holds y <=XXREAL-3R1 0NUMBERSK6 & z <=XXREAL-3R1 0NUMBERSK6 implies x *XXREAL-3K4 (y +XXREAL-3K1 z) =HIDDENR1 x *XXREAL-3K4 y +XXREAL-3K1 x *XXREAL-3K4 z"
sorry

mtheorem xxreal_3_th_98:
" for x be ExtRealXXREAL-0M1 holds  for z be ExtRealXXREAL-0M1 holds x *XXREAL-3K4 (0NUMBERSK6 +XXREAL-3K1 z) =HIDDENR1 x *XXREAL-3K4 (0NUMBERSK6) +XXREAL-3K1 x *XXREAL-3K4 z"
  using xxreal_3_lm_25 sorry

mtheorem xxreal_3_th_99:
" for f be ExtRealXXREAL-0M1 holds (-XXREAL-3K2 f)\<inverse>XXREAL-3K5 =HIDDENR1 -XXREAL-3K2 f \<inverse>XXREAL-3K5"
sorry

mtheorem xxreal_3_th_100:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds  for z be ExtRealXXREAL-0M1 holds x be realXREAL-0V1 implies x *XXREAL-3K4 (y -XXREAL-3K3 z) =HIDDENR1 x *XXREAL-3K4 y -XXREAL-3K3 x *XXREAL-3K4 z"
sorry

mtheorem xxreal_3_th_101:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds  for z be ExtRealXXREAL-0M1 holds x <=XXREAL-3R1 y & z <=XXREAL-3R1 0NUMBERSK6 implies y *XXREAL-3K4 z <=XXREAL-3R1 x *XXREAL-3K4 z"
sorry

mtheorem xxreal_3_th_102:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds  for z be ExtRealXXREAL-0M1 holds (x <XXREAL-0R3 y & z <XXREAL-0R3 0NUMBERSK6) & z <>HIDDENR2 -inftyXXREAL-0K2 implies y *XXREAL-3K4 z <XXREAL-0R3 x *XXREAL-3K4 z"
sorry

mtheorem xxreal_3_th_103:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds  for z be ExtRealXXREAL-0M1 holds x <=XXREAL-3R1 y & z <XXREAL-0R3 0NUMBERSK6 implies y /XXREAL-3K6 z <=XXREAL-3R1 x /XXREAL-3K6 z"
  using xxreal_3_th_101 sorry

mtheorem xxreal_3_th_104:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds  for z be ExtRealXXREAL-0M1 holds (x <XXREAL-0R3 y & z <XXREAL-0R3 0NUMBERSK6) & z <>HIDDENR2 -inftyXXREAL-0K2 implies y /XXREAL-3K6 z <XXREAL-0R3 x /XXREAL-3K6 z"
sorry

mtheorem xxreal_3_th_105:
" for x be ExtRealXXREAL-0M1 holds x /XXREAL-3K6 \<two>\<^sub>M +XXREAL-3K1 x /XXREAL-3K6 \<two>\<^sub>M =HIDDENR1 x"
sorry

mtheorem xxreal_3_cl_47:
  mlet "x be NatORDINAL1M6", "y be NatORDINAL1M6"
"cluster x +XXREAL-3K1 y as-term-is naturalORDINAL1V7"
proof
(*coherence*)
  show "x +XXREAL-3K1 y be naturalORDINAL1V7"
     sorry
qed "sorry"

mtheorem xxreal_3_cl_48:
  mlet "x be NatORDINAL1M6", "y be NatORDINAL1M6"
"cluster x *XXREAL-3K4 y as-term-is naturalORDINAL1V7"
proof
(*coherence*)
  show "x *XXREAL-3K4 y be naturalORDINAL1V7"
     sorry
qed "sorry"

mtheorem xxreal_3_cl_49:
"cluster -XXREAL-3K2 \<one>\<^sub>M as-term-is dim-likeINT-1V2"
proof
(*coherence*)
  show "-XXREAL-3K2 \<one>\<^sub>M be dim-likeINT-1V2"
     sorry
qed "sorry"

mtheorem xxreal_3_cl_50:
  mlet "n be dim-likeINT-1V2\<bar>numberORDINAL1M2"
"cluster n +XXREAL-3K1 \<one>\<^sub>M as-term-is naturalORDINAL1V7"
proof
(*coherence*)
  show "n +XXREAL-3K1 \<one>\<^sub>M be naturalORDINAL1V7"
     sorry
qed "sorry"

end
