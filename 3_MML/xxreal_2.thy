theory xxreal_2
  imports setwiseo rat_1 xxreal_1 classes1
   "../mizar_extension/E_number"
begin
(*begin*)
theorem xxreal_2_sch_1:
  fixes mf0 nf0 Ff1 Pp1 
  assumes
[ty]: "mf0 be IntegerINT-1M1" and
  [ty]: "nf0 be IntegerINT-1M1" and
  [ty_func]: "\<And> x1. x1 be objectHIDDENM1 \<Longrightarrow> Ff1(x1) be objectHIDDENM1"
  shows "{Ff1(i) where i be ElementSUBSET-1M1-of INTINT-1K1 : (mf0 <=XXREAL-0R1 i & i <=XXREAL-0R1 nf0) & Pp1(i) } be finiteFINSET-1V1"
sorry

reserve x, y, z, r, s for "ExtRealXXREAL-0M1"
mdef xxreal_2_def_1 ("UpperBoundXXREAL-2M1-of  _ " [70]70 ) where
  mlet "X be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2"
"mode UpperBoundXXREAL-2M1-of X \<rightarrow> ExtRealXXREAL-0M1 means
  (\<lambda>it.  for x be ExtRealXXREAL-0M1 holds x inHIDDENR3 X implies x <=XXREAL-0R1 it)"
proof-
  (*existence*)
    show " ex it be ExtRealXXREAL-0M1 st  for x be ExtRealXXREAL-0M1 holds x inHIDDENR3 X implies x <=XXREAL-0R1 it"
sorry
qed "sorry"

mdef xxreal_2_def_2 ("LowerBoundXXREAL-2M2-of  _ " [70]70 ) where
  mlet "X be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2"
"mode LowerBoundXXREAL-2M2-of X \<rightarrow> ExtRealXXREAL-0M1 means
  (\<lambda>it.  for x be ExtRealXXREAL-0M1 holds x inHIDDENR3 X implies it <=XXREAL-0R1 x)"
proof-
  (*existence*)
    show " ex it be ExtRealXXREAL-0M1 st  for x be ExtRealXXREAL-0M1 holds x inHIDDENR3 X implies it <=XXREAL-0R1 x"
sorry
qed "sorry"

mdef xxreal_2_def_3 ("supXXREAL-2K1  _ " [300]300 ) where
  mlet "X be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2"
"func supXXREAL-2K1 X \<rightarrow> ExtRealXXREAL-0M1 means
  \<lambda>it. it be UpperBoundXXREAL-2M1-of X & ( for x be UpperBoundXXREAL-2M1-of X holds it <=XXREAL-0R1 x)"
proof-
  (*existence*)
    show " ex it be ExtRealXXREAL-0M1 st it be UpperBoundXXREAL-2M1-of X & ( for x be UpperBoundXXREAL-2M1-of X holds it <=XXREAL-0R1 x)"
sorry
  (*uniqueness*)
    show " for it1 be ExtRealXXREAL-0M1 holds  for it2 be ExtRealXXREAL-0M1 holds (it1 be UpperBoundXXREAL-2M1-of X & ( for x be UpperBoundXXREAL-2M1-of X holds it1 <=XXREAL-0R1 x)) & (it2 be UpperBoundXXREAL-2M1-of X & ( for x be UpperBoundXXREAL-2M1-of X holds it2 <=XXREAL-0R1 x)) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mdef xxreal_2_def_4 ("infXXREAL-2K2  _ " [228]228 ) where
  mlet "X be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2"
"func infXXREAL-2K2 X \<rightarrow> ExtRealXXREAL-0M1 means
  \<lambda>it. it be LowerBoundXXREAL-2M2-of X & ( for x be LowerBoundXXREAL-2M2-of X holds x <=XXREAL-0R1 it)"
proof-
  (*existence*)
    show " ex it be ExtRealXXREAL-0M1 st it be LowerBoundXXREAL-2M2-of X & ( for x be LowerBoundXXREAL-2M2-of X holds x <=XXREAL-0R1 it)"
sorry
  (*uniqueness*)
    show " for it1 be ExtRealXXREAL-0M1 holds  for it2 be ExtRealXXREAL-0M1 holds (it1 be LowerBoundXXREAL-2M2-of X & ( for x be LowerBoundXXREAL-2M2-of X holds x <=XXREAL-0R1 it1)) & (it2 be LowerBoundXXREAL-2M2-of X & ( for x be LowerBoundXXREAL-2M2-of X holds x <=XXREAL-0R1 it2)) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mdef xxreal_2_def_5 ("left-endXXREAL-2V1" 70 ) where
"attr left-endXXREAL-2V1 for ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 means
  (\<lambda>X. infXXREAL-2K2 X inHIDDENR3 X)"..

mdef xxreal_2_def_6 ("right-endXXREAL-2V2" 70 ) where
"attr right-endXXREAL-2V2 for ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 means
  (\<lambda>X. supXXREAL-2K1 X inHIDDENR3 X)"..

mtheorem xxreal_2_th_1:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds y be UpperBoundXXREAL-2M1-of {TARSKIK1 x} iff x <=XXREAL-0R1 y"
sorry

mtheorem xxreal_2_th_2:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds y be LowerBoundXXREAL-2M2-of {TARSKIK1 x} iff y <=XXREAL-0R1 x"
sorry

mlemma xxreal_2_lm_1:
" for x be ExtRealXXREAL-0M1 holds supXXREAL-2K1 {TARSKIK1 x} =HIDDENR1 x"
sorry

mlemma xxreal_2_lm_2:
" for x be ExtRealXXREAL-0M1 holds infXXREAL-2K2 {TARSKIK1 x} =HIDDENR1 x"
sorry

mtheorem xxreal_2_cl_1:
"cluster note-that ext-real-memberedMEMBEREDV2 for ElementSUBSET-1M1-of FinFINSUB-1K5 (ExtREALXXREAL-0K3)"
proof
(*coherence*)
  show " for it be ElementSUBSET-1M1-of FinFINSUB-1K5 (ExtREALXXREAL-0K3) holds it be ext-real-memberedMEMBEREDV2"
sorry
qed "sorry"

reserve A, B for "ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2"
mtheorem xxreal_2_th_3:
" for x be ExtRealXXREAL-0M1 holds  for A be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds x inHIDDENR3 A implies infXXREAL-2K2 A <=XXREAL-0R1 x"
sorry

mtheorem xxreal_2_th_4:
" for x be ExtRealXXREAL-0M1 holds  for A be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds x inHIDDENR3 A implies x <=XXREAL-0R1 supXXREAL-2K1 A"
sorry

mtheorem xxreal_2_th_5:
" for A be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for B be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds B c=MEMBEREDR2 A implies ( for x be LowerBoundXXREAL-2M2-of A holds x be LowerBoundXXREAL-2M2-of B)"
sorry

mtheorem xxreal_2_th_6:
" for A be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for B be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds B c=MEMBEREDR2 A implies ( for x be UpperBoundXXREAL-2M1-of A holds x be UpperBoundXXREAL-2M1-of B)"
sorry

mtheorem xxreal_2_th_7:
" for A be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for B be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for x be LowerBoundXXREAL-2M2-of A holds  for y be LowerBoundXXREAL-2M2-of B holds minXXREAL-0K4(x,y) be LowerBoundXXREAL-2M2-of A \\/XBOOLE-0K2 B"
sorry

mtheorem xxreal_2_th_8:
" for A be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for B be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for x be UpperBoundXXREAL-2M1-of A holds  for y be UpperBoundXXREAL-2M1-of B holds maxXXREAL-0K5(x,y) be UpperBoundXXREAL-2M1-of A \\/XBOOLE-0K2 B"
sorry

mtheorem xxreal_2_th_9:
" for A be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for B be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds infXXREAL-2K2 (A \\/XBOOLE-0K2 B) =HIDDENR1 minXXREAL-0K4(infXXREAL-2K2 A,infXXREAL-2K2 B)"
sorry

mtheorem xxreal_2_th_10:
" for A be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for B be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds supXXREAL-2K1 (A \\/XBOOLE-0K2 B) =HIDDENR1 maxXXREAL-0K5(supXXREAL-2K1 A,supXXREAL-2K1 B)"
sorry

mtheorem xxreal_2_cl_2:
"cluster finiteFINSET-1V1 also-is left-endXXREAL-2V1\<bar>right-endXXREAL-2V2 for  non emptyXBOOLE-0V1\<bar>ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2"
proof
(*coherence*)
  show " for it be  non emptyXBOOLE-0V1\<bar>ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds it be finiteFINSET-1V1 implies it be left-endXXREAL-2V1\<bar>right-endXXREAL-2V2"
sorry
qed "sorry"

mtheorem xxreal_2_cl_3:
"cluster note-that left-endXXREAL-2V1 for  non emptyXBOOLE-0V1\<bar>natural-memberedMEMBEREDV6\<bar>setHIDDENM2"
proof
(*coherence*)
  show " for it be  non emptyXBOOLE-0V1\<bar>natural-memberedMEMBEREDV6\<bar>setHIDDENM2 holds it be left-endXXREAL-2V1"
sorry
qed "sorry"

mtheorem xxreal_2_cl_4:
"cluster right-endXXREAL-2V2 for  non emptyXBOOLE-0V1\<bar>natural-memberedMEMBEREDV6\<bar>setHIDDENM2"
proof
(*existence*)
  show " ex it be  non emptyXBOOLE-0V1\<bar>natural-memberedMEMBEREDV6\<bar>setHIDDENM2 st it be right-endXXREAL-2V2"
sorry
qed "sorry"

abbreviation(input) XXREAL_2K3("minXXREAL-2K3  _ " [228]228) where
  "minXXREAL-2K3 X \<equiv> infXXREAL-2K2 X"

abbreviation(input) XXREAL_2K4("maxXXREAL-2K4  _ " [228]228) where
  "maxXXREAL-2K4 X \<equiv> supXXREAL-2K1 X"

abbreviation(input) XXREAL_2K5("minXXREAL-2K5  _ " [228]228) where
  "minXXREAL-2K5 X \<equiv> infXXREAL-2K2 X"

mtheorem xxreal_2_def_7:
  mlet "X be left-endXXREAL-2V1\<bar>ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2"
"redefine func minXXREAL-2K5 X \<rightarrow> ExtRealXXREAL-0M1 means
  \<lambda>it. it inHIDDENR3 X & ( for x be ExtRealXXREAL-0M1 holds x inHIDDENR3 X implies it <=XXREAL-0R1 x)"
proof
(*compatibility*)
  show " for it be ExtRealXXREAL-0M1 holds it =HIDDENR1 minXXREAL-2K5 X iff it inHIDDENR3 X & ( for x be ExtRealXXREAL-0M1 holds x inHIDDENR3 X implies it <=XXREAL-0R1 x)"
sorry
qed "sorry"

abbreviation(input) XXREAL_2K6("maxXXREAL-2K6  _ " [228]228) where
  "maxXXREAL-2K6 X \<equiv> supXXREAL-2K1 X"

mtheorem xxreal_2_def_8:
  mlet "X be right-endXXREAL-2V2\<bar>ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2"
"redefine func maxXXREAL-2K6 X \<rightarrow> ExtRealXXREAL-0M1 means
  \<lambda>it. it inHIDDENR3 X & ( for x be ExtRealXXREAL-0M1 holds x inHIDDENR3 X implies x <=XXREAL-0R1 it)"
proof
(*compatibility*)
  show " for it be ExtRealXXREAL-0M1 holds it =HIDDENR1 maxXXREAL-2K6 X iff it inHIDDENR3 X & ( for x be ExtRealXXREAL-0M1 holds x inHIDDENR3 X implies x <=XXREAL-0R1 it)"
sorry
qed "sorry"

mtheorem xxreal_2_th_11:
" for x be ExtRealXXREAL-0M1 holds maxXXREAL-2K6 {TARSKIK1 x} =HIDDENR1 x"
  using xxreal_2_lm_1 sorry

mlemma xxreal_2_lm_3:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds x <=XXREAL-0R1 y implies y be UpperBoundXXREAL-2M1-of {TARSKIK2 x,y }"
sorry

mlemma xxreal_2_lm_4:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds  for z be UpperBoundXXREAL-2M1-of {TARSKIK2 x,y } holds y <=XXREAL-0R1 z"
sorry

mtheorem xxreal_2_th_12:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds maxXXREAL-0K5(x,y) =HIDDENR1 maxXXREAL-2K6 {TARSKIK2 x,y }"
sorry

mtheorem xxreal_2_th_13:
" for x be ExtRealXXREAL-0M1 holds minXXREAL-2K5 {TARSKIK1 x} =HIDDENR1 x"
  using xxreal_2_lm_2 sorry

mlemma xxreal_2_lm_5:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds y <=XXREAL-0R1 x implies y be LowerBoundXXREAL-2M2-of {TARSKIK2 x,y }"
sorry

mlemma xxreal_2_lm_6:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds  for z be LowerBoundXXREAL-2M2-of {TARSKIK2 x,y } holds z <=XXREAL-0R1 y"
sorry

mtheorem xxreal_2_th_14:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds minXXREAL-2K5 {TARSKIK2 x,y } =HIDDENR1 minXXREAL-0K4(x,y)"
sorry

mdef xxreal_2_def_9 ("bounded-belowXXREAL-2V3" 70 ) where
"attr bounded-belowXXREAL-2V3 for ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 means
  (\<lambda>X.  ex r be RealXREAL-0M1 st r be LowerBoundXXREAL-2M2-of X)"..

mdef xxreal_2_def_10 ("bounded-aboveXXREAL-2V4" 70 ) where
"attr bounded-aboveXXREAL-2V4 for ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 means
  (\<lambda>X.  ex r be RealXREAL-0M1 st r be UpperBoundXXREAL-2M1-of X)"..

mtheorem xxreal_2_cl_5:
"cluster  non emptyXBOOLE-0V1\<bar>finiteFINSET-1V1\<bar>natural-memberedMEMBEREDV6 for setHIDDENM2"
proof
(*existence*)
  show " ex it be setHIDDENM2 st it be  non emptyXBOOLE-0V1\<bar>finiteFINSET-1V1\<bar>natural-memberedMEMBEREDV6"
sorry
qed "sorry"

mdef xxreal_2_def_11 ("real-boundedXXREAL-2V5" 70 ) where
"attr real-boundedXXREAL-2V5 for ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 means
  (\<lambda>X. X be bounded-belowXXREAL-2V3\<bar>bounded-aboveXXREAL-2V4)"..

mtheorem xxreal_2_cl_6:
"cluster real-boundedXXREAL-2V5 also-is bounded-aboveXXREAL-2V4\<bar>bounded-belowXXREAL-2V3 for ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2"
proof
(*coherence*)
  show " for it be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds it be real-boundedXXREAL-2V5 implies it be bounded-aboveXXREAL-2V4\<bar>bounded-belowXXREAL-2V3"
     sorry
qed "sorry"

mtheorem xxreal_2_cl_7:
"cluster bounded-aboveXXREAL-2V4\<bar>bounded-belowXXREAL-2V3 also-is real-boundedXXREAL-2V5 for ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2"
proof
(*coherence*)
  show " for it be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds it be bounded-aboveXXREAL-2V4\<bar>bounded-belowXXREAL-2V3 implies it be real-boundedXXREAL-2V5"
     sorry
qed "sorry"

mtheorem xxreal_2_cl_8:
"cluster finiteFINSET-1V1 also-is real-boundedXXREAL-2V5 for real-memberedMEMBEREDV3\<bar>setHIDDENM2"
proof
(*coherence*)
  show " for it be real-memberedMEMBEREDV3\<bar>setHIDDENM2 holds it be finiteFINSET-1V1 implies it be real-boundedXXREAL-2V5"
sorry
qed "sorry"

mtheorem xxreal_2_cl_9:
"cluster real-boundedXXREAL-2V5 for  non emptyXBOOLE-0V1\<bar>natural-memberedMEMBEREDV6\<bar>setHIDDENM2"
proof
(*existence*)
  show " ex it be  non emptyXBOOLE-0V1\<bar>natural-memberedMEMBEREDV6\<bar>setHIDDENM2 st it be real-boundedXXREAL-2V5"
sorry
qed "sorry"

mtheorem xxreal_2_th_15:
" for X be  non emptyXBOOLE-0V1\<bar>real-memberedMEMBEREDV3\<bar>setHIDDENM2 holds X be bounded-belowXXREAL-2V3 implies infXXREAL-2K2 X inHIDDENR3 REALNUMBERSK2"
sorry

mtheorem xxreal_2_th_16:
" for X be  non emptyXBOOLE-0V1\<bar>real-memberedMEMBEREDV3\<bar>setHIDDENM2 holds X be bounded-aboveXXREAL-2V4 implies supXXREAL-2K1 X inHIDDENR3 REALNUMBERSK2"
sorry

mtheorem xxreal_2_cl_10:
  mlet "X be bounded-aboveXXREAL-2V4\<bar> non emptyXBOOLE-0V1\<bar>real-memberedMEMBEREDV3\<bar>setHIDDENM2"
"cluster supXXREAL-2K1 X as-term-is realXREAL-0V1"
proof
(*coherence*)
  show "supXXREAL-2K1 X be realXREAL-0V1"
sorry
qed "sorry"

mtheorem xxreal_2_cl_11:
  mlet "X be bounded-belowXXREAL-2V3\<bar> non emptyXBOOLE-0V1\<bar>real-memberedMEMBEREDV3\<bar>setHIDDENM2"
"cluster infXXREAL-2K2 X as-term-is realXREAL-0V1"
proof
(*coherence*)
  show "infXXREAL-2K2 X be realXREAL-0V1"
sorry
qed "sorry"

mtheorem xxreal_2_cl_12:
"cluster bounded-aboveXXREAL-2V4 also-is right-endXXREAL-2V2 for  non emptyXBOOLE-0V1\<bar>integer-memberedMEMBEREDV5\<bar>setHIDDENM2"
proof
(*coherence*)
  show " for it be  non emptyXBOOLE-0V1\<bar>integer-memberedMEMBEREDV5\<bar>setHIDDENM2 holds it be bounded-aboveXXREAL-2V4 implies it be right-endXXREAL-2V2"
sorry
qed "sorry"

mtheorem xxreal_2_cl_13:
"cluster bounded-belowXXREAL-2V3 also-is left-endXXREAL-2V1 for  non emptyXBOOLE-0V1\<bar>integer-memberedMEMBEREDV5\<bar>setHIDDENM2"
proof
(*coherence*)
  show " for it be  non emptyXBOOLE-0V1\<bar>integer-memberedMEMBEREDV5\<bar>setHIDDENM2 holds it be bounded-belowXXREAL-2V3 implies it be left-endXXREAL-2V1"
sorry
qed "sorry"

mtheorem xxreal_2_cl_14:
"cluster note-that bounded-belowXXREAL-2V3 for natural-memberedMEMBEREDV6\<bar>setHIDDENM2"
proof
(*coherence*)
  show " for it be natural-memberedMEMBEREDV6\<bar>setHIDDENM2 holds it be bounded-belowXXREAL-2V3"
sorry
qed "sorry"

mtheorem xxreal_2_cl_15:
  mlet "X be left-endXXREAL-2V1\<bar>real-memberedMEMBEREDV3\<bar>setHIDDENM2"
"cluster minXXREAL-2K5 X as-term-is realXREAL-0V1"
proof
(*coherence*)
  show "minXXREAL-2K5 X be realXREAL-0V1"
sorry
qed "sorry"

mtheorem xxreal_2_cl_16:
  mlet "X be left-endXXREAL-2V1\<bar>rational-memberedMEMBEREDV4\<bar>setHIDDENM2"
"cluster minXXREAL-2K5 X as-term-is rationalRAT-1V1"
proof
(*coherence*)
  show "minXXREAL-2K5 X be rationalRAT-1V1"
sorry
qed "sorry"

mtheorem xxreal_2_cl_17:
  mlet "X be left-endXXREAL-2V1\<bar>integer-memberedMEMBEREDV5\<bar>setHIDDENM2"
"cluster minXXREAL-2K5 X as-term-is integerINT-1V1"
proof
(*coherence*)
  show "minXXREAL-2K5 X be integerINT-1V1"
sorry
qed "sorry"

mtheorem xxreal_2_cl_18:
  mlet "X be left-endXXREAL-2V1\<bar>natural-memberedMEMBEREDV6\<bar>setHIDDENM2"
"cluster minXXREAL-2K5 X as-term-is naturalORDINAL1V7"
proof
(*coherence*)
  show "minXXREAL-2K5 X be naturalORDINAL1V7"
sorry
qed "sorry"

mtheorem xxreal_2_cl_19:
  mlet "X be right-endXXREAL-2V2\<bar>real-memberedMEMBEREDV3\<bar>setHIDDENM2"
"cluster maxXXREAL-2K6 X as-term-is realXREAL-0V1"
proof
(*coherence*)
  show "maxXXREAL-2K6 X be realXREAL-0V1"
sorry
qed "sorry"

mtheorem xxreal_2_cl_20:
  mlet "X be right-endXXREAL-2V2\<bar>rational-memberedMEMBEREDV4\<bar>setHIDDENM2"
"cluster maxXXREAL-2K6 X as-term-is rationalRAT-1V1"
proof
(*coherence*)
  show "maxXXREAL-2K6 X be rationalRAT-1V1"
sorry
qed "sorry"

mtheorem xxreal_2_cl_21:
  mlet "X be right-endXXREAL-2V2\<bar>integer-memberedMEMBEREDV5\<bar>setHIDDENM2"
"cluster maxXXREAL-2K6 X as-term-is integerINT-1V1"
proof
(*coherence*)
  show "maxXXREAL-2K6 X be integerINT-1V1"
sorry
qed "sorry"

mtheorem xxreal_2_cl_22:
  mlet "X be right-endXXREAL-2V2\<bar>natural-memberedMEMBEREDV6\<bar>setHIDDENM2"
"cluster maxXXREAL-2K6 X as-term-is naturalORDINAL1V7"
proof
(*coherence*)
  show "maxXXREAL-2K6 X be naturalORDINAL1V7"
sorry
qed "sorry"

mtheorem xxreal_2_cl_23:
"cluster left-endXXREAL-2V1 also-is bounded-belowXXREAL-2V3 for real-memberedMEMBEREDV3\<bar>setHIDDENM2"
proof
(*coherence*)
  show " for it be real-memberedMEMBEREDV3\<bar>setHIDDENM2 holds it be left-endXXREAL-2V1 implies it be bounded-belowXXREAL-2V3"
sorry
qed "sorry"

mtheorem xxreal_2_cl_24:
"cluster right-endXXREAL-2V2 also-is bounded-aboveXXREAL-2V4 for real-memberedMEMBEREDV3\<bar>setHIDDENM2"
proof
(*coherence*)
  show " for it be real-memberedMEMBEREDV3\<bar>setHIDDENM2 holds it be right-endXXREAL-2V2 implies it be bounded-aboveXXREAL-2V4"
sorry
qed "sorry"

mtheorem xxreal_2_th_17:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds x be LowerBoundXXREAL-2M2-of [.XXREAL-1K1 x,y .]"
sorry

mtheorem xxreal_2_th_18:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds x be LowerBoundXXREAL-2M2-of ].XXREAL-1K3 x,y .]"
sorry

mtheorem xxreal_2_th_19:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds x be LowerBoundXXREAL-2M2-of [.XXREAL-1K2 x,y .["
sorry

mtheorem xxreal_2_th_20:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds x be LowerBoundXXREAL-2M2-of ].XXREAL-1K4 x,y .["
sorry

mtheorem xxreal_2_th_21:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds y be UpperBoundXXREAL-2M1-of [.XXREAL-1K1 x,y .]"
sorry

mtheorem xxreal_2_th_22:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds y be UpperBoundXXREAL-2M1-of ].XXREAL-1K3 x,y .]"
sorry

mtheorem xxreal_2_th_23:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds y be UpperBoundXXREAL-2M1-of [.XXREAL-1K2 x,y .["
sorry

mtheorem xxreal_2_th_24:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds y be UpperBoundXXREAL-2M1-of ].XXREAL-1K4 x,y .["
sorry

mtheorem xxreal_2_th_25:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds x <=XXREAL-0R1 y implies infXXREAL-2K2 ([.XXREAL-1K1 x,y .]) =HIDDENR1 x"
sorry

mtheorem xxreal_2_th_26:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds x <XXREAL-0R3 y implies infXXREAL-2K2 ([.XXREAL-1K2 x,y .[) =HIDDENR1 x"
sorry

mtheorem xxreal_2_th_27:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds x <XXREAL-0R3 y implies infXXREAL-2K2 (].XXREAL-1K3 x,y .]) =HIDDENR1 x"
sorry

mtheorem xxreal_2_th_28:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds x <XXREAL-0R3 y implies infXXREAL-2K2 (].XXREAL-1K4 x,y .[) =HIDDENR1 x"
sorry

mtheorem xxreal_2_th_29:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds x <=XXREAL-0R1 y implies supXXREAL-2K1 ([.XXREAL-1K1 x,y .]) =HIDDENR1 y"
sorry

mtheorem xxreal_2_th_30:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds x <XXREAL-0R3 y implies supXXREAL-2K1 (].XXREAL-1K3 x,y .]) =HIDDENR1 y"
sorry

mtheorem xxreal_2_th_31:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds x <XXREAL-0R3 y implies supXXREAL-2K1 ([.XXREAL-1K2 x,y .[) =HIDDENR1 y"
sorry

mtheorem xxreal_2_th_32:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds x <XXREAL-0R3 y implies supXXREAL-2K1 (].XXREAL-1K4 x,y .[) =HIDDENR1 y"
sorry

mtheorem xxreal_2_th_33:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds x <=XXREAL-0R1 y implies [.XXREAL-1K1 x,y .] be left-endXXREAL-2V1\<bar>right-endXXREAL-2V2"
sorry

mtheorem xxreal_2_th_34:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds x <XXREAL-0R3 y implies [.XXREAL-1K2 x,y .[ be left-endXXREAL-2V1"
sorry

mtheorem xxreal_2_th_35:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds x <XXREAL-0R3 y implies ].XXREAL-1K3 x,y .] be right-endXXREAL-2V2"
sorry

mtheorem xxreal_2_th_36:
" for x be ExtRealXXREAL-0M1 holds x be LowerBoundXXREAL-2M2-of {}XBOOLE-0K1"
sorry

mtheorem xxreal_2_th_37:
" for x be ExtRealXXREAL-0M1 holds x be UpperBoundXXREAL-2M1-of {}XBOOLE-0K1"
sorry

mtheorem xxreal_2_th_38:
"infXXREAL-2K2 ({}XBOOLE-0K1) =HIDDENR1 +inftyXXREAL-0K1"
sorry

mtheorem xxreal_2_th_39:
"supXXREAL-2K1 ({}XBOOLE-0K1) =HIDDENR1 -inftyXXREAL-0K2"
sorry

mtheorem xxreal_2_th_40:
" for X be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds X be  non emptyXBOOLE-0V1 iff infXXREAL-2K2 X <=XXREAL-0R1 supXXREAL-2K1 X"
sorry

mtheorem xxreal_2_cl_25:
"cluster real-boundedXXREAL-2V5 also-is finiteFINSET-1V1 for integer-memberedMEMBEREDV5\<bar>setHIDDENM2"
proof
(*coherence*)
  show " for it be integer-memberedMEMBEREDV5\<bar>setHIDDENM2 holds it be real-boundedXXREAL-2V5 implies it be finiteFINSET-1V1"
sorry
qed "sorry"

mtheorem xxreal_2_cl_26:
"cluster note-that finiteFINSET-1V1 for bounded-aboveXXREAL-2V4\<bar>natural-memberedMEMBEREDV6\<bar>setHIDDENM2"
proof
(*coherence*)
  show " for it be bounded-aboveXXREAL-2V4\<bar>natural-memberedMEMBEREDV6\<bar>setHIDDENM2 holds it be finiteFINSET-1V1"
     sorry
qed "sorry"

mtheorem xxreal_2_th_41:
" for X be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds +inftyXXREAL-0K1 be UpperBoundXXREAL-2M1-of X"
sorry

mtheorem xxreal_2_th_42:
" for X be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds -inftyXXREAL-0K2 be LowerBoundXXREAL-2M2-of X"
sorry

mtheorem xxreal_2_th_43:
" for X be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for Y be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds X c=MEMBEREDR2 Y & Y be bounded-aboveXXREAL-2V4 implies X be bounded-aboveXXREAL-2V4"
sorry

mtheorem xxreal_2_th_44:
" for X be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for Y be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds X c=MEMBEREDR2 Y & Y be bounded-belowXXREAL-2V3 implies X be bounded-belowXXREAL-2V3"
sorry

mtheorem xxreal_2_th_45:
" for X be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for Y be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds X c=MEMBEREDR2 Y & Y be real-boundedXXREAL-2V5 implies X be real-boundedXXREAL-2V5"
  using xxreal_2_th_43 xxreal_2_th_44 sorry

mtheorem xxreal_2_th_46:
"REALNUMBERSK2 be  non bounded-belowXXREAL-2V3\<bar> non bounded-aboveXXREAL-2V4"
sorry

mtheorem xxreal_2_cl_27:
"cluster REALNUMBERSK2 as-term-is  non bounded-belowXXREAL-2V3\<bar> non bounded-aboveXXREAL-2V4"
proof
(*coherence*)
  show "REALNUMBERSK2 be  non bounded-belowXXREAL-2V3\<bar> non bounded-aboveXXREAL-2V4"
    using xxreal_2_th_46 sorry
qed "sorry"

mtheorem xxreal_2_th_47:
"{TARSKIK1 +inftyXXREAL-0K1 } be bounded-belowXXREAL-2V3"
sorry

mtheorem xxreal_2_th_48:
"{TARSKIK1 -inftyXXREAL-0K2 } be bounded-aboveXXREAL-2V4"
sorry

mtheorem xxreal_2_th_49:
" for X be bounded-aboveXXREAL-2V4\<bar> non emptyXBOOLE-0V1\<bar>ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds X <>HIDDENR2 {TARSKIK1 -inftyXXREAL-0K2 } implies ( ex x be ElementSUBSET-1M1-of REALNUMBERSK2 st x inTARSKIR2 X)"
sorry

mtheorem xxreal_2_th_50:
" for X be bounded-belowXXREAL-2V3\<bar> non emptyXBOOLE-0V1\<bar>ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds X <>HIDDENR2 {TARSKIK1 +inftyXXREAL-0K1 } implies ( ex x be ElementSUBSET-1M1-of REALNUMBERSK2 st x inTARSKIR2 X)"
sorry

mtheorem xxreal_2_th_51:
" for X be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds -inftyXXREAL-0K2 be UpperBoundXXREAL-2M1-of X implies X c=MEMBEREDR2 {TARSKIK1 -inftyXXREAL-0K2 }"
sorry

mtheorem xxreal_2_th_52:
" for X be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds +inftyXXREAL-0K1 be LowerBoundXXREAL-2M2-of X implies X c=MEMBEREDR2 {TARSKIK1 +inftyXXREAL-0K1 }"
sorry

mtheorem xxreal_2_th_53:
" for X be  non emptyXBOOLE-0V1\<bar>ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds ( ex y be UpperBoundXXREAL-2M1-of X st y <>HIDDENR2 +inftyXXREAL-0K1) implies X be bounded-aboveXXREAL-2V4"
sorry

mtheorem xxreal_2_th_54:
" for X be  non emptyXBOOLE-0V1\<bar>ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds ( ex y be LowerBoundXXREAL-2M2-of X st y <>HIDDENR2 -inftyXXREAL-0K2) implies X be bounded-belowXXREAL-2V3"
sorry

mtheorem xxreal_2_th_55:
" for X be  non emptyXBOOLE-0V1\<bar>ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for x be UpperBoundXXREAL-2M1-of X holds x inHIDDENR3 X implies x =HIDDENR1 supXXREAL-2K1 X"
sorry

mtheorem xxreal_2_th_56:
" for X be  non emptyXBOOLE-0V1\<bar>ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for x be LowerBoundXXREAL-2M2-of X holds x inHIDDENR3 X implies x =HIDDENR1 infXXREAL-2K2 X"
sorry

mtheorem xxreal_2_th_57:
" for X be  non emptyXBOOLE-0V1\<bar>ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds X be bounded-aboveXXREAL-2V4 & X <>HIDDENR2 {TARSKIK1 -inftyXXREAL-0K2 } implies supXXREAL-2K1 X inHIDDENR3 REALNUMBERSK2"
sorry

mtheorem xxreal_2_th_58:
" for X be  non emptyXBOOLE-0V1\<bar>ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds X be bounded-belowXXREAL-2V3 & X <>HIDDENR2 {TARSKIK1 +inftyXXREAL-0K1 } implies infXXREAL-2K2 X inHIDDENR3 REALNUMBERSK2"
sorry

mtheorem xxreal_2_th_59:
" for X be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for Y be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds X c=MEMBEREDR2 Y implies supXXREAL-2K1 X <=XXREAL-0R1 supXXREAL-2K1 Y"
sorry

mtheorem xxreal_2_th_60:
" for X be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for Y be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds X c=MEMBEREDR2 Y implies infXXREAL-2K2 Y <=XXREAL-0R1 infXXREAL-2K2 X"
sorry

mtheorem xxreal_2_th_61:
" for X be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for x be ExtRealXXREAL-0M1 holds ( ex y be ExtRealXXREAL-0M1 st y inHIDDENR3 X & x <=XXREAL-0R1 y) implies x <=XXREAL-0R1 supXXREAL-2K1 X"
sorry

mtheorem xxreal_2_th_62:
" for X be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for x be ExtRealXXREAL-0M1 holds ( ex y be ExtRealXXREAL-0M1 st y inHIDDENR3 X & y <=XXREAL-0R1 x) implies infXXREAL-2K2 X <=XXREAL-0R1 x"
sorry

mtheorem xxreal_2_th_63:
" for X be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for Y be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds ( for x be ExtRealXXREAL-0M1 holds x inHIDDENR3 X implies ( ex y be ExtRealXXREAL-0M1 st y inHIDDENR3 Y & x <=XXREAL-0R1 y)) implies supXXREAL-2K1 X <=XXREAL-0R1 supXXREAL-2K1 Y"
sorry

mtheorem xxreal_2_th_64:
" for X be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for Y be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds ( for y be ExtRealXXREAL-0M1 holds y inHIDDENR3 Y implies ( ex x be ExtRealXXREAL-0M1 st x inHIDDENR3 X & x <=XXREAL-0R1 y)) implies infXXREAL-2K2 X <=XXREAL-0R1 infXXREAL-2K2 Y"
sorry

mtheorem xxreal_2_th_65:
" for X be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for Y be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for x be UpperBoundXXREAL-2M1-of X holds  for y be UpperBoundXXREAL-2M1-of Y holds minXXREAL-0K4(x,y) be UpperBoundXXREAL-2M1-of X /\\XBOOLE-0K3 Y"
sorry

mtheorem xxreal_2_th_66:
" for X be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for Y be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for x be LowerBoundXXREAL-2M2-of X holds  for y be LowerBoundXXREAL-2M2-of Y holds maxXXREAL-0K5(x,y) be LowerBoundXXREAL-2M2-of X /\\XBOOLE-0K3 Y"
sorry

mtheorem xxreal_2_th_67:
" for X be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for Y be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds supXXREAL-2K1 (X /\\XBOOLE-0K3 Y) <=XXREAL-0R1 minXXREAL-0K4(supXXREAL-2K1 X,supXXREAL-2K1 Y)"
sorry

mtheorem xxreal_2_th_68:
" for X be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for Y be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds maxXXREAL-0K5(infXXREAL-2K2 X,infXXREAL-2K2 Y) <=XXREAL-0R1 infXXREAL-2K2 (X /\\XBOOLE-0K3 Y)"
sorry

mtheorem xxreal_2_cl_28:
"cluster real-boundedXXREAL-2V5 also-is real-memberedMEMBEREDV3 for ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2"
proof
(*coherence*)
  show " for it be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds it be real-boundedXXREAL-2V5 implies it be real-memberedMEMBEREDV3"
sorry
qed "sorry"

mtheorem xxreal_2_th_69:
" for A be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds A c=MEMBEREDR2 [.XXREAL-1K1 infXXREAL-2K2 A,supXXREAL-2K1 A .]"
sorry

mtheorem xxreal_2_th_70:
" for A be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds supXXREAL-2K1 A =HIDDENR1 infXXREAL-2K2 A implies A =MEMBEREDR8 {TARSKIK1 infXXREAL-2K2 A }"
sorry

mtheorem xxreal_2_th_71:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds  for A be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds x <=XXREAL-0R1 y & x be UpperBoundXXREAL-2M1-of A implies y be UpperBoundXXREAL-2M1-of A"
sorry

mtheorem xxreal_2_th_72:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds  for A be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds y <=XXREAL-0R1 x & x be LowerBoundXXREAL-2M2-of A implies y be LowerBoundXXREAL-2M2-of A"
sorry

mtheorem xxreal_2_th_73:
" for A be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds A be bounded-aboveXXREAL-2V4 iff supXXREAL-2K1 A <>HIDDENR2 +inftyXXREAL-0K1"
sorry

mtheorem xxreal_2_th_74:
" for A be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds A be bounded-belowXXREAL-2V3 iff infXXREAL-2K2 A <>HIDDENR2 -inftyXXREAL-0K2"
sorry

(*begin*)
mdef xxreal_2_def_12 ("intervalXXREAL-2V6" 70 ) where
"attr intervalXXREAL-2V6 for ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 means
  (\<lambda>A.  for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r inHIDDENR3 A & s inHIDDENR3 A implies [.XXREAL-1K1 r,s .] c=MEMBEREDR2 A)"..

mtheorem xxreal_2_cl_29:
"cluster ExtREALXXREAL-0K3 as-term-is intervalXXREAL-2V6"
proof
(*coherence*)
  show "ExtREALXXREAL-0K3 be intervalXXREAL-2V6"
    using membered_th_2 sorry
qed "sorry"

mtheorem xxreal_2_cl_30:
"cluster emptyXBOOLE-0V1 also-is intervalXXREAL-2V6 for ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2"
proof
(*coherence*)
  show " for it be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds it be emptyXBOOLE-0V1 implies it be intervalXXREAL-2V6"
     sorry
qed "sorry"

mtheorem xxreal_2_cl_31:
  mlet "r be ExtRealXXREAL-0M1", "s be ExtRealXXREAL-0M1"
"cluster [.XXREAL-1K1 r,s .] as-term-is intervalXXREAL-2V6"
proof
(*coherence*)
  show "[.XXREAL-1K1 r,s .] be intervalXXREAL-2V6"
sorry
qed "sorry"

mtheorem xxreal_2_cl_32:
  mlet "r be ExtRealXXREAL-0M1", "s be ExtRealXXREAL-0M1"
"cluster ].XXREAL-1K3 r,s .] as-term-is intervalXXREAL-2V6"
proof
(*coherence*)
  show "].XXREAL-1K3 r,s .] be intervalXXREAL-2V6"
sorry
qed "sorry"

mtheorem xxreal_2_cl_33:
  mlet "r be ExtRealXXREAL-0M1", "s be ExtRealXXREAL-0M1"
"cluster [.XXREAL-1K2 r,s .[ as-term-is intervalXXREAL-2V6"
proof
(*coherence*)
  show "[.XXREAL-1K2 r,s .[ be intervalXXREAL-2V6"
sorry
qed "sorry"

mtheorem xxreal_2_cl_34:
  mlet "r be ExtRealXXREAL-0M1", "s be ExtRealXXREAL-0M1"
"cluster ].XXREAL-1K4 r,s .[ as-term-is intervalXXREAL-2V6"
proof
(*coherence*)
  show "].XXREAL-1K4 r,s .[ be intervalXXREAL-2V6"
sorry
qed "sorry"

mtheorem xxreal_2_cl_35:
"cluster REALNUMBERSK2 as-term-is intervalXXREAL-2V6"
proof
(*coherence*)
  show "REALNUMBERSK2 be intervalXXREAL-2V6"
    using xxreal_1_th_224 sorry
qed "sorry"

mtheorem xxreal_2_cl_36:
"cluster intervalXXREAL-2V6 for  non emptyXBOOLE-0V1\<bar>ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2"
proof
(*existence*)
  show " ex it be  non emptyXBOOLE-0V1\<bar>ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 st it be intervalXXREAL-2V6"
sorry
qed "sorry"

mtheorem xxreal_2_cl_37:
  mlet "A be intervalXXREAL-2V6\<bar>ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2", "B be intervalXXREAL-2V6\<bar>ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2"
"cluster A /\\XBOOLE-0K3 B as-term-is intervalXXREAL-2V6"
proof
(*coherence*)
  show "A /\\XBOOLE-0K3 B be intervalXXREAL-2V6"
sorry
qed "sorry"

reserve A, B for "ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2"
mtheorem xxreal_2_cl_38:
  mlet "r be ExtRealXXREAL-0M1", "s be ExtRealXXREAL-0M1"
"cluster ].XXREAL-1K3 r,s .] as-term-is  non left-endXXREAL-2V1"
proof
(*coherence*)
  show "].XXREAL-1K3 r,s .] be  non left-endXXREAL-2V1"
sorry
qed "sorry"

mtheorem xxreal_2_cl_39:
  mlet "r be ExtRealXXREAL-0M1", "s be ExtRealXXREAL-0M1"
"cluster [.XXREAL-1K2 r,s .[ as-term-is  non right-endXXREAL-2V2"
proof
(*coherence*)
  show "[.XXREAL-1K2 r,s .[ be  non right-endXXREAL-2V2"
sorry
qed "sorry"

mtheorem xxreal_2_cl_40:
  mlet "r be ExtRealXXREAL-0M1", "s be ExtRealXXREAL-0M1"
"cluster ].XXREAL-1K4 r,s .[ as-term-is  non left-endXXREAL-2V1\<bar> non right-endXXREAL-2V2"
proof
(*coherence*)
  show "].XXREAL-1K4 r,s .[ be  non left-endXXREAL-2V1\<bar> non right-endXXREAL-2V2"
sorry
qed "sorry"

mtheorem xxreal_2_cl_41:
"cluster left-endXXREAL-2V1\<bar>right-endXXREAL-2V2\<bar>intervalXXREAL-2V6 for ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2"
proof
(*existence*)
  show " ex it be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 st it be left-endXXREAL-2V1\<bar>right-endXXREAL-2V2\<bar>intervalXXREAL-2V6"
sorry
qed "sorry"

mtheorem xxreal_2_cl_42:
"cluster  non left-endXXREAL-2V1\<bar>right-endXXREAL-2V2\<bar>intervalXXREAL-2V6 for ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2"
proof
(*existence*)
  show " ex it be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 st it be  non left-endXXREAL-2V1\<bar>right-endXXREAL-2V2\<bar>intervalXXREAL-2V6"
sorry
qed "sorry"

mtheorem xxreal_2_cl_43:
"cluster left-endXXREAL-2V1\<bar> non right-endXXREAL-2V2\<bar>intervalXXREAL-2V6 for ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2"
proof
(*existence*)
  show " ex it be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 st it be left-endXXREAL-2V1\<bar> non right-endXXREAL-2V2\<bar>intervalXXREAL-2V6"
sorry
qed "sorry"

mtheorem xxreal_2_cl_44:
"cluster  non left-endXXREAL-2V1\<bar> non right-endXXREAL-2V2\<bar>intervalXXREAL-2V6\<bar> non emptyXBOOLE-0V1 for ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2"
proof
(*existence*)
  show " ex it be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 st it be  non left-endXXREAL-2V1\<bar> non right-endXXREAL-2V2\<bar>intervalXXREAL-2V6\<bar> non emptyXBOOLE-0V1"
sorry
qed "sorry"

mtheorem xxreal_2_th_75:
" for A be left-endXXREAL-2V1\<bar>right-endXXREAL-2V2\<bar>intervalXXREAL-2V6\<bar>ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds A =MEMBEREDR8 [.XXREAL-1K1 minXXREAL-2K5 A,maxXXREAL-2K6 A .]"
sorry

mtheorem xxreal_2_th_76:
" for A be  non left-endXXREAL-2V1\<bar>right-endXXREAL-2V2\<bar>intervalXXREAL-2V6\<bar>ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds A =MEMBEREDR8 ].XXREAL-1K3 infXXREAL-2K2 A,maxXXREAL-2K6 A .]"
sorry

mtheorem xxreal_2_th_77:
" for A be left-endXXREAL-2V1\<bar> non right-endXXREAL-2V2\<bar>intervalXXREAL-2V6\<bar>ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds A =MEMBEREDR8 [.XXREAL-1K2 minXXREAL-2K5 A,supXXREAL-2K1 A .["
sorry

mtheorem xxreal_2_th_78:
" for A be  non left-endXXREAL-2V1\<bar> non right-endXXREAL-2V2\<bar> non emptyXBOOLE-0V1\<bar>intervalXXREAL-2V6\<bar>ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds A =MEMBEREDR8 ].XXREAL-1K4 infXXREAL-2K2 A,supXXREAL-2K1 A .["
sorry

mtheorem xxreal_2_th_79:
" for A be  non left-endXXREAL-2V1\<bar> non right-endXXREAL-2V2\<bar>intervalXXREAL-2V6\<bar>ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  ex r be ExtRealXXREAL-0M1 st  ex s be ExtRealXXREAL-0M1 st r <=XXREAL-0R1 s & A =MEMBEREDR8 ].XXREAL-1K4 r,s .["
sorry

mtheorem xxreal_2_th_80:
" for A be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds A be intervalXXREAL-2V6 implies ( for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds ((x inHIDDENR3 A & y inHIDDENR3 A) & x <=XXREAL-0R1 r) & r <=XXREAL-0R1 y implies r inHIDDENR3 A)"
sorry

mtheorem xxreal_2_th_81:
" for A be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds A be intervalXXREAL-2V6 implies ( for x be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds (x inHIDDENR3 A & x <=XXREAL-0R1 r) & r <XXREAL-0R3 supXXREAL-2K1 A implies r inHIDDENR3 A)"
sorry

mtheorem xxreal_2_th_82:
" for A be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds A be intervalXXREAL-2V6 implies ( for x be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds (x inHIDDENR3 A & infXXREAL-2K2 A <XXREAL-0R3 r) & r <=XXREAL-0R1 x implies r inHIDDENR3 A)"
sorry

mtheorem xxreal_2_th_83:
" for A be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds A be intervalXXREAL-2V6 implies ( for r be ExtRealXXREAL-0M1 holds infXXREAL-2K2 A <XXREAL-0R3 r & r <XXREAL-0R3 supXXREAL-2K1 A implies r inHIDDENR3 A)"
sorry

mtheorem xxreal_2_th_84:
" for A be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds ( for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds ((x inHIDDENR3 A & y inHIDDENR3 A) & x <XXREAL-0R3 r) & r <XXREAL-0R3 y implies r inHIDDENR3 A) implies A be intervalXXREAL-2V6"
sorry

mtheorem xxreal_2_th_85:
" for A be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds ( for x be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds (x inHIDDENR3 A & x <XXREAL-0R3 r) & r <XXREAL-0R3 supXXREAL-2K1 A implies r inHIDDENR3 A) implies A be intervalXXREAL-2V6"
sorry

mtheorem xxreal_2_th_86:
" for A be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds ( for y be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds (y inHIDDENR3 A & infXXREAL-2K2 A <XXREAL-0R3 r) & r <XXREAL-0R3 y implies r inHIDDENR3 A) implies A be intervalXXREAL-2V6"
sorry

mtheorem xxreal_2_th_87:
" for A be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds ( for r be ExtRealXXREAL-0M1 holds infXXREAL-2K2 A <XXREAL-0R3 r & r <XXREAL-0R3 supXXREAL-2K1 A implies r inHIDDENR3 A) implies A be intervalXXREAL-2V6"
sorry

mtheorem xxreal_2_th_88:
" for A be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds ( for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds  for r be ExtRealXXREAL-0M1 holds ((x inHIDDENR3 A & y inHIDDENR3 A) & x <=XXREAL-0R1 r) & r <=XXREAL-0R1 y implies r inHIDDENR3 A) implies A be intervalXXREAL-2V6"
sorry

mtheorem xxreal_2_th_89:
" for A be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for B be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds (A be intervalXXREAL-2V6 & B be intervalXXREAL-2V6) & A meetsXBOOLE-0R5 B implies A \\/XBOOLE-0K2 B be intervalXXREAL-2V6"
sorry

mtheorem xxreal_2_th_90:
" for A be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for B be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds (A be intervalXXREAL-2V6 & B be left-endXXREAL-2V1\<bar>intervalXXREAL-2V6) & supXXREAL-2K1 A =HIDDENR1 infXXREAL-2K2 B implies A \\/XBOOLE-0K2 B be intervalXXREAL-2V6"
sorry

mtheorem xxreal_2_th_91:
" for A be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for B be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds (A be right-endXXREAL-2V2\<bar>intervalXXREAL-2V6 & B be intervalXXREAL-2V6) & supXXREAL-2K1 A =HIDDENR1 infXXREAL-2K2 B implies A \\/XBOOLE-0K2 B be intervalXXREAL-2V6"
sorry

mtheorem xxreal_2_cl_45:
"cluster left-endXXREAL-2V1 also-is  non emptyXBOOLE-0V1 for ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2"
proof
(*coherence*)
  show " for it be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds it be left-endXXREAL-2V1 implies it be  non emptyXBOOLE-0V1"
     sorry
qed "sorry"

mtheorem xxreal_2_cl_46:
"cluster right-endXXREAL-2V2 also-is  non emptyXBOOLE-0V1 for ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2"
proof
(*coherence*)
  show " for it be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds it be right-endXXREAL-2V2 implies it be  non emptyXBOOLE-0V1"
     sorry
qed "sorry"

mtheorem xxreal_2_th_92:
" for A be  non emptyXBOOLE-0V1\<bar>SubsetSUBSET-1M2-of ExtREALXXREAL-0K3 holds ( for r be ElementSUBSET-1M1-of ExtREALXXREAL-0K3 holds r inTARSKIR2 A implies r <=XXREAL-0R1 -inftyXXREAL-0K2) implies A =MEMBEREDR8 {TARSKIK1 -inftyXXREAL-0K2 }"
sorry

mtheorem xxreal_2_th_93:
" for A be  non emptyXBOOLE-0V1\<bar>SubsetSUBSET-1M2-of ExtREALXXREAL-0K3 holds ( for r be ElementSUBSET-1M1-of ExtREALXXREAL-0K3 holds r inTARSKIR2 A implies +inftyXXREAL-0K1 <=XXREAL-0R1 r) implies A =MEMBEREDR8 {TARSKIK1 +inftyXXREAL-0K1 }"
sorry

mtheorem xxreal_2_th_94:
" for A be  non emptyXBOOLE-0V1\<bar>SubsetSUBSET-1M2-of ExtREALXXREAL-0K3 holds  for r be ExtRealXXREAL-0M1 holds r <XXREAL-0R3 supXXREAL-2K1 A implies ( ex s be ElementSUBSET-1M1-of ExtREALXXREAL-0K3 st s inTARSKIR2 A & r <XXREAL-0R3 s)"
sorry

mtheorem xxreal_2_th_95:
" for A be  non emptyXBOOLE-0V1\<bar>SubsetSUBSET-1M2-of ExtREALXXREAL-0K3 holds  for r be ElementSUBSET-1M1-of ExtREALXXREAL-0K3 holds infXXREAL-2K2 A <XXREAL-0R3 r implies ( ex s be ElementSUBSET-1M1-of ExtREALXXREAL-0K3 st s inTARSKIR2 A & s <XXREAL-0R3 r)"
sorry

mtheorem xxreal_2_th_96:
" for A be  non emptyXBOOLE-0V1\<bar>SubsetSUBSET-1M2-of ExtREALXXREAL-0K3 holds  for B be  non emptyXBOOLE-0V1\<bar>SubsetSUBSET-1M2-of ExtREALXXREAL-0K3 holds ( for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds r inHIDDENR3 A & s inHIDDENR3 B implies r <=XXREAL-0R1 s) implies supXXREAL-2K1 A <=XXREAL-0R1 infXXREAL-2K2 B"
sorry

end
