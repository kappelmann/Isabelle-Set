theory int_1
  imports real_1 nat_1
   "../mizar_extension/E_number"
begin
(*begin*)
reserve X for "setHIDDENM2"
reserve x, y, z for "objectHIDDENM1"
reserve k, l, n for "NatNAT-1M1"
reserve r for "RealXREAL-0M1"
mlemma int_1_lm_1:
" for z be objectHIDDENM1 holds z inHIDDENR3 [:ZFMISC-1K2 {TARSKIK1 0NUMBERSK6 },NATNUMBERSK1 :] \\SUBSET-1K6 {TARSKIK1 [TARSKIK4 0NUMBERSK6,0NUMBERSK6 ] } implies ( ex k be NatNAT-1M1 st z =HIDDENR1 -XCMPLX-0K4 k)"
sorry

mlemma int_1_lm_2:
" for x be objectHIDDENM1 holds  for k be NatNAT-1M1 holds x =HIDDENR1 -XCMPLX-0K4 k & k <>HIDDENR2 x implies x inHIDDENR3 [:ZFMISC-1K2 {TARSKIK1 0NUMBERSK6 },NATNUMBERSK1 :] \\SUBSET-1K6 {TARSKIK1 [TARSKIK4 0NUMBERSK6,0NUMBERSK6 ] }"
sorry

abbreviation(input) INT_1K1("INTINT-1K1" 355) where
  "INTINT-1K1 \<equiv> INTNUMBERSK5"

mtheorem int_1_def_1:
"redefine func INTINT-1K1 \<rightarrow> setHIDDENM2 means
  \<lambda>it.  for x be objectHIDDENM1 holds x inHIDDENR3 it iff ( ex k be NatNAT-1M1 st x =HIDDENR1 k or x =HIDDENR1 -XCMPLX-0K4 k)"
proof
(*compatibility*)
  show " for it be setHIDDENM2 holds it =HIDDENR1 INTINT-1K1 iff ( for x be objectHIDDENM1 holds x inHIDDENR3 it iff ( ex k be NatNAT-1M1 st x =HIDDENR1 k or x =HIDDENR1 -XCMPLX-0K4 k))"
sorry
qed "sorry"

mdef int_1_def_2 ("integerINT-1V1" 70 ) where
"attr integerINT-1V1 for NumberORDINAL1M1 means
  (\<lambda>i. i inHIDDENR3 INTINT-1K1)"..

mtheorem int_1_cl_1:
"cluster integerINT-1V1 for RealXREAL-0M1"
proof
(*existence*)
  show " ex it be RealXREAL-0M1 st it be integerINT-1V1"
sorry
qed "sorry"

mtheorem int_1_cl_2:
"cluster integerINT-1V1 for numberORDINAL1M2"
proof
(*existence*)
  show " ex it be numberORDINAL1M2 st it be integerINT-1V1"
sorry
qed "sorry"

mtheorem int_1_cl_3:
"cluster note-that integerINT-1V1 for ElementSUBSET-1M1-of INTINT-1K1"
proof
(*coherence*)
  show " for it be ElementSUBSET-1M1-of INTINT-1K1 holds it be integerINT-1V1"
     sorry
qed "sorry"

syntax INT_1M1 :: "Ty" ("IntegerINT-1M1" 70)
translations "IntegerINT-1M1" \<rightharpoonup> "integerINT-1V1\<bar>NumberORDINAL1M1"

mtheorem int_1_th_1:
" for r be RealXREAL-0M1 holds  for k be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds r =HIDDENR1 k or r =HIDDENR1 -XCMPLX-0K4 k implies r be IntegerINT-1M1"
sorry

mtheorem int_1_th_2:
" for r be RealXREAL-0M1 holds r be IntegerINT-1M1 implies ( ex k be NatNAT-1M1 st r =HIDDENR1 k or r =HIDDENR1 -XCMPLX-0K4 k)"
sorry

mtheorem int_1_cl_4:
"cluster naturalORDINAL1V7 also-is integerINT-1V1 for objectHIDDENM1"
proof
(*coherence*)
  show " for it be objectHIDDENM1 holds it be naturalORDINAL1V7 implies it be integerINT-1V1"
sorry
qed "sorry"

mtheorem int_1_cl_5:
"cluster integerINT-1V1 also-is realXREAL-0V1 for objectHIDDENM1"
proof
(*coherence*)
  show " for it be objectHIDDENM1 holds it be integerINT-1V1 implies it be realXREAL-0V1"
    using numbers_th_15 sorry
qed "sorry"

reserve i, i0, i1, i2, i3, i4, i5, i8, i9, j for "IntegerINT-1M1"
mtheorem int_1_cl_6:
  mlet "i1 be IntegerINT-1M1", "i2 be IntegerINT-1M1"
"cluster i1 +XCMPLX-0K2 i2 as-term-is integerINT-1V1"
proof
(*coherence*)
  show "i1 +XCMPLX-0K2 i2 be integerINT-1V1"
sorry
qed "sorry"

mtheorem int_1_cl_7:
  mlet "i1 be IntegerINT-1M1", "i2 be IntegerINT-1M1"
"cluster i1 *XCMPLX-0K3 i2 as-term-is integerINT-1V1"
proof
(*coherence*)
  show "i1 *XCMPLX-0K3 i2 be integerINT-1V1"
sorry
qed "sorry"

mtheorem int_1_cl_8:
  mlet "i0 be IntegerINT-1M1"
"cluster -XCMPLX-0K4 i0 as-term-is integerINT-1V1"
proof
(*coherence*)
  show "-XCMPLX-0K4 i0 be integerINT-1V1"
sorry
qed "sorry"

mtheorem int_1_cl_9:
  mlet "i1 be IntegerINT-1M1", "i2 be IntegerINT-1M1"
"cluster i1 -XCMPLX-0K6 i2 as-term-is integerINT-1V1"
proof
(*coherence*)
  show "i1 -XCMPLX-0K6 i2 be integerINT-1V1"
sorry
qed "sorry"

mtheorem int_1_th_3:
" for i0 be IntegerINT-1M1 holds 0NUMBERSK6 <=XXREAL-0R1 i0 implies i0 inHIDDENR3 NATNUMBERSK1"
sorry

mtheorem int_1_th_4:
" for r be RealXREAL-0M1 holds r be IntegerINT-1M1 implies r +XCMPLX-0K2 \<one>\<^sub>M be IntegerINT-1M1 & r -XCMPLX-0K6 \<one>\<^sub>M be IntegerINT-1M1"
   sorry

mtheorem int_1_th_5:
" for i1 be IntegerINT-1M1 holds  for i2 be IntegerINT-1M1 holds i2 <=XXREAL-0R1 i1 implies i1 -XCMPLX-0K6 i2 inTARSKIR2 NATNUMBERSK1"
sorry

mtheorem int_1_th_6:
" for k be NatNAT-1M1 holds  for i1 be IntegerINT-1M1 holds  for i2 be IntegerINT-1M1 holds i1 +XCMPLX-0K2 k =HIDDENR1 i2 implies i1 <=XXREAL-0R1 i2"
sorry

mlemma int_1_lm_3:
" for j be ElementSUBSET-1M1-of NATNUMBERSK1 holds j <XXREAL-0R3 \<one>\<^sub>M implies j =XBOOLE-0R4 0NUMBERSK6"
sorry

mlemma int_1_lm_4:
" for i1 be IntegerINT-1M1 holds 0NUMBERSK6 <XXREAL-0R3 i1 implies \<one>\<^sub>M <=XXREAL-0R1 i1"
sorry

mtheorem int_1_th_7:
" for i0 be IntegerINT-1M1 holds  for i1 be IntegerINT-1M1 holds i0 <XXREAL-0R3 i1 implies i0 +XCMPLX-0K2 \<one>\<^sub>M <=XXREAL-0R1 i1"
sorry

mtheorem int_1_th_8:
" for i1 be IntegerINT-1M1 holds i1 <XXREAL-0R3 0NUMBERSK6 implies i1 <=XXREAL-0R1 -XCMPLX-0K4 \<one>\<^sub>M"
sorry

mtheorem int_1_th_9:
" for i1 be IntegerINT-1M1 holds  for i2 be IntegerINT-1M1 holds i1 *XCMPLX-0K3 i2 =XBOOLE-0R4 \<one>\<^sub>M iff i1 =HIDDENR1 \<one>\<^sub>M & i2 =HIDDENR1 \<one>\<^sub>M or i1 =HIDDENR1 -XCMPLX-0K4 \<one>\<^sub>M & i2 =HIDDENR1 -XCMPLX-0K4 \<one>\<^sub>M"
sorry

mtheorem int_1_th_10:
" for i1 be IntegerINT-1M1 holds  for i2 be IntegerINT-1M1 holds i1 *XCMPLX-0K3 i2 =HIDDENR1 -XCMPLX-0K4 \<one>\<^sub>M iff i1 =HIDDENR1 -XCMPLX-0K4 \<one>\<^sub>M & i2 =HIDDENR1 \<one>\<^sub>M or i1 =HIDDENR1 \<one>\<^sub>M & i2 =HIDDENR1 -XCMPLX-0K4 \<one>\<^sub>M"
sorry

mlemma int_1_lm_5:
" for i0 be IntegerINT-1M1 holds  for i1 be IntegerINT-1M1 holds i0 <=XXREAL-0R1 i1 implies ( ex k be NatNAT-1M1 st i0 +XCMPLX-0K2 k =HIDDENR1 i1)"
sorry

mlemma int_1_lm_6:
" for i0 be IntegerINT-1M1 holds  for i1 be IntegerINT-1M1 holds i0 <=XXREAL-0R1 i1 implies ( ex k be NatNAT-1M1 st i1 -XCMPLX-0K6 k =HIDDENR1 i0)"
sorry

theorem int_1_sch_1:
  fixes Pp1 
  shows " ex X be SubsetSUBSET-1M2-of INTINT-1K1 st  for x be IntegerINT-1M1 holds x inHIDDENR3 X iff Pp1(x)"
sorry

theorem int_1_sch_2:
  fixes Ff0 Pp1 
  assumes
[ty]: "Ff0 be IntegerINT-1M1" and
   A1: "Pp1(Ff0)" and
   A2: " for i2 be IntegerINT-1M1 holds Ff0 <=XXREAL-0R1 i2 implies (Pp1(i2) implies Pp1(i2 +XCMPLX-0K2 \<one>\<^sub>M))"
  shows " for i0 be IntegerINT-1M1 holds Ff0 <=XXREAL-0R1 i0 implies Pp1(i0)"
sorry

theorem int_1_sch_3:
  fixes Ff0 Pp1 
  assumes
[ty]: "Ff0 be IntegerINT-1M1" and
   A1: "Pp1(Ff0)" and
   A2: " for i2 be IntegerINT-1M1 holds i2 <=XXREAL-0R1 Ff0 implies (Pp1(i2) implies Pp1(i2 -XCMPLX-0K6 \<one>\<^sub>M))"
  shows " for i0 be IntegerINT-1M1 holds i0 <=XXREAL-0R1 Ff0 implies Pp1(i0)"
sorry

theorem int_1_sch_4:
  fixes Ff0 Pp1 
  assumes
[ty]: "Ff0 be IntegerINT-1M1" and
   A1: "Pp1(Ff0)" and
   A2: " for i2 be IntegerINT-1M1 holds Pp1(i2) implies Pp1(i2 -XCMPLX-0K6 \<one>\<^sub>M) & Pp1(i2 +XCMPLX-0K2 \<one>\<^sub>M)"
  shows " for i0 be IntegerINT-1M1 holds Pp1(i0)"
sorry

theorem int_1_sch_5:
  fixes Ff0 Pp1 
  assumes
[ty]: "Ff0 be IntegerINT-1M1" and
   A1: " for i1 be IntegerINT-1M1 holds Pp1(i1) implies Ff0 <=XXREAL-0R1 i1" and
   A2: " ex i1 be IntegerINT-1M1 st Pp1(i1)"
  shows " ex i0 be IntegerINT-1M1 st Pp1(i0) & ( for i1 be IntegerINT-1M1 holds Pp1(i1) implies i0 <=XXREAL-0R1 i1)"
sorry

theorem int_1_sch_6:
  fixes Ff0 Pp1 
  assumes
[ty]: "Ff0 be IntegerINT-1M1" and
   A1: " for i1 be IntegerINT-1M1 holds Pp1(i1) implies i1 <=XXREAL-0R1 Ff0" and
   A2: " ex i1 be IntegerINT-1M1 st Pp1(i1)"
  shows " ex i0 be IntegerINT-1M1 st Pp1(i0) & ( for i1 be IntegerINT-1M1 holds Pp1(i1) implies i1 <=XXREAL-0R1 i0)"
sorry

mdef int_1_def_3 (" _ dividesINT-1R1  _ " [50,50]50 ) where
  mlet "i1 be IntegerINT-1M1", "i2 be IntegerINT-1M1"
"pred i1 dividesINT-1R1 i2 means
   ex i3 be IntegerINT-1M1 st i2 =HIDDENR1 i1 *XCMPLX-0K3 i3"..

mtheorem INT_1R1_reflexivity:
" for i2 be IntegerINT-1M1 holds i2 dividesINT-1R1 i2"
sorry

mdef int_1_def_4 ("'( _ , _ ')are-congruent-modINT-1R2  _ " [0,0,50]50 ) where
  mlet "i1 be IntegerINT-1M1", "i2 be IntegerINT-1M1", "i3 be IntegerINT-1M1"
"pred (i1,i2)are-congruent-modINT-1R2 i3 means
  i3 dividesINT-1R1 i1 -XCMPLX-0K6 i2"..

abbreviation(input) INT_1R3("'( _ , _ ')are-congruent-modINT-1R3  _ " [0,0,50]50) where
  "(i1,i2)are-congruent-modINT-1R3 i3 \<equiv> (i1,i2)are-congruent-modINT-1R2 i3"

mtheorem int_1_def_5:
  mlet "i1 be IntegerINT-1M1", "i2 be IntegerINT-1M1", "i3 be IntegerINT-1M1"
"redefine pred (i1,i2)are-congruent-modINT-1R3 i3 means
   ex i4 be IntegerINT-1M1 st i3 *XCMPLX-0K3 i4 =XBOOLE-0R4 i1 -XCMPLX-0K6 i2"
proof
(*compatibility*)
  show "(i1,i2)are-congruent-modINT-1R3 i3 iff ( ex i4 be IntegerINT-1M1 st i3 *XCMPLX-0K3 i4 =XBOOLE-0R4 i1 -XCMPLX-0K6 i2)"
sorry
qed "sorry"

mtheorem int_1_th_11:
" for i1 be IntegerINT-1M1 holds  for i2 be IntegerINT-1M1 holds (i1,i1)are-congruent-modINT-1R3 i2"
sorry

mtheorem int_1_th_12:
" for i1 be IntegerINT-1M1 holds (i1,0NUMBERSK6)are-congruent-modINT-1R3 i1 & (0NUMBERSK6,i1)are-congruent-modINT-1R3 i1"
sorry

mtheorem int_1_th_13:
" for i1 be IntegerINT-1M1 holds  for i2 be IntegerINT-1M1 holds (i1,i2)are-congruent-modINT-1R3 \<one>\<^sub>M"
sorry

mtheorem int_1_th_14:
" for i1 be IntegerINT-1M1 holds  for i2 be IntegerINT-1M1 holds  for i3 be IntegerINT-1M1 holds (i1,i2)are-congruent-modINT-1R3 i3 implies (i2,i1)are-congruent-modINT-1R3 i3"
sorry

mtheorem int_1_th_15:
" for i1 be IntegerINT-1M1 holds  for i2 be IntegerINT-1M1 holds  for i3 be IntegerINT-1M1 holds  for i5 be IntegerINT-1M1 holds (i1,i2)are-congruent-modINT-1R3 i5 & (i2,i3)are-congruent-modINT-1R3 i5 implies (i1,i3)are-congruent-modINT-1R3 i5"
sorry

mtheorem int_1_th_16:
" for i1 be IntegerINT-1M1 holds  for i2 be IntegerINT-1M1 holds  for i3 be IntegerINT-1M1 holds  for i4 be IntegerINT-1M1 holds  for i5 be IntegerINT-1M1 holds (i1,i2)are-congruent-modINT-1R3 i5 & (i3,i4)are-congruent-modINT-1R3 i5 implies (i1 +XCMPLX-0K2 i3,i2 +XCMPLX-0K2 i4)are-congruent-modINT-1R3 i5"
sorry

mtheorem int_1_th_17:
" for i1 be IntegerINT-1M1 holds  for i2 be IntegerINT-1M1 holds  for i3 be IntegerINT-1M1 holds  for i4 be IntegerINT-1M1 holds  for i5 be IntegerINT-1M1 holds (i1,i2)are-congruent-modINT-1R3 i5 & (i3,i4)are-congruent-modINT-1R3 i5 implies (i1 -XCMPLX-0K6 i3,i2 -XCMPLX-0K6 i4)are-congruent-modINT-1R3 i5"
sorry

mtheorem int_1_th_18:
" for i1 be IntegerINT-1M1 holds  for i2 be IntegerINT-1M1 holds  for i3 be IntegerINT-1M1 holds  for i4 be IntegerINT-1M1 holds  for i5 be IntegerINT-1M1 holds (i1,i2)are-congruent-modINT-1R3 i5 & (i3,i4)are-congruent-modINT-1R3 i5 implies (i1 *XCMPLX-0K3 i3,i2 *XCMPLX-0K3 i4)are-congruent-modINT-1R3 i5"
sorry

mtheorem int_1_th_19:
" for i1 be IntegerINT-1M1 holds  for i2 be IntegerINT-1M1 holds  for i3 be IntegerINT-1M1 holds  for i5 be IntegerINT-1M1 holds (i1 +XCMPLX-0K2 i2,i3)are-congruent-modINT-1R3 i5 iff (i1,i3 -XCMPLX-0K6 i2)are-congruent-modINT-1R3 i5"
   sorry

mtheorem int_1_th_20:
" for i1 be IntegerINT-1M1 holds  for i2 be IntegerINT-1M1 holds  for i3 be IntegerINT-1M1 holds  for i4 be IntegerINT-1M1 holds  for i5 be IntegerINT-1M1 holds i4 *XCMPLX-0K3 i5 =HIDDENR1 i3 implies ((i1,i2)are-congruent-modINT-1R3 i3 implies (i1,i2)are-congruent-modINT-1R3 i4)"
sorry

mtheorem int_1_th_21:
" for i1 be IntegerINT-1M1 holds  for i2 be IntegerINT-1M1 holds  for i5 be IntegerINT-1M1 holds (i1,i2)are-congruent-modINT-1R3 i5 iff (i1 +XCMPLX-0K2 i5,i2)are-congruent-modINT-1R3 i5"
sorry

mtheorem int_1_th_22:
" for i1 be IntegerINT-1M1 holds  for i2 be IntegerINT-1M1 holds  for i5 be IntegerINT-1M1 holds (i1,i2)are-congruent-modINT-1R3 i5 iff (i1 -XCMPLX-0K6 i5,i2)are-congruent-modINT-1R3 i5"
sorry

mtheorem int_1_th_23:
" for r be RealXREAL-0M1 holds  for i1 be IntegerINT-1M1 holds  for i2 be IntegerINT-1M1 holds ((i1 <=XXREAL-0R1 r & r -XCMPLX-0K6 \<one>\<^sub>M <XXREAL-0R3 i1) & i2 <=XXREAL-0R1 r) & r -XCMPLX-0K6 \<one>\<^sub>M <XXREAL-0R3 i2 implies i1 =HIDDENR1 i2"
sorry

mtheorem int_1_th_24:
" for r be RealXREAL-0M1 holds  for i1 be IntegerINT-1M1 holds  for i2 be IntegerINT-1M1 holds ((r <=XXREAL-0R1 i1 & i1 <XXREAL-0R3 r +XCMPLX-0K2 \<one>\<^sub>M) & r <=XXREAL-0R1 i2) & i2 <XXREAL-0R3 r +XCMPLX-0K2 \<one>\<^sub>M implies i1 =HIDDENR1 i2"
sorry

reserve r1, p, p1, g, g1, g2 for "RealXREAL-0M1"
reserve Y for "SubsetSUBSET-1M2-of REALNUMBERSK2"
mlemma int_1_lm_7:
" for r be RealXREAL-0M1 holds  ex n be NatNAT-1M1 st r <XXREAL-0R3 n"
sorry

mdef int_1_def_6 ("['\\INT-1K2  _ '/]" [0]164 ) where
  mlet "r be RealXREAL-0M1"
"func [\\INT-1K2 r/] \<rightarrow> IntegerINT-1M1 means
  \<lambda>it. it <=XXREAL-0R1 r & r -XCMPLX-0K6 \<one>\<^sub>M <XXREAL-0R3 it"
proof-
  (*existence*)
    show " ex it be IntegerINT-1M1 st it <=XXREAL-0R1 r & r -XCMPLX-0K6 \<one>\<^sub>M <XXREAL-0R3 it"
sorry
  (*uniqueness*)
    show " for it1 be IntegerINT-1M1 holds  for it2 be IntegerINT-1M1 holds (it1 <=XXREAL-0R1 r & r -XCMPLX-0K6 \<one>\<^sub>M <XXREAL-0R3 it1) & (it2 <=XXREAL-0R1 r & r -XCMPLX-0K6 \<one>\<^sub>M <XXREAL-0R3 it2) implies it1 =HIDDENR1 it2"
      using int_1_th_23 sorry
qed "sorry"

mtheorem INT_1K2_projectivity:
" for r be RealXREAL-0M1 holds [\\INT-1K2 [\\INT-1K2 r/] /] =HIDDENR1 [\\INT-1K2 r/]"
sorry

mtheorem int_1_th_25:
" for r be RealXREAL-0M1 holds [\\INT-1K2 r/] =HIDDENR1 r iff r be integerINT-1V1"
sorry

mtheorem int_1_th_26:
" for r be RealXREAL-0M1 holds [\\INT-1K2 r/] <XXREAL-0R3 r iff  not r be integerINT-1V1"
sorry

mtheorem int_1_th_27:
" for r be RealXREAL-0M1 holds [\\INT-1K2 r/] -XCMPLX-0K6 \<one>\<^sub>M <XXREAL-0R3 r & [\\INT-1K2 r/] <XXREAL-0R3 r +XCMPLX-0K2 \<one>\<^sub>M"
sorry

mtheorem int_1_th_28:
" for r be RealXREAL-0M1 holds  for i0 be IntegerINT-1M1 holds [\\INT-1K2 r/] +XCMPLX-0K2 i0 =HIDDENR1 [\\INT-1K2 r +XCMPLX-0K2 i0 /]"
sorry

mtheorem int_1_th_29:
" for r be RealXREAL-0M1 holds r <XXREAL-0R3 [\\INT-1K2 r/] +XCMPLX-0K2 \<one>\<^sub>M"
sorry

mdef int_1_def_7 ("['/INT-1K3  _ '\\]" [0]164 ) where
  mlet "r be RealXREAL-0M1"
"func [/INT-1K3 r\\] \<rightarrow> IntegerINT-1M1 means
  \<lambda>it. r <=XXREAL-0R1 it & it <XXREAL-0R3 r +XCMPLX-0K2 \<one>\<^sub>M"
proof-
  (*existence*)
    show " ex it be IntegerINT-1M1 st r <=XXREAL-0R1 it & it <XXREAL-0R3 r +XCMPLX-0K2 \<one>\<^sub>M"
sorry
  (*uniqueness*)
    show " for it1 be IntegerINT-1M1 holds  for it2 be IntegerINT-1M1 holds (r <=XXREAL-0R1 it1 & it1 <XXREAL-0R3 r +XCMPLX-0K2 \<one>\<^sub>M) & (r <=XXREAL-0R1 it2 & it2 <XXREAL-0R3 r +XCMPLX-0K2 \<one>\<^sub>M) implies it1 =HIDDENR1 it2"
      using int_1_th_24 sorry
qed "sorry"

mtheorem INT_1K3_projectivity:
" for r be RealXREAL-0M1 holds [/INT-1K3 [/INT-1K3 r\\] \\] =HIDDENR1 [/INT-1K3 r\\]"
sorry

mtheorem int_1_th_30:
" for r be RealXREAL-0M1 holds [/INT-1K3 r\\] =HIDDENR1 r iff r be integerINT-1V1"
sorry

mtheorem int_1_th_31:
" for r be RealXREAL-0M1 holds r <XXREAL-0R3 [/INT-1K3 r\\] iff  not r be integerINT-1V1"
sorry

mtheorem int_1_th_32:
" for r be RealXREAL-0M1 holds r -XCMPLX-0K6 \<one>\<^sub>M <XXREAL-0R3 [/INT-1K3 r\\] & r <XXREAL-0R3 [/INT-1K3 r\\] +XCMPLX-0K2 \<one>\<^sub>M"
sorry

mtheorem int_1_th_33:
" for r be RealXREAL-0M1 holds  for i0 be IntegerINT-1M1 holds [/INT-1K3 r\\] +XCMPLX-0K2 i0 =HIDDENR1 [/INT-1K3 r +XCMPLX-0K2 i0 \\]"
sorry

mtheorem int_1_th_34:
" for r be RealXREAL-0M1 holds [\\INT-1K2 r/] =HIDDENR1 [/INT-1K3 r\\] iff r be integerINT-1V1"
sorry

mtheorem int_1_th_35:
" for r be RealXREAL-0M1 holds [\\INT-1K2 r/] <XXREAL-0R3 [/INT-1K3 r\\] iff  not r be integerINT-1V1"
sorry

mtheorem int_1_th_36:
" for r be RealXREAL-0M1 holds [\\INT-1K2 r/] <=XXREAL-0R1 [/INT-1K3 r\\]"
sorry

mtheorem int_1_th_37:
" for r be RealXREAL-0M1 holds [\\INT-1K2 [/INT-1K3 r\\] /] =HIDDENR1 [/INT-1K3 r\\]"
  using int_1_th_25 sorry

(*\$CT 2*)
mtheorem int_1_th_40:
" for r be RealXREAL-0M1 holds [/INT-1K3 [\\INT-1K2 r/] \\] =HIDDENR1 [\\INT-1K2 r/]"
  using int_1_th_30 sorry

mtheorem int_1_th_41:
" for r be RealXREAL-0M1 holds [\\INT-1K2 r/] =HIDDENR1 [/INT-1K3 r\\] iff  not [\\INT-1K2 r/] +XCMPLX-0K2 \<one>\<^sub>M =HIDDENR1 [/INT-1K3 r\\]"
sorry

mdef int_1_def_8 ("fracINT-1K4  _ " [240]240 ) where
  mlet "r be RealXREAL-0M1"
"func fracINT-1K4 r \<rightarrow> numberORDINAL1M2 equals
  r -XCMPLX-0K6 [\\INT-1K2 r/]"
proof-
  (*coherence*)
    show "r -XCMPLX-0K6 [\\INT-1K2 r/] be numberORDINAL1M2"
       sorry
qed "sorry"

mtheorem int_1_cl_10:
  mlet "r be RealXREAL-0M1"
"cluster fracINT-1K4 r as-term-is realXREAL-0V1"
proof
(*coherence*)
  show "fracINT-1K4 r be realXREAL-0V1"
     sorry
qed "sorry"

mtheorem int_1_th_42:
" for r be RealXREAL-0M1 holds r =HIDDENR1 [\\INT-1K2 r/] +XCMPLX-0K2 fracINT-1K4 r"
   sorry

mtheorem int_1_th_43:
" for r be RealXREAL-0M1 holds fracINT-1K4 r <XXREAL-0R3 \<one>\<^sub>M & 0NUMBERSK6 <=XXREAL-0R1 fracINT-1K4 r"
sorry

mtheorem int_1_th_44:
" for r be RealXREAL-0M1 holds [\\INT-1K2 fracINT-1K4 r/] =HIDDENR1 0NUMBERSK6"
sorry

mtheorem int_1_th_45:
" for r be RealXREAL-0M1 holds fracINT-1K4 r =XBOOLE-0R4 0NUMBERSK6 iff r be integerINT-1V1"
sorry

mtheorem int_1_th_46:
" for r be RealXREAL-0M1 holds 0NUMBERSK6 <XXREAL-0R3 fracINT-1K4 r iff  not r be integerINT-1V1"
sorry

mdef int_1_def_9 (" _ divINT-1K5  _ " [132,132]132 ) where
  mlet "i1 be IntegerINT-1M1", "i2 be IntegerINT-1M1"
"func i1 divINT-1K5 i2 \<rightarrow> IntegerINT-1M1 equals
  [\\INT-1K2 i1 /XCMPLX-0K7 i2 /]"
proof-
  (*coherence*)
    show "[\\INT-1K2 i1 /XCMPLX-0K7 i2 /] be IntegerINT-1M1"
       sorry
qed "sorry"

mdef int_1_def_10 (" _ modINT-1K6  _ " [132,132]132 ) where
  mlet "i1 be IntegerINT-1M1", "i2 be IntegerINT-1M1"
"func i1 modINT-1K6 i2 \<rightarrow> IntegerINT-1M1 equals
  i1 -XCMPLX-0K6 (i1 divINT-1K5 i2)*XCMPLX-0K3 i2 if i2 <>HIDDENR2 0NUMBERSK6 otherwise 0NUMBERSK6"
proof-
  (*coherence*)
    show "(i2 <>HIDDENR2 0NUMBERSK6 implies i1 -XCMPLX-0K6 (i1 divINT-1K5 i2)*XCMPLX-0K3 i2 be IntegerINT-1M1) & ( not i2 <>HIDDENR2 0NUMBERSK6 implies 0NUMBERSK6 be IntegerINT-1M1)"
       sorry
  (*consistency*)
    show " for it be IntegerINT-1M1 holds  True "
       sorry
qed "sorry"

mtheorem int_1_th_47:
" for r be RealXREAL-0M1 holds r <>HIDDENR2 0NUMBERSK6 implies [\\INT-1K2 r /XCMPLX-0K7 r /] =HIDDENR1 \<one>\<^sub>M"
sorry

mtheorem int_1_th_48:
" for i be IntegerINT-1M1 holds i divINT-1K5 0NUMBERSK6 =HIDDENR1 0NUMBERSK6"
sorry

mtheorem int_1_th_49:
" for i be IntegerINT-1M1 holds i <>HIDDENR2 0NUMBERSK6 implies i divINT-1K5 i =HIDDENR1 \<one>\<^sub>M"
  using int_1_th_47 sorry

mtheorem int_1_th_50:
" for i be IntegerINT-1M1 holds i modINT-1K6 i =HIDDENR1 0NUMBERSK6"
sorry

(*begin*)
mtheorem int_1_th_51:
" for k be IntegerINT-1M1 holds  for i be IntegerINT-1M1 holds k <XXREAL-0R3 i implies ( ex j be ElementSUBSET-1M1-of NATNUMBERSK1 st j =XBOOLE-0R4 i -XCMPLX-0K6 k & \<one>\<^sub>M <=XXREAL-0R1 j)"
sorry

mtheorem int_1_th_52:
" for a be IntegerINT-1M1 holds  for b be IntegerINT-1M1 holds a <XXREAL-0R3 b implies a <=XXREAL-0R1 b -XCMPLX-0K6 \<one>\<^sub>M"
sorry

mtheorem int_1_th_53:
" for r be RealXREAL-0M1 holds r >=XXREAL-0R2 0NUMBERSK6 implies (([/INT-1K3 r\\] >=XXREAL-0R2 0NUMBERSK6 & [\\INT-1K2 r/] >=XXREAL-0R2 0NUMBERSK6) & [/INT-1K3 r\\] be ElementSUBSET-1M1-of NATNUMBERSK1) & [\\INT-1K2 r/] be ElementSUBSET-1M1-of NATNUMBERSK1"
sorry

mtheorem int_1_th_54:
" for i be IntegerINT-1M1 holds  for r be RealXREAL-0M1 holds i <=XXREAL-0R1 r implies i <=XXREAL-0R1 [\\INT-1K2 r/]"
sorry

mtheorem int_1_th_55:
" for m be NatNAT-1M1 holds  for n be NatNAT-1M1 holds 0NUMBERSK6 <=XXREAL-0R1 m divINT-1K5 n"
  using int_1_th_54 sorry

mtheorem int_1_th_56:
" for i be IntegerINT-1M1 holds  for j be IntegerINT-1M1 holds 0NUMBERSK6 <XXREAL-0R3 i & \<one>\<^sub>M <XXREAL-0R3 j implies i divINT-1K5 j <XXREAL-0R3 i"
sorry

mtheorem int_1_th_57:
" for i1 be IntegerINT-1M1 holds  for i2 be IntegerINT-1M1 holds i2 >=XXREAL-0R2 0NUMBERSK6 implies i1 modINT-1K6 i2 >=XXREAL-0R2 0NUMBERSK6"
sorry

mtheorem int_1_th_58:
" for i1 be IntegerINT-1M1 holds  for i2 be IntegerINT-1M1 holds i2 >XXREAL-0R4 0NUMBERSK6 implies i1 modINT-1K6 i2 <XXREAL-0R3 i2"
sorry

mtheorem int_1_th_59:
" for i1 be IntegerINT-1M1 holds  for i2 be IntegerINT-1M1 holds i2 <>HIDDENR2 0NUMBERSK6 implies i1 =HIDDENR1 (i1 divINT-1K5 i2)*XCMPLX-0K3 i2 +XCMPLX-0K2 (i1 modINT-1K6 i2)"
sorry

mtheorem int_1_th_60:
" for m be IntegerINT-1M1 holds  for j be IntegerINT-1M1 holds (m *XCMPLX-0K3 j,0NUMBERSK6)are-congruent-modINT-1R3 m"
   sorry

mtheorem int_1_th_61:
" for i be IntegerINT-1M1 holds  for j be IntegerINT-1M1 holds i >=XXREAL-0R2 0NUMBERSK6 & j >=XXREAL-0R2 0NUMBERSK6 implies i divINT-1K5 j >=XXREAL-0R2 0NUMBERSK6"
sorry

mtheorem int_1_th_62:
" for n be NatNAT-1M1 holds n >XXREAL-0R4 0NUMBERSK6 implies ( for a be IntegerINT-1M1 holds a modINT-1K6 n =HIDDENR1 0NUMBERSK6 iff n dividesINT-1R1 a)"
sorry

reserve r, s for "RealXREAL-0M1"
mtheorem int_1_th_63:
" for r be RealXREAL-0M1 holds  for s be RealXREAL-0M1 holds  not r /XCMPLX-0K7 s be IntegerINT-1M1 implies -XCMPLX-0K4 [\\INT-1K2 r /XCMPLX-0K7 s /] =HIDDENR1 [\\INT-1K2 (-XCMPLX-0K4 r)/XCMPLX-0K7 s /] +XCMPLX-0K2 \<one>\<^sub>M"
sorry

mtheorem int_1_th_64:
" for r be RealXREAL-0M1 holds  for s be RealXREAL-0M1 holds r /XCMPLX-0K7 s be IntegerINT-1M1 implies -XCMPLX-0K4 [\\INT-1K2 r /XCMPLX-0K7 s /] =HIDDENR1 [\\INT-1K2 (-XCMPLX-0K4 r)/XCMPLX-0K7 s /]"
sorry

mtheorem int_1_th_65:
" for i be IntegerINT-1M1 holds  for r be RealXREAL-0M1 holds r <=XXREAL-0R1 i implies [/INT-1K3 r\\] <=XXREAL-0R1 i"
sorry

theorem int_1_sch_7:
  fixes Mf0 Nf0 Pp1 
  assumes
[ty]: "Mf0 be ElementSUBSET-1M1-of NATNUMBERSK1" and
  [ty]: "Nf0 be ElementSUBSET-1M1-of NATNUMBERSK1" and
   A1: "Pp1(Mf0)" and
   A2: " for j be ElementSUBSET-1M1-of NATNUMBERSK1 holds Mf0 <=XXREAL-0R1 j & j <XXREAL-0R3 Nf0 implies (Pp1(j) implies Pp1(j +NAT-1K1 \<one>\<^sub>M))"
  shows " for i be ElementSUBSET-1M1-of NATNUMBERSK1 holds Mf0 <=XXREAL-0R1 i & i <=XXREAL-0R1 Nf0 implies Pp1(i)"
sorry

theorem int_1_sch_8:
  fixes Mf0 Nf0 Pp1 
  assumes
[ty]: "Mf0 be ElementSUBSET-1M1-of NATNUMBERSK1" and
  [ty]: "Nf0 be ElementSUBSET-1M1-of NATNUMBERSK1" and
   A1: "Pp1(Mf0)" and
   A2: " for j be ElementSUBSET-1M1-of NATNUMBERSK1 holds Mf0 <=XXREAL-0R1 j & j <XXREAL-0R3 Nf0 implies (( for j9 be ElementSUBSET-1M1-of NATNUMBERSK1 holds Mf0 <=XXREAL-0R1 j9 & j9 <=XXREAL-0R1 j implies Pp1(j9)) implies Pp1(j +NAT-1K1 \<one>\<^sub>M))"
  shows " for i be ElementSUBSET-1M1-of NATNUMBERSK1 holds Mf0 <=XXREAL-0R1 i & i <=XXREAL-0R1 Nf0 implies Pp1(i)"
sorry

reserve i for "IntegerINT-1M1"
reserve a, b, r, s for "RealXREAL-0M1"
mtheorem int_1_th_66:
" for i be IntegerINT-1M1 holds  for r be RealXREAL-0M1 holds fracINT-1K4 (r +XCMPLX-0K2 i) =XBOOLE-0R4 fracINT-1K4 r"
sorry

mtheorem int_1_th_67:
" for a be RealXREAL-0M1 holds  for r be RealXREAL-0M1 holds r <=XXREAL-0R1 a & a <XXREAL-0R3 [\\INT-1K2 r/] +XCMPLX-0K2 \<one>\<^sub>M implies [\\INT-1K2 a/] =HIDDENR1 [\\INT-1K2 r/]"
sorry

mtheorem int_1_th_68:
" for a be RealXREAL-0M1 holds  for r be RealXREAL-0M1 holds r <=XXREAL-0R1 a & a <XXREAL-0R3 [\\INT-1K2 r/] +XCMPLX-0K2 \<one>\<^sub>M implies fracINT-1K4 r <=XXREAL-0R1 fracINT-1K4 a"
sorry

mtheorem int_1_th_69:
" for a be RealXREAL-0M1 holds  for r be RealXREAL-0M1 holds r <XXREAL-0R3 a & a <XXREAL-0R3 [\\INT-1K2 r/] +XCMPLX-0K2 \<one>\<^sub>M implies fracINT-1K4 r <XXREAL-0R3 fracINT-1K4 a"
sorry

mtheorem int_1_th_70:
" for a be RealXREAL-0M1 holds  for r be RealXREAL-0M1 holds a >=XXREAL-0R2 [\\INT-1K2 r/] +XCMPLX-0K2 \<one>\<^sub>M & a <=XXREAL-0R1 r +XCMPLX-0K2 \<one>\<^sub>M implies [\\INT-1K2 a/] =HIDDENR1 [\\INT-1K2 r/] +XCMPLX-0K2 \<one>\<^sub>M"
sorry

mtheorem int_1_th_71:
" for a be RealXREAL-0M1 holds  for r be RealXREAL-0M1 holds a >=XXREAL-0R2 [\\INT-1K2 r/] +XCMPLX-0K2 \<one>\<^sub>M & a <XXREAL-0R3 r +XCMPLX-0K2 \<one>\<^sub>M implies fracINT-1K4 a <XXREAL-0R3 fracINT-1K4 r"
sorry

mtheorem int_1_th_72:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for r be RealXREAL-0M1 holds (((r <=XXREAL-0R1 a & a <XXREAL-0R3 r +XCMPLX-0K2 \<one>\<^sub>M) & r <=XXREAL-0R1 b) & b <XXREAL-0R3 r +XCMPLX-0K2 \<one>\<^sub>M) & fracINT-1K4 a =XBOOLE-0R4 fracINT-1K4 b implies a =HIDDENR1 b"
sorry

mtheorem int_1_reduce_1:
  mlet "i be IntegerINT-1M1"
"reduce InSUBSET-1K10(i,INTINT-1K1) to i"
proof
(*reducibility*)
  show "InSUBSET-1K10(i,INTINT-1K1) =HIDDENR1 i"
    using int_1_def_2 subset_1_def_8 sorry
qed "sorry"

mdef int_1_def_11 ("dim-likeINT-1V2" 70 ) where
"attr dim-likeINT-1V2 for NumberORDINAL1M1 means
  (\<lambda>x. x =HIDDENR1 -XCMPLX-0K4 \<one>\<^sub>M or x be naturalORDINAL1V7)"..

mtheorem int_1_cl_11:
"cluster naturalORDINAL1V7 also-is dim-likeINT-1V2 for objectHIDDENM1"
proof
(*coherence*)
  show " for it be objectHIDDENM1 holds it be naturalORDINAL1V7 implies it be dim-likeINT-1V2"
     sorry
qed "sorry"

mtheorem int_1_cl_12:
"cluster dim-likeINT-1V2 also-is integerINT-1V1 for objectHIDDENM1"
proof
(*coherence*)
  show " for it be objectHIDDENM1 holds it be dim-likeINT-1V2 implies it be integerINT-1V1"
     sorry
qed "sorry"

mtheorem int_1_cl_13:
"cluster -XCMPLX-0K4 \<one>\<^sub>M as-term-is dim-likeINT-1V2 for objectHIDDENM1"
proof
(*coherence*)
  show " for it be objectHIDDENM1 holds it =HIDDENR1 -XCMPLX-0K4 \<one>\<^sub>M implies it be dim-likeINT-1V2"
     sorry
qed "sorry"

mtheorem int_1_cl_14:
"cluster dim-likeINT-1V2 for setHIDDENM2"
proof
(*existence*)
  show " ex it be setHIDDENM2 st it be dim-likeINT-1V2"
sorry
qed "sorry"

mtheorem int_1_cl_15:
  mlet "d be dim-likeINT-1V2\<bar>objectHIDDENM1"
"cluster d +XCMPLX-0K2 \<one>\<^sub>M as-term-is naturalORDINAL1V7"
proof
(*coherence*)
  show "d +XCMPLX-0K2 \<one>\<^sub>M be naturalORDINAL1V7"
sorry
qed "sorry"

mtheorem int_1_cl_16:
  mlet "k be dim-likeINT-1V2\<bar>objectHIDDENM1", "n be  non zeroORDINAL1V8\<bar>naturalORDINAL1V7\<bar>NumberORDINAL1M1"
"cluster k +XCMPLX-0K2 n as-term-is naturalORDINAL1V7"
proof
(*coherence*)
  show "k +XCMPLX-0K2 n be naturalORDINAL1V7"
sorry
qed "sorry"

mtheorem int_1_th_73:
" for i be IntegerINT-1M1 holds 0NUMBERSK6 =HIDDENR1 0NUMBERSK6 modINT-1K6 i"
sorry

end
