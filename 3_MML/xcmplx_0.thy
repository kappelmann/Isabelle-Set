theory xcmplx_0
  imports arytm_0 funcop_1
   "../mizar_extension/E_number"
begin
(*begin*)
mdef xcmplx_0_def_1 ("<i>XCMPLX-0K1" 164 ) where
"func <i>XCMPLX-0K1 \<rightarrow> NumberORDINAL1M1 equals
  (0NUMBERSK6,\<one>\<^sub>M)-->FUNCT-4K7\<^bsub>(omegaORDINAL1K4)\<^esub>(0NUMBERSK6,\<one>\<^sub>M)"
proof-
  (*coherence*)
    show "(0NUMBERSK6,\<one>\<^sub>M)-->FUNCT-4K7\<^bsub>(omegaORDINAL1K4)\<^esub>(0NUMBERSK6,\<one>\<^sub>M) be NumberORDINAL1M1"
       sorry
qed "sorry"

mdef xcmplx_0_def_2 ("complexXCMPLX-0V1" 70 ) where
"attr complexXCMPLX-0V1 for NumberORDINAL1M1 means
  (\<lambda>c. c inHIDDENR3 COMPLEXNUMBERSK3)"..

mlemma
"0NUMBERSK6 inTARSKIR2 NATNUMBERSK1"
   sorry

mlemma
"0NUMBERSK6 inTARSKIR2 REALNUMBERSK2"
  using numbers_th_19 sorry

mlemma xcmplx_0_lm_1:
"InSUBSET-1K10(0NUMBERSK6,REALNUMBERSK2) =XBOOLE-0R4 0NUMBERSK6"
  using subset_1_def_8 sorry

mlemma
"\<one>\<^sub>M inTARSKIR2 NATNUMBERSK1"
   sorry

mlemma xcmplx_0_lm_2:
"\<one>\<^sub>M inTARSKIR2 REALNUMBERSK2"
  using numbers_th_19 sorry

mtheorem xcmplx_0_cl_1:
"cluster <i>XCMPLX-0K1 as-term-is complexXCMPLX-0V1"
proof
(*coherence*)
  show "<i>XCMPLX-0K1 be complexXCMPLX-0V1"
sorry
qed "sorry"

mtheorem xcmplx_0_cl_2:
"cluster complexXCMPLX-0V1 for NumberORDINAL1M1"
proof
(*existence*)
  show " ex it be NumberORDINAL1M1 st it be complexXCMPLX-0V1"
sorry
qed "sorry"

mtheorem xcmplx_0_cl_3:
"cluster complexXCMPLX-0V1 for numberORDINAL1M2"
proof
(*existence*)
  show " ex it be numberORDINAL1M2 st it be complexXCMPLX-0V1"
sorry
qed "sorry"

syntax XCMPLX_0M1 :: "Ty" ("ComplexXCMPLX-0M1" 70)
translations "ComplexXCMPLX-0M1" \<rightharpoonup> "complexXCMPLX-0V1\<bar>NumberORDINAL1M1"

mtheorem
"cluster sethood of ComplexXCMPLX-0M1"
proof
(*sethood*)
  show " ex cover be setHIDDENM2 st  for it be ComplexXCMPLX-0M1 holds it inHIDDENR3 cover"
sorry
qed "sorry"

(*\$CD*)
mdef xcmplx_0_def_4 (" _ +XCMPLX-0K2  _ " [132,132]132 ) where
  mlet "x be ComplexXCMPLX-0M1", "y be ComplexXCMPLX-0M1"
"func x +XCMPLX-0K2 y \<rightarrow> numberORDINAL1M2 means
  \<lambda>it.  ex x1 be ElementSUBSET-1M1-of REALNUMBERSK2 st  ex x2 be ElementSUBSET-1M1-of REALNUMBERSK2 st  ex y1 be ElementSUBSET-1M1-of REALNUMBERSK2 st  ex y2 be ElementSUBSET-1M1-of REALNUMBERSK2 st (x =HIDDENR1 [*ARYTM-0K5 x1,x2 *] & y =HIDDENR1 [*ARYTM-0K5 y1,y2 *]) & it =XBOOLE-0R4 [*ARYTM-0K5 +ARYTM-0K1(x1,y1),+ARYTM-0K1(x2,y2) *]"
proof-
  (*existence*)
    show " ex it be numberORDINAL1M2 st  ex x1 be ElementSUBSET-1M1-of REALNUMBERSK2 st  ex x2 be ElementSUBSET-1M1-of REALNUMBERSK2 st  ex y1 be ElementSUBSET-1M1-of REALNUMBERSK2 st  ex y2 be ElementSUBSET-1M1-of REALNUMBERSK2 st (x =HIDDENR1 [*ARYTM-0K5 x1,x2 *] & y =HIDDENR1 [*ARYTM-0K5 y1,y2 *]) & it =XBOOLE-0R4 [*ARYTM-0K5 +ARYTM-0K1(x1,y1),+ARYTM-0K1(x2,y2) *]"
sorry
  (*uniqueness*)
    show " for it1 be numberORDINAL1M2 holds  for it2 be numberORDINAL1M2 holds ( ex x1 be ElementSUBSET-1M1-of REALNUMBERSK2 st  ex x2 be ElementSUBSET-1M1-of REALNUMBERSK2 st  ex y1 be ElementSUBSET-1M1-of REALNUMBERSK2 st  ex y2 be ElementSUBSET-1M1-of REALNUMBERSK2 st (x =HIDDENR1 [*ARYTM-0K5 x1,x2 *] & y =HIDDENR1 [*ARYTM-0K5 y1,y2 *]) & it1 =XBOOLE-0R4 [*ARYTM-0K5 +ARYTM-0K1(x1,y1),+ARYTM-0K1(x2,y2) *]) & ( ex x1 be ElementSUBSET-1M1-of REALNUMBERSK2 st  ex x2 be ElementSUBSET-1M1-of REALNUMBERSK2 st  ex y1 be ElementSUBSET-1M1-of REALNUMBERSK2 st  ex y2 be ElementSUBSET-1M1-of REALNUMBERSK2 st (x =HIDDENR1 [*ARYTM-0K5 x1,x2 *] & y =HIDDENR1 [*ARYTM-0K5 y1,y2 *]) & it2 =XBOOLE-0R4 [*ARYTM-0K5 +ARYTM-0K1(x1,y1),+ARYTM-0K1(x2,y2) *]) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mtheorem XCMPLX_0K2_commutativity:
" for x be ComplexXCMPLX-0M1 holds  for y be ComplexXCMPLX-0M1 holds x +XCMPLX-0K2 y =HIDDENR1 y +XCMPLX-0K2 x"
sorry

mdef xcmplx_0_def_5 (" _ *XCMPLX-0K3  _ " [164,164]164 ) where
  mlet "x be ComplexXCMPLX-0M1", "y be ComplexXCMPLX-0M1"
"func x *XCMPLX-0K3 y \<rightarrow> numberORDINAL1M2 means
  \<lambda>it.  ex x1 be ElementSUBSET-1M1-of REALNUMBERSK2 st  ex x2 be ElementSUBSET-1M1-of REALNUMBERSK2 st  ex y1 be ElementSUBSET-1M1-of REALNUMBERSK2 st  ex y2 be ElementSUBSET-1M1-of REALNUMBERSK2 st (x =HIDDENR1 [*ARYTM-0K5 x1,x2 *] & y =HIDDENR1 [*ARYTM-0K5 y1,y2 *]) & it =XBOOLE-0R4 [*ARYTM-0K5 +ARYTM-0K1( *ARYTM-0K2(x1,y1),oppARYTM-0K3 ( *ARYTM-0K2(x2,y2))),+ARYTM-0K1( *ARYTM-0K2(x1,y2), *ARYTM-0K2(x2,y1)) *]"
proof-
  (*existence*)
    show " ex it be numberORDINAL1M2 st  ex x1 be ElementSUBSET-1M1-of REALNUMBERSK2 st  ex x2 be ElementSUBSET-1M1-of REALNUMBERSK2 st  ex y1 be ElementSUBSET-1M1-of REALNUMBERSK2 st  ex y2 be ElementSUBSET-1M1-of REALNUMBERSK2 st (x =HIDDENR1 [*ARYTM-0K5 x1,x2 *] & y =HIDDENR1 [*ARYTM-0K5 y1,y2 *]) & it =XBOOLE-0R4 [*ARYTM-0K5 +ARYTM-0K1( *ARYTM-0K2(x1,y1),oppARYTM-0K3 ( *ARYTM-0K2(x2,y2))),+ARYTM-0K1( *ARYTM-0K2(x1,y2), *ARYTM-0K2(x2,y1)) *]"
sorry
  (*uniqueness*)
    show " for it1 be numberORDINAL1M2 holds  for it2 be numberORDINAL1M2 holds ( ex x1 be ElementSUBSET-1M1-of REALNUMBERSK2 st  ex x2 be ElementSUBSET-1M1-of REALNUMBERSK2 st  ex y1 be ElementSUBSET-1M1-of REALNUMBERSK2 st  ex y2 be ElementSUBSET-1M1-of REALNUMBERSK2 st (x =HIDDENR1 [*ARYTM-0K5 x1,x2 *] & y =HIDDENR1 [*ARYTM-0K5 y1,y2 *]) & it1 =XBOOLE-0R4 [*ARYTM-0K5 +ARYTM-0K1( *ARYTM-0K2(x1,y1),oppARYTM-0K3 ( *ARYTM-0K2(x2,y2))),+ARYTM-0K1( *ARYTM-0K2(x1,y2), *ARYTM-0K2(x2,y1)) *]) & ( ex x1 be ElementSUBSET-1M1-of REALNUMBERSK2 st  ex x2 be ElementSUBSET-1M1-of REALNUMBERSK2 st  ex y1 be ElementSUBSET-1M1-of REALNUMBERSK2 st  ex y2 be ElementSUBSET-1M1-of REALNUMBERSK2 st (x =HIDDENR1 [*ARYTM-0K5 x1,x2 *] & y =HIDDENR1 [*ARYTM-0K5 y1,y2 *]) & it2 =XBOOLE-0R4 [*ARYTM-0K5 +ARYTM-0K1( *ARYTM-0K2(x1,y1),oppARYTM-0K3 ( *ARYTM-0K2(x2,y2))),+ARYTM-0K1( *ARYTM-0K2(x1,y2), *ARYTM-0K2(x2,y1)) *]) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mtheorem XCMPLX_0K3_commutativity:
" for x be ComplexXCMPLX-0M1 holds  for y be ComplexXCMPLX-0M1 holds x *XCMPLX-0K3 y =HIDDENR1 y *XCMPLX-0K3 x"
sorry

mlemma xcmplx_0_lm_3:
" for x be ElementSUBSET-1M1-of REALNUMBERSK2 holds  for y be ElementSUBSET-1M1-of REALNUMBERSK2 holds  for z be ElementSUBSET-1M1-of REALNUMBERSK2 holds +ARYTM-0K1(x,y) =XBOOLE-0R4 0NUMBERSK6 & +ARYTM-0K1(x,z) =XBOOLE-0R4 0NUMBERSK6 implies y =XBOOLE-0R4 z"
sorry

mtheorem xcmplx_0_cl_4:
  mlet "z be ComplexXCMPLX-0M1", "z9 be ComplexXCMPLX-0M1"
"cluster z +XCMPLX-0K2 z9 as-term-is complexXCMPLX-0V1"
proof
(*coherence*)
  show "z +XCMPLX-0K2 z9 be complexXCMPLX-0V1"
sorry
qed "sorry"

mtheorem xcmplx_0_cl_5:
  mlet "z be ComplexXCMPLX-0M1", "z9 be ComplexXCMPLX-0M1"
"cluster z *XCMPLX-0K3 z9 as-term-is complexXCMPLX-0V1"
proof
(*coherence*)
  show "z *XCMPLX-0K3 z9 be complexXCMPLX-0V1"
sorry
qed "sorry"

mdef xcmplx_0_def_6 ("-XCMPLX-0K4  _ " [132]132 ) where
  mlet "z be ComplexXCMPLX-0M1"
"func -XCMPLX-0K4 z \<rightarrow> ComplexXCMPLX-0M1 means
  \<lambda>it. z +XCMPLX-0K2 it =XBOOLE-0R4 0NUMBERSK6"
proof-
  (*existence*)
    show " ex it be ComplexXCMPLX-0M1 st z +XCMPLX-0K2 it =XBOOLE-0R4 0NUMBERSK6"
sorry
  (*uniqueness*)
    show " for it1 be ComplexXCMPLX-0M1 holds  for it2 be ComplexXCMPLX-0M1 holds z +XCMPLX-0K2 it1 =XBOOLE-0R4 0NUMBERSK6 & z +XCMPLX-0K2 it2 =XBOOLE-0R4 0NUMBERSK6 implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mtheorem XCMPLX_0K4_involutiveness:
" for z be ComplexXCMPLX-0M1 holds -XCMPLX-0K4 (-XCMPLX-0K4 z) =HIDDENR1 z"
sorry

mdef xcmplx_0_def_7 (" _ \<inverse>XCMPLX-0K5" [228]228 ) where
  mlet "z be ComplexXCMPLX-0M1"
"func z \<inverse>XCMPLX-0K5 \<rightarrow> ComplexXCMPLX-0M1 means
  \<lambda>it. z *XCMPLX-0K3 it =XBOOLE-0R4 \<one>\<^sub>M if z <>HIDDENR2 0NUMBERSK6 otherwise \<lambda>it. it =HIDDENR1 0NUMBERSK6"
proof-
  (*existence*)
    show "(z <>HIDDENR2 0NUMBERSK6 implies ( ex it be ComplexXCMPLX-0M1 st z *XCMPLX-0K3 it =XBOOLE-0R4 \<one>\<^sub>M)) & ( not z <>HIDDENR2 0NUMBERSK6 implies ( ex it be ComplexXCMPLX-0M1 st it =HIDDENR1 0NUMBERSK6))"
sorry
  (*uniqueness*)
    show " for it1 be ComplexXCMPLX-0M1 holds  for it2 be ComplexXCMPLX-0M1 holds (z <>HIDDENR2 0NUMBERSK6 implies (z *XCMPLX-0K3 it1 =XBOOLE-0R4 \<one>\<^sub>M & z *XCMPLX-0K3 it2 =XBOOLE-0R4 \<one>\<^sub>M implies it1 =HIDDENR1 it2)) & ( not z <>HIDDENR2 0NUMBERSK6 implies (it1 =HIDDENR1 0NUMBERSK6 & it2 =HIDDENR1 0NUMBERSK6 implies it1 =HIDDENR1 it2))"
sorry
  (*consistency*)
    show " for it be ComplexXCMPLX-0M1 holds  True "
sorry
qed "sorry"

mtheorem XCMPLX_0K5_involutiveness:
" for z be ComplexXCMPLX-0M1 holds (z \<inverse>XCMPLX-0K5)\<inverse>XCMPLX-0K5 =HIDDENR1 z"
sorry

mdef xcmplx_0_def_8 (" _ -XCMPLX-0K6  _ " [132,132]132 ) where
  mlet "x be ComplexXCMPLX-0M1", "y be ComplexXCMPLX-0M1"
"func x -XCMPLX-0K6 y \<rightarrow> numberORDINAL1M2 equals
  x +XCMPLX-0K2 (-XCMPLX-0K4 y)"
proof-
  (*coherence*)
    show "x +XCMPLX-0K2 (-XCMPLX-0K4 y) be numberORDINAL1M2"
       sorry
qed "sorry"

mdef xcmplx_0_def_9 (" _ '/XCMPLX-0K7  _ " [164,164]164 ) where
  mlet "x be ComplexXCMPLX-0M1", "y be ComplexXCMPLX-0M1"
"func x /XCMPLX-0K7 y \<rightarrow> numberORDINAL1M2 equals
  x *XCMPLX-0K3 y \<inverse>XCMPLX-0K5"
proof-
  (*coherence*)
    show "x *XCMPLX-0K3 y \<inverse>XCMPLX-0K5 be numberORDINAL1M2"
       sorry
qed "sorry"

mtheorem xcmplx_0_cl_6:
  mlet "x be ComplexXCMPLX-0M1", "y be ComplexXCMPLX-0M1"
"cluster x -XCMPLX-0K6 y as-term-is complexXCMPLX-0V1"
proof
(*coherence*)
  show "x -XCMPLX-0K6 y be complexXCMPLX-0V1"
     sorry
qed "sorry"

mtheorem xcmplx_0_cl_7:
  mlet "x be ComplexXCMPLX-0M1", "y be ComplexXCMPLX-0M1"
"cluster x /XCMPLX-0K7 y as-term-is complexXCMPLX-0V1"
proof
(*coherence*)
  show "x /XCMPLX-0K7 y be complexXCMPLX-0V1"
     sorry
qed "sorry"

mlemma xcmplx_0_lm_4:
" for x be ComplexXCMPLX-0M1 holds  for y be ComplexXCMPLX-0M1 holds  for z be ComplexXCMPLX-0M1 holds x *XCMPLX-0K3 (y *XCMPLX-0K3 z) =XBOOLE-0R4 (x *XCMPLX-0K3 y)*XCMPLX-0K3 z"
sorry

mtheorem xcmplx_0_cl_8:
"cluster naturalORDINAL1V7 also-is complexXCMPLX-0V1 for objectHIDDENM1"
proof
(*coherence*)
  show " for it be objectHIDDENM1 holds it be naturalORDINAL1V7 implies it be complexXCMPLX-0V1"
    using numbers_th_20 sorry
qed "sorry"

mlemma xcmplx_0_lm_5:
"\<one>\<^sub>M be ComplexXCMPLX-0M1"
   sorry

mtheorem xcmplx_0_cl_9:
"cluster zeroORDINAL1V8 for ComplexXCMPLX-0M1"
proof
(*existence*)
  show " ex it be ComplexXCMPLX-0M1 st it be zeroORDINAL1V8"
sorry
qed "sorry"

mtheorem xcmplx_0_cl_10:
"cluster  non zeroORDINAL1V8 for ComplexXCMPLX-0M1"
proof
(*existence*)
  show " ex it be ComplexXCMPLX-0M1 st it be  non zeroORDINAL1V8"
    using xcmplx_0_lm_5 sorry
qed "sorry"

mtheorem xcmplx_0_cl_11:
"cluster  non zeroORDINAL1V8 for ComplexXCMPLX-0M1"
proof
(*existence*)
  show " ex it be ComplexXCMPLX-0M1 st it be  non zeroORDINAL1V8"
    using xcmplx_0_lm_5 sorry
qed "sorry"

mlemma xcmplx_0_lm_6:
"REALNUMBERSK2 c=TARSKIR1 COMPLEXNUMBERSK3"
  using numbers_def_2 xboole_1_th_7 sorry

mtheorem xcmplx_0_cl_12:
  mlet "x be  non zeroORDINAL1V8\<bar>ComplexXCMPLX-0M1"
"cluster -XCMPLX-0K4 x as-term-is  non zeroORDINAL1V8"
proof
(*coherence*)
  show "-XCMPLX-0K4 x be  non zeroORDINAL1V8"
sorry
qed "sorry"

mtheorem xcmplx_0_cl_13:
  mlet "x be  non zeroORDINAL1V8\<bar>ComplexXCMPLX-0M1"
"cluster x \<inverse>XCMPLX-0K5 as-term-is  non zeroORDINAL1V8"
proof
(*coherence*)
  show "x \<inverse>XCMPLX-0K5 be  non zeroORDINAL1V8"
sorry
qed "sorry"

mtheorem xcmplx_0_cl_14:
  mlet "x be  non zeroORDINAL1V8\<bar>ComplexXCMPLX-0M1", "y be  non zeroORDINAL1V8\<bar>ComplexXCMPLX-0M1"
"cluster x *XCMPLX-0K3 y as-term-is  non zeroORDINAL1V8"
proof
(*coherence*)
  show "x *XCMPLX-0K3 y be  non zeroORDINAL1V8"
sorry
qed "sorry"

mtheorem xcmplx_0_cl_15:
  mlet "x be  non zeroORDINAL1V8\<bar>ComplexXCMPLX-0M1", "y be  non zeroORDINAL1V8\<bar>ComplexXCMPLX-0M1"
"cluster x /XCMPLX-0K7 y as-term-is  non zeroORDINAL1V8"
proof
(*coherence*)
  show "x /XCMPLX-0K7 y be  non zeroORDINAL1V8"
     sorry
qed "sorry"

mtheorem xcmplx_0_cl_16:
"cluster note-that complexXCMPLX-0V1 for ElementSUBSET-1M1-of REALNUMBERSK2"
proof
(*coherence*)
  show " for it be ElementSUBSET-1M1-of REALNUMBERSK2 holds it be complexXCMPLX-0V1"
sorry
qed "sorry"

mtheorem xcmplx_0_cl_17:
"cluster note-that complexXCMPLX-0V1 for ElementSUBSET-1M1-of COMPLEXNUMBERSK3"
proof
(*coherence*)
  show " for it be ElementSUBSET-1M1-of COMPLEXNUMBERSK3 holds it be complexXCMPLX-0V1"
     sorry
qed "sorry"

mtheorem xcmplx_0_reduce_1:
  mlet "i be ComplexXCMPLX-0M1"
"reduce InSUBSET-1K10(i,COMPLEXNUMBERSK3) to i"
proof
(*reducibility*)
  show "InSUBSET-1K10(i,COMPLEXNUMBERSK3) =HIDDENR1 i"
    using xcmplx_0_def_2 subset_1_def_8 sorry
qed "sorry"

end
