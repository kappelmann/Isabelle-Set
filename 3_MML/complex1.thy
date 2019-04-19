theory complex1
  imports real_1 square_1 funct_2 card_1 membered
   "../mizar_extension/E_number"
begin
(*begin*)
reserve a, b, c, d for "RealXREAL-0M1"
mtheorem complex1_th_1:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds a ^2SQUARE-1K1 +XCMPLX-0K2 b ^2SQUARE-1K1 =HIDDENR1 0NUMBERSK6 implies a =HIDDENR1 0NUMBERSK6"
sorry

mlemma complex1_lm_1:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds 0NUMBERSK6 <=XXREAL-0R1 a ^2SQUARE-1K1 +XCMPLX-0K2 b ^2SQUARE-1K1"
sorry

mdef complex1_def_1 ("ReCOMPLEX1K1  _ " [228]228 ) where
  mlet "z be ComplexXCMPLX-0M1"
"func ReCOMPLEX1K1 z \<rightarrow> numberORDINAL1M2 means
  \<lambda>it. it =HIDDENR1 z if z be realXREAL-0V1 otherwise \<lambda>it.  ex f be FunctionFUNCT-2M1-of(\<two>\<^sub>M,REALNUMBERSK2) st z =HIDDENR1 f & it =HIDDENR1 f .FUNCT-1K1 (0NUMBERSK6)"
proof-
  (*existence*)
    show "(z be realXREAL-0V1 implies ( ex it be numberORDINAL1M2 st it =HIDDENR1 z)) & ( not z be realXREAL-0V1 implies ( ex it be numberORDINAL1M2 st  ex f be FunctionFUNCT-2M1-of(\<two>\<^sub>M,REALNUMBERSK2) st z =HIDDENR1 f & it =HIDDENR1 f .FUNCT-1K1 (0NUMBERSK6)))"
sorry
  (*uniqueness*)
    show " for it1 be numberORDINAL1M2 holds  for it2 be numberORDINAL1M2 holds (z be realXREAL-0V1 implies (it1 =HIDDENR1 z & it2 =HIDDENR1 z implies it1 =HIDDENR1 it2)) & ( not z be realXREAL-0V1 implies (( ex f be FunctionFUNCT-2M1-of(\<two>\<^sub>M,REALNUMBERSK2) st z =HIDDENR1 f & it1 =HIDDENR1 f .FUNCT-1K1 (0NUMBERSK6)) & ( ex f be FunctionFUNCT-2M1-of(\<two>\<^sub>M,REALNUMBERSK2) st z =HIDDENR1 f & it2 =HIDDENR1 f .FUNCT-1K1 (0NUMBERSK6)) implies it1 =HIDDENR1 it2))"
       sorry
  (*consistency*)
    show " for it be numberORDINAL1M2 holds  True "
       sorry
qed "sorry"

mdef complex1_def_2 ("ImCOMPLEX1K2  _ " [228]228 ) where
  mlet "z be ComplexXCMPLX-0M1"
"func ImCOMPLEX1K2 z \<rightarrow> numberORDINAL1M2 means
  \<lambda>it. it =HIDDENR1 0NUMBERSK6 if z be realXREAL-0V1 otherwise \<lambda>it.  ex f be FunctionFUNCT-2M1-of(\<two>\<^sub>M,REALNUMBERSK2) st z =HIDDENR1 f & it =HIDDENR1 f .FUNCT-1K1 \<one>\<^sub>M"
proof-
  (*existence*)
    show "(z be realXREAL-0V1 implies ( ex it be numberORDINAL1M2 st it =HIDDENR1 0NUMBERSK6)) & ( not z be realXREAL-0V1 implies ( ex it be numberORDINAL1M2 st  ex f be FunctionFUNCT-2M1-of(\<two>\<^sub>M,REALNUMBERSK2) st z =HIDDENR1 f & it =HIDDENR1 f .FUNCT-1K1 \<one>\<^sub>M))"
sorry
  (*uniqueness*)
    show " for it1 be numberORDINAL1M2 holds  for it2 be numberORDINAL1M2 holds (z be realXREAL-0V1 implies (it1 =HIDDENR1 0NUMBERSK6 & it2 =HIDDENR1 0NUMBERSK6 implies it1 =HIDDENR1 it2)) & ( not z be realXREAL-0V1 implies (( ex f be FunctionFUNCT-2M1-of(\<two>\<^sub>M,REALNUMBERSK2) st z =HIDDENR1 f & it1 =HIDDENR1 f .FUNCT-1K1 \<one>\<^sub>M) & ( ex f be FunctionFUNCT-2M1-of(\<two>\<^sub>M,REALNUMBERSK2) st z =HIDDENR1 f & it2 =HIDDENR1 f .FUNCT-1K1 \<one>\<^sub>M) implies it1 =HIDDENR1 it2))"
       sorry
  (*consistency*)
    show " for it be numberORDINAL1M2 holds  True "
       sorry
qed "sorry"

mtheorem complex1_cl_1:
  mlet "z be ComplexXCMPLX-0M1"
"cluster ReCOMPLEX1K1 z as-term-is realXREAL-0V1"
proof
(*coherence*)
  show "ReCOMPLEX1K1 z be realXREAL-0V1"
sorry
qed "sorry"

mtheorem complex1_cl_2:
  mlet "z be ComplexXCMPLX-0M1"
"cluster ImCOMPLEX1K2 z as-term-is realXREAL-0V1"
proof
(*coherence*)
  show "ImCOMPLEX1K2 z be realXREAL-0V1"
sorry
qed "sorry"

abbreviation(input) COMPLEX1K3("ReCOMPLEX1K3  _ " [228]228) where
  "ReCOMPLEX1K3 z \<equiv> ReCOMPLEX1K1 z"

mtheorem complex1_add_1:
  mlet "z be ComplexXCMPLX-0M1"
"cluster ReCOMPLEX1K1 z as-term-is ElementSUBSET-1M1-of REALNUMBERSK2"
proof
(*coherence*)
  show "ReCOMPLEX1K1 z be ElementSUBSET-1M1-of REALNUMBERSK2"
    using xreal_0_def_1 sorry
qed "sorry"

abbreviation(input) COMPLEX1K4("ImCOMPLEX1K4  _ " [228]228) where
  "ImCOMPLEX1K4 z \<equiv> ImCOMPLEX1K2 z"

mtheorem complex1_add_2:
  mlet "z be ComplexXCMPLX-0M1"
"cluster ImCOMPLEX1K2 z as-term-is ElementSUBSET-1M1-of REALNUMBERSK2"
proof
(*coherence*)
  show "ImCOMPLEX1K2 z be ElementSUBSET-1M1-of REALNUMBERSK2"
    using xreal_0_def_1 sorry
qed "sorry"

mtheorem complex1_cl_3:
  mlet "r be RealXREAL-0M1"
"cluster ImCOMPLEX1K4 r as-term-is zeroORDINAL1V8"
proof
(*coherence*)
  show "ImCOMPLEX1K4 r be zeroORDINAL1V8"
sorry
qed "sorry"

mtheorem complex1_th_2:
" for f be FunctionFUNCT-2M1-of(\<two>\<^sub>M,REALNUMBERSK2) holds  ex a be ElementSUBSET-1M1-of REALNUMBERSK2 st  ex b be ElementSUBSET-1M1-of REALNUMBERSK2 st f =FUNCT-2R1\<^bsub>(\<two>\<^sub>M,REALNUMBERSK2,{TARSKIK2 0NUMBERSK6,\<one>\<^sub>M },REALNUMBERSK2)\<^esub> (0NUMBERSK6,\<one>\<^sub>M)-->FUNCT-4K7\<^bsub>(REALNUMBERSK2)\<^esub>(a,b)"
sorry

mlemma complex1_lm_2:
" for a be ElementSUBSET-1M1-of REALNUMBERSK2 holds  for b be ElementSUBSET-1M1-of REALNUMBERSK2 holds ReCOMPLEX1K3 ([*ARYTM-0K5 a,b *]) =HIDDENR1 a & ImCOMPLEX1K4 ([*ARYTM-0K5 a,b *]) =HIDDENR1 b"
sorry

reserve z, z1, z2 for "ComplexXCMPLX-0M1"
mlemma complex1_lm_3:
" for z be ComplexXCMPLX-0M1 holds [*ARYTM-0K5 ReCOMPLEX1K3 z,ImCOMPLEX1K4 z *] =HIDDENR1 z"
sorry

mtheorem complex1_th_3:
" for z1 be ComplexXCMPLX-0M1 holds  for z2 be ComplexXCMPLX-0M1 holds ReCOMPLEX1K3 z1 =HIDDENR1 ReCOMPLEX1K3 z2 & ImCOMPLEX1K4 z1 =HIDDENR1 ImCOMPLEX1K4 z2 implies z1 =HIDDENR1 z2"
sorry

abbreviation(input) COMPLEX1R1(" _ =COMPLEX1R1  _ " [50,50]50) where
  "z1 =COMPLEX1R1 z2 \<equiv> z1 =HIDDENR1 z2"

mtheorem complex1_def_3:
  mlet "z1 be ComplexXCMPLX-0M1", "z2 be ComplexXCMPLX-0M1"
"redefine pred z1 =COMPLEX1R1 z2 means
  ReCOMPLEX1K3 z1 =HIDDENR1 ReCOMPLEX1K3 z2 & ImCOMPLEX1K4 z1 =HIDDENR1 ImCOMPLEX1K4 z2"
proof
(*compatibility*)
  show "z1 =COMPLEX1R1 z2 iff ReCOMPLEX1K3 z1 =HIDDENR1 ReCOMPLEX1K3 z2 & ImCOMPLEX1K4 z1 =HIDDENR1 ImCOMPLEX1K4 z2"
    using complex1_th_3 sorry
qed "sorry"

abbreviation(input) COMPLEX1K5("0cCOMPLEX1K5" 228) where
  "0cCOMPLEX1K5 \<equiv> 0ORDINAL1K5"

abbreviation(input) COMPLEX1K6("0cCOMPLEX1K6" 228) where
  "0cCOMPLEX1K6 \<equiv> 0ORDINAL1K5"

mtheorem complex1_add_3:
"cluster 0ORDINAL1K5 as-term-is ElementSUBSET-1M1-of COMPLEXNUMBERSK3"
proof
(*coherence*)
  show "0ORDINAL1K5 be ElementSUBSET-1M1-of COMPLEXNUMBERSK3"
    using xcmplx_0_def_2 sorry
qed "sorry"

mdef complex1_def_4 ("1rCOMPLEX1K7" 228 ) where
"func 1rCOMPLEX1K7 \<rightarrow> ElementSUBSET-1M1-of COMPLEXNUMBERSK3 equals
  \<one>\<^sub>M"
proof-
  (*coherence*)
    show "\<one>\<^sub>M be ElementSUBSET-1M1-of COMPLEXNUMBERSK3"
      using xcmplx_0_def_2 sorry
qed "sorry"

abbreviation(input) COMPLEX1K8("<i>COMPLEX1K8" 164) where
  "<i>COMPLEX1K8 \<equiv> <i>XCMPLX-0K1"

mtheorem complex1_add_4:
"cluster <i>XCMPLX-0K1 as-term-is ElementSUBSET-1M1-of COMPLEXNUMBERSK3"
proof
(*coherence*)
  show "<i>XCMPLX-0K1 be ElementSUBSET-1M1-of COMPLEXNUMBERSK3"
    using xcmplx_0_def_2 sorry
qed "sorry"

mtheorem complex1_th_4:
"ReCOMPLEX1K3 (0NUMBERSK6) =COMPLEX1R1 0NUMBERSK6 & ImCOMPLEX1K4 (0NUMBERSK6) =COMPLEX1R1 0NUMBERSK6"
sorry

mtheorem complex1_th_5:
" for z be ComplexXCMPLX-0M1 holds z =COMPLEX1R1 0NUMBERSK6 iff (ReCOMPLEX1K3 z)^2SQUARE-1K1 +XCMPLX-0K2 (ImCOMPLEX1K4 z)^2SQUARE-1K1 =COMPLEX1R1 0NUMBERSK6"
  using complex1_th_4 complex1_th_1 sorry

mtheorem complex1_th_6:
"ReCOMPLEX1K3 (1rCOMPLEX1K7) =COMPLEX1R1 \<one>\<^sub>M & ImCOMPLEX1K4 (1rCOMPLEX1K7) =COMPLEX1R1 0NUMBERSK6"
sorry

mtheorem complex1_th_7:
"ReCOMPLEX1K3 (<i>COMPLEX1K8) =COMPLEX1R1 0NUMBERSK6 & ImCOMPLEX1K4 (<i>COMPLEX1K8) =COMPLEX1R1 \<one>\<^sub>M"
sorry

mlemma complex1_lm_4:
" for x be RealXREAL-0M1 holds  for x1 be ElementSUBSET-1M1-of REALNUMBERSK2 holds  for x2 be ElementSUBSET-1M1-of REALNUMBERSK2 holds x =COMPLEX1R1 [*ARYTM-0K5 x1,x2 *] implies x2 =COMPLEX1R1 0NUMBERSK6 & x =COMPLEX1R1 x1"
sorry

mlemma complex1_lm_5:
" for x9 be ElementSUBSET-1M1-of REALNUMBERSK2 holds  for y9 be ElementSUBSET-1M1-of REALNUMBERSK2 holds  for x be RealXREAL-0M1 holds  for y be RealXREAL-0M1 holds x9 =COMPLEX1R1 x & y9 =COMPLEX1R1 y implies +ARYTM-0K1(x9,y9) =COMPLEX1R1 x +XCMPLX-0K2 y"
sorry

mlemma complex1_lm_6:
" for x be ElementSUBSET-1M1-of REALNUMBERSK2 holds oppARYTM-0K3 x =COMPLEX1R1 -REAL-1K1 x"
sorry

mlemma complex1_lm_7:
" for x9 be ElementSUBSET-1M1-of REALNUMBERSK2 holds  for y9 be ElementSUBSET-1M1-of REALNUMBERSK2 holds  for x be RealXREAL-0M1 holds  for y be RealXREAL-0M1 holds x9 =COMPLEX1R1 x & y9 =COMPLEX1R1 y implies  *ARYTM-0K2(x9,y9) =COMPLEX1R1 x *XCMPLX-0K3 y"
sorry

mlemma complex1_lm_8:
" for x be ComplexXCMPLX-0M1 holds  for y be ComplexXCMPLX-0M1 holds  for z be ComplexXCMPLX-0M1 holds z =COMPLEX1R1 x +XCMPLX-0K2 y implies ReCOMPLEX1K3 z =COMPLEX1R1 ReCOMPLEX1K3 x +REAL-1K3 ReCOMPLEX1K3 y"
sorry

mlemma complex1_lm_9:
" for x be ComplexXCMPLX-0M1 holds  for y be ComplexXCMPLX-0M1 holds  for z be ComplexXCMPLX-0M1 holds z =COMPLEX1R1 x +XCMPLX-0K2 y implies ImCOMPLEX1K4 z =COMPLEX1R1 ImCOMPLEX1K4 x +REAL-1K3 ImCOMPLEX1K4 y"
sorry

mlemma complex1_lm_10:
" for x be ComplexXCMPLX-0M1 holds  for y be ComplexXCMPLX-0M1 holds  for z be ComplexXCMPLX-0M1 holds z =COMPLEX1R1 x *XCMPLX-0K3 y implies ReCOMPLEX1K3 z =COMPLEX1R1 ReCOMPLEX1K3 x *REAL-1K4 ReCOMPLEX1K3 y -REAL-1K5 ImCOMPLEX1K4 x *REAL-1K4 ImCOMPLEX1K4 y"
sorry

mlemma complex1_lm_11:
" for x be ComplexXCMPLX-0M1 holds  for y be ComplexXCMPLX-0M1 holds  for z be ComplexXCMPLX-0M1 holds z =COMPLEX1R1 x *XCMPLX-0K3 y implies ImCOMPLEX1K4 z =COMPLEX1R1 ReCOMPLEX1K3 x *REAL-1K4 ImCOMPLEX1K4 y +REAL-1K3 ImCOMPLEX1K4 x *REAL-1K4 ReCOMPLEX1K3 y"
sorry

mlemma complex1_lm_12:
" for z1 be ComplexXCMPLX-0M1 holds  for z2 be ComplexXCMPLX-0M1 holds z1 +XCMPLX-0K2 z2 =COMPLEX1R1 [*ARYTM-0K5 ReCOMPLEX1K3 z1 +REAL-1K3 ReCOMPLEX1K3 z2,ImCOMPLEX1K4 z1 +REAL-1K3 ImCOMPLEX1K4 z2 *]"
sorry

mlemma complex1_lm_13:
" for z1 be ComplexXCMPLX-0M1 holds  for z2 be ComplexXCMPLX-0M1 holds z1 *XCMPLX-0K3 z2 =COMPLEX1R1 [*ARYTM-0K5 ReCOMPLEX1K3 z1 *REAL-1K4 ReCOMPLEX1K3 z2 -REAL-1K5 ImCOMPLEX1K4 z1 *REAL-1K4 ImCOMPLEX1K4 z2,ReCOMPLEX1K3 z1 *REAL-1K4 ImCOMPLEX1K4 z2 +REAL-1K3 ReCOMPLEX1K3 z2 *REAL-1K4 ImCOMPLEX1K4 z1 *]"
sorry

mlemma complex1_lm_14:
" for z1 be ComplexXCMPLX-0M1 holds  for z2 be ComplexXCMPLX-0M1 holds ReCOMPLEX1K3 (z1 *XCMPLX-0K3 z2) =COMPLEX1R1 ReCOMPLEX1K3 z1 *REAL-1K4 ReCOMPLEX1K3 z2 -REAL-1K5 ImCOMPLEX1K4 z1 *REAL-1K4 ImCOMPLEX1K4 z2 & ImCOMPLEX1K4 (z1 *XCMPLX-0K3 z2) =COMPLEX1R1 ReCOMPLEX1K3 z1 *REAL-1K4 ImCOMPLEX1K4 z2 +REAL-1K3 ReCOMPLEX1K3 z2 *REAL-1K4 ImCOMPLEX1K4 z1"
sorry

mlemma complex1_lm_15:
" for z1 be ComplexXCMPLX-0M1 holds  for z2 be ComplexXCMPLX-0M1 holds ReCOMPLEX1K3 (z1 +XCMPLX-0K2 z2) =COMPLEX1R1 ReCOMPLEX1K3 z1 +REAL-1K3 ReCOMPLEX1K3 z2 & ImCOMPLEX1K4 (z1 +XCMPLX-0K2 z2) =COMPLEX1R1 ImCOMPLEX1K4 z1 +REAL-1K3 ImCOMPLEX1K4 z2"
sorry

mlemma complex1_lm_16:
" for x be ElementSUBSET-1M1-of REALNUMBERSK2 holds ReCOMPLEX1K3 (x *XCMPLX-0K3 (<i>COMPLEX1K8)) =COMPLEX1R1 0NUMBERSK6"
sorry

mlemma complex1_lm_17:
" for x be ElementSUBSET-1M1-of REALNUMBERSK2 holds ImCOMPLEX1K4 (x *XCMPLX-0K3 (<i>COMPLEX1K8)) =COMPLEX1R1 x"
sorry

mlemma complex1_lm_18:
" for x be ElementSUBSET-1M1-of REALNUMBERSK2 holds  for y be ElementSUBSET-1M1-of REALNUMBERSK2 holds [*ARYTM-0K5 x,y *] =COMPLEX1R1 x +XCMPLX-0K2 y *XCMPLX-0K3 (<i>COMPLEX1K8)"
sorry

(*\$CD*)
mtheorem complex1_th_8:
" for z1 be ComplexXCMPLX-0M1 holds  for z2 be ComplexXCMPLX-0M1 holds ReCOMPLEX1K3 (z1 +XCMPLX-0K2 z2) =COMPLEX1R1 ReCOMPLEX1K3 z1 +REAL-1K3 ReCOMPLEX1K3 z2 & ImCOMPLEX1K4 (z1 +XCMPLX-0K2 z2) =COMPLEX1R1 ImCOMPLEX1K4 z1 +REAL-1K3 ImCOMPLEX1K4 z2"
sorry

(*\$CD*)
mtheorem complex1_th_9:
" for z1 be ComplexXCMPLX-0M1 holds  for z2 be ComplexXCMPLX-0M1 holds ReCOMPLEX1K3 (z1 *XCMPLX-0K3 z2) =COMPLEX1R1 ReCOMPLEX1K3 z1 *REAL-1K4 ReCOMPLEX1K3 z2 -REAL-1K5 ImCOMPLEX1K4 z1 *REAL-1K4 ImCOMPLEX1K4 z2 & ImCOMPLEX1K4 (z1 *XCMPLX-0K3 z2) =COMPLEX1R1 ReCOMPLEX1K3 z1 *REAL-1K4 ImCOMPLEX1K4 z2 +REAL-1K3 ReCOMPLEX1K3 z2 *REAL-1K4 ImCOMPLEX1K4 z1"
sorry

mtheorem complex1_th_10:
" for a be RealXREAL-0M1 holds ReCOMPLEX1K3 (a *XCMPLX-0K3 (<i>COMPLEX1K8)) =COMPLEX1R1 0NUMBERSK6"
sorry

mtheorem complex1_th_11:
" for a be RealXREAL-0M1 holds ImCOMPLEX1K4 (a *XCMPLX-0K3 (<i>COMPLEX1K8)) =COMPLEX1R1 a"
sorry

mtheorem complex1_th_12:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds ReCOMPLEX1K3 (a +XCMPLX-0K2 b *XCMPLX-0K3 (<i>COMPLEX1K8)) =COMPLEX1R1 a & ImCOMPLEX1K4 (a +XCMPLX-0K2 b *XCMPLX-0K3 (<i>COMPLEX1K8)) =COMPLEX1R1 b"
sorry

mtheorem complex1_th_13:
" for z be ComplexXCMPLX-0M1 holds ReCOMPLEX1K3 z +XCMPLX-0K2 ImCOMPLEX1K4 z *XCMPLX-0K3 (<i>COMPLEX1K8) =COMPLEX1R1 z"
sorry

mtheorem complex1_th_14:
" for z1 be ComplexXCMPLX-0M1 holds  for z2 be ComplexXCMPLX-0M1 holds ImCOMPLEX1K4 z1 =COMPLEX1R1 0NUMBERSK6 & ImCOMPLEX1K4 z2 =COMPLEX1R1 0NUMBERSK6 implies ReCOMPLEX1K3 (z1 *XCMPLX-0K3 z2) =COMPLEX1R1 ReCOMPLEX1K3 z1 *REAL-1K4 ReCOMPLEX1K3 z2 & ImCOMPLEX1K4 (z1 *XCMPLX-0K3 z2) =COMPLEX1R1 0NUMBERSK6"
sorry

mtheorem complex1_th_15:
" for z1 be ComplexXCMPLX-0M1 holds  for z2 be ComplexXCMPLX-0M1 holds ReCOMPLEX1K3 z1 =COMPLEX1R1 0NUMBERSK6 & ReCOMPLEX1K3 z2 =COMPLEX1R1 0NUMBERSK6 implies ReCOMPLEX1K3 (z1 *XCMPLX-0K3 z2) =COMPLEX1R1 -REAL-1K1 ImCOMPLEX1K4 z1 *REAL-1K4 ImCOMPLEX1K4 z2 & ImCOMPLEX1K4 (z1 *XCMPLX-0K3 z2) =COMPLEX1R1 0NUMBERSK6"
sorry

mtheorem complex1_th_16:
" for z be ComplexXCMPLX-0M1 holds ReCOMPLEX1K3 (z *XCMPLX-0K3 z) =COMPLEX1R1 (ReCOMPLEX1K3 z)^2SQUARE-1K1 -XCMPLX-0K6 (ImCOMPLEX1K4 z)^2SQUARE-1K1 & ImCOMPLEX1K4 (z *XCMPLX-0K3 z) =COMPLEX1R1 \<two>\<^sub>M *XCMPLX-0K3 (ReCOMPLEX1K3 z *REAL-1K4 ImCOMPLEX1K4 z)"
sorry

(*\$CD*)
mlemma complex1_lm_19:
" for z be ComplexXCMPLX-0M1 holds -XCMPLX-0K4 z =COMPLEX1R1 (-REAL-1K1 ReCOMPLEX1K3 z)+XCMPLX-0K2 (-REAL-1K1 ImCOMPLEX1K4 z)*XCMPLX-0K3 (<i>COMPLEX1K8)"
sorry

mtheorem complex1_th_17:
" for z be ComplexXCMPLX-0M1 holds ReCOMPLEX1K3 (-XCMPLX-0K4 z) =COMPLEX1R1 -REAL-1K1 ReCOMPLEX1K3 z & ImCOMPLEX1K4 (-XCMPLX-0K4 z) =COMPLEX1R1 -REAL-1K1 ImCOMPLEX1K4 z"
sorry

mtheorem complex1_th_18:
"(<i>COMPLEX1K8)*XCMPLX-0K3 (<i>COMPLEX1K8) =COMPLEX1R1 -XCMPLX-0K4 1rCOMPLEX1K7"
   sorry

(*\$CD*)
mlemma complex1_lm_20:
" for z1 be ComplexXCMPLX-0M1 holds  for z2 be ComplexXCMPLX-0M1 holds z1 -XCMPLX-0K6 z2 =COMPLEX1R1 (ReCOMPLEX1K3 z1 -REAL-1K5 ReCOMPLEX1K3 z2)+XCMPLX-0K2 (ImCOMPLEX1K4 z1 -REAL-1K5 ImCOMPLEX1K4 z2)*XCMPLX-0K3 (<i>COMPLEX1K8)"
sorry

mtheorem complex1_th_19:
" for z1 be ComplexXCMPLX-0M1 holds  for z2 be ComplexXCMPLX-0M1 holds ReCOMPLEX1K3 (z1 -XCMPLX-0K6 z2) =COMPLEX1R1 ReCOMPLEX1K3 z1 -REAL-1K5 ReCOMPLEX1K3 z2 & ImCOMPLEX1K4 (z1 -XCMPLX-0K6 z2) =COMPLEX1R1 ImCOMPLEX1K4 z1 -REAL-1K5 ImCOMPLEX1K4 z2"
sorry

(*\$CD*)
mlemma complex1_lm_21:
" for z be ComplexXCMPLX-0M1 holds z \<inverse>XCMPLX-0K5 =COMPLEX1R1 ReCOMPLEX1K3 z /XCMPLX-0K7 ((ReCOMPLEX1K3 z)^2SQUARE-1K1 +XCMPLX-0K2 (ImCOMPLEX1K4 z)^2SQUARE-1K1) +XCMPLX-0K2 ((-REAL-1K1 ImCOMPLEX1K4 z)/XCMPLX-0K7 ((ReCOMPLEX1K3 z)^2SQUARE-1K1 +XCMPLX-0K2 (ImCOMPLEX1K4 z)^2SQUARE-1K1))*XCMPLX-0K3 (<i>COMPLEX1K8)"
sorry

mtheorem complex1_th_20:
" for z be ComplexXCMPLX-0M1 holds ReCOMPLEX1K3 (z \<inverse>XCMPLX-0K5) =COMPLEX1R1 ReCOMPLEX1K3 z /XCMPLX-0K7 ((ReCOMPLEX1K3 z)^2SQUARE-1K1 +XCMPLX-0K2 (ImCOMPLEX1K4 z)^2SQUARE-1K1) & ImCOMPLEX1K4 (z \<inverse>XCMPLX-0K5) =COMPLEX1R1 (-REAL-1K1 ImCOMPLEX1K4 z)/XCMPLX-0K7 ((ReCOMPLEX1K3 z)^2SQUARE-1K1 +XCMPLX-0K2 (ImCOMPLEX1K4 z)^2SQUARE-1K1)"
sorry

mtheorem complex1_th_21:
"(<i>COMPLEX1K8)\<inverse>XCMPLX-0K5 =COMPLEX1R1 -XCMPLX-0K4 <i>COMPLEX1K8"
   sorry

mtheorem complex1_th_22:
" for z be ComplexXCMPLX-0M1 holds ReCOMPLEX1K3 z <>HIDDENR2 0NUMBERSK6 & ImCOMPLEX1K4 z =COMPLEX1R1 0NUMBERSK6 implies ReCOMPLEX1K3 (z \<inverse>XCMPLX-0K5) =COMPLEX1R1 (ReCOMPLEX1K3 z)\<inverse>REAL-1K2 & ImCOMPLEX1K4 (z \<inverse>XCMPLX-0K5) =COMPLEX1R1 0NUMBERSK6"
sorry

mtheorem complex1_th_23:
" for z be ComplexXCMPLX-0M1 holds ReCOMPLEX1K3 z =COMPLEX1R1 0NUMBERSK6 & ImCOMPLEX1K4 z <>HIDDENR2 0NUMBERSK6 implies ReCOMPLEX1K3 (z \<inverse>XCMPLX-0K5) =COMPLEX1R1 0NUMBERSK6 & ImCOMPLEX1K4 (z \<inverse>XCMPLX-0K5) =COMPLEX1R1 -REAL-1K1 (ImCOMPLEX1K4 z)\<inverse>REAL-1K2"
sorry

(*\$CD*)
mlemma complex1_lm_22:
" for z1 be ComplexXCMPLX-0M1 holds  for z2 be ComplexXCMPLX-0M1 holds z1 /XCMPLX-0K7 z2 =COMPLEX1R1 (ReCOMPLEX1K3 z1 *REAL-1K4 ReCOMPLEX1K3 z2 +REAL-1K3 ImCOMPLEX1K4 z1 *REAL-1K4 ImCOMPLEX1K4 z2)/XCMPLX-0K7 ((ReCOMPLEX1K3 z2)^2SQUARE-1K1 +XCMPLX-0K2 (ImCOMPLEX1K4 z2)^2SQUARE-1K1) +XCMPLX-0K2 ((ReCOMPLEX1K3 z2 *REAL-1K4 ImCOMPLEX1K4 z1 -REAL-1K5 ReCOMPLEX1K3 z1 *REAL-1K4 ImCOMPLEX1K4 z2)/XCMPLX-0K7 ((ReCOMPLEX1K3 z2)^2SQUARE-1K1 +XCMPLX-0K2 (ImCOMPLEX1K4 z2)^2SQUARE-1K1))*XCMPLX-0K3 (<i>COMPLEX1K8)"
sorry

mtheorem complex1_th_24:
" for z1 be ComplexXCMPLX-0M1 holds  for z2 be ComplexXCMPLX-0M1 holds ReCOMPLEX1K3 (z1 /XCMPLX-0K7 z2) =COMPLEX1R1 (ReCOMPLEX1K3 z1 *REAL-1K4 ReCOMPLEX1K3 z2 +REAL-1K3 ImCOMPLEX1K4 z1 *REAL-1K4 ImCOMPLEX1K4 z2)/XCMPLX-0K7 ((ReCOMPLEX1K3 z2)^2SQUARE-1K1 +XCMPLX-0K2 (ImCOMPLEX1K4 z2)^2SQUARE-1K1) & ImCOMPLEX1K4 (z1 /XCMPLX-0K7 z2) =COMPLEX1R1 (ReCOMPLEX1K3 z2 *REAL-1K4 ImCOMPLEX1K4 z1 -REAL-1K5 ReCOMPLEX1K3 z1 *REAL-1K4 ImCOMPLEX1K4 z2)/XCMPLX-0K7 ((ReCOMPLEX1K3 z2)^2SQUARE-1K1 +XCMPLX-0K2 (ImCOMPLEX1K4 z2)^2SQUARE-1K1)"
sorry

mtheorem complex1_th_25:
" for z1 be ComplexXCMPLX-0M1 holds  for z2 be ComplexXCMPLX-0M1 holds (ImCOMPLEX1K4 z1 =COMPLEX1R1 0NUMBERSK6 & ImCOMPLEX1K4 z2 =COMPLEX1R1 0NUMBERSK6) & ReCOMPLEX1K3 z2 <>HIDDENR2 0NUMBERSK6 implies ReCOMPLEX1K3 (z1 /XCMPLX-0K7 z2) =COMPLEX1R1 ReCOMPLEX1K3 z1 /REAL-1K6 ReCOMPLEX1K3 z2 & ImCOMPLEX1K4 (z1 /XCMPLX-0K7 z2) =COMPLEX1R1 0NUMBERSK6"
sorry

mtheorem complex1_th_26:
" for z1 be ComplexXCMPLX-0M1 holds  for z2 be ComplexXCMPLX-0M1 holds (ReCOMPLEX1K3 z1 =COMPLEX1R1 0NUMBERSK6 & ReCOMPLEX1K3 z2 =COMPLEX1R1 0NUMBERSK6) & ImCOMPLEX1K4 z2 <>HIDDENR2 0NUMBERSK6 implies ReCOMPLEX1K3 (z1 /XCMPLX-0K7 z2) =COMPLEX1R1 ImCOMPLEX1K4 z1 /REAL-1K6 ImCOMPLEX1K4 z2 & ImCOMPLEX1K4 (z1 /XCMPLX-0K7 z2) =COMPLEX1R1 0NUMBERSK6"
sorry

mdef complex1_def_11 (" _ *''COMPLEX1K9" [228]228 ) where
  mlet "z be ComplexXCMPLX-0M1"
"func z *'COMPLEX1K9 \<rightarrow> ComplexXCMPLX-0M1 equals
  ReCOMPLEX1K3 z -XCMPLX-0K6 ImCOMPLEX1K4 z *XCMPLX-0K3 (<i>COMPLEX1K8)"
proof-
  (*coherence*)
    show "ReCOMPLEX1K3 z -XCMPLX-0K6 ImCOMPLEX1K4 z *XCMPLX-0K3 (<i>COMPLEX1K8) be ComplexXCMPLX-0M1"
       sorry
qed "sorry"

mtheorem COMPLEX1K9_involutiveness:
" for z be ComplexXCMPLX-0M1 holds (z *'COMPLEX1K9)*'COMPLEX1K9 =HIDDENR1 z"
sorry

mtheorem complex1_th_27:
" for z be ComplexXCMPLX-0M1 holds ReCOMPLEX1K3 (z *'COMPLEX1K9) =COMPLEX1R1 ReCOMPLEX1K3 z & ImCOMPLEX1K4 (z *'COMPLEX1K9) =COMPLEX1R1 -REAL-1K1 ImCOMPLEX1K4 z"
sorry

mtheorem complex1_th_28:
"(0NUMBERSK6)*'COMPLEX1K9 =COMPLEX1R1 0NUMBERSK6"
  using complex1_th_4 sorry

mtheorem complex1_th_29:
" for z be ComplexXCMPLX-0M1 holds z *'COMPLEX1K9 =COMPLEX1R1 0NUMBERSK6 implies z =COMPLEX1R1 0NUMBERSK6"
sorry

mtheorem complex1_th_30:
"(1rCOMPLEX1K7)*'COMPLEX1K9 =COMPLEX1R1 1rCOMPLEX1K7"
  using complex1_th_6 sorry

mtheorem complex1_th_31:
"(<i>COMPLEX1K8)*'COMPLEX1K9 =COMPLEX1R1 -XCMPLX-0K4 <i>COMPLEX1K8"
  using complex1_th_7 sorry

mtheorem complex1_th_32:
" for z1 be ComplexXCMPLX-0M1 holds  for z2 be ComplexXCMPLX-0M1 holds (z1 +XCMPLX-0K2 z2)*'COMPLEX1K9 =COMPLEX1R1 z1 *'COMPLEX1K9 +XCMPLX-0K2 z2 *'COMPLEX1K9"
sorry

mtheorem complex1_th_33:
" for z be ComplexXCMPLX-0M1 holds (-XCMPLX-0K4 z)*'COMPLEX1K9 =COMPLEX1R1 -XCMPLX-0K4 z *'COMPLEX1K9"
sorry

mtheorem complex1_th_34:
" for z1 be ComplexXCMPLX-0M1 holds  for z2 be ComplexXCMPLX-0M1 holds (z1 -XCMPLX-0K6 z2)*'COMPLEX1K9 =COMPLEX1R1 z1 *'COMPLEX1K9 -XCMPLX-0K6 z2 *'COMPLEX1K9"
sorry

mtheorem complex1_th_35:
" for z1 be ComplexXCMPLX-0M1 holds  for z2 be ComplexXCMPLX-0M1 holds (z1 *XCMPLX-0K3 z2)*'COMPLEX1K9 =COMPLEX1R1 z1 *'COMPLEX1K9 *XCMPLX-0K3 z2 *'COMPLEX1K9"
sorry

mtheorem complex1_th_36:
" for z be ComplexXCMPLX-0M1 holds (z \<inverse>XCMPLX-0K5)*'COMPLEX1K9 =COMPLEX1R1 (z *'COMPLEX1K9)\<inverse>XCMPLX-0K5"
sorry

mtheorem complex1_th_37:
" for z1 be ComplexXCMPLX-0M1 holds  for z2 be ComplexXCMPLX-0M1 holds (z1 /XCMPLX-0K7 z2)*'COMPLEX1K9 =COMPLEX1R1 z1 *'COMPLEX1K9 /XCMPLX-0K7 z2 *'COMPLEX1K9"
sorry

mtheorem complex1_th_38:
" for z be ComplexXCMPLX-0M1 holds ImCOMPLEX1K4 z =COMPLEX1R1 0NUMBERSK6 implies z *'COMPLEX1K9 =COMPLEX1R1 z"
  using complex1_th_27 sorry

mtheorem complex1_reduce_1:
  mlet "r be RealXREAL-0M1"
"reduce r *'COMPLEX1K9 to r"
proof
(*reducibility*)
  show "r *'COMPLEX1K9 =HIDDENR1 r"
    using complex1_th_38 sorry
qed "sorry"

mtheorem complex1_th_39:
" for z be ComplexXCMPLX-0M1 holds ReCOMPLEX1K3 z =COMPLEX1R1 0NUMBERSK6 implies z *'COMPLEX1K9 =COMPLEX1R1 -XCMPLX-0K4 z"
sorry

mtheorem complex1_th_40:
" for z be ComplexXCMPLX-0M1 holds ReCOMPLEX1K3 (z *XCMPLX-0K3 z *'COMPLEX1K9) =COMPLEX1R1 (ReCOMPLEX1K3 z)^2SQUARE-1K1 +XCMPLX-0K2 (ImCOMPLEX1K4 z)^2SQUARE-1K1 & ImCOMPLEX1K4 (z *XCMPLX-0K3 z *'COMPLEX1K9) =COMPLEX1R1 0NUMBERSK6"
sorry

mtheorem complex1_th_41:
" for z be ComplexXCMPLX-0M1 holds ReCOMPLEX1K3 (z +XCMPLX-0K2 z *'COMPLEX1K9) =COMPLEX1R1 \<two>\<^sub>M *XCMPLX-0K3 ReCOMPLEX1K3 z & ImCOMPLEX1K4 (z +XCMPLX-0K2 z *'COMPLEX1K9) =COMPLEX1R1 0NUMBERSK6"
sorry

mtheorem complex1_th_42:
" for z be ComplexXCMPLX-0M1 holds ReCOMPLEX1K3 (z -XCMPLX-0K6 z *'COMPLEX1K9) =COMPLEX1R1 0NUMBERSK6 & ImCOMPLEX1K4 (z -XCMPLX-0K6 z *'COMPLEX1K9) =COMPLEX1R1 \<two>\<^sub>M *XCMPLX-0K3 ImCOMPLEX1K4 z"
sorry

mdef complex1_def_12 ("|.COMPLEX1K10  _ .|" [0]164 ) where
  mlet "z be ComplexXCMPLX-0M1"
"func |.COMPLEX1K10 z.| \<rightarrow> RealXREAL-0M1 equals
  sqrtSQUARE-1K3 ((ReCOMPLEX1K3 z)^2SQUARE-1K1 +XCMPLX-0K2 (ImCOMPLEX1K4 z)^2SQUARE-1K1)"
proof-
  (*coherence*)
    show "sqrtSQUARE-1K3 ((ReCOMPLEX1K3 z)^2SQUARE-1K1 +XCMPLX-0K2 (ImCOMPLEX1K4 z)^2SQUARE-1K1) be RealXREAL-0M1"
       sorry
qed "sorry"

mtheorem COMPLEX1K10_projectivity:
" for z be ComplexXCMPLX-0M1 holds |.COMPLEX1K10 |.COMPLEX1K10 z.| .| =HIDDENR1 |.COMPLEX1K10 z.|"
sorry

mtheorem complex1_th_43:
" for a be RealXREAL-0M1 holds a >=XXREAL-0R2 0NUMBERSK6 implies |.COMPLEX1K10 a.| =COMPLEX1R1 a"
sorry

mtheorem complex1_cl_4:
  mlet "z be zeroORDINAL1V8\<bar>ComplexXCMPLX-0M1"
"cluster |.COMPLEX1K10 z.| as-term-is zeroORDINAL1V8"
proof
(*coherence*)
  show "|.COMPLEX1K10 z.| be zeroORDINAL1V8"
    using complex1_th_4 square_1_th_17 sorry
qed "sorry"

mtheorem complex1_th_44:
"|.COMPLEX1K10 0NUMBERSK6 .| =COMPLEX1R1 0NUMBERSK6"
   sorry

mtheorem complex1_cl_5:
  mlet "z be  non zeroORDINAL1V8\<bar>ComplexXCMPLX-0M1"
"cluster |.COMPLEX1K10 z.| as-term-is  non zeroORDINAL1V8"
proof
(*coherence*)
  show "|.COMPLEX1K10 z.| be  non zeroORDINAL1V8"
sorry
qed "sorry"

mtheorem complex1_th_45:
" for z be ComplexXCMPLX-0M1 holds |.COMPLEX1K10 z.| =COMPLEX1R1 0NUMBERSK6 implies z =COMPLEX1R1 0NUMBERSK6"
   sorry

mtheorem complex1_cl_6:
  mlet "z be ComplexXCMPLX-0M1"
"cluster |.COMPLEX1K10 z.| as-term-is  non negativeXXREAL-0V3"
proof
(*coherence*)
  show "|.COMPLEX1K10 z.| be  non negativeXXREAL-0V3"
sorry
qed "sorry"

mtheorem complex1_th_46:
" for z be ComplexXCMPLX-0M1 holds 0NUMBERSK6 <=XXREAL-0R1 |.COMPLEX1K10 z.|"
   sorry

mtheorem complex1_th_47:
" for z be ComplexXCMPLX-0M1 holds z <>HIDDENR2 0NUMBERSK6 iff 0NUMBERSK6 <XXREAL-0R3 |.COMPLEX1K10 z.|"
   sorry

mtheorem complex1_th_48:
"|.COMPLEX1K10 1rCOMPLEX1K7.| =COMPLEX1R1 \<one>\<^sub>M"
  using complex1_th_6 square_1_th_18 sorry

mtheorem complex1_th_49:
"|.COMPLEX1K10 <i>COMPLEX1K8 .| =COMPLEX1R1 \<one>\<^sub>M"
  using complex1_th_7 square_1_th_18 sorry

mlemma complex1_lm_23:
" for z be ComplexXCMPLX-0M1 holds |.COMPLEX1K10 -XCMPLX-0K4 z .| =COMPLEX1R1 |.COMPLEX1K10 z.|"
sorry

mlemma complex1_lm_24:
" for a be RealXREAL-0M1 holds a <=XXREAL-0R1 0NUMBERSK6 implies |.COMPLEX1K10 a.| =COMPLEX1R1 -XCMPLX-0K4 a"
sorry

mlemma complex1_lm_25:
" for a be RealXREAL-0M1 holds sqrtSQUARE-1K3 a ^2SQUARE-1K1 =COMPLEX1R1 |.COMPLEX1K10 a.|"
sorry

mtheorem complex1_th_50:
" for z be ComplexXCMPLX-0M1 holds ImCOMPLEX1K4 z =COMPLEX1R1 0NUMBERSK6 implies |.COMPLEX1K10 z.| =COMPLEX1R1 |.COMPLEX1K10 ReCOMPLEX1K3 z.|"
  using complex1_lm_25 sorry

mtheorem complex1_th_51:
" for z be ComplexXCMPLX-0M1 holds ReCOMPLEX1K3 z =COMPLEX1R1 0NUMBERSK6 implies |.COMPLEX1K10 z.| =COMPLEX1R1 |.COMPLEX1K10 ImCOMPLEX1K4 z.|"
  using complex1_lm_25 sorry

mtheorem complex1_th_52:
" for z be ComplexXCMPLX-0M1 holds |.COMPLEX1K10 -XCMPLX-0K4 z .| =COMPLEX1R1 |.COMPLEX1K10 z.|"
  using complex1_lm_23 sorry

mtheorem complex1_th_53:
" for z be ComplexXCMPLX-0M1 holds |.COMPLEX1K10 z *'COMPLEX1K9.| =COMPLEX1R1 |.COMPLEX1K10 z.|"
sorry

mlemma complex1_lm_26:
" for a be RealXREAL-0M1 holds -XCMPLX-0K4 |.COMPLEX1K10 a.| <=XXREAL-0R1 a & a <=XXREAL-0R1 |.COMPLEX1K10 a.|"
sorry

mtheorem complex1_th_54:
" for z be ComplexXCMPLX-0M1 holds ReCOMPLEX1K3 z <=XXREAL-0R1 |.COMPLEX1K10 z.|"
sorry

mtheorem complex1_th_55:
" for z be ComplexXCMPLX-0M1 holds ImCOMPLEX1K4 z <=XXREAL-0R1 |.COMPLEX1K10 z.|"
sorry

mtheorem complex1_th_56:
" for z1 be ComplexXCMPLX-0M1 holds  for z2 be ComplexXCMPLX-0M1 holds |.COMPLEX1K10 z1 +XCMPLX-0K2 z2 .| <=XXREAL-0R1 |.COMPLEX1K10 z1.| +XCMPLX-0K2 |.COMPLEX1K10 z2.|"
sorry

mtheorem complex1_th_57:
" for z1 be ComplexXCMPLX-0M1 holds  for z2 be ComplexXCMPLX-0M1 holds |.COMPLEX1K10 z1 -XCMPLX-0K6 z2 .| <=XXREAL-0R1 |.COMPLEX1K10 z1.| +XCMPLX-0K2 |.COMPLEX1K10 z2.|"
sorry

mtheorem complex1_th_58:
" for z1 be ComplexXCMPLX-0M1 holds  for z2 be ComplexXCMPLX-0M1 holds |.COMPLEX1K10 z1.| -XCMPLX-0K6 |.COMPLEX1K10 z2.| <=XXREAL-0R1 |.COMPLEX1K10 z1 +XCMPLX-0K2 z2 .|"
sorry

mtheorem complex1_th_59:
" for z1 be ComplexXCMPLX-0M1 holds  for z2 be ComplexXCMPLX-0M1 holds |.COMPLEX1K10 z1.| -XCMPLX-0K6 |.COMPLEX1K10 z2.| <=XXREAL-0R1 |.COMPLEX1K10 z1 -XCMPLX-0K6 z2 .|"
sorry

mtheorem complex1_th_60:
" for z1 be ComplexXCMPLX-0M1 holds  for z2 be ComplexXCMPLX-0M1 holds |.COMPLEX1K10 z1 -XCMPLX-0K6 z2 .| =COMPLEX1R1 |.COMPLEX1K10 z2 -XCMPLX-0K6 z1 .|"
sorry

mtheorem complex1_th_61:
" for z1 be ComplexXCMPLX-0M1 holds  for z2 be ComplexXCMPLX-0M1 holds |.COMPLEX1K10 z1 -XCMPLX-0K6 z2 .| =COMPLEX1R1 0NUMBERSK6 iff z1 =COMPLEX1R1 z2"
sorry

mtheorem complex1_th_62:
" for z1 be ComplexXCMPLX-0M1 holds  for z2 be ComplexXCMPLX-0M1 holds z1 <>HIDDENR2 z2 iff 0NUMBERSK6 <XXREAL-0R3 |.COMPLEX1K10 z1 -XCMPLX-0K6 z2 .|"
sorry

mtheorem complex1_th_63:
" for z be ComplexXCMPLX-0M1 holds  for z1 be ComplexXCMPLX-0M1 holds  for z2 be ComplexXCMPLX-0M1 holds |.COMPLEX1K10 z1 -XCMPLX-0K6 z2 .| <=XXREAL-0R1 |.COMPLEX1K10 z1 -XCMPLX-0K6 z .| +XCMPLX-0K2 |.COMPLEX1K10 z -XCMPLX-0K6 z2 .|"
sorry

mlemma complex1_lm_27:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds -XCMPLX-0K4 b <=XXREAL-0R1 a & a <=XXREAL-0R1 b iff |.COMPLEX1K10 a.| <=XXREAL-0R1 b"
sorry

mtheorem complex1_th_64:
" for z1 be ComplexXCMPLX-0M1 holds  for z2 be ComplexXCMPLX-0M1 holds |.COMPLEX1K10 |.COMPLEX1K10 z1.| -XCMPLX-0K6 |.COMPLEX1K10 z2.| .| <=XXREAL-0R1 |.COMPLEX1K10 z1 -XCMPLX-0K6 z2 .|"
sorry

mtheorem complex1_th_65:
" for z1 be ComplexXCMPLX-0M1 holds  for z2 be ComplexXCMPLX-0M1 holds |.COMPLEX1K10 z1 *XCMPLX-0K3 z2 .| =COMPLEX1R1 (|.COMPLEX1K10 z1.|)*XCMPLX-0K3 (|.COMPLEX1K10 z2.|)"
sorry

mtheorem complex1_th_66:
" for z be ComplexXCMPLX-0M1 holds |.COMPLEX1K10 z \<inverse>XCMPLX-0K5.| =COMPLEX1R1 (|.COMPLEX1K10 z.|)\<inverse>XCMPLX-0K5"
sorry

mtheorem complex1_th_67:
" for z1 be ComplexXCMPLX-0M1 holds  for z2 be ComplexXCMPLX-0M1 holds (|.COMPLEX1K10 z1.|)/XCMPLX-0K7 (|.COMPLEX1K10 z2.|) =COMPLEX1R1 |.COMPLEX1K10 z1 /XCMPLX-0K7 z2 .|"
sorry

mtheorem complex1_th_68:
" for z be ComplexXCMPLX-0M1 holds |.COMPLEX1K10 z *XCMPLX-0K3 z .| =COMPLEX1R1 (ReCOMPLEX1K3 z)^2SQUARE-1K1 +XCMPLX-0K2 (ImCOMPLEX1K4 z)^2SQUARE-1K1"
sorry

mtheorem complex1_th_69:
" for z be ComplexXCMPLX-0M1 holds |.COMPLEX1K10 z *XCMPLX-0K3 z .| =COMPLEX1R1 |.COMPLEX1K10 z *XCMPLX-0K3 z *'COMPLEX1K9 .|"
sorry

mtheorem complex1_th_70:
" for a be RealXREAL-0M1 holds a <=XXREAL-0R1 0NUMBERSK6 implies |.COMPLEX1K10 a.| =COMPLEX1R1 -XCMPLX-0K4 a"
  using complex1_lm_24 sorry

mtheorem complex1_th_71:
" for a be RealXREAL-0M1 holds |.COMPLEX1K10 a.| =COMPLEX1R1 a or |.COMPLEX1K10 a.| =COMPLEX1R1 -XCMPLX-0K4 a"
sorry

mtheorem complex1_th_72:
" for a be RealXREAL-0M1 holds sqrtSQUARE-1K3 a ^2SQUARE-1K1 =COMPLEX1R1 |.COMPLEX1K10 a.|"
  using complex1_lm_25 sorry

mtheorem complex1_th_73:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds minXXREAL-0K4(a,b) =COMPLEX1R1 ((a +XCMPLX-0K2 b)-XCMPLX-0K6 |.COMPLEX1K10 a -XCMPLX-0K6 b .|)/XCMPLX-0K7 \<two>\<^sub>M"
sorry

mtheorem complex1_th_74:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds maxXXREAL-0K5(a,b) =COMPLEX1R1 ((a +XCMPLX-0K2 b)+XCMPLX-0K2 |.COMPLEX1K10 a -XCMPLX-0K6 b .|)/XCMPLX-0K7 \<two>\<^sub>M"
sorry

mtheorem complex1_th_75:
" for a be RealXREAL-0M1 holds (|.COMPLEX1K10 a.|)^2SQUARE-1K1 =COMPLEX1R1 a ^2SQUARE-1K1"
sorry

mtheorem complex1_th_76:
" for a be RealXREAL-0M1 holds -XCMPLX-0K4 |.COMPLEX1K10 a.| <=XXREAL-0R1 a & a <=XXREAL-0R1 |.COMPLEX1K10 a.|"
  using complex1_lm_26 sorry

mtheorem complex1_th_77:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds  for d be RealXREAL-0M1 holds a +XCMPLX-0K2 b *XCMPLX-0K3 (<i>COMPLEX1K8) =COMPLEX1R1 c +XCMPLX-0K2 d *XCMPLX-0K3 (<i>COMPLEX1K8) implies a =COMPLEX1R1 c & b =COMPLEX1R1 d"
sorry

mtheorem complex1_th_78:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds sqrtSQUARE-1K3 (a ^2SQUARE-1K1 +XCMPLX-0K2 b ^2SQUARE-1K1) <=XXREAL-0R1 |.COMPLEX1K10 a.| +XCMPLX-0K2 |.COMPLEX1K10 b.|"
sorry

mtheorem complex1_th_79:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds |.COMPLEX1K10 a.| <=XXREAL-0R1 sqrtSQUARE-1K3 (a ^2SQUARE-1K1 +XCMPLX-0K2 b ^2SQUARE-1K1)"
sorry

mtheorem complex1_th_80:
" for z1 be ComplexXCMPLX-0M1 holds |.COMPLEX1K10 \<one>\<^sub>M /XCMPLX-0K7 z1 .| =COMPLEX1R1 \<one>\<^sub>M /XCMPLX-0K7 (|.COMPLEX1K10 z1.|)"
  using complex1_th_48 complex1_th_67 sorry

mtheorem complex1_th_81:
" for z1 be ComplexXCMPLX-0M1 holds  for z2 be ComplexXCMPLX-0M1 holds z1 +XCMPLX-0K2 z2 =COMPLEX1R1 (ReCOMPLEX1K3 z1 +REAL-1K3 ReCOMPLEX1K3 z2)+XCMPLX-0K2 (ImCOMPLEX1K4 z1 +REAL-1K3 ImCOMPLEX1K4 z2)*XCMPLX-0K3 (<i>COMPLEX1K8)"
sorry

mtheorem complex1_th_82:
" for z1 be ComplexXCMPLX-0M1 holds  for z2 be ComplexXCMPLX-0M1 holds z1 *XCMPLX-0K3 z2 =COMPLEX1R1 (ReCOMPLEX1K3 z1 *REAL-1K4 ReCOMPLEX1K3 z2 -REAL-1K5 ImCOMPLEX1K4 z1 *REAL-1K4 ImCOMPLEX1K4 z2)+XCMPLX-0K2 (ReCOMPLEX1K3 z1 *REAL-1K4 ImCOMPLEX1K4 z2 +REAL-1K3 ReCOMPLEX1K3 z2 *REAL-1K4 ImCOMPLEX1K4 z1)*XCMPLX-0K3 (<i>COMPLEX1K8)"
sorry

mtheorem complex1_th_83:
" for z be ComplexXCMPLX-0M1 holds -XCMPLX-0K4 z =COMPLEX1R1 (-REAL-1K1 ReCOMPLEX1K3 z)+XCMPLX-0K2 (-REAL-1K1 ImCOMPLEX1K4 z)*XCMPLX-0K3 (<i>COMPLEX1K8)"
  using complex1_lm_19 sorry

mtheorem complex1_th_84:
" for z1 be ComplexXCMPLX-0M1 holds  for z2 be ComplexXCMPLX-0M1 holds z1 -XCMPLX-0K6 z2 =COMPLEX1R1 (ReCOMPLEX1K3 z1 -REAL-1K5 ReCOMPLEX1K3 z2)+XCMPLX-0K2 (ImCOMPLEX1K4 z1 -REAL-1K5 ImCOMPLEX1K4 z2)*XCMPLX-0K3 (<i>COMPLEX1K8)"
  using complex1_lm_20 sorry

mtheorem complex1_th_85:
" for z be ComplexXCMPLX-0M1 holds z \<inverse>XCMPLX-0K5 =COMPLEX1R1 ReCOMPLEX1K3 z /XCMPLX-0K7 ((ReCOMPLEX1K3 z)^2SQUARE-1K1 +XCMPLX-0K2 (ImCOMPLEX1K4 z)^2SQUARE-1K1) +XCMPLX-0K2 ((-REAL-1K1 ImCOMPLEX1K4 z)/XCMPLX-0K7 ((ReCOMPLEX1K3 z)^2SQUARE-1K1 +XCMPLX-0K2 (ImCOMPLEX1K4 z)^2SQUARE-1K1))*XCMPLX-0K3 (<i>COMPLEX1K8)"
  using complex1_lm_21 sorry

mtheorem complex1_th_86:
" for z1 be ComplexXCMPLX-0M1 holds  for z2 be ComplexXCMPLX-0M1 holds z1 /XCMPLX-0K7 z2 =COMPLEX1R1 (ReCOMPLEX1K3 z1 *REAL-1K4 ReCOMPLEX1K3 z2 +REAL-1K3 ImCOMPLEX1K4 z1 *REAL-1K4 ImCOMPLEX1K4 z2)/XCMPLX-0K7 ((ReCOMPLEX1K3 z2)^2SQUARE-1K1 +XCMPLX-0K2 (ImCOMPLEX1K4 z2)^2SQUARE-1K1) +XCMPLX-0K2 ((ReCOMPLEX1K3 z2 *REAL-1K4 ImCOMPLEX1K4 z1 -REAL-1K5 ReCOMPLEX1K3 z1 *REAL-1K4 ImCOMPLEX1K4 z2)/XCMPLX-0K7 ((ReCOMPLEX1K3 z2)^2SQUARE-1K1 +XCMPLX-0K2 (ImCOMPLEX1K4 z2)^2SQUARE-1K1))*XCMPLX-0K3 (<i>COMPLEX1K8)"
  using complex1_lm_22 sorry

end
