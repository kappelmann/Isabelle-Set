theory square_1
  imports axioms xreal_1
   "../mizar_extension/E_number"
begin
(*begin*)
reserve a, b, c, x, y, z for "RealXREAL-0M1"
theorem square_1_sch_1:
  fixes Pp1 Qp1 
  assumes
    A1: " for x be RealXREAL-0M1 holds  for y be RealXREAL-0M1 holds Pp1(x) & Qp1(y) implies x <=XXREAL-0R1 y"
  shows " ex z be RealXREAL-0M1 st  for x be RealXREAL-0M1 holds  for y be RealXREAL-0M1 holds Pp1(x) & Qp1(y) implies x <=XXREAL-0R1 z & z <=XXREAL-0R1 y"
sorry

mtheorem square_1_th_1:
" for x be RealXREAL-0M1 holds  for y be RealXREAL-0M1 holds minXXREAL-0K4(x,y) +XCMPLX-0K2 maxXXREAL-0K5(x,y) =HIDDENR1 x +XCMPLX-0K2 y"
sorry

mtheorem square_1_th_2:
" for x be RealXREAL-0M1 holds  for y be RealXREAL-0M1 holds 0NUMBERSK6 <=XXREAL-0R1 x & 0NUMBERSK6 <=XXREAL-0R1 y implies maxXXREAL-0K5(x,y) <=XXREAL-0R1 x +XCMPLX-0K2 y"
sorry

mdef square_1_def_1 (" _ ^2SQUARE-1K1" [354]354 ) where
  mlet "x be ComplexXCMPLX-0M1"
"func x ^2SQUARE-1K1 \<rightarrow> numberORDINAL1M2 equals
  x *XCMPLX-0K3 x"
proof-
  (*coherence*)
    show "x *XCMPLX-0K3 x be numberORDINAL1M2"
       sorry
qed "sorry"

mtheorem square_1_cl_1:
  mlet "x be ComplexXCMPLX-0M1"
"cluster x ^2SQUARE-1K1 as-term-is complexXCMPLX-0V1"
proof
(*coherence*)
  show "x ^2SQUARE-1K1 be complexXCMPLX-0V1"
     sorry
qed "sorry"

mtheorem square_1_cl_2:
  mlet "x be RealXREAL-0M1"
"cluster x ^2SQUARE-1K1 as-term-is realXREAL-0V1"
proof
(*coherence*)
  show "x ^2SQUARE-1K1 be realXREAL-0V1"
     sorry
qed "sorry"

abbreviation(input) SQUARE_1K2(" _ ^2SQUARE-1K2" [354]354) where
  "x ^2SQUARE-1K2 \<equiv> x ^2SQUARE-1K1"

mtheorem square_1_add_1:
  mlet "x be ElementSUBSET-1M1-of COMPLEXNUMBERSK3"
"cluster x ^2SQUARE-1K1 as-term-is ElementSUBSET-1M1-of COMPLEXNUMBERSK3"
proof
(*coherence*)
  show "x ^2SQUARE-1K1 be ElementSUBSET-1M1-of COMPLEXNUMBERSK3"
    using xcmplx_0_def_2 sorry
qed "sorry"

mtheorem square_1_th_3:
" for a be ComplexXCMPLX-0M1 holds a ^2SQUARE-1K1 =HIDDENR1 (-XCMPLX-0K4 a)^2SQUARE-1K1"
   sorry

mtheorem square_1_th_4:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds (a +XCMPLX-0K2 b)^2SQUARE-1K1 =HIDDENR1 (a ^2SQUARE-1K1 +XCMPLX-0K2 (\<two>\<^sub>M *XCMPLX-0K3 a)*XCMPLX-0K3 b)+XCMPLX-0K2 b ^2SQUARE-1K1"
   sorry

mtheorem square_1_th_5:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds (a -XCMPLX-0K6 b)^2SQUARE-1K1 =HIDDENR1 (a ^2SQUARE-1K1 -XCMPLX-0K6 (\<two>\<^sub>M *XCMPLX-0K3 a)*XCMPLX-0K3 b)+XCMPLX-0K2 b ^2SQUARE-1K1"
   sorry

mtheorem square_1_th_6:
" for a be ComplexXCMPLX-0M1 holds (a +XCMPLX-0K2 \<one>\<^sub>M)^2SQUARE-1K1 =HIDDENR1 (a ^2SQUARE-1K1 +XCMPLX-0K2 \<two>\<^sub>M *XCMPLX-0K3 a)+XCMPLX-0K2 \<one>\<^sub>M"
   sorry

mtheorem square_1_th_7:
" for a be ComplexXCMPLX-0M1 holds (a -XCMPLX-0K6 \<one>\<^sub>M)^2SQUARE-1K1 =HIDDENR1 (a ^2SQUARE-1K1 -XCMPLX-0K6 \<two>\<^sub>M *XCMPLX-0K3 a)+XCMPLX-0K2 \<one>\<^sub>M"
   sorry

mtheorem square_1_th_8:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds (a -XCMPLX-0K6 b)*XCMPLX-0K3 (a +XCMPLX-0K2 b) =HIDDENR1 a ^2SQUARE-1K1 -XCMPLX-0K6 b ^2SQUARE-1K1"
   sorry

mtheorem square_1_th_9:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds (a *XCMPLX-0K3 b)^2SQUARE-1K1 =HIDDENR1 a ^2SQUARE-1K1 *XCMPLX-0K3 b ^2SQUARE-1K1"
   sorry

mtheorem square_1_th_10:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds a ^2SQUARE-1K1 -XCMPLX-0K6 b ^2SQUARE-1K1 <>HIDDENR2 0NUMBERSK6 implies \<one>\<^sub>M /XCMPLX-0K7 (a +XCMPLX-0K2 b) =HIDDENR1 (a -XCMPLX-0K6 b)/XCMPLX-0K7 (a ^2SQUARE-1K1 -XCMPLX-0K6 b ^2SQUARE-1K1)"
sorry

mtheorem square_1_th_11:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds a ^2SQUARE-1K1 -XCMPLX-0K6 b ^2SQUARE-1K1 <>HIDDENR2 0NUMBERSK6 implies \<one>\<^sub>M /XCMPLX-0K7 (a -XCMPLX-0K6 b) =HIDDENR1 (a +XCMPLX-0K2 b)/XCMPLX-0K7 (a ^2SQUARE-1K1 -XCMPLX-0K6 b ^2SQUARE-1K1)"
sorry

mtheorem square_1_th_12:
" for a be RealXREAL-0M1 holds 0NUMBERSK6 <>HIDDENR2 a implies 0NUMBERSK6 <XXREAL-0R3 a ^2SQUARE-1K1"
  using xreal_1_th_63 sorry

mtheorem square_1_th_13:
" for a be RealXREAL-0M1 holds 0NUMBERSK6 <XXREAL-0R3 a & a <XXREAL-0R3 \<one>\<^sub>M implies a ^2SQUARE-1K1 <XXREAL-0R3 a"
sorry

mtheorem square_1_th_14:
" for a be RealXREAL-0M1 holds \<one>\<^sub>M <XXREAL-0R3 a implies a <XXREAL-0R3 a ^2SQUARE-1K1"
sorry

mlemma square_1_lm_1:
" for a be RealXREAL-0M1 holds 0NUMBERSK6 <XXREAL-0R3 a implies ( ex x be RealXREAL-0M1 st 0NUMBERSK6 <XXREAL-0R3 x & x ^2SQUARE-1K1 <XXREAL-0R3 a)"
sorry

mtheorem square_1_th_15:
" for x be RealXREAL-0M1 holds  for y be RealXREAL-0M1 holds 0NUMBERSK6 <=XXREAL-0R1 x & x <=XXREAL-0R1 y implies x ^2SQUARE-1K1 <=XXREAL-0R1 y ^2SQUARE-1K1"
sorry

mtheorem square_1_th_16:
" for x be RealXREAL-0M1 holds  for y be RealXREAL-0M1 holds 0NUMBERSK6 <=XXREAL-0R1 x & x <XXREAL-0R3 y implies x ^2SQUARE-1K1 <XXREAL-0R3 y ^2SQUARE-1K1"
sorry

mlemma square_1_lm_2:
" for x be RealXREAL-0M1 holds  for y be RealXREAL-0M1 holds (0NUMBERSK6 <=XXREAL-0R1 x & 0NUMBERSK6 <=XXREAL-0R1 y) & x ^2SQUARE-1K1 =HIDDENR1 y ^2SQUARE-1K1 implies x =HIDDENR1 y"
sorry

mdef square_1_def_2 ("sqrtSQUARE-1K3  _ " [300]300 ) where
  mlet "a be RealXREAL-0M1"
"assume 0NUMBERSK6 <=XXREAL-0R1 a func sqrtSQUARE-1K3 a \<rightarrow> RealXREAL-0M1 means
  \<lambda>it. 0NUMBERSK6 <=XXREAL-0R1 it & it ^2SQUARE-1K1 =HIDDENR1 a"
proof-
  (*existence*)
    show "0NUMBERSK6 <=XXREAL-0R1 a implies ( ex it be RealXREAL-0M1 st 0NUMBERSK6 <=XXREAL-0R1 it & it ^2SQUARE-1K1 =HIDDENR1 a)"
sorry
  (*uniqueness*)
    show "0NUMBERSK6 <=XXREAL-0R1 a implies ( for it1 be RealXREAL-0M1 holds  for it2 be RealXREAL-0M1 holds (0NUMBERSK6 <=XXREAL-0R1 it1 & it1 ^2SQUARE-1K1 =HIDDENR1 a) & (0NUMBERSK6 <=XXREAL-0R1 it2 & it2 ^2SQUARE-1K1 =HIDDENR1 a) implies it1 =HIDDENR1 it2)"
sorry
qed "sorry"

mtheorem square_1_th_17:
"sqrtSQUARE-1K3 (0NUMBERSK6) =HIDDENR1 0NUMBERSK6"
sorry

mtheorem square_1_th_18:
"sqrtSQUARE-1K3 \<one>\<^sub>M =HIDDENR1 \<one>\<^sub>M"
sorry

mlemma square_1_lm_3:
" for x be RealXREAL-0M1 holds  for y be RealXREAL-0M1 holds 0NUMBERSK6 <=XXREAL-0R1 x & x <XXREAL-0R3 y implies sqrtSQUARE-1K3 x <XXREAL-0R3 sqrtSQUARE-1K3 y"
sorry

mtheorem square_1_th_19:
"\<one>\<^sub>M <XXREAL-0R3 sqrtSQUARE-1K3 \<two>\<^sub>M"
  using square_1_lm_3 square_1_th_18 sorry

mlemma square_1_lm_4:
"\<two>\<^sub>M ^2SQUARE-1K1 =HIDDENR1 \<two>\<^sub>M *XCMPLX-0K3 \<two>\<^sub>M"
   sorry

mtheorem square_1_th_20:
"sqrtSQUARE-1K3 \<four>\<^sub>M =HIDDENR1 \<two>\<^sub>M"
  using square_1_def_2 square_1_lm_4 sorry

mtheorem square_1_th_21:
"sqrtSQUARE-1K3 \<two>\<^sub>M <XXREAL-0R3 \<two>\<^sub>M"
  using square_1_lm_3 square_1_th_20 sorry

mtheorem square_1_th_22:
" for a be RealXREAL-0M1 holds 0NUMBERSK6 <=XXREAL-0R1 a implies sqrtSQUARE-1K3 a ^2SQUARE-1K1 =HIDDENR1 a"
  using square_1_def_2 sorry

mtheorem square_1_th_23:
" for a be RealXREAL-0M1 holds a <=XXREAL-0R1 0NUMBERSK6 implies sqrtSQUARE-1K3 a ^2SQUARE-1K1 =HIDDENR1 -XCMPLX-0K4 a"
sorry

mtheorem square_1_th_24:
" for a be RealXREAL-0M1 holds 0NUMBERSK6 <=XXREAL-0R1 a & sqrtSQUARE-1K3 a =HIDDENR1 0NUMBERSK6 implies a =HIDDENR1 0NUMBERSK6"
sorry

mtheorem square_1_th_25:
" for a be RealXREAL-0M1 holds 0NUMBERSK6 <XXREAL-0R3 a implies 0NUMBERSK6 <XXREAL-0R3 sqrtSQUARE-1K3 a"
sorry

mtheorem square_1_th_26:
" for x be RealXREAL-0M1 holds  for y be RealXREAL-0M1 holds 0NUMBERSK6 <=XXREAL-0R1 x & x <=XXREAL-0R1 y implies sqrtSQUARE-1K3 x <=XXREAL-0R1 sqrtSQUARE-1K3 y"
sorry

mtheorem square_1_th_27:
" for x be RealXREAL-0M1 holds  for y be RealXREAL-0M1 holds 0NUMBERSK6 <=XXREAL-0R1 x & x <XXREAL-0R3 y implies sqrtSQUARE-1K3 x <XXREAL-0R3 sqrtSQUARE-1K3 y"
  using square_1_lm_3 sorry

mtheorem square_1_th_28:
" for x be RealXREAL-0M1 holds  for y be RealXREAL-0M1 holds (0NUMBERSK6 <=XXREAL-0R1 x & 0NUMBERSK6 <=XXREAL-0R1 y) & sqrtSQUARE-1K3 x =HIDDENR1 sqrtSQUARE-1K3 y implies x =HIDDENR1 y"
sorry

mtheorem square_1_th_29:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds 0NUMBERSK6 <=XXREAL-0R1 a & 0NUMBERSK6 <=XXREAL-0R1 b implies sqrtSQUARE-1K3 (a *XCMPLX-0K3 b) =HIDDENR1 sqrtSQUARE-1K3 a *XCMPLX-0K3 sqrtSQUARE-1K3 b"
sorry

mtheorem square_1_th_30:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds 0NUMBERSK6 <=XXREAL-0R1 a & 0NUMBERSK6 <=XXREAL-0R1 b implies sqrtSQUARE-1K3 (a /XCMPLX-0K7 b) =HIDDENR1 sqrtSQUARE-1K3 a /XCMPLX-0K7 sqrtSQUARE-1K3 b"
sorry

mtheorem square_1_th_31:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds 0NUMBERSK6 <=XXREAL-0R1 a & 0NUMBERSK6 <=XXREAL-0R1 b implies (sqrtSQUARE-1K3 (a +XCMPLX-0K2 b) =HIDDENR1 0NUMBERSK6 iff a =HIDDENR1 0NUMBERSK6 & b =HIDDENR1 0NUMBERSK6)"
  using square_1_th_17 square_1_th_24 sorry

mtheorem square_1_th_32:
" for a be RealXREAL-0M1 holds 0NUMBERSK6 <XXREAL-0R3 a implies sqrtSQUARE-1K3 (\<one>\<^sub>M /XCMPLX-0K7 a) =HIDDENR1 \<one>\<^sub>M /XCMPLX-0K7 sqrtSQUARE-1K3 a"
  using square_1_th_18 square_1_th_30 sorry

mtheorem square_1_th_33:
" for a be RealXREAL-0M1 holds 0NUMBERSK6 <XXREAL-0R3 a implies sqrtSQUARE-1K3 a /XCMPLX-0K7 a =HIDDENR1 \<one>\<^sub>M /XCMPLX-0K7 sqrtSQUARE-1K3 a"
sorry

mtheorem square_1_th_34:
" for a be RealXREAL-0M1 holds 0NUMBERSK6 <XXREAL-0R3 a implies a /XCMPLX-0K7 sqrtSQUARE-1K3 a =HIDDENR1 sqrtSQUARE-1K3 a"
sorry

mtheorem square_1_th_35:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds 0NUMBERSK6 <=XXREAL-0R1 a & 0NUMBERSK6 <=XXREAL-0R1 b implies (sqrtSQUARE-1K3 a -XCMPLX-0K6 sqrtSQUARE-1K3 b)*XCMPLX-0K3 (sqrtSQUARE-1K3 a +XCMPLX-0K2 sqrtSQUARE-1K3 b) =HIDDENR1 a -XCMPLX-0K6 b"
sorry

mlemma square_1_lm_5:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds (0NUMBERSK6 <=XXREAL-0R1 a & 0NUMBERSK6 <=XXREAL-0R1 b) & a <>HIDDENR2 b implies (sqrtSQUARE-1K3 a)^2SQUARE-1K1 -XCMPLX-0K6 (sqrtSQUARE-1K3 b)^2SQUARE-1K1 <>HIDDENR2 0NUMBERSK6"
sorry

mtheorem square_1_th_36:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds (0NUMBERSK6 <=XXREAL-0R1 a & 0NUMBERSK6 <=XXREAL-0R1 b) & a <>HIDDENR2 b implies \<one>\<^sub>M /XCMPLX-0K7 (sqrtSQUARE-1K3 a +XCMPLX-0K2 sqrtSQUARE-1K3 b) =HIDDENR1 (sqrtSQUARE-1K3 a -XCMPLX-0K6 sqrtSQUARE-1K3 b)/XCMPLX-0K7 (a -XCMPLX-0K6 b)"
sorry

mtheorem square_1_th_37:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds 0NUMBERSK6 <=XXREAL-0R1 b & b <XXREAL-0R3 a implies \<one>\<^sub>M /XCMPLX-0K7 (sqrtSQUARE-1K3 a +XCMPLX-0K2 sqrtSQUARE-1K3 b) =HIDDENR1 (sqrtSQUARE-1K3 a -XCMPLX-0K6 sqrtSQUARE-1K3 b)/XCMPLX-0K7 (a -XCMPLX-0K6 b)"
sorry

mtheorem square_1_th_38:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds 0NUMBERSK6 <=XXREAL-0R1 a & 0NUMBERSK6 <=XXREAL-0R1 b implies \<one>\<^sub>M /XCMPLX-0K7 (sqrtSQUARE-1K3 a -XCMPLX-0K6 sqrtSQUARE-1K3 b) =HIDDENR1 (sqrtSQUARE-1K3 a +XCMPLX-0K2 sqrtSQUARE-1K3 b)/XCMPLX-0K7 (a -XCMPLX-0K6 b)"
sorry

mtheorem square_1_th_39:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds 0NUMBERSK6 <=XXREAL-0R1 b & b <XXREAL-0R3 a implies \<one>\<^sub>M /XCMPLX-0K7 (sqrtSQUARE-1K3 a -XCMPLX-0K6 sqrtSQUARE-1K3 b) =HIDDENR1 (sqrtSQUARE-1K3 a +XCMPLX-0K2 sqrtSQUARE-1K3 b)/XCMPLX-0K7 (a -XCMPLX-0K6 b)"
sorry

mtheorem square_1_th_40:
" for x be ComplexXCMPLX-0M1 holds  for y be ComplexXCMPLX-0M1 holds x ^2SQUARE-1K1 =HIDDENR1 y ^2SQUARE-1K1 implies x =HIDDENR1 y or x =HIDDENR1 -XCMPLX-0K4 y"
sorry

mtheorem square_1_th_41:
" for x be ComplexXCMPLX-0M1 holds x ^2SQUARE-1K1 =HIDDENR1 \<one>\<^sub>M implies x =HIDDENR1 \<one>\<^sub>M or x =HIDDENR1 -XCMPLX-0K4 \<one>\<^sub>M"
sorry

mtheorem square_1_th_42:
" for x be RealXREAL-0M1 holds 0NUMBERSK6 <=XXREAL-0R1 x & x <=XXREAL-0R1 \<one>\<^sub>M implies x ^2SQUARE-1K1 <=XXREAL-0R1 x"
sorry

mtheorem square_1_th_43:
" for x be RealXREAL-0M1 holds x ^2SQUARE-1K1 -XCMPLX-0K6 \<one>\<^sub>M <=XXREAL-0R1 0NUMBERSK6 implies -XCMPLX-0K4 \<one>\<^sub>M <=XXREAL-0R1 x & x <=XXREAL-0R1 \<one>\<^sub>M"
sorry

(*begin*)
mtheorem square_1_th_44:
" for a be RealXREAL-0M1 holds  for x be RealXREAL-0M1 holds a <=XXREAL-0R1 0NUMBERSK6 & x <XXREAL-0R3 a implies x ^2SQUARE-1K1 >XXREAL-0R4 a ^2SQUARE-1K1"
sorry

mtheorem square_1_th_45:
" for a be RealXREAL-0M1 holds -XCMPLX-0K4 \<one>\<^sub>M >=XXREAL-0R2 a implies -XCMPLX-0K4 a <=XXREAL-0R1 a ^2SQUARE-1K1"
sorry

mtheorem square_1_th_46:
" for a be RealXREAL-0M1 holds -XCMPLX-0K4 \<one>\<^sub>M >XXREAL-0R4 a implies -XCMPLX-0K4 a <XXREAL-0R3 a ^2SQUARE-1K1"
sorry

mtheorem square_1_th_47:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds b ^2SQUARE-1K1 <=XXREAL-0R1 a ^2SQUARE-1K1 & a >=XXREAL-0R2 0NUMBERSK6 implies -XCMPLX-0K4 a <=XXREAL-0R1 b & b <=XXREAL-0R1 a"
sorry

mtheorem square_1_th_48:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds b ^2SQUARE-1K1 <XXREAL-0R3 a ^2SQUARE-1K1 & a >=XXREAL-0R2 0NUMBERSK6 implies -XCMPLX-0K4 a <XXREAL-0R3 b & b <XXREAL-0R3 a"
sorry

mtheorem square_1_th_49:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds -XCMPLX-0K4 a <=XXREAL-0R1 b & b <=XXREAL-0R1 a implies b ^2SQUARE-1K1 <=XXREAL-0R1 a ^2SQUARE-1K1"
sorry

mtheorem square_1_th_50:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds -XCMPLX-0K4 a <XXREAL-0R3 b & b <XXREAL-0R3 a implies b ^2SQUARE-1K1 <XXREAL-0R3 a ^2SQUARE-1K1"
sorry

mtheorem square_1_th_51:
" for a be RealXREAL-0M1 holds a ^2SQUARE-1K1 <=XXREAL-0R1 \<one>\<^sub>M implies -XCMPLX-0K4 \<one>\<^sub>M <=XXREAL-0R1 a & a <=XXREAL-0R1 \<one>\<^sub>M"
sorry

mtheorem square_1_th_52:
" for a be RealXREAL-0M1 holds a ^2SQUARE-1K1 <XXREAL-0R3 \<one>\<^sub>M implies -XCMPLX-0K4 \<one>\<^sub>M <XXREAL-0R3 a & a <XXREAL-0R3 \<one>\<^sub>M"
sorry

mtheorem square_1_th_53:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds ((-XCMPLX-0K4 \<one>\<^sub>M <=XXREAL-0R1 a & a <=XXREAL-0R1 \<one>\<^sub>M) & -XCMPLX-0K4 \<one>\<^sub>M <=XXREAL-0R1 b) & b <=XXREAL-0R1 \<one>\<^sub>M implies a ^2SQUARE-1K1 *XCMPLX-0K3 b ^2SQUARE-1K1 <=XXREAL-0R1 \<one>\<^sub>M"
sorry

mtheorem square_1_th_54:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds a >=XXREAL-0R2 0NUMBERSK6 & b >=XXREAL-0R2 0NUMBERSK6 implies a *XCMPLX-0K3 sqrtSQUARE-1K3 b =HIDDENR1 sqrtSQUARE-1K3 (a ^2SQUARE-1K1 *XCMPLX-0K3 b)"
sorry

mlemma square_1_lm_6:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds ((-XCMPLX-0K4 \<one>\<^sub>M <=XXREAL-0R1 a & a <=XXREAL-0R1 \<one>\<^sub>M) & -XCMPLX-0K4 \<one>\<^sub>M <=XXREAL-0R1 b) & b <=XXREAL-0R1 \<one>\<^sub>M implies (\<one>\<^sub>M +XCMPLX-0K2 a ^2SQUARE-1K1)*XCMPLX-0K3 b ^2SQUARE-1K1 <=XXREAL-0R1 \<one>\<^sub>M +XCMPLX-0K2 b ^2SQUARE-1K1"
sorry

mtheorem square_1_th_55:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds ((-XCMPLX-0K4 \<one>\<^sub>M <=XXREAL-0R1 a & a <=XXREAL-0R1 \<one>\<^sub>M) & -XCMPLX-0K4 \<one>\<^sub>M <=XXREAL-0R1 b) & b <=XXREAL-0R1 \<one>\<^sub>M implies (-XCMPLX-0K4 b)*XCMPLX-0K3 sqrtSQUARE-1K3 (\<one>\<^sub>M +XCMPLX-0K2 a ^2SQUARE-1K1) <=XXREAL-0R1 sqrtSQUARE-1K3 (\<one>\<^sub>M +XCMPLX-0K2 b ^2SQUARE-1K1) & -XCMPLX-0K4 sqrtSQUARE-1K3 (\<one>\<^sub>M +XCMPLX-0K2 b ^2SQUARE-1K1) <=XXREAL-0R1 b *XCMPLX-0K3 sqrtSQUARE-1K3 (\<one>\<^sub>M +XCMPLX-0K2 a ^2SQUARE-1K1)"
sorry

mtheorem square_1_th_56:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds ((-XCMPLX-0K4 \<one>\<^sub>M <=XXREAL-0R1 a & a <=XXREAL-0R1 \<one>\<^sub>M) & -XCMPLX-0K4 \<one>\<^sub>M <=XXREAL-0R1 b) & b <=XXREAL-0R1 \<one>\<^sub>M implies b *XCMPLX-0K3 sqrtSQUARE-1K3 (\<one>\<^sub>M +XCMPLX-0K2 a ^2SQUARE-1K1) <=XXREAL-0R1 sqrtSQUARE-1K3 (\<one>\<^sub>M +XCMPLX-0K2 b ^2SQUARE-1K1)"
sorry

mlemma square_1_lm_7:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds b <=XXREAL-0R1 0NUMBERSK6 & a <=XXREAL-0R1 b implies a *XCMPLX-0K3 sqrtSQUARE-1K3 (\<one>\<^sub>M +XCMPLX-0K2 b ^2SQUARE-1K1) <=XXREAL-0R1 b *XCMPLX-0K3 sqrtSQUARE-1K3 (\<one>\<^sub>M +XCMPLX-0K2 a ^2SQUARE-1K1)"
sorry

mlemma square_1_lm_8:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds a <=XXREAL-0R1 0NUMBERSK6 & a <=XXREAL-0R1 b implies a *XCMPLX-0K3 sqrtSQUARE-1K3 (\<one>\<^sub>M +XCMPLX-0K2 b ^2SQUARE-1K1) <=XXREAL-0R1 b *XCMPLX-0K3 sqrtSQUARE-1K3 (\<one>\<^sub>M +XCMPLX-0K2 a ^2SQUARE-1K1)"
sorry

mlemma square_1_lm_9:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds a >=XXREAL-0R2 0NUMBERSK6 & a >=XXREAL-0R2 b implies a *XCMPLX-0K3 sqrtSQUARE-1K3 (\<one>\<^sub>M +XCMPLX-0K2 b ^2SQUARE-1K1) >=XXREAL-0R2 b *XCMPLX-0K3 sqrtSQUARE-1K3 (\<one>\<^sub>M +XCMPLX-0K2 a ^2SQUARE-1K1)"
sorry

mtheorem square_1_th_57:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds a >=XXREAL-0R2 b implies a *XCMPLX-0K3 sqrtSQUARE-1K3 (\<one>\<^sub>M +XCMPLX-0K2 b ^2SQUARE-1K1) >=XXREAL-0R2 b *XCMPLX-0K3 sqrtSQUARE-1K3 (\<one>\<^sub>M +XCMPLX-0K2 a ^2SQUARE-1K1)"
sorry

mtheorem square_1_th_58:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds a >=XXREAL-0R2 0NUMBERSK6 implies sqrtSQUARE-1K3 (a +XCMPLX-0K2 b ^2SQUARE-1K1) >=XXREAL-0R2 b"
sorry

mtheorem square_1_th_59:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds 0NUMBERSK6 <=XXREAL-0R1 a & 0NUMBERSK6 <=XXREAL-0R1 b implies sqrtSQUARE-1K3 (a +XCMPLX-0K2 b) <=XXREAL-0R1 sqrtSQUARE-1K3 a +XCMPLX-0K2 sqrtSQUARE-1K3 b"
sorry

end
