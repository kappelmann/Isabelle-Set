theory absvalue
  imports int_1 complex1
   "../mizar_extension/E_number"
begin
(*begin*)
reserve x, y, z, r, s, t for "RealXREAL-0M1"
abbreviation(input) ABSVALUEK1("|.ABSVALUEK1  _ .|" [0]164) where
  "|.ABSVALUEK1 x.| \<equiv> |.COMPLEX1K10 x.|"

mtheorem absvalue_def_1:
  mlet "x be RealXREAL-0M1"
"redefine func |.ABSVALUEK1 x.| \<rightarrow> objectHIDDENM1 equals
  x if 0NUMBERSK6 <=XXREAL-0R1 x otherwise -XCMPLX-0K4 x"
proof
(*compatibility*)
  show " for it be objectHIDDENM1 holds (0NUMBERSK6 <=XXREAL-0R1 x implies (it =HIDDENR1 |.ABSVALUEK1 x.| iff it =HIDDENR1 x)) & ( not 0NUMBERSK6 <=XXREAL-0R1 x implies (it =HIDDENR1 |.ABSVALUEK1 x.| iff it =HIDDENR1 -XCMPLX-0K4 x))"
    using complex1_th_43 complex1_th_70 sorry
(*consistency*)
  show " for it be objectHIDDENM1 holds  True "
    using complex1_th_43 complex1_th_70 sorry
qed "sorry"

mtheorem absvalue_reduce_1:
  mlet "x be  non negativeXXREAL-0V3\<bar>RealXREAL-0M1"
"reduce |.ABSVALUEK1 x.| to x"
proof
(*reducibility*)
  show "|.ABSVALUEK1 x.| =HIDDENR1 x"
    using absvalue_def_1 sorry
qed "sorry"

mtheorem absvalue_th_1:
" for x be RealXREAL-0M1 holds |.ABSVALUEK1 x.| =COMPLEX1R1 x or |.ABSVALUEK1 x.| =COMPLEX1R1 -XCMPLX-0K4 x"
  using absvalue_def_1 sorry

mtheorem absvalue_th_2:
" for x be RealXREAL-0M1 holds x =COMPLEX1R1 0NUMBERSK6 iff |.ABSVALUEK1 x.| =COMPLEX1R1 0NUMBERSK6"
  using complex1_th_47 sorry

mtheorem absvalue_th_3:
" for x be RealXREAL-0M1 holds |.ABSVALUEK1 x.| =COMPLEX1R1 -XCMPLX-0K4 x & x <>HIDDENR2 0NUMBERSK6 implies x <XXREAL-0R3 0NUMBERSK6"
  using absvalue_def_1 sorry

mtheorem absvalue_th_4:
" for x be RealXREAL-0M1 holds -XCMPLX-0K4 |.ABSVALUEK1 x.| <=XXREAL-0R1 x & x <=XXREAL-0R1 |.ABSVALUEK1 x.|"
sorry

mtheorem absvalue_th_5:
" for x be RealXREAL-0M1 holds  for y be RealXREAL-0M1 holds -XCMPLX-0K4 y <=XXREAL-0R1 x & x <=XXREAL-0R1 y iff |.ABSVALUEK1 x.| <=XXREAL-0R1 y"
sorry

mtheorem absvalue_th_6:
" for x be RealXREAL-0M1 holds x <>HIDDENR2 0NUMBERSK6 implies (|.ABSVALUEK1 x.|)*XCMPLX-0K3 (|.ABSVALUEK1 \<one>\<^sub>M /XCMPLX-0K7 x .|) =COMPLEX1R1 \<one>\<^sub>M"
sorry

mtheorem absvalue_th_7:
" for x be RealXREAL-0M1 holds |.ABSVALUEK1 \<one>\<^sub>M /XCMPLX-0K7 x .| =COMPLEX1R1 \<one>\<^sub>M /XCMPLX-0K7 (|.ABSVALUEK1 x.|)"
  using complex1_th_80 sorry

mtheorem absvalue_th_8:
" for x be RealXREAL-0M1 holds  for y be RealXREAL-0M1 holds 0NUMBERSK6 <=XXREAL-0R1 x *XCMPLX-0K3 y implies sqrtSQUARE-1K3 (x *XCMPLX-0K3 y) =COMPLEX1R1 sqrtSQUARE-1K3 (|.ABSVALUEK1 x.|) *XCMPLX-0K3 sqrtSQUARE-1K3 (|.ABSVALUEK1 y.|)"
sorry

mtheorem absvalue_th_9:
" for x be RealXREAL-0M1 holds  for y be RealXREAL-0M1 holds  for z be RealXREAL-0M1 holds  for t be RealXREAL-0M1 holds |.ABSVALUEK1 x.| <=XXREAL-0R1 z & |.ABSVALUEK1 y.| <=XXREAL-0R1 t implies |.ABSVALUEK1 x +XCMPLX-0K2 y .| <=XXREAL-0R1 z +XCMPLX-0K2 t"
sorry

mtheorem absvalue_th_10:
" for x be RealXREAL-0M1 holds  for y be RealXREAL-0M1 holds 0NUMBERSK6 <XXREAL-0R3 x /XCMPLX-0K7 y implies sqrtSQUARE-1K3 (x /XCMPLX-0K7 y) =COMPLEX1R1 sqrtSQUARE-1K3 (|.ABSVALUEK1 x.|) /XCMPLX-0K7 sqrtSQUARE-1K3 (|.ABSVALUEK1 y.|)"
sorry

mtheorem absvalue_th_11:
" for x be RealXREAL-0M1 holds  for y be RealXREAL-0M1 holds 0NUMBERSK6 <=XXREAL-0R1 x *XCMPLX-0K3 y implies |.ABSVALUEK1 x +XCMPLX-0K2 y .| =COMPLEX1R1 |.ABSVALUEK1 x.| +XCMPLX-0K2 |.ABSVALUEK1 y.|"
sorry

mtheorem absvalue_th_12:
" for x be RealXREAL-0M1 holds  for y be RealXREAL-0M1 holds |.ABSVALUEK1 x +XCMPLX-0K2 y .| =COMPLEX1R1 |.ABSVALUEK1 x.| +XCMPLX-0K2 |.ABSVALUEK1 y.| implies 0NUMBERSK6 <=XXREAL-0R1 x *XCMPLX-0K3 y"
sorry

mtheorem absvalue_th_13:
" for x be RealXREAL-0M1 holds  for y be RealXREAL-0M1 holds (|.ABSVALUEK1 x +XCMPLX-0K2 y .|)/XCMPLX-0K7 (\<one>\<^sub>M +XCMPLX-0K2 |.ABSVALUEK1 x +XCMPLX-0K2 y .|) <=XXREAL-0R1 (|.ABSVALUEK1 x.|)/XCMPLX-0K7 (\<one>\<^sub>M +XCMPLX-0K2 |.ABSVALUEK1 x.|) +XCMPLX-0K2 (|.ABSVALUEK1 y.|)/XCMPLX-0K7 (\<one>\<^sub>M +XCMPLX-0K2 |.ABSVALUEK1 y.|)"
sorry

mdef absvalue_def_2 ("sgnABSVALUEK2  _ " [164]164 ) where
  mlet "x be RealXREAL-0M1"
"func sgnABSVALUEK2 x \<rightarrow> RealXREAL-0M1 equals
  \<one>\<^sub>M if 0NUMBERSK6 <XXREAL-0R3 x,
  -XCMPLX-0K4 \<one>\<^sub>M if x <XXREAL-0R3 0NUMBERSK6 otherwise 0NUMBERSK6"
proof-
  (*coherence*)
    show "(0NUMBERSK6 <XXREAL-0R3 x implies \<one>\<^sub>M be RealXREAL-0M1) & ((x <XXREAL-0R3 0NUMBERSK6 implies -XCMPLX-0K4 \<one>\<^sub>M be RealXREAL-0M1) & ( not 0NUMBERSK6 <XXREAL-0R3 x &  not x <XXREAL-0R3 0NUMBERSK6 implies 0NUMBERSK6 be RealXREAL-0M1))"
       sorry
  (*consistency*)
    show " for it be RealXREAL-0M1 holds 0NUMBERSK6 <XXREAL-0R3 x & x <XXREAL-0R3 0NUMBERSK6 implies (it =HIDDENR1 \<one>\<^sub>M iff it =HIDDENR1 -XCMPLX-0K4 \<one>\<^sub>M)"
       sorry
qed "sorry"

mtheorem ABSVALUEK2_projectivity:
" for x be RealXREAL-0M1 holds sgnABSVALUEK2 (sgnABSVALUEK2 x) =HIDDENR1 sgnABSVALUEK2 x"
sorry

mtheorem absvalue_cl_1:
  mlet "x be RealXREAL-0M1"
"cluster sgnABSVALUEK2 x as-term-is integerINT-1V1"
proof
(*coherence*)
  show "sgnABSVALUEK2 x be integerINT-1V1"
sorry
qed "sorry"

mtheorem absvalue_th_14:
" for x be RealXREAL-0M1 holds sgnABSVALUEK2 x =COMPLEX1R1 \<one>\<^sub>M implies 0NUMBERSK6 <XXREAL-0R3 x"
sorry

mtheorem absvalue_th_15:
" for x be RealXREAL-0M1 holds sgnABSVALUEK2 x =COMPLEX1R1 -XCMPLX-0K4 \<one>\<^sub>M implies x <XXREAL-0R3 0NUMBERSK6"
sorry

mtheorem absvalue_th_16:
" for x be RealXREAL-0M1 holds sgnABSVALUEK2 x =COMPLEX1R1 0NUMBERSK6 implies x =COMPLEX1R1 0NUMBERSK6"
sorry

mtheorem absvalue_th_17:
" for x be RealXREAL-0M1 holds x =COMPLEX1R1 (|.ABSVALUEK1 x.|)*XCMPLX-0K3 (sgnABSVALUEK2 x)"
sorry

mtheorem absvalue_th_18:
" for x be RealXREAL-0M1 holds  for y be RealXREAL-0M1 holds sgnABSVALUEK2 (x *XCMPLX-0K3 y) =COMPLEX1R1 (sgnABSVALUEK2 x)*XCMPLX-0K3 (sgnABSVALUEK2 y)"
sorry

(*\$CT*)
mtheorem absvalue_th_20:
" for x be RealXREAL-0M1 holds  for y be RealXREAL-0M1 holds sgnABSVALUEK2 (x +XCMPLX-0K2 y) <=XXREAL-0R1 (sgnABSVALUEK2 x +XCMPLX-0K2 sgnABSVALUEK2 y)+XCMPLX-0K2 \<one>\<^sub>M"
sorry

mtheorem absvalue_th_21:
" for x be RealXREAL-0M1 holds x <>HIDDENR2 0NUMBERSK6 implies (sgnABSVALUEK2 x)*XCMPLX-0K3 (sgnABSVALUEK2 (\<one>\<^sub>M /XCMPLX-0K7 x)) =COMPLEX1R1 \<one>\<^sub>M"
sorry

mtheorem absvalue_th_22:
" for x be RealXREAL-0M1 holds \<one>\<^sub>M /XCMPLX-0K7 (sgnABSVALUEK2 x) =COMPLEX1R1 sgnABSVALUEK2 (\<one>\<^sub>M /XCMPLX-0K7 x)"
sorry

mtheorem absvalue_th_23:
" for x be RealXREAL-0M1 holds  for y be RealXREAL-0M1 holds (sgnABSVALUEK2 x +XCMPLX-0K2 sgnABSVALUEK2 y)-XCMPLX-0K6 \<one>\<^sub>M <=XXREAL-0R1 sgnABSVALUEK2 (x +XCMPLX-0K2 y)"
sorry

mtheorem absvalue_th_24:
" for x be RealXREAL-0M1 holds sgnABSVALUEK2 x =COMPLEX1R1 sgnABSVALUEK2 (\<one>\<^sub>M /XCMPLX-0K7 x)"
sorry

mtheorem absvalue_th_25:
" for x be RealXREAL-0M1 holds  for y be RealXREAL-0M1 holds sgnABSVALUEK2 (x /XCMPLX-0K7 y) =COMPLEX1R1 (sgnABSVALUEK2 x)/XCMPLX-0K7 (sgnABSVALUEK2 y)"
sorry

mtheorem absvalue_th_26:
" for r be RealXREAL-0M1 holds 0NUMBERSK6 <=XXREAL-0R1 r +XCMPLX-0K2 |.ABSVALUEK1 r.|"
sorry

mtheorem absvalue_th_27:
" for r be RealXREAL-0M1 holds 0NUMBERSK6 <=XXREAL-0R1 (-XCMPLX-0K4 r)+XCMPLX-0K2 |.ABSVALUEK1 r.|"
sorry

mtheorem absvalue_th_28:
" for r be RealXREAL-0M1 holds  for s be RealXREAL-0M1 holds |.ABSVALUEK1 r.| =COMPLEX1R1 |.ABSVALUEK1 s.| implies r =COMPLEX1R1 s or r =COMPLEX1R1 -XCMPLX-0K4 s"
sorry

mtheorem absvalue_th_29:
" for m be NatORDINAL1M6 holds m =COMPLEX1R1 |.ABSVALUEK1 m.|"
   sorry

mtheorem absvalue_th_30:
" for r be RealXREAL-0M1 holds r <=XXREAL-0R1 0NUMBERSK6 implies |.ABSVALUEK1 r.| =COMPLEX1R1 -XCMPLX-0K4 r"
sorry

end
