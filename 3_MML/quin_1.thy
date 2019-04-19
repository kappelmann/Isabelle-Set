theory quin_1
  imports square_1 membered
   "../mizar_extension/E_number"
begin
(*begin*)
reserve x, a, b, c for "RealXREAL-0M1"
mdef quin_1_def_1 ("deltaQUIN-1K1'( _ , _ , _ ')" [0,0,0]228 ) where
  mlet "a be ComplexXCMPLX-0M1", "b be ComplexXCMPLX-0M1", "c be ComplexXCMPLX-0M1"
"func deltaQUIN-1K1(a,b,c) \<rightarrow> numberORDINAL1M2 equals
  b ^2SQUARE-1K1 -XCMPLX-0K6 (\<four>\<^sub>M *XCMPLX-0K3 a)*XCMPLX-0K3 c"
proof-
  (*coherence*)
    show "b ^2SQUARE-1K1 -XCMPLX-0K6 (\<four>\<^sub>M *XCMPLX-0K3 a)*XCMPLX-0K3 c be numberORDINAL1M2"
       sorry
qed "sorry"

mtheorem quin_1_cl_1:
  mlet "a be ComplexXCMPLX-0M1", "b be ComplexXCMPLX-0M1", "c be ComplexXCMPLX-0M1"
"cluster deltaQUIN-1K1(a,b,c) as-term-is complexXCMPLX-0V1"
proof
(*coherence*)
  show "deltaQUIN-1K1(a,b,c) be complexXCMPLX-0V1"
     sorry
qed "sorry"

mtheorem quin_1_cl_2:
  mlet "a be RealXREAL-0M1", "b be RealXREAL-0M1", "c be RealXREAL-0M1"
"cluster deltaQUIN-1K1(a,b,c) as-term-is realXREAL-0V1"
proof
(*coherence*)
  show "deltaQUIN-1K1(a,b,c) be realXREAL-0V1"
     sorry
qed "sorry"

mtheorem quin_1_th_1:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds  for x be ComplexXCMPLX-0M1 holds a <>HIDDENR2 0NUMBERSK6 implies (a *XCMPLX-0K3 x ^2SQUARE-1K1 +XCMPLX-0K2 b *XCMPLX-0K3 x)+XCMPLX-0K2 c =HIDDENR1 a *XCMPLX-0K3 (x +XCMPLX-0K2 b /XCMPLX-0K7 (\<two>\<^sub>M *XCMPLX-0K3 a))^2SQUARE-1K1 -XCMPLX-0K6 deltaQUIN-1K1(a,b,c) /XCMPLX-0K7 (\<four>\<^sub>M *XCMPLX-0K3 a)"
sorry

mtheorem quin_1_th_2:
" for x be RealXREAL-0M1 holds  for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds a >XXREAL-0R4 0NUMBERSK6 & deltaQUIN-1K1(a,b,c) <=XXREAL-0R1 0NUMBERSK6 implies (a *XCMPLX-0K3 x ^2SQUARE-1K1 +XCMPLX-0K2 b *XCMPLX-0K3 x)+XCMPLX-0K2 c >=XXREAL-0R2 0NUMBERSK6"
sorry

mtheorem quin_1_th_3:
" for x be RealXREAL-0M1 holds  for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds a >XXREAL-0R4 0NUMBERSK6 & deltaQUIN-1K1(a,b,c) <XXREAL-0R3 0NUMBERSK6 implies (a *XCMPLX-0K3 x ^2SQUARE-1K1 +XCMPLX-0K2 b *XCMPLX-0K3 x)+XCMPLX-0K2 c >XXREAL-0R4 0NUMBERSK6"
sorry

mtheorem quin_1_th_4:
" for x be RealXREAL-0M1 holds  for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds a <XXREAL-0R3 0NUMBERSK6 & deltaQUIN-1K1(a,b,c) <=XXREAL-0R1 0NUMBERSK6 implies (a *XCMPLX-0K3 x ^2SQUARE-1K1 +XCMPLX-0K2 b *XCMPLX-0K3 x)+XCMPLX-0K2 c <=XXREAL-0R1 0NUMBERSK6"
sorry

mtheorem quin_1_th_5:
" for x be RealXREAL-0M1 holds  for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds a <XXREAL-0R3 0NUMBERSK6 & deltaQUIN-1K1(a,b,c) <XXREAL-0R3 0NUMBERSK6 implies (a *XCMPLX-0K3 x ^2SQUARE-1K1 +XCMPLX-0K2 b *XCMPLX-0K3 x)+XCMPLX-0K2 c <XXREAL-0R3 0NUMBERSK6"
sorry

mtheorem quin_1_th_6:
" for x be RealXREAL-0M1 holds  for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds a >XXREAL-0R4 0NUMBERSK6 & (a *XCMPLX-0K3 x ^2SQUARE-1K1 +XCMPLX-0K2 b *XCMPLX-0K3 x)+XCMPLX-0K2 c >=XXREAL-0R2 0NUMBERSK6 implies ((\<two>\<^sub>M *XCMPLX-0K3 a)*XCMPLX-0K3 x +XCMPLX-0K2 b)^2SQUARE-1K1 -XCMPLX-0K6 deltaQUIN-1K1(a,b,c) >=XXREAL-0R2 0NUMBERSK6"
sorry

mtheorem quin_1_th_7:
" for x be RealXREAL-0M1 holds  for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds a >XXREAL-0R4 0NUMBERSK6 & (a *XCMPLX-0K3 x ^2SQUARE-1K1 +XCMPLX-0K2 b *XCMPLX-0K3 x)+XCMPLX-0K2 c >XXREAL-0R4 0NUMBERSK6 implies ((\<two>\<^sub>M *XCMPLX-0K3 a)*XCMPLX-0K3 x +XCMPLX-0K2 b)^2SQUARE-1K1 -XCMPLX-0K6 deltaQUIN-1K1(a,b,c) >XXREAL-0R4 0NUMBERSK6"
sorry

mtheorem quin_1_th_8:
" for x be RealXREAL-0M1 holds  for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds a <XXREAL-0R3 0NUMBERSK6 & (a *XCMPLX-0K3 x ^2SQUARE-1K1 +XCMPLX-0K2 b *XCMPLX-0K3 x)+XCMPLX-0K2 c <=XXREAL-0R1 0NUMBERSK6 implies ((\<two>\<^sub>M *XCMPLX-0K3 a)*XCMPLX-0K3 x +XCMPLX-0K2 b)^2SQUARE-1K1 -XCMPLX-0K6 deltaQUIN-1K1(a,b,c) >=XXREAL-0R2 0NUMBERSK6"
sorry

mtheorem quin_1_th_9:
" for x be RealXREAL-0M1 holds  for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds a <XXREAL-0R3 0NUMBERSK6 & (a *XCMPLX-0K3 x ^2SQUARE-1K1 +XCMPLX-0K2 b *XCMPLX-0K3 x)+XCMPLX-0K2 c <XXREAL-0R3 0NUMBERSK6 implies ((\<two>\<^sub>M *XCMPLX-0K3 a)*XCMPLX-0K3 x +XCMPLX-0K2 b)^2SQUARE-1K1 -XCMPLX-0K6 deltaQUIN-1K1(a,b,c) >XXREAL-0R4 0NUMBERSK6"
sorry

mtheorem quin_1_th_10:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds ( for x be RealXREAL-0M1 holds (a *XCMPLX-0K3 x ^2SQUARE-1K1 +XCMPLX-0K2 b *XCMPLX-0K3 x)+XCMPLX-0K2 c >=XXREAL-0R2 0NUMBERSK6) & a >XXREAL-0R4 0NUMBERSK6 implies deltaQUIN-1K1(a,b,c) <=XXREAL-0R1 0NUMBERSK6"
sorry

mtheorem quin_1_th_11:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds ( for x be RealXREAL-0M1 holds (a *XCMPLX-0K3 x ^2SQUARE-1K1 +XCMPLX-0K2 b *XCMPLX-0K3 x)+XCMPLX-0K2 c <=XXREAL-0R1 0NUMBERSK6) & a <XXREAL-0R3 0NUMBERSK6 implies deltaQUIN-1K1(a,b,c) <=XXREAL-0R1 0NUMBERSK6"
sorry

mtheorem quin_1_th_12:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds ( for x be RealXREAL-0M1 holds (a *XCMPLX-0K3 x ^2SQUARE-1K1 +XCMPLX-0K2 b *XCMPLX-0K3 x)+XCMPLX-0K2 c >XXREAL-0R4 0NUMBERSK6) & a >XXREAL-0R4 0NUMBERSK6 implies deltaQUIN-1K1(a,b,c) <XXREAL-0R3 0NUMBERSK6"
sorry

mtheorem quin_1_th_13:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds ( for x be RealXREAL-0M1 holds (a *XCMPLX-0K3 x ^2SQUARE-1K1 +XCMPLX-0K2 b *XCMPLX-0K3 x)+XCMPLX-0K2 c <XXREAL-0R3 0NUMBERSK6) & a <XXREAL-0R3 0NUMBERSK6 implies deltaQUIN-1K1(a,b,c) <XXREAL-0R3 0NUMBERSK6"
sorry

mtheorem quin_1_th_14:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds  for x be ComplexXCMPLX-0M1 holds a <>HIDDENR2 0NUMBERSK6 & (a *XCMPLX-0K3 x ^2SQUARE-1K1 +XCMPLX-0K2 b *XCMPLX-0K3 x)+XCMPLX-0K2 c =HIDDENR1 0NUMBERSK6 implies ((\<two>\<^sub>M *XCMPLX-0K3 a)*XCMPLX-0K3 x +XCMPLX-0K2 b)^2SQUARE-1K1 -XCMPLX-0K6 deltaQUIN-1K1(a,b,c) =HIDDENR1 0NUMBERSK6"
sorry

mlemma quin_1_lm_1:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds a ^2SQUARE-1K1 =HIDDENR1 b ^2SQUARE-1K1 implies a =HIDDENR1 b or a =HIDDENR1 -XCMPLX-0K4 b"
sorry

mtheorem quin_1_th_15:
" for x be RealXREAL-0M1 holds  for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds (a <>HIDDENR2 0NUMBERSK6 & deltaQUIN-1K1(a,b,c) >=XXREAL-0R2 0NUMBERSK6) & (a *XCMPLX-0K3 x ^2SQUARE-1K1 +XCMPLX-0K2 b *XCMPLX-0K3 x)+XCMPLX-0K2 c =HIDDENR1 0NUMBERSK6 implies x =HIDDENR1 ((-XCMPLX-0K4 b)-XCMPLX-0K6 sqrtSQUARE-1K3 (deltaQUIN-1K1(a,b,c)))/XCMPLX-0K7 (\<two>\<^sub>M *XCMPLX-0K3 a) or x =HIDDENR1 ((-XCMPLX-0K4 b)+XCMPLX-0K2 sqrtSQUARE-1K3 (deltaQUIN-1K1(a,b,c)))/XCMPLX-0K7 (\<two>\<^sub>M *XCMPLX-0K3 a)"
sorry

mtheorem quin_1_th_16:
" for x be RealXREAL-0M1 holds  for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds a <>HIDDENR2 0NUMBERSK6 & deltaQUIN-1K1(a,b,c) >=XXREAL-0R2 0NUMBERSK6 implies (a *XCMPLX-0K3 x ^2SQUARE-1K1 +XCMPLX-0K2 b *XCMPLX-0K3 x)+XCMPLX-0K2 c =HIDDENR1 (a *XCMPLX-0K3 (x -XCMPLX-0K6 ((-XCMPLX-0K4 b)-XCMPLX-0K6 sqrtSQUARE-1K3 (deltaQUIN-1K1(a,b,c)))/XCMPLX-0K7 (\<two>\<^sub>M *XCMPLX-0K3 a)))*XCMPLX-0K3 (x -XCMPLX-0K6 ((-XCMPLX-0K4 b)+XCMPLX-0K2 sqrtSQUARE-1K3 (deltaQUIN-1K1(a,b,c)))/XCMPLX-0K7 (\<two>\<^sub>M *XCMPLX-0K3 a))"
sorry

mtheorem quin_1_th_17:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds a <XXREAL-0R3 0NUMBERSK6 & deltaQUIN-1K1(a,b,c) >XXREAL-0R4 0NUMBERSK6 implies ((-XCMPLX-0K4 b)+XCMPLX-0K2 sqrtSQUARE-1K3 (deltaQUIN-1K1(a,b,c)))/XCMPLX-0K7 (\<two>\<^sub>M *XCMPLX-0K3 a) <XXREAL-0R3 ((-XCMPLX-0K4 b)-XCMPLX-0K6 sqrtSQUARE-1K3 (deltaQUIN-1K1(a,b,c)))/XCMPLX-0K7 (\<two>\<^sub>M *XCMPLX-0K3 a)"
sorry

mtheorem quin_1_th_18:
" for x be RealXREAL-0M1 holds  for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds a <XXREAL-0R3 0NUMBERSK6 & deltaQUIN-1K1(a,b,c) >XXREAL-0R4 0NUMBERSK6 implies ((a *XCMPLX-0K3 x ^2SQUARE-1K1 +XCMPLX-0K2 b *XCMPLX-0K3 x)+XCMPLX-0K2 c >XXREAL-0R4 0NUMBERSK6 iff ((-XCMPLX-0K4 b)+XCMPLX-0K2 sqrtSQUARE-1K3 (deltaQUIN-1K1(a,b,c)))/XCMPLX-0K7 (\<two>\<^sub>M *XCMPLX-0K3 a) <XXREAL-0R3 x & x <XXREAL-0R3 ((-XCMPLX-0K4 b)-XCMPLX-0K6 sqrtSQUARE-1K3 (deltaQUIN-1K1(a,b,c)))/XCMPLX-0K7 (\<two>\<^sub>M *XCMPLX-0K3 a))"
sorry

mtheorem quin_1_th_19:
" for x be RealXREAL-0M1 holds  for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds a <XXREAL-0R3 0NUMBERSK6 & deltaQUIN-1K1(a,b,c) >XXREAL-0R4 0NUMBERSK6 implies ((a *XCMPLX-0K3 x ^2SQUARE-1K1 +XCMPLX-0K2 b *XCMPLX-0K3 x)+XCMPLX-0K2 c <XXREAL-0R3 0NUMBERSK6 iff x <XXREAL-0R3 ((-XCMPLX-0K4 b)+XCMPLX-0K2 sqrtSQUARE-1K3 (deltaQUIN-1K1(a,b,c)))/XCMPLX-0K7 (\<two>\<^sub>M *XCMPLX-0K3 a) or x >XXREAL-0R4 ((-XCMPLX-0K4 b)-XCMPLX-0K6 sqrtSQUARE-1K3 (deltaQUIN-1K1(a,b,c)))/XCMPLX-0K7 (\<two>\<^sub>M *XCMPLX-0K3 a))"
sorry

mtheorem quin_1_th_20:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds  for x be ComplexXCMPLX-0M1 holds (a <>HIDDENR2 0NUMBERSK6 & deltaQUIN-1K1(a,b,c) =HIDDENR1 0NUMBERSK6) & (a *XCMPLX-0K3 x ^2SQUARE-1K1 +XCMPLX-0K2 b *XCMPLX-0K3 x)+XCMPLX-0K2 c =HIDDENR1 0NUMBERSK6 implies x =HIDDENR1 -XCMPLX-0K4 b /XCMPLX-0K7 (\<two>\<^sub>M *XCMPLX-0K3 a)"
sorry

mtheorem quin_1_th_21:
" for x be RealXREAL-0M1 holds  for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds a >XXREAL-0R4 0NUMBERSK6 & ((\<two>\<^sub>M *XCMPLX-0K3 a)*XCMPLX-0K3 x +XCMPLX-0K2 b)^2SQUARE-1K1 -XCMPLX-0K6 deltaQUIN-1K1(a,b,c) >XXREAL-0R4 0NUMBERSK6 implies (a *XCMPLX-0K3 x ^2SQUARE-1K1 +XCMPLX-0K2 b *XCMPLX-0K3 x)+XCMPLX-0K2 c >XXREAL-0R4 0NUMBERSK6"
sorry

mtheorem quin_1_th_22:
" for x be RealXREAL-0M1 holds  for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds a >XXREAL-0R4 0NUMBERSK6 & deltaQUIN-1K1(a,b,c) =HIDDENR1 0NUMBERSK6 implies ((a *XCMPLX-0K3 x ^2SQUARE-1K1 +XCMPLX-0K2 b *XCMPLX-0K3 x)+XCMPLX-0K2 c >XXREAL-0R4 0NUMBERSK6 iff x <>HIDDENR2 -XCMPLX-0K4 b /XCMPLX-0K7 (\<two>\<^sub>M *XCMPLX-0K3 a))"
sorry

mtheorem quin_1_th_23:
" for x be RealXREAL-0M1 holds  for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds a <XXREAL-0R3 0NUMBERSK6 & ((\<two>\<^sub>M *XCMPLX-0K3 a)*XCMPLX-0K3 x +XCMPLX-0K2 b)^2SQUARE-1K1 -XCMPLX-0K6 deltaQUIN-1K1(a,b,c) >XXREAL-0R4 0NUMBERSK6 implies (a *XCMPLX-0K3 x ^2SQUARE-1K1 +XCMPLX-0K2 b *XCMPLX-0K3 x)+XCMPLX-0K2 c <XXREAL-0R3 0NUMBERSK6"
sorry

mtheorem quin_1_th_24:
" for x be RealXREAL-0M1 holds  for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds a <XXREAL-0R3 0NUMBERSK6 & deltaQUIN-1K1(a,b,c) =HIDDENR1 0NUMBERSK6 implies ((a *XCMPLX-0K3 x ^2SQUARE-1K1 +XCMPLX-0K2 b *XCMPLX-0K3 x)+XCMPLX-0K2 c <XXREAL-0R3 0NUMBERSK6 iff x <>HIDDENR2 -XCMPLX-0K4 b /XCMPLX-0K7 (\<two>\<^sub>M *XCMPLX-0K3 a))"
sorry

mtheorem quin_1_th_25:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds a >XXREAL-0R4 0NUMBERSK6 & deltaQUIN-1K1(a,b,c) >XXREAL-0R4 0NUMBERSK6 implies ((-XCMPLX-0K4 b)+XCMPLX-0K2 sqrtSQUARE-1K3 (deltaQUIN-1K1(a,b,c)))/XCMPLX-0K7 (\<two>\<^sub>M *XCMPLX-0K3 a) >XXREAL-0R4 ((-XCMPLX-0K4 b)-XCMPLX-0K6 sqrtSQUARE-1K3 (deltaQUIN-1K1(a,b,c)))/XCMPLX-0K7 (\<two>\<^sub>M *XCMPLX-0K3 a)"
sorry

mtheorem quin_1_th_26:
" for x be RealXREAL-0M1 holds  for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds a >XXREAL-0R4 0NUMBERSK6 & deltaQUIN-1K1(a,b,c) >XXREAL-0R4 0NUMBERSK6 implies ((a *XCMPLX-0K3 x ^2SQUARE-1K1 +XCMPLX-0K2 b *XCMPLX-0K3 x)+XCMPLX-0K2 c <XXREAL-0R3 0NUMBERSK6 iff ((-XCMPLX-0K4 b)-XCMPLX-0K6 sqrtSQUARE-1K3 (deltaQUIN-1K1(a,b,c)))/XCMPLX-0K7 (\<two>\<^sub>M *XCMPLX-0K3 a) <XXREAL-0R3 x & x <XXREAL-0R3 ((-XCMPLX-0K4 b)+XCMPLX-0K2 sqrtSQUARE-1K3 (deltaQUIN-1K1(a,b,c)))/XCMPLX-0K7 (\<two>\<^sub>M *XCMPLX-0K3 a))"
sorry

mtheorem quin_1_th_27:
" for x be RealXREAL-0M1 holds  for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds a >XXREAL-0R4 0NUMBERSK6 & deltaQUIN-1K1(a,b,c) >XXREAL-0R4 0NUMBERSK6 implies ((a *XCMPLX-0K3 x ^2SQUARE-1K1 +XCMPLX-0K2 b *XCMPLX-0K3 x)+XCMPLX-0K2 c >XXREAL-0R4 0NUMBERSK6 iff x <XXREAL-0R3 ((-XCMPLX-0K4 b)-XCMPLX-0K6 sqrtSQUARE-1K3 (deltaQUIN-1K1(a,b,c)))/XCMPLX-0K7 (\<two>\<^sub>M *XCMPLX-0K3 a) or x >XXREAL-0R4 ((-XCMPLX-0K4 b)+XCMPLX-0K2 sqrtSQUARE-1K3 (deltaQUIN-1K1(a,b,c)))/XCMPLX-0K7 (\<two>\<^sub>M *XCMPLX-0K3 a))"
sorry

end
