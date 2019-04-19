theory arytm_1
  imports arytm_2
begin
(*begin*)
reserve x, y, z for "ElementSUBSET-1M1-of REAL+ARYTM-2K2"
mtheorem arytm_1_th_1:
" for x be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for y be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds x +ARYTM-2K7 y =HIDDENR1 y implies x =HIDDENR1 {}ARYTM-3K12"
sorry

mlemma arytm_1_lm_1:
" for x be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for y be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for z be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds x *'ARYTM-2K8 y =HIDDENR1 x *'ARYTM-2K8 z & x <>HIDDENR2 {}ARYTM-3K12 implies y =HIDDENR1 z"
sorry

mtheorem arytm_1_th_2:
" for x be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for y be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds x *'ARYTM-2K8 y =HIDDENR1 {}ARYTM-3K12 implies x =HIDDENR1 {}ARYTM-3K12 or y =HIDDENR1 {}ARYTM-3K12"
sorry

mtheorem arytm_1_th_3:
" for x be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for y be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for z be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds x <='ARYTM-2R1 y & y <='ARYTM-2R1 z implies x <='ARYTM-2R1 z"
sorry

mtheorem arytm_1_th_4:
" for x be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for y be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds x <='ARYTM-2R1 y & y <='ARYTM-2R1 x implies x =HIDDENR1 y"
sorry

mtheorem arytm_1_th_5:
" for x be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for y be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds x <='ARYTM-2R1 y & y =HIDDENR1 {}ARYTM-3K12 implies x =HIDDENR1 {}ARYTM-3K12"
sorry

mtheorem arytm_1_th_6:
" for x be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for y be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds x =HIDDENR1 {}ARYTM-3K12 implies x <='ARYTM-2R1 y"
sorry

mtheorem arytm_1_th_7:
" for x be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for y be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for z be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds x <='ARYTM-2R1 y iff x +ARYTM-2K7 z <='ARYTM-2R1 y +ARYTM-2K7 z"
sorry

mtheorem arytm_1_th_8:
" for x be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for y be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for z be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds x <='ARYTM-2R1 y implies x *'ARYTM-2K8 z <='ARYTM-2R1 y *'ARYTM-2K8 z"
sorry

mlemma arytm_1_lm_2:
" for x be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for y be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for z be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds x *'ARYTM-2K8 y <='ARYTM-2R1 x *'ARYTM-2K8 z & x <>HIDDENR2 {}ARYTM-3K12 implies y <='ARYTM-2R1 z"
sorry

mdef arytm_1_def_1 (" _ -''ARYTM-1K1  _ " [132,132]132 ) where
  mlet "x be ElementSUBSET-1M1-of REAL+ARYTM-2K2", "y be ElementSUBSET-1M1-of REAL+ARYTM-2K2"
"func x -'ARYTM-1K1 y \<rightarrow> ElementSUBSET-1M1-of REAL+ARYTM-2K2 means
  \<lambda>it. it +ARYTM-2K7 y =HIDDENR1 x if y <='ARYTM-2R1 x otherwise \<lambda>it. it =HIDDENR1 {}ARYTM-3K12"
proof-
  (*existence*)
    show "(y <='ARYTM-2R1 x implies ( ex it be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st it +ARYTM-2K7 y =HIDDENR1 x)) & ( not y <='ARYTM-2R1 x implies ( ex it be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st it =HIDDENR1 {}ARYTM-3K12))"
sorry
  (*consistency*)
    show " for it be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  True "
      using arytm_2_th_11 sorry
  (*uniqueness*)
    show " for it1 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for it2 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds (y <='ARYTM-2R1 x implies (it1 +ARYTM-2K7 y =HIDDENR1 x & it2 +ARYTM-2K7 y =HIDDENR1 x implies it1 =HIDDENR1 it2)) & ( not y <='ARYTM-2R1 x implies (it1 =HIDDENR1 {}ARYTM-3K12 & it2 =HIDDENR1 {}ARYTM-3K12 implies it1 =HIDDENR1 it2))"
      using arytm_2_th_11 sorry
qed "sorry"

mlemma arytm_1_lm_3:
" for x be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds x -'ARYTM-1K1 x =HIDDENR1 {}ARYTM-3K12"
sorry

mtheorem arytm_1_th_9:
" for x be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for y be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds x <='ARYTM-2R1 y or x -'ARYTM-1K1 y <>HIDDENR2 {}ARYTM-3K12"
sorry

mtheorem arytm_1_th_10:
" for x be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for y be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds x <='ARYTM-2R1 y & y -'ARYTM-1K1 x =HIDDENR1 {}ARYTM-3K12 implies x =HIDDENR1 y"
sorry

mtheorem arytm_1_th_11:
" for x be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for y be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds x -'ARYTM-1K1 y <='ARYTM-2R1 x"
sorry

mlemma arytm_1_lm_4:
" for x be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for y be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds x =HIDDENR1 {}ARYTM-3K12 implies y -'ARYTM-1K1 x =HIDDENR1 y"
sorry

mlemma arytm_1_lm_5:
" for x be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for y be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds (x +ARYTM-2K7 y)-'ARYTM-1K1 y =HIDDENR1 x"
sorry

mlemma arytm_1_lm_6:
" for x be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for y be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds x <='ARYTM-2R1 y implies y -'ARYTM-1K1 (y -'ARYTM-1K1 x) =HIDDENR1 x"
sorry

mlemma arytm_1_lm_7:
" for x be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for y be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for z be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds z -'ARYTM-1K1 y <='ARYTM-2R1 x iff z <='ARYTM-2R1 x +ARYTM-2K7 y"
sorry

mlemma arytm_1_lm_8:
" for x be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for y be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for z be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds y <='ARYTM-2R1 x implies (z +ARYTM-2K7 y <='ARYTM-2R1 x iff z <='ARYTM-2R1 x -'ARYTM-1K1 y)"
sorry

mlemma arytm_1_lm_9:
" for x be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for y be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for z be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds (z -'ARYTM-1K1 y)-'ARYTM-1K1 x =HIDDENR1 z -'ARYTM-1K1 (x +ARYTM-2K7 y)"
sorry

mlemma arytm_1_lm_10:
" for x be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for y be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for z be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds (y -'ARYTM-1K1 z)-'ARYTM-1K1 x =HIDDENR1 (y -'ARYTM-1K1 x)-'ARYTM-1K1 z"
sorry

mtheorem arytm_1_th_12:
" for x be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for y be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for z be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds y <='ARYTM-2R1 x & y <='ARYTM-2R1 z implies x +ARYTM-2K7 (z -'ARYTM-1K1 y) =HIDDENR1 (x -'ARYTM-1K1 y)+ARYTM-2K7 z"
sorry

mtheorem arytm_1_th_13:
" for x be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for y be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for z be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds z <='ARYTM-2R1 y implies x +ARYTM-2K7 (y -'ARYTM-1K1 z) =HIDDENR1 (x +ARYTM-2K7 y)-'ARYTM-1K1 z"
sorry

mlemma arytm_1_lm_11:
" for x be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for y be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for z be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds y <='ARYTM-2R1 z implies x -'ARYTM-1K1 (z -'ARYTM-1K1 y) =HIDDENR1 (x +ARYTM-2K7 y)-'ARYTM-1K1 z"
sorry

mlemma arytm_1_lm_12:
" for x be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for y be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for z be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds z <='ARYTM-2R1 x & y <='ARYTM-2R1 z implies x -'ARYTM-1K1 (z -'ARYTM-1K1 y) =HIDDENR1 (x -'ARYTM-1K1 z)+ARYTM-2K7 y"
sorry

mlemma arytm_1_lm_13:
" for x be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for y be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for z be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds x <='ARYTM-2R1 z & y <='ARYTM-2R1 z implies x -'ARYTM-1K1 (z -'ARYTM-1K1 y) =HIDDENR1 y -'ARYTM-1K1 (z -'ARYTM-1K1 x)"
sorry

mtheorem arytm_1_th_14:
" for x be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for y be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for z be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds z <='ARYTM-2R1 x & y <='ARYTM-2R1 z implies (x -'ARYTM-1K1 z)+ARYTM-2K7 y =HIDDENR1 x -'ARYTM-1K1 (z -'ARYTM-1K1 y)"
sorry

mtheorem arytm_1_th_15:
" for x be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for y be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for z be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds y <='ARYTM-2R1 x & y <='ARYTM-2R1 z implies (z -'ARYTM-1K1 y)+ARYTM-2K7 x =HIDDENR1 (x -'ARYTM-1K1 y)+ARYTM-2K7 z"
sorry

mtheorem arytm_1_th_16:
" for x be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for y be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for z be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds x <='ARYTM-2R1 y implies z -'ARYTM-1K1 y <='ARYTM-2R1 z -'ARYTM-1K1 x"
sorry

mtheorem arytm_1_th_17:
" for x be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for y be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for z be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds x <='ARYTM-2R1 y implies x -'ARYTM-1K1 z <='ARYTM-2R1 y -'ARYTM-1K1 z"
sorry

mlemma arytm_1_lm_14:
" for x be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for y be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for z be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds x *'ARYTM-2K8 (y -'ARYTM-1K1 z) =HIDDENR1 x *'ARYTM-2K8 y -'ARYTM-1K1 x *'ARYTM-2K8 z"
sorry

mdef arytm_1_def_2 (" _ -ARYTM-1K2  _ " [132,132]132 ) where
  mlet "x be ElementSUBSET-1M1-of REAL+ARYTM-2K2", "y be ElementSUBSET-1M1-of REAL+ARYTM-2K2"
"func x -ARYTM-1K2 y \<rightarrow> setHIDDENM2 equals
  x -'ARYTM-1K1 y if y <='ARYTM-2R1 x otherwise [TARSKIK4 {}ARYTM-3K12,y -'ARYTM-1K1 x ]"
proof-
  (*coherence*)
    show "(y <='ARYTM-2R1 x implies x -'ARYTM-1K1 y be setHIDDENM2) & ( not y <='ARYTM-2R1 x implies [TARSKIK4 {}ARYTM-3K12,y -'ARYTM-1K1 x ] be setHIDDENM2)"
      using tarski_th_1 sorry
  (*consistency*)
    show " for it be setHIDDENM2 holds  True "
      using tarski_th_1 sorry
qed "sorry"

mtheorem arytm_1_th_18:
" for x be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds x -ARYTM-1K2 x =HIDDENR1 {}ARYTM-3K12"
sorry

mtheorem arytm_1_th_19:
" for x be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for y be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds x =HIDDENR1 {}ARYTM-3K12 & y <>HIDDENR2 {}ARYTM-3K12 implies x -ARYTM-1K2 y =HIDDENR1 [TARSKIK4 {}ARYTM-3K12,y ]"
sorry

mtheorem arytm_1_th_20:
" for x be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for y be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for z be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds z <='ARYTM-2R1 y implies x +ARYTM-2K7 (y -'ARYTM-1K1 z) =HIDDENR1 (x +ARYTM-2K7 y)-ARYTM-1K2 z"
sorry

mtheorem arytm_1_th_21:
" for x be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for y be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for z be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  not z <='ARYTM-2R1 y implies x -ARYTM-1K2 (z -'ARYTM-1K1 y) =HIDDENR1 (x +ARYTM-2K7 y)-ARYTM-1K2 z"
sorry

mtheorem arytm_1_th_22:
" for x be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for y be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for z be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds y <='ARYTM-2R1 x &  not y <='ARYTM-2R1 z implies x -ARYTM-1K2 (y -'ARYTM-1K1 z) =HIDDENR1 (x -'ARYTM-1K1 y)+ARYTM-2K7 z"
sorry

mtheorem arytm_1_th_23:
" for x be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for y be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for z be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  not y <='ARYTM-2R1 x &  not y <='ARYTM-2R1 z implies x -ARYTM-1K2 (y -'ARYTM-1K1 z) =HIDDENR1 z -ARYTM-1K2 (y -'ARYTM-1K1 x)"
sorry

mtheorem arytm_1_th_24:
" for x be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for y be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for z be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds y <='ARYTM-2R1 x implies x -ARYTM-1K2 (y +ARYTM-2K7 z) =HIDDENR1 (x -'ARYTM-1K1 y)-ARYTM-1K2 z"
sorry

mtheorem arytm_1_th_25:
" for x be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for y be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for z be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds x <='ARYTM-2R1 y & z <='ARYTM-2R1 y implies (y -'ARYTM-1K1 z)-ARYTM-1K2 x =HIDDENR1 (y -'ARYTM-1K1 x)-ARYTM-1K2 z"
sorry

mtheorem arytm_1_th_26:
" for x be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for y be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for z be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds z <='ARYTM-2R1 y implies x *'ARYTM-2K8 (y -'ARYTM-1K1 z) =HIDDENR1 x *'ARYTM-2K8 y -ARYTM-1K2 x *'ARYTM-2K8 z"
sorry

mtheorem arytm_1_th_27:
" for x be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for y be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for z be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  not z <='ARYTM-2R1 y & x <>HIDDENR2 {}ARYTM-3K12 implies [TARSKIK4 {}ARYTM-3K12,x *'ARYTM-2K8 (z -'ARYTM-1K1 y) ] =HIDDENR1 x *'ARYTM-2K8 y -ARYTM-1K2 x *'ARYTM-2K8 z"
sorry

mtheorem arytm_1_th_28:
" for x be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for y be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for z be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds (y -'ARYTM-1K1 z <>HIDDENR2 {}ARYTM-3K12 & z <='ARYTM-2R1 y) & x <>HIDDENR2 {}ARYTM-3K12 implies x *'ARYTM-2K8 z -ARYTM-1K2 x *'ARYTM-2K8 y =HIDDENR1 [TARSKIK4 {}ARYTM-3K12,x *'ARYTM-2K8 (y -'ARYTM-1K1 z) ]"
sorry

end
