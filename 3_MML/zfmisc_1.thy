theory zfmisc_1
  imports xregular 
begin
(*begin*)
reserve u, v, x, x1, x2, y, y1, y2, z, p, a for "objectHIDDENM1"
reserve A, B, X, X1, X2, X3, X4, Y, Y1, Y2, Z, N, M for "setHIDDENM2"
mlemma zfmisc_1_lm_1:
" for x be objectHIDDENM1 holds  for X be setHIDDENM2 holds {TARSKIK1 x} c=TARSKIR1 X iff x inHIDDENR3 X"
sorry

mlemma zfmisc_1_lm_2:
" for x be objectHIDDENM1 holds  for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds Y c=TARSKIR1 X &  not x inHIDDENR3 Y implies Y c=TARSKIR1 X \\XBOOLE-0K4 {TARSKIK1 x}"
sorry

mlemma zfmisc_1_lm_3:
" for x be objectHIDDENM1 holds  for Y be setHIDDENM2 holds Y c=TARSKIR1 {TARSKIK1 x} iff Y =XBOOLE-0R4 {}XBOOLE-0K1 or Y =XBOOLE-0R4 {TARSKIK1 x}"
sorry

mdef zfmisc_1_def_1 ("boolZFMISC-1K1  _ " [228]228 ) where
  mlet "X be setHIDDENM2"
"func boolZFMISC-1K1 X \<rightarrow> setHIDDENM2 means
  \<lambda>it.  for Z be setHIDDENM2 holds Z inTARSKIR2 it iff Z c=TARSKIR1 X"
proof-
  (*existence*)
    show " ex it be setHIDDENM2 st  for Z be setHIDDENM2 holds Z inTARSKIR2 it iff Z c=TARSKIR1 X"
sorry
  (*uniqueness*)
    show " for it1 be setHIDDENM2 holds  for it2 be setHIDDENM2 holds ( for Z be setHIDDENM2 holds Z inTARSKIR2 it1 iff Z c=TARSKIR1 X) & ( for Z be setHIDDENM2 holds Z inTARSKIR2 it2 iff Z c=TARSKIR1 X) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mdef zfmisc_1_def_2 ("[:ZFMISC-1K2 _ , _ :]" [0,0]164 ) where
  mlet "X1 be setHIDDENM2", "X2 be setHIDDENM2"
"func [:ZFMISC-1K2 X1,X2 :] \<rightarrow> setHIDDENM2 means
  \<lambda>it.  for z be objectHIDDENM1 holds z inHIDDENR3 it iff ( ex x be objectHIDDENM1 st  ex y be objectHIDDENM1 st (x inHIDDENR3 X1 & y inHIDDENR3 X2) & z =HIDDENR1 [TARSKIK4 x,y ])"
proof-
  (*existence*)
    show " ex it be setHIDDENM2 st  for z be objectHIDDENM1 holds z inHIDDENR3 it iff ( ex x be objectHIDDENM1 st  ex y be objectHIDDENM1 st (x inHIDDENR3 X1 & y inHIDDENR3 X2) & z =HIDDENR1 [TARSKIK4 x,y ])"
sorry
  (*uniqueness*)
    show " for it1 be setHIDDENM2 holds  for it2 be setHIDDENM2 holds ( for z be objectHIDDENM1 holds z inHIDDENR3 it1 iff ( ex x be objectHIDDENM1 st  ex y be objectHIDDENM1 st (x inHIDDENR3 X1 & y inHIDDENR3 X2) & z =HIDDENR1 [TARSKIK4 x,y ])) & ( for z be objectHIDDENM1 holds z inHIDDENR3 it2 iff ( ex x be objectHIDDENM1 st  ex y be objectHIDDENM1 st (x inHIDDENR3 X1 & y inHIDDENR3 X2) & z =HIDDENR1 [TARSKIK4 x,y ])) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mdef zfmisc_1_def_3 ("[:ZFMISC-1K3 _ , _ , _ :]" [0,0,0]164 ) where
  mlet "X1 be setHIDDENM2", "X2 be setHIDDENM2", "X3 be setHIDDENM2"
"func [:ZFMISC-1K3 X1,X2,X3 :] \<rightarrow> setHIDDENM2 equals
  [:ZFMISC-1K2 [:ZFMISC-1K2 X1,X2 :],X3 :]"
proof-
  (*coherence*)
    show "[:ZFMISC-1K2 [:ZFMISC-1K2 X1,X2 :],X3 :] be setHIDDENM2"
       sorry
qed "sorry"

mdef zfmisc_1_def_4 ("[:ZFMISC-1K4 _ , _ , _ , _ :]" [0,0,0,0]164 ) where
  mlet "X1 be setHIDDENM2", "X2 be setHIDDENM2", "X3 be setHIDDENM2", "X4 be setHIDDENM2"
"func [:ZFMISC-1K4 X1,X2,X3,X4 :] \<rightarrow> setHIDDENM2 equals
  [:ZFMISC-1K2 [:ZFMISC-1K3 X1,X2,X3 :],X4 :]"
proof-
  (*coherence*)
    show "[:ZFMISC-1K2 [:ZFMISC-1K3 X1,X2,X3 :],X4 :] be setHIDDENM2"
       sorry
qed "sorry"

(*begin*)
mtheorem zfmisc_1_th_1:
"boolZFMISC-1K1 ({}XBOOLE-0K1) =XBOOLE-0R4 {TARSKIK1 {}XBOOLE-0K1 }"
sorry

mtheorem zfmisc_1_th_2:
"unionTARSKIK3 ({}XBOOLE-0K1) =XBOOLE-0R4 {}XBOOLE-0K1"
sorry

mtheorem zfmisc_1_th_3:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds {TARSKIK1 x} c=TARSKIR1 {TARSKIK1 y} implies x =HIDDENR1 y"
sorry

mtheorem zfmisc_1_th_4:
" for x be objectHIDDENM1 holds  for y1 be objectHIDDENM1 holds  for y2 be objectHIDDENM1 holds {TARSKIK1 x} =XBOOLE-0R4 {TARSKIK2 y1,y2 } implies x =HIDDENR1 y1"
sorry

mtheorem zfmisc_1_th_5:
" for x be objectHIDDENM1 holds  for y1 be objectHIDDENM1 holds  for y2 be objectHIDDENM1 holds {TARSKIK1 x} =XBOOLE-0R4 {TARSKIK2 y1,y2 } implies y1 =HIDDENR1 y2"
sorry

mtheorem zfmisc_1_th_6:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for y1 be objectHIDDENM1 holds  for y2 be objectHIDDENM1 holds {TARSKIK2 x1,x2 } =XBOOLE-0R4 {TARSKIK2 y1,y2 } implies x1 =HIDDENR1 y1 or x1 =HIDDENR1 y2"
sorry

mtheorem zfmisc_1_th_7:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds {TARSKIK1 x} c=TARSKIR1 {TARSKIK2 x,y }"
sorry

mlemma zfmisc_1_lm_4:
" for x be objectHIDDENM1 holds  for X be setHIDDENM2 holds {TARSKIK1 x} \\/XBOOLE-0K2 X c=TARSKIR1 X implies x inHIDDENR3 X"
sorry

mtheorem zfmisc_1_th_8:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds {TARSKIK1 x} \\/XBOOLE-0K2 {TARSKIK1 y} =XBOOLE-0R4 {TARSKIK1 x} implies x =HIDDENR1 y"
sorry

mtheorem zfmisc_1_th_9:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds {TARSKIK1 x} \\/XBOOLE-0K2 {TARSKIK2 x,y } =XBOOLE-0R4 {TARSKIK2 x,y }"
sorry

mlemma zfmisc_1_lm_5:
" for x be objectHIDDENM1 holds  for X be setHIDDENM2 holds {TARSKIK1 x} missesXBOOLE-0R1 X implies  not x inHIDDENR3 X"
sorry

mtheorem zfmisc_1_th_10:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds {TARSKIK1 x} missesXBOOLE-0R1 {TARSKIK1 y} implies x <>HIDDENR2 y"
   sorry

mlemma zfmisc_1_lm_6:
" for x be objectHIDDENM1 holds  for X be setHIDDENM2 holds  not x inHIDDENR3 X implies {TARSKIK1 x} missesXBOOLE-0R1 X"
sorry

mtheorem zfmisc_1_th_11:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds x <>HIDDENR2 y implies {TARSKIK1 x} missesXBOOLE-0R1 {TARSKIK1 y}"
sorry

mlemma zfmisc_1_lm_7:
" for x be objectHIDDENM1 holds  for X be setHIDDENM2 holds X /\\XBOOLE-0K3 {TARSKIK1 x} =XBOOLE-0R4 {TARSKIK1 x} implies x inHIDDENR3 X"
sorry

mtheorem zfmisc_1_th_12:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds {TARSKIK1 x} /\\XBOOLE-0K3 {TARSKIK1 y} =XBOOLE-0R4 {TARSKIK1 x} implies x =HIDDENR1 y"
sorry

mlemma zfmisc_1_lm_8:
" for x be objectHIDDENM1 holds  for X be setHIDDENM2 holds x inHIDDENR3 X implies X /\\XBOOLE-0K3 {TARSKIK1 x} =XBOOLE-0R4 {TARSKIK1 x}"
  using zfmisc_1_lm_1 xboole_1_th_28 sorry

mtheorem zfmisc_1_th_13:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds {TARSKIK1 x} /\\XBOOLE-0K3 {TARSKIK2 x,y } =XBOOLE-0R4 {TARSKIK1 x}"
sorry

mlemma zfmisc_1_lm_9:
" for x be objectHIDDENM1 holds  for X be setHIDDENM2 holds {TARSKIK1 x} \\XBOOLE-0K4 X =XBOOLE-0R4 {TARSKIK1 x} iff  not x inHIDDENR3 X"
  using zfmisc_1_lm_5 zfmisc_1_lm_6 xboole_1_th_83 sorry

mtheorem zfmisc_1_th_14:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds {TARSKIK1 x} \\XBOOLE-0K4 {TARSKIK1 y} =XBOOLE-0R4 {TARSKIK1 x} iff x <>HIDDENR2 y"
sorry

mlemma zfmisc_1_lm_10:
" for x be objectHIDDENM1 holds  for X be setHIDDENM2 holds {TARSKIK1 x} \\XBOOLE-0K4 X =XBOOLE-0R4 {}XBOOLE-0K1 iff x inHIDDENR3 X"
  using zfmisc_1_lm_1 xboole_1_th_37 sorry

mtheorem zfmisc_1_th_15:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds {TARSKIK1 x} \\XBOOLE-0K4 {TARSKIK1 y} =XBOOLE-0R4 {}XBOOLE-0K1 implies x =HIDDENR1 y"
sorry

mtheorem zfmisc_1_th_16:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds {TARSKIK1 x} \\XBOOLE-0K4 {TARSKIK2 x,y } =XBOOLE-0R4 {}XBOOLE-0K1"
sorry

mlemma zfmisc_1_lm_11:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for X be setHIDDENM2 holds {TARSKIK2 x,y } \\XBOOLE-0K4 X =XBOOLE-0R4 {TARSKIK1 x} iff  not x inHIDDENR3 X & (y inHIDDENR3 X or x =HIDDENR1 y)"
sorry

mtheorem zfmisc_1_th_17:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds x <>HIDDENR2 y implies {TARSKIK2 x,y } \\XBOOLE-0K4 {TARSKIK1 y} =XBOOLE-0R4 {TARSKIK1 x}"
sorry

mtheorem zfmisc_1_th_18:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds {TARSKIK1 x} c=TARSKIR1 {TARSKIK1 y} implies x =HIDDENR1 y"
  using zfmisc_1_th_3 sorry

mtheorem zfmisc_1_th_19:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for z be objectHIDDENM1 holds {TARSKIK1 z} c=TARSKIR1 {TARSKIK2 x,y } implies z =HIDDENR1 x or z =HIDDENR1 y"
sorry

mtheorem zfmisc_1_th_20:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for z be objectHIDDENM1 holds {TARSKIK2 x,y } c=TARSKIR1 {TARSKIK1 z} implies x =HIDDENR1 z"
sorry

mtheorem zfmisc_1_th_21:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for z be objectHIDDENM1 holds {TARSKIK2 x,y } c=TARSKIR1 {TARSKIK1 z} implies {TARSKIK2 x,y } =XBOOLE-0R4 {TARSKIK1 z}"
sorry

mlemma zfmisc_1_lm_12:
" for x be objectHIDDENM1 holds  for X be setHIDDENM2 holds X <>HIDDENR2 {TARSKIK1 x} & X <>HIDDENR2 {}XBOOLE-0K1 implies ( ex y be objectHIDDENM1 st y inHIDDENR3 X & y <>HIDDENR2 x)"
sorry

mlemma zfmisc_1_lm_13:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for Z be setHIDDENM2 holds Z c=TARSKIR1 {TARSKIK2 x1,x2 } iff ((Z =XBOOLE-0R4 {}XBOOLE-0K1 or Z =XBOOLE-0R4 {TARSKIK1 x1}) or Z =XBOOLE-0R4 {TARSKIK1 x2}) or Z =XBOOLE-0R4 {TARSKIK2 x1,x2 }"
sorry

mtheorem zfmisc_1_th_22:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for y1 be objectHIDDENM1 holds  for y2 be objectHIDDENM1 holds {TARSKIK2 x1,x2 } c=TARSKIR1 {TARSKIK2 y1,y2 } implies x1 =HIDDENR1 y1 or x1 =HIDDENR1 y2"
sorry

mtheorem zfmisc_1_th_23:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds x <>HIDDENR2 y implies {TARSKIK1 x} \\+\\XBOOLE-0K5 {TARSKIK1 y} =XBOOLE-0R4 {TARSKIK2 x,y }"
sorry

mtheorem zfmisc_1_th_24:
" for x be objectHIDDENM1 holds boolZFMISC-1K1 {TARSKIK1 x} =XBOOLE-0R4 {TARSKIK2 {}XBOOLE-0K1,{TARSKIK1 x} }"
sorry

mlemma zfmisc_1_lm_14:
" for A be setHIDDENM2 holds  for X be setHIDDENM2 holds X inTARSKIR2 A implies X c=TARSKIR1 unionTARSKIK3 A"
  using tarski_def_4 sorry

mtheorem zfmisc_1_reduce_1:
  mlet "x be objectHIDDENM1"
"reduce unionTARSKIK3 {TARSKIK1 x} to x"
proof
(*reducibility*)
  show "unionTARSKIK3 {TARSKIK1 x} =HIDDENR1 x"
sorry
qed "sorry"

mtheorem zfmisc_1_th_25:
" for x be objectHIDDENM1 holds unionTARSKIK3 {TARSKIK1 x} =HIDDENR1 x"
   sorry

mlemma zfmisc_1_lm_15:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds unionTARSKIK3 {TARSKIK2 X,Y } =XBOOLE-0R4 X \\/XBOOLE-0K2 Y"
sorry

mtheorem zfmisc_1_th_26:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds unionTARSKIK3 {TARSKIK2 {TARSKIK1 x},{TARSKIK1 y} } =XBOOLE-0R4 {TARSKIK2 x,y }"
sorry

mlemma zfmisc_1_lm_16:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds [TARSKIK4 x,y ] inHIDDENR3 [:ZFMISC-1K2 X,Y :] iff x inHIDDENR3 X & y inHIDDENR3 Y"
sorry

(*\$CT*)
mtheorem zfmisc_1_th_28:
" for x be objectHIDDENM1 holds  for x1 be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for y1 be objectHIDDENM1 holds [TARSKIK4 x,y ] inHIDDENR3 [:ZFMISC-1K2 {TARSKIK1 x1},{TARSKIK1 y1} :] iff x =HIDDENR1 x1 & y =HIDDENR1 y1"
sorry

mtheorem zfmisc_1_th_29:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds [:ZFMISC-1K2 {TARSKIK1 x},{TARSKIK1 y} :] =XBOOLE-0R4 {TARSKIK1 [TARSKIK4 x,y ] }"
sorry

mtheorem zfmisc_1_th_30:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for z be objectHIDDENM1 holds [:ZFMISC-1K2 {TARSKIK1 x},{TARSKIK2 y,z } :] =XBOOLE-0R4 {TARSKIK2 [TARSKIK4 x,y ],[TARSKIK4 x,z ] } & [:ZFMISC-1K2 {TARSKIK2 x,y },{TARSKIK1 z} :] =XBOOLE-0R4 {TARSKIK2 [TARSKIK4 x,z ],[TARSKIK4 y,z ] }"
sorry

mtheorem zfmisc_1_th_31:
" for x be objectHIDDENM1 holds  for X be setHIDDENM2 holds {TARSKIK1 x} c=TARSKIR1 X iff x inHIDDENR3 X"
  using zfmisc_1_lm_1 sorry

mtheorem zfmisc_1_th_32:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for Z be setHIDDENM2 holds {TARSKIK2 x1,x2 } c=TARSKIR1 Z iff x1 inHIDDENR3 Z & x2 inHIDDENR3 Z"
sorry

mtheorem zfmisc_1_th_33:
" for x be objectHIDDENM1 holds  for Y be setHIDDENM2 holds Y c=TARSKIR1 {TARSKIK1 x} iff Y =XBOOLE-0R4 {}XBOOLE-0K1 or Y =XBOOLE-0R4 {TARSKIK1 x}"
  using zfmisc_1_lm_3 sorry

mtheorem zfmisc_1_th_34:
" for x be objectHIDDENM1 holds  for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds Y c=TARSKIR1 X &  not x inHIDDENR3 Y implies Y c=TARSKIR1 X \\XBOOLE-0K4 {TARSKIK1 x}"
  using zfmisc_1_lm_2 sorry

mtheorem zfmisc_1_th_35:
" for x be objectHIDDENM1 holds  for X be setHIDDENM2 holds X <>HIDDENR2 {TARSKIK1 x} & X <>HIDDENR2 {}XBOOLE-0K1 implies ( ex y be objectHIDDENM1 st y inHIDDENR3 X & y <>HIDDENR2 x)"
  using zfmisc_1_lm_12 sorry

mtheorem zfmisc_1_th_36:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for Z be setHIDDENM2 holds Z c=TARSKIR1 {TARSKIK2 x1,x2 } iff ((Z =XBOOLE-0R4 {}XBOOLE-0K1 or Z =XBOOLE-0R4 {TARSKIK1 x1}) or Z =XBOOLE-0R4 {TARSKIK1 x2}) or Z =XBOOLE-0R4 {TARSKIK2 x1,x2 }"
  using zfmisc_1_lm_13 sorry

mtheorem zfmisc_1_th_37:
" for z be objectHIDDENM1 holds  for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds {TARSKIK1 z} =XBOOLE-0R4 X \\/XBOOLE-0K2 Y implies (X =XBOOLE-0R4 {TARSKIK1 z} & Y =XBOOLE-0R4 {TARSKIK1 z} or X =XBOOLE-0R4 {}XBOOLE-0K1 & Y =XBOOLE-0R4 {TARSKIK1 z}) or X =XBOOLE-0R4 {TARSKIK1 z} & Y =XBOOLE-0R4 {}XBOOLE-0K1"
sorry

mtheorem zfmisc_1_th_38:
" for z be objectHIDDENM1 holds  for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds {TARSKIK1 z} =XBOOLE-0R4 X \\/XBOOLE-0K2 Y & X <>HIDDENR2 Y implies X =XBOOLE-0R4 {}XBOOLE-0K1 or Y =XBOOLE-0R4 {}XBOOLE-0K1"
sorry

mtheorem zfmisc_1_th_39:
" for x be objectHIDDENM1 holds  for X be setHIDDENM2 holds {TARSKIK1 x} \\/XBOOLE-0K2 X c=TARSKIR1 X implies x inHIDDENR3 X"
  using zfmisc_1_lm_4 sorry

mtheorem zfmisc_1_th_40:
" for x be objectHIDDENM1 holds  for X be setHIDDENM2 holds x inHIDDENR3 X implies {TARSKIK1 x} \\/XBOOLE-0K2 X =XBOOLE-0R4 X"
  using zfmisc_1_lm_1 xboole_1_th_12 sorry

mtheorem zfmisc_1_th_41:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for Z be setHIDDENM2 holds {TARSKIK2 x,y } \\/XBOOLE-0K2 Z c=TARSKIR1 Z implies x inHIDDENR3 Z"
sorry

mtheorem zfmisc_1_th_42:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for Z be setHIDDENM2 holds x inHIDDENR3 Z & y inHIDDENR3 Z implies {TARSKIK2 x,y } \\/XBOOLE-0K2 Z =XBOOLE-0R4 Z"
  using zfmisc_1_th_32 xboole_1_th_12 sorry

mtheorem zfmisc_1_th_43:
" for x be objectHIDDENM1 holds  for X be setHIDDENM2 holds {TARSKIK1 x} \\/XBOOLE-0K2 X <>HIDDENR2 {}XBOOLE-0K1"
   sorry

mtheorem zfmisc_1_th_44:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for X be setHIDDENM2 holds {TARSKIK2 x,y } \\/XBOOLE-0K2 X <>HIDDENR2 {}XBOOLE-0K1"
   sorry

mtheorem zfmisc_1_th_45:
" for x be objectHIDDENM1 holds  for X be setHIDDENM2 holds X /\\XBOOLE-0K3 {TARSKIK1 x} =XBOOLE-0R4 {TARSKIK1 x} implies x inHIDDENR3 X"
  using zfmisc_1_lm_7 sorry

mtheorem zfmisc_1_th_46:
" for x be objectHIDDENM1 holds  for X be setHIDDENM2 holds x inHIDDENR3 X implies X /\\XBOOLE-0K3 {TARSKIK1 x} =XBOOLE-0R4 {TARSKIK1 x}"
  using zfmisc_1_lm_1 xboole_1_th_28 sorry

mtheorem zfmisc_1_th_47:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for Z be setHIDDENM2 holds x inHIDDENR3 Z & y inHIDDENR3 Z implies {TARSKIK2 x,y } /\\XBOOLE-0K3 Z =XBOOLE-0R4 {TARSKIK2 x,y }"
  using zfmisc_1_th_32 xboole_1_th_28 sorry

mtheorem zfmisc_1_th_48:
" for x be objectHIDDENM1 holds  for X be setHIDDENM2 holds {TARSKIK1 x} missesXBOOLE-0R1 X implies  not x inHIDDENR3 X"
  using zfmisc_1_lm_5 sorry

mtheorem zfmisc_1_th_49:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for Z be setHIDDENM2 holds {TARSKIK2 x,y } missesXBOOLE-0R1 Z implies  not x inHIDDENR3 Z"
sorry

mtheorem zfmisc_1_th_50:
" for x be objectHIDDENM1 holds  for X be setHIDDENM2 holds  not x inHIDDENR3 X implies {TARSKIK1 x} missesXBOOLE-0R1 X"
  using zfmisc_1_lm_6 sorry

mtheorem zfmisc_1_th_51:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for Z be setHIDDENM2 holds  not x inHIDDENR3 Z &  not y inHIDDENR3 Z implies {TARSKIK2 x,y } missesXBOOLE-0R1 Z"
sorry

mtheorem zfmisc_1_th_52:
" for x be objectHIDDENM1 holds  for X be setHIDDENM2 holds {TARSKIK1 x} missesXBOOLE-0R1 X or {TARSKIK1 x} /\\XBOOLE-0K3 X =XBOOLE-0R4 {TARSKIK1 x}"
  using zfmisc_1_lm_6 zfmisc_1_lm_8 sorry

mtheorem zfmisc_1_th_53:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for X be setHIDDENM2 holds {TARSKIK2 x,y } /\\XBOOLE-0K3 X =XBOOLE-0R4 {TARSKIK1 x} implies  not y inHIDDENR3 X or x =HIDDENR1 y"
sorry

mtheorem zfmisc_1_th_54:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for X be setHIDDENM2 holds x inHIDDENR3 X & ( not y inHIDDENR3 X or x =HIDDENR1 y) implies {TARSKIK2 x,y } /\\XBOOLE-0K3 X =XBOOLE-0R4 {TARSKIK1 x}"
sorry

mtheorem zfmisc_1_th_55:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for X be setHIDDENM2 holds {TARSKIK2 x,y } /\\XBOOLE-0K3 X =XBOOLE-0R4 {TARSKIK2 x,y } implies x inHIDDENR3 X"
sorry

mtheorem zfmisc_1_th_56:
" for x be objectHIDDENM1 holds  for z be objectHIDDENM1 holds  for X be setHIDDENM2 holds z inHIDDENR3 X \\XBOOLE-0K4 {TARSKIK1 x} iff z inHIDDENR3 X & z <>HIDDENR2 x"
sorry

mtheorem zfmisc_1_th_57:
" for x be objectHIDDENM1 holds  for X be setHIDDENM2 holds X \\XBOOLE-0K4 {TARSKIK1 x} =XBOOLE-0R4 X iff  not x inHIDDENR3 X"
sorry

mtheorem zfmisc_1_th_58:
" for x be objectHIDDENM1 holds  for X be setHIDDENM2 holds X \\XBOOLE-0K4 {TARSKIK1 x} =XBOOLE-0R4 {}XBOOLE-0K1 implies X =XBOOLE-0R4 {}XBOOLE-0K1 or X =XBOOLE-0R4 {TARSKIK1 x}"
sorry

mtheorem zfmisc_1_th_59:
" for x be objectHIDDENM1 holds  for X be setHIDDENM2 holds {TARSKIK1 x} \\XBOOLE-0K4 X =XBOOLE-0R4 {TARSKIK1 x} iff  not x inHIDDENR3 X"
  using zfmisc_1_lm_5 zfmisc_1_lm_6 xboole_1_th_83 sorry

mtheorem zfmisc_1_th_60:
" for x be objectHIDDENM1 holds  for X be setHIDDENM2 holds {TARSKIK1 x} \\XBOOLE-0K4 X =XBOOLE-0R4 {}XBOOLE-0K1 iff x inHIDDENR3 X"
  using zfmisc_1_lm_1 xboole_1_th_37 sorry

mtheorem zfmisc_1_th_61:
" for x be objectHIDDENM1 holds  for X be setHIDDENM2 holds {TARSKIK1 x} \\XBOOLE-0K4 X =XBOOLE-0R4 {}XBOOLE-0K1 or {TARSKIK1 x} \\XBOOLE-0K4 X =XBOOLE-0R4 {TARSKIK1 x}"
  using zfmisc_1_lm_9 zfmisc_1_lm_10 sorry

mtheorem zfmisc_1_th_62:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for X be setHIDDENM2 holds {TARSKIK2 x,y } \\XBOOLE-0K4 X =XBOOLE-0R4 {TARSKIK1 x} iff  not x inHIDDENR3 X & (y inHIDDENR3 X or x =HIDDENR1 y)"
  using zfmisc_1_lm_11 sorry

mtheorem zfmisc_1_th_63:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for X be setHIDDENM2 holds {TARSKIK2 x,y } \\XBOOLE-0K4 X =XBOOLE-0R4 {TARSKIK2 x,y } iff  not x inHIDDENR3 X &  not y inHIDDENR3 X"
  using zfmisc_1_th_49 zfmisc_1_th_51 xboole_1_th_83 sorry

mtheorem zfmisc_1_th_64:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for X be setHIDDENM2 holds {TARSKIK2 x,y } \\XBOOLE-0K4 X =XBOOLE-0R4 {}XBOOLE-0K1 iff x inHIDDENR3 X & y inHIDDENR3 X"
sorry

mtheorem zfmisc_1_th_65:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for X be setHIDDENM2 holds (({TARSKIK2 x,y } \\XBOOLE-0K4 X =XBOOLE-0R4 {}XBOOLE-0K1 or {TARSKIK2 x,y } \\XBOOLE-0K4 X =XBOOLE-0R4 {TARSKIK1 x}) or {TARSKIK2 x,y } \\XBOOLE-0K4 X =XBOOLE-0R4 {TARSKIK1 y}) or {TARSKIK2 x,y } \\XBOOLE-0K4 X =XBOOLE-0R4 {TARSKIK2 x,y }"
sorry

mtheorem zfmisc_1_th_66:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for X be setHIDDENM2 holds X \\XBOOLE-0K4 {TARSKIK2 x,y } =XBOOLE-0R4 {}XBOOLE-0K1 iff ((X =XBOOLE-0R4 {}XBOOLE-0K1 or X =XBOOLE-0R4 {TARSKIK1 x}) or X =XBOOLE-0R4 {TARSKIK1 y}) or X =XBOOLE-0R4 {TARSKIK2 x,y }"
sorry

mtheorem zfmisc_1_th_67:
" for A be setHIDDENM2 holds  for B be setHIDDENM2 holds A c=TARSKIR1 B implies boolZFMISC-1K1 A c=TARSKIR1 boolZFMISC-1K1 B"
sorry

mtheorem zfmisc_1_th_68:
" for A be setHIDDENM2 holds {TARSKIK1 A} c=TARSKIR1 boolZFMISC-1K1 A"
sorry

mtheorem zfmisc_1_th_69:
" for A be setHIDDENM2 holds  for B be setHIDDENM2 holds boolZFMISC-1K1 A \\/XBOOLE-0K2 boolZFMISC-1K1 B c=TARSKIR1 boolZFMISC-1K1 (A \\/XBOOLE-0K2 B)"
sorry

mtheorem zfmisc_1_th_70:
" for A be setHIDDENM2 holds  for B be setHIDDENM2 holds boolZFMISC-1K1 A \\/XBOOLE-0K2 boolZFMISC-1K1 B =XBOOLE-0R4 boolZFMISC-1K1 (A \\/XBOOLE-0K2 B) implies (A,B)are-c=-comparableXBOOLE-0R3"
sorry

mtheorem zfmisc_1_th_71:
" for A be setHIDDENM2 holds  for B be setHIDDENM2 holds boolZFMISC-1K1 (A /\\XBOOLE-0K3 B) =XBOOLE-0R4 boolZFMISC-1K1 A /\\XBOOLE-0K3 boolZFMISC-1K1 B"
sorry

mtheorem zfmisc_1_th_72:
" for A be setHIDDENM2 holds  for B be setHIDDENM2 holds boolZFMISC-1K1 (A \\XBOOLE-0K4 B) c=TARSKIR1 {TARSKIK1 {}XBOOLE-0K1 } \\/XBOOLE-0K2 (boolZFMISC-1K1 A \\XBOOLE-0K4 boolZFMISC-1K1 B)"
sorry

mtheorem zfmisc_1_th_73:
" for A be setHIDDENM2 holds  for B be setHIDDENM2 holds boolZFMISC-1K1 (A \\XBOOLE-0K4 B) \\/XBOOLE-0K2 boolZFMISC-1K1 (B \\XBOOLE-0K4 A) c=TARSKIR1 boolZFMISC-1K1 (A \\+\\XBOOLE-0K5 B)"
sorry

mtheorem zfmisc_1_th_74:
" for A be setHIDDENM2 holds  for X be setHIDDENM2 holds X inTARSKIR2 A implies X c=TARSKIR1 unionTARSKIK3 A"
  using zfmisc_1_lm_14 sorry

mtheorem zfmisc_1_th_75:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds unionTARSKIK3 {TARSKIK2 X,Y } =XBOOLE-0R4 X \\/XBOOLE-0K2 Y"
  using zfmisc_1_lm_15 sorry

mtheorem zfmisc_1_th_76:
" for A be setHIDDENM2 holds  for Z be setHIDDENM2 holds ( for X be setHIDDENM2 holds X inTARSKIR2 A implies X c=TARSKIR1 Z) implies unionTARSKIK3 A c=TARSKIR1 Z"
sorry

mtheorem zfmisc_1_th_77:
" for A be setHIDDENM2 holds  for B be setHIDDENM2 holds A c=TARSKIR1 B implies unionTARSKIK3 A c=TARSKIR1 unionTARSKIK3 B"
sorry

mtheorem zfmisc_1_th_78:
" for A be setHIDDENM2 holds  for B be setHIDDENM2 holds unionTARSKIK3 (A \\/XBOOLE-0K2 B) =XBOOLE-0R4 unionTARSKIK3 A \\/XBOOLE-0K2 unionTARSKIK3 B"
sorry

mtheorem zfmisc_1_th_79:
" for A be setHIDDENM2 holds  for B be setHIDDENM2 holds unionTARSKIK3 (A /\\XBOOLE-0K3 B) c=TARSKIR1 unionTARSKIK3 A /\\XBOOLE-0K3 unionTARSKIK3 B"
sorry

mtheorem zfmisc_1_th_80:
" for A be setHIDDENM2 holds  for B be setHIDDENM2 holds ( for X be setHIDDENM2 holds X inTARSKIR2 A implies X missesXBOOLE-0R1 B) implies unionTARSKIK3 A missesXBOOLE-0R1 B"
sorry

mtheorem zfmisc_1_th_81:
" for A be setHIDDENM2 holds unionTARSKIK3 (boolZFMISC-1K1 A) =XBOOLE-0R4 A"
sorry

mtheorem zfmisc_1_th_82:
" for A be setHIDDENM2 holds A c=TARSKIR1 boolZFMISC-1K1 (unionTARSKIK3 A)"
sorry

mtheorem zfmisc_1_th_83:
" for A be setHIDDENM2 holds  for B be setHIDDENM2 holds ( for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds (X <>HIDDENR2 Y & X inTARSKIR2 A \\/XBOOLE-0K2 B) & Y inTARSKIR2 A \\/XBOOLE-0K2 B implies X missesXBOOLE-0R1 Y) implies unionTARSKIK3 (A /\\XBOOLE-0K3 B) =XBOOLE-0R4 unionTARSKIK3 A /\\XBOOLE-0K3 unionTARSKIK3 B"
sorry

mtheorem zfmisc_1_th_84:
" for z be objectHIDDENM1 holds  for A be setHIDDENM2 holds  for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds A c=TARSKIR1 [:ZFMISC-1K2 X,Y :] & z inHIDDENR3 A implies ( ex x be objectHIDDENM1 st  ex y be objectHIDDENM1 st (x inHIDDENR3 X & y inHIDDENR3 Y) & z =HIDDENR1 [TARSKIK4 x,y ])"
sorry

mtheorem zfmisc_1_th_85:
" for z be objectHIDDENM1 holds  for X1 be setHIDDENM2 holds  for X2 be setHIDDENM2 holds  for Y1 be setHIDDENM2 holds  for Y2 be setHIDDENM2 holds z inHIDDENR3 ([:ZFMISC-1K2 X1,Y1 :])/\\XBOOLE-0K3 ([:ZFMISC-1K2 X2,Y2 :]) implies ( ex x be objectHIDDENM1 st  ex y be objectHIDDENM1 st (z =HIDDENR1 [TARSKIK4 x,y ] & x inHIDDENR3 X1 /\\XBOOLE-0K3 X2) & y inHIDDENR3 Y1 /\\XBOOLE-0K3 Y2)"
sorry

mtheorem zfmisc_1_th_86:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds [:ZFMISC-1K2 X,Y :] c=TARSKIR1 boolZFMISC-1K1 (boolZFMISC-1K1 (X \\/XBOOLE-0K2 Y))"
sorry

mtheorem zfmisc_1_th_87:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds [TARSKIK4 x,y ] inHIDDENR3 [:ZFMISC-1K2 X,Y :] iff x inHIDDENR3 X & y inHIDDENR3 Y"
  using zfmisc_1_lm_16 sorry

mtheorem zfmisc_1_th_88:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds [TARSKIK4 x,y ] inHIDDENR3 [:ZFMISC-1K2 X,Y :] implies [TARSKIK4 y,x ] inHIDDENR3 [:ZFMISC-1K2 Y,X :]"
sorry

mtheorem zfmisc_1_th_89:
" for X1 be setHIDDENM2 holds  for X2 be setHIDDENM2 holds  for Y1 be setHIDDENM2 holds  for Y2 be setHIDDENM2 holds ( for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds [TARSKIK4 x,y ] inHIDDENR3 [:ZFMISC-1K2 X1,Y1 :] iff [TARSKIK4 x,y ] inHIDDENR3 [:ZFMISC-1K2 X2,Y2 :]) implies [:ZFMISC-1K2 X1,Y1 :] =XBOOLE-0R4 [:ZFMISC-1K2 X2,Y2 :]"
sorry

mlemma zfmisc_1_lm_17:
" for A be setHIDDENM2 holds  for B be setHIDDENM2 holds  for X1 be setHIDDENM2 holds  for X2 be setHIDDENM2 holds  for Y1 be setHIDDENM2 holds  for Y2 be setHIDDENM2 holds (A c=TARSKIR1 [:ZFMISC-1K2 X1,Y1 :] & B c=TARSKIR1 [:ZFMISC-1K2 X2,Y2 :]) & ( for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds [TARSKIK4 x,y ] inHIDDENR3 A iff [TARSKIK4 x,y ] inHIDDENR3 B) implies A =XBOOLE-0R4 B"
sorry

mlemma zfmisc_1_lm_18:
" for A be setHIDDENM2 holds  for B be setHIDDENM2 holds (( for z be objectHIDDENM1 holds z inHIDDENR3 A implies ( ex x be objectHIDDENM1 st  ex y be objectHIDDENM1 st z =HIDDENR1 [TARSKIK4 x,y ])) & ( for z be objectHIDDENM1 holds z inHIDDENR3 B implies ( ex x be objectHIDDENM1 st  ex y be objectHIDDENM1 st z =HIDDENR1 [TARSKIK4 x,y ]))) & ( for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds [TARSKIK4 x,y ] inHIDDENR3 A iff [TARSKIK4 x,y ] inHIDDENR3 B) implies A =XBOOLE-0R4 B"
sorry

mtheorem zfmisc_1_th_90:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds [:ZFMISC-1K2 X,Y :] =XBOOLE-0R4 {}XBOOLE-0K1 iff X =XBOOLE-0R4 {}XBOOLE-0K1 or Y =XBOOLE-0R4 {}XBOOLE-0K1"
sorry

mtheorem zfmisc_1_th_91:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds (X <>HIDDENR2 {}XBOOLE-0K1 & Y <>HIDDENR2 {}XBOOLE-0K1) & [:ZFMISC-1K2 X,Y :] =XBOOLE-0R4 [:ZFMISC-1K2 Y,X :] implies X =XBOOLE-0R4 Y"
sorry

mtheorem zfmisc_1_th_92:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds [:ZFMISC-1K2 X,X :] =XBOOLE-0R4 [:ZFMISC-1K2 Y,Y :] implies X =XBOOLE-0R4 Y"
sorry

mlemma zfmisc_1_lm_19:
" for z be objectHIDDENM1 holds  for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds z inHIDDENR3 [:ZFMISC-1K2 X,Y :] implies ( ex x be objectHIDDENM1 st  ex y be objectHIDDENM1 st [TARSKIK4 x,y ] =HIDDENR1 z)"
sorry

mtheorem zfmisc_1_th_93:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X c=TARSKIR1 [:ZFMISC-1K2 X,Y :] implies X =XBOOLE-0R4 {}XBOOLE-0K1"
sorry

mtheorem zfmisc_1_th_94:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds Z <>HIDDENR2 {}XBOOLE-0K1 & ([:ZFMISC-1K2 X,Z :] c=TARSKIR1 [:ZFMISC-1K2 Y,Z :] or [:ZFMISC-1K2 Z,X :] c=TARSKIR1 [:ZFMISC-1K2 Z,Y :]) implies X c=TARSKIR1 Y"
sorry

mtheorem zfmisc_1_th_95:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds X c=TARSKIR1 Y implies [:ZFMISC-1K2 X,Z :] c=TARSKIR1 [:ZFMISC-1K2 Y,Z :] & [:ZFMISC-1K2 Z,X :] c=TARSKIR1 [:ZFMISC-1K2 Z,Y :]"
sorry

mtheorem zfmisc_1_th_96:
" for X1 be setHIDDENM2 holds  for X2 be setHIDDENM2 holds  for Y1 be setHIDDENM2 holds  for Y2 be setHIDDENM2 holds X1 c=TARSKIR1 Y1 & X2 c=TARSKIR1 Y2 implies [:ZFMISC-1K2 X1,X2 :] c=TARSKIR1 [:ZFMISC-1K2 Y1,Y2 :]"
sorry

mtheorem zfmisc_1_th_97:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds [:ZFMISC-1K2 X \\/XBOOLE-0K2 Y,Z :] =XBOOLE-0R4 [:ZFMISC-1K2 X,Z :] \\/XBOOLE-0K2 [:ZFMISC-1K2 Y,Z :] & [:ZFMISC-1K2 Z,X \\/XBOOLE-0K2 Y :] =XBOOLE-0R4 [:ZFMISC-1K2 Z,X :] \\/XBOOLE-0K2 [:ZFMISC-1K2 Z,Y :]"
sorry

mtheorem zfmisc_1_th_98:
" for X1 be setHIDDENM2 holds  for X2 be setHIDDENM2 holds  for Y1 be setHIDDENM2 holds  for Y2 be setHIDDENM2 holds [:ZFMISC-1K2 X1 \\/XBOOLE-0K2 X2,Y1 \\/XBOOLE-0K2 Y2 :] =XBOOLE-0R4 (([:ZFMISC-1K2 X1,Y1 :] \\/XBOOLE-0K2 [:ZFMISC-1K2 X1,Y2 :])\\/XBOOLE-0K2 [:ZFMISC-1K2 X2,Y1 :])\\/XBOOLE-0K2 [:ZFMISC-1K2 X2,Y2 :]"
sorry

mtheorem zfmisc_1_th_99:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds [:ZFMISC-1K2 X /\\XBOOLE-0K3 Y,Z :] =XBOOLE-0R4 ([:ZFMISC-1K2 X,Z :])/\\XBOOLE-0K3 ([:ZFMISC-1K2 Y,Z :]) & [:ZFMISC-1K2 Z,X /\\XBOOLE-0K3 Y :] =XBOOLE-0R4 ([:ZFMISC-1K2 Z,X :])/\\XBOOLE-0K3 ([:ZFMISC-1K2 Z,Y :])"
sorry

mtheorem zfmisc_1_th_100:
" for X1 be setHIDDENM2 holds  for X2 be setHIDDENM2 holds  for Y1 be setHIDDENM2 holds  for Y2 be setHIDDENM2 holds [:ZFMISC-1K2 X1 /\\XBOOLE-0K3 X2,Y1 /\\XBOOLE-0K3 Y2 :] =XBOOLE-0R4 ([:ZFMISC-1K2 X1,Y1 :])/\\XBOOLE-0K3 ([:ZFMISC-1K2 X2,Y2 :])"
sorry

mtheorem zfmisc_1_th_101:
" for A be setHIDDENM2 holds  for B be setHIDDENM2 holds  for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds A c=TARSKIR1 X & B c=TARSKIR1 Y implies ([:ZFMISC-1K2 A,Y :])/\\XBOOLE-0K3 ([:ZFMISC-1K2 X,B :]) =XBOOLE-0R4 [:ZFMISC-1K2 A,B :]"
sorry

mtheorem zfmisc_1_th_102:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds [:ZFMISC-1K2 X \\XBOOLE-0K4 Y,Z :] =XBOOLE-0R4 [:ZFMISC-1K2 X,Z :] \\XBOOLE-0K4 [:ZFMISC-1K2 Y,Z :] & [:ZFMISC-1K2 Z,X \\XBOOLE-0K4 Y :] =XBOOLE-0R4 [:ZFMISC-1K2 Z,X :] \\XBOOLE-0K4 [:ZFMISC-1K2 Z,Y :]"
sorry

mtheorem zfmisc_1_th_103:
" for X1 be setHIDDENM2 holds  for X2 be setHIDDENM2 holds  for Y1 be setHIDDENM2 holds  for Y2 be setHIDDENM2 holds [:ZFMISC-1K2 X1,X2 :] \\XBOOLE-0K4 [:ZFMISC-1K2 Y1,Y2 :] =XBOOLE-0R4 [:ZFMISC-1K2 X1 \\XBOOLE-0K4 Y1,X2 :] \\/XBOOLE-0K2 [:ZFMISC-1K2 X1,X2 \\XBOOLE-0K4 Y2 :]"
sorry

mtheorem zfmisc_1_th_104:
" for X1 be setHIDDENM2 holds  for X2 be setHIDDENM2 holds  for Y1 be setHIDDENM2 holds  for Y2 be setHIDDENM2 holds X1 missesXBOOLE-0R1 X2 or Y1 missesXBOOLE-0R1 Y2 implies [:ZFMISC-1K2 X1,Y1 :] missesXBOOLE-0R1 [:ZFMISC-1K2 X2,Y2 :]"
sorry

mtheorem zfmisc_1_th_105:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for z be objectHIDDENM1 holds  for Y be setHIDDENM2 holds [TARSKIK4 x,y ] inHIDDENR3 [:ZFMISC-1K2 {TARSKIK1 z},Y :] iff x =HIDDENR1 z & y inHIDDENR3 Y"
sorry

mtheorem zfmisc_1_th_106:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for z be objectHIDDENM1 holds  for X be setHIDDENM2 holds [TARSKIK4 x,y ] inHIDDENR3 [:ZFMISC-1K2 X,{TARSKIK1 z} :] iff x inHIDDENR3 X & y =HIDDENR1 z"
sorry

mtheorem zfmisc_1_th_107:
" for x be objectHIDDENM1 holds  for X be setHIDDENM2 holds X <>HIDDENR2 {}XBOOLE-0K1 implies [:ZFMISC-1K2 {TARSKIK1 x},X :] <>HIDDENR2 {}XBOOLE-0K1 & [:ZFMISC-1K2 X,{TARSKIK1 x} :] <>HIDDENR2 {}XBOOLE-0K1"
  using zfmisc_1_th_90 sorry

mtheorem zfmisc_1_th_108:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds x <>HIDDENR2 y implies [:ZFMISC-1K2 {TARSKIK1 x},X :] missesXBOOLE-0R1 [:ZFMISC-1K2 {TARSKIK1 y},Y :] & [:ZFMISC-1K2 X,{TARSKIK1 x} :] missesXBOOLE-0R1 [:ZFMISC-1K2 Y,{TARSKIK1 y} :]"
sorry

mtheorem zfmisc_1_th_109:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for X be setHIDDENM2 holds [:ZFMISC-1K2 {TARSKIK2 x,y },X :] =XBOOLE-0R4 [:ZFMISC-1K2 {TARSKIK1 x},X :] \\/XBOOLE-0K2 [:ZFMISC-1K2 {TARSKIK1 y},X :] & [:ZFMISC-1K2 X,{TARSKIK2 x,y } :] =XBOOLE-0R4 [:ZFMISC-1K2 X,{TARSKIK1 x} :] \\/XBOOLE-0K2 [:ZFMISC-1K2 X,{TARSKIK1 y} :]"
sorry

mtheorem zfmisc_1_th_110:
" for X1 be setHIDDENM2 holds  for X2 be setHIDDENM2 holds  for Y1 be setHIDDENM2 holds  for Y2 be setHIDDENM2 holds (X1 <>HIDDENR2 {}XBOOLE-0K1 & Y1 <>HIDDENR2 {}XBOOLE-0K1) & [:ZFMISC-1K2 X1,Y1 :] =XBOOLE-0R4 [:ZFMISC-1K2 X2,Y2 :] implies X1 =XBOOLE-0R4 X2 & Y1 =XBOOLE-0R4 Y2"
sorry

mtheorem zfmisc_1_th_111:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X c=TARSKIR1 [:ZFMISC-1K2 X,Y :] or X c=TARSKIR1 [:ZFMISC-1K2 Y,X :] implies X =XBOOLE-0R4 {}XBOOLE-0K1"
sorry

mtheorem zfmisc_1_th_112:
" for N be setHIDDENM2 holds  ex M be setHIDDENM2 st ((N inTARSKIR2 M & ( for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X inTARSKIR2 M & Y c=TARSKIR1 X implies Y inTARSKIR2 M)) & ( for X be setHIDDENM2 holds X inTARSKIR2 M implies boolZFMISC-1K1 X inTARSKIR2 M)) & ( for X be setHIDDENM2 holds X c=TARSKIR1 M implies (X,M)are-equipotentTARSKIR3 or X inTARSKIR2 M)"
sorry

reserve e for "objectHIDDENM1"
reserve X, X1, X2, Y1, Y2 for "setHIDDENM2"
mtheorem zfmisc_1_th_113:
" for e be objectHIDDENM1 holds  for X1 be setHIDDENM2 holds  for X2 be setHIDDENM2 holds  for Y1 be setHIDDENM2 holds  for Y2 be setHIDDENM2 holds e inHIDDENR3 [:ZFMISC-1K2 X1,Y1 :] & e inHIDDENR3 [:ZFMISC-1K2 X2,Y2 :] implies e inHIDDENR3 [:ZFMISC-1K2 X1 /\\XBOOLE-0K3 X2,Y1 /\\XBOOLE-0K3 Y2 :]"
sorry

(*begin*)
mtheorem zfmisc_1_th_114:
" for X1 be setHIDDENM2 holds  for X2 be setHIDDENM2 holds  for Y1 be setHIDDENM2 holds  for Y2 be setHIDDENM2 holds [:ZFMISC-1K2 X1,X2 :] c=TARSKIR1 [:ZFMISC-1K2 Y1,Y2 :] & [:ZFMISC-1K2 X1,X2 :] <>HIDDENR2 {}XBOOLE-0K1 implies X1 c=TARSKIR1 Y1 & X2 c=TARSKIR1 Y2"
sorry

mtheorem zfmisc_1_th_115:
" for A be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for B be setHIDDENM2 holds  for C be setHIDDENM2 holds  for D be setHIDDENM2 holds [:ZFMISC-1K2 A,B :] c=TARSKIR1 [:ZFMISC-1K2 C,D :] or [:ZFMISC-1K2 B,A :] c=TARSKIR1 [:ZFMISC-1K2 D,C :] implies B c=TARSKIR1 D"
sorry

mtheorem zfmisc_1_th_116:
" for x be objectHIDDENM1 holds  for X be setHIDDENM2 holds x inHIDDENR3 X implies (X \\XBOOLE-0K4 {TARSKIK1 x})\\/XBOOLE-0K2 {TARSKIK1 x} =XBOOLE-0R4 X"
sorry

mtheorem zfmisc_1_th_117:
" for x be objectHIDDENM1 holds  for X be setHIDDENM2 holds  not x inHIDDENR3 X implies (X \\/XBOOLE-0K2 {TARSKIK1 x})\\XBOOLE-0K4 {TARSKIK1 x} =XBOOLE-0R4 X"
sorry

mtheorem zfmisc_1_th_118:
" for x be setHIDDENM2 holds  for y be setHIDDENM2 holds  for z be setHIDDENM2 holds  for Z be setHIDDENM2 holds Z c=TARSKIR1 {ENUMSET1K1 x,y,z } iff ((((((Z =XBOOLE-0R4 {}XBOOLE-0K1 or Z =XBOOLE-0R4 {TARSKIK1 x}) or Z =XBOOLE-0R4 {TARSKIK1 y}) or Z =XBOOLE-0R4 {TARSKIK1 z}) or Z =XBOOLE-0R4 {TARSKIK2 x,y }) or Z =XBOOLE-0R4 {TARSKIK2 y,z }) or Z =XBOOLE-0R4 {TARSKIK2 x,z }) or Z =XBOOLE-0R4 {ENUMSET1K1 x,y,z }"
sorry

mtheorem zfmisc_1_th_119:
" for N be setHIDDENM2 holds  for M be setHIDDENM2 holds  for X1 be setHIDDENM2 holds  for X2 be setHIDDENM2 holds  for Y1 be setHIDDENM2 holds  for Y2 be setHIDDENM2 holds N c=TARSKIR1 [:ZFMISC-1K2 X1,Y1 :] & M c=TARSKIR1 [:ZFMISC-1K2 X2,Y2 :] implies N \\/XBOOLE-0K2 M c=TARSKIR1 [:ZFMISC-1K2 X1 \\/XBOOLE-0K2 X2,Y1 \\/XBOOLE-0K2 Y2 :]"
sorry

mlemma zfmisc_1_lm_20:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for X be setHIDDENM2 holds  not x inHIDDENR3 X &  not y inHIDDENR3 X implies {TARSKIK2 x,y } missesXBOOLE-0R1 X"
sorry

mtheorem zfmisc_1_th_120:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for X be setHIDDENM2 holds  not x inHIDDENR3 X &  not y inHIDDENR3 X implies X =XBOOLE-0R4 X \\XBOOLE-0K4 {TARSKIK2 x,y }"
sorry

mtheorem zfmisc_1_th_121:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for X be setHIDDENM2 holds  not x inHIDDENR3 X &  not y inHIDDENR3 X implies X =XBOOLE-0R4 (X \\/XBOOLE-0K2 {TARSKIK2 x,y })\\XBOOLE-0K4 {TARSKIK2 x,y }"
sorry

mdef zfmisc_1_def_5 ("'( _ , _ , _ ')are-mutually-distinctZFMISC-1R1" [0,0,0]50 ) where
  mlet "x1 be objectHIDDENM1", "x2 be objectHIDDENM1", "x3 be objectHIDDENM1"
"pred (x1,x2,x3)are-mutually-distinctZFMISC-1R1 means
  (x1 <>HIDDENR2 x2 & x1 <>HIDDENR2 x3) & x2 <>HIDDENR2 x3"..

mdef zfmisc_1_def_6 ("'( _ , _ , _ , _ ')are-mutually-distinctZFMISC-1R2" [0,0,0,0]50 ) where
  mlet "x1 be objectHIDDENM1", "x2 be objectHIDDENM1", "x3 be objectHIDDENM1", "x4 be objectHIDDENM1"
"pred (x1,x2,x3,x4)are-mutually-distinctZFMISC-1R2 means
  ((((x1 <>HIDDENR2 x2 & x1 <>HIDDENR2 x3) & x1 <>HIDDENR2 x4) & x2 <>HIDDENR2 x3) & x2 <>HIDDENR2 x4) & x3 <>HIDDENR2 x4"..

mdef zfmisc_1_def_7 ("'( _ , _ , _ , _ , _ ')are-mutually-distinctZFMISC-1R3" [0,0,0,0,0]50 ) where
  mlet "x1 be objectHIDDENM1", "x2 be objectHIDDENM1", "x3 be objectHIDDENM1", "x4 be objectHIDDENM1", "x5 be objectHIDDENM1"
"pred (x1,x2,x3,x4,x5)are-mutually-distinctZFMISC-1R3 means
  ((((((((x1 <>HIDDENR2 x2 & x1 <>HIDDENR2 x3) & x1 <>HIDDENR2 x4) & x1 <>HIDDENR2 x5) & x2 <>HIDDENR2 x3) & x2 <>HIDDENR2 x4) & x2 <>HIDDENR2 x5) & x3 <>HIDDENR2 x4) & x3 <>HIDDENR2 x5) & x4 <>HIDDENR2 x5"..

mdef zfmisc_1_def_8 ("'( _ , _ , _ , _ , _ , _ ')are-mutually-distinctZFMISC-1R4" [0,0,0,0,0,0]50 ) where
  mlet "x1 be objectHIDDENM1", "x2 be objectHIDDENM1", "x3 be objectHIDDENM1", "x4 be objectHIDDENM1", "x5 be objectHIDDENM1", "x6 be objectHIDDENM1"
"pred (x1,x2,x3,x4,x5,x6)are-mutually-distinctZFMISC-1R4 means
  (((((((((((((x1 <>HIDDENR2 x2 & x1 <>HIDDENR2 x3) & x1 <>HIDDENR2 x4) & x1 <>HIDDENR2 x5) & x1 <>HIDDENR2 x6) & x2 <>HIDDENR2 x3) & x2 <>HIDDENR2 x4) & x2 <>HIDDENR2 x5) & x2 <>HIDDENR2 x6) & x3 <>HIDDENR2 x4) & x3 <>HIDDENR2 x5) & x3 <>HIDDENR2 x6) & x4 <>HIDDENR2 x5) & x4 <>HIDDENR2 x6) & x5 <>HIDDENR2 x6"..

mdef zfmisc_1_def_9 ("'( _ , _ , _ , _ , _ , _ , _ ')are-mutually-distinctZFMISC-1R5" [0,0,0,0,0,0,0]50 ) where
  mlet "x1 be objectHIDDENM1", "x2 be objectHIDDENM1", "x3 be objectHIDDENM1", "x4 be objectHIDDENM1", "x5 be objectHIDDENM1", "x6 be objectHIDDENM1", "x7 be objectHIDDENM1"
"pred (x1,x2,x3,x4,x5,x6,x7)are-mutually-distinctZFMISC-1R5 means
  (((((((((((((((((((x1 <>HIDDENR2 x2 & x1 <>HIDDENR2 x3) & x1 <>HIDDENR2 x4) & x1 <>HIDDENR2 x5) & x1 <>HIDDENR2 x6) & x1 <>HIDDENR2 x7) & x2 <>HIDDENR2 x3) & x2 <>HIDDENR2 x4) & x2 <>HIDDENR2 x5) & x2 <>HIDDENR2 x6) & x2 <>HIDDENR2 x7) & x3 <>HIDDENR2 x4) & x3 <>HIDDENR2 x5) & x3 <>HIDDENR2 x6) & x3 <>HIDDENR2 x7) & x4 <>HIDDENR2 x5) & x4 <>HIDDENR2 x6) & x4 <>HIDDENR2 x7) & x5 <>HIDDENR2 x6) & x5 <>HIDDENR2 x7) & x6 <>HIDDENR2 x7"..

mtheorem zfmisc_1_th_122:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for y1 be objectHIDDENM1 holds  for y2 be objectHIDDENM1 holds [:ZFMISC-1K2 {TARSKIK2 x1,x2 },{TARSKIK2 y1,y2 } :] =XBOOLE-0R4 {ENUMSET1K2 [TARSKIK4 x1,y1 ],[TARSKIK4 x1,y2 ],[TARSKIK4 x2,y1 ],[TARSKIK4 x2,y2 ] }"
sorry

mtheorem zfmisc_1_th_123:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for A be setHIDDENM2 holds x <>HIDDENR2 y implies (A \\/XBOOLE-0K2 {TARSKIK1 x})\\XBOOLE-0K4 {TARSKIK1 y} =XBOOLE-0R4 (A \\XBOOLE-0K4 {TARSKIK1 y})\\/XBOOLE-0K2 {TARSKIK1 x}"
  using zfmisc_1_th_11 xboole_1_th_87 sorry

mdef zfmisc_1_def_10 ("trivialZFMISC-1V1" 70 ) where
"attr trivialZFMISC-1V1 for setHIDDENM2 means
  (\<lambda>X.  for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds x inHIDDENR3 X & y inHIDDENR3 X implies x =HIDDENR1 y)"..

mtheorem zfmisc_1_cl_1:
"cluster emptyXBOOLE-0V1 also-is trivialZFMISC-1V1 for setHIDDENM2"
proof
(*coherence*)
  show " for it be setHIDDENM2 holds it be emptyXBOOLE-0V1 implies it be trivialZFMISC-1V1"
     sorry
qed "sorry"

mtheorem zfmisc_1_cl_2:
"cluster  non trivialZFMISC-1V1 also-is  non emptyXBOOLE-0V1 for setHIDDENM2"
proof
(*coherence*)
  show " for it be setHIDDENM2 holds it be  non trivialZFMISC-1V1 implies it be  non emptyXBOOLE-0V1"
     sorry
qed "sorry"

mtheorem zfmisc_1_cl_3:
  mlet "x be objectHIDDENM1"
"cluster {TARSKIK1 x} as-term-is trivialZFMISC-1V1"
proof
(*coherence*)
  show "{TARSKIK1 x} be trivialZFMISC-1V1"
sorry
qed "sorry"

mtheorem zfmisc_1_cl_4:
"cluster trivialZFMISC-1V1\<bar> non emptyXBOOLE-0V1 for setHIDDENM2"
proof
(*existence*)
  show " ex it be setHIDDENM2 st it be trivialZFMISC-1V1\<bar> non emptyXBOOLE-0V1"
sorry
qed "sorry"

mtheorem zfmisc_1_th_124:
" for A be setHIDDENM2 holds  for B be setHIDDENM2 holds  for C be setHIDDENM2 holds  for p be objectHIDDENM1 holds (A c=TARSKIR1 B & B /\\XBOOLE-0K3 C =XBOOLE-0R4 {TARSKIK1 p}) & p inHIDDENR3 A implies A /\\XBOOLE-0K3 C =XBOOLE-0R4 {TARSKIK1 p}"
sorry

mtheorem zfmisc_1_th_125:
" for p be objectHIDDENM1 holds  for A be setHIDDENM2 holds  for B be setHIDDENM2 holds  for C be setHIDDENM2 holds (A /\\XBOOLE-0K3 B c=TARSKIR1 {TARSKIK1 p} & p inHIDDENR3 C) & C missesXBOOLE-0R1 B implies A \\/XBOOLE-0K2 C missesXBOOLE-0R1 B"
sorry

mtheorem zfmisc_1_th_126:
" for A be setHIDDENM2 holds  for B be setHIDDENM2 holds ( for x be setHIDDENM2 holds  for y be setHIDDENM2 holds x inTARSKIR2 A & y inTARSKIR2 B implies x missesXBOOLE-0R1 y) implies unionTARSKIK3 A missesXBOOLE-0R1 unionTARSKIK3 B"
sorry

mtheorem zfmisc_1_cl_5:
  mlet "X be setHIDDENM2", "Y be emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster [:ZFMISC-1K2 X,Y :] as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "[:ZFMISC-1K2 X,Y :] be emptyXBOOLE-0V1"
    using zfmisc_1_th_90 sorry
qed "sorry"

mtheorem zfmisc_1_cl_6:
  mlet "X be emptyXBOOLE-0V1\<bar>setHIDDENM2", "Y be setHIDDENM2"
"cluster [:ZFMISC-1K2 X,Y :] as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "[:ZFMISC-1K2 X,Y :] be emptyXBOOLE-0V1"
    using zfmisc_1_th_90 sorry
qed "sorry"

mtheorem zfmisc_1_th_127:
" for A be setHIDDENM2 holds  for B be setHIDDENM2 holds  not A inTARSKIR2 [:ZFMISC-1K2 A,B :]"
sorry

mtheorem zfmisc_1_th_128:
" for x be objectHIDDENM1 holds  for B be setHIDDENM2 holds B =HIDDENR1 [TARSKIK4 x,{TARSKIK1 x} ] implies B inTARSKIR2 [:ZFMISC-1K2 {TARSKIK1 x},B :]"
sorry

mtheorem zfmisc_1_th_129:
" for A be setHIDDENM2 holds  for B be setHIDDENM2 holds B inTARSKIR2 [:ZFMISC-1K2 A,B :] implies ( ex x be objectHIDDENM1 st x inHIDDENR3 A & B =HIDDENR1 [TARSKIK4 x,{TARSKIK1 x} ])"
sorry

mtheorem zfmisc_1_th_130:
" for A be setHIDDENM2 holds  for B be setHIDDENM2 holds B c=TARSKIR1 A & A be trivialZFMISC-1V1 implies B be trivialZFMISC-1V1"
sorry

mtheorem zfmisc_1_cl_7:
"cluster  non trivialZFMISC-1V1 for setHIDDENM2"
proof
(*existence*)
  show " ex it be setHIDDENM2 st it be  non trivialZFMISC-1V1"
sorry
qed "sorry"

mtheorem zfmisc_1_th_131:
" for X be setHIDDENM2 holds X be  non emptyXBOOLE-0V1\<bar>trivialZFMISC-1V1 implies ( ex x be objectHIDDENM1 st X =XBOOLE-0R4 {TARSKIK1 x})"
sorry

mtheorem zfmisc_1_th_132:
" for x be setHIDDENM2 holds  for X be trivialZFMISC-1V1\<bar>setHIDDENM2 holds x inTARSKIR2 X implies X =XBOOLE-0R4 {TARSKIK1 x}"
sorry

mtheorem zfmisc_1_th_133:
" for a be setHIDDENM2 holds  for b be setHIDDENM2 holds  for c be setHIDDENM2 holds  for X be setHIDDENM2 holds (a inTARSKIR2 X & b inTARSKIR2 X) & c inTARSKIR2 X implies {ENUMSET1K1 a,b,c } c=TARSKIR1 X"
sorry

mtheorem zfmisc_1_th_134:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for X be setHIDDENM2 holds [TARSKIK4 x,y ] inHIDDENR3 X implies x inHIDDENR3 unionTARSKIK3 (unionTARSKIK3 X) & y inHIDDENR3 unionTARSKIK3 (unionTARSKIK3 X)"
sorry

mtheorem zfmisc_1_th_135:
" for x be objectHIDDENM1 holds  for Y be setHIDDENM2 holds  for X be setHIDDENM2 holds X c=TARSKIR1 Y \\/XBOOLE-0K2 {TARSKIK1 x} implies x inHIDDENR3 X or X c=TARSKIR1 Y"
sorry

mtheorem zfmisc_1_th_136:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for X be setHIDDENM2 holds x inHIDDENR3 X \\/XBOOLE-0K2 {TARSKIK1 y} iff x inHIDDENR3 X or x =HIDDENR1 y"
sorry

mtheorem zfmisc_1_th_137:
" for x be objectHIDDENM1 holds  for Y be setHIDDENM2 holds  for X be setHIDDENM2 holds X \\/XBOOLE-0K2 {TARSKIK1 x} c=TARSKIR1 Y iff x inHIDDENR3 Y & X c=TARSKIR1 Y"
sorry

mtheorem zfmisc_1_th_138:
" for a be objectHIDDENM1 holds  for A be setHIDDENM2 holds  for B be setHIDDENM2 holds A c=TARSKIR1 B & B c=TARSKIR1 A \\/XBOOLE-0K2 {TARSKIK1 a} implies A \\/XBOOLE-0K2 {TARSKIK1 a} =XBOOLE-0R4 B or A =XBOOLE-0R4 B"
sorry

mtheorem zfmisc_1_cl_8:
  mlet "A be trivialZFMISC-1V1\<bar>setHIDDENM2", "B be trivialZFMISC-1V1\<bar>setHIDDENM2"
"cluster [:ZFMISC-1K2 A,B :] as-term-is trivialZFMISC-1V1"
proof
(*coherence*)
  show "[:ZFMISC-1K2 A,B :] be trivialZFMISC-1V1"
sorry
qed "sorry"

mtheorem zfmisc_1_th_139:
" for X be setHIDDENM2 holds X be  non trivialZFMISC-1V1 iff ( for x be objectHIDDENM1 holds X \\XBOOLE-0K4 {TARSKIK1 x} be  non emptyXBOOLE-0V1)"
sorry

end
