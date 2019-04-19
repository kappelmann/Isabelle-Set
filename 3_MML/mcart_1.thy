theory mcart_1
  imports funct_1 xregular
begin
(*begin*)
reserve v, x, x1, x2, x3, x4, y, y1, y2, y3, y4, z, z1, z2 for "objectHIDDENM1"
reserve X, X1, X2, X3, X4, Y, Y1, Y2, Y3, Y4, Y5, Z, Z1, Z2, Z3, Z4, Z5 for "setHIDDENM2"
(*\$CT 8*)
mtheorem mcart_1_th_9:
" for X be setHIDDENM2 holds X <>HIDDENR2 {}XBOOLE-0K1 implies ( ex v be objectHIDDENM1 st v inHIDDENR3 X &  not ( ex x be objectHIDDENM1 st  ex y be objectHIDDENM1 st (x inHIDDENR3 X or y inHIDDENR3 X) & v =HIDDENR1 [TARSKIK4 x,y ]))"
sorry

mtheorem mcart_1_th_10:
" for z be objectHIDDENM1 holds  for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds z inHIDDENR3 [:ZFMISC-1K2 X,Y :] implies z `1XTUPLE-0K1 inHIDDENR3 X & z `2XTUPLE-0K2 inHIDDENR3 Y"
sorry

(*\$CT*)
mtheorem mcart_1_th_12:
" for x be objectHIDDENM1 holds  for z be objectHIDDENM1 holds  for Y be setHIDDENM2 holds z inHIDDENR3 [:ZFMISC-1K2 {TARSKIK1 x},Y :] implies z `1XTUPLE-0K1 =HIDDENR1 x & z `2XTUPLE-0K2 inHIDDENR3 Y"
sorry

mtheorem mcart_1_th_13:
" for y be objectHIDDENM1 holds  for z be objectHIDDENM1 holds  for X be setHIDDENM2 holds z inHIDDENR3 [:ZFMISC-1K2 X,{TARSKIK1 y} :] implies z `1XTUPLE-0K1 inHIDDENR3 X & z `2XTUPLE-0K2 =HIDDENR1 y"
sorry

mtheorem mcart_1_th_14:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for z be objectHIDDENM1 holds z inHIDDENR3 [:ZFMISC-1K2 {TARSKIK1 x},{TARSKIK1 y} :] implies z `1XTUPLE-0K1 =HIDDENR1 x & z `2XTUPLE-0K2 =HIDDENR1 y"
sorry

mtheorem mcart_1_th_15:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for z be objectHIDDENM1 holds  for Y be setHIDDENM2 holds z inHIDDENR3 [:ZFMISC-1K2 {TARSKIK2 x1,x2 },Y :] implies (z `1XTUPLE-0K1 =HIDDENR1 x1 or z `1XTUPLE-0K1 =HIDDENR1 x2) & z `2XTUPLE-0K2 inHIDDENR3 Y"
sorry

mtheorem mcart_1_th_16:
" for y1 be objectHIDDENM1 holds  for y2 be objectHIDDENM1 holds  for z be objectHIDDENM1 holds  for X be setHIDDENM2 holds z inHIDDENR3 [:ZFMISC-1K2 X,{TARSKIK2 y1,y2 } :] implies z `1XTUPLE-0K1 inHIDDENR3 X & (z `2XTUPLE-0K2 =HIDDENR1 y1 or z `2XTUPLE-0K2 =HIDDENR1 y2)"
sorry

mtheorem mcart_1_th_17:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for z be objectHIDDENM1 holds z inHIDDENR3 [:ZFMISC-1K2 {TARSKIK2 x1,x2 },{TARSKIK1 y} :] implies (z `1XTUPLE-0K1 =HIDDENR1 x1 or z `1XTUPLE-0K1 =HIDDENR1 x2) & z `2XTUPLE-0K2 =HIDDENR1 y"
sorry

mtheorem mcart_1_th_18:
" for x be objectHIDDENM1 holds  for y1 be objectHIDDENM1 holds  for y2 be objectHIDDENM1 holds  for z be objectHIDDENM1 holds z inHIDDENR3 [:ZFMISC-1K2 {TARSKIK1 x},{TARSKIK2 y1,y2 } :] implies z `1XTUPLE-0K1 =HIDDENR1 x & (z `2XTUPLE-0K2 =HIDDENR1 y1 or z `2XTUPLE-0K2 =HIDDENR1 y2)"
sorry

mtheorem mcart_1_th_19:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for y1 be objectHIDDENM1 holds  for y2 be objectHIDDENM1 holds  for z be objectHIDDENM1 holds z inHIDDENR3 [:ZFMISC-1K2 {TARSKIK2 x1,x2 },{TARSKIK2 y1,y2 } :] implies (z `1XTUPLE-0K1 =HIDDENR1 x1 or z `1XTUPLE-0K1 =HIDDENR1 x2) & (z `2XTUPLE-0K2 =HIDDENR1 y1 or z `2XTUPLE-0K2 =HIDDENR1 y2)"
sorry

mtheorem mcart_1_th_20:
" for x be objectHIDDENM1 holds ( ex y be objectHIDDENM1 st  ex z be objectHIDDENM1 st x =HIDDENR1 [TARSKIK4 y,z ]) implies x <>HIDDENR2 x `1XTUPLE-0K1 & x <>HIDDENR2 x `2XTUPLE-0K2"
sorry

reserve R for "RelationRELAT-1M1"
mtheorem mcart_1_th_21:
" for x be objectHIDDENM1 holds  for R be RelationRELAT-1M1 holds x inHIDDENR3 R implies x =HIDDENR1 [TARSKIK4 x `1XTUPLE-0K1,x `2XTUPLE-0K2 ]"
sorry

mlemma mcart_1_lm_1:
" for X1 be setHIDDENM2 holds  for X2 be setHIDDENM2 holds X1 <>HIDDENR2 {}XBOOLE-0K1 & X2 <>HIDDENR2 {}XBOOLE-0K1 implies ( for x be ElementSUBSET-1M1-of [:ZFMISC-1K2 X1,X2 :] holds  ex xx1 be ElementSUBSET-1M1-of X1 st  ex xx2 be ElementSUBSET-1M1-of X2 st x =HIDDENR1 [TARSKIK4 xx1,xx2 ])"
sorry

mtheorem mcart_1_cl_1:
  mlet "X1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "X2 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster note-that pairXTUPLE-0V1 for ElementSUBSET-1M1-of [:ZFMISC-1K2 X1,X2 :]"
proof
(*coherence*)
  show " for it be ElementSUBSET-1M1-of [:ZFMISC-1K2 X1,X2 :] holds it be pairXTUPLE-0V1"
sorry
qed "sorry"

mtheorem mcart_1_th_22:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X <>HIDDENR2 {}XBOOLE-0K1 & Y <>HIDDENR2 {}XBOOLE-0K1 implies ( for x be ElementSUBSET-1M1-of [:ZFMISC-1K2 X,Y :] holds x =HIDDENR1 [TARSKIK4 x `1XTUPLE-0K1,x `2XTUPLE-0K2 ])"
  using mcart_1_th_21 sorry

mtheorem mcart_1_th_23:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for y1 be objectHIDDENM1 holds  for y2 be objectHIDDENM1 holds [:ZFMISC-1K2 {TARSKIK2 x1,x2 },{TARSKIK2 y1,y2 } :] =XBOOLE-0R4 {ENUMSET1K2 [TARSKIK4 x1,y1 ],[TARSKIK4 x1,y2 ],[TARSKIK4 x2,y1 ],[TARSKIK4 x2,y2 ] }"
sorry

mtheorem mcart_1_th_24:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X <>HIDDENR2 {}XBOOLE-0K1 & Y <>HIDDENR2 {}XBOOLE-0K1 implies ( for x be ElementSUBSET-1M1-of [:ZFMISC-1K2 X,Y :] holds x <>HIDDENR2 x `1XTUPLE-0K1 & x <>HIDDENR2 x `2XTUPLE-0K2)"
sorry

(*\$CT*)
mtheorem mcart_1_th_26:
" for X be setHIDDENM2 holds X <>HIDDENR2 {}XBOOLE-0K1 implies ( ex v be objectHIDDENM1 st v inHIDDENR3 X &  not ( ex x be objectHIDDENM1 st  ex y be objectHIDDENM1 st  ex z be objectHIDDENM1 st (x inHIDDENR3 X or y inHIDDENR3 X) & v =HIDDENR1 [XTUPLE-0K3 x,y,z ]))"
sorry

(*\$CT 3*)
mtheorem mcart_1_th_30:
" for X be setHIDDENM2 holds X <>HIDDENR2 {}XBOOLE-0K1 implies ( ex v be objectHIDDENM1 st v inHIDDENR3 X &  not ( ex x1 be objectHIDDENM1 st  ex x2 be objectHIDDENM1 st  ex x3 be objectHIDDENM1 st  ex x4 be objectHIDDENM1 st (x1 inHIDDENR3 X or x2 inHIDDENR3 X) & v =HIDDENR1 [XTUPLE-0K7 x1,x2,x3,x4 ]))"
sorry

mtheorem mcart_1_th_31:
" for X1 be setHIDDENM2 holds  for X2 be setHIDDENM2 holds  for X3 be setHIDDENM2 holds (X1 <>HIDDENR2 {}XBOOLE-0K1 & X2 <>HIDDENR2 {}XBOOLE-0K1) & X3 <>HIDDENR2 {}XBOOLE-0K1 iff [:ZFMISC-1K3 X1,X2,X3 :] <>HIDDENR2 {}XBOOLE-0K1"
sorry

reserve xx1 for "ElementSUBSET-1M1-of X1"
reserve xx2 for "ElementSUBSET-1M1-of X2"
reserve xx3 for "ElementSUBSET-1M1-of X3"
mtheorem mcart_1_th_32:
" for X1 be setHIDDENM2 holds  for X2 be setHIDDENM2 holds  for X3 be setHIDDENM2 holds  for Y1 be setHIDDENM2 holds  for Y2 be setHIDDENM2 holds  for Y3 be setHIDDENM2 holds (X1 <>HIDDENR2 {}XBOOLE-0K1 & X2 <>HIDDENR2 {}XBOOLE-0K1) & X3 <>HIDDENR2 {}XBOOLE-0K1 implies ([:ZFMISC-1K3 X1,X2,X3 :] =XBOOLE-0R4 [:ZFMISC-1K3 Y1,Y2,Y3 :] implies (X1 =XBOOLE-0R4 Y1 & X2 =XBOOLE-0R4 Y2) & X3 =XBOOLE-0R4 Y3)"
sorry

mtheorem mcart_1_th_33:
" for X1 be setHIDDENM2 holds  for X2 be setHIDDENM2 holds  for X3 be setHIDDENM2 holds  for Y1 be setHIDDENM2 holds  for Y2 be setHIDDENM2 holds  for Y3 be setHIDDENM2 holds [:ZFMISC-1K3 X1,X2,X3 :] <>HIDDENR2 {}XBOOLE-0K1 & [:ZFMISC-1K3 X1,X2,X3 :] =XBOOLE-0R4 [:ZFMISC-1K3 Y1,Y2,Y3 :] implies (X1 =XBOOLE-0R4 Y1 & X2 =XBOOLE-0R4 Y2) & X3 =XBOOLE-0R4 Y3"
sorry

mtheorem mcart_1_th_34:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds [:ZFMISC-1K3 X,X,X :] =XBOOLE-0R4 [:ZFMISC-1K3 Y,Y,Y :] implies X =XBOOLE-0R4 Y"
sorry

mlemma mcart_1_lm_2:
" for X1 be setHIDDENM2 holds  for X2 be setHIDDENM2 holds  for X3 be setHIDDENM2 holds (X1 <>HIDDENR2 {}XBOOLE-0K1 & X2 <>HIDDENR2 {}XBOOLE-0K1) & X3 <>HIDDENR2 {}XBOOLE-0K1 implies ( for x be ElementSUBSET-1M1-of [:ZFMISC-1K3 X1,X2,X3 :] holds  ex xx1 be ElementSUBSET-1M1-of X1 st  ex xx2 be ElementSUBSET-1M1-of X2 st  ex xx3 be ElementSUBSET-1M1-of X3 st x =HIDDENR1 [XTUPLE-0K3 xx1,xx2,xx3 ])"
sorry

mtheorem mcart_1_th_35:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds [:ZFMISC-1K3 {TARSKIK1 x1},{TARSKIK1 x2},{TARSKIK1 x3} :] =XBOOLE-0R4 {TARSKIK1 [XTUPLE-0K3 x1,x2,x3 ] }"
sorry

mtheorem mcart_1_th_36:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for y1 be objectHIDDENM1 holds [:ZFMISC-1K3 {TARSKIK2 x1,y1 },{TARSKIK1 x2},{TARSKIK1 x3} :] =XBOOLE-0R4 {TARSKIK2 [XTUPLE-0K3 x1,x2,x3 ],[XTUPLE-0K3 y1,x2,x3 ] }"
sorry

mtheorem mcart_1_th_37:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for y2 be objectHIDDENM1 holds [:ZFMISC-1K3 {TARSKIK1 x1},{TARSKIK2 x2,y2 },{TARSKIK1 x3} :] =XBOOLE-0R4 {TARSKIK2 [XTUPLE-0K3 x1,x2,x3 ],[XTUPLE-0K3 x1,y2,x3 ] }"
sorry

mtheorem mcart_1_th_38:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for y3 be objectHIDDENM1 holds [:ZFMISC-1K3 {TARSKIK1 x1},{TARSKIK1 x2},{TARSKIK2 x3,y3 } :] =XBOOLE-0R4 {TARSKIK2 [XTUPLE-0K3 x1,x2,x3 ],[XTUPLE-0K3 x1,x2,y3 ] }"
sorry

mtheorem mcart_1_th_39:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for y1 be objectHIDDENM1 holds  for y2 be objectHIDDENM1 holds [:ZFMISC-1K3 {TARSKIK2 x1,y1 },{TARSKIK2 x2,y2 },{TARSKIK1 x3} :] =XBOOLE-0R4 {ENUMSET1K2 [XTUPLE-0K3 x1,x2,x3 ],[XTUPLE-0K3 y1,x2,x3 ],[XTUPLE-0K3 x1,y2,x3 ],[XTUPLE-0K3 y1,y2,x3 ] }"
sorry

mtheorem mcart_1_th_40:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for y1 be objectHIDDENM1 holds  for y3 be objectHIDDENM1 holds [:ZFMISC-1K3 {TARSKIK2 x1,y1 },{TARSKIK1 x2},{TARSKIK2 x3,y3 } :] =XBOOLE-0R4 {ENUMSET1K2 [XTUPLE-0K3 x1,x2,x3 ],[XTUPLE-0K3 y1,x2,x3 ],[XTUPLE-0K3 x1,x2,y3 ],[XTUPLE-0K3 y1,x2,y3 ] }"
sorry

mtheorem mcart_1_th_41:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for y2 be objectHIDDENM1 holds  for y3 be objectHIDDENM1 holds [:ZFMISC-1K3 {TARSKIK1 x1},{TARSKIK2 x2,y2 },{TARSKIK2 x3,y3 } :] =XBOOLE-0R4 {ENUMSET1K2 [XTUPLE-0K3 x1,x2,x3 ],[XTUPLE-0K3 x1,y2,x3 ],[XTUPLE-0K3 x1,x2,y3 ],[XTUPLE-0K3 x1,y2,y3 ] }"
sorry

mtheorem mcart_1_th_42:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for y1 be objectHIDDENM1 holds  for y2 be objectHIDDENM1 holds  for y3 be objectHIDDENM1 holds [:ZFMISC-1K3 {TARSKIK2 x1,y1 },{TARSKIK2 x2,y2 },{TARSKIK2 x3,y3 } :] =XBOOLE-0R4 {ENUMSET1K6 [XTUPLE-0K3 x1,x2,x3 ],[XTUPLE-0K3 x1,y2,x3 ],[XTUPLE-0K3 x1,x2,y3 ],[XTUPLE-0K3 x1,y2,y3 ],[XTUPLE-0K3 y1,x2,x3 ],[XTUPLE-0K3 y1,y2,x3 ],[XTUPLE-0K3 y1,x2,y3 ],[XTUPLE-0K3 y1,y2,y3 ] }"
sorry

mtheorem mcart_1_cl_2:
  mlet "X1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "X2 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "X3 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster note-that tripleXTUPLE-0V2 for ElementSUBSET-1M1-of [:ZFMISC-1K3 X1,X2,X3 :]"
proof
(*coherence*)
  show " for it be ElementSUBSET-1M1-of [:ZFMISC-1K3 X1,X2,X3 :] holds it be tripleXTUPLE-0V2"
sorry
qed "sorry"

(*\$CD 4*)
syntax MCART_1K1 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ `1-3MCART-1K1\<^bsub>'( _ , _ , _ ')\<^esub>" [164,0,0,0]164)
translations "x `1-3MCART-1K1\<^bsub>(X1,X2,X3)\<^esub>" \<rightharpoonup> "x `1-3XTUPLE-0K4"

mtheorem mcart_1_def_5:
  mlet "X1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "X2 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "X3 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "x be ElementSUBSET-1M1-of [:ZFMISC-1K3 X1,X2,X3 :]"
"redefine func x `1-3MCART-1K1\<^bsub>(X1,X2,X3)\<^esub> \<rightarrow> ElementSUBSET-1M1-of X1 means
  \<lambda>it.  for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds x =HIDDENR1 [XTUPLE-0K3 x1,x2,x3 ] implies it =HIDDENR1 x1"
proof
(*compatibility*)
  show " for it be ElementSUBSET-1M1-of X1 holds it =HIDDENR1 x `1-3MCART-1K1\<^bsub>(X1,X2,X3)\<^esub> iff ( for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds x =HIDDENR1 [XTUPLE-0K3 x1,x2,x3 ] implies it =HIDDENR1 x1)"
sorry
qed "sorry"

mtheorem mcart_1_add_1:
  mlet "X1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "X2 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "X3 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "x be ElementSUBSET-1M1-of [:ZFMISC-1K3 X1,X2,X3 :]"
"cluster x `1-3XTUPLE-0K4 as-term-is ElementSUBSET-1M1-of X1"
proof
(*coherence*)
  show "x `1-3XTUPLE-0K4 be ElementSUBSET-1M1-of X1"
sorry
qed "sorry"

syntax MCART_1K2 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ `2-3MCART-1K2\<^bsub>'( _ , _ , _ ')\<^esub>" [164,0,0,0]164)
translations "x `2-3MCART-1K2\<^bsub>(X1,X2,X3)\<^esub>" \<rightharpoonup> "x `2-3XTUPLE-0K5"

mtheorem mcart_1_def_6:
  mlet "X1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "X2 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "X3 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "x be ElementSUBSET-1M1-of [:ZFMISC-1K3 X1,X2,X3 :]"
"redefine func x `2-3MCART-1K2\<^bsub>(X1,X2,X3)\<^esub> \<rightarrow> ElementSUBSET-1M1-of X2 means
  \<lambda>it.  for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds x =HIDDENR1 [XTUPLE-0K3 x1,x2,x3 ] implies it =HIDDENR1 x2"
proof
(*compatibility*)
  show " for it be ElementSUBSET-1M1-of X2 holds it =HIDDENR1 x `2-3MCART-1K2\<^bsub>(X1,X2,X3)\<^esub> iff ( for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds x =HIDDENR1 [XTUPLE-0K3 x1,x2,x3 ] implies it =HIDDENR1 x2)"
sorry
qed "sorry"

mtheorem mcart_1_add_2:
  mlet "X1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "X2 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "X3 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "x be ElementSUBSET-1M1-of [:ZFMISC-1K3 X1,X2,X3 :]"
"cluster x `2-3XTUPLE-0K5 as-term-is ElementSUBSET-1M1-of X2"
proof
(*coherence*)
  show "x `2-3XTUPLE-0K5 be ElementSUBSET-1M1-of X2"
sorry
qed "sorry"

syntax MCART_1K3 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ `3-3MCART-1K3\<^bsub>'( _ , _ , _ ')\<^esub>" [164,0,0,0]164)
translations "x `3-3MCART-1K3\<^bsub>(X1,X2,X3)\<^esub>" \<rightharpoonup> "x `2XTUPLE-0K2"

mtheorem mcart_1_def_7:
  mlet "X1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "X2 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "X3 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "x be ElementSUBSET-1M1-of [:ZFMISC-1K3 X1,X2,X3 :]"
"redefine func x `3-3MCART-1K3\<^bsub>(X1,X2,X3)\<^esub> \<rightarrow> ElementSUBSET-1M1-of X3 means
  \<lambda>it.  for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds x =HIDDENR1 [XTUPLE-0K3 x1,x2,x3 ] implies it =HIDDENR1 x3"
proof
(*compatibility*)
  show " for it be ElementSUBSET-1M1-of X3 holds it =HIDDENR1 x `3-3MCART-1K3\<^bsub>(X1,X2,X3)\<^esub> iff ( for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds x =HIDDENR1 [XTUPLE-0K3 x1,x2,x3 ] implies it =HIDDENR1 x3)"
sorry
qed "sorry"

mtheorem mcart_1_add_3:
  mlet "X1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "X2 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "X3 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "x be ElementSUBSET-1M1-of [:ZFMISC-1K3 X1,X2,X3 :]"
"cluster x `2XTUPLE-0K2 as-term-is ElementSUBSET-1M1-of X3"
proof
(*coherence*)
  show "x `2XTUPLE-0K2 be ElementSUBSET-1M1-of X3"
sorry
qed "sorry"

(*\$CT 2*)
mtheorem mcart_1_th_45:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds (X c=TARSKIR1 [:ZFMISC-1K3 X,Y,Z :] or X c=TARSKIR1 [:ZFMISC-1K3 Y,Z,X :]) or X c=TARSKIR1 [:ZFMISC-1K3 Z,X,Y :] implies X =XBOOLE-0R4 {}XBOOLE-0K1"
sorry

(*\$CT*)
mtheorem mcart_1_th_47:
" for X1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X2 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X3 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for x be ElementSUBSET-1M1-of [:ZFMISC-1K3 X1,X2,X3 :] holds (x <>HIDDENR2 x `1-3MCART-1K1\<^bsub>(X1,X2,X3)\<^esub> & x <>HIDDENR2 x `2-3MCART-1K2\<^bsub>(X1,X2,X3)\<^esub>) & x <>HIDDENR2 x `3-3MCART-1K3\<^bsub>(X1,X2,X3)\<^esub>"
sorry

mtheorem mcart_1_th_48:
" for X1 be setHIDDENM2 holds  for X2 be setHIDDENM2 holds  for X3 be setHIDDENM2 holds  for Y1 be setHIDDENM2 holds  for Y2 be setHIDDENM2 holds  for Y3 be setHIDDENM2 holds [:ZFMISC-1K3 X1,X2,X3 :] meetsXBOOLE-0R5 [:ZFMISC-1K3 Y1,Y2,Y3 :] implies (X1 meetsXBOOLE-0R5 Y1 & X2 meetsXBOOLE-0R5 Y2) & X3 meetsXBOOLE-0R5 Y3"
sorry

mtheorem mcart_1_th_49:
" for X1 be setHIDDENM2 holds  for X2 be setHIDDENM2 holds  for X3 be setHIDDENM2 holds  for X4 be setHIDDENM2 holds [:ZFMISC-1K4 X1,X2,X3,X4 :] =XBOOLE-0R4 [:ZFMISC-1K2 [:ZFMISC-1K2 [:ZFMISC-1K2 X1,X2 :],X3 :],X4 :]"
sorry

mtheorem mcart_1_th_50:
" for X1 be setHIDDENM2 holds  for X2 be setHIDDENM2 holds  for X3 be setHIDDENM2 holds  for X4 be setHIDDENM2 holds [:ZFMISC-1K3 [:ZFMISC-1K2 X1,X2 :],X3,X4 :] =XBOOLE-0R4 [:ZFMISC-1K4 X1,X2,X3,X4 :]"
sorry

mtheorem mcart_1_th_51:
" for X1 be setHIDDENM2 holds  for X2 be setHIDDENM2 holds  for X3 be setHIDDENM2 holds  for X4 be setHIDDENM2 holds ((X1 <>HIDDENR2 {}XBOOLE-0K1 & X2 <>HIDDENR2 {}XBOOLE-0K1) & X3 <>HIDDENR2 {}XBOOLE-0K1) & X4 <>HIDDENR2 {}XBOOLE-0K1 iff [:ZFMISC-1K4 X1,X2,X3,X4 :] <>HIDDENR2 {}XBOOLE-0K1"
sorry

mtheorem mcart_1_th_52:
" for X1 be setHIDDENM2 holds  for X2 be setHIDDENM2 holds  for X3 be setHIDDENM2 holds  for X4 be setHIDDENM2 holds  for Y1 be setHIDDENM2 holds  for Y2 be setHIDDENM2 holds  for Y3 be setHIDDENM2 holds  for Y4 be setHIDDENM2 holds (((X1 <>HIDDENR2 {}XBOOLE-0K1 & X2 <>HIDDENR2 {}XBOOLE-0K1) & X3 <>HIDDENR2 {}XBOOLE-0K1) & X4 <>HIDDENR2 {}XBOOLE-0K1) & [:ZFMISC-1K4 X1,X2,X3,X4 :] =XBOOLE-0R4 [:ZFMISC-1K4 Y1,Y2,Y3,Y4 :] implies ((X1 =XBOOLE-0R4 Y1 & X2 =XBOOLE-0R4 Y2) & X3 =XBOOLE-0R4 Y3) & X4 =XBOOLE-0R4 Y4"
sorry

mtheorem mcart_1_th_53:
" for X1 be setHIDDENM2 holds  for X2 be setHIDDENM2 holds  for X3 be setHIDDENM2 holds  for X4 be setHIDDENM2 holds  for Y1 be setHIDDENM2 holds  for Y2 be setHIDDENM2 holds  for Y3 be setHIDDENM2 holds  for Y4 be setHIDDENM2 holds [:ZFMISC-1K4 X1,X2,X3,X4 :] <>HIDDENR2 {}XBOOLE-0K1 & [:ZFMISC-1K4 X1,X2,X3,X4 :] =XBOOLE-0R4 [:ZFMISC-1K4 Y1,Y2,Y3,Y4 :] implies ((X1 =XBOOLE-0R4 Y1 & X2 =XBOOLE-0R4 Y2) & X3 =XBOOLE-0R4 Y3) & X4 =XBOOLE-0R4 Y4"
sorry

mtheorem mcart_1_th_54:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds [:ZFMISC-1K4 X,X,X,X :] =XBOOLE-0R4 [:ZFMISC-1K4 Y,Y,Y,Y :] implies X =XBOOLE-0R4 Y"
sorry

reserve xx4 for "ElementSUBSET-1M1-of X4"
mlemma mcart_1_lm_3:
" for X1 be setHIDDENM2 holds  for X2 be setHIDDENM2 holds  for X3 be setHIDDENM2 holds  for X4 be setHIDDENM2 holds ((X1 <>HIDDENR2 {}XBOOLE-0K1 & X2 <>HIDDENR2 {}XBOOLE-0K1) & X3 <>HIDDENR2 {}XBOOLE-0K1) & X4 <>HIDDENR2 {}XBOOLE-0K1 implies ( for x be ElementSUBSET-1M1-of [:ZFMISC-1K4 X1,X2,X3,X4 :] holds  ex xx1 be ElementSUBSET-1M1-of X1 st  ex xx2 be ElementSUBSET-1M1-of X2 st  ex xx3 be ElementSUBSET-1M1-of X3 st  ex xx4 be ElementSUBSET-1M1-of X4 st x =HIDDENR1 [XTUPLE-0K7 xx1,xx2,xx3,xx4 ])"
sorry

mtheorem mcart_1_cl_3:
  mlet "X1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "X2 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "X3 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "X4 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster note-that quadrupleXTUPLE-0V3 for ElementSUBSET-1M1-of [:ZFMISC-1K4 X1,X2,X3,X4 :]"
proof
(*coherence*)
  show " for it be ElementSUBSET-1M1-of [:ZFMISC-1K4 X1,X2,X3,X4 :] holds it be quadrupleXTUPLE-0V3"
sorry
qed "sorry"

syntax MCART_1K4 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ `1-4MCART-1K4\<^bsub>'( _ , _ , _ , _ ')\<^esub>" [164,0,0,0,0]164)
translations "x `1-4MCART-1K4\<^bsub>(X1,X2,X3,X4)\<^esub>" \<rightharpoonup> "x `1-4XTUPLE-0K8"

mtheorem mcart_1_def_8:
  mlet "X1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "X2 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "X3 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "X4 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "x be ElementSUBSET-1M1-of [:ZFMISC-1K4 X1,X2,X3,X4 :]"
"redefine func x `1-4MCART-1K4\<^bsub>(X1,X2,X3,X4)\<^esub> \<rightarrow> ElementSUBSET-1M1-of X1 means
  \<lambda>it.  for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for x4 be objectHIDDENM1 holds x =HIDDENR1 [XTUPLE-0K7 x1,x2,x3,x4 ] implies it =HIDDENR1 x1"
proof
(*compatibility*)
  show " for it be ElementSUBSET-1M1-of X1 holds it =HIDDENR1 x `1-4MCART-1K4\<^bsub>(X1,X2,X3,X4)\<^esub> iff ( for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for x4 be objectHIDDENM1 holds x =HIDDENR1 [XTUPLE-0K7 x1,x2,x3,x4 ] implies it =HIDDENR1 x1)"
sorry
qed "sorry"

mtheorem mcart_1_add_4:
  mlet "X1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "X2 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "X3 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "X4 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "x be ElementSUBSET-1M1-of [:ZFMISC-1K4 X1,X2,X3,X4 :]"
"cluster x `1-4XTUPLE-0K8 as-term-is ElementSUBSET-1M1-of X1"
proof
(*coherence*)
  show "x `1-4XTUPLE-0K8 be ElementSUBSET-1M1-of X1"
sorry
qed "sorry"

syntax MCART_1K5 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ `2-4MCART-1K5\<^bsub>'( _ , _ , _ , _ ')\<^esub>" [164,0,0,0,0]164)
translations "x `2-4MCART-1K5\<^bsub>(X1,X2,X3,X4)\<^esub>" \<rightharpoonup> "x `2-4XTUPLE-0K9"

mtheorem mcart_1_def_9:
  mlet "X1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "X2 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "X3 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "X4 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "x be ElementSUBSET-1M1-of [:ZFMISC-1K4 X1,X2,X3,X4 :]"
"redefine func x `2-4MCART-1K5\<^bsub>(X1,X2,X3,X4)\<^esub> \<rightarrow> ElementSUBSET-1M1-of X2 means
  \<lambda>it.  for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for x4 be objectHIDDENM1 holds x =HIDDENR1 [XTUPLE-0K7 x1,x2,x3,x4 ] implies it =HIDDENR1 x2"
proof
(*compatibility*)
  show " for it be ElementSUBSET-1M1-of X2 holds it =HIDDENR1 x `2-4MCART-1K5\<^bsub>(X1,X2,X3,X4)\<^esub> iff ( for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for x4 be objectHIDDENM1 holds x =HIDDENR1 [XTUPLE-0K7 x1,x2,x3,x4 ] implies it =HIDDENR1 x2)"
sorry
qed "sorry"

mtheorem mcart_1_add_5:
  mlet "X1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "X2 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "X3 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "X4 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "x be ElementSUBSET-1M1-of [:ZFMISC-1K4 X1,X2,X3,X4 :]"
"cluster x `2-4XTUPLE-0K9 as-term-is ElementSUBSET-1M1-of X2"
proof
(*coherence*)
  show "x `2-4XTUPLE-0K9 be ElementSUBSET-1M1-of X2"
sorry
qed "sorry"

syntax MCART_1K6 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ `3-4MCART-1K6\<^bsub>'( _ , _ , _ , _ ')\<^esub>" [164,0,0,0,0]164)
translations "x `3-4MCART-1K6\<^bsub>(X1,X2,X3,X4)\<^esub>" \<rightharpoonup> "x `2-3XTUPLE-0K5"

mtheorem mcart_1_def_10:
  mlet "X1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "X2 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "X3 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "X4 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "x be ElementSUBSET-1M1-of [:ZFMISC-1K4 X1,X2,X3,X4 :]"
"redefine func x `3-4MCART-1K6\<^bsub>(X1,X2,X3,X4)\<^esub> \<rightarrow> ElementSUBSET-1M1-of X3 means
  \<lambda>it.  for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for x4 be objectHIDDENM1 holds x =HIDDENR1 [XTUPLE-0K7 x1,x2,x3,x4 ] implies it =HIDDENR1 x3"
proof
(*compatibility*)
  show " for it be ElementSUBSET-1M1-of X3 holds it =HIDDENR1 x `3-4MCART-1K6\<^bsub>(X1,X2,X3,X4)\<^esub> iff ( for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for x4 be objectHIDDENM1 holds x =HIDDENR1 [XTUPLE-0K7 x1,x2,x3,x4 ] implies it =HIDDENR1 x3)"
sorry
qed "sorry"

mtheorem mcart_1_add_6:
  mlet "X1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "X2 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "X3 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "X4 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "x be ElementSUBSET-1M1-of [:ZFMISC-1K4 X1,X2,X3,X4 :]"
"cluster x `2-3XTUPLE-0K5 as-term-is ElementSUBSET-1M1-of X3"
proof
(*coherence*)
  show "x `2-3XTUPLE-0K5 be ElementSUBSET-1M1-of X3"
sorry
qed "sorry"

syntax MCART_1K7 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ `4-4MCART-1K7\<^bsub>'( _ , _ , _ , _ ')\<^esub>" [164,0,0,0,0]164)
translations "x `4-4MCART-1K7\<^bsub>(X1,X2,X3,X4)\<^esub>" \<rightharpoonup> "x `2XTUPLE-0K2"

mtheorem mcart_1_def_11:
  mlet "X1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "X2 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "X3 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "X4 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "x be ElementSUBSET-1M1-of [:ZFMISC-1K4 X1,X2,X3,X4 :]"
"redefine func x `4-4MCART-1K7\<^bsub>(X1,X2,X3,X4)\<^esub> \<rightarrow> ElementSUBSET-1M1-of X4 means
  \<lambda>it.  for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for x4 be objectHIDDENM1 holds x =HIDDENR1 [XTUPLE-0K7 x1,x2,x3,x4 ] implies it =HIDDENR1 x4"
proof
(*compatibility*)
  show " for it be ElementSUBSET-1M1-of X4 holds it =HIDDENR1 x `4-4MCART-1K7\<^bsub>(X1,X2,X3,X4)\<^esub> iff ( for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for x4 be objectHIDDENM1 holds x =HIDDENR1 [XTUPLE-0K7 x1,x2,x3,x4 ] implies it =HIDDENR1 x4)"
sorry
qed "sorry"

mtheorem mcart_1_add_7:
  mlet "X1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "X2 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "X3 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "X4 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "x be ElementSUBSET-1M1-of [:ZFMISC-1K4 X1,X2,X3,X4 :]"
"cluster x `2XTUPLE-0K2 as-term-is ElementSUBSET-1M1-of X4"
proof
(*coherence*)
  show "x `2XTUPLE-0K2 be ElementSUBSET-1M1-of X4"
sorry
qed "sorry"

(*\$CT 3*)
mtheorem mcart_1_th_58:
" for X1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X2 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X3 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X4 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for x be ElementSUBSET-1M1-of [:ZFMISC-1K4 X1,X2,X3,X4 :] holds ((x <>HIDDENR2 x `1-4MCART-1K4\<^bsub>(X1,X2,X3,X4)\<^esub> & x <>HIDDENR2 x `2-4MCART-1K5\<^bsub>(X1,X2,X3,X4)\<^esub>) & x <>HIDDENR2 x `3-4MCART-1K6\<^bsub>(X1,X2,X3,X4)\<^esub>) & x <>HIDDENR2 x `4-4MCART-1K7\<^bsub>(X1,X2,X3,X4)\<^esub>"
sorry

mtheorem mcart_1_th_59:
" for X1 be setHIDDENM2 holds  for X2 be setHIDDENM2 holds  for X3 be setHIDDENM2 holds  for X4 be setHIDDENM2 holds ((X1 c=TARSKIR1 [:ZFMISC-1K4 X1,X2,X3,X4 :] or X1 c=TARSKIR1 [:ZFMISC-1K4 X2,X3,X4,X1 :]) or X1 c=TARSKIR1 [:ZFMISC-1K4 X3,X4,X1,X2 :]) or X1 c=TARSKIR1 [:ZFMISC-1K4 X4,X1,X2,X3 :] implies X1 =XBOOLE-0R4 {}XBOOLE-0K1"
sorry

mtheorem mcart_1_th_60:
" for X1 be setHIDDENM2 holds  for X2 be setHIDDENM2 holds  for X3 be setHIDDENM2 holds  for X4 be setHIDDENM2 holds  for Y1 be setHIDDENM2 holds  for Y2 be setHIDDENM2 holds  for Y3 be setHIDDENM2 holds  for Y4 be setHIDDENM2 holds [:ZFMISC-1K4 X1,X2,X3,X4 :] meetsXBOOLE-0R5 [:ZFMISC-1K4 Y1,Y2,Y3,Y4 :] implies ((X1 meetsXBOOLE-0R5 Y1 & X2 meetsXBOOLE-0R5 Y2) & X3 meetsXBOOLE-0R5 Y3) & X4 meetsXBOOLE-0R5 Y4"
sorry

mtheorem mcart_1_th_61:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for x4 be objectHIDDENM1 holds [:ZFMISC-1K4 {TARSKIK1 x1},{TARSKIK1 x2},{TARSKIK1 x3},{TARSKIK1 x4} :] =XBOOLE-0R4 {TARSKIK1 [XTUPLE-0K7 x1,x2,x3,x4 ] }"
sorry

mtheorem mcart_1_th_62:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds [:ZFMISC-1K2 X,Y :] <>HIDDENR2 {}XBOOLE-0K1 implies ( for x be ElementSUBSET-1M1-of [:ZFMISC-1K2 X,Y :] holds x <>HIDDENR2 x `1XTUPLE-0K1 & x <>HIDDENR2 x `2XTUPLE-0K2)"
sorry

mtheorem mcart_1_th_63:
" for x be objectHIDDENM1 holds  for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds x inHIDDENR3 [:ZFMISC-1K2 X,Y :] implies x <>HIDDENR2 x `1XTUPLE-0K1 & x <>HIDDENR2 x `2XTUPLE-0K2"
  using mcart_1_th_62 sorry

reserve A1 for "SubsetSUBSET-1M2-of X1"
reserve A2 for "SubsetSUBSET-1M2-of X2"
reserve A3 for "SubsetSUBSET-1M2-of X3"
reserve A4 for "SubsetSUBSET-1M2-of X4"
mtheorem mcart_1_th_64:
" for X1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X2 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X3 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for x be ElementSUBSET-1M1-of [:ZFMISC-1K3 X1,X2,X3 :] holds  for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds x =HIDDENR1 [XTUPLE-0K3 x1,x2,x3 ] implies (x `1-3MCART-1K1\<^bsub>(X1,X2,X3)\<^esub> =HIDDENR1 x1 & x `2-3MCART-1K2\<^bsub>(X1,X2,X3)\<^esub> =HIDDENR1 x2) & x `3-3MCART-1K3\<^bsub>(X1,X2,X3)\<^esub> =HIDDENR1 x3"
   sorry

mtheorem mcart_1_th_65:
" for y1 be objectHIDDENM1 holds  for X1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X2 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X3 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for x be ElementSUBSET-1M1-of [:ZFMISC-1K3 X1,X2,X3 :] holds ( for xx1 be ElementSUBSET-1M1-of X1 holds  for xx2 be ElementSUBSET-1M1-of X2 holds  for xx3 be ElementSUBSET-1M1-of X3 holds x =HIDDENR1 [XTUPLE-0K3 xx1,xx2,xx3 ] implies y1 =HIDDENR1 xx1) implies y1 =HIDDENR1 x `1-3MCART-1K1\<^bsub>(X1,X2,X3)\<^esub>"
sorry

mtheorem mcart_1_th_66:
" for y2 be objectHIDDENM1 holds  for X1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X2 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X3 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for x be ElementSUBSET-1M1-of [:ZFMISC-1K3 X1,X2,X3 :] holds ( for xx1 be ElementSUBSET-1M1-of X1 holds  for xx2 be ElementSUBSET-1M1-of X2 holds  for xx3 be ElementSUBSET-1M1-of X3 holds x =HIDDENR1 [XTUPLE-0K3 xx1,xx2,xx3 ] implies y2 =HIDDENR1 xx2) implies y2 =HIDDENR1 x `2-3MCART-1K2\<^bsub>(X1,X2,X3)\<^esub>"
sorry

mtheorem mcart_1_th_67:
" for y3 be objectHIDDENM1 holds  for X1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X2 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X3 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for x be ElementSUBSET-1M1-of [:ZFMISC-1K3 X1,X2,X3 :] holds ( for xx1 be ElementSUBSET-1M1-of X1 holds  for xx2 be ElementSUBSET-1M1-of X2 holds  for xx3 be ElementSUBSET-1M1-of X3 holds x =HIDDENR1 [XTUPLE-0K3 xx1,xx2,xx3 ] implies y3 =HIDDENR1 xx3) implies y3 =HIDDENR1 x `3-3MCART-1K3\<^bsub>(X1,X2,X3)\<^esub>"
sorry

mtheorem mcart_1_th_68:
" for z be objectHIDDENM1 holds  for X1 be setHIDDENM2 holds  for X2 be setHIDDENM2 holds  for X3 be setHIDDENM2 holds z inHIDDENR3 [:ZFMISC-1K3 X1,X2,X3 :] implies ( ex x1 be objectHIDDENM1 st  ex x2 be objectHIDDENM1 st  ex x3 be objectHIDDENM1 st ((x1 inHIDDENR3 X1 & x2 inHIDDENR3 X2) & x3 inHIDDENR3 X3) & z =HIDDENR1 [XTUPLE-0K3 x1,x2,x3 ])"
sorry

mtheorem mcart_1_th_69:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for X1 be setHIDDENM2 holds  for X2 be setHIDDENM2 holds  for X3 be setHIDDENM2 holds [XTUPLE-0K3 x1,x2,x3 ] inHIDDENR3 [:ZFMISC-1K3 X1,X2,X3 :] iff (x1 inHIDDENR3 X1 & x2 inHIDDENR3 X2) & x3 inHIDDENR3 X3"
sorry

mtheorem mcart_1_th_70:
" for X1 be setHIDDENM2 holds  for X2 be setHIDDENM2 holds  for X3 be setHIDDENM2 holds  for Z be setHIDDENM2 holds ( for z be objectHIDDENM1 holds z inHIDDENR3 Z iff ( ex x1 be objectHIDDENM1 st  ex x2 be objectHIDDENM1 st  ex x3 be objectHIDDENM1 st ((x1 inHIDDENR3 X1 & x2 inHIDDENR3 X2) & x3 inHIDDENR3 X3) & z =HIDDENR1 [XTUPLE-0K3 x1,x2,x3 ])) implies Z =XBOOLE-0R4 [:ZFMISC-1K3 X1,X2,X3 :]"
sorry

(*\$CT*)
mtheorem mcart_1_th_72:
" for X1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X2 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X3 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for A1 be  non emptyXBOOLE-0V1\<bar>SubsetSUBSET-1M2-of X1 holds  for A2 be  non emptyXBOOLE-0V1\<bar>SubsetSUBSET-1M2-of X2 holds  for A3 be  non emptyXBOOLE-0V1\<bar>SubsetSUBSET-1M2-of X3 holds  for x be ElementSUBSET-1M1-of [:ZFMISC-1K3 X1,X2,X3 :] holds x inTARSKIR2 [:ZFMISC-1K3 A1,A2,A3 :] implies (x `1-3MCART-1K1\<^bsub>(X1,X2,X3)\<^esub> inTARSKIR2 A1 & x `2-3MCART-1K2\<^bsub>(X1,X2,X3)\<^esub> inTARSKIR2 A2) & x `3-3MCART-1K3\<^bsub>(X1,X2,X3)\<^esub> inTARSKIR2 A3"
sorry

mtheorem mcart_1_th_73:
" for X1 be setHIDDENM2 holds  for X2 be setHIDDENM2 holds  for X3 be setHIDDENM2 holds  for Y1 be setHIDDENM2 holds  for Y2 be setHIDDENM2 holds  for Y3 be setHIDDENM2 holds (X1 c=TARSKIR1 Y1 & X2 c=TARSKIR1 Y2) & X3 c=TARSKIR1 Y3 implies [:ZFMISC-1K3 X1,X2,X3 :] c=TARSKIR1 [:ZFMISC-1K3 Y1,Y2,Y3 :]"
sorry

mtheorem mcart_1_th_74:
" for X1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X2 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X3 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X4 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for x be ElementSUBSET-1M1-of [:ZFMISC-1K4 X1,X2,X3,X4 :] holds  for x1 be setHIDDENM2 holds  for x2 be setHIDDENM2 holds  for x3 be setHIDDENM2 holds  for x4 be setHIDDENM2 holds x =HIDDENR1 [XTUPLE-0K7 x1,x2,x3,x4 ] implies ((x `1-4MCART-1K4\<^bsub>(X1,X2,X3,X4)\<^esub> =XBOOLE-0R4 x1 & x `2-4MCART-1K5\<^bsub>(X1,X2,X3,X4)\<^esub> =XBOOLE-0R4 x2) & x `3-4MCART-1K6\<^bsub>(X1,X2,X3,X4)\<^esub> =XBOOLE-0R4 x3) & x `4-4MCART-1K7\<^bsub>(X1,X2,X3,X4)\<^esub> =XBOOLE-0R4 x4"
   sorry

mtheorem mcart_1_th_75:
" for y1 be objectHIDDENM1 holds  for X1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X2 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X3 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X4 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for x be ElementSUBSET-1M1-of [:ZFMISC-1K4 X1,X2,X3,X4 :] holds ( for xx1 be ElementSUBSET-1M1-of X1 holds  for xx2 be ElementSUBSET-1M1-of X2 holds  for xx3 be ElementSUBSET-1M1-of X3 holds  for xx4 be ElementSUBSET-1M1-of X4 holds x =HIDDENR1 [XTUPLE-0K7 xx1,xx2,xx3,xx4 ] implies y1 =HIDDENR1 xx1) implies y1 =HIDDENR1 x `1-4MCART-1K4\<^bsub>(X1,X2,X3,X4)\<^esub>"
sorry

mtheorem mcart_1_th_76:
" for y2 be objectHIDDENM1 holds  for X1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X2 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X3 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X4 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for x be ElementSUBSET-1M1-of [:ZFMISC-1K4 X1,X2,X3,X4 :] holds ( for xx1 be ElementSUBSET-1M1-of X1 holds  for xx2 be ElementSUBSET-1M1-of X2 holds  for xx3 be ElementSUBSET-1M1-of X3 holds  for xx4 be ElementSUBSET-1M1-of X4 holds x =HIDDENR1 [XTUPLE-0K7 xx1,xx2,xx3,xx4 ] implies y2 =HIDDENR1 xx2) implies y2 =HIDDENR1 x `2-4MCART-1K5\<^bsub>(X1,X2,X3,X4)\<^esub>"
sorry

mtheorem mcart_1_th_77:
" for y3 be objectHIDDENM1 holds  for X1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X2 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X3 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X4 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for x be ElementSUBSET-1M1-of [:ZFMISC-1K4 X1,X2,X3,X4 :] holds ( for xx1 be ElementSUBSET-1M1-of X1 holds  for xx2 be ElementSUBSET-1M1-of X2 holds  for xx3 be ElementSUBSET-1M1-of X3 holds  for xx4 be ElementSUBSET-1M1-of X4 holds x =HIDDENR1 [XTUPLE-0K7 xx1,xx2,xx3,xx4 ] implies y3 =HIDDENR1 xx3) implies y3 =HIDDENR1 x `3-4MCART-1K6\<^bsub>(X1,X2,X3,X4)\<^esub>"
sorry

mtheorem mcart_1_th_78:
" for y4 be objectHIDDENM1 holds  for X1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X2 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X3 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X4 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for x be ElementSUBSET-1M1-of [:ZFMISC-1K4 X1,X2,X3,X4 :] holds ( for xx1 be ElementSUBSET-1M1-of X1 holds  for xx2 be ElementSUBSET-1M1-of X2 holds  for xx3 be ElementSUBSET-1M1-of X3 holds  for xx4 be ElementSUBSET-1M1-of X4 holds x =HIDDENR1 [XTUPLE-0K7 xx1,xx2,xx3,xx4 ] implies y4 =HIDDENR1 xx4) implies y4 =HIDDENR1 x `4-4MCART-1K7\<^bsub>(X1,X2,X3,X4)\<^esub>"
sorry

mtheorem mcart_1_th_79:
" for z be objectHIDDENM1 holds  for X1 be setHIDDENM2 holds  for X2 be setHIDDENM2 holds  for X3 be setHIDDENM2 holds  for X4 be setHIDDENM2 holds z inHIDDENR3 [:ZFMISC-1K4 X1,X2,X3,X4 :] implies ( ex x1 be objectHIDDENM1 st  ex x2 be objectHIDDENM1 st  ex x3 be objectHIDDENM1 st  ex x4 be objectHIDDENM1 st (((x1 inHIDDENR3 X1 & x2 inHIDDENR3 X2) & x3 inHIDDENR3 X3) & x4 inHIDDENR3 X4) & z =HIDDENR1 [XTUPLE-0K7 x1,x2,x3,x4 ])"
sorry

mtheorem mcart_1_th_80:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for x4 be objectHIDDENM1 holds  for X1 be setHIDDENM2 holds  for X2 be setHIDDENM2 holds  for X3 be setHIDDENM2 holds  for X4 be setHIDDENM2 holds [XTUPLE-0K7 x1,x2,x3,x4 ] inHIDDENR3 [:ZFMISC-1K4 X1,X2,X3,X4 :] iff ((x1 inHIDDENR3 X1 & x2 inHIDDENR3 X2) & x3 inHIDDENR3 X3) & x4 inHIDDENR3 X4"
sorry

mtheorem mcart_1_th_81:
" for X1 be setHIDDENM2 holds  for X2 be setHIDDENM2 holds  for X3 be setHIDDENM2 holds  for X4 be setHIDDENM2 holds  for Z be setHIDDENM2 holds ( for z be objectHIDDENM1 holds z inHIDDENR3 Z iff ( ex x1 be objectHIDDENM1 st  ex x2 be objectHIDDENM1 st  ex x3 be objectHIDDENM1 st  ex x4 be objectHIDDENM1 st (((x1 inHIDDENR3 X1 & x2 inHIDDENR3 X2) & x3 inHIDDENR3 X3) & x4 inHIDDENR3 X4) & z =HIDDENR1 [XTUPLE-0K7 x1,x2,x3,x4 ])) implies Z =XBOOLE-0R4 [:ZFMISC-1K4 X1,X2,X3,X4 :]"
sorry

(*\$CT*)
mtheorem mcart_1_th_83:
" for X1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X2 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X3 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X4 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for A1 be  non emptyXBOOLE-0V1\<bar>SubsetSUBSET-1M2-of X1 holds  for A2 be  non emptyXBOOLE-0V1\<bar>SubsetSUBSET-1M2-of X2 holds  for A3 be  non emptyXBOOLE-0V1\<bar>SubsetSUBSET-1M2-of X3 holds  for A4 be  non emptyXBOOLE-0V1\<bar>SubsetSUBSET-1M2-of X4 holds  for x be ElementSUBSET-1M1-of [:ZFMISC-1K4 X1,X2,X3,X4 :] holds x inTARSKIR2 [:ZFMISC-1K4 A1,A2,A3,A4 :] implies ((x `1-4MCART-1K4\<^bsub>(X1,X2,X3,X4)\<^esub> inTARSKIR2 A1 & x `2-4MCART-1K5\<^bsub>(X1,X2,X3,X4)\<^esub> inTARSKIR2 A2) & x `3-4MCART-1K6\<^bsub>(X1,X2,X3,X4)\<^esub> inTARSKIR2 A3) & x `4-4MCART-1K7\<^bsub>(X1,X2,X3,X4)\<^esub> inTARSKIR2 A4"
sorry

mtheorem mcart_1_th_84:
" for X1 be setHIDDENM2 holds  for X2 be setHIDDENM2 holds  for X3 be setHIDDENM2 holds  for X4 be setHIDDENM2 holds  for Y1 be setHIDDENM2 holds  for Y2 be setHIDDENM2 holds  for Y3 be setHIDDENM2 holds  for Y4 be setHIDDENM2 holds ((X1 c=TARSKIR1 Y1 & X2 c=TARSKIR1 Y2) & X3 c=TARSKIR1 Y3) & X4 c=TARSKIR1 Y4 implies [:ZFMISC-1K4 X1,X2,X3,X4 :] c=TARSKIR1 [:ZFMISC-1K4 Y1,Y2,Y3,Y4 :]"
sorry

syntax MCART_1K8 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" ("[:MCART-1K8\<^bsub>'( _ , _ ')\<^esub> _ , _ :]" [0,0,0,0]164)
translations "[:MCART-1K8\<^bsub>(X1,X2)\<^esub> A1,A2 :]" \<rightharpoonup> "[:ZFMISC-1K2 A1,A2 :]"

mtheorem mcart_1_add_8:
  mlet "X1 be setHIDDENM2", "X2 be setHIDDENM2", "A1 be SubsetSUBSET-1M2-of X1", "A2 be SubsetSUBSET-1M2-of X2"
"cluster [:ZFMISC-1K2 A1,A2 :] as-term-is SubsetSUBSET-1M2-of [:ZFMISC-1K2 X1,X2 :]"
proof
(*coherence*)
  show "[:ZFMISC-1K2 A1,A2 :] be SubsetSUBSET-1M2-of [:ZFMISC-1K2 X1,X2 :]"
    using zfmisc_1_th_96 sorry
qed "sorry"

syntax MCART_1K9 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" ("[:MCART-1K9\<^bsub>'( _ , _ , _ ')\<^esub> _ , _ , _ :]" [0,0,0,0,0,0]164)
translations "[:MCART-1K9\<^bsub>(X1,X2,X3)\<^esub> A1,A2,A3 :]" \<rightharpoonup> "[:ZFMISC-1K3 A1,A2,A3 :]"

mtheorem mcart_1_add_9:
  mlet "X1 be setHIDDENM2", "X2 be setHIDDENM2", "X3 be setHIDDENM2", "A1 be SubsetSUBSET-1M2-of X1", "A2 be SubsetSUBSET-1M2-of X2", "A3 be SubsetSUBSET-1M2-of X3"
"cluster [:ZFMISC-1K3 A1,A2,A3 :] as-term-is SubsetSUBSET-1M2-of [:ZFMISC-1K3 X1,X2,X3 :]"
proof
(*coherence*)
  show "[:ZFMISC-1K3 A1,A2,A3 :] be SubsetSUBSET-1M2-of [:ZFMISC-1K3 X1,X2,X3 :]"
    using mcart_1_th_73 sorry
qed "sorry"

syntax MCART_1K10 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" ("[:MCART-1K10\<^bsub>'( _ , _ , _ , _ ')\<^esub> _ , _ , _ , _ :]" [0,0,0,0,0,0,0,0]164)
translations "[:MCART-1K10\<^bsub>(X1,X2,X3,X4)\<^esub> A1,A2,A3,A4 :]" \<rightharpoonup> "[:ZFMISC-1K4 A1,A2,A3,A4 :]"

mtheorem mcart_1_add_10:
  mlet "X1 be setHIDDENM2", "X2 be setHIDDENM2", "X3 be setHIDDENM2", "X4 be setHIDDENM2", "A1 be SubsetSUBSET-1M2-of X1", "A2 be SubsetSUBSET-1M2-of X2", "A3 be SubsetSUBSET-1M2-of X3", "A4 be SubsetSUBSET-1M2-of X4"
"cluster [:ZFMISC-1K4 A1,A2,A3,A4 :] as-term-is SubsetSUBSET-1M2-of [:ZFMISC-1K4 X1,X2,X3,X4 :]"
proof
(*coherence*)
  show "[:ZFMISC-1K4 A1,A2,A3,A4 :] be SubsetSUBSET-1M2-of [:ZFMISC-1K4 X1,X2,X3,X4 :]"
    using mcart_1_th_84 sorry
qed "sorry"

(*begin*)
mdef mcart_1_def_12 ("pr1MCART-1K11  _ " [228]228 ) where
  mlet "f be FunctionFUNCT-1M1"
"func pr1MCART-1K11 f \<rightarrow> FunctionFUNCT-1M1 means
  \<lambda>it. domRELAT-1K1 it =XBOOLE-0R4 domRELAT-1K1 f & ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 f implies it .FUNCT-1K1 x =HIDDENR1 (f .FUNCT-1K1 x)`1XTUPLE-0K1)"
proof-
  (*existence*)
    show " ex it be FunctionFUNCT-1M1 st domRELAT-1K1 it =XBOOLE-0R4 domRELAT-1K1 f & ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 f implies it .FUNCT-1K1 x =HIDDENR1 (f .FUNCT-1K1 x)`1XTUPLE-0K1)"
sorry
  (*uniqueness*)
    show " for it1 be FunctionFUNCT-1M1 holds  for it2 be FunctionFUNCT-1M1 holds (domRELAT-1K1 it1 =XBOOLE-0R4 domRELAT-1K1 f & ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 f implies it1 .FUNCT-1K1 x =HIDDENR1 (f .FUNCT-1K1 x)`1XTUPLE-0K1)) & (domRELAT-1K1 it2 =XBOOLE-0R4 domRELAT-1K1 f & ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 f implies it2 .FUNCT-1K1 x =HIDDENR1 (f .FUNCT-1K1 x)`1XTUPLE-0K1)) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mdef mcart_1_def_13 ("pr2MCART-1K12  _ " [228]228 ) where
  mlet "f be FunctionFUNCT-1M1"
"func pr2MCART-1K12 f \<rightarrow> FunctionFUNCT-1M1 means
  \<lambda>it. domRELAT-1K1 it =XBOOLE-0R4 domRELAT-1K1 f & ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 f implies it .FUNCT-1K1 x =HIDDENR1 (f .FUNCT-1K1 x)`2XTUPLE-0K2)"
proof-
  (*existence*)
    show " ex it be FunctionFUNCT-1M1 st domRELAT-1K1 it =XBOOLE-0R4 domRELAT-1K1 f & ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 f implies it .FUNCT-1K1 x =HIDDENR1 (f .FUNCT-1K1 x)`2XTUPLE-0K2)"
sorry
  (*uniqueness*)
    show " for it1 be FunctionFUNCT-1M1 holds  for it2 be FunctionFUNCT-1M1 holds (domRELAT-1K1 it1 =XBOOLE-0R4 domRELAT-1K1 f & ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 f implies it1 .FUNCT-1K1 x =HIDDENR1 (f .FUNCT-1K1 x)`2XTUPLE-0K2)) & (domRELAT-1K1 it2 =XBOOLE-0R4 domRELAT-1K1 f & ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 f implies it2 .FUNCT-1K1 x =HIDDENR1 (f .FUNCT-1K1 x)`2XTUPLE-0K2)) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mdef mcart_1_def_14 (" _ `11MCART-1K13" [355]355 ) where
  mlet "x be objectHIDDENM1"
"func x `11MCART-1K13 \<rightarrow> setHIDDENM2 equals
  (x `1XTUPLE-0K1)`1XTUPLE-0K1"
proof-
  (*coherence*)
    show "(x `1XTUPLE-0K1)`1XTUPLE-0K1 be setHIDDENM2"
      using tarski_th_1 sorry
qed "sorry"

mdef mcart_1_def_15 (" _ `12MCART-1K14" [355]355 ) where
  mlet "x be objectHIDDENM1"
"func x `12MCART-1K14 \<rightarrow> setHIDDENM2 equals
  (x `1XTUPLE-0K1)`2XTUPLE-0K2"
proof-
  (*coherence*)
    show "(x `1XTUPLE-0K1)`2XTUPLE-0K2 be setHIDDENM2"
      using tarski_th_1 sorry
qed "sorry"

mdef mcart_1_def_16 (" _ `21MCART-1K15" [355]355 ) where
  mlet "x be objectHIDDENM1"
"func x `21MCART-1K15 \<rightarrow> setHIDDENM2 equals
  (x `2XTUPLE-0K2)`1XTUPLE-0K1"
proof-
  (*coherence*)
    show "(x `2XTUPLE-0K2)`1XTUPLE-0K1 be setHIDDENM2"
      using tarski_th_1 sorry
qed "sorry"

mdef mcart_1_def_17 (" _ `22MCART-1K16" [355]355 ) where
  mlet "x be objectHIDDENM1"
"func x `22MCART-1K16 \<rightarrow> setHIDDENM2 equals
  (x `2XTUPLE-0K2)`2XTUPLE-0K2"
proof-
  (*coherence*)
    show "(x `2XTUPLE-0K2)`2XTUPLE-0K2 be setHIDDENM2"
      using tarski_th_1 sorry
qed "sorry"

reserve x for "objectHIDDENM1"
mtheorem mcart_1_th_85:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for y1 be objectHIDDENM1 holds  for y2 be objectHIDDENM1 holds  for x be objectHIDDENM1 holds (([TARSKIK4 [TARSKIK4 x1,x2 ],y ] `11MCART-1K13 =HIDDENR1 x1 & [TARSKIK4 [TARSKIK4 x1,x2 ],y ] `12MCART-1K14 =HIDDENR1 x2) & [TARSKIK4 x,[TARSKIK4 y1,y2 ] ] `21MCART-1K15 =HIDDENR1 y1) & [TARSKIK4 x,[TARSKIK4 y1,y2 ] ] `22MCART-1K16 =HIDDENR1 y2"
   sorry

mtheorem mcart_1_th_86:
" for R be RelationRELAT-1M1 holds  for x be objectHIDDENM1 holds x inHIDDENR3 R implies x `1XTUPLE-0K1 inHIDDENR3 domRELAT-1K1 R & x `2XTUPLE-0K2 inHIDDENR3 rngRELAT-1K2 R"
sorry

mtheorem mcart_1_th_87:
" for R be  non emptyXBOOLE-0V1\<bar>RelationRELAT-1M1 holds  for x be objectHIDDENM1 holds ImRELAT-1K12(R,x) =XBOOLE-0R4 {I `2XTUPLE-0K2 where I be ElementSUBSET-1M1-of R : I `1XTUPLE-0K1 =HIDDENR1 x }"
sorry

mtheorem mcart_1_th_88:
" for R be RelationRELAT-1M1 holds  for x be objectHIDDENM1 holds x inHIDDENR3 R implies x `2XTUPLE-0K2 inHIDDENR3 ImRELAT-1K12(R,x `1XTUPLE-0K1)"
sorry

mtheorem mcart_1_th_89:
" for y be objectHIDDENM1 holds  for R be RelationRELAT-1M1 holds  for x be objectHIDDENM1 holds ((x inHIDDENR3 R & y inHIDDENR3 R) & x `1XTUPLE-0K1 =HIDDENR1 y `1XTUPLE-0K1) & x `2XTUPLE-0K2 =HIDDENR1 y `2XTUPLE-0K2 implies x =HIDDENR1 y"
sorry

mtheorem mcart_1_th_90:
" for R be  non emptyXBOOLE-0V1\<bar>RelationRELAT-1M1 holds  for x be ElementSUBSET-1M1-of R holds  for y be ElementSUBSET-1M1-of R holds x `1XTUPLE-0K1 =HIDDENR1 y `1XTUPLE-0K1 & x `2XTUPLE-0K2 =HIDDENR1 y `2XTUPLE-0K2 implies x =XBOOLE-0R4 y"
  using mcart_1_th_89 sorry

mtheorem mcart_1_th_91:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for y1 be objectHIDDENM1 holds  for y2 be objectHIDDENM1 holds  for y3 be objectHIDDENM1 holds proj1XTUPLE-0K12 (proj1XTUPLE-0K12 {TARSKIK2 [XTUPLE-0K3 x1,x2,x3 ],[XTUPLE-0K3 y1,y2,y3 ] }) =XBOOLE-0R4 {TARSKIK2 x1,y1 }"
sorry

mtheorem mcart_1_th_92:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds proj1XTUPLE-0K12 (proj1XTUPLE-0K12 {TARSKIK1 [XTUPLE-0K3 x1,x2,x3 ] }) =XBOOLE-0R4 {TARSKIK1 x1}"
sorry

theorem mcart_1_sch_1:
  fixes Af0 Bf0 Cf0 Pp3 
  assumes
[ty]: "Af0 be setHIDDENM2" and
  [ty]: "Bf0 be setHIDDENM2" and
  [ty]: "Cf0 be setHIDDENM2" and
   A1: " for x be objectHIDDENM1 holds x inHIDDENR3 Af0 implies ( ex y be objectHIDDENM1 st  ex z be objectHIDDENM1 st (y inHIDDENR3 Bf0 & z inHIDDENR3 Cf0) & Pp3(x,y,z))"
  shows " ex f be FunctionFUNCT-1M1 st  ex g be FunctionFUNCT-1M1 st (domRELAT-1K1 f =XBOOLE-0R4 Af0 & domRELAT-1K1 g =XBOOLE-0R4 Af0) & ( for x be objectHIDDENM1 holds x inHIDDENR3 Af0 implies Pp3(x,f .FUNCT-1K1 x,g .FUNCT-1K1 x))"
sorry

mtheorem mcart_1_th_93:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for x4 be objectHIDDENM1 holds  for y1 be objectHIDDENM1 holds  for y2 be objectHIDDENM1 holds  for y3 be objectHIDDENM1 holds  for y4 be objectHIDDENM1 holds [TARSKIK4 [TARSKIK4 x1,x2 ],[TARSKIK4 x3,x4 ] ] =HIDDENR1 [TARSKIK4 [TARSKIK4 y1,y2 ],[TARSKIK4 y3,y4 ] ] implies ((x1 =HIDDENR1 y1 & x2 =HIDDENR1 y2) & x3 =HIDDENR1 y3) & x4 =HIDDENR1 y4"
sorry

end
