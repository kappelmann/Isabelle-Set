theory domain_1
  imports ordinal1 mcart_1 partfun1
begin
(*begin*)
reserve a, b, c, d for "setHIDDENM2"
reserve D, X1, X2, X3, X4 for " non emptyXBOOLE-0V1\<bar>setHIDDENM2"
reserve x1, y1, z1 for "ElementSUBSET-1M1-of X1"
reserve x2 for "ElementSUBSET-1M1-of X2"
reserve x3 for "ElementSUBSET-1M1-of X3"
reserve x4 for "ElementSUBSET-1M1-of X4"
reserve A1, B1 for "SubsetSUBSET-1M2-of X1"
mtheorem domain_1_th_1:
" for a be setHIDDENM2 holds  for X1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X2 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds a inTARSKIR2 [:ZFMISC-1K2 X1,X2 :] implies ( ex x1 be ElementSUBSET-1M1-of X1 st  ex x2 be ElementSUBSET-1M1-of X2 st a =HIDDENR1 [TARSKIK4 x1,x2 ])"
sorry

mtheorem domain_1_th_2:
" for X1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X2 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for x be ElementSUBSET-1M1-of [:ZFMISC-1K2 X1,X2 :] holds  for y be ElementSUBSET-1M1-of [:ZFMISC-1K2 X1,X2 :] holds x `1XTUPLE-0K1 =HIDDENR1 y `1XTUPLE-0K1 & x `2XTUPLE-0K2 =HIDDENR1 y `2XTUPLE-0K2 implies x =XBOOLE-0R4 y"
sorry

syntax DOMAIN_1K1 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" ("[DOMAIN-1K1\<^bsub>'( _ , _ ')\<^esub> _ , _ ]" [0,0,0,0]356)
translations "[DOMAIN-1K1\<^bsub>(X1,X2)\<^esub> x1,x2 ]" \<rightharpoonup> "[TARSKIK4 x1,x2 ]"

mtheorem domain_1_add_1:
  mlet "X1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "X2 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "x1 be ElementSUBSET-1M1-of X1", "x2 be ElementSUBSET-1M1-of X2"
"cluster [TARSKIK4 x1,x2 ] as-term-is ElementSUBSET-1M1-of [:ZFMISC-1K2 X1,X2 :]"
proof
(*coherence*)
  show "[TARSKIK4 x1,x2 ] be ElementSUBSET-1M1-of [:ZFMISC-1K2 X1,X2 :]"
    using zfmisc_1_th_87 sorry
qed "sorry"

syntax DOMAIN_1K2 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ `1DOMAIN-1K2\<^bsub>'( _ , _ ')\<^esub>" [355,0,0]355)
translations "x `1DOMAIN-1K2\<^bsub>(X1,X2)\<^esub>" \<rightharpoonup> "x `1XTUPLE-0K1"

mtheorem domain_1_add_2:
  mlet "X1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "X2 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "x be ElementSUBSET-1M1-of [:ZFMISC-1K2 X1,X2 :]"
"cluster x `1XTUPLE-0K1 as-term-is ElementSUBSET-1M1-of X1"
proof
(*coherence*)
  show "x `1XTUPLE-0K1 be ElementSUBSET-1M1-of X1"
    using mcart_1_th_10 sorry
qed "sorry"

syntax DOMAIN_1K3 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ `2DOMAIN-1K3\<^bsub>'( _ , _ ')\<^esub>" [355,0,0]355)
translations "x `2DOMAIN-1K3\<^bsub>(X1,X2)\<^esub>" \<rightharpoonup> "x `2XTUPLE-0K2"

mtheorem domain_1_add_3:
  mlet "X1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "X2 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "x be ElementSUBSET-1M1-of [:ZFMISC-1K2 X1,X2 :]"
"cluster x `2XTUPLE-0K2 as-term-is ElementSUBSET-1M1-of X2"
proof
(*coherence*)
  show "x `2XTUPLE-0K2 be ElementSUBSET-1M1-of X2"
    using mcart_1_th_10 sorry
qed "sorry"

mtheorem domain_1_th_3:
" for a be setHIDDENM2 holds  for X1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X2 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X3 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds a inTARSKIR2 [:ZFMISC-1K3 X1,X2,X3 :] iff ( ex x1 be ElementSUBSET-1M1-of X1 st  ex x2 be ElementSUBSET-1M1-of X2 st  ex x3 be ElementSUBSET-1M1-of X3 st a =HIDDENR1 [XTUPLE-0K3 x1,x2,x3 ])"
sorry

mtheorem domain_1_th_4:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X2 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X3 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds ( for a be setHIDDENM2 holds a inTARSKIR2 D iff ( ex x1 be ElementSUBSET-1M1-of X1 st  ex x2 be ElementSUBSET-1M1-of X2 st  ex x3 be ElementSUBSET-1M1-of X3 st a =HIDDENR1 [XTUPLE-0K3 x1,x2,x3 ])) implies D =XBOOLE-0R4 [:ZFMISC-1K3 X1,X2,X3 :]"
sorry

mtheorem domain_1_th_5:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X2 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X3 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds D =XBOOLE-0R4 [:ZFMISC-1K3 X1,X2,X3 :] iff ( for a be setHIDDENM2 holds a inTARSKIR2 D iff ( ex x1 be ElementSUBSET-1M1-of X1 st  ex x2 be ElementSUBSET-1M1-of X2 st  ex x3 be ElementSUBSET-1M1-of X3 st a =HIDDENR1 [XTUPLE-0K3 x1,x2,x3 ]))"
  using domain_1_th_3 domain_1_th_4 sorry

reserve x, y for "ElementSUBSET-1M1-of [:ZFMISC-1K3 X1,X2,X3 :]"
syntax DOMAIN_1K4 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" ("[DOMAIN-1K4\<^bsub>'( _ , _ , _ ')\<^esub> _ , _ , _ ]" [0,0,0,0,0,0]356)
translations "[DOMAIN-1K4\<^bsub>(X1,X2,X3)\<^esub> x1,x2,x3 ]" \<rightharpoonup> "[XTUPLE-0K3 x1,x2,x3 ]"

mtheorem domain_1_add_4:
  mlet "X1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "X2 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "X3 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "x1 be ElementSUBSET-1M1-of X1", "x2 be ElementSUBSET-1M1-of X2", "x3 be ElementSUBSET-1M1-of X3"
"cluster [XTUPLE-0K3 x1,x2,x3 ] as-term-is ElementSUBSET-1M1-of [:ZFMISC-1K3 X1,X2,X3 :]"
proof
(*coherence*)
  show "[XTUPLE-0K3 x1,x2,x3 ] be ElementSUBSET-1M1-of [:ZFMISC-1K3 X1,X2,X3 :]"
    using mcart_1_th_69 sorry
qed "sorry"

mtheorem domain_1_th_6:
" for a be setHIDDENM2 holds  for X1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X2 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X3 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for x be ElementSUBSET-1M1-of [:ZFMISC-1K3 X1,X2,X3 :] holds a =XBOOLE-0R4 x `1-3MCART-1K1\<^bsub>(X1,X2,X3)\<^esub> iff ( for x1 be ElementSUBSET-1M1-of X1 holds  for x2 be ElementSUBSET-1M1-of X2 holds  for x3 be ElementSUBSET-1M1-of X3 holds x =XBOOLE-0R4 [DOMAIN-1K4\<^bsub>(X1,X2,X3)\<^esub> x1,x2,x3 ] implies a =XBOOLE-0R4 x1)"
  using mcart_1_th_65 sorry

mtheorem domain_1_th_7:
" for b be setHIDDENM2 holds  for X1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X2 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X3 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for x be ElementSUBSET-1M1-of [:ZFMISC-1K3 X1,X2,X3 :] holds b =XBOOLE-0R4 x `2-3MCART-1K2\<^bsub>(X1,X2,X3)\<^esub> iff ( for x1 be ElementSUBSET-1M1-of X1 holds  for x2 be ElementSUBSET-1M1-of X2 holds  for x3 be ElementSUBSET-1M1-of X3 holds x =XBOOLE-0R4 [DOMAIN-1K4\<^bsub>(X1,X2,X3)\<^esub> x1,x2,x3 ] implies b =XBOOLE-0R4 x2)"
  using mcart_1_th_66 sorry

mtheorem domain_1_th_8:
" for c be setHIDDENM2 holds  for X1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X2 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X3 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for x be ElementSUBSET-1M1-of [:ZFMISC-1K3 X1,X2,X3 :] holds c =XBOOLE-0R4 x `3-3MCART-1K3\<^bsub>(X1,X2,X3)\<^esub> iff ( for x1 be ElementSUBSET-1M1-of X1 holds  for x2 be ElementSUBSET-1M1-of X2 holds  for x3 be ElementSUBSET-1M1-of X3 holds x =XBOOLE-0R4 [DOMAIN-1K4\<^bsub>(X1,X2,X3)\<^esub> x1,x2,x3 ] implies c =XBOOLE-0R4 x3)"
  using mcart_1_th_67 sorry

mlemma domain_1_lm_1:
" for X1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X2 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X3 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for x be ElementSUBSET-1M1-of [:ZFMISC-1K3 X1,X2,X3 :] holds x =XBOOLE-0R4 [DOMAIN-1K4\<^bsub>(X1,X2,X3)\<^esub> x `1-3MCART-1K1\<^bsub>(X1,X2,X3)\<^esub>,x `2-3MCART-1K2\<^bsub>(X1,X2,X3)\<^esub>,x `3-3MCART-1K3\<^bsub>(X1,X2,X3)\<^esub> ]"
   sorry

mtheorem domain_1_th_9:
" for X1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X2 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X3 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for x be ElementSUBSET-1M1-of [:ZFMISC-1K3 X1,X2,X3 :] holds  for y be ElementSUBSET-1M1-of [:ZFMISC-1K3 X1,X2,X3 :] holds (x `1-3MCART-1K1\<^bsub>(X1,X2,X3)\<^esub> =XBOOLE-0R4 y `1-3MCART-1K1\<^bsub>(X1,X2,X3)\<^esub> & x `2-3MCART-1K2\<^bsub>(X1,X2,X3)\<^esub> =XBOOLE-0R4 y `2-3MCART-1K2\<^bsub>(X1,X2,X3)\<^esub>) & x `3-3MCART-1K3\<^bsub>(X1,X2,X3)\<^esub> =XBOOLE-0R4 y `3-3MCART-1K3\<^bsub>(X1,X2,X3)\<^esub> implies x =XBOOLE-0R4 y"
sorry

mtheorem domain_1_th_10:
" for a be setHIDDENM2 holds  for X1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X2 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X3 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X4 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds a inTARSKIR2 [:ZFMISC-1K4 X1,X2,X3,X4 :] iff ( ex x1 be ElementSUBSET-1M1-of X1 st  ex x2 be ElementSUBSET-1M1-of X2 st  ex x3 be ElementSUBSET-1M1-of X3 st  ex x4 be ElementSUBSET-1M1-of X4 st a =HIDDENR1 [XTUPLE-0K7 x1,x2,x3,x4 ])"
sorry

mtheorem domain_1_th_11:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X2 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X3 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X4 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds ( for a be setHIDDENM2 holds a inTARSKIR2 D iff ( ex x1 be ElementSUBSET-1M1-of X1 st  ex x2 be ElementSUBSET-1M1-of X2 st  ex x3 be ElementSUBSET-1M1-of X3 st  ex x4 be ElementSUBSET-1M1-of X4 st a =HIDDENR1 [XTUPLE-0K7 x1,x2,x3,x4 ])) implies D =XBOOLE-0R4 [:ZFMISC-1K4 X1,X2,X3,X4 :]"
sorry

mtheorem domain_1_th_12:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X2 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X3 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X4 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds D =XBOOLE-0R4 [:ZFMISC-1K4 X1,X2,X3,X4 :] iff ( for a be setHIDDENM2 holds a inTARSKIR2 D iff ( ex x1 be ElementSUBSET-1M1-of X1 st  ex x2 be ElementSUBSET-1M1-of X2 st  ex x3 be ElementSUBSET-1M1-of X3 st  ex x4 be ElementSUBSET-1M1-of X4 st a =HIDDENR1 [XTUPLE-0K7 x1,x2,x3,x4 ]))"
  using domain_1_th_10 domain_1_th_11 sorry

reserve x for "ElementSUBSET-1M1-of [:ZFMISC-1K4 X1,X2,X3,X4 :]"
syntax DOMAIN_1K5 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" ("[DOMAIN-1K5\<^bsub>'( _ , _ , _ , _ ')\<^esub> _ , _ , _ , _ ]" [0,0,0,0,0,0,0,0]356)
translations "[DOMAIN-1K5\<^bsub>(X1,X2,X3,X4)\<^esub> x1,x2,x3,x4 ]" \<rightharpoonup> "[XTUPLE-0K7 x1,x2,x3,x4 ]"

mtheorem domain_1_add_5:
  mlet "X1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "X2 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "X3 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "X4 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "x1 be ElementSUBSET-1M1-of X1", "x2 be ElementSUBSET-1M1-of X2", "x3 be ElementSUBSET-1M1-of X3", "x4 be ElementSUBSET-1M1-of X4"
"cluster [XTUPLE-0K7 x1,x2,x3,x4 ] as-term-is ElementSUBSET-1M1-of [:ZFMISC-1K4 X1,X2,X3,X4 :]"
proof
(*coherence*)
  show "[XTUPLE-0K7 x1,x2,x3,x4 ] be ElementSUBSET-1M1-of [:ZFMISC-1K4 X1,X2,X3,X4 :]"
    using mcart_1_th_80 sorry
qed "sorry"

mtheorem domain_1_th_13:
" for a be setHIDDENM2 holds  for X1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X2 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X3 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X4 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for x be ElementSUBSET-1M1-of [:ZFMISC-1K4 X1,X2,X3,X4 :] holds a =XBOOLE-0R4 x `1-4MCART-1K4\<^bsub>(X1,X2,X3,X4)\<^esub> iff ( for x1 be ElementSUBSET-1M1-of X1 holds  for x2 be ElementSUBSET-1M1-of X2 holds  for x3 be ElementSUBSET-1M1-of X3 holds  for x4 be ElementSUBSET-1M1-of X4 holds x =XBOOLE-0R4 [DOMAIN-1K5\<^bsub>(X1,X2,X3,X4)\<^esub> x1,x2,x3,x4 ] implies a =XBOOLE-0R4 x1)"
  using mcart_1_th_75 sorry

mtheorem domain_1_th_14:
" for b be setHIDDENM2 holds  for X1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X2 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X3 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X4 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for x be ElementSUBSET-1M1-of [:ZFMISC-1K4 X1,X2,X3,X4 :] holds b =XBOOLE-0R4 x `2-4MCART-1K5\<^bsub>(X1,X2,X3,X4)\<^esub> iff ( for x1 be ElementSUBSET-1M1-of X1 holds  for x2 be ElementSUBSET-1M1-of X2 holds  for x3 be ElementSUBSET-1M1-of X3 holds  for x4 be ElementSUBSET-1M1-of X4 holds x =XBOOLE-0R4 [DOMAIN-1K5\<^bsub>(X1,X2,X3,X4)\<^esub> x1,x2,x3,x4 ] implies b =XBOOLE-0R4 x2)"
  using mcart_1_th_76 sorry

mtheorem domain_1_th_15:
" for c be setHIDDENM2 holds  for X1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X2 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X3 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X4 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for x be ElementSUBSET-1M1-of [:ZFMISC-1K4 X1,X2,X3,X4 :] holds c =XBOOLE-0R4 x `3-4MCART-1K6\<^bsub>(X1,X2,X3,X4)\<^esub> iff ( for x1 be ElementSUBSET-1M1-of X1 holds  for x2 be ElementSUBSET-1M1-of X2 holds  for x3 be ElementSUBSET-1M1-of X3 holds  for x4 be ElementSUBSET-1M1-of X4 holds x =XBOOLE-0R4 [DOMAIN-1K5\<^bsub>(X1,X2,X3,X4)\<^esub> x1,x2,x3,x4 ] implies c =XBOOLE-0R4 x3)"
  using mcart_1_th_77 sorry

mtheorem domain_1_th_16:
" for d be setHIDDENM2 holds  for X1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X2 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X3 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X4 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for x be ElementSUBSET-1M1-of [:ZFMISC-1K4 X1,X2,X3,X4 :] holds d =XBOOLE-0R4 x `4-4MCART-1K7\<^bsub>(X1,X2,X3,X4)\<^esub> iff ( for x1 be ElementSUBSET-1M1-of X1 holds  for x2 be ElementSUBSET-1M1-of X2 holds  for x3 be ElementSUBSET-1M1-of X3 holds  for x4 be ElementSUBSET-1M1-of X4 holds x =XBOOLE-0R4 [DOMAIN-1K5\<^bsub>(X1,X2,X3,X4)\<^esub> x1,x2,x3,x4 ] implies d =XBOOLE-0R4 x4)"
  using mcart_1_th_78 sorry

mlemma domain_1_lm_2:
" for X1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X2 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X3 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X4 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for x be ElementSUBSET-1M1-of [:ZFMISC-1K4 X1,X2,X3,X4 :] holds x =XBOOLE-0R4 [DOMAIN-1K5\<^bsub>(X1,X2,X3,X4)\<^esub> x `1-4MCART-1K4\<^bsub>(X1,X2,X3,X4)\<^esub>,x `2-4MCART-1K5\<^bsub>(X1,X2,X3,X4)\<^esub>,x `3-4MCART-1K6\<^bsub>(X1,X2,X3,X4)\<^esub>,x `4-4MCART-1K7\<^bsub>(X1,X2,X3,X4)\<^esub> ]"
   sorry

mtheorem domain_1_th_17:
" for X1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X2 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X3 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X4 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for x be ElementSUBSET-1M1-of [:ZFMISC-1K4 X1,X2,X3,X4 :] holds  for y be ElementSUBSET-1M1-of [:ZFMISC-1K4 X1,X2,X3,X4 :] holds ((x `1-4MCART-1K4\<^bsub>(X1,X2,X3,X4)\<^esub> =XBOOLE-0R4 y `1-4MCART-1K4\<^bsub>(X1,X2,X3,X4)\<^esub> & x `2-4MCART-1K5\<^bsub>(X1,X2,X3,X4)\<^esub> =XBOOLE-0R4 y `2-4MCART-1K5\<^bsub>(X1,X2,X3,X4)\<^esub>) & x `3-4MCART-1K6\<^bsub>(X1,X2,X3,X4)\<^esub> =XBOOLE-0R4 y `3-4MCART-1K6\<^bsub>(X1,X2,X3,X4)\<^esub>) & x `4-4MCART-1K7\<^bsub>(X1,X2,X3,X4)\<^esub> =XBOOLE-0R4 y `4-4MCART-1K7\<^bsub>(X1,X2,X3,X4)\<^esub> implies x =XBOOLE-0R4 y"
sorry

reserve A2 for "SubsetSUBSET-1M2-of X2"
reserve A3 for "SubsetSUBSET-1M2-of X3"
reserve A4 for "SubsetSUBSET-1M2-of X4"
theorem domain_1_sch_1:
  fixes Pp1 
  shows " for X1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds {x1 where x1 be ElementSUBSET-1M1-of X1 : Pp1(x1) } be SubsetSUBSET-1M2-of X1"
sorry

theorem domain_1_sch_2:
  fixes Pp2 
  shows " for X1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X2 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds {[DOMAIN-1K1\<^bsub>(X1,X2)\<^esub> x1,x2 ] where x1 be ElementSUBSET-1M1-of X1, x2 be ElementSUBSET-1M1-of X2 : Pp2(x1,x2) } be SubsetSUBSET-1M2-of [:ZFMISC-1K2 X1,X2 :]"
sorry

theorem domain_1_sch_3:
  fixes Pp3 
  shows " for X1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X2 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X3 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds {[DOMAIN-1K4\<^bsub>(X1,X2,X3)\<^esub> x1,x2,x3 ] where x1 be ElementSUBSET-1M1-of X1, x2 be ElementSUBSET-1M1-of X2, x3 be ElementSUBSET-1M1-of X3 : Pp3(x1,x2,x3) } be SubsetSUBSET-1M2-of [:ZFMISC-1K3 X1,X2,X3 :]"
sorry

theorem domain_1_sch_4:
  fixes Pp4 
  shows " for X1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X2 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X3 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X4 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds {[DOMAIN-1K5\<^bsub>(X1,X2,X3,X4)\<^esub> x1,x2,x3,x4 ] where x1 be ElementSUBSET-1M1-of X1, x2 be ElementSUBSET-1M1-of X2, x3 be ElementSUBSET-1M1-of X3, x4 be ElementSUBSET-1M1-of X4 : Pp4(x1,x2,x3,x4) } be SubsetSUBSET-1M2-of [:ZFMISC-1K4 X1,X2,X3,X4 :]"
sorry

theorem domain_1_sch_5:
  fixes Pp1 Qp1 
  shows " for X1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds ( for x1 be ElementSUBSET-1M1-of X1 holds Pp1(x1) implies Qp1(x1)) implies {y1 where y1 be ElementSUBSET-1M1-of X1 : Pp1(y1) } c=TARSKIR1 {z1 where z1 be ElementSUBSET-1M1-of X1 : Qp1(z1) }"
sorry

theorem domain_1_sch_6:
  fixes Pp1 Qp1 
  shows " for X1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds ( for x1 be ElementSUBSET-1M1-of X1 holds Pp1(x1) iff Qp1(x1)) implies {y1 where y1 be ElementSUBSET-1M1-of X1 : Pp1(y1) } =XBOOLE-0R4 {z1 where z1 be ElementSUBSET-1M1-of X1 : Qp1(z1) }"
sorry

theorem domain_1_sch_7:
  fixes Df0 Pp1 
  assumes
[ty]: "Df0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
  shows "{d where d be ElementSUBSET-1M1-of Df0 : Pp1(d) } be SubsetSUBSET-1M2-of Df0"
sorry

mtheorem domain_1_th_18:
" for X1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds X1 =XBOOLE-0R4 {x1 where x1 be ElementSUBSET-1M1-of X1 :  True  }"
sorry

mtheorem domain_1_th_19:
" for X1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X2 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds [:ZFMISC-1K2 X1,X2 :] =XBOOLE-0R4 {[DOMAIN-1K1\<^bsub>(X1,X2)\<^esub> x1,x2 ] where x1 be ElementSUBSET-1M1-of X1, x2 be ElementSUBSET-1M1-of X2 :  True  }"
sorry

mtheorem domain_1_th_20:
" for X1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X2 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X3 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds [:ZFMISC-1K3 X1,X2,X3 :] =XBOOLE-0R4 {[DOMAIN-1K4\<^bsub>(X1,X2,X3)\<^esub> x1,x2,x3 ] where x1 be ElementSUBSET-1M1-of X1, x2 be ElementSUBSET-1M1-of X2, x3 be ElementSUBSET-1M1-of X3 :  True  }"
sorry

mtheorem domain_1_th_21:
" for X1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X2 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X3 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X4 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds [:ZFMISC-1K4 X1,X2,X3,X4 :] =XBOOLE-0R4 {[DOMAIN-1K5\<^bsub>(X1,X2,X3,X4)\<^esub> x1,x2,x3,x4 ] where x1 be ElementSUBSET-1M1-of X1, x2 be ElementSUBSET-1M1-of X2, x3 be ElementSUBSET-1M1-of X3, x4 be ElementSUBSET-1M1-of X4 :  True  }"
sorry

mtheorem domain_1_th_22:
" for X1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for A1 be SubsetSUBSET-1M2-of X1 holds A1 =XBOOLE-0R4 {x1 where x1 be ElementSUBSET-1M1-of X1 : x1 inTARSKIR2 A1 }"
sorry

mtheorem domain_1_th_23:
" for X1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X2 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for A1 be SubsetSUBSET-1M2-of X1 holds  for A2 be SubsetSUBSET-1M2-of X2 holds [:MCART-1K8\<^bsub>(X1,X2)\<^esub> A1,A2 :] =XBOOLE-0R4 {[DOMAIN-1K1\<^bsub>(X1,X2)\<^esub> x1,x2 ] where x1 be ElementSUBSET-1M1-of X1, x2 be ElementSUBSET-1M1-of X2 : x1 inTARSKIR2 A1 & x2 inTARSKIR2 A2 }"
sorry

mtheorem domain_1_th_24:
" for X1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X2 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X3 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for A1 be SubsetSUBSET-1M2-of X1 holds  for A2 be SubsetSUBSET-1M2-of X2 holds  for A3 be SubsetSUBSET-1M2-of X3 holds [:MCART-1K9\<^bsub>(X1,X2,X3)\<^esub> A1,A2,A3 :] =XBOOLE-0R4 {[DOMAIN-1K4\<^bsub>(X1,X2,X3)\<^esub> x1,x2,x3 ] where x1 be ElementSUBSET-1M1-of X1, x2 be ElementSUBSET-1M1-of X2, x3 be ElementSUBSET-1M1-of X3 : (x1 inTARSKIR2 A1 & x2 inTARSKIR2 A2) & x3 inTARSKIR2 A3 }"
sorry

mtheorem domain_1_th_25:
" for X1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X2 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X3 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X4 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for A1 be SubsetSUBSET-1M2-of X1 holds  for A2 be SubsetSUBSET-1M2-of X2 holds  for A3 be SubsetSUBSET-1M2-of X3 holds  for A4 be SubsetSUBSET-1M2-of X4 holds [:MCART-1K10\<^bsub>(X1,X2,X3,X4)\<^esub> A1,A2,A3,A4 :] =XBOOLE-0R4 {[DOMAIN-1K5\<^bsub>(X1,X2,X3,X4)\<^esub> x1,x2,x3,x4 ] where x1 be ElementSUBSET-1M1-of X1, x2 be ElementSUBSET-1M1-of X2, x3 be ElementSUBSET-1M1-of X3, x4 be ElementSUBSET-1M1-of X4 : ((x1 inTARSKIR2 A1 & x2 inTARSKIR2 A2) & x3 inTARSKIR2 A3) & x4 inTARSKIR2 A4 }"
sorry

mtheorem domain_1_th_26:
" for X1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds {}SUBSET-1K1 X1 =XBOOLE-0R4 {x1 where x1 be ElementSUBSET-1M1-of X1 :  False  }"
sorry

mtheorem domain_1_th_27:
" for X1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for A1 be SubsetSUBSET-1M2-of X1 holds A1 `SUBSET-1K3\<^bsub>(X1)\<^esub> =XBOOLE-0R4 {x1 where x1 be ElementSUBSET-1M1-of X1 :  not x1 inTARSKIR2 A1 }"
sorry

mtheorem domain_1_th_28:
" for X1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for A1 be SubsetSUBSET-1M2-of X1 holds  for B1 be SubsetSUBSET-1M2-of X1 holds A1 /\\SUBSET-1K9\<^bsub>(X1)\<^esub> B1 =XBOOLE-0R4 {x1 where x1 be ElementSUBSET-1M1-of X1 : x1 inTARSKIR2 A1 & x1 inTARSKIR2 B1 }"
sorry

mtheorem domain_1_th_29:
" for X1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for A1 be SubsetSUBSET-1M2-of X1 holds  for B1 be SubsetSUBSET-1M2-of X1 holds A1 \\/SUBSET-1K4\<^bsub>(X1)\<^esub> B1 =XBOOLE-0R4 {x1 where x1 be ElementSUBSET-1M1-of X1 : x1 inTARSKIR2 A1 or x1 inTARSKIR2 B1 }"
sorry

mtheorem domain_1_th_30:
" for X1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for A1 be SubsetSUBSET-1M2-of X1 holds  for B1 be SubsetSUBSET-1M2-of X1 holds A1 \\SUBSET-1K7\<^bsub>(X1)\<^esub> B1 =XBOOLE-0R4 {x1 where x1 be ElementSUBSET-1M1-of X1 : x1 inTARSKIR2 A1 &  not x1 inTARSKIR2 B1 }"
sorry

mtheorem domain_1_th_31:
" for X1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for A1 be SubsetSUBSET-1M2-of X1 holds  for B1 be SubsetSUBSET-1M2-of X1 holds A1 \\+\\SUBSET-1K5\<^bsub>(X1)\<^esub> B1 =XBOOLE-0R4 {x1 where x1 be ElementSUBSET-1M1-of X1 : x1 inTARSKIR2 A1 &  not x1 inTARSKIR2 B1 or  not x1 inTARSKIR2 A1 & x1 inTARSKIR2 B1 }"
sorry

mtheorem domain_1_th_32:
" for X1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for A1 be SubsetSUBSET-1M2-of X1 holds  for B1 be SubsetSUBSET-1M2-of X1 holds A1 \\+\\SUBSET-1K5\<^bsub>(X1)\<^esub> B1 =XBOOLE-0R4 {x1 where x1 be ElementSUBSET-1M1-of X1 :  not x1 inTARSKIR2 A1 iff x1 inTARSKIR2 B1 }"
sorry

mtheorem domain_1_th_33:
" for X1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for A1 be SubsetSUBSET-1M2-of X1 holds  for B1 be SubsetSUBSET-1M2-of X1 holds A1 \\+\\SUBSET-1K5\<^bsub>(X1)\<^esub> B1 =XBOOLE-0R4 {x1 where x1 be ElementSUBSET-1M1-of X1 : x1 inTARSKIR2 A1 iff  not x1 inTARSKIR2 B1 }"
sorry

mtheorem domain_1_th_34:
" for X1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for A1 be SubsetSUBSET-1M2-of X1 holds  for B1 be SubsetSUBSET-1M2-of X1 holds A1 \\+\\SUBSET-1K5\<^bsub>(X1)\<^esub> B1 =XBOOLE-0R4 {x1 where x1 be ElementSUBSET-1M1-of X1 :  not (x1 inTARSKIR2 A1 iff x1 inTARSKIR2 B1) }"
sorry

syntax DOMAIN_1K6 :: " Set \<Rightarrow>  Set \<Rightarrow> Set" ("{DOMAIN-1K6\<^bsub>'( _ ')\<^esub>  _ }" [0,0]356)
translations "{DOMAIN-1K6\<^bsub>(D)\<^esub> x1}" \<rightharpoonup> "{TARSKIK1 x1}"

mtheorem domain_1_add_6:
  mlet "D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "x1 be ElementSUBSET-1M1-of D"
"cluster {TARSKIK1 x1} as-term-is SubsetSUBSET-1M2-of D"
proof
(*coherence*)
  show "{TARSKIK1 x1} be SubsetSUBSET-1M2-of D"
    using subset_1_th_33 sorry
qed "sorry"

syntax DOMAIN_1K7 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" ("{DOMAIN-1K7\<^bsub>'( _ ')\<^esub> _ , _ }" [0,0,0]356)
translations "{DOMAIN-1K7\<^bsub>(D)\<^esub> x1,x2 }" \<rightharpoonup> "{TARSKIK2 x1,x2 }"

mtheorem domain_1_add_7:
  mlet "D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "x1 be ElementSUBSET-1M1-of D", "x2 be ElementSUBSET-1M1-of D"
"cluster {TARSKIK2 x1,x2 } as-term-is SubsetSUBSET-1M2-of D"
proof
(*coherence*)
  show "{TARSKIK2 x1,x2 } be SubsetSUBSET-1M2-of D"
    using subset_1_th_34 sorry
qed "sorry"

syntax DOMAIN_1K8 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" ("{DOMAIN-1K8\<^bsub>'( _ ')\<^esub> _ , _ , _ }" [0,0,0,0]356)
translations "{DOMAIN-1K8\<^bsub>(D)\<^esub> x1,x2,x3 }" \<rightharpoonup> "{ENUMSET1K1 x1,x2,x3 }"

mtheorem domain_1_add_8:
  mlet "D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "x1 be ElementSUBSET-1M1-of D", "x2 be ElementSUBSET-1M1-of D", "x3 be ElementSUBSET-1M1-of D"
"cluster {ENUMSET1K1 x1,x2,x3 } as-term-is SubsetSUBSET-1M2-of D"
proof
(*coherence*)
  show "{ENUMSET1K1 x1,x2,x3 } be SubsetSUBSET-1M2-of D"
    using subset_1_th_35 sorry
qed "sorry"

syntax DOMAIN_1K9 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" ("{DOMAIN-1K9\<^bsub>'( _ ')\<^esub> _ , _ , _ , _ }" [0,0,0,0,0]356)
translations "{DOMAIN-1K9\<^bsub>(D)\<^esub> x1,x2,x3,x4 }" \<rightharpoonup> "{ENUMSET1K2 x1,x2,x3,x4 }"

mtheorem domain_1_add_9:
  mlet "D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "x1 be ElementSUBSET-1M1-of D", "x2 be ElementSUBSET-1M1-of D", "x3 be ElementSUBSET-1M1-of D", "x4 be ElementSUBSET-1M1-of D"
"cluster {ENUMSET1K2 x1,x2,x3,x4 } as-term-is SubsetSUBSET-1M2-of D"
proof
(*coherence*)
  show "{ENUMSET1K2 x1,x2,x3,x4 } be SubsetSUBSET-1M2-of D"
    using subset_1_th_36 sorry
qed "sorry"

syntax DOMAIN_1K10 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" ("{DOMAIN-1K10\<^bsub>'( _ ')\<^esub> _ , _ , _ , _ , _ }" [0,0,0,0,0,0]356)
translations "{DOMAIN-1K10\<^bsub>(D)\<^esub> x1,x2,x3,x4,x5 }" \<rightharpoonup> "{ENUMSET1K3 x1,x2,x3,x4,x5 }"

mtheorem domain_1_add_10:
  mlet "D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "x1 be ElementSUBSET-1M1-of D", "x2 be ElementSUBSET-1M1-of D", "x3 be ElementSUBSET-1M1-of D", "x4 be ElementSUBSET-1M1-of D", "x5 be ElementSUBSET-1M1-of D"
"cluster {ENUMSET1K3 x1,x2,x3,x4,x5 } as-term-is SubsetSUBSET-1M2-of D"
proof
(*coherence*)
  show "{ENUMSET1K3 x1,x2,x3,x4,x5 } be SubsetSUBSET-1M2-of D"
    using subset_1_th_37 sorry
qed "sorry"

syntax DOMAIN_1K11 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" ("{DOMAIN-1K11\<^bsub>'( _ ')\<^esub> _ , _ , _ , _ , _ , _ }" [0,0,0,0,0,0,0]356)
translations "{DOMAIN-1K11\<^bsub>(D)\<^esub> x1,x2,x3,x4,x5,x6 }" \<rightharpoonup> "{ENUMSET1K4 x1,x2,x3,x4,x5,x6 }"

mtheorem domain_1_add_11:
  mlet "D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "x1 be ElementSUBSET-1M1-of D", "x2 be ElementSUBSET-1M1-of D", "x3 be ElementSUBSET-1M1-of D", "x4 be ElementSUBSET-1M1-of D", "x5 be ElementSUBSET-1M1-of D", "x6 be ElementSUBSET-1M1-of D"
"cluster {ENUMSET1K4 x1,x2,x3,x4,x5,x6 } as-term-is SubsetSUBSET-1M2-of D"
proof
(*coherence*)
  show "{ENUMSET1K4 x1,x2,x3,x4,x5,x6 } be SubsetSUBSET-1M2-of D"
    using subset_1_th_38 sorry
qed "sorry"

syntax DOMAIN_1K12 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" ("{DOMAIN-1K12\<^bsub>'( _ ')\<^esub> _ , _ , _ , _ , _ , _ , _ }" [0,0,0,0,0,0,0,0]356)
translations "{DOMAIN-1K12\<^bsub>(D)\<^esub> x1,x2,x3,x4,x5,x6,x7 }" \<rightharpoonup> "{ENUMSET1K5 x1,x2,x3,x4,x5,x6,x7 }"

mtheorem domain_1_add_12:
  mlet "D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "x1 be ElementSUBSET-1M1-of D", "x2 be ElementSUBSET-1M1-of D", "x3 be ElementSUBSET-1M1-of D", "x4 be ElementSUBSET-1M1-of D", "x5 be ElementSUBSET-1M1-of D", "x6 be ElementSUBSET-1M1-of D", "x7 be ElementSUBSET-1M1-of D"
"cluster {ENUMSET1K5 x1,x2,x3,x4,x5,x6,x7 } as-term-is SubsetSUBSET-1M2-of D"
proof
(*coherence*)
  show "{ENUMSET1K5 x1,x2,x3,x4,x5,x6,x7 } be SubsetSUBSET-1M2-of D"
    using subset_1_th_39 sorry
qed "sorry"

syntax DOMAIN_1K13 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" ("{DOMAIN-1K13\<^bsub>'( _ ')\<^esub> _ , _ , _ , _ , _ , _ , _ , _ }" [0,0,0,0,0,0,0,0,0]356)
translations "{DOMAIN-1K13\<^bsub>(D)\<^esub> x1,x2,x3,x4,x5,x6,x7,x8 }" \<rightharpoonup> "{ENUMSET1K6 x1,x2,x3,x4,x5,x6,x7,x8 }"

mtheorem domain_1_add_13:
  mlet "D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "x1 be ElementSUBSET-1M1-of D", "x2 be ElementSUBSET-1M1-of D", "x3 be ElementSUBSET-1M1-of D", "x4 be ElementSUBSET-1M1-of D", "x5 be ElementSUBSET-1M1-of D", "x6 be ElementSUBSET-1M1-of D", "x7 be ElementSUBSET-1M1-of D", "x8 be ElementSUBSET-1M1-of D"
"cluster {ENUMSET1K6 x1,x2,x3,x4,x5,x6,x7,x8 } as-term-is SubsetSUBSET-1M2-of D"
proof
(*coherence*)
  show "{ENUMSET1K6 x1,x2,x3,x4,x5,x6,x7,x8 } be SubsetSUBSET-1M2-of D"
    using subset_1_th_40 sorry
qed "sorry"

(*begin*)
theorem domain_1_sch_8:
  fixes Af0 Df0 Ff1 Pp1 
  assumes
[ty]: "Af0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
  [ty]: "Df0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
  [ty_func]: "\<And> x1. x1 be objectHIDDENM1 \<Longrightarrow> Ff1(x1) be ElementSUBSET-1M1-of Df0"
  shows "{Ff1(x) where x be ElementSUBSET-1M1-of Af0 : Pp1(x) } be SubsetSUBSET-1M2-of Df0"
sorry

theorem domain_1_sch_9:
  fixes Af0 Bf0 Df0 Ff2 Pp2 
  assumes
[ty]: "Af0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
  [ty]: "Bf0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
  [ty]: "Df0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
  [ty_func]: "\<And> x1 x2. x1 be objectHIDDENM1 \<Longrightarrow> x2 be objectHIDDENM1 \<Longrightarrow> Ff2(x1,x2) be ElementSUBSET-1M1-of Df0"
  shows "{Ff2(x,y) where x be ElementSUBSET-1M1-of Af0, y be ElementSUBSET-1M1-of Bf0 : Pp2(x,y) } be SubsetSUBSET-1M2-of Df0"
sorry

syntax DOMAIN_1K14 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ `11DOMAIN-1K14\<^bsub>'( _ , _ , _ ')\<^esub>" [355,0,0,0]355)
translations "x `11DOMAIN-1K14\<^bsub>(D1,D2,D3)\<^esub>" \<rightharpoonup> "x `11MCART-1K13"

mtheorem domain_1_add_14:
  mlet "D1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "D2 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "D3 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "x be ElementSUBSET-1M1-of [:ZFMISC-1K2 [:ZFMISC-1K2 D1,D2 :],D3 :]"
"cluster x `11MCART-1K13 as-term-is ElementSUBSET-1M1-of D1"
proof
(*coherence*)
  show "x `11MCART-1K13 be ElementSUBSET-1M1-of D1"
sorry
qed "sorry"

syntax DOMAIN_1K15 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ `12DOMAIN-1K15\<^bsub>'( _ , _ , _ ')\<^esub>" [355,0,0,0]355)
translations "x `12DOMAIN-1K15\<^bsub>(D1,D2,D3)\<^esub>" \<rightharpoonup> "x `12MCART-1K14"

mtheorem domain_1_add_15:
  mlet "D1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "D2 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "D3 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "x be ElementSUBSET-1M1-of [:ZFMISC-1K2 [:ZFMISC-1K2 D1,D2 :],D3 :]"
"cluster x `12MCART-1K14 as-term-is ElementSUBSET-1M1-of D2"
proof
(*coherence*)
  show "x `12MCART-1K14 be ElementSUBSET-1M1-of D2"
sorry
qed "sorry"

syntax DOMAIN_1K16 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ `21DOMAIN-1K16\<^bsub>'( _ , _ , _ ')\<^esub>" [355,0,0,0]355)
translations "x `21DOMAIN-1K16\<^bsub>(D1,D2,D3)\<^esub>" \<rightharpoonup> "x `21MCART-1K15"

mtheorem domain_1_add_16:
  mlet "D1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "D2 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "D3 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "x be ElementSUBSET-1M1-of [:ZFMISC-1K2 D1,[:ZFMISC-1K2 D2,D3 :] :]"
"cluster x `21MCART-1K15 as-term-is ElementSUBSET-1M1-of D2"
proof
(*coherence*)
  show "x `21MCART-1K15 be ElementSUBSET-1M1-of D2"
sorry
qed "sorry"

syntax DOMAIN_1K17 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ `22DOMAIN-1K17\<^bsub>'( _ , _ , _ ')\<^esub>" [355,0,0,0]355)
translations "x `22DOMAIN-1K17\<^bsub>(D1,D2,D3)\<^esub>" \<rightharpoonup> "x `22MCART-1K16"

mtheorem domain_1_add_17:
  mlet "D1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "D2 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "D3 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "x be ElementSUBSET-1M1-of [:ZFMISC-1K2 D1,[:ZFMISC-1K2 D2,D3 :] :]"
"cluster x `22MCART-1K16 as-term-is ElementSUBSET-1M1-of D3"
proof
(*coherence*)
  show "x `22MCART-1K16 be ElementSUBSET-1M1-of D3"
sorry
qed "sorry"

theorem domain_1_sch_10:
  fixes Af0 Pp1 Qp1 
  assumes
[ty]: "Af0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
  shows "{a where a be ElementSUBSET-1M1-of Af0 : Pp1(a) & Qp1(a) } =XBOOLE-0R4 ({a1 where a1 be ElementSUBSET-1M1-of Af0 : Pp1(a1) })/\\XBOOLE-0K3 ({a2 where a2 be ElementSUBSET-1M1-of Af0 : Qp1(a2) })"
sorry

mtheorem domain_1_cl_1:
  mlet "A be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster c=-linearORDINAL1V6\<bar> non emptyXBOOLE-0V1 for SubsetSUBSET-1M2-of A"
proof
(*existence*)
  show " ex it be SubsetSUBSET-1M2-of A st it be c=-linearORDINAL1V6\<bar> non emptyXBOOLE-0V1"
sorry
qed "sorry"

end
