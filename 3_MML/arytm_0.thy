theory arytm_0
  imports arytm_1 numbers
   "../mizar_extension/E_number"
begin
(*begin*)
mlemma arytm_0_lm_1:
" for x be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds [TARSKIK4 0NUMBERSK6,x ] inHIDDENR3 [:ZFMISC-1K2 {TARSKIK1 0NUMBERSK6 },REAL+ARYTM-2K2 :]"
sorry

mtheorem arytm_0_th_1:
"REAL+ARYTM-2K2 c=TARSKIR1 REALNUMBERSK2"
sorry

mtheorem arytm_0_th_2:
" for x be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds x <>HIDDENR2 {}ARYTM-3K12 implies [TARSKIK4 {}ARYTM-3K12,x ] inHIDDENR3 REALNUMBERSK2"
sorry

mtheorem arytm_0_th_3:
" for y be setHIDDENM2 holds [TARSKIK4 {}ARYTM-3K12,y ] inHIDDENR3 REALNUMBERSK2 implies y <>HIDDENR2 {}ARYTM-3K12"
sorry

mtheorem arytm_0_th_4:
" for x be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for y be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds x -ARYTM-1K2 y inTARSKIR2 REALNUMBERSK2"
sorry

mtheorem arytm_0_th_5:
"REAL+ARYTM-2K2 missesXBOOLE-0R1 [:ZFMISC-1K2 {TARSKIK1 {}ARYTM-3K12 },REAL+ARYTM-2K2 :]"
sorry

(*begin*)
mtheorem arytm_0_cl_1:
  mlet "x be objectHIDDENM1", "y be objectHIDDENM1"
"cluster [TARSKIK4 x,y ] as-term-is  non zeroORDINAL1V8"
proof
(*coherence*)
  show "[TARSKIK4 x,y ] be  non zeroORDINAL1V8"
     sorry
qed "sorry"

mtheorem arytm_0_th_6:
" for x be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for y be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds x -ARYTM-1K2 y =XBOOLE-0R4 {}ARYTM-3K12 implies x =XBOOLE-0R4 y"
sorry

mlemma arytm_0_lm_2:
" not ( ex a be setHIDDENM2 st  ex b be setHIDDENM2 st \<one>\<^sub>M =HIDDENR1 [TARSKIK4 a,b ])"
sorry

mtheorem arytm_0_th_7:
" for x be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for y be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for z be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds x <>HIDDENR2 {}ARYTM-3K12 & x *'ARYTM-2K8 y =XBOOLE-0R4 x *'ARYTM-2K8 z implies y =XBOOLE-0R4 z"
sorry

(*begin*)
mlemma arytm_0_lm_3:
"0NUMBERSK6 inTARSKIR2 REALNUMBERSK2"
  using numbers_th_19 sorry

mdef arytm_0_def_1 ("+ARYTM-0K1'( _ , _ ')" [0,0]132 ) where
  mlet "x be ElementSUBSET-1M1-of REALNUMBERSK2", "y be ElementSUBSET-1M1-of REALNUMBERSK2"
"func +ARYTM-0K1(x,y) \<rightarrow> ElementSUBSET-1M1-of REALNUMBERSK2 means
  \<lambda>it.  ex x9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st  ex y9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st (x =XBOOLE-0R4 x9 & y =XBOOLE-0R4 y9) & it =XBOOLE-0R4 x9 +ARYTM-2K7 y9 if x inTARSKIR2 REAL+ARYTM-2K2 & y inTARSKIR2 REAL+ARYTM-2K2,
  \<lambda>it.  ex x9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st  ex y9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st (x =XBOOLE-0R4 x9 & y =HIDDENR1 [TARSKIK4 0NUMBERSK6,y9 ]) & it =XBOOLE-0R4 x9 -ARYTM-1K2 y9 if x inTARSKIR2 REAL+ARYTM-2K2 & y inTARSKIR2 [:ZFMISC-1K2 {TARSKIK1 0NUMBERSK6 },REAL+ARYTM-2K2 :],
  \<lambda>it.  ex x9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st  ex y9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st (x =HIDDENR1 [TARSKIK4 0NUMBERSK6,x9 ] & y =XBOOLE-0R4 y9) & it =XBOOLE-0R4 y9 -ARYTM-1K2 x9 if y inTARSKIR2 REAL+ARYTM-2K2 & x inTARSKIR2 [:ZFMISC-1K2 {TARSKIK1 0NUMBERSK6 },REAL+ARYTM-2K2 :] otherwise \<lambda>it.  ex x9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st  ex y9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st (x =HIDDENR1 [TARSKIK4 0NUMBERSK6,x9 ] & y =HIDDENR1 [TARSKIK4 0NUMBERSK6,y9 ]) & it =HIDDENR1 [TARSKIK4 0NUMBERSK6,x9 +ARYTM-2K7 y9 ]"
proof-
  (*existence*)
    show "(x inTARSKIR2 REAL+ARYTM-2K2 & y inTARSKIR2 REAL+ARYTM-2K2 implies ( ex it be ElementSUBSET-1M1-of REALNUMBERSK2 st  ex x9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st  ex y9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st (x =XBOOLE-0R4 x9 & y =XBOOLE-0R4 y9) & it =XBOOLE-0R4 x9 +ARYTM-2K7 y9)) & ((x inTARSKIR2 REAL+ARYTM-2K2 & y inTARSKIR2 [:ZFMISC-1K2 {TARSKIK1 0NUMBERSK6 },REAL+ARYTM-2K2 :] implies ( ex it be ElementSUBSET-1M1-of REALNUMBERSK2 st  ex x9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st  ex y9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st (x =XBOOLE-0R4 x9 & y =HIDDENR1 [TARSKIK4 0NUMBERSK6,y9 ]) & it =XBOOLE-0R4 x9 -ARYTM-1K2 y9)) & ((y inTARSKIR2 REAL+ARYTM-2K2 & x inTARSKIR2 [:ZFMISC-1K2 {TARSKIK1 0NUMBERSK6 },REAL+ARYTM-2K2 :] implies ( ex it be ElementSUBSET-1M1-of REALNUMBERSK2 st  ex x9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st  ex y9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st (x =HIDDENR1 [TARSKIK4 0NUMBERSK6,x9 ] & y =XBOOLE-0R4 y9) & it =XBOOLE-0R4 y9 -ARYTM-1K2 x9)) & ( not (x inTARSKIR2 REAL+ARYTM-2K2 & y inTARSKIR2 REAL+ARYTM-2K2) & ( not (x inTARSKIR2 REAL+ARYTM-2K2 & y inTARSKIR2 [:ZFMISC-1K2 {TARSKIK1 0NUMBERSK6 },REAL+ARYTM-2K2 :]) &  not (y inTARSKIR2 REAL+ARYTM-2K2 & x inTARSKIR2 [:ZFMISC-1K2 {TARSKIK1 0NUMBERSK6 },REAL+ARYTM-2K2 :])) implies ( ex it be ElementSUBSET-1M1-of REALNUMBERSK2 st  ex x9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st  ex y9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st (x =HIDDENR1 [TARSKIK4 0NUMBERSK6,x9 ] & y =HIDDENR1 [TARSKIK4 0NUMBERSK6,y9 ]) & it =HIDDENR1 [TARSKIK4 0NUMBERSK6,x9 +ARYTM-2K7 y9 ]))))"
sorry
  (*uniqueness*)
    show " for it1 be ElementSUBSET-1M1-of REALNUMBERSK2 holds  for it2 be ElementSUBSET-1M1-of REALNUMBERSK2 holds (x inTARSKIR2 REAL+ARYTM-2K2 & y inTARSKIR2 REAL+ARYTM-2K2 implies (( ex x9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st  ex y9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st (x =XBOOLE-0R4 x9 & y =XBOOLE-0R4 y9) & it1 =XBOOLE-0R4 x9 +ARYTM-2K7 y9) & ( ex x9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st  ex y9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st (x =XBOOLE-0R4 x9 & y =XBOOLE-0R4 y9) & it2 =XBOOLE-0R4 x9 +ARYTM-2K7 y9) implies it1 =HIDDENR1 it2)) & ((x inTARSKIR2 REAL+ARYTM-2K2 & y inTARSKIR2 [:ZFMISC-1K2 {TARSKIK1 0NUMBERSK6 },REAL+ARYTM-2K2 :] implies (( ex x9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st  ex y9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st (x =XBOOLE-0R4 x9 & y =HIDDENR1 [TARSKIK4 0NUMBERSK6,y9 ]) & it1 =XBOOLE-0R4 x9 -ARYTM-1K2 y9) & ( ex x9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st  ex y9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st (x =XBOOLE-0R4 x9 & y =HIDDENR1 [TARSKIK4 0NUMBERSK6,y9 ]) & it2 =XBOOLE-0R4 x9 -ARYTM-1K2 y9) implies it1 =HIDDENR1 it2)) & ((y inTARSKIR2 REAL+ARYTM-2K2 & x inTARSKIR2 [:ZFMISC-1K2 {TARSKIK1 0NUMBERSK6 },REAL+ARYTM-2K2 :] implies (( ex x9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st  ex y9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st (x =HIDDENR1 [TARSKIK4 0NUMBERSK6,x9 ] & y =XBOOLE-0R4 y9) & it1 =XBOOLE-0R4 y9 -ARYTM-1K2 x9) & ( ex x9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st  ex y9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st (x =HIDDENR1 [TARSKIK4 0NUMBERSK6,x9 ] & y =XBOOLE-0R4 y9) & it2 =XBOOLE-0R4 y9 -ARYTM-1K2 x9) implies it1 =HIDDENR1 it2)) & ( not (x inTARSKIR2 REAL+ARYTM-2K2 & y inTARSKIR2 REAL+ARYTM-2K2) & ( not (x inTARSKIR2 REAL+ARYTM-2K2 & y inTARSKIR2 [:ZFMISC-1K2 {TARSKIK1 0NUMBERSK6 },REAL+ARYTM-2K2 :]) &  not (y inTARSKIR2 REAL+ARYTM-2K2 & x inTARSKIR2 [:ZFMISC-1K2 {TARSKIK1 0NUMBERSK6 },REAL+ARYTM-2K2 :])) implies (( ex x9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st  ex y9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st (x =HIDDENR1 [TARSKIK4 0NUMBERSK6,x9 ] & y =HIDDENR1 [TARSKIK4 0NUMBERSK6,y9 ]) & it1 =HIDDENR1 [TARSKIK4 0NUMBERSK6,x9 +ARYTM-2K7 y9 ]) & ( ex x9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st  ex y9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st (x =HIDDENR1 [TARSKIK4 0NUMBERSK6,x9 ] & y =HIDDENR1 [TARSKIK4 0NUMBERSK6,y9 ]) & it2 =HIDDENR1 [TARSKIK4 0NUMBERSK6,x9 +ARYTM-2K7 y9 ]) implies it1 =HIDDENR1 it2))))"
sorry
  (*consistency*)
    show " for it be ElementSUBSET-1M1-of REALNUMBERSK2 holds (((x inTARSKIR2 REAL+ARYTM-2K2 & y inTARSKIR2 REAL+ARYTM-2K2) & (x inTARSKIR2 REAL+ARYTM-2K2 & y inTARSKIR2 [:ZFMISC-1K2 {TARSKIK1 0NUMBERSK6 },REAL+ARYTM-2K2 :]) implies (( ex x9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st  ex y9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st (x =XBOOLE-0R4 x9 & y =XBOOLE-0R4 y9) & it =XBOOLE-0R4 x9 +ARYTM-2K7 y9) iff ( ex x9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st  ex y9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st (x =XBOOLE-0R4 x9 & y =HIDDENR1 [TARSKIK4 0NUMBERSK6,y9 ]) & it =XBOOLE-0R4 x9 -ARYTM-1K2 y9))) & ((x inTARSKIR2 REAL+ARYTM-2K2 & y inTARSKIR2 REAL+ARYTM-2K2) & (y inTARSKIR2 REAL+ARYTM-2K2 & x inTARSKIR2 [:ZFMISC-1K2 {TARSKIK1 0NUMBERSK6 },REAL+ARYTM-2K2 :]) implies (( ex x9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st  ex y9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st (x =XBOOLE-0R4 x9 & y =XBOOLE-0R4 y9) & it =XBOOLE-0R4 x9 +ARYTM-2K7 y9) iff ( ex x9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st  ex y9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st (x =HIDDENR1 [TARSKIK4 0NUMBERSK6,x9 ] & y =XBOOLE-0R4 y9) & it =XBOOLE-0R4 y9 -ARYTM-1K2 x9)))) & ((x inTARSKIR2 REAL+ARYTM-2K2 & y inTARSKIR2 [:ZFMISC-1K2 {TARSKIK1 0NUMBERSK6 },REAL+ARYTM-2K2 :]) & (y inTARSKIR2 REAL+ARYTM-2K2 & x inTARSKIR2 [:ZFMISC-1K2 {TARSKIK1 0NUMBERSK6 },REAL+ARYTM-2K2 :]) implies (( ex x9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st  ex y9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st (x =XBOOLE-0R4 x9 & y =HIDDENR1 [TARSKIK4 0NUMBERSK6,y9 ]) & it =XBOOLE-0R4 x9 -ARYTM-1K2 y9) iff ( ex x9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st  ex y9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st (x =HIDDENR1 [TARSKIK4 0NUMBERSK6,x9 ] & y =XBOOLE-0R4 y9) & it =XBOOLE-0R4 y9 -ARYTM-1K2 x9)))"
      using arytm_0_th_5 xboole_0_th_3 sorry
qed "sorry"

mtheorem ARYTM_0K1_commutativity:
" for x be ElementSUBSET-1M1-of REALNUMBERSK2 holds  for y be ElementSUBSET-1M1-of REALNUMBERSK2 holds +ARYTM-0K1(x,y) =HIDDENR1 +ARYTM-0K1(y,x)"
sorry

mdef arytm_0_def_2 (" *ARYTM-0K2'( _ , _ ')" [0,0]164 ) where
  mlet "x be ElementSUBSET-1M1-of REALNUMBERSK2", "y be ElementSUBSET-1M1-of REALNUMBERSK2"
"func  *ARYTM-0K2(x,y) \<rightarrow> ElementSUBSET-1M1-of REALNUMBERSK2 means
  \<lambda>it.  ex x9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st  ex y9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st (x =XBOOLE-0R4 x9 & y =XBOOLE-0R4 y9) & it =XBOOLE-0R4 x9 *'ARYTM-2K8 y9 if x inTARSKIR2 REAL+ARYTM-2K2 & y inTARSKIR2 REAL+ARYTM-2K2,
  \<lambda>it.  ex x9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st  ex y9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st (x =XBOOLE-0R4 x9 & y =HIDDENR1 [TARSKIK4 0NUMBERSK6,y9 ]) & it =HIDDENR1 [TARSKIK4 0NUMBERSK6,x9 *'ARYTM-2K8 y9 ] if (x inTARSKIR2 REAL+ARYTM-2K2 & y inTARSKIR2 [:ZFMISC-1K2 {TARSKIK1 0NUMBERSK6 },REAL+ARYTM-2K2 :]) & x <>HIDDENR2 0NUMBERSK6,
  \<lambda>it.  ex x9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st  ex y9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st (x =HIDDENR1 [TARSKIK4 0NUMBERSK6,x9 ] & y =XBOOLE-0R4 y9) & it =HIDDENR1 [TARSKIK4 0NUMBERSK6,y9 *'ARYTM-2K8 x9 ] if (y inTARSKIR2 REAL+ARYTM-2K2 & x inTARSKIR2 [:ZFMISC-1K2 {TARSKIK1 0NUMBERSK6 },REAL+ARYTM-2K2 :]) & y <>HIDDENR2 0NUMBERSK6,
  \<lambda>it.  ex x9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st  ex y9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st (x =HIDDENR1 [TARSKIK4 0NUMBERSK6,x9 ] & y =HIDDENR1 [TARSKIK4 0NUMBERSK6,y9 ]) & it =XBOOLE-0R4 y9 *'ARYTM-2K8 x9 if x inTARSKIR2 [:ZFMISC-1K2 {TARSKIK1 0NUMBERSK6 },REAL+ARYTM-2K2 :] & y inTARSKIR2 [:ZFMISC-1K2 {TARSKIK1 0NUMBERSK6 },REAL+ARYTM-2K2 :] otherwise \<lambda>it. it =XBOOLE-0R4 0NUMBERSK6"
proof-
  (*existence*)
    show "(x inTARSKIR2 REAL+ARYTM-2K2 & y inTARSKIR2 REAL+ARYTM-2K2 implies ( ex it be ElementSUBSET-1M1-of REALNUMBERSK2 st  ex x9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st  ex y9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st (x =XBOOLE-0R4 x9 & y =XBOOLE-0R4 y9) & it =XBOOLE-0R4 x9 *'ARYTM-2K8 y9)) & (((x inTARSKIR2 REAL+ARYTM-2K2 & y inTARSKIR2 [:ZFMISC-1K2 {TARSKIK1 0NUMBERSK6 },REAL+ARYTM-2K2 :]) & x <>HIDDENR2 0NUMBERSK6 implies ( ex it be ElementSUBSET-1M1-of REALNUMBERSK2 st  ex x9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st  ex y9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st (x =XBOOLE-0R4 x9 & y =HIDDENR1 [TARSKIK4 0NUMBERSK6,y9 ]) & it =HIDDENR1 [TARSKIK4 0NUMBERSK6,x9 *'ARYTM-2K8 y9 ])) & (((y inTARSKIR2 REAL+ARYTM-2K2 & x inTARSKIR2 [:ZFMISC-1K2 {TARSKIK1 0NUMBERSK6 },REAL+ARYTM-2K2 :]) & y <>HIDDENR2 0NUMBERSK6 implies ( ex it be ElementSUBSET-1M1-of REALNUMBERSK2 st  ex x9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st  ex y9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st (x =HIDDENR1 [TARSKIK4 0NUMBERSK6,x9 ] & y =XBOOLE-0R4 y9) & it =HIDDENR1 [TARSKIK4 0NUMBERSK6,y9 *'ARYTM-2K8 x9 ])) & ((x inTARSKIR2 [:ZFMISC-1K2 {TARSKIK1 0NUMBERSK6 },REAL+ARYTM-2K2 :] & y inTARSKIR2 [:ZFMISC-1K2 {TARSKIK1 0NUMBERSK6 },REAL+ARYTM-2K2 :] implies ( ex it be ElementSUBSET-1M1-of REALNUMBERSK2 st  ex x9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st  ex y9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st (x =HIDDENR1 [TARSKIK4 0NUMBERSK6,x9 ] & y =HIDDENR1 [TARSKIK4 0NUMBERSK6,y9 ]) & it =XBOOLE-0R4 y9 *'ARYTM-2K8 x9)) & ( not (x inTARSKIR2 REAL+ARYTM-2K2 & y inTARSKIR2 REAL+ARYTM-2K2) & ( not ((x inTARSKIR2 REAL+ARYTM-2K2 & y inTARSKIR2 [:ZFMISC-1K2 {TARSKIK1 0NUMBERSK6 },REAL+ARYTM-2K2 :]) & x <>HIDDENR2 0NUMBERSK6) & ( not ((y inTARSKIR2 REAL+ARYTM-2K2 & x inTARSKIR2 [:ZFMISC-1K2 {TARSKIK1 0NUMBERSK6 },REAL+ARYTM-2K2 :]) & y <>HIDDENR2 0NUMBERSK6) &  not (x inTARSKIR2 [:ZFMISC-1K2 {TARSKIK1 0NUMBERSK6 },REAL+ARYTM-2K2 :] & y inTARSKIR2 [:ZFMISC-1K2 {TARSKIK1 0NUMBERSK6 },REAL+ARYTM-2K2 :]))) implies ( ex it be ElementSUBSET-1M1-of REALNUMBERSK2 st it =XBOOLE-0R4 0NUMBERSK6)))))"
sorry
  (*uniqueness*)
    show " for it1 be ElementSUBSET-1M1-of REALNUMBERSK2 holds  for it2 be ElementSUBSET-1M1-of REALNUMBERSK2 holds (x inTARSKIR2 REAL+ARYTM-2K2 & y inTARSKIR2 REAL+ARYTM-2K2 implies (( ex x9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st  ex y9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st (x =XBOOLE-0R4 x9 & y =XBOOLE-0R4 y9) & it1 =XBOOLE-0R4 x9 *'ARYTM-2K8 y9) & ( ex x9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st  ex y9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st (x =XBOOLE-0R4 x9 & y =XBOOLE-0R4 y9) & it2 =XBOOLE-0R4 x9 *'ARYTM-2K8 y9) implies it1 =HIDDENR1 it2)) & (((x inTARSKIR2 REAL+ARYTM-2K2 & y inTARSKIR2 [:ZFMISC-1K2 {TARSKIK1 0NUMBERSK6 },REAL+ARYTM-2K2 :]) & x <>HIDDENR2 0NUMBERSK6 implies (( ex x9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st  ex y9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st (x =XBOOLE-0R4 x9 & y =HIDDENR1 [TARSKIK4 0NUMBERSK6,y9 ]) & it1 =HIDDENR1 [TARSKIK4 0NUMBERSK6,x9 *'ARYTM-2K8 y9 ]) & ( ex x9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st  ex y9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st (x =XBOOLE-0R4 x9 & y =HIDDENR1 [TARSKIK4 0NUMBERSK6,y9 ]) & it2 =HIDDENR1 [TARSKIK4 0NUMBERSK6,x9 *'ARYTM-2K8 y9 ]) implies it1 =HIDDENR1 it2)) & (((y inTARSKIR2 REAL+ARYTM-2K2 & x inTARSKIR2 [:ZFMISC-1K2 {TARSKIK1 0NUMBERSK6 },REAL+ARYTM-2K2 :]) & y <>HIDDENR2 0NUMBERSK6 implies (( ex x9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st  ex y9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st (x =HIDDENR1 [TARSKIK4 0NUMBERSK6,x9 ] & y =XBOOLE-0R4 y9) & it1 =HIDDENR1 [TARSKIK4 0NUMBERSK6,y9 *'ARYTM-2K8 x9 ]) & ( ex x9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st  ex y9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st (x =HIDDENR1 [TARSKIK4 0NUMBERSK6,x9 ] & y =XBOOLE-0R4 y9) & it2 =HIDDENR1 [TARSKIK4 0NUMBERSK6,y9 *'ARYTM-2K8 x9 ]) implies it1 =HIDDENR1 it2)) & ((x inTARSKIR2 [:ZFMISC-1K2 {TARSKIK1 0NUMBERSK6 },REAL+ARYTM-2K2 :] & y inTARSKIR2 [:ZFMISC-1K2 {TARSKIK1 0NUMBERSK6 },REAL+ARYTM-2K2 :] implies (( ex x9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st  ex y9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st (x =HIDDENR1 [TARSKIK4 0NUMBERSK6,x9 ] & y =HIDDENR1 [TARSKIK4 0NUMBERSK6,y9 ]) & it1 =XBOOLE-0R4 y9 *'ARYTM-2K8 x9) & ( ex x9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st  ex y9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st (x =HIDDENR1 [TARSKIK4 0NUMBERSK6,x9 ] & y =HIDDENR1 [TARSKIK4 0NUMBERSK6,y9 ]) & it2 =XBOOLE-0R4 y9 *'ARYTM-2K8 x9) implies it1 =HIDDENR1 it2)) & ( not (x inTARSKIR2 REAL+ARYTM-2K2 & y inTARSKIR2 REAL+ARYTM-2K2) & ( not ((x inTARSKIR2 REAL+ARYTM-2K2 & y inTARSKIR2 [:ZFMISC-1K2 {TARSKIK1 0NUMBERSK6 },REAL+ARYTM-2K2 :]) & x <>HIDDENR2 0NUMBERSK6) & ( not ((y inTARSKIR2 REAL+ARYTM-2K2 & x inTARSKIR2 [:ZFMISC-1K2 {TARSKIK1 0NUMBERSK6 },REAL+ARYTM-2K2 :]) & y <>HIDDENR2 0NUMBERSK6) &  not (x inTARSKIR2 [:ZFMISC-1K2 {TARSKIK1 0NUMBERSK6 },REAL+ARYTM-2K2 :] & y inTARSKIR2 [:ZFMISC-1K2 {TARSKIK1 0NUMBERSK6 },REAL+ARYTM-2K2 :]))) implies (it1 =XBOOLE-0R4 0NUMBERSK6 & it2 =XBOOLE-0R4 0NUMBERSK6 implies it1 =HIDDENR1 it2)))))"
sorry
  (*consistency*)
    show " for it be ElementSUBSET-1M1-of REALNUMBERSK2 holds ((((((x inTARSKIR2 REAL+ARYTM-2K2 & y inTARSKIR2 REAL+ARYTM-2K2) & ((x inTARSKIR2 REAL+ARYTM-2K2 & y inTARSKIR2 [:ZFMISC-1K2 {TARSKIK1 0NUMBERSK6 },REAL+ARYTM-2K2 :]) & x <>HIDDENR2 0NUMBERSK6) implies (( ex x9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st  ex y9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st (x =XBOOLE-0R4 x9 & y =XBOOLE-0R4 y9) & it =XBOOLE-0R4 x9 *'ARYTM-2K8 y9) iff ( ex x9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st  ex y9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st (x =XBOOLE-0R4 x9 & y =HIDDENR1 [TARSKIK4 0NUMBERSK6,y9 ]) & it =HIDDENR1 [TARSKIK4 0NUMBERSK6,x9 *'ARYTM-2K8 y9 ]))) & ((x inTARSKIR2 REAL+ARYTM-2K2 & y inTARSKIR2 REAL+ARYTM-2K2) & ((y inTARSKIR2 REAL+ARYTM-2K2 & x inTARSKIR2 [:ZFMISC-1K2 {TARSKIK1 0NUMBERSK6 },REAL+ARYTM-2K2 :]) & y <>HIDDENR2 0NUMBERSK6) implies (( ex x9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st  ex y9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st (x =XBOOLE-0R4 x9 & y =XBOOLE-0R4 y9) & it =XBOOLE-0R4 x9 *'ARYTM-2K8 y9) iff ( ex x9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st  ex y9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st (x =HIDDENR1 [TARSKIK4 0NUMBERSK6,x9 ] & y =XBOOLE-0R4 y9) & it =HIDDENR1 [TARSKIK4 0NUMBERSK6,y9 *'ARYTM-2K8 x9 ])))) & ((x inTARSKIR2 REAL+ARYTM-2K2 & y inTARSKIR2 REAL+ARYTM-2K2) & (x inTARSKIR2 [:ZFMISC-1K2 {TARSKIK1 0NUMBERSK6 },REAL+ARYTM-2K2 :] & y inTARSKIR2 [:ZFMISC-1K2 {TARSKIK1 0NUMBERSK6 },REAL+ARYTM-2K2 :]) implies (( ex x9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st  ex y9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st (x =XBOOLE-0R4 x9 & y =XBOOLE-0R4 y9) & it =XBOOLE-0R4 x9 *'ARYTM-2K8 y9) iff ( ex x9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st  ex y9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st (x =HIDDENR1 [TARSKIK4 0NUMBERSK6,x9 ] & y =HIDDENR1 [TARSKIK4 0NUMBERSK6,y9 ]) & it =XBOOLE-0R4 y9 *'ARYTM-2K8 x9)))) & (((x inTARSKIR2 REAL+ARYTM-2K2 & y inTARSKIR2 [:ZFMISC-1K2 {TARSKIK1 0NUMBERSK6 },REAL+ARYTM-2K2 :]) & x <>HIDDENR2 0NUMBERSK6) & ((y inTARSKIR2 REAL+ARYTM-2K2 & x inTARSKIR2 [:ZFMISC-1K2 {TARSKIK1 0NUMBERSK6 },REAL+ARYTM-2K2 :]) & y <>HIDDENR2 0NUMBERSK6) implies (( ex x9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st  ex y9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st (x =XBOOLE-0R4 x9 & y =HIDDENR1 [TARSKIK4 0NUMBERSK6,y9 ]) & it =HIDDENR1 [TARSKIK4 0NUMBERSK6,x9 *'ARYTM-2K8 y9 ]) iff ( ex x9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st  ex y9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st (x =HIDDENR1 [TARSKIK4 0NUMBERSK6,x9 ] & y =XBOOLE-0R4 y9) & it =HIDDENR1 [TARSKIK4 0NUMBERSK6,y9 *'ARYTM-2K8 x9 ])))) & (((x inTARSKIR2 REAL+ARYTM-2K2 & y inTARSKIR2 [:ZFMISC-1K2 {TARSKIK1 0NUMBERSK6 },REAL+ARYTM-2K2 :]) & x <>HIDDENR2 0NUMBERSK6) & (x inTARSKIR2 [:ZFMISC-1K2 {TARSKIK1 0NUMBERSK6 },REAL+ARYTM-2K2 :] & y inTARSKIR2 [:ZFMISC-1K2 {TARSKIK1 0NUMBERSK6 },REAL+ARYTM-2K2 :]) implies (( ex x9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st  ex y9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st (x =XBOOLE-0R4 x9 & y =HIDDENR1 [TARSKIK4 0NUMBERSK6,y9 ]) & it =HIDDENR1 [TARSKIK4 0NUMBERSK6,x9 *'ARYTM-2K8 y9 ]) iff ( ex x9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st  ex y9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st (x =HIDDENR1 [TARSKIK4 0NUMBERSK6,x9 ] & y =HIDDENR1 [TARSKIK4 0NUMBERSK6,y9 ]) & it =XBOOLE-0R4 y9 *'ARYTM-2K8 x9)))) & (((y inTARSKIR2 REAL+ARYTM-2K2 & x inTARSKIR2 [:ZFMISC-1K2 {TARSKIK1 0NUMBERSK6 },REAL+ARYTM-2K2 :]) & y <>HIDDENR2 0NUMBERSK6) & (x inTARSKIR2 [:ZFMISC-1K2 {TARSKIK1 0NUMBERSK6 },REAL+ARYTM-2K2 :] & y inTARSKIR2 [:ZFMISC-1K2 {TARSKIK1 0NUMBERSK6 },REAL+ARYTM-2K2 :]) implies (( ex x9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st  ex y9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st (x =HIDDENR1 [TARSKIK4 0NUMBERSK6,x9 ] & y =XBOOLE-0R4 y9) & it =HIDDENR1 [TARSKIK4 0NUMBERSK6,y9 *'ARYTM-2K8 x9 ]) iff ( ex x9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st  ex y9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st (x =HIDDENR1 [TARSKIK4 0NUMBERSK6,x9 ] & y =HIDDENR1 [TARSKIK4 0NUMBERSK6,y9 ]) & it =XBOOLE-0R4 y9 *'ARYTM-2K8 x9)))"
      using arytm_0_th_5 xboole_0_th_3 sorry
qed "sorry"

mtheorem ARYTM_0K2_commutativity:
" for x be ElementSUBSET-1M1-of REALNUMBERSK2 holds  for y be ElementSUBSET-1M1-of REALNUMBERSK2 holds  *ARYTM-0K2(x,y) =HIDDENR1  *ARYTM-0K2(y,x)"
sorry

reserve x, y for "ElementSUBSET-1M1-of REALNUMBERSK2"
mdef arytm_0_def_3 ("oppARYTM-0K3  _ " [228]228 ) where
  mlet "x be ElementSUBSET-1M1-of REALNUMBERSK2"
"func oppARYTM-0K3 x \<rightarrow> ElementSUBSET-1M1-of REALNUMBERSK2 means
  \<lambda>it. +ARYTM-0K1(x,it) =XBOOLE-0R4 0NUMBERSK6"
proof-
  (*existence*)
    show " ex it be ElementSUBSET-1M1-of REALNUMBERSK2 st +ARYTM-0K1(x,it) =XBOOLE-0R4 0NUMBERSK6"
sorry
  (*uniqueness*)
    show " for it1 be ElementSUBSET-1M1-of REALNUMBERSK2 holds  for it2 be ElementSUBSET-1M1-of REALNUMBERSK2 holds +ARYTM-0K1(x,it1) =XBOOLE-0R4 0NUMBERSK6 & +ARYTM-0K1(x,it2) =XBOOLE-0R4 0NUMBERSK6 implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mtheorem ARYTM_0K3_involutiveness:
" for x be ElementSUBSET-1M1-of REALNUMBERSK2 holds oppARYTM-0K3 (oppARYTM-0K3 x) =HIDDENR1 x"
sorry

mdef arytm_0_def_4 ("invARYTM-0K4  _ " [164]164 ) where
  mlet "x be ElementSUBSET-1M1-of REALNUMBERSK2"
"func invARYTM-0K4 x \<rightarrow> ElementSUBSET-1M1-of REALNUMBERSK2 means
  \<lambda>it.  *ARYTM-0K2(x,it) =XBOOLE-0R4 \<one>\<^sub>M if x <>HIDDENR2 0NUMBERSK6 otherwise \<lambda>it. it =XBOOLE-0R4 0NUMBERSK6"
proof-
  (*existence*)
    show "(x <>HIDDENR2 0NUMBERSK6 implies ( ex it be ElementSUBSET-1M1-of REALNUMBERSK2 st  *ARYTM-0K2(x,it) =XBOOLE-0R4 \<one>\<^sub>M)) & ( not x <>HIDDENR2 0NUMBERSK6 implies ( ex it be ElementSUBSET-1M1-of REALNUMBERSK2 st it =XBOOLE-0R4 0NUMBERSK6))"
sorry
  (*uniqueness*)
    show " for it1 be ElementSUBSET-1M1-of REALNUMBERSK2 holds  for it2 be ElementSUBSET-1M1-of REALNUMBERSK2 holds (x <>HIDDENR2 0NUMBERSK6 implies ( *ARYTM-0K2(x,it1) =XBOOLE-0R4 \<one>\<^sub>M &  *ARYTM-0K2(x,it2) =XBOOLE-0R4 \<one>\<^sub>M implies it1 =HIDDENR1 it2)) & ( not x <>HIDDENR2 0NUMBERSK6 implies (it1 =XBOOLE-0R4 0NUMBERSK6 & it2 =XBOOLE-0R4 0NUMBERSK6 implies it1 =HIDDENR1 it2))"
sorry
  (*consistency*)
    show " for it be ElementSUBSET-1M1-of REALNUMBERSK2 holds  True "
       sorry
qed "sorry"

mtheorem ARYTM_0K4_involutiveness:
" for x be ElementSUBSET-1M1-of REALNUMBERSK2 holds invARYTM-0K4 (invARYTM-0K4 x) =HIDDENR1 x"
sorry

(*begin*)
mlemma arytm_0_lm_4:
" for x be setHIDDENM2 holds  for y be setHIDDENM2 holds  for z be setHIDDENM2 holds [TARSKIK4 x,y ] =HIDDENR1 {TARSKIK1 z} implies z =XBOOLE-0R4 {TARSKIK1 x} & x =XBOOLE-0R4 y"
sorry

reserve i, j, k for "ElementSUBSET-1M1-of NATNUMBERSK1"
reserve a, b for "ElementSUBSET-1M1-of REALNUMBERSK2"
mtheorem arytm_0_th_8:
" for a be ElementSUBSET-1M1-of REALNUMBERSK2 holds  for b be ElementSUBSET-1M1-of REALNUMBERSK2 holds  not (0NUMBERSK6,\<one>\<^sub>M)-->FUNCT-4K7\<^bsub>(REALNUMBERSK2)\<^esub>(a,b) inTARSKIR2 REALNUMBERSK2"
sorry

mdef arytm_0_def_5 ("[*ARYTM-0K5 _ , _ *]" [0,0]164 ) where
  mlet "x be ElementSUBSET-1M1-of REALNUMBERSK2", "y be ElementSUBSET-1M1-of REALNUMBERSK2"
"func [*ARYTM-0K5 x,y *] \<rightarrow> ElementSUBSET-1M1-of COMPLEXNUMBERSK3 equals
  x if y =XBOOLE-0R4 0NUMBERSK6 otherwise (0NUMBERSK6,\<one>\<^sub>M)-->FUNCT-4K7\<^bsub>(REALNUMBERSK2)\<^esub>(x,y)"
proof-
  (*consistency*)
    show " for it be ElementSUBSET-1M1-of COMPLEXNUMBERSK3 holds  True "
       sorry
  (*coherence*)
    show "(y =XBOOLE-0R4 0NUMBERSK6 implies x be ElementSUBSET-1M1-of COMPLEXNUMBERSK3) & ( not y =XBOOLE-0R4 0NUMBERSK6 implies (0NUMBERSK6,\<one>\<^sub>M)-->FUNCT-4K7\<^bsub>(REALNUMBERSK2)\<^esub>(x,y) be ElementSUBSET-1M1-of COMPLEXNUMBERSK3)"
sorry
qed "sorry"

mtheorem arytm_0_th_9:
" for c be ElementSUBSET-1M1-of COMPLEXNUMBERSK3 holds  ex r be ElementSUBSET-1M1-of REALNUMBERSK2 st  ex s be ElementSUBSET-1M1-of REALNUMBERSK2 st c =XBOOLE-0R4 [*ARYTM-0K5 r,s *]"
sorry

mtheorem arytm_0_th_10:
" for x1 be ElementSUBSET-1M1-of REALNUMBERSK2 holds  for x2 be ElementSUBSET-1M1-of REALNUMBERSK2 holds  for y1 be ElementSUBSET-1M1-of REALNUMBERSK2 holds  for y2 be ElementSUBSET-1M1-of REALNUMBERSK2 holds [*ARYTM-0K5 x1,x2 *] =XBOOLE-0R4 [*ARYTM-0K5 y1,y2 *] implies x1 =XBOOLE-0R4 y1 & x2 =XBOOLE-0R4 y2"
sorry

mtheorem arytm_0_th_11:
" for x be ElementSUBSET-1M1-of REALNUMBERSK2 holds  for o be ElementSUBSET-1M1-of REALNUMBERSK2 holds o =XBOOLE-0R4 0NUMBERSK6 implies +ARYTM-0K1(x,o) =XBOOLE-0R4 x"
sorry

mtheorem arytm_0_th_12:
" for x be ElementSUBSET-1M1-of REALNUMBERSK2 holds  for o be ElementSUBSET-1M1-of REALNUMBERSK2 holds o =XBOOLE-0R4 0NUMBERSK6 implies  *ARYTM-0K2(x,o) =XBOOLE-0R4 0NUMBERSK6"
sorry

mtheorem arytm_0_th_13:
" for x be ElementSUBSET-1M1-of REALNUMBERSK2 holds  for y be ElementSUBSET-1M1-of REALNUMBERSK2 holds  for z be ElementSUBSET-1M1-of REALNUMBERSK2 holds  *ARYTM-0K2(x, *ARYTM-0K2(y,z)) =XBOOLE-0R4  *ARYTM-0K2( *ARYTM-0K2(x,y),z)"
sorry

mtheorem arytm_0_th_14:
" for x be ElementSUBSET-1M1-of REALNUMBERSK2 holds  for y be ElementSUBSET-1M1-of REALNUMBERSK2 holds  for z be ElementSUBSET-1M1-of REALNUMBERSK2 holds  *ARYTM-0K2(x,+ARYTM-0K1(y,z)) =XBOOLE-0R4 +ARYTM-0K1( *ARYTM-0K2(x,y), *ARYTM-0K2(x,z))"
sorry

mtheorem arytm_0_th_15:
" for x be ElementSUBSET-1M1-of REALNUMBERSK2 holds  for y be ElementSUBSET-1M1-of REALNUMBERSK2 holds  *ARYTM-0K2(oppARYTM-0K3 x,y) =XBOOLE-0R4 oppARYTM-0K3 ( *ARYTM-0K2(x,y))"
sorry

mtheorem arytm_0_th_16:
" for x be ElementSUBSET-1M1-of REALNUMBERSK2 holds  *ARYTM-0K2(x,x) inTARSKIR2 REAL+ARYTM-2K2"
sorry

mtheorem arytm_0_th_17:
" for x be ElementSUBSET-1M1-of REALNUMBERSK2 holds  for y be ElementSUBSET-1M1-of REALNUMBERSK2 holds +ARYTM-0K1( *ARYTM-0K2(x,x), *ARYTM-0K2(y,y)) =XBOOLE-0R4 0NUMBERSK6 implies x =XBOOLE-0R4 0NUMBERSK6"
sorry

mtheorem arytm_0_th_18:
" for x be ElementSUBSET-1M1-of REALNUMBERSK2 holds  for y be ElementSUBSET-1M1-of REALNUMBERSK2 holds  for z be ElementSUBSET-1M1-of REALNUMBERSK2 holds (x <>HIDDENR2 0NUMBERSK6 &  *ARYTM-0K2(x,y) =XBOOLE-0R4 \<one>\<^sub>M) &  *ARYTM-0K2(x,z) =XBOOLE-0R4 \<one>\<^sub>M implies y =XBOOLE-0R4 z"
sorry

mtheorem arytm_0_th_19:
" for x be ElementSUBSET-1M1-of REALNUMBERSK2 holds  for y be ElementSUBSET-1M1-of REALNUMBERSK2 holds y =XBOOLE-0R4 \<one>\<^sub>M implies  *ARYTM-0K2(x,y) =XBOOLE-0R4 x"
sorry

mtheorem arytm_0_th_20:
" for x be ElementSUBSET-1M1-of REALNUMBERSK2 holds  for y be ElementSUBSET-1M1-of REALNUMBERSK2 holds y <>HIDDENR2 0NUMBERSK6 implies  *ARYTM-0K2( *ARYTM-0K2(x,y),invARYTM-0K4 y) =XBOOLE-0R4 x"
sorry

mtheorem arytm_0_th_21:
" for x be ElementSUBSET-1M1-of REALNUMBERSK2 holds  for y be ElementSUBSET-1M1-of REALNUMBERSK2 holds  *ARYTM-0K2(x,y) =XBOOLE-0R4 0NUMBERSK6 implies x =XBOOLE-0R4 0NUMBERSK6 or y =XBOOLE-0R4 0NUMBERSK6"
sorry

mtheorem arytm_0_th_22:
" for x be ElementSUBSET-1M1-of REALNUMBERSK2 holds  for y be ElementSUBSET-1M1-of REALNUMBERSK2 holds invARYTM-0K4 ( *ARYTM-0K2(x,y)) =XBOOLE-0R4  *ARYTM-0K2(invARYTM-0K4 x,invARYTM-0K4 y)"
sorry

mtheorem arytm_0_th_23:
" for x be ElementSUBSET-1M1-of REALNUMBERSK2 holds  for y be ElementSUBSET-1M1-of REALNUMBERSK2 holds  for z be ElementSUBSET-1M1-of REALNUMBERSK2 holds +ARYTM-0K1(x,+ARYTM-0K1(y,z)) =XBOOLE-0R4 +ARYTM-0K1(+ARYTM-0K1(x,y),z)"
sorry

mtheorem arytm_0_th_24:
" for x be ElementSUBSET-1M1-of REALNUMBERSK2 holds  for y be ElementSUBSET-1M1-of REALNUMBERSK2 holds [*ARYTM-0K5 x,y *] inTARSKIR2 REALNUMBERSK2 implies y =XBOOLE-0R4 0NUMBERSK6"
sorry

mtheorem arytm_0_th_25:
" for x be ElementSUBSET-1M1-of REALNUMBERSK2 holds  for y be ElementSUBSET-1M1-of REALNUMBERSK2 holds oppARYTM-0K3 (+ARYTM-0K1(x,y)) =XBOOLE-0R4 +ARYTM-0K1(oppARYTM-0K3 x,oppARYTM-0K3 y)"
sorry

end
