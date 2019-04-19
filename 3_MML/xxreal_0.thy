theory xxreal_0
  imports arytm_0 xregular
begin
(*begin*)
mlemma xxreal_0_lm_1:
" not REALNUMBERSK2 inTARSKIR2 REALNUMBERSK2"
   sorry

mdef xxreal_0_def_1 ("ext-realXXREAL-0V1" 70 ) where
"attr ext-realXXREAL-0V1 for objectHIDDENM1 means
  (\<lambda>x. x inHIDDENR3 ExtREALNUMBERSK7)"..

mtheorem xxreal_0_cl_1:
"cluster ext-realXXREAL-0V1 for objectHIDDENM1"
proof
(*existence*)
  show " ex it be objectHIDDENM1 st it be ext-realXXREAL-0V1"
sorry
qed "sorry"

mtheorem xxreal_0_cl_2:
"cluster ext-realXXREAL-0V1 for numberORDINAL1M2"
proof
(*existence*)
  show " ex it be numberORDINAL1M2 st it be ext-realXXREAL-0V1"
sorry
qed "sorry"

mtheorem xxreal_0_cl_3:
"cluster note-that ext-realXXREAL-0V1 for ElementSUBSET-1M1-of ExtREALNUMBERSK7"
proof
(*coherence*)
  show " for it be ElementSUBSET-1M1-of ExtREALNUMBERSK7 holds it be ext-realXXREAL-0V1"
     sorry
qed "sorry"

syntax XXREAL_0M1 :: "Ty" ("ExtRealXXREAL-0M1" 70)
translations "ExtRealXXREAL-0M1" \<rightharpoonup> "ext-realXXREAL-0V1\<bar>NumberORDINAL1M1"

mtheorem
"cluster sethood of ExtRealXXREAL-0M1"
proof
(*sethood*)
  show " ex cover be setHIDDENM2 st  for it be ExtRealXXREAL-0M1 holds it inHIDDENR3 cover"
sorry
qed "sorry"

mdef xxreal_0_def_2 ("+inftyXXREAL-0K1" 300 ) where
"func +inftyXXREAL-0K1 \<rightarrow> objectHIDDENM1 equals
  REALNUMBERSK2"
proof-
  (*coherence*)
    show "REALNUMBERSK2 be objectHIDDENM1"
       sorry
qed "sorry"

mdef xxreal_0_def_3 ("-inftyXXREAL-0K2" 300 ) where
"func -inftyXXREAL-0K2 \<rightarrow> objectHIDDENM1 equals
  [TARSKIK4 0NUMBERSK6,REALNUMBERSK2 ]"
proof-
  (*coherence*)
    show "[TARSKIK4 0NUMBERSK6,REALNUMBERSK2 ] be objectHIDDENM1"
       sorry
qed "sorry"

abbreviation(input) XXREAL_0K3("ExtREALXXREAL-0K3" 164) where
  "ExtREALXXREAL-0K3 \<equiv> ExtREALNUMBERSK7"

mtheorem xxreal_0_def_4:
"redefine func ExtREALXXREAL-0K3 \<rightarrow> setHIDDENM2 equals
  REALNUMBERSK2 \\/XBOOLE-0K2 {TARSKIK2 +inftyXXREAL-0K1,-inftyXXREAL-0K2 }"
proof
(*compatibility*)
  show " for it be setHIDDENM2 holds it =HIDDENR1 ExtREALXXREAL-0K3 iff it =HIDDENR1 REALNUMBERSK2 \\/XBOOLE-0K2 {TARSKIK2 +inftyXXREAL-0K1,-inftyXXREAL-0K2 }"
     sorry
qed "sorry"

mtheorem xxreal_0_cl_4:
"cluster +inftyXXREAL-0K1 as-term-is ext-realXXREAL-0V1"
proof
(*coherence*)
  show "+inftyXXREAL-0K1 be ext-realXXREAL-0V1"
sorry
qed "sorry"

mtheorem xxreal_0_cl_5:
"cluster -inftyXXREAL-0K2 as-term-is ext-realXXREAL-0V1"
proof
(*coherence*)
  show "-inftyXXREAL-0K2 be ext-realXXREAL-0V1"
sorry
qed "sorry"

mdef xxreal_0_def_5 (" _ <=XXREAL-0R1  _ " [50,50]50 ) where
  mlet "x be ExtRealXXREAL-0M1", "y be ExtRealXXREAL-0M1"
"pred x <=XXREAL-0R1 y means
   ex x9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st  ex y9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st (x =HIDDENR1 x9 & y =HIDDENR1 y9) & x9 <='ARYTM-2R1 y9 if x inHIDDENR3 REAL+ARYTM-2K2 & y inHIDDENR3 REAL+ARYTM-2K2,
   ex x9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st  ex y9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st (x =HIDDENR1 [TARSKIK4 0NUMBERSK6,x9 ] & y =HIDDENR1 [TARSKIK4 0NUMBERSK6,y9 ]) & y9 <='ARYTM-2R1 x9 if x inHIDDENR3 [:ZFMISC-1K2 {TARSKIK1 0NUMBERSK6 },REAL+ARYTM-2K2 :] & y inHIDDENR3 [:ZFMISC-1K2 {TARSKIK1 0NUMBERSK6 },REAL+ARYTM-2K2 :] otherwise (y inHIDDENR3 REAL+ARYTM-2K2 & x inHIDDENR3 [:ZFMISC-1K2 {TARSKIK1 0NUMBERSK6 },REAL+ARYTM-2K2 :] or x =HIDDENR1 -inftyXXREAL-0K2) or y =HIDDENR1 +inftyXXREAL-0K1"
proof-
  (*consistency*)
    show "(x inHIDDENR3 REAL+ARYTM-2K2 & y inHIDDENR3 REAL+ARYTM-2K2) & (x inHIDDENR3 [:ZFMISC-1K2 {TARSKIK1 0NUMBERSK6 },REAL+ARYTM-2K2 :] & y inHIDDENR3 [:ZFMISC-1K2 {TARSKIK1 0NUMBERSK6 },REAL+ARYTM-2K2 :]) implies (( ex x9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st  ex y9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st (x =HIDDENR1 x9 & y =HIDDENR1 y9) & x9 <='ARYTM-2R1 y9) iff ( ex x9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st  ex y9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st (x =HIDDENR1 [TARSKIK4 0NUMBERSK6,x9 ] & y =HIDDENR1 [TARSKIK4 0NUMBERSK6,y9 ]) & y9 <='ARYTM-2R1 x9))"
      using arytm_0_th_5 xboole_0_th_3 sorry
qed "sorry"

mtheorem XXREAL_0R1_reflexivity:
" for y be ExtRealXXREAL-0M1 holds y <=XXREAL-0R1 y"
sorry

mtheorem XXREAL_0R1_connectedness:
" for x be ExtRealXXREAL-0M1 holds  for y be ExtRealXXREAL-0M1 holds  not x <=XXREAL-0R1 y implies y <=XXREAL-0R1 x"
sorry

reserve a, b, c, d for "ExtRealXXREAL-0M1"
abbreviation(input) XXREAL_0R2(" _ >=XXREAL-0R2  _ " [50,50]50) where
  "b >=XXREAL-0R2 a \<equiv> a <=XXREAL-0R1 b"

syntax XXREAL_0R3 :: " Set \<Rightarrow>  Set \<Rightarrow> o" (" _ <XXREAL-0R3  _ " [50,50]50)
translations "b <XXREAL-0R3 a" \<rightharpoonup> " not a <=XXREAL-0R1 b"

syntax XXREAL_0R4 :: " Set \<Rightarrow>  Set \<Rightarrow> o" (" _ >XXREAL-0R4  _ " [50,50]50)
translations "a >XXREAL-0R4 b" \<rightharpoonup> " not a <=XXREAL-0R1 b"

mlemma xxreal_0_lm_2:
"0NUMBERSK6 inTARSKIR2 REALNUMBERSK2"
  using numbers_th_19 sorry

mlemma xxreal_0_lm_3:
"+inftyXXREAL-0K1 <>HIDDENR2 [TARSKIK4 0NUMBERSK6,0NUMBERSK6 ]"
sorry

mlemma xxreal_0_lm_4:
" not +inftyXXREAL-0K1 inHIDDENR3 REAL+ARYTM-2K2"
  using arytm_0_th_1 ordinal1_th_5 sorry

mlemma xxreal_0_lm_5:
" not -inftyXXREAL-0K2 inHIDDENR3 REAL+ARYTM-2K2"
sorry

mlemma xxreal_0_lm_6:
" not +inftyXXREAL-0K1 inHIDDENR3 [:ZFMISC-1K2 {TARSKIK1 0NUMBERSK6 },REAL+ARYTM-2K2 :]"
sorry

mlemma xxreal_0_lm_7:
" not -inftyXXREAL-0K2 inHIDDENR3 [:ZFMISC-1K2 {TARSKIK1 0NUMBERSK6 },REAL+ARYTM-2K2 :]"
sorry

mlemma xxreal_0_lm_8:
"-inftyXXREAL-0K2 <XXREAL-0R3 +inftyXXREAL-0K1"
sorry

mtheorem xxreal_0_th_1:
" for a be ExtRealXXREAL-0M1 holds  for b be ExtRealXXREAL-0M1 holds a <=XXREAL-0R1 b & b <=XXREAL-0R1 a implies a =HIDDENR1 b"
sorry

mlemma xxreal_0_lm_9:
" for a be ExtRealXXREAL-0M1 holds -inftyXXREAL-0K2 >=XXREAL-0R2 a implies a =HIDDENR1 -inftyXXREAL-0K2"
sorry

mlemma xxreal_0_lm_10:
" for a be ExtRealXXREAL-0M1 holds +inftyXXREAL-0K1 <=XXREAL-0R1 a implies a =HIDDENR1 +inftyXXREAL-0K1"
sorry

mtheorem xxreal_0_th_2:
" for a be ExtRealXXREAL-0M1 holds  for b be ExtRealXXREAL-0M1 holds  for c be ExtRealXXREAL-0M1 holds a <=XXREAL-0R1 b & b <=XXREAL-0R1 c implies a <=XXREAL-0R1 c"
sorry

mtheorem xxreal_0_th_3:
" for a be ExtRealXXREAL-0M1 holds a <=XXREAL-0R1 +inftyXXREAL-0K1"
  using xxreal_0_def_5 xxreal_0_lm_4 xxreal_0_lm_6 sorry

mtheorem xxreal_0_th_4:
" for a be ExtRealXXREAL-0M1 holds +inftyXXREAL-0K1 <=XXREAL-0R1 a implies a =HIDDENR1 +inftyXXREAL-0K1"
  using xxreal_0_lm_10 sorry

mtheorem xxreal_0_th_5:
" for a be ExtRealXXREAL-0M1 holds a >=XXREAL-0R2 -inftyXXREAL-0K2"
  using xxreal_0_def_5 xxreal_0_lm_5 xxreal_0_lm_7 sorry

mtheorem xxreal_0_th_6:
" for a be ExtRealXXREAL-0M1 holds -inftyXXREAL-0K2 >=XXREAL-0R2 a implies a =HIDDENR1 -inftyXXREAL-0K2"
  using xxreal_0_lm_9 sorry

mtheorem xxreal_0_th_7:
"-inftyXXREAL-0K2 <XXREAL-0R3 +inftyXXREAL-0K1"
  using xxreal_0_lm_8 sorry

mtheorem xxreal_0_th_8:
" not +inftyXXREAL-0K1 inHIDDENR3 REALNUMBERSK2"
  using xxreal_0_lm_1 sorry

mlemma xxreal_0_lm_11:
" for a be ExtRealXXREAL-0M1 holds (a inHIDDENR3 REALNUMBERSK2 or a =HIDDENR1 +inftyXXREAL-0K1) or a =HIDDENR1 -inftyXXREAL-0K2"
sorry

mtheorem xxreal_0_th_9:
" for a be ExtRealXXREAL-0M1 holds a inHIDDENR3 REALNUMBERSK2 implies +inftyXXREAL-0K1 >XXREAL-0R4 a"
sorry

mtheorem xxreal_0_th_10:
" for a be ExtRealXXREAL-0M1 holds  for b be ExtRealXXREAL-0M1 holds a inHIDDENR3 REALNUMBERSK2 & b >=XXREAL-0R2 a implies b inHIDDENR3 REALNUMBERSK2 or b =HIDDENR1 +inftyXXREAL-0K1"
sorry

mtheorem xxreal_0_th_11:
" not -inftyXXREAL-0K2 inHIDDENR3 REALNUMBERSK2"
sorry

mtheorem xxreal_0_th_12:
" for a be ExtRealXXREAL-0M1 holds a inHIDDENR3 REALNUMBERSK2 implies -inftyXXREAL-0K2 <XXREAL-0R3 a"
sorry

mtheorem xxreal_0_th_13:
" for a be ExtRealXXREAL-0M1 holds  for b be ExtRealXXREAL-0M1 holds a inHIDDENR3 REALNUMBERSK2 & b <=XXREAL-0R1 a implies b inHIDDENR3 REALNUMBERSK2 or b =HIDDENR1 -inftyXXREAL-0K2"
sorry

mtheorem xxreal_0_th_14:
" for a be ExtRealXXREAL-0M1 holds (a inHIDDENR3 REALNUMBERSK2 or a =HIDDENR1 +inftyXXREAL-0K1) or a =HIDDENR1 -inftyXXREAL-0K2"
  using xxreal_0_lm_11 sorry

(*begin*)
mtheorem xxreal_0_cl_6:
"cluster naturalORDINAL1V7 also-is ext-realXXREAL-0V1 for objectHIDDENM1"
proof
(*coherence*)
  show " for it be objectHIDDENM1 holds it be naturalORDINAL1V7 implies it be ext-realXXREAL-0V1"
    using numbers_th_19 xboole_0_def_3 sorry
qed "sorry"

mdef xxreal_0_def_6 ("positiveXXREAL-0V2" 70 ) where
"attr positiveXXREAL-0V2 for ExtRealXXREAL-0M1 means
  (\<lambda>a. a >XXREAL-0R4 0NUMBERSK6)"..

mdef xxreal_0_def_7 ("negativeXXREAL-0V3" 70 ) where
"attr negativeXXREAL-0V3 for ExtRealXXREAL-0M1 means
  (\<lambda>a. a <XXREAL-0R3 0NUMBERSK6)"..

(*\$CD*)
mtheorem xxreal_0_cl_7:
"cluster positiveXXREAL-0V2 also-is  non negativeXXREAL-0V3\<bar> non zeroORDINAL1V8 for ExtRealXXREAL-0M1"
proof
(*coherence*)
  show " for it be ExtRealXXREAL-0M1 holds it be positiveXXREAL-0V2 implies it be  non negativeXXREAL-0V3\<bar> non zeroORDINAL1V8"
     sorry
qed "sorry"

mtheorem xxreal_0_cl_8:
"cluster  non negativeXXREAL-0V3\<bar> non zeroORDINAL1V8 also-is positiveXXREAL-0V2 for ExtRealXXREAL-0M1"
proof
(*coherence*)
  show " for it be ExtRealXXREAL-0M1 holds it be  non negativeXXREAL-0V3\<bar> non zeroORDINAL1V8 implies it be positiveXXREAL-0V2"
    using xxreal_0_th_1 sorry
qed "sorry"

mtheorem xxreal_0_cl_9:
"cluster negativeXXREAL-0V3 also-is  non positiveXXREAL-0V2\<bar> non zeroORDINAL1V8 for ExtRealXXREAL-0M1"
proof
(*coherence*)
  show " for it be ExtRealXXREAL-0M1 holds it be negativeXXREAL-0V3 implies it be  non positiveXXREAL-0V2\<bar> non zeroORDINAL1V8"
     sorry
qed "sorry"

mtheorem xxreal_0_cl_10:
"cluster  non positiveXXREAL-0V2\<bar> non zeroORDINAL1V8 also-is negativeXXREAL-0V3 for ExtRealXXREAL-0M1"
proof
(*coherence*)
  show " for it be ExtRealXXREAL-0M1 holds it be  non positiveXXREAL-0V2\<bar> non zeroORDINAL1V8 implies it be negativeXXREAL-0V3"
     sorry
qed "sorry"

mtheorem xxreal_0_cl_11:
"cluster zeroORDINAL1V8 also-is  non negativeXXREAL-0V3\<bar> non positiveXXREAL-0V2 for ExtRealXXREAL-0M1"
proof
(*coherence*)
  show " for it be ExtRealXXREAL-0M1 holds it be zeroORDINAL1V8 implies it be  non negativeXXREAL-0V3\<bar> non positiveXXREAL-0V2"
     sorry
qed "sorry"

mtheorem xxreal_0_cl_12:
"cluster  non negativeXXREAL-0V3\<bar> non positiveXXREAL-0V2 also-is zeroORDINAL1V8 for ExtRealXXREAL-0M1"
proof
(*coherence*)
  show " for it be ExtRealXXREAL-0M1 holds it be  non negativeXXREAL-0V3\<bar> non positiveXXREAL-0V2 implies it be zeroORDINAL1V8"
     sorry
qed "sorry"

mtheorem xxreal_0_cl_13:
"cluster +inftyXXREAL-0K1 as-term-is positiveXXREAL-0V2"
proof
(*coherence*)
  show "+inftyXXREAL-0K1 be positiveXXREAL-0V2"
    using xxreal_0_th_9 xxreal_0_lm_2 sorry
qed "sorry"

mtheorem xxreal_0_cl_14:
"cluster -inftyXXREAL-0K2 as-term-is negativeXXREAL-0V3"
proof
(*coherence*)
  show "-inftyXXREAL-0K2 be negativeXXREAL-0V3"
    using xxreal_0_th_12 xxreal_0_lm_2 sorry
qed "sorry"

mtheorem xxreal_0_cl_15:
"cluster positiveXXREAL-0V2 for ExtRealXXREAL-0M1"
proof
(*existence*)
  show " ex it be ExtRealXXREAL-0M1 st it be positiveXXREAL-0V2"
sorry
qed "sorry"

mtheorem xxreal_0_cl_16:
"cluster negativeXXREAL-0V3 for ExtRealXXREAL-0M1"
proof
(*existence*)
  show " ex it be ExtRealXXREAL-0M1 st it be negativeXXREAL-0V3"
sorry
qed "sorry"

mtheorem xxreal_0_cl_17:
"cluster zeroORDINAL1V8 for ExtRealXXREAL-0M1"
proof
(*existence*)
  show " ex it be ExtRealXXREAL-0M1 st it be zeroORDINAL1V8"
sorry
qed "sorry"

(*begin*)
mdef xxreal_0_def_9 ("minXXREAL-0K4'( _ , _ ')" [0,0]228 ) where
  mlet "a be ExtRealXXREAL-0M1", "b be ExtRealXXREAL-0M1"
"func minXXREAL-0K4(a,b) \<rightarrow> ExtRealXXREAL-0M1 equals
  a if a <=XXREAL-0R1 b otherwise b"
proof-
  (*coherence*)
    show "(a <=XXREAL-0R1 b implies a be ExtRealXXREAL-0M1) & ( not a <=XXREAL-0R1 b implies b be ExtRealXXREAL-0M1)"
       sorry
  (*consistency*)
    show " for it be ExtRealXXREAL-0M1 holds  True "
       sorry
qed "sorry"

mtheorem XXREAL_0K4_commutativity:
" for a be ExtRealXXREAL-0M1 holds  for b be ExtRealXXREAL-0M1 holds minXXREAL-0K4(a,b) =HIDDENR1 minXXREAL-0K4(b,a)"
sorry

mtheorem XXREAL_0K4_idempotence:
" for b be ExtRealXXREAL-0M1 holds b =HIDDENR1 minXXREAL-0K4(b,b)"
sorry

mdef xxreal_0_def_10 ("maxXXREAL-0K5'( _ , _ ')" [0,0]228 ) where
  mlet "a be ExtRealXXREAL-0M1", "b be ExtRealXXREAL-0M1"
"func maxXXREAL-0K5(a,b) \<rightarrow> ExtRealXXREAL-0M1 equals
  a if b <=XXREAL-0R1 a otherwise b"
proof-
  (*coherence*)
    show "(b <=XXREAL-0R1 a implies a be ExtRealXXREAL-0M1) & ( not b <=XXREAL-0R1 a implies b be ExtRealXXREAL-0M1)"
       sorry
  (*consistency*)
    show " for it be ExtRealXXREAL-0M1 holds  True "
       sorry
qed "sorry"

mtheorem XXREAL_0K5_commutativity:
" for a be ExtRealXXREAL-0M1 holds  for b be ExtRealXXREAL-0M1 holds maxXXREAL-0K5(a,b) =HIDDENR1 maxXXREAL-0K5(b,a)"
sorry

mtheorem XXREAL_0K5_idempotence:
" for b be ExtRealXXREAL-0M1 holds b =HIDDENR1 maxXXREAL-0K5(b,b)"
sorry

mtheorem xxreal_0_th_15:
" for a be ExtRealXXREAL-0M1 holds  for b be ExtRealXXREAL-0M1 holds minXXREAL-0K4(a,b) =HIDDENR1 a or minXXREAL-0K4(a,b) =HIDDENR1 b"
  using xxreal_0_def_9 sorry

mtheorem xxreal_0_th_16:
" for a be ExtRealXXREAL-0M1 holds  for b be ExtRealXXREAL-0M1 holds maxXXREAL-0K5(a,b) =HIDDENR1 a or maxXXREAL-0K5(a,b) =HIDDENR1 b"
  using xxreal_0_def_10 sorry

mtheorem xxreal_0_cl_18:
  mlet "a be ExtRealXXREAL-0M1", "b be ExtRealXXREAL-0M1"
"cluster minXXREAL-0K4(a,b) as-term-is ext-realXXREAL-0V1"
proof
(*coherence*)
  show "minXXREAL-0K4(a,b) be ext-realXXREAL-0V1"
     sorry
qed "sorry"

mtheorem xxreal_0_cl_19:
  mlet "a be ExtRealXXREAL-0M1", "b be ExtRealXXREAL-0M1"
"cluster maxXXREAL-0K5(a,b) as-term-is ext-realXXREAL-0V1"
proof
(*coherence*)
  show "maxXXREAL-0K5(a,b) be ext-realXXREAL-0V1"
     sorry
qed "sorry"

mtheorem xxreal_0_th_17:
" for a be ExtRealXXREAL-0M1 holds  for b be ExtRealXXREAL-0M1 holds minXXREAL-0K4(a,b) <=XXREAL-0R1 a"
sorry

mtheorem xxreal_0_th_18:
" for a be ExtRealXXREAL-0M1 holds  for b be ExtRealXXREAL-0M1 holds  for c be ExtRealXXREAL-0M1 holds  for d be ExtRealXXREAL-0M1 holds a <=XXREAL-0R1 b & c <=XXREAL-0R1 d implies minXXREAL-0K4(a,c) <=XXREAL-0R1 minXXREAL-0K4(b,d)"
sorry

mtheorem xxreal_0_th_19:
" for a be ExtRealXXREAL-0M1 holds  for b be ExtRealXXREAL-0M1 holds  for c be ExtRealXXREAL-0M1 holds  for d be ExtRealXXREAL-0M1 holds a <XXREAL-0R3 b & c <XXREAL-0R3 d implies minXXREAL-0K4(a,c) <XXREAL-0R3 minXXREAL-0K4(b,d)"
sorry

mtheorem xxreal_0_th_20:
" for a be ExtRealXXREAL-0M1 holds  for b be ExtRealXXREAL-0M1 holds  for c be ExtRealXXREAL-0M1 holds a <=XXREAL-0R1 b & a <=XXREAL-0R1 c implies a <=XXREAL-0R1 minXXREAL-0K4(b,c)"
  using xxreal_0_def_9 sorry

mtheorem xxreal_0_th_21:
" for a be ExtRealXXREAL-0M1 holds  for b be ExtRealXXREAL-0M1 holds  for c be ExtRealXXREAL-0M1 holds a <XXREAL-0R3 b & a <XXREAL-0R3 c implies a <XXREAL-0R3 minXXREAL-0K4(b,c)"
  using xxreal_0_def_9 sorry

mtheorem xxreal_0_th_22:
" for a be ExtRealXXREAL-0M1 holds  for b be ExtRealXXREAL-0M1 holds  for c be ExtRealXXREAL-0M1 holds a <=XXREAL-0R1 minXXREAL-0K4(b,c) implies a <=XXREAL-0R1 b"
sorry

mtheorem xxreal_0_th_23:
" for a be ExtRealXXREAL-0M1 holds  for b be ExtRealXXREAL-0M1 holds  for c be ExtRealXXREAL-0M1 holds a <XXREAL-0R3 minXXREAL-0K4(b,c) implies a <XXREAL-0R3 b"
sorry

mtheorem xxreal_0_th_24:
" for a be ExtRealXXREAL-0M1 holds  for b be ExtRealXXREAL-0M1 holds  for c be ExtRealXXREAL-0M1 holds (c <=XXREAL-0R1 a & c <=XXREAL-0R1 b) & ( for d be ExtRealXXREAL-0M1 holds d <=XXREAL-0R1 a & d <=XXREAL-0R1 b implies d <=XXREAL-0R1 c) implies c =HIDDENR1 minXXREAL-0K4(a,b)"
sorry

mtheorem xxreal_0_th_25:
" for a be ExtRealXXREAL-0M1 holds  for b be ExtRealXXREAL-0M1 holds a <=XXREAL-0R1 maxXXREAL-0K5(a,b)"
sorry

mtheorem xxreal_0_th_26:
" for a be ExtRealXXREAL-0M1 holds  for b be ExtRealXXREAL-0M1 holds  for c be ExtRealXXREAL-0M1 holds  for d be ExtRealXXREAL-0M1 holds a <=XXREAL-0R1 b & c <=XXREAL-0R1 d implies maxXXREAL-0K5(a,c) <=XXREAL-0R1 maxXXREAL-0K5(b,d)"
sorry

mtheorem xxreal_0_th_27:
" for a be ExtRealXXREAL-0M1 holds  for b be ExtRealXXREAL-0M1 holds  for c be ExtRealXXREAL-0M1 holds  for d be ExtRealXXREAL-0M1 holds a <XXREAL-0R3 b & c <XXREAL-0R3 d implies maxXXREAL-0K5(a,c) <XXREAL-0R3 maxXXREAL-0K5(b,d)"
sorry

mtheorem xxreal_0_th_28:
" for a be ExtRealXXREAL-0M1 holds  for b be ExtRealXXREAL-0M1 holds  for c be ExtRealXXREAL-0M1 holds b <=XXREAL-0R1 a & c <=XXREAL-0R1 a implies maxXXREAL-0K5(b,c) <=XXREAL-0R1 a"
  using xxreal_0_def_10 sorry

mtheorem xxreal_0_th_29:
" for a be ExtRealXXREAL-0M1 holds  for b be ExtRealXXREAL-0M1 holds  for c be ExtRealXXREAL-0M1 holds b <XXREAL-0R3 a & c <XXREAL-0R3 a implies maxXXREAL-0K5(b,c) <XXREAL-0R3 a"
  using xxreal_0_def_10 sorry

mtheorem xxreal_0_th_30:
" for a be ExtRealXXREAL-0M1 holds  for b be ExtRealXXREAL-0M1 holds  for c be ExtRealXXREAL-0M1 holds maxXXREAL-0K5(b,c) <=XXREAL-0R1 a implies b <=XXREAL-0R1 a"
sorry

mtheorem xxreal_0_th_31:
" for a be ExtRealXXREAL-0M1 holds  for b be ExtRealXXREAL-0M1 holds  for c be ExtRealXXREAL-0M1 holds maxXXREAL-0K5(b,c) <XXREAL-0R3 a implies b <XXREAL-0R3 a"
sorry

mtheorem xxreal_0_th_32:
" for a be ExtRealXXREAL-0M1 holds  for b be ExtRealXXREAL-0M1 holds  for c be ExtRealXXREAL-0M1 holds (a <=XXREAL-0R1 c & b <=XXREAL-0R1 c) & ( for d be ExtRealXXREAL-0M1 holds a <=XXREAL-0R1 d & b <=XXREAL-0R1 d implies c <=XXREAL-0R1 d) implies c =HIDDENR1 maxXXREAL-0K5(a,b)"
sorry

mtheorem xxreal_0_th_33:
" for a be ExtRealXXREAL-0M1 holds  for b be ExtRealXXREAL-0M1 holds  for c be ExtRealXXREAL-0M1 holds minXXREAL-0K4(minXXREAL-0K4(a,b),c) =HIDDENR1 minXXREAL-0K4(a,minXXREAL-0K4(b,c))"
sorry

mtheorem xxreal_0_th_34:
" for a be ExtRealXXREAL-0M1 holds  for b be ExtRealXXREAL-0M1 holds  for c be ExtRealXXREAL-0M1 holds maxXXREAL-0K5(maxXXREAL-0K5(a,b),c) =HIDDENR1 maxXXREAL-0K5(a,maxXXREAL-0K5(b,c))"
sorry

mtheorem xxreal_0_th_35:
" for a be ExtRealXXREAL-0M1 holds  for b be ExtRealXXREAL-0M1 holds minXXREAL-0K4(maxXXREAL-0K5(a,b),b) =HIDDENR1 b"
  using xxreal_0_th_25 xxreal_0_def_9 sorry

mtheorem xxreal_0_th_36:
" for a be ExtRealXXREAL-0M1 holds  for b be ExtRealXXREAL-0M1 holds maxXXREAL-0K5(minXXREAL-0K4(a,b),b) =HIDDENR1 b"
  using xxreal_0_th_17 xxreal_0_def_10 sorry

mtheorem xxreal_0_th_37:
" for a be ExtRealXXREAL-0M1 holds  for b be ExtRealXXREAL-0M1 holds  for c be ExtRealXXREAL-0M1 holds a <=XXREAL-0R1 c implies maxXXREAL-0K5(a,minXXREAL-0K4(b,c)) =HIDDENR1 minXXREAL-0K4(maxXXREAL-0K5(a,b),c)"
sorry

mtheorem xxreal_0_th_38:
" for a be ExtRealXXREAL-0M1 holds  for b be ExtRealXXREAL-0M1 holds  for c be ExtRealXXREAL-0M1 holds minXXREAL-0K4(a,maxXXREAL-0K5(b,c)) =HIDDENR1 maxXXREAL-0K5(minXXREAL-0K4(a,b),minXXREAL-0K4(a,c))"
sorry

mtheorem xxreal_0_th_39:
" for a be ExtRealXXREAL-0M1 holds  for b be ExtRealXXREAL-0M1 holds  for c be ExtRealXXREAL-0M1 holds maxXXREAL-0K5(a,minXXREAL-0K4(b,c)) =HIDDENR1 minXXREAL-0K4(maxXXREAL-0K5(a,b),maxXXREAL-0K5(a,c))"
sorry

mtheorem xxreal_0_th_40:
" for a be ExtRealXXREAL-0M1 holds  for b be ExtRealXXREAL-0M1 holds  for c be ExtRealXXREAL-0M1 holds maxXXREAL-0K5(maxXXREAL-0K5(minXXREAL-0K4(a,b),minXXREAL-0K4(b,c)),minXXREAL-0K4(c,a)) =HIDDENR1 minXXREAL-0K4(minXXREAL-0K4(maxXXREAL-0K5(a,b),maxXXREAL-0K5(b,c)),maxXXREAL-0K5(c,a))"
sorry

mtheorem xxreal_0_th_41:
" for a be ExtRealXXREAL-0M1 holds maxXXREAL-0K5(a,+inftyXXREAL-0K1) =HIDDENR1 +inftyXXREAL-0K1"
sorry

mtheorem xxreal_0_th_42:
" for a be ExtRealXXREAL-0M1 holds minXXREAL-0K4(a,+inftyXXREAL-0K1) =HIDDENR1 a"
sorry

mtheorem xxreal_0_th_43:
" for a be ExtRealXXREAL-0M1 holds maxXXREAL-0K5(a,-inftyXXREAL-0K2) =HIDDENR1 a"
sorry

mtheorem xxreal_0_th_44:
" for a be ExtRealXXREAL-0M1 holds minXXREAL-0K4(a,-inftyXXREAL-0K2) =HIDDENR1 -inftyXXREAL-0K2"
sorry

(*begin*)
mtheorem xxreal_0_th_45:
" for a be ExtRealXXREAL-0M1 holds  for b be ExtRealXXREAL-0M1 holds  for c be ExtRealXXREAL-0M1 holds ((a inHIDDENR3 REALNUMBERSK2 & c inHIDDENR3 REALNUMBERSK2) & a <=XXREAL-0R1 b) & b <=XXREAL-0R1 c implies b inHIDDENR3 REALNUMBERSK2"
sorry

mtheorem xxreal_0_th_46:
" for a be ExtRealXXREAL-0M1 holds  for b be ExtRealXXREAL-0M1 holds  for c be ExtRealXXREAL-0M1 holds (a inHIDDENR3 REALNUMBERSK2 & a <=XXREAL-0R1 b) & b <XXREAL-0R3 c implies b inHIDDENR3 REALNUMBERSK2"
sorry

mtheorem xxreal_0_th_47:
" for a be ExtRealXXREAL-0M1 holds  for b be ExtRealXXREAL-0M1 holds  for c be ExtRealXXREAL-0M1 holds (c inHIDDENR3 REALNUMBERSK2 & a <XXREAL-0R3 b) & b <=XXREAL-0R1 c implies b inHIDDENR3 REALNUMBERSK2"
sorry

mtheorem xxreal_0_th_48:
" for a be ExtRealXXREAL-0M1 holds  for b be ExtRealXXREAL-0M1 holds  for c be ExtRealXXREAL-0M1 holds a <XXREAL-0R3 b & b <XXREAL-0R3 c implies b inHIDDENR3 REALNUMBERSK2"
sorry

mdef xxreal_0_def_11 ("IFGTXXREAL-0K6'( _ , _ , _ , _ ')" [0,0,0,0]164 ) where
  mlet "x be ExtRealXXREAL-0M1", "y be ExtRealXXREAL-0M1", "a be objectHIDDENM1", "b be objectHIDDENM1"
"func IFGTXXREAL-0K6(x,y,a,b) \<rightarrow> objectHIDDENM1 equals
  a if x >XXREAL-0R4 y otherwise b"
proof-
  (*coherence*)
    show "(x >XXREAL-0R4 y implies a be objectHIDDENM1) & ( not x >XXREAL-0R4 y implies b be objectHIDDENM1)"
       sorry
  (*consistency*)
    show " for it be objectHIDDENM1 holds  True "
       sorry
qed "sorry"

mtheorem xxreal_0_cl_20:
  mlet "x be ExtRealXXREAL-0M1", "y be ExtRealXXREAL-0M1", "a be naturalORDINAL1V7\<bar>NumberORDINAL1M1", "b be naturalORDINAL1V7\<bar>NumberORDINAL1M1"
"cluster IFGTXXREAL-0K6(x,y,a,b) as-term-is naturalORDINAL1V7"
proof
(*coherence*)
  show "IFGTXXREAL-0K6(x,y,a,b) be naturalORDINAL1V7"
    using xxreal_0_def_11 sorry
qed "sorry"

mtheorem xxreal_0_th_49:
" for a be ExtRealXXREAL-0M1 holds  for b be ExtRealXXREAL-0M1 holds maxXXREAL-0K5(a,b) <=XXREAL-0R1 a implies maxXXREAL-0K5(a,b) =HIDDENR1 a"
sorry

mtheorem xxreal_0_th_50:
" for a be ExtRealXXREAL-0M1 holds  for b be ExtRealXXREAL-0M1 holds a <=XXREAL-0R1 minXXREAL-0K4(a,b) implies minXXREAL-0K4(a,b) =HIDDENR1 a"
sorry

mtheorem xxreal_0_reduce_1:
  mlet "x be ExtRealXXREAL-0M1"
"reduce InSUBSET-1K10(x,ExtREALXXREAL-0K3) to x"
proof
(*reducibility*)
  show "InSUBSET-1K10(x,ExtREALXXREAL-0K3) =HIDDENR1 x"
    using xxreal_0_def_1 subset_1_def_8 sorry
qed "sorry"

end
