theory xtuple_0
  imports enumset1
begin
(*begin*)
reserve x, x1, x2, x3, x4, y, y1, y2, y3, y4, z, z1, z2, z2, z4 for "objectHIDDENM1"
mdef xtuple_0_def_1 ("pairXTUPLE-0V1" 70 ) where
"attr pairXTUPLE-0V1 for objectHIDDENM1 means
  (\<lambda>x.  ex x1 be objectHIDDENM1 st  ex x2 be objectHIDDENM1 st x =HIDDENR1 [TARSKIK4 x1,x2 ])"..

mtheorem xtuple_0_cl_1:
  mlet "x1 be objectHIDDENM1", "x2 be objectHIDDENM1"
"cluster [TARSKIK4 x1,x2 ] as-term-is pairXTUPLE-0V1"
proof
(*coherence*)
  show "[TARSKIK4 x1,x2 ] be pairXTUPLE-0V1"
     sorry
qed "sorry"

mlemma xtuple_0_lm_1:
" for x be objectHIDDENM1 holds  for y1 be objectHIDDENM1 holds  for y2 be objectHIDDENM1 holds {TARSKIK1 x} =XBOOLE-0R4 {TARSKIK2 y1,y2 } implies x =HIDDENR1 y1"
sorry

mlemma xtuple_0_lm_2:
" for x be objectHIDDENM1 holds  for y1 be objectHIDDENM1 holds  for y2 be objectHIDDENM1 holds {TARSKIK1 x} =XBOOLE-0R4 {TARSKIK2 y1,y2 } implies y1 =HIDDENR1 y2"
sorry

mlemma xtuple_0_lm_3:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for y1 be objectHIDDENM1 holds  for y2 be objectHIDDENM1 holds {TARSKIK2 x1,x2 } =XBOOLE-0R4 {TARSKIK2 y1,y2 } implies x1 =HIDDENR1 y1 or x1 =HIDDENR1 y2"
sorry

mtheorem xtuple_0_th_1:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for y1 be objectHIDDENM1 holds  for y2 be objectHIDDENM1 holds [TARSKIK4 x1,x2 ] =HIDDENR1 [TARSKIK4 y1,y2 ] implies x1 =HIDDENR1 y1 & x2 =HIDDENR1 y2"
sorry

mdef xtuple_0_def_2 (" _ `1XTUPLE-0K1" [355]355 ) where
  mlet "x be objectHIDDENM1"
"assume x be pairXTUPLE-0V1 func x `1XTUPLE-0K1 \<rightarrow> objectHIDDENM1 means
  \<lambda>it.  for y1 be objectHIDDENM1 holds  for y2 be objectHIDDENM1 holds x =HIDDENR1 [TARSKIK4 y1,y2 ] implies it =HIDDENR1 y1"
proof-
  (*existence*)
    show "x be pairXTUPLE-0V1 implies ( ex it be objectHIDDENM1 st  for y1 be objectHIDDENM1 holds  for y2 be objectHIDDENM1 holds x =HIDDENR1 [TARSKIK4 y1,y2 ] implies it =HIDDENR1 y1)"
sorry
  (*uniqueness*)
    show "x be pairXTUPLE-0V1 implies ( for it1 be objectHIDDENM1 holds  for it2 be objectHIDDENM1 holds ( for y1 be objectHIDDENM1 holds  for y2 be objectHIDDENM1 holds x =HIDDENR1 [TARSKIK4 y1,y2 ] implies it1 =HIDDENR1 y1) & ( for y1 be objectHIDDENM1 holds  for y2 be objectHIDDENM1 holds x =HIDDENR1 [TARSKIK4 y1,y2 ] implies it2 =HIDDENR1 y1) implies it1 =HIDDENR1 it2)"
sorry
qed "sorry"

mdef xtuple_0_def_3 (" _ `2XTUPLE-0K2" [355]355 ) where
  mlet "x be objectHIDDENM1"
"assume x be pairXTUPLE-0V1 func x `2XTUPLE-0K2 \<rightarrow> objectHIDDENM1 means
  \<lambda>it.  for y1 be objectHIDDENM1 holds  for y2 be objectHIDDENM1 holds x =HIDDENR1 [TARSKIK4 y1,y2 ] implies it =HIDDENR1 y2"
proof-
  (*existence*)
    show "x be pairXTUPLE-0V1 implies ( ex it be objectHIDDENM1 st  for y1 be objectHIDDENM1 holds  for y2 be objectHIDDENM1 holds x =HIDDENR1 [TARSKIK4 y1,y2 ] implies it =HIDDENR1 y2)"
sorry
  (*uniqueness*)
    show "x be pairXTUPLE-0V1 implies ( for it1 be objectHIDDENM1 holds  for it2 be objectHIDDENM1 holds ( for y1 be objectHIDDENM1 holds  for y2 be objectHIDDENM1 holds x =HIDDENR1 [TARSKIK4 y1,y2 ] implies it1 =HIDDENR1 y2) & ( for y1 be objectHIDDENM1 holds  for y2 be objectHIDDENM1 holds x =HIDDENR1 [TARSKIK4 y1,y2 ] implies it2 =HIDDENR1 y2) implies it1 =HIDDENR1 it2)"
sorry
qed "sorry"

mtheorem xtuple_0_reduce_1:
  mlet "x1 be objectHIDDENM1", "x2 be objectHIDDENM1"
"reduce [TARSKIK4 x1,x2 ] `1XTUPLE-0K1 to x1"
proof
(*reducibility*)
  show "[TARSKIK4 x1,x2 ] `1XTUPLE-0K1 =HIDDENR1 x1"
    using xtuple_0_def_2 sorry
qed "sorry"

mtheorem xtuple_0_reduce_2:
  mlet "x1 be objectHIDDENM1", "x2 be objectHIDDENM1"
"reduce [TARSKIK4 x1,x2 ] `2XTUPLE-0K2 to x2"
proof
(*reducibility*)
  show "[TARSKIK4 x1,x2 ] `2XTUPLE-0K2 =HIDDENR1 x2"
    using xtuple_0_def_3 sorry
qed "sorry"

mtheorem xtuple_0_cl_2:
"cluster pairXTUPLE-0V1 for objectHIDDENM1"
proof
(*existence*)
  show " ex it be objectHIDDENM1 st it be pairXTUPLE-0V1"
sorry
qed "sorry"

mtheorem xtuple_0_reduce_3:
  mlet "x be pairXTUPLE-0V1\<bar>objectHIDDENM1"
"reduce [TARSKIK4 x `1XTUPLE-0K1,x `2XTUPLE-0K2 ] to x"
proof
(*reducibility*)
  show "[TARSKIK4 x `1XTUPLE-0K1,x `2XTUPLE-0K2 ] =HIDDENR1 x"
sorry
qed "sorry"

mtheorem xtuple_0_th_2:
" for a be pairXTUPLE-0V1\<bar>objectHIDDENM1 holds  for b be pairXTUPLE-0V1\<bar>objectHIDDENM1 holds a `1XTUPLE-0K1 =HIDDENR1 b `1XTUPLE-0K1 & a `2XTUPLE-0K2 =HIDDENR1 b `2XTUPLE-0K2 implies a =HIDDENR1 b"
sorry

(*begin*)
mdef xtuple_0_def_4 ("[XTUPLE-0K3 _ , _ , _ ]" [0,0,0]356 ) where
  mlet "x1 be objectHIDDENM1", "x2 be objectHIDDENM1", "x3 be objectHIDDENM1"
"func [XTUPLE-0K3 x1,x2,x3 ] \<rightarrow> objectHIDDENM1 equals
  [TARSKIK4 [TARSKIK4 x1,x2 ],x3 ]"
proof-
  (*coherence*)
    show "[TARSKIK4 [TARSKIK4 x1,x2 ],x3 ] be objectHIDDENM1"
       sorry
qed "sorry"

mdef xtuple_0_def_5 ("tripleXTUPLE-0V2" 70 ) where
"attr tripleXTUPLE-0V2 for objectHIDDENM1 means
  (\<lambda>x.  ex x1 be objectHIDDENM1 st  ex x2 be objectHIDDENM1 st  ex x3 be objectHIDDENM1 st x =HIDDENR1 [XTUPLE-0K3 x1,x2,x3 ])"..

mtheorem xtuple_0_cl_3:
  mlet "x1 be objectHIDDENM1", "x2 be objectHIDDENM1", "x3 be objectHIDDENM1"
"cluster [XTUPLE-0K3 x1,x2,x3 ] as-term-is tripleXTUPLE-0V2"
proof
(*coherence*)
  show "[XTUPLE-0K3 x1,x2,x3 ] be tripleXTUPLE-0V2"
     sorry
qed "sorry"

mtheorem xtuple_0_th_3:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for y1 be objectHIDDENM1 holds  for y2 be objectHIDDENM1 holds  for y3 be objectHIDDENM1 holds [XTUPLE-0K3 x1,x2,x3 ] =HIDDENR1 [XTUPLE-0K3 y1,y2,y3 ] implies (x1 =HIDDENR1 y1 & x2 =HIDDENR1 y2) & x3 =HIDDENR1 y3"
sorry

mtheorem xtuple_0_cl_4:
"cluster tripleXTUPLE-0V2 for objectHIDDENM1"
proof
(*existence*)
  show " ex it be objectHIDDENM1 st it be tripleXTUPLE-0V2"
sorry
qed "sorry"

mtheorem xtuple_0_cl_5:
"cluster tripleXTUPLE-0V2 also-is pairXTUPLE-0V1 for objectHIDDENM1"
proof
(*coherence*)
  show " for it be objectHIDDENM1 holds it be tripleXTUPLE-0V2 implies it be pairXTUPLE-0V1"
     sorry
qed "sorry"

mdef xtuple_0_def_6 (" _ `1-3XTUPLE-0K4" [164]164 ) where
  mlet "x be objectHIDDENM1"
"func x `1-3XTUPLE-0K4 \<rightarrow> objectHIDDENM1 equals
  (x `1XTUPLE-0K1)`1XTUPLE-0K1"
proof-
  (*coherence*)
    show "(x `1XTUPLE-0K1)`1XTUPLE-0K1 be objectHIDDENM1"
       sorry
qed "sorry"

mdef xtuple_0_def_7 (" _ `2-3XTUPLE-0K5" [164]164 ) where
  mlet "x be objectHIDDENM1"
"func x `2-3XTUPLE-0K5 \<rightarrow> objectHIDDENM1 equals
  (x `1XTUPLE-0K1)`2XTUPLE-0K2"
proof-
  (*coherence*)
    show "(x `1XTUPLE-0K1)`2XTUPLE-0K2 be objectHIDDENM1"
       sorry
qed "sorry"

abbreviation(input) XTUPLE_0K6(" _ `3-3XTUPLE-0K6" [164]164) where
  "x `3-3XTUPLE-0K6 \<equiv> x `2XTUPLE-0K2"

mtheorem xtuple_0_reduce_4:
  mlet "x1 be objectHIDDENM1", "x2 be objectHIDDENM1", "x3 be objectHIDDENM1"
"reduce [XTUPLE-0K3 x1,x2,x3 ] `1-3XTUPLE-0K4 to x1"
proof
(*reducibility*)
  show "[XTUPLE-0K3 x1,x2,x3 ] `1-3XTUPLE-0K4 =HIDDENR1 x1"
     sorry
qed "sorry"

mtheorem xtuple_0_reduce_5:
  mlet "x1 be objectHIDDENM1", "x2 be objectHIDDENM1", "x3 be objectHIDDENM1"
"reduce [XTUPLE-0K3 x1,x2,x3 ] `2-3XTUPLE-0K5 to x2"
proof
(*reducibility*)
  show "[XTUPLE-0K3 x1,x2,x3 ] `2-3XTUPLE-0K5 =HIDDENR1 x2"
     sorry
qed "sorry"

mtheorem xtuple_0_reduce_6:
  mlet "x1 be objectHIDDENM1", "x2 be objectHIDDENM1", "x3 be objectHIDDENM1"
"reduce [XTUPLE-0K3 x1,x2,x3 ] `3-3XTUPLE-0K6 to x3"
proof
(*reducibility*)
  show "[XTUPLE-0K3 x1,x2,x3 ] `3-3XTUPLE-0K6 =HIDDENR1 x3"
     sorry
qed "sorry"

mtheorem xtuple_0_reduce_7:
  mlet "x be tripleXTUPLE-0V2\<bar>objectHIDDENM1"
"reduce [XTUPLE-0K3 x `1-3XTUPLE-0K4,x `2-3XTUPLE-0K5,x `3-3XTUPLE-0K6 ] to x"
proof
(*reducibility*)
  show "[XTUPLE-0K3 x `1-3XTUPLE-0K4,x `2-3XTUPLE-0K5,x `3-3XTUPLE-0K6 ] =HIDDENR1 x"
sorry
qed "sorry"

mtheorem xtuple_0_th_4:
" for a be tripleXTUPLE-0V2\<bar>objectHIDDENM1 holds  for b be tripleXTUPLE-0V2\<bar>objectHIDDENM1 holds (a `1-3XTUPLE-0K4 =HIDDENR1 b `1-3XTUPLE-0K4 & a `2-3XTUPLE-0K5 =HIDDENR1 b `2-3XTUPLE-0K5) & a `3-3XTUPLE-0K6 =HIDDENR1 b `3-3XTUPLE-0K6 implies a =HIDDENR1 b"
sorry

(*begin*)
mdef xtuple_0_def_8 ("[XTUPLE-0K7 _ , _ , _ , _ ]" [0,0,0,0]356 ) where
  mlet "x1 be objectHIDDENM1", "x2 be objectHIDDENM1", "x3 be objectHIDDENM1", "x4 be objectHIDDENM1"
"func [XTUPLE-0K7 x1,x2,x3,x4 ] \<rightarrow> objectHIDDENM1 equals
  [TARSKIK4 [XTUPLE-0K3 x1,x2,x3 ],x4 ]"
proof-
  (*coherence*)
    show "[TARSKIK4 [XTUPLE-0K3 x1,x2,x3 ],x4 ] be objectHIDDENM1"
       sorry
qed "sorry"

mdef xtuple_0_def_9 ("quadrupleXTUPLE-0V3" 70 ) where
"attr quadrupleXTUPLE-0V3 for objectHIDDENM1 means
  (\<lambda>x.  ex x1 be objectHIDDENM1 st  ex x2 be objectHIDDENM1 st  ex x3 be objectHIDDENM1 st  ex x4 be objectHIDDENM1 st x =HIDDENR1 [XTUPLE-0K7 x1,x2,x3,x4 ])"..

mtheorem xtuple_0_cl_6:
  mlet "x1 be objectHIDDENM1", "x2 be objectHIDDENM1", "x3 be objectHIDDENM1", "x4 be objectHIDDENM1"
"cluster [XTUPLE-0K7 x1,x2,x3,x4 ] as-term-is quadrupleXTUPLE-0V3"
proof
(*coherence*)
  show "[XTUPLE-0K7 x1,x2,x3,x4 ] be quadrupleXTUPLE-0V3"
     sorry
qed "sorry"

mtheorem xtuple_0_th_5:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for x4 be objectHIDDENM1 holds  for y1 be objectHIDDENM1 holds  for y2 be objectHIDDENM1 holds  for y3 be objectHIDDENM1 holds  for y4 be objectHIDDENM1 holds [XTUPLE-0K7 x1,x2,x3,x4 ] =HIDDENR1 [XTUPLE-0K7 y1,y2,y3,y4 ] implies ((x1 =HIDDENR1 y1 & x2 =HIDDENR1 y2) & x3 =HIDDENR1 y3) & x4 =HIDDENR1 y4"
sorry

mtheorem xtuple_0_cl_7:
"cluster quadrupleXTUPLE-0V3 for objectHIDDENM1"
proof
(*existence*)
  show " ex it be objectHIDDENM1 st it be quadrupleXTUPLE-0V3"
sorry
qed "sorry"

mtheorem xtuple_0_cl_8:
"cluster quadrupleXTUPLE-0V3 also-is tripleXTUPLE-0V2 for objectHIDDENM1"
proof
(*coherence*)
  show " for it be objectHIDDENM1 holds it be quadrupleXTUPLE-0V3 implies it be tripleXTUPLE-0V2"
sorry
qed "sorry"

mdef xtuple_0_def_10 (" _ `1-4XTUPLE-0K8" [164]164 ) where
  mlet "x be objectHIDDENM1"
"func x `1-4XTUPLE-0K8 \<rightarrow> objectHIDDENM1 equals
  ((x `1XTUPLE-0K1)`1XTUPLE-0K1)`1XTUPLE-0K1"
proof-
  (*coherence*)
    show "((x `1XTUPLE-0K1)`1XTUPLE-0K1)`1XTUPLE-0K1 be objectHIDDENM1"
       sorry
qed "sorry"

mdef xtuple_0_def_11 (" _ `2-4XTUPLE-0K9" [164]164 ) where
  mlet "x be objectHIDDENM1"
"func x `2-4XTUPLE-0K9 \<rightarrow> objectHIDDENM1 equals
  ((x `1XTUPLE-0K1)`1XTUPLE-0K1)`2XTUPLE-0K2"
proof-
  (*coherence*)
    show "((x `1XTUPLE-0K1)`1XTUPLE-0K1)`2XTUPLE-0K2 be objectHIDDENM1"
       sorry
qed "sorry"

abbreviation(input) XTUPLE_0K10(" _ `3-4XTUPLE-0K10" [164]164) where
  "x `3-4XTUPLE-0K10 \<equiv> x `2-3XTUPLE-0K5"

abbreviation(input) XTUPLE_0K11(" _ `4-4XTUPLE-0K11" [164]164) where
  "x `4-4XTUPLE-0K11 \<equiv> x `2XTUPLE-0K2"

mtheorem xtuple_0_reduce_8:
  mlet "x1 be objectHIDDENM1", "x2 be objectHIDDENM1", "x3 be objectHIDDENM1", "x4 be objectHIDDENM1"
"reduce [XTUPLE-0K7 x1,x2,x3,x4 ] `1-4XTUPLE-0K8 to x1"
proof
(*reducibility*)
  show "[XTUPLE-0K7 x1,x2,x3,x4 ] `1-4XTUPLE-0K8 =HIDDENR1 x1"
     sorry
qed "sorry"

mtheorem xtuple_0_reduce_9:
  mlet "x1 be objectHIDDENM1", "x2 be objectHIDDENM1", "x3 be objectHIDDENM1", "x4 be objectHIDDENM1"
"reduce [XTUPLE-0K7 x1,x2,x3,x4 ] `2-4XTUPLE-0K9 to x2"
proof
(*reducibility*)
  show "[XTUPLE-0K7 x1,x2,x3,x4 ] `2-4XTUPLE-0K9 =HIDDENR1 x2"
     sorry
qed "sorry"

mtheorem xtuple_0_reduce_10:
  mlet "x1 be objectHIDDENM1", "x2 be objectHIDDENM1", "x3 be objectHIDDENM1", "x4 be objectHIDDENM1"
"reduce [XTUPLE-0K7 x1,x2,x3,x4 ] `3-4XTUPLE-0K10 to x3"
proof
(*reducibility*)
  show "[XTUPLE-0K7 x1,x2,x3,x4 ] `3-4XTUPLE-0K10 =HIDDENR1 x3"
     sorry
qed "sorry"

mtheorem xtuple_0_reduce_11:
  mlet "x1 be objectHIDDENM1", "x2 be objectHIDDENM1", "x3 be objectHIDDENM1", "x4 be objectHIDDENM1"
"reduce [XTUPLE-0K7 x1,x2,x3,x4 ] `4-4XTUPLE-0K11 to x4"
proof
(*reducibility*)
  show "[XTUPLE-0K7 x1,x2,x3,x4 ] `4-4XTUPLE-0K11 =HIDDENR1 x4"
     sorry
qed "sorry"

mtheorem xtuple_0_reduce_12:
  mlet "x be quadrupleXTUPLE-0V3\<bar>objectHIDDENM1"
"reduce [XTUPLE-0K7 x `1-4XTUPLE-0K8,x `2-4XTUPLE-0K9,x `3-4XTUPLE-0K10,x `4-4XTUPLE-0K11 ] to x"
proof
(*reducibility*)
  show "[XTUPLE-0K7 x `1-4XTUPLE-0K8,x `2-4XTUPLE-0K9,x `3-4XTUPLE-0K10,x `4-4XTUPLE-0K11 ] =HIDDENR1 x"
sorry
qed "sorry"

reserve X, X1, X2, X3, X4, Y for "setHIDDENM2"
mtheorem xtuple_0_th_6:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for X be setHIDDENM2 holds [TARSKIK4 x,y ] inHIDDENR3 X implies x inHIDDENR3 unionTARSKIK3 (unionTARSKIK3 X)"
sorry

mtheorem xtuple_0_th_7:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for X be setHIDDENM2 holds [TARSKIK4 x,y ] inHIDDENR3 X implies y inHIDDENR3 unionTARSKIK3 (unionTARSKIK3 X)"
sorry

mdef xtuple_0_def_12 ("proj1XTUPLE-0K12  _ " [228]228 ) where
  mlet "X be setHIDDENM2"
"func proj1XTUPLE-0K12 X \<rightarrow> setHIDDENM2 means
  \<lambda>it.  for x be objectHIDDENM1 holds x inHIDDENR3 it iff ( ex y be objectHIDDENM1 st [TARSKIK4 x,y ] inHIDDENR3 X)"
proof-
  (*existence*)
    show " ex it be setHIDDENM2 st  for x be objectHIDDENM1 holds x inHIDDENR3 it iff ( ex y be objectHIDDENM1 st [TARSKIK4 x,y ] inHIDDENR3 X)"
sorry
  (*uniqueness*)
    show " for it1 be setHIDDENM2 holds  for it2 be setHIDDENM2 holds ( for x be objectHIDDENM1 holds x inHIDDENR3 it1 iff ( ex y be objectHIDDENM1 st [TARSKIK4 x,y ] inHIDDENR3 X)) & ( for x be objectHIDDENM1 holds x inHIDDENR3 it2 iff ( ex y be objectHIDDENM1 st [TARSKIK4 x,y ] inHIDDENR3 X)) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mdef xtuple_0_def_13 ("proj2XTUPLE-0K13  _ " [228]228 ) where
  mlet "X be setHIDDENM2"
"func proj2XTUPLE-0K13 X \<rightarrow> setHIDDENM2 means
  \<lambda>it.  for x be objectHIDDENM1 holds x inHIDDENR3 it iff ( ex y be objectHIDDENM1 st [TARSKIK4 y,x ] inHIDDENR3 X)"
proof-
  (*existence*)
    show " ex it be setHIDDENM2 st  for x be objectHIDDENM1 holds x inHIDDENR3 it iff ( ex y be objectHIDDENM1 st [TARSKIK4 y,x ] inHIDDENR3 X)"
sorry
  (*uniqueness*)
    show " for it1 be setHIDDENM2 holds  for it2 be setHIDDENM2 holds ( for x be objectHIDDENM1 holds x inHIDDENR3 it1 iff ( ex y be objectHIDDENM1 st [TARSKIK4 y,x ] inHIDDENR3 X)) & ( for x be objectHIDDENM1 holds x inHIDDENR3 it2 iff ( ex y be objectHIDDENM1 st [TARSKIK4 y,x ] inHIDDENR3 X)) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mtheorem xtuple_0_th_8:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X c=TARSKIR1 Y implies proj1XTUPLE-0K12 X c=TARSKIR1 proj1XTUPLE-0K12 Y"
sorry

mtheorem xtuple_0_th_9:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X c=TARSKIR1 Y implies proj2XTUPLE-0K13 X c=TARSKIR1 proj2XTUPLE-0K13 Y"
sorry

mdef xtuple_0_def_14 ("proj1-3XTUPLE-0K14  _ " [164]164 ) where
  mlet "X be setHIDDENM2"
"func proj1-3XTUPLE-0K14 X \<rightarrow> setHIDDENM2 equals
  proj1XTUPLE-0K12 (proj1XTUPLE-0K12 X)"
proof-
  (*coherence*)
    show "proj1XTUPLE-0K12 (proj1XTUPLE-0K12 X) be setHIDDENM2"
       sorry
qed "sorry"

mdef xtuple_0_def_15 ("proj2-3XTUPLE-0K15  _ " [164]164 ) where
  mlet "X be setHIDDENM2"
"func proj2-3XTUPLE-0K15 X \<rightarrow> setHIDDENM2 equals
  proj2XTUPLE-0K13 (proj1XTUPLE-0K12 X)"
proof-
  (*coherence*)
    show "proj2XTUPLE-0K13 (proj1XTUPLE-0K12 X) be setHIDDENM2"
       sorry
qed "sorry"

abbreviation(input) XTUPLE_0K16("proj3-3XTUPLE-0K16  _ " [164]164) where
  "proj3-3XTUPLE-0K16 X \<equiv> proj2XTUPLE-0K13 X"

mtheorem xtuple_0_th_10:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X c=TARSKIR1 Y implies proj1-3XTUPLE-0K14 X c=TARSKIR1 proj1-3XTUPLE-0K14 Y"
sorry

mtheorem xtuple_0_th_11:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X c=TARSKIR1 Y implies proj2-3XTUPLE-0K15 X c=TARSKIR1 proj2-3XTUPLE-0K15 Y"
sorry

mtheorem xtuple_0_th_12:
" for x be objectHIDDENM1 holds  for X be setHIDDENM2 holds x inHIDDENR3 proj1-3XTUPLE-0K14 X implies ( ex y be objectHIDDENM1 st  ex z be objectHIDDENM1 st [XTUPLE-0K3 x,y,z ] inHIDDENR3 X)"
sorry

mtheorem xtuple_0_th_13:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for z be objectHIDDENM1 holds  for X be setHIDDENM2 holds [XTUPLE-0K3 x,y,z ] inHIDDENR3 X implies x inHIDDENR3 proj1-3XTUPLE-0K14 X"
sorry

mtheorem xtuple_0_th_14:
" for x be objectHIDDENM1 holds  for X be setHIDDENM2 holds x inHIDDENR3 proj2-3XTUPLE-0K15 X implies ( ex y be objectHIDDENM1 st  ex z be objectHIDDENM1 st [XTUPLE-0K3 y,x,z ] inHIDDENR3 X)"
sorry

mtheorem xtuple_0_th_15:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for z be objectHIDDENM1 holds  for X be setHIDDENM2 holds [XTUPLE-0K3 x,y,z ] inHIDDENR3 X implies y inHIDDENR3 proj2-3XTUPLE-0K15 X"
sorry

mdef xtuple_0_def_16 ("proj1-4XTUPLE-0K17  _ " [164]164 ) where
  mlet "X be setHIDDENM2"
"func proj1-4XTUPLE-0K17 X \<rightarrow> setHIDDENM2 equals
  proj1XTUPLE-0K12 (proj1-3XTUPLE-0K14 X)"
proof-
  (*coherence*)
    show "proj1XTUPLE-0K12 (proj1-3XTUPLE-0K14 X) be setHIDDENM2"
       sorry
qed "sorry"

mdef xtuple_0_def_17 ("proj2-4XTUPLE-0K18  _ " [164]164 ) where
  mlet "X be setHIDDENM2"
"func proj2-4XTUPLE-0K18 X \<rightarrow> setHIDDENM2 equals
  proj2XTUPLE-0K13 (proj1-3XTUPLE-0K14 X)"
proof-
  (*coherence*)
    show "proj2XTUPLE-0K13 (proj1-3XTUPLE-0K14 X) be setHIDDENM2"
       sorry
qed "sorry"

abbreviation(input) XTUPLE_0K19("proj3-4XTUPLE-0K19  _ " [164]164) where
  "proj3-4XTUPLE-0K19 X \<equiv> proj2-3XTUPLE-0K15 X"

abbreviation(input) XTUPLE_0K20("proj4-4XTUPLE-0K20  _ " [164]164) where
  "proj4-4XTUPLE-0K20 X \<equiv> proj2XTUPLE-0K13 X"

mtheorem xtuple_0_th_16:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X c=TARSKIR1 Y implies proj1-4XTUPLE-0K17 X c=TARSKIR1 proj1-4XTUPLE-0K17 Y"
sorry

mtheorem xtuple_0_th_17:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X c=TARSKIR1 Y implies proj2-4XTUPLE-0K18 X c=TARSKIR1 proj2-4XTUPLE-0K18 Y"
sorry

mtheorem xtuple_0_th_18:
" for x be objectHIDDENM1 holds  for X be setHIDDENM2 holds x inHIDDENR3 proj1-4XTUPLE-0K17 X implies ( ex x1 be objectHIDDENM1 st  ex x2 be objectHIDDENM1 st  ex x3 be objectHIDDENM1 st [XTUPLE-0K7 x,x1,x2,x3 ] inHIDDENR3 X)"
sorry

mtheorem xtuple_0_th_19:
" for x be objectHIDDENM1 holds  for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for X be setHIDDENM2 holds [XTUPLE-0K7 x,x1,x2,x3 ] inHIDDENR3 X implies x inHIDDENR3 proj1-4XTUPLE-0K17 X"
sorry

mtheorem xtuple_0_th_20:
" for x be objectHIDDENM1 holds  for X be setHIDDENM2 holds x inHIDDENR3 proj2-4XTUPLE-0K18 X implies ( ex x1 be objectHIDDENM1 st  ex x2 be objectHIDDENM1 st  ex x3 be objectHIDDENM1 st [XTUPLE-0K7 x1,x,x2,x3 ] inHIDDENR3 X)"
sorry

mtheorem xtuple_0_th_21:
" for x be objectHIDDENM1 holds  for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for X be setHIDDENM2 holds [XTUPLE-0K7 x1,x,x2,x3 ] inHIDDENR3 X implies x inHIDDENR3 proj2-4XTUPLE-0K18 X"
sorry

mtheorem xtuple_0_th_22:
" for a be quadrupleXTUPLE-0V3\<bar>objectHIDDENM1 holds  for b be quadrupleXTUPLE-0V3\<bar>objectHIDDENM1 holds ((a `1-4XTUPLE-0K8 =HIDDENR1 b `1-4XTUPLE-0K8 & a `2-4XTUPLE-0K9 =HIDDENR1 b `2-4XTUPLE-0K9) & a `3-4XTUPLE-0K10 =HIDDENR1 b `3-4XTUPLE-0K10) & a `4-4XTUPLE-0K11 =HIDDENR1 b `4-4XTUPLE-0K11 implies a =HIDDENR1 b"
sorry

(*begin*)
mtheorem xtuple_0_cl_9:
  mlet "X be emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster proj1XTUPLE-0K12 X as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "proj1XTUPLE-0K12 X be emptyXBOOLE-0V1"
sorry
qed "sorry"

mtheorem xtuple_0_cl_10:
  mlet "X be emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster proj2XTUPLE-0K13 X as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "proj2XTUPLE-0K13 X be emptyXBOOLE-0V1"
sorry
qed "sorry"

mtheorem xtuple_0_cl_11:
  mlet "X be emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster proj1-3XTUPLE-0K14 X as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "proj1-3XTUPLE-0K14 X be emptyXBOOLE-0V1"
     sorry
qed "sorry"

mtheorem xtuple_0_cl_12:
  mlet "X be emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster proj2-3XTUPLE-0K15 X as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "proj2-3XTUPLE-0K15 X be emptyXBOOLE-0V1"
     sorry
qed "sorry"

mtheorem xtuple_0_cl_13:
  mlet "X be emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster proj1-4XTUPLE-0K17 X as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "proj1-4XTUPLE-0K17 X be emptyXBOOLE-0V1"
     sorry
qed "sorry"

mtheorem xtuple_0_cl_14:
  mlet "X be emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster proj2-4XTUPLE-0K18 X as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "proj2-4XTUPLE-0K18 X be emptyXBOOLE-0V1"
     sorry
qed "sorry"

mtheorem xtuple_0_th_23:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds proj1XTUPLE-0K12 (X \\/XBOOLE-0K2 Y) =XBOOLE-0R4 proj1XTUPLE-0K12 X \\/XBOOLE-0K2 proj1XTUPLE-0K12 Y"
sorry

mtheorem xtuple_0_th_24:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds proj1XTUPLE-0K12 (X /\\XBOOLE-0K3 Y) c=TARSKIR1 proj1XTUPLE-0K12 X /\\XBOOLE-0K3 proj1XTUPLE-0K12 Y"
sorry

mtheorem xtuple_0_th_25:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds proj1XTUPLE-0K12 X \\XBOOLE-0K4 proj1XTUPLE-0K12 Y c=TARSKIR1 proj1XTUPLE-0K12 (X \\XBOOLE-0K4 Y)"
sorry

mtheorem xtuple_0_th_26:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds proj1XTUPLE-0K12 X \\+\\XBOOLE-0K5 proj1XTUPLE-0K12 Y c=TARSKIR1 proj1XTUPLE-0K12 (X \\+\\XBOOLE-0K5 Y)"
sorry

mtheorem xtuple_0_th_27:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds proj2XTUPLE-0K13 (X \\/XBOOLE-0K2 Y) =XBOOLE-0R4 proj2XTUPLE-0K13 X \\/XBOOLE-0K2 proj2XTUPLE-0K13 Y"
sorry

mtheorem xtuple_0_th_28:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds proj2XTUPLE-0K13 (X /\\XBOOLE-0K3 Y) c=TARSKIR1 proj2XTUPLE-0K13 X /\\XBOOLE-0K3 proj2XTUPLE-0K13 Y"
sorry

mtheorem xtuple_0_th_29:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds proj2XTUPLE-0K13 X \\XBOOLE-0K4 proj2XTUPLE-0K13 Y c=TARSKIR1 proj2XTUPLE-0K13 (X \\XBOOLE-0K4 Y)"
sorry

mtheorem xtuple_0_th_30:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds proj2XTUPLE-0K13 X \\+\\XBOOLE-0K5 proj2XTUPLE-0K13 Y c=TARSKIR1 proj2XTUPLE-0K13 (X \\+\\XBOOLE-0K5 Y)"
sorry

mtheorem xtuple_0_th_31:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds proj1-3XTUPLE-0K14 (X \\/XBOOLE-0K2 Y) =XBOOLE-0R4 proj1-3XTUPLE-0K14 X \\/XBOOLE-0K2 proj1-3XTUPLE-0K14 Y"
sorry

mtheorem xtuple_0_th_32:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds proj1-3XTUPLE-0K14 (X /\\XBOOLE-0K3 Y) c=TARSKIR1 (proj1-3XTUPLE-0K14 X)/\\XBOOLE-0K3 (proj1-3XTUPLE-0K14 Y)"
sorry

mtheorem xtuple_0_th_33:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds proj1-3XTUPLE-0K14 X \\XBOOLE-0K4 proj1-3XTUPLE-0K14 Y c=TARSKIR1 proj1-3XTUPLE-0K14 (X \\XBOOLE-0K4 Y)"
sorry

mtheorem xtuple_0_th_34:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds proj1-3XTUPLE-0K14 X \\+\\XBOOLE-0K5 proj1-3XTUPLE-0K14 Y c=TARSKIR1 proj1-3XTUPLE-0K14 (X \\+\\XBOOLE-0K5 Y)"
sorry

mtheorem xtuple_0_th_35:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds proj2-3XTUPLE-0K15 (X \\/XBOOLE-0K2 Y) =XBOOLE-0R4 proj2-3XTUPLE-0K15 X \\/XBOOLE-0K2 proj2-3XTUPLE-0K15 Y"
sorry

mtheorem xtuple_0_th_36:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds proj2-3XTUPLE-0K15 (X /\\XBOOLE-0K3 Y) c=TARSKIR1 (proj2-3XTUPLE-0K15 X)/\\XBOOLE-0K3 (proj2-3XTUPLE-0K15 Y)"
sorry

mtheorem xtuple_0_th_37:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds proj2-3XTUPLE-0K15 X \\XBOOLE-0K4 proj2-3XTUPLE-0K15 Y c=TARSKIR1 proj2-3XTUPLE-0K15 (X \\XBOOLE-0K4 Y)"
sorry

mtheorem xtuple_0_th_38:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds proj2-3XTUPLE-0K15 X \\+\\XBOOLE-0K5 proj2-3XTUPLE-0K15 Y c=TARSKIR1 proj2-3XTUPLE-0K15 (X \\+\\XBOOLE-0K5 Y)"
sorry

mtheorem xtuple_0_th_39:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds proj1-4XTUPLE-0K17 (X \\/XBOOLE-0K2 Y) =XBOOLE-0R4 proj1-4XTUPLE-0K17 X \\/XBOOLE-0K2 proj1-4XTUPLE-0K17 Y"
sorry

mtheorem xtuple_0_th_40:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds proj1-4XTUPLE-0K17 (X /\\XBOOLE-0K3 Y) c=TARSKIR1 (proj1-4XTUPLE-0K17 X)/\\XBOOLE-0K3 (proj1-4XTUPLE-0K17 Y)"
sorry

mtheorem xtuple_0_th_41:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds proj1-4XTUPLE-0K17 X \\XBOOLE-0K4 proj1-4XTUPLE-0K17 Y c=TARSKIR1 proj1-4XTUPLE-0K17 (X \\XBOOLE-0K4 Y)"
sorry

mtheorem xtuple_0_th_42:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds proj1-4XTUPLE-0K17 X \\+\\XBOOLE-0K5 proj1-4XTUPLE-0K17 Y c=TARSKIR1 proj1-4XTUPLE-0K17 (X \\+\\XBOOLE-0K5 Y)"
sorry

mtheorem xtuple_0_th_43:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds proj2-4XTUPLE-0K18 (X \\/XBOOLE-0K2 Y) =XBOOLE-0R4 proj2-4XTUPLE-0K18 X \\/XBOOLE-0K2 proj2-4XTUPLE-0K18 Y"
sorry

mtheorem xtuple_0_th_44:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds proj2-4XTUPLE-0K18 (X /\\XBOOLE-0K3 Y) c=TARSKIR1 (proj2-4XTUPLE-0K18 X)/\\XBOOLE-0K3 (proj2-4XTUPLE-0K18 Y)"
sorry

mtheorem xtuple_0_th_45:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds proj2-4XTUPLE-0K18 X \\XBOOLE-0K4 proj2-4XTUPLE-0K18 Y c=TARSKIR1 proj2-4XTUPLE-0K18 (X \\XBOOLE-0K4 Y)"
sorry

mtheorem xtuple_0_th_46:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds proj2-4XTUPLE-0K18 X \\+\\XBOOLE-0K5 proj2-4XTUPLE-0K18 Y c=TARSKIR1 proj2-4XTUPLE-0K18 (X \\+\\XBOOLE-0K5 Y)"
sorry

end
