theory enumset1
  imports xboole_1
begin
(*begin*)
reserve x, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, y for "objectHIDDENM1"
reserve X, Z for "setHIDDENM2"
mlemma enumset1_lm_1:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for X be setHIDDENM2 holds x inHIDDENR3 unionTARSKIK3 {TARSKIK2 X,{TARSKIK1 y} } iff x inHIDDENR3 X or x =HIDDENR1 y"
sorry

mdef enumset1_def_1 ("{ENUMSET1K1 _ , _ , _ }" [0,0,0]356 ) where
  mlet "x1 be objectHIDDENM1", "x2 be objectHIDDENM1", "x3 be objectHIDDENM1"
"func {ENUMSET1K1 x1,x2,x3 } \<rightarrow> setHIDDENM2 means
  \<lambda>it.  for x be objectHIDDENM1 holds x inHIDDENR3 it iff (x =HIDDENR1 x1 or x =HIDDENR1 x2) or x =HIDDENR1 x3"
proof-
  (*existence*)
    show " ex it be setHIDDENM2 st  for x be objectHIDDENM1 holds x inHIDDENR3 it iff (x =HIDDENR1 x1 or x =HIDDENR1 x2) or x =HIDDENR1 x3"
sorry
  (*uniqueness*)
    show " for it1 be setHIDDENM2 holds  for it2 be setHIDDENM2 holds ( for x be objectHIDDENM1 holds x inHIDDENR3 it1 iff (x =HIDDENR1 x1 or x =HIDDENR1 x2) or x =HIDDENR1 x3) & ( for x be objectHIDDENM1 holds x inHIDDENR3 it2 iff (x =HIDDENR1 x1 or x =HIDDENR1 x2) or x =HIDDENR1 x3) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mdef enumset1_def_2 ("{ENUMSET1K2 _ , _ , _ , _ }" [0,0,0,0]356 ) where
  mlet "x1 be objectHIDDENM1", "x2 be objectHIDDENM1", "x3 be objectHIDDENM1", "x4 be objectHIDDENM1"
"func {ENUMSET1K2 x1,x2,x3,x4 } \<rightarrow> setHIDDENM2 means
  \<lambda>it.  for x be objectHIDDENM1 holds x inHIDDENR3 it iff ((x =HIDDENR1 x1 or x =HIDDENR1 x2) or x =HIDDENR1 x3) or x =HIDDENR1 x4"
proof-
  (*existence*)
    show " ex it be setHIDDENM2 st  for x be objectHIDDENM1 holds x inHIDDENR3 it iff ((x =HIDDENR1 x1 or x =HIDDENR1 x2) or x =HIDDENR1 x3) or x =HIDDENR1 x4"
sorry
  (*uniqueness*)
    show " for it1 be setHIDDENM2 holds  for it2 be setHIDDENM2 holds ( for x be objectHIDDENM1 holds x inHIDDENR3 it1 iff ((x =HIDDENR1 x1 or x =HIDDENR1 x2) or x =HIDDENR1 x3) or x =HIDDENR1 x4) & ( for x be objectHIDDENM1 holds x inHIDDENR3 it2 iff ((x =HIDDENR1 x1 or x =HIDDENR1 x2) or x =HIDDENR1 x3) or x =HIDDENR1 x4) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mdef enumset1_def_3 ("{ENUMSET1K3 _ , _ , _ , _ , _ }" [0,0,0,0,0]356 ) where
  mlet "x1 be objectHIDDENM1", "x2 be objectHIDDENM1", "x3 be objectHIDDENM1", "x4 be objectHIDDENM1", "x5 be objectHIDDENM1"
"func {ENUMSET1K3 x1,x2,x3,x4,x5 } \<rightarrow> setHIDDENM2 means
  \<lambda>it.  for x be objectHIDDENM1 holds x inHIDDENR3 it iff (((x =HIDDENR1 x1 or x =HIDDENR1 x2) or x =HIDDENR1 x3) or x =HIDDENR1 x4) or x =HIDDENR1 x5"
proof-
  (*existence*)
    show " ex it be setHIDDENM2 st  for x be objectHIDDENM1 holds x inHIDDENR3 it iff (((x =HIDDENR1 x1 or x =HIDDENR1 x2) or x =HIDDENR1 x3) or x =HIDDENR1 x4) or x =HIDDENR1 x5"
sorry
  (*uniqueness*)
    show " for it1 be setHIDDENM2 holds  for it2 be setHIDDENM2 holds ( for x be objectHIDDENM1 holds x inHIDDENR3 it1 iff (((x =HIDDENR1 x1 or x =HIDDENR1 x2) or x =HIDDENR1 x3) or x =HIDDENR1 x4) or x =HIDDENR1 x5) & ( for x be objectHIDDENM1 holds x inHIDDENR3 it2 iff (((x =HIDDENR1 x1 or x =HIDDENR1 x2) or x =HIDDENR1 x3) or x =HIDDENR1 x4) or x =HIDDENR1 x5) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mdef enumset1_def_4 ("{ENUMSET1K4 _ , _ , _ , _ , _ , _ }" [0,0,0,0,0,0]356 ) where
  mlet "x1 be objectHIDDENM1", "x2 be objectHIDDENM1", "x3 be objectHIDDENM1", "x4 be objectHIDDENM1", "x5 be objectHIDDENM1", "x6 be objectHIDDENM1"
"func {ENUMSET1K4 x1,x2,x3,x4,x5,x6 } \<rightarrow> setHIDDENM2 means
  \<lambda>it.  for x be objectHIDDENM1 holds x inHIDDENR3 it iff ((((x =HIDDENR1 x1 or x =HIDDENR1 x2) or x =HIDDENR1 x3) or x =HIDDENR1 x4) or x =HIDDENR1 x5) or x =HIDDENR1 x6"
proof-
  (*existence*)
    show " ex it be setHIDDENM2 st  for x be objectHIDDENM1 holds x inHIDDENR3 it iff ((((x =HIDDENR1 x1 or x =HIDDENR1 x2) or x =HIDDENR1 x3) or x =HIDDENR1 x4) or x =HIDDENR1 x5) or x =HIDDENR1 x6"
sorry
  (*uniqueness*)
    show " for it1 be setHIDDENM2 holds  for it2 be setHIDDENM2 holds ( for x be objectHIDDENM1 holds x inHIDDENR3 it1 iff ((((x =HIDDENR1 x1 or x =HIDDENR1 x2) or x =HIDDENR1 x3) or x =HIDDENR1 x4) or x =HIDDENR1 x5) or x =HIDDENR1 x6) & ( for x be objectHIDDENM1 holds x inHIDDENR3 it2 iff ((((x =HIDDENR1 x1 or x =HIDDENR1 x2) or x =HIDDENR1 x3) or x =HIDDENR1 x4) or x =HIDDENR1 x5) or x =HIDDENR1 x6) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mdef enumset1_def_5 ("{ENUMSET1K5 _ , _ , _ , _ , _ , _ , _ }" [0,0,0,0,0,0,0]356 ) where
  mlet "x1 be objectHIDDENM1", "x2 be objectHIDDENM1", "x3 be objectHIDDENM1", "x4 be objectHIDDENM1", "x5 be objectHIDDENM1", "x6 be objectHIDDENM1", "x7 be objectHIDDENM1"
"func {ENUMSET1K5 x1,x2,x3,x4,x5,x6,x7 } \<rightarrow> setHIDDENM2 means
  \<lambda>it.  for x be objectHIDDENM1 holds x inHIDDENR3 it iff (((((x =HIDDENR1 x1 or x =HIDDENR1 x2) or x =HIDDENR1 x3) or x =HIDDENR1 x4) or x =HIDDENR1 x5) or x =HIDDENR1 x6) or x =HIDDENR1 x7"
proof-
  (*existence*)
    show " ex it be setHIDDENM2 st  for x be objectHIDDENM1 holds x inHIDDENR3 it iff (((((x =HIDDENR1 x1 or x =HIDDENR1 x2) or x =HIDDENR1 x3) or x =HIDDENR1 x4) or x =HIDDENR1 x5) or x =HIDDENR1 x6) or x =HIDDENR1 x7"
sorry
  (*uniqueness*)
    show " for it1 be setHIDDENM2 holds  for it2 be setHIDDENM2 holds ( for x be objectHIDDENM1 holds x inHIDDENR3 it1 iff (((((x =HIDDENR1 x1 or x =HIDDENR1 x2) or x =HIDDENR1 x3) or x =HIDDENR1 x4) or x =HIDDENR1 x5) or x =HIDDENR1 x6) or x =HIDDENR1 x7) & ( for x be objectHIDDENM1 holds x inHIDDENR3 it2 iff (((((x =HIDDENR1 x1 or x =HIDDENR1 x2) or x =HIDDENR1 x3) or x =HIDDENR1 x4) or x =HIDDENR1 x5) or x =HIDDENR1 x6) or x =HIDDENR1 x7) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mdef enumset1_def_6 ("{ENUMSET1K6 _ , _ , _ , _ , _ , _ , _ , _ }" [0,0,0,0,0,0,0,0]356 ) where
  mlet "x1 be objectHIDDENM1", "x2 be objectHIDDENM1", "x3 be objectHIDDENM1", "x4 be objectHIDDENM1", "x5 be objectHIDDENM1", "x6 be objectHIDDENM1", "x7 be objectHIDDENM1", "x8 be objectHIDDENM1"
"func {ENUMSET1K6 x1,x2,x3,x4,x5,x6,x7,x8 } \<rightarrow> setHIDDENM2 means
  \<lambda>it.  for x be objectHIDDENM1 holds x inHIDDENR3 it iff ((((((x =HIDDENR1 x1 or x =HIDDENR1 x2) or x =HIDDENR1 x3) or x =HIDDENR1 x4) or x =HIDDENR1 x5) or x =HIDDENR1 x6) or x =HIDDENR1 x7) or x =HIDDENR1 x8"
proof-
  (*existence*)
    show " ex it be setHIDDENM2 st  for x be objectHIDDENM1 holds x inHIDDENR3 it iff ((((((x =HIDDENR1 x1 or x =HIDDENR1 x2) or x =HIDDENR1 x3) or x =HIDDENR1 x4) or x =HIDDENR1 x5) or x =HIDDENR1 x6) or x =HIDDENR1 x7) or x =HIDDENR1 x8"
sorry
  (*uniqueness*)
    show " for it1 be setHIDDENM2 holds  for it2 be setHIDDENM2 holds ( for x be objectHIDDENM1 holds x inHIDDENR3 it1 iff ((((((x =HIDDENR1 x1 or x =HIDDENR1 x2) or x =HIDDENR1 x3) or x =HIDDENR1 x4) or x =HIDDENR1 x5) or x =HIDDENR1 x6) or x =HIDDENR1 x7) or x =HIDDENR1 x8) & ( for x be objectHIDDENM1 holds x inHIDDENR3 it2 iff ((((((x =HIDDENR1 x1 or x =HIDDENR1 x2) or x =HIDDENR1 x3) or x =HIDDENR1 x4) or x =HIDDENR1 x5) or x =HIDDENR1 x6) or x =HIDDENR1 x7) or x =HIDDENR1 x8) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mdef enumset1_def_7 ("{ENUMSET1K7 _ , _ , _ , _ , _ , _ , _ , _ , _ }" [0,0,0,0,0,0,0,0,0]356 ) where
  mlet "x1 be objectHIDDENM1", "x2 be objectHIDDENM1", "x3 be objectHIDDENM1", "x4 be objectHIDDENM1", "x5 be objectHIDDENM1", "x6 be objectHIDDENM1", "x7 be objectHIDDENM1", "x8 be objectHIDDENM1", "x9 be objectHIDDENM1"
"func {ENUMSET1K7 x1,x2,x3,x4,x5,x6,x7,x8,x9 } \<rightarrow> setHIDDENM2 means
  \<lambda>it.  for x be objectHIDDENM1 holds x inHIDDENR3 it iff (((((((x =HIDDENR1 x1 or x =HIDDENR1 x2) or x =HIDDENR1 x3) or x =HIDDENR1 x4) or x =HIDDENR1 x5) or x =HIDDENR1 x6) or x =HIDDENR1 x7) or x =HIDDENR1 x8) or x =HIDDENR1 x9"
proof-
  (*existence*)
    show " ex it be setHIDDENM2 st  for x be objectHIDDENM1 holds x inHIDDENR3 it iff (((((((x =HIDDENR1 x1 or x =HIDDENR1 x2) or x =HIDDENR1 x3) or x =HIDDENR1 x4) or x =HIDDENR1 x5) or x =HIDDENR1 x6) or x =HIDDENR1 x7) or x =HIDDENR1 x8) or x =HIDDENR1 x9"
sorry
  (*uniqueness*)
    show " for it1 be setHIDDENM2 holds  for it2 be setHIDDENM2 holds ( for x be objectHIDDENM1 holds x inHIDDENR3 it1 iff (((((((x =HIDDENR1 x1 or x =HIDDENR1 x2) or x =HIDDENR1 x3) or x =HIDDENR1 x4) or x =HIDDENR1 x5) or x =HIDDENR1 x6) or x =HIDDENR1 x7) or x =HIDDENR1 x8) or x =HIDDENR1 x9) & ( for x be objectHIDDENM1 holds x inHIDDENR3 it2 iff (((((((x =HIDDENR1 x1 or x =HIDDENR1 x2) or x =HIDDENR1 x3) or x =HIDDENR1 x4) or x =HIDDENR1 x5) or x =HIDDENR1 x6) or x =HIDDENR1 x7) or x =HIDDENR1 x8) or x =HIDDENR1 x9) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mdef enumset1_def_8 ("{ENUMSET1K8 _ , _ , _ , _ , _ , _ , _ , _ , _ , _ }" [0,0,0,0,0,0,0,0,0,0]356 ) where
  mlet "x1 be objectHIDDENM1", "x2 be objectHIDDENM1", "x3 be objectHIDDENM1", "x4 be objectHIDDENM1", "x5 be objectHIDDENM1", "x6 be objectHIDDENM1", "x7 be objectHIDDENM1", "x8 be objectHIDDENM1", "x9 be objectHIDDENM1", "x10 be objectHIDDENM1"
"func {ENUMSET1K8 x1,x2,x3,x4,x5,x6,x7,x8,x9,x10 } \<rightarrow> setHIDDENM2 means
  \<lambda>it.  for x be objectHIDDENM1 holds x inHIDDENR3 it iff ((((((((x =HIDDENR1 x1 or x =HIDDENR1 x2) or x =HIDDENR1 x3) or x =HIDDENR1 x4) or x =HIDDENR1 x5) or x =HIDDENR1 x6) or x =HIDDENR1 x7) or x =HIDDENR1 x8) or x =HIDDENR1 x9) or x =HIDDENR1 x10"
proof-
  (*existence*)
    show " ex it be setHIDDENM2 st  for x be objectHIDDENM1 holds x inHIDDENR3 it iff ((((((((x =HIDDENR1 x1 or x =HIDDENR1 x2) or x =HIDDENR1 x3) or x =HIDDENR1 x4) or x =HIDDENR1 x5) or x =HIDDENR1 x6) or x =HIDDENR1 x7) or x =HIDDENR1 x8) or x =HIDDENR1 x9) or x =HIDDENR1 x10"
sorry
  (*uniqueness*)
    show " for it1 be setHIDDENM2 holds  for it2 be setHIDDENM2 holds ( for x be objectHIDDENM1 holds x inHIDDENR3 it1 iff ((((((((x =HIDDENR1 x1 or x =HIDDENR1 x2) or x =HIDDENR1 x3) or x =HIDDENR1 x4) or x =HIDDENR1 x5) or x =HIDDENR1 x6) or x =HIDDENR1 x7) or x =HIDDENR1 x8) or x =HIDDENR1 x9) or x =HIDDENR1 x10) & ( for x be objectHIDDENM1 holds x inHIDDENR3 it2 iff ((((((((x =HIDDENR1 x1 or x =HIDDENR1 x2) or x =HIDDENR1 x3) or x =HIDDENR1 x4) or x =HIDDENR1 x5) or x =HIDDENR1 x6) or x =HIDDENR1 x7) or x =HIDDENR1 x8) or x =HIDDENR1 x9) or x =HIDDENR1 x10) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mtheorem enumset1_th_1:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds {TARSKIK2 x1,x2 } =XBOOLE-0R4 {TARSKIK1 x1} \\/XBOOLE-0K2 {TARSKIK1 x2}"
sorry

mtheorem enumset1_th_2:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds {ENUMSET1K1 x1,x2,x3 } =XBOOLE-0R4 {TARSKIK1 x1} \\/XBOOLE-0K2 {TARSKIK2 x2,x3 }"
sorry

mtheorem enumset1_th_3:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds {ENUMSET1K1 x1,x2,x3 } =XBOOLE-0R4 {TARSKIK2 x1,x2 } \\/XBOOLE-0K2 {TARSKIK1 x3}"
sorry

mlemma enumset1_lm_2:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for x4 be objectHIDDENM1 holds {ENUMSET1K2 x1,x2,x3,x4 } =XBOOLE-0R4 {TARSKIK2 x1,x2 } \\/XBOOLE-0K2 {TARSKIK2 x3,x4 }"
sorry

mtheorem enumset1_th_4:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for x4 be objectHIDDENM1 holds {ENUMSET1K2 x1,x2,x3,x4 } =XBOOLE-0R4 {TARSKIK1 x1} \\/XBOOLE-0K2 {ENUMSET1K1 x2,x3,x4 }"
sorry

mtheorem enumset1_th_5:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for x4 be objectHIDDENM1 holds {ENUMSET1K2 x1,x2,x3,x4 } =XBOOLE-0R4 {TARSKIK2 x1,x2 } \\/XBOOLE-0K2 {TARSKIK2 x3,x4 }"
  using enumset1_lm_2 sorry

mtheorem enumset1_th_6:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for x4 be objectHIDDENM1 holds {ENUMSET1K2 x1,x2,x3,x4 } =XBOOLE-0R4 {ENUMSET1K1 x1,x2,x3 } \\/XBOOLE-0K2 {TARSKIK1 x4}"
sorry

mlemma enumset1_lm_3:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for x4 be objectHIDDENM1 holds  for x5 be objectHIDDENM1 holds {ENUMSET1K3 x1,x2,x3,x4,x5 } =XBOOLE-0R4 {ENUMSET1K1 x1,x2,x3 } \\/XBOOLE-0K2 {TARSKIK2 x4,x5 }"
sorry

mtheorem enumset1_th_7:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for x4 be objectHIDDENM1 holds  for x5 be objectHIDDENM1 holds {ENUMSET1K3 x1,x2,x3,x4,x5 } =XBOOLE-0R4 {TARSKIK1 x1} \\/XBOOLE-0K2 {ENUMSET1K2 x2,x3,x4,x5 }"
sorry

mtheorem enumset1_th_8:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for x4 be objectHIDDENM1 holds  for x5 be objectHIDDENM1 holds {ENUMSET1K3 x1,x2,x3,x4,x5 } =XBOOLE-0R4 {TARSKIK2 x1,x2 } \\/XBOOLE-0K2 {ENUMSET1K1 x3,x4,x5 }"
sorry

mtheorem enumset1_th_9:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for x4 be objectHIDDENM1 holds  for x5 be objectHIDDENM1 holds {ENUMSET1K3 x1,x2,x3,x4,x5 } =XBOOLE-0R4 {ENUMSET1K1 x1,x2,x3 } \\/XBOOLE-0K2 {TARSKIK2 x4,x5 }"
  using enumset1_lm_3 sorry

mtheorem enumset1_th_10:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for x4 be objectHIDDENM1 holds  for x5 be objectHIDDENM1 holds {ENUMSET1K3 x1,x2,x3,x4,x5 } =XBOOLE-0R4 {ENUMSET1K2 x1,x2,x3,x4 } \\/XBOOLE-0K2 {TARSKIK1 x5}"
sorry

mlemma enumset1_lm_4:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for x4 be objectHIDDENM1 holds  for x5 be objectHIDDENM1 holds  for x6 be objectHIDDENM1 holds {ENUMSET1K4 x1,x2,x3,x4,x5,x6 } =XBOOLE-0R4 {ENUMSET1K1 x1,x2,x3 } \\/XBOOLE-0K2 {ENUMSET1K1 x4,x5,x6 }"
sorry

mtheorem enumset1_th_11:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for x4 be objectHIDDENM1 holds  for x5 be objectHIDDENM1 holds  for x6 be objectHIDDENM1 holds {ENUMSET1K4 x1,x2,x3,x4,x5,x6 } =XBOOLE-0R4 {TARSKIK1 x1} \\/XBOOLE-0K2 {ENUMSET1K3 x2,x3,x4,x5,x6 }"
sorry

mtheorem enumset1_th_12:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for x4 be objectHIDDENM1 holds  for x5 be objectHIDDENM1 holds  for x6 be objectHIDDENM1 holds {ENUMSET1K4 x1,x2,x3,x4,x5,x6 } =XBOOLE-0R4 {TARSKIK2 x1,x2 } \\/XBOOLE-0K2 {ENUMSET1K2 x3,x4,x5,x6 }"
sorry

mtheorem enumset1_th_13:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for x4 be objectHIDDENM1 holds  for x5 be objectHIDDENM1 holds  for x6 be objectHIDDENM1 holds {ENUMSET1K4 x1,x2,x3,x4,x5,x6 } =XBOOLE-0R4 {ENUMSET1K1 x1,x2,x3 } \\/XBOOLE-0K2 {ENUMSET1K1 x4,x5,x6 }"
  using enumset1_lm_4 sorry

mtheorem enumset1_th_14:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for x4 be objectHIDDENM1 holds  for x5 be objectHIDDENM1 holds  for x6 be objectHIDDENM1 holds {ENUMSET1K4 x1,x2,x3,x4,x5,x6 } =XBOOLE-0R4 {ENUMSET1K2 x1,x2,x3,x4 } \\/XBOOLE-0K2 {TARSKIK2 x5,x6 }"
sorry

mtheorem enumset1_th_15:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for x4 be objectHIDDENM1 holds  for x5 be objectHIDDENM1 holds  for x6 be objectHIDDENM1 holds {ENUMSET1K4 x1,x2,x3,x4,x5,x6 } =XBOOLE-0R4 {ENUMSET1K3 x1,x2,x3,x4,x5 } \\/XBOOLE-0K2 {TARSKIK1 x6}"
sorry

mlemma enumset1_lm_5:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for x4 be objectHIDDENM1 holds  for x5 be objectHIDDENM1 holds  for x6 be objectHIDDENM1 holds  for x7 be objectHIDDENM1 holds {ENUMSET1K5 x1,x2,x3,x4,x5,x6,x7 } =XBOOLE-0R4 {ENUMSET1K2 x1,x2,x3,x4 } \\/XBOOLE-0K2 {ENUMSET1K1 x5,x6,x7 }"
sorry

mtheorem enumset1_th_16:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for x4 be objectHIDDENM1 holds  for x5 be objectHIDDENM1 holds  for x6 be objectHIDDENM1 holds  for x7 be objectHIDDENM1 holds {ENUMSET1K5 x1,x2,x3,x4,x5,x6,x7 } =XBOOLE-0R4 {TARSKIK1 x1} \\/XBOOLE-0K2 {ENUMSET1K4 x2,x3,x4,x5,x6,x7 }"
sorry

mtheorem enumset1_th_17:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for x4 be objectHIDDENM1 holds  for x5 be objectHIDDENM1 holds  for x6 be objectHIDDENM1 holds  for x7 be objectHIDDENM1 holds {ENUMSET1K5 x1,x2,x3,x4,x5,x6,x7 } =XBOOLE-0R4 {TARSKIK2 x1,x2 } \\/XBOOLE-0K2 {ENUMSET1K3 x3,x4,x5,x6,x7 }"
sorry

mtheorem enumset1_th_18:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for x4 be objectHIDDENM1 holds  for x5 be objectHIDDENM1 holds  for x6 be objectHIDDENM1 holds  for x7 be objectHIDDENM1 holds {ENUMSET1K5 x1,x2,x3,x4,x5,x6,x7 } =XBOOLE-0R4 {ENUMSET1K1 x1,x2,x3 } \\/XBOOLE-0K2 {ENUMSET1K2 x4,x5,x6,x7 }"
sorry

mtheorem enumset1_th_19:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for x4 be objectHIDDENM1 holds  for x5 be objectHIDDENM1 holds  for x6 be objectHIDDENM1 holds  for x7 be objectHIDDENM1 holds {ENUMSET1K5 x1,x2,x3,x4,x5,x6,x7 } =XBOOLE-0R4 {ENUMSET1K2 x1,x2,x3,x4 } \\/XBOOLE-0K2 {ENUMSET1K1 x5,x6,x7 }"
  using enumset1_lm_5 sorry

mtheorem enumset1_th_20:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for x4 be objectHIDDENM1 holds  for x5 be objectHIDDENM1 holds  for x6 be objectHIDDENM1 holds  for x7 be objectHIDDENM1 holds {ENUMSET1K5 x1,x2,x3,x4,x5,x6,x7 } =XBOOLE-0R4 {ENUMSET1K3 x1,x2,x3,x4,x5 } \\/XBOOLE-0K2 {TARSKIK2 x6,x7 }"
sorry

mtheorem enumset1_th_21:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for x4 be objectHIDDENM1 holds  for x5 be objectHIDDENM1 holds  for x6 be objectHIDDENM1 holds  for x7 be objectHIDDENM1 holds {ENUMSET1K5 x1,x2,x3,x4,x5,x6,x7 } =XBOOLE-0R4 {ENUMSET1K4 x1,x2,x3,x4,x5,x6 } \\/XBOOLE-0K2 {TARSKIK1 x7}"
sorry

mlemma enumset1_lm_6:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for x4 be objectHIDDENM1 holds  for x5 be objectHIDDENM1 holds  for x6 be objectHIDDENM1 holds  for x7 be objectHIDDENM1 holds  for x8 be objectHIDDENM1 holds {ENUMSET1K6 x1,x2,x3,x4,x5,x6,x7,x8 } =XBOOLE-0R4 {ENUMSET1K2 x1,x2,x3,x4 } \\/XBOOLE-0K2 {ENUMSET1K2 x5,x6,x7,x8 }"
sorry

mtheorem enumset1_th_22:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for x4 be objectHIDDENM1 holds  for x5 be objectHIDDENM1 holds  for x6 be objectHIDDENM1 holds  for x7 be objectHIDDENM1 holds  for x8 be objectHIDDENM1 holds {ENUMSET1K6 x1,x2,x3,x4,x5,x6,x7,x8 } =XBOOLE-0R4 {TARSKIK1 x1} \\/XBOOLE-0K2 {ENUMSET1K5 x2,x3,x4,x5,x6,x7,x8 }"
sorry

mtheorem enumset1_th_23:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for x4 be objectHIDDENM1 holds  for x5 be objectHIDDENM1 holds  for x6 be objectHIDDENM1 holds  for x7 be objectHIDDENM1 holds  for x8 be objectHIDDENM1 holds {ENUMSET1K6 x1,x2,x3,x4,x5,x6,x7,x8 } =XBOOLE-0R4 {TARSKIK2 x1,x2 } \\/XBOOLE-0K2 {ENUMSET1K4 x3,x4,x5,x6,x7,x8 }"
sorry

mtheorem enumset1_th_24:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for x4 be objectHIDDENM1 holds  for x5 be objectHIDDENM1 holds  for x6 be objectHIDDENM1 holds  for x7 be objectHIDDENM1 holds  for x8 be objectHIDDENM1 holds {ENUMSET1K6 x1,x2,x3,x4,x5,x6,x7,x8 } =XBOOLE-0R4 {ENUMSET1K1 x1,x2,x3 } \\/XBOOLE-0K2 {ENUMSET1K3 x4,x5,x6,x7,x8 }"
sorry

mtheorem enumset1_th_25:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for x4 be objectHIDDENM1 holds  for x5 be objectHIDDENM1 holds  for x6 be objectHIDDENM1 holds  for x7 be objectHIDDENM1 holds  for x8 be objectHIDDENM1 holds {ENUMSET1K6 x1,x2,x3,x4,x5,x6,x7,x8 } =XBOOLE-0R4 {ENUMSET1K2 x1,x2,x3,x4 } \\/XBOOLE-0K2 {ENUMSET1K2 x5,x6,x7,x8 }"
  using enumset1_lm_6 sorry

mtheorem enumset1_th_26:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for x4 be objectHIDDENM1 holds  for x5 be objectHIDDENM1 holds  for x6 be objectHIDDENM1 holds  for x7 be objectHIDDENM1 holds  for x8 be objectHIDDENM1 holds {ENUMSET1K6 x1,x2,x3,x4,x5,x6,x7,x8 } =XBOOLE-0R4 {ENUMSET1K3 x1,x2,x3,x4,x5 } \\/XBOOLE-0K2 {ENUMSET1K1 x6,x7,x8 }"
sorry

mtheorem enumset1_th_27:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for x4 be objectHIDDENM1 holds  for x5 be objectHIDDENM1 holds  for x6 be objectHIDDENM1 holds  for x7 be objectHIDDENM1 holds  for x8 be objectHIDDENM1 holds {ENUMSET1K6 x1,x2,x3,x4,x5,x6,x7,x8 } =XBOOLE-0R4 {ENUMSET1K4 x1,x2,x3,x4,x5,x6 } \\/XBOOLE-0K2 {TARSKIK2 x7,x8 }"
sorry

mtheorem enumset1_th_28:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for x4 be objectHIDDENM1 holds  for x5 be objectHIDDENM1 holds  for x6 be objectHIDDENM1 holds  for x7 be objectHIDDENM1 holds  for x8 be objectHIDDENM1 holds {ENUMSET1K6 x1,x2,x3,x4,x5,x6,x7,x8 } =XBOOLE-0R4 {ENUMSET1K5 x1,x2,x3,x4,x5,x6,x7 } \\/XBOOLE-0K2 {TARSKIK1 x8}"
sorry

mtheorem enumset1_th_29:
" for x1 be objectHIDDENM1 holds {TARSKIK2 x1,x1 } =XBOOLE-0R4 {TARSKIK1 x1}"
sorry

mtheorem enumset1_th_30:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds {ENUMSET1K1 x1,x1,x2 } =XBOOLE-0R4 {TARSKIK2 x1,x2 }"
sorry

mtheorem enumset1_th_31:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds {ENUMSET1K2 x1,x1,x2,x3 } =XBOOLE-0R4 {ENUMSET1K1 x1,x2,x3 }"
sorry

mtheorem enumset1_th_32:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for x4 be objectHIDDENM1 holds {ENUMSET1K3 x1,x1,x2,x3,x4 } =XBOOLE-0R4 {ENUMSET1K2 x1,x2,x3,x4 }"
sorry

mtheorem enumset1_th_33:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for x4 be objectHIDDENM1 holds  for x5 be objectHIDDENM1 holds {ENUMSET1K4 x1,x1,x2,x3,x4,x5 } =XBOOLE-0R4 {ENUMSET1K3 x1,x2,x3,x4,x5 }"
sorry

mtheorem enumset1_th_34:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for x4 be objectHIDDENM1 holds  for x5 be objectHIDDENM1 holds  for x6 be objectHIDDENM1 holds {ENUMSET1K5 x1,x1,x2,x3,x4,x5,x6 } =XBOOLE-0R4 {ENUMSET1K4 x1,x2,x3,x4,x5,x6 }"
sorry

mtheorem enumset1_th_35:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for x4 be objectHIDDENM1 holds  for x5 be objectHIDDENM1 holds  for x6 be objectHIDDENM1 holds  for x7 be objectHIDDENM1 holds {ENUMSET1K6 x1,x1,x2,x3,x4,x5,x6,x7 } =XBOOLE-0R4 {ENUMSET1K5 x1,x2,x3,x4,x5,x6,x7 }"
sorry

mtheorem enumset1_th_36:
" for x1 be objectHIDDENM1 holds {ENUMSET1K1 x1,x1,x1 } =XBOOLE-0R4 {TARSKIK1 x1}"
sorry

mtheorem enumset1_th_37:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds {ENUMSET1K2 x1,x1,x1,x2 } =XBOOLE-0R4 {TARSKIK2 x1,x2 }"
sorry

mtheorem enumset1_th_38:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds {ENUMSET1K3 x1,x1,x1,x2,x3 } =XBOOLE-0R4 {ENUMSET1K1 x1,x2,x3 }"
sorry

mtheorem enumset1_th_39:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for x4 be objectHIDDENM1 holds {ENUMSET1K4 x1,x1,x1,x2,x3,x4 } =XBOOLE-0R4 {ENUMSET1K2 x1,x2,x3,x4 }"
sorry

mtheorem enumset1_th_40:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for x4 be objectHIDDENM1 holds  for x5 be objectHIDDENM1 holds {ENUMSET1K5 x1,x1,x1,x2,x3,x4,x5 } =XBOOLE-0R4 {ENUMSET1K3 x1,x2,x3,x4,x5 }"
sorry

mtheorem enumset1_th_41:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for x4 be objectHIDDENM1 holds  for x5 be objectHIDDENM1 holds  for x6 be objectHIDDENM1 holds {ENUMSET1K6 x1,x1,x1,x2,x3,x4,x5,x6 } =XBOOLE-0R4 {ENUMSET1K4 x1,x2,x3,x4,x5,x6 }"
sorry

mtheorem enumset1_th_42:
" for x1 be objectHIDDENM1 holds {ENUMSET1K2 x1,x1,x1,x1 } =XBOOLE-0R4 {TARSKIK1 x1}"
sorry

mtheorem enumset1_th_43:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds {ENUMSET1K3 x1,x1,x1,x1,x2 } =XBOOLE-0R4 {TARSKIK2 x1,x2 }"
sorry

mtheorem enumset1_th_44:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds {ENUMSET1K4 x1,x1,x1,x1,x2,x3 } =XBOOLE-0R4 {ENUMSET1K1 x1,x2,x3 }"
sorry

mtheorem enumset1_th_45:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for x4 be objectHIDDENM1 holds {ENUMSET1K5 x1,x1,x1,x1,x2,x3,x4 } =XBOOLE-0R4 {ENUMSET1K2 x1,x2,x3,x4 }"
sorry

mtheorem enumset1_th_46:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for x4 be objectHIDDENM1 holds  for x5 be objectHIDDENM1 holds {ENUMSET1K6 x1,x1,x1,x1,x2,x3,x4,x5 } =XBOOLE-0R4 {ENUMSET1K3 x1,x2,x3,x4,x5 }"
sorry

mtheorem enumset1_th_47:
" for x1 be objectHIDDENM1 holds {ENUMSET1K3 x1,x1,x1,x1,x1 } =XBOOLE-0R4 {TARSKIK1 x1}"
sorry

mtheorem enumset1_th_48:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds {ENUMSET1K4 x1,x1,x1,x1,x1,x2 } =XBOOLE-0R4 {TARSKIK2 x1,x2 }"
sorry

mtheorem enumset1_th_49:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds {ENUMSET1K5 x1,x1,x1,x1,x1,x2,x3 } =XBOOLE-0R4 {ENUMSET1K1 x1,x2,x3 }"
sorry

mtheorem enumset1_th_50:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for x4 be objectHIDDENM1 holds {ENUMSET1K6 x1,x1,x1,x1,x1,x2,x3,x4 } =XBOOLE-0R4 {ENUMSET1K2 x1,x2,x3,x4 }"
sorry

mtheorem enumset1_th_51:
" for x1 be objectHIDDENM1 holds {ENUMSET1K4 x1,x1,x1,x1,x1,x1 } =XBOOLE-0R4 {TARSKIK1 x1}"
sorry

mtheorem enumset1_th_52:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds {ENUMSET1K5 x1,x1,x1,x1,x1,x1,x2 } =XBOOLE-0R4 {TARSKIK2 x1,x2 }"
sorry

mtheorem enumset1_th_53:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds {ENUMSET1K6 x1,x1,x1,x1,x1,x1,x2,x3 } =XBOOLE-0R4 {ENUMSET1K1 x1,x2,x3 }"
sorry

mtheorem enumset1_th_54:
" for x1 be objectHIDDENM1 holds {ENUMSET1K5 x1,x1,x1,x1,x1,x1,x1 } =XBOOLE-0R4 {TARSKIK1 x1}"
sorry

mtheorem enumset1_th_55:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds {ENUMSET1K6 x1,x1,x1,x1,x1,x1,x1,x2 } =XBOOLE-0R4 {TARSKIK2 x1,x2 }"
sorry

mtheorem enumset1_th_56:
" for x1 be objectHIDDENM1 holds {ENUMSET1K6 x1,x1,x1,x1,x1,x1,x1,x1 } =XBOOLE-0R4 {TARSKIK1 x1}"
sorry

mtheorem enumset1_th_57:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds {ENUMSET1K1 x1,x2,x3 } =XBOOLE-0R4 {ENUMSET1K1 x1,x3,x2 }"
sorry

mtheorem enumset1_th_58:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds {ENUMSET1K1 x1,x2,x3 } =XBOOLE-0R4 {ENUMSET1K1 x2,x1,x3 }"
sorry

mtheorem enumset1_th_59:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds {ENUMSET1K1 x1,x2,x3 } =XBOOLE-0R4 {ENUMSET1K1 x2,x3,x1 }"
sorry

mtheorem enumset1_th_60:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds {ENUMSET1K1 x1,x2,x3 } =XBOOLE-0R4 {ENUMSET1K1 x3,x2,x1 }"
sorry

mtheorem enumset1_th_61:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for x4 be objectHIDDENM1 holds {ENUMSET1K2 x1,x2,x3,x4 } =XBOOLE-0R4 {ENUMSET1K2 x1,x2,x4,x3 }"
sorry

mtheorem enumset1_th_62:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for x4 be objectHIDDENM1 holds {ENUMSET1K2 x1,x2,x3,x4 } =XBOOLE-0R4 {ENUMSET1K2 x1,x3,x2,x4 }"
sorry

mtheorem enumset1_th_63:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for x4 be objectHIDDENM1 holds {ENUMSET1K2 x1,x2,x3,x4 } =XBOOLE-0R4 {ENUMSET1K2 x1,x3,x4,x2 }"
sorry

mtheorem enumset1_th_64:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for x4 be objectHIDDENM1 holds {ENUMSET1K2 x1,x2,x3,x4 } =XBOOLE-0R4 {ENUMSET1K2 x1,x4,x3,x2 }"
sorry

mtheorem enumset1_th_65:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for x4 be objectHIDDENM1 holds {ENUMSET1K2 x1,x2,x3,x4 } =XBOOLE-0R4 {ENUMSET1K2 x2,x1,x3,x4 }"
sorry

mlemma enumset1_lm_7:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for x4 be objectHIDDENM1 holds {ENUMSET1K2 x1,x2,x3,x4 } =XBOOLE-0R4 {ENUMSET1K2 x2,x3,x1,x4 }"
sorry

mtheorem enumset1_th_66:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for x4 be objectHIDDENM1 holds {ENUMSET1K2 x1,x2,x3,x4 } =XBOOLE-0R4 {ENUMSET1K2 x2,x1,x4,x3 }"
sorry

mtheorem enumset1_th_67:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for x4 be objectHIDDENM1 holds {ENUMSET1K2 x1,x2,x3,x4 } =XBOOLE-0R4 {ENUMSET1K2 x2,x3,x1,x4 }"
  using enumset1_lm_7 sorry

mtheorem enumset1_th_68:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for x4 be objectHIDDENM1 holds {ENUMSET1K2 x1,x2,x3,x4 } =XBOOLE-0R4 {ENUMSET1K2 x2,x3,x4,x1 }"
sorry

mtheorem enumset1_th_69:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for x4 be objectHIDDENM1 holds {ENUMSET1K2 x1,x2,x3,x4 } =XBOOLE-0R4 {ENUMSET1K2 x2,x4,x1,x3 }"
sorry

mtheorem enumset1_th_70:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for x4 be objectHIDDENM1 holds {ENUMSET1K2 x1,x2,x3,x4 } =XBOOLE-0R4 {ENUMSET1K2 x2,x4,x3,x1 }"
sorry

mlemma enumset1_lm_8:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for x4 be objectHIDDENM1 holds {ENUMSET1K2 x1,x2,x3,x4 } =XBOOLE-0R4 {ENUMSET1K2 x3,x2,x1,x4 }"
sorry

mtheorem enumset1_th_71:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for x4 be objectHIDDENM1 holds {ENUMSET1K2 x1,x2,x3,x4 } =XBOOLE-0R4 {ENUMSET1K2 x3,x2,x1,x4 }"
  using enumset1_lm_8 sorry

mtheorem enumset1_th_72:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for x4 be objectHIDDENM1 holds {ENUMSET1K2 x1,x2,x3,x4 } =XBOOLE-0R4 {ENUMSET1K2 x3,x2,x4,x1 }"
sorry

mtheorem enumset1_th_73:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for x4 be objectHIDDENM1 holds {ENUMSET1K2 x1,x2,x3,x4 } =XBOOLE-0R4 {ENUMSET1K2 x3,x4,x1,x2 }"
sorry

mtheorem enumset1_th_74:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for x4 be objectHIDDENM1 holds {ENUMSET1K2 x1,x2,x3,x4 } =XBOOLE-0R4 {ENUMSET1K2 x3,x4,x2,x1 }"
sorry

mtheorem enumset1_th_75:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for x4 be objectHIDDENM1 holds {ENUMSET1K2 x1,x2,x3,x4 } =XBOOLE-0R4 {ENUMSET1K2 x4,x2,x3,x1 }"
sorry

mtheorem enumset1_th_76:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for x4 be objectHIDDENM1 holds {ENUMSET1K2 x1,x2,x3,x4 } =XBOOLE-0R4 {ENUMSET1K2 x4,x3,x2,x1 }"
sorry

mlemma enumset1_lm_9:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for x4 be objectHIDDENM1 holds  for x5 be objectHIDDENM1 holds  for x6 be objectHIDDENM1 holds  for x7 be objectHIDDENM1 holds  for x8 be objectHIDDENM1 holds  for x9 be objectHIDDENM1 holds {ENUMSET1K7 x1,x2,x3,x4,x5,x6,x7,x8,x9 } =XBOOLE-0R4 {ENUMSET1K2 x1,x2,x3,x4 } \\/XBOOLE-0K2 {ENUMSET1K3 x5,x6,x7,x8,x9 }"
sorry

mtheorem enumset1_th_77:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for x4 be objectHIDDENM1 holds  for x5 be objectHIDDENM1 holds  for x6 be objectHIDDENM1 holds  for x7 be objectHIDDENM1 holds  for x8 be objectHIDDENM1 holds  for x9 be objectHIDDENM1 holds {ENUMSET1K7 x1,x2,x3,x4,x5,x6,x7,x8,x9 } =XBOOLE-0R4 {TARSKIK1 x1} \\/XBOOLE-0K2 {ENUMSET1K6 x2,x3,x4,x5,x6,x7,x8,x9 }"
sorry

mtheorem enumset1_th_78:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for x4 be objectHIDDENM1 holds  for x5 be objectHIDDENM1 holds  for x6 be objectHIDDENM1 holds  for x7 be objectHIDDENM1 holds  for x8 be objectHIDDENM1 holds  for x9 be objectHIDDENM1 holds {ENUMSET1K7 x1,x2,x3,x4,x5,x6,x7,x8,x9 } =XBOOLE-0R4 {TARSKIK2 x1,x2 } \\/XBOOLE-0K2 {ENUMSET1K5 x3,x4,x5,x6,x7,x8,x9 }"
sorry

mtheorem enumset1_th_79:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for x4 be objectHIDDENM1 holds  for x5 be objectHIDDENM1 holds  for x6 be objectHIDDENM1 holds  for x7 be objectHIDDENM1 holds  for x8 be objectHIDDENM1 holds  for x9 be objectHIDDENM1 holds {ENUMSET1K7 x1,x2,x3,x4,x5,x6,x7,x8,x9 } =XBOOLE-0R4 {ENUMSET1K1 x1,x2,x3 } \\/XBOOLE-0K2 {ENUMSET1K4 x4,x5,x6,x7,x8,x9 }"
sorry

mtheorem enumset1_th_80:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for x4 be objectHIDDENM1 holds  for x5 be objectHIDDENM1 holds  for x6 be objectHIDDENM1 holds  for x7 be objectHIDDENM1 holds  for x8 be objectHIDDENM1 holds  for x9 be objectHIDDENM1 holds {ENUMSET1K7 x1,x2,x3,x4,x5,x6,x7,x8,x9 } =XBOOLE-0R4 {ENUMSET1K2 x1,x2,x3,x4 } \\/XBOOLE-0K2 {ENUMSET1K3 x5,x6,x7,x8,x9 }"
  using enumset1_lm_9 sorry

mtheorem enumset1_th_81:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for x4 be objectHIDDENM1 holds  for x5 be objectHIDDENM1 holds  for x6 be objectHIDDENM1 holds  for x7 be objectHIDDENM1 holds  for x8 be objectHIDDENM1 holds  for x9 be objectHIDDENM1 holds {ENUMSET1K7 x1,x2,x3,x4,x5,x6,x7,x8,x9 } =XBOOLE-0R4 {ENUMSET1K3 x1,x2,x3,x4,x5 } \\/XBOOLE-0K2 {ENUMSET1K2 x6,x7,x8,x9 }"
sorry

mtheorem enumset1_th_82:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for x4 be objectHIDDENM1 holds  for x5 be objectHIDDENM1 holds  for x6 be objectHIDDENM1 holds  for x7 be objectHIDDENM1 holds  for x8 be objectHIDDENM1 holds  for x9 be objectHIDDENM1 holds {ENUMSET1K7 x1,x2,x3,x4,x5,x6,x7,x8,x9 } =XBOOLE-0R4 {ENUMSET1K4 x1,x2,x3,x4,x5,x6 } \\/XBOOLE-0K2 {ENUMSET1K1 x7,x8,x9 }"
sorry

mtheorem enumset1_th_83:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for x4 be objectHIDDENM1 holds  for x5 be objectHIDDENM1 holds  for x6 be objectHIDDENM1 holds  for x7 be objectHIDDENM1 holds  for x8 be objectHIDDENM1 holds  for x9 be objectHIDDENM1 holds {ENUMSET1K7 x1,x2,x3,x4,x5,x6,x7,x8,x9 } =XBOOLE-0R4 {ENUMSET1K5 x1,x2,x3,x4,x5,x6,x7 } \\/XBOOLE-0K2 {TARSKIK2 x8,x9 }"
sorry

mtheorem enumset1_th_84:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for x4 be objectHIDDENM1 holds  for x5 be objectHIDDENM1 holds  for x6 be objectHIDDENM1 holds  for x7 be objectHIDDENM1 holds  for x8 be objectHIDDENM1 holds  for x9 be objectHIDDENM1 holds {ENUMSET1K7 x1,x2,x3,x4,x5,x6,x7,x8,x9 } =XBOOLE-0R4 {ENUMSET1K6 x1,x2,x3,x4,x5,x6,x7,x8 } \\/XBOOLE-0K2 {TARSKIK1 x9}"
sorry

mtheorem enumset1_th_85:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for x4 be objectHIDDENM1 holds  for x5 be objectHIDDENM1 holds  for x6 be objectHIDDENM1 holds  for x7 be objectHIDDENM1 holds  for x8 be objectHIDDENM1 holds  for x9 be objectHIDDENM1 holds  for x10 be objectHIDDENM1 holds {ENUMSET1K8 x1,x2,x3,x4,x5,x6,x7,x8,x9,x10 } =XBOOLE-0R4 {ENUMSET1K7 x1,x2,x3,x4,x5,x6,x7,x8,x9 } \\/XBOOLE-0K2 {TARSKIK1 x10}"
sorry

(*begin*)
mtheorem enumset1_th_86:
" for x be setHIDDENM2 holds  for y be setHIDDENM2 holds  for z be setHIDDENM2 holds x <>HIDDENR2 y & x <>HIDDENR2 z implies {ENUMSET1K1 x,y,z } \\XBOOLE-0K4 {TARSKIK1 x} =XBOOLE-0R4 {TARSKIK2 y,z }"
sorry

mtheorem enumset1_th_87:
" for x1 be setHIDDENM2 holds  for x2 be setHIDDENM2 holds  for x3 be setHIDDENM2 holds {TARSKIK2 x2,x1 } \\/XBOOLE-0K2 {TARSKIK2 x3,x1 } =XBOOLE-0R4 {ENUMSET1K1 x1,x2,x3 }"
sorry

end
