theory ordinal1
  imports funct_1 xregular
begin
(*begin*)
reserve X, Y, Z, X1, X2, X3, X4, X5, X6 for "setHIDDENM2"
reserve x, y for "objectHIDDENM1"
(*\$CT 4*)
mtheorem ordinal1_th_5:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds Y inTARSKIR2 X implies  not X c=TARSKIR1 Y"
sorry

mdef ordinal1_def_1 ("succORDINAL1K1  _ " [228]228 ) where
  mlet "X be setHIDDENM2"
"func succORDINAL1K1 X \<rightarrow> setHIDDENM2 equals
  X \\/XBOOLE-0K2 {TARSKIK1 X}"
proof-
  (*coherence*)
    show "X \\/XBOOLE-0K2 {TARSKIK1 X} be setHIDDENM2"
       sorry
qed "sorry"

mtheorem ordinal1_cl_1:
  mlet "X be setHIDDENM2"
"cluster succORDINAL1K1 X as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "succORDINAL1K1 X be  non emptyXBOOLE-0V1"
     sorry
qed "sorry"

mtheorem ordinal1_th_6:
" for X be setHIDDENM2 holds X inTARSKIR2 succORDINAL1K1 X"
sorry

mtheorem ordinal1_th_7:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds succORDINAL1K1 X =XBOOLE-0R4 succORDINAL1K1 Y implies X =XBOOLE-0R4 Y"
sorry

mtheorem ordinal1_th_8:
" for X be setHIDDENM2 holds  for x be objectHIDDENM1 holds x inHIDDENR3 succORDINAL1K1 X iff x inHIDDENR3 X or x =HIDDENR1 X"
sorry

mtheorem ordinal1_th_9:
" for X be setHIDDENM2 holds X <>HIDDENR2 succORDINAL1K1 X"
sorry

reserve a, b, c for "objectHIDDENM1"
reserve X, Y, Z, x, y, z for "setHIDDENM2"
mdef ordinal1_def_2 ("epsilon-transitiveORDINAL1V1" 70 ) where
"attr epsilon-transitiveORDINAL1V1 for setHIDDENM2 means
  (\<lambda>X.  for x be setHIDDENM2 holds x inTARSKIR2 X implies x c=TARSKIR1 X)"..

mdef ordinal1_def_3 ("epsilon-connectedORDINAL1V2" 70 ) where
"attr epsilon-connectedORDINAL1V2 for setHIDDENM2 means
  (\<lambda>X.  for x be setHIDDENM2 holds  for y be setHIDDENM2 holds x inTARSKIR2 X & y inTARSKIR2 X implies (x inTARSKIR2 y or x =XBOOLE-0R4 y) or y inTARSKIR2 x)"..

mlemma ordinal1_lm_1:
"{}XBOOLE-0K1 be epsilon-transitiveORDINAL1V1\<bar>epsilon-connectedORDINAL1V2"
   sorry

mtheorem ordinal1_cl_2:
"cluster epsilon-transitiveORDINAL1V1\<bar>epsilon-connectedORDINAL1V2 for setHIDDENM2"
proof
(*existence*)
  show " ex it be setHIDDENM2 st it be epsilon-transitiveORDINAL1V1\<bar>epsilon-connectedORDINAL1V2"
    using ordinal1_lm_1 sorry
qed "sorry"

mdef ordinal1_def_4 ("ordinalORDINAL1V3" 70 ) where
"attr ordinalORDINAL1V3 for objectHIDDENM1 means
  (\<lambda>IT. IT be epsilon-transitiveORDINAL1V1\<bar>epsilon-connectedORDINAL1V2\<bar>setHIDDENM2)"..

mtheorem ordinal1_cl_3:
"cluster ordinalORDINAL1V3 also-is epsilon-transitiveORDINAL1V1\<bar>epsilon-connectedORDINAL1V2 for setHIDDENM2"
proof
(*coherence*)
  show " for it be setHIDDENM2 holds it be ordinalORDINAL1V3 implies it be epsilon-transitiveORDINAL1V1\<bar>epsilon-connectedORDINAL1V2"
     sorry
qed "sorry"

mtheorem ordinal1_cl_4:
"cluster epsilon-transitiveORDINAL1V1\<bar>epsilon-connectedORDINAL1V2 also-is ordinalORDINAL1V3 for setHIDDENM2"
proof
(*coherence*)
  show " for it be setHIDDENM2 holds it be epsilon-transitiveORDINAL1V1\<bar>epsilon-connectedORDINAL1V2 implies it be ordinalORDINAL1V3"
     sorry
qed "sorry"

abbreviation(input) ORDINAL1M1("NumberORDINAL1M1" 70) where
  "NumberORDINAL1M1 \<equiv> objectHIDDENM1"

abbreviation(input) ORDINAL1M2("numberORDINAL1M2" 70) where
  "numberORDINAL1M2 \<equiv> setHIDDENM2"

mtheorem ordinal1_cl_5:
"cluster ordinalORDINAL1V3 for numberORDINAL1M2"
proof
(*existence*)
  show " ex it be numberORDINAL1M2 st it be ordinalORDINAL1V3"
    using ordinal1_lm_1 sorry
qed "sorry"

mtheorem ordinal1_cl_6:
"cluster ordinalORDINAL1V3 for NumberORDINAL1M1"
proof
(*existence*)
  show " ex it be NumberORDINAL1M1 st it be ordinalORDINAL1V3"
    using ordinal1_lm_1 sorry
qed "sorry"

syntax ORDINAL1M3 :: "Ty" ("OrdinalORDINAL1M3" 70)
translations "OrdinalORDINAL1M3" \<rightharpoonup> "ordinalORDINAL1V3\<bar>numberORDINAL1M2"

reserve A, B, C, D for "OrdinalORDINAL1M3"
mtheorem ordinal1_th_10:
" for A be setHIDDENM2 holds  for B be setHIDDENM2 holds  for C be epsilon-transitiveORDINAL1V1\<bar>setHIDDENM2 holds A inTARSKIR2 B & B inTARSKIR2 C implies A inTARSKIR2 C"
sorry

mtheorem ordinal1_th_11:
" for x be epsilon-transitiveORDINAL1V1\<bar>setHIDDENM2 holds  for A be OrdinalORDINAL1M3 holds x c<XBOOLE-0R2 A implies x inTARSKIR2 A"
sorry

mtheorem ordinal1_th_12:
" for A be epsilon-transitiveORDINAL1V1\<bar>setHIDDENM2 holds  for B be OrdinalORDINAL1M3 holds  for C be OrdinalORDINAL1M3 holds A c=TARSKIR1 B & B inTARSKIR2 C implies A inTARSKIR2 C"
sorry

mtheorem ordinal1_th_13:
" for a be objectHIDDENM1 holds  for A be OrdinalORDINAL1M3 holds a inHIDDENR3 A implies a be OrdinalORDINAL1M3"
sorry

mtheorem ordinal1_th_14:
" for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds (A inTARSKIR2 B or A =XBOOLE-0R4 B) or B inTARSKIR2 A"
sorry

abbreviation(input) ORDINAL1R1(" _ c=ORDINAL1R1  _ " [50,50]50) where
  "A c=ORDINAL1R1 B \<equiv> A c=TARSKIR1 B"

mtheorem ordinal1_def_5:
  mlet "A be OrdinalORDINAL1M3", "B be OrdinalORDINAL1M3"
"redefine pred A c=ORDINAL1R1 B means
   for C be OrdinalORDINAL1M3 holds C inTARSKIR2 A implies C inTARSKIR2 B"
proof
(*compatibility*)
  show "A c=ORDINAL1R1 B iff ( for C be OrdinalORDINAL1M3 holds C inTARSKIR2 A implies C inTARSKIR2 B)"
sorry
qed "sorry"

mtheorem ORDINAL1R1_connectedness:
" for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds  not A c=ORDINAL1R1 B implies B c=ORDINAL1R1 A"
sorry

mtheorem ordinal1_th_15:
" for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds (A,B)are-c=-comparableXBOOLE-0R3"
sorry

mtheorem ordinal1_th_16:
" for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds A c=ORDINAL1R1 B or B inTARSKIR2 A"
sorry

mtheorem ordinal1_cl_7:
"cluster emptyXBOOLE-0V1 also-is ordinalORDINAL1V3 for numberORDINAL1M2"
proof
(*coherence*)
  show " for it be numberORDINAL1M2 holds it be emptyXBOOLE-0V1 implies it be ordinalORDINAL1V3"
    using ordinal1_lm_1 sorry
qed "sorry"

mtheorem ordinal1_th_17:
" for x be setHIDDENM2 holds x be OrdinalORDINAL1M3 implies succORDINAL1K1 x be OrdinalORDINAL1M3"
sorry

mtheorem ordinal1_th_18:
" for x be setHIDDENM2 holds x be ordinalORDINAL1V3 implies unionTARSKIK3 x be epsilon-transitiveORDINAL1V1\<bar>epsilon-connectedORDINAL1V2"
sorry

mtheorem ordinal1_cl_8:
"cluster  non emptyXBOOLE-0V1 for OrdinalORDINAL1M3"
proof
(*existence*)
  show " ex it be OrdinalORDINAL1M3 st it be  non emptyXBOOLE-0V1"
sorry
qed "sorry"

mtheorem ordinal1_cl_9:
  mlet "A be OrdinalORDINAL1M3"
"cluster succORDINAL1K1 A as-term-is  non emptyXBOOLE-0V1\<bar>ordinalORDINAL1V3"
proof
(*coherence*)
  show "succORDINAL1K1 A be  non emptyXBOOLE-0V1\<bar>ordinalORDINAL1V3"
    using ordinal1_th_17 sorry
qed "sorry"

mtheorem ordinal1_cl_10:
  mlet "A be OrdinalORDINAL1M3"
"cluster unionTARSKIK3 A as-term-is ordinalORDINAL1V3"
proof
(*coherence*)
  show "unionTARSKIK3 A be ordinalORDINAL1V3"
    using ordinal1_th_18 sorry
qed "sorry"

mtheorem ordinal1_th_19:
" for X be setHIDDENM2 holds ( for x be setHIDDENM2 holds x inTARSKIR2 X implies x be OrdinalORDINAL1M3 & x c=TARSKIR1 X) implies X be epsilon-transitiveORDINAL1V1\<bar>epsilon-connectedORDINAL1V2"
sorry

mtheorem ordinal1_th_20:
" for X be setHIDDENM2 holds  for A be OrdinalORDINAL1M3 holds X c=TARSKIR1 A & X <>HIDDENR2 {}XBOOLE-0K1 implies ( ex C be OrdinalORDINAL1M3 st C inTARSKIR2 X & ( for B be OrdinalORDINAL1M3 holds B inTARSKIR2 X implies C c=ORDINAL1R1 B))"
sorry

mtheorem ordinal1_th_21:
" for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds A inTARSKIR2 B iff succORDINAL1K1 A c=ORDINAL1R1 B"
sorry

mtheorem ordinal1_th_22:
" for A be OrdinalORDINAL1M3 holds  for C be OrdinalORDINAL1M3 holds A inTARSKIR2 succORDINAL1K1 C iff A c=ORDINAL1R1 C"
sorry

theorem ordinal1_sch_1:
  fixes Pp1 
  assumes
    A1: " ex A be OrdinalORDINAL1M3 st Pp1(A)"
  shows " ex A be OrdinalORDINAL1M3 st Pp1(A) & ( for B be OrdinalORDINAL1M3 holds Pp1(B) implies A c=ORDINAL1R1 B)"
sorry

(*\$N Transfinite induction*)
theorem ordinal1_sch_2:
  fixes Pp1 
  assumes
    A1: " for A be OrdinalORDINAL1M3 holds ( for C be OrdinalORDINAL1M3 holds C inTARSKIR2 A implies Pp1(C)) implies Pp1(A)"
  shows " for A be OrdinalORDINAL1M3 holds Pp1(A)"
sorry

mtheorem ordinal1_th_23:
" for X be setHIDDENM2 holds ( for a be objectHIDDENM1 holds a inHIDDENR3 X implies a be OrdinalORDINAL1M3) implies unionTARSKIK3 X be epsilon-transitiveORDINAL1V1\<bar>epsilon-connectedORDINAL1V2"
sorry

mtheorem ordinal1_th_24:
" for X be setHIDDENM2 holds ( for a be objectHIDDENM1 holds a inHIDDENR3 X implies a be OrdinalORDINAL1M3) implies ( ex A be OrdinalORDINAL1M3 st X c=TARSKIR1 A)"
sorry

mtheorem ordinal1_th_25:
" not ( ex X be setHIDDENM2 st  for x be setHIDDENM2 holds x inTARSKIR2 X iff x be OrdinalORDINAL1M3)"
sorry

mtheorem ordinal1_th_26:
" not ( ex X be setHIDDENM2 st  for A be OrdinalORDINAL1M3 holds A inTARSKIR2 X)"
sorry

mtheorem ordinal1_th_27:
" for X be setHIDDENM2 holds  ex A be OrdinalORDINAL1M3 st  not A inTARSKIR2 X & ( for B be OrdinalORDINAL1M3 holds  not B inTARSKIR2 X implies A c=ORDINAL1R1 B)"
sorry

mdef ordinal1_def_6 ("limit-ordinalORDINAL1V4" 70 ) where
"attr limit-ordinalORDINAL1V4 for setHIDDENM2 means
  (\<lambda>A. A =XBOOLE-0R4 unionTARSKIK3 A)"..

mtheorem ordinal1_th_28:
" for A be OrdinalORDINAL1M3 holds A be limit-ordinalORDINAL1V4 iff ( for C be OrdinalORDINAL1M3 holds C inTARSKIR2 A implies succORDINAL1K1 C inTARSKIR2 A)"
sorry

mtheorem ordinal1_th_29:
" for A be OrdinalORDINAL1M3 holds  not A be limit-ordinalORDINAL1V4 iff ( ex B be OrdinalORDINAL1M3 st A =XBOOLE-0R4 succORDINAL1K1 B)"
sorry

reserve F, G for "FunctionFUNCT-1M1"
mdef ordinal1_def_7 ("Sequence-likeORDINAL1V5" 70 ) where
"attr Sequence-likeORDINAL1V5 for setHIDDENM2 means
  (\<lambda>IT. proj1XTUPLE-0K12 IT be epsilon-transitiveORDINAL1V1\<bar>epsilon-connectedORDINAL1V2)"..

mtheorem ordinal1_cl_11:
"cluster emptyXBOOLE-0V1 also-is Sequence-likeORDINAL1V5 for setHIDDENM2"
proof
(*coherence*)
  show " for it be setHIDDENM2 holds it be emptyXBOOLE-0V1 implies it be Sequence-likeORDINAL1V5"
     sorry
qed "sorry"

syntax ORDINAL1M4 :: "Ty" ("SequenceORDINAL1M4" 70)
translations "SequenceORDINAL1M4" \<rightharpoonup> "Sequence-likeORDINAL1V5\<bar>FunctionFUNCT-1M1"

mtheorem ordinal1_cl_12:
  mlet "Z be setHIDDENM2"
"cluster Z -valuedRELAT-1V5 for SequenceORDINAL1M4"
proof
(*existence*)
  show " ex it be SequenceORDINAL1M4 st it be Z -valuedRELAT-1V5"
sorry
qed "sorry"

syntax ORDINAL1M5 :: " Set \<Rightarrow> Ty" ("SequenceORDINAL1M5-of  _ " [70]70)
translations "SequenceORDINAL1M5-of Z" \<rightharpoonup> "Z -valuedRELAT-1V5\<bar>SequenceORDINAL1M4"

mtheorem ordinal1_th_30:
" for Z be setHIDDENM2 holds {}XBOOLE-0K1 be SequenceORDINAL1M5-of Z"
sorry

reserve L, L1 for "SequenceORDINAL1M4"
mtheorem ordinal1_th_31:
" for F be FunctionFUNCT-1M1 holds domRELAT-1K1 F be OrdinalORDINAL1M3 implies F be SequenceORDINAL1M5-of rngFUNCT-1K2 F"
  using ordinal1_def_7 relat_1_def_19 sorry

mtheorem ordinal1_cl_13:
  mlet "L be SequenceORDINAL1M4"
"cluster domRELAT-1K1 L as-term-is ordinalORDINAL1V3"
proof
(*coherence*)
  show "domRELAT-1K1 L be ordinalORDINAL1V3"
    using ordinal1_def_7 sorry
qed "sorry"

mtheorem ordinal1_th_32:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X c=TARSKIR1 Y implies ( for L be SequenceORDINAL1M5-of X holds L be SequenceORDINAL1M5-of Y)"
sorry

mtheorem ordinal1_cl_14:
  mlet "L be SequenceORDINAL1M4", "A be OrdinalORDINAL1M3"
"cluster L |RELAT-1K8 A as-term-is rngFUNCT-1K2 L -valuedRELAT-1V5\<bar>Sequence-likeORDINAL1V5"
proof
(*coherence*)
  show "L |RELAT-1K8 A be rngFUNCT-1K2 L -valuedRELAT-1V5\<bar>Sequence-likeORDINAL1V5"
sorry
qed "sorry"

mtheorem ordinal1_th_33:
" for X be setHIDDENM2 holds  for L be SequenceORDINAL1M5-of X holds  for A be OrdinalORDINAL1M3 holds L |RELAT-1K8 A be SequenceORDINAL1M5-of X"
   sorry

mdef ordinal1_def_8 ("c=-linearORDINAL1V6" 70 ) where
"attr c=-linearORDINAL1V6 for setHIDDENM2 means
  (\<lambda>IT.  for x be setHIDDENM2 holds  for y be setHIDDENM2 holds x inTARSKIR2 IT & y inTARSKIR2 IT implies (x,y)are-c=-comparableXBOOLE-0R3)"..

mtheorem ordinal1_th_34:
" for X be setHIDDENM2 holds ( for a be objectHIDDENM1 holds a inHIDDENR3 X implies a be SequenceORDINAL1M4) & X be c=-linearORDINAL1V6 implies unionTARSKIK3 X be SequenceORDINAL1M4"
sorry

theorem ordinal1_sch_3:
  fixes Af0 Hf1 L1f0 L2f0 
  assumes
[ty]: "Af0 be OrdinalORDINAL1M3" and
  [ty_func]: "\<And> x1. x1 be SequenceORDINAL1M4 \<Longrightarrow> Hf1(x1) be setHIDDENM2" and
  [ty]: "L1f0 be SequenceORDINAL1M4" and
  [ty]: "L2f0 be SequenceORDINAL1M4" and
   A1: "domRELAT-1K1 L1f0 =XBOOLE-0R4 Af0 & ( for B be OrdinalORDINAL1M3 holds  for L be SequenceORDINAL1M4 holds B inTARSKIR2 Af0 & L =FUNCT-1R1 L1f0 |RELAT-1K8 B implies L1f0 .FUNCT-1K1 B =XBOOLE-0R4 Hf1(L))" and
   A2: "domRELAT-1K1 L2f0 =XBOOLE-0R4 Af0 & ( for B be OrdinalORDINAL1M3 holds  for L be SequenceORDINAL1M4 holds B inTARSKIR2 Af0 & L =FUNCT-1R1 L2f0 |RELAT-1K8 B implies L2f0 .FUNCT-1K1 B =XBOOLE-0R4 Hf1(L))"
  shows "L1f0 =FUNCT-1R1 L2f0"
sorry

theorem ordinal1_sch_4:
  fixes Af0 Hf1 
  assumes
[ty]: "Af0 be OrdinalORDINAL1M3" and
  [ty_func]: "\<And> x1. x1 be SequenceORDINAL1M4 \<Longrightarrow> Hf1(x1) be setHIDDENM2"
  shows " ex L be SequenceORDINAL1M4 st domRELAT-1K1 L =XBOOLE-0R4 Af0 & ( for B be OrdinalORDINAL1M3 holds  for L1 be SequenceORDINAL1M4 holds B inTARSKIR2 Af0 & L1 =FUNCT-1R1 L |RELAT-1K8 B implies L .FUNCT-1K1 B =XBOOLE-0R4 Hf1(L1))"
sorry

theorem ordinal1_sch_5:
  fixes Lf0 Ff1 Hf1 
  assumes
[ty]: "Lf0 be SequenceORDINAL1M4" and
  [ty_func]: "\<And> x1. x1 be OrdinalORDINAL1M3 \<Longrightarrow> Ff1(x1) be setHIDDENM2" and
  [ty_func]: "\<And> x1. x1 be SequenceORDINAL1M4 \<Longrightarrow> Hf1(x1) be setHIDDENM2" and
   A1: " for A be OrdinalORDINAL1M3 holds  for a be objectHIDDENM1 holds a =HIDDENR1 Ff1(A) iff ( ex L be SequenceORDINAL1M4 st (a =HIDDENR1 Hf1(L) & domRELAT-1K1 L =XBOOLE-0R4 A) & ( for B be OrdinalORDINAL1M3 holds B inTARSKIR2 A implies L .FUNCT-1K1 B =XBOOLE-0R4 Hf1(L |RELAT-1K8 B)))" and
   A2: " for A be OrdinalORDINAL1M3 holds A inTARSKIR2 domRELAT-1K1 Lf0 implies Lf0 .FUNCT-1K1 A =XBOOLE-0R4 Ff1(A)"
  shows " for B be OrdinalORDINAL1M3 holds B inTARSKIR2 domRELAT-1K1 Lf0 implies Lf0 .FUNCT-1K1 B =XBOOLE-0R4 Hf1(Lf0 |RELAT-1K8 B)"
sorry

mtheorem ordinal1_th_35:
" for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds (A c<XBOOLE-0R2 B or A =XBOOLE-0R4 B) or B c<XBOOLE-0R2 A"
sorry

(*begin*)
mdef ordinal1_def_9 ("OnORDINAL1K2  _ " [228]228 ) where
  mlet "X be setHIDDENM2"
"func OnORDINAL1K2 X \<rightarrow> setHIDDENM2 means
  \<lambda>it.  for x be objectHIDDENM1 holds x inHIDDENR3 it iff x inHIDDENR3 X & x be OrdinalORDINAL1M3"
proof-
  (*existence*)
    show " ex it be setHIDDENM2 st  for x be objectHIDDENM1 holds x inHIDDENR3 it iff x inHIDDENR3 X & x be OrdinalORDINAL1M3"
sorry
  (*uniqueness*)
    show " for it1 be setHIDDENM2 holds  for it2 be setHIDDENM2 holds ( for x be objectHIDDENM1 holds x inHIDDENR3 it1 iff x inHIDDENR3 X & x be OrdinalORDINAL1M3) & ( for x be objectHIDDENM1 holds x inHIDDENR3 it2 iff x inHIDDENR3 X & x be OrdinalORDINAL1M3) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mdef ordinal1_def_10 ("LimORDINAL1K3  _ " [228]228 ) where
  mlet "X be setHIDDENM2"
"func LimORDINAL1K3 X \<rightarrow> setHIDDENM2 means
  \<lambda>it.  for x be objectHIDDENM1 holds x inHIDDENR3 it iff x inHIDDENR3 X & ( ex A be OrdinalORDINAL1M3 st x =HIDDENR1 A & A be limit-ordinalORDINAL1V4)"
proof-
  (*existence*)
    show " ex it be setHIDDENM2 st  for x be objectHIDDENM1 holds x inHIDDENR3 it iff x inHIDDENR3 X & ( ex A be OrdinalORDINAL1M3 st x =HIDDENR1 A & A be limit-ordinalORDINAL1V4)"
sorry
  (*uniqueness*)
    show " for it1 be setHIDDENM2 holds  for it2 be setHIDDENM2 holds ( for x be objectHIDDENM1 holds x inHIDDENR3 it1 iff x inHIDDENR3 X & ( ex A be OrdinalORDINAL1M3 st x =HIDDENR1 A & A be limit-ordinalORDINAL1V4)) & ( for x be objectHIDDENM1 holds x inHIDDENR3 it2 iff x inHIDDENR3 X & ( ex A be OrdinalORDINAL1M3 st x =HIDDENR1 A & A be limit-ordinalORDINAL1V4)) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

(*\$N Generalized Axiom of Infinity*)
mtheorem ordinal1_th_36:
" for D be OrdinalORDINAL1M3 holds  ex A be OrdinalORDINAL1M3 st D inTARSKIR2 A & A be limit-ordinalORDINAL1V4"
sorry

mdef ordinal1_def_11 ("omegaORDINAL1K4" 228 ) where
"func omegaORDINAL1K4 \<rightarrow> setHIDDENM2 means
  \<lambda>it. (({}XBOOLE-0K1 inTARSKIR2 it & it be limit-ordinalORDINAL1V4) & it be ordinalORDINAL1V3) & ( for A be OrdinalORDINAL1M3 holds {}XBOOLE-0K1 inTARSKIR2 A & A be limit-ordinalORDINAL1V4 implies it c=TARSKIR1 A)"
proof-
  (*existence*)
    show " ex it be setHIDDENM2 st (({}XBOOLE-0K1 inTARSKIR2 it & it be limit-ordinalORDINAL1V4) & it be ordinalORDINAL1V3) & ( for A be OrdinalORDINAL1M3 holds {}XBOOLE-0K1 inTARSKIR2 A & A be limit-ordinalORDINAL1V4 implies it c=TARSKIR1 A)"
sorry
  (*uniqueness*)
    show " for it1 be setHIDDENM2 holds  for it2 be setHIDDENM2 holds ((({}XBOOLE-0K1 inTARSKIR2 it1 & it1 be limit-ordinalORDINAL1V4) & it1 be ordinalORDINAL1V3) & ( for A be OrdinalORDINAL1M3 holds {}XBOOLE-0K1 inTARSKIR2 A & A be limit-ordinalORDINAL1V4 implies it1 c=TARSKIR1 A)) & ((({}XBOOLE-0K1 inTARSKIR2 it2 & it2 be limit-ordinalORDINAL1V4) & it2 be ordinalORDINAL1V3) & ( for A be OrdinalORDINAL1M3 holds {}XBOOLE-0K1 inTARSKIR2 A & A be limit-ordinalORDINAL1V4 implies it2 c=TARSKIR1 A)) implies it1 =HIDDENR1 it2"
       sorry
qed "sorry"

mtheorem ordinal1_cl_15:
"cluster omegaORDINAL1K4 as-term-is  non emptyXBOOLE-0V1\<bar>ordinalORDINAL1V3"
proof
(*coherence*)
  show "omegaORDINAL1K4 be  non emptyXBOOLE-0V1\<bar>ordinalORDINAL1V3"
    using ordinal1_def_11 sorry
qed "sorry"

mdef ordinal1_def_12 ("naturalORDINAL1V7" 70 ) where
"attr naturalORDINAL1V7 for objectHIDDENM1 means
  (\<lambda>A. A inHIDDENR3 omegaORDINAL1K4)"..

mtheorem ordinal1_cl_16:
"cluster naturalORDINAL1V7 for NumberORDINAL1M1"
proof
(*existence*)
  show " ex it be NumberORDINAL1M1 st it be naturalORDINAL1V7"
sorry
qed "sorry"

mtheorem ordinal1_cl_17:
"cluster naturalORDINAL1V7 for setHIDDENM2"
proof
(*existence*)
  show " ex it be setHIDDENM2 st it be naturalORDINAL1V7"
sorry
qed "sorry"

syntax ORDINAL1M6 :: "Ty" ("NatORDINAL1M6" 70)
translations "NatORDINAL1M6" \<rightharpoonup> "naturalORDINAL1V7\<bar>setHIDDENM2"

mtheorem
"cluster sethood of NatORDINAL1M6"
proof
(*sethood*)
  show " ex cover be setHIDDENM2 st  for it be NatORDINAL1M6 holds it inHIDDENR3 cover"
sorry
qed "sorry"

mtheorem ordinal1_cl_18:
  mlet "A be OrdinalORDINAL1M3"
"cluster note-that ordinalORDINAL1V3 for ElementSUBSET-1M1-of A"
proof
(*coherence*)
  show " for it be ElementSUBSET-1M1-of A holds it be ordinalORDINAL1V3"
sorry
qed "sorry"

mtheorem ordinal1_cl_19:
"cluster naturalORDINAL1V7 also-is ordinalORDINAL1V3 for numberORDINAL1M2"
proof
(*coherence*)
  show " for it be numberORDINAL1M2 holds it be naturalORDINAL1V7 implies it be ordinalORDINAL1V3"
     sorry
qed "sorry"

theorem ordinal1_sch_6:
  fixes Df0 Pp2 
  assumes
[ty]: "Df0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
   A1: " for d be ElementSUBSET-1M1-of Df0 holds  ex A be OrdinalORDINAL1M3 st Pp2(d,A)"
  shows " ex F be FunctionFUNCT-1M1 st domRELAT-1K1 F =XBOOLE-0R4 Df0 & ( for d be ElementSUBSET-1M1-of Df0 holds  ex A be OrdinalORDINAL1M3 st (A =XBOOLE-0R4 F .FUNCT-1K1 d & Pp2(d,A)) & ( for B be OrdinalORDINAL1M3 holds Pp2(d,B) implies A c=ORDINAL1R1 B))"
sorry

mtheorem ordinal1_th_37:
" for X be setHIDDENM2 holds succORDINAL1K1 X \\SUBSET-1K6 {TARSKIK1 X} =XBOOLE-0R4 X"
sorry

mtheorem ordinal1_cl_20:
"cluster emptyXBOOLE-0V1 also-is naturalORDINAL1V7 for numberORDINAL1M2"
proof
(*coherence*)
  show " for it be numberORDINAL1M2 holds it be emptyXBOOLE-0V1 implies it be naturalORDINAL1V7"
    using ordinal1_def_11 sorry
qed "sorry"

mtheorem ordinal1_cl_21:
"cluster note-that naturalORDINAL1V7 for ElementSUBSET-1M1-of omegaORDINAL1K4"
proof
(*coherence*)
  show " for it be ElementSUBSET-1M1-of omegaORDINAL1K4 holds it be naturalORDINAL1V7"
     sorry
qed "sorry"

mtheorem ordinal1_cl_22:
"cluster  non emptyXBOOLE-0V1\<bar>naturalORDINAL1V7 for numberORDINAL1M2"
proof
(*existence*)
  show " ex it be numberORDINAL1M2 st it be  non emptyXBOOLE-0V1\<bar>naturalORDINAL1V7"
sorry
qed "sorry"

mtheorem ordinal1_cl_23:
  mlet "a be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3"
"cluster succORDINAL1K1 a as-term-is naturalORDINAL1V7"
proof
(*coherence*)
  show "succORDINAL1K1 a be naturalORDINAL1V7"
sorry
qed "sorry"

mtheorem ordinal1_cl_24:
"cluster emptyXBOOLE-0V1 also-is c=-linearORDINAL1V6 for setHIDDENM2"
proof
(*coherence*)
  show " for it be setHIDDENM2 holds it be emptyXBOOLE-0V1 implies it be c=-linearORDINAL1V6"
     sorry
qed "sorry"

mtheorem ordinal1_cl_25:
  mlet "X be c=-linearORDINAL1V6\<bar>setHIDDENM2"
"cluster note-that c=-linearORDINAL1V6 for SubsetSUBSET-1M2-of X"
proof
(*coherence*)
  show " for it be SubsetSUBSET-1M2-of X holds it be c=-linearORDINAL1V6"
    using ordinal1_def_8 sorry
qed "sorry"

(*\$CT*)
mdef ordinal1_def_13 ("0ORDINAL1K5" 164 ) where
"func 0ORDINAL1K5 \<rightarrow> numberORDINAL1M2 equals
  {}XBOOLE-0K1"
proof-
  (*coherence*)
    show "{}XBOOLE-0K1 be numberORDINAL1M2"
       sorry
qed "sorry"

mtheorem ordinal1_cl_26:
"cluster 0ORDINAL1K5 as-term-is naturalORDINAL1V7"
proof
(*coherence*)
  show "0ORDINAL1K5 be naturalORDINAL1V7"
     sorry
qed "sorry"

mdef ordinal1_def_14 ("zeroORDINAL1V8" 70 ) where
"attr zeroORDINAL1V8 for NumberORDINAL1M1 means
  (\<lambda>x. x =HIDDENR1 0ORDINAL1K5)"..

mtheorem ordinal1_cl_27:
"cluster 0ORDINAL1K5 as-term-is zeroORDINAL1V8"
proof
(*coherence*)
  show "0ORDINAL1K5 be zeroORDINAL1V8"
     sorry
qed "sorry"

mtheorem ordinal1_cl_28:
"cluster zeroORDINAL1V8 for NumberORDINAL1M1"
proof
(*existence*)
  show " ex it be NumberORDINAL1M1 st it be zeroORDINAL1V8"
sorry
qed "sorry"

mtheorem ordinal1_cl_29:
"cluster zeroORDINAL1V8 for setHIDDENM2"
proof
(*existence*)
  show " ex it be setHIDDENM2 st it be zeroORDINAL1V8"
sorry
qed "sorry"

mtheorem ordinal1_cl_30:
"cluster zeroORDINAL1V8 also-is naturalORDINAL1V7 for NumberORDINAL1M1"
proof
(*coherence*)
  show " for it be NumberORDINAL1M1 holds it be zeroORDINAL1V8 implies it be naturalORDINAL1V7"
     sorry
qed "sorry"

mtheorem ordinal1_cl_31:
"cluster  non zeroORDINAL1V8 for NumberORDINAL1M1"
proof
(*existence*)
  show " ex it be NumberORDINAL1M1 st it be  non zeroORDINAL1V8"
sorry
qed "sorry"

mtheorem ordinal1_cl_32:
"cluster zeroORDINAL1V8 also-is trivialSUBSET-1V2 for setHIDDENM2"
proof
(*coherence*)
  show " for it be setHIDDENM2 holds it be zeroORDINAL1V8 implies it be trivialSUBSET-1V2"
     sorry
qed "sorry"

mtheorem ordinal1_cl_33:
"cluster  non trivialSUBSET-1V2 also-is  non zeroORDINAL1V8 for setHIDDENM2"
proof
(*coherence*)
  show " for it be setHIDDENM2 holds it be  non trivialSUBSET-1V2 implies it be  non zeroORDINAL1V8"
     sorry
qed "sorry"

mdef ordinal1_def_15 ("non-zeroORDINAL1V9" 70 ) where
"attr non-zeroORDINAL1V9 for RelationRELAT-1M1 means
  (\<lambda>R.  not 0ORDINAL1K5 inTARSKIR2 rngRELAT-1K2 R)"..

mdef ordinal1_def_16 ("with-zeroORDINAL1V10" 70 ) where
"attr with-zeroORDINAL1V10 for setHIDDENM2 means
  (\<lambda>X. 0ORDINAL1K5 inTARSKIR2 X)"..

syntax ORDINAL1V11 :: "Ty" ("without-zeroORDINAL1V11" 70)
translations "without-zeroORDINAL1V11" \<rightharpoonup> " non with-zeroORDINAL1V10"

mtheorem ordinal1_cl_34:
"cluster emptyXBOOLE-0V1 also-is without-zeroORDINAL1V11 for setHIDDENM2"
proof
(*coherence*)
  show " for it be setHIDDENM2 holds it be emptyXBOOLE-0V1 implies it be without-zeroORDINAL1V11"
     sorry
qed "sorry"

mtheorem ordinal1_cl_35:
"cluster emptyXBOOLE-0V1 also-is non-zeroORDINAL1V9 for RelationRELAT-1M1"
proof
(*coherence*)
  show " for it be RelationRELAT-1M1 holds it be emptyXBOOLE-0V1 implies it be non-zeroORDINAL1V9"
     sorry
qed "sorry"

mtheorem ordinal1_cl_36:
"cluster without-zeroORDINAL1V11\<bar> non emptyXBOOLE-0V1 for setHIDDENM2"
proof
(*existence*)
  show " ex it be setHIDDENM2 st it be without-zeroORDINAL1V11\<bar> non emptyXBOOLE-0V1"
sorry
qed "sorry"

mtheorem ordinal1_cl_37:
  mlet "X be without-zeroORDINAL1V11\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster note-that  non zeroORDINAL1V8 for ElementSUBSET-1M1-of X"
proof
(*coherence*)
  show " for it be ElementSUBSET-1M1-of X holds it be  non zeroORDINAL1V8"
    using ordinal1_def_16 sorry
qed "sorry"

mtheorem ordinal1_cl_38:
"cluster non-zeroORDINAL1V9 for RelationRELAT-1M1"
proof
(*existence*)
  show " ex it be RelationRELAT-1M1 st it be non-zeroORDINAL1V9"
sorry
qed "sorry"

mtheorem ordinal1_cl_39:
"cluster  non non-zeroORDINAL1V9 for RelationRELAT-1M1"
proof
(*existence*)
  show " ex it be RelationRELAT-1M1 st it be  non non-zeroORDINAL1V9"
sorry
qed "sorry"

mtheorem ordinal1_cl_40:
  mlet "R be non-zeroORDINAL1V9\<bar>RelationRELAT-1M1"
"cluster rngRELAT-1K2 R as-term-is without-zeroORDINAL1V11"
proof
(*coherence*)
  show "rngRELAT-1K2 R be without-zeroORDINAL1V11"
    using ordinal1_def_15 sorry
qed "sorry"

mtheorem ordinal1_cl_41:
  mlet "R be  non non-zeroORDINAL1V9\<bar>RelationRELAT-1M1"
"cluster rngRELAT-1K2 R as-term-is with-zeroORDINAL1V10"
proof
(*coherence*)
  show "rngRELAT-1K2 R be with-zeroORDINAL1V10"
    using ordinal1_def_15 sorry
qed "sorry"

mtheorem ordinal1_cl_42:
  mlet "R be non-zeroORDINAL1V9\<bar>RelationRELAT-1M1", "S be RelationRELAT-1M1"
"cluster S *RELAT-1K6 R as-term-is non-zeroORDINAL1V9"
proof
(*coherence*)
  show "S *RELAT-1K6 R be non-zeroORDINAL1V9"
sorry
qed "sorry"

mtheorem ordinal1_cl_43:
"cluster without-zeroORDINAL1V11 also-is with-non-empty-elementsSETFAM-1V1 for setHIDDENM2"
proof
(*coherence*)
  show " for it be setHIDDENM2 holds it be without-zeroORDINAL1V11 implies it be with-non-empty-elementsSETFAM-1V1"
sorry
qed "sorry"

mtheorem ordinal1_cl_44:
"cluster with-zeroORDINAL1V10 also-is  non with-non-empty-elementsSETFAM-1V1 for setHIDDENM2"
proof
(*coherence*)
  show " for it be setHIDDENM2 holds it be with-zeroORDINAL1V10 implies it be  non with-non-empty-elementsSETFAM-1V1"
sorry
qed "sorry"

mtheorem ordinal1_cl_45:
"cluster with-non-empty-elementsSETFAM-1V1 also-is without-zeroORDINAL1V11 for setHIDDENM2"
proof
(*coherence*)
  show " for it be setHIDDENM2 holds it be with-non-empty-elementsSETFAM-1V1 implies it be without-zeroORDINAL1V11"
     sorry
qed "sorry"

mtheorem ordinal1_cl_46:
"cluster  non with-non-empty-elementsSETFAM-1V1 also-is with-zeroORDINAL1V10 for setHIDDENM2"
proof
(*coherence*)
  show " for it be setHIDDENM2 holds it be  non with-non-empty-elementsSETFAM-1V1 implies it be with-zeroORDINAL1V10"
     sorry
qed "sorry"

mdef ordinal1_def_17 ("SegmORDINAL1K6  _ " [164]164 ) where
  mlet "o be objectHIDDENM1"
"func SegmORDINAL1K6 o \<rightarrow> setHIDDENM2 equals
  o"
proof-
  (*coherence*)
    show "o be setHIDDENM2"
      using tarski_th_1 sorry
qed "sorry"

mtheorem ordinal1_cl_47:
  mlet "n be OrdinalORDINAL1M3"
"cluster SegmORDINAL1K6 n as-term-is ordinalORDINAL1V3"
proof
(*coherence*)
  show "SegmORDINAL1K6 n be ordinalORDINAL1V3"
     sorry
qed "sorry"

mtheorem ordinal1_cl_48:
  mlet "n be zeroORDINAL1V8\<bar>OrdinalORDINAL1M3"
"cluster SegmORDINAL1K6 n as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "SegmORDINAL1K6 n be emptyXBOOLE-0V1"
    using ordinal1_def_14 sorry
qed "sorry"

end
