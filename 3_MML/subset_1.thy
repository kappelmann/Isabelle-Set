theory subset_1
  imports zfmisc_1
begin
(*begin*)
reserve E, X, Y, x, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10 for "setHIDDENM2"
mtheorem subset_1_cl_1:
  mlet "X be setHIDDENM2"
"cluster boolZFMISC-1K1 X as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "boolZFMISC-1K1 X be  non emptyXBOOLE-0V1"
    using zfmisc_1_def_1 sorry
qed "sorry"

mtheorem subset_1_cl_2:
  mlet "x1 be objectHIDDENM1", "x2 be objectHIDDENM1", "x3 be objectHIDDENM1"
"cluster {ENUMSET1K1 x1,x2,x3 } as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "{ENUMSET1K1 x1,x2,x3 } be  non emptyXBOOLE-0V1"
    using enumset1_def_1 sorry
qed "sorry"

mtheorem subset_1_cl_3:
  mlet "x1 be objectHIDDENM1", "x2 be objectHIDDENM1", "x3 be objectHIDDENM1", "x4 be objectHIDDENM1"
"cluster {ENUMSET1K2 x1,x2,x3,x4 } as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "{ENUMSET1K2 x1,x2,x3,x4 } be  non emptyXBOOLE-0V1"
    using enumset1_def_2 sorry
qed "sorry"

mtheorem subset_1_cl_4:
  mlet "x1 be objectHIDDENM1", "x2 be objectHIDDENM1", "x3 be objectHIDDENM1", "x4 be objectHIDDENM1", "x5 be objectHIDDENM1"
"cluster {ENUMSET1K3 x1,x2,x3,x4,x5 } as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "{ENUMSET1K3 x1,x2,x3,x4,x5 } be  non emptyXBOOLE-0V1"
    using enumset1_def_3 sorry
qed "sorry"

mtheorem subset_1_cl_5:
  mlet "x1 be objectHIDDENM1", "x2 be objectHIDDENM1", "x3 be objectHIDDENM1", "x4 be objectHIDDENM1", "x5 be objectHIDDENM1", "x6 be objectHIDDENM1"
"cluster {ENUMSET1K4 x1,x2,x3,x4,x5,x6 } as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "{ENUMSET1K4 x1,x2,x3,x4,x5,x6 } be  non emptyXBOOLE-0V1"
    using enumset1_def_4 sorry
qed "sorry"

mtheorem subset_1_cl_6:
  mlet "x1 be objectHIDDENM1", "x2 be objectHIDDENM1", "x3 be objectHIDDENM1", "x4 be objectHIDDENM1", "x5 be objectHIDDENM1", "x6 be objectHIDDENM1", "x7 be objectHIDDENM1"
"cluster {ENUMSET1K5 x1,x2,x3,x4,x5,x6,x7 } as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "{ENUMSET1K5 x1,x2,x3,x4,x5,x6,x7 } be  non emptyXBOOLE-0V1"
    using enumset1_def_5 sorry
qed "sorry"

mtheorem subset_1_cl_7:
  mlet "x1 be objectHIDDENM1", "x2 be objectHIDDENM1", "x3 be objectHIDDENM1", "x4 be objectHIDDENM1", "x5 be objectHIDDENM1", "x6 be objectHIDDENM1", "x7 be objectHIDDENM1", "x8 be objectHIDDENM1"
"cluster {ENUMSET1K6 x1,x2,x3,x4,x5,x6,x7,x8 } as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "{ENUMSET1K6 x1,x2,x3,x4,x5,x6,x7,x8 } be  non emptyXBOOLE-0V1"
    using enumset1_def_6 sorry
qed "sorry"

mtheorem subset_1_cl_8:
  mlet "x1 be objectHIDDENM1", "x2 be objectHIDDENM1", "x3 be objectHIDDENM1", "x4 be objectHIDDENM1", "x5 be objectHIDDENM1", "x6 be objectHIDDENM1", "x7 be objectHIDDENM1", "x8 be objectHIDDENM1", "x9 be objectHIDDENM1"
"cluster {ENUMSET1K7 x1,x2,x3,x4,x5,x6,x7,x8,x9 } as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "{ENUMSET1K7 x1,x2,x3,x4,x5,x6,x7,x8,x9 } be  non emptyXBOOLE-0V1"
    using enumset1_def_7 sorry
qed "sorry"

mtheorem subset_1_cl_9:
  mlet "x1 be objectHIDDENM1", "x2 be objectHIDDENM1", "x3 be objectHIDDENM1", "x4 be objectHIDDENM1", "x5 be objectHIDDENM1", "x6 be objectHIDDENM1", "x7 be objectHIDDENM1", "x8 be objectHIDDENM1", "x9 be objectHIDDENM1", "x10 be objectHIDDENM1"
"cluster {ENUMSET1K8 x1,x2,x3,x4,x5,x6,x7,x8,x9,x10 } as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "{ENUMSET1K8 x1,x2,x3,x4,x5,x6,x7,x8,x9,x10 } be  non emptyXBOOLE-0V1"
    using enumset1_def_8 sorry
qed "sorry"

mdef subset_1_def_1 ("ElementSUBSET-1M1-of  _ " [70]70 ) where
  mlet "X be setHIDDENM2"
"mode ElementSUBSET-1M1-of X \<rightarrow> setHIDDENM2 means
  (\<lambda>it. it inTARSKIR2 X if X be  non emptyXBOOLE-0V1 otherwise \<lambda>it. it be emptyXBOOLE-0V1)"
proof-
  (*existence*)
    show "(X be  non emptyXBOOLE-0V1 implies ( ex it be setHIDDENM2 st it inTARSKIR2 X)) & ( not X be  non emptyXBOOLE-0V1 implies ( ex it be setHIDDENM2 st it be emptyXBOOLE-0V1))"
sorry
  (*consistency*)
    show " for it be setHIDDENM2 holds  True "
       sorry
qed "sorry"

mtheorem SUBSET_1M1sethood:
  mlet "X be setHIDDENM2"
"cluster sethood of ElementSUBSET-1M1-of X"
proof
(*sethood*)
  show " ex cover be setHIDDENM2 st  for it be ElementSUBSET-1M1-of X holds it inHIDDENR3 cover"
sorry
qed "sorry"

abbreviation(input) SUBSET_1M2("SubsetSUBSET-1M2-of  _ " [70]70) where
  "SubsetSUBSET-1M2-of X \<equiv> ElementSUBSET-1M1-of boolZFMISC-1K1 X"

mtheorem subset_1_cl_10:
  mlet "X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster  non emptyXBOOLE-0V1 for SubsetSUBSET-1M2-of X"
proof
(*existence*)
  show " ex it be SubsetSUBSET-1M2-of X st it be  non emptyXBOOLE-0V1"
sorry
qed "sorry"

mtheorem subset_1_cl_11:
  mlet "X1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "X2 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster [:ZFMISC-1K2 X1,X2 :] as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "[:ZFMISC-1K2 X1,X2 :] be  non emptyXBOOLE-0V1"
sorry
qed "sorry"

mtheorem subset_1_cl_12:
  mlet "X1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "X2 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "X3 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster [:ZFMISC-1K3 X1,X2,X3 :] as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "[:ZFMISC-1K3 X1,X2,X3 :] be  non emptyXBOOLE-0V1"
     sorry
qed "sorry"

mtheorem subset_1_cl_13:
  mlet "X1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "X2 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "X3 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "X4 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster [:ZFMISC-1K4 X1,X2,X3,X4 :] as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "[:ZFMISC-1K4 X1,X2,X3,X4 :] be  non emptyXBOOLE-0V1"
     sorry
qed "sorry"

syntax SUBSET_1M3 :: " Set \<Rightarrow>  Set \<Rightarrow> Ty" ("ElementSUBSET-1M3\<^bsub>'( _ ')\<^esub>-of  _ " [0,70]70)
translations "ElementSUBSET-1M3\<^bsub>(D)\<^esub>-of X" \<rightharpoonup> "ElementSUBSET-1M1-of X"

mtheorem subset_1_add_1:
  mlet "D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "X be  non emptyXBOOLE-0V1\<bar>SubsetSUBSET-1M2-of D"
"cluster note-that ElementSUBSET-1M1-of D for ElementSUBSET-1M1-of X"
proof
(*coherence*)
  show " for it be ElementSUBSET-1M1-of X holds it be ElementSUBSET-1M1-of D"
sorry
qed "sorry"

mlemma subset_1_lm_1:
" for E be setHIDDENM2 holds  for X be SubsetSUBSET-1M2-of E holds  for x be objectHIDDENM1 holds x inHIDDENR3 X implies x inHIDDENR3 E"
sorry

mtheorem subset_1_cl_14:
  mlet "E be setHIDDENM2"
"cluster emptyXBOOLE-0V1 for SubsetSUBSET-1M2-of E"
proof
(*existence*)
  show " ex it be SubsetSUBSET-1M2-of E st it be emptyXBOOLE-0V1"
sorry
qed "sorry"

mdef subset_1_def_2 ("{}SUBSET-1K1  _ " [228]228 ) where
  mlet "E be setHIDDENM2"
"func {}SUBSET-1K1 E \<rightarrow> SubsetSUBSET-1M2-of E equals
  {}XBOOLE-0K1"
proof-
  (*coherence*)
    show "{}XBOOLE-0K1 be SubsetSUBSET-1M2-of E"
sorry
qed "sorry"

mdef subset_1_def_3 ("[#]SUBSET-1K2  _ " [228]228 ) where
  mlet "E be setHIDDENM2"
"func [#]SUBSET-1K2 E \<rightarrow> SubsetSUBSET-1M2-of E equals
  E"
proof-
  (*coherence*)
    show "E be SubsetSUBSET-1M2-of E"
sorry
qed "sorry"

mtheorem subset_1_cl_15:
  mlet "E be setHIDDENM2"
"cluster {}SUBSET-1K1 E as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "{}SUBSET-1K1 E be emptyXBOOLE-0V1"
     sorry
qed "sorry"

mtheorem subset_1_th_1:
" for X be setHIDDENM2 holds {}XBOOLE-0K1 be SubsetSUBSET-1M2-of X"
sorry

reserve A, B, C for "SubsetSUBSET-1M2-of E"
mtheorem subset_1_th_2:
" for E be setHIDDENM2 holds  for A be SubsetSUBSET-1M2-of E holds  for B be SubsetSUBSET-1M2-of E holds ( for x be ElementSUBSET-1M1-of E holds x inTARSKIR2 A implies x inTARSKIR2 B) implies A c=TARSKIR1 B"
sorry

mtheorem subset_1_th_3:
" for E be setHIDDENM2 holds  for A be SubsetSUBSET-1M2-of E holds  for B be SubsetSUBSET-1M2-of E holds ( for x be ElementSUBSET-1M1-of E holds x inTARSKIR2 A iff x inTARSKIR2 B) implies A =XBOOLE-0R4 B"
  using subset_1_th_2 sorry

mtheorem subset_1_th_4:
" for E be setHIDDENM2 holds  for A be SubsetSUBSET-1M2-of E holds A <>HIDDENR2 {}XBOOLE-0K1 implies ( ex x be ElementSUBSET-1M1-of E st x inTARSKIR2 A)"
sorry

mdef subset_1_def_4 (" _ `SUBSET-1K3\<^bsub>'( _ ')\<^esub>" [250,0]250 ) where
  mlet "E be setHIDDENM2", "A be SubsetSUBSET-1M2-of E"
"func A `SUBSET-1K3\<^bsub>(E)\<^esub> \<rightarrow> SubsetSUBSET-1M2-of E equals
  E \\XBOOLE-0K4 A"
proof-
  (*coherence*)
    show "E \\XBOOLE-0K4 A be SubsetSUBSET-1M2-of E"
sorry
qed "sorry"

mtheorem SUBSET_1K3_involutiveness:
  mlet "E be setHIDDENM2"
" for A be SubsetSUBSET-1M2-of E holds (A `SUBSET-1K3\<^bsub>(E)\<^esub>)`SUBSET-1K3\<^bsub>(E)\<^esub> =HIDDENR1 A"
sorry

syntax SUBSET_1K4 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ '\\'/SUBSET-1K4\<^bsub>'( _ ')\<^esub>  _ " [132,0,132]132)
translations "A \\/SUBSET-1K4\<^bsub>(E)\<^esub> B" \<rightharpoonup> "A \\/XBOOLE-0K2 B"

mtheorem subset_1_add_2:
  mlet "E be setHIDDENM2", "A be SubsetSUBSET-1M2-of E", "B be SubsetSUBSET-1M2-of E"
"cluster A \\/XBOOLE-0K2 B as-term-is SubsetSUBSET-1M2-of E"
proof
(*coherence*)
  show "A \\/XBOOLE-0K2 B be SubsetSUBSET-1M2-of E"
sorry
qed "sorry"

syntax SUBSET_1K5 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ '\\+'\\SUBSET-1K5\<^bsub>'( _ ')\<^esub>  _ " [130,0,130]130)
translations "A \\+\\SUBSET-1K5\<^bsub>(E)\<^esub> B" \<rightharpoonup> "A \\+\\XBOOLE-0K5 B"

mtheorem subset_1_add_3:
  mlet "E be setHIDDENM2", "A be SubsetSUBSET-1M2-of E", "B be SubsetSUBSET-1M2-of E"
"cluster A \\+\\XBOOLE-0K5 B as-term-is SubsetSUBSET-1M2-of E"
proof
(*coherence*)
  show "A \\+\\XBOOLE-0K5 B be SubsetSUBSET-1M2-of E"
sorry
qed "sorry"

abbreviation(input) SUBSET_1K6(" _ '\\SUBSET-1K6  _ " [132,132]132) where
  "X \\SUBSET-1K6 Y \<equiv> X \\XBOOLE-0K4 Y"

mtheorem subset_1_add_4:
  mlet "X be setHIDDENM2", "Y be setHIDDENM2"
"cluster X \\XBOOLE-0K4 Y as-term-is SubsetSUBSET-1M2-of X"
proof
(*coherence*)
  show "X \\XBOOLE-0K4 Y be SubsetSUBSET-1M2-of X"
sorry
qed "sorry"

syntax SUBSET_1K7 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ '\\SUBSET-1K7\<^bsub>'( _ ')\<^esub>  _ " [132,0,132]132)
translations "A \\SUBSET-1K7\<^bsub>(E)\<^esub> X" \<rightharpoonup> "A \\XBOOLE-0K4 X"

mtheorem subset_1_add_5:
  mlet "E be setHIDDENM2", "A be SubsetSUBSET-1M2-of E", "X be setHIDDENM2"
"cluster A \\XBOOLE-0K4 X as-term-is SubsetSUBSET-1M2-of E"
proof
(*coherence*)
  show "A \\XBOOLE-0K4 X be SubsetSUBSET-1M2-of E"
sorry
qed "sorry"

syntax SUBSET_1K8 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ '/'\\SUBSET-1K8\<^bsub>'( _ ')\<^esub>  _ " [164,0,164]164)
translations "A /\\SUBSET-1K8\<^bsub>(E)\<^esub> X" \<rightharpoonup> "A /\\XBOOLE-0K3 X"

mtheorem subset_1_add_6:
  mlet "E be setHIDDENM2", "A be SubsetSUBSET-1M2-of E", "X be setHIDDENM2"
"cluster A /\\XBOOLE-0K3 X as-term-is SubsetSUBSET-1M2-of E"
proof
(*coherence*)
  show "A /\\XBOOLE-0K3 X be SubsetSUBSET-1M2-of E"
sorry
qed "sorry"

syntax SUBSET_1K9 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ '/'\\SUBSET-1K9\<^bsub>'( _ ')\<^esub>  _ " [164,0,164]164)
translations "X /\\SUBSET-1K9\<^bsub>(E)\<^esub> A" \<rightharpoonup> "X /\\XBOOLE-0K3 A"

mtheorem subset_1_add_7:
  mlet "E be setHIDDENM2", "X be setHIDDENM2", "A be SubsetSUBSET-1M2-of E"
"cluster X /\\XBOOLE-0K3 A as-term-is SubsetSUBSET-1M2-of E"
proof
(*coherence*)
  show "X /\\XBOOLE-0K3 A be SubsetSUBSET-1M2-of E"
sorry
qed "sorry"

mtheorem subset_1_th_5:
" for E be setHIDDENM2 holds  for A be SubsetSUBSET-1M2-of E holds  for B be SubsetSUBSET-1M2-of E holds  for C be SubsetSUBSET-1M2-of E holds ( for x be ElementSUBSET-1M1-of E holds x inTARSKIR2 A iff x inTARSKIR2 B or x inTARSKIR2 C) implies A =XBOOLE-0R4 B \\/SUBSET-1K4\<^bsub>(E)\<^esub> C"
sorry

mtheorem subset_1_th_6:
" for E be setHIDDENM2 holds  for A be SubsetSUBSET-1M2-of E holds  for B be SubsetSUBSET-1M2-of E holds  for C be SubsetSUBSET-1M2-of E holds ( for x be ElementSUBSET-1M1-of E holds x inTARSKIR2 A iff x inTARSKIR2 B & x inTARSKIR2 C) implies A =XBOOLE-0R4 B /\\SUBSET-1K9\<^bsub>(E)\<^esub> C"
sorry

mtheorem subset_1_th_7:
" for E be setHIDDENM2 holds  for A be SubsetSUBSET-1M2-of E holds  for B be SubsetSUBSET-1M2-of E holds  for C be SubsetSUBSET-1M2-of E holds ( for x be ElementSUBSET-1M1-of E holds x inTARSKIR2 A iff x inTARSKIR2 B &  not x inTARSKIR2 C) implies A =XBOOLE-0R4 B \\SUBSET-1K7\<^bsub>(E)\<^esub> C"
sorry

mtheorem subset_1_th_8:
" for E be setHIDDENM2 holds  for A be SubsetSUBSET-1M2-of E holds  for B be SubsetSUBSET-1M2-of E holds  for C be SubsetSUBSET-1M2-of E holds ( for x be ElementSUBSET-1M1-of E holds x inTARSKIR2 A iff  not (x inTARSKIR2 B iff x inTARSKIR2 C)) implies A =XBOOLE-0R4 B \\+\\SUBSET-1K5\<^bsub>(E)\<^esub> C"
sorry

mtheorem subset_1_th_9:
" for E be setHIDDENM2 holds [#]SUBSET-1K2 E =XBOOLE-0R4 ({}SUBSET-1K1 E)`SUBSET-1K3\<^bsub>(E)\<^esub>"
   sorry

mtheorem subset_1_th_10:
" for E be setHIDDENM2 holds  for A be SubsetSUBSET-1M2-of E holds A \\/SUBSET-1K4\<^bsub>(E)\<^esub> A `SUBSET-1K3\<^bsub>(E)\<^esub> =XBOOLE-0R4 [#]SUBSET-1K2 E"
sorry

mtheorem subset_1_th_11:
" for E be setHIDDENM2 holds  for A be SubsetSUBSET-1M2-of E holds A \\/SUBSET-1K4\<^bsub>(E)\<^esub> [#]SUBSET-1K2 E =XBOOLE-0R4 [#]SUBSET-1K2 E"
sorry

mtheorem subset_1_th_12:
" for E be setHIDDENM2 holds  for A be SubsetSUBSET-1M2-of E holds  for B be SubsetSUBSET-1M2-of E holds A c=TARSKIR1 B iff B `SUBSET-1K3\<^bsub>(E)\<^esub> c=TARSKIR1 A `SUBSET-1K3\<^bsub>(E)\<^esub>"
sorry

mtheorem subset_1_th_13:
" for E be setHIDDENM2 holds  for A be SubsetSUBSET-1M2-of E holds  for B be SubsetSUBSET-1M2-of E holds A \\SUBSET-1K7\<^bsub>(E)\<^esub> B =XBOOLE-0R4 A /\\SUBSET-1K9\<^bsub>(E)\<^esub> B `SUBSET-1K3\<^bsub>(E)\<^esub>"
sorry

mtheorem subset_1_th_14:
" for E be setHIDDENM2 holds  for A be SubsetSUBSET-1M2-of E holds  for B be SubsetSUBSET-1M2-of E holds (A \\SUBSET-1K7\<^bsub>(E)\<^esub> B)`SUBSET-1K3\<^bsub>(E)\<^esub> =XBOOLE-0R4 A `SUBSET-1K3\<^bsub>(E)\<^esub> \\/SUBSET-1K4\<^bsub>(E)\<^esub> B"
sorry

mtheorem subset_1_th_15:
" for E be setHIDDENM2 holds  for A be SubsetSUBSET-1M2-of E holds  for B be SubsetSUBSET-1M2-of E holds (A \\+\\SUBSET-1K5\<^bsub>(E)\<^esub> B)`SUBSET-1K3\<^bsub>(E)\<^esub> =XBOOLE-0R4 A /\\SUBSET-1K9\<^bsub>(E)\<^esub> B \\/SUBSET-1K4\<^bsub>(E)\<^esub> A `SUBSET-1K3\<^bsub>(E)\<^esub> /\\SUBSET-1K9\<^bsub>(E)\<^esub> B `SUBSET-1K3\<^bsub>(E)\<^esub>"
sorry

mtheorem subset_1_th_16:
" for E be setHIDDENM2 holds  for A be SubsetSUBSET-1M2-of E holds  for B be SubsetSUBSET-1M2-of E holds A c=TARSKIR1 B `SUBSET-1K3\<^bsub>(E)\<^esub> implies B c=TARSKIR1 A `SUBSET-1K3\<^bsub>(E)\<^esub>"
sorry

mtheorem subset_1_th_17:
" for E be setHIDDENM2 holds  for A be SubsetSUBSET-1M2-of E holds  for B be SubsetSUBSET-1M2-of E holds A `SUBSET-1K3\<^bsub>(E)\<^esub> c=TARSKIR1 B implies B `SUBSET-1K3\<^bsub>(E)\<^esub> c=TARSKIR1 A"
sorry

mtheorem subset_1_th_18:
" for E be setHIDDENM2 holds  for A be SubsetSUBSET-1M2-of E holds A c=TARSKIR1 A `SUBSET-1K3\<^bsub>(E)\<^esub> iff A =XBOOLE-0R4 {}SUBSET-1K1 E"
  using xboole_1_th_38 sorry

mtheorem subset_1_th_19:
" for E be setHIDDENM2 holds  for A be SubsetSUBSET-1M2-of E holds A `SUBSET-1K3\<^bsub>(E)\<^esub> c=TARSKIR1 A iff A =XBOOLE-0R4 [#]SUBSET-1K2 E"
sorry

mtheorem subset_1_th_20:
" for E be setHIDDENM2 holds  for X be setHIDDENM2 holds  for A be SubsetSUBSET-1M2-of E holds X c=TARSKIR1 A & X c=TARSKIR1 A `SUBSET-1K3\<^bsub>(E)\<^esub> implies X =XBOOLE-0R4 {}XBOOLE-0K1"
  using xboole_1_th_67 xboole_1_th_79 sorry

mtheorem subset_1_th_21:
" for E be setHIDDENM2 holds  for A be SubsetSUBSET-1M2-of E holds  for B be SubsetSUBSET-1M2-of E holds (A \\/SUBSET-1K4\<^bsub>(E)\<^esub> B)`SUBSET-1K3\<^bsub>(E)\<^esub> c=TARSKIR1 A `SUBSET-1K3\<^bsub>(E)\<^esub>"
  using subset_1_th_12 xboole_1_th_7 sorry

mtheorem subset_1_th_22:
" for E be setHIDDENM2 holds  for A be SubsetSUBSET-1M2-of E holds  for B be SubsetSUBSET-1M2-of E holds A `SUBSET-1K3\<^bsub>(E)\<^esub> c=TARSKIR1 (A /\\SUBSET-1K9\<^bsub>(E)\<^esub> B)`SUBSET-1K3\<^bsub>(E)\<^esub>"
  using subset_1_th_12 xboole_1_th_17 sorry

mtheorem subset_1_th_23:
" for E be setHIDDENM2 holds  for A be SubsetSUBSET-1M2-of E holds  for B be SubsetSUBSET-1M2-of E holds A missesXBOOLE-0R1 B iff A c=TARSKIR1 B `SUBSET-1K3\<^bsub>(E)\<^esub>"
sorry

mtheorem subset_1_th_24:
" for E be setHIDDENM2 holds  for A be SubsetSUBSET-1M2-of E holds  for B be SubsetSUBSET-1M2-of E holds A missesXBOOLE-0R1 B `SUBSET-1K3\<^bsub>(E)\<^esub> iff A c=TARSKIR1 B"
sorry

mtheorem subset_1_th_25:
" for E be setHIDDENM2 holds  for A be SubsetSUBSET-1M2-of E holds  for B be SubsetSUBSET-1M2-of E holds A missesXBOOLE-0R1 B & A `SUBSET-1K3\<^bsub>(E)\<^esub> missesXBOOLE-0R1 B `SUBSET-1K3\<^bsub>(E)\<^esub> implies A =XBOOLE-0R4 B `SUBSET-1K3\<^bsub>(E)\<^esub>"
sorry

mtheorem subset_1_th_26:
" for E be setHIDDENM2 holds  for A be SubsetSUBSET-1M2-of E holds  for B be SubsetSUBSET-1M2-of E holds  for C be SubsetSUBSET-1M2-of E holds A c=TARSKIR1 B & C missesXBOOLE-0R1 B implies A c=TARSKIR1 C `SUBSET-1K3\<^bsub>(E)\<^esub>"
sorry

mtheorem subset_1_th_27:
" for E be setHIDDENM2 holds  for A be SubsetSUBSET-1M2-of E holds  for B be SubsetSUBSET-1M2-of E holds ( for a be ElementSUBSET-1M1-of A holds a inTARSKIR2 B) implies A c=TARSKIR1 B"
sorry

mtheorem subset_1_th_28:
" for E be setHIDDENM2 holds  for A be SubsetSUBSET-1M2-of E holds ( for x be ElementSUBSET-1M1-of E holds x inTARSKIR2 A) implies E =XBOOLE-0R4 A"
sorry

mtheorem subset_1_th_29:
" for E be setHIDDENM2 holds E <>HIDDENR2 {}XBOOLE-0K1 implies ( for B be SubsetSUBSET-1M2-of E holds  for x be ElementSUBSET-1M1-of E holds  not x inTARSKIR2 B implies x inTARSKIR2 B `SUBSET-1K3\<^bsub>(E)\<^esub>)"
sorry

mtheorem subset_1_th_30:
" for E be setHIDDENM2 holds  for A be SubsetSUBSET-1M2-of E holds  for B be SubsetSUBSET-1M2-of E holds ( for x be ElementSUBSET-1M1-of E holds x inTARSKIR2 A iff  not x inTARSKIR2 B) implies A =XBOOLE-0R4 B `SUBSET-1K3\<^bsub>(E)\<^esub>"
sorry

mtheorem subset_1_th_31:
" for E be setHIDDENM2 holds  for A be SubsetSUBSET-1M2-of E holds  for B be SubsetSUBSET-1M2-of E holds ( for x be ElementSUBSET-1M1-of E holds  not x inTARSKIR2 A iff x inTARSKIR2 B) implies A =XBOOLE-0R4 B `SUBSET-1K3\<^bsub>(E)\<^esub>"
sorry

mtheorem subset_1_th_32:
" for E be setHIDDENM2 holds  for A be SubsetSUBSET-1M2-of E holds  for B be SubsetSUBSET-1M2-of E holds ( for x be ElementSUBSET-1M1-of E holds  not (x inTARSKIR2 A iff x inTARSKIR2 B)) implies A =XBOOLE-0R4 B `SUBSET-1K3\<^bsub>(E)\<^esub>"
sorry

reserve x1, x2, x3, x4, x5, x6, x7, x8 for "ElementSUBSET-1M1-of X"
mtheorem subset_1_th_33:
" for X be setHIDDENM2 holds  for x1 be ElementSUBSET-1M1-of X holds X <>HIDDENR2 {}XBOOLE-0K1 implies {TARSKIK1 x1} be SubsetSUBSET-1M2-of X"
sorry

mtheorem subset_1_th_34:
" for X be setHIDDENM2 holds  for x1 be ElementSUBSET-1M1-of X holds  for x2 be ElementSUBSET-1M1-of X holds X <>HIDDENR2 {}XBOOLE-0K1 implies {TARSKIK2 x1,x2 } be SubsetSUBSET-1M2-of X"
sorry

mtheorem subset_1_th_35:
" for X be setHIDDENM2 holds  for x1 be ElementSUBSET-1M1-of X holds  for x2 be ElementSUBSET-1M1-of X holds  for x3 be ElementSUBSET-1M1-of X holds X <>HIDDENR2 {}XBOOLE-0K1 implies {ENUMSET1K1 x1,x2,x3 } be SubsetSUBSET-1M2-of X"
sorry

mtheorem subset_1_th_36:
" for X be setHIDDENM2 holds  for x1 be ElementSUBSET-1M1-of X holds  for x2 be ElementSUBSET-1M1-of X holds  for x3 be ElementSUBSET-1M1-of X holds  for x4 be ElementSUBSET-1M1-of X holds X <>HIDDENR2 {}XBOOLE-0K1 implies {ENUMSET1K2 x1,x2,x3,x4 } be SubsetSUBSET-1M2-of X"
sorry

mtheorem subset_1_th_37:
" for X be setHIDDENM2 holds  for x1 be ElementSUBSET-1M1-of X holds  for x2 be ElementSUBSET-1M1-of X holds  for x3 be ElementSUBSET-1M1-of X holds  for x4 be ElementSUBSET-1M1-of X holds  for x5 be ElementSUBSET-1M1-of X holds X <>HIDDENR2 {}XBOOLE-0K1 implies {ENUMSET1K3 x1,x2,x3,x4,x5 } be SubsetSUBSET-1M2-of X"
sorry

mtheorem subset_1_th_38:
" for X be setHIDDENM2 holds  for x1 be ElementSUBSET-1M1-of X holds  for x2 be ElementSUBSET-1M1-of X holds  for x3 be ElementSUBSET-1M1-of X holds  for x4 be ElementSUBSET-1M1-of X holds  for x5 be ElementSUBSET-1M1-of X holds  for x6 be ElementSUBSET-1M1-of X holds X <>HIDDENR2 {}XBOOLE-0K1 implies {ENUMSET1K4 x1,x2,x3,x4,x5,x6 } be SubsetSUBSET-1M2-of X"
sorry

mtheorem subset_1_th_39:
" for X be setHIDDENM2 holds  for x1 be ElementSUBSET-1M1-of X holds  for x2 be ElementSUBSET-1M1-of X holds  for x3 be ElementSUBSET-1M1-of X holds  for x4 be ElementSUBSET-1M1-of X holds  for x5 be ElementSUBSET-1M1-of X holds  for x6 be ElementSUBSET-1M1-of X holds  for x7 be ElementSUBSET-1M1-of X holds X <>HIDDENR2 {}XBOOLE-0K1 implies {ENUMSET1K5 x1,x2,x3,x4,x5,x6,x7 } be SubsetSUBSET-1M2-of X"
sorry

mtheorem subset_1_th_40:
" for X be setHIDDENM2 holds  for x1 be ElementSUBSET-1M1-of X holds  for x2 be ElementSUBSET-1M1-of X holds  for x3 be ElementSUBSET-1M1-of X holds  for x4 be ElementSUBSET-1M1-of X holds  for x5 be ElementSUBSET-1M1-of X holds  for x6 be ElementSUBSET-1M1-of X holds  for x7 be ElementSUBSET-1M1-of X holds  for x8 be ElementSUBSET-1M1-of X holds X <>HIDDENR2 {}XBOOLE-0K1 implies {ENUMSET1K6 x1,x2,x3,x4,x5,x6,x7,x8 } be SubsetSUBSET-1M2-of X"
sorry

mtheorem subset_1_th_41:
" for X be setHIDDENM2 holds  for x be setHIDDENM2 holds x inTARSKIR2 X implies {TARSKIK1 x} be SubsetSUBSET-1M2-of X"
sorry

theorem subset_1_sch_1:
  fixes Af0 Pp1 
  assumes
[ty]: "Af0 be setHIDDENM2"
  shows " ex X be SubsetSUBSET-1M2-of Af0 st  for x be setHIDDENM2 holds x inTARSKIR2 X iff x inTARSKIR2 Af0 & Pp1(x)"
sorry

theorem subset_1_sch_2:
  fixes Xf0 X1f0 X2f0 Pp1 
  assumes
[ty]: "Xf0 be setHIDDENM2" and
  [ty]: "X1f0 be SubsetSUBSET-1M2-of Xf0" and
  [ty]: "X2f0 be SubsetSUBSET-1M2-of Xf0" and
   A1: " for y be ElementSUBSET-1M1-of Xf0 holds y inTARSKIR2 X1f0 iff Pp1(y)" and
   A2: " for y be ElementSUBSET-1M1-of Xf0 holds y inTARSKIR2 X2f0 iff Pp1(y)"
  shows "X1f0 =XBOOLE-0R4 X2f0"
sorry

abbreviation(input) SUBSET_1R1(" _ missesSUBSET-1R1  _ " [50,50]50) where
  "X missesSUBSET-1R1 Y \<equiv> X missesXBOOLE-0R1 Y"

mtheorem SUBSET_1R1_irreflexivity:
" for Y be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  not Y missesSUBSET-1R1 Y"
   sorry

abbreviation(input) SUBSET_1R2(" _ meetsSUBSET-1R2  _ " [50,50]50) where
  "X meetsSUBSET-1R2 Y \<equiv> X missesXBOOLE-0R1 Y"

mtheorem SUBSET_1R2_reflexivity:
" for Y be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds Y meetsSUBSET-1R2 Y"
   sorry

(*\$CD*)
(*begin*)
mlemma subset_1_lm_2:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds ( for x be objectHIDDENM1 holds x inHIDDENR3 X implies x inHIDDENR3 Y) implies X be SubsetSUBSET-1M2-of Y"
sorry

mlemma subset_1_lm_3:
" for E be setHIDDENM2 holds  for A be SubsetSUBSET-1M2-of E holds  for x be objectHIDDENM1 holds x inHIDDENR3 A implies x be ElementSUBSET-1M1-of E"
sorry

theorem subset_1_sch_3:
  fixes Af0 Pp1 
  assumes
[ty]: "Af0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
  shows " ex B be SubsetSUBSET-1M2-of Af0 st  for x be ElementSUBSET-1M1-of Af0 holds x inTARSKIR2 B iff Pp1(x)"
sorry

theorem subset_1_sch_4:
  fixes Af0 F1f0 F2f0 Pp1 
  assumes
[ty]: "Af0 be setHIDDENM2" and
  [ty]: "F1f0 be SubsetSUBSET-1M2-of Af0" and
  [ty]: "F2f0 be SubsetSUBSET-1M2-of Af0" and
   A1: " for X be ElementSUBSET-1M1-of Af0 holds X inTARSKIR2 F1f0 iff Pp1(X)" and
   A2: " for X be ElementSUBSET-1M1-of Af0 holds X inTARSKIR2 F2f0 iff Pp1(X)"
  shows "F1f0 =XBOOLE-0R4 F2f0"
sorry

mtheorem subset_1_th_42:
" for E be setHIDDENM2 holds  for A be SubsetSUBSET-1M2-of E holds  for B be SubsetSUBSET-1M2-of E holds A `SUBSET-1K3\<^bsub>(E)\<^esub> =XBOOLE-0R4 B `SUBSET-1K3\<^bsub>(E)\<^esub> implies A =XBOOLE-0R4 B"
sorry

mtheorem subset_1_cl_16:
  mlet "X be emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster note-that emptyXBOOLE-0V1 for SubsetSUBSET-1M2-of X"
proof
(*coherence*)
  show " for it be SubsetSUBSET-1M2-of X holds it be emptyXBOOLE-0V1"
sorry
qed "sorry"

mdef subset_1_def_6 ("properSUBSET-1V1\<^bsub>'( _ ')\<^esub>" [0]70 ) where
  mlet "E be setHIDDENM2"
"attr properSUBSET-1V1\<^bsub>(E)\<^esub> for SubsetSUBSET-1M2-of E means
  (\<lambda>A. A <>HIDDENR2 E)"..

mtheorem subset_1_cl_17:
  mlet "E be setHIDDENM2"
"cluster [#]SUBSET-1K2 E as-term-is  non properSUBSET-1V1\<^bsub>(E)\<^esub>"
proof
(*coherence*)
  show "[#]SUBSET-1K2 E be  non properSUBSET-1V1\<^bsub>(E)\<^esub>"
     sorry
qed "sorry"

mtheorem subset_1_cl_18:
  mlet "E be setHIDDENM2"
"cluster  non properSUBSET-1V1\<^bsub>(E)\<^esub> for SubsetSUBSET-1M2-of E"
proof
(*existence*)
  show " ex it be SubsetSUBSET-1M2-of E st it be  non properSUBSET-1V1\<^bsub>(E)\<^esub>"
sorry
qed "sorry"

mtheorem subset_1_cl_19:
  mlet "E be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster  non properSUBSET-1V1\<^bsub>(E)\<^esub> also-is  non emptyXBOOLE-0V1 for SubsetSUBSET-1M2-of E"
proof
(*coherence*)
  show " for it be SubsetSUBSET-1M2-of E holds it be  non properSUBSET-1V1\<^bsub>(E)\<^esub> implies it be  non emptyXBOOLE-0V1"
     sorry
qed "sorry"

mtheorem subset_1_cl_20:
  mlet "E be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster emptyXBOOLE-0V1 also-is properSUBSET-1V1\<^bsub>(E)\<^esub> for SubsetSUBSET-1M2-of E"
proof
(*coherence*)
  show " for it be SubsetSUBSET-1M2-of E holds it be emptyXBOOLE-0V1 implies it be properSUBSET-1V1\<^bsub>(E)\<^esub>"
     sorry
qed "sorry"

mtheorem subset_1_cl_21:
  mlet "E be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster properSUBSET-1V1\<^bsub>(E)\<^esub> for SubsetSUBSET-1M2-of E"
proof
(*existence*)
  show " ex it be SubsetSUBSET-1M2-of E st it be properSUBSET-1V1\<^bsub>(E)\<^esub>"
sorry
qed "sorry"

mtheorem subset_1_cl_22:
  mlet "E be emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster note-that  non properSUBSET-1V1\<^bsub>(E)\<^esub> for SubsetSUBSET-1M2-of E"
proof
(*coherence*)
  show " for it be SubsetSUBSET-1M2-of E holds it be  non properSUBSET-1V1\<^bsub>(E)\<^esub>"
     sorry
qed "sorry"

mtheorem subset_1_th_43:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for A be setHIDDENM2 holds  for z be setHIDDENM2 holds z inTARSKIR2 A & A c=TARSKIR1 [:ZFMISC-1K2 X,Y :] implies ( ex x be ElementSUBSET-1M1-of X st  ex y be ElementSUBSET-1M1-of Y st z =HIDDENR1 [TARSKIK4 x,y ])"
sorry

mtheorem subset_1_th_44:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for A be  non emptyXBOOLE-0V1\<bar>SubsetSUBSET-1M2-of X holds  for B be  non emptyXBOOLE-0V1\<bar>SubsetSUBSET-1M2-of X holds A c<XBOOLE-0R2 B implies ( ex p be ElementSUBSET-1M1-of X st p inTARSKIR2 B & A c=TARSKIR1 B \\SUBSET-1K7\<^bsub>(X)\<^esub> {TARSKIK1 p})"
sorry

abbreviation(input) SUBSET_1V2("trivialSUBSET-1V2" 70) where
  "trivialSUBSET-1V2 \<equiv> trivialZFMISC-1V1"

mtheorem subset_1_def_7:
  mlet "X be setHIDDENM2"
"redefine attr trivialSUBSET-1V2 for setHIDDENM2 means
  (\<lambda>X.  for x be ElementSUBSET-1M1-of X holds  for y be ElementSUBSET-1M1-of X holds x =XBOOLE-0R4 y)"
proof
(*compatibility*)
  show " for X be setHIDDENM2 holds X be trivialSUBSET-1V2 iff ( for x be ElementSUBSET-1M1-of X holds  for y be ElementSUBSET-1M1-of X holds x =XBOOLE-0R4 y)"
sorry
qed "sorry"

mtheorem subset_1_cl_23:
  mlet "X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster  non emptyXBOOLE-0V1\<bar>trivialSUBSET-1V2 for SubsetSUBSET-1M2-of X"
proof
(*existence*)
  show " ex it be SubsetSUBSET-1M2-of X st it be  non emptyXBOOLE-0V1\<bar>trivialSUBSET-1V2"
sorry
qed "sorry"

mtheorem subset_1_cl_24:
  mlet "X be trivialSUBSET-1V2\<bar>setHIDDENM2"
"cluster note-that trivialSUBSET-1V2 for SubsetSUBSET-1M2-of X"
proof
(*coherence*)
  show " for it be SubsetSUBSET-1M2-of X holds it be trivialSUBSET-1V2"
sorry
qed "sorry"

mtheorem subset_1_cl_25:
  mlet "X be  non trivialSUBSET-1V2\<bar>setHIDDENM2"
"cluster  non trivialSUBSET-1V2 for SubsetSUBSET-1M2-of X"
proof
(*existence*)
  show " ex it be SubsetSUBSET-1M2-of X st it be  non trivialSUBSET-1V2"
sorry
qed "sorry"

mtheorem subset_1_th_45:
" for D be setHIDDENM2 holds  for A be SubsetSUBSET-1M2-of D holds A be  non trivialSUBSET-1V2 implies ( ex d1 be ElementSUBSET-1M1-of D st  ex d2 be ElementSUBSET-1M1-of D st (d1 inTARSKIR2 A & d2 inTARSKIR2 A) & d1 <>HIDDENR2 d2)"
sorry

mtheorem subset_1_th_46:
" for X be trivialSUBSET-1V2\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  ex x be ElementSUBSET-1M1-of X st X =XBOOLE-0R4 {TARSKIK1 x}"
sorry

mtheorem subset_1_th_47:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for A be  non emptyXBOOLE-0V1\<bar>SubsetSUBSET-1M2-of X holds A be trivialSUBSET-1V2 implies ( ex x be ElementSUBSET-1M1-of X st A =XBOOLE-0R4 {TARSKIK1 x})"
sorry

mtheorem subset_1_th_48:
" for X be  non trivialSUBSET-1V2\<bar>setHIDDENM2 holds  for x be ElementSUBSET-1M1-of X holds  ex y be objectHIDDENM1 st y inHIDDENR3 X & x <>HIDDENR2 y"
sorry

reserve x for "objectHIDDENM1"
mdef subset_1_def_8 ("InSUBSET-1K10'( _ , _ ')" [0,0]164 ) where
  mlet "x be objectHIDDENM1", "X be setHIDDENM2"
"assume x inHIDDENR3 X func InSUBSET-1K10(x,X) \<rightarrow> ElementSUBSET-1M1-of X equals
  x"
proof-
  (*coherence*)
    show "x inHIDDENR3 X implies x be ElementSUBSET-1M1-of X"
sorry
qed "sorry"

mtheorem subset_1_reduce_1:
  mlet "X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "x be ElementSUBSET-1M1-of X"
"reduce InSUBSET-1K10(x,X) to x"
proof
(*reducibility*)
  show "InSUBSET-1K10(x,X) =HIDDENR1 x"
sorry
qed "sorry"

mtheorem subset_1_th_49:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for x be objectHIDDENM1 holds x inHIDDENR3 X /\\XBOOLE-0K3 Y implies InSUBSET-1K10(x,X) =XBOOLE-0R4 InSUBSET-1K10(x,Y)"
sorry

mtheorem subset_1_th_50:
" for X be  non trivialSUBSET-1V2\<bar>setHIDDENM2 holds  for p be setHIDDENM2 holds  ex q be ElementSUBSET-1M1-of X st q <>HIDDENR2 p"
sorry

mtheorem subset_1_th_51:
" for T be  non trivialSUBSET-1V2\<bar>setHIDDENM2 holds  for X be  non trivialSUBSET-1V2\<bar>SubsetSUBSET-1M2-of T holds  for p be setHIDDENM2 holds  ex q be ElementSUBSET-1M1-of T st q inTARSKIR2 X & q <>HIDDENR2 p"
sorry

theorem subset_1_sch_5:
  fixes Af0 af0 Ff1 
  assumes
[ty]: "Af0 be setHIDDENM2" and
  [ty]: "af0 be ElementSUBSET-1M1-of Af0" and
  [ty_func]: "\<And> x1. x1 be objectHIDDENM1 \<Longrightarrow> Ff1(x1) be setHIDDENM2"
  shows "unionTARSKIK3 ({Ff1(j) where j be ElementSUBSET-1M1-of Af0 : j inTARSKIR2 {TARSKIK1 af0} }) =XBOOLE-0R4 Ff1(af0)"
sorry

theorem subset_1_sch_6:
  fixes Af0 af0 bf0 Ff1 
  assumes
[ty]: "Af0 be setHIDDENM2" and
  [ty]: "af0 be ElementSUBSET-1M1-of Af0" and
  [ty]: "bf0 be ElementSUBSET-1M1-of Af0" and
  [ty_func]: "\<And> x1. x1 be objectHIDDENM1 \<Longrightarrow> Ff1(x1) be setHIDDENM2"
  shows "unionTARSKIK3 ({Ff1(j) where j be ElementSUBSET-1M1-of Af0 : j inTARSKIR2 {TARSKIK2 af0,bf0 } }) =XBOOLE-0R4 Ff1(af0) \\/XBOOLE-0K2 Ff1(bf0)"
sorry

end
