theory relat_1
  imports xtuple_0 subset_1
begin
(*begin*)
reserve A, X, X1, X2, Y, Y1, Y2 for "setHIDDENM2"
reserve a, b, c, d, x, y, z for "objectHIDDENM1"
mdef relat_1_def_1 ("Relation-likeRELAT-1V1" 70 ) where
"attr Relation-likeRELAT-1V1 for setHIDDENM2 means
  (\<lambda>IT.  for x be objectHIDDENM1 holds x inHIDDENR3 IT implies ( ex y be objectHIDDENM1 st  ex z be objectHIDDENM1 st x =HIDDENR1 [TARSKIK4 y,z ]))"..

mtheorem relat_1_cl_1:
"cluster emptyXBOOLE-0V1 also-is Relation-likeRELAT-1V1 for setHIDDENM2"
proof
(*coherence*)
  show " for it be setHIDDENM2 holds it be emptyXBOOLE-0V1 implies it be Relation-likeRELAT-1V1"
     sorry
qed "sorry"

syntax RELAT_1M1 :: "Ty" ("RelationRELAT-1M1" 70)
translations "RelationRELAT-1M1" \<rightharpoonup> "Relation-likeRELAT-1V1\<bar>setHIDDENM2"

reserve P, P1, P2, Q, R, S for "RelationRELAT-1M1"
mtheorem relat_1_cl_2:
  mlet "R be RelationRELAT-1M1"
"cluster note-that Relation-likeRELAT-1V1 for SubsetSUBSET-1M2-of R"
proof
(*coherence*)
  show " for it be SubsetSUBSET-1M2-of R holds it be Relation-likeRELAT-1V1"
    using relat_1_def_1 sorry
qed "sorry"

theorem relat_1_sch_1:
  fixes Af0 Bf0 Pp2 
  assumes
[ty]: "Af0 be setHIDDENM2" and
  [ty]: "Bf0 be setHIDDENM2"
  shows " ex R be RelationRELAT-1M1 st  for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds [TARSKIK4 x,y ] inHIDDENR3 R iff (x inHIDDENR3 Af0 & y inHIDDENR3 Bf0) & Pp2(x,y)"
sorry

abbreviation(input) RELAT_1R1(" _ =RELAT-1R1  _ " [50,50]50) where
  "P =RELAT-1R1 R \<equiv> P =HIDDENR1 R"

mtheorem relat_1_def_2:
  mlet "P be RelationRELAT-1M1", "R be RelationRELAT-1M1"
"redefine pred P =RELAT-1R1 R means
   for a be objectHIDDENM1 holds  for b be objectHIDDENM1 holds [TARSKIK4 a,b ] inHIDDENR3 P iff [TARSKIK4 a,b ] inHIDDENR3 R"
proof
(*compatibility*)
  show "P =RELAT-1R1 R iff ( for a be objectHIDDENM1 holds  for b be objectHIDDENM1 holds [TARSKIK4 a,b ] inHIDDENR3 P iff [TARSKIK4 a,b ] inHIDDENR3 R)"
sorry
qed "sorry"

mtheorem relat_1_cl_3:
  mlet "P be RelationRELAT-1M1", "X be setHIDDENM2"
"cluster P /\\XBOOLE-0K3 X as-term-is Relation-likeRELAT-1V1"
proof
(*coherence*)
  show "P /\\XBOOLE-0K3 X be Relation-likeRELAT-1V1"
sorry
qed "sorry"

mtheorem relat_1_cl_4:
  mlet "P be RelationRELAT-1M1", "X be setHIDDENM2"
"cluster P \\SUBSET-1K6 X as-term-is Relation-likeRELAT-1V1"
proof
(*coherence*)
  show "P \\SUBSET-1K6 X be Relation-likeRELAT-1V1"
     sorry
qed "sorry"

mtheorem relat_1_cl_5:
  mlet "P be RelationRELAT-1M1", "R be RelationRELAT-1M1"
"cluster P \\/XBOOLE-0K2 R as-term-is Relation-likeRELAT-1V1"
proof
(*coherence*)
  show "P \\/XBOOLE-0K2 R be Relation-likeRELAT-1V1"
sorry
qed "sorry"

mtheorem relat_1_cl_6:
  mlet "R be RelationRELAT-1M1", "S be RelationRELAT-1M1"
"cluster R \\+\\XBOOLE-0K5 S as-term-is Relation-likeRELAT-1V1"
proof
(*coherence*)
  show "R \\+\\XBOOLE-0K5 S be Relation-likeRELAT-1V1"
     sorry
qed "sorry"

mtheorem relat_1_cl_7:
  mlet "a be objectHIDDENM1", "b be objectHIDDENM1"
"cluster {TARSKIK1 [TARSKIK4 a,b ] } as-term-is Relation-likeRELAT-1V1"
proof
(*coherence*)
  show "{TARSKIK1 [TARSKIK4 a,b ] } be Relation-likeRELAT-1V1"
sorry
qed "sorry"

mtheorem relat_1_cl_8:
  mlet "a be setHIDDENM2", "b be setHIDDENM2"
"cluster [:ZFMISC-1K2 a,b :] as-term-is Relation-likeRELAT-1V1"
proof
(*coherence*)
  show "[:ZFMISC-1K2 a,b :] be Relation-likeRELAT-1V1"
sorry
qed "sorry"

mtheorem relat_1_cl_9:
  mlet "a be objectHIDDENM1", "b be objectHIDDENM1", "c be objectHIDDENM1", "d be objectHIDDENM1"
"cluster {TARSKIK2 [TARSKIK4 a,b ],[TARSKIK4 c,d ] } as-term-is Relation-likeRELAT-1V1"
proof
(*coherence*)
  show "{TARSKIK2 [TARSKIK4 a,b ],[TARSKIK4 c,d ] } be Relation-likeRELAT-1V1"
sorry
qed "sorry"

abbreviation(input) RELAT_1R2(" _ c=RELAT-1R2  _ " [50,50]50) where
  "P c=RELAT-1R2 A \<equiv> P c=TARSKIR1 A"

mtheorem relat_1_def_3:
  mlet "P be RelationRELAT-1M1", "A be setHIDDENM2"
"redefine pred P c=RELAT-1R2 A means
   for a be objectHIDDENM1 holds  for b be objectHIDDENM1 holds [TARSKIK4 a,b ] inHIDDENR3 P implies [TARSKIK4 a,b ] inHIDDENR3 A"
proof
(*compatibility*)
  show "P c=RELAT-1R2 A iff ( for a be objectHIDDENM1 holds  for b be objectHIDDENM1 holds [TARSKIK4 a,b ] inHIDDENR3 P implies [TARSKIK4 a,b ] inHIDDENR3 A)"
sorry
qed "sorry"

abbreviation(input) RELAT_1K1("domRELAT-1K1  _ " [228]228) where
  "domRELAT-1K1 R \<equiv> proj1XTUPLE-0K12 R"

abbreviation(input) RELAT_1K2("rngRELAT-1K2  _ " [228]228) where
  "rngRELAT-1K2 R \<equiv> proj2XTUPLE-0K13 R"

(*\$CT 6*)
mtheorem relat_1_th_7:
" for R be RelationRELAT-1M1 holds R c=RELAT-1R2 [:ZFMISC-1K2 domRELAT-1K1 R,rngRELAT-1K2 R :]"
sorry

mtheorem relat_1_th_8:
" for R be RelationRELAT-1M1 holds R /\\XBOOLE-0K3 ([:ZFMISC-1K2 domRELAT-1K1 R,rngRELAT-1K2 R :]) =RELAT-1R1 R"
  using relat_1_th_7 xboole_1_th_28 sorry

mtheorem relat_1_th_9:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds domRELAT-1K1 {TARSKIK1 [TARSKIK4 x,y ] } =XBOOLE-0R4 {TARSKIK1 x} & rngRELAT-1K2 {TARSKIK1 [TARSKIK4 x,y ] } =XBOOLE-0R4 {TARSKIK1 y}"
sorry

mtheorem relat_1_th_10:
" for a be objectHIDDENM1 holds  for b be objectHIDDENM1 holds  for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds domRELAT-1K1 {TARSKIK2 [TARSKIK4 a,b ],[TARSKIK4 x,y ] } =XBOOLE-0R4 {TARSKIK2 a,x } & rngRELAT-1K2 {TARSKIK2 [TARSKIK4 a,b ],[TARSKIK4 x,y ] } =XBOOLE-0R4 {TARSKIK2 b,y }"
sorry

mtheorem relat_1_th_11:
" for P be RelationRELAT-1M1 holds  for R be RelationRELAT-1M1 holds P c=RELAT-1R2 R implies domRELAT-1K1 P c=TARSKIR1 domRELAT-1K1 R & rngRELAT-1K2 P c=TARSKIR1 rngRELAT-1K2 R"
  using xtuple_0_th_8 xtuple_0_th_9 sorry

mtheorem relat_1_th_12:
" for P be RelationRELAT-1M1 holds  for R be RelationRELAT-1M1 holds rngRELAT-1K2 (P \\/XBOOLE-0K2 R) =XBOOLE-0R4 rngRELAT-1K2 P \\/XBOOLE-0K2 rngRELAT-1K2 R"
  using xtuple_0_th_27 sorry

mtheorem relat_1_th_13:
" for P be RelationRELAT-1M1 holds  for R be RelationRELAT-1M1 holds rngRELAT-1K2 (P /\\XBOOLE-0K3 R) c=TARSKIR1 rngRELAT-1K2 P /\\XBOOLE-0K3 rngRELAT-1K2 R"
  using xtuple_0_th_28 sorry

mtheorem relat_1_th_14:
" for P be RelationRELAT-1M1 holds  for R be RelationRELAT-1M1 holds rngRELAT-1K2 P \\SUBSET-1K6 rngRELAT-1K2 R c=TARSKIR1 rngRELAT-1K2 (P \\SUBSET-1K6 R)"
  using xtuple_0_th_29 sorry

(*\$CD 2*)
mdef relat_1_def_6 ("fieldRELAT-1K3  _ " [228]228 ) where
  mlet "R be RelationRELAT-1M1"
"func fieldRELAT-1K3 R \<rightarrow> setHIDDENM2 equals
  domRELAT-1K1 R \\/XBOOLE-0K2 rngRELAT-1K2 R"
proof-
  (*coherence*)
    show "domRELAT-1K1 R \\/XBOOLE-0K2 rngRELAT-1K2 R be setHIDDENM2"
       sorry
qed "sorry"

mtheorem relat_1_th_15:
" for a be objectHIDDENM1 holds  for b be objectHIDDENM1 holds  for R be RelationRELAT-1M1 holds [TARSKIK4 a,b ] inHIDDENR3 R implies a inHIDDENR3 fieldRELAT-1K3 R & b inHIDDENR3 fieldRELAT-1K3 R"
sorry

mtheorem relat_1_th_16:
" for P be RelationRELAT-1M1 holds  for R be RelationRELAT-1M1 holds P c=RELAT-1R2 R implies fieldRELAT-1K3 P c=TARSKIR1 fieldRELAT-1K3 R"
sorry

mtheorem relat_1_th_17:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds fieldRELAT-1K3 {TARSKIK1 [TARSKIK4 x,y ] } =XBOOLE-0R4 {TARSKIK2 x,y }"
sorry

mtheorem relat_1_th_18:
" for P be RelationRELAT-1M1 holds  for R be RelationRELAT-1M1 holds fieldRELAT-1K3 (P \\/XBOOLE-0K2 R) =XBOOLE-0R4 fieldRELAT-1K3 P \\/XBOOLE-0K2 fieldRELAT-1K3 R"
sorry

mtheorem relat_1_th_19:
" for P be RelationRELAT-1M1 holds  for R be RelationRELAT-1M1 holds fieldRELAT-1K3 (P /\\XBOOLE-0K3 R) c=TARSKIR1 fieldRELAT-1K3 P /\\XBOOLE-0K3 fieldRELAT-1K3 R"
sorry

mdef relat_1_def_7 (" _ ~RELAT-1K4" [228]228 ) where
  mlet "R be RelationRELAT-1M1"
"func R ~RELAT-1K4 \<rightarrow> RelationRELAT-1M1 means
  \<lambda>it.  for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds [TARSKIK4 x,y ] inHIDDENR3 it iff [TARSKIK4 y,x ] inHIDDENR3 R"
proof-
  (*existence*)
    show " ex it be RelationRELAT-1M1 st  for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds [TARSKIK4 x,y ] inHIDDENR3 it iff [TARSKIK4 y,x ] inHIDDENR3 R"
sorry
  (*uniqueness*)
    show " for it1 be RelationRELAT-1M1 holds  for it2 be RelationRELAT-1M1 holds ( for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds [TARSKIK4 x,y ] inHIDDENR3 it1 iff [TARSKIK4 y,x ] inHIDDENR3 R) & ( for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds [TARSKIK4 x,y ] inHIDDENR3 it2 iff [TARSKIK4 y,x ] inHIDDENR3 R) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mtheorem RELAT_1K4_involutiveness:
" for R be RelationRELAT-1M1 holds (R ~RELAT-1K4)~RELAT-1K4 =HIDDENR1 R"
sorry

mtheorem relat_1_th_20:
" for R be RelationRELAT-1M1 holds rngRELAT-1K2 R =XBOOLE-0R4 domRELAT-1K1 (R ~RELAT-1K4) & domRELAT-1K1 R =XBOOLE-0R4 rngRELAT-1K2 (R ~RELAT-1K4)"
sorry

mtheorem relat_1_th_21:
" for R be RelationRELAT-1M1 holds fieldRELAT-1K3 R =XBOOLE-0R4 fieldRELAT-1K3 (R ~RELAT-1K4)"
sorry

mtheorem relat_1_th_22:
" for P be RelationRELAT-1M1 holds  for R be RelationRELAT-1M1 holds (P /\\XBOOLE-0K3 R)~RELAT-1K4 =RELAT-1R1 P ~RELAT-1K4 /\\XBOOLE-0K3 R ~RELAT-1K4"
sorry

mtheorem relat_1_th_23:
" for P be RelationRELAT-1M1 holds  for R be RelationRELAT-1M1 holds (P \\/XBOOLE-0K2 R)~RELAT-1K4 =RELAT-1R1 P ~RELAT-1K4 \\/XBOOLE-0K2 R ~RELAT-1K4"
sorry

mtheorem relat_1_th_24:
" for P be RelationRELAT-1M1 holds  for R be RelationRELAT-1M1 holds (P \\SUBSET-1K6 R)~RELAT-1K4 =RELAT-1R1 P ~RELAT-1K4 \\SUBSET-1K6 R ~RELAT-1K4"
sorry

mdef relat_1_def_8 (" _ '(#')RELAT-1K5  _ " [164,164]164 ) where
  mlet "P be setHIDDENM2", "R be setHIDDENM2"
"func P (#)RELAT-1K5 R \<rightarrow> RelationRELAT-1M1 means
  \<lambda>it.  for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds [TARSKIK4 x,y ] inHIDDENR3 it iff ( ex z be objectHIDDENM1 st [TARSKIK4 x,z ] inHIDDENR3 P & [TARSKIK4 z,y ] inHIDDENR3 R)"
proof-
  (*existence*)
    show " ex it be RelationRELAT-1M1 st  for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds [TARSKIK4 x,y ] inHIDDENR3 it iff ( ex z be objectHIDDENM1 st [TARSKIK4 x,z ] inHIDDENR3 P & [TARSKIK4 z,y ] inHIDDENR3 R)"
sorry
  (*uniqueness*)
    show " for it1 be RelationRELAT-1M1 holds  for it2 be RelationRELAT-1M1 holds ( for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds [TARSKIK4 x,y ] inHIDDENR3 it1 iff ( ex z be objectHIDDENM1 st [TARSKIK4 x,z ] inHIDDENR3 P & [TARSKIK4 z,y ] inHIDDENR3 R)) & ( for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds [TARSKIK4 x,y ] inHIDDENR3 it2 iff ( ex z be objectHIDDENM1 st [TARSKIK4 x,z ] inHIDDENR3 P & [TARSKIK4 z,y ] inHIDDENR3 R)) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

abbreviation(input) RELAT_1K6(" _ *RELAT-1K6  _ " [164,164]164) where
  "P *RELAT-1K6 R \<equiv> P (#)RELAT-1K5 R"

mtheorem relat_1_th_25:
" for P be RelationRELAT-1M1 holds  for R be RelationRELAT-1M1 holds domRELAT-1K1 (P *RELAT-1K6 R) c=TARSKIR1 domRELAT-1K1 P"
sorry

mtheorem relat_1_th_26:
" for P be RelationRELAT-1M1 holds  for R be RelationRELAT-1M1 holds rngRELAT-1K2 (P *RELAT-1K6 R) c=TARSKIR1 rngRELAT-1K2 R"
sorry

mtheorem relat_1_th_27:
" for P be RelationRELAT-1M1 holds  for R be RelationRELAT-1M1 holds rngRELAT-1K2 R c=TARSKIR1 domRELAT-1K1 P implies domRELAT-1K1 (R *RELAT-1K6 P) =XBOOLE-0R4 domRELAT-1K1 R"
sorry

mtheorem relat_1_th_28:
" for P be RelationRELAT-1M1 holds  for R be RelationRELAT-1M1 holds domRELAT-1K1 P c=TARSKIR1 rngRELAT-1K2 R implies rngRELAT-1K2 (R *RELAT-1K6 P) =XBOOLE-0R4 rngRELAT-1K2 P"
sorry

mtheorem relat_1_th_29:
" for P be RelationRELAT-1M1 holds  for Q be RelationRELAT-1M1 holds  for R be RelationRELAT-1M1 holds P c=RELAT-1R2 R implies Q *RELAT-1K6 P c=RELAT-1R2 Q *RELAT-1K6 R"
sorry

mtheorem relat_1_th_30:
" for P be RelationRELAT-1M1 holds  for Q be RelationRELAT-1M1 holds  for R be RelationRELAT-1M1 holds P c=RELAT-1R2 Q implies P *RELAT-1K6 R c=RELAT-1R2 Q *RELAT-1K6 R"
sorry

mtheorem relat_1_th_31:
" for P be RelationRELAT-1M1 holds  for Q be RelationRELAT-1M1 holds  for R be RelationRELAT-1M1 holds  for S be RelationRELAT-1M1 holds P c=RELAT-1R2 R & Q c=RELAT-1R2 S implies P *RELAT-1K6 Q c=RELAT-1R2 R *RELAT-1K6 S"
sorry

mtheorem relat_1_th_32:
" for P be RelationRELAT-1M1 holds  for Q be RelationRELAT-1M1 holds  for R be RelationRELAT-1M1 holds P *RELAT-1K6 (R \\/XBOOLE-0K2 Q) =RELAT-1R1 P *RELAT-1K6 R \\/XBOOLE-0K2 P *RELAT-1K6 Q"
sorry

mtheorem relat_1_th_33:
" for P be RelationRELAT-1M1 holds  for Q be RelationRELAT-1M1 holds  for R be RelationRELAT-1M1 holds P *RELAT-1K6 (R /\\XBOOLE-0K3 Q) c=RELAT-1R2 (P *RELAT-1K6 R)/\\XBOOLE-0K3 (P *RELAT-1K6 Q)"
sorry

mtheorem relat_1_th_34:
" for P be RelationRELAT-1M1 holds  for Q be RelationRELAT-1M1 holds  for R be RelationRELAT-1M1 holds P *RELAT-1K6 R \\SUBSET-1K6 P *RELAT-1K6 Q c=RELAT-1R2 P *RELAT-1K6 (R \\SUBSET-1K6 Q)"
sorry

mtheorem relat_1_th_35:
" for P be RelationRELAT-1M1 holds  for R be RelationRELAT-1M1 holds (P *RELAT-1K6 R)~RELAT-1K4 =RELAT-1R1 R ~RELAT-1K4 *RELAT-1K6 P ~RELAT-1K4"
sorry

mtheorem relat_1_th_36:
" for P be RelationRELAT-1M1 holds  for Q be RelationRELAT-1M1 holds  for R be RelationRELAT-1M1 holds (P *RELAT-1K6 R)*RELAT-1K6 Q =RELAT-1R1 P *RELAT-1K6 (R *RELAT-1K6 Q)"
sorry

mtheorem relat_1_cl_10:
"cluster  non emptyXBOOLE-0V1 for RelationRELAT-1M1"
proof
(*existence*)
  show " ex it be RelationRELAT-1M1 st it be  non emptyXBOOLE-0V1"
sorry
qed "sorry"

mtheorem relat_1_cl_11:
  mlet "f be  non emptyXBOOLE-0V1\<bar>RelationRELAT-1M1"
"cluster domRELAT-1K1 f as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "domRELAT-1K1 f be  non emptyXBOOLE-0V1"
sorry
qed "sorry"

mtheorem relat_1_cl_12:
  mlet "f be  non emptyXBOOLE-0V1\<bar>RelationRELAT-1M1"
"cluster rngRELAT-1K2 f as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "rngRELAT-1K2 f be  non emptyXBOOLE-0V1"
sorry
qed "sorry"

mtheorem relat_1_th_37:
" for R be RelationRELAT-1M1 holds ( for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  not [TARSKIK4 x,y ] inHIDDENR3 R) implies R =RELAT-1R1 {}XBOOLE-0K1"
   sorry

mtheorem relat_1_th_38:
"domRELAT-1K1 ({}XBOOLE-0K1) =RELAT-1R1 {}XBOOLE-0K1 & rngRELAT-1K2 ({}XBOOLE-0K1) =RELAT-1R1 {}XBOOLE-0K1"
   sorry

mtheorem relat_1_th_39:
" for R be RelationRELAT-1M1 holds {}XBOOLE-0K1 *RELAT-1K6 R =RELAT-1R1 {}XBOOLE-0K1 & R *RELAT-1K6 {}XBOOLE-0K1 =RELAT-1R1 {}XBOOLE-0K1"
sorry

mtheorem relat_1_cl_13:
  mlet "X be emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster domRELAT-1K1 X as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "domRELAT-1K1 X be emptyXBOOLE-0V1"
     sorry
qed "sorry"

mtheorem relat_1_cl_14:
  mlet "X be emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster rngRELAT-1K2 X as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "rngRELAT-1K2 X be emptyXBOOLE-0V1"
     sorry
qed "sorry"

mtheorem relat_1_cl_15:
  mlet "X be emptyXBOOLE-0V1\<bar>setHIDDENM2", "R be RelationRELAT-1M1"
"cluster X *RELAT-1K6 R as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "X *RELAT-1K6 R be emptyXBOOLE-0V1"
    using relat_1_th_39 sorry
qed "sorry"

mtheorem relat_1_cl_16:
  mlet "X be emptyXBOOLE-0V1\<bar>setHIDDENM2", "R be RelationRELAT-1M1"
"cluster R *RELAT-1K6 X as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "R *RELAT-1K6 X be emptyXBOOLE-0V1"
    using relat_1_th_39 sorry
qed "sorry"

mtheorem relat_1_th_40:
"fieldRELAT-1K3 ({}XBOOLE-0K1) =XBOOLE-0R4 {}XBOOLE-0K1"
   sorry

mtheorem relat_1_th_41:
" for R be RelationRELAT-1M1 holds domRELAT-1K1 R =XBOOLE-0R4 {}XBOOLE-0K1 or rngRELAT-1K2 R =XBOOLE-0R4 {}XBOOLE-0K1 implies R =RELAT-1R1 {}XBOOLE-0K1"
   sorry

mtheorem relat_1_th_42:
" for R be RelationRELAT-1M1 holds domRELAT-1K1 R =XBOOLE-0R4 {}XBOOLE-0K1 iff rngRELAT-1K2 R =XBOOLE-0R4 {}XBOOLE-0K1"
  using relat_1_th_38 relat_1_th_41 sorry

mtheorem relat_1_cl_17:
  mlet "X be emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster X ~RELAT-1K4 as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "X ~RELAT-1K4 be emptyXBOOLE-0V1"
sorry
qed "sorry"

mtheorem relat_1_th_43:
"({}XBOOLE-0K1)~RELAT-1K4 =RELAT-1R1 {}XBOOLE-0K1"
   sorry

mtheorem relat_1_th_44:
" for P be RelationRELAT-1M1 holds  for R be RelationRELAT-1M1 holds rngRELAT-1K2 R missesXBOOLE-0R1 domRELAT-1K1 P implies R *RELAT-1K6 P =RELAT-1R1 {}XBOOLE-0K1"
sorry

mdef relat_1_def_9 ("non-emptyRELAT-1V2" 70 ) where
"attr non-emptyRELAT-1V2 for RelationRELAT-1M1 means
  (\<lambda>R.  not {}XBOOLE-0K1 inTARSKIR2 rngRELAT-1K2 R)"..

mtheorem relat_1_cl_18:
"cluster non-emptyRELAT-1V2 for RelationRELAT-1M1"
proof
(*existence*)
  show " ex it be RelationRELAT-1M1 st it be non-emptyRELAT-1V2"
sorry
qed "sorry"

mtheorem relat_1_cl_19:
  mlet "R be RelationRELAT-1M1", "S be non-emptyRELAT-1V2\<bar>RelationRELAT-1M1"
"cluster R *RELAT-1K6 S as-term-is non-emptyRELAT-1V2"
proof
(*coherence*)
  show "R *RELAT-1K6 S be non-emptyRELAT-1V2"
sorry
qed "sorry"

mdef relat_1_def_10 ("idRELAT-1K7  _ " [228]228 ) where
  mlet "X be setHIDDENM2"
"func idRELAT-1K7 X \<rightarrow> RelationRELAT-1M1 means
  \<lambda>it.  for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds [TARSKIK4 x,y ] inHIDDENR3 it iff x inHIDDENR3 X & x =HIDDENR1 y"
proof-
  (*existence*)
    show " ex it be RelationRELAT-1M1 st  for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds [TARSKIK4 x,y ] inHIDDENR3 it iff x inHIDDENR3 X & x =HIDDENR1 y"
sorry
  (*uniqueness*)
    show " for it1 be RelationRELAT-1M1 holds  for it2 be RelationRELAT-1M1 holds ( for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds [TARSKIK4 x,y ] inHIDDENR3 it1 iff x inHIDDENR3 X & x =HIDDENR1 y) & ( for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds [TARSKIK4 x,y ] inHIDDENR3 it2 iff x inHIDDENR3 X & x =HIDDENR1 y) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mtheorem relat_1_reduce_1:
  mlet "X be setHIDDENM2"
"reduce domRELAT-1K1 (idRELAT-1K7 X) to X"
proof
(*reducibility*)
  show "domRELAT-1K1 (idRELAT-1K7 X) =HIDDENR1 X"
sorry
qed "sorry"

mtheorem relat_1_reduce_2:
  mlet "X be setHIDDENM2"
"reduce rngRELAT-1K2 (idRELAT-1K7 X) to X"
proof
(*reducibility*)
  show "rngRELAT-1K2 (idRELAT-1K7 X) =HIDDENR1 X"
sorry
qed "sorry"

mtheorem relat_1_th_45:
" for X be setHIDDENM2 holds domRELAT-1K1 (idRELAT-1K7 X) =XBOOLE-0R4 X & rngRELAT-1K2 (idRELAT-1K7 X) =XBOOLE-0R4 X"
   sorry

mtheorem relat_1_reduce_3:
  mlet "X be setHIDDENM2"
"reduce (idRELAT-1K7 X)~RELAT-1K4 to idRELAT-1K7 X"
proof
(*reducibility*)
  show "(idRELAT-1K7 X)~RELAT-1K4 =HIDDENR1 idRELAT-1K7 X"
sorry
qed "sorry"

mtheorem relat_1_th_46:
" for X be setHIDDENM2 holds (idRELAT-1K7 X)~RELAT-1K4 =RELAT-1R1 idRELAT-1K7 X"
   sorry

mtheorem relat_1_th_47:
" for X be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds ( for x be objectHIDDENM1 holds x inHIDDENR3 X implies [TARSKIK4 x,x ] inHIDDENR3 R) implies idRELAT-1K7 X c=RELAT-1R2 R"
sorry

mtheorem relat_1_th_48:
" for X be setHIDDENM2 holds  for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for R be RelationRELAT-1M1 holds [TARSKIK4 x,y ] inHIDDENR3 idRELAT-1K7 X *RELAT-1K6 R iff x inHIDDENR3 X & [TARSKIK4 x,y ] inHIDDENR3 R"
sorry

mtheorem relat_1_th_49:
" for Y be setHIDDENM2 holds  for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for R be RelationRELAT-1M1 holds [TARSKIK4 x,y ] inHIDDENR3 R *RELAT-1K6 idRELAT-1K7 Y iff y inHIDDENR3 Y & [TARSKIK4 x,y ] inHIDDENR3 R"
sorry

mtheorem relat_1_th_50:
" for X be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds R *RELAT-1K6 idRELAT-1K7 X c=RELAT-1R2 R & idRELAT-1K7 X *RELAT-1K6 R c=RELAT-1R2 R"
sorry

mtheorem relat_1_th_51:
" for X be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds domRELAT-1K1 R c=TARSKIR1 X implies idRELAT-1K7 X *RELAT-1K6 R =RELAT-1R1 R"
sorry

mtheorem relat_1_th_52:
" for R be RelationRELAT-1M1 holds idRELAT-1K7 (domRELAT-1K1 R) *RELAT-1K6 R =RELAT-1R1 R"
  using relat_1_th_51 sorry

mtheorem relat_1_th_53:
" for Y be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds rngRELAT-1K2 R c=TARSKIR1 Y implies R *RELAT-1K6 idRELAT-1K7 Y =RELAT-1R1 R"
sorry

mtheorem relat_1_th_54:
" for R be RelationRELAT-1M1 holds R *RELAT-1K6 idRELAT-1K7 (rngRELAT-1K2 R) =RELAT-1R1 R"
  using relat_1_th_53 sorry

mtheorem relat_1_th_55:
"idRELAT-1K7 ({}XBOOLE-0K1) =RELAT-1R1 {}XBOOLE-0K1"
sorry

mtheorem relat_1_th_56:
" for X be setHIDDENM2 holds  for P1 be RelationRELAT-1M1 holds  for P2 be RelationRELAT-1M1 holds  for R be RelationRELAT-1M1 holds (rngRELAT-1K2 P2 c=TARSKIR1 X & P2 *RELAT-1K6 R =RELAT-1R1 idRELAT-1K7 (domRELAT-1K1 P1)) & R *RELAT-1K6 P1 =RELAT-1R1 idRELAT-1K7 X implies P1 =RELAT-1R1 P2"
sorry

mdef relat_1_def_11 (" _ |RELAT-1K8  _ " [200,200]200 ) where
  mlet "R be RelationRELAT-1M1", "X be setHIDDENM2"
"func R |RELAT-1K8 X \<rightarrow> RelationRELAT-1M1 means
  \<lambda>it.  for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds [TARSKIK4 x,y ] inHIDDENR3 it iff x inHIDDENR3 X & [TARSKIK4 x,y ] inHIDDENR3 R"
proof-
  (*existence*)
    show " ex it be RelationRELAT-1M1 st  for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds [TARSKIK4 x,y ] inHIDDENR3 it iff x inHIDDENR3 X & [TARSKIK4 x,y ] inHIDDENR3 R"
sorry
  (*uniqueness*)
    show " for it1 be RelationRELAT-1M1 holds  for it2 be RelationRELAT-1M1 holds ( for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds [TARSKIK4 x,y ] inHIDDENR3 it1 iff x inHIDDENR3 X & [TARSKIK4 x,y ] inHIDDENR3 R) & ( for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds [TARSKIK4 x,y ] inHIDDENR3 it2 iff x inHIDDENR3 X & [TARSKIK4 x,y ] inHIDDENR3 R) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mtheorem relat_1_cl_20:
  mlet "R be RelationRELAT-1M1", "X be emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster R |RELAT-1K8 X as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "R |RELAT-1K8 X be emptyXBOOLE-0V1"
sorry
qed "sorry"

mtheorem relat_1_th_57:
" for X be setHIDDENM2 holds  for x be objectHIDDENM1 holds  for R be RelationRELAT-1M1 holds x inHIDDENR3 domRELAT-1K1 (R |RELAT-1K8 X) iff x inHIDDENR3 X & x inHIDDENR3 domRELAT-1K1 R"
sorry

mtheorem relat_1_th_58:
" for X be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds domRELAT-1K1 (R |RELAT-1K8 X) c=TARSKIR1 X"
  using relat_1_th_57 sorry

mtheorem relat_1_th_59:
" for X be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds R |RELAT-1K8 X c=RELAT-1R2 R"
  using relat_1_def_11 sorry

mtheorem relat_1_th_60:
" for X be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds domRELAT-1K1 (R |RELAT-1K8 X) c=TARSKIR1 domRELAT-1K1 R"
  using relat_1_th_57 sorry

mtheorem relat_1_th_61:
" for X be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds domRELAT-1K1 (R |RELAT-1K8 X) =XBOOLE-0R4 domRELAT-1K1 R /\\XBOOLE-0K3 X"
sorry

mtheorem relat_1_th_62:
" for X be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds X c=TARSKIR1 domRELAT-1K1 R implies domRELAT-1K1 (R |RELAT-1K8 X) =XBOOLE-0R4 X"
sorry

mtheorem relat_1_th_63:
" for X be setHIDDENM2 holds  for P be RelationRELAT-1M1 holds  for R be RelationRELAT-1M1 holds R |RELAT-1K8 X *RELAT-1K6 P c=RELAT-1R2 R *RELAT-1K6 P"
  using relat_1_th_30 relat_1_th_59 sorry

mtheorem relat_1_th_64:
" for X be setHIDDENM2 holds  for P be RelationRELAT-1M1 holds  for R be RelationRELAT-1M1 holds P *RELAT-1K6 R |RELAT-1K8 X c=RELAT-1R2 P *RELAT-1K6 R"
  using relat_1_th_29 relat_1_th_59 sorry

mtheorem relat_1_th_65:
" for X be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds R |RELAT-1K8 X =RELAT-1R1 idRELAT-1K7 X *RELAT-1K6 R"
sorry

mtheorem relat_1_th_66:
" for X be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds R |RELAT-1K8 X =RELAT-1R1 {}XBOOLE-0K1 iff domRELAT-1K1 R missesXBOOLE-0R1 X"
sorry

mtheorem relat_1_th_67:
" for X be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds R |RELAT-1K8 X =RELAT-1R1 R /\\XBOOLE-0K3 ([:ZFMISC-1K2 X,rngRELAT-1K2 R :])"
sorry

mtheorem relat_1_th_68:
" for X be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds domRELAT-1K1 R c=TARSKIR1 X implies R |RELAT-1K8 X =RELAT-1R1 R"
sorry

mtheorem relat_1_reduce_4:
  mlet "R be RelationRELAT-1M1"
"reduce R |RELAT-1K8 domRELAT-1K1 R to R"
proof
(*reducibility*)
  show "R |RELAT-1K8 domRELAT-1K1 R =HIDDENR1 R"
    using relat_1_th_68 sorry
qed "sorry"

mtheorem relat_1_th_69:
" for R be RelationRELAT-1M1 holds R |RELAT-1K8 domRELAT-1K1 R =RELAT-1R1 R"
   sorry

mtheorem relat_1_th_70:
" for X be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds rngRELAT-1K2 (R |RELAT-1K8 X) c=TARSKIR1 rngRELAT-1K2 R"
  using relat_1_th_59 xtuple_0_th_9 sorry

mtheorem relat_1_th_71:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds (R |RELAT-1K8 X)|RELAT-1K8 Y =RELAT-1R1 R |RELAT-1K8 (X /\\XBOOLE-0K3 Y)"
sorry

mtheorem relat_1_reduce_5:
  mlet "R be RelationRELAT-1M1", "X be setHIDDENM2"
"reduce (R |RELAT-1K8 X)|RELAT-1K8 X to R |RELAT-1K8 X"
proof
(*reducibility*)
  show "(R |RELAT-1K8 X)|RELAT-1K8 X =HIDDENR1 R |RELAT-1K8 X"
sorry
qed "sorry"

mtheorem relat_1_th_72:
" for X be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds (R |RELAT-1K8 X)|RELAT-1K8 X =RELAT-1R1 R |RELAT-1K8 X"
   sorry

mtheorem relat_1_th_73:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds X c=TARSKIR1 Y implies (R |RELAT-1K8 X)|RELAT-1K8 Y =RELAT-1R1 R |RELAT-1K8 X"
sorry

mtheorem relat_1_th_74:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds Y c=TARSKIR1 X implies (R |RELAT-1K8 X)|RELAT-1K8 Y =RELAT-1R1 R |RELAT-1K8 Y"
sorry

mtheorem relat_1_th_75:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds X c=TARSKIR1 Y implies R |RELAT-1K8 X c=RELAT-1R2 R |RELAT-1K8 Y"
sorry

mtheorem relat_1_th_76:
" for X be setHIDDENM2 holds  for P be RelationRELAT-1M1 holds  for R be RelationRELAT-1M1 holds P c=RELAT-1R2 R implies P |RELAT-1K8 X c=RELAT-1R2 R |RELAT-1K8 X"
sorry

mtheorem relat_1_th_77:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for P be RelationRELAT-1M1 holds  for R be RelationRELAT-1M1 holds P c=RELAT-1R2 R & X c=TARSKIR1 Y implies P |RELAT-1K8 X c=RELAT-1R2 R |RELAT-1K8 Y"
sorry

mtheorem relat_1_th_78:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds R |RELAT-1K8 (X \\/XBOOLE-0K2 Y) =RELAT-1R1 R |RELAT-1K8 X \\/XBOOLE-0K2 R |RELAT-1K8 Y"
sorry

mtheorem relat_1_th_79:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds R |RELAT-1K8 (X /\\XBOOLE-0K3 Y) =RELAT-1R1 R |RELAT-1K8 X /\\XBOOLE-0K3 R |RELAT-1K8 Y"
sorry

mtheorem relat_1_th_80:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds R |RELAT-1K8 (X \\SUBSET-1K6 Y) =RELAT-1R1 R |RELAT-1K8 X \\SUBSET-1K6 R |RELAT-1K8 Y"
sorry

mtheorem relat_1_cl_21:
  mlet "R be emptyXBOOLE-0V1\<bar>RelationRELAT-1M1", "X be setHIDDENM2"
"cluster R |RELAT-1K8 X as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "R |RELAT-1K8 X be emptyXBOOLE-0V1"
sorry
qed "sorry"

mtheorem relat_1_th_81:
" for R be RelationRELAT-1M1 holds R |RELAT-1K8 {}XBOOLE-0K1 =RELAT-1R1 {}XBOOLE-0K1"
   sorry

mtheorem relat_1_th_82:
" for X be setHIDDENM2 holds {}XBOOLE-0K1 |RELAT-1K8 X =RELAT-1R1 {}XBOOLE-0K1"
   sorry

mtheorem relat_1_th_83:
" for X be setHIDDENM2 holds  for P be RelationRELAT-1M1 holds  for R be RelationRELAT-1M1 holds (P *RELAT-1K6 R)|RELAT-1K8 X =RELAT-1R1 P |RELAT-1K8 X *RELAT-1K6 R"
sorry

mdef relat_1_def_12 (" _ |`RELAT-1K9  _ " [200,200]200 ) where
  mlet "Y be setHIDDENM2", "R be RelationRELAT-1M1"
"func Y |`RELAT-1K9 R \<rightarrow> RelationRELAT-1M1 means
  \<lambda>it.  for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds [TARSKIK4 x,y ] inHIDDENR3 it iff y inHIDDENR3 Y & [TARSKIK4 x,y ] inHIDDENR3 R"
proof-
  (*existence*)
    show " ex it be RelationRELAT-1M1 st  for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds [TARSKIK4 x,y ] inHIDDENR3 it iff y inHIDDENR3 Y & [TARSKIK4 x,y ] inHIDDENR3 R"
sorry
  (*uniqueness*)
    show " for it1 be RelationRELAT-1M1 holds  for it2 be RelationRELAT-1M1 holds ( for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds [TARSKIK4 x,y ] inHIDDENR3 it1 iff y inHIDDENR3 Y & [TARSKIK4 x,y ] inHIDDENR3 R) & ( for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds [TARSKIK4 x,y ] inHIDDENR3 it2 iff y inHIDDENR3 Y & [TARSKIK4 x,y ] inHIDDENR3 R) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mtheorem relat_1_cl_22:
  mlet "R be RelationRELAT-1M1", "X be emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster X |`RELAT-1K9 R as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "X |`RELAT-1K9 R be emptyXBOOLE-0V1"
sorry
qed "sorry"

mtheorem relat_1_th_84:
" for Y be setHIDDENM2 holds  for y be objectHIDDENM1 holds  for R be RelationRELAT-1M1 holds y inHIDDENR3 rngRELAT-1K2 (Y |`RELAT-1K9 R) iff y inHIDDENR3 Y & y inHIDDENR3 rngRELAT-1K2 R"
sorry

mtheorem relat_1_th_85:
" for Y be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds rngRELAT-1K2 (Y |`RELAT-1K9 R) c=TARSKIR1 Y"
  using relat_1_th_84 sorry

mtheorem relat_1_th_86:
" for Y be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds Y |`RELAT-1K9 R c=RELAT-1R2 R"
  using relat_1_def_12 sorry

mtheorem relat_1_th_87:
" for Y be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds rngRELAT-1K2 (Y |`RELAT-1K9 R) c=TARSKIR1 rngRELAT-1K2 R"
  using relat_1_th_86 xtuple_0_th_9 sorry

mtheorem relat_1_th_88:
" for Y be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds rngRELAT-1K2 (Y |`RELAT-1K9 R) =XBOOLE-0R4 rngRELAT-1K2 R /\\XBOOLE-0K3 Y"
sorry

mtheorem relat_1_th_89:
" for Y be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds Y c=TARSKIR1 rngRELAT-1K2 R implies rngRELAT-1K2 (Y |`RELAT-1K9 R) =XBOOLE-0R4 Y"
sorry

mtheorem relat_1_th_90:
" for Y be setHIDDENM2 holds  for P be RelationRELAT-1M1 holds  for R be RelationRELAT-1M1 holds Y |`RELAT-1K9 R *RELAT-1K6 P c=RELAT-1R2 R *RELAT-1K6 P"
  using relat_1_th_30 relat_1_th_86 sorry

mtheorem relat_1_th_91:
" for Y be setHIDDENM2 holds  for P be RelationRELAT-1M1 holds  for R be RelationRELAT-1M1 holds P *RELAT-1K6 Y |`RELAT-1K9 R c=RELAT-1R2 P *RELAT-1K6 R"
  using relat_1_th_29 relat_1_th_86 sorry

mtheorem relat_1_th_92:
" for Y be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds Y |`RELAT-1K9 R =RELAT-1R1 R *RELAT-1K6 idRELAT-1K7 Y"
sorry

mtheorem relat_1_th_93:
" for Y be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds Y |`RELAT-1K9 R =RELAT-1R1 R /\\XBOOLE-0K3 ([:ZFMISC-1K2 domRELAT-1K1 R,Y :])"
sorry

mtheorem relat_1_th_94:
" for Y be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds rngRELAT-1K2 R c=TARSKIR1 Y implies Y |`RELAT-1K9 R =RELAT-1R1 R"
sorry

mtheorem relat_1_reduce_6:
  mlet "R be RelationRELAT-1M1"
"reduce rngRELAT-1K2 R |`RELAT-1K9 R to R"
proof
(*reducibility*)
  show "rngRELAT-1K2 R |`RELAT-1K9 R =HIDDENR1 R"
    using relat_1_th_94 sorry
qed "sorry"

mtheorem relat_1_th_95:
" for R be RelationRELAT-1M1 holds rngRELAT-1K2 R |`RELAT-1K9 R =RELAT-1R1 R"
   sorry

mtheorem relat_1_th_96:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds Y |`RELAT-1K9 (X |`RELAT-1K9 R) =RELAT-1R1 (Y /\\XBOOLE-0K3 X)|`RELAT-1K9 R"
sorry

mtheorem relat_1_reduce_7:
  mlet "Y be setHIDDENM2", "R be RelationRELAT-1M1"
"reduce Y |`RELAT-1K9 (Y |`RELAT-1K9 R) to Y |`RELAT-1K9 R"
proof
(*reducibility*)
  show "Y |`RELAT-1K9 (Y |`RELAT-1K9 R) =HIDDENR1 Y |`RELAT-1K9 R"
sorry
qed "sorry"

mtheorem relat_1_th_97:
" for Y be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds Y |`RELAT-1K9 (Y |`RELAT-1K9 R) =RELAT-1R1 Y |`RELAT-1K9 R"
   sorry

mtheorem relat_1_th_98:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds X c=TARSKIR1 Y implies Y |`RELAT-1K9 (X |`RELAT-1K9 R) =RELAT-1R1 X |`RELAT-1K9 R"
sorry

mtheorem relat_1_th_99:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds Y c=TARSKIR1 X implies Y |`RELAT-1K9 (X |`RELAT-1K9 R) =RELAT-1R1 Y |`RELAT-1K9 R"
sorry

mtheorem relat_1_th_100:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds X c=TARSKIR1 Y implies X |`RELAT-1K9 R c=RELAT-1R2 Y |`RELAT-1K9 R"
sorry

mtheorem relat_1_th_101:
" for Y be setHIDDENM2 holds  for P1 be RelationRELAT-1M1 holds  for P2 be RelationRELAT-1M1 holds P1 c=RELAT-1R2 P2 implies Y |`RELAT-1K9 P1 c=RELAT-1R2 Y |`RELAT-1K9 P2"
sorry

mtheorem relat_1_th_102:
" for Y1 be setHIDDENM2 holds  for Y2 be setHIDDENM2 holds  for P1 be RelationRELAT-1M1 holds  for P2 be RelationRELAT-1M1 holds P1 c=RELAT-1R2 P2 & Y1 c=TARSKIR1 Y2 implies Y1 |`RELAT-1K9 P1 c=RELAT-1R2 Y2 |`RELAT-1K9 P2"
sorry

mtheorem relat_1_th_103:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds (X \\/XBOOLE-0K2 Y)|`RELAT-1K9 R =RELAT-1R1 X |`RELAT-1K9 R \\/XBOOLE-0K2 Y |`RELAT-1K9 R"
sorry

mtheorem relat_1_th_104:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds (X /\\XBOOLE-0K3 Y)|`RELAT-1K9 R =RELAT-1R1 X |`RELAT-1K9 R /\\XBOOLE-0K3 Y |`RELAT-1K9 R"
sorry

mtheorem relat_1_th_105:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds (X \\SUBSET-1K6 Y)|`RELAT-1K9 R =RELAT-1R1 X |`RELAT-1K9 R \\SUBSET-1K6 Y |`RELAT-1K9 R"
sorry

mtheorem relat_1_th_106:
" for R be RelationRELAT-1M1 holds {}XBOOLE-0K1 |`RELAT-1K9 R =RELAT-1R1 {}XBOOLE-0K1"
   sorry

mtheorem relat_1_th_107:
" for Y be setHIDDENM2 holds Y |`RELAT-1K9 {}XBOOLE-0K1 =RELAT-1R1 {}XBOOLE-0K1"
  using relat_1_def_12 sorry

mtheorem relat_1_th_108:
" for Y be setHIDDENM2 holds  for P be RelationRELAT-1M1 holds  for R be RelationRELAT-1M1 holds Y |`RELAT-1K9 (P *RELAT-1K6 R) =RELAT-1R1 P *RELAT-1K6 Y |`RELAT-1K9 R"
sorry

mtheorem relat_1_th_109:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds (Y |`RELAT-1K9 R)|RELAT-1K8 X =RELAT-1R1 Y |`RELAT-1K9 (R |RELAT-1K8 X)"
sorry

mdef relat_1_def_13 (" _ .:RELAT-1K10  _ " [200,200]200 ) where
  mlet "R be RelationRELAT-1M1", "X be setHIDDENM2"
"func R .:RELAT-1K10 X \<rightarrow> setHIDDENM2 means
  \<lambda>it.  for y be objectHIDDENM1 holds y inHIDDENR3 it iff ( ex x be objectHIDDENM1 st [TARSKIK4 x,y ] inHIDDENR3 R & x inHIDDENR3 X)"
proof-
  (*existence*)
    show " ex it be setHIDDENM2 st  for y be objectHIDDENM1 holds y inHIDDENR3 it iff ( ex x be objectHIDDENM1 st [TARSKIK4 x,y ] inHIDDENR3 R & x inHIDDENR3 X)"
sorry
  (*uniqueness*)
    show " for it1 be setHIDDENM2 holds  for it2 be setHIDDENM2 holds ( for y be objectHIDDENM1 holds y inHIDDENR3 it1 iff ( ex x be objectHIDDENM1 st [TARSKIK4 x,y ] inHIDDENR3 R & x inHIDDENR3 X)) & ( for y be objectHIDDENM1 holds y inHIDDENR3 it2 iff ( ex x be objectHIDDENM1 st [TARSKIK4 x,y ] inHIDDENR3 R & x inHIDDENR3 X)) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mtheorem relat_1_th_110:
" for X be setHIDDENM2 holds  for y be objectHIDDENM1 holds  for R be RelationRELAT-1M1 holds y inHIDDENR3 R .:RELAT-1K10 X iff ( ex x be objectHIDDENM1 st (x inHIDDENR3 domRELAT-1K1 R & [TARSKIK4 x,y ] inHIDDENR3 R) & x inHIDDENR3 X)"
sorry

mtheorem relat_1_th_111:
" for X be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds R .:RELAT-1K10 X c=TARSKIR1 rngRELAT-1K2 R"
sorry

mtheorem relat_1_th_112:
" for X be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds R .:RELAT-1K10 X =XBOOLE-0R4 R .:RELAT-1K10 (domRELAT-1K1 R /\\XBOOLE-0K3 X)"
sorry

mtheorem relat_1_th_113:
" for R be RelationRELAT-1M1 holds R .:RELAT-1K10 domRELAT-1K1 R =XBOOLE-0R4 rngRELAT-1K2 R"
sorry

mtheorem relat_1_th_114:
" for X be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds R .:RELAT-1K10 X c=TARSKIR1 R .:RELAT-1K10 domRELAT-1K1 R"
sorry

mtheorem relat_1_th_115:
" for X be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds rngRELAT-1K2 (R |RELAT-1K8 X) =XBOOLE-0R4 R .:RELAT-1K10 X"
sorry

mtheorem relat_1_cl_23:
  mlet "R be RelationRELAT-1M1", "X be emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster R .:RELAT-1K10 X as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "R .:RELAT-1K10 X be emptyXBOOLE-0V1"
sorry
qed "sorry"

mtheorem relat_1_cl_24:
  mlet "R be emptyXBOOLE-0V1\<bar>RelationRELAT-1M1", "X be setHIDDENM2"
"cluster R .:RELAT-1K10 X as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "R .:RELAT-1K10 X be emptyXBOOLE-0V1"
sorry
qed "sorry"

(*\$CT 2*)
mtheorem relat_1_th_118:
" for X be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds R .:RELAT-1K10 X =XBOOLE-0R4 {}XBOOLE-0K1 iff domRELAT-1K1 R missesXBOOLE-0R1 X"
sorry

mtheorem relat_1_th_119:
" for X be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds X <>HIDDENR2 {}XBOOLE-0K1 & X c=TARSKIR1 domRELAT-1K1 R implies R .:RELAT-1K10 X <>HIDDENR2 {}XBOOLE-0K1"
sorry

mtheorem relat_1_th_120:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds R .:RELAT-1K10 (X \\/XBOOLE-0K2 Y) =XBOOLE-0R4 R .:RELAT-1K10 X \\/XBOOLE-0K2 R .:RELAT-1K10 Y"
sorry

mtheorem relat_1_th_121:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds R .:RELAT-1K10 (X /\\XBOOLE-0K3 Y) c=TARSKIR1 R .:RELAT-1K10 X /\\XBOOLE-0K3 R .:RELAT-1K10 Y"
sorry

mtheorem relat_1_th_122:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds R .:RELAT-1K10 X \\SUBSET-1K6 R .:RELAT-1K10 Y c=TARSKIR1 R .:RELAT-1K10 (X \\SUBSET-1K6 Y)"
sorry

mtheorem relat_1_th_123:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds X c=TARSKIR1 Y implies R .:RELAT-1K10 X c=TARSKIR1 R .:RELAT-1K10 Y"
sorry

mtheorem relat_1_th_124:
" for X be setHIDDENM2 holds  for P be RelationRELAT-1M1 holds  for R be RelationRELAT-1M1 holds P c=RELAT-1R2 R implies P .:RELAT-1K10 X c=TARSKIR1 R .:RELAT-1K10 X"
sorry

mtheorem relat_1_th_125:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for P be RelationRELAT-1M1 holds  for R be RelationRELAT-1M1 holds P c=RELAT-1R2 R & X c=TARSKIR1 Y implies P .:RELAT-1K10 X c=TARSKIR1 R .:RELAT-1K10 Y"
sorry

mtheorem relat_1_th_126:
" for X be setHIDDENM2 holds  for P be RelationRELAT-1M1 holds  for R be RelationRELAT-1M1 holds (P *RELAT-1K6 R).:RELAT-1K10 X =XBOOLE-0R4 R .:RELAT-1K10 (P .:RELAT-1K10 X)"
sorry

mtheorem relat_1_th_127:
" for P be RelationRELAT-1M1 holds  for R be RelationRELAT-1M1 holds rngRELAT-1K2 (P *RELAT-1K6 R) =XBOOLE-0R4 R .:RELAT-1K10 rngRELAT-1K2 P"
sorry

mtheorem relat_1_th_128:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds (R |RELAT-1K8 X).:RELAT-1K10 Y c=TARSKIR1 R .:RELAT-1K10 Y"
  using relat_1_th_59 relat_1_th_124 sorry

mtheorem relat_1_th_129:
" for R be RelationRELAT-1M1 holds  for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X c=TARSKIR1 Y implies (R |RELAT-1K8 Y).:RELAT-1K10 X =XBOOLE-0R4 R .:RELAT-1K10 X"
sorry

mtheorem relat_1_th_130:
" for X be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds domRELAT-1K1 R /\\XBOOLE-0K3 X c=TARSKIR1 R ~RELAT-1K4 .:RELAT-1K10 (R .:RELAT-1K10 X)"
sorry

mdef relat_1_def_14 (" _ \<inverse>RELAT-1K11  _ " [228,228]228 ) where
  mlet "R be RelationRELAT-1M1", "Y be setHIDDENM2"
"func R \<inverse>RELAT-1K11 Y \<rightarrow> setHIDDENM2 means
  \<lambda>it.  for x be objectHIDDENM1 holds x inHIDDENR3 it iff ( ex y be objectHIDDENM1 st [TARSKIK4 x,y ] inHIDDENR3 R & y inHIDDENR3 Y)"
proof-
  (*existence*)
    show " ex it be setHIDDENM2 st  for x be objectHIDDENM1 holds x inHIDDENR3 it iff ( ex y be objectHIDDENM1 st [TARSKIK4 x,y ] inHIDDENR3 R & y inHIDDENR3 Y)"
sorry
  (*uniqueness*)
    show " for it1 be setHIDDENM2 holds  for it2 be setHIDDENM2 holds ( for x be objectHIDDENM1 holds x inHIDDENR3 it1 iff ( ex y be objectHIDDENM1 st [TARSKIK4 x,y ] inHIDDENR3 R & y inHIDDENR3 Y)) & ( for x be objectHIDDENM1 holds x inHIDDENR3 it2 iff ( ex y be objectHIDDENM1 st [TARSKIK4 x,y ] inHIDDENR3 R & y inHIDDENR3 Y)) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mtheorem relat_1_th_131:
" for Y be setHIDDENM2 holds  for x be objectHIDDENM1 holds  for R be RelationRELAT-1M1 holds x inHIDDENR3 R \<inverse>RELAT-1K11 Y iff ( ex y be objectHIDDENM1 st (y inHIDDENR3 rngRELAT-1K2 R & [TARSKIK4 x,y ] inHIDDENR3 R) & y inHIDDENR3 Y)"
sorry

mtheorem relat_1_th_132:
" for Y be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds R \<inverse>RELAT-1K11 Y c=TARSKIR1 domRELAT-1K1 R"
sorry

mtheorem relat_1_th_133:
" for Y be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds R \<inverse>RELAT-1K11 Y =XBOOLE-0R4 R \<inverse>RELAT-1K11 (rngRELAT-1K2 R /\\XBOOLE-0K3 Y)"
sorry

mtheorem relat_1_th_134:
" for R be RelationRELAT-1M1 holds R \<inverse>RELAT-1K11 (rngRELAT-1K2 R) =XBOOLE-0R4 domRELAT-1K1 R"
sorry

mtheorem relat_1_th_135:
" for Y be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds R \<inverse>RELAT-1K11 Y c=TARSKIR1 R \<inverse>RELAT-1K11 (rngRELAT-1K2 R)"
sorry

mtheorem relat_1_cl_25:
  mlet "R be RelationRELAT-1M1", "Y be emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster R \<inverse>RELAT-1K11 Y as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "R \<inverse>RELAT-1K11 Y be emptyXBOOLE-0V1"
sorry
qed "sorry"

mtheorem relat_1_cl_26:
  mlet "R be emptyXBOOLE-0V1\<bar>RelationRELAT-1M1", "Y be setHIDDENM2"
"cluster R \<inverse>RELAT-1K11 Y as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "R \<inverse>RELAT-1K11 Y be emptyXBOOLE-0V1"
sorry
qed "sorry"

(*\$CT 2*)
mtheorem relat_1_th_138:
" for Y be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds R \<inverse>RELAT-1K11 Y =XBOOLE-0R4 {}XBOOLE-0K1 iff rngRELAT-1K2 R missesXBOOLE-0R1 Y"
sorry

mtheorem relat_1_th_139:
" for Y be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds Y <>HIDDENR2 {}XBOOLE-0K1 & Y c=TARSKIR1 rngRELAT-1K2 R implies R \<inverse>RELAT-1K11 Y <>HIDDENR2 {}XBOOLE-0K1"
sorry

mtheorem relat_1_th_140:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds R \<inverse>RELAT-1K11 (X \\/XBOOLE-0K2 Y) =XBOOLE-0R4 R \<inverse>RELAT-1K11 X \\/XBOOLE-0K2 R \<inverse>RELAT-1K11 Y"
sorry

mtheorem relat_1_th_141:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds R \<inverse>RELAT-1K11 (X /\\XBOOLE-0K3 Y) c=TARSKIR1 R \<inverse>RELAT-1K11 X /\\XBOOLE-0K3 R \<inverse>RELAT-1K11 Y"
sorry

mtheorem relat_1_th_142:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds R \<inverse>RELAT-1K11 X \\SUBSET-1K6 R \<inverse>RELAT-1K11 Y c=TARSKIR1 R \<inverse>RELAT-1K11 (X \\SUBSET-1K6 Y)"
sorry

mtheorem relat_1_th_143:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds X c=TARSKIR1 Y implies R \<inverse>RELAT-1K11 X c=TARSKIR1 R \<inverse>RELAT-1K11 Y"
sorry

mtheorem relat_1_th_144:
" for Y be setHIDDENM2 holds  for P be RelationRELAT-1M1 holds  for R be RelationRELAT-1M1 holds P c=RELAT-1R2 R implies P \<inverse>RELAT-1K11 Y c=TARSKIR1 R \<inverse>RELAT-1K11 Y"
sorry

mtheorem relat_1_th_145:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for P be RelationRELAT-1M1 holds  for R be RelationRELAT-1M1 holds P c=RELAT-1R2 R & X c=TARSKIR1 Y implies P \<inverse>RELAT-1K11 X c=TARSKIR1 R \<inverse>RELAT-1K11 Y"
sorry

mtheorem relat_1_th_146:
" for Y be setHIDDENM2 holds  for P be RelationRELAT-1M1 holds  for R be RelationRELAT-1M1 holds (P *RELAT-1K6 R)\<inverse>RELAT-1K11 Y =XBOOLE-0R4 P \<inverse>RELAT-1K11 (R \<inverse>RELAT-1K11 Y)"
sorry

mtheorem relat_1_th_147:
" for P be RelationRELAT-1M1 holds  for R be RelationRELAT-1M1 holds domRELAT-1K1 (P *RELAT-1K6 R) =XBOOLE-0R4 P \<inverse>RELAT-1K11 (domRELAT-1K1 R)"
sorry

mtheorem relat_1_th_148:
" for Y be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds rngRELAT-1K2 R /\\XBOOLE-0K3 Y c=TARSKIR1 (R ~RELAT-1K4)\<inverse>RELAT-1K11 (R \<inverse>RELAT-1K11 Y)"
sorry

(*begin*)
mdef relat_1_def_15 ("empty-yieldingRELAT-1V3" 70 ) where
"attr empty-yieldingRELAT-1V3 for RelationRELAT-1M1 means
  (\<lambda>R. rngRELAT-1K2 R c=TARSKIR1 {TARSKIK1 {}XBOOLE-0K1 })"..

mtheorem relat_1_th_149:
" for R be RelationRELAT-1M1 holds R be empty-yieldingRELAT-1V3 iff ( for X be setHIDDENM2 holds X inTARSKIR2 rngRELAT-1K2 R implies X =XBOOLE-0R4 {}XBOOLE-0K1)"
sorry

mtheorem relat_1_th_150:
" for f be RelationRELAT-1M1 holds  for g be RelationRELAT-1M1 holds  for A be setHIDDENM2 holds  for B be setHIDDENM2 holds f |RELAT-1K8 A =RELAT-1R1 g |RELAT-1K8 A & f |RELAT-1K8 B =RELAT-1R1 g |RELAT-1K8 B implies f |RELAT-1K8 (A \\/XBOOLE-0K2 B) =RELAT-1R1 g |RELAT-1K8 (A \\/XBOOLE-0K2 B)"
sorry

mtheorem relat_1_th_151:
" for X be setHIDDENM2 holds  for f be RelationRELAT-1M1 holds  for g be RelationRELAT-1M1 holds domRELAT-1K1 g c=TARSKIR1 X & g c=RELAT-1R2 f implies g c=RELAT-1R2 f |RELAT-1K8 X"
sorry

mtheorem relat_1_th_152:
" for f be RelationRELAT-1M1 holds  for X be setHIDDENM2 holds X missesXBOOLE-0R1 domRELAT-1K1 f implies f |RELAT-1K8 X =RELAT-1R1 {}XBOOLE-0K1"
sorry

mtheorem relat_1_th_153:
" for f be RelationRELAT-1M1 holds  for g be RelationRELAT-1M1 holds  for A be setHIDDENM2 holds  for B be setHIDDENM2 holds A c=TARSKIR1 B & f |RELAT-1K8 B =RELAT-1R1 g |RELAT-1K8 B implies f |RELAT-1K8 A =RELAT-1R1 g |RELAT-1K8 A"
sorry

mtheorem relat_1_th_154:
" for R be RelationRELAT-1M1 holds  for S be RelationRELAT-1M1 holds R |RELAT-1K8 domRELAT-1K1 S =RELAT-1R1 R |RELAT-1K8 domRELAT-1K1 (S |RELAT-1K8 domRELAT-1K1 R)"
sorry

mtheorem relat_1_cl_27:
"cluster emptyXBOOLE-0V1 also-is empty-yieldingRELAT-1V3 for RelationRELAT-1M1"
proof
(*coherence*)
  show " for it be RelationRELAT-1M1 holds it be emptyXBOOLE-0V1 implies it be empty-yieldingRELAT-1V3"
sorry
qed "sorry"

mtheorem relat_1_cl_28:
  mlet "R be empty-yieldingRELAT-1V3\<bar>RelationRELAT-1M1", "X be setHIDDENM2"
"cluster R |RELAT-1K8 X as-term-is empty-yieldingRELAT-1V3"
proof
(*coherence*)
  show "R |RELAT-1K8 X be empty-yieldingRELAT-1V3"
sorry
qed "sorry"

mtheorem relat_1_th_155:
" for X be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds R |RELAT-1K8 X be  non empty-yieldingRELAT-1V3 implies R be  non empty-yieldingRELAT-1V3"
   sorry

mdef relat_1_def_16 ("ImRELAT-1K12'( _ , _ ')" [0,0]228 ) where
  mlet "R be RelationRELAT-1M1", "x be objectHIDDENM1"
"func ImRELAT-1K12(R,x) \<rightarrow> setHIDDENM2 equals
  R .:RELAT-1K10 {TARSKIK1 x}"
proof-
  (*coherence*)
    show "R .:RELAT-1K10 {TARSKIK1 x} be setHIDDENM2"
       sorry
qed "sorry"

theorem relat_1_sch_2:
  fixes Af0 Bf0 Pp2 
  assumes
[ty]: "Af0 be RelationRELAT-1M1" and
  [ty]: "Bf0 be RelationRELAT-1M1" and
   A1: " for a be objectHIDDENM1 holds  for b be objectHIDDENM1 holds [TARSKIK4 a,b ] inHIDDENR3 Af0 iff Pp2(a,b)" and
   A2: " for a be objectHIDDENM1 holds  for b be objectHIDDENM1 holds [TARSKIK4 a,b ] inHIDDENR3 Bf0 iff Pp2(a,b)"
  shows "Af0 =RELAT-1R1 Bf0"
sorry

mtheorem relat_1_th_156:
" for X be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds domRELAT-1K1 (R |RELAT-1K8 (domRELAT-1K1 R \\SUBSET-1K6 X)) =XBOOLE-0R4 domRELAT-1K1 R \\SUBSET-1K6 X"
sorry

mtheorem relat_1_th_157:
" for X be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds R |RELAT-1K8 X =RELAT-1R1 R |RELAT-1K8 (domRELAT-1K1 R /\\XBOOLE-0K3 X)"
sorry

mtheorem relat_1_th_158:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds domRELAT-1K1 ([:ZFMISC-1K2 X,Y :]) c=TARSKIR1 X"
sorry

mtheorem relat_1_th_159:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds rngRELAT-1K2 ([:ZFMISC-1K2 X,Y :]) c=TARSKIR1 Y"
sorry

mtheorem relat_1_th_160:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X <>HIDDENR2 {}XBOOLE-0K1 & Y <>HIDDENR2 {}XBOOLE-0K1 implies domRELAT-1K1 ([:ZFMISC-1K2 X,Y :]) =XBOOLE-0R4 X & rngRELAT-1K2 ([:ZFMISC-1K2 X,Y :]) =XBOOLE-0R4 Y"
sorry

mtheorem relat_1_th_161:
" for Q be RelationRELAT-1M1 holds  for R be RelationRELAT-1M1 holds domRELAT-1K1 R =XBOOLE-0R4 {}XBOOLE-0K1 & domRELAT-1K1 Q =XBOOLE-0R4 {}XBOOLE-0K1 implies R =RELAT-1R1 Q"
   sorry

mtheorem relat_1_th_162:
" for Q be RelationRELAT-1M1 holds  for R be RelationRELAT-1M1 holds rngRELAT-1K2 R =XBOOLE-0R4 {}XBOOLE-0K1 & rngRELAT-1K2 Q =XBOOLE-0R4 {}XBOOLE-0K1 implies R =RELAT-1R1 Q"
   sorry

mtheorem relat_1_th_163:
" for Q be RelationRELAT-1M1 holds  for R be RelationRELAT-1M1 holds  for S be RelationRELAT-1M1 holds domRELAT-1K1 R =XBOOLE-0R4 domRELAT-1K1 Q implies domRELAT-1K1 (S *RELAT-1K6 R) =XBOOLE-0R4 domRELAT-1K1 (S *RELAT-1K6 Q)"
sorry

mtheorem relat_1_th_164:
" for Q be RelationRELAT-1M1 holds  for R be RelationRELAT-1M1 holds  for S be RelationRELAT-1M1 holds rngRELAT-1K2 R =XBOOLE-0R4 rngRELAT-1K2 Q implies rngRELAT-1K2 (R *RELAT-1K6 S) =XBOOLE-0R4 rngRELAT-1K2 (Q *RELAT-1K6 S)"
sorry

mdef relat_1_def_17 ("CoimRELAT-1K13'( _ , _ ')" [0,0]164 ) where
  mlet "R be RelationRELAT-1M1", "x be objectHIDDENM1"
"func CoimRELAT-1K13(R,x) \<rightarrow> setHIDDENM2 equals
  R \<inverse>RELAT-1K11 {TARSKIK1 x}"
proof-
  (*coherence*)
    show "R \<inverse>RELAT-1K11 {TARSKIK1 x} be setHIDDENM2"
       sorry
qed "sorry"

mtheorem relat_1_cl_29:
  mlet "R be trivialSUBSET-1V2\<bar>RelationRELAT-1M1"
"cluster domRELAT-1K1 R as-term-is trivialSUBSET-1V2"
proof
(*coherence*)
  show "domRELAT-1K1 R be trivialSUBSET-1V2"
sorry
qed "sorry"

mtheorem relat_1_cl_30:
  mlet "R be trivialSUBSET-1V2\<bar>RelationRELAT-1M1"
"cluster rngRELAT-1K2 R as-term-is trivialSUBSET-1V2"
proof
(*coherence*)
  show "rngRELAT-1K2 R be trivialSUBSET-1V2"
sorry
qed "sorry"

mtheorem relat_1_th_165:
" for X be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds  for S be RelationRELAT-1M1 holds rngRELAT-1K2 R c=TARSKIR1 domRELAT-1K1 (S |RELAT-1K8 X) implies R *RELAT-1K6 S |RELAT-1K8 X =RELAT-1R1 R *RELAT-1K6 S"
sorry

mtheorem relat_1_th_166:
" for A be setHIDDENM2 holds  for Q be RelationRELAT-1M1 holds  for R be RelationRELAT-1M1 holds Q |RELAT-1K8 A =RELAT-1R1 R |RELAT-1K8 A implies Q .:RELAT-1K10 A =XBOOLE-0R4 R .:RELAT-1K10 A"
sorry

mdef relat_1_def_18 (" _ -definedRELAT-1V4" [70]70 ) where
  mlet "X be setHIDDENM2"
"attr X -definedRELAT-1V4 for RelationRELAT-1M1 means
  (\<lambda>R. domRELAT-1K1 R c=TARSKIR1 X)"..

mdef relat_1_def_19 (" _ -valuedRELAT-1V5" [70]70 ) where
  mlet "X be setHIDDENM2"
"attr X -valuedRELAT-1V5 for RelationRELAT-1M1 means
  (\<lambda>R. rngRELAT-1K2 R c=TARSKIR1 X)"..

mlemma relat_1_lm_1:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds {}XBOOLE-0K1 be X -definedRELAT-1V4\<bar>Y -valuedRELAT-1V5"
sorry

mtheorem relat_1_cl_31:
  mlet "X be setHIDDENM2", "Y be setHIDDENM2"
"cluster X -definedRELAT-1V4\<bar>Y -valuedRELAT-1V5 for RelationRELAT-1M1"
proof
(*existence*)
  show " ex it be RelationRELAT-1M1 st it be X -definedRELAT-1V4\<bar>Y -valuedRELAT-1V5"
sorry
qed "sorry"

mtheorem relat_1_th_167:
" for D be setHIDDENM2 holds  for R be D -valuedRELAT-1V5\<bar>RelationRELAT-1M1 holds  for y be objectHIDDENM1 holds y inHIDDENR3 rngRELAT-1K2 R implies y inHIDDENR3 D"
sorry

mtheorem relat_1_cl_32:
  mlet "X be setHIDDENM2", "A be setHIDDENM2", "R be A -valuedRELAT-1V5\<bar>RelationRELAT-1M1"
"cluster R |RELAT-1K8 X as-term-is A -valuedRELAT-1V5"
proof
(*coherence*)
  show "R |RELAT-1K8 X be A -valuedRELAT-1V5"
sorry
qed "sorry"

mtheorem relat_1_cl_33:
  mlet "X be setHIDDENM2", "A be setHIDDENM2", "R be A -definedRELAT-1V4\<bar>RelationRELAT-1M1"
"cluster R |RELAT-1K8 X as-term-is A -definedRELAT-1V4\<bar>X -definedRELAT-1V4"
proof
(*coherence*)
  show "R |RELAT-1K8 X be A -definedRELAT-1V4\<bar>X -definedRELAT-1V4"
sorry
qed "sorry"

mtheorem relat_1_cl_34:
  mlet "X be setHIDDENM2"
"cluster idRELAT-1K7 X as-term-is X -definedRELAT-1V4\<bar>X -valuedRELAT-1V5"
proof
(*coherence*)
  show "idRELAT-1K7 X be X -definedRELAT-1V4\<bar>X -valuedRELAT-1V5"
     sorry
qed "sorry"

mtheorem relat_1_cl_35:
  mlet "A be setHIDDENM2", "R be A -valuedRELAT-1V5\<bar>RelationRELAT-1M1", "S be RelationRELAT-1M1"
"cluster S *RELAT-1K6 R as-term-is A -valuedRELAT-1V5"
proof
(*coherence*)
  show "S *RELAT-1K6 R be A -valuedRELAT-1V5"
sorry
qed "sorry"

mtheorem relat_1_cl_36:
  mlet "A be setHIDDENM2", "R be A -definedRELAT-1V4\<bar>RelationRELAT-1M1", "S be RelationRELAT-1M1"
"cluster R *RELAT-1K6 S as-term-is A -definedRELAT-1V4"
proof
(*coherence*)
  show "R *RELAT-1K6 S be A -definedRELAT-1V4"
sorry
qed "sorry"

mtheorem relat_1_th_168:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for x be objectHIDDENM1 holds x inHIDDENR3 X implies ImRELAT-1K12([:ZFMISC-1K2 X,Y :],x) =XBOOLE-0R4 Y"
sorry

mtheorem relat_1_th_169:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for R be RelationRELAT-1M1 holds [TARSKIK4 x,y ] inHIDDENR3 R iff y inHIDDENR3 ImRELAT-1K12(R,x)"
sorry

mtheorem relat_1_th_170:
" for x be objectHIDDENM1 holds  for R be RelationRELAT-1M1 holds x inHIDDENR3 domRELAT-1K1 R iff ImRELAT-1K12(R,x) <>HIDDENR2 {}XBOOLE-0K1"
sorry

mtheorem relat_1_th_171:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds {}XBOOLE-0K1 be X -definedRELAT-1V4\<bar>Y -valuedRELAT-1V5"
  using relat_1_lm_1 sorry

mtheorem relat_1_cl_37:
"cluster emptyXBOOLE-0V1 also-is non-emptyRELAT-1V2 for RelationRELAT-1M1"
proof
(*coherence*)
  show " for it be RelationRELAT-1M1 holds it be emptyXBOOLE-0V1 implies it be non-emptyRELAT-1V2"
     sorry
qed "sorry"

mtheorem relat_1_cl_38:
  mlet "X be setHIDDENM2", "R be X -definedRELAT-1V4\<bar>RelationRELAT-1M1"
"cluster note-that X -definedRELAT-1V4 for SubsetSUBSET-1M2-of R"
proof
(*coherence*)
  show " for it be SubsetSUBSET-1M2-of R holds it be X -definedRELAT-1V4"
sorry
qed "sorry"

mtheorem relat_1_cl_39:
  mlet "X be setHIDDENM2", "R be X -valuedRELAT-1V5\<bar>RelationRELAT-1M1"
"cluster note-that X -valuedRELAT-1V5 for SubsetSUBSET-1M2-of R"
proof
(*coherence*)
  show " for it be SubsetSUBSET-1M2-of R holds it be X -valuedRELAT-1V5"
sorry
qed "sorry"

mtheorem relat_1_th_172:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds X missesXBOOLE-0R1 Y implies (R |RELAT-1K8 X)|RELAT-1K8 Y =RELAT-1R1 {}XBOOLE-0K1"
sorry

mtheorem relat_1_th_173:
" for x be objectHIDDENM1 holds fieldRELAT-1K3 {TARSKIK1 [TARSKIK4 x,x ] } =XBOOLE-0R4 {TARSKIK1 x}"
sorry

mtheorem relat_1_reduce_8:
  mlet "X be setHIDDENM2", "R be X -definedRELAT-1V4\<bar>RelationRELAT-1M1"
"reduce R |RELAT-1K8 X to R"
proof
(*reducibility*)
  show "R |RELAT-1K8 X =HIDDENR1 R"
sorry
qed "sorry"

mtheorem relat_1_reduce_9:
  mlet "Y be setHIDDENM2", "R be Y -valuedRELAT-1V5\<bar>RelationRELAT-1M1"
"reduce Y |`RELAT-1K9 R to R"
proof
(*reducibility*)
  show "Y |`RELAT-1K9 R =HIDDENR1 R"
sorry
qed "sorry"

mtheorem relat_1_th_174:
" for X be setHIDDENM2 holds  for R be X -definedRELAT-1V4\<bar>RelationRELAT-1M1 holds R =RELAT-1R1 R |RELAT-1K8 X"
   sorry

mtheorem relat_1_th_175:
" for X be setHIDDENM2 holds  for S be RelationRELAT-1M1 holds  for R be X -definedRELAT-1V4\<bar>RelationRELAT-1M1 holds R c=RELAT-1R2 S implies R c=RELAT-1R2 S |RELAT-1K8 X"
sorry

mtheorem relat_1_th_176:
" for A be setHIDDENM2 holds  for X be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds domRELAT-1K1 R c=TARSKIR1 X implies R \\SUBSET-1K6 R |RELAT-1K8 A =RELAT-1R1 R |RELAT-1K8 (X \\SUBSET-1K6 A)"
sorry

mtheorem relat_1_th_177:
" for A be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds domRELAT-1K1 (R \\SUBSET-1K6 R |RELAT-1K8 A) =XBOOLE-0R4 domRELAT-1K1 R \\SUBSET-1K6 A"
sorry

mtheorem relat_1_th_178:
" for A be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds domRELAT-1K1 R \\SUBSET-1K6 domRELAT-1K1 (R |RELAT-1K8 A) =XBOOLE-0R4 domRELAT-1K1 (R \\SUBSET-1K6 R |RELAT-1K8 A)"
sorry

mtheorem relat_1_th_179:
" for R be RelationRELAT-1M1 holds  for S be RelationRELAT-1M1 holds domRELAT-1K1 R missesXBOOLE-0R1 domRELAT-1K1 S implies R missesXBOOLE-0R1 S"
sorry

mtheorem relat_1_th_180:
" for R be RelationRELAT-1M1 holds  for S be RelationRELAT-1M1 holds rngRELAT-1K2 R missesXBOOLE-0R1 rngRELAT-1K2 S implies R missesXBOOLE-0R1 S"
sorry

mtheorem relat_1_th_181:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds X c=TARSKIR1 Y implies (R \\SUBSET-1K6 R |RELAT-1K8 Y)|RELAT-1K8 X =RELAT-1R1 {}XBOOLE-0K1"
sorry

mtheorem relat_1_th_182:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X c=TARSKIR1 Y implies ( for R be X -definedRELAT-1V4\<bar>RelationRELAT-1M1 holds R be Y -definedRELAT-1V4)"
sorry

mtheorem relat_1_th_183:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X c=TARSKIR1 Y implies ( for R be X -valuedRELAT-1V5\<bar>RelationRELAT-1M1 holds R be Y -valuedRELAT-1V5)"
sorry

mtheorem relat_1_th_184:
" for R be RelationRELAT-1M1 holds  for S be RelationRELAT-1M1 holds R c=RELAT-1R2 S iff R c=RELAT-1R2 S |RELAT-1K8 domRELAT-1K1 R"
sorry

mtheorem relat_1_th_185:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for R be X -definedRELAT-1V4\<bar>Y -valuedRELAT-1V5\<bar>RelationRELAT-1M1 holds R c=RELAT-1R2 [:ZFMISC-1K2 X,Y :]"
sorry

mtheorem relat_1_th_186:
" for X be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds domRELAT-1K1 (X |`RELAT-1K9 R) c=TARSKIR1 domRELAT-1K1 R"
  using relat_1_th_86 xtuple_0_th_8 sorry

mtheorem relat_1_cl_40:
  mlet "A be setHIDDENM2", "X be setHIDDENM2", "R be A -definedRELAT-1V4\<bar>RelationRELAT-1M1"
"cluster X |`RELAT-1K9 R as-term-is A -definedRELAT-1V4"
proof
(*coherence*)
  show "X |`RELAT-1K9 R be A -definedRELAT-1V4"
sorry
qed "sorry"

mtheorem relat_1_cl_41:
  mlet "X be setHIDDENM2", "A be setHIDDENM2", "R be A -valuedRELAT-1V5\<bar>RelationRELAT-1M1"
"cluster X |`RELAT-1K9 R as-term-is A -valuedRELAT-1V5\<bar>X -valuedRELAT-1V5"
proof
(*coherence*)
  show "X |`RELAT-1K9 R be A -valuedRELAT-1V5\<bar>X -valuedRELAT-1V5"
sorry
qed "sorry"

mtheorem relat_1_cl_42:
  mlet "X be emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster note-that emptyXBOOLE-0V1 for X -definedRELAT-1V4\<bar>RelationRELAT-1M1"
proof
(*coherence*)
  show " for it be X -definedRELAT-1V4\<bar>RelationRELAT-1M1 holds it be emptyXBOOLE-0V1"
sorry
qed "sorry"

mtheorem relat_1_cl_43:
  mlet "X be emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster note-that emptyXBOOLE-0V1 for X -valuedRELAT-1V5\<bar>RelationRELAT-1M1"
proof
(*coherence*)
  show " for it be X -valuedRELAT-1V5\<bar>RelationRELAT-1M1 holds it be emptyXBOOLE-0V1"
sorry
qed "sorry"

mtheorem relat_1_th_187:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for P be RelationRELAT-1M1 holds  for R be RelationRELAT-1M1 holds X missesXBOOLE-0R1 Y implies P |RELAT-1K8 X missesXBOOLE-0R1 R |RELAT-1K8 Y"
sorry

mtheorem relat_1_th_188:
" for Y be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds Y |`RELAT-1K9 R c=RELAT-1R2 R |RELAT-1K8 R \<inverse>RELAT-1K11 Y"
sorry

mtheorem relat_1_th_189:
" for f be RelationRELAT-1M1 holds  for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds domRELAT-1K1 f =XBOOLE-0R4 {TARSKIK1 x} & rngRELAT-1K2 f =XBOOLE-0R4 {TARSKIK1 y} implies f =RELAT-1R1 {TARSKIK1 [TARSKIK4 x,y ] }"
sorry

mtheorem
  mlet "X be setHIDDENM2", "Y be setHIDDENM2"
"cluster sethood of X -definedRELAT-1V4\<bar>Y -valuedRELAT-1V5\<bar>RelationRELAT-1M1"
proof
(*sethood*)
  show " ex cover be setHIDDENM2 st  for it be X -definedRELAT-1V4\<bar>Y -valuedRELAT-1V5\<bar>RelationRELAT-1M1 holds it inHIDDENR3 cover"
sorry
qed "sorry"

end
