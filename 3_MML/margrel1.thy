theory margrel1
  imports xboolean finseq_3
   "../mizar_extension/E_number"
begin
(*begin*)
reserve k for "ElementSUBSET-1M1-of NATNUMBERSK1"
reserve D for " non emptyXBOOLE-0V1\<bar>setHIDDENM2"
abbreviation(input) MARGREL1V1("with-common-domainMARGREL1V1" 70) where
  "with-common-domainMARGREL1V1 \<equiv> with-common-domainCARD-3V2"

mtheorem margrel1_def_1:
  mlet "IT be FinSequence-memberedFINSEQ-1V3\<bar>setHIDDENM2"
"redefine attr with-common-domainMARGREL1V1 for FinSequence-memberedFINSEQ-1V3\<bar>setHIDDENM2 means
  (\<lambda>IT.  for a be FinSequenceFINSEQ-1M1 holds  for b be FinSequenceFINSEQ-1M1 holds a inTARSKIR2 IT & b inTARSKIR2 IT implies lenFINSEQ-1K4 a =XBOOLE-0R4 lenFINSEQ-1K4 b)"
proof
(*compatibility*)
  show " for IT be FinSequence-memberedFINSEQ-1V3\<bar>setHIDDENM2 holds IT be with-common-domainMARGREL1V1 iff ( for a be FinSequenceFINSEQ-1M1 holds  for b be FinSequenceFINSEQ-1M1 holds a inTARSKIR2 IT & b inTARSKIR2 IT implies lenFINSEQ-1K4 a =XBOOLE-0R4 lenFINSEQ-1K4 b)"
sorry
qed "sorry"

mtheorem margrel1_cl_1:
"cluster FinSequence-memberedFINSEQ-1V3\<bar>with-common-domainCARD-3V2 for setHIDDENM2"
proof
(*existence*)
  show " ex it be setHIDDENM2 st it be FinSequence-memberedFINSEQ-1V3\<bar>with-common-domainCARD-3V2"
sorry
qed "sorry"

syntax MARGREL1M1 :: "Ty" ("relationMARGREL1M1" 70)
translations "relationMARGREL1M1" \<rightharpoonup> "FinSequence-memberedFINSEQ-1V3\<bar>with-common-domainCARD-3V2\<bar>setHIDDENM2"

reserve X for "setHIDDENM2"
reserve p, r for "relationMARGREL1M1"
reserve a, a1, a2, b for "FinSequenceFINSEQ-1M1"
mtheorem margrel1_th_1:
" for X be setHIDDENM2 holds  for p be relationMARGREL1M1 holds X c=TARSKIR1 p implies X be relationMARGREL1M1"
   sorry

mtheorem margrel1_th_2:
" for a be FinSequenceFINSEQ-1M1 holds {TARSKIK1 a} be relationMARGREL1M1"
sorry

theorem margrel1_sch_1:
  fixes Af0 Pp1 
  assumes
[ty]: "Af0 be setHIDDENM2" and
   A1: " for a be FinSequenceFINSEQ-1M1 holds  for b be FinSequenceFINSEQ-1M1 holds Pp1(a) & Pp1(b) implies lenFINSEQ-1K4 a =XBOOLE-0R4 lenFINSEQ-1K4 b"
  shows " ex r be relationMARGREL1M1 st  for a be FinSequenceFINSEQ-1M1 holds a inTARSKIR2 r iff a inTARSKIR2 Af0 & Pp1(a)"
sorry

abbreviation(input) MARGREL1R1(" _ =MARGREL1R1  _ " [50,50]50) where
  "p =MARGREL1R1 r \<equiv> p =HIDDENR1 r"

mtheorem margrel1_def_2:
  mlet "p be relationMARGREL1M1", "r be relationMARGREL1M1"
"redefine pred p =MARGREL1R1 r means
   for a be FinSequenceFINSEQ-1M1 holds a inTARSKIR2 p iff a inTARSKIR2 r"
proof
(*compatibility*)
  show "p =MARGREL1R1 r iff ( for a be FinSequenceFINSEQ-1M1 holds a inTARSKIR2 p iff a inTARSKIR2 r)"
sorry
qed "sorry"

mtheorem margrel1_cl_2:
"cluster emptyXBOOLE-0V1 also-is with-common-domainCARD-3V2 for setHIDDENM2"
proof
(*coherence*)
  show " for it be setHIDDENM2 holds it be emptyXBOOLE-0V1 implies it be with-common-domainCARD-3V2"
     sorry
qed "sorry"

mtheorem margrel1_th_3:
" for p be relationMARGREL1M1 holds ( for a be FinSequenceFINSEQ-1M1 holds  not a inTARSKIR2 p) implies p =MARGREL1R1 {}XBOOLE-0K1"
   sorry

mdef margrel1_def_3 ("the-arity-ofMARGREL1K1  _ " [120]120 ) where
  mlet "p be relationMARGREL1M1"
"assume p <>HIDDENR2 {}XBOOLE-0K1 func the-arity-ofMARGREL1K1 p \<rightarrow> ElementSUBSET-1M1-of NATNUMBERSK1 means
  \<lambda>it.  for a be FinSequenceFINSEQ-1M1 holds a inTARSKIR2 p implies it =XBOOLE-0R4 lenFINSEQ-1K4 a"
proof-
  (*existence*)
    show "p <>HIDDENR2 {}XBOOLE-0K1 implies ( ex it be ElementSUBSET-1M1-of NATNUMBERSK1 st  for a be FinSequenceFINSEQ-1M1 holds a inTARSKIR2 p implies it =XBOOLE-0R4 lenFINSEQ-1K4 a)"
sorry
  (*uniqueness*)
    show "p <>HIDDENR2 {}XBOOLE-0K1 implies ( for it1 be ElementSUBSET-1M1-of NATNUMBERSK1 holds  for it2 be ElementSUBSET-1M1-of NATNUMBERSK1 holds ( for a be FinSequenceFINSEQ-1M1 holds a inTARSKIR2 p implies it1 =XBOOLE-0R4 lenFINSEQ-1K4 a) & ( for a be FinSequenceFINSEQ-1M1 holds a inTARSKIR2 p implies it2 =XBOOLE-0R4 lenFINSEQ-1K4 a) implies it1 =HIDDENR1 it2)"
sorry
qed "sorry"

mdef margrel1_def_4 ("relation-lengthMARGREL1M2-of  _ " [70]70 ) where
  mlet "k be ElementSUBSET-1M1-of NATNUMBERSK1"
"mode relation-lengthMARGREL1M2-of k \<rightarrow> relationMARGREL1M1 means
  (\<lambda>it.  for a be FinSequenceFINSEQ-1M1 holds a inTARSKIR2 it implies lenFINSEQ-1K4 a =XBOOLE-0R4 k)"
proof-
  (*existence*)
    show " ex it be relationMARGREL1M1 st  for a be FinSequenceFINSEQ-1M1 holds a inTARSKIR2 it implies lenFINSEQ-1K4 a =XBOOLE-0R4 k"
sorry
qed "sorry"

mdef margrel1_def_5 ("relationMARGREL1M3-of  _ " [70]70 ) where
  mlet "X be setHIDDENM2"
"mode relationMARGREL1M3-of X \<rightarrow> relationMARGREL1M1 means
  (\<lambda>it.  for a be FinSequenceFINSEQ-1M1 holds a inTARSKIR2 it implies rngRELAT-1K2 a c=TARSKIR1 X)"
proof-
  (*existence*)
    show " ex it be relationMARGREL1M1 st  for a be FinSequenceFINSEQ-1M1 holds a inTARSKIR2 it implies rngRELAT-1K2 a c=TARSKIR1 X"
sorry
qed "sorry"

mtheorem margrel1_th_4:
" for X be setHIDDENM2 holds {}XBOOLE-0K1 be relationMARGREL1M3-of X"
sorry

mtheorem margrel1_th_5:
" for k be ElementSUBSET-1M1-of NATNUMBERSK1 holds {}XBOOLE-0K1 be relation-lengthMARGREL1M2-of k"
sorry

mdef margrel1_def_6 ("relationMARGREL1M4-of'( _ , _ ')" [0,0]70 ) where
  mlet "X be setHIDDENM2", "k be ElementSUBSET-1M1-of NATNUMBERSK1"
"mode relationMARGREL1M4-of(X,k) \<rightarrow> relationMARGREL1M1 means
  (\<lambda>it. it be relationMARGREL1M3-of X & it be relation-lengthMARGREL1M2-of k)"
proof-
  (*existence*)
    show " ex it be relationMARGREL1M1 st it be relationMARGREL1M3-of X & it be relation-lengthMARGREL1M2-of k"
sorry
qed "sorry"

mdef margrel1_def_7 ("relations-onMARGREL1K2  _ " [164]164 ) where
  mlet "D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
"func relations-onMARGREL1K2 D \<rightarrow> setHIDDENM2 means
  \<lambda>it.  for X be setHIDDENM2 holds X inTARSKIR2 it iff X c=TARSKIR1 D * FINSEQ-2K3 & ( for a be FinSequenceFINSEQ-1M3-of D holds  for b be FinSequenceFINSEQ-1M3-of D holds a inTARSKIR2 X & b inTARSKIR2 X implies lenFINSEQ-1K4 a =XBOOLE-0R4 lenFINSEQ-1K4 b)"
proof-
  (*existence*)
    show " ex it be setHIDDENM2 st  for X be setHIDDENM2 holds X inTARSKIR2 it iff X c=TARSKIR1 D * FINSEQ-2K3 & ( for a be FinSequenceFINSEQ-1M3-of D holds  for b be FinSequenceFINSEQ-1M3-of D holds a inTARSKIR2 X & b inTARSKIR2 X implies lenFINSEQ-1K4 a =XBOOLE-0R4 lenFINSEQ-1K4 b)"
sorry
  (*uniqueness*)
    show " for it1 be setHIDDENM2 holds  for it2 be setHIDDENM2 holds ( for X be setHIDDENM2 holds X inTARSKIR2 it1 iff X c=TARSKIR1 D * FINSEQ-2K3 & ( for a be FinSequenceFINSEQ-1M3-of D holds  for b be FinSequenceFINSEQ-1M3-of D holds a inTARSKIR2 X & b inTARSKIR2 X implies lenFINSEQ-1K4 a =XBOOLE-0R4 lenFINSEQ-1K4 b)) & ( for X be setHIDDENM2 holds X inTARSKIR2 it2 iff X c=TARSKIR1 D * FINSEQ-2K3 & ( for a be FinSequenceFINSEQ-1M3-of D holds  for b be FinSequenceFINSEQ-1M3-of D holds a inTARSKIR2 X & b inTARSKIR2 X implies lenFINSEQ-1K4 a =XBOOLE-0R4 lenFINSEQ-1K4 b)) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mtheorem margrel1_cl_3:
  mlet "D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster relations-onMARGREL1K2 D as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "relations-onMARGREL1K2 D be  non emptyXBOOLE-0V1"
sorry
qed "sorry"

abbreviation(input) MARGREL1M5("relationMARGREL1M5-of  _ " [70]70) where
  "relationMARGREL1M5-of D \<equiv> ElementSUBSET-1M1-of relations-onMARGREL1K2 D"

reserve a, b for "FinSequenceFINSEQ-1M3-of D"
reserve p, r for "ElementSUBSET-1M1-of relations-onMARGREL1K2 D"
mtheorem margrel1_th_6:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X be setHIDDENM2 holds  for r be ElementSUBSET-1M1-of relations-onMARGREL1K2 D holds X c=TARSKIR1 r implies X be ElementSUBSET-1M1-of relations-onMARGREL1K2 D"
sorry

mtheorem margrel1_th_7:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for a be FinSequenceFINSEQ-1M3-of D holds {TARSKIK1 a} be ElementSUBSET-1M1-of relations-onMARGREL1K2 D"
sorry

mtheorem margrel1_th_8:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for x be ElementSUBSET-1M1-of D holds  for y be ElementSUBSET-1M1-of D holds {TARSKIK1 <*FINSEQ-1K11 x,y *> } be ElementSUBSET-1M1-of relations-onMARGREL1K2 D"
sorry

syntax MARGREL1R2 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> o" (" _ =MARGREL1R2\<^bsub>'( _ ')\<^esub>  _ " [50,0,50]50)
translations "p =MARGREL1R2\<^bsub>(D)\<^esub> r" \<rightharpoonup> "p =HIDDENR1 r"

mtheorem margrel1_def_8:
  mlet "D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "p be ElementSUBSET-1M1-of relations-onMARGREL1K2 D", "r be ElementSUBSET-1M1-of relations-onMARGREL1K2 D"
"redefine pred p =MARGREL1R2\<^bsub>(D)\<^esub> r means
   for a be FinSequenceFINSEQ-1M3-of D holds a inTARSKIR2 p iff a inTARSKIR2 r"
proof
(*compatibility*)
  show "p =MARGREL1R2\<^bsub>(D)\<^esub> r iff ( for a be FinSequenceFINSEQ-1M3-of D holds a inTARSKIR2 p iff a inTARSKIR2 r)"
sorry
qed "sorry"

theorem margrel1_sch_2:
  fixes Df0 Pp1 
  assumes
[ty]: "Df0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
   A1: " for a be FinSequenceFINSEQ-1M3-of Df0 holds  for b be FinSequenceFINSEQ-1M3-of Df0 holds Pp1(a) & Pp1(b) implies lenFINSEQ-1K4 a =XBOOLE-0R4 lenFINSEQ-1K4 b"
  shows " ex r be ElementSUBSET-1M1-of relations-onMARGREL1K2 Df0 st  for a be FinSequenceFINSEQ-1M3-of Df0 holds a inTARSKIR2 r iff Pp1(a)"
sorry

mdef margrel1_def_9 ("empty-relMARGREL1K3  _ " [164]164 ) where
  mlet "D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
"func empty-relMARGREL1K3 D \<rightarrow> ElementSUBSET-1M1-of relations-onMARGREL1K2 D means
  \<lambda>it.  for a be FinSequenceFINSEQ-1M3-of D holds  not a inTARSKIR2 it"
proof-
  (*existence*)
    show " ex it be ElementSUBSET-1M1-of relations-onMARGREL1K2 D st  for a be FinSequenceFINSEQ-1M3-of D holds  not a inTARSKIR2 it"
sorry
  (*uniqueness*)
    show " for it1 be ElementSUBSET-1M1-of relations-onMARGREL1K2 D holds  for it2 be ElementSUBSET-1M1-of relations-onMARGREL1K2 D holds ( for a be FinSequenceFINSEQ-1M3-of D holds  not a inTARSKIR2 it1) & ( for a be FinSequenceFINSEQ-1M3-of D holds  not a inTARSKIR2 it2) implies it1 =HIDDENR1 it2"
       sorry
qed "sorry"

mtheorem margrel1_th_9:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds empty-relMARGREL1K3 D =XBOOLE-0R4 {}XBOOLE-0K1"
sorry

mdef margrel1_def_10 ("the-arity-ofMARGREL1K4\<^bsub>'( _ ')\<^esub>  _ " [0,120]120 ) where
  mlet "D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "p be ElementSUBSET-1M1-of relations-onMARGREL1K2 D"
"assume p <>HIDDENR2 empty-relMARGREL1K3 D func the-arity-ofMARGREL1K4\<^bsub>(D)\<^esub> p \<rightarrow> ElementSUBSET-1M1-of NATNUMBERSK1 means
  \<lambda>it.  for a be FinSequenceFINSEQ-1M3-of D holds a inTARSKIR2 p implies it =XBOOLE-0R4 lenFINSEQ-1K4 a"
proof-
  (*existence*)
    show "p <>HIDDENR2 empty-relMARGREL1K3 D implies ( ex it be ElementSUBSET-1M1-of NATNUMBERSK1 st  for a be FinSequenceFINSEQ-1M3-of D holds a inTARSKIR2 p implies it =XBOOLE-0R4 lenFINSEQ-1K4 a)"
sorry
  (*uniqueness*)
    show "p <>HIDDENR2 empty-relMARGREL1K3 D implies ( for it1 be ElementSUBSET-1M1-of NATNUMBERSK1 holds  for it2 be ElementSUBSET-1M1-of NATNUMBERSK1 holds ( for a be FinSequenceFINSEQ-1M3-of D holds a inTARSKIR2 p implies it1 =XBOOLE-0R4 lenFINSEQ-1K4 a) & ( for a be FinSequenceFINSEQ-1M3-of D holds a inTARSKIR2 p implies it2 =XBOOLE-0R4 lenFINSEQ-1K4 a) implies it1 =HIDDENR1 it2)"
sorry
qed "sorry"

theorem margrel1_sch_3:
  fixes Df0 kf0 Pp1 
  assumes
[ty]: "Df0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
  [ty]: "kf0 be ElementSUBSET-1M1-of NATNUMBERSK1"
  shows " ex r be ElementSUBSET-1M1-of relations-onMARGREL1K2 Df0 st  for a be FinSequenceFINSEQ-1M3-of Df0 holds lenFINSEQ-1K4 a =XBOOLE-0R4 kf0 implies (a inTARSKIR2 r iff Pp1(a))"
sorry

mdef margrel1_def_11 ("BOOLEANMARGREL1K5" 164 ) where
"func BOOLEANMARGREL1K5 \<rightarrow> setHIDDENM2 equals
  {TARSKIK2 0NUMBERSK6,\<one>\<^sub>M }"
proof-
  (*coherence*)
    show "{TARSKIK2 0NUMBERSK6,\<one>\<^sub>M } be setHIDDENM2"
       sorry
qed "sorry"

mtheorem margrel1_cl_4:
"cluster BOOLEANMARGREL1K5 as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "BOOLEANMARGREL1K5 be  non emptyXBOOLE-0V1"
     sorry
qed "sorry"

abbreviation(input) MARGREL1K6("FALSEMARGREL1K6" 164) where
  "FALSEMARGREL1K6 \<equiv> FALSEXBOOLEANK1"

mtheorem margrel1_add_1:
"cluster FALSEXBOOLEANK1 as-term-is ElementSUBSET-1M1-of BOOLEANMARGREL1K5"
proof
(*coherence*)
  show "FALSEXBOOLEANK1 be ElementSUBSET-1M1-of BOOLEANMARGREL1K5"
    using tarski_def_2 sorry
qed "sorry"

abbreviation(input) MARGREL1K7("TRUEMARGREL1K7" 164) where
  "TRUEMARGREL1K7 \<equiv> TRUEXBOOLEANK2"

mtheorem margrel1_add_2:
"cluster TRUEXBOOLEANK2 as-term-is ElementSUBSET-1M1-of BOOLEANMARGREL1K5"
proof
(*coherence*)
  show "TRUEXBOOLEANK2 be ElementSUBSET-1M1-of BOOLEANMARGREL1K5"
    using tarski_def_2 sorry
qed "sorry"

abbreviation(input) MARGREL1V2("booleanMARGREL1V2" 70) where
  "booleanMARGREL1V2 \<equiv> booleanXBOOLEANV1"

mtheorem margrel1_def_12:
  mlet "x be objectHIDDENM1"
"redefine attr booleanMARGREL1V2 for objectHIDDENM1 means
  (\<lambda>x. x inHIDDENR3 BOOLEANMARGREL1K5)"
proof
(*compatibility*)
  show " for x be objectHIDDENM1 holds x be booleanMARGREL1V2 iff x inHIDDENR3 BOOLEANMARGREL1K5"
sorry
qed "sorry"

mtheorem margrel1_cl_5:
"cluster note-that booleanMARGREL1V2 for ElementSUBSET-1M1-of BOOLEANMARGREL1K5"
proof
(*coherence*)
  show " for it be ElementSUBSET-1M1-of BOOLEANMARGREL1K5 holds it be booleanMARGREL1V2"
     sorry
qed "sorry"

reserve u, v, w for "booleanMARGREL1V2\<bar>objectHIDDENM1"
abbreviation(input) MARGREL1K8("''not''MARGREL1K8  _ " [182]182) where
  "'not'MARGREL1K8 v \<equiv> 'not'XBOOLEANK3 v"

mtheorem margrel1_def_13:
  mlet "v be booleanMARGREL1V2\<bar>objectHIDDENM1"
"redefine func 'not'MARGREL1K8 v \<rightarrow> objectHIDDENM1 equals
  TRUEMARGREL1K7 if v =HIDDENR1 FALSEMARGREL1K6 otherwise FALSEMARGREL1K6"
proof
(*compatibility*)
  show " for it be objectHIDDENM1 holds (v =HIDDENR1 FALSEMARGREL1K6 implies (it =HIDDENR1 'not'MARGREL1K8 v iff it =HIDDENR1 TRUEMARGREL1K7)) & ( not v =HIDDENR1 FALSEMARGREL1K6 implies (it =HIDDENR1 'not'MARGREL1K8 v iff it =HIDDENR1 FALSEMARGREL1K6))"
sorry
(*consistency*)
  show " for it be objectHIDDENM1 holds  True "
     sorry
qed "sorry"

abbreviation(input) MARGREL1K9(" _ ''&''MARGREL1K9  _ " [180,180]180) where
  "v '&'MARGREL1K9 w \<equiv> v '&'XBOOLEANK4 w"

mtheorem margrel1_def_14:
  mlet "v be booleanMARGREL1V2\<bar>objectHIDDENM1", "w be booleanMARGREL1V2\<bar>objectHIDDENM1"
"redefine func v '&'MARGREL1K9 w \<rightarrow> objectHIDDENM1 equals
  TRUEMARGREL1K7 if v =HIDDENR1 TRUEMARGREL1K7 & w =HIDDENR1 TRUEMARGREL1K7 otherwise FALSEMARGREL1K6"
proof
(*compatibility*)
  show " for it be objectHIDDENM1 holds (v =HIDDENR1 TRUEMARGREL1K7 & w =HIDDENR1 TRUEMARGREL1K7 implies (it =HIDDENR1 v '&'MARGREL1K9 w iff it =HIDDENR1 TRUEMARGREL1K7)) & ( not (v =HIDDENR1 TRUEMARGREL1K7 & w =HIDDENR1 TRUEMARGREL1K7) implies (it =HIDDENR1 v '&'MARGREL1K9 w iff it =HIDDENR1 FALSEMARGREL1K6))"
sorry
(*consistency*)
  show " for it be objectHIDDENM1 holds  True "
     sorry
qed "sorry"

abbreviation(input) MARGREL1K10("''not''MARGREL1K10  _ " [182]182) where
  "'not'MARGREL1K10 v \<equiv> 'not'XBOOLEANK3 v"

mtheorem margrel1_add_3:
  mlet "v be ElementSUBSET-1M1-of BOOLEANMARGREL1K5"
"cluster 'not'XBOOLEANK3 v as-term-is ElementSUBSET-1M1-of BOOLEANMARGREL1K5"
proof
(*coherence*)
  show "'not'XBOOLEANK3 v be ElementSUBSET-1M1-of BOOLEANMARGREL1K5"
    using margrel1_def_12 sorry
qed "sorry"

abbreviation(input) MARGREL1K11(" _ ''&''MARGREL1K11  _ " [180,180]180) where
  "v '&'MARGREL1K11 w \<equiv> v '&'XBOOLEANK4 w"

mtheorem margrel1_add_4:
  mlet "v be ElementSUBSET-1M1-of BOOLEANMARGREL1K5", "w be ElementSUBSET-1M1-of BOOLEANMARGREL1K5"
"cluster v '&'XBOOLEANK4 w as-term-is ElementSUBSET-1M1-of BOOLEANMARGREL1K5"
proof
(*coherence*)
  show "v '&'XBOOLEANK4 w be ElementSUBSET-1M1-of BOOLEANMARGREL1K5"
    using margrel1_def_12 sorry
qed "sorry"

(*\$CT*)
mtheorem margrel1_th_11:
" for v be booleanMARGREL1V2\<bar>objectHIDDENM1 holds (v =HIDDENR1 FALSEMARGREL1K6 iff 'not'MARGREL1K8 v =HIDDENR1 TRUEMARGREL1K7) & (v =HIDDENR1 TRUEMARGREL1K7 iff 'not'MARGREL1K8 v =HIDDENR1 FALSEMARGREL1K6)"
   sorry

mtheorem margrel1_th_12:
" for v be booleanMARGREL1V2\<bar>objectHIDDENM1 holds  for w be booleanMARGREL1V2\<bar>objectHIDDENM1 holds (v '&'MARGREL1K9 w =HIDDENR1 TRUEMARGREL1K7 iff v =HIDDENR1 TRUEMARGREL1K7 & w =HIDDENR1 TRUEMARGREL1K7) & (v '&'MARGREL1K9 w =HIDDENR1 FALSEMARGREL1K6 iff v =HIDDENR1 FALSEMARGREL1K6 or w =HIDDENR1 FALSEMARGREL1K6)"
  using xboolean_th_101 xboolean_th_140 sorry

mtheorem margrel1_th_13:
" for v be booleanMARGREL1V2\<bar>objectHIDDENM1 holds (FALSEMARGREL1K6)'&'MARGREL1K9 v =HIDDENR1 FALSEMARGREL1K6"
   sorry

mtheorem margrel1_th_14:
" for v be booleanMARGREL1V2\<bar>objectHIDDENM1 holds (TRUEMARGREL1K7)'&'MARGREL1K9 v =HIDDENR1 v"
   sorry

mtheorem margrel1_th_15:
" for v be booleanMARGREL1V2\<bar>objectHIDDENM1 holds v '&'MARGREL1K9 v =HIDDENR1 FALSEMARGREL1K6 implies v =HIDDENR1 FALSEMARGREL1K6"
   sorry

mtheorem margrel1_th_16:
" for u be booleanMARGREL1V2\<bar>objectHIDDENM1 holds  for v be booleanMARGREL1V2\<bar>objectHIDDENM1 holds  for w be booleanMARGREL1V2\<bar>objectHIDDENM1 holds v '&'MARGREL1K9 (w '&'MARGREL1K9 u) =HIDDENR1 (v '&'MARGREL1K9 w)'&'MARGREL1K9 u"
   sorry

mdef margrel1_def_15 ("ALLMARGREL1K12  _ " [164]164 ) where
  mlet "X be setHIDDENM2"
"func ALLMARGREL1K12 X \<rightarrow> setHIDDENM2 equals
  TRUEMARGREL1K7 if  not FALSEMARGREL1K6 inTARSKIR2 X otherwise FALSEMARGREL1K6"
proof-
  (*coherence*)
    show "( not FALSEMARGREL1K6 inTARSKIR2 X implies TRUEMARGREL1K7 be setHIDDENM2) & ( not ( not FALSEMARGREL1K6 inTARSKIR2 X) implies FALSEMARGREL1K6 be setHIDDENM2)"
       sorry
  (*consistency*)
    show " for it be setHIDDENM2 holds  True "
       sorry
qed "sorry"

mtheorem margrel1_cl_6:
  mlet "X be setHIDDENM2"
"cluster ALLMARGREL1K12 X as-term-is booleanMARGREL1V2"
proof
(*coherence*)
  show "ALLMARGREL1K12 X be booleanMARGREL1V2"
    using margrel1_def_15 sorry
qed "sorry"

abbreviation(input) MARGREL1K13("ALLMARGREL1K13  _ " [164]164) where
  "ALLMARGREL1K13 X \<equiv> ALLMARGREL1K12 X"

mtheorem margrel1_add_5:
  mlet "X be setHIDDENM2"
"cluster ALLMARGREL1K12 X as-term-is ElementSUBSET-1M1-of BOOLEANMARGREL1K5"
proof
(*coherence*)
  show "ALLMARGREL1K12 X be ElementSUBSET-1M1-of BOOLEANMARGREL1K5"
    using margrel1_def_12 sorry
qed "sorry"

mtheorem margrel1_th_17:
" for X be setHIDDENM2 holds ( not FALSEMARGREL1K6 inTARSKIR2 X iff ALLMARGREL1K13 X =XBOOLE-0R4 TRUEMARGREL1K7) & (FALSEMARGREL1K6 inTARSKIR2 X iff ALLMARGREL1K13 X =XBOOLE-0R4 FALSEMARGREL1K6)"
  using margrel1_def_15 sorry

(*begin*)
mdef margrel1_def_16 ("boolean-valuedMARGREL1V3" 70 ) where
"attr boolean-valuedMARGREL1V3 for RelationRELAT-1M1 means
  (\<lambda>f. rngRELAT-1K2 f c=TARSKIR1 BOOLEANMARGREL1K5)"..

mtheorem margrel1_cl_7:
"cluster boolean-valuedMARGREL1V3 for FunctionFUNCT-1M1"
proof
(*existence*)
  show " ex it be FunctionFUNCT-1M1 st it be boolean-valuedMARGREL1V3"
sorry
qed "sorry"

mtheorem margrel1_cl_8:
  mlet "f be boolean-valuedMARGREL1V3\<bar>FunctionFUNCT-1M1", "x be objectHIDDENM1"
"cluster f .FUNCT-1K1 x as-term-is booleanMARGREL1V2"
proof
(*coherence*)
  show "f .FUNCT-1K1 x be booleanMARGREL1V2"
sorry
qed "sorry"

mdef margrel1_def_17 ("''not''MARGREL1K14  _ " [182]182 ) where
  mlet "p be boolean-valuedMARGREL1V3\<bar>FunctionFUNCT-1M1"
"func 'not'MARGREL1K14 p \<rightarrow> boolean-valuedMARGREL1V3\<bar>FunctionFUNCT-1M1 means
  \<lambda>it. domRELAT-1K1 it =XBOOLE-0R4 domRELAT-1K1 p & ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 p implies it .FUNCT-1K1 x =HIDDENR1 'not'MARGREL1K8 p .FUNCT-1K1 x)"
proof-
  (*existence*)
    show " ex it be boolean-valuedMARGREL1V3\<bar>FunctionFUNCT-1M1 st domRELAT-1K1 it =XBOOLE-0R4 domRELAT-1K1 p & ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 p implies it .FUNCT-1K1 x =HIDDENR1 'not'MARGREL1K8 p .FUNCT-1K1 x)"
sorry
  (*uniqueness*)
    show " for it1 be boolean-valuedMARGREL1V3\<bar>FunctionFUNCT-1M1 holds  for it2 be boolean-valuedMARGREL1V3\<bar>FunctionFUNCT-1M1 holds (domRELAT-1K1 it1 =XBOOLE-0R4 domRELAT-1K1 p & ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 p implies it1 .FUNCT-1K1 x =HIDDENR1 'not'MARGREL1K8 p .FUNCT-1K1 x)) & (domRELAT-1K1 it2 =XBOOLE-0R4 domRELAT-1K1 p & ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 p implies it2 .FUNCT-1K1 x =HIDDENR1 'not'MARGREL1K8 p .FUNCT-1K1 x)) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mtheorem MARGREL1K14_involutiveness:
" for p be boolean-valuedMARGREL1V3\<bar>FunctionFUNCT-1M1 holds 'not'MARGREL1K14 ('not'MARGREL1K14 p) =HIDDENR1 p"
sorry

mdef margrel1_def_18 (" _ ''&''MARGREL1K15  _ " [180,180]180 ) where
  mlet "p be boolean-valuedMARGREL1V3\<bar>FunctionFUNCT-1M1", "q be boolean-valuedMARGREL1V3\<bar>FunctionFUNCT-1M1"
"func p '&'MARGREL1K15 q \<rightarrow> boolean-valuedMARGREL1V3\<bar>FunctionFUNCT-1M1 means
  \<lambda>it. domRELAT-1K1 it =XBOOLE-0R4 domRELAT-1K1 p /\\XBOOLE-0K3 domRELAT-1K1 q & ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 it implies it .FUNCT-1K1 x =HIDDENR1 p .FUNCT-1K1 x '&'MARGREL1K9 q .FUNCT-1K1 x)"
proof-
  (*existence*)
    show " ex it be boolean-valuedMARGREL1V3\<bar>FunctionFUNCT-1M1 st domRELAT-1K1 it =XBOOLE-0R4 domRELAT-1K1 p /\\XBOOLE-0K3 domRELAT-1K1 q & ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 it implies it .FUNCT-1K1 x =HIDDENR1 p .FUNCT-1K1 x '&'MARGREL1K9 q .FUNCT-1K1 x)"
sorry
  (*uniqueness*)
    show " for it1 be boolean-valuedMARGREL1V3\<bar>FunctionFUNCT-1M1 holds  for it2 be boolean-valuedMARGREL1V3\<bar>FunctionFUNCT-1M1 holds (domRELAT-1K1 it1 =XBOOLE-0R4 domRELAT-1K1 p /\\XBOOLE-0K3 domRELAT-1K1 q & ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 it1 implies it1 .FUNCT-1K1 x =HIDDENR1 p .FUNCT-1K1 x '&'MARGREL1K9 q .FUNCT-1K1 x)) & (domRELAT-1K1 it2 =XBOOLE-0R4 domRELAT-1K1 p /\\XBOOLE-0K3 domRELAT-1K1 q & ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 it2 implies it2 .FUNCT-1K1 x =HIDDENR1 p .FUNCT-1K1 x '&'MARGREL1K9 q .FUNCT-1K1 x)) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mtheorem MARGREL1K15_commutativity:
" for p be boolean-valuedMARGREL1V3\<bar>FunctionFUNCT-1M1 holds  for q be boolean-valuedMARGREL1V3\<bar>FunctionFUNCT-1M1 holds p '&'MARGREL1K15 q =HIDDENR1 q '&'MARGREL1K15 p"
sorry

mtheorem MARGREL1K15_idempotence:
" for q be boolean-valuedMARGREL1V3\<bar>FunctionFUNCT-1M1 holds q =HIDDENR1 q '&'MARGREL1K15 q"
sorry

mtheorem margrel1_cl_9:
  mlet "A be setHIDDENM2"
"cluster note-that boolean-valuedMARGREL1V3 for FunctionFUNCT-2M1-of(A,BOOLEANMARGREL1K5)"
proof
(*coherence*)
  show " for it be FunctionFUNCT-2M1-of(A,BOOLEANMARGREL1K5) holds it be boolean-valuedMARGREL1V3"
    using relat_1_def_19 sorry
qed "sorry"

syntax MARGREL1K16 :: " Set \<Rightarrow>  Set \<Rightarrow> Set" ("''not''MARGREL1K16\<^bsub>'( _ ')\<^esub>  _ " [0,182]182)
translations "'not'MARGREL1K16\<^bsub>(A)\<^esub> p" \<rightharpoonup> "'not'MARGREL1K14 p"

mtheorem margrel1_def_19:
  mlet "A be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "p be FunctionFUNCT-2M1-of(A,BOOLEANMARGREL1K5)"
"redefine func 'not'MARGREL1K16\<^bsub>(A)\<^esub> p \<rightarrow> FunctionFUNCT-2M1-of(A,BOOLEANMARGREL1K5) means
  \<lambda>it.  for x be ElementSUBSET-1M1-of A holds it .FUNCT-2K3\<^bsub>(A,BOOLEANMARGREL1K5)\<^esub> x =XBOOLE-0R4 'not'MARGREL1K10 p .FUNCT-2K3\<^bsub>(A,BOOLEANMARGREL1K5)\<^esub> x"
proof
(*compatibility*)
  show " for it be FunctionFUNCT-2M1-of(A,BOOLEANMARGREL1K5) holds it =HIDDENR1 'not'MARGREL1K16\<^bsub>(A)\<^esub> p iff ( for x be ElementSUBSET-1M1-of A holds it .FUNCT-2K3\<^bsub>(A,BOOLEANMARGREL1K5)\<^esub> x =XBOOLE-0R4 'not'MARGREL1K10 p .FUNCT-2K3\<^bsub>(A,BOOLEANMARGREL1K5)\<^esub> x)"
sorry
qed "sorry"

mtheorem margrel1_add_6:
  mlet "A be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "p be FunctionFUNCT-2M1-of(A,BOOLEANMARGREL1K5)"
"cluster 'not'MARGREL1K14 p as-term-is FunctionFUNCT-2M1-of(A,BOOLEANMARGREL1K5)"
proof
(*coherence*)
  show "'not'MARGREL1K14 p be FunctionFUNCT-2M1-of(A,BOOLEANMARGREL1K5)"
sorry
qed "sorry"

syntax MARGREL1K17 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ ''&''MARGREL1K17\<^bsub>'( _ ')\<^esub>  _ " [180,0,180]180)
translations "p '&'MARGREL1K17\<^bsub>(A)\<^esub> q" \<rightharpoonup> "p '&'MARGREL1K15 q"

mtheorem margrel1_def_20:
  mlet "A be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "p be FunctionFUNCT-2M1-of(A,BOOLEANMARGREL1K5)", "q be FunctionFUNCT-2M1-of(A,BOOLEANMARGREL1K5)"
"redefine func p '&'MARGREL1K17\<^bsub>(A)\<^esub> q \<rightarrow> FunctionFUNCT-2M1-of(A,BOOLEANMARGREL1K5) means
  \<lambda>it.  for x be ElementSUBSET-1M1-of A holds it .FUNCT-2K3\<^bsub>(A,BOOLEANMARGREL1K5)\<^esub> x =XBOOLE-0R4 p .FUNCT-2K3\<^bsub>(A,BOOLEANMARGREL1K5)\<^esub> x '&'MARGREL1K11 q .FUNCT-2K3\<^bsub>(A,BOOLEANMARGREL1K5)\<^esub> x"
proof
(*compatibility*)
  show " for it be FunctionFUNCT-2M1-of(A,BOOLEANMARGREL1K5) holds it =HIDDENR1 p '&'MARGREL1K17\<^bsub>(A)\<^esub> q iff ( for x be ElementSUBSET-1M1-of A holds it .FUNCT-2K3\<^bsub>(A,BOOLEANMARGREL1K5)\<^esub> x =XBOOLE-0R4 p .FUNCT-2K3\<^bsub>(A,BOOLEANMARGREL1K5)\<^esub> x '&'MARGREL1K11 q .FUNCT-2K3\<^bsub>(A,BOOLEANMARGREL1K5)\<^esub> x)"
sorry
qed "sorry"

mtheorem margrel1_add_7:
  mlet "A be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "p be FunctionFUNCT-2M1-of(A,BOOLEANMARGREL1K5)", "q be FunctionFUNCT-2M1-of(A,BOOLEANMARGREL1K5)"
"cluster p '&'MARGREL1K15 q as-term-is FunctionFUNCT-2M1-of(A,BOOLEANMARGREL1K5)"
proof
(*coherence*)
  show "p '&'MARGREL1K15 q be FunctionFUNCT-2M1-of(A,BOOLEANMARGREL1K5)"
sorry
qed "sorry"

(*begin*)
reserve A, z for "setHIDDENM2"
reserve x, y for "FinSequenceFINSEQ-1M3-of A"
reserve h for "PartFuncPARTFUN1M1-of(A * FINSEQ-2K3,A)"
reserve n, m for "NatNAT-1M1"
mdef margrel1_def_21 ("homogeneousMARGREL1V4" 70 ) where
"attr homogeneousMARGREL1V4 for RelationRELAT-1M1 means
  (\<lambda>IT. domRELAT-1K1 IT be with-common-domainCARD-3V2)"..

mdef margrel1_def_22 ("quasi-totalMARGREL1V5\<^bsub>'( _ ')\<^esub>" [0]70 ) where
  mlet "A be setHIDDENM2"
"attr quasi-totalMARGREL1V5\<^bsub>(A)\<^esub> for PartFuncPARTFUN1M1-of(A * FINSEQ-2K3,A) means
  (\<lambda>IT.  for x be FinSequenceFINSEQ-1M3-of A holds  for y be FinSequenceFINSEQ-1M3-of A holds lenFINSEQ-1K4 x =XBOOLE-0R4 lenFINSEQ-1K4 y & x inTARSKIR2 domRELAT-1K1 IT implies y inTARSKIR2 domRELAT-1K1 IT)"..

mtheorem margrel1_cl_10:
  mlet "f be RelationRELAT-1M1", "X be with-common-domainCARD-3V2\<bar>setHIDDENM2"
"cluster f |RELAT-1K8 X as-term-is homogeneousMARGREL1V4"
proof
(*coherence*)
  show "f |RELAT-1K8 X be homogeneousMARGREL1V4"
sorry
qed "sorry"

mtheorem margrel1_cl_11:
  mlet "A be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "f be PartFuncPARTFUN1M1-of(A * FINSEQ-2K3,A)"
"cluster domRELAT-1K1 f as-term-is FinSequence-memberedFINSEQ-1V3"
proof
(*coherence*)
  show "domRELAT-1K1 f be FinSequence-memberedFINSEQ-1V3"
sorry
qed "sorry"

mtheorem margrel1_cl_12:
  mlet "A be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster homogeneousMARGREL1V4\<bar>quasi-totalMARGREL1V5\<^bsub>(A)\<^esub>\<bar> non emptyXBOOLE-0V1 for PartFuncPARTFUN1M1-of(A * FINSEQ-2K3,A)"
proof
(*existence*)
  show " ex it be PartFuncPARTFUN1M1-of(A * FINSEQ-2K3,A) st it be homogeneousMARGREL1V4\<bar>quasi-totalMARGREL1V5\<^bsub>(A)\<^esub>\<bar> non emptyXBOOLE-0V1"
sorry
qed "sorry"

mtheorem margrel1_cl_13:
"cluster homogeneousMARGREL1V4\<bar> non emptyXBOOLE-0V1 for FunctionFUNCT-1M1"
proof
(*existence*)
  show " ex it be FunctionFUNCT-1M1 st it be homogeneousMARGREL1V4\<bar> non emptyXBOOLE-0V1"
sorry
qed "sorry"

mtheorem margrel1_cl_14:
  mlet "R be homogeneousMARGREL1V4\<bar>RelationRELAT-1M1"
"cluster domRELAT-1K1 R as-term-is with-common-domainCARD-3V2"
proof
(*coherence*)
  show "domRELAT-1K1 R be with-common-domainCARD-3V2"
    using margrel1_def_21 sorry
qed "sorry"

mtheorem margrel1_th_18:
" for A be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for a be ElementSUBSET-1M1-of A holds <*>FINSEQ-1K7 A .-->FUNCOP-1K17 a be homogeneousMARGREL1V4\<bar>quasi-totalMARGREL1V5\<^bsub>(A)\<^esub>\<bar> non emptyXBOOLE-0V1\<bar>PartFuncPARTFUN1M1-of(A * FINSEQ-2K3,A)"
sorry

mtheorem margrel1_th_19:
" for A be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for a be ElementSUBSET-1M1-of A holds <*>FINSEQ-1K7 A .-->FUNCOP-1K17 a be ElementSUBSET-1M1-of PFuncsPARTFUN1K4(A * FINSEQ-2K3,A)"
sorry

abbreviation(input) MARGREL1M6("PFuncFinSequenceMARGREL1M6-of  _ " [70]70) where
  "PFuncFinSequenceMARGREL1M6-of A \<equiv> FinSequenceFINSEQ-1M3-of PFuncsPARTFUN1K4(A * FINSEQ-2K3,A)"

mdef margrel1_def_23 ("homogeneousMARGREL1V6\<^bsub>'( _ ')\<^esub>" [0]70 ) where
  mlet "A be setHIDDENM2"
"attr homogeneousMARGREL1V6\<^bsub>(A)\<^esub> for PFuncFinSequenceMARGREL1M6-of A means
  (\<lambda>IT.  for n be NatNAT-1M1 holds  for h be PartFuncPARTFUN1M1-of(A * FINSEQ-2K3,A) holds n inTARSKIR2 domFINSEQ-1K5 IT & h =RELAT-1R1 IT .FUNCT-1K1 n implies h be homogeneousMARGREL1V4)"..

mdef margrel1_def_24 ("quasi-totalMARGREL1V7\<^bsub>'( _ ')\<^esub>" [0]70 ) where
  mlet "A be setHIDDENM2"
"attr quasi-totalMARGREL1V7\<^bsub>(A)\<^esub> for PFuncFinSequenceMARGREL1M6-of A means
  (\<lambda>IT.  for n be NatNAT-1M1 holds  for h be PartFuncPARTFUN1M1-of(A * FINSEQ-2K3,A) holds n inTARSKIR2 domFINSEQ-1K5 IT & h =RELAT-1R1 IT .FUNCT-1K1 n implies h be quasi-totalMARGREL1V5\<^bsub>(A)\<^esub>)"..

syntax MARGREL1K18 :: " Set \<Rightarrow>  Set \<Rightarrow> Set" ("<*MARGREL1K18\<^bsub>'( _ ')\<^esub>  _ *>" [0,0]164)
translations "<*MARGREL1K18\<^bsub>(A)\<^esub> x*>" \<rightharpoonup> "<*FINSEQ-1K6 x*>"

mtheorem margrel1_add_8:
  mlet "A be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "x be ElementSUBSET-1M1-of PFuncsPARTFUN1K4(A * FINSEQ-2K3,A)"
"cluster <*FINSEQ-1K6 x*> as-term-is PFuncFinSequenceMARGREL1M6-of A"
proof
(*coherence*)
  show "<*FINSEQ-1K6 x*> be PFuncFinSequenceMARGREL1M6-of A"
sorry
qed "sorry"

mtheorem margrel1_cl_15:
  mlet "A be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster homogeneousMARGREL1V6\<^bsub>(A)\<^esub>\<bar>quasi-totalMARGREL1V7\<^bsub>(A)\<^esub>\<bar>non-emptyRELAT-1V2 for PFuncFinSequenceMARGREL1M6-of A"
proof
(*existence*)
  show " ex it be PFuncFinSequenceMARGREL1M6-of A st it be homogeneousMARGREL1V6\<^bsub>(A)\<^esub>\<bar>quasi-totalMARGREL1V7\<^bsub>(A)\<^esub>\<bar>non-emptyRELAT-1V2"
sorry
qed "sorry"

mtheorem margrel1_cl_16:
  mlet "A be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "f be homogeneousMARGREL1V6\<^bsub>(A)\<^esub>\<bar>PFuncFinSequenceMARGREL1M6-of A", "i be setHIDDENM2"
"cluster f .FUNCT-1K1 i as-term-is homogeneousMARGREL1V4"
proof
(*coherence*)
  show "f .FUNCT-1K1 i be homogeneousMARGREL1V4"
sorry
qed "sorry"

reserve A for " non emptyXBOOLE-0V1\<bar>setHIDDENM2"
reserve h for "PartFuncPARTFUN1M1-of(A * FINSEQ-2K3,A)"
reserve a for "ElementSUBSET-1M1-of A"
mtheorem margrel1_th_20:
" for A be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for a be ElementSUBSET-1M1-of A holds  for x be ElementSUBSET-1M1-of PFuncsPARTFUN1K4(A * FINSEQ-2K3,A) holds x =RELAT-1R1 <*>FINSEQ-1K7 A .-->FUNCOP-1K17 a implies <*MARGREL1K18\<^bsub>(A)\<^esub> x*> be homogeneousMARGREL1V6\<^bsub>(A)\<^esub>\<bar>quasi-totalMARGREL1V7\<^bsub>(A)\<^esub>\<bar>non-emptyRELAT-1V2"
sorry

mdef margrel1_def_25 ("arityMARGREL1K19  _ " [228]228 ) where
  mlet "f be homogeneousMARGREL1V4\<bar>RelationRELAT-1M1"
"func arityMARGREL1K19 f \<rightarrow> NatNAT-1M1 means
  \<lambda>it.  for x be FinSequenceFINSEQ-1M1 holds x inTARSKIR2 domRELAT-1K1 f implies it =XBOOLE-0R4 lenFINSEQ-1K4 x if  ex x be FinSequenceFINSEQ-1M1 st x inTARSKIR2 domRELAT-1K1 f otherwise \<lambda>it. it =XBOOLE-0R4 0NUMBERSK6"
proof-
  (*consistency*)
    show " for it be NatNAT-1M1 holds  True "
       sorry
  (*existence*)
    show "(( ex x be FinSequenceFINSEQ-1M1 st x inTARSKIR2 domRELAT-1K1 f) implies ( ex it be NatNAT-1M1 st  for x be FinSequenceFINSEQ-1M1 holds x inTARSKIR2 domRELAT-1K1 f implies it =XBOOLE-0R4 lenFINSEQ-1K4 x)) & ( not ( ex x be FinSequenceFINSEQ-1M1 st x inTARSKIR2 domRELAT-1K1 f) implies ( ex it be NatNAT-1M1 st it =XBOOLE-0R4 0NUMBERSK6))"
sorry
  (*uniqueness*)
    show " for it1 be NatNAT-1M1 holds  for it2 be NatNAT-1M1 holds (( ex x be FinSequenceFINSEQ-1M1 st x inTARSKIR2 domRELAT-1K1 f) implies (( for x be FinSequenceFINSEQ-1M1 holds x inTARSKIR2 domRELAT-1K1 f implies it1 =XBOOLE-0R4 lenFINSEQ-1K4 x) & ( for x be FinSequenceFINSEQ-1M1 holds x inTARSKIR2 domRELAT-1K1 f implies it2 =XBOOLE-0R4 lenFINSEQ-1K4 x) implies it1 =HIDDENR1 it2)) & ( not ( ex x be FinSequenceFINSEQ-1M1 st x inTARSKIR2 domRELAT-1K1 f) implies (it1 =XBOOLE-0R4 0NUMBERSK6 & it2 =XBOOLE-0R4 0NUMBERSK6 implies it1 =HIDDENR1 it2))"
sorry
qed "sorry"

abbreviation(input) MARGREL1K20("arityMARGREL1K20  _ " [228]228) where
  "arityMARGREL1K20 f \<equiv> arityMARGREL1K19 f"

mtheorem margrel1_add_9:
  mlet "f be homogeneousMARGREL1V4\<bar>FunctionFUNCT-1M1"
"cluster arityMARGREL1K19 f as-term-is ElementSUBSET-1M1-of NATNUMBERSK1"
proof
(*coherence*)
  show "arityMARGREL1K19 f be ElementSUBSET-1M1-of NATNUMBERSK1"
    using ordinal1_def_12 sorry
qed "sorry"

(*begin*)
mtheorem margrel1_th_21:
" for n be NatNAT-1M1 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D1 be  non emptyXBOOLE-0V1\<bar>SubsetSUBSET-1M2-of D holds n -tuples-onFINSEQ-2K4 D /\\XBOOLE-0K3 n -tuples-onFINSEQ-2K4 D1 =XBOOLE-0R4 n -tuples-onFINSEQ-2K4 D1"
sorry

mtheorem margrel1_th_22:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for h be homogeneousMARGREL1V4\<bar>quasi-totalMARGREL1V5\<^bsub>(D)\<^esub>\<bar> non emptyXBOOLE-0V1\<bar>PartFuncPARTFUN1M1-of(D * FINSEQ-2K3,D) holds domRELAT-1K1 h =XBOOLE-0R4 (arityMARGREL1K20 h)-tuples-onFINSEQ-2K4 D"
sorry

mdef margrel1_def_26 ("PFuncsDomHQNMARGREL1M7-of  _ " [70]70 ) where
  mlet "D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
"mode PFuncsDomHQNMARGREL1M7-of D \<rightarrow>  non emptyXBOOLE-0V1\<bar>setHIDDENM2 means
  (\<lambda>it.  for x be ElementSUBSET-1M1-of it holds x be homogeneousMARGREL1V4\<bar>quasi-totalMARGREL1V5\<^bsub>(D)\<^esub>\<bar> non emptyXBOOLE-0V1\<bar>PartFuncPARTFUN1M1-of(D * FINSEQ-2K3,D))"
proof-
  (*existence*)
    show " ex it be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 st  for x be ElementSUBSET-1M1-of it holds x be homogeneousMARGREL1V4\<bar>quasi-totalMARGREL1V5\<^bsub>(D)\<^esub>\<bar> non emptyXBOOLE-0V1\<bar>PartFuncPARTFUN1M1-of(D * FINSEQ-2K3,D)"
sorry
qed "sorry"

syntax MARGREL1M8 :: " Set \<Rightarrow>  Set \<Rightarrow> Ty" ("ElementMARGREL1M8\<^bsub>'( _ ')\<^esub>-of  _ " [0,70]70)
translations "ElementMARGREL1M8\<^bsub>(D)\<^esub>-of P" \<rightharpoonup> "ElementSUBSET-1M1-of P"

mtheorem margrel1_add_10:
  mlet "D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "P be PFuncsDomHQNMARGREL1M7-of D"
"cluster note-that homogeneousMARGREL1V4\<bar>quasi-totalMARGREL1V5\<^bsub>(D)\<^esub>\<bar> non emptyXBOOLE-0V1\<bar>PartFuncPARTFUN1M1-of(D * FINSEQ-2K3,D) for ElementSUBSET-1M1-of P"
proof
(*coherence*)
  show " for it be ElementSUBSET-1M1-of P holds it be homogeneousMARGREL1V4\<bar>quasi-totalMARGREL1V5\<^bsub>(D)\<^esub>\<bar> non emptyXBOOLE-0V1\<bar>PartFuncPARTFUN1M1-of(D * FINSEQ-2K3,D)"
    using margrel1_def_26 sorry
qed "sorry"

end
