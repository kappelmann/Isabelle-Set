theory trees_1
  imports finseq_3
   "../mizar_extension/E_number"
begin
(*begin*)
reserve X, x, y, z for "setHIDDENM2"
reserve k, n, m for "NatNAT-1M1"
reserve f for "FunctionFUNCT-1M1"
reserve p, q, r for "FinSequenceFINSEQ-1M3-of NATNUMBERSK1"
abbreviation(input) TREES_1R1(" _ is-a-prefix-ofTREES-1R1  _ " [50,50]50) where
  "p is-a-prefix-ofTREES-1R1 q \<equiv> p c=RELAT-1R2 q"

abbreviation(input) TREES_1R2(" _ is-a-prefix-ofTREES-1R2  _ " [50,50]50) where
  "p is-a-prefix-ofTREES-1R2 q \<equiv> p c=TARSKIR1 q"

mtheorem trees_1_def_1:
  mlet "p be FinSequenceFINSEQ-1M1", "q be FinSequenceFINSEQ-1M1"
"redefine pred p is-a-prefix-ofTREES-1R2 q means
   ex n be NatNAT-1M1 st p =FUNCT-1R1 q |RELAT-1K8 SegFINSEQ-1K2 n"
proof
(*compatibility*)
  show "p is-a-prefix-ofTREES-1R2 q iff ( ex n be NatNAT-1M1 st p =FUNCT-1R1 q |RELAT-1K8 SegFINSEQ-1K2 n)"
sorry
qed "sorry"

mtheorem trees_1_th_1:
" for p be FinSequenceFINSEQ-1M1 holds  for q be FinSequenceFINSEQ-1M1 holds p is-a-prefix-ofTREES-1R2 q iff ( ex r be FinSequenceFINSEQ-1M1 st q =FINSEQ-1R1 p ^FINSEQ-1K8 r)"
sorry

(*\$CT*)
mtheorem trees_1_th_3:
" for x be setHIDDENM2 holds  for y be setHIDDENM2 holds <*FINSEQ-1K10 x*> is-a-prefix-ofTREES-1R2 <*FINSEQ-1K10 y*> implies x =XBOOLE-0R4 y"
sorry

abbreviation(input) TREES_1R3(" _ is-a-proper-prefix-ofTREES-1R3  _ " [50,50]50) where
  "p is-a-proper-prefix-ofTREES-1R3 q \<equiv> p c<XBOOLE-0R2 q"

mtheorem trees_1_th_4:
" for p be finiteFINSET-1V1\<bar>setHIDDENM2 holds  for q be finiteFINSET-1V1\<bar>setHIDDENM2 holds (p,q)are-c=-comparableXBOOLE-0R3 & cardCARD-1K4 p =XBOOLE-0R4 cardCARD-1K4 q implies p =XBOOLE-0R4 q"
  using card_2_th_102 sorry

reserve p1, p2, p3 for "FinSequenceFINSEQ-1M1"
mtheorem trees_1_th_5:
" for x be setHIDDENM2 holds  for y be setHIDDENM2 holds (<*FINSEQ-1K10 x*>,<*FINSEQ-1K10 y*>)are-c=-comparableXBOOLE-0R3 implies x =XBOOLE-0R4 y"
sorry

mtheorem trees_1_th_6:
" for p be finiteFINSET-1V1\<bar>setHIDDENM2 holds  for q be finiteFINSET-1V1\<bar>setHIDDENM2 holds p c<XBOOLE-0R2 q implies cardCARD-1K4 p <XXREAL-0R3 cardCARD-1K4 q"
sorry

mtheorem trees_1_th_7:
" for x be setHIDDENM2 holds  for p1 be FinSequenceFINSEQ-1M1 holds  for p2 be FinSequenceFINSEQ-1M1 holds p1 ^FINSEQ-1K8 (<*FINSEQ-1K10 x*>) is-a-prefix-ofTREES-1R2 p2 implies p1 is-a-proper-prefix-ofTREES-1R3 p2"
sorry

mtheorem trees_1_th_8:
" for x be setHIDDENM2 holds  for p1 be FinSequenceFINSEQ-1M1 holds  for p2 be FinSequenceFINSEQ-1M1 holds p1 is-a-prefix-ofTREES-1R2 p2 implies p1 is-a-proper-prefix-ofTREES-1R3 p2 ^FINSEQ-1K8 (<*FINSEQ-1K10 x*>)"
sorry

mtheorem trees_1_th_9:
" for x be setHIDDENM2 holds  for p1 be FinSequenceFINSEQ-1M1 holds  for p2 be FinSequenceFINSEQ-1M1 holds p1 is-a-proper-prefix-ofTREES-1R3 p2 ^FINSEQ-1K8 (<*FINSEQ-1K10 x*>) implies p1 is-a-prefix-ofTREES-1R2 p2"
sorry

mtheorem trees_1_th_10:
" for p1 be FinSequenceFINSEQ-1M1 holds  for p2 be FinSequenceFINSEQ-1M1 holds {}XBOOLE-0K1 is-a-proper-prefix-ofTREES-1R3 p2 or {}XBOOLE-0K1 <>HIDDENR2 p2 implies p1 is-a-proper-prefix-ofTREES-1R3 p1 ^FINSEQ-1K8 p2"
sorry

mdef trees_1_def_2 ("ProperPrefixesTREES-1K1  _ " [228]228 ) where
  mlet "p be FinSequenceFINSEQ-1M1"
"func ProperPrefixesTREES-1K1 p \<rightarrow> setHIDDENM2 means
  \<lambda>it.  for x be objectHIDDENM1 holds x inHIDDENR3 it iff ( ex q be FinSequenceFINSEQ-1M1 st x =HIDDENR1 q & q is-a-proper-prefix-ofTREES-1R3 p)"
proof-
  (*existence*)
    show " ex it be setHIDDENM2 st  for x be objectHIDDENM1 holds x inHIDDENR3 it iff ( ex q be FinSequenceFINSEQ-1M1 st x =HIDDENR1 q & q is-a-proper-prefix-ofTREES-1R3 p)"
sorry
  (*uniqueness*)
    show " for it1 be setHIDDENM2 holds  for it2 be setHIDDENM2 holds ( for x be objectHIDDENM1 holds x inHIDDENR3 it1 iff ( ex q be FinSequenceFINSEQ-1M1 st x =HIDDENR1 q & q is-a-proper-prefix-ofTREES-1R3 p)) & ( for x be objectHIDDENM1 holds x inHIDDENR3 it2 iff ( ex q be FinSequenceFINSEQ-1M1 st x =HIDDENR1 q & q is-a-proper-prefix-ofTREES-1R3 p)) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mtheorem trees_1_th_11:
" for x be setHIDDENM2 holds  for p be FinSequenceFINSEQ-1M1 holds x inTARSKIR2 ProperPrefixesTREES-1K1 p implies x be FinSequenceFINSEQ-1M1"
sorry

mtheorem trees_1_th_12:
" for p be FinSequenceFINSEQ-1M1 holds  for q be FinSequenceFINSEQ-1M1 holds p inTARSKIR2 ProperPrefixesTREES-1K1 q iff p is-a-proper-prefix-ofTREES-1R3 q"
sorry

mtheorem trees_1_th_13:
" for p be FinSequenceFINSEQ-1M1 holds  for q be FinSequenceFINSEQ-1M1 holds p inTARSKIR2 ProperPrefixesTREES-1K1 q implies lenFINSEQ-1K4 p <XXREAL-0R3 lenFINSEQ-1K4 q"
  using trees_1_th_12 trees_1_th_6 sorry

mtheorem trees_1_th_14:
" for p be FinSequenceFINSEQ-1M1 holds  for q be FinSequenceFINSEQ-1M1 holds  for r be FinSequenceFINSEQ-1M1 holds q ^FINSEQ-1K8 r inTARSKIR2 ProperPrefixesTREES-1K1 p implies q inTARSKIR2 ProperPrefixesTREES-1K1 p"
sorry

mtheorem trees_1_th_15:
"ProperPrefixesTREES-1K1 ({}XBOOLE-0K1) =XBOOLE-0R4 {}XBOOLE-0K1"
sorry

mtheorem trees_1_th_16:
" for x be setHIDDENM2 holds ProperPrefixesTREES-1K1 (<*FINSEQ-1K10 x*>) =XBOOLE-0R4 {TARSKIK1 {}XBOOLE-0K1 }"
sorry

mtheorem trees_1_th_17:
" for p be FinSequenceFINSEQ-1M1 holds  for q be FinSequenceFINSEQ-1M1 holds p is-a-prefix-ofTREES-1R2 q implies ProperPrefixesTREES-1K1 p c=TARSKIR1 ProperPrefixesTREES-1K1 q"
sorry

mtheorem trees_1_th_18:
" for p be FinSequenceFINSEQ-1M1 holds  for q be FinSequenceFINSEQ-1M1 holds  for r be FinSequenceFINSEQ-1M1 holds q inTARSKIR2 ProperPrefixesTREES-1K1 p & r inTARSKIR2 ProperPrefixesTREES-1K1 p implies (q,r)are-c=-comparableXBOOLE-0R3"
sorry

mdef trees_1_def_3 ("Tree-likeTREES-1V1" 70 ) where
"attr Tree-likeTREES-1V1 for setHIDDENM2 means
  (\<lambda>X. (X c=TARSKIR1 NATNUMBERSK1 * FINSEQ-2K3 & ( for p be FinSequenceFINSEQ-1M3-of NATNUMBERSK1 holds p inTARSKIR2 X implies ProperPrefixesTREES-1K1 p c=TARSKIR1 X)) & ( for p be FinSequenceFINSEQ-1M3-of NATNUMBERSK1 holds  for k be NatNAT-1M1 holds  for n be NatNAT-1M1 holds p ^FINSEQ-1K8 (<*FINSEQ-1K10 k*>) inTARSKIR2 X & n <=XXREAL-0R1 k implies p ^FINSEQ-1K8 (<*FINSEQ-1K10 n*>) inTARSKIR2 X))"..

mtheorem trees_1_cl_1:
"cluster {TARSKIK1 {}XBOOLE-0K1 } as-term-is Tree-likeTREES-1V1"
proof
(*coherence*)
  show "{TARSKIK1 {}XBOOLE-0K1 } be Tree-likeTREES-1V1"
sorry
qed "sorry"

mtheorem trees_1_cl_2:
"cluster  non emptyXBOOLE-0V1\<bar>Tree-likeTREES-1V1 for setHIDDENM2"
proof
(*existence*)
  show " ex it be setHIDDENM2 st it be  non emptyXBOOLE-0V1\<bar>Tree-likeTREES-1V1"
sorry
qed "sorry"

syntax TREES_1M1 :: "Ty" ("TreeTREES-1M1" 70)
translations "TreeTREES-1M1" \<rightharpoonup> "Tree-likeTREES-1V1\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2"

reserve T, T1 for "TreeTREES-1M1"
mtheorem trees_1_th_19:
" for x be setHIDDENM2 holds  for T be TreeTREES-1M1 holds x inTARSKIR2 T implies x be FinSequenceFINSEQ-1M3-of NATNUMBERSK1"
sorry

abbreviation(input) TREES_1M2("ElementTREES-1M2-of  _ " [70]70) where
  "ElementTREES-1M2-of T \<equiv> ElementSUBSET-1M1-of T"

mtheorem trees_1_add_1:
  mlet "T be TreeTREES-1M1"
"cluster note-that FinSequenceFINSEQ-1M3-of NATNUMBERSK1 for ElementSUBSET-1M1-of T"
proof
(*coherence*)
  show " for it be ElementSUBSET-1M1-of T holds it be FinSequenceFINSEQ-1M3-of NATNUMBERSK1"
    using trees_1_th_19 sorry
qed "sorry"

mtheorem trees_1_th_20:
" for T be TreeTREES-1M1 holds  for p be FinSequenceFINSEQ-1M1 holds  for q be FinSequenceFINSEQ-1M1 holds p inTARSKIR2 T & q is-a-prefix-ofTREES-1R2 p implies q inTARSKIR2 T"
sorry

mtheorem trees_1_th_21:
" for q be FinSequenceFINSEQ-1M3-of NATNUMBERSK1 holds  for T be TreeTREES-1M1 holds  for r be FinSequenceFINSEQ-1M1 holds q ^FINSEQ-1K8 r inTARSKIR2 T implies q inTARSKIR2 T"
sorry

mtheorem trees_1_th_22:
" for T be TreeTREES-1M1 holds {}XBOOLE-0K1 inTARSKIR2 T & <*>FINSEQ-1K7 NATNUMBERSK1 inTARSKIR2 T"
sorry

mtheorem trees_1_th_23:
"{TARSKIK1 {}XBOOLE-0K1 } be TreeTREES-1M1"
   sorry

mtheorem trees_1_cl_3:
  mlet "T be TreeTREES-1M1", "T1 be TreeTREES-1M1"
"cluster T \\/XBOOLE-0K2 T1 as-term-is Tree-likeTREES-1V1"
proof
(*coherence*)
  show "T \\/XBOOLE-0K2 T1 be Tree-likeTREES-1V1"
sorry
qed "sorry"

mtheorem trees_1_cl_4:
  mlet "T be TreeTREES-1M1", "T1 be TreeTREES-1M1"
"cluster T /\\XBOOLE-0K3 T1 as-term-is Tree-likeTREES-1V1\<bar> non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "T /\\XBOOLE-0K3 T1 be Tree-likeTREES-1V1\<bar> non emptyXBOOLE-0V1"
sorry
qed "sorry"

mtheorem trees_1_th_24:
" for T be TreeTREES-1M1 holds  for T1 be TreeTREES-1M1 holds T \\/XBOOLE-0K2 T1 be TreeTREES-1M1"
   sorry

mtheorem trees_1_th_25:
" for T be TreeTREES-1M1 holds  for T1 be TreeTREES-1M1 holds T /\\XBOOLE-0K3 T1 be TreeTREES-1M1"
   sorry

mtheorem trees_1_cl_5:
"cluster finiteFINSET-1V1 for TreeTREES-1M1"
proof
(*existence*)
  show " ex it be TreeTREES-1M1 st it be finiteFINSET-1V1"
sorry
qed "sorry"

reserve fT, fT1 for "finiteFINSET-1V1\<bar>TreeTREES-1M1"
mtheorem trees_1_th_26:
" for fT be finiteFINSET-1V1\<bar>TreeTREES-1M1 holds  for fT1 be finiteFINSET-1V1\<bar>TreeTREES-1M1 holds fT \\/XBOOLE-0K2 fT1 be finiteFINSET-1V1\<bar>TreeTREES-1M1"
   sorry

mtheorem trees_1_th_27:
" for T be TreeTREES-1M1 holds  for fT be finiteFINSET-1V1\<bar>TreeTREES-1M1 holds fT /\\XBOOLE-0K3 T be finiteFINSET-1V1\<bar>TreeTREES-1M1"
   sorry

mdef trees_1_def_4 ("elementary-treeTREES-1K2  _ " [228]228 ) where
  mlet "n be NatNAT-1M1"
"func elementary-treeTREES-1K2 n \<rightarrow> TreeTREES-1M1 equals
  ({<*FINSEQ-1K10 k*> where k be NatNAT-1M1 : k <XXREAL-0R3 n })\\/XBOOLE-0K2 {TARSKIK1 {}XBOOLE-0K1 }"
proof-
  (*coherence*)
    show "({<*FINSEQ-1K10 k*> where k be NatNAT-1M1 : k <XXREAL-0R3 n })\\/XBOOLE-0K2 {TARSKIK1 {}XBOOLE-0K1 } be TreeTREES-1M1"
sorry
qed "sorry"

mtheorem trees_1_cl_6:
  mlet "n be NatNAT-1M1"
"cluster elementary-treeTREES-1K2 n as-term-is finiteFINSET-1V1"
proof
(*coherence*)
  show "elementary-treeTREES-1K2 n be finiteFINSET-1V1"
sorry
qed "sorry"

mtheorem trees_1_th_28:
" for k be NatNAT-1M1 holds  for n be NatNAT-1M1 holds k <XXREAL-0R3 n implies <*FINSEQ-1K10 k*> inTARSKIR2 elementary-treeTREES-1K2 n"
sorry

mtheorem trees_1_th_29:
"elementary-treeTREES-1K2 (0NUMBERSK6) =XBOOLE-0R4 {TARSKIK1 {}XBOOLE-0K1 }"
sorry

mtheorem trees_1_th_30:
" for n be NatNAT-1M1 holds  for p be FinSequenceFINSEQ-1M3-of NATNUMBERSK1 holds p inTARSKIR2 elementary-treeTREES-1K2 n implies p =FINSEQ-1R1 {}XBOOLE-0K1 or ( ex k be NatNAT-1M1 st k <XXREAL-0R3 n & p =FINSEQ-1R1 <*FINSEQ-1K10 k*>)"
sorry

mdef trees_1_def_5 ("LeavesTREES-1K3  _ " [164]164 ) where
  mlet "T be TreeTREES-1M1"
"func LeavesTREES-1K3 T \<rightarrow> SubsetSUBSET-1M2-of T means
  \<lambda>it.  for p be FinSequenceFINSEQ-1M3-of NATNUMBERSK1 holds p inTARSKIR2 it iff p inTARSKIR2 T &  not ( ex q be FinSequenceFINSEQ-1M3-of NATNUMBERSK1 st q inTARSKIR2 T & p is-a-proper-prefix-ofTREES-1R3 q)"
proof-
  (*existence*)
    show " ex it be SubsetSUBSET-1M2-of T st  for p be FinSequenceFINSEQ-1M3-of NATNUMBERSK1 holds p inTARSKIR2 it iff p inTARSKIR2 T &  not ( ex q be FinSequenceFINSEQ-1M3-of NATNUMBERSK1 st q inTARSKIR2 T & p is-a-proper-prefix-ofTREES-1R3 q)"
sorry
  (*uniqueness*)
    show " for it1 be SubsetSUBSET-1M2-of T holds  for it2 be SubsetSUBSET-1M2-of T holds ( for p be FinSequenceFINSEQ-1M3-of NATNUMBERSK1 holds p inTARSKIR2 it1 iff p inTARSKIR2 T &  not ( ex q be FinSequenceFINSEQ-1M3-of NATNUMBERSK1 st q inTARSKIR2 T & p is-a-proper-prefix-ofTREES-1R3 q)) & ( for p be FinSequenceFINSEQ-1M3-of NATNUMBERSK1 holds p inTARSKIR2 it2 iff p inTARSKIR2 T &  not ( ex q be FinSequenceFINSEQ-1M3-of NATNUMBERSK1 st q inTARSKIR2 T & p is-a-proper-prefix-ofTREES-1R3 q)) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mdef trees_1_def_6 (" _ |TREES-1K4  _ " [200,200]200 ) where
  mlet "T be TreeTREES-1M1", "p be FinSequenceFINSEQ-1M3-of NATNUMBERSK1"
"assume p inTARSKIR2 T func T |TREES-1K4 p \<rightarrow> TreeTREES-1M1 means
  \<lambda>it.  for q be FinSequenceFINSEQ-1M3-of NATNUMBERSK1 holds q inTARSKIR2 it iff p ^FINSEQ-1K9\<^bsub>(NATNUMBERSK1)\<^esub> q inTARSKIR2 T"
proof-
  (*existence*)
    show "p inTARSKIR2 T implies ( ex it be TreeTREES-1M1 st  for q be FinSequenceFINSEQ-1M3-of NATNUMBERSK1 holds q inTARSKIR2 it iff p ^FINSEQ-1K9\<^bsub>(NATNUMBERSK1)\<^esub> q inTARSKIR2 T)"
sorry
  (*uniqueness*)
    show "p inTARSKIR2 T implies ( for it1 be TreeTREES-1M1 holds  for it2 be TreeTREES-1M1 holds ( for q be FinSequenceFINSEQ-1M3-of NATNUMBERSK1 holds q inTARSKIR2 it1 iff p ^FINSEQ-1K9\<^bsub>(NATNUMBERSK1)\<^esub> q inTARSKIR2 T) & ( for q be FinSequenceFINSEQ-1M3-of NATNUMBERSK1 holds q inTARSKIR2 it2 iff p ^FINSEQ-1K9\<^bsub>(NATNUMBERSK1)\<^esub> q inTARSKIR2 T) implies it1 =HIDDENR1 it2)"
sorry
qed "sorry"

mtheorem trees_1_th_31:
" for T be TreeTREES-1M1 holds T |TREES-1K4 <*>FINSEQ-1K7 NATNUMBERSK1 =XBOOLE-0R4 T"
sorry

mtheorem trees_1_cl_7:
  mlet "T be finiteFINSET-1V1\<bar>TreeTREES-1M1", "p be ElementTREES-1M2-of T"
"cluster T |TREES-1K4 p as-term-is finiteFINSET-1V1"
proof
(*coherence*)
  show "T |TREES-1K4 p be finiteFINSET-1V1"
sorry
qed "sorry"

mdef trees_1_def_7 ("LeafTREES-1M3-of  _ " [70]70 ) where
  mlet "T be TreeTREES-1M1"
"assume LeavesTREES-1K3 T <>HIDDENR2 {}XBOOLE-0K1 mode LeafTREES-1M3-of T \<rightarrow> ElementTREES-1M2-of T means
  (\<lambda>it. it inTARSKIR2 LeavesTREES-1K3 T)"
proof-
  (*existence*)
    show "LeavesTREES-1K3 T <>HIDDENR2 {}XBOOLE-0K1 implies ( ex it be ElementTREES-1M2-of T st it inTARSKIR2 LeavesTREES-1K3 T)"
sorry
qed "sorry"

mdef trees_1_def_8 ("SubtreeTREES-1M4-of  _ " [70]70 ) where
  mlet "T be TreeTREES-1M1"
"mode SubtreeTREES-1M4-of T \<rightarrow> TreeTREES-1M1 means
  (\<lambda>it.  ex p be ElementTREES-1M2-of T st it =XBOOLE-0R4 T |TREES-1K4 p)"
proof-
  (*existence*)
    show " ex it be TreeTREES-1M1 st  ex p be ElementTREES-1M2-of T st it =XBOOLE-0R4 T |TREES-1K4 p"
sorry
qed "sorry"

reserve t for "ElementTREES-1M2-of T"
mdef trees_1_def_9 (" _ with-replacementTREES-1K5'( _ , _ ')" [164,0,0]164 ) where
  mlet "T be TreeTREES-1M1", "p be FinSequenceFINSEQ-1M3-of NATNUMBERSK1", "T1 be TreeTREES-1M1"
"assume p inTARSKIR2 T func T with-replacementTREES-1K5(p,T1) \<rightarrow> TreeTREES-1M1 means
  \<lambda>it.  for q be FinSequenceFINSEQ-1M3-of NATNUMBERSK1 holds q inTARSKIR2 it iff q inTARSKIR2 T &  not p is-a-proper-prefix-ofTREES-1R3 q or ( ex r be FinSequenceFINSEQ-1M3-of NATNUMBERSK1 st r inTARSKIR2 T1 & q =FINSEQ-1R1 p ^FINSEQ-1K9\<^bsub>(NATNUMBERSK1)\<^esub> r)"
proof-
  (*existence*)
    show "p inTARSKIR2 T implies ( ex it be TreeTREES-1M1 st  for q be FinSequenceFINSEQ-1M3-of NATNUMBERSK1 holds q inTARSKIR2 it iff q inTARSKIR2 T &  not p is-a-proper-prefix-ofTREES-1R3 q or ( ex r be FinSequenceFINSEQ-1M3-of NATNUMBERSK1 st r inTARSKIR2 T1 & q =FINSEQ-1R1 p ^FINSEQ-1K9\<^bsub>(NATNUMBERSK1)\<^esub> r))"
sorry
  (*uniqueness*)
    show "p inTARSKIR2 T implies ( for it1 be TreeTREES-1M1 holds  for it2 be TreeTREES-1M1 holds ( for q be FinSequenceFINSEQ-1M3-of NATNUMBERSK1 holds q inTARSKIR2 it1 iff q inTARSKIR2 T &  not p is-a-proper-prefix-ofTREES-1R3 q or ( ex r be FinSequenceFINSEQ-1M3-of NATNUMBERSK1 st r inTARSKIR2 T1 & q =FINSEQ-1R1 p ^FINSEQ-1K9\<^bsub>(NATNUMBERSK1)\<^esub> r)) & ( for q be FinSequenceFINSEQ-1M3-of NATNUMBERSK1 holds q inTARSKIR2 it2 iff q inTARSKIR2 T &  not p is-a-proper-prefix-ofTREES-1R3 q or ( ex r be FinSequenceFINSEQ-1M3-of NATNUMBERSK1 st r inTARSKIR2 T1 & q =FINSEQ-1R1 p ^FINSEQ-1K9\<^bsub>(NATNUMBERSK1)\<^esub> r)) implies it1 =HIDDENR1 it2)"
sorry
qed "sorry"

mtheorem trees_1_th_32:
" for p be FinSequenceFINSEQ-1M3-of NATNUMBERSK1 holds  for T be TreeTREES-1M1 holds  for T1 be TreeTREES-1M1 holds p inTARSKIR2 T implies T with-replacementTREES-1K5(p,T1) =XBOOLE-0R4 ({t1 where t1 be ElementTREES-1M2-of T :  not p is-a-proper-prefix-ofTREES-1R3 t1 })\\/XBOOLE-0K2 ({p ^FINSEQ-1K9\<^bsub>(NATNUMBERSK1)\<^esub> s where s be ElementTREES-1M2-of T1 :  True  })"
sorry

mtheorem trees_1_th_33:
" for p be FinSequenceFINSEQ-1M3-of NATNUMBERSK1 holds  for T be TreeTREES-1M1 holds  for T1 be TreeTREES-1M1 holds p inTARSKIR2 T implies T1 =XBOOLE-0R4 (T with-replacementTREES-1K5(p,T1))|TREES-1K4 p"
sorry

mtheorem trees_1_cl_8:
  mlet "T be finiteFINSET-1V1\<bar>TreeTREES-1M1", "t be ElementTREES-1M2-of T", "T1 be finiteFINSET-1V1\<bar>TreeTREES-1M1"
"cluster T with-replacementTREES-1K5(t,T1) as-term-is finiteFINSET-1V1"
proof
(*coherence*)
  show "T with-replacementTREES-1K5(t,T1) be finiteFINSET-1V1"
sorry
qed "sorry"

reserve w for "FinSequenceFINSEQ-1M1"
mtheorem trees_1_th_34:
" for p be FinSequenceFINSEQ-1M1 holds (ProperPrefixesTREES-1K1 p,domFINSEQ-1K5 p)are-equipotentTARSKIR3"
sorry

mtheorem trees_1_cl_9:
  mlet "p be FinSequenceFINSEQ-1M1"
"cluster ProperPrefixesTREES-1K1 p as-term-is finiteFINSET-1V1"
proof
(*coherence*)
  show "ProperPrefixesTREES-1K1 p be finiteFINSET-1V1"
sorry
qed "sorry"

mtheorem trees_1_th_35:
" for p be FinSequenceFINSEQ-1M1 holds cardCARD-1K4 (ProperPrefixesTREES-1K1 p) =XBOOLE-0R4 lenFINSEQ-1K4 p"
sorry

mdef trees_1_def_10 ("AntiChain-of-Prefixes-likeTREES-1V2" 70 ) where
"attr AntiChain-of-Prefixes-likeTREES-1V2 for setHIDDENM2 means
  (\<lambda>IT. ( for x be setHIDDENM2 holds x inTARSKIR2 IT implies x be FinSequenceFINSEQ-1M1) & ( for p1 be FinSequenceFINSEQ-1M1 holds  for p2 be FinSequenceFINSEQ-1M1 holds (p1 inTARSKIR2 IT & p2 inTARSKIR2 IT) & p1 <>HIDDENR2 p2 implies  not (p1,p2)are-c=-comparableXBOOLE-0R3))"..

mtheorem trees_1_cl_10:
"cluster AntiChain-of-Prefixes-likeTREES-1V2 for setHIDDENM2"
proof
(*existence*)
  show " ex it be setHIDDENM2 st it be AntiChain-of-Prefixes-likeTREES-1V2"
sorry
qed "sorry"

syntax TREES_1M5 :: "Ty" ("AntiChain-of-PrefixesTREES-1M5" 70)
translations "AntiChain-of-PrefixesTREES-1M5" \<rightharpoonup> "AntiChain-of-Prefixes-likeTREES-1V2\<bar>setHIDDENM2"

mtheorem trees_1_th_36:
" for w be FinSequenceFINSEQ-1M1 holds {TARSKIK1 w} be AntiChain-of-Prefixes-likeTREES-1V2"
sorry

mtheorem trees_1_th_37:
" for p1 be FinSequenceFINSEQ-1M1 holds  for p2 be FinSequenceFINSEQ-1M1 holds  not (p1,p2)are-c=-comparableXBOOLE-0R3 implies {TARSKIK2 p1,p2 } be AntiChain-of-Prefixes-likeTREES-1V2"
sorry

mdef trees_1_def_11 ("AntiChain-of-PrefixesTREES-1M6-of  _ " [70]70 ) where
  mlet "T be TreeTREES-1M1"
"mode AntiChain-of-PrefixesTREES-1M6-of T \<rightarrow> AntiChain-of-PrefixesTREES-1M5 means
  (\<lambda>it. it c=TARSKIR1 T)"
proof-
  (*existence*)
    show " ex it be AntiChain-of-PrefixesTREES-1M5 st it c=TARSKIR1 T"
sorry
qed "sorry"

reserve t1, t2 for "ElementTREES-1M2-of T"
mtheorem trees_1_th_38:
" for T be TreeTREES-1M1 holds {}XBOOLE-0K1 be AntiChain-of-PrefixesTREES-1M6-of T & {TARSKIK1 {}XBOOLE-0K1 } be AntiChain-of-PrefixesTREES-1M6-of T"
sorry

mtheorem trees_1_th_39:
" for T be TreeTREES-1M1 holds  for t be ElementTREES-1M2-of T holds {TARSKIK1 t} be AntiChain-of-PrefixesTREES-1M6-of T"
sorry

mtheorem trees_1_th_40:
" for T be TreeTREES-1M1 holds  for t1 be ElementTREES-1M2-of T holds  for t2 be ElementTREES-1M2-of T holds  not (t1,t2)are-c=-comparableXBOOLE-0R3 implies {TARSKIK2 t1,t2 } be AntiChain-of-PrefixesTREES-1M6-of T"
sorry

mtheorem trees_1_cl_11:
  mlet "T be finiteFINSET-1V1\<bar>TreeTREES-1M1"
"cluster note-that finiteFINSET-1V1 for AntiChain-of-PrefixesTREES-1M6-of T"
proof
(*coherence*)
  show " for it be AntiChain-of-PrefixesTREES-1M6-of T holds it be finiteFINSET-1V1"
sorry
qed "sorry"

mdef trees_1_def_12 ("heightTREES-1K6  _ " [228]228 ) where
  mlet "T be finiteFINSET-1V1\<bar>TreeTREES-1M1"
"func heightTREES-1K6 T \<rightarrow> NatNAT-1M1 means
  \<lambda>it. ( ex p be FinSequenceFINSEQ-1M3-of NATNUMBERSK1 st p inTARSKIR2 T & lenFINSEQ-1K4 p =XBOOLE-0R4 it) & ( for p be FinSequenceFINSEQ-1M3-of NATNUMBERSK1 holds p inTARSKIR2 T implies lenFINSEQ-1K4 p <=XXREAL-0R1 it)"
proof-
  (*existence*)
    show " ex it be NatNAT-1M1 st ( ex p be FinSequenceFINSEQ-1M3-of NATNUMBERSK1 st p inTARSKIR2 T & lenFINSEQ-1K4 p =XBOOLE-0R4 it) & ( for p be FinSequenceFINSEQ-1M3-of NATNUMBERSK1 holds p inTARSKIR2 T implies lenFINSEQ-1K4 p <=XXREAL-0R1 it)"
sorry
  (*uniqueness*)
    show " for it1 be NatNAT-1M1 holds  for it2 be NatNAT-1M1 holds (( ex p be FinSequenceFINSEQ-1M3-of NATNUMBERSK1 st p inTARSKIR2 T & lenFINSEQ-1K4 p =XBOOLE-0R4 it1) & ( for p be FinSequenceFINSEQ-1M3-of NATNUMBERSK1 holds p inTARSKIR2 T implies lenFINSEQ-1K4 p <=XXREAL-0R1 it1)) & (( ex p be FinSequenceFINSEQ-1M3-of NATNUMBERSK1 st p inTARSKIR2 T & lenFINSEQ-1K4 p =XBOOLE-0R4 it2) & ( for p be FinSequenceFINSEQ-1M3-of NATNUMBERSK1 holds p inTARSKIR2 T implies lenFINSEQ-1K4 p <=XXREAL-0R1 it2)) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mdef trees_1_def_13 ("widthTREES-1K7  _ " [228]228 ) where
  mlet "T be finiteFINSET-1V1\<bar>TreeTREES-1M1"
"func widthTREES-1K7 T \<rightarrow> NatNAT-1M1 means
  \<lambda>it.  ex X be AntiChain-of-PrefixesTREES-1M6-of T st it =XBOOLE-0R4 cardCARD-1K4 X & ( for Y be AntiChain-of-PrefixesTREES-1M6-of T holds cardCARD-1K4 Y <=XXREAL-0R1 cardCARD-1K4 X)"
proof-
  (*existence*)
    show " ex it be NatNAT-1M1 st  ex X be AntiChain-of-PrefixesTREES-1M6-of T st it =XBOOLE-0R4 cardCARD-1K4 X & ( for Y be AntiChain-of-PrefixesTREES-1M6-of T holds cardCARD-1K4 Y <=XXREAL-0R1 cardCARD-1K4 X)"
sorry
  (*uniqueness*)
    show " for it1 be NatNAT-1M1 holds  for it2 be NatNAT-1M1 holds ( ex X be AntiChain-of-PrefixesTREES-1M6-of T st it1 =XBOOLE-0R4 cardCARD-1K4 X & ( for Y be AntiChain-of-PrefixesTREES-1M6-of T holds cardCARD-1K4 Y <=XXREAL-0R1 cardCARD-1K4 X)) & ( ex X be AntiChain-of-PrefixesTREES-1M6-of T st it2 =XBOOLE-0R4 cardCARD-1K4 X & ( for Y be AntiChain-of-PrefixesTREES-1M6-of T holds cardCARD-1K4 Y <=XXREAL-0R1 cardCARD-1K4 X)) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mtheorem trees_1_th_41:
" for fT be finiteFINSET-1V1\<bar>TreeTREES-1M1 holds \<one>\<^sub>M <=XXREAL-0R1 widthTREES-1K7 fT"
sorry

mtheorem trees_1_th_42:
"heightTREES-1K6 (elementary-treeTREES-1K2 (0NUMBERSK6)) =XBOOLE-0R4 0NUMBERSK6"
sorry

mtheorem trees_1_th_43:
" for fT be finiteFINSET-1V1\<bar>TreeTREES-1M1 holds heightTREES-1K6 fT =XBOOLE-0R4 0NUMBERSK6 implies fT =XBOOLE-0R4 elementary-treeTREES-1K2 (0NUMBERSK6)"
sorry

mtheorem trees_1_th_44:
" for n be NatNAT-1M1 holds heightTREES-1K6 (elementary-treeTREES-1K2 (n +NAT-1K1 \<one>\<^sub>M)) =XBOOLE-0R4 \<one>\<^sub>M"
sorry

mtheorem trees_1_th_45:
"widthTREES-1K7 (elementary-treeTREES-1K2 (0NUMBERSK6)) =XBOOLE-0R4 \<one>\<^sub>M"
sorry

mtheorem trees_1_th_46:
" for n be NatNAT-1M1 holds widthTREES-1K7 (elementary-treeTREES-1K2 (n +NAT-1K1 \<one>\<^sub>M)) =XBOOLE-0R4 n +NAT-1K1 \<one>\<^sub>M"
sorry

mtheorem trees_1_th_47:
" for fT be finiteFINSET-1V1\<bar>TreeTREES-1M1 holds  for t be ElementTREES-1M2-of fT holds heightTREES-1K6 (fT |TREES-1K4 t) <=XXREAL-0R1 heightTREES-1K6 fT"
sorry

mtheorem trees_1_th_48:
" for fT be finiteFINSET-1V1\<bar>TreeTREES-1M1 holds  for t be ElementTREES-1M2-of fT holds t <>HIDDENR2 {}XBOOLE-0K1 implies heightTREES-1K6 (fT |TREES-1K4 t) <XXREAL-0R3 heightTREES-1K6 fT"
sorry

theorem trees_1_sch_1:
  fixes Pp1 
  assumes
    A1: " for fT be finiteFINSET-1V1\<bar>TreeTREES-1M1 holds ( for n be ElementSUBSET-1M1-of NATNUMBERSK1 holds <*FINSEQ-1K13\<^bsub>(NATNUMBERSK1)\<^esub> n*> inTARSKIR2 fT implies Pp1(fT |TREES-1K4 (<*FINSEQ-1K13\<^bsub>(NATNUMBERSK1)\<^esub> n*>))) implies Pp1(fT)"
  shows " for fT be finiteFINSET-1V1\<bar>TreeTREES-1M1 holds Pp1(fT)"
sorry

(*begin*)
reserve s, t for "FinSequenceFINSEQ-1M1"
mtheorem trees_1_th_49:
" for w be FinSequenceFINSEQ-1M1 holds  for s be FinSequenceFINSEQ-1M1 holds  for t be FinSequenceFINSEQ-1M1 holds w ^FINSEQ-1K8 t is-a-proper-prefix-ofTREES-1R3 w ^FINSEQ-1K8 s implies t is-a-proper-prefix-ofTREES-1R3 s"
sorry

mtheorem trees_1_th_50:
" for n be NatNAT-1M1 holds  for m be NatNAT-1M1 holds  for s be FinSequenceFINSEQ-1M1 holds n <>HIDDENR2 m implies  not <*FINSEQ-1K10 n*> is-a-prefix-ofTREES-1R2 (<*FINSEQ-1K10 m*>)^FINSEQ-1K8 s"
sorry

mtheorem trees_1_th_51:
"elementary-treeTREES-1K2 \<one>\<^sub>M =XBOOLE-0R4 {TARSKIK2 {}XBOOLE-0K1,<*FINSEQ-1K13\<^bsub>(omegaORDINAL1K4)\<^esub> 0NUMBERSK6 *> }"
sorry

mtheorem trees_1_th_52:
" for n be NatNAT-1M1 holds  for m be NatNAT-1M1 holds  not <*FINSEQ-1K10 n*> is-a-proper-prefix-ofTREES-1R3 <*FINSEQ-1K10 m*>"
  using trees_1_th_3 sorry

mtheorem trees_1_th_53:
"elementary-treeTREES-1K2 \<two>\<^sub>M =XBOOLE-0R4 {ENUMSET1K1 {}XBOOLE-0K1,<*FINSEQ-1K13\<^bsub>(omegaORDINAL1K4)\<^esub> 0NUMBERSK6 *>,<*FINSEQ-1K13\<^bsub>(omegaORDINAL1K4)\<^esub> \<one>\<^sub>M*> }"
sorry

mtheorem trees_1_th_54:
" for T be TreeTREES-1M1 holds  for t be ElementTREES-1M2-of T holds t inTARSKIR2 LeavesTREES-1K3 T iff  not t ^FINSEQ-1K9\<^bsub>(omegaORDINAL1K4)\<^esub> (<*FINSEQ-1K13\<^bsub>(omegaORDINAL1K4)\<^esub> 0NUMBERSK6 *>) inTARSKIR2 T"
sorry

mtheorem trees_1_th_55:
" for T be TreeTREES-1M1 holds  for t be ElementTREES-1M2-of T holds t inTARSKIR2 LeavesTREES-1K3 T iff  not ( ex n be NatNAT-1M1 st t ^FINSEQ-1K8 (<*FINSEQ-1K10 n*>) inTARSKIR2 T)"
sorry

mdef trees_1_def_14 ("TrivialInfiniteTreeTREES-1K8" 164 ) where
"func TrivialInfiniteTreeTREES-1K8 \<rightarrow> setHIDDENM2 equals
  {k |->FINSEQ-2K5\<^bsub>(omegaORDINAL1K4)\<^esub> (0NUMBERSK6) where k be NatNAT-1M1 :  True  }"
proof-
  (*coherence*)
    show "{k |->FINSEQ-2K5\<^bsub>(omegaORDINAL1K4)\<^esub> (0NUMBERSK6) where k be NatNAT-1M1 :  True  } be setHIDDENM2"
       sorry
qed "sorry"

mtheorem trees_1_cl_12:
"cluster TrivialInfiniteTreeTREES-1K8 as-term-is  non emptyXBOOLE-0V1\<bar>Tree-likeTREES-1V1"
proof
(*coherence*)
  show "TrivialInfiniteTreeTREES-1K8 be  non emptyXBOOLE-0V1\<bar>Tree-likeTREES-1V1"
sorry
qed "sorry"

mtheorem trees_1_th_56:
"(NATNUMBERSK1,TrivialInfiniteTreeTREES-1K8)are-equipotentTARSKIR3"
sorry

mtheorem trees_1_cl_13:
"cluster TrivialInfiniteTreeTREES-1K8 as-term-is infiniteFINSET-1V2"
proof
(*coherence*)
  show "TrivialInfiniteTreeTREES-1K8 be infiniteFINSET-1V2"
    using trees_1_th_56 card_1_th_38 sorry
qed "sorry"

end
