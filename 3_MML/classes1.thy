theory classes1
  imports funct_2 card_1 xfamily
begin
(*begin*)
reserve W, X, Y, Z for "setHIDDENM2"
reserve f, g for "FunctionFUNCT-1M1"
reserve a, x, y, z for "setHIDDENM2"
mdef classes1_def_1 ("subset-closedCLASSES1V1" 70 ) where
"attr subset-closedCLASSES1V1 for setHIDDENM2 means
  (\<lambda>B.  for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X inTARSKIR2 B & Y c=TARSKIR1 X implies Y inTARSKIR2 B)"..

mdef classes1_def_2 ("TarskiCLASSES1V2" 70 ) where
"attr TarskiCLASSES1V2 for setHIDDENM2 means
  (\<lambda>B. (B be subset-closedCLASSES1V1 & ( for X be setHIDDENM2 holds X inTARSKIR2 B implies boolSETFAM-1K9 X inTARSKIR2 B)) & ( for X be setHIDDENM2 holds X c=TARSKIR1 B implies (X,B)are-equipotentTARSKIR3 or X inTARSKIR2 B))"..

mdef classes1_def_3 (" _ is-Tarski-Class-ofCLASSES1R1  _ " [50,50]50 ) where
  mlet "A be setHIDDENM2", "B be setHIDDENM2"
"pred B is-Tarski-Class-ofCLASSES1R1 A means
  A inTARSKIR2 B & B be TarskiCLASSES1V2"..

mdef classes1_def_4 ("Tarski-ClassCLASSES1K1  _ " [300]300 ) where
  mlet "A be setHIDDENM2"
"func Tarski-ClassCLASSES1K1 A \<rightarrow> setHIDDENM2 means
  \<lambda>it. it is-Tarski-Class-ofCLASSES1R1 A & ( for D be setHIDDENM2 holds D is-Tarski-Class-ofCLASSES1R1 A implies it c=TARSKIR1 D)"
proof-
  (*existence*)
    show " ex it be setHIDDENM2 st it is-Tarski-Class-ofCLASSES1R1 A & ( for D be setHIDDENM2 holds D is-Tarski-Class-ofCLASSES1R1 A implies it c=TARSKIR1 D)"
sorry
  (*uniqueness*)
    show " for it1 be setHIDDENM2 holds  for it2 be setHIDDENM2 holds (it1 is-Tarski-Class-ofCLASSES1R1 A & ( for D be setHIDDENM2 holds D is-Tarski-Class-ofCLASSES1R1 A implies it1 c=TARSKIR1 D)) & (it2 is-Tarski-Class-ofCLASSES1R1 A & ( for D be setHIDDENM2 holds D is-Tarski-Class-ofCLASSES1R1 A implies it2 c=TARSKIR1 D)) implies it1 =HIDDENR1 it2"
       sorry
qed "sorry"

mtheorem classes1_cl_1:
  mlet "A be setHIDDENM2"
"cluster Tarski-ClassCLASSES1K1 A as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "Tarski-ClassCLASSES1K1 A be  non emptyXBOOLE-0V1"
sorry
qed "sorry"

mtheorem classes1_th_1:
" for W be setHIDDENM2 holds W be TarskiCLASSES1V2 iff (W be subset-closedCLASSES1V1 & ( for X be setHIDDENM2 holds X inTARSKIR2 W implies boolSETFAM-1K9 X inTARSKIR2 W)) & ( for X be setHIDDENM2 holds X c=TARSKIR1 W & cardCARD-1K1 X inTARSKIR2 cardCARD-1K1 W implies X inTARSKIR2 W)"
sorry

mtheorem classes1_th_2:
" for X be setHIDDENM2 holds X inTARSKIR2 Tarski-ClassCLASSES1K1 X"
sorry

mtheorem classes1_th_3:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds Y inTARSKIR2 Tarski-ClassCLASSES1K1 X & Z c=TARSKIR1 Y implies Z inTARSKIR2 Tarski-ClassCLASSES1K1 X"
sorry

mtheorem classes1_th_4:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds Y inTARSKIR2 Tarski-ClassCLASSES1K1 X implies boolSETFAM-1K9 Y inTARSKIR2 Tarski-ClassCLASSES1K1 X"
sorry

mtheorem classes1_th_5:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds Y c=TARSKIR1 Tarski-ClassCLASSES1K1 X implies (Y,Tarski-ClassCLASSES1K1 X)are-equipotentTARSKIR3 or Y inTARSKIR2 Tarski-ClassCLASSES1K1 X"
sorry

mtheorem classes1_th_6:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds Y c=TARSKIR1 Tarski-ClassCLASSES1K1 X & cardCARD-1K1 Y inTARSKIR2 cardCARD-1K1 Tarski-ClassCLASSES1K1 X implies Y inTARSKIR2 Tarski-ClassCLASSES1K1 X"
sorry

reserve u, v for "ElementSUBSET-1M1-of Tarski-ClassCLASSES1K1 X"
reserve A, B, C for "OrdinalORDINAL1M3"
reserve L for "SequenceORDINAL1M4"
mdef classes1_def_5 ("Tarski-ClassCLASSES1K2'( _ , _ ')" [0,0]300 ) where
  mlet "X be setHIDDENM2", "A be OrdinalORDINAL1M3"
"func Tarski-ClassCLASSES1K2(X,A) \<rightarrow> setHIDDENM2 means
  \<lambda>it.  ex L be SequenceORDINAL1M4 st (((it =XBOOLE-0R4 lastORDINAL2K1 L & domRELAT-1K1 L =XBOOLE-0R4 succORDINAL1K1 A) & L .FUNCT-1K1 (0ORDINAL1K5) =XBOOLE-0R4 {TARSKIK1 X}) & ( for C be OrdinalORDINAL1M3 holds succORDINAL1K1 C inTARSKIR2 succORDINAL1K1 A implies L .FUNCT-1K1 succORDINAL1K1 C =XBOOLE-0R4 (({u where u be ElementSUBSET-1M1-of Tarski-ClassCLASSES1K1 X :  ex v be ElementSUBSET-1M1-of Tarski-ClassCLASSES1K1 X st v inTARSKIR2 L .FUNCT-1K1 C & u c=TARSKIR1 v })\\/XBOOLE-0K2 ({boolSETFAM-1K9 v where v be ElementSUBSET-1M1-of Tarski-ClassCLASSES1K1 X : v inTARSKIR2 L .FUNCT-1K1 C }))\\/XBOOLE-0K2 boolSETFAM-1K9 (L .FUNCT-1K1 C) /\\SUBSET-1K8\<^bsub>(boolZFMISC-1K1 (L .FUNCT-1K1 C))\<^esub> Tarski-ClassCLASSES1K1 X)) & ( for C be OrdinalORDINAL1M3 holds (C inTARSKIR2 succORDINAL1K1 A & C <>HIDDENR2 0ORDINAL1K5) & C be limit-ordinalORDINAL1V4 implies L .FUNCT-1K1 C =XBOOLE-0R4 unionTARSKIK3 (rngFUNCT-1K2 (L |RELAT-1K8 C)) /\\XBOOLE-0K3 Tarski-ClassCLASSES1K1 X)"
proof-
  (*existence*)
    show " ex it be setHIDDENM2 st  ex L be SequenceORDINAL1M4 st (((it =XBOOLE-0R4 lastORDINAL2K1 L & domRELAT-1K1 L =XBOOLE-0R4 succORDINAL1K1 A) & L .FUNCT-1K1 (0ORDINAL1K5) =XBOOLE-0R4 {TARSKIK1 X}) & ( for C be OrdinalORDINAL1M3 holds succORDINAL1K1 C inTARSKIR2 succORDINAL1K1 A implies L .FUNCT-1K1 succORDINAL1K1 C =XBOOLE-0R4 (({u where u be ElementSUBSET-1M1-of Tarski-ClassCLASSES1K1 X :  ex v be ElementSUBSET-1M1-of Tarski-ClassCLASSES1K1 X st v inTARSKIR2 L .FUNCT-1K1 C & u c=TARSKIR1 v })\\/XBOOLE-0K2 ({boolSETFAM-1K9 v where v be ElementSUBSET-1M1-of Tarski-ClassCLASSES1K1 X : v inTARSKIR2 L .FUNCT-1K1 C }))\\/XBOOLE-0K2 boolSETFAM-1K9 (L .FUNCT-1K1 C) /\\SUBSET-1K8\<^bsub>(boolZFMISC-1K1 (L .FUNCT-1K1 C))\<^esub> Tarski-ClassCLASSES1K1 X)) & ( for C be OrdinalORDINAL1M3 holds (C inTARSKIR2 succORDINAL1K1 A & C <>HIDDENR2 0ORDINAL1K5) & C be limit-ordinalORDINAL1V4 implies L .FUNCT-1K1 C =XBOOLE-0R4 unionTARSKIK3 (rngFUNCT-1K2 (L |RELAT-1K8 C)) /\\XBOOLE-0K3 Tarski-ClassCLASSES1K1 X)"
sorry
  (*uniqueness*)
    show " for it1 be setHIDDENM2 holds  for it2 be setHIDDENM2 holds ( ex L be SequenceORDINAL1M4 st (((it1 =XBOOLE-0R4 lastORDINAL2K1 L & domRELAT-1K1 L =XBOOLE-0R4 succORDINAL1K1 A) & L .FUNCT-1K1 (0ORDINAL1K5) =XBOOLE-0R4 {TARSKIK1 X}) & ( for C be OrdinalORDINAL1M3 holds succORDINAL1K1 C inTARSKIR2 succORDINAL1K1 A implies L .FUNCT-1K1 succORDINAL1K1 C =XBOOLE-0R4 (({u where u be ElementSUBSET-1M1-of Tarski-ClassCLASSES1K1 X :  ex v be ElementSUBSET-1M1-of Tarski-ClassCLASSES1K1 X st v inTARSKIR2 L .FUNCT-1K1 C & u c=TARSKIR1 v })\\/XBOOLE-0K2 ({boolSETFAM-1K9 v where v be ElementSUBSET-1M1-of Tarski-ClassCLASSES1K1 X : v inTARSKIR2 L .FUNCT-1K1 C }))\\/XBOOLE-0K2 boolSETFAM-1K9 (L .FUNCT-1K1 C) /\\SUBSET-1K8\<^bsub>(boolZFMISC-1K1 (L .FUNCT-1K1 C))\<^esub> Tarski-ClassCLASSES1K1 X)) & ( for C be OrdinalORDINAL1M3 holds (C inTARSKIR2 succORDINAL1K1 A & C <>HIDDENR2 0ORDINAL1K5) & C be limit-ordinalORDINAL1V4 implies L .FUNCT-1K1 C =XBOOLE-0R4 unionTARSKIK3 (rngFUNCT-1K2 (L |RELAT-1K8 C)) /\\XBOOLE-0K3 Tarski-ClassCLASSES1K1 X)) & ( ex L be SequenceORDINAL1M4 st (((it2 =XBOOLE-0R4 lastORDINAL2K1 L & domRELAT-1K1 L =XBOOLE-0R4 succORDINAL1K1 A) & L .FUNCT-1K1 (0ORDINAL1K5) =XBOOLE-0R4 {TARSKIK1 X}) & ( for C be OrdinalORDINAL1M3 holds succORDINAL1K1 C inTARSKIR2 succORDINAL1K1 A implies L .FUNCT-1K1 succORDINAL1K1 C =XBOOLE-0R4 (({u where u be ElementSUBSET-1M1-of Tarski-ClassCLASSES1K1 X :  ex v be ElementSUBSET-1M1-of Tarski-ClassCLASSES1K1 X st v inTARSKIR2 L .FUNCT-1K1 C & u c=TARSKIR1 v })\\/XBOOLE-0K2 ({boolSETFAM-1K9 v where v be ElementSUBSET-1M1-of Tarski-ClassCLASSES1K1 X : v inTARSKIR2 L .FUNCT-1K1 C }))\\/XBOOLE-0K2 boolSETFAM-1K9 (L .FUNCT-1K1 C) /\\SUBSET-1K8\<^bsub>(boolZFMISC-1K1 (L .FUNCT-1K1 C))\<^esub> Tarski-ClassCLASSES1K1 X)) & ( for C be OrdinalORDINAL1M3 holds (C inTARSKIR2 succORDINAL1K1 A & C <>HIDDENR2 0ORDINAL1K5) & C be limit-ordinalORDINAL1V4 implies L .FUNCT-1K1 C =XBOOLE-0R4 unionTARSKIK3 (rngFUNCT-1K2 (L |RELAT-1K8 C)) /\\XBOOLE-0K3 Tarski-ClassCLASSES1K1 X)) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mlemma classes1_lm_1:
" for X be setHIDDENM2 holds Tarski-ClassCLASSES1K2(X,0ORDINAL1K5) =XBOOLE-0R4 {TARSKIK1 X} & (( for A be OrdinalORDINAL1M3 holds Tarski-ClassCLASSES1K2(X,succORDINAL1K1 A) =XBOOLE-0R4 (({uc where uc be ElementSUBSET-1M1-of Tarski-ClassCLASSES1K1 X :  ex vc be ElementSUBSET-1M1-of Tarski-ClassCLASSES1K1 X st vc inTARSKIR2 Tarski-ClassCLASSES1K2(X,A) & uc c=TARSKIR1 vc })\\/XBOOLE-0K2 ({boolSETFAM-1K9 vc where vc be ElementSUBSET-1M1-of Tarski-ClassCLASSES1K1 X : vc inTARSKIR2 Tarski-ClassCLASSES1K2(X,A) }))\\/XBOOLE-0K2 boolSETFAM-1K9 Tarski-ClassCLASSES1K2(X,A) /\\SUBSET-1K8\<^bsub>(boolZFMISC-1K1 Tarski-ClassCLASSES1K2(X,A))\<^esub> Tarski-ClassCLASSES1K1 X) & ( for A be OrdinalORDINAL1M3 holds  for L be SequenceORDINAL1M4 holds ((A <>HIDDENR2 0ORDINAL1K5 & A be limit-ordinalORDINAL1V4) & domRELAT-1K1 L =XBOOLE-0R4 A) & ( for B be OrdinalORDINAL1M3 holds B inTARSKIR2 A implies L .FUNCT-1K1 B =XBOOLE-0R4 Tarski-ClassCLASSES1K2(X,B)) implies Tarski-ClassCLASSES1K2(X,A) =XBOOLE-0R4 unionTARSKIK3 (rngFUNCT-1K2 L) /\\XBOOLE-0K3 Tarski-ClassCLASSES1K1 X))"
sorry

abbreviation(input) CLASSES1K3("Tarski-ClassCLASSES1K3'( _ , _ ')" [0,0]300) where
  "Tarski-ClassCLASSES1K3(X,A) \<equiv> Tarski-ClassCLASSES1K2(X,A)"

mtheorem classes1_add_1:
  mlet "X be setHIDDENM2", "A be OrdinalORDINAL1M3"
"cluster Tarski-ClassCLASSES1K2(X,A) as-term-is SubsetSUBSET-1M2-of Tarski-ClassCLASSES1K1 X"
proof
(*coherence*)
  show "Tarski-ClassCLASSES1K2(X,A) be SubsetSUBSET-1M2-of Tarski-ClassCLASSES1K1 X"
sorry
qed "sorry"

mtheorem classes1_th_7:
" for X be setHIDDENM2 holds Tarski-ClassCLASSES1K3(X,{}XBOOLE-0K1) =XBOOLE-0R4 {TARSKIK1 X}"
  using classes1_lm_1 sorry

mtheorem classes1_th_8:
" for X be setHIDDENM2 holds  for A be OrdinalORDINAL1M3 holds Tarski-ClassCLASSES1K3(X,succORDINAL1K1 A) =XBOOLE-0R4 (({u where u be ElementSUBSET-1M1-of Tarski-ClassCLASSES1K1 X :  ex v be ElementSUBSET-1M1-of Tarski-ClassCLASSES1K1 X st v inTARSKIR2 Tarski-ClassCLASSES1K3(X,A) & u c=TARSKIR1 v })\\/XBOOLE-0K2 ({boolSETFAM-1K9 v where v be ElementSUBSET-1M1-of Tarski-ClassCLASSES1K1 X : v inTARSKIR2 Tarski-ClassCLASSES1K3(X,A) }))\\/XBOOLE-0K2 boolSETFAM-1K9 Tarski-ClassCLASSES1K3(X,A) /\\SUBSET-1K8\<^bsub>(boolZFMISC-1K1 Tarski-ClassCLASSES1K3(X,A))\<^esub> Tarski-ClassCLASSES1K1 X"
  using classes1_lm_1 sorry

mtheorem classes1_th_9:
" for X be setHIDDENM2 holds  for A be OrdinalORDINAL1M3 holds A <>HIDDENR2 {}XBOOLE-0K1 & A be limit-ordinalORDINAL1V4 implies Tarski-ClassCLASSES1K3(X,A) =XBOOLE-0R4 {u where u be ElementSUBSET-1M1-of Tarski-ClassCLASSES1K1 X :  ex B be OrdinalORDINAL1M3 st B inTARSKIR2 A & u inTARSKIR2 Tarski-ClassCLASSES1K3(X,B) }"
sorry

mtheorem classes1_th_10:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for A be OrdinalORDINAL1M3 holds Y inTARSKIR2 Tarski-ClassCLASSES1K3(X,succORDINAL1K1 A) iff Y c=TARSKIR1 Tarski-ClassCLASSES1K3(X,A) & Y inTARSKIR2 Tarski-ClassCLASSES1K1 X or ( ex Z be setHIDDENM2 st Z inTARSKIR2 Tarski-ClassCLASSES1K3(X,A) & (Y c=TARSKIR1 Z or Y =XBOOLE-0R4 boolSETFAM-1K9 Z))"
sorry

mtheorem classes1_th_11:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds  for A be OrdinalORDINAL1M3 holds Y c=TARSKIR1 Z & Z inTARSKIR2 Tarski-ClassCLASSES1K3(X,A) implies Y inTARSKIR2 Tarski-ClassCLASSES1K3(X,succORDINAL1K1 A)"
  using classes1_th_10 sorry

mtheorem classes1_th_12:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for A be OrdinalORDINAL1M3 holds Y inTARSKIR2 Tarski-ClassCLASSES1K3(X,A) implies boolSETFAM-1K9 Y inTARSKIR2 Tarski-ClassCLASSES1K3(X,succORDINAL1K1 A)"
  using classes1_th_10 sorry

mtheorem classes1_th_13:
" for X be setHIDDENM2 holds  for x be setHIDDENM2 holds  for A be OrdinalORDINAL1M3 holds A <>HIDDENR2 {}XBOOLE-0K1 & A be limit-ordinalORDINAL1V4 implies (x inTARSKIR2 Tarski-ClassCLASSES1K3(X,A) iff ( ex B be OrdinalORDINAL1M3 st B inTARSKIR2 A & x inTARSKIR2 Tarski-ClassCLASSES1K3(X,B)))"
sorry

mtheorem classes1_th_14:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds  for A be OrdinalORDINAL1M3 holds ((A <>HIDDENR2 {}XBOOLE-0K1 & A be limit-ordinalORDINAL1V4) & Y inTARSKIR2 Tarski-ClassCLASSES1K3(X,A)) & (Z c=TARSKIR1 Y or Z =XBOOLE-0R4 boolSETFAM-1K9 Y) implies Z inTARSKIR2 Tarski-ClassCLASSES1K3(X,A)"
sorry

mtheorem classes1_th_15:
" for X be setHIDDENM2 holds  for A be OrdinalORDINAL1M3 holds Tarski-ClassCLASSES1K3(X,A) c=TARSKIR1 Tarski-ClassCLASSES1K3(X,succORDINAL1K1 A)"
sorry

mtheorem classes1_th_16:
" for X be setHIDDENM2 holds  for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds A c=ORDINAL1R1 B implies Tarski-ClassCLASSES1K3(X,A) c=TARSKIR1 Tarski-ClassCLASSES1K3(X,B)"
sorry

mtheorem classes1_th_17:
" for X be setHIDDENM2 holds  ex A be OrdinalORDINAL1M3 st Tarski-ClassCLASSES1K3(X,A) =XBOOLE-0R4 Tarski-ClassCLASSES1K3(X,succORDINAL1K1 A)"
sorry

mtheorem classes1_th_18:
" for X be setHIDDENM2 holds  for A be OrdinalORDINAL1M3 holds Tarski-ClassCLASSES1K3(X,A) =XBOOLE-0R4 Tarski-ClassCLASSES1K3(X,succORDINAL1K1 A) implies Tarski-ClassCLASSES1K3(X,A) =XBOOLE-0R4 Tarski-ClassCLASSES1K1 X"
sorry

mtheorem classes1_th_19:
" for X be setHIDDENM2 holds  ex A be OrdinalORDINAL1M3 st Tarski-ClassCLASSES1K3(X,A) =XBOOLE-0R4 Tarski-ClassCLASSES1K1 X"
sorry

mtheorem classes1_th_20:
" for X be setHIDDENM2 holds  ex A be OrdinalORDINAL1M3 st Tarski-ClassCLASSES1K3(X,A) =XBOOLE-0R4 Tarski-ClassCLASSES1K1 X & ( for B be OrdinalORDINAL1M3 holds B inTARSKIR2 A implies Tarski-ClassCLASSES1K3(X,B) <>HIDDENR2 Tarski-ClassCLASSES1K1 X)"
sorry

mtheorem classes1_th_21:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds Y <>HIDDENR2 X & Y inTARSKIR2 Tarski-ClassCLASSES1K1 X implies ( ex A be OrdinalORDINAL1M3 st  not Y inTARSKIR2 Tarski-ClassCLASSES1K3(X,A) & Y inTARSKIR2 Tarski-ClassCLASSES1K3(X,succORDINAL1K1 A))"
sorry

mtheorem classes1_th_22:
" for X be setHIDDENM2 holds X be epsilon-transitiveORDINAL1V1 implies ( for A be OrdinalORDINAL1M3 holds A <>HIDDENR2 {}XBOOLE-0K1 implies Tarski-ClassCLASSES1K3(X,A) be epsilon-transitiveORDINAL1V1)"
sorry

mtheorem classes1_th_23:
" for X be setHIDDENM2 holds X be epsilon-transitiveORDINAL1V1 implies Tarski-ClassCLASSES1K1 X be epsilon-transitiveORDINAL1V1"
sorry

mtheorem classes1_th_24:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds Y inTARSKIR2 Tarski-ClassCLASSES1K1 X implies cardCARD-1K1 Y inTARSKIR2 cardCARD-1K1 Tarski-ClassCLASSES1K1 X"
sorry

mtheorem classes1_th_25:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds Y inTARSKIR2 Tarski-ClassCLASSES1K1 X implies  not (Y,Tarski-ClassCLASSES1K1 X)are-equipotentTARSKIR3"
sorry

mtheorem classes1_th_26:
" for X be setHIDDENM2 holds  for x be setHIDDENM2 holds  for y be setHIDDENM2 holds (x inTARSKIR2 Tarski-ClassCLASSES1K1 X implies {TARSKIK1 x} inTARSKIR2 Tarski-ClassCLASSES1K1 X) & (x inTARSKIR2 Tarski-ClassCLASSES1K1 X & y inTARSKIR2 Tarski-ClassCLASSES1K1 X implies {TARSKIK2 x,y } inTARSKIR2 Tarski-ClassCLASSES1K1 X)"
sorry

mtheorem classes1_th_27:
" for X be setHIDDENM2 holds  for x be setHIDDENM2 holds  for y be setHIDDENM2 holds x inTARSKIR2 Tarski-ClassCLASSES1K1 X & y inTARSKIR2 Tarski-ClassCLASSES1K1 X implies [TARSKIK4 x,y ] inHIDDENR3 Tarski-ClassCLASSES1K1 X"
sorry

mtheorem classes1_th_28:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds Y c=TARSKIR1 Tarski-ClassCLASSES1K1 X & Z c=TARSKIR1 Tarski-ClassCLASSES1K1 X implies [:ZFMISC-1K2 Y,Z :] c=RELAT-1R2 Tarski-ClassCLASSES1K1 X"
sorry

mdef classes1_def_6 ("RankCLASSES1K4  _ " [300]300 ) where
  mlet "A be OrdinalORDINAL1M3"
"func RankCLASSES1K4 A \<rightarrow> setHIDDENM2 means
  \<lambda>it.  ex L be SequenceORDINAL1M4 st (((it =XBOOLE-0R4 lastORDINAL2K1 L & domRELAT-1K1 L =XBOOLE-0R4 succORDINAL1K1 A) & L .FUNCT-1K1 (0ORDINAL1K5) =XBOOLE-0R4 {}XBOOLE-0K1) & ( for C be OrdinalORDINAL1M3 holds succORDINAL1K1 C inTARSKIR2 succORDINAL1K1 A implies L .FUNCT-1K1 succORDINAL1K1 C =XBOOLE-0R4 boolSETFAM-1K9 (L .FUNCT-1K1 C))) & ( for C be OrdinalORDINAL1M3 holds (C inTARSKIR2 succORDINAL1K1 A & C <>HIDDENR2 0ORDINAL1K5) & C be limit-ordinalORDINAL1V4 implies L .FUNCT-1K1 C =XBOOLE-0R4 unionTARSKIK3 (rngFUNCT-1K2 (L |RELAT-1K8 C)))"
proof-
  (*existence*)
    show " ex it be setHIDDENM2 st  ex L be SequenceORDINAL1M4 st (((it =XBOOLE-0R4 lastORDINAL2K1 L & domRELAT-1K1 L =XBOOLE-0R4 succORDINAL1K1 A) & L .FUNCT-1K1 (0ORDINAL1K5) =XBOOLE-0R4 {}XBOOLE-0K1) & ( for C be OrdinalORDINAL1M3 holds succORDINAL1K1 C inTARSKIR2 succORDINAL1K1 A implies L .FUNCT-1K1 succORDINAL1K1 C =XBOOLE-0R4 boolSETFAM-1K9 (L .FUNCT-1K1 C))) & ( for C be OrdinalORDINAL1M3 holds (C inTARSKIR2 succORDINAL1K1 A & C <>HIDDENR2 0ORDINAL1K5) & C be limit-ordinalORDINAL1V4 implies L .FUNCT-1K1 C =XBOOLE-0R4 unionTARSKIK3 (rngFUNCT-1K2 (L |RELAT-1K8 C)))"
sorry
  (*uniqueness*)
    show " for it1 be setHIDDENM2 holds  for it2 be setHIDDENM2 holds ( ex L be SequenceORDINAL1M4 st (((it1 =XBOOLE-0R4 lastORDINAL2K1 L & domRELAT-1K1 L =XBOOLE-0R4 succORDINAL1K1 A) & L .FUNCT-1K1 (0ORDINAL1K5) =XBOOLE-0R4 {}XBOOLE-0K1) & ( for C be OrdinalORDINAL1M3 holds succORDINAL1K1 C inTARSKIR2 succORDINAL1K1 A implies L .FUNCT-1K1 succORDINAL1K1 C =XBOOLE-0R4 boolSETFAM-1K9 (L .FUNCT-1K1 C))) & ( for C be OrdinalORDINAL1M3 holds (C inTARSKIR2 succORDINAL1K1 A & C <>HIDDENR2 0ORDINAL1K5) & C be limit-ordinalORDINAL1V4 implies L .FUNCT-1K1 C =XBOOLE-0R4 unionTARSKIK3 (rngFUNCT-1K2 (L |RELAT-1K8 C)))) & ( ex L be SequenceORDINAL1M4 st (((it2 =XBOOLE-0R4 lastORDINAL2K1 L & domRELAT-1K1 L =XBOOLE-0R4 succORDINAL1K1 A) & L .FUNCT-1K1 (0ORDINAL1K5) =XBOOLE-0R4 {}XBOOLE-0K1) & ( for C be OrdinalORDINAL1M3 holds succORDINAL1K1 C inTARSKIR2 succORDINAL1K1 A implies L .FUNCT-1K1 succORDINAL1K1 C =XBOOLE-0R4 boolSETFAM-1K9 (L .FUNCT-1K1 C))) & ( for C be OrdinalORDINAL1M3 holds (C inTARSKIR2 succORDINAL1K1 A & C <>HIDDENR2 0ORDINAL1K5) & C be limit-ordinalORDINAL1V4 implies L .FUNCT-1K1 C =XBOOLE-0R4 unionTARSKIK3 (rngFUNCT-1K2 (L |RELAT-1K8 C)))) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mlemma classes1_lm_2:
"RankCLASSES1K4 (0ORDINAL1K5) =XBOOLE-0R4 {}XBOOLE-0K1 & (( for A be OrdinalORDINAL1M3 holds RankCLASSES1K4 (succORDINAL1K1 A) =XBOOLE-0R4 boolSETFAM-1K9 RankCLASSES1K4 A) & ( for A be OrdinalORDINAL1M3 holds  for L be SequenceORDINAL1M4 holds ((A <>HIDDENR2 0ORDINAL1K5 & A be limit-ordinalORDINAL1V4) & domRELAT-1K1 L =XBOOLE-0R4 A) & ( for B be OrdinalORDINAL1M3 holds B inTARSKIR2 A implies L .FUNCT-1K1 B =XBOOLE-0R4 RankCLASSES1K4 B) implies RankCLASSES1K4 A =XBOOLE-0R4 unionTARSKIK3 (rngFUNCT-1K2 L)))"
sorry

mtheorem classes1_th_29:
"RankCLASSES1K4 ({}XBOOLE-0K1) =XBOOLE-0R4 {}XBOOLE-0K1"
  using classes1_lm_2 sorry

mtheorem classes1_th_30:
" for A be OrdinalORDINAL1M3 holds RankCLASSES1K4 (succORDINAL1K1 A) =XBOOLE-0R4 boolSETFAM-1K9 RankCLASSES1K4 A"
  using classes1_lm_2 sorry

mtheorem classes1_th_31:
" for A be OrdinalORDINAL1M3 holds A <>HIDDENR2 {}XBOOLE-0K1 & A be limit-ordinalORDINAL1V4 implies ( for x be setHIDDENM2 holds x inTARSKIR2 RankCLASSES1K4 A iff ( ex B be OrdinalORDINAL1M3 st B inTARSKIR2 A & x inTARSKIR2 RankCLASSES1K4 B))"
sorry

mtheorem classes1_th_32:
" for X be setHIDDENM2 holds  for A be OrdinalORDINAL1M3 holds X c=TARSKIR1 RankCLASSES1K4 A iff X inTARSKIR2 RankCLASSES1K4 (succORDINAL1K1 A)"
sorry

mtheorem classes1_cl_2:
  mlet "A be OrdinalORDINAL1M3"
"cluster RankCLASSES1K4 A as-term-is epsilon-transitiveORDINAL1V1"
proof
(*coherence*)
  show "RankCLASSES1K4 A be epsilon-transitiveORDINAL1V1"
sorry
qed "sorry"

mtheorem classes1_th_33:
" for A be OrdinalORDINAL1M3 holds RankCLASSES1K4 A c=TARSKIR1 RankCLASSES1K4 (succORDINAL1K1 A)"
sorry

mtheorem classes1_th_34:
" for A be OrdinalORDINAL1M3 holds unionTARSKIK3 RankCLASSES1K4 A c=TARSKIR1 RankCLASSES1K4 A"
sorry

mtheorem classes1_th_35:
" for X be setHIDDENM2 holds  for A be OrdinalORDINAL1M3 holds X inTARSKIR2 RankCLASSES1K4 A implies unionTARSKIK3 X inTARSKIR2 RankCLASSES1K4 A"
sorry

mtheorem classes1_th_36:
" for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds A inTARSKIR2 B iff RankCLASSES1K4 A inTARSKIR2 RankCLASSES1K4 B"
sorry

mtheorem classes1_th_37:
" for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds A c=ORDINAL1R1 B iff RankCLASSES1K4 A c=TARSKIR1 RankCLASSES1K4 B"
sorry

mtheorem classes1_th_38:
" for A be OrdinalORDINAL1M3 holds A c=TARSKIR1 RankCLASSES1K4 A"
sorry

mtheorem classes1_th_39:
" for A be OrdinalORDINAL1M3 holds  for X be setHIDDENM2 holds X inTARSKIR2 RankCLASSES1K4 A implies  not (X,RankCLASSES1K4 A)are-equipotentTARSKIR3 & cardCARD-1K1 X inTARSKIR2 cardCARD-1K1 RankCLASSES1K4 A"
sorry

mtheorem classes1_th_40:
" for X be setHIDDENM2 holds  for A be OrdinalORDINAL1M3 holds X c=TARSKIR1 RankCLASSES1K4 A iff boolSETFAM-1K9 X c=TARSKIR1 RankCLASSES1K4 (succORDINAL1K1 A)"
sorry

mtheorem classes1_th_41:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for A be OrdinalORDINAL1M3 holds X c=TARSKIR1 Y & Y inTARSKIR2 RankCLASSES1K4 A implies X inTARSKIR2 RankCLASSES1K4 A"
sorry

mtheorem classes1_th_42:
" for X be setHIDDENM2 holds  for A be OrdinalORDINAL1M3 holds X inTARSKIR2 RankCLASSES1K4 A iff boolSETFAM-1K9 X inTARSKIR2 RankCLASSES1K4 (succORDINAL1K1 A)"
sorry

mtheorem classes1_th_43:
" for x be setHIDDENM2 holds  for A be OrdinalORDINAL1M3 holds x inTARSKIR2 RankCLASSES1K4 A iff {TARSKIK1 x} inTARSKIR2 RankCLASSES1K4 (succORDINAL1K1 A)"
sorry

mtheorem classes1_th_44:
" for x be setHIDDENM2 holds  for y be setHIDDENM2 holds  for A be OrdinalORDINAL1M3 holds x inTARSKIR2 RankCLASSES1K4 A & y inTARSKIR2 RankCLASSES1K4 A iff {TARSKIK2 x,y } inTARSKIR2 RankCLASSES1K4 (succORDINAL1K1 A)"
sorry

mtheorem classes1_th_45:
" for x be setHIDDENM2 holds  for y be setHIDDENM2 holds  for A be OrdinalORDINAL1M3 holds x inTARSKIR2 RankCLASSES1K4 A & y inTARSKIR2 RankCLASSES1K4 A iff [TARSKIK4 x,y ] inHIDDENR3 RankCLASSES1K4 (succORDINAL1K1 (succORDINAL1K1 A))"
sorry

mtheorem classes1_th_46:
" for X be setHIDDENM2 holds  for A be OrdinalORDINAL1M3 holds X be epsilon-transitiveORDINAL1V1 & RankCLASSES1K4 A /\\XBOOLE-0K3 Tarski-ClassCLASSES1K1 X =XBOOLE-0R4 RankCLASSES1K4 (succORDINAL1K1 A) /\\XBOOLE-0K3 Tarski-ClassCLASSES1K1 X implies Tarski-ClassCLASSES1K1 X c=TARSKIR1 RankCLASSES1K4 A"
sorry

mtheorem classes1_th_47:
" for X be setHIDDENM2 holds X be epsilon-transitiveORDINAL1V1 implies ( ex A be OrdinalORDINAL1M3 st Tarski-ClassCLASSES1K1 X c=TARSKIR1 RankCLASSES1K4 A)"
sorry

mtheorem classes1_th_48:
" for X be setHIDDENM2 holds X be epsilon-transitiveORDINAL1V1 implies unionTARSKIK3 X c=TARSKIR1 X"
sorry

mtheorem classes1_th_49:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X be epsilon-transitiveORDINAL1V1 & Y be epsilon-transitiveORDINAL1V1 implies X \\/XBOOLE-0K2 Y be epsilon-transitiveORDINAL1V1"
sorry

mtheorem classes1_th_50:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X be epsilon-transitiveORDINAL1V1 & Y be epsilon-transitiveORDINAL1V1 implies X /\\XBOOLE-0K3 Y be epsilon-transitiveORDINAL1V1"
sorry

reserve n for "ElementSUBSET-1M1-of omegaORDINAL1K4"
mdef classes1_def_7 ("the-transitive-closure-ofCLASSES1K5  _ " [228]228 ) where
  mlet "X be setHIDDENM2"
"func the-transitive-closure-ofCLASSES1K5 X \<rightarrow> setHIDDENM2 means
  \<lambda>it.  for x be objectHIDDENM1 holds x inHIDDENR3 it iff ( ex f be FunctionFUNCT-1M1 st  ex n be ElementSUBSET-1M1-of omegaORDINAL1K4 st ((x inHIDDENR3 f .FUNCT-1K1 n & domRELAT-1K1 f =XBOOLE-0R4 omegaORDINAL1K4) & f .FUNCT-1K1 (0ORDINAL1K5) =XBOOLE-0R4 X) & ( for k be NatORDINAL1M6 holds f .FUNCT-1K1 succORDINAL1K1 k =XBOOLE-0R4 unionTARSKIK3 (f .FUNCT-1K1 k)))"
proof-
  (*existence*)
    show " ex it be setHIDDENM2 st  for x be objectHIDDENM1 holds x inHIDDENR3 it iff ( ex f be FunctionFUNCT-1M1 st  ex n be ElementSUBSET-1M1-of omegaORDINAL1K4 st ((x inHIDDENR3 f .FUNCT-1K1 n & domRELAT-1K1 f =XBOOLE-0R4 omegaORDINAL1K4) & f .FUNCT-1K1 (0ORDINAL1K5) =XBOOLE-0R4 X) & ( for k be NatORDINAL1M6 holds f .FUNCT-1K1 succORDINAL1K1 k =XBOOLE-0R4 unionTARSKIK3 (f .FUNCT-1K1 k)))"
sorry
  (*uniqueness*)
    show " for it1 be setHIDDENM2 holds  for it2 be setHIDDENM2 holds ( for x be objectHIDDENM1 holds x inHIDDENR3 it1 iff ( ex f be FunctionFUNCT-1M1 st  ex n be ElementSUBSET-1M1-of omegaORDINAL1K4 st ((x inHIDDENR3 f .FUNCT-1K1 n & domRELAT-1K1 f =XBOOLE-0R4 omegaORDINAL1K4) & f .FUNCT-1K1 (0ORDINAL1K5) =XBOOLE-0R4 X) & ( for k be NatORDINAL1M6 holds f .FUNCT-1K1 succORDINAL1K1 k =XBOOLE-0R4 unionTARSKIK3 (f .FUNCT-1K1 k)))) & ( for x be objectHIDDENM1 holds x inHIDDENR3 it2 iff ( ex f be FunctionFUNCT-1M1 st  ex n be ElementSUBSET-1M1-of omegaORDINAL1K4 st ((x inHIDDENR3 f .FUNCT-1K1 n & domRELAT-1K1 f =XBOOLE-0R4 omegaORDINAL1K4) & f .FUNCT-1K1 (0ORDINAL1K5) =XBOOLE-0R4 X) & ( for k be NatORDINAL1M6 holds f .FUNCT-1K1 succORDINAL1K1 k =XBOOLE-0R4 unionTARSKIK3 (f .FUNCT-1K1 k)))) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mtheorem classes1_cl_3:
  mlet "X be setHIDDENM2"
"cluster the-transitive-closure-ofCLASSES1K5 X as-term-is epsilon-transitiveORDINAL1V1"
proof
(*coherence*)
  show "the-transitive-closure-ofCLASSES1K5 X be epsilon-transitiveORDINAL1V1"
sorry
qed "sorry"

mtheorem classes1_th_51:
" for X be setHIDDENM2 holds the-transitive-closure-ofCLASSES1K5 X be epsilon-transitiveORDINAL1V1"
   sorry

mtheorem classes1_th_52:
" for X be setHIDDENM2 holds X c=TARSKIR1 the-transitive-closure-ofCLASSES1K5 X"
sorry

mtheorem classes1_th_53:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X c=TARSKIR1 Y & Y be epsilon-transitiveORDINAL1V1 implies the-transitive-closure-ofCLASSES1K5 X c=TARSKIR1 Y"
sorry

mtheorem classes1_th_54:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds (( for Z be setHIDDENM2 holds X c=TARSKIR1 Z & Z be epsilon-transitiveORDINAL1V1 implies Y c=TARSKIR1 Z) & X c=TARSKIR1 Y) & Y be epsilon-transitiveORDINAL1V1 implies the-transitive-closure-ofCLASSES1K5 X =XBOOLE-0R4 Y"
  using classes1_th_53 classes1_th_52 sorry

mtheorem classes1_th_55:
" for X be setHIDDENM2 holds X be epsilon-transitiveORDINAL1V1 implies the-transitive-closure-ofCLASSES1K5 X =XBOOLE-0R4 X"
sorry

mtheorem classes1_th_56:
"the-transitive-closure-ofCLASSES1K5 ({}XBOOLE-0K1) =XBOOLE-0R4 {}XBOOLE-0K1"
  using classes1_th_55 sorry

mtheorem classes1_th_57:
" for A be OrdinalORDINAL1M3 holds the-transitive-closure-ofCLASSES1K5 A =XBOOLE-0R4 A"
  using classes1_th_55 sorry

mtheorem classes1_th_58:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X c=TARSKIR1 Y implies the-transitive-closure-ofCLASSES1K5 X c=TARSKIR1 the-transitive-closure-ofCLASSES1K5 Y"
sorry

mtheorem classes1_th_59:
" for X be setHIDDENM2 holds the-transitive-closure-ofCLASSES1K5 (the-transitive-closure-ofCLASSES1K5 X) =XBOOLE-0R4 the-transitive-closure-ofCLASSES1K5 X"
  using classes1_th_55 sorry

mtheorem classes1_th_60:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds the-transitive-closure-ofCLASSES1K5 (X \\/XBOOLE-0K2 Y) =XBOOLE-0R4 the-transitive-closure-ofCLASSES1K5 X \\/XBOOLE-0K2 the-transitive-closure-ofCLASSES1K5 Y"
sorry

mtheorem classes1_th_61:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds the-transitive-closure-ofCLASSES1K5 (X /\\XBOOLE-0K3 Y) c=TARSKIR1 the-transitive-closure-ofCLASSES1K5 X /\\XBOOLE-0K3 the-transitive-closure-ofCLASSES1K5 Y"
sorry

mtheorem classes1_th_62:
" for X be setHIDDENM2 holds  ex A be OrdinalORDINAL1M3 st X c=TARSKIR1 RankCLASSES1K4 A"
sorry

mdef classes1_def_8 ("the-rank-ofCLASSES1K6  _ " [300]300 ) where
  mlet "x be objectHIDDENM1"
"func the-rank-ofCLASSES1K6 x \<rightarrow> OrdinalORDINAL1M3 means
  \<lambda>it. x inHIDDENR3 RankCLASSES1K4 (succORDINAL1K1 it) & ( for B be OrdinalORDINAL1M3 holds x inHIDDENR3 RankCLASSES1K4 (succORDINAL1K1 B) implies it c=ORDINAL1R1 B)"
proof-
  (*existence*)
    show " ex it be OrdinalORDINAL1M3 st x inHIDDENR3 RankCLASSES1K4 (succORDINAL1K1 it) & ( for B be OrdinalORDINAL1M3 holds x inHIDDENR3 RankCLASSES1K4 (succORDINAL1K1 B) implies it c=ORDINAL1R1 B)"
sorry
  (*uniqueness*)
    show " for it1 be OrdinalORDINAL1M3 holds  for it2 be OrdinalORDINAL1M3 holds (x inHIDDENR3 RankCLASSES1K4 (succORDINAL1K1 it1) & ( for B be OrdinalORDINAL1M3 holds x inHIDDENR3 RankCLASSES1K4 (succORDINAL1K1 B) implies it1 c=ORDINAL1R1 B)) & (x inHIDDENR3 RankCLASSES1K4 (succORDINAL1K1 it2) & ( for B be OrdinalORDINAL1M3 holds x inHIDDENR3 RankCLASSES1K4 (succORDINAL1K1 B) implies it2 c=ORDINAL1R1 B)) implies it1 =HIDDENR1 it2"
       sorry
qed "sorry"

abbreviation(input) CLASSES1K7("the-rank-ofCLASSES1K7  _ " [300]300) where
  "the-rank-ofCLASSES1K7 X \<equiv> the-rank-ofCLASSES1K6 X"

mtheorem classes1_def_9:
  mlet "X be setHIDDENM2"
"redefine func the-rank-ofCLASSES1K7 X \<rightarrow> OrdinalORDINAL1M3 means
  \<lambda>it. X c=TARSKIR1 RankCLASSES1K4 it & ( for B be OrdinalORDINAL1M3 holds X c=TARSKIR1 RankCLASSES1K4 B implies it c=ORDINAL1R1 B)"
proof
(*compatibility*)
  show " for it be OrdinalORDINAL1M3 holds it =HIDDENR1 the-rank-ofCLASSES1K7 X iff X c=TARSKIR1 RankCLASSES1K4 it & ( for B be OrdinalORDINAL1M3 holds X c=TARSKIR1 RankCLASSES1K4 B implies it c=ORDINAL1R1 B)"
sorry
qed "sorry"

mtheorem classes1_th_63:
" for X be setHIDDENM2 holds the-rank-ofCLASSES1K7 (boolSETFAM-1K9 X) =XBOOLE-0R4 succORDINAL1K1 the-rank-ofCLASSES1K7 X"
sorry

mtheorem classes1_th_64:
" for A be OrdinalORDINAL1M3 holds the-rank-ofCLASSES1K7 (RankCLASSES1K4 A) =XBOOLE-0R4 A"
sorry

mtheorem classes1_th_65:
" for X be setHIDDENM2 holds  for A be OrdinalORDINAL1M3 holds X c=TARSKIR1 RankCLASSES1K4 A iff the-rank-ofCLASSES1K7 X c=ORDINAL1R1 A"
sorry

mtheorem classes1_th_66:
" for X be setHIDDENM2 holds  for A be OrdinalORDINAL1M3 holds X inTARSKIR2 RankCLASSES1K4 A iff the-rank-ofCLASSES1K7 X inTARSKIR2 A"
sorry

mtheorem classes1_th_67:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X c=TARSKIR1 Y implies the-rank-ofCLASSES1K7 X c=ORDINAL1R1 the-rank-ofCLASSES1K7 Y"
sorry

mtheorem classes1_th_68:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X inTARSKIR2 Y implies the-rank-ofCLASSES1K7 X inTARSKIR2 the-rank-ofCLASSES1K7 Y"
sorry

mtheorem classes1_th_69:
" for X be setHIDDENM2 holds  for A be OrdinalORDINAL1M3 holds the-rank-ofCLASSES1K7 X c=ORDINAL1R1 A iff ( for Y be setHIDDENM2 holds Y inTARSKIR2 X implies the-rank-ofCLASSES1K7 Y inTARSKIR2 A)"
sorry

mtheorem classes1_th_70:
" for X be setHIDDENM2 holds  for A be OrdinalORDINAL1M3 holds A c=ORDINAL1R1 the-rank-ofCLASSES1K7 X iff ( for B be OrdinalORDINAL1M3 holds B inTARSKIR2 A implies ( ex Y be setHIDDENM2 st Y inTARSKIR2 X & B c=ORDINAL1R1 the-rank-ofCLASSES1K7 Y))"
sorry

mtheorem classes1_th_71:
" for X be setHIDDENM2 holds the-rank-ofCLASSES1K7 X =XBOOLE-0R4 {}XBOOLE-0K1 iff X =XBOOLE-0R4 {}XBOOLE-0K1"
sorry

mtheorem classes1_th_72:
" for X be setHIDDENM2 holds  for A be OrdinalORDINAL1M3 holds the-rank-ofCLASSES1K7 X =XBOOLE-0R4 succORDINAL1K1 A implies ( ex Y be setHIDDENM2 st Y inTARSKIR2 X & the-rank-ofCLASSES1K7 Y =XBOOLE-0R4 A)"
sorry

mtheorem classes1_th_73:
" for A be OrdinalORDINAL1M3 holds the-rank-ofCLASSES1K7 A =XBOOLE-0R4 A"
sorry

mtheorem classes1_th_74:
" for X be setHIDDENM2 holds the-rank-ofCLASSES1K7 (Tarski-ClassCLASSES1K1 X) <>HIDDENR2 {}XBOOLE-0K1 & the-rank-ofCLASSES1K7 (Tarski-ClassCLASSES1K1 X) be limit-ordinalORDINAL1V4"
sorry

(*begin*)
reserve e, u for "setHIDDENM2"
theorem classes1_sch_1:
  fixes Xf0 Pp2 
  assumes
[ty]: "Xf0 be setHIDDENM2" and
   A1: " for e be objectHIDDENM1 holds e inHIDDENR3 Xf0 implies ( ex u be objectHIDDENM1 st Pp2(e,u))"
  shows " ex f be FunctionFUNCT-1M1 st domRELAT-1K1 f =XBOOLE-0R4 Xf0 & ( for e be objectHIDDENM1 holds e inHIDDENR3 Xf0 implies Pp2(e,f .FUNCT-1K1 e))"
sorry

mdef classes1_def_10 ("'( _ , _ ')are-fiberwise-equipotentCLASSES1R2" [0,0]50 ) where
  mlet "F be RelationRELAT-1M1", "G be RelationRELAT-1M1"
"pred (F,G)are-fiberwise-equipotentCLASSES1R2 means
   for x be objectHIDDENM1 holds cardCARD-1K1 (CoimRELAT-1K13(F,x)) =XBOOLE-0R4 cardCARD-1K1 (CoimRELAT-1K13(G,x))"..

mtheorem CLASSES1R2_reflexivity:
" for G be RelationRELAT-1M1 holds (G,G)are-fiberwise-equipotentCLASSES1R2"
sorry

mtheorem CLASSES1R2_symmetry:
" for F be RelationRELAT-1M1 holds  for G be RelationRELAT-1M1 holds (F,G)are-fiberwise-equipotentCLASSES1R2 implies (G,F)are-fiberwise-equipotentCLASSES1R2"
sorry

mlemma classes1_lm_3:
" for F be FunctionFUNCT-1M1 holds  for x be objectHIDDENM1 holds  not x inHIDDENR3 rngFUNCT-1K2 F implies CoimRELAT-1K13(F,x) =XBOOLE-0R4 {}XBOOLE-0K1"
sorry

mtheorem classes1_th_75:
" for F be FunctionFUNCT-1M1 holds  for G be FunctionFUNCT-1M1 holds (F,G)are-fiberwise-equipotentCLASSES1R2 implies rngFUNCT-1K2 F =XBOOLE-0R4 rngFUNCT-1K2 G"
sorry

mtheorem classes1_th_76:
" for F be FunctionFUNCT-1M1 holds  for G be FunctionFUNCT-1M1 holds  for H be FunctionFUNCT-1M1 holds (F,G)are-fiberwise-equipotentCLASSES1R2 & (F,H)are-fiberwise-equipotentCLASSES1R2 implies (G,H)are-fiberwise-equipotentCLASSES1R2"
sorry

mtheorem classes1_th_77:
" for F be FunctionFUNCT-1M1 holds  for G be FunctionFUNCT-1M1 holds (F,G)are-fiberwise-equipotentCLASSES1R2 iff ( ex H be FunctionFUNCT-1M1 st ((domRELAT-1K1 H =XBOOLE-0R4 domRELAT-1K1 F & rngFUNCT-1K2 H =XBOOLE-0R4 domRELAT-1K1 G) & H be one-to-oneFUNCT-1V2) & F =FUNCT-1R1 G *FUNCT-1K3 H)"
sorry

mtheorem classes1_th_78:
" for F be FunctionFUNCT-1M1 holds  for G be FunctionFUNCT-1M1 holds (F,G)are-fiberwise-equipotentCLASSES1R2 iff ( for X be setHIDDENM2 holds cardCARD-1K1 (F \<inverse>FUNCT-1K6 X) =XBOOLE-0R4 cardCARD-1K1 (G \<inverse>FUNCT-1K6 X))"
sorry

mtheorem classes1_th_79:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for F be FunctionFUNCT-1M1 holds  for G be FunctionFUNCT-1M1 holds (rngFUNCT-1K2 F c=TARSKIR1 D & rngFUNCT-1K2 G c=TARSKIR1 D) & ( for d be ElementSUBSET-1M1-of D holds cardCARD-1K1 (CoimRELAT-1K13(F,d)) =XBOOLE-0R4 cardCARD-1K1 (CoimRELAT-1K13(G,d))) implies (F,G)are-fiberwise-equipotentCLASSES1R2"
sorry

mtheorem classes1_th_80:
" for F be FunctionFUNCT-1M1 holds  for G be FunctionFUNCT-1M1 holds domRELAT-1K1 F =XBOOLE-0R4 domRELAT-1K1 G implies ((F,G)are-fiberwise-equipotentCLASSES1R2 iff ( ex P be PermutationFUNCT-2M2-of domRELAT-1K1 F st F =FUNCT-1R1 G *FUNCT-1K3 P))"
sorry

mtheorem classes1_th_81:
" for F be FunctionFUNCT-1M1 holds  for G be FunctionFUNCT-1M1 holds (F,G)are-fiberwise-equipotentCLASSES1R2 implies cardCARD-1K1 (domRELAT-1K1 F) =XBOOLE-0R4 cardCARD-1K1 (domRELAT-1K1 G)"
sorry

mtheorem classes1_th_82:
" for f be setHIDDENM2 holds  for p be RelationRELAT-1M1 holds  for x be setHIDDENM2 holds x inTARSKIR2 rngRELAT-1K2 p implies the-rank-ofCLASSES1K7 x inTARSKIR2 the-rank-ofCLASSES1K6 [TARSKIK4 p,f ]"
sorry

mtheorem classes1_th_83:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds  for h be FunctionFUNCT-1M1 holds ((domRELAT-1K1 f =XBOOLE-0R4 domRELAT-1K1 g & rngFUNCT-1K2 f c=TARSKIR1 domRELAT-1K1 h) & rngFUNCT-1K2 g c=TARSKIR1 domRELAT-1K1 h) & (f,g)are-fiberwise-equipotentCLASSES1R2 implies (h *FUNCT-1K3 f,h *FUNCT-1K3 g)are-fiberwise-equipotentCLASSES1R2"
sorry

theorem classes1_sch_2:
  fixes Af0 Bf0 Ff1 
  assumes
[ty]: "Af0 be setHIDDENM2" and
  [ty]: "Bf0 be setHIDDENM2" and
  [ty_func]: "\<And> x1. x1 be ElementSUBSET-1M1-of Bf0 \<Longrightarrow> Ff1(x1) be setHIDDENM2"
  shows " ex f be FunctionFUNCT-1M1 st domRELAT-1K1 f =XBOOLE-0R4 Af0 & ( for x be ElementSUBSET-1M1-of Bf0 holds x inTARSKIR2 Af0 implies f .FUNCT-1K1 x =XBOOLE-0R4 Ff1(x))"
sorry

mtheorem classes1_th_84:
" for x be setHIDDENM2 holds  for y be setHIDDENM2 holds the-rank-ofCLASSES1K7 x inTARSKIR2 the-rank-ofCLASSES1K6 [TARSKIK4 x,y ] & the-rank-ofCLASSES1K7 y inTARSKIR2 the-rank-ofCLASSES1K6 [TARSKIK4 x,y ]"
sorry

end
