theory finsub_1
  imports finset_1
begin
(*begin*)
reserve X, Y, x for "setHIDDENM2"
mdef finsub_1_def_1 ("cup-closedFINSUB-1V1" 70 ) where
"attr cup-closedFINSUB-1V1 for setHIDDENM2 means
  (\<lambda>IT.  for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X inTARSKIR2 IT & Y inTARSKIR2 IT implies X \\/XBOOLE-0K2 Y inTARSKIR2 IT)"..

mdef finsub_1_def_2 ("cap-closedFINSUB-1V2" 70 ) where
"attr cap-closedFINSUB-1V2 for setHIDDENM2 means
  (\<lambda>IT.  for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X inTARSKIR2 IT & Y inTARSKIR2 IT implies X /\\XBOOLE-0K3 Y inTARSKIR2 IT)"..

mdef finsub_1_def_3 ("diff-closedFINSUB-1V3" 70 ) where
"attr diff-closedFINSUB-1V3 for setHIDDENM2 means
  (\<lambda>IT.  for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X inTARSKIR2 IT & Y inTARSKIR2 IT implies X \\SUBSET-1K6 Y inTARSKIR2 IT)"..

mdef finsub_1_def_4 ("preBooleanFINSUB-1V4" 70 ) where
"attr preBooleanFINSUB-1V4 for setHIDDENM2 means
  (\<lambda>IT. IT be cup-closedFINSUB-1V1\<bar>diff-closedFINSUB-1V3)"..

mtheorem finsub_1_cl_1:
"cluster preBooleanFINSUB-1V4 also-is cup-closedFINSUB-1V1\<bar>diff-closedFINSUB-1V3 for setHIDDENM2"
proof
(*coherence*)
  show " for it be setHIDDENM2 holds it be preBooleanFINSUB-1V4 implies it be cup-closedFINSUB-1V1\<bar>diff-closedFINSUB-1V3"
     sorry
qed "sorry"

mtheorem finsub_1_cl_2:
"cluster cup-closedFINSUB-1V1\<bar>diff-closedFINSUB-1V3 also-is preBooleanFINSUB-1V4 for setHIDDENM2"
proof
(*coherence*)
  show " for it be setHIDDENM2 holds it be cup-closedFINSUB-1V1\<bar>diff-closedFINSUB-1V3 implies it be preBooleanFINSUB-1V4"
     sorry
qed "sorry"

mtheorem finsub_1_cl_3:
"cluster  non emptyXBOOLE-0V1\<bar>cup-closedFINSUB-1V1\<bar>cap-closedFINSUB-1V2\<bar>diff-closedFINSUB-1V3 for setHIDDENM2"
proof
(*existence*)
  show " ex it be setHIDDENM2 st it be  non emptyXBOOLE-0V1\<bar>cup-closedFINSUB-1V1\<bar>cap-closedFINSUB-1V2\<bar>diff-closedFINSUB-1V3"
sorry
qed "sorry"

mtheorem finsub_1_th_1:
" for A be setHIDDENM2 holds A be preBooleanFINSUB-1V4 iff ( for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X inTARSKIR2 A & Y inTARSKIR2 A implies X \\/XBOOLE-0K2 Y inTARSKIR2 A & X \\SUBSET-1K6 Y inTARSKIR2 A)"
sorry

reserve A for " non emptyXBOOLE-0V1\<bar>preBooleanFINSUB-1V4\<bar>setHIDDENM2"
syntax FINSUB_1K1 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ '\\'/FINSUB-1K1\<^bsub>'( _ ')\<^esub>  _ " [132,0,132]132)
translations "X \\/FINSUB-1K1\<^bsub>(A)\<^esub> Y" \<rightharpoonup> "X \\/XBOOLE-0K2 Y"

mtheorem finsub_1_add_1:
  mlet "A be  non emptyXBOOLE-0V1\<bar>preBooleanFINSUB-1V4\<bar>setHIDDENM2", "X be ElementSUBSET-1M1-of A", "Y be ElementSUBSET-1M1-of A"
"cluster X \\/XBOOLE-0K2 Y as-term-is ElementSUBSET-1M1-of A"
proof
(*coherence*)
  show "X \\/XBOOLE-0K2 Y be ElementSUBSET-1M1-of A"
    using finsub_1_th_1 sorry
qed "sorry"

syntax FINSUB_1K2 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ '\\FINSUB-1K2\<^bsub>'( _ ')\<^esub>  _ " [132,0,132]132)
translations "X \\FINSUB-1K2\<^bsub>(A)\<^esub> Y" \<rightharpoonup> "X \\XBOOLE-0K4 Y"

mtheorem finsub_1_add_2:
  mlet "A be  non emptyXBOOLE-0V1\<bar>preBooleanFINSUB-1V4\<bar>setHIDDENM2", "X be ElementSUBSET-1M1-of A", "Y be ElementSUBSET-1M1-of A"
"cluster X \\XBOOLE-0K4 Y as-term-is ElementSUBSET-1M1-of A"
proof
(*coherence*)
  show "X \\XBOOLE-0K4 Y be ElementSUBSET-1M1-of A"
    using finsub_1_th_1 sorry
qed "sorry"

mtheorem finsub_1_th_2:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for A be  non emptyXBOOLE-0V1\<bar>preBooleanFINSUB-1V4\<bar>setHIDDENM2 holds X be ElementSUBSET-1M1-of A & Y be ElementSUBSET-1M1-of A implies X /\\XBOOLE-0K3 Y be ElementSUBSET-1M1-of A"
sorry

mtheorem finsub_1_th_3:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for A be  non emptyXBOOLE-0V1\<bar>preBooleanFINSUB-1V4\<bar>setHIDDENM2 holds X be ElementSUBSET-1M1-of A & Y be ElementSUBSET-1M1-of A implies X \\+\\XBOOLE-0K5 Y be ElementSUBSET-1M1-of A"
sorry

mtheorem finsub_1_th_4:
" for A be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds ( for X be ElementSUBSET-1M1-of A holds  for Y be ElementSUBSET-1M1-of A holds X \\+\\XBOOLE-0K5 Y inTARSKIR2 A & X \\SUBSET-1K6 Y inTARSKIR2 A) implies A be preBooleanFINSUB-1V4"
sorry

mtheorem finsub_1_th_5:
" for A be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds ( for X be ElementSUBSET-1M1-of A holds  for Y be ElementSUBSET-1M1-of A holds X \\+\\XBOOLE-0K5 Y inTARSKIR2 A & X /\\XBOOLE-0K3 Y inTARSKIR2 A) implies A be preBooleanFINSUB-1V4"
sorry

mtheorem finsub_1_th_6:
" for A be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds ( for X be ElementSUBSET-1M1-of A holds  for Y be ElementSUBSET-1M1-of A holds X \\+\\XBOOLE-0K5 Y inTARSKIR2 A & X \\/XBOOLE-0K2 Y inTARSKIR2 A) implies A be preBooleanFINSUB-1V4"
sorry

syntax FINSUB_1K3 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ '/'\\FINSUB-1K3\<^bsub>'( _ ')\<^esub>  _ " [164,0,164]164)
translations "X /\\FINSUB-1K3\<^bsub>(A)\<^esub> Y" \<rightharpoonup> "X /\\XBOOLE-0K3 Y"

mtheorem finsub_1_add_3:
  mlet "A be  non emptyXBOOLE-0V1\<bar>preBooleanFINSUB-1V4\<bar>setHIDDENM2", "X be ElementSUBSET-1M1-of A", "Y be ElementSUBSET-1M1-of A"
"cluster X /\\XBOOLE-0K3 Y as-term-is ElementSUBSET-1M1-of A"
proof
(*coherence*)
  show "X /\\XBOOLE-0K3 Y be ElementSUBSET-1M1-of A"
    using finsub_1_th_2 sorry
qed "sorry"

syntax FINSUB_1K4 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ '\\+'\\FINSUB-1K4\<^bsub>'( _ ')\<^esub>  _ " [130,0,130]130)
translations "X \\+\\FINSUB-1K4\<^bsub>(A)\<^esub> Y" \<rightharpoonup> "X \\+\\XBOOLE-0K5 Y"

mtheorem finsub_1_add_4:
  mlet "A be  non emptyXBOOLE-0V1\<bar>preBooleanFINSUB-1V4\<bar>setHIDDENM2", "X be ElementSUBSET-1M1-of A", "Y be ElementSUBSET-1M1-of A"
"cluster X \\+\\XBOOLE-0K5 Y as-term-is ElementSUBSET-1M1-of A"
proof
(*coherence*)
  show "X \\+\\XBOOLE-0K5 Y be ElementSUBSET-1M1-of A"
    using finsub_1_th_3 sorry
qed "sorry"

mtheorem finsub_1_th_7:
" for A be  non emptyXBOOLE-0V1\<bar>preBooleanFINSUB-1V4\<bar>setHIDDENM2 holds {}XBOOLE-0K1 inTARSKIR2 A"
sorry

mtheorem finsub_1_th_8:
" for A be setHIDDENM2 holds boolZFMISC-1K1 A be preBooleanFINSUB-1V4"
sorry

mtheorem finsub_1_cl_4:
  mlet "A be setHIDDENM2"
"cluster boolZFMISC-1K1 A as-term-is preBooleanFINSUB-1V4"
proof
(*coherence*)
  show "boolZFMISC-1K1 A be preBooleanFINSUB-1V4"
    using finsub_1_th_8 sorry
qed "sorry"

mtheorem finsub_1_th_9:
" for A be  non emptyXBOOLE-0V1\<bar>preBooleanFINSUB-1V4\<bar>setHIDDENM2 holds  for B be  non emptyXBOOLE-0V1\<bar>preBooleanFINSUB-1V4\<bar>setHIDDENM2 holds A /\\XBOOLE-0K3 B be  non emptyXBOOLE-0V1\<bar>preBooleanFINSUB-1V4"
sorry

mdef finsub_1_def_5 ("FinFINSUB-1K5  _ " [228]228 ) where
  mlet "A be setHIDDENM2"
"func FinFINSUB-1K5 A \<rightarrow> preBooleanFINSUB-1V4\<bar>setHIDDENM2 means
  \<lambda>it.  for X be setHIDDENM2 holds X inTARSKIR2 it iff X c=TARSKIR1 A & X be finiteFINSET-1V1"
proof-
  (*existence*)
    show " ex it be preBooleanFINSUB-1V4\<bar>setHIDDENM2 st  for X be setHIDDENM2 holds X inTARSKIR2 it iff X c=TARSKIR1 A & X be finiteFINSET-1V1"
sorry
  (*uniqueness*)
    show " for it1 be preBooleanFINSUB-1V4\<bar>setHIDDENM2 holds  for it2 be preBooleanFINSUB-1V4\<bar>setHIDDENM2 holds ( for X be setHIDDENM2 holds X inTARSKIR2 it1 iff X c=TARSKIR1 A & X be finiteFINSET-1V1) & ( for X be setHIDDENM2 holds X inTARSKIR2 it2 iff X c=TARSKIR1 A & X be finiteFINSET-1V1) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mtheorem finsub_1_cl_5:
  mlet "A be setHIDDENM2"
"cluster FinFINSUB-1K5 A as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "FinFINSUB-1K5 A be  non emptyXBOOLE-0V1"
sorry
qed "sorry"

mtheorem finsub_1_cl_6:
  mlet "A be setHIDDENM2"
"cluster note-that finiteFINSET-1V1 for ElementSUBSET-1M1-of FinFINSUB-1K5 A"
proof
(*coherence*)
  show " for it be ElementSUBSET-1M1-of FinFINSUB-1K5 A holds it be finiteFINSET-1V1"
    using finsub_1_def_5 sorry
qed "sorry"

mtheorem finsub_1_th_10:
" for A be setHIDDENM2 holds  for B be setHIDDENM2 holds A c=TARSKIR1 B implies FinFINSUB-1K5 A c=TARSKIR1 FinFINSUB-1K5 B"
sorry

mtheorem finsub_1_th_11:
" for A be setHIDDENM2 holds  for B be setHIDDENM2 holds FinFINSUB-1K5 (A /\\XBOOLE-0K3 B) =XBOOLE-0R4 FinFINSUB-1K5 A /\\XBOOLE-0K3 FinFINSUB-1K5 B"
sorry

mtheorem finsub_1_th_12:
" for A be setHIDDENM2 holds  for B be setHIDDENM2 holds FinFINSUB-1K5 A \\/XBOOLE-0K2 FinFINSUB-1K5 B c=TARSKIR1 FinFINSUB-1K5 (A \\/XBOOLE-0K2 B)"
sorry

mtheorem finsub_1_th_13:
" for A be setHIDDENM2 holds FinFINSUB-1K5 A c=TARSKIR1 boolZFMISC-1K1 A"
sorry

mtheorem finsub_1_th_14:
" for A be setHIDDENM2 holds A be finiteFINSET-1V1 implies FinFINSUB-1K5 A =XBOOLE-0R4 boolZFMISC-1K1 A"
sorry

mtheorem finsub_1_th_15:
"FinFINSUB-1K5 ({}XBOOLE-0K1) =XBOOLE-0R4 {TARSKIK1 {}XBOOLE-0K1 }"
  using finsub_1_th_14 zfmisc_1_th_1 sorry

mtheorem finsub_1_th_16:
" for A be setHIDDENM2 holds  for X be ElementSUBSET-1M1-of FinFINSUB-1K5 A holds X be SubsetSUBSET-1M2-of A"
  using finsub_1_def_5 sorry

mtheorem finsub_1_th_17:
" for A be setHIDDENM2 holds  for X be SubsetSUBSET-1M2-of A holds A be finiteFINSET-1V1 implies X be ElementSUBSET-1M1-of FinFINSUB-1K5 A"
  using finsub_1_def_5 sorry

end
