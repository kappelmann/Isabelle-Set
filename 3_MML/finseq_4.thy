theory finseq_4
  imports finseq_3
   "../mizar_extension/E_number"
begin
(*begin*)
reserve f for "FunctionFUNCT-1M1"
reserve p, q for "FinSequenceFINSEQ-1M1"
reserve A, B, C for "setHIDDENM2"
reserve x, x1, x2, y, z for "objectHIDDENM1"
reserve k, l, m, n for "NatNAT-1M1"
reserve a for "NatNAT-1M1"
mdef finseq_4_def_1 (" _ is-one-to-one-atFINSEQ-4R1  _ " [50,50]50 ) where
  mlet "f be FunctionFUNCT-1M1", "x be objectHIDDENM1"
"pred f is-one-to-one-atFINSEQ-4R1 x means
  f \<inverse>FUNCT-1K6 (ImRELAT-1K12(f,x)) =XBOOLE-0R4 {TARSKIK1 x}"..

mtheorem finseq_4_th_1:
" for f be FunctionFUNCT-1M1 holds  for x be objectHIDDENM1 holds f is-one-to-one-atFINSEQ-4R1 x implies x inHIDDENR3 domRELAT-1K1 f"
sorry

mtheorem finseq_4_th_2:
" for f be FunctionFUNCT-1M1 holds  for x be objectHIDDENM1 holds f is-one-to-one-atFINSEQ-4R1 x iff x inHIDDENR3 domRELAT-1K1 f & f \<inverse>FUNCT-1K6 {TARSKIK1 f .FUNCT-1K1 x } =XBOOLE-0R4 {TARSKIK1 x}"
sorry

mtheorem finseq_4_th_3:
" for f be FunctionFUNCT-1M1 holds  for x be objectHIDDENM1 holds f is-one-to-one-atFINSEQ-4R1 x iff x inHIDDENR3 domRELAT-1K1 f & ( for z be objectHIDDENM1 holds z inHIDDENR3 domRELAT-1K1 f & x <>HIDDENR2 z implies f .FUNCT-1K1 x <>HIDDENR2 f .FUNCT-1K1 z)"
sorry

mtheorem finseq_4_th_4:
" for f be FunctionFUNCT-1M1 holds ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 f implies f is-one-to-one-atFINSEQ-4R1 x) iff f be one-to-oneFUNCT-1V2"
sorry

mdef finseq_4_def_2 (" _ just-once-valuesFINSEQ-4R2  _ " [50,50]50 ) where
  mlet "R be RelationRELAT-1M1", "y be objectHIDDENM1"
"pred R just-once-valuesFINSEQ-4R2 y means
  cardCARD-1K1 (CoimRELAT-1K13(R,y)) =XBOOLE-0R4 \<one>\<^sub>M"..

mtheorem finseq_4_th_5:
" for f be FunctionFUNCT-1M1 holds  for y be objectHIDDENM1 holds f just-once-valuesFINSEQ-4R2 y implies y inHIDDENR3 rngFUNCT-1K2 f"
sorry

mtheorem finseq_4_th_6:
" for f be FunctionFUNCT-1M1 holds  for y be objectHIDDENM1 holds f just-once-valuesFINSEQ-4R2 y iff ( ex x be objectHIDDENM1 st {TARSKIK1 x} =XBOOLE-0R4 f \<inverse>FUNCT-1K6 {TARSKIK1 y})"
  using card_2_th_42 sorry

mtheorem finseq_4_th_7:
" for f be FunctionFUNCT-1M1 holds  for y be objectHIDDENM1 holds f just-once-valuesFINSEQ-4R2 y iff ( ex x be objectHIDDENM1 st (x inHIDDENR3 domRELAT-1K1 f & y =HIDDENR1 f .FUNCT-1K1 x) & ( for z be objectHIDDENM1 holds z inHIDDENR3 domRELAT-1K1 f & z <>HIDDENR2 x implies f .FUNCT-1K1 z <>HIDDENR2 y))"
sorry

mtheorem finseq_4_th_8:
" for f be FunctionFUNCT-1M1 holds f be one-to-oneFUNCT-1V2 iff ( for y be objectHIDDENM1 holds y inHIDDENR3 rngFUNCT-1K2 f implies f just-once-valuesFINSEQ-4R2 y)"
sorry

mtheorem finseq_4_th_9:
" for f be FunctionFUNCT-1M1 holds  for x be objectHIDDENM1 holds f is-one-to-one-atFINSEQ-4R1 x iff x inHIDDENR3 domRELAT-1K1 f & f just-once-valuesFINSEQ-4R2 f .FUNCT-1K1 x"
sorry

mdef finseq_4_def_3 (" _ <-FINSEQ-4K1  _ " [200,200]200 ) where
  mlet "f be FunctionFUNCT-1M1", "y be objectHIDDENM1"
"assume f just-once-valuesFINSEQ-4R2 y func f <-FINSEQ-4K1 y \<rightarrow> setHIDDENM2 means
  \<lambda>it. it inTARSKIR2 domRELAT-1K1 f & f .FUNCT-1K1 it =HIDDENR1 y"
proof-
  (*existence*)
    show "f just-once-valuesFINSEQ-4R2 y implies ( ex it be setHIDDENM2 st it inTARSKIR2 domRELAT-1K1 f & f .FUNCT-1K1 it =HIDDENR1 y)"
sorry
  (*uniqueness*)
    show "f just-once-valuesFINSEQ-4R2 y implies ( for it1 be setHIDDENM2 holds  for it2 be setHIDDENM2 holds (it1 inTARSKIR2 domRELAT-1K1 f & f .FUNCT-1K1 it1 =HIDDENR1 y) & (it2 inTARSKIR2 domRELAT-1K1 f & f .FUNCT-1K1 it2 =HIDDENR1 y) implies it1 =HIDDENR1 it2)"
sorry
qed "sorry"

mtheorem finseq_4_th_10:
" for f be FunctionFUNCT-1M1 holds  for y be objectHIDDENM1 holds f just-once-valuesFINSEQ-4R2 y implies ImRELAT-1K12(f,f <-FINSEQ-4K1 y) =XBOOLE-0R4 {TARSKIK1 y}"
sorry

mtheorem finseq_4_th_11:
" for f be FunctionFUNCT-1M1 holds  for y be objectHIDDENM1 holds f just-once-valuesFINSEQ-4R2 y implies f \<inverse>FUNCT-1K6 {TARSKIK1 y} =XBOOLE-0R4 {TARSKIK1 f <-FINSEQ-4K1 y }"
sorry

mtheorem finseq_4_th_12:
" for f be FunctionFUNCT-1M1 holds  for y be objectHIDDENM1 holds f be one-to-oneFUNCT-1V2 & y inHIDDENR3 rngFUNCT-1K2 f implies f \<inverse>FUNCT-1K4 .FUNCT-1K1 y =XBOOLE-0R4 f <-FINSEQ-4K1 y"
sorry

mtheorem finseq_4_th_13:
" for f be FunctionFUNCT-1M1 holds  for x be objectHIDDENM1 holds f is-one-to-one-atFINSEQ-4R1 x implies f <-FINSEQ-4K1 (f .FUNCT-1K1 x) =HIDDENR1 x"
sorry

mtheorem finseq_4_th_14:
" for f be FunctionFUNCT-1M1 holds  for y be objectHIDDENM1 holds f just-once-valuesFINSEQ-4R2 y implies f is-one-to-one-atFINSEQ-4R1 f <-FINSEQ-4K1 y"
sorry

reserve D for " non emptyXBOOLE-0V1\<bar>setHIDDENM2"
reserve d, d1, d2, d3 for "ElementSUBSET-1M1-of D"
syntax FINSEQ_4K2 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" ("<*FINSEQ-4K2\<^bsub>'( _ ')\<^esub> _ , _ *>" [0,0,0]164)
translations "<*FINSEQ-4K2\<^bsub>(D)\<^esub> d1,d2 *>" \<rightharpoonup> "<*FINSEQ-1K11 d1,d2 *>"

mtheorem finseq_4_add_1:
  mlet "D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "d1 be ElementSUBSET-1M1-of D", "d2 be ElementSUBSET-1M1-of D"
"cluster <*FINSEQ-1K11 d1,d2 *> as-term-is FinSequenceFINSEQ-1M3-of D"
proof
(*coherence*)
  show "<*FINSEQ-1K11 d1,d2 *> be FinSequenceFINSEQ-1M3-of D"
    using finseq_2_th_13 sorry
qed "sorry"

syntax FINSEQ_4K3 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" ("<*FINSEQ-4K3\<^bsub>'( _ ')\<^esub> _ , _ , _ *>" [0,0,0,0]164)
translations "<*FINSEQ-4K3\<^bsub>(D)\<^esub> d1,d2,d3 *>" \<rightharpoonup> "<*FINSEQ-1K12 d1,d2,d3 *>"

mtheorem finseq_4_add_2:
  mlet "D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "d1 be ElementSUBSET-1M1-of D", "d2 be ElementSUBSET-1M1-of D", "d3 be ElementSUBSET-1M1-of D"
"cluster <*FINSEQ-1K12 d1,d2,d3 *> as-term-is FinSequenceFINSEQ-1M3-of D"
proof
(*coherence*)
  show "<*FINSEQ-1K12 d1,d2,d3 *> be FinSequenceFINSEQ-1M3-of D"
    using finseq_2_th_14 sorry
qed "sorry"

mtheorem finseq_4_th_15:
" for i be NatNAT-1M1 holds  for D be setHIDDENM2 holds  for P be FinSequenceFINSEQ-1M3-of D holds \<one>\<^sub>M <=XXREAL-0R1 i & i <=XXREAL-0R1 lenFINSEQ-1K4 P implies P /.PARTFUN1K7\<^bsub>(D)\<^esub> i =XBOOLE-0R4 P .FUNCT-1K1 i"
sorry

mtheorem finseq_4_th_16:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d be ElementSUBSET-1M1-of D holds (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>)/.PARTFUN1K7\<^bsub>(D)\<^esub> \<one>\<^sub>M =XBOOLE-0R4 d"
sorry

mtheorem finseq_4_th_17:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d1 be ElementSUBSET-1M1-of D holds  for d2 be ElementSUBSET-1M1-of D holds (<*FINSEQ-4K2\<^bsub>(D)\<^esub> d1,d2 *>)/.PARTFUN1K7\<^bsub>(D)\<^esub> \<one>\<^sub>M =XBOOLE-0R4 d1 & (<*FINSEQ-4K2\<^bsub>(D)\<^esub> d1,d2 *>)/.PARTFUN1K7\<^bsub>(D)\<^esub> \<two>\<^sub>M =XBOOLE-0R4 d2"
sorry

mtheorem finseq_4_th_18:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d1 be ElementSUBSET-1M1-of D holds  for d2 be ElementSUBSET-1M1-of D holds  for d3 be ElementSUBSET-1M1-of D holds ((<*FINSEQ-4K3\<^bsub>(D)\<^esub> d1,d2,d3 *>)/.PARTFUN1K7\<^bsub>(D)\<^esub> \<one>\<^sub>M =XBOOLE-0R4 d1 & (<*FINSEQ-4K3\<^bsub>(D)\<^esub> d1,d2,d3 *>)/.PARTFUN1K7\<^bsub>(D)\<^esub> \<two>\<^sub>M =XBOOLE-0R4 d2) & (<*FINSEQ-4K3\<^bsub>(D)\<^esub> d1,d2,d3 *>)/.PARTFUN1K7\<^bsub>(D)\<^esub> \<three>\<^sub>M =XBOOLE-0R4 d3"
sorry

mdef finseq_4_def_4 (" _ ..FINSEQ-4K4  _ " [200,200]200 ) where
  mlet "p be FinSequenceFINSEQ-1M1", "x be objectHIDDENM1"
"func x ..FINSEQ-4K4 p \<rightarrow> ElementSUBSET-1M1-of NATNUMBERSK1 equals
  SgmFINSEQ-1K15 (p \<inverse>FUNCT-1K6 {TARSKIK1 x}) .FUNCT-1K1 \<one>\<^sub>M"
proof-
  (*coherence*)
    show "SgmFINSEQ-1K15 (p \<inverse>FUNCT-1K6 {TARSKIK1 x}) .FUNCT-1K1 \<one>\<^sub>M be ElementSUBSET-1M1-of NATNUMBERSK1"
sorry
qed "sorry"

mtheorem finseq_4_th_19:
" for p be FinSequenceFINSEQ-1M1 holds  for x be objectHIDDENM1 holds x inHIDDENR3 rngFUNCT-1K2 p implies p .FUNCT-1K1 (x ..FINSEQ-4K4 p) =HIDDENR1 x"
sorry

mtheorem finseq_4_th_20:
" for p be FinSequenceFINSEQ-1M1 holds  for x be objectHIDDENM1 holds x inHIDDENR3 rngFUNCT-1K2 p implies x ..FINSEQ-4K4 p inTARSKIR2 domFINSEQ-1K5 p"
sorry

mtheorem finseq_4_th_21:
" for p be FinSequenceFINSEQ-1M1 holds  for x be objectHIDDENM1 holds x inHIDDENR3 rngFUNCT-1K2 p implies \<one>\<^sub>M <=XXREAL-0R1 x ..FINSEQ-4K4 p & x ..FINSEQ-4K4 p <=XXREAL-0R1 lenFINSEQ-1K4 p"
sorry

mtheorem finseq_4_th_22:
" for p be FinSequenceFINSEQ-1M1 holds  for x be objectHIDDENM1 holds x inHIDDENR3 rngFUNCT-1K2 p implies x ..FINSEQ-4K4 p -XCMPLX-0K6 \<one>\<^sub>M be ElementSUBSET-1M1-of NATNUMBERSK1 & lenFINSEQ-1K4 p -XCMPLX-0K6 x ..FINSEQ-4K4 p be ElementSUBSET-1M1-of NATNUMBERSK1"
sorry

mtheorem finseq_4_th_23:
" for p be FinSequenceFINSEQ-1M1 holds  for x be objectHIDDENM1 holds x inHIDDENR3 rngFUNCT-1K2 p implies x ..FINSEQ-4K4 p inTARSKIR2 p \<inverse>FUNCT-1K6 {TARSKIK1 x}"
sorry

mtheorem finseq_4_th_24:
" for p be FinSequenceFINSEQ-1M1 holds  for x be objectHIDDENM1 holds  for k be NatNAT-1M1 holds k inTARSKIR2 domFINSEQ-1K5 p & k <XXREAL-0R3 x ..FINSEQ-4K4 p implies p .FUNCT-1K1 k <>HIDDENR2 x"
sorry

mtheorem finseq_4_th_25:
" for p be FinSequenceFINSEQ-1M1 holds  for x be objectHIDDENM1 holds p just-once-valuesFINSEQ-4R2 x implies p <-FINSEQ-4K1 x =XBOOLE-0R4 x ..FINSEQ-4K4 p"
sorry

mtheorem finseq_4_th_26:
" for p be FinSequenceFINSEQ-1M1 holds  for x be objectHIDDENM1 holds p just-once-valuesFINSEQ-4R2 x implies ( for k be NatNAT-1M1 holds k inTARSKIR2 domFINSEQ-1K5 p & k <>HIDDENR2 x ..FINSEQ-4K4 p implies p .FUNCT-1K1 k <>HIDDENR2 x)"
sorry

mtheorem finseq_4_th_27:
" for p be FinSequenceFINSEQ-1M1 holds  for x be objectHIDDENM1 holds x inHIDDENR3 rngFUNCT-1K2 p & ( for k be NatNAT-1M1 holds k inTARSKIR2 domFINSEQ-1K5 p & k <>HIDDENR2 x ..FINSEQ-4K4 p implies p .FUNCT-1K1 k <>HIDDENR2 x) implies p just-once-valuesFINSEQ-4R2 x"
sorry

mtheorem finseq_4_th_28:
" for p be FinSequenceFINSEQ-1M1 holds  for x be objectHIDDENM1 holds p just-once-valuesFINSEQ-4R2 x iff x inHIDDENR3 rngFUNCT-1K2 p & {TARSKIK1 x ..FINSEQ-4K4 p } =XBOOLE-0R4 p \<inverse>FUNCT-1K6 {TARSKIK1 x}"
sorry

mtheorem finseq_4_th_29:
" for p be FinSequenceFINSEQ-1M1 holds  for x be objectHIDDENM1 holds p be one-to-oneFUNCT-1V2 & x inHIDDENR3 rngFUNCT-1K2 p implies {TARSKIK1 x ..FINSEQ-4K4 p } =XBOOLE-0R4 p \<inverse>FUNCT-1K6 {TARSKIK1 x}"
sorry

mtheorem finseq_4_th_30:
" for p be FinSequenceFINSEQ-1M1 holds  for x be objectHIDDENM1 holds p just-once-valuesFINSEQ-4R2 x iff lenFINSEQ-1K4 (p -FINSEQ-3K1 {TARSKIK1 x}) =XBOOLE-0R4 lenFINSEQ-1K4 p -XCMPLX-0K6 \<one>\<^sub>M"
sorry

reserve L, M for "ElementSUBSET-1M1-of NATNUMBERSK1"
mtheorem finseq_4_th_31:
" for p be FinSequenceFINSEQ-1M1 holds  for x be objectHIDDENM1 holds p just-once-valuesFINSEQ-4R2 x implies ( for k be NatNAT-1M1 holds k inTARSKIR2 domFINSEQ-1K5 (p -FINSEQ-3K1 {TARSKIK1 x}) implies (k <XXREAL-0R3 x ..FINSEQ-4K4 p implies (p -FINSEQ-3K1 {TARSKIK1 x}).FUNCT-1K1 k =XBOOLE-0R4 p .FUNCT-1K1 k) & (x ..FINSEQ-4K4 p <=XXREAL-0R1 k implies (p -FINSEQ-3K1 {TARSKIK1 x}).FUNCT-1K1 k =XBOOLE-0R4 p .FUNCT-1K1 (k +NAT-1K1 \<one>\<^sub>M)))"
sorry

mtheorem finseq_4_th_32:
" for p be FinSequenceFINSEQ-1M1 holds  for x be objectHIDDENM1 holds p be one-to-oneFUNCT-1V2 & x inHIDDENR3 rngFUNCT-1K2 p implies ( for k be NatNAT-1M1 holds k inTARSKIR2 domFINSEQ-1K5 (p -FINSEQ-3K1 {TARSKIK1 x}) implies ((p -FINSEQ-3K1 {TARSKIK1 x}).FUNCT-1K1 k =XBOOLE-0R4 p .FUNCT-1K1 k iff k <XXREAL-0R3 x ..FINSEQ-4K4 p) & ((p -FINSEQ-3K1 {TARSKIK1 x}).FUNCT-1K1 k =XBOOLE-0R4 p .FUNCT-1K1 (k +NAT-1K1 \<one>\<^sub>M) iff x ..FINSEQ-4K4 p <=XXREAL-0R1 k))"
sorry

mdef finseq_4_def_5 (" _ -|FINSEQ-4K5  _ " [132,132]132 ) where
  mlet "p be FinSequenceFINSEQ-1M1", "x be objectHIDDENM1"
"assume x inHIDDENR3 rngFUNCT-1K2 p func p -|FINSEQ-4K5 x \<rightarrow> FinSequenceFINSEQ-1M1 means
  \<lambda>it.  ex n be NatNAT-1M1 st n =XBOOLE-0R4 x ..FINSEQ-4K4 p -XCMPLX-0K6 \<one>\<^sub>M & it =FUNCT-1R1 p |RELAT-1K8 SegFINSEQ-1K2 n"
proof-
  (*existence*)
    show "x inHIDDENR3 rngFUNCT-1K2 p implies ( ex it be FinSequenceFINSEQ-1M1 st  ex n be NatNAT-1M1 st n =XBOOLE-0R4 x ..FINSEQ-4K4 p -XCMPLX-0K6 \<one>\<^sub>M & it =FUNCT-1R1 p |RELAT-1K8 SegFINSEQ-1K2 n)"
sorry
  (*uniqueness*)
    show "x inHIDDENR3 rngFUNCT-1K2 p implies ( for it1 be FinSequenceFINSEQ-1M1 holds  for it2 be FinSequenceFINSEQ-1M1 holds ( ex n be NatNAT-1M1 st n =XBOOLE-0R4 x ..FINSEQ-4K4 p -XCMPLX-0K6 \<one>\<^sub>M & it1 =FUNCT-1R1 p |RELAT-1K8 SegFINSEQ-1K2 n) & ( ex n be NatNAT-1M1 st n =XBOOLE-0R4 x ..FINSEQ-4K4 p -XCMPLX-0K6 \<one>\<^sub>M & it2 =FUNCT-1R1 p |RELAT-1K8 SegFINSEQ-1K2 n) implies it1 =HIDDENR1 it2)"
sorry
qed "sorry"

mtheorem finseq_4_th_33:
" for p be FinSequenceFINSEQ-1M1 holds  for x be objectHIDDENM1 holds  for n be NatNAT-1M1 holds x inHIDDENR3 rngFUNCT-1K2 p & n =XBOOLE-0R4 x ..FINSEQ-4K4 p -XCMPLX-0K6 \<one>\<^sub>M implies p |RELAT-1K8 SegFINSEQ-1K2 n =FUNCT-1R1 p -|FINSEQ-4K5 x"
sorry

mtheorem finseq_4_th_34:
" for p be FinSequenceFINSEQ-1M1 holds  for x be objectHIDDENM1 holds x inHIDDENR3 rngFUNCT-1K2 p implies lenFINSEQ-1K4 (p -|FINSEQ-4K5 x) =XBOOLE-0R4 x ..FINSEQ-4K4 p -XCMPLX-0K6 \<one>\<^sub>M"
sorry

mtheorem finseq_4_th_35:
" for p be FinSequenceFINSEQ-1M1 holds  for x be objectHIDDENM1 holds  for n be NatNAT-1M1 holds x inHIDDENR3 rngFUNCT-1K2 p & n =XBOOLE-0R4 x ..FINSEQ-4K4 p -XCMPLX-0K6 \<one>\<^sub>M implies domFINSEQ-1K5 (p -|FINSEQ-4K5 x) =XBOOLE-0R4 SegFINSEQ-1K2 n"
sorry

mtheorem finseq_4_th_36:
" for p be FinSequenceFINSEQ-1M1 holds  for x be objectHIDDENM1 holds  for k be NatNAT-1M1 holds x inHIDDENR3 rngFUNCT-1K2 p & k inTARSKIR2 domFINSEQ-1K5 (p -|FINSEQ-4K5 x) implies p .FUNCT-1K1 k =XBOOLE-0R4 (p -|FINSEQ-4K5 x).FUNCT-1K1 k"
sorry

mtheorem finseq_4_th_37:
" for p be FinSequenceFINSEQ-1M1 holds  for x be objectHIDDENM1 holds x inHIDDENR3 rngFUNCT-1K2 p implies  not x inHIDDENR3 rngFUNCT-1K2 (p -|FINSEQ-4K5 x)"
sorry

mtheorem finseq_4_th_38:
" for p be FinSequenceFINSEQ-1M1 holds  for x be objectHIDDENM1 holds x inHIDDENR3 rngFUNCT-1K2 p implies rngFUNCT-1K2 (p -|FINSEQ-4K5 x) missesXBOOLE-0R1 {TARSKIK1 x}"
sorry

mtheorem finseq_4_th_39:
" for p be FinSequenceFINSEQ-1M1 holds  for x be objectHIDDENM1 holds x inHIDDENR3 rngFUNCT-1K2 p implies rngFUNCT-1K2 (p -|FINSEQ-4K5 x) c=TARSKIR1 rngFUNCT-1K2 p"
sorry

mtheorem finseq_4_th_40:
" for p be FinSequenceFINSEQ-1M1 holds  for x be objectHIDDENM1 holds x inHIDDENR3 rngFUNCT-1K2 p implies (x ..FINSEQ-4K4 p =XBOOLE-0R4 \<one>\<^sub>M iff p -|FINSEQ-4K5 x =FINSEQ-1R1 {}XBOOLE-0K1)"
sorry

mtheorem finseq_4_th_41:
" for p be FinSequenceFINSEQ-1M1 holds  for x be objectHIDDENM1 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds x inHIDDENR3 rngFUNCT-1K2 p & p be FinSequenceFINSEQ-1M3-of D implies p -|FINSEQ-4K5 x be FinSequenceFINSEQ-1M3-of D"
sorry

mdef finseq_4_def_6 (" _ |--FINSEQ-4K6  _ " [132,132]132 ) where
  mlet "p be FinSequenceFINSEQ-1M1", "x be objectHIDDENM1"
"assume x inHIDDENR3 rngFUNCT-1K2 p func p |--FINSEQ-4K6 x \<rightarrow> FinSequenceFINSEQ-1M1 means
  \<lambda>it. lenFINSEQ-1K4 it =XBOOLE-0R4 lenFINSEQ-1K4 p -XCMPLX-0K6 x ..FINSEQ-4K4 p & ( for k be NatNAT-1M1 holds k inTARSKIR2 domFINSEQ-1K5 it implies it .FUNCT-1K1 k =XBOOLE-0R4 p .FUNCT-1K1 (k +NAT-1K1 x ..FINSEQ-4K4 p))"
proof-
  (*existence*)
    show "x inHIDDENR3 rngFUNCT-1K2 p implies ( ex it be FinSequenceFINSEQ-1M1 st lenFINSEQ-1K4 it =XBOOLE-0R4 lenFINSEQ-1K4 p -XCMPLX-0K6 x ..FINSEQ-4K4 p & ( for k be NatNAT-1M1 holds k inTARSKIR2 domFINSEQ-1K5 it implies it .FUNCT-1K1 k =XBOOLE-0R4 p .FUNCT-1K1 (k +NAT-1K1 x ..FINSEQ-4K4 p)))"
sorry
  (*uniqueness*)
    show "x inHIDDENR3 rngFUNCT-1K2 p implies ( for it1 be FinSequenceFINSEQ-1M1 holds  for it2 be FinSequenceFINSEQ-1M1 holds (lenFINSEQ-1K4 it1 =XBOOLE-0R4 lenFINSEQ-1K4 p -XCMPLX-0K6 x ..FINSEQ-4K4 p & ( for k be NatNAT-1M1 holds k inTARSKIR2 domFINSEQ-1K5 it1 implies it1 .FUNCT-1K1 k =XBOOLE-0R4 p .FUNCT-1K1 (k +NAT-1K1 x ..FINSEQ-4K4 p))) & (lenFINSEQ-1K4 it2 =XBOOLE-0R4 lenFINSEQ-1K4 p -XCMPLX-0K6 x ..FINSEQ-4K4 p & ( for k be NatNAT-1M1 holds k inTARSKIR2 domFINSEQ-1K5 it2 implies it2 .FUNCT-1K1 k =XBOOLE-0R4 p .FUNCT-1K1 (k +NAT-1K1 x ..FINSEQ-4K4 p))) implies it1 =HIDDENR1 it2)"
sorry
qed "sorry"

mtheorem finseq_4_th_42:
" for p be FinSequenceFINSEQ-1M1 holds  for x be objectHIDDENM1 holds  for n be NatNAT-1M1 holds x inHIDDENR3 rngFUNCT-1K2 p & n =XBOOLE-0R4 lenFINSEQ-1K4 p -XCMPLX-0K6 x ..FINSEQ-4K4 p implies domFINSEQ-1K5 (p |--FINSEQ-4K6 x) =XBOOLE-0R4 SegFINSEQ-1K2 n"
sorry

mtheorem finseq_4_th_43:
" for p be FinSequenceFINSEQ-1M1 holds  for x be objectHIDDENM1 holds  for n be NatNAT-1M1 holds x inHIDDENR3 rngFUNCT-1K2 p & n inTARSKIR2 domFINSEQ-1K5 (p |--FINSEQ-4K6 x) implies n +NAT-1K1 x ..FINSEQ-4K4 p inTARSKIR2 domFINSEQ-1K5 p"
sorry

mtheorem finseq_4_th_44:
" for p be FinSequenceFINSEQ-1M1 holds  for x be objectHIDDENM1 holds x inHIDDENR3 rngFUNCT-1K2 p implies rngFUNCT-1K2 (p |--FINSEQ-4K6 x) c=TARSKIR1 rngFUNCT-1K2 p"
sorry

mtheorem finseq_4_th_45:
" for p be FinSequenceFINSEQ-1M1 holds  for x be objectHIDDENM1 holds p just-once-valuesFINSEQ-4R2 x iff x inHIDDENR3 rngFUNCT-1K2 p &  not x inHIDDENR3 rngFUNCT-1K2 (p |--FINSEQ-4K6 x)"
sorry

mtheorem finseq_4_th_46:
" for p be FinSequenceFINSEQ-1M1 holds  for x be objectHIDDENM1 holds x inHIDDENR3 rngFUNCT-1K2 p & p be one-to-oneFUNCT-1V2 implies  not x inHIDDENR3 rngFUNCT-1K2 (p |--FINSEQ-4K6 x)"
sorry

mtheorem finseq_4_th_47:
" for p be FinSequenceFINSEQ-1M1 holds  for x be objectHIDDENM1 holds p just-once-valuesFINSEQ-4R2 x iff x inHIDDENR3 rngFUNCT-1K2 p & rngFUNCT-1K2 (p |--FINSEQ-4K6 x) missesXBOOLE-0R1 {TARSKIK1 x}"
sorry

mtheorem finseq_4_th_48:
" for p be FinSequenceFINSEQ-1M1 holds  for x be objectHIDDENM1 holds x inHIDDENR3 rngFUNCT-1K2 p & p be one-to-oneFUNCT-1V2 implies rngFUNCT-1K2 (p |--FINSEQ-4K6 x) missesXBOOLE-0R1 {TARSKIK1 x}"
sorry

mtheorem finseq_4_th_49:
" for p be FinSequenceFINSEQ-1M1 holds  for x be objectHIDDENM1 holds x inHIDDENR3 rngFUNCT-1K2 p implies (x ..FINSEQ-4K4 p =XBOOLE-0R4 lenFINSEQ-1K4 p iff p |--FINSEQ-4K6 x =FINSEQ-1R1 {}XBOOLE-0K1)"
sorry

mtheorem finseq_4_th_50:
" for p be FinSequenceFINSEQ-1M1 holds  for x be objectHIDDENM1 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds x inHIDDENR3 rngFUNCT-1K2 p & p be FinSequenceFINSEQ-1M3-of D implies p |--FINSEQ-4K6 x be FinSequenceFINSEQ-1M3-of D"
sorry

mtheorem finseq_4_th_51:
" for p be FinSequenceFINSEQ-1M1 holds  for x be objectHIDDENM1 holds x inHIDDENR3 rngFUNCT-1K2 p implies p =FINSEQ-1R1 ((p -|FINSEQ-4K5 x)^FINSEQ-1K8 (<*FINSEQ-1K10 x*>))^FINSEQ-1K8 (p |--FINSEQ-4K6 x)"
sorry

mtheorem finseq_4_th_52:
" for p be FinSequenceFINSEQ-1M1 holds  for x be objectHIDDENM1 holds x inHIDDENR3 rngFUNCT-1K2 p & p be one-to-oneFUNCT-1V2 implies p -|FINSEQ-4K5 x be one-to-oneFUNCT-1V2"
sorry

mtheorem finseq_4_th_53:
" for p be FinSequenceFINSEQ-1M1 holds  for x be objectHIDDENM1 holds x inHIDDENR3 rngFUNCT-1K2 p & p be one-to-oneFUNCT-1V2 implies p |--FINSEQ-4K6 x be one-to-oneFUNCT-1V2"
sorry

mtheorem finseq_4_th_54:
" for p be FinSequenceFINSEQ-1M1 holds  for x be objectHIDDENM1 holds p just-once-valuesFINSEQ-4R2 x iff x inHIDDENR3 rngFUNCT-1K2 p & p -FINSEQ-3K1 {TARSKIK1 x} =FINSEQ-1R1 (p -|FINSEQ-4K5 x)^FINSEQ-1K8 (p |--FINSEQ-4K6 x)"
sorry

mtheorem finseq_4_th_55:
" for p be FinSequenceFINSEQ-1M1 holds  for x be objectHIDDENM1 holds x inHIDDENR3 rngFUNCT-1K2 p & p be one-to-oneFUNCT-1V2 implies p -FINSEQ-3K1 {TARSKIK1 x} =FINSEQ-1R1 (p -|FINSEQ-4K5 x)^FINSEQ-1K8 (p |--FINSEQ-4K6 x)"
sorry

mtheorem finseq_4_th_56:
" for p be FinSequenceFINSEQ-1M1 holds  for x be objectHIDDENM1 holds (x inHIDDENR3 rngFUNCT-1K2 p & p -FINSEQ-3K1 {TARSKIK1 x} be one-to-oneFUNCT-1V2) & p -FINSEQ-3K1 {TARSKIK1 x} =FINSEQ-1R1 (p -|FINSEQ-4K5 x)^FINSEQ-1K8 (p |--FINSEQ-4K6 x) implies p be one-to-oneFUNCT-1V2"
sorry

mtheorem finseq_4_th_57:
" for p be FinSequenceFINSEQ-1M1 holds  for x be objectHIDDENM1 holds x inHIDDENR3 rngFUNCT-1K2 p & p be one-to-oneFUNCT-1V2 implies rngFUNCT-1K2 (p -|FINSEQ-4K5 x) missesXBOOLE-0R1 rngFUNCT-1K2 (p |--FINSEQ-4K6 x)"
sorry

mtheorem finseq_4_th_58:
" for A be setHIDDENM2 holds A be finiteFINSET-1V1 implies ( ex p be FinSequenceFINSEQ-1M1 st rngFUNCT-1K2 p =XBOOLE-0R4 A & p be one-to-oneFUNCT-1V2)"
sorry

mtheorem finseq_4_th_59:
" for p be FinSequenceFINSEQ-1M1 holds rngFUNCT-1K2 p c=TARSKIR1 domFINSEQ-1K5 p & p be one-to-oneFUNCT-1V2 implies rngFUNCT-1K2 p =XBOOLE-0R4 domFINSEQ-1K5 p"
sorry

mtheorem finseq_4_th_60:
" for p be FinSequenceFINSEQ-1M1 holds rngFUNCT-1K2 p =XBOOLE-0R4 domFINSEQ-1K5 p implies p be one-to-oneFUNCT-1V2"
sorry

mtheorem finseq_4_th_61:
" for p be FinSequenceFINSEQ-1M1 holds  for q be FinSequenceFINSEQ-1M1 holds (rngFUNCT-1K2 p =XBOOLE-0R4 rngFUNCT-1K2 q & lenFINSEQ-1K4 p =XBOOLE-0R4 lenFINSEQ-1K4 q) & q be one-to-oneFUNCT-1V2 implies p be one-to-oneFUNCT-1V2"
sorry

mlemma finseq_4_lm_1:
" for A be finiteFINSET-1V1\<bar>setHIDDENM2 holds  for B be finiteFINSET-1V1\<bar>setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(A,B) holds cardCARD-1K4 A =XBOOLE-0R4 cardCARD-1K4 B & rngFUNCT-1K2 f =XBOOLE-0R4 B implies f be one-to-oneFUNCT-1V2"
sorry

mtheorem finseq_4_th_62:
" for p be FinSequenceFINSEQ-1M1 holds p be one-to-oneFUNCT-1V2 iff cardCARD-1K4 (rngFUNCT-1K2 p) =XBOOLE-0R4 lenFINSEQ-1K4 p"
sorry

reserve f for "FunctionFUNCT-2M1-of(A,B)"
mtheorem finseq_4_th_63:
" for A be finiteFINSET-1V1\<bar>setHIDDENM2 holds  for B be finiteFINSET-1V1\<bar>setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(A,B) holds cardCARD-1K4 A =XBOOLE-0R4 cardCARD-1K4 B & f be one-to-oneFUNCT-1V2 implies rngFUNCT-1K2 f =XBOOLE-0R4 B"
sorry

mtheorem finseq_4_th_64:
" for A be finiteFINSET-1V1\<bar>setHIDDENM2 holds  for B be finiteFINSET-1V1\<bar>setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(A,B) holds cardCARD-1K4 A =XBOOLE-0R4 cardCARD-1K4 B & rngFUNCT-1K2 f =XBOOLE-0R4 B implies f be one-to-oneFUNCT-1V2"
  using finseq_4_lm_1 sorry

(*\$N Dirichlet Principle*)
(*\$N Pigeon Hole Principle*)
mtheorem finseq_4_th_65:
" for A be setHIDDENM2 holds  for B be setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(A,B) holds cardCARD-1K1 B inTARSKIR2 cardCARD-1K1 A & B <>HIDDENR2 {}XBOOLE-0K1 implies ( ex x be objectHIDDENM1 st  ex y be objectHIDDENM1 st ((x inHIDDENR3 A & y inHIDDENR3 A) & x <>HIDDENR2 y) & f .FUNCT-1K1 x =XBOOLE-0R4 f .FUNCT-1K1 y)"
sorry

mtheorem finseq_4_th_66:
" for A be setHIDDENM2 holds  for B be setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(A,B) holds cardCARD-1K1 A inTARSKIR2 cardCARD-1K1 B implies ( ex x be objectHIDDENM1 st x inHIDDENR3 B & ( for y be objectHIDDENM1 holds y inHIDDENR3 A implies f .FUNCT-1K1 y <>HIDDENR2 x))"
sorry

(*begin*)
mtheorem finseq_4_th_67:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for f be FinSequenceFINSEQ-1M3-of D holds  for p be ElementSUBSET-1M1-of D holds (f ^FINSEQ-1K9\<^bsub>(D)\<^esub> (<*FINSEQ-1K13\<^bsub>(D)\<^esub> p*>))/.PARTFUN1K7\<^bsub>(D)\<^esub> (lenFINSEQ-1K4 f +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 p"
sorry

mtheorem finseq_4_th_68:
" for k be NatNAT-1M1 holds  for E be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for p be FinSequenceFINSEQ-1M3-of E holds  for q be FinSequenceFINSEQ-1M3-of E holds k inTARSKIR2 domFINSEQ-1K5 p implies (p ^FINSEQ-1K9\<^bsub>(E)\<^esub> q)/.PARTFUN1K7\<^bsub>(E)\<^esub> k =XBOOLE-0R4 p /.PARTFUN1K7\<^bsub>(E)\<^esub> k"
sorry

mtheorem finseq_4_th_69:
" for k be NatNAT-1M1 holds  for E be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for p be FinSequenceFINSEQ-1M3-of E holds  for q be FinSequenceFINSEQ-1M3-of E holds k inTARSKIR2 domFINSEQ-1K5 q implies (p ^FINSEQ-1K9\<^bsub>(E)\<^esub> q)/.PARTFUN1K7\<^bsub>(E)\<^esub> (lenFINSEQ-1K4 p +XCMPLX-0K2 k) =XBOOLE-0R4 q /.PARTFUN1K7\<^bsub>(E)\<^esub> k"
sorry

mtheorem finseq_4_th_70:
" for a be NatNAT-1M1 holds  for m be NatNAT-1M1 holds  for D be setHIDDENM2 holds  for p be FinSequenceFINSEQ-1M3-of D holds a inTARSKIR2 domFINSEQ-1K5 (p |FINSEQ-1K18\<^bsub>(D)\<^esub> m) implies (p |FINSEQ-1K18\<^bsub>(D)\<^esub> m)/.PARTFUN1K7\<^bsub>(D)\<^esub> a =XBOOLE-0R4 p /.PARTFUN1K7\<^bsub>(D)\<^esub> a"
sorry

mtheorem finseq_4_th_71:
" for D be setHIDDENM2 holds  for f be FinSequenceFINSEQ-1M3-of D holds  for n be NatNAT-1M1 holds  for m be NatNAT-1M1 holds n inTARSKIR2 domFINSEQ-1K5 f & m inTARSKIR2 SegFINSEQ-1K2 n implies m inTARSKIR2 domFINSEQ-1K5 f & (f |FINSEQ-1K18\<^bsub>(D)\<^esub> n)/.PARTFUN1K7\<^bsub>(D)\<^esub> m =XBOOLE-0R4 f /.PARTFUN1K7\<^bsub>(D)\<^esub> m"
sorry

mtheorem finseq_4_th_72:
" for n be NatNAT-1M1 holds  for X be finiteFINSET-1V1\<bar>setHIDDENM2 holds n <=XXREAL-0R1 cardCARD-1K4 X implies ( ex A be finiteFINSET-1V1\<bar>SubsetSUBSET-1M2-of X st cardCARD-1K4 A =XBOOLE-0R4 n)"
sorry

reserve f for "FunctionFUNCT-1M1"
mtheorem finseq_4_th_73:
" for x be objectHIDDENM1 holds  for f be FunctionFUNCT-1M1 holds f be one-to-oneFUNCT-1V2 & x inHIDDENR3 rngFUNCT-1K2 f implies cardCARD-1K1 (CoimRELAT-1K13(f,x)) =XBOOLE-0R4 \<one>\<^sub>M"
  using finseq_4_th_8 finseq_4_def_2 sorry

mdef finseq_4_def_7 ("<*FINSEQ-4K7 _ , _ , _ , _ *>" [0,0,0,0]164 ) where
  mlet "x1 be objectHIDDENM1", "x2 be objectHIDDENM1", "x3 be objectHIDDENM1", "x4 be objectHIDDENM1"
"func <*FINSEQ-4K7 x1,x2,x3,x4 *> \<rightarrow> setHIDDENM2 equals
  (<*FINSEQ-1K12 x1,x2,x3 *>)^FINSEQ-1K8 (<*FINSEQ-1K10 x4*>)"
proof-
  (*coherence*)
    show "(<*FINSEQ-1K12 x1,x2,x3 *>)^FINSEQ-1K8 (<*FINSEQ-1K10 x4*>) be setHIDDENM2"
       sorry
qed "sorry"

mdef finseq_4_def_8 ("<*FINSEQ-4K8 _ , _ , _ , _ , _ *>" [0,0,0,0,0]164 ) where
  mlet "x1 be objectHIDDENM1", "x2 be objectHIDDENM1", "x3 be objectHIDDENM1", "x4 be objectHIDDENM1", "x5 be objectHIDDENM1"
"func <*FINSEQ-4K8 x1,x2,x3,x4,x5 *> \<rightarrow> setHIDDENM2 equals
  (<*FINSEQ-1K12 x1,x2,x3 *>)^FINSEQ-1K8 (<*FINSEQ-1K11 x4,x5 *>)"
proof-
  (*coherence*)
    show "(<*FINSEQ-1K12 x1,x2,x3 *>)^FINSEQ-1K8 (<*FINSEQ-1K11 x4,x5 *>) be setHIDDENM2"
       sorry
qed "sorry"

mtheorem finseq_4_cl_1:
  mlet "x1 be objectHIDDENM1", "x2 be objectHIDDENM1", "x3 be objectHIDDENM1", "x4 be objectHIDDENM1"
"cluster <*FINSEQ-4K7 x1,x2,x3,x4 *> as-term-is  non emptyXBOOLE-0V1\<bar>Function-likeFUNCT-1V1\<bar>Relation-likeRELAT-1V1"
proof
(*coherence*)
  show "<*FINSEQ-4K7 x1,x2,x3,x4 *> be  non emptyXBOOLE-0V1\<bar>Function-likeFUNCT-1V1\<bar>Relation-likeRELAT-1V1"
     sorry
qed "sorry"

mtheorem finseq_4_cl_2:
  mlet "x1 be objectHIDDENM1", "x2 be objectHIDDENM1", "x3 be objectHIDDENM1", "x4 be objectHIDDENM1", "x5 be objectHIDDENM1"
"cluster <*FINSEQ-4K8 x1,x2,x3,x4,x5 *> as-term-is  non emptyXBOOLE-0V1\<bar>Function-likeFUNCT-1V1\<bar>Relation-likeRELAT-1V1"
proof
(*coherence*)
  show "<*FINSEQ-4K8 x1,x2,x3,x4,x5 *> be  non emptyXBOOLE-0V1\<bar>Function-likeFUNCT-1V1\<bar>Relation-likeRELAT-1V1"
     sorry
qed "sorry"

mtheorem finseq_4_cl_3:
  mlet "x1 be objectHIDDENM1", "x2 be objectHIDDENM1", "x3 be objectHIDDENM1", "x4 be objectHIDDENM1"
"cluster <*FINSEQ-4K7 x1,x2,x3,x4 *> as-term-is FinSequence-likeFINSEQ-1V1"
proof
(*coherence*)
  show "<*FINSEQ-4K7 x1,x2,x3,x4 *> be FinSequence-likeFINSEQ-1V1"
     sorry
qed "sorry"

mtheorem finseq_4_cl_4:
  mlet "x1 be objectHIDDENM1", "x2 be objectHIDDENM1", "x3 be objectHIDDENM1", "x4 be objectHIDDENM1", "x5 be objectHIDDENM1"
"cluster <*FINSEQ-4K8 x1,x2,x3,x4,x5 *> as-term-is FinSequence-likeFINSEQ-1V1"
proof
(*coherence*)
  show "<*FINSEQ-4K8 x1,x2,x3,x4,x5 *> be FinSequence-likeFINSEQ-1V1"
     sorry
qed "sorry"

syntax FINSEQ_4K9 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" ("<*FINSEQ-4K9\<^bsub>'( _ ')\<^esub> _ , _ , _ , _ *>" [0,0,0,0,0]164)
translations "<*FINSEQ-4K9\<^bsub>(D)\<^esub> x1,x2,x3,x4 *>" \<rightharpoonup> "<*FINSEQ-4K7 x1,x2,x3,x4 *>"

mtheorem finseq_4_add_3:
  mlet "D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "x1 be ElementSUBSET-1M1-of D", "x2 be ElementSUBSET-1M1-of D", "x3 be ElementSUBSET-1M1-of D", "x4 be ElementSUBSET-1M1-of D"
"cluster <*FINSEQ-4K7 x1,x2,x3,x4 *> as-term-is FinSequenceFINSEQ-1M3-of D"
proof
(*coherence*)
  show "<*FINSEQ-4K7 x1,x2,x3,x4 *> be FinSequenceFINSEQ-1M3-of D"
sorry
qed "sorry"

syntax FINSEQ_4K10 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" ("<*FINSEQ-4K10\<^bsub>'( _ ')\<^esub> _ , _ , _ , _ , _ *>" [0,0,0,0,0,0]164)
translations "<*FINSEQ-4K10\<^bsub>(D)\<^esub> x1,x2,x3,x4,x5 *>" \<rightharpoonup> "<*FINSEQ-4K8 x1,x2,x3,x4,x5 *>"

mtheorem finseq_4_add_4:
  mlet "D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "x1 be ElementSUBSET-1M1-of D", "x2 be ElementSUBSET-1M1-of D", "x3 be ElementSUBSET-1M1-of D", "x4 be ElementSUBSET-1M1-of D", "x5 be ElementSUBSET-1M1-of D"
"cluster <*FINSEQ-4K8 x1,x2,x3,x4,x5 *> as-term-is FinSequenceFINSEQ-1M3-of D"
proof
(*coherence*)
  show "<*FINSEQ-4K8 x1,x2,x3,x4,x5 *> be FinSequenceFINSEQ-1M3-of D"
sorry
qed "sorry"

reserve x1, x2, x3, x4, x5 for "objectHIDDENM1"
mtheorem finseq_4_th_74:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for x4 be objectHIDDENM1 holds ((<*FINSEQ-4K7 x1,x2,x3,x4 *> =FINSEQ-1R1 (<*FINSEQ-1K12 x1,x2,x3 *>)^FINSEQ-1K8 (<*FINSEQ-1K10 x4*>) & <*FINSEQ-4K7 x1,x2,x3,x4 *> =FINSEQ-1R1 (<*FINSEQ-1K11 x1,x2 *>)^FINSEQ-1K8 (<*FINSEQ-1K11 x3,x4 *>)) & <*FINSEQ-4K7 x1,x2,x3,x4 *> =FINSEQ-1R1 (<*FINSEQ-1K10 x1*>)^FINSEQ-1K8 (<*FINSEQ-1K12 x2,x3,x4 *>)) & <*FINSEQ-4K7 x1,x2,x3,x4 *> =FINSEQ-1R1 (((<*FINSEQ-1K10 x1*>)^FINSEQ-1K8 (<*FINSEQ-1K10 x2*>))^FINSEQ-1K8 (<*FINSEQ-1K10 x3*>))^FINSEQ-1K8 (<*FINSEQ-1K10 x4*>)"
sorry

mtheorem finseq_4_th_75:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for x4 be objectHIDDENM1 holds  for x5 be objectHIDDENM1 holds (((<*FINSEQ-4K8 x1,x2,x3,x4,x5 *> =FINSEQ-1R1 (<*FINSEQ-1K12 x1,x2,x3 *>)^FINSEQ-1K8 (<*FINSEQ-1K11 x4,x5 *>) & <*FINSEQ-4K8 x1,x2,x3,x4,x5 *> =FINSEQ-1R1 (<*FINSEQ-4K7 x1,x2,x3,x4 *>)^FINSEQ-1K8 (<*FINSEQ-1K10 x5*>)) & <*FINSEQ-4K8 x1,x2,x3,x4,x5 *> =FINSEQ-1R1 ((((<*FINSEQ-1K10 x1*>)^FINSEQ-1K8 (<*FINSEQ-1K10 x2*>))^FINSEQ-1K8 (<*FINSEQ-1K10 x3*>))^FINSEQ-1K8 (<*FINSEQ-1K10 x4*>))^FINSEQ-1K8 (<*FINSEQ-1K10 x5*>)) & <*FINSEQ-4K8 x1,x2,x3,x4,x5 *> =FINSEQ-1R1 (<*FINSEQ-1K11 x1,x2 *>)^FINSEQ-1K8 (<*FINSEQ-1K12 x3,x4,x5 *>)) & <*FINSEQ-4K8 x1,x2,x3,x4,x5 *> =FINSEQ-1R1 (<*FINSEQ-1K10 x1*>)^FINSEQ-1K8 (<*FINSEQ-4K7 x2,x3,x4,x5 *>)"
sorry

reserve p for "FinSequenceFINSEQ-1M1"
mtheorem finseq_4_th_76:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for x4 be objectHIDDENM1 holds  for p be FinSequenceFINSEQ-1M1 holds p =FINSEQ-1R1 <*FINSEQ-4K7 x1,x2,x3,x4 *> iff (((lenFINSEQ-1K4 p =XBOOLE-0R4 \<four>\<^sub>M & p .FUNCT-1K1 \<one>\<^sub>M =HIDDENR1 x1) & p .FUNCT-1K1 \<two>\<^sub>M =HIDDENR1 x2) & p .FUNCT-1K1 \<three>\<^sub>M =HIDDENR1 x3) & p .FUNCT-1K1 \<four>\<^sub>M =HIDDENR1 x4"
sorry

(*\$CT*)
mtheorem finseq_4_th_78:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for x4 be objectHIDDENM1 holds  for x5 be objectHIDDENM1 holds  for p be FinSequenceFINSEQ-1M1 holds p =FINSEQ-1R1 <*FINSEQ-4K8 x1,x2,x3,x4,x5 *> iff ((((lenFINSEQ-1K4 p =XBOOLE-0R4 \<five>\<^sub>M & p .FUNCT-1K1 \<one>\<^sub>M =HIDDENR1 x1) & p .FUNCT-1K1 \<two>\<^sub>M =HIDDENR1 x2) & p .FUNCT-1K1 \<three>\<^sub>M =HIDDENR1 x3) & p .FUNCT-1K1 \<four>\<^sub>M =HIDDENR1 x4) & p .FUNCT-1K1 \<five>\<^sub>M =HIDDENR1 x5"
sorry

reserve ND for " non emptyXBOOLE-0V1\<bar>setHIDDENM2"
reserve y1, y2, y3, y4, y5 for "ElementSUBSET-1M1-of ND"
(*\$CT*)
mtheorem finseq_4_th_80:
" for ND be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for y1 be ElementSUBSET-1M1-of ND holds  for y2 be ElementSUBSET-1M1-of ND holds  for y3 be ElementSUBSET-1M1-of ND holds  for y4 be ElementSUBSET-1M1-of ND holds (((<*FINSEQ-4K9\<^bsub>(ND)\<^esub> y1,y2,y3,y4 *>)/.PARTFUN1K7\<^bsub>(ND)\<^esub> \<one>\<^sub>M =XBOOLE-0R4 y1 & (<*FINSEQ-4K9\<^bsub>(ND)\<^esub> y1,y2,y3,y4 *>)/.PARTFUN1K7\<^bsub>(ND)\<^esub> \<two>\<^sub>M =XBOOLE-0R4 y2) & (<*FINSEQ-4K9\<^bsub>(ND)\<^esub> y1,y2,y3,y4 *>)/.PARTFUN1K7\<^bsub>(ND)\<^esub> \<three>\<^sub>M =XBOOLE-0R4 y3) & (<*FINSEQ-4K9\<^bsub>(ND)\<^esub> y1,y2,y3,y4 *>)/.PARTFUN1K7\<^bsub>(ND)\<^esub> \<four>\<^sub>M =XBOOLE-0R4 y4"
sorry

mtheorem finseq_4_th_81:
" for ND be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for y1 be ElementSUBSET-1M1-of ND holds  for y2 be ElementSUBSET-1M1-of ND holds  for y3 be ElementSUBSET-1M1-of ND holds  for y4 be ElementSUBSET-1M1-of ND holds  for y5 be ElementSUBSET-1M1-of ND holds ((((<*FINSEQ-4K10\<^bsub>(ND)\<^esub> y1,y2,y3,y4,y5 *>)/.PARTFUN1K7\<^bsub>(ND)\<^esub> \<one>\<^sub>M =XBOOLE-0R4 y1 & (<*FINSEQ-4K10\<^bsub>(ND)\<^esub> y1,y2,y3,y4,y5 *>)/.PARTFUN1K7\<^bsub>(ND)\<^esub> \<two>\<^sub>M =XBOOLE-0R4 y2) & (<*FINSEQ-4K10\<^bsub>(ND)\<^esub> y1,y2,y3,y4,y5 *>)/.PARTFUN1K7\<^bsub>(ND)\<^esub> \<three>\<^sub>M =XBOOLE-0R4 y3) & (<*FINSEQ-4K10\<^bsub>(ND)\<^esub> y1,y2,y3,y4,y5 *>)/.PARTFUN1K7\<^bsub>(ND)\<^esub> \<four>\<^sub>M =XBOOLE-0R4 y4) & (<*FINSEQ-4K10\<^bsub>(ND)\<^esub> y1,y2,y3,y4,y5 *>)/.PARTFUN1K7\<^bsub>(ND)\<^esub> \<five>\<^sub>M =XBOOLE-0R4 y5"
sorry

theorem finseq_4_sch_1:
  fixes Df0 Nf0 Pp2 
  assumes
[ty]: "Df0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
  [ty]: "Nf0 be NatNAT-1M1" and
   A1: " for n be NatNAT-1M1 holds n inTARSKIR2 SegFINSEQ-1K2 Nf0 implies ( ex d be ElementSUBSET-1M1-of Df0 st Pp2(n,d))"
  shows " ex f be FinSequenceFINSEQ-1M3-of Df0 st lenFINSEQ-1K4 f =XBOOLE-0R4 Nf0 & ( for n be NatNAT-1M1 holds n inTARSKIR2 SegFINSEQ-1K2 Nf0 implies Pp2(n,f /.PARTFUN1K7\<^bsub>(Df0)\<^esub> n))"
sorry

mtheorem finseq_4_th_82:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for p be FinSequenceFINSEQ-1M3-of D holds  for q be FinSequenceFINSEQ-1M3-of D holds p c=RELAT-1R2 q implies ( ex p9 be FinSequenceFINSEQ-1M3-of D st p ^FINSEQ-1K9\<^bsub>(D)\<^esub> p9 =FINSEQ-1R1 q)"
sorry

mtheorem finseq_4_th_83:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for p be FinSequenceFINSEQ-1M3-of D holds  for q be FinSequenceFINSEQ-1M3-of D holds  for i be ElementSUBSET-1M1-of NATNUMBERSK1 holds (p c=RELAT-1R2 q & \<one>\<^sub>M <=XXREAL-0R1 i) & i <=XXREAL-0R1 lenFINSEQ-1K4 p implies q .FUNCT-1K1 i =XBOOLE-0R4 p .FUNCT-1K1 i"
sorry

theorem finseq_4_sch_2:
  fixes Df0 lf0 Ff1 
  assumes
[ty]: "Df0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
  [ty]: "lf0 be NatNAT-1M1" and
  [ty_func]: "\<And> x1. x1 be setHIDDENM2 \<Longrightarrow> Ff1(x1) be ElementSUBSET-1M1-of Df0"
  shows " ex g be FinSequenceFINSEQ-1M3-of Df0 st lenFINSEQ-1K4 g =XBOOLE-0R4 lf0 & ( for n be NatNAT-1M1 holds n inTARSKIR2 domFINSEQ-1K5 g implies g /.PARTFUN1K7\<^bsub>(Df0)\<^esub> n =XBOOLE-0R4 Ff1(n))"
sorry

mtheorem finseq_4_cl_5:
  mlet "x1 be objectHIDDENM1", "x2 be objectHIDDENM1", "x3 be objectHIDDENM1", "x4 be objectHIDDENM1"
"cluster <*FINSEQ-4K7 x1,x2,x3,x4 *> as-term-is \<four>\<^sub>M -elementCARD-1V3"
proof
(*coherence*)
  show "<*FINSEQ-4K7 x1,x2,x3,x4 *> be \<four>\<^sub>M -elementCARD-1V3"
     sorry
qed "sorry"

mtheorem finseq_4_cl_6:
  mlet "x1 be objectHIDDENM1", "x2 be objectHIDDENM1", "x3 be objectHIDDENM1", "x4 be objectHIDDENM1", "x5 be objectHIDDENM1"
"cluster <*FINSEQ-4K8 x1,x2,x3,x4,x5 *> as-term-is \<five>\<^sub>M -elementCARD-1V3"
proof
(*coherence*)
  show "<*FINSEQ-4K8 x1,x2,x3,x4,x5 *> be \<five>\<^sub>M -elementCARD-1V3"
     sorry
qed "sorry"

(*begin*)
mtheorem finseq_4_th_84:
" for m be NatNAT-1M1 holds  for n be NatNAT-1M1 holds m <XXREAL-0R3 n implies ( ex p be ElementSUBSET-1M1-of NATNUMBERSK1 st n =XBOOLE-0R4 m +NAT-1K1 p & \<one>\<^sub>M <=XXREAL-0R1 p)"
sorry

mtheorem finseq_4_th_85:
" for S be setHIDDENM2 holds  for D1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D2 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for f1 be FunctionFUNCT-2M1-of(S,D1) holds  for f2 be FunctionFUNCT-2M1-of(D1,D2) holds f1 be bijectiveFUNCT-2V3\<^bsub>(S,D1)\<^esub> & f2 be bijectiveFUNCT-2V3\<^bsub>(D1,D2)\<^esub> implies f2 *PARTFUN1K1\<^bsub>(S,D1,D1,D2)\<^esub> f1 be bijectiveFUNCT-2V3\<^bsub>(S,D2)\<^esub>"
sorry

mtheorem finseq_4_th_86:
" for Y be setHIDDENM2 holds  for E1 be Equivalence-RelationEQREL-1M2-of Y holds  for E2 be Equivalence-RelationEQREL-1M2-of Y holds ClassEQREL-1K9\<^bsub>(Y)\<^esub> E1 =XBOOLE-0R4 ClassEQREL-1K9\<^bsub>(Y)\<^esub> E2 implies E1 =RELAT-1R1 E2"
sorry

mtheorem finseq_4_cl_7:
  mlet "Z be finiteFINSET-1V1\<bar>setHIDDENM2"
"cluster note-that finiteFINSET-1V1 for a-partitionEQREL-1M3-of Z"
proof
(*coherence*)
  show " for it be a-partitionEQREL-1M3-of Z holds it be finiteFINSET-1V1"
     sorry
qed "sorry"

mtheorem finseq_4_cl_8:
  mlet "X be  non emptyXBOOLE-0V1\<bar>finiteFINSET-1V1\<bar>setHIDDENM2"
"cluster  non emptyXBOOLE-0V1\<bar>finiteFINSET-1V1 for a-partitionEQREL-1M3-of X"
proof
(*existence*)
  show " ex it be a-partitionEQREL-1M3-of X st it be  non emptyXBOOLE-0V1\<bar>finiteFINSET-1V1"
sorry
qed "sorry"

reserve X, A for " non emptyXBOOLE-0V1\<bar>finiteFINSET-1V1\<bar>setHIDDENM2"
reserve PX for "a-partitionEQREL-1M3-of X"
reserve PA1, PA2 for "a-partitionEQREL-1M3-of A"
mtheorem finseq_4_th_87:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for PX be a-partitionEQREL-1M3-of X holds  for Pi be setHIDDENM2 holds Pi inTARSKIR2 PX implies ( ex x be ElementSUBSET-1M1-of X st x inTARSKIR2 Pi)"
sorry

mtheorem finseq_4_th_88:
" for X be  non emptyXBOOLE-0V1\<bar>finiteFINSET-1V1\<bar>setHIDDENM2 holds  for PX be a-partitionEQREL-1M3-of X holds cardCARD-1K4 PX <=XXREAL-0R1 cardCARD-1K4 X"
sorry

mtheorem finseq_4_th_89:
" for A be  non emptyXBOOLE-0V1\<bar>finiteFINSET-1V1\<bar>setHIDDENM2 holds  for PA1 be a-partitionEQREL-1M3-of A holds  for PA2 be a-partitionEQREL-1M3-of A holds PA1 is-finer-thanSETFAM-1R1 PA2 implies cardCARD-1K4 PA2 <=XXREAL-0R1 cardCARD-1K4 PA1"
sorry

mtheorem finseq_4_th_90:
" for A be  non emptyXBOOLE-0V1\<bar>finiteFINSET-1V1\<bar>setHIDDENM2 holds  for PA1 be a-partitionEQREL-1M3-of A holds  for PA2 be a-partitionEQREL-1M3-of A holds PA1 is-finer-thanSETFAM-1R1 PA2 implies ( for p2 be ElementSUBSET-1M3\<^bsub>(boolZFMISC-1K1 A)\<^esub>-of PA2 holds  ex p1 be ElementSUBSET-1M3\<^bsub>(boolZFMISC-1K1 A)\<^esub>-of PA1 st p1 c=TARSKIR1 p2)"
sorry

mtheorem finseq_4_th_91:
" for A be  non emptyXBOOLE-0V1\<bar>finiteFINSET-1V1\<bar>setHIDDENM2 holds  for PA1 be a-partitionEQREL-1M3-of A holds  for PA2 be a-partitionEQREL-1M3-of A holds PA1 is-finer-thanSETFAM-1R1 PA2 & cardCARD-1K4 PA1 =XBOOLE-0R4 cardCARD-1K4 PA2 implies PA1 =XBOOLE-0R4 PA2"
sorry

mtheorem finseq_4_cl_9:
  mlet "D be setHIDDENM2", "M be FinSequenceFINSEQ-1M3-of D * FINSEQ-1K14", "k be NatNAT-1M1"
"cluster M /.PARTFUN1K7\<^bsub>(D * FINSEQ-1K14)\<^esub> k as-term-is Function-likeFUNCT-1V1\<bar>Relation-likeRELAT-1V1"
proof
(*coherence*)
  show "M /.PARTFUN1K7\<^bsub>(D * FINSEQ-1K14)\<^esub> k be Function-likeFUNCT-1V1\<bar>Relation-likeRELAT-1V1"
     sorry
qed "sorry"

mtheorem finseq_4_cl_10:
  mlet "D be setHIDDENM2", "M be FinSequenceFINSEQ-1M3-of D * FINSEQ-1K14", "k be NatNAT-1M1"
"cluster M /.PARTFUN1K7\<^bsub>(D * FINSEQ-1K14)\<^esub> k as-term-is FinSequence-likeFINSEQ-1V1\<bar>D -valuedRELAT-1V5 for FunctionFUNCT-1M1"
proof
(*coherence*)
  show " for it be FunctionFUNCT-1M1 holds it =HIDDENR1 M /.PARTFUN1K7\<^bsub>(D * FINSEQ-1K14)\<^esub> k implies it be FinSequence-likeFINSEQ-1V1\<bar>D -valuedRELAT-1V5"
    using finseq_1_def_11 sorry
qed "sorry"

reserve f for "FinSequenceFINSEQ-1M3-of D"
mtheorem finseq_4_th_92:
" for m be NatNAT-1M1 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for f be FinSequenceFINSEQ-1M3-of D holds m inTARSKIR2 domFINSEQ-1K5 f implies f /.PARTFUN1K7\<^bsub>(D)\<^esub> \<one>\<^sub>M =XBOOLE-0R4 (f |FINSEQ-1K18\<^bsub>(D)\<^esub> m)/.PARTFUN1K7\<^bsub>(D)\<^esub> \<one>\<^sub>M"
sorry

mtheorem finseq_4_th_93:
" for m be NatNAT-1M1 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for f be FinSequenceFINSEQ-1M3-of D holds m inTARSKIR2 domFINSEQ-1K5 f implies f /.PARTFUN1K7\<^bsub>(D)\<^esub> m =XBOOLE-0R4 (f |FINSEQ-1K18\<^bsub>(D)\<^esub> m)/.PARTFUN1K7\<^bsub>(D)\<^esub> lenFINSEQ-1K4 (f |FINSEQ-1K18\<^bsub>(D)\<^esub> m)"
sorry

end
