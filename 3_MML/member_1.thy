theory member_1
  imports membered xxreal_3 binop_2
   "../mizar_extension/E_number"
begin
(*begin*)
reserve w, w1, w2 for "ElementSUBSET-1M1-of ExtREALXXREAL-0K3"
reserve c, c1, c2 for "ComplexXCMPLX-0M1"
reserve A, B, C, D for "complex-memberedMEMBEREDV1\<bar>setHIDDENM2"
reserve F, G, H, I for "ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2"
reserve a, b, s, t, z for "ComplexXCMPLX-0M1"
reserve f, g, h, i, j for "ExtRealXXREAL-0M1"
reserve r for "RealXREAL-0M1"
reserve e for "setHIDDENM2"
abbreviation(input) MEMBER_1K1("-MEMBER-1K1  _ " [132]132) where
  "-MEMBER-1K1 w \<equiv> -XXREAL-3K2 w"

mtheorem member_1_add_1:
  mlet "w be ElementSUBSET-1M1-of ExtREALXXREAL-0K3"
"cluster -XXREAL-3K2 w as-term-is ElementSUBSET-1M1-of ExtREALXXREAL-0K3"
proof
(*coherence*)
  show "-XXREAL-3K2 w be ElementSUBSET-1M1-of ExtREALXXREAL-0K3"
    using xxreal_0_def_1 sorry
qed "sorry"

abbreviation(input) MEMBER_1K2(" _ \<inverse>MEMBER-1K2" [228]228) where
  "w \<inverse>MEMBER-1K2 \<equiv> w \<inverse>XXREAL-3K5"

mtheorem member_1_add_2:
  mlet "w be ElementSUBSET-1M1-of ExtREALXXREAL-0K3"
"cluster w \<inverse>XXREAL-3K5 as-term-is ElementSUBSET-1M1-of ExtREALXXREAL-0K3"
proof
(*coherence*)
  show "w \<inverse>XXREAL-3K5 be ElementSUBSET-1M1-of ExtREALXXREAL-0K3"
    using xxreal_0_def_1 sorry
qed "sorry"

abbreviation(input) MEMBER_1K3(" _ *MEMBER-1K3  _ " [164,164]164) where
  "w *MEMBER-1K3 w1 \<equiv> w *XXREAL-3K4 w1"

mtheorem member_1_add_3:
  mlet "w be ElementSUBSET-1M1-of ExtREALXXREAL-0K3", "w1 be ElementSUBSET-1M1-of ExtREALXXREAL-0K3"
"cluster w *XXREAL-3K4 w1 as-term-is ElementSUBSET-1M1-of ExtREALXXREAL-0K3"
proof
(*coherence*)
  show "w *XXREAL-3K4 w1 be ElementSUBSET-1M1-of ExtREALXXREAL-0K3"
    using xxreal_0_def_1 sorry
qed "sorry"

mtheorem member_1_cl_1:
  mlet "a be ComplexXCMPLX-0M1", "b be ComplexXCMPLX-0M1", "c be ComplexXCMPLX-0M1", "d be ComplexXCMPLX-0M1"
"cluster {ENUMSET1K2 a,b,c,d } as-term-is complex-memberedMEMBEREDV1"
proof
(*coherence*)
  show "{ENUMSET1K2 a,b,c,d } be complex-memberedMEMBEREDV1"
    using enumset1_def_2 sorry
qed "sorry"

mtheorem member_1_cl_2:
  mlet "a be ExtRealXXREAL-0M1", "b be ExtRealXXREAL-0M1", "c be ExtRealXXREAL-0M1", "d be ExtRealXXREAL-0M1"
"cluster {ENUMSET1K2 a,b,c,d } as-term-is ext-real-memberedMEMBEREDV2"
proof
(*coherence*)
  show "{ENUMSET1K2 a,b,c,d } be ext-real-memberedMEMBEREDV2"
    using enumset1_def_2 sorry
qed "sorry"

mdef member_1_def_1 ("--MEMBER-1K4  _ " [132]132 ) where
  mlet "F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2"
"func --MEMBER-1K4 F \<rightarrow> ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 equals
  {-MEMBER-1K1 w where w be ElementSUBSET-1M1-of ExtREALXXREAL-0K3 : w inTARSKIR2 F }"
proof-
  (*coherence*)
    show "{-MEMBER-1K1 w where w be ElementSUBSET-1M1-of ExtREALXXREAL-0K3 : w inTARSKIR2 F } be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2"
sorry
qed "sorry"

mtheorem MEMBER_1K4_involutiveness:
" for F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds --MEMBER-1K4 (--MEMBER-1K4 F) =HIDDENR1 F"
sorry

mtheorem member_1_th_1:
" for F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for f be ExtRealXXREAL-0M1 holds f inHIDDENR3 F iff -XXREAL-3K2 f inHIDDENR3 --MEMBER-1K4 F"
sorry

mtheorem member_1_th_2:
" for F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for f be ExtRealXXREAL-0M1 holds -XXREAL-3K2 f inHIDDENR3 F iff f inHIDDENR3 --MEMBER-1K4 F"
sorry

mtheorem member_1_cl_3:
  mlet "F be emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster --MEMBER-1K4 F as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "--MEMBER-1K4 F be emptyXBOOLE-0V1"
sorry
qed "sorry"

mtheorem member_1_cl_4:
  mlet "F be ext-real-memberedMEMBEREDV2\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster --MEMBER-1K4 F as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "--MEMBER-1K4 F be  non emptyXBOOLE-0V1"
sorry
qed "sorry"

mlemma member_1_lm_1:
" for F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for G be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds F c=MEMBEREDR2 G implies --MEMBER-1K4 F c=MEMBEREDR2 --MEMBER-1K4 G"
sorry

mtheorem member_1_th_3:
" for F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for G be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds F c=MEMBEREDR2 G iff --MEMBER-1K4 F c=MEMBEREDR2 --MEMBER-1K4 G"
sorry

mtheorem member_1_th_4:
" for F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for G be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds --MEMBER-1K4 F =MEMBEREDR8 --MEMBER-1K4 G implies F =MEMBEREDR8 G"
sorry

mtheorem member_1_th_5:
" for F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for G be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds --MEMBER-1K4 (F \\/XBOOLE-0K2 G) =MEMBEREDR8 (--MEMBER-1K4 F)\\/XBOOLE-0K2 (--MEMBER-1K4 G)"
sorry

mtheorem member_1_th_6:
" for F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for G be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds --MEMBER-1K4 F /\\XBOOLE-0K3 G =MEMBEREDR8 (--MEMBER-1K4 F)/\\XBOOLE-0K3 (--MEMBER-1K4 G)"
sorry

mtheorem member_1_th_7:
" for F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for G be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds --MEMBER-1K4 (F \\SUBSET-1K6 G) =MEMBEREDR8 (--MEMBER-1K4 F)\\SUBSET-1K6 (--MEMBER-1K4 G)"
sorry

mtheorem member_1_th_8:
" for F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for G be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds --MEMBER-1K4 (F \\+\\XBOOLE-0K5 G) =MEMBEREDR8 --MEMBER-1K4 F \\+\\XBOOLE-0K5 --MEMBER-1K4 G"
sorry

mtheorem member_1_th_9:
" for f be ExtRealXXREAL-0M1 holds --MEMBER-1K4 {TARSKIK1 f} =MEMBEREDR8 {TARSKIK1 -XXREAL-3K2 f }"
sorry

mtheorem member_1_th_10:
" for f be ExtRealXXREAL-0M1 holds  for g be ExtRealXXREAL-0M1 holds --MEMBER-1K4 {TARSKIK2 f,g } =MEMBEREDR8 {TARSKIK2 -XXREAL-3K2 f,-XXREAL-3K2 g }"
sorry

mdef member_1_def_2 ("--MEMBER-1K5  _ " [132]132 ) where
  mlet "A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2"
"func --MEMBER-1K5 A \<rightarrow> complex-memberedMEMBEREDV1\<bar>setHIDDENM2 equals
  {-XCMPLX-0K4 c where c be ComplexXCMPLX-0M1 : c inHIDDENR3 A }"
proof-
  (*coherence*)
    show "{-XCMPLX-0K4 c where c be ComplexXCMPLX-0M1 : c inHIDDENR3 A } be complex-memberedMEMBEREDV1\<bar>setHIDDENM2"
sorry
qed "sorry"

mtheorem MEMBER_1K5_involutiveness:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds --MEMBER-1K5 (--MEMBER-1K5 A) =HIDDENR1 A"
sorry

mtheorem member_1_th_11:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for a be ComplexXCMPLX-0M1 holds a inHIDDENR3 A iff -XCMPLX-0K4 a inHIDDENR3 --MEMBER-1K5 A"
sorry

mtheorem member_1_th_12:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for a be ComplexXCMPLX-0M1 holds -XCMPLX-0K4 a inHIDDENR3 A iff a inHIDDENR3 --MEMBER-1K5 A"
sorry

mtheorem member_1_cl_5:
  mlet "A be emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster --MEMBER-1K5 A as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "--MEMBER-1K5 A be emptyXBOOLE-0V1"
sorry
qed "sorry"

mtheorem member_1_cl_6:
  mlet "A be complex-memberedMEMBEREDV1\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster --MEMBER-1K5 A as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "--MEMBER-1K5 A be  non emptyXBOOLE-0V1"
sorry
qed "sorry"

mtheorem member_1_cl_7:
  mlet "A be real-memberedMEMBEREDV3\<bar>setHIDDENM2"
"cluster --MEMBER-1K5 A as-term-is real-memberedMEMBEREDV3"
proof
(*coherence*)
  show "--MEMBER-1K5 A be real-memberedMEMBEREDV3"
sorry
qed "sorry"

mtheorem member_1_cl_8:
  mlet "A be rational-memberedMEMBEREDV4\<bar>setHIDDENM2"
"cluster --MEMBER-1K5 A as-term-is rational-memberedMEMBEREDV4"
proof
(*coherence*)
  show "--MEMBER-1K5 A be rational-memberedMEMBEREDV4"
sorry
qed "sorry"

mtheorem member_1_cl_9:
  mlet "A be integer-memberedMEMBEREDV5\<bar>setHIDDENM2"
"cluster --MEMBER-1K5 A as-term-is integer-memberedMEMBEREDV5"
proof
(*coherence*)
  show "--MEMBER-1K5 A be integer-memberedMEMBEREDV5"
sorry
qed "sorry"

mtheorem member_1_ident_1:
  mlet "A be real-memberedMEMBEREDV3\<bar>setHIDDENM2", "F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2"
"identify --MEMBER-1K5 A with --MEMBER-1K4 F when A =HIDDENR1 F"
proof
(*compatibility*)
  show "A =HIDDENR1 F implies --MEMBER-1K5 A =HIDDENR1 --MEMBER-1K4 F"
sorry
qed "sorry"

mlemma member_1_lm_2:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds A c=MEMBEREDR1 B implies --MEMBER-1K5 A c=MEMBEREDR1 --MEMBER-1K5 B"
sorry

mtheorem member_1_th_13:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds A c=MEMBEREDR1 B iff --MEMBER-1K5 A c=MEMBEREDR1 --MEMBER-1K5 B"
sorry

mtheorem member_1_th_14:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds --MEMBER-1K5 A =MEMBEREDR7 --MEMBER-1K5 B implies A =MEMBEREDR7 B"
sorry

mtheorem member_1_th_15:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds --MEMBER-1K5 (A \\/XBOOLE-0K2 B) =MEMBEREDR7 (--MEMBER-1K5 A)\\/XBOOLE-0K2 (--MEMBER-1K5 B)"
sorry

mtheorem member_1_th_16:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds --MEMBER-1K5 A /\\XBOOLE-0K3 B =MEMBEREDR7 (--MEMBER-1K5 A)/\\XBOOLE-0K3 (--MEMBER-1K5 B)"
sorry

mtheorem member_1_th_17:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds --MEMBER-1K5 (A \\SUBSET-1K6 B) =MEMBEREDR7 (--MEMBER-1K5 A)\\SUBSET-1K6 (--MEMBER-1K5 B)"
sorry

mtheorem member_1_th_18:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds --MEMBER-1K5 (A \\+\\XBOOLE-0K5 B) =MEMBEREDR7 --MEMBER-1K5 A \\+\\XBOOLE-0K5 --MEMBER-1K5 B"
sorry

mtheorem member_1_th_19:
" for a be ComplexXCMPLX-0M1 holds --MEMBER-1K5 {TARSKIK1 a} =MEMBEREDR7 {TARSKIK1 -XCMPLX-0K4 a }"
sorry

mtheorem member_1_th_20:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds --MEMBER-1K5 {TARSKIK2 a,b } =MEMBEREDR7 {TARSKIK2 -XCMPLX-0K4 a,-XCMPLX-0K4 b }"
sorry

mdef member_1_def_3 (" _ \<inverse>\<inverse>MEMBER-1K6" [164]164 ) where
  mlet "F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2"
"func F \<inverse>\<inverse>MEMBER-1K6 \<rightarrow> ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 equals
  {w \<inverse>MEMBER-1K2 where w be ElementSUBSET-1M1-of ExtREALXXREAL-0K3 : w inTARSKIR2 F }"
proof-
  (*coherence*)
    show "{w \<inverse>MEMBER-1K2 where w be ElementSUBSET-1M1-of ExtREALXXREAL-0K3 : w inTARSKIR2 F } be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2"
sorry
qed "sorry"

mtheorem member_1_th_21:
" for F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for f be ExtRealXXREAL-0M1 holds f inHIDDENR3 F implies f \<inverse>XXREAL-3K5 inHIDDENR3 F \<inverse>\<inverse>MEMBER-1K6"
sorry

mtheorem member_1_cl_10:
  mlet "F be emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster F \<inverse>\<inverse>MEMBER-1K6 as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "F \<inverse>\<inverse>MEMBER-1K6 be emptyXBOOLE-0V1"
sorry
qed "sorry"

mtheorem member_1_cl_11:
  mlet "F be ext-real-memberedMEMBEREDV2\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster F \<inverse>\<inverse>MEMBER-1K6 as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "F \<inverse>\<inverse>MEMBER-1K6 be  non emptyXBOOLE-0V1"
sorry
qed "sorry"

mtheorem member_1_th_22:
" for F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for G be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds F c=MEMBEREDR2 G implies F \<inverse>\<inverse>MEMBER-1K6 c=MEMBEREDR2 G \<inverse>\<inverse>MEMBER-1K6"
sorry

mtheorem member_1_th_23:
" for F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for G be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds (F \\/XBOOLE-0K2 G)\<inverse>\<inverse>MEMBER-1K6 =MEMBEREDR8 F \<inverse>\<inverse>MEMBER-1K6 \\/XBOOLE-0K2 G \<inverse>\<inverse>MEMBER-1K6"
sorry

mtheorem member_1_th_24:
" for F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for G be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds (F /\\XBOOLE-0K3 G)\<inverse>\<inverse>MEMBER-1K6 c=MEMBEREDR2 (F \<inverse>\<inverse>MEMBER-1K6)/\\XBOOLE-0K3 (G \<inverse>\<inverse>MEMBER-1K6)"
sorry

mtheorem member_1_th_25:
" for F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds --MEMBER-1K4 F \<inverse>\<inverse>MEMBER-1K6 =MEMBEREDR8 (--MEMBER-1K4 F)\<inverse>\<inverse>MEMBER-1K6"
sorry

mtheorem member_1_th_26:
" for f be ExtRealXXREAL-0M1 holds {TARSKIK1 f} \<inverse>\<inverse>MEMBER-1K6 =MEMBEREDR8 {TARSKIK1 f \<inverse>XXREAL-3K5 }"
sorry

mtheorem member_1_th_27:
" for f be ExtRealXXREAL-0M1 holds  for g be ExtRealXXREAL-0M1 holds {TARSKIK2 f,g } \<inverse>\<inverse>MEMBER-1K6 =MEMBEREDR8 {TARSKIK2 f \<inverse>XXREAL-3K5,g \<inverse>XXREAL-3K5 }"
sorry

mdef member_1_def_4 (" _ \<inverse>\<inverse>MEMBER-1K7" [164]164 ) where
  mlet "A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2"
"func A \<inverse>\<inverse>MEMBER-1K7 \<rightarrow> complex-memberedMEMBEREDV1\<bar>setHIDDENM2 equals
  {c \<inverse>XCMPLX-0K5 where c be ComplexXCMPLX-0M1 : c inHIDDENR3 A }"
proof-
  (*coherence*)
    show "{c \<inverse>XCMPLX-0K5 where c be ComplexXCMPLX-0M1 : c inHIDDENR3 A } be complex-memberedMEMBEREDV1\<bar>setHIDDENM2"
sorry
qed "sorry"

mtheorem MEMBER_1K7_involutiveness:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds (A \<inverse>\<inverse>MEMBER-1K7)\<inverse>\<inverse>MEMBER-1K7 =HIDDENR1 A"
sorry

mtheorem member_1_th_28:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for a be ComplexXCMPLX-0M1 holds a inHIDDENR3 A iff a \<inverse>XCMPLX-0K5 inHIDDENR3 A \<inverse>\<inverse>MEMBER-1K7"
sorry

mtheorem member_1_th_29:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for a be ComplexXCMPLX-0M1 holds a \<inverse>XCMPLX-0K5 inHIDDENR3 A iff a inHIDDENR3 A \<inverse>\<inverse>MEMBER-1K7"
sorry

mtheorem member_1_cl_12:
  mlet "A be emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster A \<inverse>\<inverse>MEMBER-1K7 as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "A \<inverse>\<inverse>MEMBER-1K7 be emptyXBOOLE-0V1"
sorry
qed "sorry"

mtheorem member_1_cl_13:
  mlet "A be complex-memberedMEMBEREDV1\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster A \<inverse>\<inverse>MEMBER-1K7 as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "A \<inverse>\<inverse>MEMBER-1K7 be  non emptyXBOOLE-0V1"
sorry
qed "sorry"

mtheorem member_1_cl_14:
  mlet "A be real-memberedMEMBEREDV3\<bar>setHIDDENM2"
"cluster A \<inverse>\<inverse>MEMBER-1K7 as-term-is real-memberedMEMBEREDV3"
proof
(*coherence*)
  show "A \<inverse>\<inverse>MEMBER-1K7 be real-memberedMEMBEREDV3"
sorry
qed "sorry"

mtheorem member_1_cl_15:
  mlet "A be rational-memberedMEMBEREDV4\<bar>setHIDDENM2"
"cluster A \<inverse>\<inverse>MEMBER-1K7 as-term-is rational-memberedMEMBEREDV4"
proof
(*coherence*)
  show "A \<inverse>\<inverse>MEMBER-1K7 be rational-memberedMEMBEREDV4"
sorry
qed "sorry"

mtheorem member_1_ident_2:
  mlet "A be real-memberedMEMBEREDV3\<bar>setHIDDENM2", "F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2"
"identify A \<inverse>\<inverse>MEMBER-1K7 with F \<inverse>\<inverse>MEMBER-1K6 when A =HIDDENR1 F"
proof
(*compatibility*)
  show "A =HIDDENR1 F implies A \<inverse>\<inverse>MEMBER-1K7 =HIDDENR1 F \<inverse>\<inverse>MEMBER-1K6"
sorry
qed "sorry"

mlemma member_1_lm_3:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds A c=MEMBEREDR1 B implies A \<inverse>\<inverse>MEMBER-1K7 c=MEMBEREDR1 B \<inverse>\<inverse>MEMBER-1K7"
sorry

mtheorem member_1_th_30:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds A c=MEMBEREDR1 B iff A \<inverse>\<inverse>MEMBER-1K7 c=MEMBEREDR1 B \<inverse>\<inverse>MEMBER-1K7"
sorry

mtheorem member_1_th_31:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds A \<inverse>\<inverse>MEMBER-1K7 =MEMBEREDR7 B \<inverse>\<inverse>MEMBER-1K7 implies A =MEMBEREDR7 B"
sorry

mtheorem member_1_th_32:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds (A \\/XBOOLE-0K2 B)\<inverse>\<inverse>MEMBER-1K7 =MEMBEREDR7 A \<inverse>\<inverse>MEMBER-1K7 \\/XBOOLE-0K2 B \<inverse>\<inverse>MEMBER-1K7"
sorry

mtheorem member_1_th_33:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds (A /\\XBOOLE-0K3 B)\<inverse>\<inverse>MEMBER-1K7 =MEMBEREDR7 (A \<inverse>\<inverse>MEMBER-1K7)/\\XBOOLE-0K3 (B \<inverse>\<inverse>MEMBER-1K7)"
sorry

mtheorem member_1_th_34:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds (A \\SUBSET-1K6 B)\<inverse>\<inverse>MEMBER-1K7 =MEMBEREDR7 A \<inverse>\<inverse>MEMBER-1K7 \\SUBSET-1K6 B \<inverse>\<inverse>MEMBER-1K7"
sorry

mtheorem member_1_th_35:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds (A \\+\\XBOOLE-0K5 B)\<inverse>\<inverse>MEMBER-1K7 =MEMBEREDR7 A \<inverse>\<inverse>MEMBER-1K7 \\+\\XBOOLE-0K5 B \<inverse>\<inverse>MEMBER-1K7"
sorry

mtheorem member_1_th_36:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds --MEMBER-1K5 A \<inverse>\<inverse>MEMBER-1K7 =MEMBEREDR7 (--MEMBER-1K5 A)\<inverse>\<inverse>MEMBER-1K7"
sorry

mtheorem member_1_th_37:
" for a be ComplexXCMPLX-0M1 holds {TARSKIK1 a} \<inverse>\<inverse>MEMBER-1K7 =MEMBEREDR7 {TARSKIK1 a \<inverse>XCMPLX-0K5 }"
sorry

mtheorem member_1_th_38:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds {TARSKIK2 a,b } \<inverse>\<inverse>MEMBER-1K7 =MEMBEREDR7 {TARSKIK2 a \<inverse>XCMPLX-0K5,b \<inverse>XCMPLX-0K5 }"
sorry

mdef member_1_def_5 (" _ ++MEMBER-1K8  _ " [132,132]132 ) where
  mlet "F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2", "G be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2"
"func F ++MEMBER-1K8 G \<rightarrow> setHIDDENM2 equals
  {w1 +XXREAL-3K1 w2 where w1 be ElementSUBSET-1M1-of ExtREALXXREAL-0K3, w2 be ElementSUBSET-1M1-of ExtREALXXREAL-0K3 : w1 inTARSKIR2 F & w2 inTARSKIR2 G }"
proof-
  (*coherence*)
    show "{w1 +XXREAL-3K1 w2 where w1 be ElementSUBSET-1M1-of ExtREALXXREAL-0K3, w2 be ElementSUBSET-1M1-of ExtREALXXREAL-0K3 : w1 inTARSKIR2 F & w2 inTARSKIR2 G } be setHIDDENM2"
       sorry
qed "sorry"

mtheorem MEMBER_1K8_commutativity:
" for F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for G be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds F ++MEMBER-1K8 G =HIDDENR1 G ++MEMBER-1K8 F"
sorry

mtheorem member_1_th_39:
" for F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for G be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for f be ExtRealXXREAL-0M1 holds  for g be ExtRealXXREAL-0M1 holds f inHIDDENR3 F & g inHIDDENR3 G implies f +XXREAL-3K1 g inHIDDENR3 F ++MEMBER-1K8 G"
sorry

mtheorem member_1_cl_16:
  mlet "F be emptyXBOOLE-0V1\<bar>setHIDDENM2", "G be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2"
"cluster F ++MEMBER-1K8 G as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "F ++MEMBER-1K8 G be emptyXBOOLE-0V1"
sorry
qed "sorry"

mtheorem member_1_cl_17:
  mlet "F be emptyXBOOLE-0V1\<bar>setHIDDENM2", "G be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2"
"cluster G ++MEMBER-1K8 F as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "G ++MEMBER-1K8 F be emptyXBOOLE-0V1"
     sorry
qed "sorry"

mtheorem member_1_cl_18:
  mlet "F be ext-real-memberedMEMBEREDV2\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2", "G be ext-real-memberedMEMBEREDV2\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster F ++MEMBER-1K8 G as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "F ++MEMBER-1K8 G be  non emptyXBOOLE-0V1"
sorry
qed "sorry"

mtheorem member_1_cl_19:
  mlet "F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2", "G be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2"
"cluster F ++MEMBER-1K8 G as-term-is ext-real-memberedMEMBEREDV2"
proof
(*coherence*)
  show "F ++MEMBER-1K8 G be ext-real-memberedMEMBEREDV2"
sorry
qed "sorry"

mtheorem member_1_th_40:
" for F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for G be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for H be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for I be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds F c=MEMBEREDR2 G & H c=MEMBEREDR2 I implies F ++MEMBER-1K8 H c=MEMBEREDR2 G ++MEMBER-1K8 I"
sorry

mtheorem member_1_th_41:
" for F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for G be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for H be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds F ++MEMBER-1K8 (G \\/XBOOLE-0K2 H) =MEMBEREDR8 (F ++MEMBER-1K8 G)\\/XBOOLE-0K2 (F ++MEMBER-1K8 H)"
sorry

mtheorem member_1_th_42:
" for F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for G be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for H be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds F ++MEMBER-1K8 G /\\XBOOLE-0K3 H c=MEMBEREDR2 (F ++MEMBER-1K8 G)/\\XBOOLE-0K3 (F ++MEMBER-1K8 H)"
sorry

mtheorem member_1_th_43:
" for f be ExtRealXXREAL-0M1 holds  for g be ExtRealXXREAL-0M1 holds {TARSKIK1 f} ++MEMBER-1K8 {TARSKIK1 g} =MEMBEREDR8 {TARSKIK1 f +XXREAL-3K1 g }"
sorry

mtheorem member_1_th_44:
" for f be ExtRealXXREAL-0M1 holds  for g be ExtRealXXREAL-0M1 holds  for h be ExtRealXXREAL-0M1 holds {TARSKIK1 f} ++MEMBER-1K8 {TARSKIK2 g,h } =MEMBEREDR8 {TARSKIK2 f +XXREAL-3K1 g,f +XXREAL-3K1 h }"
sorry

mtheorem member_1_th_45:
" for f be ExtRealXXREAL-0M1 holds  for g be ExtRealXXREAL-0M1 holds  for h be ExtRealXXREAL-0M1 holds  for i be ExtRealXXREAL-0M1 holds {TARSKIK2 f,g } ++MEMBER-1K8 {TARSKIK2 h,i } =MEMBEREDR8 {ENUMSET1K2 f +XXREAL-3K1 h,f +XXREAL-3K1 i,g +XXREAL-3K1 h,g +XXREAL-3K1 i }"
sorry

mdef member_1_def_6 (" _ ++MEMBER-1K9  _ " [132,132]132 ) where
  mlet "A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2", "B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2"
"func A ++MEMBER-1K9 B \<rightarrow> setHIDDENM2 equals
  {c1 +XCMPLX-0K2 c2 where c1 be ComplexXCMPLX-0M1, c2 be ComplexXCMPLX-0M1 : c1 inHIDDENR3 A & c2 inHIDDENR3 B }"
proof-
  (*coherence*)
    show "{c1 +XCMPLX-0K2 c2 where c1 be ComplexXCMPLX-0M1, c2 be ComplexXCMPLX-0M1 : c1 inHIDDENR3 A & c2 inHIDDENR3 B } be setHIDDENM2"
       sorry
qed "sorry"

mtheorem MEMBER_1K9_commutativity:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds A ++MEMBER-1K9 B =HIDDENR1 B ++MEMBER-1K9 A"
sorry

mtheorem member_1_th_46:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds a inHIDDENR3 A & b inHIDDENR3 B implies a +XCMPLX-0K2 b inTARSKIR2 A ++MEMBER-1K9 B"
   sorry

mtheorem member_1_cl_20:
  mlet "A be emptyXBOOLE-0V1\<bar>setHIDDENM2", "B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2"
"cluster A ++MEMBER-1K9 B as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "A ++MEMBER-1K9 B be emptyXBOOLE-0V1"
sorry
qed "sorry"

mtheorem member_1_cl_21:
  mlet "A be emptyXBOOLE-0V1\<bar>setHIDDENM2", "B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2"
"cluster B ++MEMBER-1K9 A as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "B ++MEMBER-1K9 A be emptyXBOOLE-0V1"
     sorry
qed "sorry"

mtheorem member_1_cl_22:
  mlet "A be complex-memberedMEMBEREDV1\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2", "B be complex-memberedMEMBEREDV1\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster A ++MEMBER-1K9 B as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "A ++MEMBER-1K9 B be  non emptyXBOOLE-0V1"
sorry
qed "sorry"

mtheorem member_1_cl_23:
  mlet "A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2", "B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2"
"cluster A ++MEMBER-1K9 B as-term-is complex-memberedMEMBEREDV1"
proof
(*coherence*)
  show "A ++MEMBER-1K9 B be complex-memberedMEMBEREDV1"
sorry
qed "sorry"

mtheorem member_1_cl_24:
  mlet "A be real-memberedMEMBEREDV3\<bar>setHIDDENM2", "B be real-memberedMEMBEREDV3\<bar>setHIDDENM2"
"cluster A ++MEMBER-1K9 B as-term-is real-memberedMEMBEREDV3"
proof
(*coherence*)
  show "A ++MEMBER-1K9 B be real-memberedMEMBEREDV3"
sorry
qed "sorry"

mtheorem member_1_cl_25:
  mlet "A be rational-memberedMEMBEREDV4\<bar>setHIDDENM2", "B be rational-memberedMEMBEREDV4\<bar>setHIDDENM2"
"cluster A ++MEMBER-1K9 B as-term-is rational-memberedMEMBEREDV4"
proof
(*coherence*)
  show "A ++MEMBER-1K9 B be rational-memberedMEMBEREDV4"
sorry
qed "sorry"

mtheorem member_1_cl_26:
  mlet "A be integer-memberedMEMBEREDV5\<bar>setHIDDENM2", "B be integer-memberedMEMBEREDV5\<bar>setHIDDENM2"
"cluster A ++MEMBER-1K9 B as-term-is integer-memberedMEMBEREDV5"
proof
(*coherence*)
  show "A ++MEMBER-1K9 B be integer-memberedMEMBEREDV5"
sorry
qed "sorry"

mtheorem member_1_cl_27:
  mlet "A be natural-memberedMEMBEREDV6\<bar>setHIDDENM2", "B be natural-memberedMEMBEREDV6\<bar>setHIDDENM2"
"cluster A ++MEMBER-1K9 B as-term-is natural-memberedMEMBEREDV6"
proof
(*coherence*)
  show "A ++MEMBER-1K9 B be natural-memberedMEMBEREDV6"
sorry
qed "sorry"

mtheorem member_1_ident_3:
  mlet "A be real-memberedMEMBEREDV3\<bar>setHIDDENM2", "B be real-memberedMEMBEREDV3\<bar>setHIDDENM2", "F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2", "G be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2"
"identify A ++MEMBER-1K9 B with F ++MEMBER-1K8 G when A =HIDDENR1 F & B =HIDDENR1 G"
proof
(*compatibility*)
  show "A =HIDDENR1 F & B =HIDDENR1 G implies A ++MEMBER-1K9 B =HIDDENR1 F ++MEMBER-1K8 G"
sorry
qed "sorry"

mtheorem member_1_th_47:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for C be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for D be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds A c=MEMBEREDR1 B & C c=MEMBEREDR1 D implies A ++MEMBER-1K9 C c=MEMBEREDR1 B ++MEMBER-1K9 D"
sorry

mtheorem member_1_th_48:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for C be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds A ++MEMBER-1K9 (B \\/XBOOLE-0K2 C) =MEMBEREDR7 (A ++MEMBER-1K9 B)\\/XBOOLE-0K2 (A ++MEMBER-1K9 C)"
sorry

mtheorem member_1_th_49:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for C be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds A ++MEMBER-1K9 B /\\XBOOLE-0K3 C c=MEMBEREDR1 (A ++MEMBER-1K9 B)/\\XBOOLE-0K3 (A ++MEMBER-1K9 C)"
sorry

mtheorem member_1_th_50:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for C be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds (A ++MEMBER-1K9 B)++MEMBER-1K9 C =MEMBEREDR7 A ++MEMBER-1K9 (B ++MEMBER-1K9 C)"
sorry

mtheorem member_1_th_51:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds {TARSKIK1 a} ++MEMBER-1K9 {TARSKIK1 b} =MEMBEREDR7 {TARSKIK1 a +XCMPLX-0K2 b }"
sorry

mtheorem member_1_th_52:
" for a be ComplexXCMPLX-0M1 holds  for s be ComplexXCMPLX-0M1 holds  for t be ComplexXCMPLX-0M1 holds {TARSKIK1 a} ++MEMBER-1K9 {TARSKIK2 s,t } =MEMBEREDR7 {TARSKIK2 a +XCMPLX-0K2 s,a +XCMPLX-0K2 t }"
sorry

mtheorem member_1_th_53:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for s be ComplexXCMPLX-0M1 holds  for t be ComplexXCMPLX-0M1 holds {TARSKIK2 a,b } ++MEMBER-1K9 {TARSKIK2 s,t } =MEMBEREDR7 {ENUMSET1K2 a +XCMPLX-0K2 s,a +XCMPLX-0K2 t,b +XCMPLX-0K2 s,b +XCMPLX-0K2 t }"
sorry

mdef member_1_def_7 (" _ --MEMBER-1K10  _ " [132,132]132 ) where
  mlet "F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2", "G be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2"
"func F --MEMBER-1K10 G \<rightarrow> setHIDDENM2 equals
  F ++MEMBER-1K8 (--MEMBER-1K4 G)"
proof-
  (*coherence*)
    show "F ++MEMBER-1K8 (--MEMBER-1K4 G) be setHIDDENM2"
       sorry
qed "sorry"

mtheorem member_1_th_54:
" for F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for G be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds F --MEMBER-1K10 G =XBOOLE-0R4 {w1 -XXREAL-3K3 w2 where w1 be ElementSUBSET-1M1-of ExtREALXXREAL-0K3, w2 be ElementSUBSET-1M1-of ExtREALXXREAL-0K3 : w1 inTARSKIR2 F & w2 inTARSKIR2 G }"
sorry

mtheorem member_1_th_55:
" for F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for G be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for f be ExtRealXXREAL-0M1 holds  for g be ExtRealXXREAL-0M1 holds f inHIDDENR3 F & g inHIDDENR3 G implies f -XXREAL-3K3 g inHIDDENR3 F --MEMBER-1K10 G"
sorry

mtheorem member_1_cl_28:
  mlet "F be emptyXBOOLE-0V1\<bar>setHIDDENM2", "G be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2"
"cluster F --MEMBER-1K10 G as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "F --MEMBER-1K10 G be emptyXBOOLE-0V1"
     sorry
qed "sorry"

mtheorem member_1_cl_29:
  mlet "F be emptyXBOOLE-0V1\<bar>setHIDDENM2", "G be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2"
"cluster G --MEMBER-1K10 F as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "G --MEMBER-1K10 F be emptyXBOOLE-0V1"
     sorry
qed "sorry"

mtheorem member_1_cl_30:
  mlet "F be ext-real-memberedMEMBEREDV2\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2", "G be ext-real-memberedMEMBEREDV2\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster F --MEMBER-1K10 G as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "F --MEMBER-1K10 G be  non emptyXBOOLE-0V1"
     sorry
qed "sorry"

mtheorem member_1_cl_31:
  mlet "F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2", "G be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2"
"cluster F --MEMBER-1K10 G as-term-is ext-real-memberedMEMBEREDV2"
proof
(*coherence*)
  show "F --MEMBER-1K10 G be ext-real-memberedMEMBEREDV2"
     sorry
qed "sorry"

mtheorem member_1_th_56:
" for F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for G be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for H be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for I be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds F c=MEMBEREDR2 G & H c=MEMBEREDR2 I implies F --MEMBER-1K10 H c=MEMBEREDR2 G --MEMBER-1K10 I"
sorry

mtheorem member_1_th_57:
" for F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for G be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for H be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds F --MEMBER-1K10 (G \\/XBOOLE-0K2 H) =MEMBEREDR8 (F --MEMBER-1K10 G)\\/XBOOLE-0K2 (F --MEMBER-1K10 H)"
sorry

mtheorem member_1_th_58:
" for F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for G be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for H be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds F --MEMBER-1K10 G /\\XBOOLE-0K3 H c=MEMBEREDR2 (F --MEMBER-1K10 G)/\\XBOOLE-0K3 (F --MEMBER-1K10 H)"
sorry

mlemma member_1_lm_4:
" for F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for G be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds --MEMBER-1K4 (F ++MEMBER-1K8 G) =MEMBEREDR8 (--MEMBER-1K4 F)++MEMBER-1K8 (--MEMBER-1K4 G)"
sorry

mtheorem member_1_th_59:
" for F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for G be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds --MEMBER-1K4 (F ++MEMBER-1K8 G) =MEMBEREDR8 (--MEMBER-1K4 F)--MEMBER-1K10 G"
  using member_1_lm_4 sorry

mtheorem member_1_th_60:
" for F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for G be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds --MEMBER-1K4 (F --MEMBER-1K10 G) =MEMBEREDR8 (--MEMBER-1K4 F)++MEMBER-1K8 G"
sorry

mtheorem member_1_th_61:
" for f be ExtRealXXREAL-0M1 holds  for g be ExtRealXXREAL-0M1 holds {TARSKIK1 f} --MEMBER-1K10 {TARSKIK1 g} =MEMBEREDR8 {TARSKIK1 f -XXREAL-3K3 g }"
sorry

mtheorem member_1_th_62:
" for f be ExtRealXXREAL-0M1 holds  for h be ExtRealXXREAL-0M1 holds  for i be ExtRealXXREAL-0M1 holds {TARSKIK1 f} --MEMBER-1K10 {TARSKIK2 h,i } =MEMBEREDR8 {TARSKIK2 f -XXREAL-3K3 h,f -XXREAL-3K3 i }"
sorry

mtheorem member_1_th_63:
" for f be ExtRealXXREAL-0M1 holds  for g be ExtRealXXREAL-0M1 holds  for h be ExtRealXXREAL-0M1 holds {TARSKIK2 f,g } --MEMBER-1K10 {TARSKIK1 h} =MEMBEREDR8 {TARSKIK2 f -XXREAL-3K3 h,g -XXREAL-3K3 h }"
sorry

mtheorem member_1_th_64:
" for f be ExtRealXXREAL-0M1 holds  for g be ExtRealXXREAL-0M1 holds  for h be ExtRealXXREAL-0M1 holds  for i be ExtRealXXREAL-0M1 holds {TARSKIK2 f,g } --MEMBER-1K10 {TARSKIK2 h,i } =MEMBEREDR8 {ENUMSET1K2 f -XXREAL-3K3 h,f -XXREAL-3K3 i,g -XXREAL-3K3 h,g -XXREAL-3K3 i }"
sorry

mdef member_1_def_8 (" _ --MEMBER-1K11  _ " [132,132]132 ) where
  mlet "A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2", "B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2"
"func A --MEMBER-1K11 B \<rightarrow> setHIDDENM2 equals
  A ++MEMBER-1K9 (--MEMBER-1K5 B)"
proof-
  (*coherence*)
    show "A ++MEMBER-1K9 (--MEMBER-1K5 B) be setHIDDENM2"
       sorry
qed "sorry"

mtheorem member_1_th_65:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds A --MEMBER-1K11 B =XBOOLE-0R4 {c1 -XCMPLX-0K6 c2 where c1 be ComplexXCMPLX-0M1, c2 be ComplexXCMPLX-0M1 : c1 inHIDDENR3 A & c2 inHIDDENR3 B }"
sorry

mtheorem member_1_th_66:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds a inHIDDENR3 A & b inHIDDENR3 B implies a -XCMPLX-0K6 b inTARSKIR2 A --MEMBER-1K11 B"
sorry

mtheorem member_1_cl_32:
  mlet "A be emptyXBOOLE-0V1\<bar>setHIDDENM2", "B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2"
"cluster A --MEMBER-1K11 B as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "A --MEMBER-1K11 B be emptyXBOOLE-0V1"
     sorry
qed "sorry"

mtheorem member_1_cl_33:
  mlet "A be emptyXBOOLE-0V1\<bar>setHIDDENM2", "B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2"
"cluster B --MEMBER-1K11 A as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "B --MEMBER-1K11 A be emptyXBOOLE-0V1"
     sorry
qed "sorry"

mtheorem member_1_cl_34:
  mlet "A be complex-memberedMEMBEREDV1\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2", "B be complex-memberedMEMBEREDV1\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster A --MEMBER-1K11 B as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "A --MEMBER-1K11 B be  non emptyXBOOLE-0V1"
     sorry
qed "sorry"

mtheorem member_1_cl_35:
  mlet "A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2", "B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2"
"cluster A --MEMBER-1K11 B as-term-is complex-memberedMEMBEREDV1"
proof
(*coherence*)
  show "A --MEMBER-1K11 B be complex-memberedMEMBEREDV1"
     sorry
qed "sorry"

mtheorem member_1_cl_36:
  mlet "A be real-memberedMEMBEREDV3\<bar>setHIDDENM2", "B be real-memberedMEMBEREDV3\<bar>setHIDDENM2"
"cluster A --MEMBER-1K11 B as-term-is real-memberedMEMBEREDV3"
proof
(*coherence*)
  show "A --MEMBER-1K11 B be real-memberedMEMBEREDV3"
     sorry
qed "sorry"

mtheorem member_1_cl_37:
  mlet "A be rational-memberedMEMBEREDV4\<bar>setHIDDENM2", "B be rational-memberedMEMBEREDV4\<bar>setHIDDENM2"
"cluster A --MEMBER-1K11 B as-term-is rational-memberedMEMBEREDV4"
proof
(*coherence*)
  show "A --MEMBER-1K11 B be rational-memberedMEMBEREDV4"
     sorry
qed "sorry"

mtheorem member_1_cl_38:
  mlet "A be integer-memberedMEMBEREDV5\<bar>setHIDDENM2", "B be integer-memberedMEMBEREDV5\<bar>setHIDDENM2"
"cluster A --MEMBER-1K11 B as-term-is integer-memberedMEMBEREDV5"
proof
(*coherence*)
  show "A --MEMBER-1K11 B be integer-memberedMEMBEREDV5"
     sorry
qed "sorry"

mtheorem member_1_ident_4:
  mlet "A be real-memberedMEMBEREDV3\<bar>setHIDDENM2", "B be real-memberedMEMBEREDV3\<bar>setHIDDENM2", "F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2", "G be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2"
"identify A --MEMBER-1K11 B with F --MEMBER-1K10 G when A =HIDDENR1 F & B =HIDDENR1 G"
proof
(*compatibility*)
  show "A =HIDDENR1 F & B =HIDDENR1 G implies A --MEMBER-1K11 B =HIDDENR1 F --MEMBER-1K10 G"
     sorry
qed "sorry"

mtheorem member_1_th_67:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for C be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for D be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds A c=MEMBEREDR1 B & C c=MEMBEREDR1 D implies A --MEMBER-1K11 C c=MEMBEREDR1 B --MEMBER-1K11 D"
sorry

mlemma member_1_lm_5:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds --MEMBER-1K5 (A ++MEMBER-1K9 B) =MEMBEREDR7 (--MEMBER-1K5 A)++MEMBER-1K9 (--MEMBER-1K5 B)"
sorry

mtheorem member_1_th_68:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for C be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds A --MEMBER-1K11 (B \\/XBOOLE-0K2 C) =MEMBEREDR7 (A --MEMBER-1K11 B)\\/XBOOLE-0K2 (A --MEMBER-1K11 C)"
sorry

mtheorem member_1_th_69:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for C be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds A --MEMBER-1K11 B /\\XBOOLE-0K3 C c=MEMBEREDR1 (A --MEMBER-1K11 B)/\\XBOOLE-0K3 (A --MEMBER-1K11 C)"
sorry

mtheorem member_1_th_70:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds --MEMBER-1K5 (A ++MEMBER-1K9 B) =MEMBEREDR7 (--MEMBER-1K5 A)--MEMBER-1K11 B"
  using member_1_lm_5 sorry

mtheorem member_1_th_71:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds --MEMBER-1K5 (A --MEMBER-1K11 B) =MEMBEREDR7 (--MEMBER-1K5 A)++MEMBER-1K9 B"
sorry

mtheorem member_1_th_72:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for C be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds A ++MEMBER-1K9 (B --MEMBER-1K11 C) =MEMBEREDR7 (A ++MEMBER-1K9 B)--MEMBER-1K11 C"
  using member_1_th_50 sorry

mtheorem member_1_th_73:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for C be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds A --MEMBER-1K11 (B ++MEMBER-1K9 C) =MEMBEREDR7 (A --MEMBER-1K11 B)--MEMBER-1K11 C"
sorry

mtheorem member_1_th_74:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for C be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds A --MEMBER-1K11 (B --MEMBER-1K11 C) =MEMBEREDR7 (A --MEMBER-1K11 B)++MEMBER-1K9 C"
sorry

mtheorem member_1_th_75:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds {TARSKIK1 a} --MEMBER-1K11 {TARSKIK1 b} =MEMBEREDR7 {TARSKIK1 a -XCMPLX-0K6 b }"
sorry

mtheorem member_1_th_76:
" for a be ComplexXCMPLX-0M1 holds  for s be ComplexXCMPLX-0M1 holds  for t be ComplexXCMPLX-0M1 holds {TARSKIK1 a} --MEMBER-1K11 {TARSKIK2 s,t } =MEMBEREDR7 {TARSKIK2 a -XCMPLX-0K6 s,a -XCMPLX-0K6 t }"
sorry

mtheorem member_1_th_77:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for s be ComplexXCMPLX-0M1 holds {TARSKIK2 a,b } --MEMBER-1K11 {TARSKIK1 s} =MEMBEREDR7 {TARSKIK2 a -XCMPLX-0K6 s,b -XCMPLX-0K6 s }"
sorry

mtheorem member_1_th_78:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for s be ComplexXCMPLX-0M1 holds  for t be ComplexXCMPLX-0M1 holds {TARSKIK2 a,b } --MEMBER-1K11 {TARSKIK2 s,t } =MEMBEREDR7 {ENUMSET1K2 a -XCMPLX-0K6 s,a -XCMPLX-0K6 t,b -XCMPLX-0K6 s,b -XCMPLX-0K6 t }"
sorry

mdef member_1_def_9 (" _ **MEMBER-1K12  _ " [164,164]164 ) where
  mlet "F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2", "G be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2"
"func F **MEMBER-1K12 G \<rightarrow> setHIDDENM2 equals
  {w1 *MEMBER-1K3 w2 where w1 be ElementSUBSET-1M1-of ExtREALXXREAL-0K3, w2 be ElementSUBSET-1M1-of ExtREALXXREAL-0K3 : w1 inTARSKIR2 F & w2 inTARSKIR2 G }"
proof-
  (*coherence*)
    show "{w1 *MEMBER-1K3 w2 where w1 be ElementSUBSET-1M1-of ExtREALXXREAL-0K3, w2 be ElementSUBSET-1M1-of ExtREALXXREAL-0K3 : w1 inTARSKIR2 F & w2 inTARSKIR2 G } be setHIDDENM2"
       sorry
qed "sorry"

mtheorem MEMBER_1K12_commutativity:
" for F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for G be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds F **MEMBER-1K12 G =HIDDENR1 G **MEMBER-1K12 F"
sorry

mtheorem member_1_cl_39:
  mlet "F be emptyXBOOLE-0V1\<bar>setHIDDENM2", "G be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2"
"cluster F **MEMBER-1K12 G as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "F **MEMBER-1K12 G be emptyXBOOLE-0V1"
sorry
qed "sorry"

mtheorem member_1_cl_40:
  mlet "F be emptyXBOOLE-0V1\<bar>setHIDDENM2", "G be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2"
"cluster G **MEMBER-1K12 F as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "G **MEMBER-1K12 F be emptyXBOOLE-0V1"
     sorry
qed "sorry"

mtheorem member_1_cl_41:
  mlet "F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2", "G be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2"
"cluster F **MEMBER-1K12 G as-term-is ext-real-memberedMEMBEREDV2"
proof
(*coherence*)
  show "F **MEMBER-1K12 G be ext-real-memberedMEMBEREDV2"
sorry
qed "sorry"

mtheorem member_1_th_79:
" for F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for G be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for f be ExtRealXXREAL-0M1 holds  for g be ExtRealXXREAL-0M1 holds f inHIDDENR3 F & g inHIDDENR3 G implies f *XXREAL-3K4 g inHIDDENR3 F **MEMBER-1K12 G"
sorry

mtheorem member_1_cl_42:
  mlet "F be ext-real-memberedMEMBEREDV2\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2", "G be ext-real-memberedMEMBEREDV2\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster F **MEMBER-1K12 G as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "F **MEMBER-1K12 G be  non emptyXBOOLE-0V1"
sorry
qed "sorry"

mtheorem member_1_th_80:
" for F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for G be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for H be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds (F **MEMBER-1K12 G)**MEMBER-1K12 H =MEMBEREDR8 F **MEMBER-1K12 (G **MEMBER-1K12 H)"
sorry

mtheorem member_1_th_81:
" for F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for G be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for H be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for I be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds F c=MEMBEREDR2 G & H c=MEMBEREDR2 I implies F **MEMBER-1K12 H c=MEMBEREDR2 G **MEMBER-1K12 I"
sorry

mtheorem member_1_th_82:
" for F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for G be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for H be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds F **MEMBER-1K12 (G \\/XBOOLE-0K2 H) =MEMBEREDR8 F **MEMBER-1K12 G \\/XBOOLE-0K2 F **MEMBER-1K12 H"
sorry

mtheorem member_1_th_83:
" for F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for G be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for H be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds F **MEMBER-1K12 (G /\\XBOOLE-0K3 H) c=MEMBEREDR2 (F **MEMBER-1K12 G)/\\XBOOLE-0K3 (F **MEMBER-1K12 H)"
sorry

mtheorem member_1_th_84:
" for F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for G be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds F **MEMBER-1K12 (--MEMBER-1K4 G) =MEMBEREDR8 --MEMBER-1K4 F **MEMBER-1K12 G"
sorry

mtheorem member_1_th_85:
" for F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for G be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds (F **MEMBER-1K12 G)\<inverse>\<inverse>MEMBER-1K6 =MEMBEREDR8 (F \<inverse>\<inverse>MEMBER-1K6)**MEMBER-1K12 (G \<inverse>\<inverse>MEMBER-1K6)"
sorry

mtheorem member_1_th_86:
" for f be ExtRealXXREAL-0M1 holds  for g be ExtRealXXREAL-0M1 holds {TARSKIK1 f} **MEMBER-1K12 {TARSKIK1 g} =MEMBEREDR8 {TARSKIK1 f *XXREAL-3K4 g }"
sorry

mtheorem member_1_th_87:
" for f be ExtRealXXREAL-0M1 holds  for h be ExtRealXXREAL-0M1 holds  for i be ExtRealXXREAL-0M1 holds {TARSKIK1 f} **MEMBER-1K12 {TARSKIK2 h,i } =MEMBEREDR8 {TARSKIK2 f *XXREAL-3K4 h,f *XXREAL-3K4 i }"
sorry

mtheorem member_1_th_88:
" for f be ExtRealXXREAL-0M1 holds  for g be ExtRealXXREAL-0M1 holds  for h be ExtRealXXREAL-0M1 holds  for i be ExtRealXXREAL-0M1 holds {TARSKIK2 f,g } **MEMBER-1K12 {TARSKIK2 h,i } =MEMBEREDR8 {ENUMSET1K2 f *XXREAL-3K4 h,f *XXREAL-3K4 i,g *XXREAL-3K4 h,g *XXREAL-3K4 i }"
sorry

mdef member_1_def_10 (" _ **MEMBER-1K13  _ " [164,164]164 ) where
  mlet "A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2", "B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2"
"func A **MEMBER-1K13 B \<rightarrow> setHIDDENM2 equals
  {c1 *XCMPLX-0K3 c2 where c1 be ComplexXCMPLX-0M1, c2 be ComplexXCMPLX-0M1 : c1 inHIDDENR3 A & c2 inHIDDENR3 B }"
proof-
  (*coherence*)
    show "{c1 *XCMPLX-0K3 c2 where c1 be ComplexXCMPLX-0M1, c2 be ComplexXCMPLX-0M1 : c1 inHIDDENR3 A & c2 inHIDDENR3 B } be setHIDDENM2"
       sorry
qed "sorry"

mtheorem MEMBER_1K13_commutativity:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds A **MEMBER-1K13 B =HIDDENR1 B **MEMBER-1K13 A"
sorry

mtheorem member_1_th_89:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds a inHIDDENR3 A & b inHIDDENR3 B implies a *XCMPLX-0K3 b inTARSKIR2 A **MEMBER-1K13 B"
   sorry

mtheorem member_1_cl_43:
  mlet "A be emptyXBOOLE-0V1\<bar>setHIDDENM2", "B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2"
"cluster A **MEMBER-1K13 B as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "A **MEMBER-1K13 B be emptyXBOOLE-0V1"
sorry
qed "sorry"

mtheorem member_1_cl_44:
  mlet "A be emptyXBOOLE-0V1\<bar>setHIDDENM2", "B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2"
"cluster B **MEMBER-1K13 A as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "B **MEMBER-1K13 A be emptyXBOOLE-0V1"
     sorry
qed "sorry"

mtheorem member_1_cl_45:
  mlet "A be complex-memberedMEMBEREDV1\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2", "B be complex-memberedMEMBEREDV1\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster A **MEMBER-1K13 B as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "A **MEMBER-1K13 B be  non emptyXBOOLE-0V1"
sorry
qed "sorry"

mtheorem member_1_cl_46:
  mlet "A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2", "B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2"
"cluster A **MEMBER-1K13 B as-term-is complex-memberedMEMBEREDV1"
proof
(*coherence*)
  show "A **MEMBER-1K13 B be complex-memberedMEMBEREDV1"
sorry
qed "sorry"

mtheorem member_1_cl_47:
  mlet "A be real-memberedMEMBEREDV3\<bar>setHIDDENM2", "B be real-memberedMEMBEREDV3\<bar>setHIDDENM2"
"cluster A **MEMBER-1K13 B as-term-is real-memberedMEMBEREDV3"
proof
(*coherence*)
  show "A **MEMBER-1K13 B be real-memberedMEMBEREDV3"
sorry
qed "sorry"

mtheorem member_1_cl_48:
  mlet "A be rational-memberedMEMBEREDV4\<bar>setHIDDENM2", "B be rational-memberedMEMBEREDV4\<bar>setHIDDENM2"
"cluster A **MEMBER-1K13 B as-term-is rational-memberedMEMBEREDV4"
proof
(*coherence*)
  show "A **MEMBER-1K13 B be rational-memberedMEMBEREDV4"
sorry
qed "sorry"

mtheorem member_1_cl_49:
  mlet "A be integer-memberedMEMBEREDV5\<bar>setHIDDENM2", "B be integer-memberedMEMBEREDV5\<bar>setHIDDENM2"
"cluster A **MEMBER-1K13 B as-term-is integer-memberedMEMBEREDV5"
proof
(*coherence*)
  show "A **MEMBER-1K13 B be integer-memberedMEMBEREDV5"
sorry
qed "sorry"

mtheorem member_1_cl_50:
  mlet "A be natural-memberedMEMBEREDV6\<bar>setHIDDENM2", "B be natural-memberedMEMBEREDV6\<bar>setHIDDENM2"
"cluster A **MEMBER-1K13 B as-term-is natural-memberedMEMBEREDV6"
proof
(*coherence*)
  show "A **MEMBER-1K13 B be natural-memberedMEMBEREDV6"
sorry
qed "sorry"

mtheorem member_1_ident_5:
  mlet "A be real-memberedMEMBEREDV3\<bar>setHIDDENM2", "B be real-memberedMEMBEREDV3\<bar>setHIDDENM2", "F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2", "G be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2"
"identify A **MEMBER-1K13 B with F **MEMBER-1K12 G when A =HIDDENR1 F & B =HIDDENR1 G"
proof
(*compatibility*)
  show "A =HIDDENR1 F & B =HIDDENR1 G implies A **MEMBER-1K13 B =HIDDENR1 F **MEMBER-1K12 G"
sorry
qed "sorry"

mtheorem member_1_th_90:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for C be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds (A **MEMBER-1K13 B)**MEMBER-1K13 C =MEMBEREDR7 A **MEMBER-1K13 (B **MEMBER-1K13 C)"
sorry

mtheorem member_1_th_91:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for C be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for D be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds A c=MEMBEREDR1 B & C c=MEMBEREDR1 D implies A **MEMBER-1K13 C c=MEMBEREDR1 B **MEMBER-1K13 D"
sorry

mtheorem member_1_th_92:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for C be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds A **MEMBER-1K13 (B \\/XBOOLE-0K2 C) =MEMBEREDR7 A **MEMBER-1K13 B \\/XBOOLE-0K2 A **MEMBER-1K13 C"
sorry

mtheorem member_1_th_93:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for C be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds A **MEMBER-1K13 (B /\\XBOOLE-0K3 C) c=MEMBEREDR1 (A **MEMBER-1K13 B)/\\XBOOLE-0K3 (A **MEMBER-1K13 C)"
sorry

mtheorem member_1_th_94:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds A **MEMBER-1K13 (--MEMBER-1K5 B) =MEMBEREDR7 --MEMBER-1K5 A **MEMBER-1K13 B"
sorry

mtheorem member_1_th_95:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for C be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds A **MEMBER-1K13 (B ++MEMBER-1K9 C) c=MEMBEREDR1 A **MEMBER-1K13 B ++MEMBER-1K9 A **MEMBER-1K13 C"
sorry

mtheorem member_1_th_96:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for C be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds A **MEMBER-1K13 (B --MEMBER-1K11 C) c=MEMBEREDR1 A **MEMBER-1K13 B --MEMBER-1K11 A **MEMBER-1K13 C"
sorry

mtheorem member_1_th_97:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds (A **MEMBER-1K13 B)\<inverse>\<inverse>MEMBER-1K7 =MEMBEREDR7 (A \<inverse>\<inverse>MEMBER-1K7)**MEMBER-1K13 (B \<inverse>\<inverse>MEMBER-1K7)"
sorry

mtheorem member_1_th_98:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds {TARSKIK1 a} **MEMBER-1K13 {TARSKIK1 b} =MEMBEREDR7 {TARSKIK1 a *XCMPLX-0K3 b }"
sorry

mtheorem member_1_th_99:
" for a be ComplexXCMPLX-0M1 holds  for s be ComplexXCMPLX-0M1 holds  for t be ComplexXCMPLX-0M1 holds {TARSKIK1 a} **MEMBER-1K13 {TARSKIK2 s,t } =MEMBEREDR7 {TARSKIK2 a *XCMPLX-0K3 s,a *XCMPLX-0K3 t }"
sorry

mtheorem member_1_th_100:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for s be ComplexXCMPLX-0M1 holds  for t be ComplexXCMPLX-0M1 holds {TARSKIK2 a,b } **MEMBER-1K13 {TARSKIK2 s,t } =MEMBEREDR7 {ENUMSET1K2 a *XCMPLX-0K3 s,a *XCMPLX-0K3 t,b *XCMPLX-0K3 s,b *XCMPLX-0K3 t }"
sorry

mdef member_1_def_11 (" _ '/'/'/MEMBER-1K14  _ " [164,164]164 ) where
  mlet "F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2", "G be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2"
"func F ///MEMBER-1K14 G \<rightarrow> setHIDDENM2 equals
  F **MEMBER-1K12 (G \<inverse>\<inverse>MEMBER-1K6)"
proof-
  (*coherence*)
    show "F **MEMBER-1K12 (G \<inverse>\<inverse>MEMBER-1K6) be setHIDDENM2"
       sorry
qed "sorry"

mtheorem member_1_th_101:
" for F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for G be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds F ///MEMBER-1K14 G =XBOOLE-0R4 {w1 /XXREAL-3K6 w2 where w1 be ElementSUBSET-1M1-of ExtREALXXREAL-0K3, w2 be ElementSUBSET-1M1-of ExtREALXXREAL-0K3 : w1 inTARSKIR2 F & w2 inTARSKIR2 G }"
sorry

mtheorem member_1_th_102:
" for F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for G be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for f be ExtRealXXREAL-0M1 holds  for g be ExtRealXXREAL-0M1 holds f inHIDDENR3 F & g inHIDDENR3 G implies f /XXREAL-3K6 g inHIDDENR3 F ///MEMBER-1K14 G"
sorry

mtheorem member_1_cl_51:
  mlet "F be emptyXBOOLE-0V1\<bar>setHIDDENM2", "G be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2"
"cluster F ///MEMBER-1K14 G as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "F ///MEMBER-1K14 G be emptyXBOOLE-0V1"
     sorry
qed "sorry"

mtheorem member_1_cl_52:
  mlet "F be emptyXBOOLE-0V1\<bar>setHIDDENM2", "G be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2"
"cluster G ///MEMBER-1K14 F as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "G ///MEMBER-1K14 F be emptyXBOOLE-0V1"
     sorry
qed "sorry"

mtheorem member_1_cl_53:
  mlet "F be ext-real-memberedMEMBEREDV2\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2", "G be ext-real-memberedMEMBEREDV2\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster F ///MEMBER-1K14 G as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "F ///MEMBER-1K14 G be  non emptyXBOOLE-0V1"
     sorry
qed "sorry"

mtheorem member_1_cl_54:
  mlet "F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2", "G be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2"
"cluster F ///MEMBER-1K14 G as-term-is ext-real-memberedMEMBEREDV2"
proof
(*coherence*)
  show "F ///MEMBER-1K14 G be ext-real-memberedMEMBEREDV2"
     sorry
qed "sorry"

mtheorem member_1_th_103:
" for F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for G be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for H be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for I be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds F c=MEMBEREDR2 G & H c=MEMBEREDR2 I implies F ///MEMBER-1K14 H c=MEMBEREDR2 G ///MEMBER-1K14 I"
sorry

mtheorem member_1_th_104:
" for F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for G be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for H be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds (F \\/XBOOLE-0K2 G)///MEMBER-1K14 H =MEMBEREDR8 F ///MEMBER-1K14 H \\/XBOOLE-0K2 G ///MEMBER-1K14 H"
  using member_1_th_82 sorry

mtheorem member_1_th_105:
" for F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for G be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for H be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds (F /\\XBOOLE-0K3 G)///MEMBER-1K14 H c=MEMBEREDR2 (F ///MEMBER-1K14 H)/\\XBOOLE-0K3 (G ///MEMBER-1K14 H)"
  using member_1_th_83 sorry

mtheorem member_1_th_106:
" for F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for G be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for H be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds F ///MEMBER-1K14 (G \\/XBOOLE-0K2 H) =MEMBEREDR8 F ///MEMBER-1K14 G \\/XBOOLE-0K2 F ///MEMBER-1K14 H"
sorry

mtheorem member_1_th_107:
" for F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for G be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for H be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds F ///MEMBER-1K14 (G /\\XBOOLE-0K3 H) c=MEMBEREDR2 (F ///MEMBER-1K14 G)/\\XBOOLE-0K3 (F ///MEMBER-1K14 H)"
sorry

mtheorem member_1_th_108:
" for F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for G be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for H be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds (F **MEMBER-1K12 G)///MEMBER-1K14 H =MEMBEREDR8 F **MEMBER-1K12 (G ///MEMBER-1K14 H)"
  using member_1_th_80 sorry

mtheorem member_1_th_109:
" for F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for G be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for H be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds (F ///MEMBER-1K14 G)**MEMBER-1K12 H =MEMBEREDR8 (F **MEMBER-1K12 H)///MEMBER-1K14 G"
  using member_1_th_80 sorry

mtheorem member_1_th_110:
" for F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for G be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for H be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds (F ///MEMBER-1K14 G)///MEMBER-1K14 H =MEMBEREDR8 F ///MEMBER-1K14 (G **MEMBER-1K12 H)"
sorry

mtheorem member_1_th_111:
" for f be ExtRealXXREAL-0M1 holds  for g be ExtRealXXREAL-0M1 holds {TARSKIK1 f} ///MEMBER-1K14 {TARSKIK1 g} =MEMBEREDR8 {TARSKIK1 f /XXREAL-3K6 g }"
sorry

mtheorem member_1_th_112:
" for f be ExtRealXXREAL-0M1 holds  for h be ExtRealXXREAL-0M1 holds  for i be ExtRealXXREAL-0M1 holds {TARSKIK1 f} ///MEMBER-1K14 {TARSKIK2 h,i } =MEMBEREDR8 {TARSKIK2 f /XXREAL-3K6 h,f /XXREAL-3K6 i }"
sorry

mtheorem member_1_th_113:
" for f be ExtRealXXREAL-0M1 holds  for g be ExtRealXXREAL-0M1 holds  for h be ExtRealXXREAL-0M1 holds {TARSKIK2 f,g } ///MEMBER-1K14 {TARSKIK1 h} =MEMBEREDR8 {TARSKIK2 f /XXREAL-3K6 h,g /XXREAL-3K6 h }"
sorry

mtheorem member_1_th_114:
" for f be ExtRealXXREAL-0M1 holds  for g be ExtRealXXREAL-0M1 holds  for h be ExtRealXXREAL-0M1 holds  for i be ExtRealXXREAL-0M1 holds {TARSKIK2 f,g } ///MEMBER-1K14 {TARSKIK2 h,i } =MEMBEREDR8 {ENUMSET1K2 f /XXREAL-3K6 h,f /XXREAL-3K6 i,g /XXREAL-3K6 h,g /XXREAL-3K6 i }"
sorry

mdef member_1_def_12 (" _ '/'/'/MEMBER-1K15  _ " [164,164]164 ) where
  mlet "A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2", "B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2"
"func A ///MEMBER-1K15 B \<rightarrow> setHIDDENM2 equals
  A **MEMBER-1K13 (B \<inverse>\<inverse>MEMBER-1K7)"
proof-
  (*coherence*)
    show "A **MEMBER-1K13 (B \<inverse>\<inverse>MEMBER-1K7) be setHIDDENM2"
       sorry
qed "sorry"

mtheorem member_1_th_115:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds A ///MEMBER-1K15 B =XBOOLE-0R4 {c1 /XCMPLX-0K7 c2 where c1 be ComplexXCMPLX-0M1, c2 be ComplexXCMPLX-0M1 : c1 inHIDDENR3 A & c2 inHIDDENR3 B }"
sorry

mtheorem member_1_th_116:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds a inHIDDENR3 A & b inHIDDENR3 B implies a /XCMPLX-0K7 b inTARSKIR2 A ///MEMBER-1K15 B"
sorry

mtheorem member_1_cl_55:
  mlet "A be emptyXBOOLE-0V1\<bar>setHIDDENM2", "B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2"
"cluster A ///MEMBER-1K15 B as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "A ///MEMBER-1K15 B be emptyXBOOLE-0V1"
     sorry
qed "sorry"

mtheorem member_1_cl_56:
  mlet "A be emptyXBOOLE-0V1\<bar>setHIDDENM2", "B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2"
"cluster B ///MEMBER-1K15 A as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "B ///MEMBER-1K15 A be emptyXBOOLE-0V1"
     sorry
qed "sorry"

mtheorem member_1_cl_57:
  mlet "A be complex-memberedMEMBEREDV1\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2", "B be complex-memberedMEMBEREDV1\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster A ///MEMBER-1K15 B as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "A ///MEMBER-1K15 B be  non emptyXBOOLE-0V1"
     sorry
qed "sorry"

mtheorem member_1_cl_58:
  mlet "A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2", "B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2"
"cluster A ///MEMBER-1K15 B as-term-is complex-memberedMEMBEREDV1"
proof
(*coherence*)
  show "A ///MEMBER-1K15 B be complex-memberedMEMBEREDV1"
     sorry
qed "sorry"

mtheorem member_1_cl_59:
  mlet "A be real-memberedMEMBEREDV3\<bar>setHIDDENM2", "B be real-memberedMEMBEREDV3\<bar>setHIDDENM2"
"cluster A ///MEMBER-1K15 B as-term-is real-memberedMEMBEREDV3"
proof
(*coherence*)
  show "A ///MEMBER-1K15 B be real-memberedMEMBEREDV3"
     sorry
qed "sorry"

mtheorem member_1_cl_60:
  mlet "A be rational-memberedMEMBEREDV4\<bar>setHIDDENM2", "B be rational-memberedMEMBEREDV4\<bar>setHIDDENM2"
"cluster A ///MEMBER-1K15 B as-term-is rational-memberedMEMBEREDV4"
proof
(*coherence*)
  show "A ///MEMBER-1K15 B be rational-memberedMEMBEREDV4"
     sorry
qed "sorry"

mtheorem member_1_ident_6:
  mlet "A be real-memberedMEMBEREDV3\<bar>setHIDDENM2", "B be real-memberedMEMBEREDV3\<bar>setHIDDENM2", "F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2", "G be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2"
"identify A ///MEMBER-1K15 B with F ///MEMBER-1K14 G when A =HIDDENR1 F & B =HIDDENR1 G"
proof
(*compatibility*)
  show "A =HIDDENR1 F & B =HIDDENR1 G implies A ///MEMBER-1K15 B =HIDDENR1 F ///MEMBER-1K14 G"
     sorry
qed "sorry"

mtheorem member_1_th_117:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for C be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for D be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds A c=MEMBEREDR1 B & C c=MEMBEREDR1 D implies A ///MEMBER-1K15 C c=MEMBEREDR1 B ///MEMBER-1K15 D"
sorry

mtheorem member_1_th_118:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for C be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds A ///MEMBER-1K15 (B \\/XBOOLE-0K2 C) =MEMBEREDR7 A ///MEMBER-1K15 B \\/XBOOLE-0K2 A ///MEMBER-1K15 C"
sorry

mtheorem member_1_th_119:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for C be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds A ///MEMBER-1K15 (B /\\XBOOLE-0K3 C) c=MEMBEREDR1 (A ///MEMBER-1K15 B)/\\XBOOLE-0K3 (A ///MEMBER-1K15 C)"
sorry

mtheorem member_1_th_120:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds A ///MEMBER-1K15 (--MEMBER-1K5 B) =MEMBEREDR7 --MEMBER-1K5 A ///MEMBER-1K15 B"
sorry

mtheorem member_1_th_121:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds (--MEMBER-1K5 A)///MEMBER-1K15 B =MEMBEREDR7 --MEMBER-1K5 A ///MEMBER-1K15 B"
  using member_1_th_94 sorry

mtheorem member_1_th_122:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for C be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds (A ++MEMBER-1K9 B)///MEMBER-1K15 C c=MEMBEREDR1 A ///MEMBER-1K15 C ++MEMBER-1K9 B ///MEMBER-1K15 C"
  using member_1_th_95 sorry

mtheorem member_1_th_123:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for C be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds (A --MEMBER-1K11 B)///MEMBER-1K15 C c=MEMBEREDR1 A ///MEMBER-1K15 C --MEMBER-1K11 B ///MEMBER-1K15 C"
sorry

mtheorem member_1_th_124:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for C be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds (A **MEMBER-1K13 B)///MEMBER-1K15 C =MEMBEREDR7 A **MEMBER-1K13 (B ///MEMBER-1K15 C)"
  using member_1_th_90 sorry

mtheorem member_1_th_125:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for C be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds (A ///MEMBER-1K15 B)**MEMBER-1K13 C =MEMBEREDR7 (A **MEMBER-1K13 C)///MEMBER-1K15 B"
  using member_1_th_90 sorry

mtheorem member_1_th_126:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for C be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds (A ///MEMBER-1K15 B)///MEMBER-1K15 C =MEMBEREDR7 A ///MEMBER-1K15 (B **MEMBER-1K13 C)"
sorry

mtheorem member_1_th_127:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for C be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds A ///MEMBER-1K15 (B ///MEMBER-1K15 C) =MEMBEREDR7 (A **MEMBER-1K13 C)///MEMBER-1K15 B"
sorry

mtheorem member_1_th_128:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds {TARSKIK1 a} ///MEMBER-1K15 {TARSKIK1 b} =MEMBEREDR7 {TARSKIK1 a /XCMPLX-0K7 b }"
sorry

mtheorem member_1_th_129:
" for a be ComplexXCMPLX-0M1 holds  for s be ComplexXCMPLX-0M1 holds  for t be ComplexXCMPLX-0M1 holds {TARSKIK1 a} ///MEMBER-1K15 {TARSKIK2 s,t } =MEMBEREDR7 {TARSKIK2 a /XCMPLX-0K7 s,a /XCMPLX-0K7 t }"
sorry

mtheorem member_1_th_130:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for s be ComplexXCMPLX-0M1 holds {TARSKIK2 a,b } ///MEMBER-1K15 {TARSKIK1 s} =MEMBEREDR7 {TARSKIK2 a /XCMPLX-0K7 s,b /XCMPLX-0K7 s }"
sorry

mtheorem member_1_th_131:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for s be ComplexXCMPLX-0M1 holds  for t be ComplexXCMPLX-0M1 holds {TARSKIK2 a,b } ///MEMBER-1K15 {TARSKIK2 s,t } =MEMBEREDR7 {ENUMSET1K2 a /XCMPLX-0K7 s,a /XCMPLX-0K7 t,b /XCMPLX-0K7 s,b /XCMPLX-0K7 t }"
sorry

mdef member_1_def_13 (" _ ++MEMBER-1K16  _ " [132,132]132 ) where
  mlet "F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2", "f be ExtRealXXREAL-0M1"
"func f ++MEMBER-1K16 F \<rightarrow> setHIDDENM2 equals
  {TARSKIK1 f} ++MEMBER-1K8 F"
proof-
  (*coherence*)
    show "{TARSKIK1 f} ++MEMBER-1K8 F be setHIDDENM2"
       sorry
qed "sorry"

mtheorem member_1_th_132:
" for G be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for f be ExtRealXXREAL-0M1 holds  for g be ExtRealXXREAL-0M1 holds g inHIDDENR3 G implies f +XXREAL-3K1 g inHIDDENR3 f ++MEMBER-1K16 G"
sorry

mtheorem member_1_th_133:
" for F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for f be ExtRealXXREAL-0M1 holds f ++MEMBER-1K16 F =XBOOLE-0R4 {f +XXREAL-3K1 w where w be ElementSUBSET-1M1-of ExtREALXXREAL-0K3 : w inTARSKIR2 F }"
sorry

mtheorem member_1_th_134:
" for F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for f be ExtRealXXREAL-0M1 holds  for e be setHIDDENM2 holds e inTARSKIR2 f ++MEMBER-1K16 F implies ( ex w be ElementSUBSET-1M1-of ExtREALXXREAL-0K3 st e =HIDDENR1 f +XXREAL-3K1 w & w inTARSKIR2 F)"
sorry

mtheorem member_1_cl_61:
  mlet "F be emptyXBOOLE-0V1\<bar>setHIDDENM2", "f be ExtRealXXREAL-0M1"
"cluster f ++MEMBER-1K16 F as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "f ++MEMBER-1K16 F be emptyXBOOLE-0V1"
     sorry
qed "sorry"

mtheorem member_1_cl_62:
  mlet "F be ext-real-memberedMEMBEREDV2\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2", "f be ExtRealXXREAL-0M1"
"cluster f ++MEMBER-1K16 F as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "f ++MEMBER-1K16 F be  non emptyXBOOLE-0V1"
     sorry
qed "sorry"

mtheorem member_1_cl_63:
  mlet "F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2", "f be ExtRealXXREAL-0M1"
"cluster f ++MEMBER-1K16 F as-term-is ext-real-memberedMEMBEREDV2"
proof
(*coherence*)
  show "f ++MEMBER-1K16 F be ext-real-memberedMEMBEREDV2"
     sorry
qed "sorry"

mtheorem member_1_th_135:
" for F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for G be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for r be RealXREAL-0M1 holds r ++MEMBER-1K16 F c=MEMBEREDR2 r ++MEMBER-1K16 G implies F c=MEMBEREDR2 G"
sorry

mtheorem member_1_th_136:
" for F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for G be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for r be RealXREAL-0M1 holds r ++MEMBER-1K16 F =MEMBEREDR8 r ++MEMBER-1K16 G implies F =MEMBEREDR8 G"
sorry

mtheorem member_1_th_137:
" for F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for G be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for r be RealXREAL-0M1 holds r ++MEMBER-1K16 F /\\XBOOLE-0K3 G =MEMBEREDR8 (r ++MEMBER-1K16 F)/\\XBOOLE-0K3 (r ++MEMBER-1K16 G)"
sorry

mtheorem member_1_th_138:
" for F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for G be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for f be ExtRealXXREAL-0M1 holds (f ++MEMBER-1K16 F)\\SUBSET-1K6 (f ++MEMBER-1K16 G) c=MEMBEREDR2 f ++MEMBER-1K16 (F \\SUBSET-1K6 G)"
sorry

mtheorem member_1_th_139:
" for F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for G be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for r be RealXREAL-0M1 holds r ++MEMBER-1K16 (F \\SUBSET-1K6 G) =MEMBEREDR8 (r ++MEMBER-1K16 F)\\SUBSET-1K6 (r ++MEMBER-1K16 G)"
sorry

mtheorem member_1_th_140:
" for F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for G be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for r be RealXREAL-0M1 holds r ++MEMBER-1K16 (F \\+\\XBOOLE-0K5 G) =MEMBEREDR8 r ++MEMBER-1K16 F \\+\\XBOOLE-0K5 r ++MEMBER-1K16 G"
sorry

mdef member_1_def_14 (" _ ++MEMBER-1K17  _ " [132,132]132 ) where
  mlet "A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2", "a be ComplexXCMPLX-0M1"
"func a ++MEMBER-1K17 A \<rightarrow> setHIDDENM2 equals
  {TARSKIK1 a} ++MEMBER-1K9 A"
proof-
  (*coherence*)
    show "{TARSKIK1 a} ++MEMBER-1K9 A be setHIDDENM2"
       sorry
qed "sorry"

mtheorem member_1_th_141:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds b inHIDDENR3 A implies a +XCMPLX-0K2 b inTARSKIR2 a ++MEMBER-1K17 A"
sorry

mtheorem member_1_th_142:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for a be ComplexXCMPLX-0M1 holds a ++MEMBER-1K17 A =XBOOLE-0R4 {a +XCMPLX-0K2 c where c be ComplexXCMPLX-0M1 : c inHIDDENR3 A }"
sorry

mtheorem member_1_th_143:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for a be ComplexXCMPLX-0M1 holds  for e be setHIDDENM2 holds e inTARSKIR2 a ++MEMBER-1K17 A implies ( ex c be ComplexXCMPLX-0M1 st e =XBOOLE-0R4 a +XCMPLX-0K2 c & c inHIDDENR3 A)"
sorry

mtheorem member_1_cl_64:
  mlet "A be emptyXBOOLE-0V1\<bar>setHIDDENM2", "a be ComplexXCMPLX-0M1"
"cluster a ++MEMBER-1K17 A as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "a ++MEMBER-1K17 A be emptyXBOOLE-0V1"
     sorry
qed "sorry"

mtheorem member_1_cl_65:
  mlet "A be complex-memberedMEMBEREDV1\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2", "a be ComplexXCMPLX-0M1"
"cluster a ++MEMBER-1K17 A as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "a ++MEMBER-1K17 A be  non emptyXBOOLE-0V1"
     sorry
qed "sorry"

mtheorem member_1_cl_66:
  mlet "A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2", "a be ComplexXCMPLX-0M1"
"cluster a ++MEMBER-1K17 A as-term-is complex-memberedMEMBEREDV1"
proof
(*coherence*)
  show "a ++MEMBER-1K17 A be complex-memberedMEMBEREDV1"
     sorry
qed "sorry"

mtheorem member_1_cl_67:
  mlet "A be real-memberedMEMBEREDV3\<bar>setHIDDENM2", "a be RealXREAL-0M1"
"cluster a ++MEMBER-1K17 A as-term-is real-memberedMEMBEREDV3"
proof
(*coherence*)
  show "a ++MEMBER-1K17 A be real-memberedMEMBEREDV3"
     sorry
qed "sorry"

mtheorem member_1_cl_68:
  mlet "A be rational-memberedMEMBEREDV4\<bar>setHIDDENM2", "a be RationalRAT-1M1"
"cluster a ++MEMBER-1K17 A as-term-is rational-memberedMEMBEREDV4"
proof
(*coherence*)
  show "a ++MEMBER-1K17 A be rational-memberedMEMBEREDV4"
     sorry
qed "sorry"

mtheorem member_1_cl_69:
  mlet "A be integer-memberedMEMBEREDV5\<bar>setHIDDENM2", "a be IntegerINT-1M1"
"cluster a ++MEMBER-1K17 A as-term-is integer-memberedMEMBEREDV5"
proof
(*coherence*)
  show "a ++MEMBER-1K17 A be integer-memberedMEMBEREDV5"
     sorry
qed "sorry"

mtheorem member_1_cl_70:
  mlet "A be natural-memberedMEMBEREDV6\<bar>setHIDDENM2", "a be NatORDINAL1M6"
"cluster a ++MEMBER-1K17 A as-term-is natural-memberedMEMBEREDV6"
proof
(*coherence*)
  show "a ++MEMBER-1K17 A be natural-memberedMEMBEREDV6"
     sorry
qed "sorry"

mtheorem member_1_ident_7:
  mlet "A be real-memberedMEMBEREDV3\<bar>setHIDDENM2", "F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2", "a be RealXREAL-0M1", "f be ExtRealXXREAL-0M1"
"identify a ++MEMBER-1K17 A with f ++MEMBER-1K16 F when a =HIDDENR1 f & A =HIDDENR1 F"
proof
(*compatibility*)
  show "a =HIDDENR1 f & A =HIDDENR1 F implies a ++MEMBER-1K17 A =HIDDENR1 f ++MEMBER-1K16 F"
     sorry
qed "sorry"

mtheorem member_1_th_144:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for a be ComplexXCMPLX-0M1 holds A c=MEMBEREDR1 B iff a ++MEMBER-1K17 A c=MEMBEREDR1 a ++MEMBER-1K17 B"
sorry

mtheorem member_1_th_145:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for a be ComplexXCMPLX-0M1 holds a ++MEMBER-1K17 A =MEMBEREDR7 a ++MEMBER-1K17 B implies A =MEMBEREDR7 B"
sorry

mtheorem member_1_th_146:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds 0NUMBERSK6 ++MEMBER-1K17 A =MEMBEREDR7 A"
sorry

mtheorem member_1_th_147:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds (a +XCMPLX-0K2 b)++MEMBER-1K17 A =MEMBEREDR7 a ++MEMBER-1K17 (b ++MEMBER-1K17 A)"
sorry

mtheorem member_1_th_148:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for a be ComplexXCMPLX-0M1 holds a ++MEMBER-1K17 (A ++MEMBER-1K9 B) =MEMBEREDR7 (a ++MEMBER-1K17 A)++MEMBER-1K9 B"
  using member_1_th_50 sorry

mtheorem member_1_th_149:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for a be ComplexXCMPLX-0M1 holds a ++MEMBER-1K17 A /\\XBOOLE-0K3 B =MEMBEREDR7 (a ++MEMBER-1K17 A)/\\XBOOLE-0K3 (a ++MEMBER-1K17 B)"
sorry

mtheorem member_1_th_150:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for a be ComplexXCMPLX-0M1 holds a ++MEMBER-1K17 (A \\SUBSET-1K6 B) =MEMBEREDR7 (a ++MEMBER-1K17 A)\\SUBSET-1K6 (a ++MEMBER-1K17 B)"
sorry

mtheorem member_1_th_151:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for a be ComplexXCMPLX-0M1 holds a ++MEMBER-1K17 (A \\+\\XBOOLE-0K5 B) =MEMBEREDR7 a ++MEMBER-1K17 A \\+\\XBOOLE-0K5 a ++MEMBER-1K17 B"
sorry

mdef member_1_def_15 (" _ --MEMBER-1K18  _ " [132,132]132 ) where
  mlet "F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2", "f be ExtRealXXREAL-0M1"
"func f --MEMBER-1K18 F \<rightarrow> setHIDDENM2 equals
  {TARSKIK1 f} --MEMBER-1K10 F"
proof-
  (*coherence*)
    show "{TARSKIK1 f} --MEMBER-1K10 F be setHIDDENM2"
       sorry
qed "sorry"

mtheorem member_1_th_152:
" for G be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for f be ExtRealXXREAL-0M1 holds  for g be ExtRealXXREAL-0M1 holds g inHIDDENR3 G implies f -XXREAL-3K3 g inHIDDENR3 f --MEMBER-1K18 G"
sorry

mtheorem member_1_th_153:
" for F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for f be ExtRealXXREAL-0M1 holds f --MEMBER-1K18 F =XBOOLE-0R4 {f -XXREAL-3K3 w where w be ElementSUBSET-1M1-of ExtREALXXREAL-0K3 : w inTARSKIR2 F }"
sorry

mtheorem member_1_th_154:
" for F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for f be ExtRealXXREAL-0M1 holds  for e be setHIDDENM2 holds e inTARSKIR2 f --MEMBER-1K18 F implies ( ex w be ElementSUBSET-1M1-of ExtREALXXREAL-0K3 st e =HIDDENR1 f -XXREAL-3K3 w & w inTARSKIR2 F)"
sorry

mtheorem member_1_cl_71:
  mlet "F be emptyXBOOLE-0V1\<bar>setHIDDENM2", "f be ExtRealXXREAL-0M1"
"cluster f --MEMBER-1K18 F as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "f --MEMBER-1K18 F be emptyXBOOLE-0V1"
     sorry
qed "sorry"

mtheorem member_1_cl_72:
  mlet "F be ext-real-memberedMEMBEREDV2\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2", "f be ExtRealXXREAL-0M1"
"cluster f --MEMBER-1K18 F as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "f --MEMBER-1K18 F be  non emptyXBOOLE-0V1"
     sorry
qed "sorry"

mtheorem member_1_cl_73:
  mlet "F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2", "f be ExtRealXXREAL-0M1"
"cluster f --MEMBER-1K18 F as-term-is ext-real-memberedMEMBEREDV2"
proof
(*coherence*)
  show "f --MEMBER-1K18 F be ext-real-memberedMEMBEREDV2"
     sorry
qed "sorry"

mtheorem member_1_th_155:
" for F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for G be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for r be RealXREAL-0M1 holds r --MEMBER-1K18 F c=MEMBEREDR2 r --MEMBER-1K18 G implies F c=MEMBEREDR2 G"
sorry

mtheorem member_1_th_156:
" for F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for G be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for r be RealXREAL-0M1 holds r --MEMBER-1K18 F =MEMBEREDR8 r --MEMBER-1K18 G implies F =MEMBEREDR8 G"
sorry

mtheorem member_1_th_157:
" for F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for G be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for r be RealXREAL-0M1 holds r --MEMBER-1K18 F /\\XBOOLE-0K3 G =MEMBEREDR8 (r --MEMBER-1K18 F)/\\XBOOLE-0K3 (r --MEMBER-1K18 G)"
sorry

mtheorem member_1_th_158:
" for F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for G be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for r be RealXREAL-0M1 holds r --MEMBER-1K18 (F \\SUBSET-1K6 G) =MEMBEREDR8 (r --MEMBER-1K18 F)\\SUBSET-1K6 (r --MEMBER-1K18 G)"
sorry

mtheorem member_1_th_159:
" for F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for G be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for r be RealXREAL-0M1 holds r --MEMBER-1K18 (F \\+\\XBOOLE-0K5 G) =MEMBEREDR8 r --MEMBER-1K18 F \\+\\XBOOLE-0K5 r --MEMBER-1K18 G"
sorry

mdef member_1_def_16 (" _ --MEMBER-1K19  _ " [132,132]132 ) where
  mlet "A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2", "a be ComplexXCMPLX-0M1"
"func a --MEMBER-1K19 A \<rightarrow> setHIDDENM2 equals
  {TARSKIK1 a} --MEMBER-1K11 A"
proof-
  (*coherence*)
    show "{TARSKIK1 a} --MEMBER-1K11 A be setHIDDENM2"
       sorry
qed "sorry"

mtheorem member_1_th_160:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds b inHIDDENR3 A implies a -XCMPLX-0K6 b inTARSKIR2 a --MEMBER-1K19 A"
sorry

mtheorem member_1_th_161:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for a be ComplexXCMPLX-0M1 holds a --MEMBER-1K19 A =XBOOLE-0R4 {a -XCMPLX-0K6 c where c be ComplexXCMPLX-0M1 : c inHIDDENR3 A }"
sorry

mtheorem member_1_th_162:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for a be ComplexXCMPLX-0M1 holds  for e be setHIDDENM2 holds e inTARSKIR2 a --MEMBER-1K19 A implies ( ex c be ComplexXCMPLX-0M1 st e =XBOOLE-0R4 a -XCMPLX-0K6 c & c inHIDDENR3 A)"
sorry

mtheorem member_1_cl_74:
  mlet "A be emptyXBOOLE-0V1\<bar>setHIDDENM2", "a be ComplexXCMPLX-0M1"
"cluster a --MEMBER-1K19 A as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "a --MEMBER-1K19 A be emptyXBOOLE-0V1"
     sorry
qed "sorry"

mtheorem member_1_cl_75:
  mlet "A be complex-memberedMEMBEREDV1\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2", "a be ComplexXCMPLX-0M1"
"cluster a --MEMBER-1K19 A as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "a --MEMBER-1K19 A be  non emptyXBOOLE-0V1"
     sorry
qed "sorry"

mtheorem member_1_cl_76:
  mlet "A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2", "a be ComplexXCMPLX-0M1"
"cluster a --MEMBER-1K19 A as-term-is complex-memberedMEMBEREDV1"
proof
(*coherence*)
  show "a --MEMBER-1K19 A be complex-memberedMEMBEREDV1"
     sorry
qed "sorry"

mtheorem member_1_cl_77:
  mlet "A be real-memberedMEMBEREDV3\<bar>setHIDDENM2", "a be RealXREAL-0M1"
"cluster a --MEMBER-1K19 A as-term-is real-memberedMEMBEREDV3"
proof
(*coherence*)
  show "a --MEMBER-1K19 A be real-memberedMEMBEREDV3"
     sorry
qed "sorry"

mtheorem member_1_cl_78:
  mlet "A be rational-memberedMEMBEREDV4\<bar>setHIDDENM2", "a be RationalRAT-1M1"
"cluster a --MEMBER-1K19 A as-term-is rational-memberedMEMBEREDV4"
proof
(*coherence*)
  show "a --MEMBER-1K19 A be rational-memberedMEMBEREDV4"
     sorry
qed "sorry"

mtheorem member_1_cl_79:
  mlet "A be integer-memberedMEMBEREDV5\<bar>setHIDDENM2", "a be IntegerINT-1M1"
"cluster a --MEMBER-1K19 A as-term-is integer-memberedMEMBEREDV5"
proof
(*coherence*)
  show "a --MEMBER-1K19 A be integer-memberedMEMBEREDV5"
     sorry
qed "sorry"

mtheorem member_1_ident_8:
  mlet "A be real-memberedMEMBEREDV3\<bar>setHIDDENM2", "F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2", "a be RealXREAL-0M1", "f be ExtRealXXREAL-0M1"
"identify a --MEMBER-1K19 A with f --MEMBER-1K18 F when a =HIDDENR1 f & A =HIDDENR1 F"
proof
(*compatibility*)
  show "a =HIDDENR1 f & A =HIDDENR1 F implies a --MEMBER-1K19 A =HIDDENR1 f --MEMBER-1K18 F"
     sorry
qed "sorry"

mtheorem member_1_th_163:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for a be ComplexXCMPLX-0M1 holds A c=MEMBEREDR1 B iff a --MEMBER-1K19 A c=MEMBEREDR1 a --MEMBER-1K19 B"
sorry

mtheorem member_1_th_164:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for a be ComplexXCMPLX-0M1 holds a --MEMBER-1K19 A =MEMBEREDR7 a --MEMBER-1K19 B implies A =MEMBEREDR7 B"
sorry

mtheorem member_1_th_165:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for a be ComplexXCMPLX-0M1 holds a --MEMBER-1K19 A /\\XBOOLE-0K3 B =MEMBEREDR7 (a --MEMBER-1K19 A)/\\XBOOLE-0K3 (a --MEMBER-1K19 B)"
sorry

mtheorem member_1_th_166:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for a be ComplexXCMPLX-0M1 holds a --MEMBER-1K19 (A \\SUBSET-1K6 B) =MEMBEREDR7 (a --MEMBER-1K19 A)\\SUBSET-1K6 (a --MEMBER-1K19 B)"
sorry

mtheorem member_1_th_167:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for a be ComplexXCMPLX-0M1 holds a --MEMBER-1K19 (A \\+\\XBOOLE-0K5 B) =MEMBEREDR7 a --MEMBER-1K19 A \\+\\XBOOLE-0K5 a --MEMBER-1K19 B"
sorry

mdef member_1_def_17 (" _ --MEMBER-1K20  _ " [132,132]132 ) where
  mlet "F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2", "f be ExtRealXXREAL-0M1"
"func F --MEMBER-1K20 f \<rightarrow> setHIDDENM2 equals
  F --MEMBER-1K10 {TARSKIK1 f}"
proof-
  (*coherence*)
    show "F --MEMBER-1K10 {TARSKIK1 f} be setHIDDENM2"
       sorry
qed "sorry"

mtheorem member_1_th_168:
" for G be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for f be ExtRealXXREAL-0M1 holds  for g be ExtRealXXREAL-0M1 holds g inHIDDENR3 G implies g -XXREAL-3K3 f inHIDDENR3 G --MEMBER-1K20 f"
sorry

mtheorem member_1_th_169:
" for F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for f be ExtRealXXREAL-0M1 holds F --MEMBER-1K20 f =XBOOLE-0R4 {w -XXREAL-3K3 f where w be ElementSUBSET-1M1-of ExtREALXXREAL-0K3 : w inTARSKIR2 F }"
sorry

mtheorem member_1_th_170:
" for F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for f be ExtRealXXREAL-0M1 holds  for e be setHIDDENM2 holds e inTARSKIR2 F --MEMBER-1K20 f implies ( ex w be ElementSUBSET-1M1-of ExtREALXXREAL-0K3 st e =HIDDENR1 w -XXREAL-3K3 f & w inTARSKIR2 F)"
sorry

mtheorem member_1_cl_80:
  mlet "F be emptyXBOOLE-0V1\<bar>setHIDDENM2", "f be ExtRealXXREAL-0M1"
"cluster F --MEMBER-1K20 f as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "F --MEMBER-1K20 f be emptyXBOOLE-0V1"
     sorry
qed "sorry"

mtheorem member_1_cl_81:
  mlet "F be ext-real-memberedMEMBEREDV2\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2", "f be ExtRealXXREAL-0M1"
"cluster F --MEMBER-1K20 f as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "F --MEMBER-1K20 f be  non emptyXBOOLE-0V1"
     sorry
qed "sorry"

mtheorem member_1_cl_82:
  mlet "F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2", "f be ExtRealXXREAL-0M1"
"cluster F --MEMBER-1K20 f as-term-is ext-real-memberedMEMBEREDV2"
proof
(*coherence*)
  show "F --MEMBER-1K20 f be ext-real-memberedMEMBEREDV2"
     sorry
qed "sorry"

mtheorem member_1_th_171:
" for F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for f be ExtRealXXREAL-0M1 holds F --MEMBER-1K20 f =MEMBEREDR8 --MEMBER-1K4 (f --MEMBER-1K18 F)"
  using member_1_th_60 sorry

mtheorem member_1_th_172:
" for F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for f be ExtRealXXREAL-0M1 holds f --MEMBER-1K18 F =MEMBEREDR8 --MEMBER-1K4 (F --MEMBER-1K20 f)"
  using member_1_th_60 sorry

mtheorem member_1_th_173:
" for F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for G be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for r be RealXREAL-0M1 holds F /\\XBOOLE-0K3 G --MEMBER-1K20 r =MEMBEREDR8 (F --MEMBER-1K20 r)/\\XBOOLE-0K3 (G --MEMBER-1K20 r)"
sorry

mtheorem member_1_th_174:
" for F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for G be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for r be RealXREAL-0M1 holds (F \\SUBSET-1K6 G)--MEMBER-1K20 r =MEMBEREDR8 (F --MEMBER-1K20 r)\\SUBSET-1K6 (G --MEMBER-1K20 r)"
sorry

mtheorem member_1_th_175:
" for F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for G be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for r be RealXREAL-0M1 holds (F \\+\\XBOOLE-0K5 G)--MEMBER-1K20 r =MEMBEREDR8 F --MEMBER-1K20 r \\+\\XBOOLE-0K5 G --MEMBER-1K20 r"
sorry

mdef member_1_def_18 (" _ --MEMBER-1K21  _ " [132,132]132 ) where
  mlet "A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2", "a be ComplexXCMPLX-0M1"
"func A --MEMBER-1K21 a \<rightarrow> setHIDDENM2 equals
  A --MEMBER-1K11 {TARSKIK1 a}"
proof-
  (*coherence*)
    show "A --MEMBER-1K11 {TARSKIK1 a} be setHIDDENM2"
       sorry
qed "sorry"

mtheorem member_1_th_176:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds b inHIDDENR3 A implies b -XCMPLX-0K6 a inTARSKIR2 A --MEMBER-1K21 a"
sorry

mtheorem member_1_th_177:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for a be ComplexXCMPLX-0M1 holds A --MEMBER-1K21 a =XBOOLE-0R4 {c -XCMPLX-0K6 a where c be ComplexXCMPLX-0M1 : c inHIDDENR3 A }"
sorry

mtheorem member_1_th_178:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for a be ComplexXCMPLX-0M1 holds  for e be setHIDDENM2 holds e inTARSKIR2 A --MEMBER-1K21 a implies ( ex c be ComplexXCMPLX-0M1 st e =XBOOLE-0R4 c -XCMPLX-0K6 a & c inHIDDENR3 A)"
sorry

mtheorem member_1_cl_83:
  mlet "A be emptyXBOOLE-0V1\<bar>setHIDDENM2", "a be ComplexXCMPLX-0M1"
"cluster A --MEMBER-1K21 a as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "A --MEMBER-1K21 a be emptyXBOOLE-0V1"
     sorry
qed "sorry"

mtheorem member_1_cl_84:
  mlet "A be complex-memberedMEMBEREDV1\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2", "a be ComplexXCMPLX-0M1"
"cluster A --MEMBER-1K21 a as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "A --MEMBER-1K21 a be  non emptyXBOOLE-0V1"
     sorry
qed "sorry"

mtheorem member_1_cl_85:
  mlet "A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2", "a be ComplexXCMPLX-0M1"
"cluster A --MEMBER-1K21 a as-term-is complex-memberedMEMBEREDV1"
proof
(*coherence*)
  show "A --MEMBER-1K21 a be complex-memberedMEMBEREDV1"
     sorry
qed "sorry"

mtheorem member_1_cl_86:
  mlet "A be real-memberedMEMBEREDV3\<bar>setHIDDENM2", "a be RealXREAL-0M1"
"cluster A --MEMBER-1K21 a as-term-is real-memberedMEMBEREDV3"
proof
(*coherence*)
  show "A --MEMBER-1K21 a be real-memberedMEMBEREDV3"
     sorry
qed "sorry"

mtheorem member_1_cl_87:
  mlet "A be rational-memberedMEMBEREDV4\<bar>setHIDDENM2", "a be RationalRAT-1M1"
"cluster A --MEMBER-1K21 a as-term-is rational-memberedMEMBEREDV4"
proof
(*coherence*)
  show "A --MEMBER-1K21 a be rational-memberedMEMBEREDV4"
     sorry
qed "sorry"

mtheorem member_1_cl_88:
  mlet "A be integer-memberedMEMBEREDV5\<bar>setHIDDENM2", "a be IntegerINT-1M1"
"cluster A --MEMBER-1K21 a as-term-is integer-memberedMEMBEREDV5"
proof
(*coherence*)
  show "A --MEMBER-1K21 a be integer-memberedMEMBEREDV5"
     sorry
qed "sorry"

mtheorem member_1_ident_9:
  mlet "A be real-memberedMEMBEREDV3\<bar>setHIDDENM2", "F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2", "a be RealXREAL-0M1", "f be ExtRealXXREAL-0M1"
"identify A --MEMBER-1K21 a with F --MEMBER-1K20 f when a =HIDDENR1 f & A =HIDDENR1 F"
proof
(*compatibility*)
  show "a =HIDDENR1 f & A =HIDDENR1 F implies A --MEMBER-1K21 a =HIDDENR1 F --MEMBER-1K20 f"
     sorry
qed "sorry"

mtheorem member_1_th_179:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for a be ComplexXCMPLX-0M1 holds A c=MEMBEREDR1 B iff A --MEMBER-1K21 a c=MEMBEREDR1 B --MEMBER-1K21 a"
sorry

mtheorem member_1_th_180:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for a be ComplexXCMPLX-0M1 holds A --MEMBER-1K21 a =MEMBEREDR7 B --MEMBER-1K21 a implies A =MEMBEREDR7 B"
sorry

mtheorem member_1_th_181:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for a be ComplexXCMPLX-0M1 holds A --MEMBER-1K21 a =MEMBEREDR7 --MEMBER-1K5 (a --MEMBER-1K19 A)"
  using member_1_th_71 sorry

mtheorem member_1_th_182:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for a be ComplexXCMPLX-0M1 holds a --MEMBER-1K19 A =MEMBEREDR7 --MEMBER-1K5 (A --MEMBER-1K21 a)"
  using member_1_th_71 sorry

mtheorem member_1_th_183:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for a be ComplexXCMPLX-0M1 holds A /\\XBOOLE-0K3 B --MEMBER-1K21 a =MEMBEREDR7 (A --MEMBER-1K21 a)/\\XBOOLE-0K3 (B --MEMBER-1K21 a)"
sorry

mtheorem member_1_th_184:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for a be ComplexXCMPLX-0M1 holds (A \\SUBSET-1K6 B)--MEMBER-1K21 a =MEMBEREDR7 (A --MEMBER-1K21 a)\\SUBSET-1K6 (B --MEMBER-1K21 a)"
sorry

mtheorem member_1_th_185:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for a be ComplexXCMPLX-0M1 holds (A \\+\\XBOOLE-0K5 B)--MEMBER-1K21 a =MEMBEREDR7 A --MEMBER-1K21 a \\+\\XBOOLE-0K5 B --MEMBER-1K21 a"
sorry

mdef member_1_def_19 (" _ **MEMBER-1K22  _ " [164,164]164 ) where
  mlet "F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2", "f be ExtRealXXREAL-0M1"
"func f **MEMBER-1K22 F \<rightarrow> setHIDDENM2 equals
  {TARSKIK1 f} **MEMBER-1K12 F"
proof-
  (*coherence*)
    show "{TARSKIK1 f} **MEMBER-1K12 F be setHIDDENM2"
       sorry
qed "sorry"

mtheorem member_1_th_186:
" for G be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for f be ExtRealXXREAL-0M1 holds  for g be ExtRealXXREAL-0M1 holds g inHIDDENR3 G implies f *XXREAL-3K4 g inHIDDENR3 f **MEMBER-1K22 G"
sorry

mtheorem member_1_th_187:
" for F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for f be ExtRealXXREAL-0M1 holds f **MEMBER-1K22 F =XBOOLE-0R4 {f *XXREAL-3K4 w where w be ElementSUBSET-1M1-of ExtREALXXREAL-0K3 : w inTARSKIR2 F }"
sorry

mtheorem member_1_th_188:
" for F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for f be ExtRealXXREAL-0M1 holds  for e be setHIDDENM2 holds e inTARSKIR2 f **MEMBER-1K22 F implies ( ex w be ElementSUBSET-1M1-of ExtREALXXREAL-0K3 st e =HIDDENR1 f *XXREAL-3K4 w & w inTARSKIR2 F)"
sorry

mtheorem member_1_cl_89:
  mlet "F be emptyXBOOLE-0V1\<bar>setHIDDENM2", "f be ExtRealXXREAL-0M1"
"cluster f **MEMBER-1K22 F as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "f **MEMBER-1K22 F be emptyXBOOLE-0V1"
     sorry
qed "sorry"

mtheorem member_1_cl_90:
  mlet "F be ext-real-memberedMEMBEREDV2\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2", "f be ExtRealXXREAL-0M1"
"cluster f **MEMBER-1K22 F as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "f **MEMBER-1K22 F be  non emptyXBOOLE-0V1"
     sorry
qed "sorry"

mtheorem member_1_cl_91:
  mlet "F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2", "f be ExtRealXXREAL-0M1"
"cluster f **MEMBER-1K22 F as-term-is ext-real-memberedMEMBEREDV2"
proof
(*coherence*)
  show "f **MEMBER-1K22 F be ext-real-memberedMEMBEREDV2"
     sorry
qed "sorry"

mtheorem member_1_th_189:
" for F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for G be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for r be RealXREAL-0M1 holds r <>HIDDENR2 0NUMBERSK6 implies r **MEMBER-1K22 (F /\\XBOOLE-0K3 G) =MEMBEREDR8 (r **MEMBER-1K22 F)/\\XBOOLE-0K3 (r **MEMBER-1K22 G)"
sorry

mtheorem member_1_th_190:
" for F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for G be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for f be ExtRealXXREAL-0M1 holds f **MEMBER-1K22 F \\SUBSET-1K6 f **MEMBER-1K22 G c=MEMBEREDR2 f **MEMBER-1K22 (F \\SUBSET-1K6 G)"
sorry

mtheorem member_1_th_191:
" for F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for G be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for r be RealXREAL-0M1 holds r <>HIDDENR2 0NUMBERSK6 implies r **MEMBER-1K22 (F \\SUBSET-1K6 G) =MEMBEREDR8 r **MEMBER-1K22 F \\SUBSET-1K6 r **MEMBER-1K22 G"
sorry

mtheorem member_1_th_192:
" for F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for G be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for r be RealXREAL-0M1 holds r <>HIDDENR2 0NUMBERSK6 implies r **MEMBER-1K22 (F \\+\\XBOOLE-0K5 G) =MEMBEREDR8 r **MEMBER-1K22 F \\+\\XBOOLE-0K5 r **MEMBER-1K22 G"
sorry

mdef member_1_def_20 (" _ **MEMBER-1K23  _ " [164,164]164 ) where
  mlet "A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2", "a be ComplexXCMPLX-0M1"
"func a **MEMBER-1K23 A \<rightarrow> setHIDDENM2 equals
  {TARSKIK1 a} **MEMBER-1K13 A"
proof-
  (*coherence*)
    show "{TARSKIK1 a} **MEMBER-1K13 A be setHIDDENM2"
       sorry
qed "sorry"

mtheorem member_1_th_193:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds b inHIDDENR3 A implies a *XCMPLX-0K3 b inTARSKIR2 a **MEMBER-1K23 A"
sorry

mtheorem member_1_th_194:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for a be ComplexXCMPLX-0M1 holds a **MEMBER-1K23 A =XBOOLE-0R4 {a *XCMPLX-0K3 c where c be ComplexXCMPLX-0M1 : c inHIDDENR3 A }"
sorry

mtheorem member_1_th_195:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for a be ComplexXCMPLX-0M1 holds  for e be setHIDDENM2 holds e inTARSKIR2 a **MEMBER-1K23 A implies ( ex c be ComplexXCMPLX-0M1 st e =XBOOLE-0R4 a *XCMPLX-0K3 c & c inHIDDENR3 A)"
sorry

mtheorem member_1_cl_92:
  mlet "A be emptyXBOOLE-0V1\<bar>setHIDDENM2", "a be ComplexXCMPLX-0M1"
"cluster a **MEMBER-1K23 A as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "a **MEMBER-1K23 A be emptyXBOOLE-0V1"
     sorry
qed "sorry"

mtheorem member_1_cl_93:
  mlet "A be complex-memberedMEMBEREDV1\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2", "a be ComplexXCMPLX-0M1"
"cluster a **MEMBER-1K23 A as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "a **MEMBER-1K23 A be  non emptyXBOOLE-0V1"
     sorry
qed "sorry"

mtheorem member_1_cl_94:
  mlet "A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2", "a be ComplexXCMPLX-0M1"
"cluster a **MEMBER-1K23 A as-term-is complex-memberedMEMBEREDV1"
proof
(*coherence*)
  show "a **MEMBER-1K23 A be complex-memberedMEMBEREDV1"
     sorry
qed "sorry"

mtheorem member_1_cl_95:
  mlet "A be real-memberedMEMBEREDV3\<bar>setHIDDENM2", "a be RealXREAL-0M1"
"cluster a **MEMBER-1K23 A as-term-is real-memberedMEMBEREDV3"
proof
(*coherence*)
  show "a **MEMBER-1K23 A be real-memberedMEMBEREDV3"
     sorry
qed "sorry"

mtheorem member_1_cl_96:
  mlet "A be rational-memberedMEMBEREDV4\<bar>setHIDDENM2", "a be RationalRAT-1M1"
"cluster a **MEMBER-1K23 A as-term-is rational-memberedMEMBEREDV4"
proof
(*coherence*)
  show "a **MEMBER-1K23 A be rational-memberedMEMBEREDV4"
     sorry
qed "sorry"

mtheorem member_1_cl_97:
  mlet "A be integer-memberedMEMBEREDV5\<bar>setHIDDENM2", "a be IntegerINT-1M1"
"cluster a **MEMBER-1K23 A as-term-is integer-memberedMEMBEREDV5"
proof
(*coherence*)
  show "a **MEMBER-1K23 A be integer-memberedMEMBEREDV5"
     sorry
qed "sorry"

mtheorem member_1_cl_98:
  mlet "A be natural-memberedMEMBEREDV6\<bar>setHIDDENM2", "a be NatORDINAL1M6"
"cluster a **MEMBER-1K23 A as-term-is natural-memberedMEMBEREDV6"
proof
(*coherence*)
  show "a **MEMBER-1K23 A be natural-memberedMEMBEREDV6"
     sorry
qed "sorry"

mtheorem member_1_ident_10:
  mlet "A be real-memberedMEMBEREDV3\<bar>setHIDDENM2", "F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2", "a be RealXREAL-0M1", "f be ExtRealXXREAL-0M1"
"identify a **MEMBER-1K23 A with f **MEMBER-1K22 F when a =HIDDENR1 f & A =HIDDENR1 F"
proof
(*compatibility*)
  show "a =HIDDENR1 f & A =HIDDENR1 F implies a **MEMBER-1K23 A =HIDDENR1 f **MEMBER-1K22 F"
     sorry
qed "sorry"

mtheorem member_1_th_196:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for a be ComplexXCMPLX-0M1 holds a <>HIDDENR2 0NUMBERSK6 & a **MEMBER-1K23 A c=MEMBEREDR1 a **MEMBER-1K23 B implies A c=MEMBEREDR1 B"
sorry

mtheorem member_1_th_197:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for a be ComplexXCMPLX-0M1 holds a <>HIDDENR2 0NUMBERSK6 & a **MEMBER-1K23 A =MEMBEREDR7 a **MEMBER-1K23 B implies A =MEMBEREDR7 B"
sorry

mtheorem member_1_th_198:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for a be ComplexXCMPLX-0M1 holds a <>HIDDENR2 0NUMBERSK6 implies a **MEMBER-1K23 (A /\\XBOOLE-0K3 B) =MEMBEREDR7 (a **MEMBER-1K23 A)/\\XBOOLE-0K3 (a **MEMBER-1K23 B)"
sorry

mtheorem member_1_th_199:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for a be ComplexXCMPLX-0M1 holds a <>HIDDENR2 0NUMBERSK6 implies a **MEMBER-1K23 (A \\SUBSET-1K6 B) =MEMBEREDR7 a **MEMBER-1K23 A \\SUBSET-1K6 a **MEMBER-1K23 B"
sorry

mtheorem member_1_th_200:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for a be ComplexXCMPLX-0M1 holds a <>HIDDENR2 0NUMBERSK6 implies a **MEMBER-1K23 (A \\+\\XBOOLE-0K5 B) =MEMBEREDR7 a **MEMBER-1K23 A \\+\\XBOOLE-0K5 a **MEMBER-1K23 B"
sorry

mtheorem member_1_th_201:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds (0NUMBERSK6)**MEMBER-1K23 A c=MEMBEREDR1 {TARSKIK1 0NUMBERSK6 }"
sorry

mtheorem member_1_th_202:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds A <>HIDDENR2 {}XBOOLE-0K1 implies (0NUMBERSK6)**MEMBER-1K23 A =MEMBEREDR7 {TARSKIK1 0NUMBERSK6 }"
sorry

mtheorem member_1_th_203:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds \<one>\<^sub>M **MEMBER-1K23 A =MEMBEREDR7 A"
sorry

mtheorem member_1_th_204:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds (a *XCMPLX-0K3 b)**MEMBER-1K23 A =MEMBEREDR7 a **MEMBER-1K23 (b **MEMBER-1K23 A)"
sorry

mtheorem member_1_th_205:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for a be ComplexXCMPLX-0M1 holds a **MEMBER-1K23 (A **MEMBER-1K13 B) =MEMBEREDR7 (a **MEMBER-1K23 A)**MEMBER-1K13 B"
  using member_1_th_90 sorry

mtheorem member_1_th_206:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds (a +XCMPLX-0K2 b)**MEMBER-1K23 A c=MEMBEREDR1 a **MEMBER-1K23 A ++MEMBER-1K9 b **MEMBER-1K23 A"
sorry

mtheorem member_1_th_207:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds (a -XCMPLX-0K6 b)**MEMBER-1K23 A c=MEMBEREDR1 a **MEMBER-1K23 A --MEMBER-1K11 b **MEMBER-1K23 A"
sorry

mtheorem member_1_th_208:
" for B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for C be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for a be ComplexXCMPLX-0M1 holds a **MEMBER-1K23 (B ++MEMBER-1K9 C) =MEMBEREDR7 a **MEMBER-1K23 B ++MEMBER-1K9 a **MEMBER-1K23 C"
sorry

mtheorem member_1_th_209:
" for B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for C be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for a be ComplexXCMPLX-0M1 holds a **MEMBER-1K23 (B --MEMBER-1K11 C) =MEMBEREDR7 a **MEMBER-1K23 B --MEMBER-1K11 a **MEMBER-1K23 C"
sorry

mdef member_1_def_21 (" _ '/'/'/MEMBER-1K24  _ " [164,164]164 ) where
  mlet "F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2", "f be ExtRealXXREAL-0M1"
"func f ///MEMBER-1K24 F \<rightarrow> setHIDDENM2 equals
  {TARSKIK1 f} ///MEMBER-1K14 F"
proof-
  (*coherence*)
    show "{TARSKIK1 f} ///MEMBER-1K14 F be setHIDDENM2"
       sorry
qed "sorry"

mtheorem member_1_th_210:
" for G be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for f be ExtRealXXREAL-0M1 holds  for g be ExtRealXXREAL-0M1 holds g inHIDDENR3 G implies f /XXREAL-3K6 g inHIDDENR3 f ///MEMBER-1K24 G"
sorry

mtheorem member_1_th_211:
" for F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for f be ExtRealXXREAL-0M1 holds f ///MEMBER-1K24 F =XBOOLE-0R4 {f /XXREAL-3K6 w where w be ElementSUBSET-1M1-of ExtREALXXREAL-0K3 : w inTARSKIR2 F }"
sorry

mtheorem member_1_th_212:
" for F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for f be ExtRealXXREAL-0M1 holds  for e be setHIDDENM2 holds e inTARSKIR2 f ///MEMBER-1K24 F implies ( ex w be ElementSUBSET-1M1-of ExtREALXXREAL-0K3 st e =HIDDENR1 f /XXREAL-3K6 w & w inTARSKIR2 F)"
sorry

mtheorem member_1_cl_99:
  mlet "F be emptyXBOOLE-0V1\<bar>setHIDDENM2", "f be ExtRealXXREAL-0M1"
"cluster f ///MEMBER-1K24 F as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "f ///MEMBER-1K24 F be emptyXBOOLE-0V1"
     sorry
qed "sorry"

mtheorem member_1_cl_100:
  mlet "F be ext-real-memberedMEMBEREDV2\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2", "f be ExtRealXXREAL-0M1"
"cluster f ///MEMBER-1K24 F as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "f ///MEMBER-1K24 F be  non emptyXBOOLE-0V1"
     sorry
qed "sorry"

mtheorem member_1_cl_101:
  mlet "F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2", "f be ExtRealXXREAL-0M1"
"cluster f ///MEMBER-1K24 F as-term-is ext-real-memberedMEMBEREDV2"
proof
(*coherence*)
  show "f ///MEMBER-1K24 F be ext-real-memberedMEMBEREDV2"
     sorry
qed "sorry"

mdef member_1_def_22 (" _ '/'/'/MEMBER-1K25  _ " [164,164]164 ) where
  mlet "A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2", "a be ComplexXCMPLX-0M1"
"func a ///MEMBER-1K25 A \<rightarrow> setHIDDENM2 equals
  {TARSKIK1 a} ///MEMBER-1K15 A"
proof-
  (*coherence*)
    show "{TARSKIK1 a} ///MEMBER-1K15 A be setHIDDENM2"
       sorry
qed "sorry"

mtheorem member_1_th_213:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds b inHIDDENR3 A implies a /XCMPLX-0K7 b inTARSKIR2 a ///MEMBER-1K25 A"
sorry

mtheorem member_1_th_214:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for a be ComplexXCMPLX-0M1 holds a ///MEMBER-1K25 A =XBOOLE-0R4 {a /XCMPLX-0K7 c where c be ComplexXCMPLX-0M1 : c inHIDDENR3 A }"
sorry

mtheorem member_1_th_215:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for a be ComplexXCMPLX-0M1 holds  for e be setHIDDENM2 holds e inTARSKIR2 a ///MEMBER-1K25 A implies ( ex c be ComplexXCMPLX-0M1 st e =XBOOLE-0R4 a /XCMPLX-0K7 c & c inHIDDENR3 A)"
sorry

mtheorem member_1_cl_102:
  mlet "A be emptyXBOOLE-0V1\<bar>setHIDDENM2", "a be ComplexXCMPLX-0M1"
"cluster a ///MEMBER-1K25 A as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "a ///MEMBER-1K25 A be emptyXBOOLE-0V1"
     sorry
qed "sorry"

mtheorem member_1_cl_103:
  mlet "A be complex-memberedMEMBEREDV1\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2", "a be ComplexXCMPLX-0M1"
"cluster a ///MEMBER-1K25 A as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "a ///MEMBER-1K25 A be  non emptyXBOOLE-0V1"
     sorry
qed "sorry"

mtheorem member_1_cl_104:
  mlet "A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2", "a be ComplexXCMPLX-0M1"
"cluster a ///MEMBER-1K25 A as-term-is complex-memberedMEMBEREDV1"
proof
(*coherence*)
  show "a ///MEMBER-1K25 A be complex-memberedMEMBEREDV1"
     sorry
qed "sorry"

mtheorem member_1_cl_105:
  mlet "A be real-memberedMEMBEREDV3\<bar>setHIDDENM2", "a be RealXREAL-0M1"
"cluster a ///MEMBER-1K25 A as-term-is real-memberedMEMBEREDV3"
proof
(*coherence*)
  show "a ///MEMBER-1K25 A be real-memberedMEMBEREDV3"
     sorry
qed "sorry"

mtheorem member_1_cl_106:
  mlet "A be rational-memberedMEMBEREDV4\<bar>setHIDDENM2", "a be RationalRAT-1M1"
"cluster a ///MEMBER-1K25 A as-term-is rational-memberedMEMBEREDV4"
proof
(*coherence*)
  show "a ///MEMBER-1K25 A be rational-memberedMEMBEREDV4"
     sorry
qed "sorry"

mtheorem member_1_ident_11:
  mlet "A be real-memberedMEMBEREDV3\<bar>setHIDDENM2", "F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2", "a be RealXREAL-0M1", "f be ExtRealXXREAL-0M1"
"identify a ///MEMBER-1K25 A with f ///MEMBER-1K24 F when a =HIDDENR1 f & A =HIDDENR1 F"
proof
(*compatibility*)
  show "a =HIDDENR1 f & A =HIDDENR1 F implies a ///MEMBER-1K25 A =HIDDENR1 f ///MEMBER-1K24 F"
     sorry
qed "sorry"

mtheorem member_1_th_216:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for a be ComplexXCMPLX-0M1 holds a <>HIDDENR2 0NUMBERSK6 & a ///MEMBER-1K25 A c=MEMBEREDR1 a ///MEMBER-1K25 B implies A c=MEMBEREDR1 B"
sorry

mtheorem member_1_th_217:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for a be ComplexXCMPLX-0M1 holds a <>HIDDENR2 0NUMBERSK6 & a ///MEMBER-1K25 A =MEMBEREDR7 a ///MEMBER-1K25 B implies A =MEMBEREDR7 B"
sorry

mtheorem member_1_th_218:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for a be ComplexXCMPLX-0M1 holds a <>HIDDENR2 0NUMBERSK6 implies a ///MEMBER-1K25 (A /\\XBOOLE-0K3 B) =MEMBEREDR7 (a ///MEMBER-1K25 A)/\\XBOOLE-0K3 (a ///MEMBER-1K25 B)"
sorry

mtheorem member_1_th_219:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for a be ComplexXCMPLX-0M1 holds a <>HIDDENR2 0NUMBERSK6 implies a ///MEMBER-1K25 (A \\SUBSET-1K6 B) =MEMBEREDR7 a ///MEMBER-1K25 A \\SUBSET-1K6 a ///MEMBER-1K25 B"
sorry

mtheorem member_1_th_220:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for a be ComplexXCMPLX-0M1 holds a <>HIDDENR2 0NUMBERSK6 implies a ///MEMBER-1K25 (A \\+\\XBOOLE-0K5 B) =MEMBEREDR7 a ///MEMBER-1K25 A \\+\\XBOOLE-0K5 a ///MEMBER-1K25 B"
sorry

mtheorem member_1_th_221:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds (a +XCMPLX-0K2 b)///MEMBER-1K25 A c=MEMBEREDR1 a ///MEMBER-1K25 A ++MEMBER-1K9 b ///MEMBER-1K25 A"
sorry

mtheorem member_1_th_222:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds (a -XCMPLX-0K6 b)///MEMBER-1K25 A c=MEMBEREDR1 a ///MEMBER-1K25 A --MEMBER-1K11 b ///MEMBER-1K25 A"
sorry

mdef member_1_def_23 (" _ '/'/'/MEMBER-1K26  _ " [164,164]164 ) where
  mlet "F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2", "f be ExtRealXXREAL-0M1"
"func F ///MEMBER-1K26 f \<rightarrow> setHIDDENM2 equals
  F ///MEMBER-1K14 {TARSKIK1 f}"
proof-
  (*coherence*)
    show "F ///MEMBER-1K14 {TARSKIK1 f} be setHIDDENM2"
       sorry
qed "sorry"

mtheorem member_1_th_223:
" for G be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for f be ExtRealXXREAL-0M1 holds  for g be ExtRealXXREAL-0M1 holds g inHIDDENR3 G implies g /XXREAL-3K6 f inHIDDENR3 G ///MEMBER-1K26 f"
sorry

mtheorem member_1_th_224:
" for F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for f be ExtRealXXREAL-0M1 holds F ///MEMBER-1K26 f =XBOOLE-0R4 {w /XXREAL-3K6 f where w be ElementSUBSET-1M1-of ExtREALXXREAL-0K3 : w inTARSKIR2 F }"
sorry

mtheorem member_1_th_225:
" for F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for f be ExtRealXXREAL-0M1 holds  for e be setHIDDENM2 holds e inTARSKIR2 F ///MEMBER-1K26 f implies ( ex w be ElementSUBSET-1M1-of ExtREALXXREAL-0K3 st e =HIDDENR1 w /XXREAL-3K6 f & w inTARSKIR2 F)"
sorry

mtheorem member_1_cl_107:
  mlet "F be emptyXBOOLE-0V1\<bar>setHIDDENM2", "f be ExtRealXXREAL-0M1"
"cluster F ///MEMBER-1K26 f as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "F ///MEMBER-1K26 f be emptyXBOOLE-0V1"
     sorry
qed "sorry"

mtheorem member_1_cl_108:
  mlet "F be ext-real-memberedMEMBEREDV2\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2", "f be ExtRealXXREAL-0M1"
"cluster F ///MEMBER-1K26 f as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "F ///MEMBER-1K26 f be  non emptyXBOOLE-0V1"
     sorry
qed "sorry"

mtheorem member_1_cl_109:
  mlet "F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2", "f be ExtRealXXREAL-0M1"
"cluster F ///MEMBER-1K26 f as-term-is ext-real-memberedMEMBEREDV2"
proof
(*coherence*)
  show "F ///MEMBER-1K26 f be ext-real-memberedMEMBEREDV2"
     sorry
qed "sorry"

mdef member_1_def_24 (" _ '/'/'/MEMBER-1K27  _ " [164,164]164 ) where
  mlet "A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2", "a be ComplexXCMPLX-0M1"
"func A ///MEMBER-1K27 a \<rightarrow> setHIDDENM2 equals
  A ///MEMBER-1K15 {TARSKIK1 a}"
proof-
  (*coherence*)
    show "A ///MEMBER-1K15 {TARSKIK1 a} be setHIDDENM2"
       sorry
qed "sorry"

mtheorem member_1_th_226:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds b inHIDDENR3 A implies b /XCMPLX-0K7 a inTARSKIR2 A ///MEMBER-1K27 a"
sorry

mtheorem member_1_th_227:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for a be ComplexXCMPLX-0M1 holds A ///MEMBER-1K27 a =XBOOLE-0R4 {c /XCMPLX-0K7 a where c be ComplexXCMPLX-0M1 : c inHIDDENR3 A }"
sorry

mtheorem member_1_th_228:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for a be ComplexXCMPLX-0M1 holds  for e be setHIDDENM2 holds e inTARSKIR2 A ///MEMBER-1K27 a implies ( ex c be ComplexXCMPLX-0M1 st e =XBOOLE-0R4 c /XCMPLX-0K7 a & c inHIDDENR3 A)"
sorry

mtheorem member_1_cl_110:
  mlet "A be emptyXBOOLE-0V1\<bar>setHIDDENM2", "a be ComplexXCMPLX-0M1"
"cluster A ///MEMBER-1K27 a as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "A ///MEMBER-1K27 a be emptyXBOOLE-0V1"
     sorry
qed "sorry"

mtheorem member_1_cl_111:
  mlet "A be complex-memberedMEMBEREDV1\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2", "a be ComplexXCMPLX-0M1"
"cluster A ///MEMBER-1K27 a as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "A ///MEMBER-1K27 a be  non emptyXBOOLE-0V1"
     sorry
qed "sorry"

mtheorem member_1_cl_112:
  mlet "A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2", "a be ComplexXCMPLX-0M1"
"cluster A ///MEMBER-1K27 a as-term-is complex-memberedMEMBEREDV1"
proof
(*coherence*)
  show "A ///MEMBER-1K27 a be complex-memberedMEMBEREDV1"
     sorry
qed "sorry"

mtheorem member_1_cl_113:
  mlet "A be real-memberedMEMBEREDV3\<bar>setHIDDENM2", "a be RealXREAL-0M1"
"cluster A ///MEMBER-1K27 a as-term-is real-memberedMEMBEREDV3"
proof
(*coherence*)
  show "A ///MEMBER-1K27 a be real-memberedMEMBEREDV3"
     sorry
qed "sorry"

mtheorem member_1_cl_114:
  mlet "A be rational-memberedMEMBEREDV4\<bar>setHIDDENM2", "a be RationalRAT-1M1"
"cluster A ///MEMBER-1K27 a as-term-is rational-memberedMEMBEREDV4"
proof
(*coherence*)
  show "A ///MEMBER-1K27 a be rational-memberedMEMBEREDV4"
     sorry
qed "sorry"

mtheorem member_1_ident_12:
  mlet "A be real-memberedMEMBEREDV3\<bar>setHIDDENM2", "F be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2", "a be RealXREAL-0M1", "f be ExtRealXXREAL-0M1"
"identify A ///MEMBER-1K27 a with F ///MEMBER-1K26 f when a =HIDDENR1 f & A =HIDDENR1 F"
proof
(*compatibility*)
  show "a =HIDDENR1 f & A =HIDDENR1 F implies A ///MEMBER-1K27 a =HIDDENR1 F ///MEMBER-1K26 f"
     sorry
qed "sorry"

mtheorem member_1_th_229:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for a be ComplexXCMPLX-0M1 holds a <>HIDDENR2 0NUMBERSK6 & A ///MEMBER-1K27 a c=MEMBEREDR1 B ///MEMBER-1K27 a implies A c=MEMBEREDR1 B"
sorry

mtheorem member_1_th_230:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for a be ComplexXCMPLX-0M1 holds a <>HIDDENR2 0NUMBERSK6 & A ///MEMBER-1K27 a =MEMBEREDR7 B ///MEMBER-1K27 a implies A =MEMBEREDR7 B"
sorry

mtheorem member_1_th_231:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for a be ComplexXCMPLX-0M1 holds a <>HIDDENR2 0NUMBERSK6 implies (A /\\XBOOLE-0K3 B)///MEMBER-1K27 a =MEMBEREDR7 (A ///MEMBER-1K27 a)/\\XBOOLE-0K3 (B ///MEMBER-1K27 a)"
sorry

mtheorem member_1_th_232:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for a be ComplexXCMPLX-0M1 holds a <>HIDDENR2 0NUMBERSK6 implies (A \\SUBSET-1K6 B)///MEMBER-1K27 a =MEMBEREDR7 A ///MEMBER-1K27 a \\SUBSET-1K6 B ///MEMBER-1K27 a"
sorry

mtheorem member_1_th_233:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for a be ComplexXCMPLX-0M1 holds a <>HIDDENR2 0NUMBERSK6 implies (A \\+\\XBOOLE-0K5 B)///MEMBER-1K27 a =MEMBEREDR7 A ///MEMBER-1K27 a \\+\\XBOOLE-0K5 B ///MEMBER-1K27 a"
sorry

mtheorem member_1_th_234:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for a be ComplexXCMPLX-0M1 holds (A ++MEMBER-1K9 B)///MEMBER-1K27 a =MEMBEREDR7 A ///MEMBER-1K27 a ++MEMBER-1K9 B ///MEMBER-1K27 a"
sorry

mtheorem member_1_th_235:
" for A be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for B be complex-memberedMEMBEREDV1\<bar>setHIDDENM2 holds  for a be ComplexXCMPLX-0M1 holds (A --MEMBER-1K11 B)///MEMBER-1K27 a =MEMBEREDR7 A ///MEMBER-1K27 a --MEMBER-1K11 B ///MEMBER-1K27 a"
sorry

end
