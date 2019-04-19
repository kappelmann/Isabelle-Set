theory int_2
  imports absvalue card_1
   "../mizar_extension/E_number"
begin
(*begin*)
abbreviation(input) INT_2K1("|.INT-2K1  _ .|" [0]164) where
  "|.INT-2K1 a.| \<equiv> |.COMPLEX1K10 a.|"

mtheorem int_2_add_1:
  mlet "a be IntegerINT-1M1"
"cluster |.COMPLEX1K10 a.| as-term-is ElementSUBSET-1M1-of NATNUMBERSK1"
proof
(*coherence*)
  show "|.COMPLEX1K10 a.| be ElementSUBSET-1M1-of NATNUMBERSK1"
sorry
qed "sorry"

reserve a, b, c for "IntegerINT-1M1"
mtheorem int_2_th_1:
" for a be IntegerINT-1M1 holds  for b be IntegerINT-1M1 holds  for c be IntegerINT-1M1 holds a dividesINT-1R1 b & a dividesINT-1R1 b +XCMPLX-0K2 c implies a dividesINT-1R1 c"
sorry

mtheorem int_2_th_2:
" for a be IntegerINT-1M1 holds  for b be IntegerINT-1M1 holds  for c be IntegerINT-1M1 holds a dividesINT-1R1 b implies a dividesINT-1R1 b *XCMPLX-0K3 c"
sorry

mtheorem int_2_th_3:
" for a be IntegerINT-1M1 holds 0NUMBERSK6 dividesINT-1R1 a iff a =COMPLEX1R1 0NUMBERSK6"
   sorry

mlemma int_2_lm_1:
" for a be IntegerINT-1M1 holds a dividesINT-1R1 -XCMPLX-0K4 a & -XCMPLX-0K4 a dividesINT-1R1 a"
sorry

mlemma int_2_lm_2:
" for a be IntegerINT-1M1 holds  for b be IntegerINT-1M1 holds  for c be IntegerINT-1M1 holds a dividesINT-1R1 b & b dividesINT-1R1 c implies a dividesINT-1R1 c"
sorry

mlemma int_2_lm_3:
" for a be IntegerINT-1M1 holds  for b be IntegerINT-1M1 holds a dividesINT-1R1 b iff a dividesINT-1R1 -XCMPLX-0K4 b"
sorry

mlemma int_2_lm_4:
" for a be IntegerINT-1M1 holds  for b be IntegerINT-1M1 holds a dividesINT-1R1 b iff -XCMPLX-0K4 a dividesINT-1R1 b"
sorry

mlemma int_2_lm_5:
" for a be IntegerINT-1M1 holds (a dividesINT-1R1 0NUMBERSK6 & \<one>\<^sub>M dividesINT-1R1 a) & -XCMPLX-0K4 \<one>\<^sub>M dividesINT-1R1 a"
sorry

mlemma int_2_lm_6:
" for a be IntegerINT-1M1 holds  for b be IntegerINT-1M1 holds  for c be IntegerINT-1M1 holds a dividesINT-1R1 b & a dividesINT-1R1 c implies a dividesINT-1R1 b modINT-1K6 c"
sorry

reserve i, j, k, l for "NatNAT-1M1"
mlemma int_2_lm_7:
" for k be NatNAT-1M1 holds  for l be NatNAT-1M1 holds k dividesINT-1R1 l iff ( ex t be NatNAT-1M1 st l =COMPLEX1R1 k *XCMPLX-0K3 t)"
sorry

mlemma int_2_lm_8:
" for i be NatNAT-1M1 holds  for j be NatNAT-1M1 holds i dividesINT-1R1 j & j dividesINT-1R1 i implies i =COMPLEX1R1 j"
sorry

mdef int_2_def_1 (" _ lcmINT-2K2  _ " [132,132]132 ) where
  mlet "a be IntegerINT-1M1", "b be IntegerINT-1M1"
"func a lcmINT-2K2 b \<rightarrow> NatNAT-1M1 means
  \<lambda>it. (a dividesINT-1R1 it & b dividesINT-1R1 it) & ( for m be IntegerINT-1M1 holds a dividesINT-1R1 m & b dividesINT-1R1 m implies it dividesINT-1R1 m)"
proof-
  (*existence*)
    show " ex it be NatNAT-1M1 st (a dividesINT-1R1 it & b dividesINT-1R1 it) & ( for m be IntegerINT-1M1 holds a dividesINT-1R1 m & b dividesINT-1R1 m implies it dividesINT-1R1 m)"
sorry
  (*uniqueness*)
    show " for it1 be NatNAT-1M1 holds  for it2 be NatNAT-1M1 holds ((a dividesINT-1R1 it1 & b dividesINT-1R1 it1) & ( for m be IntegerINT-1M1 holds a dividesINT-1R1 m & b dividesINT-1R1 m implies it1 dividesINT-1R1 m)) & ((a dividesINT-1R1 it2 & b dividesINT-1R1 it2) & ( for m be IntegerINT-1M1 holds a dividesINT-1R1 m & b dividesINT-1R1 m implies it2 dividesINT-1R1 m)) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mtheorem INT_2K2_commutativity:
" for a be IntegerINT-1M1 holds  for b be IntegerINT-1M1 holds a lcmINT-2K2 b =HIDDENR1 b lcmINT-2K2 a"
sorry

mtheorem int_2_th_4:
" for a be IntegerINT-1M1 holds  for b be IntegerINT-1M1 holds a =COMPLEX1R1 0NUMBERSK6 or b =COMPLEX1R1 0NUMBERSK6 iff a lcmINT-2K2 b =COMPLEX1R1 0NUMBERSK6"
sorry

mlemma int_2_lm_9:
" for i be NatNAT-1M1 holds  for j be NatNAT-1M1 holds 0NUMBERSK6 <XXREAL-0R3 j & i dividesINT-1R1 j implies i <=XXREAL-0R1 j"
sorry

mdef int_2_def_2 (" _ gcdINT-2K3  _ " [132,132]132 ) where
  mlet "a be IntegerINT-1M1", "b be IntegerINT-1M1"
"func a gcdINT-2K3 b \<rightarrow> NatNAT-1M1 means
  \<lambda>it. (it dividesINT-1R1 a & it dividesINT-1R1 b) & ( for m be IntegerINT-1M1 holds m dividesINT-1R1 a & m dividesINT-1R1 b implies m dividesINT-1R1 it)"
proof-
  (*existence*)
    show " ex it be NatNAT-1M1 st (it dividesINT-1R1 a & it dividesINT-1R1 b) & ( for m be IntegerINT-1M1 holds m dividesINT-1R1 a & m dividesINT-1R1 b implies m dividesINT-1R1 it)"
sorry
  (*uniqueness*)
    show " for it1 be NatNAT-1M1 holds  for it2 be NatNAT-1M1 holds ((it1 dividesINT-1R1 a & it1 dividesINT-1R1 b) & ( for m be IntegerINT-1M1 holds m dividesINT-1R1 a & m dividesINT-1R1 b implies m dividesINT-1R1 it1)) & ((it2 dividesINT-1R1 a & it2 dividesINT-1R1 b) & ( for m be IntegerINT-1M1 holds m dividesINT-1R1 a & m dividesINT-1R1 b implies m dividesINT-1R1 it2)) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mtheorem INT_2K3_commutativity:
" for a be IntegerINT-1M1 holds  for b be IntegerINT-1M1 holds a gcdINT-2K3 b =HIDDENR1 b gcdINT-2K3 a"
sorry

mtheorem int_2_th_5:
" for a be IntegerINT-1M1 holds  for b be IntegerINT-1M1 holds a =COMPLEX1R1 0NUMBERSK6 & b =COMPLEX1R1 0NUMBERSK6 iff a gcdINT-2K3 b =COMPLEX1R1 0NUMBERSK6"
sorry

reserve n for "NatNAT-1M1"
reserve a, b, c, d, a1, b1, a2, b2, k, l for "IntegerINT-1M1"
mtheorem int_2_th_6:
" for n be NatNAT-1M1 holds -XCMPLX-0K4 n be ElementSUBSET-1M1-of NATNUMBERSK1 iff n =COMPLEX1R1 0NUMBERSK6"
sorry

mtheorem int_2_cl_1:
  mlet "n be  non zeroORDINAL1V8\<bar>NatNAT-1M1"
"cluster -XCMPLX-0K4 n as-term-is  non naturalORDINAL1V7"
proof
(*coherence*)
  show "-XCMPLX-0K4 n be  non naturalORDINAL1V7"
sorry
qed "sorry"

mtheorem int_2_th_7:
" not -XCMPLX-0K4 \<one>\<^sub>M be ElementSUBSET-1M1-of NATNUMBERSK1"
   sorry

mtheorem int_2_th_8:
" for a be IntegerINT-1M1 holds a dividesINT-1R1 -XCMPLX-0K4 a & -XCMPLX-0K4 a dividesINT-1R1 a"
  using int_2_lm_1 sorry

mtheorem int_2_th_9:
" for a be IntegerINT-1M1 holds  for b be IntegerINT-1M1 holds  for c be IntegerINT-1M1 holds a dividesINT-1R1 b & b dividesINT-1R1 c implies a dividesINT-1R1 c"
  using int_2_lm_2 sorry

mtheorem int_2_th_10:
" for a be IntegerINT-1M1 holds  for b be IntegerINT-1M1 holds (((a dividesINT-1R1 b iff a dividesINT-1R1 -XCMPLX-0K4 b) & (a dividesINT-1R1 b iff -XCMPLX-0K4 a dividesINT-1R1 b)) & (a dividesINT-1R1 b iff -XCMPLX-0K4 a dividesINT-1R1 -XCMPLX-0K4 b)) & (a dividesINT-1R1 -XCMPLX-0K4 b iff -XCMPLX-0K4 a dividesINT-1R1 b)"
sorry

mtheorem int_2_th_11:
" for a be IntegerINT-1M1 holds  for b be IntegerINT-1M1 holds a dividesINT-1R1 b & b dividesINT-1R1 a implies a =COMPLEX1R1 b or a =COMPLEX1R1 -XCMPLX-0K4 b"
sorry

mtheorem int_2_th_12:
" for a be IntegerINT-1M1 holds (a dividesINT-1R1 0NUMBERSK6 & \<one>\<^sub>M dividesINT-1R1 a) & -XCMPLX-0K4 \<one>\<^sub>M dividesINT-1R1 a"
  using int_2_lm_5 sorry

mtheorem int_2_th_13:
" for a be IntegerINT-1M1 holds a dividesINT-1R1 \<one>\<^sub>M or a dividesINT-1R1 -XCMPLX-0K4 \<one>\<^sub>M implies a =COMPLEX1R1 \<one>\<^sub>M or a =COMPLEX1R1 -XCMPLX-0K4 \<one>\<^sub>M"
  using int_1_th_9 int_1_th_10 sorry

mtheorem int_2_th_14:
" for a be IntegerINT-1M1 holds a =COMPLEX1R1 \<one>\<^sub>M or a =COMPLEX1R1 -XCMPLX-0K4 \<one>\<^sub>M implies a dividesINT-1R1 \<one>\<^sub>M & a dividesINT-1R1 -XCMPLX-0K4 \<one>\<^sub>M"
  using int_2_lm_5 sorry

mtheorem int_2_th_15:
" for a be IntegerINT-1M1 holds  for b be IntegerINT-1M1 holds  for c be IntegerINT-1M1 holds (a,b)are-congruent-modINT-1R3 c iff c dividesINT-1R1 a -XCMPLX-0K6 b"
   sorry

mtheorem int_2_th_16:
" for a be IntegerINT-1M1 holds  for b be IntegerINT-1M1 holds a dividesINT-1R1 b iff |.INT-2K1 a.| dividesINT-1R1 |.INT-2K1 b.|"
sorry

mtheorem int_2_th_17:
" for a be IntegerINT-1M1 holds  for b be IntegerINT-1M1 holds a lcmINT-2K2 b be ElementSUBSET-1M1-of NATNUMBERSK1"
  using ordinal1_def_12 sorry

mtheorem int_2_th_18:
" for a be IntegerINT-1M1 holds  for b be IntegerINT-1M1 holds a dividesINT-1R1 a lcmINT-2K2 b"
  using int_2_def_1 sorry

mtheorem int_2_th_19:
" for a be IntegerINT-1M1 holds  for b be IntegerINT-1M1 holds  for c be IntegerINT-1M1 holds a dividesINT-1R1 c & b dividesINT-1R1 c implies a lcmINT-2K2 b dividesINT-1R1 c"
  using int_2_def_1 sorry

mtheorem int_2_th_20:
" for a be IntegerINT-1M1 holds  for b be IntegerINT-1M1 holds a gcdINT-2K3 b be ElementSUBSET-1M1-of NATNUMBERSK1"
  using ordinal1_def_12 sorry

mtheorem int_2_th_21:
" for a be IntegerINT-1M1 holds  for b be IntegerINT-1M1 holds a gcdINT-2K3 b dividesINT-1R1 a"
  using int_2_def_2 sorry

mtheorem int_2_th_22:
" for a be IntegerINT-1M1 holds  for b be IntegerINT-1M1 holds  for c be IntegerINT-1M1 holds c dividesINT-1R1 a & c dividesINT-1R1 b implies c dividesINT-1R1 a gcdINT-2K3 b"
  using int_2_def_2 sorry

mdef int_2_def_3 ("'( _ , _ ')are-coprimeINT-2R1" [0,0]50 ) where
  mlet "a be IntegerINT-1M1", "b be IntegerINT-1M1"
"pred (a,b)are-coprimeINT-2R1 means
  a gcdINT-2K3 b =COMPLEX1R1 \<one>\<^sub>M"..

mtheorem INT_2R1_symmetry:
" for a be IntegerINT-1M1 holds  for b be IntegerINT-1M1 holds (a,b)are-coprimeINT-2R1 implies (b,a)are-coprimeINT-2R1"
sorry

mtheorem int_2_th_23:
" for a be IntegerINT-1M1 holds  for b be IntegerINT-1M1 holds a <>HIDDENR2 0NUMBERSK6 or b <>HIDDENR2 0NUMBERSK6 implies ( ex a1 be IntegerINT-1M1 st  ex b1 be IntegerINT-1M1 st (a =COMPLEX1R1 (a gcdINT-2K3 b)*XCMPLX-0K3 a1 & b =COMPLEX1R1 (a gcdINT-2K3 b)*XCMPLX-0K3 b1) & (a1,b1)are-coprimeINT-2R1)"
sorry

mtheorem int_2_th_24:
" for a be IntegerINT-1M1 holds  for b be IntegerINT-1M1 holds  for c be IntegerINT-1M1 holds (a,b)are-coprimeINT-2R1 implies ((c *XCMPLX-0K3 a gcdINT-2K3 c *XCMPLX-0K3 b =COMPLEX1R1 |.INT-2K1 c.| & c *XCMPLX-0K3 a gcdINT-2K3 b *XCMPLX-0K3 c =COMPLEX1R1 |.INT-2K1 c.|) & a *XCMPLX-0K3 c gcdINT-2K3 c *XCMPLX-0K3 b =COMPLEX1R1 |.INT-2K1 c.|) & a *XCMPLX-0K3 c gcdINT-2K3 b *XCMPLX-0K3 c =COMPLEX1R1 |.INT-2K1 c.|"
sorry

mtheorem int_2_th_25:
" for a be IntegerINT-1M1 holds  for b be IntegerINT-1M1 holds  for c be IntegerINT-1M1 holds c dividesINT-1R1 a *XCMPLX-0K3 b & (a,c)are-coprimeINT-2R1 implies c dividesINT-1R1 b"
sorry

mtheorem int_2_th_26:
" for a be IntegerINT-1M1 holds  for b be IntegerINT-1M1 holds  for c be IntegerINT-1M1 holds (a,c)are-coprimeINT-2R1 & (b,c)are-coprimeINT-2R1 implies (a *XCMPLX-0K3 b,c)are-coprimeINT-2R1"
sorry

reserve p, p1, q, l for "NatNAT-1M1"
mdef int_2_def_4 ("primeINT-2V1" 70 ) where
"attr primeINT-2V1 for integerINT-1V1\<bar>NumberORDINAL1M1 means
  (\<lambda>p. p >XXREAL-0R4 \<one>\<^sub>M & ( for n be NatNAT-1M1 holds n dividesINT-1R1 p implies n =COMPLEX1R1 \<one>\<^sub>M or n =COMPLEX1R1 p))"..

mtheorem int_2_cl_2:
"cluster primeINT-2V1 also-is naturalORDINAL1V7 for integerINT-1V1\<bar>NumberORDINAL1M1"
proof
(*coherence*)
  show " for it be integerINT-1V1\<bar>NumberORDINAL1M1 holds it be primeINT-2V1 implies it be naturalORDINAL1V7"
sorry
qed "sorry"

mtheorem int_2_th_27:
" for a be IntegerINT-1M1 holds  for b be IntegerINT-1M1 holds 0NUMBERSK6 <XXREAL-0R3 b & a dividesINT-1R1 b implies a <=XXREAL-0R1 b"
sorry

mtheorem int_2_th_28:
"\<two>\<^sub>M be primeINT-2V1"
sorry

mtheorem int_2_th_29:
" not \<four>\<^sub>M be primeINT-2V1"
sorry

mtheorem int_2_cl_3:
"cluster primeINT-2V1 for NatNAT-1M1"
proof
(*existence*)
  show " ex it be NatNAT-1M1 st it be primeINT-2V1"
    using int_2_th_28 sorry
qed "sorry"

mtheorem int_2_cl_4:
"cluster  non zeroORDINAL1V8\<bar> non primeINT-2V1 for NatNAT-1M1"
proof
(*existence*)
  show " ex it be NatNAT-1M1 st it be  non zeroORDINAL1V8\<bar> non primeINT-2V1"
    using int_2_th_29 sorry
qed "sorry"

mtheorem int_2_th_30:
" for p be NatNAT-1M1 holds  for q be NatNAT-1M1 holds p be primeINT-2V1 & q be primeINT-2V1 implies (p,q)are-coprimeINT-2R1 or p =COMPLEX1R1 q"
sorry

mtheorem int_2_th_31:
" for l be NatNAT-1M1 holds l >=XXREAL-0R2 \<two>\<^sub>M implies ( ex p be ElementSUBSET-1M1-of NATNUMBERSK1 st p be primeINT-2V1 & p dividesINT-1R1 l)"
sorry

(*begin*)
mtheorem int_2_th_32:
" for i be IntegerINT-1M1 holds  for j be IntegerINT-1M1 holds i >=XXREAL-0R2 0NUMBERSK6 & j >=XXREAL-0R2 0NUMBERSK6 implies |.INT-2K1 i.| modINT-1K6 |.INT-2K1 j.| =COMPLEX1R1 i modINT-1K6 j & |.INT-2K1 i.| divINT-1K5 |.INT-2K1 j.| =COMPLEX1R1 i divINT-1K5 j"
sorry

mtheorem int_2_th_33:
" for a be IntegerINT-1M1 holds  for b be IntegerINT-1M1 holds a lcmINT-2K2 b =COMPLEX1R1 |.INT-2K1 a.| lcmINT-2K2 |.INT-2K1 b.|"
sorry

mtheorem int_2_th_34:
" for a be IntegerINT-1M1 holds  for b be IntegerINT-1M1 holds a gcdINT-2K3 b =COMPLEX1R1 |.INT-2K1 a.| gcdINT-2K3 |.INT-2K1 b.|"
sorry

end
