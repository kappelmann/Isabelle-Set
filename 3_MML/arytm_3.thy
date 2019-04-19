theory arytm_3
  imports ordinal3
   "../mizar_extension/E_number"
begin
(*begin*)
reserve A, B, C for "OrdinalORDINAL1M3"
mlemma arytm_3_lm_1:
"{}XBOOLE-0K1 inTARSKIR2 omegaORDINAL1K4"
  using ordinal1_def_11 sorry

mlemma arytm_3_lm_2:
"\<one>\<^sub>M inTARSKIR2 omegaORDINAL1K4"
   sorry

mdef arytm_3_def_1 ("oneARYTM-3K1" 228 ) where
"func oneARYTM-3K1 \<rightarrow> setHIDDENM2 equals
  \<one>\<^sub>M"
proof-
  (*coherence*)
    show "\<one>\<^sub>M be setHIDDENM2"
       sorry
qed "sorry"

(*begin*)
mdef arytm_3_def_2 ("'( _ , _ ')are-coprimeARYTM-3R1" [0,0]50 ) where
  mlet "a be OrdinalORDINAL1M3", "b be OrdinalORDINAL1M3"
"pred (a,b)are-coprimeARYTM-3R1 means
   for c be OrdinalORDINAL1M3 holds  for d1 be OrdinalORDINAL1M3 holds  for d2 be OrdinalORDINAL1M3 holds a =XBOOLE-0R4 c *^ORDINAL2K11 d1 & b =XBOOLE-0R4 c *^ORDINAL2K11 d2 implies c =XBOOLE-0R4 \<one>\<^sub>M"..

mtheorem ARYTM_3R1_symmetry:
" for a be OrdinalORDINAL1M3 holds  for b be OrdinalORDINAL1M3 holds (a,b)are-coprimeARYTM-3R1 implies (b,a)are-coprimeARYTM-3R1"
sorry

mtheorem arytm_3_th_1:
" not ({}XBOOLE-0K1,{}XBOOLE-0K1)are-coprimeARYTM-3R1"
sorry

mtheorem arytm_3_th_2:
" for A be OrdinalORDINAL1M3 holds (\<one>\<^sub>M,A)are-coprimeARYTM-3R1"
  using ordinal3_th_37 sorry

mtheorem arytm_3_th_3:
" for A be OrdinalORDINAL1M3 holds ({}XBOOLE-0K1,A)are-coprimeARYTM-3R1 implies A =XBOOLE-0R4 \<one>\<^sub>M"
sorry

reserve a, b, c, d for "naturalORDINAL1V7\<bar>OrdinalORDINAL1M3"
mtheorem arytm_3_th_4:
" for a be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 holds  for b be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 holds a <>HIDDENR2 {}XBOOLE-0K1 or b <>HIDDENR2 {}XBOOLE-0K1 implies ( ex c be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 st  ex d1 be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 st  ex d2 be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 st ((d1,d2)are-coprimeARYTM-3R1 & a =XBOOLE-0R4 c *^ORDINAL3K9 d1) & b =XBOOLE-0R4 c *^ORDINAL3K9 d2)"
sorry

reserve l, m, n for "naturalORDINAL1V7\<bar>OrdinalORDINAL1M3"
mtheorem arytm_3_cl_1:
  mlet "m be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3", "n be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3"
"cluster m div^ORDINAL3K6 n as-term-is naturalORDINAL1V7"
proof
(*coherence*)
  show "m div^ORDINAL3K6 n be naturalORDINAL1V7"
sorry
qed "sorry"

mtheorem arytm_3_cl_2:
  mlet "m be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3", "n be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3"
"cluster m mod^ORDINAL3K7 n as-term-is naturalORDINAL1V7"
proof
(*coherence*)
  show "m mod^ORDINAL3K7 n be naturalORDINAL1V7"
sorry
qed "sorry"

mdef arytm_3_def_3 (" _ dividesARYTM-3R2  _ " [50,50]50 ) where
  mlet "k be OrdinalORDINAL1M3", "n be OrdinalORDINAL1M3"
"pred k dividesARYTM-3R2 n means
   ex a be OrdinalORDINAL1M3 st n =XBOOLE-0R4 k *^ORDINAL2K11 a"..

mtheorem ARYTM_3R2_reflexivity:
" for n be OrdinalORDINAL1M3 holds n dividesARYTM-3R2 n"
sorry

mtheorem arytm_3_th_5:
" for a be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 holds  for b be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 holds a dividesARYTM-3R2 b iff ( ex c be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 st b =XBOOLE-0R4 a *^ORDINAL3K9 c)"
sorry

mtheorem arytm_3_th_6:
" for m be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 holds  for n be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 holds {}XBOOLE-0K1 inTARSKIR2 m implies n mod^ORDINAL3K7 m inTARSKIR2 m"
sorry

mtheorem arytm_3_th_7:
" for n be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 holds  for m be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 holds m dividesARYTM-3R2 n iff n =XBOOLE-0R4 m *^ORDINAL3K9 (n div^ORDINAL3K6 m)"
sorry

mtheorem arytm_3_th_8:
" for n be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 holds  for m be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 holds n dividesARYTM-3R2 m & m dividesARYTM-3R2 n implies n =XBOOLE-0R4 m"
sorry

mtheorem arytm_3_th_9:
" for n be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 holds n dividesARYTM-3R2 {}XBOOLE-0K1 & \<one>\<^sub>M dividesARYTM-3R2 n"
sorry

mtheorem arytm_3_th_10:
" for n be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 holds  for m be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 holds {}XBOOLE-0K1 inTARSKIR2 m & n dividesARYTM-3R2 m implies n c=ORDINAL1R1 m"
sorry

mtheorem arytm_3_th_11:
" for n be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 holds  for m be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 holds  for l be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 holds n dividesARYTM-3R2 m & n dividesARYTM-3R2 m +^ORDINAL3K8 l implies n dividesARYTM-3R2 l"
sorry

mlemma arytm_3_lm_3:
"\<one>\<^sub>M =XBOOLE-0R4 succORDINAL1K1 (0ORDINAL1K5)"
   sorry

mdef arytm_3_def_4 (" _ lcmARYTM-3K2  _ " [132,132]132 ) where
  mlet "k be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3", "n be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3"
"func k lcmARYTM-3K2 n \<rightarrow> ElementSUBSET-1M1-of omegaORDINAL1K4 means
  \<lambda>it. (k dividesARYTM-3R2 it & n dividesARYTM-3R2 it) & ( for m be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 holds k dividesARYTM-3R2 m & n dividesARYTM-3R2 m implies it dividesARYTM-3R2 m)"
proof-
  (*existence*)
    show " ex it be ElementSUBSET-1M1-of omegaORDINAL1K4 st (k dividesARYTM-3R2 it & n dividesARYTM-3R2 it) & ( for m be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 holds k dividesARYTM-3R2 m & n dividesARYTM-3R2 m implies it dividesARYTM-3R2 m)"
sorry
  (*uniqueness*)
    show " for it1 be ElementSUBSET-1M1-of omegaORDINAL1K4 holds  for it2 be ElementSUBSET-1M1-of omegaORDINAL1K4 holds ((k dividesARYTM-3R2 it1 & n dividesARYTM-3R2 it1) & ( for m be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 holds k dividesARYTM-3R2 m & n dividesARYTM-3R2 m implies it1 dividesARYTM-3R2 m)) & ((k dividesARYTM-3R2 it2 & n dividesARYTM-3R2 it2) & ( for m be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 holds k dividesARYTM-3R2 m & n dividesARYTM-3R2 m implies it2 dividesARYTM-3R2 m)) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mtheorem ARYTM_3K2_commutativity:
" for k be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 holds  for n be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 holds k lcmARYTM-3K2 n =HIDDENR1 n lcmARYTM-3K2 k"
sorry

mtheorem arytm_3_th_12:
" for m be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 holds  for n be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 holds m lcmARYTM-3K2 n dividesARYTM-3R2 m *^ORDINAL3K9 n"
sorry

mtheorem arytm_3_th_13:
" for m be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 holds  for n be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 holds n <>HIDDENR2 {}XBOOLE-0K1 implies m *^ORDINAL3K9 n div^ORDINAL3K6 (m lcmARYTM-3K2 n) dividesARYTM-3R2 m"
sorry

mdef arytm_3_def_5 (" _ hcfARYTM-3K3  _ " [132,132]132 ) where
  mlet "k be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3", "n be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3"
"func k hcfARYTM-3K3 n \<rightarrow> ElementSUBSET-1M1-of omegaORDINAL1K4 means
  \<lambda>it. (it dividesARYTM-3R2 k & it dividesARYTM-3R2 n) & ( for m be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 holds m dividesARYTM-3R2 k & m dividesARYTM-3R2 n implies m dividesARYTM-3R2 it)"
proof-
  (*existence*)
    show " ex it be ElementSUBSET-1M1-of omegaORDINAL1K4 st (it dividesARYTM-3R2 k & it dividesARYTM-3R2 n) & ( for m be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 holds m dividesARYTM-3R2 k & m dividesARYTM-3R2 n implies m dividesARYTM-3R2 it)"
sorry
  (*uniqueness*)
    show " for it1 be ElementSUBSET-1M1-of omegaORDINAL1K4 holds  for it2 be ElementSUBSET-1M1-of omegaORDINAL1K4 holds ((it1 dividesARYTM-3R2 k & it1 dividesARYTM-3R2 n) & ( for m be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 holds m dividesARYTM-3R2 k & m dividesARYTM-3R2 n implies m dividesARYTM-3R2 it1)) & ((it2 dividesARYTM-3R2 k & it2 dividesARYTM-3R2 n) & ( for m be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 holds m dividesARYTM-3R2 k & m dividesARYTM-3R2 n implies m dividesARYTM-3R2 it2)) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mtheorem ARYTM_3K3_commutativity:
" for k be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 holds  for n be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 holds k hcfARYTM-3K3 n =HIDDENR1 n hcfARYTM-3K3 k"
sorry

mtheorem arytm_3_th_14:
" for a be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 holds a hcfARYTM-3K3 {}XBOOLE-0K1 =XBOOLE-0R4 a & a lcmARYTM-3K2 {}XBOOLE-0K1 =XBOOLE-0R4 {}XBOOLE-0K1"
sorry

mtheorem arytm_3_th_15:
" for a be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 holds  for b be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 holds a hcfARYTM-3K3 b =XBOOLE-0R4 {}XBOOLE-0K1 implies a =XBOOLE-0R4 {}XBOOLE-0K1"
sorry

mtheorem arytm_3_th_16:
" for a be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 holds a hcfARYTM-3K3 a =XBOOLE-0R4 a & a lcmARYTM-3K2 a =XBOOLE-0R4 a"
sorry

mtheorem arytm_3_th_17:
" for a be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 holds  for b be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 holds  for c be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 holds a *^ORDINAL3K9 c hcfARYTM-3K3 b *^ORDINAL3K9 c =XBOOLE-0R4 (a hcfARYTM-3K3 b)*^ORDINAL3K9 c"
sorry

mtheorem arytm_3_th_18:
" for a be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 holds  for b be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 holds b <>HIDDENR2 {}XBOOLE-0K1 implies a hcfARYTM-3K3 b <>HIDDENR2 {}XBOOLE-0K1 & b div^ORDINAL3K6 (a hcfARYTM-3K3 b) <>HIDDENR2 {}XBOOLE-0K1"
sorry

mtheorem arytm_3_th_19:
" for a be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 holds  for b be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 holds a <>HIDDENR2 {}XBOOLE-0K1 or b <>HIDDENR2 {}XBOOLE-0K1 implies (a div^ORDINAL3K6 (a hcfARYTM-3K3 b),b div^ORDINAL3K6 (a hcfARYTM-3K3 b))are-coprimeARYTM-3R1"
sorry

mlemma arytm_3_lm_4:
"0ORDINAL1K5 =XBOOLE-0R4 {}XBOOLE-0K1"
   sorry

mtheorem arytm_3_th_20:
" for a be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 holds  for b be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 holds (a,b)are-coprimeARYTM-3R1 iff a hcfARYTM-3K3 b =XBOOLE-0R4 \<one>\<^sub>M"
sorry

mdef arytm_3_def_6 ("REDARYTM-3K4'( _ , _ ')" [0,0]164 ) where
  mlet "a be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3", "b be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3"
"func REDARYTM-3K4(a,b) \<rightarrow> ElementSUBSET-1M1-of omegaORDINAL1K4 equals
  a div^ORDINAL3K6 (a hcfARYTM-3K3 b)"
proof-
  (*coherence*)
    show "a div^ORDINAL3K6 (a hcfARYTM-3K3 b) be ElementSUBSET-1M1-of omegaORDINAL1K4"
      using ordinal1_def_12 sorry
qed "sorry"

mtheorem arytm_3_th_21:
" for a be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 holds  for b be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 holds (REDARYTM-3K4(a,b))*^ORDINAL3K9 (a hcfARYTM-3K3 b) =XBOOLE-0R4 a"
sorry

mtheorem arytm_3_th_22:
" for a be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 holds  for b be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 holds a <>HIDDENR2 {}XBOOLE-0K1 or b <>HIDDENR2 {}XBOOLE-0K1 implies (REDARYTM-3K4(a,b),REDARYTM-3K4(b,a))are-coprimeARYTM-3R1"
  using arytm_3_th_19 sorry

mtheorem arytm_3_th_23:
" for a be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 holds  for b be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 holds (a,b)are-coprimeARYTM-3R1 implies REDARYTM-3K4(a,b) =XBOOLE-0R4 a"
sorry

mtheorem arytm_3_th_24:
" for a be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 holds REDARYTM-3K4(a,\<one>\<^sub>M) =XBOOLE-0R4 a & REDARYTM-3K4(\<one>\<^sub>M,a) =XBOOLE-0R4 \<one>\<^sub>M"
sorry

mtheorem arytm_3_th_25:
" for a be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 holds  for b be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 holds b <>HIDDENR2 {}XBOOLE-0K1 implies REDARYTM-3K4(b,a) <>HIDDENR2 {}XBOOLE-0K1"
  using arytm_3_th_18 sorry

mtheorem arytm_3_th_26:
" for a be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 holds REDARYTM-3K4({}XBOOLE-0K1,a) =XBOOLE-0R4 {}XBOOLE-0K1 & (a <>HIDDENR2 {}XBOOLE-0K1 implies REDARYTM-3K4(a,{}XBOOLE-0K1) =XBOOLE-0R4 \<one>\<^sub>M)"
sorry

mtheorem arytm_3_th_27:
" for a be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 holds a <>HIDDENR2 {}XBOOLE-0K1 implies REDARYTM-3K4(a,a) =XBOOLE-0R4 \<one>\<^sub>M"
sorry

mtheorem arytm_3_th_28:
" for a be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 holds  for b be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 holds  for c be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 holds c <>HIDDENR2 {}XBOOLE-0K1 implies REDARYTM-3K4(a *^ORDINAL3K9 c,b *^ORDINAL3K9 c) =XBOOLE-0R4 REDARYTM-3K4(a,b)"
sorry

mlemma arytm_3_lm_5:
" for a be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 holds  for b be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 holds [TARSKIK4 a,b ] inHIDDENR3 {[TARSKIK4 a,b ] where a be ElementSUBSET-1M1-of omegaORDINAL1K4, b be ElementSUBSET-1M1-of omegaORDINAL1K4 : (a,b)are-coprimeARYTM-3R1 & b <>HIDDENR2 {}XBOOLE-0K1 } implies (a,b)are-coprimeARYTM-3R1 & b <>HIDDENR2 {}XBOOLE-0K1"
sorry

(*begin*)
reserve i, j, k for "ElementSUBSET-1M1-of omegaORDINAL1K4"
mdef arytm_3_def_7 ("RAT+ARYTM-3K5" 164 ) where
"func RAT+ARYTM-3K5 \<rightarrow> setHIDDENM2 equals
  (({[TARSKIK4 i,j ] where i be ElementSUBSET-1M1-of omegaORDINAL1K4, j be ElementSUBSET-1M1-of omegaORDINAL1K4 : (i,j)are-coprimeARYTM-3R1 & j <>HIDDENR2 {}XBOOLE-0K1 })\\SUBSET-1K6 ({[TARSKIK4 k,\<one>\<^sub>M ] where k be ElementSUBSET-1M1-of omegaORDINAL1K4 :  True  }))\\/XBOOLE-0K2 omegaORDINAL1K4"
proof-
  (*coherence*)
    show "(({[TARSKIK4 i,j ] where i be ElementSUBSET-1M1-of omegaORDINAL1K4, j be ElementSUBSET-1M1-of omegaORDINAL1K4 : (i,j)are-coprimeARYTM-3R1 & j <>HIDDENR2 {}XBOOLE-0K1 })\\SUBSET-1K6 ({[TARSKIK4 k,\<one>\<^sub>M ] where k be ElementSUBSET-1M1-of omegaORDINAL1K4 :  True  }))\\/XBOOLE-0K2 omegaORDINAL1K4 be setHIDDENM2"
       sorry
qed "sorry"

mlemma arytm_3_lm_6:
"omegaORDINAL1K4 c=TARSKIR1 RAT+ARYTM-3K5"
  using xboole_1_th_7 sorry

reserve x, y, z for "ElementSUBSET-1M1-of RAT+ARYTM-3K5"
mtheorem arytm_3_cl_3:
"cluster RAT+ARYTM-3K5 as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "RAT+ARYTM-3K5 be  non emptyXBOOLE-0V1"
     sorry
qed "sorry"

mtheorem arytm_3_cl_4:
"cluster  non emptyXBOOLE-0V1\<bar>ordinalORDINAL1V3 for ElementSUBSET-1M1-of RAT+ARYTM-3K5"
proof
(*existence*)
  show " ex it be ElementSUBSET-1M1-of RAT+ARYTM-3K5 st it be  non emptyXBOOLE-0V1\<bar>ordinalORDINAL1V3"
    using arytm_3_lm_2 arytm_3_lm_6 arytm_3_lm_4 sorry
qed "sorry"

mtheorem arytm_3_th_29:
" for x be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds x inTARSKIR2 omegaORDINAL1K4 or ( ex i be ElementSUBSET-1M1-of omegaORDINAL1K4 st  ex j be ElementSUBSET-1M1-of omegaORDINAL1K4 st ((x =HIDDENR1 [TARSKIK4 i,j ] & (i,j)are-coprimeARYTM-3R1) & j <>HIDDENR2 {}XBOOLE-0K1) & j <>HIDDENR2 \<one>\<^sub>M)"
sorry

mtheorem arytm_3_th_30:
" not ( ex i be setHIDDENM2 st  ex j be setHIDDENM2 st [TARSKIK4 i,j ] be OrdinalORDINAL1M3)"
sorry

mtheorem arytm_3_th_31:
" for A be OrdinalORDINAL1M3 holds A inTARSKIR2 RAT+ARYTM-3K5 implies A inTARSKIR2 omegaORDINAL1K4"
sorry

mtheorem arytm_3_cl_5:
"cluster note-that naturalORDINAL1V7 for ordinalORDINAL1V3\<bar>ElementSUBSET-1M1-of RAT+ARYTM-3K5"
proof
(*coherence*)
  show " for it be ordinalORDINAL1V3\<bar>ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds it be naturalORDINAL1V7"
sorry
qed "sorry"

mtheorem arytm_3_th_32:
" not ( ex i be objectHIDDENM1 st  ex j be objectHIDDENM1 st [TARSKIK4 i,j ] inHIDDENR3 omegaORDINAL1K4)"
sorry

mtheorem arytm_3_th_33:
" for i be ElementSUBSET-1M1-of omegaORDINAL1K4 holds  for j be ElementSUBSET-1M1-of omegaORDINAL1K4 holds [TARSKIK4 i,j ] inHIDDENR3 RAT+ARYTM-3K5 iff ((i,j)are-coprimeARYTM-3R1 & j <>HIDDENR2 {}XBOOLE-0K1) & j <>HIDDENR2 \<one>\<^sub>M"
sorry

mdef arytm_3_def_8 ("numeratorARYTM-3K6  _ " [250]250 ) where
  mlet "x be ElementSUBSET-1M1-of RAT+ARYTM-3K5"
"func numeratorARYTM-3K6 x \<rightarrow> ElementSUBSET-1M1-of omegaORDINAL1K4 means
  \<lambda>it. it =XBOOLE-0R4 x if x inTARSKIR2 omegaORDINAL1K4 otherwise \<lambda>it.  ex a be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 st x =HIDDENR1 [TARSKIK4 it,a ]"
proof-
  (*existence*)
    show "(x inTARSKIR2 omegaORDINAL1K4 implies ( ex it be ElementSUBSET-1M1-of omegaORDINAL1K4 st it =XBOOLE-0R4 x)) & ( not x inTARSKIR2 omegaORDINAL1K4 implies ( ex it be ElementSUBSET-1M1-of omegaORDINAL1K4 st  ex a be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 st x =HIDDENR1 [TARSKIK4 it,a ]))"
sorry
  (*consistency*)
    show " for it be ElementSUBSET-1M1-of omegaORDINAL1K4 holds  True "
      using xtuple_0_th_1 sorry
  (*uniqueness*)
    show " for it1 be ElementSUBSET-1M1-of omegaORDINAL1K4 holds  for it2 be ElementSUBSET-1M1-of omegaORDINAL1K4 holds (x inTARSKIR2 omegaORDINAL1K4 implies (it1 =XBOOLE-0R4 x & it2 =XBOOLE-0R4 x implies it1 =HIDDENR1 it2)) & ( not x inTARSKIR2 omegaORDINAL1K4 implies (( ex a be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 st x =HIDDENR1 [TARSKIK4 it1,a ]) & ( ex a be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 st x =HIDDENR1 [TARSKIK4 it2,a ]) implies it1 =HIDDENR1 it2))"
      using xtuple_0_th_1 sorry
qed "sorry"

mdef arytm_3_def_9 ("denominatorARYTM-3K7  _ " [250]250 ) where
  mlet "x be ElementSUBSET-1M1-of RAT+ARYTM-3K5"
"func denominatorARYTM-3K7 x \<rightarrow> ElementSUBSET-1M1-of omegaORDINAL1K4 means
  \<lambda>it. it =XBOOLE-0R4 \<one>\<^sub>M if x inTARSKIR2 omegaORDINAL1K4 otherwise \<lambda>it.  ex a be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 st x =HIDDENR1 [TARSKIK4 a,it ]"
proof-
  (*existence*)
    show "(x inTARSKIR2 omegaORDINAL1K4 implies ( ex it be ElementSUBSET-1M1-of omegaORDINAL1K4 st it =XBOOLE-0R4 \<one>\<^sub>M)) & ( not x inTARSKIR2 omegaORDINAL1K4 implies ( ex it be ElementSUBSET-1M1-of omegaORDINAL1K4 st  ex a be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 st x =HIDDENR1 [TARSKIK4 a,it ]))"
sorry
  (*consistency*)
    show " for it be ElementSUBSET-1M1-of omegaORDINAL1K4 holds  True "
      using xtuple_0_th_1 sorry
  (*uniqueness*)
    show " for it1 be ElementSUBSET-1M1-of omegaORDINAL1K4 holds  for it2 be ElementSUBSET-1M1-of omegaORDINAL1K4 holds (x inTARSKIR2 omegaORDINAL1K4 implies (it1 =XBOOLE-0R4 \<one>\<^sub>M & it2 =XBOOLE-0R4 \<one>\<^sub>M implies it1 =HIDDENR1 it2)) & ( not x inTARSKIR2 omegaORDINAL1K4 implies (( ex a be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 st x =HIDDENR1 [TARSKIK4 a,it1 ]) & ( ex a be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 st x =HIDDENR1 [TARSKIK4 a,it2 ]) implies it1 =HIDDENR1 it2))"
      using xtuple_0_th_1 sorry
qed "sorry"

mtheorem arytm_3_th_34:
" for x be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds (numeratorARYTM-3K6 x,denominatorARYTM-3K7 x)are-coprimeARYTM-3R1"
sorry

mtheorem arytm_3_th_35:
" for x be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds denominatorARYTM-3K7 x <>HIDDENR2 {}XBOOLE-0K1"
sorry

mtheorem arytm_3_th_36:
" for x be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds  not x inTARSKIR2 omegaORDINAL1K4 implies x =HIDDENR1 [TARSKIK4 numeratorARYTM-3K6 x,denominatorARYTM-3K7 x ] & denominatorARYTM-3K7 x <>HIDDENR2 \<one>\<^sub>M"
sorry

mtheorem arytm_3_th_37:
" for x be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds x <>HIDDENR2 {}XBOOLE-0K1 iff numeratorARYTM-3K6 x <>HIDDENR2 {}XBOOLE-0K1"
sorry

mtheorem arytm_3_th_38:
" for x be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds x inTARSKIR2 omegaORDINAL1K4 iff denominatorARYTM-3K7 x =XBOOLE-0R4 \<one>\<^sub>M"
  using arytm_3_def_9 arytm_3_th_36 sorry

mdef arytm_3_def_10 (" _ '/ARYTM-3K8  _ " [164,164]164 ) where
  mlet "i be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3", "j be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3"
"func i /ARYTM-3K8 j \<rightarrow> ElementSUBSET-1M1-of RAT+ARYTM-3K5 equals
  {}XBOOLE-0K1 if j =XBOOLE-0R4 {}XBOOLE-0K1,
  REDARYTM-3K4(i,j) if REDARYTM-3K4(j,i) =XBOOLE-0R4 \<one>\<^sub>M otherwise [TARSKIK4 REDARYTM-3K4(i,j),REDARYTM-3K4(j,i) ]"
proof-
  (*coherence*)
    show "(j =XBOOLE-0R4 {}XBOOLE-0K1 implies {}XBOOLE-0K1 be ElementSUBSET-1M1-of RAT+ARYTM-3K5) & ((REDARYTM-3K4(j,i) =XBOOLE-0R4 \<one>\<^sub>M implies REDARYTM-3K4(i,j) be ElementSUBSET-1M1-of RAT+ARYTM-3K5) & ( not j =XBOOLE-0R4 {}XBOOLE-0K1 &  not REDARYTM-3K4(j,i) =XBOOLE-0R4 \<one>\<^sub>M implies [TARSKIK4 REDARYTM-3K4(i,j),REDARYTM-3K4(j,i) ] be ElementSUBSET-1M1-of RAT+ARYTM-3K5))"
sorry
  (*consistency*)
    show " for it be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds j =XBOOLE-0R4 {}XBOOLE-0K1 & REDARYTM-3K4(j,i) =XBOOLE-0R4 \<one>\<^sub>M implies (it =HIDDENR1 {}XBOOLE-0K1 iff it =HIDDENR1 REDARYTM-3K4(i,j))"
      using arytm_3_th_26 arytm_3_lm_4 sorry
qed "sorry"

abbreviation(input) ARYTM_3K9("quotientARYTM-3K9'( _ , _ ')" [0,0]164) where
  "quotientARYTM-3K9(i,j) \<equiv> i /ARYTM-3K8 j"

mtheorem arytm_3_th_39:
" for x be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds numeratorARYTM-3K6 x /ARYTM-3K8 denominatorARYTM-3K7 x =XBOOLE-0R4 x"
sorry

mtheorem arytm_3_th_40:
" for a be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 holds  for b be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 holds {}XBOOLE-0K1 /ARYTM-3K8 b =XBOOLE-0R4 {}XBOOLE-0K1 & a /ARYTM-3K8 \<one>\<^sub>M =XBOOLE-0R4 a"
sorry

mtheorem arytm_3_th_41:
" for a be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 holds a <>HIDDENR2 {}XBOOLE-0K1 implies a /ARYTM-3K8 a =XBOOLE-0R4 \<one>\<^sub>M"
sorry

mtheorem arytm_3_th_42:
" for a be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 holds  for b be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 holds b <>HIDDENR2 {}XBOOLE-0K1 implies numeratorARYTM-3K6 (a /ARYTM-3K8 b) =XBOOLE-0R4 REDARYTM-3K4(a,b) & denominatorARYTM-3K7 (a /ARYTM-3K8 b) =XBOOLE-0R4 REDARYTM-3K4(b,a)"
sorry

mtheorem arytm_3_th_43:
" for i be ElementSUBSET-1M1-of omegaORDINAL1K4 holds  for j be ElementSUBSET-1M1-of omegaORDINAL1K4 holds (i,j)are-coprimeARYTM-3R1 & j <>HIDDENR2 {}XBOOLE-0K1 implies numeratorARYTM-3K6 (i /ARYTM-3K8 j) =XBOOLE-0R4 i & denominatorARYTM-3K7 (i /ARYTM-3K8 j) =XBOOLE-0R4 j"
sorry

mtheorem arytm_3_th_44:
" for a be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 holds  for b be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 holds  for c be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 holds c <>HIDDENR2 {}XBOOLE-0K1 implies (a *^ORDINAL3K9 c)/ARYTM-3K8 (b *^ORDINAL3K9 c) =XBOOLE-0R4 a /ARYTM-3K8 b"
sorry

reserve i, j, k for "naturalORDINAL1V7\<bar>OrdinalORDINAL1M3"
mtheorem arytm_3_th_45:
" for l be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 holds  for i be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 holds  for j be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 holds  for k be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 holds j <>HIDDENR2 {}XBOOLE-0K1 & l <>HIDDENR2 {}XBOOLE-0K1 implies (i /ARYTM-3K8 j =XBOOLE-0R4 k /ARYTM-3K8 l iff i *^ORDINAL3K9 l =XBOOLE-0R4 j *^ORDINAL3K9 k)"
sorry

mdef arytm_3_def_11 (" _ +ARYTM-3K10  _ " [132,132]132 ) where
  mlet "x be ElementSUBSET-1M1-of RAT+ARYTM-3K5", "y be ElementSUBSET-1M1-of RAT+ARYTM-3K5"
"func x +ARYTM-3K10 y \<rightarrow> ElementSUBSET-1M1-of RAT+ARYTM-3K5 equals
  (numeratorARYTM-3K6 x *^ORDINAL3K9 denominatorARYTM-3K7 y +^ORDINAL3K8 numeratorARYTM-3K6 y *^ORDINAL3K9 denominatorARYTM-3K7 x)/ARYTM-3K8 (denominatorARYTM-3K7 x *^ORDINAL3K9 denominatorARYTM-3K7 y)"
proof-
  (*coherence*)
    show "(numeratorARYTM-3K6 x *^ORDINAL3K9 denominatorARYTM-3K7 y +^ORDINAL3K8 numeratorARYTM-3K6 y *^ORDINAL3K9 denominatorARYTM-3K7 x)/ARYTM-3K8 (denominatorARYTM-3K7 x *^ORDINAL3K9 denominatorARYTM-3K7 y) be ElementSUBSET-1M1-of RAT+ARYTM-3K5"
       sorry
qed "sorry"

mtheorem ARYTM_3K10_commutativity:
" for x be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds  for y be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds x +ARYTM-3K10 y =HIDDENR1 y +ARYTM-3K10 x"
sorry

mdef arytm_3_def_12 (" _ *''ARYTM-3K11  _ " [228,228]228 ) where
  mlet "x be ElementSUBSET-1M1-of RAT+ARYTM-3K5", "y be ElementSUBSET-1M1-of RAT+ARYTM-3K5"
"func x *'ARYTM-3K11 y \<rightarrow> ElementSUBSET-1M1-of RAT+ARYTM-3K5 equals
  (numeratorARYTM-3K6 x *^ORDINAL3K9 numeratorARYTM-3K6 y)/ARYTM-3K8 (denominatorARYTM-3K7 x *^ORDINAL3K9 denominatorARYTM-3K7 y)"
proof-
  (*coherence*)
    show "(numeratorARYTM-3K6 x *^ORDINAL3K9 numeratorARYTM-3K6 y)/ARYTM-3K8 (denominatorARYTM-3K7 x *^ORDINAL3K9 denominatorARYTM-3K7 y) be ElementSUBSET-1M1-of RAT+ARYTM-3K5"
       sorry
qed "sorry"

mtheorem ARYTM_3K11_commutativity:
" for x be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds  for y be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds x *'ARYTM-3K11 y =HIDDENR1 y *'ARYTM-3K11 x"
sorry

mtheorem arytm_3_th_46:
" for l be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 holds  for i be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 holds  for j be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 holds  for k be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 holds j <>HIDDENR2 {}XBOOLE-0K1 & l <>HIDDENR2 {}XBOOLE-0K1 implies i /ARYTM-3K8 j +ARYTM-3K10 k /ARYTM-3K8 l =XBOOLE-0R4 (i *^ORDINAL3K9 l +^ORDINAL3K8 j *^ORDINAL3K9 k)/ARYTM-3K8 (j *^ORDINAL3K9 l)"
sorry

mtheorem arytm_3_th_47:
" for i be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 holds  for j be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 holds  for k be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 holds k <>HIDDENR2 {}XBOOLE-0K1 implies i /ARYTM-3K8 k +ARYTM-3K10 j /ARYTM-3K8 k =XBOOLE-0R4 (i +^ORDINAL3K8 j)/ARYTM-3K8 k"
sorry

mtheorem arytm_3_cl_6:
"cluster emptyXBOOLE-0V1 for ElementSUBSET-1M1-of RAT+ARYTM-3K5"
proof
(*existence*)
  show " ex it be ElementSUBSET-1M1-of RAT+ARYTM-3K5 st it be emptyXBOOLE-0V1"
    using arytm_3_lm_1 arytm_3_lm_6 sorry
qed "sorry"

abbreviation(input) ARYTM_3K12("{}ARYTM-3K12" 228) where
  "{}ARYTM-3K12 \<equiv> {}XBOOLE-0K1"

mtheorem arytm_3_add_1:
"cluster {}XBOOLE-0K1 as-term-is ElementSUBSET-1M1-of RAT+ARYTM-3K5"
proof
(*coherence*)
  show "{}XBOOLE-0K1 be ElementSUBSET-1M1-of RAT+ARYTM-3K5"
    using arytm_3_lm_1 arytm_3_lm_6 sorry
qed "sorry"

abbreviation(input) ARYTM_3K13("oneARYTM-3K13" 228) where
  "oneARYTM-3K13 \<equiv> oneARYTM-3K1"

mtheorem arytm_3_add_2:
"cluster oneARYTM-3K1 as-term-is  non emptyXBOOLE-0V1\<bar>ordinalORDINAL1V3\<bar>ElementSUBSET-1M1-of RAT+ARYTM-3K5"
proof
(*coherence*)
  show "oneARYTM-3K1 be  non emptyXBOOLE-0V1\<bar>ordinalORDINAL1V3\<bar>ElementSUBSET-1M1-of RAT+ARYTM-3K5"
    using arytm_3_lm_6 arytm_3_lm_4 sorry
qed "sorry"

mtheorem arytm_3_th_48:
" for x be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds x *'ARYTM-3K11 ({}ARYTM-3K12) =XBOOLE-0R4 {}ARYTM-3K12"
sorry

mtheorem arytm_3_th_49:
" for l be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 holds  for i be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 holds  for j be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 holds  for k be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 holds (i /ARYTM-3K8 j)*'ARYTM-3K11 (k /ARYTM-3K8 l) =XBOOLE-0R4 (i *^ORDINAL3K9 k)/ARYTM-3K8 (j *^ORDINAL3K9 l)"
sorry

mtheorem arytm_3_th_50:
" for x be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds x +ARYTM-3K10 {}ARYTM-3K12 =XBOOLE-0R4 x"
sorry

mtheorem arytm_3_th_51:
" for x be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds  for y be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds  for z be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds (x +ARYTM-3K10 y)+ARYTM-3K10 z =XBOOLE-0R4 x +ARYTM-3K10 (y +ARYTM-3K10 z)"
sorry

mtheorem arytm_3_th_52:
" for x be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds  for y be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds  for z be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds (x *'ARYTM-3K11 y)*'ARYTM-3K11 z =XBOOLE-0R4 x *'ARYTM-3K11 (y *'ARYTM-3K11 z)"
sorry

mtheorem arytm_3_th_53:
" for x be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds x *'ARYTM-3K11 (oneARYTM-3K13) =XBOOLE-0R4 x"
sorry

mtheorem arytm_3_th_54:
" for x be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds x <>HIDDENR2 {}ARYTM-3K12 implies ( ex y be ElementSUBSET-1M1-of RAT+ARYTM-3K5 st x *'ARYTM-3K11 y =XBOOLE-0R4 \<one>\<^sub>M)"
sorry

mtheorem arytm_3_th_55:
" for x be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds  for y be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds x <>HIDDENR2 {}ARYTM-3K12 implies ( ex z be ElementSUBSET-1M1-of RAT+ARYTM-3K5 st y =XBOOLE-0R4 x *'ARYTM-3K11 z)"
sorry

mtheorem arytm_3_th_56:
" for x be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds  for y be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds  for z be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds x <>HIDDENR2 {}ARYTM-3K12 & x *'ARYTM-3K11 y =XBOOLE-0R4 x *'ARYTM-3K11 z implies y =XBOOLE-0R4 z"
sorry

mtheorem arytm_3_th_57:
" for x be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds  for y be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds  for z be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds x *'ARYTM-3K11 (y +ARYTM-3K10 z) =XBOOLE-0R4 x *'ARYTM-3K11 y +ARYTM-3K10 x *'ARYTM-3K11 z"
sorry

mtheorem arytm_3_th_58:
" for i be ordinalORDINAL1V3\<bar>ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds  for j be ordinalORDINAL1V3\<bar>ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds i +ARYTM-3K10 j =XBOOLE-0R4 i +^ORDINAL3K8 j"
sorry

mtheorem arytm_3_th_59:
" for i be ordinalORDINAL1V3\<bar>ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds  for j be ordinalORDINAL1V3\<bar>ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds i *'ARYTM-3K11 j =XBOOLE-0R4 i *^ORDINAL3K9 j"
sorry

mtheorem arytm_3_th_60:
" for x be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds  ex y be ElementSUBSET-1M1-of RAT+ARYTM-3K5 st x =XBOOLE-0R4 y +ARYTM-3K10 y"
sorry

mdef arytm_3_def_13 (" _ <=''ARYTM-3R3  _ " [50,50]50 ) where
  mlet "x be ElementSUBSET-1M1-of RAT+ARYTM-3K5", "y be ElementSUBSET-1M1-of RAT+ARYTM-3K5"
"pred x <='ARYTM-3R3 y means
   ex z be ElementSUBSET-1M1-of RAT+ARYTM-3K5 st y =XBOOLE-0R4 x +ARYTM-3K10 z"..

mtheorem ARYTM_3R3_connectedness:
" for x be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds  for y be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds  not x <='ARYTM-3R3 y implies y <='ARYTM-3R3 x"
sorry

syntax ARYTM_3R4 :: " Set \<Rightarrow>  Set \<Rightarrow> o" (" _ <ARYTM-3R4  _ " [50,50]50)
translations "y <ARYTM-3R4 x" \<rightharpoonup> " not x <='ARYTM-3R3 y"

reserve r, s, t for "ElementSUBSET-1M1-of RAT+ARYTM-3K5"
mtheorem arytm_3_th_61:
" not ( ex y be objectHIDDENM1 st [TARSKIK4 {}ARYTM-3K12,y ] inHIDDENR3 RAT+ARYTM-3K5)"
sorry

mtheorem arytm_3_th_62:
" for r be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds  for s be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds  for t be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds s +ARYTM-3K10 t =XBOOLE-0R4 r +ARYTM-3K10 t implies s =XBOOLE-0R4 r"
sorry

mtheorem arytm_3_th_63:
" for r be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds  for s be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds r +ARYTM-3K10 s =XBOOLE-0R4 {}ARYTM-3K12 implies r =XBOOLE-0R4 {}ARYTM-3K12"
sorry

mtheorem arytm_3_th_64:
" for s be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds {}ARYTM-3K12 <='ARYTM-3R3 s"
sorry

mtheorem arytm_3_th_65:
" for s be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds s <='ARYTM-3R3 {}ARYTM-3K12 implies s =XBOOLE-0R4 {}ARYTM-3K12"
  using arytm_3_th_63 sorry

mtheorem arytm_3_th_66:
" for r be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds  for s be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds r <='ARYTM-3R3 s & s <='ARYTM-3R3 r implies r =XBOOLE-0R4 s"
sorry

mtheorem arytm_3_th_67:
" for r be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds  for s be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds  for t be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds r <='ARYTM-3R3 s & s <='ARYTM-3R3 t implies r <='ARYTM-3R3 t"
sorry

mtheorem arytm_3_th_68:
" for r be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds  for s be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds r <ARYTM-3R4 s iff r <='ARYTM-3R3 s & r <>HIDDENR2 s"
  using arytm_3_th_66 sorry

mtheorem arytm_3_th_69:
" for r be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds  for s be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds  for t be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds r <ARYTM-3R4 s & s <='ARYTM-3R3 t or r <='ARYTM-3R3 s & s <ARYTM-3R4 t implies r <ARYTM-3R4 t"
  using arytm_3_th_67 sorry

mtheorem arytm_3_th_70:
" for r be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds  for s be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds  for t be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds r <ARYTM-3R4 s & s <ARYTM-3R4 t implies r <ARYTM-3R4 t"
  using arytm_3_th_67 sorry

mtheorem arytm_3_th_71:
" for x be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds  for y be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds x inTARSKIR2 omegaORDINAL1K4 & x +ARYTM-3K10 y inTARSKIR2 omegaORDINAL1K4 implies y inTARSKIR2 omegaORDINAL1K4"
sorry

mtheorem arytm_3_th_72:
" for x be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds  for i be ordinalORDINAL1V3\<bar>ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds i <ARYTM-3R4 x & x <ARYTM-3R4 i +ARYTM-3K10 oneARYTM-3K13 implies  not x inTARSKIR2 omegaORDINAL1K4"
sorry

mtheorem arytm_3_th_73:
" for t be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds t <>HIDDENR2 {}ARYTM-3K12 implies ( ex r be ElementSUBSET-1M1-of RAT+ARYTM-3K5 st r <ARYTM-3R4 t &  not r inTARSKIR2 omegaORDINAL1K4)"
sorry

mtheorem arytm_3_th_74:
" for t be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds {s where s be ElementSUBSET-1M1-of RAT+ARYTM-3K5 : s <ARYTM-3R4 t } inTARSKIR2 RAT+ARYTM-3K5 iff t =XBOOLE-0R4 {}ARYTM-3K12"
sorry

mtheorem arytm_3_th_75:
" for A be SubsetSUBSET-1M2-of RAT+ARYTM-3K5 holds ( ex t be ElementSUBSET-1M1-of RAT+ARYTM-3K5 st t inTARSKIR2 A & t <>HIDDENR2 {}ARYTM-3K12) & ( for r be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds  for s be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds r inTARSKIR2 A & s <='ARYTM-3R3 r implies s inTARSKIR2 A) implies ( ex r1 be ElementSUBSET-1M1-of RAT+ARYTM-3K5 st  ex r2 be ElementSUBSET-1M1-of RAT+ARYTM-3K5 st  ex r3 be ElementSUBSET-1M1-of RAT+ARYTM-3K5 st ((((r1 inTARSKIR2 A & r2 inTARSKIR2 A) & r3 inTARSKIR2 A) & r1 <>HIDDENR2 r2) & r2 <>HIDDENR2 r3) & r3 <>HIDDENR2 r1)"
sorry

mtheorem arytm_3_th_76:
" for r be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds  for s be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds  for t be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds s +ARYTM-3K10 t <='ARYTM-3R3 r +ARYTM-3K10 t iff s <='ARYTM-3R3 r"
sorry

mtheorem arytm_3_th_77:
" for s be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds  for t be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds s <='ARYTM-3R3 s +ARYTM-3K10 t"
   sorry

mtheorem arytm_3_th_78:
" for r be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds  for s be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds r *'ARYTM-3K11 s =XBOOLE-0R4 {}ARYTM-3K12 implies r =XBOOLE-0R4 {}ARYTM-3K12 or s =XBOOLE-0R4 {}ARYTM-3K12"
sorry

mtheorem arytm_3_th_79:
" for r be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds  for s be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds  for t be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds r <='ARYTM-3R3 s *'ARYTM-3K11 t implies ( ex t0 be ElementSUBSET-1M1-of RAT+ARYTM-3K5 st r =XBOOLE-0R4 s *'ARYTM-3K11 t0 & t0 <='ARYTM-3R3 t)"
sorry

mtheorem arytm_3_th_80:
" for r be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds  for s be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds  for t be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds t <>HIDDENR2 {}ARYTM-3K12 & s *'ARYTM-3K11 t <='ARYTM-3R3 r *'ARYTM-3K11 t implies s <='ARYTM-3R3 r"
sorry

mtheorem arytm_3_th_81:
" for r1 be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds  for r2 be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds  for s1 be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds  for s2 be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds r1 +ARYTM-3K10 r2 =XBOOLE-0R4 s1 +ARYTM-3K10 s2 implies r1 <='ARYTM-3R3 s1 or r2 <='ARYTM-3R3 s2"
sorry

mtheorem arytm_3_th_82:
" for r be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds  for s be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds  for t be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds s <='ARYTM-3R3 r implies s *'ARYTM-3K11 t <='ARYTM-3R3 r *'ARYTM-3K11 t"
sorry

mtheorem arytm_3_th_83:
" for r1 be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds  for r2 be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds  for s1 be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds  for s2 be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds r1 *'ARYTM-3K11 r2 =XBOOLE-0R4 s1 *'ARYTM-3K11 s2 implies r1 <='ARYTM-3R3 s1 or r2 <='ARYTM-3R3 s2"
sorry

mtheorem arytm_3_th_84:
" for r be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds  for s be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds r =XBOOLE-0R4 {}ARYTM-3K12 iff r +ARYTM-3K10 s =XBOOLE-0R4 s"
sorry

mtheorem arytm_3_th_85:
" for s1 be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds  for t1 be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds  for s2 be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds  for t2 be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds s1 +ARYTM-3K10 t1 =XBOOLE-0R4 s2 +ARYTM-3K10 t2 & s1 <='ARYTM-3R3 s2 implies t2 <='ARYTM-3R3 t1"
sorry

mtheorem arytm_3_th_86:
" for r be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds  for s be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds  for t be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds r <='ARYTM-3R3 s & s <='ARYTM-3R3 r +ARYTM-3K10 t implies ( ex t0 be ElementSUBSET-1M1-of RAT+ARYTM-3K5 st s =XBOOLE-0R4 r +ARYTM-3K10 t0 & t0 <='ARYTM-3R3 t)"
  using arytm_3_th_76 sorry

mtheorem arytm_3_th_87:
" for r be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds  for s be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds  for t be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds r <='ARYTM-3R3 s +ARYTM-3K10 t implies ( ex s0 be ElementSUBSET-1M1-of RAT+ARYTM-3K5 st  ex t0 be ElementSUBSET-1M1-of RAT+ARYTM-3K5 st (r =XBOOLE-0R4 s0 +ARYTM-3K10 t0 & s0 <='ARYTM-3R3 s) & t0 <='ARYTM-3R3 t)"
sorry

mtheorem arytm_3_th_88:
" for r be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds  for s be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds  for t be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds r <ARYTM-3R4 s & r <ARYTM-3R4 t implies ( ex t0 be ElementSUBSET-1M1-of RAT+ARYTM-3K5 st (t0 <='ARYTM-3R3 s & t0 <='ARYTM-3R3 t) & r <ARYTM-3R4 t0)"
sorry

mtheorem arytm_3_th_89:
" for r be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds  for s be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds  for t be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds (r <='ARYTM-3R3 s & s <='ARYTM-3R3 t) & s <>HIDDENR2 t implies r <>HIDDENR2 t"
  using arytm_3_th_66 sorry

mtheorem arytm_3_th_90:
" for r be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds  for s be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds  for t be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds s <ARYTM-3R4 r +ARYTM-3K10 t & t <>HIDDENR2 {}ARYTM-3K12 implies ( ex r0 be ElementSUBSET-1M1-of RAT+ARYTM-3K5 st  ex t0 be ElementSUBSET-1M1-of RAT+ARYTM-3K5 st ((s =XBOOLE-0R4 r0 +ARYTM-3K10 t0 & r0 <='ARYTM-3R3 r) & t0 <='ARYTM-3R3 t) & t0 <>HIDDENR2 t)"
sorry

mtheorem arytm_3_th_91:
" for A be  non emptyXBOOLE-0V1\<bar>SubsetSUBSET-1M2-of RAT+ARYTM-3K5 holds A inTARSKIR2 RAT+ARYTM-3K5 implies ( ex s be ElementSUBSET-1M1-of RAT+ARYTM-3K5 st s inTARSKIR2 A & ( for r be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds r inTARSKIR2 A implies r <='ARYTM-3R3 s))"
sorry

mtheorem arytm_3_th_92:
" for r be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds  for s be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds  ex t be ElementSUBSET-1M1-of RAT+ARYTM-3K5 st r +ARYTM-3K10 t =XBOOLE-0R4 s or s +ARYTM-3K10 t =XBOOLE-0R4 r"
sorry

mtheorem arytm_3_th_93:
" for r be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds  for s be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds r <ARYTM-3R4 s implies ( ex t be ElementSUBSET-1M1-of RAT+ARYTM-3K5 st r <ARYTM-3R4 t & t <ARYTM-3R4 s)"
sorry

mtheorem arytm_3_th_94:
" for r be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds  ex s be ElementSUBSET-1M1-of RAT+ARYTM-3K5 st r <ARYTM-3R4 s"
sorry

mtheorem arytm_3_th_95:
" for r be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds  for t be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds t <>HIDDENR2 {}ARYTM-3K12 implies ( ex s be ElementSUBSET-1M1-of RAT+ARYTM-3K5 st s inTARSKIR2 omegaORDINAL1K4 & r <='ARYTM-3R3 s *'ARYTM-3K11 t)"
sorry

theorem arytm_3_sch_1:
  fixes n0f0 n1f0 n2f0 Pp1 
  assumes
[ty]: "n0f0 be ElementSUBSET-1M1-of RAT+ARYTM-3K5" and
  [ty]: "n1f0 be ElementSUBSET-1M1-of RAT+ARYTM-3K5" and
  [ty]: "n2f0 be ElementSUBSET-1M1-of RAT+ARYTM-3K5" and
   A1: "n1f0 =XBOOLE-0R4 \<one>\<^sub>M" and
   A2: "n0f0 =XBOOLE-0R4 {}ARYTM-3K12" and
   A3: "n2f0 inTARSKIR2 omegaORDINAL1K4" and
   A4: "Pp1(n0f0)" and
   A5: " not Pp1(n2f0)"
  shows " ex s be ElementSUBSET-1M1-of RAT+ARYTM-3K5 st (s inTARSKIR2 omegaORDINAL1K4 & Pp1(s)) &  not Pp1(s +ARYTM-3K10 n1f0)"
sorry

end
