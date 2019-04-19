theory nat_d
  imports finset_1 int_2
   "../mizar_extension/E_number"
begin
(*begin*)
reserve a, b, p, k, l, m, n, s, h, i, j, t, i1, i2 for "naturalORDINAL1V7\<bar>NumberORDINAL1M1"
mlemma nat_d_lm_1:
" for k be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for l be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds k divINT-1K5 l be NatNAT-1M1"
sorry

mlemma nat_d_lm_2:
" for k be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for l be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds k modINT-1K6 l be NatNAT-1M1"
sorry

abbreviation(input) NAT_DK1(" _ divNAT-DK1  _ " [132,132]132) where
  "k divNAT-DK1 l \<equiv> k divINT-1K5 l"

mtheorem nat_d_def_1:
  mlet "k be naturalORDINAL1V7\<bar>NumberORDINAL1M1", "l be naturalORDINAL1V7\<bar>NumberORDINAL1M1"
"redefine func k divNAT-DK1 l \<rightarrow> NatNAT-1M1 means
  \<lambda>it. ( ex t be NatNAT-1M1 st k =HIDDENR1 l *XCMPLX-0K3 it +XCMPLX-0K2 t & t <XXREAL-0R3 l) or it =XBOOLE-0R4 0NUMBERSK6 & l =HIDDENR1 0NUMBERSK6"
proof
(*compatibility*)
  show " for it be NatNAT-1M1 holds it =HIDDENR1 k divNAT-DK1 l iff ( ex t be NatNAT-1M1 st k =HIDDENR1 l *XCMPLX-0K3 it +XCMPLX-0K2 t & t <XXREAL-0R3 l) or it =XBOOLE-0R4 0NUMBERSK6 & l =HIDDENR1 0NUMBERSK6"
sorry
qed "sorry"

mtheorem nat_d_add_1:
  mlet "k be naturalORDINAL1V7\<bar>NumberORDINAL1M1", "l be naturalORDINAL1V7\<bar>NumberORDINAL1M1"
"cluster k divINT-1K5 l as-term-is NatNAT-1M1"
proof
(*coherence*)
  show "k divINT-1K5 l be NatNAT-1M1"
    using nat_d_lm_1 sorry
qed "sorry"

abbreviation(input) NAT_DK2(" _ modNAT-DK2  _ " [132,132]132) where
  "k modNAT-DK2 l \<equiv> k modINT-1K6 l"

mtheorem nat_d_def_2:
  mlet "k be naturalORDINAL1V7\<bar>NumberORDINAL1M1", "l be naturalORDINAL1V7\<bar>NumberORDINAL1M1"
"redefine func k modNAT-DK2 l \<rightarrow> NatNAT-1M1 means
  \<lambda>it. ( ex t be NatNAT-1M1 st k =HIDDENR1 l *XCMPLX-0K3 t +XCMPLX-0K2 it & it <XXREAL-0R3 l) or it =XBOOLE-0R4 0NUMBERSK6 & l =HIDDENR1 0NUMBERSK6"
proof
(*compatibility*)
  show " for it be NatNAT-1M1 holds it =HIDDENR1 k modNAT-DK2 l iff ( ex t be NatNAT-1M1 st k =HIDDENR1 l *XCMPLX-0K3 t +XCMPLX-0K2 it & it <XXREAL-0R3 l) or it =XBOOLE-0R4 0NUMBERSK6 & l =HIDDENR1 0NUMBERSK6"
sorry
qed "sorry"

mtheorem nat_d_add_2:
  mlet "k be naturalORDINAL1V7\<bar>NumberORDINAL1M1", "l be naturalORDINAL1V7\<bar>NumberORDINAL1M1"
"cluster k modINT-1K6 l as-term-is NatNAT-1M1"
proof
(*coherence*)
  show "k modINT-1K6 l be NatNAT-1M1"
    using nat_d_lm_2 sorry
qed "sorry"

abbreviation(input) NAT_DK3(" _ divNAT-DK3  _ " [132,132]132) where
  "k divNAT-DK3 l \<equiv> k divINT-1K5 l"

mtheorem nat_d_add_3:
  mlet "k be NatNAT-1M1", "l be NatNAT-1M1"
"cluster k divINT-1K5 l as-term-is ElementSUBSET-1M1-of NATNUMBERSK1"
proof
(*coherence*)
  show "k divINT-1K5 l be ElementSUBSET-1M1-of NATNUMBERSK1"
sorry
qed "sorry"

abbreviation(input) NAT_DK4(" _ modNAT-DK4  _ " [132,132]132) where
  "k modNAT-DK4 l \<equiv> k modINT-1K6 l"

mtheorem nat_d_add_4:
  mlet "k be NatNAT-1M1", "l be NatNAT-1M1"
"cluster k modINT-1K6 l as-term-is ElementSUBSET-1M1-of NATNUMBERSK1"
proof
(*coherence*)
  show "k modINT-1K6 l be ElementSUBSET-1M1-of NATNUMBERSK1"
sorry
qed "sorry"

mtheorem nat_d_th_1:
" for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for j be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds 0NUMBERSK6 <XXREAL-0R3 i implies j modNAT-DK2 i <XXREAL-0R3 i"
  using int_1_th_58 sorry

mtheorem nat_d_th_2:
" for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for j be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds 0NUMBERSK6 <XXREAL-0R3 i implies j =HIDDENR1 i *XCMPLX-0K3 (j divNAT-DK1 i) +XCMPLX-0K2 (j modNAT-DK2 i)"
  using int_1_th_59 sorry

abbreviation(input) NAT_DR1(" _ dividesNAT-DR1  _ " [50,50]50) where
  "k dividesNAT-DR1 l \<equiv> k dividesINT-1R1 l"

mtheorem nat_d_def_3:
  mlet "k be naturalORDINAL1V7\<bar>NumberORDINAL1M1", "l be naturalORDINAL1V7\<bar>NumberORDINAL1M1"
"redefine pred k dividesNAT-DR1 l means
   ex t be NatNAT-1M1 st l =HIDDENR1 k *XCMPLX-0K3 t"
proof
(*compatibility*)
  show "k dividesNAT-DR1 l iff ( ex t be NatNAT-1M1 st l =HIDDENR1 k *XCMPLX-0K3 t)"
sorry
qed "sorry"

mtheorem NAT_DR1_reflexivity:
" for l be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds l dividesNAT-DR1 l"
sorry

mtheorem nat_d_th_3:
" for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for j be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds j dividesNAT-DR1 i iff i =HIDDENR1 j *XCMPLX-0K3 (i divNAT-DK1 j)"
sorry

mtheorem nat_d_th_4:
" for h be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for j be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds i dividesNAT-DR1 j & j dividesNAT-DR1 h implies i dividesNAT-DR1 h"
  using int_2_th_9 sorry

mtheorem nat_d_th_5:
" for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for j be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds i dividesNAT-DR1 j & j dividesNAT-DR1 i implies i =HIDDENR1 j"
sorry

mtheorem nat_d_th_6:
" for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds i dividesNAT-DR1 0NUMBERSK6 & \<one>\<^sub>M dividesNAT-DR1 i"
  using int_2_th_12 sorry

mtheorem nat_d_th_7:
" for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for j be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds 0NUMBERSK6 <XXREAL-0R3 j & i dividesNAT-DR1 j implies i <=XXREAL-0R1 j"
  using int_2_th_27 sorry

mtheorem nat_d_th_8:
" for h be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for j be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds i dividesNAT-DR1 j & i dividesNAT-DR1 h implies i dividesNAT-DR1 j +XCMPLX-0K2 h"
sorry

mtheorem nat_d_th_9:
" for h be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for j be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds i dividesNAT-DR1 j implies i dividesNAT-DR1 j *XCMPLX-0K3 h"
  using int_2_th_2 sorry

mtheorem nat_d_th_10:
" for h be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for j be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds i dividesNAT-DR1 j & i dividesNAT-DR1 j +XCMPLX-0K2 h implies i dividesNAT-DR1 h"
sorry

mtheorem nat_d_th_11:
" for h be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for j be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds i dividesNAT-DR1 j & i dividesNAT-DR1 h implies i dividesNAT-DR1 j modNAT-DK2 h"
sorry

abbreviation(input) NAT_DK5(" _ lcmNAT-DK5  _ " [132,132]132) where
  "k lcmNAT-DK5 n \<equiv> k lcmINT-2K2 n"

mtheorem nat_d_def_4:
  mlet "k be naturalORDINAL1V7\<bar>NumberORDINAL1M1", "n be naturalORDINAL1V7\<bar>NumberORDINAL1M1"
"redefine func k lcmNAT-DK5 n \<rightarrow> setHIDDENM2 means
  \<lambda>it. (k dividesNAT-DR1 it & n dividesNAT-DR1 it) & ( for m be NatNAT-1M1 holds k dividesNAT-DR1 m & n dividesNAT-DR1 m implies it dividesNAT-DR1 m)"
proof
(*compatibility*)
  show " for it be setHIDDENM2 holds it =HIDDENR1 k lcmNAT-DK5 n iff (k dividesNAT-DR1 it & n dividesNAT-DR1 it) & ( for m be NatNAT-1M1 holds k dividesNAT-DR1 m & n dividesNAT-DR1 m implies it dividesNAT-DR1 m)"
sorry
qed "sorry"

abbreviation(input) NAT_DK6(" _ lcmNAT-DK6  _ " [132,132]132) where
  "k lcmNAT-DK6 n \<equiv> k lcmINT-2K2 n"

mtheorem nat_d_add_5:
  mlet "k be NatNAT-1M1", "n be NatNAT-1M1"
"cluster k lcmINT-2K2 n as-term-is ElementSUBSET-1M1-of NATNUMBERSK1"
proof
(*coherence*)
  show "k lcmINT-2K2 n be ElementSUBSET-1M1-of NATNUMBERSK1"
    using ordinal1_def_12 sorry
qed "sorry"

abbreviation(input) NAT_DK7(" _ gcdNAT-DK7  _ " [132,132]132) where
  "k gcdNAT-DK7 n \<equiv> k gcdINT-2K3 n"

mtheorem nat_d_def_5:
  mlet "k be naturalORDINAL1V7\<bar>NumberORDINAL1M1", "n be naturalORDINAL1V7\<bar>NumberORDINAL1M1"
"redefine func k gcdNAT-DK7 n \<rightarrow> setHIDDENM2 means
  \<lambda>it. (it dividesNAT-DR1 k & it dividesNAT-DR1 n) & ( for m be NatNAT-1M1 holds m dividesNAT-DR1 k & m dividesNAT-DR1 n implies m dividesNAT-DR1 it)"
proof
(*compatibility*)
  show " for it be setHIDDENM2 holds it =HIDDENR1 k gcdNAT-DK7 n iff (it dividesNAT-DR1 k & it dividesNAT-DR1 n) & ( for m be NatNAT-1M1 holds m dividesNAT-DR1 k & m dividesNAT-DR1 n implies m dividesNAT-DR1 it)"
sorry
qed "sorry"

abbreviation(input) NAT_DK8(" _ gcdNAT-DK8  _ " [132,132]132) where
  "k gcdNAT-DK8 n \<equiv> k gcdINT-2K3 n"

mtheorem nat_d_add_6:
  mlet "k be NatNAT-1M1", "n be NatNAT-1M1"
"cluster k gcdINT-2K3 n as-term-is ElementSUBSET-1M1-of NATNUMBERSK1"
proof
(*coherence*)
  show "k gcdINT-2K3 n be ElementSUBSET-1M1-of NATNUMBERSK1"
    using ordinal1_def_12 sorry
qed "sorry"

(*\$N Correctness of Euclid's Algorithm*)
(*\$N Greatest Common Divisor Algorithm*)
theorem nat_d_sch_1:
  fixes Qf1 af0 bf0 
  assumes
[ty_func]: "\<And> x1. x1 be NatNAT-1M1 \<Longrightarrow> Qf1(x1) be NatNAT-1M1" and
  [ty]: "af0 be NatNAT-1M1" and
  [ty]: "bf0 be NatNAT-1M1" and
   A1: "0NUMBERSK6 <XXREAL-0R3 bf0 & bf0 <XXREAL-0R3 af0" and
   A2: "Qf1(0NUMBERSK6) =XBOOLE-0R4 af0 & Qf1(\<one>\<^sub>M) =XBOOLE-0R4 bf0" and
   A3: " for n be NatNAT-1M1 holds Qf1(n +NAT-1K1 \<two>\<^sub>M) =XBOOLE-0R4 Qf1(n) modNAT-DK4 Qf1(n +NAT-1K1 \<one>\<^sub>M)"
  shows " ex n be NatNAT-1M1 st Qf1(n) =XBOOLE-0R4 af0 gcdNAT-DK8 bf0 & Qf1(n +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 0NUMBERSK6"
sorry

mtheorem nat_d_th_12:
" for n be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds n modNAT-DK2 \<two>\<^sub>M =XBOOLE-0R4 0NUMBERSK6 or n modNAT-DK2 \<two>\<^sub>M =XBOOLE-0R4 \<one>\<^sub>M"
sorry

mtheorem nat_d_th_13:
" for k be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for n be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds k *XCMPLX-0K3 n modNAT-DK2 k =XBOOLE-0R4 0NUMBERSK6"
sorry

mtheorem nat_d_th_14:
" for k be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds k >XXREAL-0R4 \<one>\<^sub>M implies \<one>\<^sub>M modNAT-DK2 k =XBOOLE-0R4 \<one>\<^sub>M"
sorry

mtheorem nat_d_th_15:
" for k be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for l be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for m be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for n be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds k modNAT-DK2 n =XBOOLE-0R4 0NUMBERSK6 & l =HIDDENR1 k -XCMPLX-0K6 m *XCMPLX-0K3 n implies l modNAT-DK2 n =XBOOLE-0R4 0NUMBERSK6"
sorry

mtheorem nat_d_th_16:
" for k be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for l be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for n be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds (n <>HIDDENR2 0NUMBERSK6 & k modNAT-DK2 n =XBOOLE-0R4 0NUMBERSK6) & l <XXREAL-0R3 n implies (k +XCMPLX-0K2 l)modNAT-DK2 n =HIDDENR1 l"
sorry

mtheorem nat_d_th_17:
" for k be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for l be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for n be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds k modNAT-DK2 n =XBOOLE-0R4 0NUMBERSK6 implies (k +XCMPLX-0K2 l)modNAT-DK2 n =XBOOLE-0R4 l modNAT-DK2 n"
sorry

mtheorem nat_d_th_18:
" for k be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for n be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds k <>HIDDENR2 0NUMBERSK6 implies k *XCMPLX-0K3 n divNAT-DK1 k =HIDDENR1 n"
sorry

mtheorem nat_d_th_19:
" for k be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for l be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for n be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds k modNAT-DK2 n =XBOOLE-0R4 0NUMBERSK6 implies (k +XCMPLX-0K2 l)divNAT-DK1 n =XBOOLE-0R4 (k divNAT-DK1 n)+XCMPLX-0K2 (l divNAT-DK1 n)"
sorry

(*begin*)
(*\$CT*)
mtheorem nat_d_th_21:
" for k be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for m be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for n be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds m modNAT-DK2 n =XBOOLE-0R4 (n *XCMPLX-0K3 k +XCMPLX-0K2 m)modNAT-DK2 n"
sorry

mtheorem nat_d_th_22:
" for p be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for n be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for s be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds (p +XCMPLX-0K2 s)modNAT-DK2 n =XBOOLE-0R4 ((p modNAT-DK2 n)+XCMPLX-0K2 s)modNAT-DK2 n"
sorry

mtheorem nat_d_th_23:
" for p be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for n be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for s be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds (p +XCMPLX-0K2 s)modNAT-DK2 n =XBOOLE-0R4 (p +XCMPLX-0K2 (s modNAT-DK2 n))modNAT-DK2 n"
  using nat_d_th_22 sorry

mtheorem nat_d_th_24:
" for k be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for n be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds k <XXREAL-0R3 n implies k modNAT-DK2 n =HIDDENR1 k"
sorry

mtheorem nat_d_th_25:
" for n be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds n modNAT-DK2 n =XBOOLE-0R4 0NUMBERSK6"
sorry

mtheorem nat_d_th_26:
" for n be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds 0NUMBERSK6 =XBOOLE-0R4 0NUMBERSK6 modNAT-DK2 n"
sorry

mtheorem nat_d_th_27:
" for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for j be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds i <XXREAL-0R3 j implies i divNAT-DK1 j =XBOOLE-0R4 0NUMBERSK6"
sorry

mtheorem nat_d_th_28:
" for m be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for n be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds m >XXREAL-0R4 0NUMBERSK6 implies n gcdNAT-DK7 m =XBOOLE-0R4 m gcdNAT-DK7 (n modNAT-DK2 m)"
sorry

theorem nat_d_sch_2:
  fixes kf0 nf0 Pp1 
  assumes
[ty]: "kf0 be ElementSUBSET-1M1-of NATNUMBERSK1" and
  [ty]: "nf0 be ElementSUBSET-1M1-of NATNUMBERSK1" and
   A1: "Pp1(0NUMBERSK6)" and
   A2: "kf0 >XXREAL-0R4 0NUMBERSK6" and
   A3: " for i be NatNAT-1M1 holds  for j be NatNAT-1M1 holds (Pp1(kf0 *XCMPLX-0K3 i) & j <>HIDDENR2 0NUMBERSK6) & j <=XXREAL-0R1 kf0 implies Pp1(kf0 *XCMPLX-0K3 i +XCMPLX-0K2 j)"
  shows "Pp1(nf0)"
sorry

mtheorem nat_d_th_29:
" for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for j be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds i *XCMPLX-0K3 j =XBOOLE-0R4 (i lcmNAT-DK5 j)*XCMPLX-0K3 (i gcdNAT-DK7 j)"
sorry

mtheorem nat_d_th_30:
" for i be IntegerINT-1M1 holds  for j be IntegerINT-1M1 holds i >=XXREAL-0R2 0NUMBERSK6 & j >XXREAL-0R4 0NUMBERSK6 implies i gcdINT-2K3 j =XBOOLE-0R4 j gcdINT-2K3 (i modINT-1K6 j)"
sorry

mtheorem nat_d_th_31:
" for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds i lcmNAT-DK5 i =HIDDENR1 i"
sorry

mtheorem nat_d_th_32:
" for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds i gcdNAT-DK7 i =HIDDENR1 i"
sorry

mtheorem nat_d_th_33:
" for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for j be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds i <XXREAL-0R3 j & i <>HIDDENR2 0NUMBERSK6 implies  not i /XCMPLX-0K7 j be integerINT-1V1"
sorry

abbreviation(input) NAT_DK9(" _ -''NAT-DK9  _ " [132,132]132) where
  "i -'NAT-DK9 j \<equiv> i -'XREAL-0K1 j"

mtheorem nat_d_add_7:
  mlet "i be NatNAT-1M1", "j be NatNAT-1M1"
"cluster i -'XREAL-0K1 j as-term-is ElementSUBSET-1M1-of NATNUMBERSK1"
proof
(*coherence*)
  show "i -'XREAL-0K1 j be ElementSUBSET-1M1-of NATNUMBERSK1"
sorry
qed "sorry"

mtheorem nat_d_th_34:
" for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for j be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds (i +XCMPLX-0K2 j)-'XREAL-0K1 j =HIDDENR1 i"
sorry

mtheorem nat_d_th_35:
" for a be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for b be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds a -'XREAL-0K1 b <=XXREAL-0R1 a"
sorry

mtheorem nat_d_th_36:
" for n be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds n -'XREAL-0K1 i =XBOOLE-0R4 0NUMBERSK6 implies n <=XXREAL-0R1 i"
sorry

mtheorem nat_d_th_37:
" for k be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for j be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds i <=XXREAL-0R1 j implies (j +XCMPLX-0K2 k)-'XREAL-0K1 i =XBOOLE-0R4 (j +XCMPLX-0K2 k)-XCMPLX-0K6 i"
  using nat_1_th_12 xreal_1_th_233 sorry

mtheorem nat_d_th_38:
" for k be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for j be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds i <=XXREAL-0R1 j implies (j +XCMPLX-0K2 k)-'XREAL-0K1 i =XBOOLE-0R4 (j -'XREAL-0K1 i)+XCMPLX-0K2 k"
sorry

mtheorem nat_d_th_39:
" for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for i1 be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds i -'XREAL-0K1 i1 >=XXREAL-0R2 \<one>\<^sub>M or i -XCMPLX-0K6 i1 >=XXREAL-0R2 \<one>\<^sub>M implies i -'XREAL-0K1 i1 =XBOOLE-0R4 i -XCMPLX-0K6 i1"
sorry

mtheorem nat_d_th_40:
" for n be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds n -'XREAL-0K1 0NUMBERSK6 =HIDDENR1 n"
sorry

mtheorem nat_d_th_41:
" for n be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for i1 be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for i2 be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds i1 <=XXREAL-0R1 i2 implies n -'XREAL-0K1 i2 <=XXREAL-0R1 n -'XREAL-0K1 i1"
sorry

mtheorem nat_d_th_42:
" for n be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for i1 be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for i2 be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds i1 <=XXREAL-0R1 i2 implies i1 -'XREAL-0K1 n <=XXREAL-0R1 i2 -'XREAL-0K1 n"
sorry

mtheorem nat_d_th_43:
" for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for i1 be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds i -'XREAL-0K1 i1 >=XXREAL-0R2 \<one>\<^sub>M or i -XCMPLX-0K6 i1 >=XXREAL-0R2 \<one>\<^sub>M implies (i -'XREAL-0K1 i1)+XCMPLX-0K2 i1 =HIDDENR1 i"
sorry

mtheorem nat_d_th_44:
" for i1 be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for i2 be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds i1 <=XXREAL-0R1 i2 implies i1 -'XREAL-0K1 \<one>\<^sub>M <=XXREAL-0R1 i2"
sorry

mtheorem nat_d_th_45:
" for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds i -'XREAL-0K1 \<two>\<^sub>M =XBOOLE-0R4 (i -'XREAL-0K1 \<one>\<^sub>M)-'XREAL-0K1 \<one>\<^sub>M"
sorry

mtheorem nat_d_th_46:
" for i1 be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for i2 be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds i1 +NAT-1K1 \<one>\<^sub>M <=XXREAL-0R1 i2 implies (i1 -'XREAL-0K1 \<one>\<^sub>M <XXREAL-0R3 i2 & i1 -'XREAL-0K1 \<two>\<^sub>M <XXREAL-0R3 i2) & i1 <=XXREAL-0R1 i2"
sorry

mtheorem nat_d_th_47:
" for i1 be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for i2 be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds i1 +NAT-1K1 \<two>\<^sub>M <=XXREAL-0R1 i2 or (i1 +NAT-1K1 \<one>\<^sub>M)+NAT-1K1 \<one>\<^sub>M <=XXREAL-0R1 i2 implies ((((((((i1 +NAT-1K1 \<one>\<^sub>M <XXREAL-0R3 i2 & (i1 +NAT-1K1 \<one>\<^sub>M)-'NAT-DK9 \<one>\<^sub>M <XXREAL-0R3 i2) & (i1 +NAT-1K1 \<one>\<^sub>M)-'NAT-DK9 \<two>\<^sub>M <XXREAL-0R3 i2) & i1 +NAT-1K1 \<one>\<^sub>M <=XXREAL-0R1 i2) & (i1 -'XREAL-0K1 \<one>\<^sub>M)+XCMPLX-0K2 \<one>\<^sub>M <XXREAL-0R3 i2) & ((i1 -'XREAL-0K1 \<one>\<^sub>M)+XCMPLX-0K2 \<one>\<^sub>M)-'XREAL-0K1 \<one>\<^sub>M <XXREAL-0R3 i2) & i1 <XXREAL-0R3 i2) & i1 -'XREAL-0K1 \<one>\<^sub>M <XXREAL-0R3 i2) & i1 -'XREAL-0K1 \<two>\<^sub>M <XXREAL-0R3 i2) & i1 <=XXREAL-0R1 i2"
sorry

mtheorem nat_d_th_48:
" for i1 be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for i2 be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds i1 <=XXREAL-0R1 i2 or i1 <=XXREAL-0R1 i2 -'XREAL-0K1 \<one>\<^sub>M implies ((((i1 <XXREAL-0R3 i2 +NAT-1K1 \<one>\<^sub>M & i1 <=XXREAL-0R1 i2 +NAT-1K1 \<one>\<^sub>M) & i1 <XXREAL-0R3 (i2 +NAT-1K1 \<one>\<^sub>M)+NAT-1K1 \<one>\<^sub>M) & i1 <=XXREAL-0R1 (i2 +NAT-1K1 \<one>\<^sub>M)+NAT-1K1 \<one>\<^sub>M) & i1 <XXREAL-0R3 i2 +NAT-1K1 \<two>\<^sub>M) & i1 <=XXREAL-0R1 i2 +NAT-1K1 \<two>\<^sub>M"
sorry

mtheorem nat_d_th_49:
" for i1 be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for i2 be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds i1 <XXREAL-0R3 i2 or i1 +NAT-1K1 \<one>\<^sub>M <=XXREAL-0R1 i2 implies i1 <=XXREAL-0R1 i2 -'XREAL-0K1 \<one>\<^sub>M"
sorry

mtheorem nat_d_th_50:
" for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for i1 be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for i2 be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds i >=XXREAL-0R2 i1 implies i >=XXREAL-0R2 i1 -'XREAL-0K1 i2"
sorry

mtheorem nat_d_th_51:
" for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for i1 be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds \<one>\<^sub>M <=XXREAL-0R1 i & \<one>\<^sub>M <=XXREAL-0R1 i1 -'XREAL-0K1 i implies i1 -'XREAL-0K1 i <XXREAL-0R3 i1"
sorry

mtheorem nat_d_th_52:
" for k be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for j be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds i -'XREAL-0K1 k <=XXREAL-0R1 j implies i <=XXREAL-0R1 j +XCMPLX-0K2 k"
sorry

mtheorem nat_d_th_53:
" for k be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for j be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds i <=XXREAL-0R1 j +XCMPLX-0K2 k implies i -'XREAL-0K1 k <=XXREAL-0R1 j"
sorry

mtheorem nat_d_th_54:
" for k be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for j be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds i <=XXREAL-0R1 j -'XREAL-0K1 k & k <=XXREAL-0R1 j implies i +XCMPLX-0K2 k <=XXREAL-0R1 j"
sorry

mtheorem nat_d_th_55:
" for k be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for j be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds j +XCMPLX-0K2 k <=XXREAL-0R1 i implies k <=XXREAL-0R1 i -'XREAL-0K1 j"
sorry

mtheorem nat_d_th_56:
" for k be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for j be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds k <=XXREAL-0R1 i & i <XXREAL-0R3 j implies i -'XREAL-0K1 k <XXREAL-0R3 j -'XREAL-0K1 k"
sorry

mtheorem nat_d_th_57:
" for k be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for j be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds i <XXREAL-0R3 j & k <XXREAL-0R3 j implies i -'XREAL-0K1 k <XXREAL-0R3 j -'XREAL-0K1 k"
sorry

mtheorem nat_d_th_58:
" for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for j be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds i <=XXREAL-0R1 j implies j -'XREAL-0K1 (j -'XREAL-0K1 i) =HIDDENR1 i"
sorry

mtheorem nat_d_th_59:
" for k be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for n be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds n <XXREAL-0R3 k implies (k -'XREAL-0K1 (n +NAT-1K1 \<one>\<^sub>M))+XCMPLX-0K2 \<one>\<^sub>M =XBOOLE-0R4 k -'XREAL-0K1 n"
sorry

mtheorem nat_d_th_60:
" for A be finiteFINSET-1V1\<bar>setHIDDENM2 holds A be trivialSUBSET-1V2 iff cardCARD-1K4 A <XXREAL-0R3 \<two>\<^sub>M"
sorry

mtheorem nat_d_th_61:
" for n be IntegerINT-1M1 holds  for a be IntegerINT-1M1 holds  for k be IntegerINT-1M1 holds (n <>HIDDENR2 0NUMBERSK6 implies (a +XCMPLX-0K2 n *XCMPLX-0K3 k)divINT-1K5 n =HIDDENR1 (a divINT-1K5 n)+XCMPLX-0K2 k) & (a +XCMPLX-0K2 n *XCMPLX-0K3 k)modINT-1K6 n =HIDDENR1 a modINT-1K6 n"
sorry

mtheorem nat_d_th_62:
" for n be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds n >XXREAL-0R4 0NUMBERSK6 implies ( for a be IntegerINT-1M1 holds a modINT-1K6 n >=XXREAL-0R2 0NUMBERSK6 & a modINT-1K6 n <XXREAL-0R3 n)"
sorry

mtheorem nat_d_th_63:
" for n be IntegerINT-1M1 holds  for a be IntegerINT-1M1 holds (0NUMBERSK6 <=XXREAL-0R1 a & a <XXREAL-0R3 n implies a modINT-1K6 n =HIDDENR1 a) & (0NUMBERSK6 >XXREAL-0R4 a & a >=XXREAL-0R2 -XCMPLX-0K4 n implies a modINT-1K6 n =HIDDENR1 n +XCMPLX-0K2 a)"
sorry

mtheorem nat_d_th_64:
" for n be IntegerINT-1M1 holds  for a be IntegerINT-1M1 holds  for b be IntegerINT-1M1 holds (n <>HIDDENR2 0NUMBERSK6 & a modINT-1K6 n =HIDDENR1 b modINT-1K6 n implies (a,b)are-congruent-modINT-1R3 n) & ((a,b)are-congruent-modINT-1R3 n implies a modINT-1K6 n =HIDDENR1 b modINT-1K6 n)"
sorry

mtheorem nat_d_th_65:
" for n be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for a be IntegerINT-1M1 holds (a modINT-1K6 n)modINT-1K6 n =HIDDENR1 a modINT-1K6 n"
sorry

mtheorem nat_d_th_66:
" for n be IntegerINT-1M1 holds  for a be IntegerINT-1M1 holds  for b be IntegerINT-1M1 holds (a +XCMPLX-0K2 b)modINT-1K6 n =HIDDENR1 ((a modINT-1K6 n)+XCMPLX-0K2 (b modINT-1K6 n))modINT-1K6 n"
sorry

mtheorem nat_d_th_67:
" for n be IntegerINT-1M1 holds  for a be IntegerINT-1M1 holds  for b be IntegerINT-1M1 holds a *XCMPLX-0K3 b modINT-1K6 n =HIDDENR1 (a modINT-1K6 n)*XCMPLX-0K3 (b modINT-1K6 n) modINT-1K6 n"
sorry

(*\$N Bezout's identity*)
(*\$N Bezout's lemma*)
mtheorem nat_d_th_68:
" for a be IntegerINT-1M1 holds  for b be IntegerINT-1M1 holds  ex s be IntegerINT-1M1 st  ex t be IntegerINT-1M1 st a gcdINT-2K3 b =XBOOLE-0R4 s *XCMPLX-0K3 a +XCMPLX-0K2 t *XCMPLX-0K3 b"
sorry

mtheorem nat_d_th_69:
" for k be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for n be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds n modNAT-DK2 k =XBOOLE-0R4 k -XCMPLX-0K6 \<one>\<^sub>M implies (n +NAT-1K1 \<one>\<^sub>M)modNAT-DK2 k =XBOOLE-0R4 0NUMBERSK6"
sorry

mtheorem nat_d_th_70:
" for k be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for n be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds n modNAT-DK2 k <XXREAL-0R3 k -XCMPLX-0K6 \<one>\<^sub>M implies (n +NAT-1K1 \<one>\<^sub>M)modNAT-DK2 k =XBOOLE-0R4 (n modNAT-DK2 k)+NAT-1K1 \<one>\<^sub>M"
sorry

mtheorem nat_d_th_71:
" for i be IntegerINT-1M1 holds  for n be NatNAT-1M1 holds i *XCMPLX-0K3 n modINT-1K6 n =HIDDENR1 0NUMBERSK6"
sorry

mtheorem nat_d_th_72:
" for m be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for n be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds m -XCMPLX-0K6 n >=XXREAL-0R2 0NUMBERSK6 implies (m -'XREAL-0K1 n)+XCMPLX-0K2 n =HIDDENR1 m"
sorry

end
