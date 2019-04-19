theory nat_1
  imports card_1 pboole axioms xreal_1
   "../mizar_extension/E_number"
begin
(*begin*)
mtheorem nat_1_cl_1:
"cluster naturalORDINAL1V7 for objectHIDDENM1"
proof
(*existence*)
  show " ex it be objectHIDDENM1 st it be naturalORDINAL1V7"
sorry
qed "sorry"

syntax NAT_1M1 :: "Ty" ("NatNAT-1M1" 70)
translations "NatNAT-1M1" \<rightharpoonup> "naturalORDINAL1V7\<bar>numberORDINAL1M2"

reserve x for "RealXREAL-0M1"
reserve p, k, l, m, n, s, h, i, j, k1, t, t1 for "NatNAT-1M1"
reserve X for "SubsetSUBSET-1M2-of REALNUMBERSK2"
mtheorem nat_1_th_1:
" for X be SubsetSUBSET-1M2-of REALNUMBERSK2 holds 0NUMBERSK6 inTARSKIR2 X & ( for x be RealXREAL-0M1 holds x inHIDDENR3 X implies x +XCMPLX-0K2 \<one>\<^sub>M inTARSKIR2 X) implies ( for n be NatNAT-1M1 holds n inTARSKIR2 X)"
sorry

mtheorem nat_1_cl_2:
  mlet "n be naturalORDINAL1V7\<bar>NumberORDINAL1M1", "k be naturalORDINAL1V7\<bar>NumberORDINAL1M1"
"cluster n +XCMPLX-0K2 k as-term-is naturalORDINAL1V7"
proof
(*coherence*)
  show "n +XCMPLX-0K2 k be naturalORDINAL1V7"
sorry
qed "sorry"

abbreviation(input) NAT_1K1(" _ +NAT-1K1  _ " [132,132]132) where
  "n +NAT-1K1 k \<equiv> n +XCMPLX-0K2 k"

mtheorem nat_1_add_1:
  mlet "n be naturalORDINAL1V7\<bar>NumberORDINAL1M1", "k be ElementSUBSET-1M1-of NATNUMBERSK1"
"cluster n +XCMPLX-0K2 k as-term-is ElementSUBSET-1M1-of NATNUMBERSK1"
proof
(*coherence*)
  show "n +XCMPLX-0K2 k be ElementSUBSET-1M1-of NATNUMBERSK1"
    using ordinal1_def_12 sorry
qed "sorry"

(*\$CS*)
(*\$N The Principle of Mathematical Induction*)
theorem nat_1_sch_2:
  fixes Pp1 
  assumes
    A1: "Pp1(0NUMBERSK6)" and
   A2: " for k be NatNAT-1M1 holds Pp1(k) implies Pp1(k +NAT-1K1 \<one>\<^sub>M)"
  shows " for k be NatNAT-1M1 holds Pp1(k)"
sorry

mtheorem nat_1_cl_3:
  mlet "n be naturalORDINAL1V7\<bar>NumberORDINAL1M1", "k be naturalORDINAL1V7\<bar>NumberORDINAL1M1"
"cluster n *XCMPLX-0K3 k as-term-is naturalORDINAL1V7"
proof
(*coherence*)
  show "n *XCMPLX-0K3 k be naturalORDINAL1V7"
sorry
qed "sorry"

abbreviation(input) NAT_1K2(" _ *NAT-1K2  _ " [164,164]164) where
  "n *NAT-1K2 k \<equiv> n *XCMPLX-0K3 k"

mtheorem nat_1_add_2:
  mlet "n be ElementSUBSET-1M1-of NATNUMBERSK1", "k be ElementSUBSET-1M1-of NATNUMBERSK1"
"cluster n *XCMPLX-0K3 k as-term-is ElementSUBSET-1M1-of NATNUMBERSK1"
proof
(*coherence*)
  show "n *XCMPLX-0K3 k be ElementSUBSET-1M1-of NATNUMBERSK1"
    using ordinal1_def_12 sorry
qed "sorry"

mtheorem nat_1_th_2:
" for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds 0NUMBERSK6 <=XXREAL-0R1 i"
sorry

mtheorem nat_1_th_3:
" for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds 0NUMBERSK6 <>HIDDENR2 i implies 0NUMBERSK6 <XXREAL-0R3 i"
  using nat_1_th_2 sorry

mtheorem nat_1_th_4:
" for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for j be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for h be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds i <=XXREAL-0R1 j implies i *XCMPLX-0K3 h <=XXREAL-0R1 j *XCMPLX-0K3 h"
sorry

mtheorem nat_1_th_5:
" for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds 0NUMBERSK6 <XXREAL-0R3 i +NAT-1K1 \<one>\<^sub>M"
sorry

mtheorem nat_1_th_6:
" for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds i =HIDDENR1 0NUMBERSK6 or ( ex k be NatNAT-1M1 st i =HIDDENR1 k +NAT-1K1 \<one>\<^sub>M)"
sorry

mtheorem nat_1_th_7:
" for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for j be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds i +XCMPLX-0K2 j =XBOOLE-0R4 0NUMBERSK6 implies i =HIDDENR1 0NUMBERSK6 & j =HIDDENR1 0NUMBERSK6"
sorry

mtheorem nat_1_cl_4:
"cluster zeroORDINAL1V8\<bar>naturalORDINAL1V7 for objectHIDDENM1"
proof
(*existence*)
  show " ex it be objectHIDDENM1 st it be zeroORDINAL1V8\<bar>naturalORDINAL1V7"
sorry
qed "sorry"

mtheorem nat_1_cl_5:
"cluster  non zeroORDINAL1V8\<bar>naturalORDINAL1V7 for objectHIDDENM1"
proof
(*existence*)
  show " ex it be objectHIDDENM1 st it be  non zeroORDINAL1V8\<bar>naturalORDINAL1V7"
sorry
qed "sorry"

mtheorem nat_1_cl_6:
  mlet "m be naturalORDINAL1V7\<bar>NumberORDINAL1M1", "n be  non zeroORDINAL1V8\<bar>naturalORDINAL1V7\<bar>NumberORDINAL1M1"
"cluster m +XCMPLX-0K2 n as-term-is  non zeroORDINAL1V8"
proof
(*coherence*)
  show "m +XCMPLX-0K2 n be  non zeroORDINAL1V8"
    using nat_1_th_7 sorry
qed "sorry"

mtheorem nat_1_cl_7:
  mlet "m be naturalORDINAL1V7\<bar>NumberORDINAL1M1", "n be  non zeroORDINAL1V8\<bar>naturalORDINAL1V7\<bar>NumberORDINAL1M1"
"cluster n +XCMPLX-0K2 m as-term-is  non zeroORDINAL1V8"
proof
(*coherence*)
  show "n +XCMPLX-0K2 m be  non zeroORDINAL1V8"
     sorry
qed "sorry"

theorem nat_1_sch_3:
  fixes Nf0 Ff2 Pp2 
  assumes
[ty]: "Nf0 be NatNAT-1M1" and
  [ty_func]: "\<And> x1 x2. x1 be NatNAT-1M1 \<Longrightarrow> x2 be NatNAT-1M1 \<Longrightarrow> Ff2(x1,x2) be NatNAT-1M1" and
   A1: " for k be NatNAT-1M1 holds  for n be NatNAT-1M1 holds Pp2(k,n) iff k =XBOOLE-0R4 0NUMBERSK6 & n =XBOOLE-0R4 Nf0 or ( ex m be NatNAT-1M1 st  ex l be NatNAT-1M1 st (k =XBOOLE-0R4 m +NAT-1K1 \<one>\<^sub>M & Pp2(m,l)) & n =XBOOLE-0R4 Ff2(k,l))"
  shows "( for k be NatNAT-1M1 holds  ex n be NatNAT-1M1 st Pp2(k,n)) & ( for k be NatNAT-1M1 holds  for n be NatNAT-1M1 holds  for m be NatNAT-1M1 holds Pp2(k,n) & Pp2(k,m) implies n =XBOOLE-0R4 m)"
sorry

mtheorem nat_1_th_8:
" for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for j be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds i <=XXREAL-0R1 j +NAT-1K1 \<one>\<^sub>M implies i <=XXREAL-0R1 j or i =HIDDENR1 j +NAT-1K1 \<one>\<^sub>M"
sorry

mtheorem nat_1_th_9:
" for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for j be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds i <=XXREAL-0R1 j & j <=XXREAL-0R1 i +NAT-1K1 \<one>\<^sub>M implies i =HIDDENR1 j or j =HIDDENR1 i +NAT-1K1 \<one>\<^sub>M"
sorry

mtheorem nat_1_th_10:
" for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for j be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds i <=XXREAL-0R1 j implies ( ex k be NatNAT-1M1 st j =HIDDENR1 i +XCMPLX-0K2 k)"
sorry

mtheorem nat_1_th_11:
" for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for j be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds i <=XXREAL-0R1 i +XCMPLX-0K2 j"
sorry

theorem nat_1_sch_4:
  fixes Pp1 
  assumes
    A1: " for k be NatNAT-1M1 holds ( for n be NatNAT-1M1 holds n <XXREAL-0R3 k implies Pp1(n)) implies Pp1(k)"
  shows " for k be NatNAT-1M1 holds Pp1(k)"
sorry

theorem nat_1_sch_5:
  fixes Pp1 
  assumes
    A1: " ex k be NatNAT-1M1 st Pp1(k)"
  shows " ex k be NatNAT-1M1 st Pp1(k) & ( for n be NatNAT-1M1 holds Pp1(n) implies k <=XXREAL-0R1 n)"
sorry

theorem nat_1_sch_6:
  fixes Nf0 Pp1 
  assumes
[ty]: "Nf0 be NatNAT-1M1" and
   A1: " for k be NatNAT-1M1 holds Pp1(k) implies k <=XXREAL-0R1 Nf0" and
   A2: " ex k be NatNAT-1M1 st Pp1(k)"
  shows " ex k be NatNAT-1M1 st Pp1(k) & ( for n be NatNAT-1M1 holds Pp1(n) implies n <=XXREAL-0R1 k)"
sorry

mtheorem nat_1_th_12:
" for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for j be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for h be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds i <=XXREAL-0R1 j implies i <=XXREAL-0R1 j +XCMPLX-0K2 h"
sorry

mtheorem nat_1_th_13:
" for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for j be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds i <XXREAL-0R3 j +NAT-1K1 \<one>\<^sub>M iff i <=XXREAL-0R1 j"
sorry

mtheorem nat_1_th_14:
" for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds i <XXREAL-0R3 \<one>\<^sub>M implies i =HIDDENR1 0NUMBERSK6"
sorry

mtheorem nat_1_th_15:
" for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for j be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds i *XCMPLX-0K3 j =XBOOLE-0R4 \<one>\<^sub>M implies i =HIDDENR1 \<one>\<^sub>M"
sorry

mtheorem nat_1_th_16:
" for n be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for k be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds k <>HIDDENR2 0NUMBERSK6 implies n <XXREAL-0R3 n +XCMPLX-0K2 k"
sorry

theorem nat_1_sch_7:
  fixes Pp1 
  assumes
    A1: " ex k be NatNAT-1M1 st Pp1(k)" and
   A2: " for k be NatNAT-1M1 holds k <>HIDDENR2 0NUMBERSK6 & Pp1(k) implies ( ex n be NatNAT-1M1 st n <XXREAL-0R3 k & Pp1(n))"
  shows "Pp1(0NUMBERSK6)"
sorry

mtheorem nat_1_th_17:
" for m be NatNAT-1M1 holds 0NUMBERSK6 <XXREAL-0R3 m implies ( for n be NatNAT-1M1 holds  ex k be NatNAT-1M1 st  ex t be NatNAT-1M1 st n =XBOOLE-0R4 m *XCMPLX-0K3 k +XCMPLX-0K2 t & t <XXREAL-0R3 m)"
sorry

mtheorem nat_1_th_18:
" for n be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for m be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for k be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for t be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for k1 be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for t1 be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds ((n =HIDDENR1 m *XCMPLX-0K3 k +XCMPLX-0K2 t & t <XXREAL-0R3 m) & n =HIDDENR1 m *XCMPLX-0K3 k1 +XCMPLX-0K2 t1) & t1 <XXREAL-0R3 m implies k =HIDDENR1 k1 & t =HIDDENR1 t1"
sorry

mtheorem nat_1_cl_8:
"cluster note-that ordinalORDINAL1V3 for naturalORDINAL1V7\<bar>NumberORDINAL1M1"
proof
(*coherence*)
  show " for it be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds it be ordinalORDINAL1V3"
sorry
qed "sorry"

mtheorem nat_1_cl_9:
"cluster  non emptyXBOOLE-0V1\<bar>ordinalORDINAL1V3 for SubsetSUBSET-1M2-of REALNUMBERSK2"
proof
(*existence*)
  show " ex it be SubsetSUBSET-1M2-of REALNUMBERSK2 st it be  non emptyXBOOLE-0V1\<bar>ordinalORDINAL1V3"
sorry
qed "sorry"

mtheorem nat_1_th_19:
" for k be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for n be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds k <XXREAL-0R3 k +XCMPLX-0K2 n iff \<one>\<^sub>M <=XXREAL-0R1 n"
sorry

mtheorem nat_1_th_20:
" for k be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for n be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds k <XXREAL-0R3 n implies n -XCMPLX-0K6 \<one>\<^sub>M be ElementSUBSET-1M1-of NATNUMBERSK1"
sorry

mtheorem nat_1_th_21:
" for k be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for n be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds k <=XXREAL-0R1 n implies n -XCMPLX-0K6 k be ElementSUBSET-1M1-of NATNUMBERSK1"
sorry

(*begin*)
mtheorem nat_1_th_22:
" for m be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for n be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds m <XXREAL-0R3 n +NAT-1K1 \<one>\<^sub>M implies m <XXREAL-0R3 n or m =HIDDENR1 n"
sorry

mtheorem nat_1_th_23:
" for k be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds k <XXREAL-0R3 \<two>\<^sub>M implies k =HIDDENR1 0NUMBERSK6 or k =HIDDENR1 \<one>\<^sub>M"
sorry

mtheorem nat_1_cl_10:
"cluster  non zeroORDINAL1V8 for ElementSUBSET-1M1-of NATNUMBERSK1"
proof
(*existence*)
  show " ex it be ElementSUBSET-1M1-of NATNUMBERSK1 st it be  non zeroORDINAL1V8"
sorry
qed "sorry"

mtheorem nat_1_cl_11:
"cluster note-that  non negativeXXREAL-0V3 for ElementSUBSET-1M1-of NATNUMBERSK1"
proof
(*coherence*)
  show " for it be ElementSUBSET-1M1-of NATNUMBERSK1 holds it be  non negativeXXREAL-0V3"
    using nat_1_th_2 sorry
qed "sorry"

mtheorem nat_1_cl_12:
"cluster note-that  non negativeXXREAL-0V3 for naturalORDINAL1V7\<bar>NumberORDINAL1M1"
proof
(*coherence*)
  show " for it be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds it be  non negativeXXREAL-0V3"
    using nat_1_th_2 sorry
qed "sorry"

mtheorem nat_1_th_24:
" for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for j be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for h be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds i <>HIDDENR2 0NUMBERSK6 & h =HIDDENR1 j *XCMPLX-0K3 i implies j <=XXREAL-0R1 h"
sorry

theorem nat_1_sch_8:
  fixes Mf0 Pp1 
  assumes
[ty]: "Mf0 be NatNAT-1M1" and
   A1: "Pp1(Mf0)" and
   A2: " for j be NatNAT-1M1 holds Mf0 <=XXREAL-0R1 j implies (Pp1(j) implies Pp1(j +NAT-1K1 \<one>\<^sub>M))"
  shows " for i be NatNAT-1M1 holds Mf0 <=XXREAL-0R1 i implies Pp1(i)"
sorry

theorem nat_1_sch_9:
  fixes af0 Pp1 
  assumes
[ty]: "af0 be NatNAT-1M1" and
   A1: " for k be NatNAT-1M1 holds k >=XXREAL-0R2 af0 & ( for n be NatNAT-1M1 holds n >=XXREAL-0R2 af0 & n <XXREAL-0R3 k implies Pp1(n)) implies Pp1(k)"
  shows " for k be NatNAT-1M1 holds k >=XXREAL-0R2 af0 implies Pp1(k)"
sorry

mtheorem nat_1_th_25:
" for n be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds n <=XXREAL-0R1 \<one>\<^sub>M implies n =HIDDENR1 0NUMBERSK6 or n =HIDDENR1 \<one>\<^sub>M"
sorry

theorem nat_1_sch_10:
  fixes Pp1 
  assumes
    A1: "Pp1(\<one>\<^sub>M)" and
   A2: " for k be  non zeroORDINAL1V8\<bar>NatNAT-1M1 holds Pp1(k) implies Pp1(k +NAT-1K1 \<one>\<^sub>M)"
  shows " for k be  non zeroORDINAL1V8\<bar>NatNAT-1M1 holds Pp1(k)"
sorry

mdef nat_1_def_1 ("min*NAT-1K3  _ " [164]164 ) where
  mlet "A be setHIDDENM2"
"func min*NAT-1K3 A \<rightarrow> ElementSUBSET-1M1-of NATNUMBERSK1 means
  \<lambda>it. it inTARSKIR2 A & ( for k be NatNAT-1M1 holds k inTARSKIR2 A implies it <=XXREAL-0R1 k) if A be  non emptyXBOOLE-0V1\<bar>SubsetSUBSET-1M2-of NATNUMBERSK1 otherwise \<lambda>it. it =XBOOLE-0R4 0NUMBERSK6"
proof-
  (*existence*)
    show "(A be  non emptyXBOOLE-0V1\<bar>SubsetSUBSET-1M2-of NATNUMBERSK1 implies ( ex it be ElementSUBSET-1M1-of NATNUMBERSK1 st it inTARSKIR2 A & ( for k be NatNAT-1M1 holds k inTARSKIR2 A implies it <=XXREAL-0R1 k))) & ( not A be  non emptyXBOOLE-0V1\<bar>SubsetSUBSET-1M2-of NATNUMBERSK1 implies ( ex it be ElementSUBSET-1M1-of NATNUMBERSK1 st it =XBOOLE-0R4 0NUMBERSK6))"
sorry
  (*uniqueness*)
    show " for it1 be ElementSUBSET-1M1-of NATNUMBERSK1 holds  for it2 be ElementSUBSET-1M1-of NATNUMBERSK1 holds (A be  non emptyXBOOLE-0V1\<bar>SubsetSUBSET-1M2-of NATNUMBERSK1 implies ((it1 inTARSKIR2 A & ( for k be NatNAT-1M1 holds k inTARSKIR2 A implies it1 <=XXREAL-0R1 k)) & (it2 inTARSKIR2 A & ( for k be NatNAT-1M1 holds k inTARSKIR2 A implies it2 <=XXREAL-0R1 k)) implies it1 =HIDDENR1 it2)) & ( not A be  non emptyXBOOLE-0V1\<bar>SubsetSUBSET-1M2-of NATNUMBERSK1 implies (it1 =XBOOLE-0R4 0NUMBERSK6 & it2 =XBOOLE-0R4 0NUMBERSK6 implies it1 =HIDDENR1 it2))"
sorry
  (*consistency*)
    show " for it be ElementSUBSET-1M1-of NATNUMBERSK1 holds  True "
       sorry
qed "sorry"

reserve x for "objectHIDDENM1"
reserve X, Y, Z for "setHIDDENM2"
(*\$CT 12*)
mtheorem nat_1_th_38:
" for n be NatNAT-1M1 holds succORDINAL1K1 (SegmCARD-1K5 n) =XBOOLE-0R4 SegmCARD-1K5 (n +NAT-1K1 \<one>\<^sub>M)"
sorry

mtheorem nat_1_th_39:
" for m be NatNAT-1M1 holds  for n be NatNAT-1M1 holds n <=XXREAL-0R1 m iff SegmCARD-1K5 n c=ORDINAL1R1 SegmCARD-1K5 m"
sorry

mtheorem nat_1_th_40:
" for m be NatNAT-1M1 holds  for n be NatNAT-1M1 holds cardCARD-1K4 (SegmCARD-1K5 n) c=ORDINAL1R1 cardCARD-1K4 (SegmCARD-1K5 m) iff n <=XXREAL-0R1 m"
  using nat_1_th_39 sorry

mtheorem nat_1_th_41:
" for m be NatNAT-1M1 holds  for n be NatNAT-1M1 holds cardCARD-1K4 (SegmCARD-1K5 n) inTARSKIR2 cardCARD-1K4 (SegmCARD-1K5 m) iff n <XXREAL-0R3 m"
sorry

reserve M, N for "CardinalCARD-1M1"
mtheorem nat_1_th_42:
" for n be NatNAT-1M1 holds nextcardCARD-1K2 (cardCARD-1K4 (SegmCARD-1K5 n)) =XBOOLE-0R4 cardCARD-1K4 (SegmCARD-1K5 (n +NAT-1K1 \<one>\<^sub>M))"
sorry

(*\$CD*)
mtheorem nat_1_th_43:
" for X be finiteFINSET-1V1\<bar>setHIDDENM2 holds  for Y be finiteFINSET-1V1\<bar>setHIDDENM2 holds X c=TARSKIR1 Y implies cardCARD-1K4 X <=XXREAL-0R1 cardCARD-1K4 Y"
sorry

mtheorem nat_1_th_44:
" for k be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for n be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds k inHIDDENR3 SegmCARD-1K5 n iff k <XXREAL-0R3 n"
sorry

mtheorem nat_1_th_45:
" for n be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds n inHIDDENR3 SegmCARD-1K5 (n +NAT-1K1 \<one>\<^sub>M)"
sorry

(*\$CT*)
syntax NAT_1M2 :: " Set \<Rightarrow> Ty" ("sequenceNAT-1M2-of  _ " [70]70)
translations "sequenceNAT-1M2-of X" \<rightharpoonup> "FunctionFUNCT-2M1-of(NATNUMBERSK1,X)"

theorem nat_1_sch_11:
  fixes Af0 Gf2 
  assumes
[ty]: "Af0 be objectHIDDENM1" and
  [ty_func]: "\<And> x1 x2. x1 be objectHIDDENM1 \<Longrightarrow> x2 be objectHIDDENM1 \<Longrightarrow> Gf2(x1,x2) be objectHIDDENM1"
  shows " ex f be FunctionFUNCT-1M1 st (domRELAT-1K1 f =XBOOLE-0R4 NATNUMBERSK1 & f .FUNCT-1K1 (0NUMBERSK6) =HIDDENR1 Af0) & ( for n be NatNAT-1M1 holds f .FUNCT-1K1 (n +NAT-1K1 \<one>\<^sub>M) =HIDDENR1 Gf2(n,f .FUNCT-1K1 n))"
sorry

theorem nat_1_sch_12:
  fixes Df0 Af0 Gf2 
  assumes
[ty]: "Df0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
  [ty]: "Af0 be ElementSUBSET-1M1-of Df0" and
  [ty_func]: "\<And> x1 x2. x1 be objectHIDDENM1 \<Longrightarrow> x2 be objectHIDDENM1 \<Longrightarrow> Gf2(x1,x2) be ElementSUBSET-1M1-of Df0"
  shows " ex f be sequenceNAT-1M2-of Df0 st f .FUNCT-2K3\<^bsub>(omegaORDINAL1K4,Df0)\<^esub> (0NUMBERSK6) =XBOOLE-0R4 Af0 & ( for n be NatNAT-1M1 holds f .FUNCT-2K3\<^bsub>(NATNUMBERSK1,Df0)\<^esub> (n +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 Gf2(n,f .FUNCT-1K1 n))"
sorry

theorem nat_1_sch_13:
  fixes Af0 Ff0 Gf0 Pp3 
  assumes
[ty]: "Af0 be objectHIDDENM1" and
  [ty]: "Ff0 be FunctionFUNCT-1M1" and
  [ty]: "Gf0 be FunctionFUNCT-1M1" and
   A1: "domRELAT-1K1 Ff0 =XBOOLE-0R4 NATNUMBERSK1" and
   A2: "Ff0 .FUNCT-1K1 (0NUMBERSK6) =HIDDENR1 Af0" and
   A3: " for n be NatNAT-1M1 holds Pp3(n,Ff0 .FUNCT-1K1 n,Ff0 .FUNCT-1K1 (n +NAT-1K1 \<one>\<^sub>M))" and
   A4: "domRELAT-1K1 Gf0 =XBOOLE-0R4 NATNUMBERSK1" and
   A5: "Gf0 .FUNCT-1K1 (0NUMBERSK6) =HIDDENR1 Af0" and
   A6: " for n be NatNAT-1M1 holds Pp3(n,Gf0 .FUNCT-1K1 n,Gf0 .FUNCT-1K1 (n +NAT-1K1 \<one>\<^sub>M))" and
   A7: " for n be NatNAT-1M1 holds  for x be setHIDDENM2 holds  for y1 be setHIDDENM2 holds  for y2 be setHIDDENM2 holds Pp3(n,x,y1) & Pp3(n,x,y2) implies y1 =XBOOLE-0R4 y2"
  shows "Ff0 =FUNCT-1R1 Gf0"
sorry

theorem nat_1_sch_14:
  fixes Df0 Af0 Ff0 Gf0 Pp3 
  assumes
[ty]: "Df0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
  [ty]: "Af0 be ElementSUBSET-1M1-of Df0" and
  [ty]: "Ff0 be sequenceNAT-1M2-of Df0" and
  [ty]: "Gf0 be sequenceNAT-1M2-of Df0" and
   A1: "Ff0 .FUNCT-2K3\<^bsub>(omegaORDINAL1K4,Df0)\<^esub> (0NUMBERSK6) =XBOOLE-0R4 Af0" and
   A2: " for n be NatNAT-1M1 holds Pp3(n,Ff0 .FUNCT-1K1 n,Ff0 .FUNCT-2K3\<^bsub>(NATNUMBERSK1,Df0)\<^esub> (n +NAT-1K1 \<one>\<^sub>M))" and
   A3: "Gf0 .FUNCT-2K3\<^bsub>(omegaORDINAL1K4,Df0)\<^esub> (0NUMBERSK6) =XBOOLE-0R4 Af0" and
   A4: " for n be NatNAT-1M1 holds Pp3(n,Gf0 .FUNCT-1K1 n,Gf0 .FUNCT-2K3\<^bsub>(NATNUMBERSK1,Df0)\<^esub> (n +NAT-1K1 \<one>\<^sub>M))" and
   A5: " for n be NatNAT-1M1 holds  for x be ElementSUBSET-1M1-of Df0 holds  for y1 be ElementSUBSET-1M1-of Df0 holds  for y2 be ElementSUBSET-1M1-of Df0 holds Pp3(n,x,y1) & Pp3(n,x,y2) implies y1 =XBOOLE-0R4 y2"
  shows "Ff0 =FUNCT-2R2\<^bsub>(NATNUMBERSK1,Df0)\<^esub> Gf0"
sorry

theorem nat_1_sch_15:
  fixes Af0 RecFunf2 Ff0 Gf0 
  assumes
[ty]: "Af0 be objectHIDDENM1" and
  [ty_func]: "\<And> x1 x2. x1 be objectHIDDENM1 \<Longrightarrow> x2 be objectHIDDENM1 \<Longrightarrow> RecFunf2(x1,x2) be objectHIDDENM1" and
  [ty]: "Ff0 be FunctionFUNCT-1M1" and
  [ty]: "Gf0 be FunctionFUNCT-1M1" and
   A1: "domRELAT-1K1 Ff0 =XBOOLE-0R4 NATNUMBERSK1" and
   A2: "Ff0 .FUNCT-1K1 (0NUMBERSK6) =HIDDENR1 Af0" and
   A3: " for n be NatNAT-1M1 holds Ff0 .FUNCT-1K1 (n +NAT-1K1 \<one>\<^sub>M) =HIDDENR1 RecFunf2(n,Ff0 .FUNCT-1K1 n)" and
   A4: "domRELAT-1K1 Gf0 =XBOOLE-0R4 NATNUMBERSK1" and
   A5: "Gf0 .FUNCT-1K1 (0NUMBERSK6) =HIDDENR1 Af0" and
   A6: " for n be NatNAT-1M1 holds Gf0 .FUNCT-1K1 (n +NAT-1K1 \<one>\<^sub>M) =HIDDENR1 RecFunf2(n,Gf0 .FUNCT-1K1 n)"
  shows "Ff0 =FUNCT-1R1 Gf0"
sorry

theorem nat_1_sch_16:
  fixes Df0 Af0 RecFunf2 Ff0 Gf0 
  assumes
[ty]: "Df0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
  [ty]: "Af0 be ElementSUBSET-1M1-of Df0" and
  [ty_func]: "\<And> x1 x2. x1 be objectHIDDENM1 \<Longrightarrow> x2 be objectHIDDENM1 \<Longrightarrow> RecFunf2(x1,x2) be ElementSUBSET-1M1-of Df0" and
  [ty]: "Ff0 be sequenceNAT-1M2-of Df0" and
  [ty]: "Gf0 be sequenceNAT-1M2-of Df0" and
   A1: "Ff0 .FUNCT-2K3\<^bsub>(omegaORDINAL1K4,Df0)\<^esub> (0NUMBERSK6) =XBOOLE-0R4 Af0" and
   A2: " for n be NatNAT-1M1 holds Ff0 .FUNCT-2K3\<^bsub>(NATNUMBERSK1,Df0)\<^esub> (n +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 RecFunf2(n,Ff0 .FUNCT-1K1 n)" and
   A3: "Gf0 .FUNCT-2K3\<^bsub>(omegaORDINAL1K4,Df0)\<^esub> (0NUMBERSK6) =XBOOLE-0R4 Af0" and
   A4: " for n be NatNAT-1M1 holds Gf0 .FUNCT-2K3\<^bsub>(NATNUMBERSK1,Df0)\<^esub> (n +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 RecFunf2(n,Gf0 .FUNCT-1K1 n)"
  shows "Ff0 =FUNCT-2R2\<^bsub>(NATNUMBERSK1,Df0)\<^esub> Gf0"
sorry

mtheorem nat_1_cl_13:
  mlet "x be naturalORDINAL1V7\<bar>NumberORDINAL1M1", "y be naturalORDINAL1V7\<bar>NumberORDINAL1M1"
"cluster minXXREAL-0K4(x,y) as-term-is naturalORDINAL1V7"
proof
(*coherence*)
  show "minXXREAL-0K4(x,y) be naturalORDINAL1V7"
    using xxreal_0_th_15 sorry
qed "sorry"

mtheorem nat_1_cl_14:
  mlet "x be naturalORDINAL1V7\<bar>NumberORDINAL1M1", "y be naturalORDINAL1V7\<bar>NumberORDINAL1M1"
"cluster maxXXREAL-0K5(x,y) as-term-is naturalORDINAL1V7"
proof
(*coherence*)
  show "maxXXREAL-0K5(x,y) be naturalORDINAL1V7"
    using xxreal_0_th_16 sorry
qed "sorry"

abbreviation(input) NAT_1K4("minNAT-1K4'( _ , _ ')" [0,0]228) where
  "minNAT-1K4(x,y) \<equiv> minXXREAL-0K4(x,y)"

mtheorem nat_1_add_3:
  mlet "x be ElementSUBSET-1M1-of NATNUMBERSK1", "y be ElementSUBSET-1M1-of NATNUMBERSK1"
"cluster minXXREAL-0K4(x,y) as-term-is ElementSUBSET-1M1-of NATNUMBERSK1"
proof
(*coherence*)
  show "minXXREAL-0K4(x,y) be ElementSUBSET-1M1-of NATNUMBERSK1"
    using xxreal_0_th_15 sorry
qed "sorry"

abbreviation(input) NAT_1K5("maxNAT-1K5'( _ , _ ')" [0,0]228) where
  "maxNAT-1K5(x,y) \<equiv> maxXXREAL-0K5(x,y)"

mtheorem nat_1_add_4:
  mlet "x be ElementSUBSET-1M1-of NATNUMBERSK1", "y be ElementSUBSET-1M1-of NATNUMBERSK1"
"cluster maxXXREAL-0K5(x,y) as-term-is ElementSUBSET-1M1-of NATNUMBERSK1"
proof
(*coherence*)
  show "maxXXREAL-0K5(x,y) be ElementSUBSET-1M1-of NATNUMBERSK1"
    using xxreal_0_th_16 sorry
qed "sorry"

theorem nat_1_sch_17:
  fixes Ff1 
  assumes
[ty_func]: "\<And> x1. x1 be NatNAT-1M1 \<Longrightarrow> Ff1(x1) be NatNAT-1M1" and
   A1: " for k be NatNAT-1M1 holds Ff1(k +NAT-1K1 \<one>\<^sub>M) <XXREAL-0R3 Ff1(k) or Ff1(k) =XBOOLE-0R4 0NUMBERSK6"
  shows " ex k be NatNAT-1M1 st Ff1(k) =XBOOLE-0R4 0NUMBERSK6 & ( for n be NatNAT-1M1 holds Ff1(n) =XBOOLE-0R4 0NUMBERSK6 implies k <=XXREAL-0R1 n)"
sorry

mdef nat_1_def_3 (" _ ^'\\NAT-1K6  _ " [164,164]164 ) where
  mlet "s be ManySortedSetPBOOLEM1-of NATNUMBERSK1", "k be naturalORDINAL1V7\<bar>NumberORDINAL1M1"
"func s ^\\NAT-1K6 k \<rightarrow> ManySortedSetPBOOLEM1-of NATNUMBERSK1 means
  \<lambda>it.  for n be NatNAT-1M1 holds it .FUNCT-1K1 n =XBOOLE-0R4 s .FUNCT-1K1 (n +XCMPLX-0K2 k)"
proof-
  (*existence*)
    show " ex it be ManySortedSetPBOOLEM1-of NATNUMBERSK1 st  for n be NatNAT-1M1 holds it .FUNCT-1K1 n =XBOOLE-0R4 s .FUNCT-1K1 (n +XCMPLX-0K2 k)"
sorry
  (*uniqueness*)
    show " for it1 be ManySortedSetPBOOLEM1-of NATNUMBERSK1 holds  for it2 be ManySortedSetPBOOLEM1-of NATNUMBERSK1 holds ( for n be NatNAT-1M1 holds it1 .FUNCT-1K1 n =XBOOLE-0R4 s .FUNCT-1K1 (n +XCMPLX-0K2 k)) & ( for n be NatNAT-1M1 holds it2 .FUNCT-1K1 n =XBOOLE-0R4 s .FUNCT-1K1 (n +XCMPLX-0K2 k)) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mlemma nat_1_lm_1:
" for s be ManySortedSetPBOOLEM1-of NATNUMBERSK1 holds  for k be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds rngFUNCT-1K2 (s ^\\NAT-1K6 k) c=TARSKIR1 rngFUNCT-1K2 s"
sorry

mtheorem nat_1_cl_15:
  mlet "X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "s be X -valuedRELAT-1V5\<bar>ManySortedSetPBOOLEM1-of NATNUMBERSK1", "k be naturalORDINAL1V7\<bar>NumberORDINAL1M1"
"cluster s ^\\NAT-1K6 k as-term-is X -valuedRELAT-1V5"
proof
(*coherence*)
  show "s ^\\NAT-1K6 k be X -valuedRELAT-1V5"
sorry
qed "sorry"

syntax NAT_1K7 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ ^'\\NAT-1K7\<^bsub>'( _ ')\<^esub>  _ " [164,0,164]164)
translations "s ^\\NAT-1K7\<^bsub>(X)\<^esub> k" \<rightharpoonup> "s ^\\NAT-1K6 k"

mtheorem nat_1_add_5:
  mlet "X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "s be sequenceNAT-1M2-of X", "k be NatNAT-1M1"
"cluster s ^\\NAT-1K6 k as-term-is sequenceNAT-1M2-of X"
proof
(*coherence*)
  show "s ^\\NAT-1K6 k be sequenceNAT-1M2-of X"
sorry
qed "sorry"

reserve X for " non emptyXBOOLE-0V1\<bar>setHIDDENM2"
reserve s for "sequenceNAT-1M2-of X"
mtheorem nat_1_th_47:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for s be sequenceNAT-1M2-of X holds s ^\\NAT-1K7\<^bsub>(X)\<^esub> (0NUMBERSK6) =FUNCT-2R2\<^bsub>(NATNUMBERSK1,X)\<^esub> s"
sorry

mtheorem nat_1_th_48:
" for k be NatNAT-1M1 holds  for m be NatNAT-1M1 holds  for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for s be sequenceNAT-1M2-of X holds (s ^\\NAT-1K7\<^bsub>(X)\<^esub> k)^\\NAT-1K7\<^bsub>(X)\<^esub> m =FUNCT-2R2\<^bsub>(NATNUMBERSK1,X)\<^esub> s ^\\NAT-1K7\<^bsub>(X)\<^esub> (k +XCMPLX-0K2 m)"
sorry

mtheorem nat_1_th_49:
" for k be NatNAT-1M1 holds  for m be NatNAT-1M1 holds  for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for s be sequenceNAT-1M2-of X holds (s ^\\NAT-1K7\<^bsub>(X)\<^esub> k)^\\NAT-1K7\<^bsub>(X)\<^esub> m =FUNCT-2R2\<^bsub>(NATNUMBERSK1,X)\<^esub> (s ^\\NAT-1K7\<^bsub>(X)\<^esub> m)^\\NAT-1K7\<^bsub>(X)\<^esub> k"
sorry

mtheorem nat_1_cl_16:
  mlet "N be sequenceNAT-1M2-of NATNUMBERSK1", "X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "s be sequenceNAT-1M2-of X"
"cluster s *PARTFUN1K1\<^bsub>(NATNUMBERSK1,NATNUMBERSK1,NATNUMBERSK1,X)\<^esub> N as-term-is Function-likeFUNCT-1V1\<bar>NATNUMBERSK1 -definedRELAT-1V4\<bar>X -valuedRELAT-1V5"
proof
(*coherence*)
  show "s *PARTFUN1K1\<^bsub>(NATNUMBERSK1,NATNUMBERSK1,NATNUMBERSK1,X)\<^esub> N be Function-likeFUNCT-1V1\<bar>NATNUMBERSK1 -definedRELAT-1V4\<bar>X -valuedRELAT-1V5"
     sorry
qed "sorry"

mtheorem nat_1_cl_17:
  mlet "N be sequenceNAT-1M2-of NATNUMBERSK1", "X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "s be sequenceNAT-1M2-of X"
"cluster s *PARTFUN1K1\<^bsub>(NATNUMBERSK1,NATNUMBERSK1,NATNUMBERSK1,X)\<^esub> N as-term-is totalPARTFUN1V1\<^bsub>(NATNUMBERSK1)\<^esub>"
proof
(*coherence*)
  show "s *PARTFUN1K1\<^bsub>(NATNUMBERSK1,NATNUMBERSK1,NATNUMBERSK1,X)\<^esub> N be totalPARTFUN1V1\<^bsub>(NATNUMBERSK1)\<^esub>"
     sorry
qed "sorry"

mtheorem nat_1_th_50:
" for k be NatNAT-1M1 holds  for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for s be sequenceNAT-1M2-of X holds  for N be sequenceNAT-1M2-of NATNUMBERSK1 holds (s *PARTFUN1K1\<^bsub>(NATNUMBERSK1,NATNUMBERSK1,NATNUMBERSK1,X)\<^esub> N)^\\NAT-1K7\<^bsub>(X)\<^esub> k =FUNCT-2R2\<^bsub>(NATNUMBERSK1,X)\<^esub> s *PARTFUN1K1\<^bsub>(NATNUMBERSK1,NATNUMBERSK1,NATNUMBERSK1,X)\<^esub> (N ^\\NAT-1K7\<^bsub>(NATNUMBERSK1)\<^esub> k)"
sorry

mtheorem nat_1_th_51:
" for n be NatNAT-1M1 holds  for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for s be sequenceNAT-1M2-of X holds s .FUNCT-1K1 n inTARSKIR2 rngFUNCT-1K2 s"
sorry

mtheorem nat_1_th_52:
" for Y be setHIDDENM2 holds  for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for s be sequenceNAT-1M2-of X holds ( for n be NatNAT-1M1 holds s .FUNCT-1K1 n inTARSKIR2 Y) implies rngFUNCT-1K2 s c=TARSKIR1 Y"
sorry

mtheorem nat_1_th_53:
" for n be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds n be  non zeroORDINAL1V8 implies n =HIDDENR1 \<one>\<^sub>M or n >XXREAL-0R4 \<one>\<^sub>M"
sorry

mtheorem nat_1_th_54:
" for n be NatNAT-1M1 holds succORDINAL1K1 (SegmCARD-1K5 n) =XBOOLE-0R4 {l where l be NatNAT-1M1 : l <=XXREAL-0R1 n }"
sorry

mtheorem nat_1_reduce_1:
  mlet "n be naturalORDINAL1V7\<bar>NumberORDINAL1M1"
"reduce InSUBSET-1K10(n,NATNUMBERSK1) to n"
proof
(*reducibility*)
  show "InSUBSET-1K10(n,NATNUMBERSK1) =HIDDENR1 n"
    using ordinal1_def_12 subset_1_def_8 sorry
qed "sorry"

theorem nat_1_sch_18:
  fixes Ff1 Pp1 
  assumes
[ty_func]: "\<And> x1. x1 be NatNAT-1M1 \<Longrightarrow> Ff1(x1) be NatNAT-1M1" and
   A1: " for k be NatNAT-1M1 holds Ff1(k +NAT-1K1 \<one>\<^sub>M) <XXREAL-0R3 Ff1(k) or Pp1(k)"
  shows " ex k be NatNAT-1M1 st Pp1(k) & ( for n be NatNAT-1M1 holds Pp1(n) implies k <=XXREAL-0R1 n)"
sorry

mtheorem nat_1_cl_18:
  mlet "k be OrdinalORDINAL1M3", "x be objectHIDDENM1"
"cluster k -->FUNCOP-1K7 x as-term-is Sequence-likeORDINAL1V5"
proof
(*coherence*)
  show "k -->FUNCOP-1K7 x be Sequence-likeORDINAL1V5"
    using funcop_1_th_13 sorry
qed "sorry"

mtheorem nat_1_th_55:
" for s be ManySortedSetPBOOLEM1-of NATNUMBERSK1 holds  for k be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds rngFUNCT-1K2 (s ^\\NAT-1K6 k) c=TARSKIR1 rngFUNCT-1K2 s"
  using nat_1_lm_1 sorry

(*\$CT 3*)
mtheorem nat_1_th_59:
" for X be finiteFINSET-1V1\<bar>setHIDDENM2 holds \<one>\<^sub>M <XXREAL-0R3 cardCARD-1K4 X implies ( ex x1 be setHIDDENM2 st  ex x2 be setHIDDENM2 st (x1 inTARSKIR2 X & x2 inTARSKIR2 X) & x1 <>HIDDENR2 x2)"
sorry

mtheorem nat_1_th_60:
" for k be NatNAT-1M1 holds  for n be NatNAT-1M1 holds k <=XXREAL-0R1 n implies ( ex VarFor3 be setHIDDENM2 st (0NUMBERSK6 <=XXREAL-0R1 VarFor3 & VarFor3 <=XXREAL-0R1 n) & k =XBOOLE-0R4 VarFor3)"
sorry

mtheorem nat_1_th_61:
" for n be NatNAT-1M1 holds  for x be objectHIDDENM1 holds x inHIDDENR3 SegmCARD-1K5 (n +NAT-1K1 \<one>\<^sub>M) implies ( ex VarFor3 be setHIDDENM2 st (0NUMBERSK6 <=XXREAL-0R1 VarFor3 & VarFor3 <=XXREAL-0R1 n) & x =HIDDENR1 VarFor3)"
sorry

mtheorem nat_1_th_62:
" for k be NatNAT-1M1 holds  for m be NatNAT-1M1 holds  for i be NatNAT-1M1 holds m <=XXREAL-0R1 i & i <=XXREAL-0R1 m +XCMPLX-0K2 k implies ( ex VarFor4 be setHIDDENM2 st (m +NAT-1K1 0NUMBERSK6 <=XXREAL-0R1 VarFor4 & VarFor4 <=XXREAL-0R1 m +XCMPLX-0K2 k) & i =XBOOLE-0R4 VarFor4)"
sorry

syntax NAT_1K8 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ .NAT-1K8\<^bsub>'( _ ')\<^esub>  _ " [200,0,200]200)
translations "s .NAT-1K8\<^bsub>(D)\<^esub> n" \<rightharpoonup> "s .FUNCT-1K1 n"

mtheorem nat_1_add_6:
  mlet "D be setHIDDENM2", "s be sequenceNAT-1M2-of D", "n be naturalORDINAL1V7\<bar>NumberORDINAL1M1"
"cluster s .FUNCT-1K1 n as-term-is ElementSUBSET-1M1-of D"
proof
(*coherence*)
  show "s .FUNCT-1K1 n be ElementSUBSET-1M1-of D"
sorry
qed "sorry"

mtheorem nat_1_cl_19:
"cluster zeroORDINAL1V8 also-is  non positiveXXREAL-0V2 for naturalORDINAL1V7\<bar>NumberORDINAL1M1"
proof
(*coherence*)
  show " for it be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds it be zeroORDINAL1V8 implies it be  non positiveXXREAL-0V2"
     sorry
qed "sorry"

mtheorem nat_1_cl_20:
  mlet "A be  non zeroORDINAL1V8\<bar>objectHIDDENM1"
"cluster {TARSKIK1 A} as-term-is with-non-empty-elementsSETFAM-1V1"
proof
(*coherence*)
  show "{TARSKIK1 A} be with-non-empty-elementsSETFAM-1V1"
    using tarski_def_1 sorry
qed "sorry"

mtheorem nat_1_cl_21:
  mlet "A be  non zeroORDINAL1V8\<bar>objectHIDDENM1", "B be  non zeroORDINAL1V8\<bar>objectHIDDENM1"
"cluster {TARSKIK2 A,B } as-term-is with-non-empty-elementsSETFAM-1V1"
proof
(*coherence*)
  show "{TARSKIK2 A,B } be with-non-empty-elementsSETFAM-1V1"
    using tarski_def_2 sorry
qed "sorry"

mtheorem nat_1_cl_22:
  mlet "A be  non zeroORDINAL1V8\<bar>objectHIDDENM1", "B be  non zeroORDINAL1V8\<bar>objectHIDDENM1", "C be  non zeroORDINAL1V8\<bar>objectHIDDENM1"
"cluster {ENUMSET1K1 A,B,C } as-term-is with-non-empty-elementsSETFAM-1V1"
proof
(*coherence*)
  show "{ENUMSET1K1 A,B,C } be with-non-empty-elementsSETFAM-1V1"
    using enumset1_def_1 sorry
qed "sorry"

mtheorem nat_1_cl_23:
  mlet "A be  non zeroORDINAL1V8\<bar>objectHIDDENM1", "B be  non zeroORDINAL1V8\<bar>objectHIDDENM1", "C be  non zeroORDINAL1V8\<bar>objectHIDDENM1", "D be  non zeroORDINAL1V8\<bar>objectHIDDENM1"
"cluster {ENUMSET1K2 A,B,C,D } as-term-is with-non-empty-elementsSETFAM-1V1"
proof
(*coherence*)
  show "{ENUMSET1K2 A,B,C,D } be with-non-empty-elementsSETFAM-1V1"
    using enumset1_def_2 sorry
qed "sorry"

mtheorem nat_1_cl_24:
  mlet "A be  non zeroORDINAL1V8\<bar>objectHIDDENM1", "B be  non zeroORDINAL1V8\<bar>objectHIDDENM1", "C be  non zeroORDINAL1V8\<bar>objectHIDDENM1", "D be  non zeroORDINAL1V8\<bar>objectHIDDENM1", "E be  non zeroORDINAL1V8\<bar>objectHIDDENM1"
"cluster {ENUMSET1K3 A,B,C,D,E } as-term-is with-non-empty-elementsSETFAM-1V1"
proof
(*coherence*)
  show "{ENUMSET1K3 A,B,C,D,E } be with-non-empty-elementsSETFAM-1V1"
    using enumset1_def_3 sorry
qed "sorry"

mtheorem nat_1_cl_25:
  mlet "A be  non zeroORDINAL1V8\<bar>objectHIDDENM1", "B be  non zeroORDINAL1V8\<bar>objectHIDDENM1", "C be  non zeroORDINAL1V8\<bar>objectHIDDENM1", "D be  non zeroORDINAL1V8\<bar>objectHIDDENM1", "E be  non zeroORDINAL1V8\<bar>objectHIDDENM1", "F be  non zeroORDINAL1V8\<bar>objectHIDDENM1"
"cluster {ENUMSET1K4 A,B,C,D,E,F } as-term-is with-non-empty-elementsSETFAM-1V1"
proof
(*coherence*)
  show "{ENUMSET1K4 A,B,C,D,E,F } be with-non-empty-elementsSETFAM-1V1"
    using enumset1_def_4 sorry
qed "sorry"

mtheorem nat_1_cl_26:
  mlet "A be  non zeroORDINAL1V8\<bar>objectHIDDENM1", "B be  non zeroORDINAL1V8\<bar>objectHIDDENM1", "C be  non zeroORDINAL1V8\<bar>objectHIDDENM1", "D be  non zeroORDINAL1V8\<bar>objectHIDDENM1", "E be  non zeroORDINAL1V8\<bar>objectHIDDENM1", "F be  non zeroORDINAL1V8\<bar>objectHIDDENM1", "G be  non zeroORDINAL1V8\<bar>objectHIDDENM1"
"cluster {ENUMSET1K5 A,B,C,D,E,F,G } as-term-is with-non-empty-elementsSETFAM-1V1"
proof
(*coherence*)
  show "{ENUMSET1K5 A,B,C,D,E,F,G } be with-non-empty-elementsSETFAM-1V1"
    using enumset1_def_5 sorry
qed "sorry"

mtheorem nat_1_cl_27:
  mlet "A be  non zeroORDINAL1V8\<bar>objectHIDDENM1", "B be  non zeroORDINAL1V8\<bar>objectHIDDENM1", "C be  non zeroORDINAL1V8\<bar>objectHIDDENM1", "D be  non zeroORDINAL1V8\<bar>objectHIDDENM1", "E be  non zeroORDINAL1V8\<bar>objectHIDDENM1", "F be  non zeroORDINAL1V8\<bar>objectHIDDENM1", "G be  non zeroORDINAL1V8\<bar>objectHIDDENM1", "H be  non zeroORDINAL1V8\<bar>objectHIDDENM1"
"cluster {ENUMSET1K6 A,B,C,D,E,F,G,H } as-term-is with-non-empty-elementsSETFAM-1V1"
proof
(*coherence*)
  show "{ENUMSET1K6 A,B,C,D,E,F,G,H } be with-non-empty-elementsSETFAM-1V1"
    using enumset1_def_6 sorry
qed "sorry"

mtheorem nat_1_cl_28:
  mlet "A be  non zeroORDINAL1V8\<bar>objectHIDDENM1", "B be  non zeroORDINAL1V8\<bar>objectHIDDENM1", "C be  non zeroORDINAL1V8\<bar>objectHIDDENM1", "D be  non zeroORDINAL1V8\<bar>objectHIDDENM1", "E be  non zeroORDINAL1V8\<bar>objectHIDDENM1", "F be  non zeroORDINAL1V8\<bar>objectHIDDENM1", "G be  non zeroORDINAL1V8\<bar>objectHIDDENM1", "H be  non zeroORDINAL1V8\<bar>objectHIDDENM1", "I be  non zeroORDINAL1V8\<bar>objectHIDDENM1"
"cluster {ENUMSET1K7 A,B,C,D,E,F,G,H,I } as-term-is with-non-empty-elementsSETFAM-1V1"
proof
(*coherence*)
  show "{ENUMSET1K7 A,B,C,D,E,F,G,H,I } be with-non-empty-elementsSETFAM-1V1"
    using enumset1_def_7 sorry
qed "sorry"

mtheorem nat_1_cl_29:
  mlet "A be  non zeroORDINAL1V8\<bar>objectHIDDENM1", "B be  non zeroORDINAL1V8\<bar>objectHIDDENM1", "C be  non zeroORDINAL1V8\<bar>objectHIDDENM1", "D be  non zeroORDINAL1V8\<bar>objectHIDDENM1", "E be  non zeroORDINAL1V8\<bar>objectHIDDENM1", "F be  non zeroORDINAL1V8\<bar>objectHIDDENM1", "G be  non zeroORDINAL1V8\<bar>objectHIDDENM1", "H be  non zeroORDINAL1V8\<bar>objectHIDDENM1", "I be  non zeroORDINAL1V8\<bar>objectHIDDENM1", "J be  non zeroORDINAL1V8\<bar>objectHIDDENM1"
"cluster {ENUMSET1K8 A,B,C,D,E,F,G,H,I,J } as-term-is with-non-empty-elementsSETFAM-1V1"
proof
(*coherence*)
  show "{ENUMSET1K8 A,B,C,D,E,F,G,H,I,J } be with-non-empty-elementsSETFAM-1V1"
    using enumset1_def_8 sorry
qed "sorry"

mtheorem nat_1_cl_30:
"cluster emptyXBOOLE-0V1 also-is zeroORDINAL1V8 for setHIDDENM2"
proof
(*coherence*)
  show " for it be setHIDDENM2 holds it be emptyXBOOLE-0V1 implies it be zeroORDINAL1V8"
     sorry
qed "sorry"

mtheorem nat_1_cl_31:
"cluster  non zeroORDINAL1V8 also-is  non emptyXBOOLE-0V1 for setHIDDENM2"
proof
(*coherence*)
  show " for it be setHIDDENM2 holds it be  non zeroORDINAL1V8 implies it be  non emptyXBOOLE-0V1"
     sorry
qed "sorry"

syntax NAT_1K9 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ .NAT-1K9\<^bsub>'( _ ')\<^esub>'( _ , _ ')" [200,0,0,0]200)
translations "B .NAT-1K9\<^bsub>(G)\<^esub>(g,i)" \<rightharpoonup> "B .BINOP-1K1(g,i)"

mtheorem nat_1_add_7:
  mlet "G be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "B be FunctionFUNCT-2M1-of([:ZFMISC-1K2 G,NATNUMBERSK1 :],G)", "g be ElementSUBSET-1M1-of G", "i be NatNAT-1M1"
"cluster B .BINOP-1K1(g,i) as-term-is ElementSUBSET-1M1-of G"
proof
(*coherence*)
  show "B .BINOP-1K1(g,i) be ElementSUBSET-1M1-of G"
sorry
qed "sorry"

syntax NAT_1K10 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ .NAT-1K10\<^bsub>'( _ ')\<^esub>'( _ , _ ')" [200,0,0,0]200)
translations "B .NAT-1K10\<^bsub>(G)\<^esub>(i,g)" \<rightharpoonup> "B .BINOP-1K1(i,g)"

mtheorem nat_1_add_8:
  mlet "G be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "B be FunctionFUNCT-2M1-of([:ZFMISC-1K2 NATNUMBERSK1,G :],G)", "i be NatNAT-1M1", "g be ElementSUBSET-1M1-of G"
"cluster B .BINOP-1K1(i,g) as-term-is ElementSUBSET-1M1-of G"
proof
(*coherence*)
  show "B .BINOP-1K1(i,g) be ElementSUBSET-1M1-of G"
sorry
qed "sorry"

theorem nat_1_sch_19:
  fixes Xf0 Zf0 Pp3 
  assumes
[ty]: "Xf0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
  [ty]: "Zf0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
   A1: " for x be ElementSUBSET-1M1-of Xf0 holds  for y be NatNAT-1M1 holds  ex z be ElementSUBSET-1M1-of Zf0 st Pp3(x,y,z)"
  shows " ex f be FunctionFUNCT-2M1-of([:ZFMISC-1K2 Xf0,NATNUMBERSK1 :],Zf0) st  for x be ElementSUBSET-1M1-of Xf0 holds  for y be NatNAT-1M1 holds Pp3(x,y,f .BINOP-1K1(x,y))"
sorry

mtheorem nat_1_th_63:
" for n be NatNAT-1M1 holds SegmCARD-1K5 n c=ORDINAL1R1 SegmCARD-1K5 (n +NAT-1K1 \<one>\<^sub>M)"
  using nat_1_th_11 nat_1_th_39 sorry

end
