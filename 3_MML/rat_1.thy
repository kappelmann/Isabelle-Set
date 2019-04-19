theory rat_1
  imports arytm_3 int_1
   "../mizar_extension/E_number"
begin
(*begin*)
reserve x for "objectHIDDENM1"
reserve a, b for "RealXREAL-0M1"
reserve k, k1, i1, j1, w for "NatNAT-1M1"
reserve m, m1, n, n1 for "IntegerINT-1M1"
mlemma rat_1_lm_1:
"omegaORDINAL1K4 c=TARSKIR1 (({[TARSKIK4 c,d ] where c be ElementSUBSET-1M1-of omegaORDINAL1K4, d be ElementSUBSET-1M1-of omegaORDINAL1K4 : (c,d)are-coprimeARYTM-3R1 & d <>HIDDENR2 {}ARYTM-3K12 })\\SUBSET-1K6 ({[TARSKIK4 k,\<one>\<^sub>M ] where k be ElementSUBSET-1M1-of omegaORDINAL1K4 :  True  }))\\/XBOOLE-0K2 omegaORDINAL1K4"
  using xboole_1_th_7 sorry

mlemma rat_1_lm_2:
" for i1 be NatNAT-1M1 holds  for j1 be NatNAT-1M1 holds quotientARYTM-3K9(i1,j1) =XBOOLE-0R4 i1 /XCMPLX-0K7 j1"
sorry

mlemma rat_1_lm_3:
" for a be RealXREAL-0M1 holds  for Z9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds Z9 =XBOOLE-0R4 0NUMBERSK6 implies ( for x9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds x9 =HIDDENR1 a implies Z9 -ARYTM-1K2 x9 =HIDDENR1 -XCMPLX-0K4 a)"
sorry

mlemma rat_1_lm_4:
" for x be objectHIDDENM1 holds x inHIDDENR3 RATNUMBERSK4 implies ( ex m be IntegerINT-1M1 st  ex n be IntegerINT-1M1 st x =HIDDENR1 m /XCMPLX-0K7 n)"
sorry

mlemma rat_1_lm_5:
" for x be objectHIDDENM1 holds  for w be NatNAT-1M1 holds  for m be IntegerINT-1M1 holds x =HIDDENR1 m /XCMPLX-0K7 w implies x inHIDDENR3 RATNUMBERSK4"
sorry

mlemma rat_1_lm_6:
" for x be objectHIDDENM1 holds  for m be IntegerINT-1M1 holds  for n be IntegerINT-1M1 holds x =HIDDENR1 m /XCMPLX-0K7 n implies x inHIDDENR3 RATNUMBERSK4"
sorry

abbreviation(input) RAT_1K1("RATRAT-1K1" 355) where
  "RATRAT-1K1 \<equiv> RATNUMBERSK4"

mtheorem rat_1_def_1:
"redefine func RATRAT-1K1 \<rightarrow> setHIDDENM2 means
  \<lambda>it.  for x be objectHIDDENM1 holds x inHIDDENR3 it iff ( ex m be IntegerINT-1M1 st  ex n be IntegerINT-1M1 st x =HIDDENR1 m /XCMPLX-0K7 n)"
proof
(*compatibility*)
  show " for it be setHIDDENM2 holds it =HIDDENR1 RATRAT-1K1 iff ( for x be objectHIDDENM1 holds x inHIDDENR3 it iff ( ex m be IntegerINT-1M1 st  ex n be IntegerINT-1M1 st x =HIDDENR1 m /XCMPLX-0K7 n))"
sorry
qed "sorry"

mdef rat_1_def_2 ("rationalRAT-1V1" 70 ) where
"attr rationalRAT-1V1 for objectHIDDENM1 means
  (\<lambda>r. r inHIDDENR3 RATRAT-1K1)"..

mtheorem rat_1_cl_1:
"cluster rationalRAT-1V1 for RealXREAL-0M1"
proof
(*existence*)
  show " ex it be RealXREAL-0M1 st it be rationalRAT-1V1"
sorry
qed "sorry"

mtheorem rat_1_cl_2:
"cluster rationalRAT-1V1 for numberORDINAL1M2"
proof
(*existence*)
  show " ex it be numberORDINAL1M2 st it be rationalRAT-1V1"
sorry
qed "sorry"

syntax RAT_1M1 :: "Ty" ("RationalRAT-1M1" 70)
translations "RationalRAT-1M1" \<rightharpoonup> "rationalRAT-1V1\<bar>NumberORDINAL1M1"

mtheorem rat_1_th_1:
" for x be objectHIDDENM1 holds x inHIDDENR3 RATRAT-1K1 implies ( ex m be IntegerINT-1M1 st  ex n be IntegerINT-1M1 st n <>HIDDENR2 0NUMBERSK6 & x =HIDDENR1 m /XCMPLX-0K7 n)"
sorry

mtheorem rat_1_th_2:
" for x be objectHIDDENM1 holds x be rationalRAT-1V1 implies ( ex m be IntegerINT-1M1 st  ex n be IntegerINT-1M1 st n <>HIDDENR2 0NUMBERSK6 & x =HIDDENR1 m /XCMPLX-0K7 n)"
  using rat_1_th_1 sorry

mtheorem rat_1_cl_3:
"cluster rationalRAT-1V1 also-is realXREAL-0V1 for objectHIDDENM1"
proof
(*coherence*)
  show " for it be objectHIDDENM1 holds it be rationalRAT-1V1 implies it be realXREAL-0V1"
    using numbers_th_12 sorry
qed "sorry"

mtheorem rat_1_th_3:
" for m be IntegerINT-1M1 holds  for n be IntegerINT-1M1 holds m /XCMPLX-0K7 n be rationalRAT-1V1"
  using rat_1_def_1 sorry

mtheorem rat_1_cl_4:
"cluster integerINT-1V1 also-is rationalRAT-1V1 for objectHIDDENM1"
proof
(*coherence*)
  show " for it be objectHIDDENM1 holds it be integerINT-1V1 implies it be rationalRAT-1V1"
sorry
qed "sorry"

reserve p, q for "RationalRAT-1M1"
mtheorem rat_1_cl_5:
  mlet "p be RationalRAT-1M1", "q be RationalRAT-1M1"
"cluster p *XCMPLX-0K3 q as-term-is rationalRAT-1V1"
proof
(*coherence*)
  show "p *XCMPLX-0K3 q be rationalRAT-1V1"
sorry
qed "sorry"

mtheorem rat_1_cl_6:
  mlet "p be RationalRAT-1M1", "q be RationalRAT-1M1"
"cluster p +XCMPLX-0K2 q as-term-is rationalRAT-1V1"
proof
(*coherence*)
  show "p +XCMPLX-0K2 q be rationalRAT-1V1"
sorry
qed "sorry"

mtheorem rat_1_cl_7:
  mlet "p be RationalRAT-1M1", "q be RationalRAT-1M1"
"cluster p -XCMPLX-0K6 q as-term-is rationalRAT-1V1"
proof
(*coherence*)
  show "p -XCMPLX-0K6 q be rationalRAT-1V1"
sorry
qed "sorry"

mtheorem rat_1_cl_8:
  mlet "p be RationalRAT-1M1", "q be RationalRAT-1M1"
"cluster p /XCMPLX-0K7 q as-term-is rationalRAT-1V1"
proof
(*coherence*)
  show "p /XCMPLX-0K7 q be rationalRAT-1V1"
sorry
qed "sorry"

mtheorem rat_1_cl_9:
  mlet "p be RationalRAT-1M1"
"cluster -XCMPLX-0K4 p as-term-is rationalRAT-1V1"
proof
(*coherence*)
  show "-XCMPLX-0K4 p be rationalRAT-1V1"
sorry
qed "sorry"

mtheorem rat_1_cl_10:
  mlet "p be RationalRAT-1M1"
"cluster p \<inverse>XCMPLX-0K5 as-term-is rationalRAT-1V1"
proof
(*coherence*)
  show "p \<inverse>XCMPLX-0K5 be rationalRAT-1V1"
sorry
qed "sorry"

(*\$CT 3*)
mtheorem rat_1_th_7:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds a <XXREAL-0R3 b implies ( ex p be RationalRAT-1M1 st a <XXREAL-0R3 p & p <XXREAL-0R3 b)"
sorry

mtheorem rat_1_th_8:
" for p be RationalRAT-1M1 holds  ex m be IntegerINT-1M1 st  ex k be NatNAT-1M1 st k <>HIDDENR2 0NUMBERSK6 & p =HIDDENR1 m /XCMPLX-0K7 k"
sorry

mtheorem rat_1_th_9:
" for p be RationalRAT-1M1 holds  ex m be IntegerINT-1M1 st  ex k be NatNAT-1M1 st (k <>HIDDENR2 0NUMBERSK6 & p =HIDDENR1 m /XCMPLX-0K7 k) & ( for n be IntegerINT-1M1 holds  for w be NatNAT-1M1 holds w <>HIDDENR2 0NUMBERSK6 & p =HIDDENR1 n /XCMPLX-0K7 w implies k <=XXREAL-0R1 w)"
sorry

mdef rat_1_def_3 ("denominatorRAT-1K2  _ " [250]250 ) where
  mlet "p be RationalRAT-1M1"
"func denominatorRAT-1K2 p \<rightarrow> NatNAT-1M1 means
  \<lambda>it. (it <>HIDDENR2 0NUMBERSK6 & ( ex m be IntegerINT-1M1 st p =HIDDENR1 m /XCMPLX-0K7 it)) & ( for n be IntegerINT-1M1 holds  for k be NatNAT-1M1 holds k <>HIDDENR2 0NUMBERSK6 & p =HIDDENR1 n /XCMPLX-0K7 k implies it <=XXREAL-0R1 k)"
proof-
  (*existence*)
    show " ex it be NatNAT-1M1 st (it <>HIDDENR2 0NUMBERSK6 & ( ex m be IntegerINT-1M1 st p =HIDDENR1 m /XCMPLX-0K7 it)) & ( for n be IntegerINT-1M1 holds  for k be NatNAT-1M1 holds k <>HIDDENR2 0NUMBERSK6 & p =HIDDENR1 n /XCMPLX-0K7 k implies it <=XXREAL-0R1 k)"
sorry
  (*uniqueness*)
    show " for it1 be NatNAT-1M1 holds  for it2 be NatNAT-1M1 holds ((it1 <>HIDDENR2 0NUMBERSK6 & ( ex m be IntegerINT-1M1 st p =HIDDENR1 m /XCMPLX-0K7 it1)) & ( for n be IntegerINT-1M1 holds  for k be NatNAT-1M1 holds k <>HIDDENR2 0NUMBERSK6 & p =HIDDENR1 n /XCMPLX-0K7 k implies it1 <=XXREAL-0R1 k)) & ((it2 <>HIDDENR2 0NUMBERSK6 & ( ex m be IntegerINT-1M1 st p =HIDDENR1 m /XCMPLX-0K7 it2)) & ( for n be IntegerINT-1M1 holds  for k be NatNAT-1M1 holds k <>HIDDENR2 0NUMBERSK6 & p =HIDDENR1 n /XCMPLX-0K7 k implies it2 <=XXREAL-0R1 k)) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mdef rat_1_def_4 ("numeratorRAT-1K3  _ " [250]250 ) where
  mlet "p be RationalRAT-1M1"
"func numeratorRAT-1K3 p \<rightarrow> IntegerINT-1M1 equals
  denominatorRAT-1K2 p *XCMPLX-0K3 p"
proof-
  (*coherence*)
    show "denominatorRAT-1K2 p *XCMPLX-0K3 p be IntegerINT-1M1"
sorry
qed "sorry"

mtheorem rat_1_th_10:
" for p be RationalRAT-1M1 holds 0NUMBERSK6 <XXREAL-0R3 denominatorRAT-1K2 p"
sorry

mtheorem rat_1_cl_11:
  mlet "p be RationalRAT-1M1"
"cluster denominatorRAT-1K2 p as-term-is positiveXXREAL-0V2"
proof
(*coherence*)
  show "denominatorRAT-1K2 p be positiveXXREAL-0V2"
    using rat_1_th_10 sorry
qed "sorry"

mtheorem rat_1_th_11:
" for p be RationalRAT-1M1 holds \<one>\<^sub>M <=XXREAL-0R1 denominatorRAT-1K2 p"
sorry

mtheorem rat_1_th_12:
" for p be RationalRAT-1M1 holds 0NUMBERSK6 <XXREAL-0R3 denominatorRAT-1K2 p \<inverse>XCMPLX-0K5"
   sorry

mtheorem rat_1_th_13:
" for p be RationalRAT-1M1 holds \<one>\<^sub>M >=XXREAL-0R2 denominatorRAT-1K2 p \<inverse>XCMPLX-0K5"
sorry

mtheorem rat_1_th_14:
" for p be RationalRAT-1M1 holds numeratorRAT-1K3 p =HIDDENR1 0NUMBERSK6 iff p =HIDDENR1 0NUMBERSK6"
  using xcmplx_1_th_6 sorry

mtheorem rat_1_th_15:
" for p be RationalRAT-1M1 holds p =HIDDENR1 numeratorRAT-1K3 p /XCMPLX-0K7 denominatorRAT-1K2 p & p =HIDDENR1 numeratorRAT-1K3 p *XCMPLX-0K3 denominatorRAT-1K2 p \<inverse>XCMPLX-0K5"
sorry

mtheorem rat_1_th_16:
" for p be RationalRAT-1M1 holds p <>HIDDENR2 0NUMBERSK6 implies denominatorRAT-1K2 p =XBOOLE-0R4 numeratorRAT-1K3 p /XCMPLX-0K7 p"
sorry

mtheorem rat_1_th_17:
" for p be RationalRAT-1M1 holds p be IntegerINT-1M1 implies denominatorRAT-1K2 p =XBOOLE-0R4 \<one>\<^sub>M & numeratorRAT-1K3 p =HIDDENR1 p"
sorry

mtheorem rat_1_th_18:
" for p be RationalRAT-1M1 holds numeratorRAT-1K3 p =HIDDENR1 p or denominatorRAT-1K2 p =XBOOLE-0R4 \<one>\<^sub>M implies p be IntegerINT-1M1"
sorry

mtheorem rat_1_th_19:
" for p be RationalRAT-1M1 holds numeratorRAT-1K3 p =HIDDENR1 p iff denominatorRAT-1K2 p =XBOOLE-0R4 \<one>\<^sub>M"
  using rat_1_th_17 sorry

mtheorem rat_1_th_20:
" for p be RationalRAT-1M1 holds (numeratorRAT-1K3 p =HIDDENR1 p or denominatorRAT-1K2 p =XBOOLE-0R4 \<one>\<^sub>M) & 0NUMBERSK6 <=XXREAL-0R1 p implies p be ElementSUBSET-1M1-of NATNUMBERSK1"
sorry

mtheorem rat_1_th_21:
" for p be RationalRAT-1M1 holds \<one>\<^sub>M <XXREAL-0R3 denominatorRAT-1K2 p iff  not p be integerINT-1V1"
sorry

mlemma rat_1_lm_7:
"\<one>\<^sub>M \<inverse>XCMPLX-0K5 =HIDDENR1 \<one>\<^sub>M"
   sorry

mtheorem rat_1_th_22:
" for p be RationalRAT-1M1 holds \<one>\<^sub>M >XXREAL-0R4 denominatorRAT-1K2 p \<inverse>XCMPLX-0K5 iff  not p be integerINT-1V1"
sorry

mtheorem rat_1_th_23:
" for p be RationalRAT-1M1 holds numeratorRAT-1K3 p =HIDDENR1 denominatorRAT-1K2 p iff p =HIDDENR1 \<one>\<^sub>M"
sorry

mtheorem rat_1_th_24:
" for p be RationalRAT-1M1 holds numeratorRAT-1K3 p =HIDDENR1 -XCMPLX-0K4 denominatorRAT-1K2 p iff p =HIDDENR1 -XCMPLX-0K4 \<one>\<^sub>M"
sorry

mtheorem rat_1_th_25:
" for p be RationalRAT-1M1 holds -XCMPLX-0K4 numeratorRAT-1K3 p =HIDDENR1 denominatorRAT-1K2 p iff p =HIDDENR1 -XCMPLX-0K4 \<one>\<^sub>M"
sorry

mtheorem rat_1_th_26:
" for m be IntegerINT-1M1 holds  for p be RationalRAT-1M1 holds m <>HIDDENR2 0NUMBERSK6 implies p =HIDDENR1 (numeratorRAT-1K3 p *XCMPLX-0K3 m)/XCMPLX-0K7 (denominatorRAT-1K2 p *XCMPLX-0K3 m)"
sorry

mtheorem rat_1_th_27:
" for k be NatNAT-1M1 holds  for m be IntegerINT-1M1 holds  for p be RationalRAT-1M1 holds k <>HIDDENR2 0NUMBERSK6 & p =HIDDENR1 m /XCMPLX-0K7 k implies ( ex w be NatNAT-1M1 st m =HIDDENR1 numeratorRAT-1K3 p *XCMPLX-0K3 w & k =XBOOLE-0R4 denominatorRAT-1K2 p *XCMPLX-0K3 w)"
sorry

mtheorem rat_1_th_28:
" for m be IntegerINT-1M1 holds  for n be IntegerINT-1M1 holds  for p be RationalRAT-1M1 holds p =HIDDENR1 m /XCMPLX-0K7 n & n <>HIDDENR2 0NUMBERSK6 implies ( ex m1 be IntegerINT-1M1 st m =HIDDENR1 numeratorRAT-1K3 p *XCMPLX-0K3 m1 & n =HIDDENR1 denominatorRAT-1K2 p *XCMPLX-0K3 m1)"
sorry

mtheorem rat_1_th_29:
" for p be RationalRAT-1M1 holds  not ( ex w be NatNAT-1M1 st \<one>\<^sub>M <XXREAL-0R3 w & ( ex m be IntegerINT-1M1 st  ex k be NatNAT-1M1 st numeratorRAT-1K3 p =HIDDENR1 m *XCMPLX-0K3 w & denominatorRAT-1K2 p =XBOOLE-0R4 k *XCMPLX-0K3 w))"
sorry

mtheorem rat_1_th_30:
" for k be NatNAT-1M1 holds  for m be IntegerINT-1M1 holds  for p be RationalRAT-1M1 holds (p =HIDDENR1 m /XCMPLX-0K7 k & k <>HIDDENR2 0NUMBERSK6) &  not ( ex w be NatNAT-1M1 st \<one>\<^sub>M <XXREAL-0R3 w & ( ex m1 be IntegerINT-1M1 st  ex k1 be NatNAT-1M1 st m =HIDDENR1 m1 *XCMPLX-0K3 w & k =XBOOLE-0R4 k1 *XCMPLX-0K3 w)) implies k =XBOOLE-0R4 denominatorRAT-1K2 p & m =HIDDENR1 numeratorRAT-1K3 p"
sorry

mtheorem rat_1_th_31:
" for p be RationalRAT-1M1 holds p <XXREAL-0R3 -XCMPLX-0K4 \<one>\<^sub>M iff numeratorRAT-1K3 p <XXREAL-0R3 -XCMPLX-0K4 denominatorRAT-1K2 p"
sorry

mtheorem rat_1_th_32:
" for p be RationalRAT-1M1 holds p <=XXREAL-0R1 -XCMPLX-0K4 \<one>\<^sub>M iff numeratorRAT-1K3 p <=XXREAL-0R1 -XCMPLX-0K4 denominatorRAT-1K2 p"
sorry

mtheorem rat_1_th_33:
" for p be RationalRAT-1M1 holds p <XXREAL-0R3 -XCMPLX-0K4 \<one>\<^sub>M iff denominatorRAT-1K2 p <XXREAL-0R3 -XCMPLX-0K4 numeratorRAT-1K3 p"
sorry

mtheorem rat_1_th_34:
" for p be RationalRAT-1M1 holds p <=XXREAL-0R1 -XCMPLX-0K4 \<one>\<^sub>M iff denominatorRAT-1K2 p <=XXREAL-0R1 -XCMPLX-0K4 numeratorRAT-1K3 p"
sorry

mtheorem rat_1_th_35:
" for p be RationalRAT-1M1 holds p <XXREAL-0R3 \<one>\<^sub>M iff numeratorRAT-1K3 p <XXREAL-0R3 denominatorRAT-1K2 p"
sorry

mtheorem rat_1_th_36:
" for p be RationalRAT-1M1 holds p <=XXREAL-0R1 \<one>\<^sub>M iff numeratorRAT-1K3 p <=XXREAL-0R1 denominatorRAT-1K2 p"
sorry

mtheorem rat_1_th_37:
" for p be RationalRAT-1M1 holds p <XXREAL-0R3 0NUMBERSK6 iff numeratorRAT-1K3 p <XXREAL-0R3 0NUMBERSK6"
sorry

mtheorem rat_1_th_38:
" for p be RationalRAT-1M1 holds p <=XXREAL-0R1 0NUMBERSK6 iff numeratorRAT-1K3 p <=XXREAL-0R1 0NUMBERSK6"
sorry

mtheorem rat_1_th_39:
" for a be RealXREAL-0M1 holds  for p be RationalRAT-1M1 holds a <XXREAL-0R3 p iff a *XCMPLX-0K3 denominatorRAT-1K2 p <XXREAL-0R3 numeratorRAT-1K3 p"
sorry

mtheorem rat_1_th_40:
" for a be RealXREAL-0M1 holds  for p be RationalRAT-1M1 holds a <=XXREAL-0R1 p iff a *XCMPLX-0K3 denominatorRAT-1K2 p <=XXREAL-0R1 numeratorRAT-1K3 p"
sorry

mtheorem rat_1_th_41:
" for p be RationalRAT-1M1 holds  for q be RationalRAT-1M1 holds denominatorRAT-1K2 p =XBOOLE-0R4 denominatorRAT-1K2 q & numeratorRAT-1K3 p =HIDDENR1 numeratorRAT-1K3 q implies p =HIDDENR1 q"
sorry

mtheorem rat_1_th_42:
" for p be RationalRAT-1M1 holds  for q be RationalRAT-1M1 holds p <XXREAL-0R3 q iff numeratorRAT-1K3 p *XCMPLX-0K3 denominatorRAT-1K2 q <XXREAL-0R3 numeratorRAT-1K3 q *XCMPLX-0K3 denominatorRAT-1K2 p"
sorry

mtheorem rat_1_th_43:
" for p be RationalRAT-1M1 holds denominatorRAT-1K2 (-XCMPLX-0K4 p) =XBOOLE-0R4 denominatorRAT-1K2 p & numeratorRAT-1K3 (-XCMPLX-0K4 p) =HIDDENR1 -XCMPLX-0K4 numeratorRAT-1K3 p"
sorry

mtheorem rat_1_th_44:
" for p be RationalRAT-1M1 holds  for q be RationalRAT-1M1 holds 0NUMBERSK6 <XXREAL-0R3 p & q =HIDDENR1 \<one>\<^sub>M /XCMPLX-0K7 p iff numeratorRAT-1K3 q =HIDDENR1 denominatorRAT-1K2 p & denominatorRAT-1K2 q =HIDDENR1 numeratorRAT-1K3 p"
sorry

mtheorem rat_1_th_45:
" for p be RationalRAT-1M1 holds  for q be RationalRAT-1M1 holds p <XXREAL-0R3 0NUMBERSK6 & q =HIDDENR1 \<one>\<^sub>M /XCMPLX-0K7 p iff numeratorRAT-1K3 q =HIDDENR1 -XCMPLX-0K4 denominatorRAT-1K2 p & denominatorRAT-1K2 q =HIDDENR1 -XCMPLX-0K4 numeratorRAT-1K3 p"
sorry

end
