theory arytm_2
  imports arytm_3
   "../mizar_extension/E_number"
begin
(*begin*)
reserve r, s, t, x9, y9, z9, p, q for "ElementSUBSET-1M1-of RAT+ARYTM-3K5"
mdef arytm_2_def_1 ("DEDEKIND-CUTSARYTM-2K1" 164 ) where
"func DEDEKIND-CUTSARYTM-2K1 \<rightarrow> Subset-FamilySETFAM-1M1-of RAT+ARYTM-3K5 equals
  ({A where A be SubsetSUBSET-1M2-of RAT+ARYTM-3K5 :  for r be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds r inTARSKIR2 A implies ( for s be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds s <='ARYTM-3R3 r implies s inTARSKIR2 A) & ( ex s be ElementSUBSET-1M1-of RAT+ARYTM-3K5 st s inTARSKIR2 A & r <ARYTM-3R4 s) })\\SUBSET-1K6 {TARSKIK1 RAT+ARYTM-3K5 }"
proof-
  (*coherence*)
    show "({A where A be SubsetSUBSET-1M2-of RAT+ARYTM-3K5 :  for r be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds r inTARSKIR2 A implies ( for s be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds s <='ARYTM-3R3 r implies s inTARSKIR2 A) & ( ex s be ElementSUBSET-1M1-of RAT+ARYTM-3K5 st s inTARSKIR2 A & r <ARYTM-3R4 s) })\\SUBSET-1K6 {TARSKIK1 RAT+ARYTM-3K5 } be Subset-FamilySETFAM-1M1-of RAT+ARYTM-3K5"
sorry
qed "sorry"

mtheorem arytm_2_cl_1:
"cluster DEDEKIND-CUTSARYTM-2K1 as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "DEDEKIND-CUTSARYTM-2K1 be  non emptyXBOOLE-0V1"
sorry
qed "sorry"

mdef arytm_2_def_2 ("REAL+ARYTM-2K2" 164 ) where
"func REAL+ARYTM-2K2 \<rightarrow> setHIDDENM2 equals
  (RAT+ARYTM-3K5 \\/XBOOLE-0K2 DEDEKIND-CUTSARYTM-2K1)\\SUBSET-1K6 ({{s where s be ElementSUBSET-1M1-of RAT+ARYTM-3K5 : s <ARYTM-3R4 t } where t be ElementSUBSET-1M1-of RAT+ARYTM-3K5 : t <>HIDDENR2 {}ARYTM-3K12 })"
proof-
  (*coherence*)
    show "(RAT+ARYTM-3K5 \\/XBOOLE-0K2 DEDEKIND-CUTSARYTM-2K1)\\SUBSET-1K6 ({{s where s be ElementSUBSET-1M1-of RAT+ARYTM-3K5 : s <ARYTM-3R4 t } where t be ElementSUBSET-1M1-of RAT+ARYTM-3K5 : t <>HIDDENR2 {}ARYTM-3K12 }) be setHIDDENM2"
       sorry
qed "sorry"

reserve x, y, z for "ElementSUBSET-1M1-of REAL+ARYTM-2K2"
mlemma arytm_2_lm_1:
" not ( ex x be objectHIDDENM1 st  ex y be objectHIDDENM1 st [TARSKIK4 x,y ] inHIDDENR3 {A where A be SubsetSUBSET-1M2-of RAT+ARYTM-3K5 :  for r be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds r inTARSKIR2 A implies ( for s be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds s <='ARYTM-3R3 r implies s inTARSKIR2 A) & ( ex s be ElementSUBSET-1M1-of RAT+ARYTM-3K5 st s inTARSKIR2 A & r <ARYTM-3R4 s) })"
sorry

mlemma arytm_2_lm_2:
"RAT+ARYTM-3K5 missesXBOOLE-0R1 {{s where s be ElementSUBSET-1M1-of RAT+ARYTM-3K5 : s <ARYTM-3R4 t } where t be ElementSUBSET-1M1-of RAT+ARYTM-3K5 : t <>HIDDENR2 {}ARYTM-3K12 }"
sorry

mtheorem arytm_2_th_1:
"RAT+ARYTM-3K5 c=TARSKIR1 REAL+ARYTM-2K2"
  using arytm_2_lm_2 xboole_1_th_7 xboole_1_th_86 sorry

mlemma
"RAT+ARYTM-3K5 \\/XBOOLE-0K2 DEDEKIND-CUTSARYTM-2K1 c=TARSKIR1 RAT+ARYTM-3K5 \\/XBOOLE-0K2 ({A where A be SubsetSUBSET-1M2-of RAT+ARYTM-3K5 :  for r be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds r inTARSKIR2 A implies ( for s be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds s <='ARYTM-3R3 r implies s inTARSKIR2 A) & ( ex s be ElementSUBSET-1M1-of RAT+ARYTM-3K5 st s inTARSKIR2 A & r <ARYTM-3R4 s) })"
  using xboole_1_th_9 sorry

mlemma arytm_2_lm_3:
"REAL+ARYTM-2K2 c=TARSKIR1 RAT+ARYTM-3K5 \\/XBOOLE-0K2 ({A where A be SubsetSUBSET-1M2-of RAT+ARYTM-3K5 :  for r be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds r inTARSKIR2 A implies ( for s be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds s <='ARYTM-3R3 r implies s inTARSKIR2 A) & ( ex s be ElementSUBSET-1M1-of RAT+ARYTM-3K5 st s inTARSKIR2 A & r <ARYTM-3R4 s) })"
   sorry

mlemma
"REAL+ARYTM-2K2 =XBOOLE-0R4 RAT+ARYTM-3K5 \\/XBOOLE-0K2 ((({A where A be SubsetSUBSET-1M2-of RAT+ARYTM-3K5 :  for r be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds r inTARSKIR2 A implies ( for s be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds s <='ARYTM-3R3 r implies s inTARSKIR2 A) & ( ex s be ElementSUBSET-1M1-of RAT+ARYTM-3K5 st s inTARSKIR2 A & r <ARYTM-3R4 s) })\\SUBSET-1K6 {TARSKIK1 RAT+ARYTM-3K5 })\\SUBSET-1K7\<^bsub>({A where A be SubsetSUBSET-1M2-of RAT+ARYTM-3K5 :  for r be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds  not (r inTARSKIR2 A &  not (( for s be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds  not (s <='ARYTM-3R3 r &  not s inTARSKIR2 A)) &  not ( for s be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds  not (s inTARSKIR2 A &  not r <ARYTM-3R4 s)))) })\<^esub> ({{s where s be ElementSUBSET-1M1-of RAT+ARYTM-3K5 : s <ARYTM-3R4 t } where t be ElementSUBSET-1M1-of RAT+ARYTM-3K5 : t <>HIDDENR2 {}ARYTM-3K12 }))"
  using arytm_2_lm_2 xboole_1_th_87 sorry

mlemma arytm_2_lm_4:
"DEDEKIND-CUTSARYTM-2K1 \\SUBSET-1K7\<^bsub>(boolZFMISC-1K1 (RAT+ARYTM-3K5))\<^esub> ({{s where s be ElementSUBSET-1M1-of RAT+ARYTM-3K5 : s <ARYTM-3R4 t } where t be ElementSUBSET-1M1-of RAT+ARYTM-3K5 : t <>HIDDENR2 {}ARYTM-3K12 }) c=TARSKIR1 REAL+ARYTM-2K2"
  using xboole_1_th_7 sorry

mlemma arytm_2_lm_5:
"omegaORDINAL1K4 c=TARSKIR1 (({[TARSKIK4 c,d ] where c be ElementSUBSET-1M1-of omegaORDINAL1K4, d be ElementSUBSET-1M1-of omegaORDINAL1K4 : (c,d)are-coprimeARYTM-3R1 & d <>HIDDENR2 {}ARYTM-3K12 })\\SUBSET-1K6 ({[TARSKIK4 k,\<one>\<^sub>M ] where k be ElementSUBSET-1M1-of omegaORDINAL1K4 :  True  }))\\/XBOOLE-0K2 omegaORDINAL1K4"
  using xboole_1_th_7 sorry

mtheorem arytm_2_th_2:
"omegaORDINAL1K4 c=TARSKIR1 REAL+ARYTM-2K2"
  using arytm_2_lm_5 arytm_2_th_1 sorry

mtheorem arytm_2_cl_2:
"cluster REAL+ARYTM-2K2 as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "REAL+ARYTM-2K2 be  non emptyXBOOLE-0V1"
    using arytm_2_th_1 sorry
qed "sorry"

mdef arytm_2_def_3 ("DEDEKIND-CUTARYTM-2K3  _ " [230]230 ) where
  mlet "x be ElementSUBSET-1M1-of REAL+ARYTM-2K2"
"func DEDEKIND-CUTARYTM-2K3 x \<rightarrow> ElementSUBSET-1M3\<^bsub>(boolZFMISC-1K1 (RAT+ARYTM-3K5))\<^esub>-of DEDEKIND-CUTSARYTM-2K1 means
  \<lambda>it.  ex r be ElementSUBSET-1M1-of RAT+ARYTM-3K5 st x =XBOOLE-0R4 r & it =XBOOLE-0R4 {s where s be ElementSUBSET-1M1-of RAT+ARYTM-3K5 : s <ARYTM-3R4 r } if x inTARSKIR2 RAT+ARYTM-3K5 otherwise \<lambda>it. it =XBOOLE-0R4 x"
proof-
  (*existence*)
    show "(x inTARSKIR2 RAT+ARYTM-3K5 implies ( ex it be ElementSUBSET-1M3\<^bsub>(boolZFMISC-1K1 (RAT+ARYTM-3K5))\<^esub>-of DEDEKIND-CUTSARYTM-2K1 st  ex r be ElementSUBSET-1M1-of RAT+ARYTM-3K5 st x =XBOOLE-0R4 r & it =XBOOLE-0R4 {s where s be ElementSUBSET-1M1-of RAT+ARYTM-3K5 : s <ARYTM-3R4 r })) & ( not x inTARSKIR2 RAT+ARYTM-3K5 implies ( ex it be ElementSUBSET-1M3\<^bsub>(boolZFMISC-1K1 (RAT+ARYTM-3K5))\<^esub>-of DEDEKIND-CUTSARYTM-2K1 st it =XBOOLE-0R4 x))"
sorry
  (*uniqueness*)
    show " for it1 be ElementSUBSET-1M3\<^bsub>(boolZFMISC-1K1 (RAT+ARYTM-3K5))\<^esub>-of DEDEKIND-CUTSARYTM-2K1 holds  for it2 be ElementSUBSET-1M3\<^bsub>(boolZFMISC-1K1 (RAT+ARYTM-3K5))\<^esub>-of DEDEKIND-CUTSARYTM-2K1 holds (x inTARSKIR2 RAT+ARYTM-3K5 implies (( ex r be ElementSUBSET-1M1-of RAT+ARYTM-3K5 st x =XBOOLE-0R4 r & it1 =XBOOLE-0R4 {s where s be ElementSUBSET-1M1-of RAT+ARYTM-3K5 : s <ARYTM-3R4 r }) & ( ex r be ElementSUBSET-1M1-of RAT+ARYTM-3K5 st x =XBOOLE-0R4 r & it2 =XBOOLE-0R4 {s where s be ElementSUBSET-1M1-of RAT+ARYTM-3K5 : s <ARYTM-3R4 r }) implies it1 =HIDDENR1 it2)) & ( not x inTARSKIR2 RAT+ARYTM-3K5 implies (it1 =XBOOLE-0R4 x & it2 =XBOOLE-0R4 x implies it1 =HIDDENR1 it2))"
       sorry
  (*consistency*)
    show " for it be ElementSUBSET-1M3\<^bsub>(boolZFMISC-1K1 (RAT+ARYTM-3K5))\<^esub>-of DEDEKIND-CUTSARYTM-2K1 holds  True "
       sorry
qed "sorry"

mtheorem arytm_2_th_3:
" not ( ex y be objectHIDDENM1 st [TARSKIK4 {}ARYTM-3K12,y ] inHIDDENR3 REAL+ARYTM-2K2)"
sorry

mlemma arytm_2_lm_6:
" for s be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds  for t be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds ( for r be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds r <ARYTM-3R4 s iff r <ARYTM-3R4 t) implies s =XBOOLE-0R4 t"
sorry

mdef arytm_2_def_4 ("GLUEDARYTM-2K4  _ " [230]230 ) where
  mlet "x be ElementSUBSET-1M3\<^bsub>(boolZFMISC-1K1 (RAT+ARYTM-3K5))\<^esub>-of DEDEKIND-CUTSARYTM-2K1"
"func GLUEDARYTM-2K4 x \<rightarrow> ElementSUBSET-1M1-of REAL+ARYTM-2K2 means
  \<lambda>it.  ex r be ElementSUBSET-1M1-of RAT+ARYTM-3K5 st it =XBOOLE-0R4 r & ( for s be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds s inTARSKIR2 x iff s <ARYTM-3R4 r) if  ex r be ElementSUBSET-1M1-of RAT+ARYTM-3K5 st  for s be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds s inTARSKIR2 x iff s <ARYTM-3R4 r otherwise \<lambda>it. it =XBOOLE-0R4 x"
proof-
  (*uniqueness*)
    show " for it1 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for it2 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds (( ex r be ElementSUBSET-1M1-of RAT+ARYTM-3K5 st  for s be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds s inTARSKIR2 x iff s <ARYTM-3R4 r) implies (( ex r be ElementSUBSET-1M1-of RAT+ARYTM-3K5 st it1 =XBOOLE-0R4 r & ( for s be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds s inTARSKIR2 x iff s <ARYTM-3R4 r)) & ( ex r be ElementSUBSET-1M1-of RAT+ARYTM-3K5 st it2 =XBOOLE-0R4 r & ( for s be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds s inTARSKIR2 x iff s <ARYTM-3R4 r)) implies it1 =HIDDENR1 it2)) & ( not ( ex r be ElementSUBSET-1M1-of RAT+ARYTM-3K5 st  for s be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds s inTARSKIR2 x iff s <ARYTM-3R4 r) implies (it1 =XBOOLE-0R4 x & it2 =XBOOLE-0R4 x implies it1 =HIDDENR1 it2))"
sorry
  (*existence*)
    show "(( ex r be ElementSUBSET-1M1-of RAT+ARYTM-3K5 st  for s be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds s inTARSKIR2 x iff s <ARYTM-3R4 r) implies ( ex it be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st  ex r be ElementSUBSET-1M1-of RAT+ARYTM-3K5 st it =XBOOLE-0R4 r & ( for s be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds s inTARSKIR2 x iff s <ARYTM-3R4 r))) & ( not ( ex r be ElementSUBSET-1M1-of RAT+ARYTM-3K5 st  for s be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds s inTARSKIR2 x iff s <ARYTM-3R4 r) implies ( ex it be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st it =XBOOLE-0R4 x))"
sorry
  (*consistency*)
    show " for it be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  True "
       sorry
qed "sorry"

mlemma arytm_2_lm_7:
" for r be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds  for B be setHIDDENM2 holds B inTARSKIR2 DEDEKIND-CUTSARYTM-2K1 & r inTARSKIR2 B implies ( ex s be ElementSUBSET-1M1-of RAT+ARYTM-3K5 st s inTARSKIR2 B & r <ARYTM-3R4 s)"
sorry

mlemma arytm_2_lm_8:
"{}ARYTM-3K12 inTARSKIR2 DEDEKIND-CUTSARYTM-2K1"
sorry

mlemma arytm_2_lm_9:
"(DEDEKIND-CUTSARYTM-2K1)/\\SUBSET-1K8\<^bsub>(boolZFMISC-1K1 (RAT+ARYTM-3K5))\<^esub> (RAT+ARYTM-3K5) =XBOOLE-0R4 {TARSKIK1 {}ARYTM-3K12 }"
sorry

mlemma arytm_2_lm_10:
" for x be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds DEDEKIND-CUTARYTM-2K3 x =XBOOLE-0R4 {}ARYTM-3K12 iff x =XBOOLE-0R4 {}ARYTM-3K12"
sorry

mlemma arytm_2_lm_11:
" for A be ElementSUBSET-1M3\<^bsub>(boolZFMISC-1K1 (RAT+ARYTM-3K5))\<^esub>-of DEDEKIND-CUTSARYTM-2K1 holds GLUEDARYTM-2K4 A =XBOOLE-0R4 {}ARYTM-3K12 iff A =XBOOLE-0R4 {}ARYTM-3K12"
sorry

mlemma arytm_2_lm_12:
" for A be ElementSUBSET-1M3\<^bsub>(boolZFMISC-1K1 (RAT+ARYTM-3K5))\<^esub>-of DEDEKIND-CUTSARYTM-2K1 holds DEDEKIND-CUTARYTM-2K3 (GLUEDARYTM-2K4 A) =XBOOLE-0R4 A"
sorry

mlemma arytm_2_lm_13:
" for x be setHIDDENM2 holds  for y be setHIDDENM2 holds x inTARSKIR2 {A where A be SubsetSUBSET-1M2-of RAT+ARYTM-3K5 :  for r be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds r inTARSKIR2 A implies ( for s be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds s <='ARYTM-3R3 r implies s inTARSKIR2 A) & ( ex s be ElementSUBSET-1M1-of RAT+ARYTM-3K5 st s inTARSKIR2 A & r <ARYTM-3R4 s) } & y inTARSKIR2 {A where A be SubsetSUBSET-1M2-of RAT+ARYTM-3K5 :  for r be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds r inTARSKIR2 A implies ( for s be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds s <='ARYTM-3R3 r implies s inTARSKIR2 A) & ( ex s be ElementSUBSET-1M1-of RAT+ARYTM-3K5 st s inTARSKIR2 A & r <ARYTM-3R4 s) } implies x c=TARSKIR1 y or y c=TARSKIR1 x"
sorry

mdef arytm_2_def_5 (" _ <=''ARYTM-2R1  _ " [50,50]50 ) where
  mlet "x be ElementSUBSET-1M1-of REAL+ARYTM-2K2", "y be ElementSUBSET-1M1-of REAL+ARYTM-2K2"
"pred x <='ARYTM-2R1 y means
   ex x9 be ElementSUBSET-1M1-of RAT+ARYTM-3K5 st  ex y9 be ElementSUBSET-1M1-of RAT+ARYTM-3K5 st (x =XBOOLE-0R4 x9 & y =XBOOLE-0R4 y9) & x9 <='ARYTM-3R3 y9 if x inTARSKIR2 RAT+ARYTM-3K5 & y inTARSKIR2 RAT+ARYTM-3K5,
  x inTARSKIR2 y if x inTARSKIR2 RAT+ARYTM-3K5 &  not y inTARSKIR2 RAT+ARYTM-3K5,
   not y inTARSKIR2 x if  not x inTARSKIR2 RAT+ARYTM-3K5 & y inTARSKIR2 RAT+ARYTM-3K5 otherwise x c=TARSKIR1 y"
proof-
  (*consistency*)
    show "(((x inTARSKIR2 RAT+ARYTM-3K5 & y inTARSKIR2 RAT+ARYTM-3K5) & (x inTARSKIR2 RAT+ARYTM-3K5 &  not y inTARSKIR2 RAT+ARYTM-3K5) implies (( ex x9 be ElementSUBSET-1M1-of RAT+ARYTM-3K5 st  ex y9 be ElementSUBSET-1M1-of RAT+ARYTM-3K5 st (x =XBOOLE-0R4 x9 & y =XBOOLE-0R4 y9) & x9 <='ARYTM-3R3 y9) iff x inTARSKIR2 y)) & ((x inTARSKIR2 RAT+ARYTM-3K5 & y inTARSKIR2 RAT+ARYTM-3K5) & ( not x inTARSKIR2 RAT+ARYTM-3K5 & y inTARSKIR2 RAT+ARYTM-3K5) implies (( ex x9 be ElementSUBSET-1M1-of RAT+ARYTM-3K5 st  ex y9 be ElementSUBSET-1M1-of RAT+ARYTM-3K5 st (x =XBOOLE-0R4 x9 & y =XBOOLE-0R4 y9) & x9 <='ARYTM-3R3 y9) iff  not y inTARSKIR2 x))) & ((x inTARSKIR2 RAT+ARYTM-3K5 &  not y inTARSKIR2 RAT+ARYTM-3K5) & ( not x inTARSKIR2 RAT+ARYTM-3K5 & y inTARSKIR2 RAT+ARYTM-3K5) implies (x inTARSKIR2 y iff  not y inTARSKIR2 x))"
       sorry
qed "sorry"

mtheorem ARYTM_2R1_connectedness:
" for x be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for y be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  not x <='ARYTM-2R1 y implies y <='ARYTM-2R1 x"
sorry

syntax ARYTM_2R2 :: " Set \<Rightarrow>  Set \<Rightarrow> o" (" _ <ARYTM-2R2  _ " [50,50]50)
translations "y <ARYTM-2R2 x" \<rightharpoonup> " not x <='ARYTM-2R1 y"

mlemma arytm_2_lm_14:
" for x9 be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds  for y9 be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds  for x be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for y be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds x =XBOOLE-0R4 x9 & y =XBOOLE-0R4 y9 implies (x <='ARYTM-2R1 y iff x9 <='ARYTM-3R3 y9)"
sorry

mlemma arytm_2_lm_15:
" for B be setHIDDENM2 holds B inTARSKIR2 DEDEKIND-CUTSARYTM-2K1 & B <>HIDDENR2 {}ARYTM-3K12 implies ( ex r be ElementSUBSET-1M1-of RAT+ARYTM-3K5 st r inTARSKIR2 B & r <>HIDDENR2 {}ARYTM-3K12)"
sorry

mlemma arytm_2_lm_16:
" for r be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds  for s be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds  for B be setHIDDENM2 holds (B inTARSKIR2 DEDEKIND-CUTSARYTM-2K1 & r inTARSKIR2 B) & s <='ARYTM-3R3 r implies s inTARSKIR2 B"
sorry

mlemma arytm_2_lm_17:
" for B be setHIDDENM2 holds B inTARSKIR2 DEDEKIND-CUTSARYTM-2K1 & B <>HIDDENR2 {}ARYTM-3K12 implies {}ARYTM-3K12 inTARSKIR2 B"
sorry

mlemma arytm_2_lm_18:
" for r be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds  for B be setHIDDENM2 holds (B inTARSKIR2 DEDEKIND-CUTSARYTM-2K1 \\SUBSET-1K7\<^bsub>(boolZFMISC-1K1 (RAT+ARYTM-3K5))\<^esub> ({{s where s be ElementSUBSET-1M1-of RAT+ARYTM-3K5 : s <ARYTM-3R4 t } where t be ElementSUBSET-1M1-of RAT+ARYTM-3K5 : t <>HIDDENR2 {}ARYTM-3K12 }) &  not r inTARSKIR2 B) & B <>HIDDENR2 {}ARYTM-3K12 implies ( ex s be ElementSUBSET-1M1-of RAT+ARYTM-3K5 st  not s inTARSKIR2 B & s <ARYTM-3R4 r)"
sorry

mlemma arytm_2_lm_19:
" for x be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds DEDEKIND-CUTARYTM-2K3 x inTARSKIR2 {{s where s be ElementSUBSET-1M1-of RAT+ARYTM-3K5 : s <ARYTM-3R4 t } where t be ElementSUBSET-1M1-of RAT+ARYTM-3K5 : t <>HIDDENR2 {}ARYTM-3K12 } implies x inTARSKIR2 RAT+ARYTM-3K5"
sorry

mlemma arytm_2_lm_20:
" for x be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for y be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds DEDEKIND-CUTARYTM-2K3 x c=TARSKIR1 DEDEKIND-CUTARYTM-2K3 y implies x <='ARYTM-2R1 y"
sorry

mlemma arytm_2_lm_21:
" for x be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for y be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds x <='ARYTM-2R1 y & y <='ARYTM-2R1 x implies x =XBOOLE-0R4 y"
sorry

mlemma arytm_2_lm_22:
" for x be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for y be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds DEDEKIND-CUTARYTM-2K3 x =XBOOLE-0R4 DEDEKIND-CUTARYTM-2K3 y implies x =XBOOLE-0R4 y"
sorry

mlemma arytm_2_lm_23:
" for x be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds GLUEDARYTM-2K4 (DEDEKIND-CUTARYTM-2K3 x) =XBOOLE-0R4 x"
sorry

mdef arytm_2_def_6 (" _ +ARYTM-2K5  _ " [132,132]132 ) where
  mlet "A be ElementSUBSET-1M3\<^bsub>(boolZFMISC-1K1 (RAT+ARYTM-3K5))\<^esub>-of DEDEKIND-CUTSARYTM-2K1", "B be ElementSUBSET-1M3\<^bsub>(boolZFMISC-1K1 (RAT+ARYTM-3K5))\<^esub>-of DEDEKIND-CUTSARYTM-2K1"
"func A +ARYTM-2K5 B \<rightarrow> ElementSUBSET-1M3\<^bsub>(boolZFMISC-1K1 (RAT+ARYTM-3K5))\<^esub>-of DEDEKIND-CUTSARYTM-2K1 equals
  {r +ARYTM-3K10 s where r be ElementSUBSET-1M1-of RAT+ARYTM-3K5, s be ElementSUBSET-1M1-of RAT+ARYTM-3K5 : r inTARSKIR2 A & s inTARSKIR2 B }"
proof-
  (*coherence*)
    show "{r +ARYTM-3K10 s where r be ElementSUBSET-1M1-of RAT+ARYTM-3K5, s be ElementSUBSET-1M1-of RAT+ARYTM-3K5 : r inTARSKIR2 A & s inTARSKIR2 B } be ElementSUBSET-1M3\<^bsub>(boolZFMISC-1K1 (RAT+ARYTM-3K5))\<^esub>-of DEDEKIND-CUTSARYTM-2K1"
sorry
qed "sorry"

mtheorem ARYTM_2K5_commutativity:
" for A be ElementSUBSET-1M3\<^bsub>(boolZFMISC-1K1 (RAT+ARYTM-3K5))\<^esub>-of DEDEKIND-CUTSARYTM-2K1 holds  for B be ElementSUBSET-1M3\<^bsub>(boolZFMISC-1K1 (RAT+ARYTM-3K5))\<^esub>-of DEDEKIND-CUTSARYTM-2K1 holds A +ARYTM-2K5 B =HIDDENR1 B +ARYTM-2K5 A"
sorry

mlemma arytm_2_lm_24:
" for B be setHIDDENM2 holds B inTARSKIR2 DEDEKIND-CUTSARYTM-2K1 implies ( ex r be ElementSUBSET-1M1-of RAT+ARYTM-3K5 st  not r inTARSKIR2 B)"
sorry

mdef arytm_2_def_7 (" _ *''ARYTM-2K6  _ " [228,228]228 ) where
  mlet "A be ElementSUBSET-1M3\<^bsub>(boolZFMISC-1K1 (RAT+ARYTM-3K5))\<^esub>-of DEDEKIND-CUTSARYTM-2K1", "B be ElementSUBSET-1M3\<^bsub>(boolZFMISC-1K1 (RAT+ARYTM-3K5))\<^esub>-of DEDEKIND-CUTSARYTM-2K1"
"func A *'ARYTM-2K6 B \<rightarrow> ElementSUBSET-1M3\<^bsub>(boolZFMISC-1K1 (RAT+ARYTM-3K5))\<^esub>-of DEDEKIND-CUTSARYTM-2K1 equals
  {r *'ARYTM-3K11 s where r be ElementSUBSET-1M1-of RAT+ARYTM-3K5, s be ElementSUBSET-1M1-of RAT+ARYTM-3K5 : r inTARSKIR2 A & s inTARSKIR2 B }"
proof-
  (*coherence*)
    show "{r *'ARYTM-3K11 s where r be ElementSUBSET-1M1-of RAT+ARYTM-3K5, s be ElementSUBSET-1M1-of RAT+ARYTM-3K5 : r inTARSKIR2 A & s inTARSKIR2 B } be ElementSUBSET-1M3\<^bsub>(boolZFMISC-1K1 (RAT+ARYTM-3K5))\<^esub>-of DEDEKIND-CUTSARYTM-2K1"
sorry
qed "sorry"

mtheorem ARYTM_2K6_commutativity:
" for A be ElementSUBSET-1M3\<^bsub>(boolZFMISC-1K1 (RAT+ARYTM-3K5))\<^esub>-of DEDEKIND-CUTSARYTM-2K1 holds  for B be ElementSUBSET-1M3\<^bsub>(boolZFMISC-1K1 (RAT+ARYTM-3K5))\<^esub>-of DEDEKIND-CUTSARYTM-2K1 holds A *'ARYTM-2K6 B =HIDDENR1 B *'ARYTM-2K6 A"
sorry

mdef arytm_2_def_8 (" _ +ARYTM-2K7  _ " [132,132]132 ) where
  mlet "x be ElementSUBSET-1M1-of REAL+ARYTM-2K2", "y be ElementSUBSET-1M1-of REAL+ARYTM-2K2"
"func x +ARYTM-2K7 y \<rightarrow> ElementSUBSET-1M1-of REAL+ARYTM-2K2 equals
  x if y =XBOOLE-0R4 {}ARYTM-3K12,
  y if x =XBOOLE-0R4 {}ARYTM-3K12 otherwise GLUEDARYTM-2K4 (DEDEKIND-CUTARYTM-2K3 x +ARYTM-2K5 DEDEKIND-CUTARYTM-2K3 y)"
proof-
  (*coherence*)
    show "(y =XBOOLE-0R4 {}ARYTM-3K12 implies x be ElementSUBSET-1M1-of REAL+ARYTM-2K2) & ((x =XBOOLE-0R4 {}ARYTM-3K12 implies y be ElementSUBSET-1M1-of REAL+ARYTM-2K2) & ( not y =XBOOLE-0R4 {}ARYTM-3K12 &  not x =XBOOLE-0R4 {}ARYTM-3K12 implies GLUEDARYTM-2K4 (DEDEKIND-CUTARYTM-2K3 x +ARYTM-2K5 DEDEKIND-CUTARYTM-2K3 y) be ElementSUBSET-1M1-of REAL+ARYTM-2K2))"
       sorry
  (*consistency*)
    show " for it be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds y =XBOOLE-0R4 {}ARYTM-3K12 & x =XBOOLE-0R4 {}ARYTM-3K12 implies (it =HIDDENR1 x iff it =HIDDENR1 y)"
       sorry
qed "sorry"

mtheorem ARYTM_2K7_commutativity:
" for x be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for y be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds x +ARYTM-2K7 y =HIDDENR1 y +ARYTM-2K7 x"
sorry

mdef arytm_2_def_9 (" _ *''ARYTM-2K8  _ " [228,228]228 ) where
  mlet "x be ElementSUBSET-1M1-of REAL+ARYTM-2K2", "y be ElementSUBSET-1M1-of REAL+ARYTM-2K2"
"func x *'ARYTM-2K8 y \<rightarrow> ElementSUBSET-1M1-of REAL+ARYTM-2K2 equals
  GLUEDARYTM-2K4 (DEDEKIND-CUTARYTM-2K3 x *'ARYTM-2K6 DEDEKIND-CUTARYTM-2K3 y)"
proof-
  (*coherence*)
    show "GLUEDARYTM-2K4 (DEDEKIND-CUTARYTM-2K3 x *'ARYTM-2K6 DEDEKIND-CUTARYTM-2K3 y) be ElementSUBSET-1M1-of REAL+ARYTM-2K2"
       sorry
qed "sorry"

mtheorem ARYTM_2K8_commutativity:
" for x be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for y be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds x *'ARYTM-2K8 y =HIDDENR1 y *'ARYTM-2K8 x"
sorry

mtheorem arytm_2_th_4:
" for x be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for y be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds x =XBOOLE-0R4 {}ARYTM-3K12 implies x *'ARYTM-2K8 y =XBOOLE-0R4 {}ARYTM-3K12"
sorry

mtheorem arytm_2_th_5:
" for x be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for y be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds x +ARYTM-2K7 y =XBOOLE-0R4 {}ARYTM-3K12 implies x =XBOOLE-0R4 {}ARYTM-3K12"
sorry

mlemma arytm_2_lm_25:
" for A be ElementSUBSET-1M3\<^bsub>(boolZFMISC-1K1 (RAT+ARYTM-3K5))\<^esub>-of DEDEKIND-CUTSARYTM-2K1 holds  for B be ElementSUBSET-1M3\<^bsub>(boolZFMISC-1K1 (RAT+ARYTM-3K5))\<^esub>-of DEDEKIND-CUTSARYTM-2K1 holds  for C be ElementSUBSET-1M3\<^bsub>(boolZFMISC-1K1 (RAT+ARYTM-3K5))\<^esub>-of DEDEKIND-CUTSARYTM-2K1 holds A +ARYTM-2K5 (B +ARYTM-2K5 C) c=TARSKIR1 (A +ARYTM-2K5 B)+ARYTM-2K5 C"
sorry

mlemma arytm_2_lm_26:
" for A be ElementSUBSET-1M3\<^bsub>(boolZFMISC-1K1 (RAT+ARYTM-3K5))\<^esub>-of DEDEKIND-CUTSARYTM-2K1 holds  for B be ElementSUBSET-1M3\<^bsub>(boolZFMISC-1K1 (RAT+ARYTM-3K5))\<^esub>-of DEDEKIND-CUTSARYTM-2K1 holds  for C be ElementSUBSET-1M3\<^bsub>(boolZFMISC-1K1 (RAT+ARYTM-3K5))\<^esub>-of DEDEKIND-CUTSARYTM-2K1 holds A +ARYTM-2K5 (B +ARYTM-2K5 C) =XBOOLE-0R4 (A +ARYTM-2K5 B)+ARYTM-2K5 C"
  using arytm_2_lm_25 sorry

mlemma arytm_2_lm_27:
" for A be ElementSUBSET-1M3\<^bsub>(boolZFMISC-1K1 (RAT+ARYTM-3K5))\<^esub>-of DEDEKIND-CUTSARYTM-2K1 holds  for B be ElementSUBSET-1M3\<^bsub>(boolZFMISC-1K1 (RAT+ARYTM-3K5))\<^esub>-of DEDEKIND-CUTSARYTM-2K1 holds A +ARYTM-2K5 B =XBOOLE-0R4 {}ARYTM-3K12 implies A =XBOOLE-0R4 {}ARYTM-3K12 or B =XBOOLE-0R4 {}ARYTM-3K12"
sorry

mtheorem arytm_2_th_6:
" for x be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for y be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for z be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds x +ARYTM-2K7 (y +ARYTM-2K7 z) =XBOOLE-0R4 (x +ARYTM-2K7 y)+ARYTM-2K7 z"
sorry

mtheorem arytm_2_th_7:
"{A where A be SubsetSUBSET-1M2-of RAT+ARYTM-3K5 :  for r be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds r inTARSKIR2 A implies ( for s be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds s <='ARYTM-3R3 r implies s inTARSKIR2 A) & ( ex s be ElementSUBSET-1M1-of RAT+ARYTM-3K5 st s inTARSKIR2 A & r <ARYTM-3R4 s) } be c=-linearORDINAL1V6"
sorry

mlemma arytm_2_lm_28:
" for e be setHIDDENM2 holds e inTARSKIR2 REAL+ARYTM-2K2 implies e <>HIDDENR2 RAT+ARYTM-3K5"
sorry

mlemma arytm_2_lm_29:
" for r be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds  for s be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds  for B be setHIDDENM2 holds (B inTARSKIR2 {A where A be SubsetSUBSET-1M2-of RAT+ARYTM-3K5 :  for r be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds r inTARSKIR2 A implies ( for s be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds s <='ARYTM-3R3 r implies s inTARSKIR2 A) & ( ex s be ElementSUBSET-1M1-of RAT+ARYTM-3K5 st s inTARSKIR2 A & r <ARYTM-3R4 s) } & r inTARSKIR2 B) & s <='ARYTM-3R3 r implies s inTARSKIR2 B"
sorry

mlemma arytm_2_lm_30:
" for x be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for y be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds y <ARYTM-2R2 x implies ( ex z be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st (z inTARSKIR2 RAT+ARYTM-3K5 & z <ARYTM-2R2 x) & y <ARYTM-2R2 z)"
sorry

mlemma arytm_2_lm_31:
" for x be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for y be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for z be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds x <='ARYTM-2R1 y & y <='ARYTM-2R1 z implies x <='ARYTM-2R1 z"
sorry

mtheorem arytm_2_th_8:
" for X be SubsetSUBSET-1M2-of REAL+ARYTM-2K2 holds  for Y be SubsetSUBSET-1M2-of REAL+ARYTM-2K2 holds ( ex x be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st x inTARSKIR2 Y) & ( for x be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for y be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds x inTARSKIR2 X & y inTARSKIR2 Y implies x <='ARYTM-2R1 y) implies ( ex z be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st  for x be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for y be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds x inTARSKIR2 X & y inTARSKIR2 Y implies x <='ARYTM-2R1 z & z <='ARYTM-2R1 y)"
sorry

mlemma arytm_2_lm_32:
"oneARYTM-3K13 =XBOOLE-0R4 \<one>\<^sub>M"
   sorry

mlemma arytm_2_lm_33:
"{}ARYTM-3K12 =XBOOLE-0R4 {}ARYTM-3K12"
   sorry

mlemma arytm_2_lm_34:
" for A be ElementSUBSET-1M3\<^bsub>(boolZFMISC-1K1 (RAT+ARYTM-3K5))\<^esub>-of DEDEKIND-CUTSARYTM-2K1 holds  for B be ElementSUBSET-1M3\<^bsub>(boolZFMISC-1K1 (RAT+ARYTM-3K5))\<^esub>-of DEDEKIND-CUTSARYTM-2K1 holds A +ARYTM-2K5 B =XBOOLE-0R4 A & A <>HIDDENR2 {}ARYTM-3K12 implies B =XBOOLE-0R4 {}ARYTM-3K12"
sorry

mlemma arytm_2_lm_35:
" for x be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for y be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds x +ARYTM-2K7 y =XBOOLE-0R4 x implies y =XBOOLE-0R4 {}ARYTM-3K12"
sorry

mlemma arytm_2_lm_36:
" for A be ElementSUBSET-1M3\<^bsub>(boolZFMISC-1K1 (RAT+ARYTM-3K5))\<^esub>-of DEDEKIND-CUTSARYTM-2K1 holds  for B be ElementSUBSET-1M3\<^bsub>(boolZFMISC-1K1 (RAT+ARYTM-3K5))\<^esub>-of DEDEKIND-CUTSARYTM-2K1 holds (A <>HIDDENR2 {}ARYTM-3K12 & A c=TARSKIR1 B) & A <>HIDDENR2 B implies ( ex C be ElementSUBSET-1M3\<^bsub>(boolZFMISC-1K1 (RAT+ARYTM-3K5))\<^esub>-of DEDEKIND-CUTSARYTM-2K1 st A +ARYTM-2K5 C =XBOOLE-0R4 B)"
sorry

mlemma arytm_2_lm_37:
" for x be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for y be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds x <='ARYTM-2R1 y implies DEDEKIND-CUTARYTM-2K3 x c=TARSKIR1 DEDEKIND-CUTARYTM-2K3 y"
sorry

mtheorem arytm_2_th_9:
" for x be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for y be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds x <='ARYTM-2R1 y implies ( ex z be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st x +ARYTM-2K7 z =XBOOLE-0R4 y)"
sorry

mtheorem arytm_2_th_10:
" for x be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for y be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  ex z be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st x +ARYTM-2K7 z =XBOOLE-0R4 y or y +ARYTM-2K7 z =XBOOLE-0R4 x"
sorry

mtheorem arytm_2_th_11:
" for x be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for y be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for z be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds x +ARYTM-2K7 y =XBOOLE-0R4 x +ARYTM-2K7 z implies y =XBOOLE-0R4 z"
sorry

mlemma arytm_2_lm_38:
" for A be ElementSUBSET-1M3\<^bsub>(boolZFMISC-1K1 (RAT+ARYTM-3K5))\<^esub>-of DEDEKIND-CUTSARYTM-2K1 holds  for B be ElementSUBSET-1M3\<^bsub>(boolZFMISC-1K1 (RAT+ARYTM-3K5))\<^esub>-of DEDEKIND-CUTSARYTM-2K1 holds  for C be ElementSUBSET-1M3\<^bsub>(boolZFMISC-1K1 (RAT+ARYTM-3K5))\<^esub>-of DEDEKIND-CUTSARYTM-2K1 holds A *'ARYTM-2K6 (B *'ARYTM-2K6 C) c=TARSKIR1 (A *'ARYTM-2K6 B)*'ARYTM-2K6 C"
sorry

mlemma arytm_2_lm_39:
" for A be ElementSUBSET-1M3\<^bsub>(boolZFMISC-1K1 (RAT+ARYTM-3K5))\<^esub>-of DEDEKIND-CUTSARYTM-2K1 holds  for B be ElementSUBSET-1M3\<^bsub>(boolZFMISC-1K1 (RAT+ARYTM-3K5))\<^esub>-of DEDEKIND-CUTSARYTM-2K1 holds  for C be ElementSUBSET-1M3\<^bsub>(boolZFMISC-1K1 (RAT+ARYTM-3K5))\<^esub>-of DEDEKIND-CUTSARYTM-2K1 holds A *'ARYTM-2K6 (B *'ARYTM-2K6 C) =XBOOLE-0R4 (A *'ARYTM-2K6 B)*'ARYTM-2K6 C"
  using arytm_2_lm_38 sorry

mtheorem arytm_2_th_12:
" for x be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for y be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for z be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds x *'ARYTM-2K8 (y *'ARYTM-2K8 z) =XBOOLE-0R4 (x *'ARYTM-2K8 y)*'ARYTM-2K8 z"
sorry

mlemma arytm_2_lm_40:
" for x be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for y be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds x *'ARYTM-2K8 y =XBOOLE-0R4 {}ARYTM-3K12 implies x =XBOOLE-0R4 {}ARYTM-3K12 or y =XBOOLE-0R4 {}ARYTM-3K12"
sorry

mlemma arytm_2_lm_41:
" for A be ElementSUBSET-1M3\<^bsub>(boolZFMISC-1K1 (RAT+ARYTM-3K5))\<^esub>-of DEDEKIND-CUTSARYTM-2K1 holds  for B be ElementSUBSET-1M3\<^bsub>(boolZFMISC-1K1 (RAT+ARYTM-3K5))\<^esub>-of DEDEKIND-CUTSARYTM-2K1 holds  for C be ElementSUBSET-1M3\<^bsub>(boolZFMISC-1K1 (RAT+ARYTM-3K5))\<^esub>-of DEDEKIND-CUTSARYTM-2K1 holds A *'ARYTM-2K6 (B +ARYTM-2K5 C) =XBOOLE-0R4 A *'ARYTM-2K6 B +ARYTM-2K5 A *'ARYTM-2K6 C"
sorry

mtheorem arytm_2_th_13:
" for x be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for y be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for z be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds x *'ARYTM-2K8 (y +ARYTM-2K7 z) =XBOOLE-0R4 x *'ARYTM-2K8 y +ARYTM-2K7 x *'ARYTM-2K8 z"
sorry

mlemma arytm_2_lm_42:
" for B be setHIDDENM2 holds B inTARSKIR2 {A where A be SubsetSUBSET-1M2-of RAT+ARYTM-3K5 :  for r be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds r inTARSKIR2 A implies ( for s be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds s <='ARYTM-3R3 r implies s inTARSKIR2 A) & ( ex s be ElementSUBSET-1M1-of RAT+ARYTM-3K5 st s inTARSKIR2 A & r <ARYTM-3R4 s) } & B <>HIDDENR2 {}ARYTM-3K12 implies ( ex r be ElementSUBSET-1M1-of RAT+ARYTM-3K5 st r inTARSKIR2 B & r <>HIDDENR2 {}ARYTM-3K12)"
sorry

mlemma arytm_2_lm_43:
" for rone be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds rone =XBOOLE-0R4 oneARYTM-3K13 implies ( for A be ElementSUBSET-1M3\<^bsub>(boolZFMISC-1K1 (RAT+ARYTM-3K5))\<^esub>-of DEDEKIND-CUTSARYTM-2K1 holds A <>HIDDENR2 {}ARYTM-3K12 implies ( ex B be ElementSUBSET-1M3\<^bsub>(boolZFMISC-1K1 (RAT+ARYTM-3K5))\<^esub>-of DEDEKIND-CUTSARYTM-2K1 st A *'ARYTM-2K6 B =XBOOLE-0R4 DEDEKIND-CUTARYTM-2K3 rone))"
sorry

mtheorem arytm_2_th_14:
" for x be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds x <>HIDDENR2 {}ARYTM-3K12 implies ( ex y be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st x *'ARYTM-2K8 y =XBOOLE-0R4 oneARYTM-3K13)"
sorry

mlemma arytm_2_lm_44:
" for A be ElementSUBSET-1M3\<^bsub>(boolZFMISC-1K1 (RAT+ARYTM-3K5))\<^esub>-of DEDEKIND-CUTSARYTM-2K1 holds  for B be ElementSUBSET-1M3\<^bsub>(boolZFMISC-1K1 (RAT+ARYTM-3K5))\<^esub>-of DEDEKIND-CUTSARYTM-2K1 holds A =XBOOLE-0R4 {r where r be ElementSUBSET-1M1-of RAT+ARYTM-3K5 : r <ARYTM-3R4 oneARYTM-3K13 } implies A *'ARYTM-2K6 B =XBOOLE-0R4 B"
sorry

mtheorem arytm_2_th_15:
" for x be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for y be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds x =XBOOLE-0R4 oneARYTM-3K13 implies x *'ARYTM-2K8 y =XBOOLE-0R4 y"
sorry

mlemma arytm_2_lm_45:
" for i be ElementSUBSET-1M1-of omegaORDINAL1K4 holds  for j be ElementSUBSET-1M1-of omegaORDINAL1K4 holds  for x9 be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds  for y9 be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds i =XBOOLE-0R4 x9 & j =XBOOLE-0R4 y9 implies i +^ORDINAL2K10 j =XBOOLE-0R4 x9 +ARYTM-3K10 y9"
sorry

mlemma arytm_2_lm_46:
" for x9 be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds  for y9 be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds  for z9 be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds (z9 <ARYTM-3R4 x9 +ARYTM-3K10 y9 & x9 <>HIDDENR2 {}ARYTM-3K12) & y9 <>HIDDENR2 {}ARYTM-3K12 implies ( ex r be ElementSUBSET-1M1-of RAT+ARYTM-3K5 st  ex s be ElementSUBSET-1M1-of RAT+ARYTM-3K5 st (z9 =XBOOLE-0R4 r +ARYTM-3K10 s & r <ARYTM-3R4 x9) & s <ARYTM-3R4 y9)"
sorry

mlemma arytm_2_lm_47:
" for x be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for y be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds x inTARSKIR2 RAT+ARYTM-3K5 & y inTARSKIR2 RAT+ARYTM-3K5 implies ( ex x9 be ElementSUBSET-1M1-of RAT+ARYTM-3K5 st  ex y9 be ElementSUBSET-1M1-of RAT+ARYTM-3K5 st (x =XBOOLE-0R4 x9 & y =XBOOLE-0R4 y9) & x +ARYTM-2K7 y =XBOOLE-0R4 x9 +ARYTM-3K10 y9)"
sorry

mtheorem arytm_2_th_16:
" for x be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for y be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds x inTARSKIR2 omegaORDINAL1K4 & y inTARSKIR2 omegaORDINAL1K4 implies y +ARYTM-2K7 x inTARSKIR2 omegaORDINAL1K4"
sorry

mtheorem arytm_2_th_17:
" for A be SubsetSUBSET-1M2-of REAL+ARYTM-2K2 holds 0ORDINAL1K5 inTARSKIR2 A & ( for x be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for y be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds x inTARSKIR2 A & y =XBOOLE-0R4 oneARYTM-3K13 implies x +ARYTM-2K7 y inTARSKIR2 A) implies omegaORDINAL1K4 c=TARSKIR1 A"
sorry

mtheorem arytm_2_th_18:
" for x be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds x inTARSKIR2 omegaORDINAL1K4 implies ( for y be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds y inTARSKIR2 x iff (y inTARSKIR2 omegaORDINAL1K4 & y <>HIDDENR2 x) & y <='ARYTM-2R1 x)"
sorry

mtheorem arytm_2_th_19:
" for x be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for y be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for z be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds x =XBOOLE-0R4 y +ARYTM-2K7 z implies z <='ARYTM-2R1 x"
sorry

mtheorem arytm_2_th_20:
"{}ARYTM-3K12 inTARSKIR2 REAL+ARYTM-2K2 & oneARYTM-3K13 inTARSKIR2 REAL+ARYTM-2K2"
  using arytm_2_th_1 sorry

mtheorem arytm_2_th_21:
" for x be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds  for y be ElementSUBSET-1M1-of REAL+ARYTM-2K2 holds x inTARSKIR2 RAT+ARYTM-3K5 & y inTARSKIR2 RAT+ARYTM-3K5 implies ( ex x9 be ElementSUBSET-1M1-of RAT+ARYTM-3K5 st  ex y9 be ElementSUBSET-1M1-of RAT+ARYTM-3K5 st (x =XBOOLE-0R4 x9 & y =XBOOLE-0R4 y9) & x *'ARYTM-2K8 y =XBOOLE-0R4 x9 *'ARYTM-3K11 y9)"
sorry

end
