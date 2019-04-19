theory eqrel_1
  imports domain_1 finseq_1 orders_1 setwiseo
   "../mizar_extension/E_number"
begin
(*begin*)
reserve X, Y, Z for "setHIDDENM2"
reserve x, y, z for "objectHIDDENM1"
reserve i, j for "NatNAT-1M1"
reserve A, B, C for "SubsetSUBSET-1M2-of X"
reserve R, R1, R2 for "RelationRELSET-1M2-of X"
reserve AX for "SubsetSUBSET-1M2-of [:ZFMISC-1K2 X,X :]"
reserve SFXX for "Subset-FamilySETFAM-1M1-of [:ZFMISC-1K2 X,X :]"
mdef eqrel_1_def_1 ("nablaEQREL-1K1  _ " [164]164 ) where
  mlet "X be setHIDDENM2"
"func nablaEQREL-1K1 X \<rightarrow> RelationRELSET-1M2-of X equals
  [:ZFMISC-1K2 X,X :]"
proof-
  (*coherence*)
    show "[:ZFMISC-1K2 X,X :] be RelationRELSET-1M2-of X"
sorry
qed "sorry"

mtheorem eqrel_1_cl_1:
  mlet "X be setHIDDENM2"
"cluster nablaEQREL-1K1 X as-term-is totalPARTFUN1V1\<^bsub>(X)\<^esub>\<bar>reflexiveRELAT-2V1"
proof
(*coherence*)
  show "nablaEQREL-1K1 X be totalPARTFUN1V1\<^bsub>(X)\<^esub>\<bar>reflexiveRELAT-2V1"
sorry
qed "sorry"

syntax EQREL_1K2 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ '/'\\EQREL-1K2\<^bsub>'( _ ')\<^esub>  _ " [164,0,164]164)
translations "R1 /\\EQREL-1K2\<^bsub>(X)\<^esub> R2" \<rightharpoonup> "R1 /\\XBOOLE-0K3 R2"

mtheorem eqrel_1_add_1:
  mlet "X be setHIDDENM2", "R1 be RelationRELSET-1M2-of X", "R2 be RelationRELSET-1M2-of X"
"cluster R1 /\\XBOOLE-0K3 R2 as-term-is RelationRELSET-1M2-of X"
proof
(*coherence*)
  show "R1 /\\XBOOLE-0K3 R2 be RelationRELSET-1M2-of X"
sorry
qed "sorry"

syntax EQREL_1K3 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ '\\'/EQREL-1K3\<^bsub>'( _ ')\<^esub>  _ " [132,0,132]132)
translations "R1 \\/EQREL-1K3\<^bsub>(X)\<^esub> R2" \<rightharpoonup> "R1 \\/XBOOLE-0K2 R2"

mtheorem eqrel_1_add_2:
  mlet "X be setHIDDENM2", "R1 be RelationRELSET-1M2-of X", "R2 be RelationRELSET-1M2-of X"
"cluster R1 \\/XBOOLE-0K2 R2 as-term-is RelationRELSET-1M2-of X"
proof
(*coherence*)
  show "R1 \\/XBOOLE-0K2 R2 be RelationRELSET-1M2-of X"
sorry
qed "sorry"

mtheorem eqrel_1_th_1:
" for X be setHIDDENM2 holds  for R1 be RelationRELSET-1M2-of X holds nablaEQREL-1K1 X \\/EQREL-1K3\<^bsub>(X)\<^esub> R1 =RELSET-1R2\<^bsub>(X,X)\<^esub> nablaEQREL-1K1 X"
  using xboole_1_th_12 sorry

mtheorem eqrel_1_th_2:
" for X be setHIDDENM2 holds (idPARTFUN1K6 X is-reflexive-inRELAT-2R1 X & idPARTFUN1K6 X is-symmetric-inRELAT-2R3 X) & idPARTFUN1K6 X is-transitive-inRELAT-2R8 X"
  using relat_1_def_10 sorry

syntax EQREL_1M1 :: " Set \<Rightarrow> Ty" ("ToleranceEQREL-1M1-of  _ " [70]70)
translations "ToleranceEQREL-1M1-of X" \<rightharpoonup> "totalPARTFUN1V1\<^bsub>(X)\<^esub>\<bar>reflexiveRELAT-2V1\<bar>symmetricRELAT-2V3\<bar>RelationRELSET-1M2-of X"

syntax EQREL_1M2 :: " Set \<Rightarrow> Ty" ("Equivalence-RelationEQREL-1M2-of  _ " [70]70)
translations "Equivalence-RelationEQREL-1M2-of X" \<rightharpoonup> "totalPARTFUN1V1\<^bsub>(X)\<^esub>\<bar>symmetricRELAT-2V3\<bar>transitiveRELAT-2V8\<bar>RelationRELSET-1M2-of X"

mtheorem eqrel_1_th_3:
" for X be setHIDDENM2 holds idPARTFUN1K6 X be Equivalence-RelationEQREL-1M2-of X"
   sorry

mtheorem eqrel_1_th_4:
" for X be setHIDDENM2 holds nablaEQREL-1K1 X be Equivalence-RelationEQREL-1M2-of X"
sorry

mtheorem eqrel_1_cl_2:
  mlet "X be setHIDDENM2"
"cluster nablaEQREL-1K1 X as-term-is totalPARTFUN1V1\<^bsub>(X)\<^esub>\<bar>symmetricRELAT-2V3\<bar>transitiveRELAT-2V8"
proof
(*coherence*)
  show "nablaEQREL-1K1 X be totalPARTFUN1V1\<^bsub>(X)\<^esub>\<bar>symmetricRELAT-2V3\<bar>transitiveRELAT-2V8"
    using eqrel_1_th_4 sorry
qed "sorry"

reserve EqR, EqR1, EqR2, EqR3 for "Equivalence-RelationEQREL-1M2-of X"
mlemma eqrel_1_lm_1:
" for X be setHIDDENM2 holds  for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for R be RelationRELSET-1M2-of X holds [TARSKIK4 x,y ] inHIDDENR3 R implies x inHIDDENR3 X & y inHIDDENR3 X"
sorry

mtheorem eqrel_1_th_5:
" for X be setHIDDENM2 holds  for x be objectHIDDENM1 holds  for R be totalPARTFUN1V1\<^bsub>(X)\<^esub>\<bar>reflexiveRELAT-2V1\<bar>RelationRELSET-1M2-of X holds x inHIDDENR3 X implies [TARSKIK4 x,x ] inHIDDENR3 R"
sorry

mtheorem eqrel_1_th_6:
" for X be setHIDDENM2 holds  for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for R be totalPARTFUN1V1\<^bsub>(X)\<^esub>\<bar>symmetricRELAT-2V3\<bar>RelationRELSET-1M2-of X holds [TARSKIK4 x,y ] inHIDDENR3 R implies [TARSKIK4 y,x ] inHIDDENR3 R"
sorry

mtheorem eqrel_1_th_7:
" for X be setHIDDENM2 holds  for z be objectHIDDENM1 holds  for R be totalPARTFUN1V1\<^bsub>(X)\<^esub>\<bar>transitiveRELAT-2V8\<bar>RelationRELSET-1M2-of X holds  for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds [TARSKIK4 x,y ] inHIDDENR3 R & [TARSKIK4 y,z ] inHIDDENR3 R implies [TARSKIK4 x,z ] inHIDDENR3 R"
sorry

mtheorem eqrel_1_th_8:
" for X be setHIDDENM2 holds  for R be totalPARTFUN1V1\<^bsub>(X)\<^esub>\<bar>reflexiveRELAT-2V1\<bar>RelationRELSET-1M2-of X holds ( ex x be setHIDDENM2 st x inTARSKIR2 X) implies R <>HIDDENR2 {}XBOOLE-0K1"
   sorry

mtheorem eqrel_1_th_9:
" for X be setHIDDENM2 holds  for R be RelationRELSET-1M2-of X holds R be Equivalence-RelationEQREL-1M2-of X iff R be reflexiveRELAT-2V1\<bar>symmetricRELAT-2V3\<bar>transitiveRELAT-2V8 & fieldRELAT-1K3 R =XBOOLE-0R4 X"
  using orders_1_th_12 orders_1_th_13 partfun1_def_2 sorry

syntax EQREL_1K4 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ '/'\\EQREL-1K4\<^bsub>'( _ ')\<^esub>  _ " [164,0,164]164)
translations "EqR1 /\\EQREL-1K4\<^bsub>(X)\<^esub> EqR2" \<rightharpoonup> "EqR1 /\\XBOOLE-0K3 EqR2"

mtheorem eqrel_1_add_3:
  mlet "X be setHIDDENM2", "EqR1 be Equivalence-RelationEQREL-1M2-of X", "EqR2 be Equivalence-RelationEQREL-1M2-of X"
"cluster EqR1 /\\XBOOLE-0K3 EqR2 as-term-is Equivalence-RelationEQREL-1M2-of X"
proof
(*coherence*)
  show "EqR1 /\\XBOOLE-0K3 EqR2 be Equivalence-RelationEQREL-1M2-of X"
sorry
qed "sorry"

mtheorem eqrel_1_th_10:
" for X be setHIDDENM2 holds  for EqR be Equivalence-RelationEQREL-1M2-of X holds idPARTFUN1K6 X /\\EQREL-1K4\<^bsub>(X)\<^esub> EqR =RELSET-1R2\<^bsub>(X,X)\<^esub> idPARTFUN1K6 X"
sorry

mtheorem eqrel_1_th_11:
" for X be setHIDDENM2 holds  for SFXX be Subset-FamilySETFAM-1M1-of [:ZFMISC-1K2 X,X :] holds SFXX <>HIDDENR2 {}XBOOLE-0K1 & ( for Y be setHIDDENM2 holds Y inTARSKIR2 SFXX implies Y be Equivalence-RelationEQREL-1M2-of X) implies meetSETFAM-1K6\<^bsub>([:ZFMISC-1K2 X,X :])\<^esub> SFXX be Equivalence-RelationEQREL-1M2-of X"
sorry

mtheorem eqrel_1_th_12:
" for X be setHIDDENM2 holds  for R be RelationRELSET-1M2-of X holds  ex EqR be Equivalence-RelationEQREL-1M2-of X st R c=RELSET-1R1\<^bsub>(X,X)\<^esub> EqR & ( for EqR2 be Equivalence-RelationEQREL-1M2-of X holds R c=RELSET-1R1\<^bsub>(X,X)\<^esub> EqR2 implies EqR c=RELSET-1R1\<^bsub>(X,X)\<^esub> EqR2)"
sorry

mdef eqrel_1_def_2 (" _ \<inverse>'\\'/\<inverse>EQREL-1K5\<^bsub>'( _ ')\<^esub>  _ " [164,0,164]164 ) where
  mlet "X be setHIDDENM2", "EqR1 be Equivalence-RelationEQREL-1M2-of X", "EqR2 be Equivalence-RelationEQREL-1M2-of X"
"func EqR1 \<inverse>\\/\<inverse>EQREL-1K5\<^bsub>(X)\<^esub> EqR2 \<rightarrow> Equivalence-RelationEQREL-1M2-of X means
  \<lambda>it. EqR1 \\/EQREL-1K3\<^bsub>(X)\<^esub> EqR2 c=RELSET-1R1\<^bsub>(X,X)\<^esub> it & ( for EqR be Equivalence-RelationEQREL-1M2-of X holds EqR1 \\/EQREL-1K3\<^bsub>(X)\<^esub> EqR2 c=RELSET-1R1\<^bsub>(X,X)\<^esub> EqR implies it c=RELSET-1R1\<^bsub>(X,X)\<^esub> EqR)"
proof-
  (*existence*)
    show " ex it be Equivalence-RelationEQREL-1M2-of X st EqR1 \\/EQREL-1K3\<^bsub>(X)\<^esub> EqR2 c=RELSET-1R1\<^bsub>(X,X)\<^esub> it & ( for EqR be Equivalence-RelationEQREL-1M2-of X holds EqR1 \\/EQREL-1K3\<^bsub>(X)\<^esub> EqR2 c=RELSET-1R1\<^bsub>(X,X)\<^esub> EqR implies it c=RELSET-1R1\<^bsub>(X,X)\<^esub> EqR)"
      using eqrel_1_th_12 sorry
  (*uniqueness*)
    show " for it1 be Equivalence-RelationEQREL-1M2-of X holds  for it2 be Equivalence-RelationEQREL-1M2-of X holds (EqR1 \\/EQREL-1K3\<^bsub>(X)\<^esub> EqR2 c=RELSET-1R1\<^bsub>(X,X)\<^esub> it1 & ( for EqR be Equivalence-RelationEQREL-1M2-of X holds EqR1 \\/EQREL-1K3\<^bsub>(X)\<^esub> EqR2 c=RELSET-1R1\<^bsub>(X,X)\<^esub> EqR implies it1 c=RELSET-1R1\<^bsub>(X,X)\<^esub> EqR)) & (EqR1 \\/EQREL-1K3\<^bsub>(X)\<^esub> EqR2 c=RELSET-1R1\<^bsub>(X,X)\<^esub> it2 & ( for EqR be Equivalence-RelationEQREL-1M2-of X holds EqR1 \\/EQREL-1K3\<^bsub>(X)\<^esub> EqR2 c=RELSET-1R1\<^bsub>(X,X)\<^esub> EqR implies it2 c=RELSET-1R1\<^bsub>(X,X)\<^esub> EqR)) implies it1 =HIDDENR1 it2"
       sorry
qed "sorry"

mtheorem EQREL_1K5_commutativity:
  mlet "X be setHIDDENM2"
" for EqR1 be Equivalence-RelationEQREL-1M2-of X holds  for EqR2 be Equivalence-RelationEQREL-1M2-of X holds EqR1 \<inverse>\\/\<inverse>EQREL-1K5\<^bsub>(X)\<^esub> EqR2 =HIDDENR1 EqR2 \<inverse>\\/\<inverse>EQREL-1K5\<^bsub>(X)\<^esub> EqR1"
sorry

mtheorem EQREL_1K5_idempotence:
  mlet "X be setHIDDENM2"
" for EqR2 be Equivalence-RelationEQREL-1M2-of X holds EqR2 =HIDDENR1 EqR2 \<inverse>\\/\<inverse>EQREL-1K5\<^bsub>(X)\<^esub> EqR2"
sorry

mtheorem eqrel_1_th_13:
" for X be setHIDDENM2 holds  for EqR1 be Equivalence-RelationEQREL-1M2-of X holds  for EqR2 be Equivalence-RelationEQREL-1M2-of X holds  for EqR3 be Equivalence-RelationEQREL-1M2-of X holds (EqR1 \<inverse>\\/\<inverse>EQREL-1K5\<^bsub>(X)\<^esub> EqR2)\<inverse>\\/\<inverse>EQREL-1K5\<^bsub>(X)\<^esub> EqR3 =RELSET-1R2\<^bsub>(X,X)\<^esub> EqR1 \<inverse>\\/\<inverse>EQREL-1K5\<^bsub>(X)\<^esub> (EqR2 \<inverse>\\/\<inverse>EQREL-1K5\<^bsub>(X)\<^esub> EqR3)"
sorry

mtheorem eqrel_1_th_14:
" for X be setHIDDENM2 holds  for EqR be Equivalence-RelationEQREL-1M2-of X holds EqR \<inverse>\\/\<inverse>EQREL-1K5\<^bsub>(X)\<^esub> EqR =RELSET-1R2\<^bsub>(X,X)\<^esub> EqR"
   sorry

mtheorem eqrel_1_th_15:
" for X be setHIDDENM2 holds  for EqR1 be Equivalence-RelationEQREL-1M2-of X holds  for EqR2 be Equivalence-RelationEQREL-1M2-of X holds EqR1 \<inverse>\\/\<inverse>EQREL-1K5\<^bsub>(X)\<^esub> EqR2 =RELSET-1R2\<^bsub>(X,X)\<^esub> EqR2 \<inverse>\\/\<inverse>EQREL-1K5\<^bsub>(X)\<^esub> EqR1"
   sorry

mtheorem eqrel_1_th_16:
" for X be setHIDDENM2 holds  for EqR1 be Equivalence-RelationEQREL-1M2-of X holds  for EqR2 be Equivalence-RelationEQREL-1M2-of X holds EqR1 /\\EQREL-1K4\<^bsub>(X)\<^esub> (EqR1 \<inverse>\\/\<inverse>EQREL-1K5\<^bsub>(X)\<^esub> EqR2) =RELSET-1R2\<^bsub>(X,X)\<^esub> EqR1"
sorry

mtheorem eqrel_1_th_17:
" for X be setHIDDENM2 holds  for EqR1 be Equivalence-RelationEQREL-1M2-of X holds  for EqR2 be Equivalence-RelationEQREL-1M2-of X holds EqR1 \<inverse>\\/\<inverse>EQREL-1K5\<^bsub>(X)\<^esub> (EqR1 /\\EQREL-1K4\<^bsub>(X)\<^esub> EqR2) =RELSET-1R2\<^bsub>(X,X)\<^esub> EqR1"
sorry

theorem eqrel_1_sch_1:
  fixes Xf0 Pp2 
  assumes
[ty]: "Xf0 be setHIDDENM2" and
   A1: " for x be objectHIDDENM1 holds x inHIDDENR3 Xf0 implies Pp2(x,x)" and
   A2: " for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds Pp2(x,y) implies Pp2(y,x)" and
   A3: " for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for z be objectHIDDENM1 holds Pp2(x,y) & Pp2(y,z) implies Pp2(x,z)"
  shows " ex EqR be Equivalence-RelationEQREL-1M2-of Xf0 st  for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds [TARSKIK4 x,y ] inHIDDENR3 EqR iff (x inHIDDENR3 Xf0 & y inHIDDENR3 Xf0) & Pp2(x,y)"
sorry

abbreviation(input) EQREL_1K6("ClassEQREL-1K6'( _ , _ ')" [0,0]164) where
  "ClassEQREL-1K6(R,x) \<equiv> ImRELAT-1K12(R,x)"

syntax EQREL_1K7 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" ("ClassEQREL-1K7\<^bsub>'( _ , _ ')\<^esub>'( _ , _ ')" [0,0,0,0]164)
translations "ClassEQREL-1K7\<^bsub>(X,Y)\<^esub>(R,x)" \<rightharpoonup> "ImRELAT-1K12(R,x)"

mtheorem eqrel_1_add_4:
  mlet "X be setHIDDENM2", "Y be setHIDDENM2", "R be RelationRELSET-1M1-of(X,Y)", "x be objectHIDDENM1"
"cluster ImRELAT-1K12(R,x) as-term-is SubsetSUBSET-1M2-of Y"
proof
(*coherence*)
  show "ImRELAT-1K12(R,x) be SubsetSUBSET-1M2-of Y"
sorry
qed "sorry"

mtheorem eqrel_1_th_18:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for R be RelationRELAT-1M1 holds y inHIDDENR3 ClassEQREL-1K6(R,x) iff [TARSKIK4 x,y ] inHIDDENR3 R"
sorry

mtheorem eqrel_1_th_19:
" for X be setHIDDENM2 holds  for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for R be totalPARTFUN1V1\<^bsub>(X)\<^esub>\<bar>symmetricRELAT-2V3\<bar>RelationRELSET-1M2-of X holds y inHIDDENR3 ClassEQREL-1K7\<^bsub>(X,X)\<^esub>(R,x) iff [TARSKIK4 y,x ] inHIDDENR3 R"
sorry

mtheorem eqrel_1_th_20:
" for X be setHIDDENM2 holds  for R be ToleranceEQREL-1M1-of X holds  for x be objectHIDDENM1 holds x inHIDDENR3 X implies x inHIDDENR3 ClassEQREL-1K7\<^bsub>(X,X)\<^esub>(R,x)"
sorry

mtheorem eqrel_1_th_21:
" for X be setHIDDENM2 holds  for R be ToleranceEQREL-1M1-of X holds  for x be objectHIDDENM1 holds x inHIDDENR3 X implies ( ex y be objectHIDDENM1 st x inHIDDENR3 ClassEQREL-1K7\<^bsub>(X,X)\<^esub>(R,y))"
sorry

mtheorem eqrel_1_th_22:
" for X be setHIDDENM2 holds  for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for z be objectHIDDENM1 holds  for R be transitiveRELAT-2V8\<bar>ToleranceEQREL-1M1-of X holds y inHIDDENR3 ClassEQREL-1K7\<^bsub>(X,X)\<^esub>(R,x) & z inHIDDENR3 ClassEQREL-1K7\<^bsub>(X,X)\<^esub>(R,x) implies [TARSKIK4 y,z ] inHIDDENR3 R"
sorry

mlemma eqrel_1_lm_2:
" for X be setHIDDENM2 holds  for y be objectHIDDENM1 holds  for EqR be Equivalence-RelationEQREL-1M2-of X holds  for x be objectHIDDENM1 holds x inHIDDENR3 X implies ([TARSKIK4 x,y ] inHIDDENR3 EqR iff ClassEQREL-1K7\<^bsub>(X,X)\<^esub>(EqR,x) =XBOOLE-0R4 ClassEQREL-1K7\<^bsub>(X,X)\<^esub>(EqR,y))"
sorry

mtheorem eqrel_1_th_23:
" for X be setHIDDENM2 holds  for y be objectHIDDENM1 holds  for EqR be Equivalence-RelationEQREL-1M2-of X holds  for x be objectHIDDENM1 holds x inHIDDENR3 X implies (y inHIDDENR3 ClassEQREL-1K7\<^bsub>(X,X)\<^esub>(EqR,x) iff ClassEQREL-1K7\<^bsub>(X,X)\<^esub>(EqR,x) =XBOOLE-0R4 ClassEQREL-1K7\<^bsub>(X,X)\<^esub>(EqR,y))"
sorry

mtheorem eqrel_1_th_24:
" for X be setHIDDENM2 holds  for EqR be Equivalence-RelationEQREL-1M2-of X holds  for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds y inHIDDENR3 X implies ClassEQREL-1K7\<^bsub>(X,X)\<^esub>(EqR,x) =XBOOLE-0R4 ClassEQREL-1K7\<^bsub>(X,X)\<^esub>(EqR,y) or ClassEQREL-1K7\<^bsub>(X,X)\<^esub>(EqR,x) missesXBOOLE-0R1 ClassEQREL-1K7\<^bsub>(X,X)\<^esub>(EqR,y)"
sorry

mtheorem eqrel_1_th_25:
" for X be setHIDDENM2 holds  for x be objectHIDDENM1 holds x inHIDDENR3 X implies ClassEQREL-1K7\<^bsub>(X,X)\<^esub>(idPARTFUN1K6 X,x) =XBOOLE-0R4 {TARSKIK1 x}"
sorry

mtheorem eqrel_1_th_26:
" for X be setHIDDENM2 holds  for x be objectHIDDENM1 holds x inHIDDENR3 X implies ClassEQREL-1K7\<^bsub>(X,X)\<^esub>(nablaEQREL-1K1 X,x) =XBOOLE-0R4 X"
sorry

mtheorem eqrel_1_th_27:
" for X be setHIDDENM2 holds  for EqR be Equivalence-RelationEQREL-1M2-of X holds ( ex x be objectHIDDENM1 st ClassEQREL-1K7\<^bsub>(X,X)\<^esub>(EqR,x) =XBOOLE-0R4 X) implies EqR =RELSET-1R2\<^bsub>(X,X)\<^esub> nablaEQREL-1K1 X"
sorry

mtheorem eqrel_1_th_28:
" for X be setHIDDENM2 holds  for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for EqR1 be Equivalence-RelationEQREL-1M2-of X holds  for EqR2 be Equivalence-RelationEQREL-1M2-of X holds x inHIDDENR3 X implies ([TARSKIK4 x,y ] inHIDDENR3 EqR1 \<inverse>\\/\<inverse>EQREL-1K5\<^bsub>(X)\<^esub> EqR2 iff ( ex f be FinSequenceFINSEQ-1M1 st ((\<one>\<^sub>M <=XXREAL-0R1 lenFINSEQ-1K4 f & x =HIDDENR1 f .FUNCT-1K1 \<one>\<^sub>M) & y =HIDDENR1 f .FUNCT-1K1 lenFINSEQ-1K4 f) & ( for i be NatNAT-1M1 holds \<one>\<^sub>M <=XXREAL-0R1 i & i <XXREAL-0R3 lenFINSEQ-1K4 f implies [TARSKIK4 f .FUNCT-1K1 i,f .FUNCT-1K1 (i +NAT-1K1 \<one>\<^sub>M) ] inHIDDENR3 EqR1 \\/EQREL-1K3\<^bsub>(X)\<^esub> EqR2)))"
sorry

mtheorem eqrel_1_th_29:
" for X be setHIDDENM2 holds  for EqR1 be Equivalence-RelationEQREL-1M2-of X holds  for EqR2 be Equivalence-RelationEQREL-1M2-of X holds  for E be Equivalence-RelationEQREL-1M2-of X holds E =RELSET-1R2\<^bsub>(X,X)\<^esub> EqR1 \\/EQREL-1K3\<^bsub>(X)\<^esub> EqR2 implies ( for x be objectHIDDENM1 holds x inHIDDENR3 X implies ClassEQREL-1K7\<^bsub>(X,X)\<^esub>(E,x) =XBOOLE-0R4 ClassEQREL-1K7\<^bsub>(X,X)\<^esub>(EqR1,x) or ClassEQREL-1K7\<^bsub>(X,X)\<^esub>(E,x) =XBOOLE-0R4 ClassEQREL-1K7\<^bsub>(X,X)\<^esub>(EqR2,x))"
sorry

mtheorem eqrel_1_th_30:
" for X be setHIDDENM2 holds  for EqR1 be Equivalence-RelationEQREL-1M2-of X holds  for EqR2 be Equivalence-RelationEQREL-1M2-of X holds EqR1 \\/EQREL-1K3\<^bsub>(X)\<^esub> EqR2 =RELSET-1R2\<^bsub>(X,X)\<^esub> nablaEQREL-1K1 X implies EqR1 =RELSET-1R2\<^bsub>(X,X)\<^esub> nablaEQREL-1K1 X or EqR2 =RELSET-1R2\<^bsub>(X,X)\<^esub> nablaEQREL-1K1 X"
sorry

mdef eqrel_1_def_3 ("ClassEQREL-1K8\<^bsub>'( _ ')\<^esub>  _ " [0,164]164 ) where
  mlet "X be setHIDDENM2", "EqR be Equivalence-RelationEQREL-1M2-of X"
"func ClassEQREL-1K8\<^bsub>(X)\<^esub> EqR \<rightarrow> Subset-FamilySETFAM-1M1-of X means
  \<lambda>it.  for A be SubsetSUBSET-1M2-of X holds A inTARSKIR2 it iff ( ex x be objectHIDDENM1 st x inHIDDENR3 X & A =XBOOLE-0R4 ClassEQREL-1K7\<^bsub>(X,X)\<^esub>(EqR,x))"
proof-
  (*existence*)
    show " ex it be Subset-FamilySETFAM-1M1-of X st  for A be SubsetSUBSET-1M2-of X holds A inTARSKIR2 it iff ( ex x be objectHIDDENM1 st x inHIDDENR3 X & A =XBOOLE-0R4 ClassEQREL-1K7\<^bsub>(X,X)\<^esub>(EqR,x))"
sorry
  (*uniqueness*)
    show " for it1 be Subset-FamilySETFAM-1M1-of X holds  for it2 be Subset-FamilySETFAM-1M1-of X holds ( for A be SubsetSUBSET-1M2-of X holds A inTARSKIR2 it1 iff ( ex x be objectHIDDENM1 st x inHIDDENR3 X & A =XBOOLE-0R4 ClassEQREL-1K7\<^bsub>(X,X)\<^esub>(EqR,x))) & ( for A be SubsetSUBSET-1M2-of X holds A inTARSKIR2 it2 iff ( ex x be objectHIDDENM1 st x inHIDDENR3 X & A =XBOOLE-0R4 ClassEQREL-1K7\<^bsub>(X,X)\<^esub>(EqR,x))) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mtheorem eqrel_1_th_31:
" for X be setHIDDENM2 holds  for EqR be Equivalence-RelationEQREL-1M2-of X holds X =XBOOLE-0R4 {}XBOOLE-0K1 implies ClassEQREL-1K8\<^bsub>(X)\<^esub> EqR =XBOOLE-0R4 {}XBOOLE-0K1"
sorry

mdef eqrel_1_def_4 ("a-partitionEQREL-1M3-of  _ " [70]70 ) where
  mlet "X be setHIDDENM2"
"mode a-partitionEQREL-1M3-of X \<rightarrow> Subset-FamilySETFAM-1M1-of X means
  (\<lambda>it. unionSETFAM-1K5\<^bsub>(X)\<^esub> it =XBOOLE-0R4 X & ( for A be SubsetSUBSET-1M2-of X holds A inTARSKIR2 it implies A <>HIDDENR2 {}XBOOLE-0K1 & ( for B be SubsetSUBSET-1M2-of X holds B inTARSKIR2 it implies A =XBOOLE-0R4 B or A missesXBOOLE-0R1 B)))"
proof-
  (*existence*)
    show " ex it be Subset-FamilySETFAM-1M1-of X st unionSETFAM-1K5\<^bsub>(X)\<^esub> it =XBOOLE-0R4 X & ( for A be SubsetSUBSET-1M2-of X holds A inTARSKIR2 it implies A <>HIDDENR2 {}XBOOLE-0K1 & ( for B be SubsetSUBSET-1M2-of X holds B inTARSKIR2 it implies A =XBOOLE-0R4 B or A missesXBOOLE-0R1 B))"
sorry
qed "sorry"

mtheorem eqrel_1_th_32:
" for P be a-partitionEQREL-1M3-of {}XBOOLE-0K1 holds P =XBOOLE-0R4 {}XBOOLE-0K1"
sorry

mtheorem eqrel_1_cl_3:
  mlet "X be emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster note-that emptyXBOOLE-0V1 for a-partitionEQREL-1M3-of X"
proof
(*coherence*)
  show " for it be a-partitionEQREL-1M3-of X holds it be emptyXBOOLE-0V1"
    using eqrel_1_th_32 sorry
qed "sorry"

mtheorem eqrel_1_cl_4:
  mlet "X be emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster emptyXBOOLE-0V1 for a-partitionEQREL-1M3-of X"
proof
(*existence*)
  show " ex it be a-partitionEQREL-1M3-of X st it be emptyXBOOLE-0V1"
sorry
qed "sorry"

mtheorem eqrel_1_th_33:
" for X be setHIDDENM2 holds  for EqR be Equivalence-RelationEQREL-1M2-of X holds ClassEQREL-1K8\<^bsub>(X)\<^esub> EqR be a-partitionEQREL-1M3-of X"
sorry

mtheorem eqrel_1_th_34:
" for X be setHIDDENM2 holds  for P be a-partitionEQREL-1M3-of X holds  ex EqR be Equivalence-RelationEQREL-1M2-of X st P =XBOOLE-0R4 ClassEQREL-1K8\<^bsub>(X)\<^esub> EqR"
sorry

mtheorem eqrel_1_th_35:
" for X be setHIDDENM2 holds  for y be objectHIDDENM1 holds  for EqR be Equivalence-RelationEQREL-1M2-of X holds  for x be objectHIDDENM1 holds x inHIDDENR3 X implies ([TARSKIK4 x,y ] inHIDDENR3 EqR iff ClassEQREL-1K7\<^bsub>(X,X)\<^esub>(EqR,x) =XBOOLE-0R4 ClassEQREL-1K7\<^bsub>(X,X)\<^esub>(EqR,y))"
  using eqrel_1_lm_2 sorry

mtheorem eqrel_1_th_36:
" for X be setHIDDENM2 holds  for x be objectHIDDENM1 holds  for EqR be Equivalence-RelationEQREL-1M2-of X holds x inHIDDENR3 ClassEQREL-1K8\<^bsub>(X)\<^esub> EqR implies ( ex y be ElementSUBSET-1M1-of X st x =HIDDENR1 ClassEQREL-1K7\<^bsub>(X,X)\<^esub>(EqR,y))"
sorry

(*begin*)
mtheorem eqrel_1_cl_5:
  mlet "X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster note-that  non emptyXBOOLE-0V1 for a-partitionEQREL-1M3-of X"
proof
(*coherence*)
  show " for it be a-partitionEQREL-1M3-of X holds it be  non emptyXBOOLE-0V1"
sorry
qed "sorry"

mtheorem eqrel_1_cl_6:
  mlet "X be setHIDDENM2"
"cluster note-that with-non-empty-elementsSETFAM-1V1 for a-partitionEQREL-1M3-of X"
proof
(*coherence*)
  show " for it be a-partitionEQREL-1M3-of X holds it be with-non-empty-elementsSETFAM-1V1"
sorry
qed "sorry"

abbreviation(input) EQREL_1K9("ClassEQREL-1K9\<^bsub>'( _ ')\<^esub>  _ " [0,164]164) where
  "ClassEQREL-1K9\<^bsub>(X)\<^esub> R \<equiv> ClassEQREL-1K8\<^bsub>(X)\<^esub> R"

mtheorem eqrel_1_add_5:
  mlet "X be setHIDDENM2", "R be Equivalence-RelationEQREL-1M2-of X"
"cluster ClassEQREL-1K8\<^bsub>(X)\<^esub> R as-term-is a-partitionEQREL-1M3-of X"
proof
(*coherence*)
  show "ClassEQREL-1K8\<^bsub>(X)\<^esub> R be a-partitionEQREL-1M3-of X"
    using eqrel_1_th_33 sorry
qed "sorry"

mtheorem eqrel_1_cl_7:
  mlet "I be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "R be Equivalence-RelationEQREL-1M2-of I"
"cluster ClassEQREL-1K9\<^bsub>(I)\<^esub> R as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "ClassEQREL-1K9\<^bsub>(I)\<^esub> R be  non emptyXBOOLE-0V1"
     sorry
qed "sorry"

mtheorem eqrel_1_cl_8:
  mlet "I be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "R be Equivalence-RelationEQREL-1M2-of I"
"cluster ClassEQREL-1K9\<^bsub>(I)\<^esub> R as-term-is with-non-empty-elementsSETFAM-1V1"
proof
(*coherence*)
  show "ClassEQREL-1K9\<^bsub>(I)\<^esub> R be with-non-empty-elementsSETFAM-1V1"
     sorry
qed "sorry"

syntax EQREL_1K10 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" ("EqClassEQREL-1K10\<^bsub>'( _ ')\<^esub>'( _ , _ ')" [0,0,0]164)
translations "EqClassEQREL-1K10\<^bsub>(I)\<^esub>(R,x)" \<rightharpoonup> "ClassEQREL-1K6(R,x)"

syntax EQREL_1K11 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" ("EqClassEQREL-1K11\<^bsub>'( _ ')\<^esub>'( _ , _ ')" [0,0,0]164)
translations "EqClassEQREL-1K11\<^bsub>(I)\<^esub>(R,x)" \<rightharpoonup> "ImRELAT-1K12(R,x)"

mtheorem eqrel_1_add_6:
  mlet "I be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "R be Equivalence-RelationEQREL-1M2-of I", "x be ElementSUBSET-1M1-of I"
"cluster ImRELAT-1K12(R,x) as-term-is ElementSUBSET-1M3\<^bsub>(boolZFMISC-1K1 I)\<^esub>-of ClassEQREL-1K9\<^bsub>(I)\<^esub> R"
proof
(*coherence*)
  show "ImRELAT-1K12(R,x) be ElementSUBSET-1M3\<^bsub>(boolZFMISC-1K1 I)\<^esub>-of ClassEQREL-1K9\<^bsub>(I)\<^esub> R"
sorry
qed "sorry"

mdef eqrel_1_def_5 ("SmallestPartitionEQREL-1K12  _ " [164]164 ) where
  mlet "X be setHIDDENM2"
"func SmallestPartitionEQREL-1K12 X \<rightarrow> setHIDDENM2 equals
  ClassEQREL-1K9\<^bsub>(X)\<^esub> idPARTFUN1K6 X"
proof-
  (*coherence*)
    show "ClassEQREL-1K9\<^bsub>(X)\<^esub> idPARTFUN1K6 X be setHIDDENM2"
       sorry
qed "sorry"

abbreviation(input) EQREL_1K13("SmallestPartitionEQREL-1K13  _ " [164]164) where
  "SmallestPartitionEQREL-1K13 X \<equiv> SmallestPartitionEQREL-1K12 X"

mtheorem eqrel_1_add_7:
  mlet "X be setHIDDENM2"
"cluster SmallestPartitionEQREL-1K12 X as-term-is a-partitionEQREL-1M3-of X"
proof
(*coherence*)
  show "SmallestPartitionEQREL-1K12 X be a-partitionEQREL-1M3-of X"
     sorry
qed "sorry"

mtheorem eqrel_1_th_37:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds SmallestPartitionEQREL-1K13 X =XBOOLE-0R4 {{DOMAIN-1K6\<^bsub>(X)\<^esub> x} where x be ElementSUBSET-1M1-of X :  True  }"
sorry

reserve X for " non emptyXBOOLE-0V1\<bar>setHIDDENM2"
reserve x for "ElementSUBSET-1M1-of X"
mdef eqrel_1_def_6 ("EqClassEQREL-1K14\<^bsub>'( _ ')\<^esub>'( _ , _ ')" [0,0,0]164 ) where
  mlet "X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "x be ElementSUBSET-1M1-of X", "S1 be a-partitionEQREL-1M3-of X"
"func EqClassEQREL-1K14\<^bsub>(X)\<^esub>(x,S1) \<rightarrow> SubsetSUBSET-1M2-of X means
  \<lambda>it. x inTARSKIR2 it & it inTARSKIR2 S1"
proof-
  (*existence*)
    show " ex it be SubsetSUBSET-1M2-of X st x inTARSKIR2 it & it inTARSKIR2 S1"
sorry
  (*uniqueness*)
    show " for it1 be SubsetSUBSET-1M2-of X holds  for it2 be SubsetSUBSET-1M2-of X holds (x inTARSKIR2 it1 & it1 inTARSKIR2 S1) & (x inTARSKIR2 it2 & it2 inTARSKIR2 S1) implies it1 =HIDDENR1 it2"
      using eqrel_1_def_4 xboole_0_th_3 sorry
qed "sorry"

mtheorem eqrel_1_th_38:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for S1 be a-partitionEQREL-1M3-of X holds  for S2 be a-partitionEQREL-1M3-of X holds ( for x be ElementSUBSET-1M1-of X holds EqClassEQREL-1K14\<^bsub>(X)\<^esub>(x,S1) =XBOOLE-0R4 EqClassEQREL-1K14\<^bsub>(X)\<^esub>(x,S2)) implies S1 =XBOOLE-0R4 S2"
sorry

mtheorem eqrel_1_th_39:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds {TARSKIK1 X} be a-partitionEQREL-1M3-of X"
sorry

abbreviation(input) EQREL_1M4("Family-ClassEQREL-1M4-of  _ " [70]70) where
  "Family-ClassEQREL-1M4-of X \<equiv> Subset-FamilySETFAM-1M1-of boolSETFAM-1K9 X"

mdef eqrel_1_def_7 ("partition-memberedEQREL-1V1\<^bsub>'( _ ')\<^esub>" [0]70 ) where
  mlet "X be setHIDDENM2"
"attr partition-memberedEQREL-1V1\<^bsub>(X)\<^esub> for Family-ClassEQREL-1M4-of X means
  (\<lambda>F.  for S be setHIDDENM2 holds S inTARSKIR2 F implies S be a-partitionEQREL-1M3-of X)"..

mtheorem eqrel_1_cl_9:
  mlet "X be setHIDDENM2"
"cluster partition-memberedEQREL-1V1\<^bsub>(X)\<^esub> for Family-ClassEQREL-1M4-of X"
proof
(*existence*)
  show " ex it be Family-ClassEQREL-1M4-of X st it be partition-memberedEQREL-1V1\<^bsub>(X)\<^esub>"
sorry
qed "sorry"

syntax EQREL_1M5 :: " Set \<Rightarrow> Ty" ("Part-FamilyEQREL-1M5-of  _ " [70]70)
translations "Part-FamilyEQREL-1M5-of X" \<rightharpoonup> "partition-memberedEQREL-1V1\<^bsub>(X)\<^esub>\<bar>Family-ClassEQREL-1M4-of X"

reserve F for "Part-FamilyEQREL-1M5-of X"
mtheorem eqrel_1_cl_10:
  mlet "X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster  non emptyXBOOLE-0V1 for a-partitionEQREL-1M3-of X"
proof
(*existence*)
  show " ex it be a-partitionEQREL-1M3-of X st it be  non emptyXBOOLE-0V1"
sorry
qed "sorry"

mtheorem eqrel_1_th_40:
" for X be setHIDDENM2 holds  for p be a-partitionEQREL-1M3-of X holds {DOMAIN-1K6\<^bsub>(boolZFMISC-1K1 (boolZFMISC-1K1 X))\<^esub> p} be Part-FamilyEQREL-1M5-of X"
sorry

mtheorem eqrel_1_cl_11:
  mlet "X be setHIDDENM2"
"cluster  non emptyXBOOLE-0V1 for Part-FamilyEQREL-1M5-of X"
proof
(*existence*)
  show " ex it be Part-FamilyEQREL-1M5-of X st it be  non emptyXBOOLE-0V1"
sorry
qed "sorry"

mtheorem eqrel_1_th_41:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for S1 be a-partitionEQREL-1M3-of X holds  for x be ElementSUBSET-1M1-of X holds  for y be ElementSUBSET-1M1-of X holds EqClassEQREL-1K14\<^bsub>(X)\<^esub>(x,S1) meetsXBOOLE-0R5 EqClassEQREL-1K14\<^bsub>(X)\<^esub>(y,S1) implies EqClassEQREL-1K14\<^bsub>(X)\<^esub>(x,S1) =XBOOLE-0R4 EqClassEQREL-1K14\<^bsub>(X)\<^esub>(y,S1)"
sorry

mlemma eqrel_1_lm_3:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for x be ElementSUBSET-1M1-of X holds  for F be Part-FamilyEQREL-1M5-of X holds  for A be setHIDDENM2 holds A inTARSKIR2 {EqClassEQREL-1K14\<^bsub>(X)\<^esub>(x,S) where S be a-partitionEQREL-1M3-of X : S inTARSKIR2 F } implies ( ex T be a-partitionEQREL-1M3-of X st T inTARSKIR2 F & A =XBOOLE-0R4 EqClassEQREL-1K14\<^bsub>(X)\<^esub>(x,T))"
sorry

mtheorem eqrel_1_th_42:
" for A be setHIDDENM2 holds  for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for S be a-partitionEQREL-1M3-of X holds A inTARSKIR2 S implies ( ex x be ElementSUBSET-1M1-of X st A =XBOOLE-0R4 EqClassEQREL-1K14\<^bsub>(X)\<^esub>(x,S))"
sorry

mdef eqrel_1_def_8 ("IntersectionEQREL-1K15\<^bsub>'( _ ')\<^esub>  _ " [0,164]164 ) where
  mlet "X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "F be  non emptyXBOOLE-0V1\<bar>Part-FamilyEQREL-1M5-of X"
"func IntersectionEQREL-1K15\<^bsub>(X)\<^esub> F \<rightarrow>  non emptyXBOOLE-0V1\<bar>a-partitionEQREL-1M3-of X means
  \<lambda>it.  for x be ElementSUBSET-1M1-of X holds EqClassEQREL-1K14\<^bsub>(X)\<^esub>(x,it) =XBOOLE-0R4 meetSETFAM-1K1 ({EqClassEQREL-1K14\<^bsub>(X)\<^esub>(x,S) where S be a-partitionEQREL-1M3-of X : S inTARSKIR2 F })"
proof-
  (*uniqueness*)
    show " for it1 be  non emptyXBOOLE-0V1\<bar>a-partitionEQREL-1M3-of X holds  for it2 be  non emptyXBOOLE-0V1\<bar>a-partitionEQREL-1M3-of X holds ( for x be ElementSUBSET-1M1-of X holds EqClassEQREL-1K14\<^bsub>(X)\<^esub>(x,it1) =XBOOLE-0R4 meetSETFAM-1K1 ({EqClassEQREL-1K14\<^bsub>(X)\<^esub>(x,S) where S be a-partitionEQREL-1M3-of X : S inTARSKIR2 F })) & ( for x be ElementSUBSET-1M1-of X holds EqClassEQREL-1K14\<^bsub>(X)\<^esub>(x,it2) =XBOOLE-0R4 meetSETFAM-1K1 ({EqClassEQREL-1K14\<^bsub>(X)\<^esub>(x,S) where S be a-partitionEQREL-1M3-of X : S inTARSKIR2 F })) implies it1 =HIDDENR1 it2"
sorry
  (*existence*)
    show " ex it be  non emptyXBOOLE-0V1\<bar>a-partitionEQREL-1M3-of X st  for x be ElementSUBSET-1M1-of X holds EqClassEQREL-1K14\<^bsub>(X)\<^esub>(x,it) =XBOOLE-0R4 meetSETFAM-1K1 ({EqClassEQREL-1K14\<^bsub>(X)\<^esub>(x,S) where S be a-partitionEQREL-1M3-of X : S inTARSKIR2 F })"
sorry
qed "sorry"

mtheorem eqrel_1_th_43:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for S be a-partitionEQREL-1M3-of X holds  for A be SubsetSUBSET-1M2-of S holds unionSETFAM-1K5\<^bsub>(X)\<^esub> S \\SUBSET-1K7\<^bsub>(X)\<^esub> unionTARSKIK3 A =XBOOLE-0R4 unionSETFAM-1K5\<^bsub>(X)\<^esub> (S \\SUBSET-1K7\<^bsub>(boolZFMISC-1K1 X)\<^esub> A)"
sorry

mtheorem eqrel_1_th_44:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for A be SubsetSUBSET-1M2-of X holds  for S be a-partitionEQREL-1M3-of X holds A inTARSKIR2 S implies unionSETFAM-1K5\<^bsub>(X)\<^esub> (S \\SUBSET-1K7\<^bsub>(boolZFMISC-1K1 X)\<^esub> {DOMAIN-1K6\<^bsub>(boolZFMISC-1K1 X)\<^esub> A}) =XBOOLE-0R4 X \\SUBSET-1K6 A"
sorry

mtheorem eqrel_1_th_45:
"{}XBOOLE-0K1 be a-partitionEQREL-1M3-of {}XBOOLE-0K1"
sorry

(*begin*)
reserve e, u, v for "objectHIDDENM1"
reserve E, X, Y, X1 for "setHIDDENM2"
mtheorem eqrel_1_th_46:
" for X be setHIDDENM2 holds  for X1 be setHIDDENM2 holds  for F be FunctionFUNCT-1M1 holds X c=TARSKIR1 F \<inverse>FUNCT-1K6 X1 implies F .:FUNCT-1K5 X c=TARSKIR1 X1"
sorry

mtheorem eqrel_1_th_47:
" for E be setHIDDENM2 holds  for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds E c=TARSKIR1 [:ZFMISC-1K2 X,Y :] implies (.:FUNCT-3K1 pr1FUNCT-3K10(X,Y)).FUNCT-1K1 E =XBOOLE-0R4 pr1FUNCT-3K10(X,Y) .:RELSET-1K7\<^bsub>([:ZFMISC-1K2 X,Y :],X)\<^esub> E"
sorry

mtheorem eqrel_1_th_48:
" for E be setHIDDENM2 holds  for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds E c=TARSKIR1 [:ZFMISC-1K2 X,Y :] implies (.:FUNCT-3K1 pr2FUNCT-3K11(X,Y)).FUNCT-1K1 E =XBOOLE-0R4 pr2FUNCT-3K11(X,Y) .:RELSET-1K7\<^bsub>([:ZFMISC-1K2 X,Y :],Y)\<^esub> E"
sorry

mtheorem eqrel_1_th_49:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for X1 be SubsetSUBSET-1M2-of X holds  for Y1 be SubsetSUBSET-1M2-of Y holds [:MCART-1K8\<^bsub>(X,Y)\<^esub> X1,Y1 :] <>HIDDENR2 {}XBOOLE-0K1 implies pr1FUNCT-3K10(X,Y) .:RELSET-1K7\<^bsub>([:ZFMISC-1K2 X,Y :],X)\<^esub> ([:MCART-1K8\<^bsub>(X,Y)\<^esub> X1,Y1 :]) =XBOOLE-0R4 X1 & pr2FUNCT-3K11(X,Y) .:RELSET-1K7\<^bsub>([:ZFMISC-1K2 X,Y :],Y)\<^esub> ([:MCART-1K8\<^bsub>(X,Y)\<^esub> X1,Y1 :]) =XBOOLE-0R4 Y1"
sorry

mtheorem eqrel_1_th_50:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for X1 be SubsetSUBSET-1M2-of X holds  for Y1 be SubsetSUBSET-1M2-of Y holds [:MCART-1K8\<^bsub>(X,Y)\<^esub> X1,Y1 :] <>HIDDENR2 {}XBOOLE-0K1 implies (.:FUNCT-3K1 pr1FUNCT-3K10(X,Y)).FUNCT-1K1 ([:MCART-1K8\<^bsub>(X,Y)\<^esub> X1,Y1 :]) =XBOOLE-0R4 X1 & (.:FUNCT-3K1 pr2FUNCT-3K11(X,Y)).FUNCT-1K1 ([:MCART-1K8\<^bsub>(X,Y)\<^esub> X1,Y1 :]) =XBOOLE-0R4 Y1"
sorry

mtheorem eqrel_1_th_51:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for A be SubsetSUBSET-1M2-of [:ZFMISC-1K2 X,Y :] holds  for H be Subset-FamilySETFAM-1M1-of [:ZFMISC-1K2 X,Y :] holds ( for E be setHIDDENM2 holds E inTARSKIR2 H implies E c=TARSKIR1 A & ( ex X1 be SubsetSUBSET-1M2-of X st  ex Y1 be SubsetSUBSET-1M2-of Y st E =XBOOLE-0R4 [:MCART-1K8\<^bsub>(X,Y)\<^esub> X1,Y1 :])) implies [:ZFMISC-1K2 unionTARSKIK3 ((.:FUNCT-3K1 pr1FUNCT-3K10(X,Y)).:FUNCT-1K5 H),meetSETFAM-1K1 ((.:FUNCT-3K1 pr2FUNCT-3K11(X,Y)).:FUNCT-1K5 H) :] c=RELAT-1R2 A"
sorry

mtheorem eqrel_1_th_52:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for A be SubsetSUBSET-1M2-of [:ZFMISC-1K2 X,Y :] holds  for H be Subset-FamilySETFAM-1M1-of [:ZFMISC-1K2 X,Y :] holds ( for E be setHIDDENM2 holds E inTARSKIR2 H implies E c=TARSKIR1 A & ( ex X1 be SubsetSUBSET-1M2-of X st  ex Y1 be SubsetSUBSET-1M2-of Y st E =XBOOLE-0R4 [:MCART-1K8\<^bsub>(X,Y)\<^esub> X1,Y1 :])) implies [:ZFMISC-1K2 meetSETFAM-1K1 ((.:FUNCT-3K1 pr1FUNCT-3K10(X,Y)).:FUNCT-1K5 H),unionTARSKIK3 ((.:FUNCT-3K1 pr2FUNCT-3K11(X,Y)).:FUNCT-1K5 H) :] c=RELAT-1R2 A"
sorry

mtheorem eqrel_1_th_53:
" for X be setHIDDENM2 holds  for Y be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(X,Y) holds  for H be Subset-FamilySETFAM-1M1-of X holds unionSETFAM-1K5\<^bsub>(Y)\<^esub> ((.:FUNCT-3K2\<^bsub>(X,Y)\<^esub> f).:RELSET-1K7\<^bsub>(boolZFMISC-1K1 X,boolZFMISC-1K1 Y)\<^esub> H) =XBOOLE-0R4 f .:RELSET-1K7\<^bsub>(X,Y)\<^esub> unionSETFAM-1K5\<^bsub>(X)\<^esub> H"
sorry

reserve X, Y, Z for " non emptyXBOOLE-0V1\<bar>setHIDDENM2"
mtheorem eqrel_1_th_54:
" for X be setHIDDENM2 holds  for a be Subset-FamilySETFAM-1M1-of X holds unionTARSKIK3 (unionSETFAM-1K5\<^bsub>(X)\<^esub> a) =XBOOLE-0R4 unionTARSKIK3 ({unionTARSKIK3 A where A be SubsetSUBSET-1M2-of X : A inTARSKIR2 a })"
sorry

mtheorem eqrel_1_th_55:
" for X be setHIDDENM2 holds  for D be Subset-FamilySETFAM-1M1-of X holds unionSETFAM-1K5\<^bsub>(X)\<^esub> D =XBOOLE-0R4 X implies ( for A be SubsetSUBSET-1M2-of D holds  for B be SubsetSUBSET-1M2-of X holds B =XBOOLE-0R4 unionTARSKIK3 A implies B `SUBSET-1K3\<^bsub>(X)\<^esub> c=TARSKIR1 unionTARSKIK3 A `SUBSET-1K3\<^bsub>(D)\<^esub>)"
sorry

mtheorem eqrel_1_th_56:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for Y be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for Z be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for F be FunctionFUNCT-2M1-of(X,Y) holds  for G be FunctionFUNCT-2M1-of(X,Z) holds ( for x be ElementSUBSET-1M1-of X holds  for x9 be ElementSUBSET-1M1-of X holds F .FUNCT-2K3\<^bsub>(X,Y)\<^esub> x =XBOOLE-0R4 F .FUNCT-2K3\<^bsub>(X,Y)\<^esub> x9 implies G .FUNCT-2K3\<^bsub>(X,Z)\<^esub> x =XBOOLE-0R4 G .FUNCT-2K3\<^bsub>(X,Z)\<^esub> x9) implies ( ex H be FunctionFUNCT-2M1-of(Y,Z) st H *PARTFUN1K1\<^bsub>(X,Y,Y,Z)\<^esub> F =FUNCT-2R2\<^bsub>(X,Z)\<^esub> G)"
sorry

mtheorem eqrel_1_th_57:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for Y be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for Z be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for y be ElementSUBSET-1M1-of Y holds  for F be FunctionFUNCT-2M1-of(X,Y) holds  for G be FunctionFUNCT-2M1-of(Y,Z) holds F \<inverse>RELSET-1K8\<^bsub>(X,Y)\<^esub> {DOMAIN-1K6\<^bsub>(Y)\<^esub> y} c=TARSKIR1 (G *PARTFUN1K1\<^bsub>(X,Y,Y,Z)\<^esub> F)\<inverse>RELSET-1K8\<^bsub>(X,Z)\<^esub> {DOMAIN-1K6\<^bsub>(Z)\<^esub> G .FUNCT-2K3\<^bsub>(Y,Z)\<^esub> y }"
sorry

mtheorem eqrel_1_th_58:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for Y be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for Z be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for F be FunctionFUNCT-2M1-of(X,Y) holds  for x be ElementSUBSET-1M1-of X holds  for z be ElementSUBSET-1M1-of Z holds ([:FUNCT-3K17\<^bsub>(X,Z,Y,Z)\<^esub> F,idPARTFUN1K6 Z :]).BINOP-1K2\<^bsub>(X,Z,[:ZFMISC-1K2 Y,Z :])\<^esub>(x,z) =XBOOLE-0R4 [DOMAIN-1K1\<^bsub>(Y,Z)\<^esub> F .FUNCT-2K3\<^bsub>(X,Y)\<^esub> x,z ]"
sorry

mtheorem eqrel_1_th_59:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for Y be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for Z be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for F be FunctionFUNCT-2M1-of(X,Y) holds  for A be SubsetSUBSET-1M2-of X holds  for B be SubsetSUBSET-1M2-of Z holds ([:FUNCT-3K17\<^bsub>(X,Z,Y,Z)\<^esub> F,idPARTFUN1K6 Z :]).:RELSET-1K7\<^bsub>([:ZFMISC-1K2 X,Z :],[:ZFMISC-1K2 Y,Z :])\<^esub> ([:MCART-1K8\<^bsub>(X,Z)\<^esub> A,B :]) =RELSET-1R2\<^bsub>(Y,Z)\<^esub> [:MCART-1K8\<^bsub>(Y,Z)\<^esub> F .:RELSET-1K7\<^bsub>(X,Y)\<^esub> A,B :]"
sorry

mtheorem eqrel_1_th_60:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for Y be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for Z be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for F be FunctionFUNCT-2M1-of(X,Y) holds  for y be ElementSUBSET-1M1-of Y holds  for z be ElementSUBSET-1M1-of Z holds ([:FUNCT-3K17\<^bsub>(X,Z,Y,Z)\<^esub> F,idPARTFUN1K6 Z :])\<inverse>RELSET-1K8\<^bsub>([:ZFMISC-1K2 X,Z :],[:ZFMISC-1K2 Y,Z :])\<^esub> {DOMAIN-1K6\<^bsub>([:ZFMISC-1K2 Y,Z :])\<^esub> [DOMAIN-1K1\<^bsub>(Y,Z)\<^esub> y,z ] } =RELSET-1R2\<^bsub>(X,Z)\<^esub> [:MCART-1K8\<^bsub>(X,Z)\<^esub> F \<inverse>RELSET-1K8\<^bsub>(X,Y)\<^esub> {DOMAIN-1K6\<^bsub>(Y)\<^esub> y},{DOMAIN-1K6\<^bsub>(Z)\<^esub> z} :]"
sorry

mtheorem eqrel_1_th_61:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D be Subset-FamilySETFAM-1M1-of X holds  for A be SubsetSUBSET-1M2-of D holds unionTARSKIK3 A be SubsetSUBSET-1M2-of X"
sorry

mtheorem eqrel_1_th_62:
" for X be setHIDDENM2 holds  for D be a-partitionEQREL-1M3-of X holds  for A be SubsetSUBSET-1M2-of D holds  for B be SubsetSUBSET-1M2-of D holds unionTARSKIK3 (A /\\SUBSET-1K9\<^bsub>(D)\<^esub> B) =XBOOLE-0R4 unionTARSKIK3 A /\\XBOOLE-0K3 unionTARSKIK3 B"
sorry

mtheorem eqrel_1_th_63:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D be a-partitionEQREL-1M3-of X holds  for A be SubsetSUBSET-1M2-of D holds  for B be SubsetSUBSET-1M2-of X holds B =XBOOLE-0R4 unionTARSKIK3 A implies B `SUBSET-1K3\<^bsub>(X)\<^esub> =XBOOLE-0R4 unionTARSKIK3 A `SUBSET-1K3\<^bsub>(D)\<^esub>"
sorry

mtheorem eqrel_1_th_64:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for E be Equivalence-RelationEQREL-1M2-of X holds ClassEQREL-1K9\<^bsub>(X)\<^esub> E be  non emptyXBOOLE-0V1"
   sorry

mdef eqrel_1_def_9 ("projEQREL-1K16\<^bsub>'( _ ')\<^esub>  _ " [0,228]228 ) where
  mlet "X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "D be  non emptyXBOOLE-0V1\<bar>a-partitionEQREL-1M3-of X"
"func projEQREL-1K16\<^bsub>(X)\<^esub> D \<rightarrow> FunctionFUNCT-2M1-of(X,D) means
  \<lambda>it.  for p be ElementSUBSET-1M1-of X holds p inTARSKIR2 it .FUNCT-2K3\<^bsub>(X,D)\<^esub> p"
proof-
  (*existence*)
    show " ex it be FunctionFUNCT-2M1-of(X,D) st  for p be ElementSUBSET-1M1-of X holds p inTARSKIR2 it .FUNCT-2K3\<^bsub>(X,D)\<^esub> p"
sorry
  (*uniqueness*)
    show " for it1 be FunctionFUNCT-2M1-of(X,D) holds  for it2 be FunctionFUNCT-2M1-of(X,D) holds ( for p be ElementSUBSET-1M1-of X holds p inTARSKIR2 it1 .FUNCT-2K3\<^bsub>(X,D)\<^esub> p) & ( for p be ElementSUBSET-1M1-of X holds p inTARSKIR2 it2 .FUNCT-2K3\<^bsub>(X,D)\<^esub> p) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mtheorem eqrel_1_th_65:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>a-partitionEQREL-1M3-of X holds  for p be ElementSUBSET-1M1-of X holds  for A be ElementSUBSET-1M3\<^bsub>(boolZFMISC-1K1 X)\<^esub>-of D holds p inTARSKIR2 A implies A =XBOOLE-0R4 projEQREL-1K16\<^bsub>(X)\<^esub> D .FUNCT-2K3\<^bsub>(X,D)\<^esub> p"
sorry

mtheorem eqrel_1_th_66:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>a-partitionEQREL-1M3-of X holds  for p be ElementSUBSET-1M3\<^bsub>(boolZFMISC-1K1 X)\<^esub>-of D holds p =XBOOLE-0R4 (projEQREL-1K16\<^bsub>(X)\<^esub> D)\<inverse>RELSET-1K8\<^bsub>(X,D)\<^esub> {DOMAIN-1K6\<^bsub>(D)\<^esub> p}"
sorry

mtheorem eqrel_1_th_67:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>a-partitionEQREL-1M3-of X holds  for A be SubsetSUBSET-1M2-of D holds (projEQREL-1K16\<^bsub>(X)\<^esub> D)\<inverse>RELSET-1K8\<^bsub>(X,D)\<^esub> A =XBOOLE-0R4 unionTARSKIK3 A"
sorry

mtheorem eqrel_1_th_68:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>a-partitionEQREL-1M3-of X holds  for W be ElementSUBSET-1M3\<^bsub>(boolZFMISC-1K1 X)\<^esub>-of D holds  ex W9 be ElementSUBSET-1M1-of X st projEQREL-1K16\<^bsub>(X)\<^esub> D .FUNCT-2K3\<^bsub>(X,D)\<^esub> W9 =XBOOLE-0R4 W"
sorry

mtheorem eqrel_1_th_69:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>a-partitionEQREL-1M3-of X holds  for W be SubsetSUBSET-1M2-of X holds ( for B be SubsetSUBSET-1M2-of X holds B inTARSKIR2 D & B meetsXBOOLE-0R5 W implies B c=TARSKIR1 W) implies W =XBOOLE-0R4 (projEQREL-1K16\<^bsub>(X)\<^esub> D)\<inverse>RELSET-1K8\<^bsub>(X,D)\<^esub> (projEQREL-1K16\<^bsub>(X)\<^esub> D .:RELSET-1K7\<^bsub>(X,D)\<^esub> W)"
sorry

mtheorem eqrel_1_th_70:
" for X be setHIDDENM2 holds  for P be a-partitionEQREL-1M3-of X holds  for x be setHIDDENM2 holds  for a be setHIDDENM2 holds  for b be setHIDDENM2 holds ((x inTARSKIR2 a & a inTARSKIR2 P) & x inTARSKIR2 b) & b inTARSKIR2 P implies a =XBOOLE-0R4 b"
  using eqrel_1_def_4 xboole_0_th_3 sorry

end
