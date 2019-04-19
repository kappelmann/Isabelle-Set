theory realset1
  imports funcop_1 setfam_1
begin
(*begin*)
mtheorem realset1_th_1:
" for X be setHIDDENM2 holds  for x be setHIDDENM2 holds  for F be FunctionFUNCT-2M1-of([:ZFMISC-1K2 X,X :],X) holds x inTARSKIR2 [:ZFMISC-1K2 X,X :] implies F .FUNCT-1K1 x inTARSKIR2 X"
sorry

mdef realset1_def_1 (" _ -binopclosedREALSET1V1\<^bsub>'( _ ')\<^esub>" [70,0]70 ) where
  mlet "X be setHIDDENM2", "F be BinOpBINOP-1M2-of X"
"attr F -binopclosedREALSET1V1\<^bsub>(X)\<^esub> for SubsetSUBSET-1M2-of X means
  (\<lambda>A.  for x be setHIDDENM2 holds x inTARSKIR2 [:ZFMISC-1K2 A,A :] implies F .FUNCT-1K1 x inTARSKIR2 A)"..

mtheorem realset1_cl_1:
  mlet "X be setHIDDENM2", "F be BinOpBINOP-1M2-of X"
"cluster X -binopclosedREALSET1V1\<^bsub>(F)\<^esub> for SubsetSUBSET-1M2-of X"
proof
(*existence*)
  show " ex it be SubsetSUBSET-1M2-of X st it be X -binopclosedREALSET1V1\<^bsub>(F)\<^esub>"
sorry
qed "sorry"

abbreviation(input) REALSET1M1("PreservREALSET1M1\<^bsub>'( _ ')\<^esub>-of  _ " [0,70]70) where
  "PreservREALSET1M1\<^bsub>(X)\<^esub>-of F \<equiv> X -binopclosedREALSET1V1\<^bsub>(F)\<^esub>\<bar>SubsetSUBSET-1M2-of X"

mdef realset1_def_2 (" _ ||REALSET1K1  _ " [200,200]200 ) where
  mlet "R be RelationRELAT-1M1", "A be setHIDDENM2"
"func R ||REALSET1K1 A \<rightarrow> setHIDDENM2 equals
  R |RELAT-1K8 ([:ZFMISC-1K2 A,A :])"
proof-
  (*coherence*)
    show "R |RELAT-1K8 ([:ZFMISC-1K2 A,A :]) be setHIDDENM2"
       sorry
qed "sorry"

mtheorem realset1_cl_2:
  mlet "R be RelationRELAT-1M1", "A be setHIDDENM2"
"cluster R ||REALSET1K1 A as-term-is Relation-likeRELAT-1V1"
proof
(*coherence*)
  show "R ||REALSET1K1 A be Relation-likeRELAT-1V1"
     sorry
qed "sorry"

mtheorem realset1_cl_3:
  mlet "R be FunctionFUNCT-1M1", "A be setHIDDENM2"
"cluster R ||REALSET1K1 A as-term-is Function-likeFUNCT-1V1"
proof
(*coherence*)
  show "R ||REALSET1K1 A be Function-likeFUNCT-1V1"
     sorry
qed "sorry"

mtheorem realset1_th_2:
" for X be setHIDDENM2 holds  for F be BinOpBINOP-1M2-of X holds  for A be X -binopclosedREALSET1V1\<^bsub>(F)\<^esub>\<bar>SubsetSUBSET-1M2-of X holds F ||REALSET1K1 A be BinOpBINOP-1M2-of A"
sorry

syntax REALSET1K2 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ ||REALSET1K2\<^bsub>'( _ ')\<^esub>  _ " [200,0,200]200)
translations "F ||REALSET1K2\<^bsub>(X)\<^esub> A" \<rightharpoonup> "F ||REALSET1K1 A"

mtheorem realset1_add_1:
  mlet "X be setHIDDENM2", "F be BinOpBINOP-1M2-of X", "A be X -binopclosedREALSET1V1\<^bsub>(F)\<^esub>\<bar>SubsetSUBSET-1M2-of X"
"cluster F ||REALSET1K1 A as-term-is BinOpBINOP-1M2-of A"
proof
(*coherence*)
  show "F ||REALSET1K1 A be BinOpBINOP-1M2-of A"
    using realset1_th_2 sorry
qed "sorry"

(*\$CT 2*)
mtheorem realset1_th_5:
" for X be setHIDDENM2 holds  for A be SubsetSUBSET-1M2-of X holds A be X -binopclosedREALSET1V1\<^bsub>(pr1FUNCT-3K10(X,X))\<^esub>"
sorry

(*\$CD*)
mdef realset1_def_4 (" _ -subsetpreservingREALSET1V2\<^bsub>'( _ ')\<^esub>" [70,0]70 ) where
  mlet "X be setHIDDENM2", "A be SubsetSUBSET-1M2-of X"
"attr A -subsetpreservingREALSET1V2\<^bsub>(X)\<^esub> for BinOpBINOP-1M2-of X means
  (\<lambda>F.  for x be setHIDDENM2 holds x inTARSKIR2 [:ZFMISC-1K2 A,A :] implies F .FUNCT-1K1 x inTARSKIR2 A)"..

mtheorem realset1_cl_4:
  mlet "X be setHIDDENM2", "A be SubsetSUBSET-1M2-of X"
"cluster X -subsetpreservingREALSET1V2\<^bsub>(A)\<^esub> for BinOpBINOP-1M2-of X"
proof
(*existence*)
  show " ex it be BinOpBINOP-1M2-of X st it be X -subsetpreservingREALSET1V2\<^bsub>(A)\<^esub>"
sorry
qed "sorry"

abbreviation(input) REALSET1M2("PresvREALSET1M2-of'( _ , _ ')" [0,0]70) where
  "PresvREALSET1M2-of(X,A) \<equiv> X -subsetpreservingREALSET1V2\<^bsub>(A)\<^esub>\<bar>BinOpBINOP-1M2-of X"

mtheorem realset1_th_6:
" for X be setHIDDENM2 holds  for A be SubsetSUBSET-1M2-of X holds  for F be X -subsetpreservingREALSET1V2\<^bsub>(A)\<^esub>\<bar>BinOpBINOP-1M2-of X holds F ||REALSET1K1 A be BinOpBINOP-1M2-of A"
sorry

mdef realset1_def_5 (" _ |||REALSET1K3\<^bsub>'( _ ')\<^esub>  _ " [200,0,200]200 ) where
  mlet "X be setHIDDENM2", "A be SubsetSUBSET-1M2-of X", "F be X -subsetpreservingREALSET1V2\<^bsub>(A)\<^esub>\<bar>BinOpBINOP-1M2-of X"
"func F |||REALSET1K3\<^bsub>(X)\<^esub> A \<rightarrow> BinOpBINOP-1M2-of A equals
  F ||REALSET1K1 A"
proof-
  (*coherence*)
    show "F ||REALSET1K1 A be BinOpBINOP-1M2-of A"
      using realset1_th_6 sorry
qed "sorry"

mtheorem realset1_th_7:
" for A be  non trivialSUBSET-1V2\<bar>setHIDDENM2 holds  for x be ElementSUBSET-1M1-of A holds  for F be A -subsetpreservingREALSET1V2\<^bsub>(A \\SUBSET-1K6 {DOMAIN-1K6\<^bsub>(A)\<^esub> x})\<^esub>\<bar>BinOpBINOP-1M2-of A holds F ||REALSET1K1 (A \\SUBSET-1K6 {DOMAIN-1K6\<^bsub>(A)\<^esub> x}) be BinOpBINOP-1M2-of A \\SUBSET-1K6 {DOMAIN-1K6\<^bsub>(A)\<^esub> x}"
sorry

(*\$CD*)
mdef realset1_def_7 (" _ !REALSET1K4'( _ , _ ')" [164,0,0]164 ) where
  mlet "A be  non trivialSUBSET-1V2\<bar>setHIDDENM2", "x be ElementSUBSET-1M1-of A", "F be A -subsetpreservingREALSET1V2\<^bsub>(A \\SUBSET-1K6 {DOMAIN-1K6\<^bsub>(A)\<^esub> x})\<^esub>\<bar>BinOpBINOP-1M2-of A"
"func F !REALSET1K4(A,x) \<rightarrow> BinOpBINOP-1M2-of A \\SUBSET-1K6 {DOMAIN-1K6\<^bsub>(A)\<^esub> x} equals
  F ||REALSET1K1 (A \\SUBSET-1K6 {DOMAIN-1K6\<^bsub>(A)\<^esub> x})"
proof-
  (*coherence*)
    show "F ||REALSET1K1 (A \\SUBSET-1K6 {DOMAIN-1K6\<^bsub>(A)\<^esub> x}) be BinOpBINOP-1M2-of A \\SUBSET-1K6 {DOMAIN-1K6\<^bsub>(A)\<^esub> x}"
      using realset1_th_7 sorry
qed "sorry"

end
