theory toler_1
  imports eqrel_1 enumset1 xfamily
begin
(*begin*)
reserve X, Y, Z, x, y, z for "setHIDDENM2"
mtheorem toler_1_cl_1:
"cluster emptyXBOOLE-0V1 also-is reflexiveRELAT-2V1\<bar>irreflexiveRELAT-2V2\<bar>symmetricRELAT-2V3\<bar>antisymmetricRELAT-2V4\<bar>asymmetricRELAT-2V5\<bar>connectedRELAT-2V6\<bar>strongly-connectedRELAT-2V7\<bar>transitiveRELAT-2V8 for RelationRELAT-1M1"
proof
(*coherence*)
  show " for it be RelationRELAT-1M1 holds it be emptyXBOOLE-0V1 implies it be reflexiveRELAT-2V1\<bar>irreflexiveRELAT-2V2\<bar>symmetricRELAT-2V3\<bar>antisymmetricRELAT-2V4\<bar>asymmetricRELAT-2V5\<bar>connectedRELAT-2V6\<bar>strongly-connectedRELAT-2V7\<bar>transitiveRELAT-2V8"
sorry
qed "sorry"

abbreviation(input) TOLER_1K1("TotalTOLER-1K1  _ " [164]164) where
  "TotalTOLER-1K1 X \<equiv> nablaEQREL-1K1 X"

abbreviation(input) TOLER_1K2(" _ |-2TOLER-1K2  _ " [200,200]200) where
  "R |-2TOLER-1K2 Y \<equiv> R |-2WELLORD1K2 Y"

mtheorem toler_1_add_1:
  mlet "R be RelationRELAT-1M1", "Y be setHIDDENM2"
"cluster R |-2WELLORD1K2 Y as-term-is RelationRELSET-1M1-of(Y,Y)"
proof
(*coherence*)
  show "R |-2WELLORD1K2 Y be RelationRELSET-1M1-of(Y,Y)"
    using xboole_1_th_17 sorry
qed "sorry"

mtheorem toler_1_th_1:
" for X be setHIDDENM2 holds rngRELSET-1K2\<^bsub>(X)\<^esub> (TotalTOLER-1K1 X) =XBOOLE-0R4 X"
sorry

mtheorem toler_1_th_2:
" for X be setHIDDENM2 holds  for x be setHIDDENM2 holds  for y be setHIDDENM2 holds x inTARSKIR2 X & y inTARSKIR2 X implies [TARSKIK4 x,y ] inHIDDENR3 TotalTOLER-1K1 X"
sorry

mtheorem toler_1_th_3:
" for X be setHIDDENM2 holds  for x be setHIDDENM2 holds  for y be setHIDDENM2 holds x inTARSKIR2 fieldRELAT-1K3 (TotalTOLER-1K1 X) & y inTARSKIR2 fieldRELAT-1K3 (TotalTOLER-1K1 X) implies [TARSKIK4 x,y ] inHIDDENR3 TotalTOLER-1K1 X"
sorry

mtheorem toler_1_th_4:
" for X be setHIDDENM2 holds TotalTOLER-1K1 X be strongly-connectedRELAT-2V7"
sorry

mtheorem toler_1_th_5:
" for X be setHIDDENM2 holds TotalTOLER-1K1 X be connectedRELAT-2V6"
sorry

reserve T, R for "ToleranceEQREL-1M1-of X"
mtheorem toler_1_th_6:
" for X be setHIDDENM2 holds  for T be ToleranceEQREL-1M1-of X holds rngRELSET-1K2\<^bsub>(X)\<^esub> T =XBOOLE-0R4 X"
sorry

mtheorem toler_1_th_7:
" for X be setHIDDENM2 holds  for x be objectHIDDENM1 holds  for T be totalPARTFUN1V1\<^bsub>(X)\<^esub>\<bar>reflexiveRELAT-2V1\<bar>RelationRELSET-1M2-of X holds x inHIDDENR3 X iff [TARSKIK4 x,x ] inHIDDENR3 T"
sorry

mtheorem toler_1_th_8:
" for X be setHIDDENM2 holds  for T be ToleranceEQREL-1M1-of X holds T is-reflexive-inRELAT-2R1 X"
sorry

mtheorem toler_1_th_9:
" for X be setHIDDENM2 holds  for T be ToleranceEQREL-1M1-of X holds T is-symmetric-inRELAT-2R3 X"
sorry

mtheorem toler_1_th_10:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds  for R be RelationRELSET-1M1-of(X,Y) holds R be symmetricRELAT-2V3 implies R |-2TOLER-1K2 Z be symmetricRELAT-2V3"
sorry

syntax TOLER_1K3 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ |-2TOLER-1K3\<^bsub>'( _ ')\<^esub>  _ " [200,0,200]200)
translations "T |-2TOLER-1K3\<^bsub>(X)\<^esub> Y" \<rightharpoonup> "T |-2WELLORD1K2 Y"

mtheorem toler_1_add_2:
  mlet "X be setHIDDENM2", "T be ToleranceEQREL-1M1-of X", "Y be SubsetSUBSET-1M2-of X"
"cluster T |-2WELLORD1K2 Y as-term-is ToleranceEQREL-1M1-of Y"
proof
(*coherence*)
  show "T |-2WELLORD1K2 Y be ToleranceEQREL-1M1-of Y"
sorry
qed "sorry"

mtheorem toler_1_th_11:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for T be ToleranceEQREL-1M1-of X holds Y c=TARSKIR1 X implies T |-2TOLER-1K2 Y be ToleranceEQREL-1M1-of Y"
sorry

mdef toler_1_def_1 ("TolSetTOLER-1M1\<^bsub>'( _ ')\<^esub>-of  _ " [0,70]70 ) where
  mlet "X be setHIDDENM2", "T be ToleranceEQREL-1M1-of X"
"mode TolSetTOLER-1M1\<^bsub>(X)\<^esub>-of T \<rightarrow> setHIDDENM2 means
  (\<lambda>it.  for x be setHIDDENM2 holds  for y be setHIDDENM2 holds x inTARSKIR2 it & y inTARSKIR2 it implies [TARSKIK4 x,y ] inHIDDENR3 T)"
proof-
  (*existence*)
    show " ex it be setHIDDENM2 st  for x be setHIDDENM2 holds  for y be setHIDDENM2 holds x inTARSKIR2 it & y inTARSKIR2 it implies [TARSKIK4 x,y ] inHIDDENR3 T"
sorry
qed "sorry"

mtheorem toler_1_th_12:
" for X be setHIDDENM2 holds  for T be ToleranceEQREL-1M1-of X holds {}XBOOLE-0K1 be TolSetTOLER-1M1\<^bsub>(X)\<^esub>-of T"
sorry

mdef toler_1_def_2 ("TolClass-likeTOLER-1V1\<^bsub>'( _ , _ ')\<^esub>" [0,0]70 ) where
  mlet "X be setHIDDENM2", "T be ToleranceEQREL-1M1-of X"
"attr TolClass-likeTOLER-1V1\<^bsub>(X,T)\<^esub> for TolSetTOLER-1M1\<^bsub>(X)\<^esub>-of T means
  (\<lambda>IT.  for x be setHIDDENM2 holds  not x inTARSKIR2 IT & x inTARSKIR2 X implies ( ex y be setHIDDENM2 st y inTARSKIR2 IT &  not [TARSKIK4 x,y ] inHIDDENR3 T))"..

mtheorem toler_1_cl_2:
  mlet "X be setHIDDENM2", "T be ToleranceEQREL-1M1-of X"
"cluster TolClass-likeTOLER-1V1\<^bsub>(X,T)\<^esub> for TolSetTOLER-1M1\<^bsub>(X)\<^esub>-of T"
proof
(*existence*)
  show " ex it be TolSetTOLER-1M1\<^bsub>(X)\<^esub>-of T st it be TolClass-likeTOLER-1V1\<^bsub>(X,T)\<^esub>"
sorry
qed "sorry"

abbreviation(input) TOLER_1M2("TolClassTOLER-1M2\<^bsub>'( _ ')\<^esub>-of  _ " [0,70]70) where
  "TolClassTOLER-1M2\<^bsub>(X)\<^esub>-of T \<equiv> TolClass-likeTOLER-1V1\<^bsub>(X,T)\<^esub>\<bar>TolSetTOLER-1M1\<^bsub>(X)\<^esub>-of T"

mtheorem toler_1_th_13:
" for X be setHIDDENM2 holds  for T be ToleranceEQREL-1M1-of X holds {}XBOOLE-0K1 be TolClassTOLER-1M2\<^bsub>(X)\<^esub>-of T implies T =RELAT-1R1 {}XBOOLE-0K1"
sorry

mtheorem toler_1_th_14:
"{}XBOOLE-0K1 be ToleranceEQREL-1M1-of {}XBOOLE-0K1"
  using relset_1_th_12 sorry

mtheorem toler_1_th_15:
" for X be setHIDDENM2 holds  for T be ToleranceEQREL-1M1-of X holds  for x be setHIDDENM2 holds  for y be setHIDDENM2 holds [TARSKIK4 x,y ] inHIDDENR3 T implies {TARSKIK2 x,y } be TolSetTOLER-1M1\<^bsub>(X)\<^esub>-of T"
sorry

mtheorem toler_1_th_16:
" for X be setHIDDENM2 holds  for T be ToleranceEQREL-1M1-of X holds  for x be setHIDDENM2 holds x inTARSKIR2 X implies {TARSKIK1 x} be TolSetTOLER-1M1\<^bsub>(X)\<^esub>-of T"
sorry

mtheorem toler_1_th_17:
" for X be setHIDDENM2 holds  for T be ToleranceEQREL-1M1-of X holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds Y be TolSetTOLER-1M1\<^bsub>(X)\<^esub>-of T implies Y /\\XBOOLE-0K3 Z be TolSetTOLER-1M1\<^bsub>(X)\<^esub>-of T"
sorry

mtheorem toler_1_th_18:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for T be ToleranceEQREL-1M1-of X holds Y be TolSetTOLER-1M1\<^bsub>(X)\<^esub>-of T implies Y c=TARSKIR1 X"
sorry

mtheorem toler_1_th_19:
" for X be setHIDDENM2 holds  for T be ToleranceEQREL-1M1-of X holds  for Y be TolSetTOLER-1M1\<^bsub>(X)\<^esub>-of T holds  ex Z be TolClassTOLER-1M2\<^bsub>(X)\<^esub>-of T st Y c=TARSKIR1 Z"
sorry

mtheorem toler_1_th_20:
" for X be setHIDDENM2 holds  for T be ToleranceEQREL-1M1-of X holds  for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds [TARSKIK4 x,y ] inHIDDENR3 T implies ( ex Z be TolClassTOLER-1M2\<^bsub>(X)\<^esub>-of T st x inHIDDENR3 Z & y inHIDDENR3 Z)"
sorry

mtheorem toler_1_th_21:
" for X be setHIDDENM2 holds  for T be ToleranceEQREL-1M1-of X holds  for x be setHIDDENM2 holds x inTARSKIR2 X implies ( ex Z be TolClassTOLER-1M2\<^bsub>(X)\<^esub>-of T st x inTARSKIR2 Z)"
sorry

mtheorem toler_1_th_22:
" for X be setHIDDENM2 holds  for T be ToleranceEQREL-1M1-of X holds T c=RELSET-1R1\<^bsub>(X,X)\<^esub> TotalTOLER-1K1 X"
sorry

mtheorem toler_1_th_23:
" for X be setHIDDENM2 holds  for T be ToleranceEQREL-1M1-of X holds idPARTFUN1K6 X c=RELSET-1R1\<^bsub>(X,X)\<^esub> T"
sorry

theorem toler_1_sch_1:
  fixes Af0 Pp2 
  assumes
[ty]: "Af0 be setHIDDENM2" and
   A1: " for x be setHIDDENM2 holds x inTARSKIR2 Af0 implies Pp2(x,x)" and
   A2: " for x be setHIDDENM2 holds  for y be setHIDDENM2 holds (x inTARSKIR2 Af0 & y inTARSKIR2 Af0) & Pp2(x,y) implies Pp2(y,x)"
  shows " ex T be ToleranceEQREL-1M1-of Af0 st  for x be setHIDDENM2 holds  for y be setHIDDENM2 holds x inTARSKIR2 Af0 & y inTARSKIR2 Af0 implies ([TARSKIK4 x,y ] inHIDDENR3 T iff Pp2(x,y))"
sorry

mtheorem toler_1_th_24:
" for Y be setHIDDENM2 holds  ex T be ToleranceEQREL-1M1-of unionTARSKIK3 Y st  for Z be setHIDDENM2 holds Z inTARSKIR2 Y implies Z be TolSetTOLER-1M1\<^bsub>(unionTARSKIK3 Y)\<^esub>-of T"
sorry

mtheorem toler_1_th_25:
" for Y be setHIDDENM2 holds  for T be ToleranceEQREL-1M1-of unionTARSKIK3 Y holds  for R be ToleranceEQREL-1M1-of unionTARSKIK3 Y holds ( for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds [TARSKIK4 x,y ] inHIDDENR3 T iff ( ex Z be setHIDDENM2 st (Z inTARSKIR2 Y & x inHIDDENR3 Z) & y inHIDDENR3 Z)) & ( for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds [TARSKIK4 x,y ] inHIDDENR3 R iff ( ex Z be setHIDDENM2 st (Z inTARSKIR2 Y & x inHIDDENR3 Z) & y inHIDDENR3 Z)) implies T =RELSET-1R2\<^bsub>(unionTARSKIK3 Y,unionTARSKIK3 Y)\<^esub> R"
sorry

mtheorem toler_1_th_26:
" for X be setHIDDENM2 holds  for T be ToleranceEQREL-1M1-of X holds  for R be ToleranceEQREL-1M1-of X holds ( for Z be setHIDDENM2 holds Z be TolClassTOLER-1M2\<^bsub>(X)\<^esub>-of T iff Z be TolClassTOLER-1M2\<^bsub>(X)\<^esub>-of R) implies T =RELSET-1R2\<^bsub>(X,X)\<^esub> R"
sorry

syntax TOLER_1K4 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" ("neighbourhoodTOLER-1K4\<^bsub>'( _ , _ ')\<^esub>'( _ , _ ')" [0,0,0,0]164)
translations "neighbourhoodTOLER-1K4\<^bsub>(X,Y)\<^esub>(x,T)" \<rightharpoonup> "ClassEQREL-1K6(T,x)"

mtheorem toler_1_th_27:
" for X be setHIDDENM2 holds  for T be ToleranceEQREL-1M1-of X holds  for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds y inHIDDENR3 ImRELAT-1K12(T,x) iff [TARSKIK4 x,y ] inHIDDENR3 T"
sorry

mtheorem toler_1_th_28:
" for X be setHIDDENM2 holds  for x be setHIDDENM2 holds  for T be ToleranceEQREL-1M1-of X holds  for Y be setHIDDENM2 holds ( for Z be setHIDDENM2 holds Z inTARSKIR2 Y iff x inTARSKIR2 Z & Z be TolClassTOLER-1M2\<^bsub>(X)\<^esub>-of T) implies ImRELAT-1K12(T,x) =XBOOLE-0R4 unionTARSKIK3 Y"
sorry

mtheorem toler_1_th_29:
" for X be setHIDDENM2 holds  for x be setHIDDENM2 holds  for T be ToleranceEQREL-1M1-of X holds  for Y be setHIDDENM2 holds ( for Z be setHIDDENM2 holds Z inTARSKIR2 Y iff x inTARSKIR2 Z & Z be TolSetTOLER-1M1\<^bsub>(X)\<^esub>-of T) implies ImRELAT-1K12(T,x) =XBOOLE-0R4 unionTARSKIK3 Y"
sorry

mdef toler_1_def_3 ("TolSetsTOLER-1K5\<^bsub>'( _ ')\<^esub>  _ " [0,164]164 ) where
  mlet "X be setHIDDENM2", "T be ToleranceEQREL-1M1-of X"
"func TolSetsTOLER-1K5\<^bsub>(X)\<^esub> T \<rightarrow> setHIDDENM2 means
  \<lambda>it.  for Y be setHIDDENM2 holds Y inTARSKIR2 it iff Y be TolSetTOLER-1M1\<^bsub>(X)\<^esub>-of T"
proof-
  (*existence*)
    show " ex it be setHIDDENM2 st  for Y be setHIDDENM2 holds Y inTARSKIR2 it iff Y be TolSetTOLER-1M1\<^bsub>(X)\<^esub>-of T"
sorry
  (*uniqueness*)
    show " for it1 be setHIDDENM2 holds  for it2 be setHIDDENM2 holds ( for Y be setHIDDENM2 holds Y inTARSKIR2 it1 iff Y be TolSetTOLER-1M1\<^bsub>(X)\<^esub>-of T) & ( for Y be setHIDDENM2 holds Y inTARSKIR2 it2 iff Y be TolSetTOLER-1M1\<^bsub>(X)\<^esub>-of T) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mdef toler_1_def_4 ("TolClassesTOLER-1K6\<^bsub>'( _ ')\<^esub>  _ " [0,164]164 ) where
  mlet "X be setHIDDENM2", "T be ToleranceEQREL-1M1-of X"
"func TolClassesTOLER-1K6\<^bsub>(X)\<^esub> T \<rightarrow> setHIDDENM2 means
  \<lambda>it.  for Y be setHIDDENM2 holds Y inTARSKIR2 it iff Y be TolClassTOLER-1M2\<^bsub>(X)\<^esub>-of T"
proof-
  (*existence*)
    show " ex it be setHIDDENM2 st  for Y be setHIDDENM2 holds Y inTARSKIR2 it iff Y be TolClassTOLER-1M2\<^bsub>(X)\<^esub>-of T"
sorry
  (*uniqueness*)
    show " for it1 be setHIDDENM2 holds  for it2 be setHIDDENM2 holds ( for Y be setHIDDENM2 holds Y inTARSKIR2 it1 iff Y be TolClassTOLER-1M2\<^bsub>(X)\<^esub>-of T) & ( for Y be setHIDDENM2 holds Y inTARSKIR2 it2 iff Y be TolClassTOLER-1M2\<^bsub>(X)\<^esub>-of T) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mtheorem toler_1_th_30:
" for X be setHIDDENM2 holds  for T be ToleranceEQREL-1M1-of X holds  for R be ToleranceEQREL-1M1-of X holds TolClassesTOLER-1K6\<^bsub>(X)\<^esub> R c=TARSKIR1 TolClassesTOLER-1K6\<^bsub>(X)\<^esub> T implies R c=RELSET-1R1\<^bsub>(X,X)\<^esub> T"
sorry

mtheorem toler_1_th_31:
" for X be setHIDDENM2 holds  for T be ToleranceEQREL-1M1-of X holds  for R be ToleranceEQREL-1M1-of X holds TolClassesTOLER-1K6\<^bsub>(X)\<^esub> T =XBOOLE-0R4 TolClassesTOLER-1K6\<^bsub>(X)\<^esub> R implies T =RELSET-1R2\<^bsub>(X,X)\<^esub> R"
sorry

mtheorem toler_1_th_32:
" for X be setHIDDENM2 holds  for T be ToleranceEQREL-1M1-of X holds unionTARSKIK3 (TolClassesTOLER-1K6\<^bsub>(X)\<^esub> T) =XBOOLE-0R4 X"
sorry

mtheorem toler_1_th_33:
" for X be setHIDDENM2 holds  for T be ToleranceEQREL-1M1-of X holds unionTARSKIK3 (TolSetsTOLER-1K5\<^bsub>(X)\<^esub> T) =XBOOLE-0R4 X"
sorry

mtheorem toler_1_th_34:
" for X be setHIDDENM2 holds  for T be ToleranceEQREL-1M1-of X holds ( for x be setHIDDENM2 holds x inTARSKIR2 X implies ImRELAT-1K12(T,x) be TolSetTOLER-1M1\<^bsub>(X)\<^esub>-of T) implies T be transitiveRELAT-2V8"
sorry

mtheorem toler_1_th_35:
" for X be setHIDDENM2 holds  for T be ToleranceEQREL-1M1-of X holds T be transitiveRELAT-2V8 implies ( for x be setHIDDENM2 holds x inTARSKIR2 X implies ImRELAT-1K12(T,x) be TolClassTOLER-1M2\<^bsub>(X)\<^esub>-of T)"
sorry

mtheorem toler_1_th_36:
" for X be setHIDDENM2 holds  for T be ToleranceEQREL-1M1-of X holds  for x be setHIDDENM2 holds  for Y be TolClassTOLER-1M2\<^bsub>(X)\<^esub>-of T holds x inTARSKIR2 Y implies Y c=TARSKIR1 ImRELAT-1K12(T,x)"
sorry

mtheorem toler_1_th_37:
" for X be setHIDDENM2 holds  for T be ToleranceEQREL-1M1-of X holds  for R be ToleranceEQREL-1M1-of X holds TolSetsTOLER-1K5\<^bsub>(X)\<^esub> R c=TARSKIR1 TolSetsTOLER-1K5\<^bsub>(X)\<^esub> T iff R c=RELSET-1R1\<^bsub>(X,X)\<^esub> T"
sorry

mtheorem toler_1_th_38:
" for X be setHIDDENM2 holds  for T be ToleranceEQREL-1M1-of X holds TolClassesTOLER-1K6\<^bsub>(X)\<^esub> T c=TARSKIR1 TolSetsTOLER-1K5\<^bsub>(X)\<^esub> T"
sorry

mtheorem toler_1_th_39:
" for X be setHIDDENM2 holds  for T be ToleranceEQREL-1M1-of X holds  for R be ToleranceEQREL-1M1-of X holds ( for x be setHIDDENM2 holds x inTARSKIR2 X implies ImRELAT-1K12(R,x) c=TARSKIR1 ImRELAT-1K12(T,x)) implies R c=RELSET-1R1\<^bsub>(X,X)\<^esub> T"
sorry

mtheorem toler_1_th_40:
" for X be setHIDDENM2 holds  for T be ToleranceEQREL-1M1-of X holds T c=RELSET-1R1\<^bsub>(X,X)\<^esub> T *RELSET-1K4\<^bsub>(X,X,X,X)\<^esub> T"
sorry

end
