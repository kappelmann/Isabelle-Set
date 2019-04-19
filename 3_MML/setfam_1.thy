theory setfam_1
  imports subset_1 xfamily
begin
(*begin*)
reserve X, Y, Z, Z1, Z2, D for "setHIDDENM2"
reserve x, y for "objectHIDDENM1"
mdef setfam_1_def_1 ("meetSETFAM-1K1  _ " [228]228 ) where
  mlet "X be setHIDDENM2"
"func meetSETFAM-1K1 X \<rightarrow> setHIDDENM2 means
  \<lambda>it.  for x be objectHIDDENM1 holds x inHIDDENR3 it iff ( for Y be setHIDDENM2 holds Y inTARSKIR2 X implies x inHIDDENR3 Y) if X <>HIDDENR2 {}XBOOLE-0K1 otherwise \<lambda>it. it =XBOOLE-0R4 {}XBOOLE-0K1"
proof-
  (*existence*)
    show "(X <>HIDDENR2 {}XBOOLE-0K1 implies ( ex it be setHIDDENM2 st  for x be objectHIDDENM1 holds x inHIDDENR3 it iff ( for Y be setHIDDENM2 holds Y inTARSKIR2 X implies x inHIDDENR3 Y))) & ( not X <>HIDDENR2 {}XBOOLE-0K1 implies ( ex it be setHIDDENM2 st it =XBOOLE-0R4 {}XBOOLE-0K1))"
sorry
  (*uniqueness*)
    show " for it1 be setHIDDENM2 holds  for it2 be setHIDDENM2 holds (X <>HIDDENR2 {}XBOOLE-0K1 implies (( for x be objectHIDDENM1 holds x inHIDDENR3 it1 iff ( for Y be setHIDDENM2 holds Y inTARSKIR2 X implies x inHIDDENR3 Y)) & ( for x be objectHIDDENM1 holds x inHIDDENR3 it2 iff ( for Y be setHIDDENM2 holds Y inTARSKIR2 X implies x inHIDDENR3 Y)) implies it1 =HIDDENR1 it2)) & ( not X <>HIDDENR2 {}XBOOLE-0K1 implies (it1 =XBOOLE-0R4 {}XBOOLE-0K1 & it2 =XBOOLE-0R4 {}XBOOLE-0K1 implies it1 =HIDDENR1 it2))"
sorry
  (*consistency*)
    show " for it be setHIDDENM2 holds  True "
       sorry
qed "sorry"

mtheorem setfam_1_th_1:
"meetSETFAM-1K1 ({}XBOOLE-0K1) =XBOOLE-0R4 {}XBOOLE-0K1"
  using setfam_1_def_1 sorry

mtheorem setfam_1_th_2:
" for X be setHIDDENM2 holds meetSETFAM-1K1 X c=TARSKIR1 unionTARSKIK3 X"
sorry

mtheorem setfam_1_th_3:
" for X be setHIDDENM2 holds  for Z be setHIDDENM2 holds Z inTARSKIR2 X implies meetSETFAM-1K1 X c=TARSKIR1 Z"
  using setfam_1_def_1 sorry

mtheorem setfam_1_th_4:
" for X be setHIDDENM2 holds {}XBOOLE-0K1 inTARSKIR2 X implies meetSETFAM-1K1 X =XBOOLE-0R4 {}XBOOLE-0K1"
  using setfam_1_th_3 xboole_1_th_3 sorry

mtheorem setfam_1_th_5:
" for X be setHIDDENM2 holds  for Z be setHIDDENM2 holds X <>HIDDENR2 {}XBOOLE-0K1 & ( for Z1 be setHIDDENM2 holds Z1 inTARSKIR2 X implies Z c=TARSKIR1 Z1) implies Z c=TARSKIR1 meetSETFAM-1K1 X"
sorry

mtheorem setfam_1_th_6:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X <>HIDDENR2 {}XBOOLE-0K1 & X c=TARSKIR1 Y implies meetSETFAM-1K1 Y c=TARSKIR1 meetSETFAM-1K1 X"
sorry

mtheorem setfam_1_th_7:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds X inTARSKIR2 Y & X c=TARSKIR1 Z implies meetSETFAM-1K1 Y c=TARSKIR1 Z"
sorry

mtheorem setfam_1_th_8:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds X inTARSKIR2 Y & X missesXBOOLE-0R1 Z implies meetSETFAM-1K1 Y missesXBOOLE-0R1 Z"
  using setfam_1_th_3 xboole_1_th_63 sorry

mtheorem setfam_1_th_9:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X <>HIDDENR2 {}XBOOLE-0K1 & Y <>HIDDENR2 {}XBOOLE-0K1 implies meetSETFAM-1K1 (X \\/XBOOLE-0K2 Y) =XBOOLE-0R4 meetSETFAM-1K1 X /\\XBOOLE-0K3 meetSETFAM-1K1 Y"
sorry

mtheorem setfam_1_th_10:
" for X be setHIDDENM2 holds meetSETFAM-1K1 {TARSKIK1 X} =XBOOLE-0R4 X"
sorry

mtheorem setfam_1_th_11:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds meetSETFAM-1K1 {TARSKIK2 X,Y } =XBOOLE-0R4 X /\\XBOOLE-0K3 Y"
sorry

reserve SFX, SFY, SFZ for "setHIDDENM2"
mdef setfam_1_def_2 (" _ is-finer-thanSETFAM-1R1  _ " [50,50]50 ) where
  mlet "SFX be setHIDDENM2", "SFY be setHIDDENM2"
"pred SFX is-finer-thanSETFAM-1R1 SFY means
   for X be setHIDDENM2 holds X inTARSKIR2 SFX implies ( ex Y be setHIDDENM2 st Y inTARSKIR2 SFY & X c=TARSKIR1 Y)"..

mtheorem SETFAM_1R1_reflexivity:
" for SFY be setHIDDENM2 holds SFY is-finer-thanSETFAM-1R1 SFY"
sorry

mdef setfam_1_def_3 (" _ is-coarser-thanSETFAM-1R2  _ " [50,50]50 ) where
  mlet "SFX be setHIDDENM2", "SFY be setHIDDENM2"
"pred SFY is-coarser-thanSETFAM-1R2 SFX means
   for Y be setHIDDENM2 holds Y inTARSKIR2 SFY implies ( ex X be setHIDDENM2 st X inTARSKIR2 SFX & X c=TARSKIR1 Y)"..

mtheorem SETFAM_1R2_reflexivity:
" for SFY be setHIDDENM2 holds SFY is-coarser-thanSETFAM-1R2 SFY"
sorry

mtheorem setfam_1_th_12:
" for SFX be setHIDDENM2 holds  for SFY be setHIDDENM2 holds SFX c=TARSKIR1 SFY implies SFX is-finer-thanSETFAM-1R1 SFY"
   sorry

mtheorem setfam_1_th_13:
" for SFX be setHIDDENM2 holds  for SFY be setHIDDENM2 holds SFX is-finer-thanSETFAM-1R1 SFY implies unionTARSKIK3 SFX c=TARSKIR1 unionTARSKIK3 SFY"
sorry

mtheorem setfam_1_th_14:
" for SFX be setHIDDENM2 holds  for SFY be setHIDDENM2 holds SFY <>HIDDENR2 {}XBOOLE-0K1 & SFY is-coarser-thanSETFAM-1R2 SFX implies meetSETFAM-1K1 SFX c=TARSKIR1 meetSETFAM-1K1 SFY"
sorry

mtheorem setfam_1_th_15:
" for SFX be setHIDDENM2 holds {}XBOOLE-0K1 is-finer-thanSETFAM-1R1 SFX"
   sorry

mtheorem setfam_1_th_16:
" for SFX be setHIDDENM2 holds SFX is-finer-thanSETFAM-1R1 {}XBOOLE-0K1 implies SFX =XBOOLE-0R4 {}XBOOLE-0K1"
sorry

mtheorem setfam_1_th_17:
" for SFX be setHIDDENM2 holds  for SFY be setHIDDENM2 holds  for SFZ be setHIDDENM2 holds SFX is-finer-thanSETFAM-1R1 SFY & SFY is-finer-thanSETFAM-1R1 SFZ implies SFX is-finer-thanSETFAM-1R1 SFZ"
sorry

mtheorem setfam_1_th_18:
" for Y be setHIDDENM2 holds  for SFX be setHIDDENM2 holds SFX is-finer-thanSETFAM-1R1 {TARSKIK1 Y} implies ( for X be setHIDDENM2 holds X inTARSKIR2 SFX implies X c=TARSKIR1 Y)"
sorry

mtheorem setfam_1_th_19:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for SFX be setHIDDENM2 holds SFX is-finer-thanSETFAM-1R1 {TARSKIK2 X,Y } implies ( for Z be setHIDDENM2 holds Z inTARSKIR2 SFX implies Z c=TARSKIR1 X or Z c=TARSKIR1 Y)"
sorry

mdef setfam_1_def_4 ("UNIONSETFAM-1K2'( _ , _ ')" [0,0]164 ) where
  mlet "SFX be setHIDDENM2", "SFY be setHIDDENM2"
"func UNIONSETFAM-1K2(SFX,SFY) \<rightarrow> setHIDDENM2 means
  \<lambda>it.  for Z be setHIDDENM2 holds Z inTARSKIR2 it iff ( ex X be setHIDDENM2 st  ex Y be setHIDDENM2 st (X inTARSKIR2 SFX & Y inTARSKIR2 SFY) & Z =XBOOLE-0R4 X \\/XBOOLE-0K2 Y)"
proof-
  (*existence*)
    show " ex it be setHIDDENM2 st  for Z be setHIDDENM2 holds Z inTARSKIR2 it iff ( ex X be setHIDDENM2 st  ex Y be setHIDDENM2 st (X inTARSKIR2 SFX & Y inTARSKIR2 SFY) & Z =XBOOLE-0R4 X \\/XBOOLE-0K2 Y)"
sorry
  (*uniqueness*)
    show " for it1 be setHIDDENM2 holds  for it2 be setHIDDENM2 holds ( for Z be setHIDDENM2 holds Z inTARSKIR2 it1 iff ( ex X be setHIDDENM2 st  ex Y be setHIDDENM2 st (X inTARSKIR2 SFX & Y inTARSKIR2 SFY) & Z =XBOOLE-0R4 X \\/XBOOLE-0K2 Y)) & ( for Z be setHIDDENM2 holds Z inTARSKIR2 it2 iff ( ex X be setHIDDENM2 st  ex Y be setHIDDENM2 st (X inTARSKIR2 SFX & Y inTARSKIR2 SFY) & Z =XBOOLE-0R4 X \\/XBOOLE-0K2 Y)) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mtheorem SETFAM_1K2_commutativity:
" for SFX be setHIDDENM2 holds  for SFY be setHIDDENM2 holds UNIONSETFAM-1K2(SFX,SFY) =HIDDENR1 UNIONSETFAM-1K2(SFY,SFX)"
sorry

mdef setfam_1_def_5 ("INTERSECTIONSETFAM-1K3'( _ , _ ')" [0,0]164 ) where
  mlet "SFX be setHIDDENM2", "SFY be setHIDDENM2"
"func INTERSECTIONSETFAM-1K3(SFX,SFY) \<rightarrow> setHIDDENM2 means
  \<lambda>it.  for Z be setHIDDENM2 holds Z inTARSKIR2 it iff ( ex X be setHIDDENM2 st  ex Y be setHIDDENM2 st (X inTARSKIR2 SFX & Y inTARSKIR2 SFY) & Z =XBOOLE-0R4 X /\\XBOOLE-0K3 Y)"
proof-
  (*existence*)
    show " ex it be setHIDDENM2 st  for Z be setHIDDENM2 holds Z inTARSKIR2 it iff ( ex X be setHIDDENM2 st  ex Y be setHIDDENM2 st (X inTARSKIR2 SFX & Y inTARSKIR2 SFY) & Z =XBOOLE-0R4 X /\\XBOOLE-0K3 Y)"
sorry
  (*uniqueness*)
    show " for it1 be setHIDDENM2 holds  for it2 be setHIDDENM2 holds ( for Z be setHIDDENM2 holds Z inTARSKIR2 it1 iff ( ex X be setHIDDENM2 st  ex Y be setHIDDENM2 st (X inTARSKIR2 SFX & Y inTARSKIR2 SFY) & Z =XBOOLE-0R4 X /\\XBOOLE-0K3 Y)) & ( for Z be setHIDDENM2 holds Z inTARSKIR2 it2 iff ( ex X be setHIDDENM2 st  ex Y be setHIDDENM2 st (X inTARSKIR2 SFX & Y inTARSKIR2 SFY) & Z =XBOOLE-0R4 X /\\XBOOLE-0K3 Y)) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mtheorem SETFAM_1K3_commutativity:
" for SFX be setHIDDENM2 holds  for SFY be setHIDDENM2 holds INTERSECTIONSETFAM-1K3(SFX,SFY) =HIDDENR1 INTERSECTIONSETFAM-1K3(SFY,SFX)"
sorry

mdef setfam_1_def_6 ("DIFFERENCESETFAM-1K4'( _ , _ ')" [0,0]164 ) where
  mlet "SFX be setHIDDENM2", "SFY be setHIDDENM2"
"func DIFFERENCESETFAM-1K4(SFX,SFY) \<rightarrow> setHIDDENM2 means
  \<lambda>it.  for Z be setHIDDENM2 holds Z inTARSKIR2 it iff ( ex X be setHIDDENM2 st  ex Y be setHIDDENM2 st (X inTARSKIR2 SFX & Y inTARSKIR2 SFY) & Z =XBOOLE-0R4 X \\SUBSET-1K6 Y)"
proof-
  (*existence*)
    show " ex it be setHIDDENM2 st  for Z be setHIDDENM2 holds Z inTARSKIR2 it iff ( ex X be setHIDDENM2 st  ex Y be setHIDDENM2 st (X inTARSKIR2 SFX & Y inTARSKIR2 SFY) & Z =XBOOLE-0R4 X \\SUBSET-1K6 Y)"
sorry
  (*uniqueness*)
    show " for it1 be setHIDDENM2 holds  for it2 be setHIDDENM2 holds ( for Z be setHIDDENM2 holds Z inTARSKIR2 it1 iff ( ex X be setHIDDENM2 st  ex Y be setHIDDENM2 st (X inTARSKIR2 SFX & Y inTARSKIR2 SFY) & Z =XBOOLE-0R4 X \\SUBSET-1K6 Y)) & ( for Z be setHIDDENM2 holds Z inTARSKIR2 it2 iff ( ex X be setHIDDENM2 st  ex Y be setHIDDENM2 st (X inTARSKIR2 SFX & Y inTARSKIR2 SFY) & Z =XBOOLE-0R4 X \\SUBSET-1K6 Y)) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mtheorem setfam_1_th_20:
" for SFX be setHIDDENM2 holds SFX is-finer-thanSETFAM-1R1 UNIONSETFAM-1K2(SFX,SFX)"
sorry

mtheorem setfam_1_th_21:
" for SFX be setHIDDENM2 holds INTERSECTIONSETFAM-1K3(SFX,SFX) is-finer-thanSETFAM-1R1 SFX"
sorry

mtheorem setfam_1_th_22:
" for SFX be setHIDDENM2 holds DIFFERENCESETFAM-1K4(SFX,SFX) is-finer-thanSETFAM-1R1 SFX"
sorry

mtheorem setfam_1_th_23:
" for SFX be setHIDDENM2 holds  for SFY be setHIDDENM2 holds SFX meetsXBOOLE-0R5 SFY implies meetSETFAM-1K1 SFX /\\XBOOLE-0K3 meetSETFAM-1K1 SFY =XBOOLE-0R4 meetSETFAM-1K1 (INTERSECTIONSETFAM-1K3(SFX,SFY))"
sorry

mtheorem setfam_1_th_24:
" for X be setHIDDENM2 holds  for SFY be setHIDDENM2 holds SFY <>HIDDENR2 {}XBOOLE-0K1 implies X \\/XBOOLE-0K2 meetSETFAM-1K1 SFY =XBOOLE-0R4 meetSETFAM-1K1 (UNIONSETFAM-1K2({TARSKIK1 X},SFY))"
sorry

mtheorem setfam_1_th_25:
" for X be setHIDDENM2 holds  for SFY be setHIDDENM2 holds X /\\XBOOLE-0K3 unionTARSKIK3 SFY =XBOOLE-0R4 unionTARSKIK3 (INTERSECTIONSETFAM-1K3({TARSKIK1 X},SFY))"
sorry

mtheorem setfam_1_th_26:
" for X be setHIDDENM2 holds  for SFY be setHIDDENM2 holds SFY <>HIDDENR2 {}XBOOLE-0K1 implies X \\SUBSET-1K6 unionTARSKIK3 SFY =XBOOLE-0R4 meetSETFAM-1K1 (DIFFERENCESETFAM-1K4({TARSKIK1 X},SFY))"
sorry

mtheorem setfam_1_th_27:
" for X be setHIDDENM2 holds  for SFY be setHIDDENM2 holds SFY <>HIDDENR2 {}XBOOLE-0K1 implies X \\SUBSET-1K6 meetSETFAM-1K1 SFY =XBOOLE-0R4 unionTARSKIK3 (DIFFERENCESETFAM-1K4({TARSKIK1 X},SFY))"
sorry

mtheorem setfam_1_th_28:
" for SFX be setHIDDENM2 holds  for SFY be setHIDDENM2 holds unionTARSKIK3 (INTERSECTIONSETFAM-1K3(SFX,SFY)) =XBOOLE-0R4 unionTARSKIK3 SFX /\\XBOOLE-0K3 unionTARSKIK3 SFY"
sorry

mtheorem setfam_1_th_29:
" for SFX be setHIDDENM2 holds  for SFY be setHIDDENM2 holds SFX <>HIDDENR2 {}XBOOLE-0K1 & SFY <>HIDDENR2 {}XBOOLE-0K1 implies meetSETFAM-1K1 SFX \\/XBOOLE-0K2 meetSETFAM-1K1 SFY c=TARSKIR1 meetSETFAM-1K1 (UNIONSETFAM-1K2(SFX,SFY))"
sorry

mtheorem setfam_1_th_30:
" for SFX be setHIDDENM2 holds  for SFY be setHIDDENM2 holds meetSETFAM-1K1 (DIFFERENCESETFAM-1K4(SFX,SFY)) c=TARSKIR1 meetSETFAM-1K1 SFX \\SUBSET-1K6 meetSETFAM-1K1 SFY"
sorry

abbreviation(input) SETFAM_1M1("Subset-FamilySETFAM-1M1-of  _ " [70]70) where
  "Subset-FamilySETFAM-1M1-of D \<equiv> SubsetSUBSET-1M2-of boolZFMISC-1K1 D"

reserve F, G for "Subset-FamilySETFAM-1M1-of D"
reserve P for "SubsetSUBSET-1M2-of D"
syntax SETFAM_1K5 :: " Set \<Rightarrow>  Set \<Rightarrow> Set" ("unionSETFAM-1K5\<^bsub>'( _ ')\<^esub>  _ " [0,228]228)
translations "unionSETFAM-1K5\<^bsub>(D)\<^esub> F" \<rightharpoonup> "unionTARSKIK3 F"

mtheorem setfam_1_add_1:
  mlet "D be setHIDDENM2", "F be Subset-FamilySETFAM-1M1-of D"
"cluster unionTARSKIK3 F as-term-is SubsetSUBSET-1M2-of D"
proof
(*coherence*)
  show "unionTARSKIK3 F be SubsetSUBSET-1M2-of D"
sorry
qed "sorry"

syntax SETFAM_1K6 :: " Set \<Rightarrow>  Set \<Rightarrow> Set" ("meetSETFAM-1K6\<^bsub>'( _ ')\<^esub>  _ " [0,228]228)
translations "meetSETFAM-1K6\<^bsub>(D)\<^esub> F" \<rightharpoonup> "meetSETFAM-1K1 F"

mtheorem setfam_1_add_2:
  mlet "D be setHIDDENM2", "F be Subset-FamilySETFAM-1M1-of D"
"cluster meetSETFAM-1K1 F as-term-is SubsetSUBSET-1M2-of D"
proof
(*coherence*)
  show "meetSETFAM-1K1 F be SubsetSUBSET-1M2-of D"
sorry
qed "sorry"

mtheorem setfam_1_th_31:
" for D be setHIDDENM2 holds  for F be Subset-FamilySETFAM-1M1-of D holds  for G be Subset-FamilySETFAM-1M1-of D holds ( for P be SubsetSUBSET-1M2-of D holds P inTARSKIR2 F iff P inTARSKIR2 G) implies F =XBOOLE-0R4 G"
sorry

mdef setfam_1_def_7 ("COMPLEMENTSETFAM-1K7\<^bsub>'( _ ')\<^esub>  _ " [0,164]164 ) where
  mlet "D be setHIDDENM2", "F be Subset-FamilySETFAM-1M1-of D"
"func COMPLEMENTSETFAM-1K7\<^bsub>(D)\<^esub> F \<rightarrow> Subset-FamilySETFAM-1M1-of D means
  \<lambda>it.  for P be SubsetSUBSET-1M2-of D holds P inTARSKIR2 it iff P `SUBSET-1K3\<^bsub>(D)\<^esub> inTARSKIR2 F"
proof-
  (*existence*)
    show " ex it be Subset-FamilySETFAM-1M1-of D st  for P be SubsetSUBSET-1M2-of D holds P inTARSKIR2 it iff P `SUBSET-1K3\<^bsub>(D)\<^esub> inTARSKIR2 F"
sorry
  (*uniqueness*)
    show " for it1 be Subset-FamilySETFAM-1M1-of D holds  for it2 be Subset-FamilySETFAM-1M1-of D holds ( for P be SubsetSUBSET-1M2-of D holds P inTARSKIR2 it1 iff P `SUBSET-1K3\<^bsub>(D)\<^esub> inTARSKIR2 F) & ( for P be SubsetSUBSET-1M2-of D holds P inTARSKIR2 it2 iff P `SUBSET-1K3\<^bsub>(D)\<^esub> inTARSKIR2 F) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mtheorem SETFAM_1K7_involutiveness:
  mlet "D be setHIDDENM2"
" for F be Subset-FamilySETFAM-1M1-of D holds COMPLEMENTSETFAM-1K7\<^bsub>(D)\<^esub> (COMPLEMENTSETFAM-1K7\<^bsub>(D)\<^esub> F) =HIDDENR1 F"
sorry

mtheorem setfam_1_th_32:
" for D be setHIDDENM2 holds  for F be Subset-FamilySETFAM-1M1-of D holds F <>HIDDENR2 {}XBOOLE-0K1 implies COMPLEMENTSETFAM-1K7\<^bsub>(D)\<^esub> F <>HIDDENR2 {}XBOOLE-0K1"
sorry

mtheorem setfam_1_th_33:
" for D be setHIDDENM2 holds  for F be Subset-FamilySETFAM-1M1-of D holds F <>HIDDENR2 {}XBOOLE-0K1 implies [#]SUBSET-1K2 D \\SUBSET-1K7\<^bsub>(D)\<^esub> unionSETFAM-1K5\<^bsub>(D)\<^esub> F =XBOOLE-0R4 meetSETFAM-1K6\<^bsub>(D)\<^esub> (COMPLEMENTSETFAM-1K7\<^bsub>(D)\<^esub> F)"
sorry

mtheorem setfam_1_th_34:
" for D be setHIDDENM2 holds  for F be Subset-FamilySETFAM-1M1-of D holds F <>HIDDENR2 {}XBOOLE-0K1 implies unionSETFAM-1K5\<^bsub>(D)\<^esub> (COMPLEMENTSETFAM-1K7\<^bsub>(D)\<^esub> F) =XBOOLE-0R4 [#]SUBSET-1K2 D \\SUBSET-1K7\<^bsub>(D)\<^esub> meetSETFAM-1K6\<^bsub>(D)\<^esub> F"
sorry

(*begin*)
mtheorem setfam_1_th_35:
" for X be setHIDDENM2 holds  for F be Subset-FamilySETFAM-1M1-of X holds  for P be SubsetSUBSET-1M2-of X holds P `SUBSET-1K3\<^bsub>(X)\<^esub> inTARSKIR2 COMPLEMENTSETFAM-1K7\<^bsub>(X)\<^esub> F iff P inTARSKIR2 F"
sorry

mtheorem setfam_1_th_36:
" for X be setHIDDENM2 holds  for F be Subset-FamilySETFAM-1M1-of X holds  for G be Subset-FamilySETFAM-1M1-of X holds COMPLEMENTSETFAM-1K7\<^bsub>(X)\<^esub> F c=TARSKIR1 COMPLEMENTSETFAM-1K7\<^bsub>(X)\<^esub> G implies F c=TARSKIR1 G"
sorry

mtheorem setfam_1_th_37:
" for X be setHIDDENM2 holds  for F be Subset-FamilySETFAM-1M1-of X holds  for G be Subset-FamilySETFAM-1M1-of X holds COMPLEMENTSETFAM-1K7\<^bsub>(X)\<^esub> F c=TARSKIR1 G iff F c=TARSKIR1 COMPLEMENTSETFAM-1K7\<^bsub>(X)\<^esub> G"
sorry

mtheorem setfam_1_th_38:
" for X be setHIDDENM2 holds  for F be Subset-FamilySETFAM-1M1-of X holds  for G be Subset-FamilySETFAM-1M1-of X holds COMPLEMENTSETFAM-1K7\<^bsub>(X)\<^esub> F =XBOOLE-0R4 COMPLEMENTSETFAM-1K7\<^bsub>(X)\<^esub> G implies F =XBOOLE-0R4 G"
sorry

mtheorem setfam_1_th_39:
" for X be setHIDDENM2 holds  for F be Subset-FamilySETFAM-1M1-of X holds  for G be Subset-FamilySETFAM-1M1-of X holds COMPLEMENTSETFAM-1K7\<^bsub>(X)\<^esub> (F \\/SUBSET-1K4\<^bsub>(boolZFMISC-1K1 X)\<^esub> G) =XBOOLE-0R4 COMPLEMENTSETFAM-1K7\<^bsub>(X)\<^esub> F \\/SUBSET-1K4\<^bsub>(boolZFMISC-1K1 X)\<^esub> COMPLEMENTSETFAM-1K7\<^bsub>(X)\<^esub> G"
sorry

mtheorem setfam_1_th_40:
" for X be setHIDDENM2 holds  for F be Subset-FamilySETFAM-1M1-of X holds F =XBOOLE-0R4 {TARSKIK1 X} implies COMPLEMENTSETFAM-1K7\<^bsub>(X)\<^esub> F =XBOOLE-0R4 {TARSKIK1 {}XBOOLE-0K1 }"
sorry

mtheorem setfam_1_cl_1:
  mlet "X be setHIDDENM2", "F be emptyXBOOLE-0V1\<bar>Subset-FamilySETFAM-1M1-of X"
"cluster COMPLEMENTSETFAM-1K7\<^bsub>(X)\<^esub> F as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "COMPLEMENTSETFAM-1K7\<^bsub>(X)\<^esub> F be emptyXBOOLE-0V1"
    using setfam_1_def_7 sorry
qed "sorry"

mdef setfam_1_def_8 ("with-non-empty-elementsSETFAM-1V1" 70 ) where
"attr with-non-empty-elementsSETFAM-1V1 for setHIDDENM2 means
  (\<lambda>IT.  not {}XBOOLE-0K1 inTARSKIR2 IT)"..

mtheorem setfam_1_cl_2:
"cluster  non emptyXBOOLE-0V1\<bar>with-non-empty-elementsSETFAM-1V1 for setHIDDENM2"
proof
(*existence*)
  show " ex it be setHIDDENM2 st it be  non emptyXBOOLE-0V1\<bar>with-non-empty-elementsSETFAM-1V1"
sorry
qed "sorry"

mtheorem setfam_1_cl_3:
  mlet "A be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster {TARSKIK1 A} as-term-is with-non-empty-elementsSETFAM-1V1"
proof
(*coherence*)
  show "{TARSKIK1 A} be with-non-empty-elementsSETFAM-1V1"
    using tarski_def_1 sorry
qed "sorry"

mtheorem setfam_1_cl_4:
  mlet "A be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "B be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster {TARSKIK2 A,B } as-term-is with-non-empty-elementsSETFAM-1V1"
proof
(*coherence*)
  show "{TARSKIK2 A,B } be with-non-empty-elementsSETFAM-1V1"
    using tarski_def_2 sorry
qed "sorry"

mtheorem setfam_1_cl_5:
  mlet "A be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "B be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster {ENUMSET1K1 A,B,C } as-term-is with-non-empty-elementsSETFAM-1V1"
proof
(*coherence*)
  show "{ENUMSET1K1 A,B,C } be with-non-empty-elementsSETFAM-1V1"
    using enumset1_def_1 sorry
qed "sorry"

mtheorem setfam_1_cl_6:
  mlet "A be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "B be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster {ENUMSET1K2 A,B,C,D } as-term-is with-non-empty-elementsSETFAM-1V1"
proof
(*coherence*)
  show "{ENUMSET1K2 A,B,C,D } be with-non-empty-elementsSETFAM-1V1"
    using enumset1_def_2 sorry
qed "sorry"

mtheorem setfam_1_cl_7:
  mlet "A be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "B be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "E be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster {ENUMSET1K3 A,B,C,D,E } as-term-is with-non-empty-elementsSETFAM-1V1"
proof
(*coherence*)
  show "{ENUMSET1K3 A,B,C,D,E } be with-non-empty-elementsSETFAM-1V1"
    using enumset1_def_3 sorry
qed "sorry"

mtheorem setfam_1_cl_8:
  mlet "A be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "B be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "E be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "F be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster {ENUMSET1K4 A,B,C,D,E,F } as-term-is with-non-empty-elementsSETFAM-1V1"
proof
(*coherence*)
  show "{ENUMSET1K4 A,B,C,D,E,F } be with-non-empty-elementsSETFAM-1V1"
    using enumset1_def_4 sorry
qed "sorry"

mtheorem setfam_1_cl_9:
  mlet "A be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "B be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "E be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "F be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "G be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster {ENUMSET1K5 A,B,C,D,E,F,G } as-term-is with-non-empty-elementsSETFAM-1V1"
proof
(*coherence*)
  show "{ENUMSET1K5 A,B,C,D,E,F,G } be with-non-empty-elementsSETFAM-1V1"
    using enumset1_def_5 sorry
qed "sorry"

mtheorem setfam_1_cl_10:
  mlet "A be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "B be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "E be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "F be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "G be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "H be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster {ENUMSET1K6 A,B,C,D,E,F,G,H } as-term-is with-non-empty-elementsSETFAM-1V1"
proof
(*coherence*)
  show "{ENUMSET1K6 A,B,C,D,E,F,G,H } be with-non-empty-elementsSETFAM-1V1"
    using enumset1_def_6 sorry
qed "sorry"

mtheorem setfam_1_cl_11:
  mlet "A be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "B be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "E be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "F be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "G be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "H be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "I be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster {ENUMSET1K7 A,B,C,D,E,F,G,H,I } as-term-is with-non-empty-elementsSETFAM-1V1"
proof
(*coherence*)
  show "{ENUMSET1K7 A,B,C,D,E,F,G,H,I } be with-non-empty-elementsSETFAM-1V1"
    using enumset1_def_7 sorry
qed "sorry"

mtheorem setfam_1_cl_12:
  mlet "A be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "B be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "E be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "F be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "G be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "H be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "I be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "J be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster {ENUMSET1K8 A,B,C,D,E,F,G,H,I,J } as-term-is with-non-empty-elementsSETFAM-1V1"
proof
(*coherence*)
  show "{ENUMSET1K8 A,B,C,D,E,F,G,H,I,J } be with-non-empty-elementsSETFAM-1V1"
    using enumset1_def_8 sorry
qed "sorry"

mtheorem setfam_1_cl_13:
  mlet "A be with-non-empty-elementsSETFAM-1V1\<bar>setHIDDENM2", "B be with-non-empty-elementsSETFAM-1V1\<bar>setHIDDENM2"
"cluster A \\/XBOOLE-0K2 B as-term-is with-non-empty-elementsSETFAM-1V1"
proof
(*coherence*)
  show "A \\/XBOOLE-0K2 B be with-non-empty-elementsSETFAM-1V1"
sorry
qed "sorry"

mtheorem setfam_1_th_41:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds unionTARSKIK3 Y c=TARSKIR1 Z & X inTARSKIR2 Y implies X c=TARSKIR1 Z"
sorry

mtheorem setfam_1_th_42:
" for A be setHIDDENM2 holds  for B be setHIDDENM2 holds  for X be setHIDDENM2 holds X c=TARSKIR1 unionTARSKIK3 (A \\/XBOOLE-0K2 B) & ( for Y be setHIDDENM2 holds Y inTARSKIR2 B implies Y missesXBOOLE-0R1 X) implies X c=TARSKIR1 unionTARSKIK3 A"
sorry

mdef setfam_1_def_9 ("IntersectSETFAM-1K8\<^bsub>'( _ ')\<^esub>  _ " [0,164]164 ) where
  mlet "M be setHIDDENM2", "B be Subset-FamilySETFAM-1M1-of M"
"func IntersectSETFAM-1K8\<^bsub>(M)\<^esub> B \<rightarrow> SubsetSUBSET-1M2-of M equals
  meetSETFAM-1K6\<^bsub>(M)\<^esub> B if B <>HIDDENR2 {}XBOOLE-0K1 otherwise M"
proof-
  (*coherence*)
    show "(B <>HIDDENR2 {}XBOOLE-0K1 implies meetSETFAM-1K6\<^bsub>(M)\<^esub> B be SubsetSUBSET-1M2-of M) & ( not B <>HIDDENR2 {}XBOOLE-0K1 implies M be SubsetSUBSET-1M2-of M)"
sorry
  (*consistency*)
    show " for it be SubsetSUBSET-1M2-of M holds  True "
       sorry
qed "sorry"

mtheorem setfam_1_th_43:
" for X be setHIDDENM2 holds  for x be setHIDDENM2 holds  for R be Subset-FamilySETFAM-1M1-of X holds x inTARSKIR2 X implies (x inTARSKIR2 IntersectSETFAM-1K8\<^bsub>(X)\<^esub> R iff ( for Y be setHIDDENM2 holds Y inTARSKIR2 R implies x inTARSKIR2 Y))"
sorry

mtheorem setfam_1_th_44:
" for X be setHIDDENM2 holds  for H be Subset-FamilySETFAM-1M1-of X holds  for J be Subset-FamilySETFAM-1M1-of X holds H c=TARSKIR1 J implies IntersectSETFAM-1K8\<^bsub>(X)\<^esub> J c=TARSKIR1 IntersectSETFAM-1K8\<^bsub>(X)\<^esub> H"
sorry

mtheorem setfam_1_cl_14:
  mlet "X be  non emptyXBOOLE-0V1\<bar>with-non-empty-elementsSETFAM-1V1\<bar>setHIDDENM2"
"cluster note-that  non emptyXBOOLE-0V1 for ElementSUBSET-1M1-of X"
proof
(*coherence*)
  show " for it be ElementSUBSET-1M1-of X holds it be  non emptyXBOOLE-0V1"
    using setfam_1_def_8 sorry
qed "sorry"

reserve E for "setHIDDENM2"
mdef setfam_1_def_10 ("empty-memberedSETFAM-1V2" 70 ) where
"attr empty-memberedSETFAM-1V2 for setHIDDENM2 means
  (\<lambda>E.  not ( ex x be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 st x inTARSKIR2 E))"..

syntax SETFAM_1V3 :: "Ty" ("with-non-empty-elementSETFAM-1V3" 70)
translations "with-non-empty-elementSETFAM-1V3" \<rightharpoonup> " non empty-memberedSETFAM-1V2"

mtheorem setfam_1_cl_15:
"cluster with-non-empty-elementSETFAM-1V3 for setHIDDENM2"
proof
(*existence*)
  show " ex it be setHIDDENM2 st it be with-non-empty-elementSETFAM-1V3"
sorry
qed "sorry"

mtheorem setfam_1_cl_16:
"cluster with-non-empty-elementSETFAM-1V3 also-is  non emptyXBOOLE-0V1 for setHIDDENM2"
proof
(*coherence*)
  show " for it be setHIDDENM2 holds it be with-non-empty-elementSETFAM-1V3 implies it be  non emptyXBOOLE-0V1"
     sorry
qed "sorry"

mtheorem setfam_1_cl_17:
  mlet "X be with-non-empty-elementSETFAM-1V3\<bar>setHIDDENM2"
"cluster  non emptyXBOOLE-0V1 for ElementSUBSET-1M1-of X"
proof
(*existence*)
  show " ex it be ElementSUBSET-1M1-of X st it be  non emptyXBOOLE-0V1"
sorry
qed "sorry"

mtheorem setfam_1_cl_18:
  mlet "D be  non emptyXBOOLE-0V1\<bar>with-non-empty-elementsSETFAM-1V1\<bar>setHIDDENM2"
"cluster unionTARSKIK3 D as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "unionTARSKIK3 D be  non emptyXBOOLE-0V1"
sorry
qed "sorry"

mtheorem setfam_1_cl_19:
"cluster  non emptyXBOOLE-0V1\<bar>with-non-empty-elementsSETFAM-1V1 also-is with-non-empty-elementSETFAM-1V3 for setHIDDENM2"
proof
(*coherence*)
  show " for it be setHIDDENM2 holds it be  non emptyXBOOLE-0V1\<bar>with-non-empty-elementsSETFAM-1V1 implies it be with-non-empty-elementSETFAM-1V3"
     sorry
qed "sorry"

mdef setfam_1_def_11 ("CoverSETFAM-1M2-of  _ " [70]70 ) where
  mlet "X be setHIDDENM2"
"mode CoverSETFAM-1M2-of X \<rightarrow> setHIDDENM2 means
  (\<lambda>it. X c=TARSKIR1 unionTARSKIK3 it)"
proof-
  (*existence*)
    show " ex it be setHIDDENM2 st X c=TARSKIR1 unionTARSKIK3 it"
sorry
qed "sorry"

mtheorem setfam_1_th_45:
" for X be setHIDDENM2 holds  for F be Subset-FamilySETFAM-1M1-of X holds F be CoverSETFAM-1M2-of X iff unionSETFAM-1K5\<^bsub>(X)\<^esub> F =XBOOLE-0R4 X"
  using setfam_1_def_11 sorry

mtheorem setfam_1_th_46:
" for X be setHIDDENM2 holds {TARSKIK1 {}XBOOLE-0K1 } be Subset-FamilySETFAM-1M1-of X"
sorry

mdef setfam_1_def_12 ("with-proper-subsetsSETFAM-1V4\<^bsub>'( _ ')\<^esub>" [0]70 ) where
  mlet "X be setHIDDENM2"
"attr with-proper-subsetsSETFAM-1V4\<^bsub>(X)\<^esub> for Subset-FamilySETFAM-1M1-of X means
  (\<lambda>F.  not X inTARSKIR2 F)"..

mtheorem setfam_1_th_47:
" for TS be setHIDDENM2 holds  for F be Subset-FamilySETFAM-1M1-of TS holds  for G be Subset-FamilySETFAM-1M1-of TS holds F be with-proper-subsetsSETFAM-1V4\<^bsub>(TS)\<^esub> & G c=TARSKIR1 F implies G be with-proper-subsetsSETFAM-1V4\<^bsub>(TS)\<^esub>"
   sorry

mtheorem setfam_1_cl_20:
  mlet "TS be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster with-proper-subsetsSETFAM-1V4\<^bsub>(TS)\<^esub> for Subset-FamilySETFAM-1M1-of TS"
proof
(*existence*)
  show " ex it be Subset-FamilySETFAM-1M1-of TS st it be with-proper-subsetsSETFAM-1V4\<^bsub>(TS)\<^esub>"
sorry
qed "sorry"

mtheorem setfam_1_th_48:
" for TS be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for A be with-proper-subsetsSETFAM-1V4\<^bsub>(TS)\<^esub>\<bar>Subset-FamilySETFAM-1M1-of TS holds  for B be with-proper-subsetsSETFAM-1V4\<^bsub>(TS)\<^esub>\<bar>Subset-FamilySETFAM-1M1-of TS holds A \\/SUBSET-1K4\<^bsub>(boolZFMISC-1K1 TS)\<^esub> B be with-proper-subsetsSETFAM-1V4\<^bsub>(TS)\<^esub>"
sorry

mtheorem setfam_1_cl_21:
"cluster  non trivialSUBSET-1V2 also-is with-non-empty-elementSETFAM-1V3 for setHIDDENM2"
proof
(*coherence*)
  show " for it be setHIDDENM2 holds it be  non trivialSUBSET-1V2 implies it be with-non-empty-elementSETFAM-1V3"
sorry
qed "sorry"

abbreviation(input) SETFAM_1K9("boolSETFAM-1K9  _ " [228]228) where
  "boolSETFAM-1K9 X \<equiv> boolZFMISC-1K1 X"

mtheorem setfam_1_add_3:
  mlet "X be setHIDDENM2"
"cluster boolZFMISC-1K1 X as-term-is Subset-FamilySETFAM-1M1-of X"
proof
(*coherence*)
  show "boolZFMISC-1K1 X be Subset-FamilySETFAM-1M1-of X"
    using zfmisc_1_def_1 sorry
qed "sorry"

mtheorem setfam_1_th_49:
" for A be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for b be objectHIDDENM1 holds A <>HIDDENR2 {TARSKIK1 b} implies ( ex a be ElementSUBSET-1M1-of A st a <>HIDDENR2 b)"
sorry

end
