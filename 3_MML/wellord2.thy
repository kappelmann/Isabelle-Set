theory wellord2
  imports mcart_1 wellord1 ordinal1
begin
(*begin*)
reserve X, Y, Z for "setHIDDENM2"
reserve a, b, c, d, x, y, z, u for "objectHIDDENM1"
reserve R for "RelationRELAT-1M1"
reserve A, B, C for "OrdinalORDINAL1M3"
mdef wellord2_def_1 ("RelInclWELLORD2K1  _ " [228]228 ) where
  mlet "X be setHIDDENM2"
"func RelInclWELLORD2K1 X \<rightarrow> RelationRELAT-1M1 means
  \<lambda>it. fieldRELAT-1K3 it =XBOOLE-0R4 X & ( for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds Y inTARSKIR2 X & Z inTARSKIR2 X implies ([TARSKIK4 Y,Z ] inHIDDENR3 it iff Y c=TARSKIR1 Z))"
proof-
  (*existence*)
    show " ex it be RelationRELAT-1M1 st fieldRELAT-1K3 it =XBOOLE-0R4 X & ( for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds Y inTARSKIR2 X & Z inTARSKIR2 X implies ([TARSKIK4 Y,Z ] inHIDDENR3 it iff Y c=TARSKIR1 Z))"
sorry
  (*uniqueness*)
    show " for it1 be RelationRELAT-1M1 holds  for it2 be RelationRELAT-1M1 holds (fieldRELAT-1K3 it1 =XBOOLE-0R4 X & ( for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds Y inTARSKIR2 X & Z inTARSKIR2 X implies ([TARSKIK4 Y,Z ] inHIDDENR3 it1 iff Y c=TARSKIR1 Z))) & (fieldRELAT-1K3 it2 =XBOOLE-0R4 X & ( for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds Y inTARSKIR2 X & Z inTARSKIR2 X implies ([TARSKIK4 Y,Z ] inHIDDENR3 it2 iff Y c=TARSKIR1 Z))) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

(*\$CT 6*)
mtheorem wellord2_cl_1:
  mlet "X be setHIDDENM2"
"cluster RelInclWELLORD2K1 X as-term-is reflexiveRELAT-2V1"
proof
(*coherence*)
  show "RelInclWELLORD2K1 X be reflexiveRELAT-2V1"
sorry
qed "sorry"

mtheorem wellord2_cl_2:
  mlet "X be setHIDDENM2"
"cluster RelInclWELLORD2K1 X as-term-is transitiveRELAT-2V8"
proof
(*coherence*)
  show "RelInclWELLORD2K1 X be transitiveRELAT-2V8"
sorry
qed "sorry"

mtheorem wellord2_cl_3:
  mlet "X be setHIDDENM2"
"cluster RelInclWELLORD2K1 X as-term-is antisymmetricRELAT-2V4"
proof
(*coherence*)
  show "RelInclWELLORD2K1 X be antisymmetricRELAT-2V4"
sorry
qed "sorry"

mtheorem wellord2_cl_4:
  mlet "A be OrdinalORDINAL1M3"
"cluster RelInclWELLORD2K1 A as-term-is connectedRELAT-2V6"
proof
(*coherence*)
  show "RelInclWELLORD2K1 A be connectedRELAT-2V6"
sorry
qed "sorry"

mtheorem wellord2_cl_5:
  mlet "A be OrdinalORDINAL1M3"
"cluster RelInclWELLORD2K1 A as-term-is well-foundedWELLORD1V1"
proof
(*coherence*)
  show "RelInclWELLORD2K1 A be well-foundedWELLORD1V1"
sorry
qed "sorry"

mtheorem wellord2_th_7:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds Y c=TARSKIR1 X implies RelInclWELLORD2K1 X |-2WELLORD1K2 Y =RELAT-1R1 RelInclWELLORD2K1 Y"
sorry

mtheorem wellord2_th_8:
" for A be OrdinalORDINAL1M3 holds  for X be setHIDDENM2 holds X c=TARSKIR1 A implies RelInclWELLORD2K1 X be well-orderingWELLORD1V2"
sorry

reserve H for "FunctionFUNCT-1M1"
mtheorem wellord2_th_9:
" for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds A inTARSKIR2 B implies A =XBOOLE-0R4 (RelInclWELLORD2K1 B)-SegWELLORD1K1 A"
sorry

mtheorem wellord2_th_10:
" for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds (RelInclWELLORD2K1 A,RelInclWELLORD2K1 B)are-isomorphicWELLORD1R4 implies A =XBOOLE-0R4 B"
sorry

mtheorem wellord2_th_11:
" for R be RelationRELAT-1M1 holds  for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds (R,RelInclWELLORD2K1 A)are-isomorphicWELLORD1R4 & (R,RelInclWELLORD2K1 B)are-isomorphicWELLORD1R4 implies A =XBOOLE-0R4 B"
sorry

mtheorem wellord2_th_12:
" for R be RelationRELAT-1M1 holds R be well-orderingWELLORD1V2 & ( for a be objectHIDDENM1 holds a inHIDDENR3 fieldRELAT-1K3 R implies ( ex A be OrdinalORDINAL1M3 st (R |-2WELLORD1K2 R -SegWELLORD1K1 a,RelInclWELLORD2K1 A)are-isomorphicWELLORD1R4)) implies ( ex A be OrdinalORDINAL1M3 st (R,RelInclWELLORD2K1 A)are-isomorphicWELLORD1R4)"
sorry

mtheorem wellord2_th_13:
" for R be RelationRELAT-1M1 holds R be well-orderingWELLORD1V2 implies ( ex A be OrdinalORDINAL1M3 st (R,RelInclWELLORD2K1 A)are-isomorphicWELLORD1R4)"
sorry

mdef wellord2_def_2 ("order-type-ofWELLORD2K2  _ " [132]132 ) where
  mlet "R be RelationRELAT-1M1"
"assume R be well-orderingWELLORD1V2 func order-type-ofWELLORD2K2 R \<rightarrow> OrdinalORDINAL1M3 means
  \<lambda>it. (R,RelInclWELLORD2K1 it)are-isomorphicWELLORD1R4"
proof-
  (*existence*)
    show "R be well-orderingWELLORD1V2 implies ( ex it be OrdinalORDINAL1M3 st (R,RelInclWELLORD2K1 it)are-isomorphicWELLORD1R4)"
sorry
  (*uniqueness*)
    show "R be well-orderingWELLORD1V2 implies ( for it1 be OrdinalORDINAL1M3 holds  for it2 be OrdinalORDINAL1M3 holds (R,RelInclWELLORD2K1 it1)are-isomorphicWELLORD1R4 & (R,RelInclWELLORD2K1 it2)are-isomorphicWELLORD1R4 implies it1 =HIDDENR1 it2)"
sorry
qed "sorry"

mdef wellord2_def_3 (" _ is-order-type-ofWELLORD2R1  _ " [50,50]50 ) where
  mlet "A be OrdinalORDINAL1M3", "R be RelationRELAT-1M1"
"pred A is-order-type-ofWELLORD2R1 R means
  A =XBOOLE-0R4 order-type-ofWELLORD2K2 R"..

mtheorem wellord2_th_14:
" for X be setHIDDENM2 holds  for A be OrdinalORDINAL1M3 holds X c=TARSKIR1 A implies order-type-ofWELLORD2K2 RelInclWELLORD2K1 X c=ORDINAL1R1 A"
sorry

reserve f, g for "FunctionFUNCT-1M1"
abbreviation(input) WELLORD2R2("'( _ , _ ')are-equipotentWELLORD2R2" [0,0]50) where
  "(X,Y)are-equipotentWELLORD2R2 \<equiv> (X,Y)are-equipotentTARSKIR3"

mtheorem wellord2_def_4:
  mlet "X be setHIDDENM2", "Y be setHIDDENM2"
"redefine pred (X,Y)are-equipotentWELLORD2R2 means
   ex f be FunctionFUNCT-1M1 st (f be one-to-oneFUNCT-1V2 & domRELAT-1K1 f =XBOOLE-0R4 X) & rngFUNCT-1K2 f =XBOOLE-0R4 Y"
proof
(*compatibility*)
  show "(X,Y)are-equipotentWELLORD2R2 iff ( ex f be FunctionFUNCT-1M1 st (f be one-to-oneFUNCT-1V2 & domRELAT-1K1 f =XBOOLE-0R4 X) & rngFUNCT-1K2 f =XBOOLE-0R4 Y)"
sorry
qed "sorry"

mtheorem WELLORD2R2_reflexivity:
" for Y be setHIDDENM2 holds (Y,Y)are-equipotentWELLORD2R2"
sorry

mtheorem WELLORD2R2_symmetry:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds (X,Y)are-equipotentWELLORD2R2 implies (Y,X)are-equipotentWELLORD2R2"
sorry

mtheorem wellord2_th_15:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds (X,Y)are-equipotentWELLORD2R2 & (Y,Z)are-equipotentWELLORD2R2 implies (X,Z)are-equipotentWELLORD2R2"
sorry

mtheorem wellord2_th_16:
" for X be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds R well-ordersWELLORD1R2 X implies fieldRELAT-1K3 (R |-2WELLORD1K2 X) =XBOOLE-0R4 X & R |-2WELLORD1K2 X be well-orderingWELLORD1V2"
sorry

mlemma wellord2_lm_1:
" for X be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds R be well-orderingWELLORD1V2 & (X,fieldRELAT-1K3 R)are-equipotentWELLORD2R2 implies ( ex R be RelationRELAT-1M1 st R well-ordersWELLORD1R2 X)"
sorry

(*\$N Zermelo Theorem*)
mtheorem wellord2_th_17:
" for X be setHIDDENM2 holds  ex R be RelationRELAT-1M1 st R well-ordersWELLORD1R2 X"
sorry

reserve M for " non emptyXBOOLE-0V1\<bar>setHIDDENM2"
(*\$N Axiom of Choice*)
mtheorem wellord2_th_18:
" for M be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds ( for X be setHIDDENM2 holds X inTARSKIR2 M implies X <>HIDDENR2 {}XBOOLE-0K1) & ( for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds (X inTARSKIR2 M & Y inTARSKIR2 M) & X <>HIDDENR2 Y implies X missesXBOOLE-0R1 Y) implies ( ex Choice be setHIDDENM2 st  for X be setHIDDENM2 holds X inTARSKIR2 M implies ( ex x be objectHIDDENM1 st Choice /\\XBOOLE-0K3 X =XBOOLE-0R4 {TARSKIK1 x}))"
sorry

(*begin*)
mtheorem wellord2_th_19:
" for X be setHIDDENM2 holds RelInclWELLORD2K1 X is-reflexive-inRELAT-2R1 X"
  using wellord2_def_1 sorry

mtheorem wellord2_th_20:
" for X be setHIDDENM2 holds RelInclWELLORD2K1 X is-transitive-inRELAT-2R8 X"
sorry

mtheorem wellord2_th_21:
" for X be setHIDDENM2 holds RelInclWELLORD2K1 X is-antisymmetric-inRELAT-2R4 X"
sorry

mtheorem wellord2_cl_6:
"cluster RelInclWELLORD2K1 ({}XBOOLE-0K1) as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "RelInclWELLORD2K1 ({}XBOOLE-0K1) be emptyXBOOLE-0V1"
sorry
qed "sorry"

mtheorem wellord2_cl_7:
  mlet "X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster RelInclWELLORD2K1 X as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "RelInclWELLORD2K1 X be  non emptyXBOOLE-0V1"
sorry
qed "sorry"

mtheorem wellord2_th_22:
" for x be objectHIDDENM1 holds RelInclWELLORD2K1 {TARSKIK1 x} =RELAT-1R1 {TARSKIK1 [TARSKIK4 x,x ] }"
sorry

mtheorem wellord2_th_23:
" for X be setHIDDENM2 holds RelInclWELLORD2K1 X c=RELAT-1R2 [:ZFMISC-1K2 X,X :]"
sorry

end
