theory wellord1
  imports relat_2 funct_1
begin
(*begin*)
reserve a, b, c, d, x, y, z for "objectHIDDENM1"
reserve X, Y, Z for "setHIDDENM2"
reserve R, S, T for "RelationRELAT-1M1"
mlemma wellord1_lm_1:
" for R be RelationRELAT-1M1 holds R be reflexiveRELAT-2V1 iff ( for x be objectHIDDENM1 holds x inHIDDENR3 fieldRELAT-1K3 R implies [TARSKIK4 x,x ] inHIDDENR3 R)"
  using relat_2_def_1 relat_2_def_9 sorry

mlemma wellord1_lm_2:
" for R be RelationRELAT-1M1 holds R be transitiveRELAT-2V8 iff ( for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for z be objectHIDDENM1 holds [TARSKIK4 x,y ] inHIDDENR3 R & [TARSKIK4 y,z ] inHIDDENR3 R implies [TARSKIK4 x,z ] inHIDDENR3 R)"
sorry

mlemma wellord1_lm_3:
" for R be RelationRELAT-1M1 holds R be antisymmetricRELAT-2V4 iff ( for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds [TARSKIK4 x,y ] inHIDDENR3 R & [TARSKIK4 y,x ] inHIDDENR3 R implies x =HIDDENR1 y)"
sorry

mlemma wellord1_lm_4:
" for R be RelationRELAT-1M1 holds R be connectedRELAT-2V6 iff ( for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds (x inHIDDENR3 fieldRELAT-1K3 R & y inHIDDENR3 fieldRELAT-1K3 R) & x <>HIDDENR2 y implies [TARSKIK4 x,y ] inHIDDENR3 R or [TARSKIK4 y,x ] inHIDDENR3 R)"
  using relat_2_def_6 relat_2_def_14 sorry

mdef wellord1_def_1 (" _ -SegWELLORD1K1  _ " [228,228]228 ) where
  mlet "R be RelationRELAT-1M1", "a be objectHIDDENM1"
"func R -SegWELLORD1K1 a \<rightarrow> setHIDDENM2 equals
  CoimRELAT-1K13(R,a) \\SUBSET-1K6 {TARSKIK1 a}"
proof-
  (*coherence*)
    show "CoimRELAT-1K13(R,a) \\SUBSET-1K6 {TARSKIK1 a} be setHIDDENM2"
       sorry
qed "sorry"

mtheorem wellord1_th_1:
" for a be objectHIDDENM1 holds  for x be objectHIDDENM1 holds  for R be RelationRELAT-1M1 holds x inHIDDENR3 R -SegWELLORD1K1 a iff x <>HIDDENR2 a & [TARSKIK4 x,a ] inHIDDENR3 R"
sorry

mtheorem wellord1_th_2:
" for x be objectHIDDENM1 holds  for R be RelationRELAT-1M1 holds x inHIDDENR3 fieldRELAT-1K3 R or R -SegWELLORD1K1 x =XBOOLE-0R4 {}XBOOLE-0K1"
sorry

mdef wellord1_def_2 ("well-foundedWELLORD1V1" 70 ) where
"attr well-foundedWELLORD1V1 for RelationRELAT-1M1 means
  (\<lambda>R.  for Y be setHIDDENM2 holds Y c=TARSKIR1 fieldRELAT-1K3 R & Y <>HIDDENR2 {}XBOOLE-0K1 implies ( ex a be objectHIDDENM1 st a inHIDDENR3 Y & R -SegWELLORD1K1 a missesXBOOLE-0R1 Y))"..

mdef wellord1_def_3 (" _ is-well-founded-inWELLORD1R1  _ " [50,50]50 ) where
  mlet "R be RelationRELAT-1M1", "X be setHIDDENM2"
"pred R is-well-founded-inWELLORD1R1 X means
   for Y be setHIDDENM2 holds Y c=TARSKIR1 X & Y <>HIDDENR2 {}XBOOLE-0K1 implies ( ex a be objectHIDDENM1 st a inHIDDENR3 Y & R -SegWELLORD1K1 a missesXBOOLE-0R1 Y)"..

mtheorem wellord1_th_3:
" for R be RelationRELAT-1M1 holds R be well-foundedWELLORD1V1 iff R is-well-founded-inWELLORD1R1 fieldRELAT-1K3 R"
   sorry

mdef wellord1_def_4 ("well-orderingWELLORD1V2" 70 ) where
"attr well-orderingWELLORD1V2 for RelationRELAT-1M1 means
  (\<lambda>R. (((R be reflexiveRELAT-2V1 & R be transitiveRELAT-2V8) & R be antisymmetricRELAT-2V4) & R be connectedRELAT-2V6) & R be well-foundedWELLORD1V1)"..

mdef wellord1_def_5 (" _ well-ordersWELLORD1R2  _ " [50,50]50 ) where
  mlet "R be RelationRELAT-1M1", "X be setHIDDENM2"
"pred R well-ordersWELLORD1R2 X means
  (((R is-reflexive-inRELAT-2R1 X & R is-transitive-inRELAT-2R8 X) & R is-antisymmetric-inRELAT-2R4 X) & R is-connected-inRELAT-2R6 X) & R is-well-founded-inWELLORD1R1 X"..

mtheorem wellord1_cl_1:
"cluster well-orderingWELLORD1V2 also-is reflexiveRELAT-2V1\<bar>transitiveRELAT-2V8\<bar>antisymmetricRELAT-2V4\<bar>connectedRELAT-2V6\<bar>well-foundedWELLORD1V1 for RelationRELAT-1M1"
proof
(*coherence*)
  show " for it be RelationRELAT-1M1 holds it be well-orderingWELLORD1V2 implies it be reflexiveRELAT-2V1\<bar>transitiveRELAT-2V8\<bar>antisymmetricRELAT-2V4\<bar>connectedRELAT-2V6\<bar>well-foundedWELLORD1V1"
     sorry
qed "sorry"

mtheorem wellord1_cl_2:
"cluster reflexiveRELAT-2V1\<bar>transitiveRELAT-2V8\<bar>antisymmetricRELAT-2V4\<bar>connectedRELAT-2V6\<bar>well-foundedWELLORD1V1 also-is well-orderingWELLORD1V2 for RelationRELAT-1M1"
proof
(*coherence*)
  show " for it be RelationRELAT-1M1 holds it be reflexiveRELAT-2V1\<bar>transitiveRELAT-2V8\<bar>antisymmetricRELAT-2V4\<bar>connectedRELAT-2V6\<bar>well-foundedWELLORD1V1 implies it be well-orderingWELLORD1V2"
     sorry
qed "sorry"

mtheorem wellord1_th_4:
" for R be RelationRELAT-1M1 holds R well-ordersWELLORD1R2 fieldRELAT-1K3 R iff R be well-orderingWELLORD1V2"
sorry

mtheorem wellord1_th_5:
" for X be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds R well-ordersWELLORD1R2 X implies ( for Y be setHIDDENM2 holds Y c=TARSKIR1 X & Y <>HIDDENR2 {}XBOOLE-0K1 implies ( ex a be objectHIDDENM1 st a inHIDDENR3 Y & ( for b be objectHIDDENM1 holds b inHIDDENR3 Y implies [TARSKIK4 a,b ] inHIDDENR3 R)))"
sorry

mtheorem wellord1_th_6:
" for R be RelationRELAT-1M1 holds R be well-orderingWELLORD1V2 implies ( for Y be setHIDDENM2 holds Y c=TARSKIR1 fieldRELAT-1K3 R & Y <>HIDDENR2 {}XBOOLE-0K1 implies ( ex a be objectHIDDENM1 st a inHIDDENR3 Y & ( for b be objectHIDDENM1 holds b inHIDDENR3 Y implies [TARSKIK4 a,b ] inHIDDENR3 R)))"
sorry

mtheorem wellord1_th_7:
" for R be RelationRELAT-1M1 holds R be well-orderingWELLORD1V2 & fieldRELAT-1K3 R <>HIDDENR2 {}XBOOLE-0K1 implies ( ex a be objectHIDDENM1 st a inHIDDENR3 fieldRELAT-1K3 R & ( for b be objectHIDDENM1 holds b inHIDDENR3 fieldRELAT-1K3 R implies [TARSKIK4 a,b ] inHIDDENR3 R))"
  using wellord1_th_6 sorry

mtheorem wellord1_th_8:
" for R be RelationRELAT-1M1 holds R be well-orderingWELLORD1V2 implies ( for a be objectHIDDENM1 holds a inHIDDENR3 fieldRELAT-1K3 R implies ( for b be objectHIDDENM1 holds b inHIDDENR3 fieldRELAT-1K3 R implies [TARSKIK4 b,a ] inHIDDENR3 R) or ( ex b be objectHIDDENM1 st (b inHIDDENR3 fieldRELAT-1K3 R & [TARSKIK4 a,b ] inHIDDENR3 R) & ( for c be objectHIDDENM1 holds c inHIDDENR3 fieldRELAT-1K3 R & [TARSKIK4 a,c ] inHIDDENR3 R implies c =HIDDENR1 a or [TARSKIK4 b,c ] inHIDDENR3 R)))"
sorry

reserve F, G for "FunctionFUNCT-1M1"
mtheorem wellord1_th_9:
" for a be objectHIDDENM1 holds  for R be RelationRELAT-1M1 holds R -SegWELLORD1K1 a c=TARSKIR1 fieldRELAT-1K3 R"
sorry

mdef wellord1_def_6 (" _ |-2WELLORD1K2  _ " [200,200]200 ) where
  mlet "R be RelationRELAT-1M1", "Y be setHIDDENM2"
"func R |-2WELLORD1K2 Y \<rightarrow> RelationRELAT-1M1 equals
  R /\\XBOOLE-0K3 ([:ZFMISC-1K2 Y,Y :])"
proof-
  (*coherence*)
    show "R /\\XBOOLE-0K3 ([:ZFMISC-1K2 Y,Y :]) be RelationRELAT-1M1"
       sorry
qed "sorry"

mtheorem wellord1_th_10:
" for X be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds R |-2WELLORD1K2 X =RELAT-1R1 (X |`RELAT-1K9 R)|RELAT-1K8 X"
sorry

mtheorem wellord1_th_11:
" for X be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds R |-2WELLORD1K2 X =RELAT-1R1 X |`RELAT-1K9 (R |RELAT-1K8 X)"
sorry

mlemma wellord1_lm_5:
" for X be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds domRELAT-1K1 (X |`RELAT-1K9 R) c=TARSKIR1 domRELAT-1K1 R"
sorry

mtheorem wellord1_th_12:
" for x be objectHIDDENM1 holds  for X be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds x inHIDDENR3 fieldRELAT-1K3 (R |-2WELLORD1K2 X) implies x inHIDDENR3 fieldRELAT-1K3 R & x inHIDDENR3 X"
sorry

mtheorem wellord1_th_13:
" for X be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds fieldRELAT-1K3 (R |-2WELLORD1K2 X) c=TARSKIR1 fieldRELAT-1K3 R & fieldRELAT-1K3 (R |-2WELLORD1K2 X) c=TARSKIR1 X"
  using wellord1_th_12 sorry

mtheorem wellord1_th_14:
" for a be objectHIDDENM1 holds  for X be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds (R |-2WELLORD1K2 X)-SegWELLORD1K1 a c=TARSKIR1 R -SegWELLORD1K1 a"
sorry

mtheorem wellord1_th_15:
" for X be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds R be reflexiveRELAT-2V1 implies R |-2WELLORD1K2 X be reflexiveRELAT-2V1"
sorry

mtheorem wellord1_th_16:
" for Y be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds R be connectedRELAT-2V6 implies R |-2WELLORD1K2 Y be connectedRELAT-2V6"
sorry

mtheorem wellord1_th_17:
" for Y be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds R be transitiveRELAT-2V8 implies R |-2WELLORD1K2 Y be transitiveRELAT-2V8"
sorry

mtheorem wellord1_th_18:
" for Y be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds R be antisymmetricRELAT-2V4 implies R |-2WELLORD1K2 Y be antisymmetricRELAT-2V4"
sorry

mtheorem wellord1_th_19:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds (R |-2WELLORD1K2 X)|-2WELLORD1K2 Y =RELAT-1R1 R |-2WELLORD1K2 (X /\\XBOOLE-0K3 Y)"
sorry

mtheorem wellord1_th_20:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds (R |-2WELLORD1K2 X)|-2WELLORD1K2 Y =RELAT-1R1 (R |-2WELLORD1K2 Y)|-2WELLORD1K2 X"
sorry

mtheorem wellord1_th_21:
" for Y be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds (R |-2WELLORD1K2 Y)|-2WELLORD1K2 Y =RELAT-1R1 R |-2WELLORD1K2 Y"
sorry

mtheorem wellord1_th_22:
" for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds Z c=TARSKIR1 Y implies (R |-2WELLORD1K2 Y)|-2WELLORD1K2 Z =RELAT-1R1 R |-2WELLORD1K2 Z"
sorry

mtheorem wellord1_th_23:
" for R be RelationRELAT-1M1 holds R |-2WELLORD1K2 fieldRELAT-1K3 R =RELAT-1R1 R"
sorry

mtheorem wellord1_th_24:
" for X be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds R be well-foundedWELLORD1V1 implies R |-2WELLORD1K2 X be well-foundedWELLORD1V1"
sorry

mtheorem wellord1_th_25:
" for Y be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds R be well-orderingWELLORD1V2 implies R |-2WELLORD1K2 Y be well-orderingWELLORD1V2"
  using wellord1_th_15 wellord1_th_16 wellord1_th_17 wellord1_th_18 wellord1_th_24 sorry

mtheorem wellord1_th_26:
" for a be objectHIDDENM1 holds  for b be objectHIDDENM1 holds  for R be RelationRELAT-1M1 holds R be well-orderingWELLORD1V2 implies (R -SegWELLORD1K1 a,R -SegWELLORD1K1 b)are-c=-comparableXBOOLE-0R3"
sorry

mtheorem wellord1_th_27:
" for a be objectHIDDENM1 holds  for b be objectHIDDENM1 holds  for R be RelationRELAT-1M1 holds R be well-orderingWELLORD1V2 & b inHIDDENR3 R -SegWELLORD1K1 a implies (R |-2WELLORD1K2 R -SegWELLORD1K1 a)-SegWELLORD1K1 b =XBOOLE-0R4 R -SegWELLORD1K1 b"
sorry

mtheorem wellord1_th_28:
" for Y be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds R be well-orderingWELLORD1V2 & Y c=TARSKIR1 fieldRELAT-1K3 R implies (Y =XBOOLE-0R4 fieldRELAT-1K3 R or ( ex a be objectHIDDENM1 st a inHIDDENR3 fieldRELAT-1K3 R & Y =XBOOLE-0R4 R -SegWELLORD1K1 a) iff ( for a be objectHIDDENM1 holds a inHIDDENR3 Y implies ( for b be objectHIDDENM1 holds [TARSKIK4 b,a ] inHIDDENR3 R implies b inHIDDENR3 Y)))"
sorry

mtheorem wellord1_th_29:
" for a be objectHIDDENM1 holds  for b be objectHIDDENM1 holds  for R be RelationRELAT-1M1 holds (R be well-orderingWELLORD1V2 & a inHIDDENR3 fieldRELAT-1K3 R) & b inHIDDENR3 fieldRELAT-1K3 R implies ([TARSKIK4 a,b ] inHIDDENR3 R iff R -SegWELLORD1K1 a c=TARSKIR1 R -SegWELLORD1K1 b)"
sorry

mtheorem wellord1_th_30:
" for a be objectHIDDENM1 holds  for b be objectHIDDENM1 holds  for R be RelationRELAT-1M1 holds (R be well-orderingWELLORD1V2 & a inHIDDENR3 fieldRELAT-1K3 R) & b inHIDDENR3 fieldRELAT-1K3 R implies (R -SegWELLORD1K1 a c=TARSKIR1 R -SegWELLORD1K1 b iff a =HIDDENR1 b or a inHIDDENR3 R -SegWELLORD1K1 b)"
sorry

mtheorem wellord1_th_31:
" for X be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds R be well-orderingWELLORD1V2 & X c=TARSKIR1 fieldRELAT-1K3 R implies fieldRELAT-1K3 (R |-2WELLORD1K2 X) =XBOOLE-0R4 X"
sorry

mtheorem wellord1_th_32:
" for a be objectHIDDENM1 holds  for R be RelationRELAT-1M1 holds R be well-orderingWELLORD1V2 implies fieldRELAT-1K3 (R |-2WELLORD1K2 R -SegWELLORD1K1 a) =XBOOLE-0R4 R -SegWELLORD1K1 a"
sorry

mtheorem wellord1_th_33:
" for R be RelationRELAT-1M1 holds R be well-orderingWELLORD1V2 implies ( for Z be setHIDDENM2 holds ( for a be objectHIDDENM1 holds a inHIDDENR3 fieldRELAT-1K3 R & R -SegWELLORD1K1 a c=TARSKIR1 Z implies a inHIDDENR3 Z) implies fieldRELAT-1K3 R c=TARSKIR1 Z)"
sorry

mtheorem wellord1_th_34:
" for a be objectHIDDENM1 holds  for b be objectHIDDENM1 holds  for R be RelationRELAT-1M1 holds ((R be well-orderingWELLORD1V2 & a inHIDDENR3 fieldRELAT-1K3 R) & b inHIDDENR3 fieldRELAT-1K3 R) & ( for c be objectHIDDENM1 holds c inHIDDENR3 R -SegWELLORD1K1 a implies [TARSKIK4 c,b ] inHIDDENR3 R & c <>HIDDENR2 b) implies [TARSKIK4 a,b ] inHIDDENR3 R"
sorry

mtheorem wellord1_th_35:
" for R be RelationRELAT-1M1 holds  for F be FunctionFUNCT-1M1 holds ((R be well-orderingWELLORD1V2 & domRELAT-1K1 F =XBOOLE-0R4 fieldRELAT-1K3 R) & rngFUNCT-1K2 F c=TARSKIR1 fieldRELAT-1K3 R) & ( for a be objectHIDDENM1 holds  for b be objectHIDDENM1 holds [TARSKIK4 a,b ] inHIDDENR3 R & a <>HIDDENR2 b implies [TARSKIK4 F .FUNCT-1K1 a,F .FUNCT-1K1 b ] inHIDDENR3 R & F .FUNCT-1K1 a <>HIDDENR2 F .FUNCT-1K1 b) implies ( for a be objectHIDDENM1 holds a inHIDDENR3 fieldRELAT-1K3 R implies [TARSKIK4 a,F .FUNCT-1K1 a ] inHIDDENR3 R)"
sorry

mdef wellord1_def_7 (" _ is-isomorphism-ofWELLORD1R3'( _ , _ ')" [50,0,0]50 ) where
  mlet "R be RelationRELAT-1M1", "S be RelationRELAT-1M1", "F be FunctionFUNCT-1M1"
"pred F is-isomorphism-ofWELLORD1R3(R,S) means
  ((domRELAT-1K1 F =XBOOLE-0R4 fieldRELAT-1K3 R & rngFUNCT-1K2 F =XBOOLE-0R4 fieldRELAT-1K3 S) & F be one-to-oneFUNCT-1V2) & ( for a be objectHIDDENM1 holds  for b be objectHIDDENM1 holds [TARSKIK4 a,b ] inHIDDENR3 R iff (a inHIDDENR3 fieldRELAT-1K3 R & b inHIDDENR3 fieldRELAT-1K3 R) & [TARSKIK4 F .FUNCT-1K1 a,F .FUNCT-1K1 b ] inHIDDENR3 S)"..

mtheorem wellord1_th_36:
" for R be RelationRELAT-1M1 holds  for S be RelationRELAT-1M1 holds  for F be FunctionFUNCT-1M1 holds F is-isomorphism-ofWELLORD1R3(R,S) implies ( for a be objectHIDDENM1 holds  for b be objectHIDDENM1 holds [TARSKIK4 a,b ] inHIDDENR3 R & a <>HIDDENR2 b implies [TARSKIK4 F .FUNCT-1K1 a,F .FUNCT-1K1 b ] inHIDDENR3 S & F .FUNCT-1K1 a <>HIDDENR2 F .FUNCT-1K1 b)"
sorry

mdef wellord1_def_8 ("'( _ , _ ')are-isomorphicWELLORD1R4" [0,0]50 ) where
  mlet "R be RelationRELAT-1M1", "S be RelationRELAT-1M1"
"pred (R,S)are-isomorphicWELLORD1R4 means
   ex F be FunctionFUNCT-1M1 st F is-isomorphism-ofWELLORD1R3(R,S)"..

mtheorem wellord1_th_37:
" for R be RelationRELAT-1M1 holds idRELAT-1K7 (fieldRELAT-1K3 R) is-isomorphism-ofWELLORD1R3(R,R)"
sorry

mtheorem wellord1_th_38:
" for R be RelationRELAT-1M1 holds (R,R)are-isomorphicWELLORD1R4"
sorry

mtheorem wellord1_th_39:
" for R be RelationRELAT-1M1 holds  for S be RelationRELAT-1M1 holds  for F be FunctionFUNCT-1M1 holds F is-isomorphism-ofWELLORD1R3(R,S) implies F \<inverse>FUNCT-1K4 is-isomorphism-ofWELLORD1R3(S,R)"
sorry

mtheorem wellord1_th_40:
" for R be RelationRELAT-1M1 holds  for S be RelationRELAT-1M1 holds (R,S)are-isomorphicWELLORD1R4 implies (S,R)are-isomorphicWELLORD1R4"
sorry

mtheorem wellord1_th_41:
" for R be RelationRELAT-1M1 holds  for S be RelationRELAT-1M1 holds  for T be RelationRELAT-1M1 holds  for F be FunctionFUNCT-1M1 holds  for G be FunctionFUNCT-1M1 holds F is-isomorphism-ofWELLORD1R3(R,S) & G is-isomorphism-ofWELLORD1R3(S,T) implies G *FUNCT-1K3 F is-isomorphism-ofWELLORD1R3(R,T)"
sorry

mtheorem wellord1_th_42:
" for R be RelationRELAT-1M1 holds  for S be RelationRELAT-1M1 holds  for T be RelationRELAT-1M1 holds (R,S)are-isomorphicWELLORD1R4 & (S,T)are-isomorphicWELLORD1R4 implies (R,T)are-isomorphicWELLORD1R4"
sorry

mtheorem wellord1_th_43:
" for R be RelationRELAT-1M1 holds  for S be RelationRELAT-1M1 holds  for F be FunctionFUNCT-1M1 holds F is-isomorphism-ofWELLORD1R3(R,S) implies ((((R be reflexiveRELAT-2V1 implies S be reflexiveRELAT-2V1) & (R be transitiveRELAT-2V8 implies S be transitiveRELAT-2V8)) & (R be connectedRELAT-2V6 implies S be connectedRELAT-2V6)) & (R be antisymmetricRELAT-2V4 implies S be antisymmetricRELAT-2V4)) & (R be well-foundedWELLORD1V1 implies S be well-foundedWELLORD1V1)"
sorry

mtheorem wellord1_th_44:
" for R be RelationRELAT-1M1 holds  for S be RelationRELAT-1M1 holds  for F be FunctionFUNCT-1M1 holds R be well-orderingWELLORD1V2 & F is-isomorphism-ofWELLORD1R3(R,S) implies S be well-orderingWELLORD1V2"
  using wellord1_th_43 sorry

mtheorem wellord1_th_45:
" for R be RelationRELAT-1M1 holds  for S be RelationRELAT-1M1 holds R be well-orderingWELLORD1V2 implies ( for F be FunctionFUNCT-1M1 holds  for G be FunctionFUNCT-1M1 holds F is-isomorphism-ofWELLORD1R3(R,S) & G is-isomorphism-ofWELLORD1R3(R,S) implies F =FUNCT-1R1 G)"
sorry

mdef wellord1_def_9 ("canonical-isomorphism-ofWELLORD1K3'( _ , _ ')" [0,0]200 ) where
  mlet "R be RelationRELAT-1M1", "S be RelationRELAT-1M1"
"assume R be well-orderingWELLORD1V2 & (R,S)are-isomorphicWELLORD1R4 func canonical-isomorphism-ofWELLORD1K3(R,S) \<rightarrow> FunctionFUNCT-1M1 means
  \<lambda>it. it is-isomorphism-ofWELLORD1R3(R,S)"
proof-
  (*existence*)
    show "R be well-orderingWELLORD1V2 & (R,S)are-isomorphicWELLORD1R4 implies ( ex it be FunctionFUNCT-1M1 st it is-isomorphism-ofWELLORD1R3(R,S))"
sorry
  (*uniqueness*)
    show "R be well-orderingWELLORD1V2 & (R,S)are-isomorphicWELLORD1R4 implies ( for it1 be FunctionFUNCT-1M1 holds  for it2 be FunctionFUNCT-1M1 holds it1 is-isomorphism-ofWELLORD1R3(R,S) & it2 is-isomorphism-ofWELLORD1R3(R,S) implies it1 =HIDDENR1 it2)"
sorry
qed "sorry"

mtheorem wellord1_th_46:
" for R be RelationRELAT-1M1 holds R be well-orderingWELLORD1V2 implies ( for a be objectHIDDENM1 holds a inHIDDENR3 fieldRELAT-1K3 R implies  not (R,R |-2WELLORD1K2 R -SegWELLORD1K1 a)are-isomorphicWELLORD1R4)"
sorry

mtheorem wellord1_th_47:
" for a be objectHIDDENM1 holds  for b be objectHIDDENM1 holds  for R be RelationRELAT-1M1 holds ((R be well-orderingWELLORD1V2 & a inHIDDENR3 fieldRELAT-1K3 R) & b inHIDDENR3 fieldRELAT-1K3 R) & a <>HIDDENR2 b implies  not (R |-2WELLORD1K2 R -SegWELLORD1K1 a,R |-2WELLORD1K2 R -SegWELLORD1K1 b)are-isomorphicWELLORD1R4"
sorry

mtheorem wellord1_th_48:
" for Z be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds  for S be RelationRELAT-1M1 holds  for F be FunctionFUNCT-1M1 holds (R be well-orderingWELLORD1V2 & Z c=TARSKIR1 fieldRELAT-1K3 R) & F is-isomorphism-ofWELLORD1R3(R,S) implies F |RELAT-1K8 Z is-isomorphism-ofWELLORD1R3(R |-2WELLORD1K2 Z,S |-2WELLORD1K2 (F .:FUNCT-1K5 Z)) & (R |-2WELLORD1K2 Z,S |-2WELLORD1K2 (F .:FUNCT-1K5 Z))are-isomorphicWELLORD1R4"
sorry

mtheorem wellord1_th_49:
" for R be RelationRELAT-1M1 holds  for S be RelationRELAT-1M1 holds  for F be FunctionFUNCT-1M1 holds F is-isomorphism-ofWELLORD1R3(R,S) implies ( for a be objectHIDDENM1 holds a inHIDDENR3 fieldRELAT-1K3 R implies ( ex b be objectHIDDENM1 st b inHIDDENR3 fieldRELAT-1K3 S & F .:FUNCT-1K5 R -SegWELLORD1K1 a =XBOOLE-0R4 S -SegWELLORD1K1 b))"
sorry

mtheorem wellord1_th_50:
" for R be RelationRELAT-1M1 holds  for S be RelationRELAT-1M1 holds  for F be FunctionFUNCT-1M1 holds R be well-orderingWELLORD1V2 & F is-isomorphism-ofWELLORD1R3(R,S) implies ( for a be objectHIDDENM1 holds a inHIDDENR3 fieldRELAT-1K3 R implies ( ex b be objectHIDDENM1 st b inHIDDENR3 fieldRELAT-1K3 S & (R |-2WELLORD1K2 R -SegWELLORD1K1 a,S |-2WELLORD1K2 S -SegWELLORD1K1 b)are-isomorphicWELLORD1R4))"
sorry

mtheorem wellord1_th_51:
" for a be objectHIDDENM1 holds  for b be objectHIDDENM1 holds  for c be objectHIDDENM1 holds  for R be RelationRELAT-1M1 holds  for S be RelationRELAT-1M1 holds (((((R be well-orderingWELLORD1V2 & S be well-orderingWELLORD1V2) & a inHIDDENR3 fieldRELAT-1K3 R) & b inHIDDENR3 fieldRELAT-1K3 S) & c inHIDDENR3 fieldRELAT-1K3 S) & (R,S |-2WELLORD1K2 S -SegWELLORD1K1 b)are-isomorphicWELLORD1R4) & (R |-2WELLORD1K2 R -SegWELLORD1K1 a,S |-2WELLORD1K2 S -SegWELLORD1K1 c)are-isomorphicWELLORD1R4 implies S -SegWELLORD1K1 c c=TARSKIR1 S -SegWELLORD1K1 b & [TARSKIK4 c,b ] inHIDDENR3 S"
sorry

mtheorem wellord1_th_52:
" for R be RelationRELAT-1M1 holds  for S be RelationRELAT-1M1 holds R be well-orderingWELLORD1V2 & S be well-orderingWELLORD1V2 implies ((R,S)are-isomorphicWELLORD1R4 or ( ex a be objectHIDDENM1 st a inHIDDENR3 fieldRELAT-1K3 R & (R |-2WELLORD1K2 R -SegWELLORD1K1 a,S)are-isomorphicWELLORD1R4)) or ( ex a be objectHIDDENM1 st a inHIDDENR3 fieldRELAT-1K3 S & (R,S |-2WELLORD1K2 S -SegWELLORD1K1 a)are-isomorphicWELLORD1R4)"
sorry

mtheorem wellord1_th_53:
" for Y be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds Y c=TARSKIR1 fieldRELAT-1K3 R & R be well-orderingWELLORD1V2 implies (R,R |-2WELLORD1K2 Y)are-isomorphicWELLORD1R4 or ( ex a be objectHIDDENM1 st a inHIDDENR3 fieldRELAT-1K3 R & (R |-2WELLORD1K2 R -SegWELLORD1K1 a,R |-2WELLORD1K2 Y)are-isomorphicWELLORD1R4)"
sorry

mtheorem wellord1_th_54:
" for R be RelationRELAT-1M1 holds  for S be RelationRELAT-1M1 holds (R,S)are-isomorphicWELLORD1R4 & R be well-orderingWELLORD1V2 implies S be well-orderingWELLORD1V2"
  using wellord1_th_44 sorry

end
