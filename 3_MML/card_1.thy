theory card_1
  imports wellord2 finset_1
   "../mizar_extension/E_number"
begin
(*begin*)
reserve A, B, C for "OrdinalORDINAL1M3"
reserve X, X1, Y, Y1, Z for "setHIDDENM2"
reserve a, b, b1, b2, x, y, z for "objectHIDDENM1"
reserve R for "RelationRELAT-1M1"
reserve f, g, h for "FunctionFUNCT-1M1"
reserve k, m, n for "NatORDINAL1M6"
mdef card_1_def_1 ("cardinalCARD-1V1" 70 ) where
"attr cardinalCARD-1V1 for objectHIDDENM1 means
  (\<lambda>IT.  ex B be OrdinalORDINAL1M3 st IT =HIDDENR1 B & ( for A be OrdinalORDINAL1M3 holds (A,B)are-equipotentWELLORD2R2 implies B c=ORDINAL1R1 A))"..

mtheorem card_1_cl_1:
"cluster cardinalCARD-1V1 for setHIDDENM2"
proof
(*existence*)
  show " ex it be setHIDDENM2 st it be cardinalCARD-1V1"
sorry
qed "sorry"

syntax CARD_1M1 :: "Ty" ("CardinalCARD-1M1" 70)
translations "CardinalCARD-1M1" \<rightharpoonup> "cardinalCARD-1V1\<bar>setHIDDENM2"

mtheorem card_1_cl_2:
"cluster cardinalCARD-1V1 also-is ordinalORDINAL1V3 for setHIDDENM2"
proof
(*coherence*)
  show " for it be setHIDDENM2 holds it be cardinalCARD-1V1 implies it be ordinalORDINAL1V3"
     sorry
qed "sorry"

reserve M, N for "CardinalCARD-1M1"
(*\$CT*)
mtheorem card_1_th_2:
" for M be CardinalCARD-1M1 holds  for N be CardinalCARD-1M1 holds (M,N)are-equipotentWELLORD2R2 implies M =XBOOLE-0R4 N"
sorry

mtheorem card_1_th_3:
" for M be CardinalCARD-1M1 holds  for N be CardinalCARD-1M1 holds M inTARSKIR2 N iff M c=ORDINAL1R1 N & M <>HIDDENR2 N"
  using ordinal1_th_11 xboole_0_def_8 sorry

mtheorem card_1_th_4:
" for M be CardinalCARD-1M1 holds  for N be CardinalCARD-1M1 holds M inTARSKIR2 N iff  not N c=ORDINAL1R1 M"
  using ordinal1_th_5 ordinal1_th_16 sorry

mdef card_1_def_2 ("cardCARD-1K1  _ " [228]228 ) where
  mlet "X be setHIDDENM2"
"func cardCARD-1K1 X \<rightarrow> CardinalCARD-1M1 means
  \<lambda>it. (X,it)are-equipotentWELLORD2R2"
proof-
  (*existence*)
    show " ex it be CardinalCARD-1M1 st (X,it)are-equipotentWELLORD2R2"
sorry
  (*uniqueness*)
    show " for it1 be CardinalCARD-1M1 holds  for it2 be CardinalCARD-1M1 holds (X,it1)are-equipotentWELLORD2R2 & (X,it2)are-equipotentWELLORD2R2 implies it1 =HIDDENR1 it2"
      using card_1_th_2 wellord2_th_15 sorry
qed "sorry"

mtheorem CARD_1K1_projectivity:
" for X be setHIDDENM2 holds cardCARD-1K1 (cardCARD-1K1 X) =HIDDENR1 cardCARD-1K1 X"
sorry

mtheorem card_1_reduce_1:
  mlet "C be CardinalCARD-1M1"
"reduce cardCARD-1K1 C to C"
proof
(*reducibility*)
  show "cardCARD-1K1 C =HIDDENR1 C"
    using card_1_def_2 sorry
qed "sorry"

mtheorem card_1_cl_3:
"cluster emptyXBOOLE-0V1 also-is cardinalCARD-1V1 for setHIDDENM2"
proof
(*coherence*)
  show " for it be setHIDDENM2 holds it be emptyXBOOLE-0V1 implies it be cardinalCARD-1V1"
sorry
qed "sorry"

mtheorem card_1_cl_4:
  mlet "X be emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster cardCARD-1K1 X as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "cardCARD-1K1 X be emptyXBOOLE-0V1"
     sorry
qed "sorry"

mtheorem card_1_cl_5:
  mlet "X be emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster cardCARD-1K1 X as-term-is zeroORDINAL1V8"
proof
(*coherence*)
  show "cardCARD-1K1 X be zeroORDINAL1V8"
     sorry
qed "sorry"

mtheorem card_1_cl_6:
  mlet "X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster cardCARD-1K1 X as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "cardCARD-1K1 X be  non emptyXBOOLE-0V1"
sorry
qed "sorry"

mtheorem card_1_cl_7:
  mlet "X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster cardCARD-1K1 X as-term-is  non zeroORDINAL1V8"
proof
(*coherence*)
  show "cardCARD-1K1 X be  non zeroORDINAL1V8"
     sorry
qed "sorry"

mtheorem card_1_th_5:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds (X,Y)are-equipotentWELLORD2R2 iff cardCARD-1K1 X =XBOOLE-0R4 cardCARD-1K1 Y"
sorry

mtheorem card_1_th_6:
" for R be RelationRELAT-1M1 holds R be well-orderingWELLORD1V2 implies (fieldRELAT-1K3 R,order-type-ofWELLORD2K2 R)are-equipotentWELLORD2R2"
sorry

mtheorem card_1_th_7:
" for X be setHIDDENM2 holds  for M be CardinalCARD-1M1 holds X c=TARSKIR1 M implies cardCARD-1K1 X c=ORDINAL1R1 M"
sorry

mtheorem card_1_th_8:
" for A be OrdinalORDINAL1M3 holds cardCARD-1K1 A c=ORDINAL1R1 A"
sorry

mtheorem card_1_th_9:
" for X be setHIDDENM2 holds  for M be CardinalCARD-1M1 holds X inTARSKIR2 M implies cardCARD-1K1 X inTARSKIR2 M"
  using card_1_th_8 ordinal1_th_12 sorry

(*\$N Cantor-Bernstein Theorem*)
mtheorem card_1_th_10:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds cardCARD-1K1 X c=ORDINAL1R1 cardCARD-1K1 Y iff ( ex f be FunctionFUNCT-1M1 st (f be one-to-oneFUNCT-1V2 & domRELAT-1K1 f =XBOOLE-0R4 X) & rngFUNCT-1K2 f c=TARSKIR1 Y)"
sorry

mtheorem card_1_th_11:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X c=TARSKIR1 Y implies cardCARD-1K1 X c=ORDINAL1R1 cardCARD-1K1 Y"
sorry

mtheorem card_1_th_12:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds cardCARD-1K1 X c=ORDINAL1R1 cardCARD-1K1 Y iff ( ex f be FunctionFUNCT-1M1 st domRELAT-1K1 f =XBOOLE-0R4 Y & X c=TARSKIR1 rngFUNCT-1K2 f)"
sorry

mtheorem card_1_th_13:
" for X be setHIDDENM2 holds  not (X,boolZFMISC-1K1 X)are-equipotentWELLORD2R2"
sorry

(*\$N Cantor Theorem*)
mtheorem card_1_th_14:
" for X be setHIDDENM2 holds cardCARD-1K1 X inTARSKIR2 cardCARD-1K1 (boolZFMISC-1K1 X)"
sorry

mdef card_1_def_3 ("nextcardCARD-1K2  _ " [228]228 ) where
  mlet "X be setHIDDENM2"
"func nextcardCARD-1K2 X \<rightarrow> CardinalCARD-1M1 means
  \<lambda>it. cardCARD-1K1 X inTARSKIR2 it & ( for M be CardinalCARD-1M1 holds cardCARD-1K1 X inTARSKIR2 M implies it c=ORDINAL1R1 M)"
proof-
  (*existence*)
    show " ex it be CardinalCARD-1M1 st cardCARD-1K1 X inTARSKIR2 it & ( for M be CardinalCARD-1M1 holds cardCARD-1K1 X inTARSKIR2 M implies it c=ORDINAL1R1 M)"
sorry
  (*uniqueness*)
    show " for it1 be CardinalCARD-1M1 holds  for it2 be CardinalCARD-1M1 holds (cardCARD-1K1 X inTARSKIR2 it1 & ( for M be CardinalCARD-1M1 holds cardCARD-1K1 X inTARSKIR2 M implies it1 c=ORDINAL1R1 M)) & (cardCARD-1K1 X inTARSKIR2 it2 & ( for M be CardinalCARD-1M1 holds cardCARD-1K1 X inTARSKIR2 M implies it2 c=ORDINAL1R1 M)) implies it1 =HIDDENR1 it2"
       sorry
qed "sorry"

mtheorem card_1_th_15:
" for X be setHIDDENM2 holds {}XBOOLE-0K1 inTARSKIR2 nextcardCARD-1K2 X"
sorry

mtheorem card_1_th_16:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds cardCARD-1K1 X =XBOOLE-0R4 cardCARD-1K1 Y implies nextcardCARD-1K2 X =XBOOLE-0R4 nextcardCARD-1K2 Y"
sorry

mtheorem card_1_th_17:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds (X,Y)are-equipotentWELLORD2R2 implies nextcardCARD-1K2 X =XBOOLE-0R4 nextcardCARD-1K2 Y"
sorry

mtheorem card_1_th_18:
" for A be OrdinalORDINAL1M3 holds A inTARSKIR2 nextcardCARD-1K2 A"
sorry

reserve S for "SequenceORDINAL1M4"
mdef card_1_def_4 ("limit-cardinalCARD-1V2" 70 ) where
"attr limit-cardinalCARD-1V2 for CardinalCARD-1M1 means
  (\<lambda>M.  not ( ex N be CardinalCARD-1M1 st M =XBOOLE-0R4 nextcardCARD-1K2 N))"..

mdef card_1_def_5 ("alephCARD-1K3  _ " [228]228 ) where
  mlet "A be OrdinalORDINAL1M3"
"func alephCARD-1K3 A \<rightarrow> setHIDDENM2 means
  \<lambda>it.  ex S be SequenceORDINAL1M4 st (((it =XBOOLE-0R4 lastORDINAL2K1 S & domRELAT-1K1 S =XBOOLE-0R4 succORDINAL1K1 A) & S .FUNCT-1K1 (0ORDINAL1K5) =XBOOLE-0R4 cardCARD-1K1 (omegaORDINAL1K4)) & ( for B be OrdinalORDINAL1M3 holds succORDINAL1K1 B inTARSKIR2 succORDINAL1K1 A implies S .FUNCT-1K1 succORDINAL1K1 B =XBOOLE-0R4 nextcardCARD-1K2 (S .FUNCT-1K1 B))) & ( for B be OrdinalORDINAL1M3 holds (B inTARSKIR2 succORDINAL1K1 A & B <>HIDDENR2 0ORDINAL1K5) & B be limit-ordinalORDINAL1V4 implies S .FUNCT-1K1 B =XBOOLE-0R4 cardCARD-1K1 supORDINAL2K4 (S |RELAT-1K8 B))"
proof-
  (*existence*)
    show " ex it be setHIDDENM2 st  ex S be SequenceORDINAL1M4 st (((it =XBOOLE-0R4 lastORDINAL2K1 S & domRELAT-1K1 S =XBOOLE-0R4 succORDINAL1K1 A) & S .FUNCT-1K1 (0ORDINAL1K5) =XBOOLE-0R4 cardCARD-1K1 (omegaORDINAL1K4)) & ( for B be OrdinalORDINAL1M3 holds succORDINAL1K1 B inTARSKIR2 succORDINAL1K1 A implies S .FUNCT-1K1 succORDINAL1K1 B =XBOOLE-0R4 nextcardCARD-1K2 (S .FUNCT-1K1 B))) & ( for B be OrdinalORDINAL1M3 holds (B inTARSKIR2 succORDINAL1K1 A & B <>HIDDENR2 0ORDINAL1K5) & B be limit-ordinalORDINAL1V4 implies S .FUNCT-1K1 B =XBOOLE-0R4 cardCARD-1K1 supORDINAL2K4 (S |RELAT-1K8 B))"
sorry
  (*uniqueness*)
    show " for it1 be setHIDDENM2 holds  for it2 be setHIDDENM2 holds ( ex S be SequenceORDINAL1M4 st (((it1 =XBOOLE-0R4 lastORDINAL2K1 S & domRELAT-1K1 S =XBOOLE-0R4 succORDINAL1K1 A) & S .FUNCT-1K1 (0ORDINAL1K5) =XBOOLE-0R4 cardCARD-1K1 (omegaORDINAL1K4)) & ( for B be OrdinalORDINAL1M3 holds succORDINAL1K1 B inTARSKIR2 succORDINAL1K1 A implies S .FUNCT-1K1 succORDINAL1K1 B =XBOOLE-0R4 nextcardCARD-1K2 (S .FUNCT-1K1 B))) & ( for B be OrdinalORDINAL1M3 holds (B inTARSKIR2 succORDINAL1K1 A & B <>HIDDENR2 0ORDINAL1K5) & B be limit-ordinalORDINAL1V4 implies S .FUNCT-1K1 B =XBOOLE-0R4 cardCARD-1K1 supORDINAL2K4 (S |RELAT-1K8 B))) & ( ex S be SequenceORDINAL1M4 st (((it2 =XBOOLE-0R4 lastORDINAL2K1 S & domRELAT-1K1 S =XBOOLE-0R4 succORDINAL1K1 A) & S .FUNCT-1K1 (0ORDINAL1K5) =XBOOLE-0R4 cardCARD-1K1 (omegaORDINAL1K4)) & ( for B be OrdinalORDINAL1M3 holds succORDINAL1K1 B inTARSKIR2 succORDINAL1K1 A implies S .FUNCT-1K1 succORDINAL1K1 B =XBOOLE-0R4 nextcardCARD-1K2 (S .FUNCT-1K1 B))) & ( for B be OrdinalORDINAL1M3 holds (B inTARSKIR2 succORDINAL1K1 A & B <>HIDDENR2 0ORDINAL1K5) & B be limit-ordinalORDINAL1V4 implies S .FUNCT-1K1 B =XBOOLE-0R4 cardCARD-1K1 supORDINAL2K4 (S |RELAT-1K8 B))) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mlemma card_1_lm_1:
"alephCARD-1K3 (0ORDINAL1K5) =XBOOLE-0R4 cardCARD-1K1 (omegaORDINAL1K4) & (( for A be OrdinalORDINAL1M3 holds alephCARD-1K3 (succORDINAL1K1 A) =XBOOLE-0R4 nextcardCARD-1K2 (alephCARD-1K3 A)) & ( for A be OrdinalORDINAL1M3 holds A <>HIDDENR2 0ORDINAL1K5 & A be limit-ordinalORDINAL1V4 implies ( for S be SequenceORDINAL1M4 holds domRELAT-1K1 S =XBOOLE-0R4 A & ( for B be OrdinalORDINAL1M3 holds B inTARSKIR2 A implies S .FUNCT-1K1 B =XBOOLE-0R4 alephCARD-1K3 B) implies alephCARD-1K3 A =XBOOLE-0R4 cardCARD-1K1 supORDINAL2K4 S)))"
sorry

mtheorem card_1_cl_8:
  mlet "A be OrdinalORDINAL1M3"
"cluster alephCARD-1K3 A as-term-is cardinalCARD-1V1"
proof
(*coherence*)
  show "alephCARD-1K3 A be cardinalCARD-1V1"
sorry
qed "sorry"

mtheorem card_1_th_19:
" for A be OrdinalORDINAL1M3 holds alephCARD-1K3 (succORDINAL1K1 A) =XBOOLE-0R4 nextcardCARD-1K2 (alephCARD-1K3 A)"
  using card_1_lm_1 sorry

mtheorem card_1_th_20:
" for A be OrdinalORDINAL1M3 holds A <>HIDDENR2 {}XBOOLE-0K1 & A be limit-ordinalORDINAL1V4 implies ( for S be SequenceORDINAL1M4 holds domRELAT-1K1 S =XBOOLE-0R4 A & ( for B be OrdinalORDINAL1M3 holds B inTARSKIR2 A implies S .FUNCT-1K1 B =XBOOLE-0R4 alephCARD-1K3 B) implies alephCARD-1K3 A =XBOOLE-0R4 cardCARD-1K1 supORDINAL2K4 S)"
  using card_1_lm_1 sorry

mtheorem card_1_th_21:
" for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds A inTARSKIR2 B iff alephCARD-1K3 A inTARSKIR2 alephCARD-1K3 B"
sorry

mtheorem card_1_th_22:
" for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds alephCARD-1K3 A =XBOOLE-0R4 alephCARD-1K3 B implies A =XBOOLE-0R4 B"
sorry

mtheorem card_1_th_23:
" for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds A c=ORDINAL1R1 B iff alephCARD-1K3 A c=ORDINAL1R1 alephCARD-1K3 B"
sorry

mtheorem card_1_th_24:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds (X c=TARSKIR1 Y & Y c=TARSKIR1 Z) & (X,Z)are-equipotentWELLORD2R2 implies (X,Y)are-equipotentWELLORD2R2 & (Y,Z)are-equipotentWELLORD2R2"
sorry

mtheorem card_1_th_25:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds boolZFMISC-1K1 Y c=TARSKIR1 X implies cardCARD-1K1 Y inTARSKIR2 cardCARD-1K1 X &  not (Y,X)are-equipotentWELLORD2R2"
sorry

mtheorem card_1_th_26:
" for X be setHIDDENM2 holds (X,{}XBOOLE-0K1)are-equipotentWELLORD2R2 implies X =XBOOLE-0R4 {}XBOOLE-0K1"
  using relat_1_th_42 sorry

mtheorem card_1_th_27:
"cardCARD-1K1 ({}XBOOLE-0K1) =XBOOLE-0R4 0ORDINAL1K5"
   sorry

mtheorem card_1_th_28:
" for X be setHIDDENM2 holds  for x be objectHIDDENM1 holds (X,{TARSKIK1 x})are-equipotentWELLORD2R2 iff ( ex x be objectHIDDENM1 st X =XBOOLE-0R4 {TARSKIK1 x})"
sorry

mtheorem card_1_th_29:
" for X be setHIDDENM2 holds  for x be objectHIDDENM1 holds cardCARD-1K1 X =XBOOLE-0R4 cardCARD-1K1 {TARSKIK1 x} iff ( ex x be objectHIDDENM1 st X =XBOOLE-0R4 {TARSKIK1 x})"
  using card_1_th_5 card_1_th_28 sorry

mtheorem card_1_th_30:
" for x be objectHIDDENM1 holds cardCARD-1K1 {TARSKIK1 x} =XBOOLE-0R4 \<one>\<^sub>M"
sorry

mtheorem card_1_th_31:
" for X be setHIDDENM2 holds  for X1 be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Y1 be setHIDDENM2 holds ((X missesXBOOLE-0R1 X1 & Y missesXBOOLE-0R1 Y1) & (X,Y)are-equipotentWELLORD2R2) & (X1,Y1)are-equipotentWELLORD2R2 implies (X \\/XBOOLE-0K2 X1,Y \\/XBOOLE-0K2 Y1)are-equipotentWELLORD2R2"
sorry

mtheorem card_1_th_32:
" for X be setHIDDENM2 holds  for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds x inHIDDENR3 X & y inHIDDENR3 X implies (X \\SUBSET-1K6 {TARSKIK1 x},X \\SUBSET-1K6 {TARSKIK1 y})are-equipotentWELLORD2R2"
sorry

mtheorem card_1_th_33:
" for X be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds X c=TARSKIR1 domRELAT-1K1 f & f be one-to-oneFUNCT-1V2 implies (X,f .:FUNCT-1K5 X)are-equipotentWELLORD2R2"
sorry

mtheorem card_1_th_34:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds ((X,Y)are-equipotentWELLORD2R2 & x inHIDDENR3 X) & y inHIDDENR3 Y implies (X \\SUBSET-1K6 {TARSKIK1 x},Y \\SUBSET-1K6 {TARSKIK1 y})are-equipotentWELLORD2R2"
sorry

mtheorem card_1_th_35:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds (succORDINAL1K1 X,succORDINAL1K1 Y)are-equipotentWELLORD2R2 implies (X,Y)are-equipotentWELLORD2R2"
sorry

mtheorem card_1_th_36:
" for n be NatORDINAL1M6 holds n =XBOOLE-0R4 {}XBOOLE-0K1 or ( ex m be NatORDINAL1M6 st n =XBOOLE-0R4 succORDINAL1K1 m)"
sorry

mlemma card_1_lm_2:
" for m be NatORDINAL1M6 holds  for n be NatORDINAL1M6 holds (n,m)are-equipotentWELLORD2R2 implies n =XBOOLE-0R4 m"
sorry

mtheorem card_1_th_37:
" for x be objectHIDDENM1 holds x inHIDDENR3 omegaORDINAL1K4 implies x be cardinalCARD-1V1"
sorry

mtheorem card_1_cl_9:
"cluster naturalORDINAL1V7 also-is cardinalCARD-1V1 for numberORDINAL1M2"
proof
(*coherence*)
  show " for it be numberORDINAL1M2 holds it be naturalORDINAL1V7 implies it be cardinalCARD-1V1"
    using card_1_th_37 sorry
qed "sorry"

mtheorem card_1_th_38:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds (X,Y)are-equipotentWELLORD2R2 & X be finiteFINSET-1V1 implies Y be finiteFINSET-1V1"
sorry

mtheorem card_1_th_39:
" for n be NatORDINAL1M6 holds n be finiteFINSET-1V1 & cardCARD-1K1 n be finiteFINSET-1V1"
sorry

mtheorem card_1_th_40:
" for m be NatORDINAL1M6 holds  for n be NatORDINAL1M6 holds cardCARD-1K1 n =XBOOLE-0R4 cardCARD-1K1 m implies n =XBOOLE-0R4 m"
   sorry

mtheorem card_1_th_41:
" for m be NatORDINAL1M6 holds  for n be NatORDINAL1M6 holds cardCARD-1K1 n c=ORDINAL1R1 cardCARD-1K1 m iff n c=ORDINAL1R1 m"
   sorry

mtheorem card_1_th_42:
" for m be NatORDINAL1M6 holds  for n be NatORDINAL1M6 holds cardCARD-1K1 n inTARSKIR2 cardCARD-1K1 m iff n inTARSKIR2 m"
   sorry

mlemma card_1_lm_3:
" for X be setHIDDENM2 holds X be finiteFINSET-1V1 implies ( ex n be NatORDINAL1M6 st (X,n)are-equipotentWELLORD2R2)"
sorry

(*\$CT*)
mtheorem card_1_th_44:
" for n be NatORDINAL1M6 holds nextcardCARD-1K2 (cardCARD-1K1 n) =XBOOLE-0R4 cardCARD-1K1 (succORDINAL1K1 n)"
sorry

abbreviation(input) CARD_1K4("cardCARD-1K4  _ " [228]228) where
  "cardCARD-1K4 X \<equiv> cardCARD-1K1 X"

mtheorem card_1_add_1:
  mlet "X be finiteFINSET-1V1\<bar>setHIDDENM2"
"cluster cardCARD-1K1 X as-term-is ElementSUBSET-1M1-of omegaORDINAL1K4"
proof
(*coherence*)
  show "cardCARD-1K1 X be ElementSUBSET-1M1-of omegaORDINAL1K4"
sorry
qed "sorry"

mtheorem card_1_th_45:
" for X be setHIDDENM2 holds X be finiteFINSET-1V1 implies nextcardCARD-1K2 X be finiteFINSET-1V1"
sorry

theorem card_1_sch_1:
  fixes Sigmap1 
  assumes
    A1: "Sigmap1({}XBOOLE-0K1)" and
   A2: " for M be CardinalCARD-1M1 holds Sigmap1(M) implies Sigmap1(nextcardCARD-1K2 M)" and
   A3: " for M be CardinalCARD-1M1 holds (M <>HIDDENR2 {}XBOOLE-0K1 & M be limit-cardinalCARD-1V2) & ( for N be CardinalCARD-1M1 holds N inTARSKIR2 M implies Sigmap1(N)) implies Sigmap1(M)"
  shows " for M be CardinalCARD-1M1 holds Sigmap1(M)"
sorry

theorem card_1_sch_2:
  fixes Sigmap1 
  assumes
    A1: " for M be CardinalCARD-1M1 holds ( for N be CardinalCARD-1M1 holds N inTARSKIR2 M implies Sigmap1(N)) implies Sigmap1(M)"
  shows " for M be CardinalCARD-1M1 holds Sigmap1(M)"
sorry

mtheorem card_1_th_46:
"alephCARD-1K3 (0ORDINAL1K5) =XBOOLE-0R4 omegaORDINAL1K4"
sorry

mtheorem card_1_cl_10:
"cluster omegaORDINAL1K4 as-term-is cardinalCARD-1V1 for numberORDINAL1M2"
proof
(*coherence*)
  show " for it be numberORDINAL1M2 holds it =HIDDENR1 omegaORDINAL1K4 implies it be cardinalCARD-1V1"
    using card_1_th_46 sorry
qed "sorry"

mtheorem card_1_th_47:
"cardCARD-1K1 (omegaORDINAL1K4) =XBOOLE-0R4 omegaORDINAL1K4"
   sorry

mtheorem card_1_cl_11:
"cluster omegaORDINAL1K4 as-term-is limit-cardinalCARD-1V2"
proof
(*coherence*)
  show "omegaORDINAL1K4 be limit-cardinalCARD-1V2"
sorry
qed "sorry"

mtheorem card_1_cl_12:
"cluster note-that finiteFINSET-1V1 for ElementSUBSET-1M1-of omegaORDINAL1K4"
proof
(*coherence*)
  show " for it be ElementSUBSET-1M1-of omegaORDINAL1K4 holds it be finiteFINSET-1V1"
    using card_1_th_39 sorry
qed "sorry"

mtheorem card_1_cl_13:
"cluster finiteFINSET-1V1 for CardinalCARD-1M1"
proof
(*existence*)
  show " ex it be CardinalCARD-1M1 st it be finiteFINSET-1V1"
sorry
qed "sorry"

mtheorem card_1_th_48:
" for M be finiteFINSET-1V1\<bar>CardinalCARD-1M1 holds  ex n be NatORDINAL1M6 st M =XBOOLE-0R4 cardCARD-1K1 n"
sorry

mtheorem card_1_cl_14:
  mlet "X be finiteFINSET-1V1\<bar>setHIDDENM2"
"cluster cardCARD-1K4 X as-term-is finiteFINSET-1V1"
proof
(*coherence*)
  show "cardCARD-1K4 X be finiteFINSET-1V1"
     sorry
qed "sorry"

mlemma card_1_lm_4:
" for A be OrdinalORDINAL1M3 holds  for n be NatORDINAL1M6 holds (A,n)are-equipotentWELLORD2R2 implies A =XBOOLE-0R4 n"
sorry

mlemma card_1_lm_5:
" for A be OrdinalORDINAL1M3 holds A be finiteFINSET-1V1 iff A inTARSKIR2 omegaORDINAL1K4"
sorry

mtheorem card_1_cl_15:
"cluster omegaORDINAL1K4 as-term-is infiniteFINSET-1V2"
proof
(*coherence*)
  show "omegaORDINAL1K4 be infiniteFINSET-1V2"
sorry
qed "sorry"

mtheorem card_1_cl_16:
"cluster infiniteFINSET-1V2 for setHIDDENM2"
proof
(*existence*)
  show " ex it be setHIDDENM2 st it be infiniteFINSET-1V2"
sorry
qed "sorry"

mtheorem card_1_cl_17:
  mlet "X be infiniteFINSET-1V2\<bar>setHIDDENM2"
"cluster cardCARD-1K1 X as-term-is infiniteFINSET-1V2"
proof
(*coherence*)
  show "cardCARD-1K1 X be infiniteFINSET-1V2"
sorry
qed "sorry"

(*begin*)
mtheorem card_1_th_49:
"\<one>\<^sub>M =XBOOLE-0R4 {TARSKIK1 0ORDINAL1K5 }"
sorry

mtheorem card_1_th_50:
"\<two>\<^sub>M =XBOOLE-0R4 {TARSKIK2 0ORDINAL1K5,\<one>\<^sub>M }"
sorry

mtheorem card_1_th_51:
"\<three>\<^sub>M =XBOOLE-0R4 {ENUMSET1K1 0ORDINAL1K5,\<one>\<^sub>M,\<two>\<^sub>M }"
sorry

mtheorem card_1_th_52:
"\<four>\<^sub>M =XBOOLE-0R4 {ENUMSET1K2 0ORDINAL1K5,\<one>\<^sub>M,\<two>\<^sub>M,\<three>\<^sub>M }"
sorry

mtheorem card_1_th_53:
"\<five>\<^sub>M =XBOOLE-0R4 {ENUMSET1K3 0ORDINAL1K5,\<one>\<^sub>M,\<two>\<^sub>M,\<three>\<^sub>M,\<four>\<^sub>M }"
sorry

mtheorem card_1_th_54:
"\<six>\<^sub>M =XBOOLE-0R4 {ENUMSET1K4 0ORDINAL1K5,\<one>\<^sub>M,\<two>\<^sub>M,\<three>\<^sub>M,\<four>\<^sub>M,\<five>\<^sub>M }"
sorry

mtheorem card_1_th_55:
"\<seven>\<^sub>M =XBOOLE-0R4 {ENUMSET1K5 0ORDINAL1K5,\<one>\<^sub>M,\<two>\<^sub>M,\<three>\<^sub>M,\<four>\<^sub>M,\<five>\<^sub>M,\<six>\<^sub>M }"
sorry

mtheorem card_1_th_56:
"\<eight>\<^sub>M =XBOOLE-0R4 {ENUMSET1K6 0ORDINAL1K5,\<one>\<^sub>M,\<two>\<^sub>M,\<three>\<^sub>M,\<four>\<^sub>M,\<five>\<^sub>M,\<six>\<^sub>M,\<seven>\<^sub>M }"
sorry

mtheorem card_1_th_57:
"\<nine>\<^sub>M =XBOOLE-0R4 {ENUMSET1K7 0ORDINAL1K5,\<one>\<^sub>M,\<two>\<^sub>M,\<three>\<^sub>M,\<four>\<^sub>M,\<five>\<^sub>M,\<six>\<^sub>M,\<seven>\<^sub>M,\<eight>\<^sub>M }"
sorry

mtheorem card_1_th_58:
"\<one>\<zero>\<^sub>M =XBOOLE-0R4 {ENUMSET1K8 0ORDINAL1K5,\<one>\<^sub>M,\<two>\<^sub>M,\<three>\<^sub>M,\<four>\<^sub>M,\<five>\<^sub>M,\<six>\<^sub>M,\<seven>\<^sub>M,\<eight>\<^sub>M,\<nine>\<^sub>M }"
sorry

mtheorem card_1_th_59:
" for f be FunctionFUNCT-1M1 holds domRELAT-1K1 f be infiniteFINSET-1V2 & f be one-to-oneFUNCT-1V2 implies rngFUNCT-1K2 f be infiniteFINSET-1V2"
sorry

reserve k, n, m for "NatORDINAL1M6"
mtheorem card_1_cl_18:
"cluster  non zeroORDINAL1V8\<bar>naturalORDINAL1V7 for objectHIDDENM1"
proof
(*existence*)
  show " ex it be objectHIDDENM1 st it be  non zeroORDINAL1V8\<bar>naturalORDINAL1V7"
sorry
qed "sorry"

mtheorem card_1_cl_19:
"cluster  non zeroORDINAL1V8 for NatORDINAL1M6"
proof
(*existence*)
  show " ex it be NatORDINAL1M6 st it be  non zeroORDINAL1V8"
sorry
qed "sorry"

mtheorem card_1_cl_20:
  mlet "n be  non zeroORDINAL1V8\<bar>naturalORDINAL1V7\<bar>NumberORDINAL1M1"
"cluster SegmORDINAL1K6 n as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "SegmORDINAL1K6 n be  non emptyXBOOLE-0V1"
sorry
qed "sorry"

abbreviation(input) CARD_1K5("SegmCARD-1K5  _ " [164]164) where
  "SegmCARD-1K5 n \<equiv> SegmORDINAL1K6 n"

mtheorem card_1_add_2:
  mlet "n be naturalORDINAL1V7\<bar>NumberORDINAL1M1"
"cluster SegmORDINAL1K6 n as-term-is SubsetSUBSET-1M2-of omegaORDINAL1K4"
proof
(*coherence*)
  show "SegmORDINAL1K6 n be SubsetSUBSET-1M2-of omegaORDINAL1K4"
sorry
qed "sorry"

mtheorem card_1_th_60:
" for A be OrdinalORDINAL1M3 holds  for n be NatORDINAL1M6 holds (A,n)are-equipotentWELLORD2R2 implies A =XBOOLE-0R4 n"
  using card_1_lm_4 sorry

mtheorem card_1_th_61:
" for A be OrdinalORDINAL1M3 holds A be finiteFINSET-1V1 iff A inTARSKIR2 omegaORDINAL1K4"
  using card_1_lm_5 sorry

mtheorem card_1_cl_21:
"cluster naturalORDINAL1V7 also-is finiteFINSET-1V1 for setHIDDENM2"
proof
(*coherence*)
  show " for it be setHIDDENM2 holds it be naturalORDINAL1V7 implies it be finiteFINSET-1V1"
     sorry
qed "sorry"

mtheorem card_1_cl_22:
  mlet "A be infiniteFINSET-1V2\<bar>setHIDDENM2"
"cluster boolZFMISC-1K1 A as-term-is infiniteFINSET-1V2"
proof
(*coherence*)
  show "boolZFMISC-1K1 A be infiniteFINSET-1V2"
sorry
qed "sorry"

mtheorem card_1_cl_23:
  mlet "A be infiniteFINSET-1V2\<bar>setHIDDENM2", "B be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster [:ZFMISC-1K2 A,B :] as-term-is infiniteFINSET-1V2"
proof
(*coherence*)
  show "[:ZFMISC-1K2 A,B :] be infiniteFINSET-1V2"
sorry
qed "sorry"

mtheorem card_1_cl_24:
  mlet "A be infiniteFINSET-1V2\<bar>setHIDDENM2", "B be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster [:ZFMISC-1K2 B,A :] as-term-is infiniteFINSET-1V2"
proof
(*coherence*)
  show "[:ZFMISC-1K2 B,A :] be infiniteFINSET-1V2"
sorry
qed "sorry"

mtheorem card_1_cl_25:
  mlet "X be infiniteFINSET-1V2\<bar>setHIDDENM2"
"cluster infiniteFINSET-1V2 for SubsetSUBSET-1M2-of X"
proof
(*existence*)
  show " ex it be SubsetSUBSET-1M2-of X st it be infiniteFINSET-1V2"
sorry
qed "sorry"

mtheorem card_1_cl_26:
"cluster finiteFINSET-1V1\<bar>ordinalORDINAL1V3 also-is naturalORDINAL1V7 for numberORDINAL1M2"
proof
(*coherence*)
  show " for it be numberORDINAL1M2 holds it be finiteFINSET-1V1\<bar>ordinalORDINAL1V3 implies it be naturalORDINAL1V7"
    using card_1_lm_5 sorry
qed "sorry"

mtheorem card_1_th_62:
" for f be FunctionFUNCT-1M1 holds cardCARD-1K1 f =XBOOLE-0R4 cardCARD-1K1 (domRELAT-1K1 f)"
sorry

mtheorem card_1_cl_27:
  mlet "X be finiteFINSET-1V1\<bar>setHIDDENM2"
"cluster RelInclWELLORD2K1 X as-term-is finiteFINSET-1V1"
proof
(*coherence*)
  show "RelInclWELLORD2K1 X be finiteFINSET-1V1"
sorry
qed "sorry"

mtheorem card_1_th_63:
" for X be setHIDDENM2 holds RelInclWELLORD2K1 X be finiteFINSET-1V1 implies X be finiteFINSET-1V1"
sorry

mtheorem card_1_th_64:
" for x be objectHIDDENM1 holds  for k be NatORDINAL1M6 holds cardCARD-1K1 (k -->FUNCOP-1K7 x) =XBOOLE-0R4 k"
sorry

(*begin*)
(*\$CD*)
mdef card_1_def_7 (" _ -elementCARD-1V3" [70]70 ) where
  mlet "N be objectHIDDENM1"
"attr N -elementCARD-1V3 for setHIDDENM2 means
  (\<lambda>X. cardCARD-1K1 X =HIDDENR1 N)"..

mtheorem card_1_cl_28:
  mlet "N be CardinalCARD-1M1"
"cluster N -elementCARD-1V3 for setHIDDENM2"
proof
(*existence*)
  show " ex it be setHIDDENM2 st it be N -elementCARD-1V3"
sorry
qed "sorry"

mtheorem card_1_cl_29:
"cluster 0ORDINAL1K5 -elementCARD-1V3 also-is emptyXBOOLE-0V1 for setHIDDENM2"
proof
(*coherence*)
  show " for it be setHIDDENM2 holds it be 0ORDINAL1K5 -elementCARD-1V3 implies it be emptyXBOOLE-0V1"
     sorry
qed "sorry"

mtheorem card_1_cl_30:
"cluster emptyXBOOLE-0V1 also-is 0ORDINAL1K5 -elementCARD-1V3 for setHIDDENM2"
proof
(*coherence*)
  show " for it be setHIDDENM2 holds it be emptyXBOOLE-0V1 implies it be 0ORDINAL1K5 -elementCARD-1V3"
     sorry
qed "sorry"

mtheorem card_1_cl_31:
  mlet "x be objectHIDDENM1"
"cluster {TARSKIK1 x} as-term-is \<one>\<^sub>M -elementCARD-1V3"
proof
(*coherence*)
  show "{TARSKIK1 x} be \<one>\<^sub>M -elementCARD-1V3"
sorry
qed "sorry"

mtheorem card_1_cl_32:
  mlet "N be CardinalCARD-1M1"
"cluster N -elementCARD-1V3 for FunctionFUNCT-1M1"
proof
(*existence*)
  show " ex it be FunctionFUNCT-1M1 st it be N -elementCARD-1V3"
sorry
qed "sorry"

mtheorem card_1_cl_33:
  mlet "N be CardinalCARD-1M1", "f be N -elementCARD-1V3\<bar>FunctionFUNCT-1M1"
"cluster domRELAT-1K1 f as-term-is N -elementCARD-1V3"
proof
(*coherence*)
  show "domRELAT-1K1 f be N -elementCARD-1V3"
sorry
qed "sorry"

mtheorem card_1_cl_34:
"cluster \<one>\<^sub>M -elementCARD-1V3 also-is trivialSUBSET-1V2\<bar> non emptyXBOOLE-0V1 for setHIDDENM2"
proof
(*coherence*)
  show " for it be setHIDDENM2 holds it be \<one>\<^sub>M -elementCARD-1V3 implies it be trivialSUBSET-1V2\<bar> non emptyXBOOLE-0V1"
sorry
qed "sorry"

mtheorem card_1_cl_35:
"cluster trivialSUBSET-1V2\<bar> non emptyXBOOLE-0V1 also-is \<one>\<^sub>M -elementCARD-1V3 for setHIDDENM2"
proof
(*coherence*)
  show " for it be setHIDDENM2 holds it be trivialSUBSET-1V2\<bar> non emptyXBOOLE-0V1 implies it be \<one>\<^sub>M -elementCARD-1V3"
sorry
qed "sorry"

mtheorem card_1_cl_36:
  mlet "X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster \<one>\<^sub>M -elementCARD-1V3 for SubsetSUBSET-1M2-of X"
proof
(*existence*)
  show " ex it be SubsetSUBSET-1M2-of X st it be \<one>\<^sub>M -elementCARD-1V3"
sorry
qed "sorry"

syntax CARD_1M2 :: " Set \<Rightarrow> Ty" ("SingletonCARD-1M2-of  _ " [70]70)
translations "SingletonCARD-1M2-of X" \<rightharpoonup> "\<one>\<^sub>M -elementCARD-1V3\<bar>SubsetSUBSET-1M2-of X"

mtheorem card_1_th_65:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for A be SingletonCARD-1M2-of X holds  ex x be ElementSUBSET-1M1-of X st A =XBOOLE-0R4 {TARSKIK1 x}"
sorry

mtheorem card_1_th_66:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds cardCARD-1K1 X c=ORDINAL1R1 cardCARD-1K1 Y iff ( ex f be FunctionFUNCT-1M1 st X c=TARSKIR1 f .:FUNCT-1K5 Y)"
sorry

mtheorem card_1_th_67:
" for X be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds cardCARD-1K1 (f .:FUNCT-1K5 X) c=ORDINAL1R1 cardCARD-1K1 X"
  using card_1_th_66 sorry

mtheorem card_1_th_68:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds cardCARD-1K1 X inTARSKIR2 cardCARD-1K1 Y implies Y \\SUBSET-1K6 X <>HIDDENR2 {}XBOOLE-0K1"
sorry

mtheorem card_1_th_69:
" for X be setHIDDENM2 holds  for x be objectHIDDENM1 holds (X,[:ZFMISC-1K2 X,{TARSKIK1 x} :])are-equipotentWELLORD2R2 & cardCARD-1K1 X =XBOOLE-0R4 cardCARD-1K1 ([:ZFMISC-1K2 X,{TARSKIK1 x} :])"
sorry

mtheorem card_1_th_70:
" for f be FunctionFUNCT-1M1 holds f be one-to-oneFUNCT-1V2 implies cardCARD-1K1 (domRELAT-1K1 f) =XBOOLE-0R4 cardCARD-1K1 (rngFUNCT-1K2 f)"
sorry

mtheorem card_1_cl_37:
  mlet "F be  non trivialSUBSET-1V2\<bar>setHIDDENM2", "A be SingletonCARD-1M2-of F"
"cluster F \\SUBSET-1K6 A as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "F \\SUBSET-1K6 A be  non emptyXBOOLE-0V1"
sorry
qed "sorry"

mtheorem card_1_cl_38:
  mlet "k be  non emptyXBOOLE-0V1\<bar>CardinalCARD-1M1"
"cluster k -elementCARD-1V3 also-is  non emptyXBOOLE-0V1 for setHIDDENM2"
proof
(*coherence*)
  show " for it be setHIDDENM2 holds it be k -elementCARD-1V3 implies it be  non emptyXBOOLE-0V1"
     sorry
qed "sorry"

mtheorem card_1_cl_39:
  mlet "k be naturalORDINAL1V7\<bar>NumberORDINAL1M1"
"cluster SegmCARD-1K5 k as-term-is finiteFINSET-1V1"
proof
(*coherence*)
  show "SegmCARD-1K5 k be finiteFINSET-1V1"
     sorry
qed "sorry"

mtheorem card_1_th_71:
" for f be FunctionFUNCT-1M1 holds  for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds cardCARD-1K1 (f +~FUNCT-4K8(x,y)) =XBOOLE-0R4 cardCARD-1K1 f"
sorry

mtheorem card_1_cl_40:
  mlet "n be  non zeroORDINAL1V8\<bar>naturalORDINAL1V7\<bar>NumberORDINAL1M1"
"cluster SegmCARD-1K5 n as-term-is with-zeroORDINAL1V10"
proof
(*coherence*)
  show "SegmCARD-1K5 n be with-zeroORDINAL1V10"
    using ordinal3_th_8 sorry
qed "sorry"

end
