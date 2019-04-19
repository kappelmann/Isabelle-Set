theory classes2
  imports card_2
   "../mizar_extension/E_number"
begin
(*begin*)
reserve m for "CardinalCARD-1M1"
reserve A, B, C for "OrdinalORDINAL1M3"
reserve x, y, z, X, Y, Z, W for "setHIDDENM2"
reserve f for "FunctionFUNCT-1M1"
mlemma classes2_lm_1:
" for X be setHIDDENM2 holds Tarski-ClassCLASSES1K1 X be TarskiCLASSES1V2"
sorry

mtheorem classes2_cl_1:
"cluster TarskiCLASSES1V2 also-is subset-closedCLASSES1V1 for setHIDDENM2"
proof
(*coherence*)
  show " for it be setHIDDENM2 holds it be TarskiCLASSES1V2 implies it be subset-closedCLASSES1V1"
     sorry
qed "sorry"

mtheorem classes2_cl_2:
  mlet "X be setHIDDENM2"
"cluster Tarski-ClassCLASSES1K1 X as-term-is TarskiCLASSES1V2"
proof
(*coherence*)
  show "Tarski-ClassCLASSES1K1 X be TarskiCLASSES1V2"
    using classes2_lm_1 sorry
qed "sorry"

mtheorem classes2_th_1:
" for X be setHIDDENM2 holds  for W be setHIDDENM2 holds W be subset-closedCLASSES1V1 & X inTARSKIR2 W implies  not (X,W)are-equipotentTARSKIR3 & cardCARD-1K1 X inTARSKIR2 cardCARD-1K1 W"
sorry

mtheorem classes2_th_2:
" for x be setHIDDENM2 holds  for y be setHIDDENM2 holds  for W be setHIDDENM2 holds (W be TarskiCLASSES1V2 & x inTARSKIR2 W) & y inTARSKIR2 W implies {TARSKIK1 x} inTARSKIR2 W & {TARSKIK2 x,y } inTARSKIR2 W"
sorry

mtheorem classes2_th_3:
" for x be setHIDDENM2 holds  for y be setHIDDENM2 holds  for W be setHIDDENM2 holds (W be TarskiCLASSES1V2 & x inTARSKIR2 W) & y inTARSKIR2 W implies [TARSKIK4 x,y ] inHIDDENR3 W"
sorry

mtheorem classes2_th_4:
" for X be setHIDDENM2 holds  for W be setHIDDENM2 holds W be TarskiCLASSES1V2 & X inTARSKIR2 W implies Tarski-ClassCLASSES1K1 X c=TARSKIR1 W"
sorry

mtheorem classes2_th_5:
" for A be OrdinalORDINAL1M3 holds  for W be setHIDDENM2 holds W be TarskiCLASSES1V2 & A inTARSKIR2 W implies succORDINAL1K1 A inTARSKIR2 W & A c=TARSKIR1 W"
sorry

mtheorem classes2_th_6:
" for A be OrdinalORDINAL1M3 holds  for W be setHIDDENM2 holds A inTARSKIR2 Tarski-ClassCLASSES1K1 W implies succORDINAL1K1 A inTARSKIR2 Tarski-ClassCLASSES1K1 W & A c=TARSKIR1 Tarski-ClassCLASSES1K1 W"
  using classes2_th_5 sorry

mtheorem classes2_th_7:
" for X be setHIDDENM2 holds  for W be setHIDDENM2 holds (W be subset-closedCLASSES1V1 & X be epsilon-transitiveORDINAL1V1) & X inTARSKIR2 W implies X c=TARSKIR1 W"
   sorry

mtheorem classes2_th_8:
" for X be setHIDDENM2 holds  for W be setHIDDENM2 holds X be epsilon-transitiveORDINAL1V1 & X inTARSKIR2 Tarski-ClassCLASSES1K1 W implies X c=TARSKIR1 Tarski-ClassCLASSES1K1 W"
  using classes2_th_7 sorry

mtheorem classes2_th_9:
" for W be setHIDDENM2 holds W be TarskiCLASSES1V2 implies OnORDINAL1K2 W =XBOOLE-0R4 cardCARD-1K1 W"
sorry

mtheorem classes2_th_10:
" for W be setHIDDENM2 holds OnORDINAL1K2 Tarski-ClassCLASSES1K1 W =XBOOLE-0R4 cardCARD-1K1 Tarski-ClassCLASSES1K1 W"
  using classes2_th_9 sorry

mtheorem classes2_th_11:
" for X be setHIDDENM2 holds  for W be setHIDDENM2 holds W be TarskiCLASSES1V2 & X inTARSKIR2 W implies cardCARD-1K1 X inTARSKIR2 W"
sorry

mtheorem classes2_th_12:
" for X be setHIDDENM2 holds  for W be setHIDDENM2 holds X inTARSKIR2 Tarski-ClassCLASSES1K1 W implies cardCARD-1K1 X inTARSKIR2 Tarski-ClassCLASSES1K1 W"
  using classes2_th_11 sorry

mtheorem classes2_th_13:
" for x be setHIDDENM2 holds  for W be setHIDDENM2 holds W be TarskiCLASSES1V2 & x inTARSKIR2 cardCARD-1K1 W implies x inTARSKIR2 W"
sorry

mtheorem classes2_th_14:
" for x be setHIDDENM2 holds  for W be setHIDDENM2 holds x inTARSKIR2 cardCARD-1K1 Tarski-ClassCLASSES1K1 W implies x inTARSKIR2 Tarski-ClassCLASSES1K1 W"
  using classes2_th_13 sorry

mtheorem classes2_th_15:
" for m be CardinalCARD-1M1 holds  for W be setHIDDENM2 holds W be TarskiCLASSES1V2 & m inTARSKIR2 cardCARD-1K1 W implies m inTARSKIR2 W"
sorry

mtheorem classes2_th_16:
" for m be CardinalCARD-1M1 holds  for W be setHIDDENM2 holds m inTARSKIR2 cardCARD-1K1 Tarski-ClassCLASSES1K1 W implies m inTARSKIR2 Tarski-ClassCLASSES1K1 W"
sorry

mtheorem classes2_th_17:
" for m be CardinalCARD-1M1 holds  for W be setHIDDENM2 holds W be TarskiCLASSES1V2 & m inTARSKIR2 W implies m c=TARSKIR1 W"
  using classes2_th_5 sorry

mtheorem classes2_th_18:
" for m be CardinalCARD-1M1 holds  for W be setHIDDENM2 holds m inTARSKIR2 Tarski-ClassCLASSES1K1 W implies m c=TARSKIR1 Tarski-ClassCLASSES1K1 W"
  using classes2_th_5 sorry

mtheorem classes2_th_19:
" for W be setHIDDENM2 holds W be TarskiCLASSES1V2 implies cardCARD-1K1 W be limit-ordinalORDINAL1V4"
sorry

mtheorem classes2_th_20:
" for W be setHIDDENM2 holds W be TarskiCLASSES1V2 & W <>HIDDENR2 {}XBOOLE-0K1 implies (cardCARD-1K1 W <>HIDDENR2 0NUMBERSK6 & cardCARD-1K1 W <>HIDDENR2 {}XBOOLE-0K1) & cardCARD-1K1 W be limit-ordinalORDINAL1V4"
  using classes2_th_19 sorry

mtheorem classes2_th_21:
" for W be setHIDDENM2 holds (cardCARD-1K1 Tarski-ClassCLASSES1K1 W <>HIDDENR2 0NUMBERSK6 & cardCARD-1K1 Tarski-ClassCLASSES1K1 W <>HIDDENR2 {}XBOOLE-0K1) & cardCARD-1K1 Tarski-ClassCLASSES1K1 W be limit-ordinalORDINAL1V4"
sorry

reserve f, g for "FunctionFUNCT-1M1"
reserve L for "SequenceORDINAL1M4"
reserve F for "Cardinal-FunctionCARD-3M1"
mtheorem classes2_th_22:
" for X be setHIDDENM2 holds  for W be setHIDDENM2 holds W be TarskiCLASSES1V2 & ((X inTARSKIR2 W & W be epsilon-transitiveORDINAL1V1 or X inTARSKIR2 W & X c=TARSKIR1 W) or cardCARD-1K1 X inTARSKIR2 cardCARD-1K1 W & X c=TARSKIR1 W) implies FuncsFUNCT-2K1(X,W) c=TARSKIR1 W"
sorry

mtheorem classes2_th_23:
" for X be setHIDDENM2 holds  for W be setHIDDENM2 holds (X inTARSKIR2 Tarski-ClassCLASSES1K1 W & W be epsilon-transitiveORDINAL1V1 or X inTARSKIR2 Tarski-ClassCLASSES1K1 W & X c=TARSKIR1 Tarski-ClassCLASSES1K1 W) or cardCARD-1K1 X inTARSKIR2 cardCARD-1K1 Tarski-ClassCLASSES1K1 W & X c=TARSKIR1 Tarski-ClassCLASSES1K1 W implies FuncsFUNCT-2K9(X,Tarski-ClassCLASSES1K1 W) c=TARSKIR1 Tarski-ClassCLASSES1K1 W"
sorry

mtheorem classes2_th_24:
" for L be SequenceORDINAL1M4 holds domRELAT-1K1 L be limit-ordinalORDINAL1V4 & ( for A be OrdinalORDINAL1M3 holds A inTARSKIR2 domRELAT-1K1 L implies L .FUNCT-1K1 A =XBOOLE-0R4 RankCLASSES1K4 A) implies RankCLASSES1K4 (domRELAT-1K1 L) =XBOOLE-0R4 UnionCARD-3K3 L"
sorry

mlemma classes2_lm_2:
"W be TarskiCLASSES1V2 & 0NUMBERSK6 inTARSKIR2 OnORDINAL1K2 W implies cardCARD-1K1 RankCLASSES1K4 (0NUMBERSK6) inTARSKIR2 cardCARD-1K1 W & RankCLASSES1K4 (0NUMBERSK6) inTARSKIR2 W"
  using classes2_th_9 classes1_th_29 ordinal1_def_9 sorry

mlemma classes2_lm_3:
" for A be OrdinalORDINAL1M3 holds (W be TarskiCLASSES1V2 & A inTARSKIR2 OnORDINAL1K2 W implies cardCARD-1K1 RankCLASSES1K4 A inTARSKIR2 cardCARD-1K1 W & RankCLASSES1K4 A inTARSKIR2 W) implies (W be TarskiCLASSES1V2 & succORDINAL1K1 A inTARSKIR2 OnORDINAL1K2 W implies cardCARD-1K1 RankCLASSES1K4 (succORDINAL1K1 A) inTARSKIR2 cardCARD-1K1 W & RankCLASSES1K4 (succORDINAL1K1 A) inTARSKIR2 W)"
sorry

mlemma classes2_lm_4:
" for A be OrdinalORDINAL1M3 holds (A <>HIDDENR2 0NUMBERSK6 & A be limit-ordinalORDINAL1V4) & ( for B be OrdinalORDINAL1M3 holds B inTARSKIR2 A implies (W be TarskiCLASSES1V2 & B inTARSKIR2 OnORDINAL1K2 W implies cardCARD-1K1 RankCLASSES1K4 B inTARSKIR2 cardCARD-1K1 W & RankCLASSES1K4 B inTARSKIR2 W)) implies (W be TarskiCLASSES1V2 & A inTARSKIR2 OnORDINAL1K2 W implies cardCARD-1K1 RankCLASSES1K4 A inTARSKIR2 cardCARD-1K1 W & RankCLASSES1K4 A inTARSKIR2 W)"
sorry

mtheorem classes2_th_25:
" for A be OrdinalORDINAL1M3 holds  for W be setHIDDENM2 holds W be TarskiCLASSES1V2 & A inTARSKIR2 OnORDINAL1K2 W implies cardCARD-1K1 RankCLASSES1K4 A inTARSKIR2 cardCARD-1K1 W & RankCLASSES1K4 A inTARSKIR2 W"
sorry

mtheorem classes2_th_26:
" for A be OrdinalORDINAL1M3 holds  for W be setHIDDENM2 holds A inTARSKIR2 OnORDINAL1K2 Tarski-ClassCLASSES1K1 W implies cardCARD-1K1 RankCLASSES1K4 A inTARSKIR2 cardCARD-1K1 Tarski-ClassCLASSES1K1 W & RankCLASSES1K4 A inTARSKIR2 Tarski-ClassCLASSES1K1 W"
  using classes2_th_25 sorry

mtheorem classes2_th_27:
" for W be setHIDDENM2 holds W be TarskiCLASSES1V2 implies RankCLASSES1K4 (cardCARD-1K1 W) c=TARSKIR1 W"
sorry

mtheorem classes2_th_28:
" for W be setHIDDENM2 holds RankCLASSES1K4 (cardCARD-1K1 Tarski-ClassCLASSES1K1 W) c=TARSKIR1 Tarski-ClassCLASSES1K1 W"
sorry

mtheorem classes2_th_29:
" for X be setHIDDENM2 holds  for W be setHIDDENM2 holds (W be TarskiCLASSES1V2 & W be epsilon-transitiveORDINAL1V1) & X inTARSKIR2 W implies the-rank-ofCLASSES1K7 X inTARSKIR2 W"
sorry

mtheorem classes2_th_30:
" for W be setHIDDENM2 holds W be TarskiCLASSES1V2 & W be epsilon-transitiveORDINAL1V1 implies W c=TARSKIR1 RankCLASSES1K4 (cardCARD-1K1 W)"
sorry

mtheorem classes2_th_31:
" for W be setHIDDENM2 holds W be TarskiCLASSES1V2 & W be epsilon-transitiveORDINAL1V1 implies RankCLASSES1K4 (cardCARD-1K1 W) =XBOOLE-0R4 W"
  using classes2_th_27 classes2_th_30 sorry

mtheorem classes2_th_32:
" for A be OrdinalORDINAL1M3 holds  for W be setHIDDENM2 holds W be TarskiCLASSES1V2 & A inTARSKIR2 OnORDINAL1K2 W implies cardCARD-1K1 RankCLASSES1K4 A c=ORDINAL1R1 cardCARD-1K1 W"
sorry

mtheorem classes2_th_33:
" for A be OrdinalORDINAL1M3 holds  for W be setHIDDENM2 holds A inTARSKIR2 OnORDINAL1K2 Tarski-ClassCLASSES1K1 W implies cardCARD-1K1 RankCLASSES1K4 A c=ORDINAL1R1 cardCARD-1K1 Tarski-ClassCLASSES1K1 W"
sorry

mtheorem classes2_th_34:
" for W be setHIDDENM2 holds W be TarskiCLASSES1V2 implies cardCARD-1K1 W =XBOOLE-0R4 cardCARD-1K1 RankCLASSES1K4 (cardCARD-1K1 W)"
sorry

mtheorem classes2_th_35:
" for W be setHIDDENM2 holds cardCARD-1K1 Tarski-ClassCLASSES1K1 W =XBOOLE-0R4 cardCARD-1K1 RankCLASSES1K4 (cardCARD-1K1 Tarski-ClassCLASSES1K1 W)"
  using classes2_th_34 sorry

mtheorem classes2_th_36:
" for X be setHIDDENM2 holds  for W be setHIDDENM2 holds W be TarskiCLASSES1V2 & X c=TARSKIR1 RankCLASSES1K4 (cardCARD-1K1 W) implies (X,RankCLASSES1K4 (cardCARD-1K1 W))are-equipotentTARSKIR3 or X inTARSKIR2 RankCLASSES1K4 (cardCARD-1K1 W)"
sorry

mtheorem classes2_th_37:
" for X be setHIDDENM2 holds  for W be setHIDDENM2 holds X c=TARSKIR1 RankCLASSES1K4 (cardCARD-1K1 Tarski-ClassCLASSES1K1 W) implies (X,RankCLASSES1K4 (cardCARD-1K1 Tarski-ClassCLASSES1K1 W))are-equipotentTARSKIR3 or X inTARSKIR2 RankCLASSES1K4 (cardCARD-1K1 Tarski-ClassCLASSES1K1 W)"
  using classes2_th_36 sorry

mtheorem classes2_th_38:
" for W be setHIDDENM2 holds W be TarskiCLASSES1V2 implies RankCLASSES1K4 (cardCARD-1K1 W) be TarskiCLASSES1V2"
sorry

mtheorem classes2_th_39:
" for W be setHIDDENM2 holds RankCLASSES1K4 (cardCARD-1K1 Tarski-ClassCLASSES1K1 W) be TarskiCLASSES1V2"
  using classes2_th_38 sorry

mtheorem classes2_th_40:
" for A be OrdinalORDINAL1M3 holds  for X be setHIDDENM2 holds X be epsilon-transitiveORDINAL1V1 & A inTARSKIR2 the-rank-ofCLASSES1K7 X implies ( ex Y be setHIDDENM2 st Y inTARSKIR2 X & the-rank-ofCLASSES1K7 Y =XBOOLE-0R4 A)"
sorry

mtheorem classes2_th_41:
" for X be setHIDDENM2 holds X be epsilon-transitiveORDINAL1V1 implies cardCARD-1K1 the-rank-ofCLASSES1K7 X c=ORDINAL1R1 cardCARD-1K1 X"
sorry

mtheorem classes2_th_42:
" for X be setHIDDENM2 holds  for W be setHIDDENM2 holds (W be TarskiCLASSES1V2 & X be epsilon-transitiveORDINAL1V1) & X inTARSKIR2 W implies X inTARSKIR2 RankCLASSES1K4 (cardCARD-1K1 W)"
sorry

mtheorem classes2_th_43:
" for X be setHIDDENM2 holds  for W be setHIDDENM2 holds X be epsilon-transitiveORDINAL1V1 & X inTARSKIR2 Tarski-ClassCLASSES1K1 W implies X inTARSKIR2 RankCLASSES1K4 (cardCARD-1K1 Tarski-ClassCLASSES1K1 W)"
  using classes2_th_42 sorry

mtheorem classes2_th_44:
" for W be setHIDDENM2 holds W be epsilon-transitiveORDINAL1V1 implies RankCLASSES1K4 (cardCARD-1K1 Tarski-ClassCLASSES1K1 W) is-Tarski-Class-ofCLASSES1R1 W"
  using classes1_th_2 classes2_th_38 classes2_th_42 sorry

mtheorem classes2_th_45:
" for W be setHIDDENM2 holds W be epsilon-transitiveORDINAL1V1 implies RankCLASSES1K4 (cardCARD-1K1 Tarski-ClassCLASSES1K1 W) =XBOOLE-0R4 Tarski-ClassCLASSES1K1 W"
sorry

mdef classes2_def_1 ("universalCLASSES2V1" 70 ) where
"attr universalCLASSES2V1 for setHIDDENM2 means
  (\<lambda>IT. IT be epsilon-transitiveORDINAL1V1 & IT be TarskiCLASSES1V2)"..

mtheorem classes2_cl_3:
"cluster universalCLASSES2V1 also-is epsilon-transitiveORDINAL1V1\<bar>TarskiCLASSES1V2 for setHIDDENM2"
proof
(*coherence*)
  show " for it be setHIDDENM2 holds it be universalCLASSES2V1 implies it be epsilon-transitiveORDINAL1V1\<bar>TarskiCLASSES1V2"
     sorry
qed "sorry"

mtheorem classes2_cl_4:
"cluster epsilon-transitiveORDINAL1V1\<bar>TarskiCLASSES1V2 also-is universalCLASSES2V1 for setHIDDENM2"
proof
(*coherence*)
  show " for it be setHIDDENM2 holds it be epsilon-transitiveORDINAL1V1\<bar>TarskiCLASSES1V2 implies it be universalCLASSES2V1"
     sorry
qed "sorry"

mtheorem classes2_cl_5:
"cluster universalCLASSES2V1\<bar> non emptyXBOOLE-0V1 for setHIDDENM2"
proof
(*existence*)
  show " ex it be setHIDDENM2 st it be universalCLASSES2V1\<bar> non emptyXBOOLE-0V1"
sorry
qed "sorry"

syntax CLASSES2M1 :: "Ty" ("UniverseCLASSES2M1" 70)
translations "UniverseCLASSES2M1" \<rightharpoonup> "universalCLASSES2V1\<bar> non emptyXBOOLE-0V1\<bar>setHIDDENM2"

reserve U1, U2, U for "UniverseCLASSES2M1"
mtheorem classes2_th_46:
" for U be UniverseCLASSES2M1 holds OnORDINAL1K2 U be OrdinalORDINAL1M3"
sorry

mtheorem classes2_th_47:
" for X be setHIDDENM2 holds X be epsilon-transitiveORDINAL1V1 implies Tarski-ClassCLASSES1K1 X be universalCLASSES2V1"
  using classes1_th_23 sorry

mtheorem classes2_th_48:
" for U be UniverseCLASSES2M1 holds Tarski-ClassCLASSES1K1 U be UniverseCLASSES2M1"
  using classes2_th_47 sorry

mtheorem classes2_cl_6:
  mlet "U be UniverseCLASSES2M1"
"cluster OnORDINAL1K2 U as-term-is ordinalORDINAL1V3"
proof
(*coherence*)
  show "OnORDINAL1K2 U be ordinalORDINAL1V3"
    using classes2_th_46 sorry
qed "sorry"

mtheorem classes2_cl_7:
  mlet "U be UniverseCLASSES2M1"
"cluster Tarski-ClassCLASSES1K1 U as-term-is universalCLASSES2V1"
proof
(*coherence*)
  show "Tarski-ClassCLASSES1K1 U be universalCLASSES2V1"
    using classes2_th_47 sorry
qed "sorry"

mtheorem classes2_th_49:
" for A be OrdinalORDINAL1M3 holds Tarski-ClassCLASSES1K1 A be universalCLASSES2V1"
  using classes1_th_23 sorry

mtheorem classes2_cl_8:
  mlet "A be OrdinalORDINAL1M3"
"cluster Tarski-ClassCLASSES1K1 A as-term-is universalCLASSES2V1"
proof
(*coherence*)
  show "Tarski-ClassCLASSES1K1 A be universalCLASSES2V1"
    using classes2_th_49 sorry
qed "sorry"

mtheorem classes2_th_50:
" for U be UniverseCLASSES2M1 holds U =XBOOLE-0R4 RankCLASSES1K4 (OnORDINAL1K2 U)"
sorry

mtheorem classes2_th_51:
" for U be UniverseCLASSES2M1 holds OnORDINAL1K2 U <>HIDDENR2 {}XBOOLE-0K1 & OnORDINAL1K2 U be limit-ordinalORDINAL1V4"
sorry

mtheorem classes2_th_52:
" for U1 be UniverseCLASSES2M1 holds  for U2 be UniverseCLASSES2M1 holds (U1 inTARSKIR2 U2 or U1 =XBOOLE-0R4 U2) or U2 inTARSKIR2 U1"
sorry

mtheorem classes2_th_53:
" for U1 be UniverseCLASSES2M1 holds  for U2 be UniverseCLASSES2M1 holds U1 c=TARSKIR1 U2 or U2 inTARSKIR2 U1"
sorry

mtheorem classes2_th_54:
" for U1 be UniverseCLASSES2M1 holds  for U2 be UniverseCLASSES2M1 holds (U1,U2)are-c=-comparableXBOOLE-0R3"
sorry

mtheorem classes2_th_55:
" for U1 be UniverseCLASSES2M1 holds  for U2 be UniverseCLASSES2M1 holds U1 \\/XBOOLE-0K2 U2 be UniverseCLASSES2M1 & U1 /\\XBOOLE-0K3 U2 be UniverseCLASSES2M1"
sorry

mtheorem classes2_th_56:
" for U be UniverseCLASSES2M1 holds {}XBOOLE-0K1 inTARSKIR2 U"
sorry

mtheorem classes2_th_57:
" for x be setHIDDENM2 holds  for U be UniverseCLASSES2M1 holds x inTARSKIR2 U implies {TARSKIK1 x} inTARSKIR2 U"
  using classes2_th_2 sorry

mtheorem classes2_th_58:
" for x be setHIDDENM2 holds  for y be setHIDDENM2 holds  for U be UniverseCLASSES2M1 holds x inTARSKIR2 U & y inTARSKIR2 U implies {TARSKIK2 x,y } inTARSKIR2 U & [TARSKIK4 x,y ] inHIDDENR3 U"
  using classes2_th_2 classes2_th_3 sorry

mtheorem classes2_th_59:
" for X be setHIDDENM2 holds  for U be UniverseCLASSES2M1 holds X inTARSKIR2 U implies (boolSETFAM-1K9 X inTARSKIR2 U & unionTARSKIK3 X inTARSKIR2 U) & meetSETFAM-1K1 X inTARSKIR2 U"
sorry

mtheorem classes2_th_60:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for U be UniverseCLASSES2M1 holds X inTARSKIR2 U & Y inTARSKIR2 U implies ((X \\/XBOOLE-0K2 Y inTARSKIR2 U & X /\\XBOOLE-0K3 Y inTARSKIR2 U) & X \\SUBSET-1K6 Y inTARSKIR2 U) & X \\+\\XBOOLE-0K5 Y inTARSKIR2 U"
sorry

mtheorem classes2_th_61:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for U be UniverseCLASSES2M1 holds X inTARSKIR2 U & Y inTARSKIR2 U implies [:ZFMISC-1K2 X,Y :] inTARSKIR2 U & FuncsFUNCT-2K1(X,Y) inTARSKIR2 U"
sorry

reserve u, v for "ElementSUBSET-1M1-of U"
mtheorem classes2_cl_9:
  mlet "U1 be UniverseCLASSES2M1"
"cluster  non emptyXBOOLE-0V1 for ElementSUBSET-1M1-of U1"
proof
(*existence*)
  show " ex it be ElementSUBSET-1M1-of U1 st it be  non emptyXBOOLE-0V1"
sorry
qed "sorry"

syntax CLASSES2K1 :: " Set \<Rightarrow>  Set \<Rightarrow> Set" ("{CLASSES2K1\<^bsub>'( _ ')\<^esub>  _ }" [0,0]356)
translations "{CLASSES2K1\<^bsub>(U)\<^esub> u}" \<rightharpoonup> "{TARSKIK1 u}"

mtheorem classes2_add_1:
  mlet "U be UniverseCLASSES2M1", "u be ElementSUBSET-1M1-of U"
"cluster {TARSKIK1 u} as-term-is ElementSUBSET-1M1-of U"
proof
(*coherence*)
  show "{TARSKIK1 u} be ElementSUBSET-1M1-of U"
    using classes2_th_2 sorry
qed "sorry"

syntax CLASSES2K2 :: " Set \<Rightarrow>  Set \<Rightarrow> Set" ("boolCLASSES2K2\<^bsub>'( _ ')\<^esub>  _ " [0,228]228)
translations "boolCLASSES2K2\<^bsub>(U)\<^esub> u" \<rightharpoonup> "boolZFMISC-1K1 u"

mtheorem classes2_add_2:
  mlet "U be UniverseCLASSES2M1", "u be ElementSUBSET-1M1-of U"
"cluster boolZFMISC-1K1 u as-term-is ElementSUBSET-1M1-of U"
proof
(*coherence*)
  show "boolZFMISC-1K1 u be ElementSUBSET-1M1-of U"
    using classes2_th_59 sorry
qed "sorry"

syntax CLASSES2K3 :: " Set \<Rightarrow>  Set \<Rightarrow> Set" ("unionCLASSES2K3\<^bsub>'( _ ')\<^esub>  _ " [0,228]228)
translations "unionCLASSES2K3\<^bsub>(U)\<^esub> u" \<rightharpoonup> "unionTARSKIK3 u"

mtheorem classes2_add_3:
  mlet "U be UniverseCLASSES2M1", "u be ElementSUBSET-1M1-of U"
"cluster unionTARSKIK3 u as-term-is ElementSUBSET-1M1-of U"
proof
(*coherence*)
  show "unionTARSKIK3 u be ElementSUBSET-1M1-of U"
    using classes2_th_59 sorry
qed "sorry"

syntax CLASSES2K4 :: " Set \<Rightarrow>  Set \<Rightarrow> Set" ("meetCLASSES2K4\<^bsub>'( _ ')\<^esub>  _ " [0,228]228)
translations "meetCLASSES2K4\<^bsub>(U)\<^esub> u" \<rightharpoonup> "meetSETFAM-1K1 u"

mtheorem classes2_add_4:
  mlet "U be UniverseCLASSES2M1", "u be ElementSUBSET-1M1-of U"
"cluster meetSETFAM-1K1 u as-term-is ElementSUBSET-1M1-of U"
proof
(*coherence*)
  show "meetSETFAM-1K1 u be ElementSUBSET-1M1-of U"
    using classes2_th_59 sorry
qed "sorry"

syntax CLASSES2K5 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" ("{CLASSES2K5\<^bsub>'( _ ')\<^esub> _ , _ }" [0,0,0]356)
translations "{CLASSES2K5\<^bsub>(U)\<^esub> u,v }" \<rightharpoonup> "{TARSKIK2 u,v }"

mtheorem classes2_add_5:
  mlet "U be UniverseCLASSES2M1", "u be ElementSUBSET-1M1-of U", "v be ElementSUBSET-1M1-of U"
"cluster {TARSKIK2 u,v } as-term-is ElementSUBSET-1M1-of U"
proof
(*coherence*)
  show "{TARSKIK2 u,v } be ElementSUBSET-1M1-of U"
    using classes2_th_2 sorry
qed "sorry"

syntax CLASSES2K6 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" ("[CLASSES2K6\<^bsub>'( _ ')\<^esub> _ , _ ]" [0,0,0]356)
translations "[CLASSES2K6\<^bsub>(U)\<^esub> u,v ]" \<rightharpoonup> "[TARSKIK4 u,v ]"

mtheorem classes2_add_6:
  mlet "U be UniverseCLASSES2M1", "u be ElementSUBSET-1M1-of U", "v be ElementSUBSET-1M1-of U"
"cluster [TARSKIK4 u,v ] as-term-is ElementSUBSET-1M1-of U"
proof
(*coherence*)
  show "[TARSKIK4 u,v ] be ElementSUBSET-1M1-of U"
    using classes2_th_3 sorry
qed "sorry"

syntax CLASSES2K7 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ '\\'/CLASSES2K7\<^bsub>'( _ ')\<^esub>  _ " [132,0,132]132)
translations "u \\/CLASSES2K7\<^bsub>(U)\<^esub> v" \<rightharpoonup> "u \\/XBOOLE-0K2 v"

mtheorem classes2_add_7:
  mlet "U be UniverseCLASSES2M1", "u be ElementSUBSET-1M1-of U", "v be ElementSUBSET-1M1-of U"
"cluster u \\/XBOOLE-0K2 v as-term-is ElementSUBSET-1M1-of U"
proof
(*coherence*)
  show "u \\/XBOOLE-0K2 v be ElementSUBSET-1M1-of U"
    using classes2_th_60 sorry
qed "sorry"

syntax CLASSES2K8 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ '/'\\CLASSES2K8\<^bsub>'( _ ')\<^esub>  _ " [164,0,164]164)
translations "u /\\CLASSES2K8\<^bsub>(U)\<^esub> v" \<rightharpoonup> "u /\\XBOOLE-0K3 v"

mtheorem classes2_add_8:
  mlet "U be UniverseCLASSES2M1", "u be ElementSUBSET-1M1-of U", "v be ElementSUBSET-1M1-of U"
"cluster u /\\XBOOLE-0K3 v as-term-is ElementSUBSET-1M1-of U"
proof
(*coherence*)
  show "u /\\XBOOLE-0K3 v be ElementSUBSET-1M1-of U"
    using classes2_th_60 sorry
qed "sorry"

syntax CLASSES2K9 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ '\\CLASSES2K9\<^bsub>'( _ ')\<^esub>  _ " [132,0,132]132)
translations "u \\CLASSES2K9\<^bsub>(U)\<^esub> v" \<rightharpoonup> "u \\XBOOLE-0K4 v"

mtheorem classes2_add_9:
  mlet "U be UniverseCLASSES2M1", "u be ElementSUBSET-1M1-of U", "v be ElementSUBSET-1M1-of U"
"cluster u \\XBOOLE-0K4 v as-term-is ElementSUBSET-1M1-of U"
proof
(*coherence*)
  show "u \\XBOOLE-0K4 v be ElementSUBSET-1M1-of U"
    using classes2_th_60 sorry
qed "sorry"

syntax CLASSES2K10 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ '\\+'\\CLASSES2K10\<^bsub>'( _ ')\<^esub>  _ " [130,0,130]130)
translations "u \\+\\CLASSES2K10\<^bsub>(U)\<^esub> v" \<rightharpoonup> "u \\+\\XBOOLE-0K5 v"

mtheorem classes2_add_10:
  mlet "U be UniverseCLASSES2M1", "u be ElementSUBSET-1M1-of U", "v be ElementSUBSET-1M1-of U"
"cluster u \\+\\XBOOLE-0K5 v as-term-is ElementSUBSET-1M1-of U"
proof
(*coherence*)
  show "u \\+\\XBOOLE-0K5 v be ElementSUBSET-1M1-of U"
    using classes2_th_60 sorry
qed "sorry"

syntax CLASSES2K11 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" ("[:CLASSES2K11\<^bsub>'( _ ')\<^esub> _ , _ :]" [0,0,0]164)
translations "[:CLASSES2K11\<^bsub>(U)\<^esub> u,v :]" \<rightharpoonup> "[:ZFMISC-1K2 u,v :]"

mtheorem classes2_add_11:
  mlet "U be UniverseCLASSES2M1", "u be ElementSUBSET-1M1-of U", "v be ElementSUBSET-1M1-of U"
"cluster [:ZFMISC-1K2 u,v :] as-term-is ElementSUBSET-1M1-of U"
proof
(*coherence*)
  show "[:ZFMISC-1K2 u,v :] be ElementSUBSET-1M1-of U"
    using classes2_th_61 sorry
qed "sorry"

syntax CLASSES2K12 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" ("FuncsCLASSES2K12\<^bsub>'( _ ')\<^esub>'( _ , _ ')" [0,0,0]228)
translations "FuncsCLASSES2K12\<^bsub>(U)\<^esub>(u,v)" \<rightharpoonup> "FuncsFUNCT-2K1(u,v)"

mtheorem classes2_add_12:
  mlet "U be UniverseCLASSES2M1", "u be ElementSUBSET-1M1-of U", "v be ElementSUBSET-1M1-of U"
"cluster FuncsFUNCT-2K1(u,v) as-term-is ElementSUBSET-1M1-of U"
proof
(*coherence*)
  show "FuncsFUNCT-2K1(u,v) be ElementSUBSET-1M1-of U"
    using classes2_th_61 sorry
qed "sorry"

mdef classes2_def_2 ("FinSETSCLASSES2K13" 300 ) where
"func FinSETSCLASSES2K13 \<rightarrow> UniverseCLASSES2M1 equals
  Tarski-ClassCLASSES1K1 ({}XBOOLE-0K1)"
proof-
  (*coherence*)
    show "Tarski-ClassCLASSES1K1 ({}XBOOLE-0K1) be UniverseCLASSES2M1"
       sorry
qed "sorry"

mlemma classes2_lm_5:
"omegaORDINAL1K4 be limit-ordinalORDINAL1V4"
  using ordinal1_def_11 sorry

mtheorem classes2_th_62:
"cardCARD-1K1 RankCLASSES1K4 (omegaORDINAL1K4) =XBOOLE-0R4 cardCARD-1K1 (omegaORDINAL1K4)"
sorry

mtheorem classes2_th_63:
"RankCLASSES1K4 (omegaORDINAL1K4) be TarskiCLASSES1V2"
sorry

mtheorem classes2_th_64:
"FinSETSCLASSES2K13 =XBOOLE-0R4 RankCLASSES1K4 (omegaORDINAL1K4)"
sorry

mdef classes2_def_3 ("SETSCLASSES2K14" 300 ) where
"func SETSCLASSES2K14 \<rightarrow> UniverseCLASSES2M1 equals
  Tarski-ClassCLASSES1K1 (FinSETSCLASSES2K13)"
proof-
  (*coherence*)
    show "Tarski-ClassCLASSES1K1 (FinSETSCLASSES2K13) be UniverseCLASSES2M1"
       sorry
qed "sorry"

mtheorem classes2_cl_10:
  mlet "X be setHIDDENM2"
"cluster the-transitive-closure-ofCLASSES1K5 X as-term-is epsilon-transitiveORDINAL1V1"
proof
(*coherence*)
  show "the-transitive-closure-ofCLASSES1K5 X be epsilon-transitiveORDINAL1V1"
     sorry
qed "sorry"

mtheorem classes2_cl_11:
  mlet "X be epsilon-transitiveORDINAL1V1\<bar>setHIDDENM2"
"cluster Tarski-ClassCLASSES1K1 X as-term-is epsilon-transitiveORDINAL1V1"
proof
(*coherence*)
  show "Tarski-ClassCLASSES1K1 X be epsilon-transitiveORDINAL1V1"
    using classes1_th_23 sorry
qed "sorry"

mdef classes2_def_4 ("Universe-closureCLASSES2K15  _ " [164]164 ) where
  mlet "X be setHIDDENM2"
"func Universe-closureCLASSES2K15 X \<rightarrow> UniverseCLASSES2M1 means
  \<lambda>it. X c=TARSKIR1 it & ( for Y be UniverseCLASSES2M1 holds X c=TARSKIR1 Y implies it c=TARSKIR1 Y)"
proof-
  (*uniqueness*)
    show " for it1 be UniverseCLASSES2M1 holds  for it2 be UniverseCLASSES2M1 holds (X c=TARSKIR1 it1 & ( for Y be UniverseCLASSES2M1 holds X c=TARSKIR1 Y implies it1 c=TARSKIR1 Y)) & (X c=TARSKIR1 it2 & ( for Y be UniverseCLASSES2M1 holds X c=TARSKIR1 Y implies it2 c=TARSKIR1 Y)) implies it1 =HIDDENR1 it2"
       sorry
  (*existence*)
    show " ex it be UniverseCLASSES2M1 st X c=TARSKIR1 it & ( for Y be UniverseCLASSES2M1 holds X c=TARSKIR1 Y implies it c=TARSKIR1 Y)"
sorry
qed "sorry"

syntax CLASSES2M2 :: "Ty" ("FinSetCLASSES2M2" 70)
translations "FinSetCLASSES2M2" \<rightharpoonup> "ElementSUBSET-1M1-of FinSETSCLASSES2K13"

syntax CLASSES2M3 :: "Ty" ("SetCLASSES2M3" 70)
translations "SetCLASSES2M3" \<rightharpoonup> "ElementSUBSET-1M1-of SETSCLASSES2K14"

mdef classes2_def_5 ("UNIVERSECLASSES2K16  _ " [164]164 ) where
  mlet "A be OrdinalORDINAL1M3"
"func UNIVERSECLASSES2K16 A \<rightarrow> setHIDDENM2 means
  \<lambda>it.  ex L be SequenceORDINAL1M4 st (((it =XBOOLE-0R4 lastORDINAL2K1 L & domRELAT-1K1 L =XBOOLE-0R4 succORDINAL1K1 A) & L .FUNCT-1K1 (0NUMBERSK6) =XBOOLE-0R4 FinSETSCLASSES2K13) & ( for C be OrdinalORDINAL1M3 holds succORDINAL1K1 C inTARSKIR2 succORDINAL1K1 A implies L .FUNCT-1K1 succORDINAL1K1 C =XBOOLE-0R4 Tarski-ClassCLASSES1K1 (L .FUNCT-1K1 C))) & ( for C be OrdinalORDINAL1M3 holds (C inTARSKIR2 succORDINAL1K1 A & C <>HIDDENR2 0NUMBERSK6) & C be limit-ordinalORDINAL1V4 implies L .FUNCT-1K1 C =XBOOLE-0R4 Universe-closureCLASSES2K15 (UnionCARD-3K3 L |RELAT-1K8 C))"
proof-
  (*existence*)
    show " ex it be setHIDDENM2 st  ex L be SequenceORDINAL1M4 st (((it =XBOOLE-0R4 lastORDINAL2K1 L & domRELAT-1K1 L =XBOOLE-0R4 succORDINAL1K1 A) & L .FUNCT-1K1 (0NUMBERSK6) =XBOOLE-0R4 FinSETSCLASSES2K13) & ( for C be OrdinalORDINAL1M3 holds succORDINAL1K1 C inTARSKIR2 succORDINAL1K1 A implies L .FUNCT-1K1 succORDINAL1K1 C =XBOOLE-0R4 Tarski-ClassCLASSES1K1 (L .FUNCT-1K1 C))) & ( for C be OrdinalORDINAL1M3 holds (C inTARSKIR2 succORDINAL1K1 A & C <>HIDDENR2 0NUMBERSK6) & C be limit-ordinalORDINAL1V4 implies L .FUNCT-1K1 C =XBOOLE-0R4 Universe-closureCLASSES2K15 (UnionCARD-3K3 L |RELAT-1K8 C))"
sorry
  (*uniqueness*)
    show " for it1 be setHIDDENM2 holds  for it2 be setHIDDENM2 holds ( ex L be SequenceORDINAL1M4 st (((it1 =XBOOLE-0R4 lastORDINAL2K1 L & domRELAT-1K1 L =XBOOLE-0R4 succORDINAL1K1 A) & L .FUNCT-1K1 (0NUMBERSK6) =XBOOLE-0R4 FinSETSCLASSES2K13) & ( for C be OrdinalORDINAL1M3 holds succORDINAL1K1 C inTARSKIR2 succORDINAL1K1 A implies L .FUNCT-1K1 succORDINAL1K1 C =XBOOLE-0R4 Tarski-ClassCLASSES1K1 (L .FUNCT-1K1 C))) & ( for C be OrdinalORDINAL1M3 holds (C inTARSKIR2 succORDINAL1K1 A & C <>HIDDENR2 0NUMBERSK6) & C be limit-ordinalORDINAL1V4 implies L .FUNCT-1K1 C =XBOOLE-0R4 Universe-closureCLASSES2K15 (UnionCARD-3K3 L |RELAT-1K8 C))) & ( ex L be SequenceORDINAL1M4 st (((it2 =XBOOLE-0R4 lastORDINAL2K1 L & domRELAT-1K1 L =XBOOLE-0R4 succORDINAL1K1 A) & L .FUNCT-1K1 (0NUMBERSK6) =XBOOLE-0R4 FinSETSCLASSES2K13) & ( for C be OrdinalORDINAL1M3 holds succORDINAL1K1 C inTARSKIR2 succORDINAL1K1 A implies L .FUNCT-1K1 succORDINAL1K1 C =XBOOLE-0R4 Tarski-ClassCLASSES1K1 (L .FUNCT-1K1 C))) & ( for C be OrdinalORDINAL1M3 holds (C inTARSKIR2 succORDINAL1K1 A & C <>HIDDENR2 0NUMBERSK6) & C be limit-ordinalORDINAL1V4 implies L .FUNCT-1K1 C =XBOOLE-0R4 Universe-closureCLASSES2K15 (UnionCARD-3K3 L |RELAT-1K8 C))) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mlemma classes2_lm_6:
"UNIVERSECLASSES2K16 (0NUMBERSK6) =XBOOLE-0R4 FinSETSCLASSES2K13 & (( for A be OrdinalORDINAL1M3 holds UNIVERSECLASSES2K16 succORDINAL1K1 A =XBOOLE-0R4 Tarski-ClassCLASSES1K1 (UNIVERSECLASSES2K16 A)) & ( for A be OrdinalORDINAL1M3 holds  for L be SequenceORDINAL1M4 holds (A <>HIDDENR2 0NUMBERSK6 & A be limit-ordinalORDINAL1V4) & (domRELAT-1K1 L =XBOOLE-0R4 A & ( for B be OrdinalORDINAL1M3 holds B inTARSKIR2 A implies L .FUNCT-1K1 B =XBOOLE-0R4 UNIVERSECLASSES2K16 B)) implies UNIVERSECLASSES2K16 A =XBOOLE-0R4 Universe-closureCLASSES2K15 (UnionCARD-3K3 L)))"
sorry

mtheorem classes2_cl_12:
  mlet "A be OrdinalORDINAL1M3"
"cluster UNIVERSECLASSES2K16 A as-term-is universalCLASSES2V1\<bar> non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "UNIVERSECLASSES2K16 A be universalCLASSES2V1\<bar> non emptyXBOOLE-0V1"
sorry
qed "sorry"

mtheorem classes2_th_65:
"UNIVERSECLASSES2K16 {}XBOOLE-0K1 =XBOOLE-0R4 FinSETSCLASSES2K13"
  using classes2_lm_6 sorry

mtheorem classes2_th_66:
" for A be OrdinalORDINAL1M3 holds UNIVERSECLASSES2K16 succORDINAL1K1 A =XBOOLE-0R4 Tarski-ClassCLASSES1K1 (UNIVERSECLASSES2K16 A)"
  using classes2_lm_6 sorry

mlemma classes2_lm_7:
"\<one>\<^sub>M =XBOOLE-0R4 succORDINAL1K1 (0NUMBERSK6)"
   sorry

mtheorem classes2_th_67:
"UNIVERSECLASSES2K16 \<one>\<^sub>M =XBOOLE-0R4 SETSCLASSES2K14"
  using classes2_lm_6 classes2_lm_7 sorry

mtheorem classes2_th_68:
" for A be OrdinalORDINAL1M3 holds  for L be SequenceORDINAL1M4 holds ((A <>HIDDENR2 {}XBOOLE-0K1 & A be limit-ordinalORDINAL1V4) & domRELAT-1K1 L =XBOOLE-0R4 A) & ( for B be OrdinalORDINAL1M3 holds B inTARSKIR2 A implies L .FUNCT-1K1 B =XBOOLE-0R4 UNIVERSECLASSES2K16 B) implies UNIVERSECLASSES2K16 A =XBOOLE-0R4 Universe-closureCLASSES2K15 (UnionCARD-3K3 L)"
  using classes2_lm_6 sorry

mtheorem classes2_th_69:
" for U be UniverseCLASSES2M1 holds (FinSETSCLASSES2K13 c=TARSKIR1 U & Tarski-ClassCLASSES1K1 ({}XBOOLE-0K1) c=TARSKIR1 U) & UNIVERSECLASSES2K16 {}XBOOLE-0K1 c=TARSKIR1 U"
sorry

mtheorem classes2_th_70:
" for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds A inTARSKIR2 B iff UNIVERSECLASSES2K16 A inTARSKIR2 UNIVERSECLASSES2K16 B"
sorry

mtheorem classes2_th_71:
" for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds UNIVERSECLASSES2K16 A =XBOOLE-0R4 UNIVERSECLASSES2K16 B implies A =XBOOLE-0R4 B"
sorry

mtheorem classes2_th_72:
" for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds A c=ORDINAL1R1 B iff UNIVERSECLASSES2K16 A c=TARSKIR1 UNIVERSECLASSES2K16 B"
sorry

reserve u, v for "ElementSUBSET-1M1-of Tarski-ClassCLASSES1K1 X"
mtheorem classes2_th_73:
" for X be setHIDDENM2 holds Tarski-ClassCLASSES1K3(X,{}XBOOLE-0K1) inTARSKIR2 Tarski-ClassCLASSES1K3(X,\<one>\<^sub>M) & Tarski-ClassCLASSES1K3(X,{}XBOOLE-0K1) <>HIDDENR2 Tarski-ClassCLASSES1K3(X,\<one>\<^sub>M)"
sorry

end
