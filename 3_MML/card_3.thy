theory card_3
  imports wellord1 finsub_1 pboole funct_5 grfunc_1 ordinal3
   "../mizar_extension/E_number"
begin
(*begin*)
reserve A, B, C for "OrdinalORDINAL1M3"
reserve K, L, M, N for "CardinalCARD-1M1"
reserve x, y, y1, y2, z, u for "objectHIDDENM1"
reserve X, Y, Z, Z1, Z2 for "setHIDDENM2"
reserve f, f1, g, h for "FunctionFUNCT-1M1"
reserve Q, R for "RelationRELAT-1M1"
mdef card_3_def_1 ("Cardinal-yieldingCARD-3V1" 70 ) where
"attr Cardinal-yieldingCARD-3V1 for FunctionFUNCT-1M1 means
  (\<lambda>IT.  for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 IT implies IT .FUNCT-1K1 x be CardinalCARD-1M1)"..

mtheorem card_3_cl_1:
"cluster emptyXBOOLE-0V1 also-is Cardinal-yieldingCARD-3V1 for FunctionFUNCT-1M1"
proof
(*coherence*)
  show " for it be FunctionFUNCT-1M1 holds it be emptyXBOOLE-0V1 implies it be Cardinal-yieldingCARD-3V1"
     sorry
qed "sorry"

mtheorem card_3_cl_2:
"cluster Cardinal-yieldingCARD-3V1 for FunctionFUNCT-1M1"
proof
(*existence*)
  show " ex it be FunctionFUNCT-1M1 st it be Cardinal-yieldingCARD-3V1"
sorry
qed "sorry"

syntax CARD_3M1 :: "Ty" ("Cardinal-FunctionCARD-3M1" 70)
translations "Cardinal-FunctionCARD-3M1" \<rightharpoonup> "Cardinal-yieldingCARD-3V1\<bar>FunctionFUNCT-1M1"

reserve ff for "Cardinal-FunctionCARD-3M1"
mtheorem card_3_cl_3:
  mlet "ff be Cardinal-FunctionCARD-3M1", "X be setHIDDENM2"
"cluster ff |RELAT-1K8 X as-term-is Cardinal-yieldingCARD-3V1"
proof
(*coherence*)
  show "ff |RELAT-1K8 X be Cardinal-yieldingCARD-3V1"
sorry
qed "sorry"

mtheorem card_3_cl_4:
  mlet "X be setHIDDENM2", "K be CardinalCARD-1M1"
"cluster X -->FUNCOP-1K7 K as-term-is Cardinal-yieldingCARD-3V1"
proof
(*coherence*)
  show "X -->FUNCOP-1K7 K be Cardinal-yieldingCARD-3V1"
sorry
qed "sorry"

mtheorem card_3_cl_5:
  mlet "X be objectHIDDENM1", "K be CardinalCARD-1M1"
"cluster X .-->FUNCOP-1K17 K as-term-is Cardinal-yieldingCARD-3V1"
proof
(*coherence*)
  show "X .-->FUNCOP-1K17 K be Cardinal-yieldingCARD-3V1"
     sorry
qed "sorry"

theorem card_3_sch_1:
  fixes Af0 Ff1 
  assumes
[ty]: "Af0 be setHIDDENM2" and
  [ty_func]: "\<And> x1. x1 be objectHIDDENM1 \<Longrightarrow> Ff1(x1) be CardinalCARD-1M1"
  shows " ex ff be Cardinal-FunctionCARD-3M1 st domRELAT-1K1 ff =XBOOLE-0R4 Af0 & ( for x be setHIDDENM2 holds x inTARSKIR2 Af0 implies ff .FUNCT-1K1 x =XBOOLE-0R4 Ff1(x))"
sorry

mdef card_3_def_2 ("CardCARD-3K1  _ " [228]228 ) where
  mlet "f be FunctionFUNCT-1M1"
"func CardCARD-3K1 f \<rightarrow> Cardinal-FunctionCARD-3M1 means
  \<lambda>it. domRELAT-1K1 it =XBOOLE-0R4 domRELAT-1K1 f & ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 f implies it .FUNCT-1K1 x =XBOOLE-0R4 cardCARD-1K1 (f .FUNCT-1K1 x))"
proof-
  (*existence*)
    show " ex it be Cardinal-FunctionCARD-3M1 st domRELAT-1K1 it =XBOOLE-0R4 domRELAT-1K1 f & ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 f implies it .FUNCT-1K1 x =XBOOLE-0R4 cardCARD-1K1 (f .FUNCT-1K1 x))"
sorry
  (*uniqueness*)
    show " for it1 be Cardinal-FunctionCARD-3M1 holds  for it2 be Cardinal-FunctionCARD-3M1 holds (domRELAT-1K1 it1 =XBOOLE-0R4 domRELAT-1K1 f & ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 f implies it1 .FUNCT-1K1 x =XBOOLE-0R4 cardCARD-1K1 (f .FUNCT-1K1 x))) & (domRELAT-1K1 it2 =XBOOLE-0R4 domRELAT-1K1 f & ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 f implies it2 .FUNCT-1K1 x =XBOOLE-0R4 cardCARD-1K1 (f .FUNCT-1K1 x))) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mdef card_3_def_3 ("disjoinCARD-3K2  _ " [228]228 ) where
  mlet "f be FunctionFUNCT-1M1"
"func disjoinCARD-3K2 f \<rightarrow> FunctionFUNCT-1M1 means
  \<lambda>it. domRELAT-1K1 it =XBOOLE-0R4 domRELAT-1K1 f & ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 f implies it .FUNCT-1K1 x =XBOOLE-0R4 [:ZFMISC-1K2 f .FUNCT-1K1 x,{TARSKIK1 x} :])"
proof-
  (*existence*)
    show " ex it be FunctionFUNCT-1M1 st domRELAT-1K1 it =XBOOLE-0R4 domRELAT-1K1 f & ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 f implies it .FUNCT-1K1 x =XBOOLE-0R4 [:ZFMISC-1K2 f .FUNCT-1K1 x,{TARSKIK1 x} :])"
sorry
  (*uniqueness*)
    show " for it1 be FunctionFUNCT-1M1 holds  for it2 be FunctionFUNCT-1M1 holds (domRELAT-1K1 it1 =XBOOLE-0R4 domRELAT-1K1 f & ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 f implies it1 .FUNCT-1K1 x =XBOOLE-0R4 [:ZFMISC-1K2 f .FUNCT-1K1 x,{TARSKIK1 x} :])) & (domRELAT-1K1 it2 =XBOOLE-0R4 domRELAT-1K1 f & ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 f implies it2 .FUNCT-1K1 x =XBOOLE-0R4 [:ZFMISC-1K2 f .FUNCT-1K1 x,{TARSKIK1 x} :])) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mdef card_3_def_4 ("UnionCARD-3K3  _ " [164]164 ) where
  mlet "f be FunctionFUNCT-1M1"
"func UnionCARD-3K3 f \<rightarrow> setHIDDENM2 equals
  unionTARSKIK3 (rngFUNCT-1K2 f)"
proof-
  (*coherence*)
    show "unionTARSKIK3 (rngFUNCT-1K2 f) be setHIDDENM2"
       sorry
qed "sorry"

mdef card_3_def_5 ("productCARD-3K4  _ " [228]228 ) where
  mlet "f be FunctionFUNCT-1M1"
"func productCARD-3K4 f \<rightarrow> setHIDDENM2 means
  \<lambda>it.  for x be objectHIDDENM1 holds x inHIDDENR3 it iff ( ex g be FunctionFUNCT-1M1 st (x =HIDDENR1 g & domRELAT-1K1 g =XBOOLE-0R4 domRELAT-1K1 f) & ( for y be objectHIDDENM1 holds y inHIDDENR3 domRELAT-1K1 f implies g .FUNCT-1K1 y inTARSKIR2 f .FUNCT-1K1 y))"
proof-
  (*existence*)
    show " ex it be setHIDDENM2 st  for x be objectHIDDENM1 holds x inHIDDENR3 it iff ( ex g be FunctionFUNCT-1M1 st (x =HIDDENR1 g & domRELAT-1K1 g =XBOOLE-0R4 domRELAT-1K1 f) & ( for y be objectHIDDENM1 holds y inHIDDENR3 domRELAT-1K1 f implies g .FUNCT-1K1 y inTARSKIR2 f .FUNCT-1K1 y))"
sorry
  (*uniqueness*)
    show " for it1 be setHIDDENM2 holds  for it2 be setHIDDENM2 holds ( for x be objectHIDDENM1 holds x inHIDDENR3 it1 iff ( ex g be FunctionFUNCT-1M1 st (x =HIDDENR1 g & domRELAT-1K1 g =XBOOLE-0R4 domRELAT-1K1 f) & ( for y be objectHIDDENM1 holds y inHIDDENR3 domRELAT-1K1 f implies g .FUNCT-1K1 y inTARSKIR2 f .FUNCT-1K1 y))) & ( for x be objectHIDDENM1 holds x inHIDDENR3 it2 iff ( ex g be FunctionFUNCT-1M1 st (x =HIDDENR1 g & domRELAT-1K1 g =XBOOLE-0R4 domRELAT-1K1 f) & ( for y be objectHIDDENM1 holds y inHIDDENR3 domRELAT-1K1 f implies g .FUNCT-1K1 y inTARSKIR2 f .FUNCT-1K1 y))) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mtheorem card_3_th_1:
" for ff be Cardinal-FunctionCARD-3M1 holds CardCARD-3K1 ff =FUNCT-1R1 ff"
sorry

mtheorem card_3_th_2:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds CardCARD-3K1 (X -->FUNCOP-1K7 Y) =FUNCT-1R1 X -->FUNCOP-1K7 cardCARD-1K1 Y"
sorry

mtheorem card_3_th_3:
"disjoinCARD-3K2 ({}XBOOLE-0K1) =FUNCT-1R1 {}XBOOLE-0K1"
  using card_3_def_3 relat_1_th_38 sorry

mtheorem card_3_th_4:
" for x be objectHIDDENM1 holds  for X be setHIDDENM2 holds disjoinCARD-3K2 (x .-->FUNCOP-1K17 X) =FUNCT-1R1 x .-->FUNCOP-1K17 ([:ZFMISC-1K2 X,{TARSKIK1 x} :])"
sorry

mtheorem card_3_th_5:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for f be FunctionFUNCT-1M1 holds (x inHIDDENR3 domRELAT-1K1 f & y inHIDDENR3 domRELAT-1K1 f) & x <>HIDDENR2 y implies disjoinCARD-3K2 f .FUNCT-1K1 x missesXBOOLE-0R1 disjoinCARD-3K2 f .FUNCT-1K1 y"
sorry

mtheorem card_3_th_6:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds UnionCARD-3K3 (X -->FUNCOP-1K7 Y) c=TARSKIR1 Y"
sorry

mtheorem card_3_th_7:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X <>HIDDENR2 {}XBOOLE-0K1 implies UnionCARD-3K3 (X -->FUNCOP-1K7 Y) =XBOOLE-0R4 Y"
sorry

mtheorem card_3_th_8:
" for x be objectHIDDENM1 holds  for Y be setHIDDENM2 holds UnionCARD-3K3 (x .-->FUNCOP-1K17 Y) =XBOOLE-0R4 Y"
  using card_3_th_7 sorry

mtheorem card_3_th_9:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds g inTARSKIR2 productCARD-3K4 f iff domRELAT-1K1 g =XBOOLE-0R4 domRELAT-1K1 f & ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 f implies g .FUNCT-1K1 x inTARSKIR2 f .FUNCT-1K1 x)"
sorry

mtheorem card_3_th_10:
"productCARD-3K4 ({}XBOOLE-0K1) =XBOOLE-0R4 {TARSKIK1 {}XBOOLE-0K1 }"
sorry

mtheorem card_3_th_11:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds FuncsFUNCT-2K1(X,Y) =XBOOLE-0R4 productCARD-3K4 (X -->FUNCOP-1K7 Y)"
sorry

mdef card_3_def_6 ("piCARD-3K5'( _ , _ ')" [0,0]228 ) where
  mlet "x be objectHIDDENM1", "X be setHIDDENM2"
"func piCARD-3K5(X,x) \<rightarrow> setHIDDENM2 means
  \<lambda>it.  for y be objectHIDDENM1 holds y inHIDDENR3 it iff ( ex f be FunctionFUNCT-1M1 st f inTARSKIR2 X & y =HIDDENR1 f .FUNCT-1K1 x)"
proof-
  (*existence*)
    show " ex it be setHIDDENM2 st  for y be objectHIDDENM1 holds y inHIDDENR3 it iff ( ex f be FunctionFUNCT-1M1 st f inTARSKIR2 X & y =HIDDENR1 f .FUNCT-1K1 x)"
sorry
  (*uniqueness*)
    show " for it1 be setHIDDENM2 holds  for it2 be setHIDDENM2 holds ( for y be objectHIDDENM1 holds y inHIDDENR3 it1 iff ( ex f be FunctionFUNCT-1M1 st f inTARSKIR2 X & y =HIDDENR1 f .FUNCT-1K1 x)) & ( for y be objectHIDDENM1 holds y inHIDDENR3 it2 iff ( ex f be FunctionFUNCT-1M1 st f inTARSKIR2 X & y =HIDDENR1 f .FUNCT-1K1 x)) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mtheorem card_3_th_12:
" for x be objectHIDDENM1 holds  for f be FunctionFUNCT-1M1 holds x inHIDDENR3 domRELAT-1K1 f & productCARD-3K4 f <>HIDDENR2 {}XBOOLE-0K1 implies piCARD-3K5(productCARD-3K4 f,x) =XBOOLE-0R4 f .FUNCT-1K1 x"
sorry

mtheorem card_3_th_13:
" for x be objectHIDDENM1 holds piCARD-3K5({}XBOOLE-0K1,x) =XBOOLE-0R4 {}XBOOLE-0K1"
sorry

mtheorem card_3_th_14:
" for x be objectHIDDENM1 holds  for g be FunctionFUNCT-1M1 holds piCARD-3K5({TARSKIK1 g},x) =XBOOLE-0R4 {TARSKIK1 g .FUNCT-1K1 x }"
sorry

mtheorem card_3_th_15:
" for x be objectHIDDENM1 holds  for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds piCARD-3K5({TARSKIK2 f,g },x) =XBOOLE-0R4 {TARSKIK2 f .FUNCT-1K1 x,g .FUNCT-1K1 x }"
sorry

mtheorem card_3_th_16:
" for x be objectHIDDENM1 holds  for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds piCARD-3K5(X \\/XBOOLE-0K2 Y,x) =XBOOLE-0R4 piCARD-3K5(X,x) \\/XBOOLE-0K2 piCARD-3K5(Y,x)"
sorry

mtheorem card_3_th_17:
" for x be objectHIDDENM1 holds  for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds piCARD-3K5(X /\\XBOOLE-0K3 Y,x) c=TARSKIR1 piCARD-3K5(X,x) /\\XBOOLE-0K3 piCARD-3K5(Y,x)"
sorry

mtheorem card_3_th_18:
" for x be objectHIDDENM1 holds  for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds piCARD-3K5(X,x) \\SUBSET-1K6 piCARD-3K5(Y,x) c=TARSKIR1 piCARD-3K5(X \\SUBSET-1K6 Y,x)"
sorry

mtheorem card_3_th_19:
" for x be objectHIDDENM1 holds  for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds piCARD-3K5(X,x) \\+\\XBOOLE-0K5 piCARD-3K5(Y,x) c=TARSKIR1 piCARD-3K5(X \\+\\XBOOLE-0K5 Y,x)"
sorry

mtheorem card_3_th_20:
" for x be objectHIDDENM1 holds  for X be setHIDDENM2 holds cardCARD-1K1 (piCARD-3K5(X,x)) c=ORDINAL1R1 cardCARD-1K1 X"
sorry

mtheorem card_3_th_21:
" for x be objectHIDDENM1 holds  for f be FunctionFUNCT-1M1 holds x inHIDDENR3 UnionCARD-3K3 disjoinCARD-3K2 f implies ( ex y be objectHIDDENM1 st  ex z be objectHIDDENM1 st x =HIDDENR1 [TARSKIK4 y,z ])"
sorry

mtheorem card_3_th_22:
" for x be objectHIDDENM1 holds  for f be FunctionFUNCT-1M1 holds x inHIDDENR3 UnionCARD-3K3 disjoinCARD-3K2 f iff (x `2XTUPLE-0K2 inHIDDENR3 domRELAT-1K1 f & x `1XTUPLE-0K1 inHIDDENR3 f .FUNCT-1K1 x `2XTUPLE-0K2) & x =HIDDENR1 [TARSKIK4 x `1XTUPLE-0K1,x `2XTUPLE-0K2 ]"
sorry

mtheorem card_3_th_23:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds f c=RELAT-1R2 g implies disjoinCARD-3K2 f c=RELAT-1R2 disjoinCARD-3K2 g"
sorry

mtheorem card_3_th_24:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds f c=RELAT-1R2 g implies UnionCARD-3K3 f c=TARSKIR1 UnionCARD-3K3 g"
sorry

mtheorem card_3_th_25:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds UnionCARD-3K3 disjoinCARD-3K2 (Y -->FUNCOP-1K7 X) =XBOOLE-0R4 [:ZFMISC-1K2 X,Y :]"
sorry

mtheorem card_3_th_26:
" for f be FunctionFUNCT-1M1 holds productCARD-3K4 f =XBOOLE-0R4 {}XBOOLE-0K1 iff {}XBOOLE-0K1 inTARSKIR2 rngFUNCT-1K2 f"
sorry

mtheorem card_3_th_27:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds domRELAT-1K1 f =XBOOLE-0R4 domRELAT-1K1 g & ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 f implies f .FUNCT-1K1 x c=TARSKIR1 g .FUNCT-1K1 x) implies productCARD-3K4 f c=TARSKIR1 productCARD-3K4 g"
sorry

reserve F, G for "Cardinal-FunctionCARD-3M1"
mtheorem card_3_th_28:
" for F be Cardinal-FunctionCARD-3M1 holds  for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 F implies cardCARD-1K1 (F .FUNCT-1K1 x) =XBOOLE-0R4 F .FUNCT-1K1 x"
sorry

mtheorem card_3_th_29:
" for F be Cardinal-FunctionCARD-3M1 holds  for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 F implies cardCARD-1K1 (disjoinCARD-3K2 F .FUNCT-1K1 x) =XBOOLE-0R4 F .FUNCT-1K1 x"
sorry

mdef card_3_def_7 ("SumCARD-3K6  _ " [260]260 ) where
  mlet "F be Cardinal-FunctionCARD-3M1"
"func SumCARD-3K6 F \<rightarrow> CardinalCARD-1M1 equals
  cardCARD-1K1 (UnionCARD-3K3 disjoinCARD-3K2 F)"
proof-
  (*coherence*)
    show "cardCARD-1K1 (UnionCARD-3K3 disjoinCARD-3K2 F) be CardinalCARD-1M1"
       sorry
qed "sorry"

mdef card_3_def_8 ("ProductCARD-3K7  _ " [228]228 ) where
  mlet "F be Cardinal-FunctionCARD-3M1"
"func ProductCARD-3K7 F \<rightarrow> CardinalCARD-1M1 equals
  cardCARD-1K1 (productCARD-3K4 F)"
proof-
  (*coherence*)
    show "cardCARD-1K1 (productCARD-3K4 F) be CardinalCARD-1M1"
       sorry
qed "sorry"

mtheorem card_3_th_30:
" for F be Cardinal-FunctionCARD-3M1 holds  for G be Cardinal-FunctionCARD-3M1 holds domRELAT-1K1 F =XBOOLE-0R4 domRELAT-1K1 G & ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 F implies F .FUNCT-1K1 x c=TARSKIR1 G .FUNCT-1K1 x) implies SumCARD-3K6 F c=ORDINAL1R1 SumCARD-3K6 G"
sorry

mtheorem card_3_th_31:
" for F be Cardinal-FunctionCARD-3M1 holds {}XBOOLE-0K1 inTARSKIR2 rngFUNCT-1K2 F iff ProductCARD-3K7 F =XBOOLE-0R4 0ORDINAL1K5"
sorry

mtheorem card_3_th_32:
" for F be Cardinal-FunctionCARD-3M1 holds  for G be Cardinal-FunctionCARD-3M1 holds domRELAT-1K1 F =XBOOLE-0R4 domRELAT-1K1 G & ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 F implies F .FUNCT-1K1 x c=TARSKIR1 G .FUNCT-1K1 x) implies ProductCARD-3K7 F c=ORDINAL1R1 ProductCARD-3K7 G"
  using card_3_th_27 card_1_th_11 sorry

mtheorem card_3_th_33:
" for F be Cardinal-FunctionCARD-3M1 holds  for G be Cardinal-FunctionCARD-3M1 holds F c=RELAT-1R2 G implies SumCARD-3K6 F c=ORDINAL1R1 SumCARD-3K6 G"
sorry

mtheorem card_3_th_34:
" for F be Cardinal-FunctionCARD-3M1 holds  for G be Cardinal-FunctionCARD-3M1 holds F c=RELAT-1R2 G &  not 0ORDINAL1K5 inTARSKIR2 rngFUNCT-1K2 G implies ProductCARD-3K7 F c=ORDINAL1R1 ProductCARD-3K7 G"
sorry

mtheorem card_3_th_35:
" for K be CardinalCARD-1M1 holds SumCARD-3K6 ({}XBOOLE-0K1 -->FUNCOP-1K7 K) =XBOOLE-0R4 0ORDINAL1K5"
sorry

mtheorem card_3_th_36:
" for K be CardinalCARD-1M1 holds ProductCARD-3K7 ({}XBOOLE-0K1 -->FUNCOP-1K7 K) =XBOOLE-0R4 \<one>\<^sub>M"
  using card_3_th_10 card_1_th_30 sorry

mtheorem card_3_th_37:
" for K be CardinalCARD-1M1 holds  for x be objectHIDDENM1 holds SumCARD-3K6 (x .-->FUNCOP-1K17 K) =XBOOLE-0R4 K"
sorry

mtheorem card_3_th_38:
" for K be CardinalCARD-1M1 holds  for x be objectHIDDENM1 holds ProductCARD-3K7 (x .-->FUNCOP-1K17 K) =XBOOLE-0R4 K"
sorry

mtheorem card_3_th_39:
" for f be FunctionFUNCT-1M1 holds cardCARD-1K1 (UnionCARD-3K3 f) c=ORDINAL1R1 SumCARD-3K6 (CardCARD-3K1 f)"
sorry

mtheorem card_3_th_40:
" for F be Cardinal-FunctionCARD-3M1 holds cardCARD-1K1 (UnionCARD-3K3 F) c=ORDINAL1R1 SumCARD-3K6 F"
sorry

(*\$N Koenig Theorem*)
mtheorem card_3_th_41:
" for F be Cardinal-FunctionCARD-3M1 holds  for G be Cardinal-FunctionCARD-3M1 holds domRELAT-1K1 F =XBOOLE-0R4 domRELAT-1K1 G & ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 F implies F .FUNCT-1K1 x inTARSKIR2 G .FUNCT-1K1 x) implies SumCARD-3K6 F inTARSKIR2 ProductCARD-3K7 G"
sorry

theorem card_3_sch_2:
  fixes Xf0 Ff1 Pp2 
  assumes
[ty]: "Xf0 be setHIDDENM2" and
  [ty_func]: "\<And> x1. x1 be objectHIDDENM1 \<Longrightarrow> Ff1(x1) be setHIDDENM2"
  shows " ex f be FunctionFUNCT-1M1 st domRELAT-1K1 f =XBOOLE-0R4 Xf0 & ( for x be objectHIDDENM1 holds x inHIDDENR3 Xf0 implies ( for y be objectHIDDENM1 holds y inHIDDENR3 f .FUNCT-1K1 x iff y inHIDDENR3 Ff1(x) & Pp2(x,y)))"
sorry

mlemma card_3_lm_1:
" for x be objectHIDDENM1 holds  for R be RelationRELAT-1M1 holds x inHIDDENR3 fieldRELAT-1K3 R implies ( ex y be objectHIDDENM1 st [TARSKIK4 x,y ] inHIDDENR3 R or [TARSKIK4 y,x ] inHIDDENR3 R)"
sorry

mtheorem card_3_th_42:
" for X be setHIDDENM2 holds X be finiteFINSET-1V1 implies cardCARD-1K1 X inTARSKIR2 cardCARD-1K1 (omegaORDINAL1K4)"
sorry

mtheorem card_3_th_43:
" for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds cardCARD-1K1 A inTARSKIR2 cardCARD-1K1 B implies A inTARSKIR2 B"
sorry

mtheorem card_3_th_44:
" for A be OrdinalORDINAL1M3 holds  for M be CardinalCARD-1M1 holds cardCARD-1K1 A inTARSKIR2 M implies A inTARSKIR2 M"
sorry

mtheorem card_3_th_45:
" for X be setHIDDENM2 holds X be c=-linearORDINAL1V6 implies ( ex Y be setHIDDENM2 st (Y c=TARSKIR1 X & unionTARSKIK3 Y =XBOOLE-0R4 unionTARSKIK3 X) & ( for Z be setHIDDENM2 holds Z c=TARSKIR1 Y & Z <>HIDDENR2 {}XBOOLE-0K1 implies ( ex Z1 be setHIDDENM2 st Z1 inTARSKIR2 Z & ( for Z2 be setHIDDENM2 holds Z2 inTARSKIR2 Z implies Z1 c=TARSKIR1 Z2))))"
sorry

mtheorem card_3_th_46:
" for M be CardinalCARD-1M1 holds  for X be setHIDDENM2 holds ( for Z be setHIDDENM2 holds Z inTARSKIR2 X implies cardCARD-1K1 Z inTARSKIR2 M) & X be c=-linearORDINAL1V6 implies cardCARD-1K1 (unionTARSKIK3 X) c=ORDINAL1R1 M"
sorry

(*begin*)
mtheorem card_3_cl_6:
  mlet "f be FunctionFUNCT-1M1"
"cluster productCARD-3K4 f as-term-is functionalFUNCT-1V6"
proof
(*coherence*)
  show "productCARD-3K4 f be functionalFUNCT-1V6"
sorry
qed "sorry"

mtheorem card_3_cl_7:
  mlet "A be setHIDDENM2", "B be with-non-empty-elementsSETFAM-1V1\<bar>setHIDDENM2"
"cluster note-that non-emptyFUNCT-1V4 for FunctionFUNCT-2M1-of(A,B)"
proof
(*coherence*)
  show " for it be FunctionFUNCT-2M1-of(A,B) holds it be non-emptyFUNCT-1V4"
sorry
qed "sorry"

mtheorem card_3_cl_8:
  mlet "f be non-emptyFUNCT-1V4\<bar>FunctionFUNCT-1M1"
"cluster productCARD-3K4 f as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "productCARD-3K4 f be  non emptyXBOOLE-0V1"
sorry
qed "sorry"

mtheorem card_3_th_47:
" for a be setHIDDENM2 holds  for b be setHIDDENM2 holds  for c be setHIDDENM2 holds  for d be setHIDDENM2 holds a <>HIDDENR2 b implies productCARD-3K4 ((a,b)-->FUNCT-4K6({TARSKIK1 c},{TARSKIK1 d})) =XBOOLE-0R4 {TARSKIK1 (a,b)-->FUNCT-4K6(c,d) }"
sorry

mtheorem card_3_th_48:
" for x be objectHIDDENM1 holds  for f be FunctionFUNCT-1M1 holds x inHIDDENR3 productCARD-3K4 f implies x be FunctionFUNCT-1M1"
   sorry

(*begin*)
reserve A, B for "setHIDDENM2"
mdef card_3_def_9 ("sproductCARD-3K8  _ " [164]164 ) where
  mlet "f be FunctionFUNCT-1M1"
"func sproductCARD-3K8 f \<rightarrow> setHIDDENM2 means
  \<lambda>it.  for x be objectHIDDENM1 holds x inHIDDENR3 it iff ( ex g be FunctionFUNCT-1M1 st (x =HIDDENR1 g & domRELAT-1K1 g c=TARSKIR1 domRELAT-1K1 f) & ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 g implies g .FUNCT-1K1 x inTARSKIR2 f .FUNCT-1K1 x))"
proof-
  (*existence*)
    show " ex it be setHIDDENM2 st  for x be objectHIDDENM1 holds x inHIDDENR3 it iff ( ex g be FunctionFUNCT-1M1 st (x =HIDDENR1 g & domRELAT-1K1 g c=TARSKIR1 domRELAT-1K1 f) & ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 g implies g .FUNCT-1K1 x inTARSKIR2 f .FUNCT-1K1 x))"
sorry
  (*uniqueness*)
    show " for it1 be setHIDDENM2 holds  for it2 be setHIDDENM2 holds ( for x be objectHIDDENM1 holds x inHIDDENR3 it1 iff ( ex g be FunctionFUNCT-1M1 st (x =HIDDENR1 g & domRELAT-1K1 g c=TARSKIR1 domRELAT-1K1 f) & ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 g implies g .FUNCT-1K1 x inTARSKIR2 f .FUNCT-1K1 x))) & ( for x be objectHIDDENM1 holds x inHIDDENR3 it2 iff ( ex g be FunctionFUNCT-1M1 st (x =HIDDENR1 g & domRELAT-1K1 g c=TARSKIR1 domRELAT-1K1 f) & ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 g implies g .FUNCT-1K1 x inTARSKIR2 f .FUNCT-1K1 x))) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mtheorem card_3_cl_9:
  mlet "f be FunctionFUNCT-1M1"
"cluster sproductCARD-3K8 f as-term-is functionalFUNCT-1V6\<bar> non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "sproductCARD-3K8 f be functionalFUNCT-1V6\<bar> non emptyXBOOLE-0V1"
sorry
qed "sorry"

mtheorem card_3_th_49:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds g inTARSKIR2 sproductCARD-3K8 f implies domRELAT-1K1 g c=TARSKIR1 domRELAT-1K1 f & ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 g implies g .FUNCT-1K1 x inTARSKIR2 f .FUNCT-1K1 x)"
sorry

mtheorem card_3_th_50:
" for f be FunctionFUNCT-1M1 holds {}XBOOLE-0K1 inTARSKIR2 sproductCARD-3K8 f"
sorry

mtheorem card_3_cl_10:
  mlet "f be FunctionFUNCT-1M1"
"cluster emptyXBOOLE-0V1 for ElementSUBSET-1M1-of sproductCARD-3K8 f"
proof
(*existence*)
  show " ex it be ElementSUBSET-1M1-of sproductCARD-3K8 f st it be emptyXBOOLE-0V1"
sorry
qed "sorry"

mtheorem card_3_th_51:
" for f be FunctionFUNCT-1M1 holds productCARD-3K4 f c=TARSKIR1 sproductCARD-3K8 f"
sorry

mtheorem card_3_th_52:
" for x be objectHIDDENM1 holds  for f be FunctionFUNCT-1M1 holds x inHIDDENR3 sproductCARD-3K8 f implies x be PartFuncPARTFUN1M1-of(domRELAT-1K1 f,unionTARSKIK3 (rngFUNCT-1K2 f))"
sorry

mtheorem card_3_th_53:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds  for h be FunctionFUNCT-1M1 holds g inTARSKIR2 productCARD-3K4 f & h inTARSKIR2 sproductCARD-3K8 f implies g +*FUNCT-4K1 h inTARSKIR2 productCARD-3K4 f"
sorry

mtheorem card_3_th_54:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds productCARD-3K4 f <>HIDDENR2 {}XBOOLE-0K1 implies (g inTARSKIR2 sproductCARD-3K8 f iff ( ex h be FunctionFUNCT-1M1 st h inTARSKIR2 productCARD-3K4 f & g c=RELAT-1R2 h))"
sorry

mtheorem card_3_th_55:
" for f be FunctionFUNCT-1M1 holds sproductCARD-3K8 f c=TARSKIR1 PFuncsPARTFUN1K4(domRELAT-1K1 f,unionTARSKIK3 (rngFUNCT-1K2 f))"
sorry

mtheorem card_3_th_56:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds f c=RELAT-1R2 g implies sproductCARD-3K8 f c=TARSKIR1 sproductCARD-3K8 g"
sorry

mtheorem card_3_th_57:
"sproductCARD-3K8 {}XBOOLE-0K1 =XBOOLE-0R4 {TARSKIK1 {}XBOOLE-0K1 }"
sorry

mtheorem card_3_th_58:
" for A be setHIDDENM2 holds  for B be setHIDDENM2 holds PFuncsPARTFUN1K4(A,B) =XBOOLE-0R4 sproductCARD-3K8 (A -->FUNCOP-1K7 B)"
sorry

mtheorem card_3_th_59:
" for A be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for B be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(A,B) holds sproductCARD-3K8 f =XBOOLE-0R4 sproductCARD-3K8 f |PARTFUN1K2\<^bsub>(A,B)\<^esub> ({x where x be ElementSUBSET-1M1-of A : f .FUNCT-2K3\<^bsub>(A,B)\<^esub> x <>HIDDENR2 {}XBOOLE-0K1 })"
sorry

mtheorem card_3_th_60:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for f be FunctionFUNCT-1M1 holds x inHIDDENR3 domRELAT-1K1 f & y inHIDDENR3 f .FUNCT-1K1 x implies x .-->FUNCOP-1K17 y inTARSKIR2 sproductCARD-3K8 f"
sorry

mtheorem card_3_th_61:
" for f be FunctionFUNCT-1M1 holds sproductCARD-3K8 f =XBOOLE-0R4 {TARSKIK1 {}XBOOLE-0K1 } iff ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 f implies f .FUNCT-1K1 x =XBOOLE-0R4 {}XBOOLE-0K1)"
sorry

mtheorem card_3_th_62:
" for f be FunctionFUNCT-1M1 holds  for A be setHIDDENM2 holds A c=TARSKIR1 sproductCARD-3K8 f & ( for h1 be FunctionFUNCT-1M1 holds  for h2 be FunctionFUNCT-1M1 holds h1 inTARSKIR2 A & h2 inTARSKIR2 A implies h1 toleratesPARTFUN1R1 h2) implies unionTARSKIK3 A inTARSKIR2 sproductCARD-3K8 f"
sorry

mtheorem card_3_th_63:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds  for h be FunctionFUNCT-1M1 holds (g toleratesPARTFUN1R1 h & g inTARSKIR2 sproductCARD-3K8 f) & h inTARSKIR2 sproductCARD-3K8 f implies g \\/XBOOLE-0K2 h inTARSKIR2 sproductCARD-3K8 f"
sorry

mtheorem card_3_th_64:
" for f be FunctionFUNCT-1M1 holds  for h be FunctionFUNCT-1M1 holds  for x be setHIDDENM2 holds x c=TARSKIR1 h & h inTARSKIR2 sproductCARD-3K8 f implies x inTARSKIR2 sproductCARD-3K8 f"
sorry

mtheorem card_3_th_65:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds  for A be setHIDDENM2 holds g inTARSKIR2 sproductCARD-3K8 f implies g |RELAT-1K8 A inTARSKIR2 sproductCARD-3K8 f"
  using card_3_th_64 relat_1_th_59 sorry

mtheorem card_3_th_66:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds  for A be setHIDDENM2 holds g inTARSKIR2 sproductCARD-3K8 f implies g |RELAT-1K8 A inTARSKIR2 sproductCARD-3K8 f |RELAT-1K8 A"
sorry

mtheorem card_3_th_67:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds  for h be FunctionFUNCT-1M1 holds h inTARSKIR2 sproductCARD-3K8 (f +*FUNCT-4K1 g) implies ( ex f9 be FunctionFUNCT-1M1 st  ex g9 be FunctionFUNCT-1M1 st (f9 inTARSKIR2 sproductCARD-3K8 f & g9 inTARSKIR2 sproductCARD-3K8 g) & h =FUNCT-1R1 f9 +*FUNCT-4K1 g9)"
sorry

mtheorem card_3_th_68:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds  for f9 be FunctionFUNCT-1M1 holds  for g9 be FunctionFUNCT-1M1 holds (domRELAT-1K1 g missesXBOOLE-0R1 domRELAT-1K1 f9 \\SUBSET-1K6 domRELAT-1K1 g9 & f9 inTARSKIR2 sproductCARD-3K8 f) & g9 inTARSKIR2 sproductCARD-3K8 g implies f9 +*FUNCT-4K1 g9 inTARSKIR2 sproductCARD-3K8 (f +*FUNCT-4K1 g)"
sorry

mtheorem card_3_th_69:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds  for f9 be FunctionFUNCT-1M1 holds  for g9 be FunctionFUNCT-1M1 holds (domRELAT-1K1 f9 missesXBOOLE-0R1 domRELAT-1K1 g \\SUBSET-1K6 domRELAT-1K1 g9 & f9 inTARSKIR2 sproductCARD-3K8 f) & g9 inTARSKIR2 sproductCARD-3K8 g implies f9 +*FUNCT-4K1 g9 inTARSKIR2 sproductCARD-3K8 (f +*FUNCT-4K1 g)"
sorry

mtheorem card_3_th_70:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds  for h be FunctionFUNCT-1M1 holds g inTARSKIR2 sproductCARD-3K8 f & h inTARSKIR2 sproductCARD-3K8 f implies g +*FUNCT-4K1 h inTARSKIR2 sproductCARD-3K8 f"
sorry

mtheorem card_3_th_71:
" for f be FunctionFUNCT-1M1 holds  for x1 be setHIDDENM2 holds  for x2 be setHIDDENM2 holds  for y1 be setHIDDENM2 holds  for y2 be setHIDDENM2 holds ((x1 inTARSKIR2 domRELAT-1K1 f & y1 inTARSKIR2 f .FUNCT-1K1 x1) & x2 inTARSKIR2 domRELAT-1K1 f) & y2 inTARSKIR2 f .FUNCT-1K1 x2 implies (x1,x2)-->FUNCT-4K6(y1,y2) inTARSKIR2 sproductCARD-3K8 f"
sorry

(*begin*)
mdef card_3_def_10 ("with-common-domainCARD-3V2" 70 ) where
"attr with-common-domainCARD-3V2 for setHIDDENM2 means
  (\<lambda>IT.  for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds f inTARSKIR2 IT & g inTARSKIR2 IT implies domRELAT-1K1 f =XBOOLE-0R4 domRELAT-1K1 g)"..

mtheorem card_3_cl_11:
"cluster with-common-domainCARD-3V2\<bar>functionalFUNCT-1V6\<bar> non emptyXBOOLE-0V1 for setHIDDENM2"
proof
(*existence*)
  show " ex it be setHIDDENM2 st it be with-common-domainCARD-3V2\<bar>functionalFUNCT-1V6\<bar> non emptyXBOOLE-0V1"
sorry
qed "sorry"

mtheorem card_3_cl_12:
  mlet "f be FunctionFUNCT-1M1"
"cluster {TARSKIK1 f} as-term-is with-common-domainCARD-3V2"
proof
(*coherence*)
  show "{TARSKIK1 f} be with-common-domainCARD-3V2"
sorry
qed "sorry"

mdef card_3_def_11 ("DOMCARD-3K9  _ " [164]164 ) where
  mlet "X be functionalFUNCT-1V6\<bar>setHIDDENM2"
"func DOMCARD-3K9 X \<rightarrow> setHIDDENM2 equals
  meetSETFAM-1K1 ({domRELAT-1K1 f where f be ElementSUBSET-1M1-of X :  True  })"
proof-
  (*coherence*)
    show "meetSETFAM-1K1 ({domRELAT-1K1 f where f be ElementSUBSET-1M1-of X :  True  }) be setHIDDENM2"
       sorry
qed "sorry"

mlemma card_3_lm_2:
" for X be functionalFUNCT-1V6\<bar>with-common-domainCARD-3V2\<bar>setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds f inTARSKIR2 X implies domRELAT-1K1 f =XBOOLE-0R4 DOMCARD-3K9 X"
sorry

mtheorem card_3_th_72:
" for X be with-common-domainCARD-3V2\<bar>functionalFUNCT-1V6\<bar>setHIDDENM2 holds X =XBOOLE-0R4 {TARSKIK1 {}XBOOLE-0K1 } implies DOMCARD-3K9 X =XBOOLE-0R4 {}XBOOLE-0K1"
sorry

mtheorem card_3_cl_13:
  mlet "X be emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster DOMCARD-3K9 X as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "DOMCARD-3K9 X be emptyXBOOLE-0V1"
sorry
qed "sorry"

(*begin*)
mdef card_3_def_12 ("product\<inverse>CARD-3K10  _ " [228]228 ) where
  mlet "S be functionalFUNCT-1V6\<bar>setHIDDENM2"
"func product\<inverse>CARD-3K10 S \<rightarrow> FunctionFUNCT-1M1 means
  \<lambda>it. domRELAT-1K1 it =XBOOLE-0R4 DOMCARD-3K9 S & ( for i be setHIDDENM2 holds i inTARSKIR2 domRELAT-1K1 it implies it .FUNCT-1K1 i =XBOOLE-0R4 piCARD-3K5(S,i))"
proof-
  (*existence*)
    show " ex it be FunctionFUNCT-1M1 st domRELAT-1K1 it =XBOOLE-0R4 DOMCARD-3K9 S & ( for i be setHIDDENM2 holds i inTARSKIR2 domRELAT-1K1 it implies it .FUNCT-1K1 i =XBOOLE-0R4 piCARD-3K5(S,i))"
sorry
  (*uniqueness*)
    show " for it1 be FunctionFUNCT-1M1 holds  for it2 be FunctionFUNCT-1M1 holds (domRELAT-1K1 it1 =XBOOLE-0R4 DOMCARD-3K9 S & ( for i be setHIDDENM2 holds i inTARSKIR2 domRELAT-1K1 it1 implies it1 .FUNCT-1K1 i =XBOOLE-0R4 piCARD-3K5(S,i))) & (domRELAT-1K1 it2 =XBOOLE-0R4 DOMCARD-3K9 S & ( for i be setHIDDENM2 holds i inTARSKIR2 domRELAT-1K1 it2 implies it2 .FUNCT-1K1 i =XBOOLE-0R4 piCARD-3K5(S,i))) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

(*\$CT*)
mtheorem card_3_th_74:
" for S be  non emptyXBOOLE-0V1\<bar>functionalFUNCT-1V6\<bar>setHIDDENM2 holds  for i be setHIDDENM2 holds i inTARSKIR2 domRELAT-1K1 (product\<inverse>CARD-3K10 S) implies product\<inverse>CARD-3K10 S .FUNCT-1K1 i =XBOOLE-0R4 {f .FUNCT-1K1 i where f be ElementSUBSET-1M1-of S :  True  }"
sorry

mdef card_3_def_13 ("product-likeCARD-3V3" 70 ) where
"attr product-likeCARD-3V3 for setHIDDENM2 means
  (\<lambda>S.  ex f be FunctionFUNCT-1M1 st S =XBOOLE-0R4 productCARD-3K4 f)"..

mtheorem card_3_cl_14:
  mlet "f be FunctionFUNCT-1M1"
"cluster productCARD-3K4 f as-term-is product-likeCARD-3V3"
proof
(*coherence*)
  show "productCARD-3K4 f be product-likeCARD-3V3"
     sorry
qed "sorry"

mtheorem card_3_cl_15:
"cluster product-likeCARD-3V3 also-is functionalFUNCT-1V6\<bar>with-common-domainCARD-3V2 for setHIDDENM2"
proof
(*coherence*)
  show " for it be setHIDDENM2 holds it be product-likeCARD-3V3 implies it be functionalFUNCT-1V6\<bar>with-common-domainCARD-3V2"
sorry
qed "sorry"

mtheorem card_3_cl_16:
"cluster product-likeCARD-3V3\<bar> non emptyXBOOLE-0V1 for setHIDDENM2"
proof
(*existence*)
  show " ex it be setHIDDENM2 st it be product-likeCARD-3V3\<bar> non emptyXBOOLE-0V1"
sorry
qed "sorry"

(*\$CT 2*)
mtheorem card_3_th_77:
" for S be functionalFUNCT-1V6\<bar>with-common-domainCARD-3V2\<bar>setHIDDENM2 holds S c=TARSKIR1 productCARD-3K4 (product\<inverse>CARD-3K10 S)"
sorry

mtheorem card_3_th_78:
" for S be  non emptyXBOOLE-0V1\<bar>product-likeCARD-3V3\<bar>setHIDDENM2 holds S =XBOOLE-0R4 productCARD-3K4 (product\<inverse>CARD-3K10 S)"
sorry

mtheorem card_3_th_79:
" for f be FunctionFUNCT-1M1 holds  for s be ElementSUBSET-1M1-of productCARD-3K4 f holds  for t be ElementSUBSET-1M1-of productCARD-3K4 f holds  for A be setHIDDENM2 holds s +*FUNCT-4K1 t |RELAT-1K8 A be ElementSUBSET-1M1-of productCARD-3K4 f"
sorry

mtheorem card_3_th_80:
" for f be non-emptyFUNCT-1V4\<bar>FunctionFUNCT-1M1 holds  for p be ElementSUBSET-1M1-of sproductCARD-3K8 f holds  ex s be ElementSUBSET-1M1-of productCARD-3K4 f st p c=RELAT-1R2 s"
sorry

mtheorem card_3_th_81:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds  for A be setHIDDENM2 holds g inTARSKIR2 productCARD-3K4 f implies g |RELAT-1K8 A inTARSKIR2 sproductCARD-3K8 f"
sorry

syntax CARD_3K11 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ |CARD-3K11\<^bsub>'( _ ')\<^esub>  _ " [200,0,200]200)
translations "g |CARD-3K11\<^bsub>(f)\<^esub> X" \<rightharpoonup> "g |RELAT-1K8 X"

mtheorem card_3_add_1:
  mlet "f be non-emptyFUNCT-1V4\<bar>FunctionFUNCT-1M1", "g be ElementSUBSET-1M1-of productCARD-3K4 f", "X be setHIDDENM2"
"cluster g |RELAT-1K8 X as-term-is ElementSUBSET-1M1-of sproductCARD-3K8 f"
proof
(*coherence*)
  show "g |RELAT-1K8 X be ElementSUBSET-1M1-of sproductCARD-3K8 f"
    using card_3_th_81 sorry
qed "sorry"

mtheorem card_3_th_82:
" for f be non-emptyFUNCT-1V4\<bar>FunctionFUNCT-1M1 holds  for s be ElementSUBSET-1M1-of productCARD-3K4 f holds  for ss be ElementSUBSET-1M1-of productCARD-3K4 f holds  for A be setHIDDENM2 holds (ss +*FUNCT-4K1 s |CARD-3K11\<^bsub>(f)\<^esub> A)|RELAT-1K8 A =FUNCT-1R1 s |CARD-3K11\<^bsub>(f)\<^esub> A"
sorry

mtheorem card_3_th_83:
" for M be FunctionFUNCT-1M1 holds  for x be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds x inTARSKIR2 productCARD-3K4 M implies x *FUNCT-1K3 g inTARSKIR2 productCARD-3K4 (M *FUNCT-1K3 g)"
sorry

mtheorem card_3_th_84:
" for X be setHIDDENM2 holds X be finiteFINSET-1V1 iff cardCARD-1K1 X inTARSKIR2 omegaORDINAL1K4"
  using card_3_th_42 sorry

reserve A, B for "OrdinalORDINAL1M3"
mtheorem card_3_th_85:
" for A be OrdinalORDINAL1M3 holds A be infiniteFINSET-1V2 iff omegaORDINAL1K4 c=ORDINAL1R1 A"
sorry

mtheorem card_3_th_86:
" for M be CardinalCARD-1M1 holds  for N be CardinalCARD-1M1 holds N be finiteFINSET-1V1 &  not M be finiteFINSET-1V1 implies N inTARSKIR2 M & N c=ORDINAL1R1 M"
sorry

mtheorem card_3_th_87:
" for X be setHIDDENM2 holds  not X be finiteFINSET-1V1 iff ( ex Y be setHIDDENM2 st Y c=TARSKIR1 X & cardCARD-1K1 Y =XBOOLE-0R4 omegaORDINAL1K4)"
sorry

mtheorem card_3_th_88:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds cardCARD-1K1 X =XBOOLE-0R4 cardCARD-1K1 Y iff nextcardCARD-1K2 X =XBOOLE-0R4 nextcardCARD-1K2 Y"
sorry

mtheorem card_3_th_89:
" for M be CardinalCARD-1M1 holds  for N be CardinalCARD-1M1 holds nextcardCARD-1K2 N =XBOOLE-0R4 nextcardCARD-1K2 M implies M =XBOOLE-0R4 N"
sorry

mtheorem card_3_th_90:
" for M be CardinalCARD-1M1 holds  for N be CardinalCARD-1M1 holds N inTARSKIR2 M iff nextcardCARD-1K2 N c=ORDINAL1R1 M"
sorry

mtheorem card_3_th_91:
" for M be CardinalCARD-1M1 holds  for N be CardinalCARD-1M1 holds N inTARSKIR2 nextcardCARD-1K2 M iff N c=ORDINAL1R1 M"
sorry

mtheorem card_3_th_92:
" for M be CardinalCARD-1M1 holds  for N be CardinalCARD-1M1 holds M be finiteFINSET-1V1 & (N c=ORDINAL1R1 M or N inTARSKIR2 M) implies N be finiteFINSET-1V1"
sorry

mdef card_3_def_14 ("countableCARD-3V4" 70 ) where
"attr countableCARD-3V4 for setHIDDENM2 means
  (\<lambda>X. cardCARD-1K1 X c=ORDINAL1R1 omegaORDINAL1K4)"..

mdef card_3_def_15 ("denumerableCARD-3V5" 70 ) where
"attr denumerableCARD-3V5 for setHIDDENM2 means
  (\<lambda>X. cardCARD-1K1 X =XBOOLE-0R4 omegaORDINAL1K4)"..

mtheorem card_3_cl_17:
"cluster denumerableCARD-3V5 also-is countableCARD-3V4\<bar>infiniteFINSET-1V2 for setHIDDENM2"
proof
(*coherence*)
  show " for it be setHIDDENM2 holds it be denumerableCARD-3V5 implies it be countableCARD-3V4\<bar>infiniteFINSET-1V2"
     sorry
qed "sorry"

mtheorem card_3_cl_18:
"cluster countableCARD-3V4\<bar>infiniteFINSET-1V2 also-is denumerableCARD-3V5 for setHIDDENM2"
proof
(*coherence*)
  show " for it be setHIDDENM2 holds it be countableCARD-3V4\<bar>infiniteFINSET-1V2 implies it be denumerableCARD-3V5"
sorry
qed "sorry"

mtheorem card_3_cl_19:
"cluster finiteFINSET-1V1 also-is countableCARD-3V4 for setHIDDENM2"
proof
(*coherence*)
  show " for it be setHIDDENM2 holds it be finiteFINSET-1V1 implies it be countableCARD-3V4"
     sorry
qed "sorry"

mtheorem card_3_cl_20:
"cluster omegaORDINAL1K4 as-term-is denumerableCARD-3V5"
proof
(*coherence*)
  show "omegaORDINAL1K4 be denumerableCARD-3V5"
     sorry
qed "sorry"

mtheorem card_3_cl_21:
"cluster denumerableCARD-3V5 for setHIDDENM2"
proof
(*existence*)
  show " ex it be setHIDDENM2 st it be denumerableCARD-3V5"
sorry
qed "sorry"

mtheorem card_3_th_93:
" for X be setHIDDENM2 holds X be countableCARD-3V4 iff ( ex f be FunctionFUNCT-1M1 st domRELAT-1K1 f =XBOOLE-0R4 omegaORDINAL1K4 & X c=TARSKIR1 rngFUNCT-1K2 f)"
  using card_1_th_12 card_1_th_47 sorry

mtheorem card_3_cl_22:
  mlet "X be countableCARD-3V4\<bar>setHIDDENM2"
"cluster note-that countableCARD-3V4 for SubsetSUBSET-1M2-of X"
proof
(*coherence*)
  show " for it be SubsetSUBSET-1M2-of X holds it be countableCARD-3V4"
sorry
qed "sorry"

mlemma card_3_lm_3:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds Y c=TARSKIR1 X & X be countableCARD-3V4 implies Y be countableCARD-3V4"
   sorry

mtheorem card_3_th_94:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X be countableCARD-3V4 implies X /\\XBOOLE-0K3 Y be countableCARD-3V4"
  using card_3_lm_3 xboole_1_th_17 sorry

mtheorem card_3_th_95:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X be countableCARD-3V4 implies X \\SUBSET-1K6 Y be countableCARD-3V4"
   sorry

mtheorem card_3_th_96:
" for A be  non emptyXBOOLE-0V1\<bar>countableCARD-3V4\<bar>setHIDDENM2 holds  ex f be FunctionFUNCT-2M1-of(omegaORDINAL1K4,A) st rngRELSET-1K2\<^bsub>(A)\<^esub> f =XBOOLE-0R4 A"
sorry

mtheorem card_3_th_97:
" for f be non-emptyFUNCT-1V4\<bar>FunctionFUNCT-1M1 holds  for g be non-emptyFUNCT-1V4\<bar>FunctionFUNCT-1M1 holds  for x be ElementSUBSET-1M1-of productCARD-3K4 f holds  for y be ElementSUBSET-1M1-of productCARD-3K4 g holds x +*FUNCT-4K1 y inTARSKIR2 productCARD-3K4 (f +*FUNCT-4K1 g)"
sorry

mtheorem card_3_th_98:
" for f be non-emptyFUNCT-1V4\<bar>FunctionFUNCT-1M1 holds  for g be non-emptyFUNCT-1V4\<bar>FunctionFUNCT-1M1 holds  for x be ElementSUBSET-1M1-of productCARD-3K4 (f +*FUNCT-4K1 g) holds x |CARD-3K11\<^bsub>(f +*FUNCT-4K1 g)\<^esub> domRELAT-1K1 g inTARSKIR2 productCARD-3K4 g"
sorry

mtheorem card_3_th_99:
" for f be non-emptyFUNCT-1V4\<bar>FunctionFUNCT-1M1 holds  for g be non-emptyFUNCT-1V4\<bar>FunctionFUNCT-1M1 holds f toleratesPARTFUN1R1 g implies ( for x be ElementSUBSET-1M1-of productCARD-3K4 (f +*FUNCT-4K1 g) holds x |CARD-3K11\<^bsub>(f +*FUNCT-4K1 g)\<^esub> domRELAT-1K1 f inTARSKIR2 productCARD-3K4 f)"
sorry

mtheorem card_3_th_100:
" for S be with-common-domainCARD-3V2\<bar>functionalFUNCT-1V6\<bar>setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds f inTARSKIR2 S implies domRELAT-1K1 f =XBOOLE-0R4 domRELAT-1K1 (product\<inverse>CARD-3K10 S)"
sorry

mtheorem card_3_th_101:
" for S be functionalFUNCT-1V6\<bar>setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds  for i be setHIDDENM2 holds f inTARSKIR2 S & i inTARSKIR2 domRELAT-1K1 (product\<inverse>CARD-3K10 S) implies f .FUNCT-1K1 i inTARSKIR2 product\<inverse>CARD-3K10 S .FUNCT-1K1 i"
sorry

mtheorem card_3_th_102:
" for S be with-common-domainCARD-3V2\<bar>functionalFUNCT-1V6\<bar>setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds  for i be setHIDDENM2 holds f inTARSKIR2 S & i inTARSKIR2 domRELAT-1K1 f implies f .FUNCT-1K1 i inTARSKIR2 product\<inverse>CARD-3K10 S .FUNCT-1K1 i"
sorry

mtheorem card_3_cl_23:
  mlet "X be with-common-domainCARD-3V2\<bar>setHIDDENM2"
"cluster note-that with-common-domainCARD-3V2 for SubsetSUBSET-1M2-of X"
proof
(*coherence*)
  show " for it be SubsetSUBSET-1M2-of X holds it be with-common-domainCARD-3V2"
    using card_3_def_10 sorry
qed "sorry"

mdef card_3_def_16 ("projCARD-3K12'( _ , _ ')" [0,0]228 ) where
  mlet "f be FunctionFUNCT-1M1", "x be objectHIDDENM1"
"func projCARD-3K12(f,x) \<rightarrow> FunctionFUNCT-1M1 means
  \<lambda>it. domRELAT-1K1 it =XBOOLE-0R4 productCARD-3K4 f & ( for y be FunctionFUNCT-1M1 holds y inTARSKIR2 domRELAT-1K1 it implies it .FUNCT-1K1 y =XBOOLE-0R4 y .FUNCT-1K1 x)"
proof-
  (*existence*)
    show " ex it be FunctionFUNCT-1M1 st domRELAT-1K1 it =XBOOLE-0R4 productCARD-3K4 f & ( for y be FunctionFUNCT-1M1 holds y inTARSKIR2 domRELAT-1K1 it implies it .FUNCT-1K1 y =XBOOLE-0R4 y .FUNCT-1K1 x)"
sorry
  (*uniqueness*)
    show " for it1 be FunctionFUNCT-1M1 holds  for it2 be FunctionFUNCT-1M1 holds (domRELAT-1K1 it1 =XBOOLE-0R4 productCARD-3K4 f & ( for y be FunctionFUNCT-1M1 holds y inTARSKIR2 domRELAT-1K1 it1 implies it1 .FUNCT-1K1 y =XBOOLE-0R4 y .FUNCT-1K1 x)) & (domRELAT-1K1 it2 =XBOOLE-0R4 productCARD-3K4 f & ( for y be FunctionFUNCT-1M1 holds y inTARSKIR2 domRELAT-1K1 it2 implies it2 .FUNCT-1K1 y =XBOOLE-0R4 y .FUNCT-1K1 x)) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mtheorem card_3_cl_24:
  mlet "f be FunctionFUNCT-1M1", "x be objectHIDDENM1"
"cluster projCARD-3K12(f,x) as-term-is productCARD-3K4 f -definedRELAT-1V4"
proof
(*coherence*)
  show "projCARD-3K12(f,x) be productCARD-3K4 f -definedRELAT-1V4"
    using card_3_def_16 sorry
qed "sorry"

mtheorem card_3_cl_25:
  mlet "f be FunctionFUNCT-1M1", "x be objectHIDDENM1"
"cluster projCARD-3K12(f,x) as-term-is totalPARTFUN1V1\<^bsub>(productCARD-3K4 f)\<^esub>"
proof
(*coherence*)
  show "projCARD-3K12(f,x) be totalPARTFUN1V1\<^bsub>(productCARD-3K4 f)\<^esub>"
    using card_3_def_16 sorry
qed "sorry"

mtheorem card_3_cl_26:
  mlet "f be non-emptyFUNCT-1V4\<bar>FunctionFUNCT-1M1"
"cluster note-that f -compatibleFUNCT-1V7 for ElementSUBSET-1M1-of productCARD-3K4 f"
proof
(*coherence*)
  show " for it be ElementSUBSET-1M1-of productCARD-3K4 f holds it be f -compatibleFUNCT-1V7"
sorry
qed "sorry"

mtheorem card_3_cl_27:
  mlet "I be setHIDDENM2", "f be I -definedRELAT-1V4\<bar>non-emptyFUNCT-1V4\<bar>FunctionFUNCT-1M1"
"cluster note-that I -definedRELAT-1V4 for ElementSUBSET-1M1-of productCARD-3K4 f"
proof
(*coherence*)
  show " for it be ElementSUBSET-1M1-of productCARD-3K4 f holds it be I -definedRELAT-1V4"
     sorry
qed "sorry"

mtheorem card_3_cl_28:
  mlet "f be FunctionFUNCT-1M1"
"cluster note-that f -compatibleFUNCT-1V7 for ElementSUBSET-1M1-of sproductCARD-3K8 f"
proof
(*coherence*)
  show " for it be ElementSUBSET-1M1-of sproductCARD-3K8 f holds it be f -compatibleFUNCT-1V7"
    using card_3_th_49 sorry
qed "sorry"

mtheorem card_3_cl_29:
  mlet "I be setHIDDENM2", "f be I -definedRELAT-1V4\<bar>FunctionFUNCT-1M1"
"cluster note-that I -definedRELAT-1V4 for ElementSUBSET-1M1-of sproductCARD-3K8 f"
proof
(*coherence*)
  show " for it be ElementSUBSET-1M1-of sproductCARD-3K8 f holds it be I -definedRELAT-1V4"
     sorry
qed "sorry"

mtheorem card_3_cl_30:
  mlet "I be setHIDDENM2", "f be totalPARTFUN1V1\<^bsub>(I)\<^esub>\<bar>I -definedRELAT-1V4\<bar>non-emptyFUNCT-1V4\<bar>FunctionFUNCT-1M1"
"cluster note-that totalPARTFUN1V1\<^bsub>(I)\<^esub> for ElementSUBSET-1M1-of productCARD-3K4 f"
proof
(*coherence*)
  show " for it be ElementSUBSET-1M1-of productCARD-3K4 f holds it be totalPARTFUN1V1\<^bsub>(I)\<^esub>"
sorry
qed "sorry"

mtheorem card_3_th_103:
" for I be setHIDDENM2 holds  for f be non-emptyFUNCT-1V4\<bar>I -definedRELAT-1V4\<bar>FunctionFUNCT-1M1 holds  for p be f -compatibleFUNCT-1V7\<bar>I -definedRELAT-1V4\<bar>FunctionFUNCT-1M1 holds p inTARSKIR2 sproductCARD-3K8 f"
sorry

mtheorem card_3_th_104:
" for I be setHIDDENM2 holds  for f be non-emptyFUNCT-1V4\<bar>I -definedRELAT-1V4\<bar>FunctionFUNCT-1M1 holds  for p be f -compatibleFUNCT-1V7\<bar>I -definedRELAT-1V4\<bar>FunctionFUNCT-1M1 holds  ex s be ElementSUBSET-1M1-of productCARD-3K4 f st p c=RELAT-1R2 s"
sorry

mtheorem card_3_cl_31:
  mlet "X be infiniteFINSET-1V2\<bar>setHIDDENM2", "a be setHIDDENM2"
"cluster X -->FUNCOP-1K7 a as-term-is infiniteFINSET-1V2"
proof
(*coherence*)
  show "X -->FUNCOP-1K7 a be infiniteFINSET-1V2"
     sorry
qed "sorry"

mtheorem card_3_cl_32:
"cluster infiniteFINSET-1V2 for FunctionFUNCT-1M1"
proof
(*existence*)
  show " ex it be FunctionFUNCT-1M1 st it be infiniteFINSET-1V2"
sorry
qed "sorry"

mlemma card_3_lm_4:
" for R be RelationRELAT-1M1 holds fieldRELAT-1K3 R be finiteFINSET-1V1 implies R be finiteFINSET-1V1"
sorry

mtheorem card_3_cl_33:
  mlet "R be infiniteFINSET-1V2\<bar>RelationRELAT-1M1"
"cluster fieldRELAT-1K3 R as-term-is infiniteFINSET-1V2"
proof
(*coherence*)
  show "fieldRELAT-1K3 R be infiniteFINSET-1V2"
    using card_3_lm_4 sorry
qed "sorry"

mtheorem card_3_cl_34:
  mlet "X be infiniteFINSET-1V2\<bar>setHIDDENM2"
"cluster RelInclWELLORD2K1 X as-term-is infiniteFINSET-1V2"
proof
(*coherence*)
  show "RelInclWELLORD2K1 X be infiniteFINSET-1V2"
    using card_1_th_63 sorry
qed "sorry"

mtheorem card_3_th_105:
" for R be RelationRELAT-1M1 holds  for S be RelationRELAT-1M1 holds (R,S)are-isomorphicWELLORD1R4 & R be finiteFINSET-1V1 implies S be finiteFINSET-1V1"
sorry

mtheorem card_3_th_106:
"product\<inverse>CARD-3K10 {TARSKIK1 {}XBOOLE-0K1 } =FUNCT-1R1 {}XBOOLE-0K1"
sorry

mtheorem card_3_th_107:
" for I be setHIDDENM2 holds  for f be non-emptyRELAT-1V2\<bar>ManySortedSetPBOOLEM1-of I holds  for s be f -compatibleFUNCT-1V7\<bar>ManySortedSetPBOOLEM1-of I holds s inTARSKIR2 productCARD-3K4 f"
sorry

mtheorem card_3_cl_35:
  mlet "I be setHIDDENM2", "f be non-emptyRELAT-1V2\<bar>ManySortedSetPBOOLEM1-of I"
"cluster note-that totalPARTFUN1V1\<^bsub>(I)\<^esub> for ElementSUBSET-1M1-of productCARD-3K4 f"
proof
(*coherence*)
  show " for it be ElementSUBSET-1M1-of productCARD-3K4 f holds it be totalPARTFUN1V1\<^bsub>(I)\<^esub>"
     sorry
qed "sorry"

mdef card_3_def_17 ("downCARD-3K13\<^bsub>'( _ , _ ')\<^esub>  _ " [0,0,164]164 ) where
  mlet "I be setHIDDENM2", "f be non-emptyRELAT-1V2\<bar>ManySortedSetPBOOLEM1-of I", "M be f -compatibleFUNCT-1V7\<bar>ManySortedSetPBOOLEM1-of I"
"func downCARD-3K13\<^bsub>(I,f)\<^esub> M \<rightarrow> ElementSUBSET-1M1-of productCARD-3K4 f equals
  M"
proof-
  (*coherence*)
    show "M be ElementSUBSET-1M1-of productCARD-3K4 f"
      using card_3_th_107 sorry
qed "sorry"

mtheorem card_3_th_108:
" for X be functionalFUNCT-1V6\<bar>with-common-domainCARD-3V2\<bar>setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds f inTARSKIR2 X implies domRELAT-1K1 f =XBOOLE-0R4 DOMCARD-3K9 X"
  using card_3_lm_2 sorry

mtheorem card_3_th_109:
" for x be objectHIDDENM1 holds  for X be  non emptyXBOOLE-0V1\<bar>functionalFUNCT-1V6\<bar>setHIDDENM2 holds ( for f be FunctionFUNCT-1M1 holds f inTARSKIR2 X implies x inHIDDENR3 domRELAT-1K1 f) implies x inHIDDENR3 DOMCARD-3K9 X"
sorry

theorem card_3_sch_3:
  fixes Xf0 Ff1 Pp2 
  assumes
[ty]: "Xf0 be setHIDDENM2" and
  [ty_func]: "\<And> x1. x1 be objectHIDDENM1 \<Longrightarrow> Ff1(x1) be setHIDDENM2"
  shows " ex f be FunctionFUNCT-1M1 st domRELAT-1K1 f =XBOOLE-0R4 Xf0 & ( for x be setHIDDENM2 holds x inTARSKIR2 Xf0 implies ( for y be setHIDDENM2 holds y inTARSKIR2 f .FUNCT-1K1 x iff y inTARSKIR2 Ff1(x) & Pp2(x,y)))"
sorry

syntax CARD_3V6 :: "Ty" ("uncountableCARD-3V6" 70)
translations "uncountableCARD-3V6" \<rightharpoonup> " non countableCARD-3V4"

mtheorem card_3_cl_36:
"cluster uncountableCARD-3V6 also-is  non emptyXBOOLE-0V1 for setHIDDENM2"
proof
(*coherence*)
  show " for it be setHIDDENM2 holds it be uncountableCARD-3V6 implies it be  non emptyXBOOLE-0V1"
     sorry
qed "sorry"

end
