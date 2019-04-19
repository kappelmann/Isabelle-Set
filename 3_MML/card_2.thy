theory card_2
  imports ordinal3 nat_1 funct_6 fraenkel
   "../mizar_extension/E_number"
begin
(*begin*)
reserve A, B for "OrdinalORDINAL1M3"
reserve K, M, N for "CardinalCARD-1M1"
reserve x, x1, x2, y, y1, y2, z, u for "objectHIDDENM1"
reserve X, Y, Z, X1, X2, Y1, Y2 for "setHIDDENM2"
reserve f, g for "FunctionFUNCT-1M1"
mtheorem card_2_th_1:
" for x be objectHIDDENM1 holds  for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds x inHIDDENR3 X & (X,Y)are-equipotentWELLORD2R2 implies Y <>HIDDENR2 {}XBOOLE-0K1 & ( ex x be objectHIDDENM1 st x inHIDDENR3 Y)"
sorry

mtheorem card_2_th_2:
" for X be setHIDDENM2 holds (boolZFMISC-1K1 X,boolZFMISC-1K1 (cardCARD-1K1 X))are-equipotentWELLORD2R2 & cardCARD-1K1 (boolZFMISC-1K1 X) =XBOOLE-0R4 cardCARD-1K1 (boolZFMISC-1K1 (cardCARD-1K1 X))"
sorry

mtheorem card_2_th_3:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds Z inTARSKIR2 FuncsFUNCT-2K1(X,Y) implies (Z,X)are-equipotentWELLORD2R2 & cardCARD-1K1 Z =XBOOLE-0R4 cardCARD-1K1 X"
sorry

mlemma card_2_lm_1:
" for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds  for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds x1 <>HIDDENR2 x2 implies (A +^ORDINAL2K10 B,[:ZFMISC-1K2 A,{TARSKIK1 x1} :] \\/XBOOLE-0K2 [:ZFMISC-1K2 B,{TARSKIK1 x2} :])are-equipotentWELLORD2R2 & cardCARD-1K1 (A +^ORDINAL2K10 B) =XBOOLE-0R4 cardCARD-1K1 ([:ZFMISC-1K2 A,{TARSKIK1 x1} :] \\/XBOOLE-0K2 [:ZFMISC-1K2 B,{TARSKIK1 x2} :])"
sorry

mlemma card_2_lm_2:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds ([:ZFMISC-1K2 X,Y :],[:ZFMISC-1K2 Y,X :])are-equipotentWELLORD2R2 & cardCARD-1K1 ([:ZFMISC-1K2 X,Y :]) =XBOOLE-0R4 cardCARD-1K1 ([:ZFMISC-1K2 Y,X :])"
sorry

mdef card_2_def_1 (" _ +`CARD-2K1  _ " [132,132]132 ) where
  mlet "M be CardinalCARD-1M1", "N be CardinalCARD-1M1"
"func M +`CARD-2K1 N \<rightarrow> CardinalCARD-1M1 equals
  cardCARD-1K1 (M +^ORDINAL2K10 N)"
proof-
  (*coherence*)
    show "cardCARD-1K1 (M +^ORDINAL2K10 N) be CardinalCARD-1M1"
       sorry
qed "sorry"

mtheorem CARD_2K1_commutativity:
" for M be CardinalCARD-1M1 holds  for N be CardinalCARD-1M1 holds M +`CARD-2K1 N =HIDDENR1 N +`CARD-2K1 M"
sorry

mdef card_2_def_2 (" _ *`CARD-2K2  _ " [164,164]164 ) where
  mlet "M be CardinalCARD-1M1", "N be CardinalCARD-1M1"
"func M *`CARD-2K2 N \<rightarrow> CardinalCARD-1M1 equals
  cardCARD-1K1 ([:ZFMISC-1K2 M,N :])"
proof-
  (*coherence*)
    show "cardCARD-1K1 ([:ZFMISC-1K2 M,N :]) be CardinalCARD-1M1"
       sorry
qed "sorry"

mtheorem CARD_2K2_commutativity:
" for M be CardinalCARD-1M1 holds  for N be CardinalCARD-1M1 holds M *`CARD-2K2 N =HIDDENR1 N *`CARD-2K2 M"
sorry

mdef card_2_def_3 ("expCARD-2K3'( _ , _ ')" [0,0]164 ) where
  mlet "M be CardinalCARD-1M1", "N be CardinalCARD-1M1"
"func expCARD-2K3(M,N) \<rightarrow> CardinalCARD-1M1 equals
  cardCARD-1K1 (FuncsFUNCT-2K1(N,M))"
proof-
  (*coherence*)
    show "cardCARD-1K1 (FuncsFUNCT-2K1(N,M)) be CardinalCARD-1M1"
       sorry
qed "sorry"

mtheorem card_2_th_4:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds ([:ZFMISC-1K2 X,Y :],[:ZFMISC-1K2 Y,X :])are-equipotentWELLORD2R2 & cardCARD-1K1 ([:ZFMISC-1K2 X,Y :]) =XBOOLE-0R4 cardCARD-1K1 ([:ZFMISC-1K2 Y,X :])"
  using card_2_lm_2 sorry

mtheorem card_2_th_5:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds ([:ZFMISC-1K2 [:ZFMISC-1K2 X,Y :],Z :],[:ZFMISC-1K2 X,[:ZFMISC-1K2 Y,Z :] :])are-equipotentWELLORD2R2 & cardCARD-1K1 ([:ZFMISC-1K2 [:ZFMISC-1K2 X,Y :],Z :]) =XBOOLE-0R4 cardCARD-1K1 ([:ZFMISC-1K2 X,[:ZFMISC-1K2 Y,Z :] :])"
sorry

mlemma card_2_lm_3:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds ([:ZFMISC-1K2 X,Y :],[:ZFMISC-1K2 cardCARD-1K1 X,Y :])are-equipotentWELLORD2R2"
sorry

(*\$CT*)
mtheorem card_2_th_7:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds ((((([:ZFMISC-1K2 X,Y :],[:ZFMISC-1K2 cardCARD-1K1 X,Y :])are-equipotentWELLORD2R2 & ([:ZFMISC-1K2 X,Y :],[:ZFMISC-1K2 X,cardCARD-1K1 Y :])are-equipotentWELLORD2R2) & ([:ZFMISC-1K2 X,Y :],[:ZFMISC-1K2 cardCARD-1K1 X,cardCARD-1K1 Y :])are-equipotentWELLORD2R2) & cardCARD-1K1 ([:ZFMISC-1K2 X,Y :]) =XBOOLE-0R4 cardCARD-1K1 ([:ZFMISC-1K2 cardCARD-1K1 X,Y :])) & cardCARD-1K1 ([:ZFMISC-1K2 X,Y :]) =XBOOLE-0R4 cardCARD-1K1 ([:ZFMISC-1K2 X,cardCARD-1K1 Y :])) & cardCARD-1K1 ([:ZFMISC-1K2 X,Y :]) =XBOOLE-0R4 cardCARD-1K1 ([:ZFMISC-1K2 cardCARD-1K1 X,cardCARD-1K1 Y :])"
sorry

mtheorem card_2_th_8:
" for X1 be setHIDDENM2 holds  for X2 be setHIDDENM2 holds  for Y1 be setHIDDENM2 holds  for Y2 be setHIDDENM2 holds (X1,Y1)are-equipotentWELLORD2R2 & (X2,Y2)are-equipotentWELLORD2R2 implies ([:ZFMISC-1K2 X1,X2 :],[:ZFMISC-1K2 Y1,Y2 :])are-equipotentWELLORD2R2 & cardCARD-1K1 ([:ZFMISC-1K2 X1,X2 :]) =XBOOLE-0R4 cardCARD-1K1 ([:ZFMISC-1K2 Y1,Y2 :])"
sorry

mtheorem card_2_th_9:
" for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds  for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds x1 <>HIDDENR2 x2 implies (A +^ORDINAL2K10 B,[:ZFMISC-1K2 A,{TARSKIK1 x1} :] \\/XBOOLE-0K2 [:ZFMISC-1K2 B,{TARSKIK1 x2} :])are-equipotentWELLORD2R2 & cardCARD-1K1 (A +^ORDINAL2K10 B) =XBOOLE-0R4 cardCARD-1K1 ([:ZFMISC-1K2 A,{TARSKIK1 x1} :] \\/XBOOLE-0K2 [:ZFMISC-1K2 B,{TARSKIK1 x2} :])"
  using card_2_lm_1 sorry

mtheorem card_2_th_10:
" for K be CardinalCARD-1M1 holds  for M be CardinalCARD-1M1 holds  for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds x1 <>HIDDENR2 x2 implies (K +`CARD-2K1 M,[:ZFMISC-1K2 K,{TARSKIK1 x1} :] \\/XBOOLE-0K2 [:ZFMISC-1K2 M,{TARSKIK1 x2} :])are-equipotentWELLORD2R2 & K +`CARD-2K1 M =XBOOLE-0R4 cardCARD-1K1 ([:ZFMISC-1K2 K,{TARSKIK1 x1} :] \\/XBOOLE-0K2 [:ZFMISC-1K2 M,{TARSKIK1 x2} :])"
sorry

mtheorem card_2_th_11:
" for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds (A *^ORDINAL2K11 B,[:ZFMISC-1K2 A,B :])are-equipotentWELLORD2R2 & cardCARD-1K1 (A *^ORDINAL2K11 B) =XBOOLE-0R4 cardCARD-1K1 ([:ZFMISC-1K2 A,B :])"
sorry

mtheorem card_2_th_12:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for y1 be objectHIDDENM1 holds  for y2 be objectHIDDENM1 holds  for X1 be setHIDDENM2 holds  for X2 be setHIDDENM2 holds  for Y1 be setHIDDENM2 holds  for Y2 be setHIDDENM2 holds (((X1,Y1)are-equipotentWELLORD2R2 & (X2,Y2)are-equipotentWELLORD2R2) & x1 <>HIDDENR2 x2) & y1 <>HIDDENR2 y2 implies ([:ZFMISC-1K2 X1,{TARSKIK1 x1} :] \\/XBOOLE-0K2 [:ZFMISC-1K2 X2,{TARSKIK1 x2} :],[:ZFMISC-1K2 Y1,{TARSKIK1 y1} :] \\/XBOOLE-0K2 [:ZFMISC-1K2 Y2,{TARSKIK1 y2} :])are-equipotentWELLORD2R2 & cardCARD-1K1 ([:ZFMISC-1K2 X1,{TARSKIK1 x1} :] \\/XBOOLE-0K2 [:ZFMISC-1K2 X2,{TARSKIK1 x2} :]) =XBOOLE-0R4 cardCARD-1K1 ([:ZFMISC-1K2 Y1,{TARSKIK1 y1} :] \\/XBOOLE-0K2 [:ZFMISC-1K2 Y2,{TARSKIK1 y2} :])"
sorry

mtheorem card_2_th_13:
" for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds cardCARD-1K1 (A +^ORDINAL2K10 B) =XBOOLE-0R4 cardCARD-1K1 A +`CARD-2K1 cardCARD-1K1 B"
sorry

mtheorem card_2_th_14:
" for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds cardCARD-1K1 (A *^ORDINAL2K11 B) =XBOOLE-0R4 cardCARD-1K1 A *`CARD-2K2 cardCARD-1K1 B"
sorry

mtheorem card_2_th_15:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds ([:ZFMISC-1K2 X,{TARSKIK1 0NUMBERSK6 } :] \\/XBOOLE-0K2 [:ZFMISC-1K2 Y,{TARSKIK1 \<one>\<^sub>M} :],[:ZFMISC-1K2 Y,{TARSKIK1 0NUMBERSK6 } :] \\/XBOOLE-0K2 [:ZFMISC-1K2 X,{TARSKIK1 \<one>\<^sub>M} :])are-equipotentWELLORD2R2 & cardCARD-1K1 ([:ZFMISC-1K2 X,{TARSKIK1 0NUMBERSK6 } :] \\/XBOOLE-0K2 [:ZFMISC-1K2 Y,{TARSKIK1 \<one>\<^sub>M} :]) =XBOOLE-0R4 cardCARD-1K1 ([:ZFMISC-1K2 Y,{TARSKIK1 0NUMBERSK6 } :] \\/XBOOLE-0K2 [:ZFMISC-1K2 X,{TARSKIK1 \<one>\<^sub>M} :])"
  using card_2_th_12 sorry

mtheorem card_2_th_16:
" for X1 be setHIDDENM2 holds  for X2 be setHIDDENM2 holds  for Y1 be setHIDDENM2 holds  for Y2 be setHIDDENM2 holds ([:ZFMISC-1K2 X1,X2 :] \\/XBOOLE-0K2 [:ZFMISC-1K2 Y1,Y2 :],[:ZFMISC-1K2 X2,X1 :] \\/XBOOLE-0K2 [:ZFMISC-1K2 Y2,Y1 :])are-equipotentWELLORD2R2 & cardCARD-1K1 ([:ZFMISC-1K2 X1,X2 :] \\/XBOOLE-0K2 [:ZFMISC-1K2 Y1,Y2 :]) =XBOOLE-0R4 cardCARD-1K1 ([:ZFMISC-1K2 X2,X1 :] \\/XBOOLE-0K2 [:ZFMISC-1K2 Y2,Y1 :])"
sorry

mtheorem card_2_th_17:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds x <>HIDDENR2 y implies cardCARD-1K1 X +`CARD-2K1 cardCARD-1K1 Y =XBOOLE-0R4 cardCARD-1K1 ([:ZFMISC-1K2 X,{TARSKIK1 x} :] \\/XBOOLE-0K2 [:ZFMISC-1K2 Y,{TARSKIK1 y} :])"
sorry

mtheorem card_2_th_18:
" for M be CardinalCARD-1M1 holds M +`CARD-2K1 0NUMBERSK6 =XBOOLE-0R4 M"
sorry

mlemma card_2_lm_4:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds x <>HIDDENR2 y implies [:ZFMISC-1K2 X,{TARSKIK1 x} :] missesXBOOLE-0R1 [:ZFMISC-1K2 Y,{TARSKIK1 y} :]"
sorry

mtheorem card_2_th_19:
" for K be CardinalCARD-1M1 holds  for M be CardinalCARD-1M1 holds  for N be CardinalCARD-1M1 holds (K +`CARD-2K1 M)+`CARD-2K1 N =XBOOLE-0R4 K +`CARD-2K1 (M +`CARD-2K1 N)"
sorry

mtheorem card_2_th_20:
" for K be CardinalCARD-1M1 holds K *`CARD-2K2 (0NUMBERSK6) =XBOOLE-0R4 0NUMBERSK6"
   sorry

mtheorem card_2_th_21:
" for K be CardinalCARD-1M1 holds K *`CARD-2K2 \<one>\<^sub>M =XBOOLE-0R4 K"
sorry

mtheorem card_2_th_22:
" for K be CardinalCARD-1M1 holds  for M be CardinalCARD-1M1 holds  for N be CardinalCARD-1M1 holds (K *`CARD-2K2 M)*`CARD-2K2 N =XBOOLE-0R4 K *`CARD-2K2 (M *`CARD-2K2 N)"
sorry

mtheorem card_2_th_23:
" for K be CardinalCARD-1M1 holds \<two>\<^sub>M *`CARD-2K2 K =XBOOLE-0R4 K +`CARD-2K1 K"
sorry

mtheorem card_2_th_24:
" for K be CardinalCARD-1M1 holds  for M be CardinalCARD-1M1 holds  for N be CardinalCARD-1M1 holds K *`CARD-2K2 (M +`CARD-2K1 N) =XBOOLE-0R4 K *`CARD-2K2 M +`CARD-2K1 K *`CARD-2K2 N"
sorry

mtheorem card_2_th_25:
" for K be CardinalCARD-1M1 holds expCARD-2K3(K,0NUMBERSK6) =XBOOLE-0R4 \<one>\<^sub>M"
sorry

mtheorem card_2_th_26:
" for K be CardinalCARD-1M1 holds K <>HIDDENR2 0NUMBERSK6 implies expCARD-2K3(0NUMBERSK6,K) =XBOOLE-0R4 0NUMBERSK6"
   sorry

mtheorem card_2_th_27:
" for K be CardinalCARD-1M1 holds expCARD-2K3(K,\<one>\<^sub>M) =XBOOLE-0R4 K & expCARD-2K3(\<one>\<^sub>M,K) =XBOOLE-0R4 \<one>\<^sub>M"
sorry

mtheorem card_2_th_28:
" for K be CardinalCARD-1M1 holds  for M be CardinalCARD-1M1 holds  for N be CardinalCARD-1M1 holds expCARD-2K3(K,M +`CARD-2K1 N) =XBOOLE-0R4 (expCARD-2K3(K,M))*`CARD-2K2 (expCARD-2K3(K,N))"
sorry

mtheorem card_2_th_29:
" for K be CardinalCARD-1M1 holds  for M be CardinalCARD-1M1 holds  for N be CardinalCARD-1M1 holds expCARD-2K3(K *`CARD-2K2 M,N) =XBOOLE-0R4 (expCARD-2K3(K,N))*`CARD-2K2 (expCARD-2K3(M,N))"
sorry

mtheorem card_2_th_30:
" for K be CardinalCARD-1M1 holds  for M be CardinalCARD-1M1 holds  for N be CardinalCARD-1M1 holds expCARD-2K3(K,M *`CARD-2K2 N) =XBOOLE-0R4 expCARD-2K3(expCARD-2K3(K,M),N)"
sorry

(*\$N The Number of Subsets of a Set*)
mtheorem card_2_th_31:
" for X be setHIDDENM2 holds expCARD-2K3(\<two>\<^sub>M,cardCARD-1K1 X) =XBOOLE-0R4 cardCARD-1K1 (boolZFMISC-1K1 X)"
sorry

mtheorem card_2_th_32:
" for K be CardinalCARD-1M1 holds expCARD-2K3(K,\<two>\<^sub>M) =XBOOLE-0R4 K *`CARD-2K2 K"
  using card_1_th_50 funct_5_th_66 sorry

mtheorem card_2_th_33:
" for K be CardinalCARD-1M1 holds  for M be CardinalCARD-1M1 holds expCARD-2K3(K +`CARD-2K1 M,\<two>\<^sub>M) =XBOOLE-0R4 (K *`CARD-2K2 K +`CARD-2K1 (\<two>\<^sub>M *`CARD-2K2 K)*`CARD-2K2 M)+`CARD-2K1 M *`CARD-2K2 M"
sorry

mtheorem card_2_th_34:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds cardCARD-1K1 (X \\/XBOOLE-0K2 Y) c=ORDINAL1R1 cardCARD-1K1 X +`CARD-2K1 cardCARD-1K1 Y"
sorry

mtheorem card_2_th_35:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X missesXBOOLE-0R1 Y implies cardCARD-1K1 (X \\/XBOOLE-0K2 Y) =XBOOLE-0R4 cardCARD-1K1 X +`CARD-2K1 cardCARD-1K1 Y"
sorry

reserve m, n for "NatORDINAL1M6"
mtheorem card_2_th_36:
" for m be NatORDINAL1M6 holds  for n be NatORDINAL1M6 holds n +XCMPLX-0K2 m =XBOOLE-0R4 n +^ORDINAL3K8 m"
sorry

mtheorem card_2_th_37:
" for m be NatORDINAL1M6 holds  for n be NatORDINAL1M6 holds n *XCMPLX-0K3 m =XBOOLE-0R4 n *^ORDINAL3K9 m"
sorry

mtheorem card_2_th_38:
" for m be NatORDINAL1M6 holds  for n be NatORDINAL1M6 holds cardCARD-1K4 (n +XCMPLX-0K2 m) =XBOOLE-0R4 cardCARD-1K4 n +`CARD-2K1 cardCARD-1K4 m"
  using card_2_th_36 sorry

mtheorem card_2_th_39:
" for m be NatORDINAL1M6 holds  for n be NatORDINAL1M6 holds cardCARD-1K4 (n *XCMPLX-0K3 m) =XBOOLE-0R4 cardCARD-1K4 n *`CARD-2K2 cardCARD-1K4 m"
sorry

mtheorem card_2_th_40:
" for X be finiteFINSET-1V1\<bar>setHIDDENM2 holds  for Y be finiteFINSET-1V1\<bar>setHIDDENM2 holds X missesXBOOLE-0R1 Y implies cardCARD-1K4 (X \\/XBOOLE-0K2 Y) =XBOOLE-0R4 cardCARD-1K4 X +XCMPLX-0K2 cardCARD-1K4 Y"
sorry

mtheorem card_2_th_41:
" for x be objectHIDDENM1 holds  for X be finiteFINSET-1V1\<bar>setHIDDENM2 holds  not x inHIDDENR3 X implies cardCARD-1K4 (X \\/XBOOLE-0K2 {TARSKIK1 x}) =XBOOLE-0R4 cardCARD-1K4 X +XCMPLX-0K2 \<one>\<^sub>M"
sorry

mtheorem card_2_th_42:
" for X be setHIDDENM2 holds cardCARD-1K1 X =XBOOLE-0R4 \<one>\<^sub>M iff ( ex x be objectHIDDENM1 st X =XBOOLE-0R4 {TARSKIK1 x})"
sorry

mtheorem card_2_th_43:
" for X be finiteFINSET-1V1\<bar>setHIDDENM2 holds  for Y be finiteFINSET-1V1\<bar>setHIDDENM2 holds cardCARD-1K4 (X \\/XBOOLE-0K2 Y) <=XXREAL-0R1 cardCARD-1K4 X +XCMPLX-0K2 cardCARD-1K4 Y"
sorry

mtheorem card_2_th_44:
" for X be finiteFINSET-1V1\<bar>setHIDDENM2 holds  for Y be finiteFINSET-1V1\<bar>setHIDDENM2 holds Y c=TARSKIR1 X implies cardCARD-1K4 (X \\SUBSET-1K6 Y) =XBOOLE-0R4 cardCARD-1K4 X -XCMPLX-0K6 cardCARD-1K4 Y"
sorry

mtheorem card_2_th_45:
" for X be finiteFINSET-1V1\<bar>setHIDDENM2 holds  for Y be finiteFINSET-1V1\<bar>setHIDDENM2 holds cardCARD-1K4 (X \\/XBOOLE-0K2 Y) =XBOOLE-0R4 (cardCARD-1K4 X +XCMPLX-0K2 cardCARD-1K4 Y)-XCMPLX-0K6 cardCARD-1K4 (X /\\XBOOLE-0K3 Y)"
sorry

mtheorem card_2_th_46:
" for X be finiteFINSET-1V1\<bar>setHIDDENM2 holds  for Y be finiteFINSET-1V1\<bar>setHIDDENM2 holds cardCARD-1K4 ([:ZFMISC-1K2 X,Y :]) =XBOOLE-0R4 cardCARD-1K4 X *XCMPLX-0K3 cardCARD-1K4 Y"
sorry

mtheorem card_2_th_47:
" for f be finiteFINSET-1V1\<bar>FunctionFUNCT-1M1 holds cardCARD-1K4 (rngFUNCT-1K2 f) <=XXREAL-0R1 cardCARD-1K4 (domRELAT-1K1 f)"
sorry

mtheorem card_2_th_48:
" for X be finiteFINSET-1V1\<bar>setHIDDENM2 holds  for Y be finiteFINSET-1V1\<bar>setHIDDENM2 holds X c<XBOOLE-0R2 Y implies cardCARD-1K4 X <XXREAL-0R3 cardCARD-1K4 Y & cardCARD-1K4 X inTARSKIR2 SegmCARD-1K5 cardCARD-1K4 Y"
sorry

mtheorem card_2_th_49:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds (cardCARD-1K1 X c=ORDINAL1R1 cardCARD-1K1 Y or cardCARD-1K1 X inTARSKIR2 cardCARD-1K1 Y) & Y be finiteFINSET-1V1 implies X be finiteFINSET-1V1"
sorry

reserve x1, x2, x3, x4, x5, x6, x7, x8 for "objectHIDDENM1"
mtheorem card_2_th_50:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds cardCARD-1K4 {TARSKIK2 x1,x2 } <=XXREAL-0R1 \<two>\<^sub>M"
sorry

mtheorem card_2_th_51:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds cardCARD-1K4 {ENUMSET1K1 x1,x2,x3 } <=XXREAL-0R1 \<three>\<^sub>M"
sorry

mtheorem card_2_th_52:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for x4 be objectHIDDENM1 holds cardCARD-1K4 {ENUMSET1K2 x1,x2,x3,x4 } <=XXREAL-0R1 \<four>\<^sub>M"
sorry

mtheorem card_2_th_53:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for x4 be objectHIDDENM1 holds  for x5 be objectHIDDENM1 holds cardCARD-1K4 {ENUMSET1K3 x1,x2,x3,x4,x5 } <=XXREAL-0R1 \<five>\<^sub>M"
sorry

mtheorem card_2_th_54:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for x4 be objectHIDDENM1 holds  for x5 be objectHIDDENM1 holds  for x6 be objectHIDDENM1 holds cardCARD-1K4 {ENUMSET1K4 x1,x2,x3,x4,x5,x6 } <=XXREAL-0R1 \<six>\<^sub>M"
sorry

mtheorem card_2_th_55:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for x4 be objectHIDDENM1 holds  for x5 be objectHIDDENM1 holds  for x6 be objectHIDDENM1 holds  for x7 be objectHIDDENM1 holds cardCARD-1K4 {ENUMSET1K5 x1,x2,x3,x4,x5,x6,x7 } <=XXREAL-0R1 \<seven>\<^sub>M"
sorry

mtheorem card_2_th_56:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for x4 be objectHIDDENM1 holds  for x5 be objectHIDDENM1 holds  for x6 be objectHIDDENM1 holds  for x7 be objectHIDDENM1 holds  for x8 be objectHIDDENM1 holds cardCARD-1K4 {ENUMSET1K6 x1,x2,x3,x4,x5,x6,x7,x8 } <=XXREAL-0R1 \<eight>\<^sub>M"
sorry

mtheorem card_2_th_57:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds x1 <>HIDDENR2 x2 implies cardCARD-1K4 {TARSKIK2 x1,x2 } =XBOOLE-0R4 \<two>\<^sub>M"
sorry

mtheorem card_2_th_58:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds (x1 <>HIDDENR2 x2 & x1 <>HIDDENR2 x3) & x2 <>HIDDENR2 x3 implies cardCARD-1K4 {ENUMSET1K1 x1,x2,x3 } =XBOOLE-0R4 \<three>\<^sub>M"
sorry

mtheorem card_2_th_59:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for x4 be objectHIDDENM1 holds ((((x1 <>HIDDENR2 x2 & x1 <>HIDDENR2 x3) & x1 <>HIDDENR2 x4) & x2 <>HIDDENR2 x3) & x2 <>HIDDENR2 x4) & x3 <>HIDDENR2 x4 implies cardCARD-1K4 {ENUMSET1K2 x1,x2,x3,x4 } =XBOOLE-0R4 \<four>\<^sub>M"
sorry

(*begin*)
mtheorem card_2_th_60:
" for X be setHIDDENM2 holds cardCARD-1K1 X =XBOOLE-0R4 \<two>\<^sub>M implies ( ex x be objectHIDDENM1 st  ex y be objectHIDDENM1 st x <>HIDDENR2 y & X =XBOOLE-0R4 {TARSKIK2 x,y })"
sorry

mtheorem card_2_th_61:
" for f be FunctionFUNCT-1M1 holds cardCARD-1K1 (rngFUNCT-1K2 f) c=ORDINAL1R1 cardCARD-1K1 (domRELAT-1K1 f)"
sorry

mlemma card_2_lm_5:
" for n be NatORDINAL1M6 holds ( for Z be finiteFINSET-1V1\<bar>setHIDDENM2 holds (cardCARD-1K4 Z =XBOOLE-0R4 n & Z <>HIDDENR2 {}XBOOLE-0K1) & ( for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X inTARSKIR2 Z & Y inTARSKIR2 Z implies X c=TARSKIR1 Y or Y c=TARSKIR1 X) implies unionTARSKIK3 Z inTARSKIR2 Z) implies ( for Z be finiteFINSET-1V1\<bar>setHIDDENM2 holds cardCARD-1K4 Z =XBOOLE-0R4 n +XCMPLX-0K2 \<one>\<^sub>M & (Z <>HIDDENR2 {}XBOOLE-0K1 & ( for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X inTARSKIR2 Z & Y inTARSKIR2 Z implies X c=TARSKIR1 Y or Y c=TARSKIR1 X)) implies unionTARSKIK3 Z inTARSKIR2 Z)"
sorry

mlemma card_2_lm_6:
" for Z be finiteFINSET-1V1\<bar>setHIDDENM2 holds Z <>HIDDENR2 {}XBOOLE-0K1 & ( for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X inTARSKIR2 Z & Y inTARSKIR2 Z implies X c=TARSKIR1 Y or Y c=TARSKIR1 X) implies unionTARSKIK3 Z inTARSKIR2 Z"
sorry

mtheorem card_2_th_62:
" for Z be setHIDDENM2 holds (Z <>HIDDENR2 {}XBOOLE-0K1 & Z be finiteFINSET-1V1) & ( for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X inTARSKIR2 Z & Y inTARSKIR2 Z implies X c=TARSKIR1 Y or Y c=TARSKIR1 X) implies unionTARSKIK3 Z inTARSKIR2 Z"
  using card_2_lm_6 sorry

mtheorem card_2_th_63:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for x3 be objectHIDDENM1 holds  for x4 be objectHIDDENM1 holds  for x5 be objectHIDDENM1 holds (x1,x2,x3,x4,x5)are-mutually-distinctZFMISC-1R3 implies cardCARD-1K4 {ENUMSET1K3 x1,x2,x3,x4,x5 } =XBOOLE-0R4 \<five>\<^sub>M"
sorry

mtheorem card_2_th_64:
" for M1 be setHIDDENM2 holds  for M2 be setHIDDENM2 holds cardCARD-1K1 M1 =XBOOLE-0R4 0NUMBERSK6 & cardCARD-1K1 M2 =XBOOLE-0R4 0NUMBERSK6 implies M1 =XBOOLE-0R4 M2"
sorry

mtheorem card_2_cl_1:
  mlet "x be objectHIDDENM1", "y be objectHIDDENM1"
"cluster [TARSKIK4 x,y ] as-term-is  non naturalORDINAL1V7"
proof
(*coherence*)
  show "[TARSKIK4 x,y ] be  non naturalORDINAL1V7"
sorry
qed "sorry"

(*begin*)
reserve A, B, C for "OrdinalORDINAL1M3"
reserve K, L, M, N for "CardinalCARD-1M1"
reserve x, y, y1, y2, z, u for "objectHIDDENM1"
reserve X, Y, Z, Z1, Z2 for "setHIDDENM2"
reserve n for "NatORDINAL1M6"
reserve f, f1, g, h for "FunctionFUNCT-1M1"
mtheorem card_2_th_65:
" for M be CardinalCARD-1M1 holds  for N be CardinalCARD-1M1 holds SumCARD-3K6 (M -->FUNCOP-1K7 N) =XBOOLE-0R4 M *`CARD-2K2 N"
sorry

mtheorem card_2_th_66:
" for M be CardinalCARD-1M1 holds  for N be CardinalCARD-1M1 holds ProductCARD-3K7 (N -->FUNCOP-1K7 M) =XBOOLE-0R4 expCARD-2K3(M,N)"
  using card_3_th_11 sorry

theorem card_2_sch_1:
  fixes Xf0 Pp2 
  assumes
[ty]: "Xf0 be finiteFINSET-1V1\<bar>setHIDDENM2" and
   A1: "Xf0 <>HIDDENR2 {}XBOOLE-0K1" and
   A2: " for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds Pp2(x,y) & Pp2(y,x) implies x =HIDDENR1 y" and
   A3: " for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for z be objectHIDDENM1 holds Pp2(x,y) & Pp2(y,z) implies Pp2(x,z)"
  shows " ex x be objectHIDDENM1 st x inHIDDENR3 Xf0 & ( for y be objectHIDDENM1 holds y inHIDDENR3 Xf0 & y <>HIDDENR2 x implies  not Pp2(y,x))"
sorry

theorem card_2_sch_2:
  fixes Xf0 Pp2 
  assumes
[ty]: "Xf0 be finiteFINSET-1V1\<bar>setHIDDENM2" and
   A1: "Xf0 <>HIDDENR2 {}XBOOLE-0K1" and
   A2: " for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds Pp2(x,y) or Pp2(y,x)" and
   A3: " for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for z be objectHIDDENM1 holds Pp2(x,y) & Pp2(y,z) implies Pp2(x,z)"
  shows " ex x be objectHIDDENM1 st x inHIDDENR3 Xf0 & ( for y be objectHIDDENM1 holds y inHIDDENR3 Xf0 implies Pp2(x,y))"
sorry

mlemma card_2_lm_7:
" for n be NatORDINAL1M6 holds RankCLASSES1K4 n be finiteFINSET-1V1 implies RankCLASSES1K4 (n +XCMPLX-0K2 \<one>\<^sub>M) be finiteFINSET-1V1"
sorry

mlemma card_2_lm_8:
"\<one>\<^sub>M =XBOOLE-0R4 cardCARD-1K4 \<one>\<^sub>M"
   sorry

mtheorem card_2_th_67:
" for n be NatORDINAL1M6 holds RankCLASSES1K4 n be finiteFINSET-1V1"
sorry

mtheorem card_2_th_68:
" for M be CardinalCARD-1M1 holds 0NUMBERSK6 inTARSKIR2 M iff \<one>\<^sub>M c=ORDINAL1R1 M"
sorry

mtheorem card_2_th_69:
" for M be CardinalCARD-1M1 holds \<one>\<^sub>M inTARSKIR2 M iff \<two>\<^sub>M c=ORDINAL1R1 M"
sorry

reserve n, k for "NatORDINAL1M6"
mtheorem card_2_th_70:
" for A be OrdinalORDINAL1M3 holds A be limit-ordinalORDINAL1V4 iff ( for B be OrdinalORDINAL1M3 holds  for n be NatORDINAL1M6 holds B inTARSKIR2 A implies B +^ORDINAL2K10 n inTARSKIR2 A)"
sorry

mtheorem card_2_th_71:
" for A be OrdinalORDINAL1M3 holds  for n be NatORDINAL1M6 holds A +^ORDINAL2K10 succORDINAL1K1 n =XBOOLE-0R4 succORDINAL1K1 A +^ORDINAL2K10 n & A +^ORDINAL2K10 (n +XCMPLX-0K2 \<one>\<^sub>M) =XBOOLE-0R4 succORDINAL1K1 A +^ORDINAL2K10 n"
sorry

mtheorem card_2_th_72:
" for A be OrdinalORDINAL1M3 holds  ex n be NatORDINAL1M6 st A *^ORDINAL2K11 succORDINAL1K1 \<one>\<^sub>M =XBOOLE-0R4 A +^ORDINAL2K10 n"
sorry

mtheorem card_2_th_73:
" for A be OrdinalORDINAL1M3 holds A be limit-ordinalORDINAL1V4 implies A *^ORDINAL2K11 succORDINAL1K1 \<one>\<^sub>M =XBOOLE-0R4 A"
sorry

mlemma card_2_lm_9:
"omegaORDINAL1K4 be limit-ordinalORDINAL1V4"
  using ordinal1_def_11 sorry

mtheorem card_2_th_74:
" for A be OrdinalORDINAL1M3 holds omegaORDINAL1K4 c=ORDINAL1R1 A implies \<one>\<^sub>M +^ORDINAL2K10 A =XBOOLE-0R4 A"
sorry

mtheorem card_2_cl_2:
"cluster infiniteFINSET-1V2 also-is limit-ordinalORDINAL1V4 for CardinalCARD-1M1"
proof
(*coherence*)
  show " for it be CardinalCARD-1M1 holds it be infiniteFINSET-1V2 implies it be limit-ordinalORDINAL1V4"
sorry
qed "sorry"

mtheorem card_2_th_75:
" for M be CardinalCARD-1M1 holds  not M be finiteFINSET-1V1 implies M +`CARD-2K1 M =XBOOLE-0R4 M"
sorry

mtheorem card_2_th_76:
" for M be CardinalCARD-1M1 holds  for N be CardinalCARD-1M1 holds  not M be finiteFINSET-1V1 & (N c=ORDINAL1R1 M or N inTARSKIR2 M) implies M +`CARD-2K1 N =XBOOLE-0R4 M & N +`CARD-2K1 M =XBOOLE-0R4 M"
sorry

mtheorem card_2_th_77:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  not X be finiteFINSET-1V1 & ((X,Y)are-equipotentWELLORD2R2 or (Y,X)are-equipotentWELLORD2R2) implies (X \\/XBOOLE-0K2 Y,X)are-equipotentWELLORD2R2 & cardCARD-1K1 (X \\/XBOOLE-0K2 Y) =XBOOLE-0R4 cardCARD-1K1 X"
sorry

mtheorem card_2_th_78:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  not X be finiteFINSET-1V1 & Y be finiteFINSET-1V1 implies (X \\/XBOOLE-0K2 Y,X)are-equipotentWELLORD2R2 & cardCARD-1K1 (X \\/XBOOLE-0K2 Y) =XBOOLE-0R4 cardCARD-1K1 X"
sorry

mtheorem card_2_th_79:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  not X be finiteFINSET-1V1 & (cardCARD-1K1 Y inTARSKIR2 cardCARD-1K1 X or cardCARD-1K1 Y c=ORDINAL1R1 cardCARD-1K1 X) implies (X \\/XBOOLE-0K2 Y,X)are-equipotentWELLORD2R2 & cardCARD-1K1 (X \\/XBOOLE-0K2 Y) =XBOOLE-0R4 cardCARD-1K1 X"
sorry

mtheorem card_2_cl_3:
  mlet "M be finiteFINSET-1V1\<bar>CardinalCARD-1M1", "N be finiteFINSET-1V1\<bar>CardinalCARD-1M1"
"cluster M +`CARD-2K1 N as-term-is finiteFINSET-1V1"
proof
(*coherence*)
  show "M +`CARD-2K1 N be finiteFINSET-1V1"
sorry
qed "sorry"

mtheorem card_2_th_80:
" for M be finiteFINSET-1V1\<bar>CardinalCARD-1M1 holds  for N be finiteFINSET-1V1\<bar>CardinalCARD-1M1 holds M +`CARD-2K1 N be finiteFINSET-1V1"
   sorry

mtheorem card_2_th_81:
" for M be CardinalCARD-1M1 holds  for N be CardinalCARD-1M1 holds  not M be finiteFINSET-1V1 implies  not M +`CARD-2K1 N be finiteFINSET-1V1 &  not N +`CARD-2K1 M be finiteFINSET-1V1"
sorry

mtheorem card_2_th_82:
" for M be finiteFINSET-1V1\<bar>CardinalCARD-1M1 holds  for N be finiteFINSET-1V1\<bar>CardinalCARD-1M1 holds M *`CARD-2K2 N be finiteFINSET-1V1"
   sorry

mtheorem card_2_th_83:
" for K be CardinalCARD-1M1 holds  for L be CardinalCARD-1M1 holds  for M be CardinalCARD-1M1 holds  for N be CardinalCARD-1M1 holds ((K inTARSKIR2 L & M inTARSKIR2 N or K c=ORDINAL1R1 L & M inTARSKIR2 N) or K inTARSKIR2 L & M c=ORDINAL1R1 N) or K c=ORDINAL1R1 L & M c=ORDINAL1R1 N implies K +`CARD-2K1 M c=ORDINAL1R1 L +`CARD-2K1 N & M +`CARD-2K1 K c=ORDINAL1R1 L +`CARD-2K1 N"
sorry

mtheorem card_2_th_84:
" for K be CardinalCARD-1M1 holds  for M be CardinalCARD-1M1 holds  for N be CardinalCARD-1M1 holds M inTARSKIR2 N or M c=ORDINAL1R1 N implies ((K +`CARD-2K1 M c=ORDINAL1R1 K +`CARD-2K1 N & K +`CARD-2K1 M c=ORDINAL1R1 N +`CARD-2K1 K) & M +`CARD-2K1 K c=ORDINAL1R1 K +`CARD-2K1 N) & M +`CARD-2K1 K c=ORDINAL1R1 N +`CARD-2K1 K"
  using card_2_th_83 sorry

mtheorem card_2_th_85:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X be countableCARD-3V4 & Y be countableCARD-3V4 implies X \\/XBOOLE-0K2 Y be countableCARD-3V4"
sorry

mtheorem card_2_th_86:
" for M be CardinalCARD-1M1 holds  for N be CardinalCARD-1M1 holds  for f be FunctionFUNCT-1M1 holds cardCARD-1K1 (domRELAT-1K1 f) c=ORDINAL1R1 M & ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 f implies cardCARD-1K1 (f .FUNCT-1K1 x) c=ORDINAL1R1 N) implies cardCARD-1K1 (UnionCARD-3K3 f) c=ORDINAL1R1 M *`CARD-2K2 N"
sorry

mtheorem card_2_th_87:
" for M be CardinalCARD-1M1 holds  for N be CardinalCARD-1M1 holds  for X be setHIDDENM2 holds cardCARD-1K1 X c=ORDINAL1R1 M & ( for Y be setHIDDENM2 holds Y inTARSKIR2 X implies cardCARD-1K1 Y c=ORDINAL1R1 N) implies cardCARD-1K1 (unionTARSKIK3 X) c=ORDINAL1R1 M *`CARD-2K2 N"
sorry

mtheorem card_2_th_88:
" for f be FunctionFUNCT-1M1 holds domRELAT-1K1 f be finiteFINSET-1V1 & ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 f implies f .FUNCT-1K1 x be finiteFINSET-1V1) implies UnionCARD-3K3 f be finiteFINSET-1V1"
sorry

mtheorem card_2_th_89:
" for n be NatORDINAL1M6 holds omegaORDINAL1K4 *`CARD-2K2 cardCARD-1K4 n c=ORDINAL1R1 omegaORDINAL1K4 & cardCARD-1K4 n *`CARD-2K2 omegaORDINAL1K4 c=ORDINAL1R1 omegaORDINAL1K4"
sorry

mtheorem card_2_th_90:
" for K be CardinalCARD-1M1 holds  for L be CardinalCARD-1M1 holds  for M be CardinalCARD-1M1 holds  for N be CardinalCARD-1M1 holds ((K inTARSKIR2 L & M inTARSKIR2 N or K c=ORDINAL1R1 L & M inTARSKIR2 N) or K inTARSKIR2 L & M c=ORDINAL1R1 N) or K c=ORDINAL1R1 L & M c=ORDINAL1R1 N implies K *`CARD-2K2 M c=ORDINAL1R1 L *`CARD-2K2 N & M *`CARD-2K2 K c=ORDINAL1R1 L *`CARD-2K2 N"
sorry

mtheorem card_2_th_91:
" for K be CardinalCARD-1M1 holds  for M be CardinalCARD-1M1 holds  for N be CardinalCARD-1M1 holds M inTARSKIR2 N or M c=ORDINAL1R1 N implies ((K *`CARD-2K2 M c=ORDINAL1R1 K *`CARD-2K2 N & K *`CARD-2K2 M c=ORDINAL1R1 N *`CARD-2K2 K) & M *`CARD-2K2 K c=ORDINAL1R1 K *`CARD-2K2 N) & M *`CARD-2K2 K c=ORDINAL1R1 N *`CARD-2K2 K"
  using card_2_th_90 sorry

mtheorem card_2_th_92:
" for K be CardinalCARD-1M1 holds  for L be CardinalCARD-1M1 holds  for M be CardinalCARD-1M1 holds  for N be CardinalCARD-1M1 holds ((K inTARSKIR2 L & M inTARSKIR2 N or K c=ORDINAL1R1 L & M inTARSKIR2 N) or K inTARSKIR2 L & M c=ORDINAL1R1 N) or K c=ORDINAL1R1 L & M c=ORDINAL1R1 N implies K =XBOOLE-0R4 0NUMBERSK6 or expCARD-2K3(K,M) c=ORDINAL1R1 expCARD-2K3(L,N)"
sorry

mtheorem card_2_th_93:
" for K be CardinalCARD-1M1 holds  for M be CardinalCARD-1M1 holds  for N be CardinalCARD-1M1 holds M inTARSKIR2 N or M c=ORDINAL1R1 N implies K =XBOOLE-0R4 0NUMBERSK6 or expCARD-2K3(K,M) c=ORDINAL1R1 expCARD-2K3(K,N) & expCARD-2K3(M,K) c=ORDINAL1R1 expCARD-2K3(N,K)"
sorry

mtheorem card_2_th_94:
" for M be CardinalCARD-1M1 holds  for N be CardinalCARD-1M1 holds M c=ORDINAL1R1 M +`CARD-2K1 N & N c=ORDINAL1R1 M +`CARD-2K1 N"
sorry

mtheorem card_2_th_95:
" for M be CardinalCARD-1M1 holds  for N be CardinalCARD-1M1 holds N <>HIDDENR2 0NUMBERSK6 implies M c=ORDINAL1R1 M *`CARD-2K2 N & M c=ORDINAL1R1 N *`CARD-2K2 M"
sorry

mtheorem card_2_th_96:
" for K be CardinalCARD-1M1 holds  for L be CardinalCARD-1M1 holds  for M be CardinalCARD-1M1 holds  for N be CardinalCARD-1M1 holds K inTARSKIR2 L & M inTARSKIR2 N implies K +`CARD-2K1 M inTARSKIR2 L +`CARD-2K1 N & M +`CARD-2K1 K inTARSKIR2 L +`CARD-2K1 N"
sorry

mtheorem card_2_th_97:
" for K be CardinalCARD-1M1 holds  for M be CardinalCARD-1M1 holds  for N be CardinalCARD-1M1 holds K +`CARD-2K1 M inTARSKIR2 K +`CARD-2K1 N implies M inTARSKIR2 N"
sorry

mtheorem card_2_th_98:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds cardCARD-1K1 X +`CARD-2K1 cardCARD-1K1 Y =XBOOLE-0R4 cardCARD-1K1 X & cardCARD-1K1 Y inTARSKIR2 cardCARD-1K1 X implies cardCARD-1K1 (X \\SUBSET-1K6 Y) =XBOOLE-0R4 cardCARD-1K1 X"
sorry

mtheorem card_2_th_99:
" for K be CardinalCARD-1M1 holds  for M be CardinalCARD-1M1 holds  for N be CardinalCARD-1M1 holds K *`CARD-2K2 M inTARSKIR2 K *`CARD-2K2 N implies M inTARSKIR2 N"
sorry

mtheorem card_2_th_100:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X be countableCARD-3V4 & Y be countableCARD-3V4 implies X \\+\\XBOOLE-0K5 Y be countableCARD-3V4"
sorry

mtheorem card_2_cl_4:
  mlet "A be finiteFINSET-1V1\<bar>setHIDDENM2", "B be setHIDDENM2", "f be FunctionFUNCT-2M1-of(A,FinFINSUB-1K5 B)"
"cluster UnionCARD-3K3 f as-term-is finiteFINSET-1V1"
proof
(*coherence*)
  show "UnionCARD-3K3 f be finiteFINSET-1V1"
sorry
qed "sorry"

mtheorem card_2_cl_5:
  mlet "f be finiteFINSET-1V1\<bar>finite-yieldingFINSET-1V5\<bar>FunctionFUNCT-1M1"
"cluster productCARD-3K4 f as-term-is finiteFINSET-1V1"
proof
(*coherence*)
  show "productCARD-3K4 f be finiteFINSET-1V1"
sorry
qed "sorry"

mtheorem card_2_th_101:
" for F be FunctionFUNCT-1M1 holds domRELAT-1K1 F be infiniteFINSET-1V2 & rngFUNCT-1K2 F be finiteFINSET-1V1 implies ( ex x be objectHIDDENM1 st x inHIDDENR3 rngFUNCT-1K2 F & F \<inverse>FUNCT-1K6 {TARSKIK1 x} be infiniteFINSET-1V2)"
sorry

mtheorem card_2_th_102:
" for X be finiteFINSET-1V1\<bar>setHIDDENM2 holds  for Y be finiteFINSET-1V1\<bar>setHIDDENM2 holds X c=TARSKIR1 Y & cardCARD-1K4 X =XBOOLE-0R4 cardCARD-1K4 Y implies X =XBOOLE-0R4 Y"
sorry

theorem card_2_sch_3:
  fixes Xf0 Pp2 
  assumes
[ty]: "Xf0 be finiteFINSET-1V1\<bar>setHIDDENM2" and
   A1: "Xf0 <>HIDDENR2 {}XBOOLE-0K1" and
   A2: " for x be setHIDDENM2 holds  for y be setHIDDENM2 holds Pp2(x,y) & Pp2(y,x) implies x =XBOOLE-0R4 y" and
   A3: " for x be setHIDDENM2 holds  for y be setHIDDENM2 holds  for z be setHIDDENM2 holds Pp2(x,y) & Pp2(y,z) implies Pp2(x,z)"
  shows " ex x be setHIDDENM2 st x inTARSKIR2 Xf0 & ( for y be setHIDDENM2 holds y inTARSKIR2 Xf0 & y <>HIDDENR2 x implies  not Pp2(y,x))"
sorry

end
