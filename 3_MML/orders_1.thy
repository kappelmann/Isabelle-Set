theory orders_1
  imports wellord2 finset_1 pboole
begin
(*begin*)
reserve X, Y for "setHIDDENM2"
reserve x, x1, x2, y, y1, y2, z for "setHIDDENM2"
reserve f, g, h for "FunctionFUNCT-1M1"
mlemma orders_1_lm_1:
" for Y be setHIDDENM2 holds ( ex X be setHIDDENM2 st X <>HIDDENR2 {}XBOOLE-0K1 & X inTARSKIR2 Y) iff unionTARSKIK3 Y <>HIDDENR2 {}XBOOLE-0K1"
sorry

mdef orders_1_def_1 ("ChoiceORDERS-1M1-of  _ " [70]70 ) where
  mlet "f be FunctionFUNCT-1M1"
"mode ChoiceORDERS-1M1-of f \<rightarrow> FunctionFUNCT-1M1 means
  (\<lambda>it. domRELAT-1K1 it =XBOOLE-0R4 domRELAT-1K1 f & ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 f implies it .FUNCT-1K1 x =XBOOLE-0R4 the ElementSUBSET-1M1-of f .FUNCT-1K1 x))"
proof-
  (*existence*)
    show " ex it be FunctionFUNCT-1M1 st domRELAT-1K1 it =XBOOLE-0R4 domRELAT-1K1 f & ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 f implies it .FUNCT-1K1 x =XBOOLE-0R4 the ElementSUBSET-1M1-of f .FUNCT-1K1 x)"
sorry
qed "sorry"

syntax ORDERS_1M2 :: " Set \<Rightarrow>  Set \<Rightarrow> Ty" ("ChoiceORDERS-1M2\<^bsub>'( _ ')\<^esub>-of  _ " [0,70]70)
translations "ChoiceORDERS-1M2\<^bsub>(I)\<^esub>-of M" \<rightharpoonup> "ChoiceORDERS-1M1-of M"

mtheorem orders_1_def_2:
  mlet "I be setHIDDENM2", "M be ManySortedSetPBOOLEM1-of I"
"redefine mode ChoiceORDERS-1M2\<^bsub>(I)\<^esub>-of M \<rightarrow> ManySortedSetPBOOLEM1-of I means
  (\<lambda>it.  for x be objectHIDDENM1 holds x inHIDDENR3 I implies it .FUNCT-1K1 x =XBOOLE-0R4 the ElementSUBSET-1M1-of M .FUNCT-1K1 x)"
proof
(*compatibility*)
  show " for it be ManySortedSetPBOOLEM1-of I holds it be ChoiceORDERS-1M2\<^bsub>(I)\<^esub>-of M iff ( for x be objectHIDDENM1 holds x inHIDDENR3 I implies it .FUNCT-1K1 x =XBOOLE-0R4 the ElementSUBSET-1M1-of M .FUNCT-1K1 x)"
sorry
qed "sorry"

mtheorem orders_1_add_1:
  mlet "I be setHIDDENM2", "M be ManySortedSetPBOOLEM1-of I"
"cluster note-that ManySortedSetPBOOLEM1-of I for ChoiceORDERS-1M1-of M"
proof
(*coherence*)
  show " for it be ChoiceORDERS-1M1-of M holds it be ManySortedSetPBOOLEM1-of I"
sorry
qed "sorry"

syntax ORDERS_1M3 :: " Set \<Rightarrow> Ty" ("Choice-FunctionORDERS-1M3-of  _ " [70]70)
translations "Choice-FunctionORDERS-1M3-of A" \<rightharpoonup> "ChoiceORDERS-1M2\<^bsub>(A)\<^esub>-of idPARTFUN1K6 A"

reserve M for " non emptyXBOOLE-0V1\<bar>setHIDDENM2"
mlemma orders_1_lm_2:
" for M be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  not {}XBOOLE-0K1 inTARSKIR2 M implies ( for Ch be Choice-FunctionORDERS-1M3-of M holds  for X be setHIDDENM2 holds X inTARSKIR2 M implies Ch .FUNCT-1K1 X inTARSKIR2 X)"
sorry

mlemma orders_1_lm_3:
" for M be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  not {}XBOOLE-0K1 inTARSKIR2 M implies ( for Ch be Choice-FunctionORDERS-1M3-of M holds Ch be FunctionFUNCT-2M1-of(M,unionTARSKIK3 M))"
sorry

reserve D for " non emptyXBOOLE-0V1\<bar>setHIDDENM2"
mdef orders_1_def_3 ("BOOLORDERS-1K1  _ " [222]222 ) where
  mlet "D be setHIDDENM2"
"func BOOLORDERS-1K1 D \<rightarrow> setHIDDENM2 equals
  boolSETFAM-1K9 D \\SUBSET-1K7\<^bsub>(boolZFMISC-1K1 D)\<^esub> {TARSKIK1 {}XBOOLE-0K1 }"
proof-
  (*coherence*)
    show "boolSETFAM-1K9 D \\SUBSET-1K7\<^bsub>(boolZFMISC-1K1 D)\<^esub> {TARSKIK1 {}XBOOLE-0K1 } be setHIDDENM2"
       sorry
qed "sorry"

mtheorem orders_1_cl_1:
  mlet "D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster BOOLORDERS-1K1 D as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "BOOLORDERS-1K1 D be  non emptyXBOOLE-0V1"
sorry
qed "sorry"

mtheorem orders_1_th_1:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  not {}XBOOLE-0K1 inTARSKIR2 BOOLORDERS-1K1 D"
sorry

mtheorem orders_1_th_2:
" for X be setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds D c=TARSKIR1 X iff D inTARSKIR2 BOOLORDERS-1K1 X"
sorry

reserve P for "RelationRELAT-1M1"
syntax ORDERS_1M4 :: " Set \<Rightarrow> Ty" ("OrderORDERS-1M4-of  _ " [70]70)
translations "OrderORDERS-1M4-of X" \<rightharpoonup> "totalPARTFUN1V1\<^bsub>(X)\<^esub>\<bar>reflexiveRELAT-2V1\<bar>antisymmetricRELAT-2V4\<bar>transitiveRELAT-2V8\<bar>RelationRELSET-1M2-of X"

reserve O for "OrderORDERS-1M4-of X"
mlemma orders_1_lm_4:
" for X be setHIDDENM2 holds  for R be totalPARTFUN1V1\<^bsub>(X)\<^esub>\<bar>RelationRELSET-1M2-of X holds fieldRELAT-1K3 R =XBOOLE-0R4 X"
sorry

mtheorem orders_1_th_3:
" for X be setHIDDENM2 holds  for x be setHIDDENM2 holds  for O be OrderORDERS-1M4-of X holds x inTARSKIR2 X implies [TARSKIK4 x,x ] inHIDDENR3 O"
sorry

mtheorem orders_1_th_4:
" for X be setHIDDENM2 holds  for x be setHIDDENM2 holds  for y be setHIDDENM2 holds  for O be OrderORDERS-1M4-of X holds ((x inTARSKIR2 X & y inTARSKIR2 X) & [TARSKIK4 x,y ] inHIDDENR3 O) & [TARSKIK4 y,x ] inHIDDENR3 O implies x =XBOOLE-0R4 y"
sorry

mtheorem orders_1_th_5:
" for X be setHIDDENM2 holds  for x be setHIDDENM2 holds  for y be setHIDDENM2 holds  for z be setHIDDENM2 holds  for O be OrderORDERS-1M4-of X holds (((x inTARSKIR2 X & y inTARSKIR2 X) & z inTARSKIR2 X) & [TARSKIK4 x,y ] inHIDDENR3 O) & [TARSKIK4 y,z ] inHIDDENR3 O implies [TARSKIK4 x,z ] inHIDDENR3 O"
sorry

mtheorem orders_1_th_6:
" for Y be setHIDDENM2 holds ( ex X be setHIDDENM2 st X <>HIDDENR2 {}XBOOLE-0K1 & X inTARSKIR2 Y) iff unionTARSKIK3 Y <>HIDDENR2 {}XBOOLE-0K1"
  using orders_1_lm_1 sorry

mtheorem orders_1_th_7:
" for X be setHIDDENM2 holds  for P be RelationRELAT-1M1 holds P is-strongly-connected-inRELAT-2R7 X iff P is-reflexive-inRELAT-2R1 X & P is-connected-inRELAT-2R6 X"
sorry

mtheorem orders_1_th_8:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for P be RelationRELAT-1M1 holds P is-reflexive-inRELAT-2R1 X & Y c=TARSKIR1 X implies P is-reflexive-inRELAT-2R1 Y"
   sorry

mtheorem orders_1_th_9:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for P be RelationRELAT-1M1 holds P is-antisymmetric-inRELAT-2R4 X & Y c=TARSKIR1 X implies P is-antisymmetric-inRELAT-2R4 Y"
   sorry

mtheorem orders_1_th_10:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for P be RelationRELAT-1M1 holds P is-transitive-inRELAT-2R8 X & Y c=TARSKIR1 X implies P is-transitive-inRELAT-2R8 Y"
   sorry

mtheorem orders_1_th_11:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for P be RelationRELAT-1M1 holds P is-strongly-connected-inRELAT-2R7 X & Y c=TARSKIR1 X implies P is-strongly-connected-inRELAT-2R7 Y"
   sorry

mtheorem orders_1_th_12:
" for X be setHIDDENM2 holds  for R be totalPARTFUN1V1\<^bsub>(X)\<^esub>\<bar>RelationRELSET-1M2-of X holds fieldRELAT-1K3 R =XBOOLE-0R4 X"
  using orders_1_lm_4 sorry

mtheorem orders_1_th_13:
" for A be setHIDDENM2 holds  for R be RelationRELSET-1M2-of A holds R is-reflexive-inRELAT-2R1 A implies domRELSET-1K1\<^bsub>(A)\<^esub> R =XBOOLE-0R4 A & fieldRELAT-1K3 R =XBOOLE-0R4 A"
sorry

(*begin*)
reserve R, P for "RelationRELAT-1M1"
reserve X, X1, X2, Y, Z, x, y, z, u for "setHIDDENM2"
reserve g, h for "FunctionFUNCT-1M1"
reserve O for "OrderORDERS-1M4-of X"
reserve D for " non emptyXBOOLE-0V1\<bar>setHIDDENM2"
reserve d, d1, d2 for "ElementSUBSET-1M1-of D"
reserve A1, A2, B for "OrdinalORDINAL1M3"
reserve L, L1, L2 for "SequenceORDINAL1M4"
mtheorem orders_1_th_14:
" for X be setHIDDENM2 holds  for O be OrderORDERS-1M4-of X holds domRELSET-1K1\<^bsub>(X)\<^esub> O =XBOOLE-0R4 X & rngRELSET-1K2\<^bsub>(X)\<^esub> O =XBOOLE-0R4 X"
sorry

mtheorem orders_1_th_15:
" for X be setHIDDENM2 holds  for O be OrderORDERS-1M4-of X holds fieldRELAT-1K3 O =XBOOLE-0R4 X"
sorry

mdef orders_1_def_4 ("being-quasi-orderORDERS-1V1" 70 ) where
"attr being-quasi-orderORDERS-1V1 for RelationRELAT-1M1 means
  (\<lambda>R. R be reflexiveRELAT-2V1\<bar>transitiveRELAT-2V8)"..

mdef orders_1_def_5 ("being-partial-orderORDERS-1V2" 70 ) where
"attr being-partial-orderORDERS-1V2 for RelationRELAT-1M1 means
  (\<lambda>R. R be reflexiveRELAT-2V1\<bar>transitiveRELAT-2V8\<bar>antisymmetricRELAT-2V4)"..

mdef orders_1_def_6 ("being-linear-orderORDERS-1V3" 70 ) where
"attr being-linear-orderORDERS-1V3 for RelationRELAT-1M1 means
  (\<lambda>R. R be reflexiveRELAT-2V1\<bar>transitiveRELAT-2V8\<bar>antisymmetricRELAT-2V4\<bar>connectedRELAT-2V6)"..

mtheorem orders_1_th_16:
" for R be RelationRELAT-1M1 holds R be being-quasi-orderORDERS-1V1 implies R ~RELAT-1K4 be being-quasi-orderORDERS-1V1"
   sorry

mtheorem orders_1_th_17:
" for R be RelationRELAT-1M1 holds R be being-partial-orderORDERS-1V2 implies R ~RELAT-1K4 be being-partial-orderORDERS-1V2"
   sorry

mlemma orders_1_lm_5:
" for R be RelationRELAT-1M1 holds R be connectedRELAT-2V6 implies R ~RELAT-1K4 be connectedRELAT-2V6"
sorry

mtheorem orders_1_th_18:
" for R be RelationRELAT-1M1 holds R be being-linear-orderORDERS-1V3 implies R ~RELAT-1K4 be being-linear-orderORDERS-1V3"
  using orders_1_lm_5 sorry

mtheorem orders_1_th_19:
" for R be RelationRELAT-1M1 holds R be well-orderingWELLORD1V2 implies (R be being-quasi-orderORDERS-1V1 & R be being-partial-orderORDERS-1V2) & R be being-linear-orderORDERS-1V3"
   sorry

mtheorem orders_1_th_20:
" for R be RelationRELAT-1M1 holds R be being-linear-orderORDERS-1V3 implies R be being-quasi-orderORDERS-1V1 & R be being-partial-orderORDERS-1V2"
   sorry

mtheorem orders_1_th_21:
" for R be RelationRELAT-1M1 holds R be being-partial-orderORDERS-1V2 implies R be being-quasi-orderORDERS-1V1"
   sorry

mtheorem orders_1_th_22:
" for X be setHIDDENM2 holds  for O be OrderORDERS-1M4-of X holds O be being-partial-orderORDERS-1V2"
   sorry

mtheorem orders_1_th_23:
" for X be setHIDDENM2 holds  for O be OrderORDERS-1M4-of X holds O be being-quasi-orderORDERS-1V1"
   sorry

mtheorem orders_1_th_24:
" for X be setHIDDENM2 holds  for O be OrderORDERS-1M4-of X holds O be connectedRELAT-2V6 implies O be being-linear-orderORDERS-1V3"
   sorry

mlemma orders_1_lm_6:
" for R be RelationRELAT-1M1 holds R c=RELAT-1R2 [:ZFMISC-1K2 fieldRELAT-1K3 R,fieldRELAT-1K3 R :]"
sorry

mlemma orders_1_lm_7:
" for R be RelationRELAT-1M1 holds  for X be setHIDDENM2 holds R be reflexiveRELAT-2V1 & X c=TARSKIR1 fieldRELAT-1K3 R implies fieldRELAT-1K3 (R |-2WELLORD1K2 X) =XBOOLE-0R4 X"
sorry

mtheorem orders_1_th_25:
" for R be RelationRELAT-1M1 holds  for X be setHIDDENM2 holds R be being-quasi-orderORDERS-1V1 implies R |-2WELLORD1K2 X be being-quasi-orderORDERS-1V1"
  using wellord1_th_15 wellord1_th_17 sorry

mtheorem orders_1_th_26:
" for R be RelationRELAT-1M1 holds  for X be setHIDDENM2 holds R be being-partial-orderORDERS-1V2 implies R |-2WELLORD1K2 X be being-partial-orderORDERS-1V2"
  using wellord1_th_15 wellord1_th_17 sorry

mtheorem orders_1_th_27:
" for R be RelationRELAT-1M1 holds  for X be setHIDDENM2 holds R be being-linear-orderORDERS-1V3 implies R |-2WELLORD1K2 X be being-linear-orderORDERS-1V3"
  using wellord1_th_15 wellord1_th_16 wellord1_th_17 sorry

mtheorem orders_1_cl_2:
  mlet "R be emptyXBOOLE-0V1\<bar>RelationRELAT-1M1"
"cluster fieldRELAT-1K3 R as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "fieldRELAT-1K3 R be emptyXBOOLE-0V1"
     sorry
qed "sorry"

mtheorem orders_1_cl_3:
"cluster emptyXBOOLE-0V1 also-is being-quasi-orderORDERS-1V1\<bar>being-partial-orderORDERS-1V2\<bar>being-linear-orderORDERS-1V3\<bar>well-orderingWELLORD1V2 for RelationRELAT-1M1"
proof
(*coherence*)
  show " for it be RelationRELAT-1M1 holds it be emptyXBOOLE-0V1 implies it be being-quasi-orderORDERS-1V1\<bar>being-partial-orderORDERS-1V2\<bar>being-linear-orderORDERS-1V3\<bar>well-orderingWELLORD1V2"
sorry
qed "sorry"

mtheorem orders_1_cl_4:
  mlet "X be setHIDDENM2"
"cluster idPARTFUN1K6 X as-term-is being-quasi-orderORDERS-1V1\<bar>being-partial-orderORDERS-1V2"
proof
(*coherence*)
  show "idPARTFUN1K6 X be being-quasi-orderORDERS-1V1\<bar>being-partial-orderORDERS-1V2"
     sorry
qed "sorry"

mdef orders_1_def_7 (" _ quasi-ordersORDERS-1R1  _ " [50,50]50 ) where
  mlet "R be RelationRELAT-1M1", "X be setHIDDENM2"
"pred R quasi-ordersORDERS-1R1 X means
  R is-reflexive-inRELAT-2R1 X & R is-transitive-inRELAT-2R8 X"..

mdef orders_1_def_8 (" _ partially-ordersORDERS-1R2  _ " [50,50]50 ) where
  mlet "R be RelationRELAT-1M1", "X be setHIDDENM2"
"pred R partially-ordersORDERS-1R2 X means
  (R is-reflexive-inRELAT-2R1 X & R is-transitive-inRELAT-2R8 X) & R is-antisymmetric-inRELAT-2R4 X"..

mdef orders_1_def_9 (" _ linearly-ordersORDERS-1R3  _ " [50,50]50 ) where
  mlet "R be RelationRELAT-1M1", "X be setHIDDENM2"
"pred R linearly-ordersORDERS-1R3 X means
  ((R is-reflexive-inRELAT-2R1 X & R is-transitive-inRELAT-2R8 X) & R is-antisymmetric-inRELAT-2R4 X) & R is-connected-inRELAT-2R6 X"..

mtheorem orders_1_th_28:
" for R be RelationRELAT-1M1 holds  for X be setHIDDENM2 holds R well-ordersWELLORD1R2 X implies (R quasi-ordersORDERS-1R1 X & R partially-ordersORDERS-1R2 X) & R linearly-ordersORDERS-1R3 X"
   sorry

mtheorem orders_1_th_29:
" for R be RelationRELAT-1M1 holds  for X be setHIDDENM2 holds R linearly-ordersORDERS-1R3 X implies R quasi-ordersORDERS-1R1 X & R partially-ordersORDERS-1R2 X"
   sorry

mtheorem orders_1_th_30:
" for R be RelationRELAT-1M1 holds  for X be setHIDDENM2 holds R partially-ordersORDERS-1R2 X implies R quasi-ordersORDERS-1R1 X"
   sorry

mtheorem orders_1_th_31:
" for R be RelationRELAT-1M1 holds R be being-quasi-orderORDERS-1V1 implies R quasi-ordersORDERS-1R1 fieldRELAT-1K3 R"
sorry

mtheorem orders_1_th_32:
" for R be RelationRELAT-1M1 holds  for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds R quasi-ordersORDERS-1R1 Y & X c=TARSKIR1 Y implies R quasi-ordersORDERS-1R1 X"
sorry

mlemma orders_1_lm_8:
" for R be RelationRELAT-1M1 holds  for X be setHIDDENM2 holds R is-reflexive-inRELAT-2R1 X implies R |-2WELLORD1K2 X be reflexiveRELAT-2V1"
sorry

mlemma orders_1_lm_9:
" for R be RelationRELAT-1M1 holds  for X be setHIDDENM2 holds R is-transitive-inRELAT-2R8 X implies R |-2WELLORD1K2 X be transitiveRELAT-2V8"
sorry

mlemma orders_1_lm_10:
" for R be RelationRELAT-1M1 holds  for X be setHIDDENM2 holds R is-antisymmetric-inRELAT-2R4 X implies R |-2WELLORD1K2 X be antisymmetricRELAT-2V4"
sorry

mlemma orders_1_lm_11:
" for R be RelationRELAT-1M1 holds  for X be setHIDDENM2 holds R is-connected-inRELAT-2R6 X implies R |-2WELLORD1K2 X be connectedRELAT-2V6"
sorry

mtheorem orders_1_th_33:
" for R be RelationRELAT-1M1 holds  for X be setHIDDENM2 holds R quasi-ordersORDERS-1R1 X implies R |-2WELLORD1K2 X be being-quasi-orderORDERS-1V1"
  using orders_1_lm_8 orders_1_lm_9 sorry

mtheorem orders_1_th_34:
" for R be RelationRELAT-1M1 holds R be being-partial-orderORDERS-1V2 implies R partially-ordersORDERS-1R2 fieldRELAT-1K3 R"
sorry

mtheorem orders_1_th_35:
" for R be RelationRELAT-1M1 holds  for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds R partially-ordersORDERS-1R2 Y & X c=TARSKIR1 Y implies R partially-ordersORDERS-1R2 X"
sorry

mtheorem orders_1_th_36:
" for R be RelationRELAT-1M1 holds  for X be setHIDDENM2 holds R partially-ordersORDERS-1R2 X implies R |-2WELLORD1K2 X be being-partial-orderORDERS-1V2"
  using orders_1_lm_8 orders_1_lm_9 orders_1_lm_10 sorry

mtheorem orders_1_th_37:
" for R be RelationRELAT-1M1 holds R be being-linear-orderORDERS-1V3 implies R linearly-ordersORDERS-1R3 fieldRELAT-1K3 R"
sorry

mtheorem orders_1_th_38:
" for R be RelationRELAT-1M1 holds  for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds R linearly-ordersORDERS-1R3 Y & X c=TARSKIR1 Y implies R linearly-ordersORDERS-1R3 X"
sorry

mtheorem orders_1_th_39:
" for R be RelationRELAT-1M1 holds  for X be setHIDDENM2 holds R linearly-ordersORDERS-1R3 X implies R |-2WELLORD1K2 X be being-linear-orderORDERS-1V3"
  using orders_1_lm_8 orders_1_lm_9 orders_1_lm_10 orders_1_lm_11 sorry

mlemma orders_1_lm_12:
" for R be RelationRELAT-1M1 holds  for X be setHIDDENM2 holds R is-reflexive-inRELAT-2R1 X implies R ~RELAT-1K4 is-reflexive-inRELAT-2R1 X"
sorry

mlemma orders_1_lm_13:
" for R be RelationRELAT-1M1 holds  for X be setHIDDENM2 holds R is-transitive-inRELAT-2R8 X implies R ~RELAT-1K4 is-transitive-inRELAT-2R8 X"
sorry

mlemma orders_1_lm_14:
" for R be RelationRELAT-1M1 holds  for X be setHIDDENM2 holds R is-antisymmetric-inRELAT-2R4 X implies R ~RELAT-1K4 is-antisymmetric-inRELAT-2R4 X"
sorry

mlemma orders_1_lm_15:
" for R be RelationRELAT-1M1 holds  for X be setHIDDENM2 holds R is-connected-inRELAT-2R6 X implies R ~RELAT-1K4 is-connected-inRELAT-2R6 X"
sorry

mtheorem orders_1_th_40:
" for R be RelationRELAT-1M1 holds  for X be setHIDDENM2 holds R quasi-ordersORDERS-1R1 X implies R ~RELAT-1K4 quasi-ordersORDERS-1R1 X"
  using orders_1_lm_12 orders_1_lm_13 sorry

mtheorem orders_1_th_41:
" for R be RelationRELAT-1M1 holds  for X be setHIDDENM2 holds R partially-ordersORDERS-1R2 X implies R ~RELAT-1K4 partially-ordersORDERS-1R2 X"
  using orders_1_lm_12 orders_1_lm_13 orders_1_lm_14 sorry

mtheorem orders_1_th_42:
" for R be RelationRELAT-1M1 holds  for X be setHIDDENM2 holds R linearly-ordersORDERS-1R3 X implies R ~RELAT-1K4 linearly-ordersORDERS-1R3 X"
  using orders_1_lm_12 orders_1_lm_13 orders_1_lm_14 orders_1_lm_15 sorry

mtheorem orders_1_th_43:
" for X be setHIDDENM2 holds  for O be OrderORDERS-1M4-of X holds O quasi-ordersORDERS-1R1 X"
sorry

mtheorem orders_1_th_44:
" for X be setHIDDENM2 holds  for O be OrderORDERS-1M4-of X holds O partially-ordersORDERS-1R2 X"
sorry

mtheorem orders_1_th_45:
" for R be RelationRELAT-1M1 holds  for X be setHIDDENM2 holds R partially-ordersORDERS-1R2 X implies R |-2WELLORD1K2 X be OrderORDERS-1M4-of X"
sorry

mtheorem orders_1_th_46:
" for R be RelationRELAT-1M1 holds  for X be setHIDDENM2 holds R linearly-ordersORDERS-1R3 X implies R |-2WELLORD1K2 X be OrderORDERS-1M4-of X"
  using orders_1_th_29 orders_1_th_45 sorry

mtheorem orders_1_th_47:
" for R be RelationRELAT-1M1 holds  for X be setHIDDENM2 holds R well-ordersWELLORD1R2 X implies R |-2WELLORD1K2 X be OrderORDERS-1M4-of X"
  using orders_1_th_28 orders_1_th_45 sorry

mtheorem orders_1_th_48:
" for X be setHIDDENM2 holds idPARTFUN1K6 X quasi-ordersORDERS-1R1 X & idPARTFUN1K6 X partially-ordersORDERS-1R2 X"
sorry

mdef orders_1_def_10 (" _ has-upper-Zorn-property-wrtORDERS-1R4  _ " [50,50]50 ) where
  mlet "R be RelationRELAT-1M1", "X be setHIDDENM2"
"pred X has-upper-Zorn-property-wrtORDERS-1R4 R means
   for Y be setHIDDENM2 holds Y c=TARSKIR1 X & R |-2WELLORD1K2 Y be being-linear-orderORDERS-1V3 implies ( ex x be setHIDDENM2 st x inTARSKIR2 X & ( for y be setHIDDENM2 holds y inTARSKIR2 Y implies [TARSKIK4 y,x ] inHIDDENR3 R))"..

mdef orders_1_def_11 (" _ has-lower-Zorn-property-wrtORDERS-1R5  _ " [50,50]50 ) where
  mlet "R be RelationRELAT-1M1", "X be setHIDDENM2"
"pred X has-lower-Zorn-property-wrtORDERS-1R5 R means
   for Y be setHIDDENM2 holds Y c=TARSKIR1 X & R |-2WELLORD1K2 Y be being-linear-orderORDERS-1V3 implies ( ex x be setHIDDENM2 st x inTARSKIR2 X & ( for y be setHIDDENM2 holds y inTARSKIR2 Y implies [TARSKIK4 x,y ] inHIDDENR3 R))"..

mlemma orders_1_lm_16:
" for R be RelationRELAT-1M1 holds  for X be setHIDDENM2 holds (R |-2WELLORD1K2 X)~RELAT-1K4 =RELAT-1R1 R ~RELAT-1K4 |-2WELLORD1K2 X"
sorry

mlemma orders_1_lm_17:
" for R be RelationRELAT-1M1 holds R |-2WELLORD1K2 {}XBOOLE-0K1 =HIDDENR1 {}XBOOLE-0K1"
sorry

mtheorem orders_1_th_49:
" for R be RelationRELAT-1M1 holds  for X be setHIDDENM2 holds X has-upper-Zorn-property-wrtORDERS-1R4 R implies X <>HIDDENR2 {}XBOOLE-0K1"
sorry

mtheorem orders_1_th_50:
" for R be RelationRELAT-1M1 holds  for X be setHIDDENM2 holds X has-lower-Zorn-property-wrtORDERS-1R5 R implies X <>HIDDENR2 {}XBOOLE-0K1"
sorry

mtheorem orders_1_th_51:
" for R be RelationRELAT-1M1 holds  for X be setHIDDENM2 holds X has-upper-Zorn-property-wrtORDERS-1R4 R iff X has-lower-Zorn-property-wrtORDERS-1R5 R ~RELAT-1K4"
sorry

mtheorem orders_1_th_52:
" for R be RelationRELAT-1M1 holds  for X be setHIDDENM2 holds X has-upper-Zorn-property-wrtORDERS-1R4 R ~RELAT-1K4 iff X has-lower-Zorn-property-wrtORDERS-1R5 R"
sorry

mdef orders_1_def_12 (" _ is-maximal-inORDERS-1R6  _ " [50,50]50 ) where
  mlet "R be RelationRELAT-1M1", "x be setHIDDENM2"
"pred x is-maximal-inORDERS-1R6 R means
  x inTARSKIR2 fieldRELAT-1K3 R &  not ( ex y be setHIDDENM2 st (y inTARSKIR2 fieldRELAT-1K3 R & y <>HIDDENR2 x) & [TARSKIK4 x,y ] inHIDDENR3 R)"..

mdef orders_1_def_13 (" _ is-minimal-inORDERS-1R7  _ " [50,50]50 ) where
  mlet "R be RelationRELAT-1M1", "x be setHIDDENM2"
"pred x is-minimal-inORDERS-1R7 R means
  x inTARSKIR2 fieldRELAT-1K3 R &  not ( ex y be setHIDDENM2 st (y inTARSKIR2 fieldRELAT-1K3 R & y <>HIDDENR2 x) & [TARSKIK4 y,x ] inHIDDENR3 R)"..

mdef orders_1_def_14 (" _ is-superior-ofORDERS-1R8  _ " [50,50]50 ) where
  mlet "R be RelationRELAT-1M1", "x be setHIDDENM2"
"pred x is-superior-ofORDERS-1R8 R means
  x inTARSKIR2 fieldRELAT-1K3 R & ( for y be setHIDDENM2 holds y inTARSKIR2 fieldRELAT-1K3 R & y <>HIDDENR2 x implies [TARSKIK4 y,x ] inHIDDENR3 R)"..

mdef orders_1_def_15 (" _ is-inferior-ofORDERS-1R9  _ " [50,50]50 ) where
  mlet "R be RelationRELAT-1M1", "x be setHIDDENM2"
"pred x is-inferior-ofORDERS-1R9 R means
  x inTARSKIR2 fieldRELAT-1K3 R & ( for y be setHIDDENM2 holds y inTARSKIR2 fieldRELAT-1K3 R & y <>HIDDENR2 x implies [TARSKIK4 x,y ] inHIDDENR3 R)"..

mtheorem orders_1_th_53:
" for R be RelationRELAT-1M1 holds  for x be setHIDDENM2 holds x is-inferior-ofORDERS-1R9 R & R be antisymmetricRELAT-2V4 implies x is-minimal-inORDERS-1R7 R"
sorry

mtheorem orders_1_th_54:
" for R be RelationRELAT-1M1 holds  for x be setHIDDENM2 holds x is-superior-ofORDERS-1R8 R & R be antisymmetricRELAT-2V4 implies x is-maximal-inORDERS-1R6 R"
sorry

mtheorem orders_1_th_55:
" for R be RelationRELAT-1M1 holds  for x be setHIDDENM2 holds x is-minimal-inORDERS-1R7 R & R be connectedRELAT-2V6 implies x is-inferior-ofORDERS-1R9 R"
sorry

mtheorem orders_1_th_56:
" for R be RelationRELAT-1M1 holds  for x be setHIDDENM2 holds x is-maximal-inORDERS-1R6 R & R be connectedRELAT-2V6 implies x is-superior-ofORDERS-1R8 R"
sorry

mtheorem orders_1_th_57:
" for R be RelationRELAT-1M1 holds  for X be setHIDDENM2 holds  for x be setHIDDENM2 holds ((x inTARSKIR2 X & x is-superior-ofORDERS-1R8 R) & X c=TARSKIR1 fieldRELAT-1K3 R) & R be reflexiveRELAT-2V1 implies X has-upper-Zorn-property-wrtORDERS-1R4 R"
sorry

mtheorem orders_1_th_58:
" for R be RelationRELAT-1M1 holds  for X be setHIDDENM2 holds  for x be setHIDDENM2 holds ((x inTARSKIR2 X & x is-inferior-ofORDERS-1R9 R) & X c=TARSKIR1 fieldRELAT-1K3 R) & R be reflexiveRELAT-2V1 implies X has-lower-Zorn-property-wrtORDERS-1R5 R"
sorry

mtheorem orders_1_th_59:
" for R be RelationRELAT-1M1 holds  for x be setHIDDENM2 holds x is-minimal-inORDERS-1R7 R iff x is-maximal-inORDERS-1R6 R ~RELAT-1K4"
sorry

mtheorem orders_1_th_60:
" for R be RelationRELAT-1M1 holds  for x be setHIDDENM2 holds x is-minimal-inORDERS-1R7 R ~RELAT-1K4 iff x is-maximal-inORDERS-1R6 R"
sorry

mtheorem orders_1_th_61:
" for R be RelationRELAT-1M1 holds  for x be setHIDDENM2 holds x is-inferior-ofORDERS-1R9 R iff x is-superior-ofORDERS-1R8 R ~RELAT-1K4"
sorry

mtheorem orders_1_th_62:
" for R be RelationRELAT-1M1 holds  for x be setHIDDENM2 holds x is-inferior-ofORDERS-1R9 R ~RELAT-1K4 iff x is-superior-ofORDERS-1R8 R"
sorry

mlemma orders_1_lm_18:
" for R be RelationRELAT-1M1 holds  for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds R well-ordersWELLORD1R2 X & Y c=TARSKIR1 X implies R well-ordersWELLORD1R2 Y"
sorry

reserve A, C for "OrdinalORDINAL1M3"
mtheorem orders_1_th_63:
" for R be RelationRELAT-1M1 holds  for X be setHIDDENM2 holds (R partially-ordersORDERS-1R2 X & fieldRELAT-1K3 R =XBOOLE-0R4 X) & X has-upper-Zorn-property-wrtORDERS-1R4 R implies ( ex x be setHIDDENM2 st x is-maximal-inORDERS-1R6 R)"
sorry

mtheorem orders_1_th_64:
" for R be RelationRELAT-1M1 holds  for X be setHIDDENM2 holds (R partially-ordersORDERS-1R2 X & fieldRELAT-1K3 R =XBOOLE-0R4 X) & X has-lower-Zorn-property-wrtORDERS-1R5 R implies ( ex x be setHIDDENM2 st x is-minimal-inORDERS-1R7 R)"
sorry

(*\$N Kuratowski-Zorn Lemma*)
(*\$N Zorn Lemma*)
mtheorem orders_1_th_65:
" for X be setHIDDENM2 holds X <>HIDDENR2 {}XBOOLE-0K1 & ( for Z be setHIDDENM2 holds Z c=TARSKIR1 X & Z be c=-linearORDINAL1V6 implies ( ex Y be setHIDDENM2 st Y inTARSKIR2 X & ( for X1 be setHIDDENM2 holds X1 inTARSKIR2 Z implies X1 c=TARSKIR1 Y))) implies ( ex Y be setHIDDENM2 st Y inTARSKIR2 X & ( for Z be setHIDDENM2 holds Z inTARSKIR2 X & Z <>HIDDENR2 Y implies  not Y c=TARSKIR1 Z))"
sorry

mtheorem orders_1_th_66:
" for X be setHIDDENM2 holds X <>HIDDENR2 {}XBOOLE-0K1 & ( for Z be setHIDDENM2 holds Z c=TARSKIR1 X & Z be c=-linearORDINAL1V6 implies ( ex Y be setHIDDENM2 st Y inTARSKIR2 X & ( for X1 be setHIDDENM2 holds X1 inTARSKIR2 Z implies Y c=TARSKIR1 X1))) implies ( ex Y be setHIDDENM2 st Y inTARSKIR2 X & ( for Z be setHIDDENM2 holds Z inTARSKIR2 X & Z <>HIDDENR2 Y implies  not Z c=TARSKIR1 Y))"
sorry

mtheorem orders_1_th_67:
" for X be setHIDDENM2 holds X <>HIDDENR2 {}XBOOLE-0K1 & ( for Z be setHIDDENM2 holds (Z <>HIDDENR2 {}XBOOLE-0K1 & Z c=TARSKIR1 X) & Z be c=-linearORDINAL1V6 implies unionTARSKIK3 Z inTARSKIR2 X) implies ( ex Y be setHIDDENM2 st Y inTARSKIR2 X & ( for Z be setHIDDENM2 holds Z inTARSKIR2 X & Z <>HIDDENR2 Y implies  not Y c=TARSKIR1 Z))"
sorry

mtheorem orders_1_th_68:
" for X be setHIDDENM2 holds X <>HIDDENR2 {}XBOOLE-0K1 & ( for Z be setHIDDENM2 holds (Z <>HIDDENR2 {}XBOOLE-0K1 & Z c=TARSKIR1 X) & Z be c=-linearORDINAL1V6 implies meetSETFAM-1K1 Z inTARSKIR2 X) implies ( ex Y be setHIDDENM2 st Y inTARSKIR2 X & ( for Z be setHIDDENM2 holds Z inTARSKIR2 X & Z <>HIDDENR2 Y implies  not Z c=TARSKIR1 Y))"
sorry

theorem orders_1_sch_1:
  fixes Af0 Pp2 
  assumes
[ty]: "Af0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
   A1: " for x be ElementSUBSET-1M1-of Af0 holds Pp2(x,x)" and
   A2: " for x be ElementSUBSET-1M1-of Af0 holds  for y be ElementSUBSET-1M1-of Af0 holds Pp2(x,y) & Pp2(y,x) implies x =XBOOLE-0R4 y" and
   A3: " for x be ElementSUBSET-1M1-of Af0 holds  for y be ElementSUBSET-1M1-of Af0 holds  for z be ElementSUBSET-1M1-of Af0 holds Pp2(x,y) & Pp2(y,z) implies Pp2(x,z)" and
   A4: " for X be setHIDDENM2 holds X c=TARSKIR1 Af0 & ( for x be ElementSUBSET-1M1-of Af0 holds  for y be ElementSUBSET-1M1-of Af0 holds x inTARSKIR2 X & y inTARSKIR2 X implies Pp2(x,y) or Pp2(y,x)) implies ( ex y be ElementSUBSET-1M1-of Af0 st  for x be ElementSUBSET-1M1-of Af0 holds x inTARSKIR2 X implies Pp2(x,y))"
  shows " ex x be ElementSUBSET-1M1-of Af0 st  for y be ElementSUBSET-1M1-of Af0 holds x <>HIDDENR2 y implies  not Pp2(x,y)"
sorry

theorem orders_1_sch_2:
  fixes Af0 Pp2 
  assumes
[ty]: "Af0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
   A1: " for x be ElementSUBSET-1M1-of Af0 holds Pp2(x,x)" and
   A2: " for x be ElementSUBSET-1M1-of Af0 holds  for y be ElementSUBSET-1M1-of Af0 holds Pp2(x,y) & Pp2(y,x) implies x =XBOOLE-0R4 y" and
   A3: " for x be ElementSUBSET-1M1-of Af0 holds  for y be ElementSUBSET-1M1-of Af0 holds  for z be ElementSUBSET-1M1-of Af0 holds Pp2(x,y) & Pp2(y,z) implies Pp2(x,z)" and
   A4: " for X be setHIDDENM2 holds X c=TARSKIR1 Af0 & ( for x be ElementSUBSET-1M1-of Af0 holds  for y be ElementSUBSET-1M1-of Af0 holds x inTARSKIR2 X & y inTARSKIR2 X implies Pp2(x,y) or Pp2(y,x)) implies ( ex y be ElementSUBSET-1M1-of Af0 st  for x be ElementSUBSET-1M1-of Af0 holds x inTARSKIR2 X implies Pp2(y,x))"
  shows " ex x be ElementSUBSET-1M1-of Af0 st  for y be ElementSUBSET-1M1-of Af0 holds x <>HIDDENR2 y implies  not Pp2(y,x)"
sorry

mtheorem orders_1_th_69:
" for R be RelationRELAT-1M1 holds  for X be setHIDDENM2 holds R partially-ordersORDERS-1R2 X & fieldRELAT-1K3 R =XBOOLE-0R4 X implies ( ex P be RelationRELAT-1M1 st (R c=RELAT-1R2 P & P linearly-ordersORDERS-1R3 X) & fieldRELAT-1K3 P =XBOOLE-0R4 X)"
sorry

mtheorem orders_1_th_70:
" for R be RelationRELAT-1M1 holds R c=RELAT-1R2 [:ZFMISC-1K2 fieldRELAT-1K3 R,fieldRELAT-1K3 R :]"
  using orders_1_lm_6 sorry

mtheorem orders_1_th_71:
" for R be RelationRELAT-1M1 holds  for X be setHIDDENM2 holds R be reflexiveRELAT-2V1 & X c=TARSKIR1 fieldRELAT-1K3 R implies fieldRELAT-1K3 (R |-2WELLORD1K2 X) =XBOOLE-0R4 X"
  using orders_1_lm_7 sorry

mtheorem orders_1_th_72:
" for R be RelationRELAT-1M1 holds  for X be setHIDDENM2 holds R is-reflexive-inRELAT-2R1 X implies R |-2WELLORD1K2 X be reflexiveRELAT-2V1"
  using orders_1_lm_8 sorry

mtheorem orders_1_th_73:
" for R be RelationRELAT-1M1 holds  for X be setHIDDENM2 holds R is-transitive-inRELAT-2R8 X implies R |-2WELLORD1K2 X be transitiveRELAT-2V8"
  using orders_1_lm_9 sorry

mtheorem orders_1_th_74:
" for R be RelationRELAT-1M1 holds  for X be setHIDDENM2 holds R is-antisymmetric-inRELAT-2R4 X implies R |-2WELLORD1K2 X be antisymmetricRELAT-2V4"
  using orders_1_lm_10 sorry

mtheorem orders_1_th_75:
" for R be RelationRELAT-1M1 holds  for X be setHIDDENM2 holds R is-connected-inRELAT-2R6 X implies R |-2WELLORD1K2 X be connectedRELAT-2V6"
  using orders_1_lm_11 sorry

mtheorem orders_1_th_76:
" for R be RelationRELAT-1M1 holds  for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds R is-connected-inRELAT-2R6 X & Y c=TARSKIR1 X implies R is-connected-inRELAT-2R6 Y"
   sorry

mtheorem orders_1_th_77:
" for R be RelationRELAT-1M1 holds  for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds R well-ordersWELLORD1R2 X & Y c=TARSKIR1 X implies R well-ordersWELLORD1R2 Y"
  using orders_1_lm_18 sorry

mtheorem orders_1_th_78:
" for R be RelationRELAT-1M1 holds R be connectedRELAT-2V6 implies R ~RELAT-1K4 be connectedRELAT-2V6"
  using orders_1_lm_5 sorry

mtheorem orders_1_th_79:
" for R be RelationRELAT-1M1 holds  for X be setHIDDENM2 holds R is-reflexive-inRELAT-2R1 X implies R ~RELAT-1K4 is-reflexive-inRELAT-2R1 X"
  using orders_1_lm_12 sorry

mtheorem orders_1_th_80:
" for R be RelationRELAT-1M1 holds  for X be setHIDDENM2 holds R is-transitive-inRELAT-2R8 X implies R ~RELAT-1K4 is-transitive-inRELAT-2R8 X"
  using orders_1_lm_13 sorry

mtheorem orders_1_th_81:
" for R be RelationRELAT-1M1 holds  for X be setHIDDENM2 holds R is-antisymmetric-inRELAT-2R4 X implies R ~RELAT-1K4 is-antisymmetric-inRELAT-2R4 X"
  using orders_1_lm_14 sorry

mtheorem orders_1_th_82:
" for R be RelationRELAT-1M1 holds  for X be setHIDDENM2 holds R is-connected-inRELAT-2R6 X implies R ~RELAT-1K4 is-connected-inRELAT-2R6 X"
  using orders_1_lm_15 sorry

mtheorem orders_1_th_83:
" for R be RelationRELAT-1M1 holds  for X be setHIDDENM2 holds (R |-2WELLORD1K2 X)~RELAT-1K4 =RELAT-1R1 R ~RELAT-1K4 |-2WELLORD1K2 X"
  using orders_1_lm_16 sorry

mtheorem orders_1_th_84:
" for R be RelationRELAT-1M1 holds R |-2WELLORD1K2 {}XBOOLE-0K1 =RELAT-1R1 {}XBOOLE-0K1"
  using orders_1_lm_17 sorry

(*begin*)
mtheorem orders_1_th_85:
" for f be FunctionFUNCT-1M1 holds  for Z be setHIDDENM2 holds Z be finiteFINSET-1V1 & Z c=TARSKIR1 rngFUNCT-1K2 f implies ( ex Y be setHIDDENM2 st (Y c=TARSKIR1 domRELAT-1K1 f & Y be finiteFINSET-1V1) & f .:FUNCT-1K5 Y =XBOOLE-0R4 Z)"
sorry

mtheorem orders_1_th_86:
" for R be RelationRELAT-1M1 holds fieldRELAT-1K3 R be finiteFINSET-1V1 implies R be finiteFINSET-1V1"
sorry

mtheorem orders_1_th_87:
" for R be RelationRELAT-1M1 holds domRELAT-1K1 R be finiteFINSET-1V1 & rngRELAT-1K2 R be finiteFINSET-1V1 implies R be finiteFINSET-1V1"
sorry

mtheorem orders_1_cl_5:
"cluster order-type-ofWELLORD2K2 {}XBOOLE-0K1 as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "order-type-ofWELLORD2K2 {}XBOOLE-0K1 be emptyXBOOLE-0V1"
sorry
qed "sorry"

mtheorem orders_1_th_88:
" for O be OrdinalORDINAL1M3 holds order-type-ofWELLORD2K2 RelInclWELLORD2K1 O =XBOOLE-0R4 O"
sorry

abbreviation(input) ORDERS_1K2("RelInclORDERS-1K2  _ " [228]228) where
  "RelInclORDERS-1K2 X \<equiv> RelInclWELLORD2K1 X"

mtheorem orders_1_add_2:
  mlet "X be setHIDDENM2"
"cluster RelInclWELLORD2K1 X as-term-is OrderORDERS-1M4-of X"
proof
(*coherence*)
  show "RelInclWELLORD2K1 X be OrderORDERS-1M4-of X"
sorry
qed "sorry"

mtheorem orders_1_th_89:
" for M be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  not {}XBOOLE-0K1 inTARSKIR2 M implies ( for Ch be Choice-FunctionORDERS-1M3-of M holds  for X be setHIDDENM2 holds X inTARSKIR2 M implies Ch .FUNCT-1K1 X inTARSKIR2 X)"
  using orders_1_lm_2 sorry

mtheorem orders_1_th_90:
" for M be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  not {}XBOOLE-0K1 inTARSKIR2 M implies ( for Ch be Choice-FunctionORDERS-1M3-of M holds Ch be FunctionFUNCT-2M1-of(M,unionTARSKIK3 M))"
  using orders_1_lm_3 sorry

end
