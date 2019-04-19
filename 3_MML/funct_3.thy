theory funct_3
  imports binop_1 domain_1
   "../mizar_extension/E_number"
begin
(*begin*)
reserve p, q, x, x1, x2, y, y1, y2, z, z1, z2 for "setHIDDENM2"
reserve A, B, V, X, X1, X2, Y, Y1, Y2, Z for "setHIDDENM2"
reserve C, C1, C2, D, D1, D2 for " non emptyXBOOLE-0V1\<bar>setHIDDENM2"
mtheorem funct_3_th_1:
" for A be setHIDDENM2 holds  for Y be setHIDDENM2 holds A c=TARSKIR1 Y implies idRELAT-1K7 A =FUNCT-1R1 idRELAT-1K7 Y |RELAT-1K8 A"
sorry

mtheorem funct_3_th_2:
" for X be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds X c=TARSKIR1 domRELAT-1K1 (g *FUNCT-1K3 f) implies f .:FUNCT-1K5 X c=TARSKIR1 domRELAT-1K1 g"
sorry

mtheorem funct_3_th_3:
" for X be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds X c=TARSKIR1 domRELAT-1K1 f & f .:FUNCT-1K5 X c=TARSKIR1 domRELAT-1K1 g implies X c=TARSKIR1 domRELAT-1K1 (g *FUNCT-1K3 f)"
sorry

mtheorem funct_3_th_4:
" for Y be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds Y c=TARSKIR1 rngFUNCT-1K2 (g *FUNCT-1K3 f) & g be one-to-oneFUNCT-1V2 implies g \<inverse>FUNCT-1K6 Y c=TARSKIR1 rngFUNCT-1K2 f"
sorry

mtheorem funct_3_th_5:
" for Y be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds Y c=TARSKIR1 rngFUNCT-1K2 g & g \<inverse>FUNCT-1K6 Y c=TARSKIR1 rngFUNCT-1K2 f implies Y c=TARSKIR1 rngFUNCT-1K2 (g *FUNCT-1K3 f)"
sorry

theorem funct_3_sch_1:
  fixes Af0 Bf0 Pp3 
  assumes
[ty]: "Af0 be setHIDDENM2" and
  [ty]: "Bf0 be setHIDDENM2" and
   A1: " for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for z1 be objectHIDDENM1 holds  for z2 be objectHIDDENM1 holds ((x inHIDDENR3 Af0 & y inHIDDENR3 Bf0) & Pp3(x,y,z1)) & Pp3(x,y,z2) implies z1 =HIDDENR1 z2" and
   A2: " for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds x inHIDDENR3 Af0 & y inHIDDENR3 Bf0 implies ( ex z be objectHIDDENM1 st Pp3(x,y,z))"
  shows " ex f be FunctionFUNCT-1M1 st domRELAT-1K1 f =XBOOLE-0R4 [:ZFMISC-1K2 Af0,Bf0 :] & ( for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds x inHIDDENR3 Af0 & y inHIDDENR3 Bf0 implies Pp3(x,y,f .BINOP-1K1(x,y)))"
sorry

theorem funct_3_sch_2:
  fixes Af0 Bf0 Ff2 
  assumes
[ty]: "Af0 be setHIDDENM2" and
  [ty]: "Bf0 be setHIDDENM2" and
  [ty_func]: "\<And> x1 x2. x1 be objectHIDDENM1 \<Longrightarrow> x2 be objectHIDDENM1 \<Longrightarrow> Ff2(x1,x2) be objectHIDDENM1"
  shows " ex f be FunctionFUNCT-1M1 st domRELAT-1K1 f =XBOOLE-0R4 [:ZFMISC-1K2 Af0,Bf0 :] & ( for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds x inHIDDENR3 Af0 & y inHIDDENR3 Bf0 implies f .BINOP-1K1(x,y) =HIDDENR1 Ff2(x,y))"
sorry

mtheorem funct_3_th_6:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds (domRELAT-1K1 f =XBOOLE-0R4 [:ZFMISC-1K2 X,Y :] & domRELAT-1K1 g =XBOOLE-0R4 [:ZFMISC-1K2 X,Y :]) & ( for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds x inHIDDENR3 X & y inHIDDENR3 Y implies f .BINOP-1K1(x,y) =XBOOLE-0R4 g .BINOP-1K1(x,y)) implies f =FUNCT-1R1 g"
sorry

mdef funct_3_def_1 (".:FUNCT-3K1  _ " [200]200 ) where
  mlet "f be FunctionFUNCT-1M1"
"func .:FUNCT-3K1 f \<rightarrow> FunctionFUNCT-1M1 means
  \<lambda>it. domRELAT-1K1 it =XBOOLE-0R4 boolZFMISC-1K1 (domRELAT-1K1 f) & ( for X be setHIDDENM2 holds X c=TARSKIR1 domRELAT-1K1 f implies it .FUNCT-1K1 X =XBOOLE-0R4 f .:FUNCT-1K5 X)"
proof-
  (*existence*)
    show " ex it be FunctionFUNCT-1M1 st domRELAT-1K1 it =XBOOLE-0R4 boolZFMISC-1K1 (domRELAT-1K1 f) & ( for X be setHIDDENM2 holds X c=TARSKIR1 domRELAT-1K1 f implies it .FUNCT-1K1 X =XBOOLE-0R4 f .:FUNCT-1K5 X)"
sorry
  (*uniqueness*)
    show " for it1 be FunctionFUNCT-1M1 holds  for it2 be FunctionFUNCT-1M1 holds (domRELAT-1K1 it1 =XBOOLE-0R4 boolZFMISC-1K1 (domRELAT-1K1 f) & ( for X be setHIDDENM2 holds X c=TARSKIR1 domRELAT-1K1 f implies it1 .FUNCT-1K1 X =XBOOLE-0R4 f .:FUNCT-1K5 X)) & (domRELAT-1K1 it2 =XBOOLE-0R4 boolZFMISC-1K1 (domRELAT-1K1 f) & ( for X be setHIDDENM2 holds X c=TARSKIR1 domRELAT-1K1 f implies it2 .FUNCT-1K1 X =XBOOLE-0R4 f .:FUNCT-1K5 X)) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mtheorem funct_3_th_7:
" for X be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds X inTARSKIR2 domRELAT-1K1 (.:FUNCT-3K1 f) implies (.:FUNCT-3K1 f).FUNCT-1K1 X =XBOOLE-0R4 f .:FUNCT-1K5 X"
sorry

mtheorem funct_3_th_8:
" for f be FunctionFUNCT-1M1 holds (.:FUNCT-3K1 f).FUNCT-1K1 {}XBOOLE-0K1 =XBOOLE-0R4 {}XBOOLE-0K1"
sorry

mtheorem funct_3_th_9:
" for f be FunctionFUNCT-1M1 holds rngFUNCT-1K2 (.:FUNCT-3K1 f) c=TARSKIR1 boolZFMISC-1K1 (rngFUNCT-1K2 f)"
sorry

mtheorem funct_3_th_10:
" for A be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds (.:FUNCT-3K1 f).:FUNCT-1K5 A c=TARSKIR1 boolZFMISC-1K1 (rngFUNCT-1K2 f)"
sorry

mtheorem funct_3_th_11:
" for B be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds (.:FUNCT-3K1 f)\<inverse>FUNCT-1K6 B c=TARSKIR1 boolZFMISC-1K1 (domRELAT-1K1 f)"
sorry

mtheorem funct_3_th_12:
" for B be setHIDDENM2 holds  for X be setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(X,D) holds (.:FUNCT-3K1 f)\<inverse>FUNCT-1K6 B c=TARSKIR1 boolZFMISC-1K1 X"
sorry

mtheorem funct_3_th_13:
" for A be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds unionTARSKIK3 ((.:FUNCT-3K1 f).:FUNCT-1K5 A) c=TARSKIR1 f .:FUNCT-1K5 unionTARSKIK3 A"
sorry

mtheorem funct_3_th_14:
" for A be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds A c=TARSKIR1 boolZFMISC-1K1 (domRELAT-1K1 f) implies f .:FUNCT-1K5 unionTARSKIK3 A =XBOOLE-0R4 unionTARSKIK3 ((.:FUNCT-3K1 f).:FUNCT-1K5 A)"
sorry

mtheorem funct_3_th_15:
" for A be setHIDDENM2 holds  for X be setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(X,D) holds A c=TARSKIR1 boolZFMISC-1K1 X implies f .:FUNCT-1K5 unionTARSKIK3 A =XBOOLE-0R4 unionTARSKIK3 ((.:FUNCT-3K1 f).:FUNCT-1K5 A)"
sorry

mtheorem funct_3_th_16:
" for B be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds unionTARSKIK3 ((.:FUNCT-3K1 f)\<inverse>FUNCT-1K6 B) c=TARSKIR1 f \<inverse>FUNCT-1K6 (unionTARSKIK3 B)"
sorry

mtheorem funct_3_th_17:
" for B be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds B c=TARSKIR1 boolZFMISC-1K1 (rngFUNCT-1K2 f) implies f \<inverse>FUNCT-1K6 (unionTARSKIK3 B) =XBOOLE-0R4 unionTARSKIK3 ((.:FUNCT-3K1 f)\<inverse>FUNCT-1K6 B)"
sorry

mtheorem funct_3_th_18:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds .:FUNCT-3K1 (g *FUNCT-1K3 f) =FUNCT-1R1 .:FUNCT-3K1 g *FUNCT-1K3 .:FUNCT-3K1 f"
sorry

mtheorem funct_3_th_19:
" for f be FunctionFUNCT-1M1 holds .:FUNCT-3K1 f be FunctionFUNCT-2M1-of(boolZFMISC-1K1 (domRELAT-1K1 f),boolZFMISC-1K1 (rngFUNCT-1K2 f))"
sorry

mtheorem funct_3_th_20:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(X,Y) holds (Y =XBOOLE-0R4 {}XBOOLE-0K1 implies X =XBOOLE-0R4 {}XBOOLE-0K1) implies .:FUNCT-3K1 f be FunctionFUNCT-2M1-of(boolZFMISC-1K1 X,boolZFMISC-1K1 Y)"
sorry

syntax FUNCT_3K2 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (".:FUNCT-3K2\<^bsub>'( _ , _ ')\<^esub>  _ " [0,0,200]200)
translations ".:FUNCT-3K2\<^bsub>(X,D)\<^esub> f" \<rightharpoonup> ".:FUNCT-3K1 f"

mtheorem funct_3_add_1:
  mlet "X be setHIDDENM2", "D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "f be FunctionFUNCT-2M1-of(X,D)"
"cluster .:FUNCT-3K1 f as-term-is FunctionFUNCT-2M1-of(boolZFMISC-1K1 X,boolZFMISC-1K1 D)"
proof
(*coherence*)
  show ".:FUNCT-3K1 f be FunctionFUNCT-2M1-of(boolZFMISC-1K1 X,boolZFMISC-1K1 D)"
    using funct_3_th_20 sorry
qed "sorry"

mdef funct_3_def_2 ("\<inverse>FUNCT-3K3  _ " [228]228 ) where
  mlet "f be FunctionFUNCT-1M1"
"func \<inverse>FUNCT-3K3 f \<rightarrow> FunctionFUNCT-1M1 means
  \<lambda>it. domRELAT-1K1 it =XBOOLE-0R4 boolZFMISC-1K1 (rngFUNCT-1K2 f) & ( for Y be setHIDDENM2 holds Y c=TARSKIR1 rngFUNCT-1K2 f implies it .FUNCT-1K1 Y =XBOOLE-0R4 f \<inverse>FUNCT-1K6 Y)"
proof-
  (*existence*)
    show " ex it be FunctionFUNCT-1M1 st domRELAT-1K1 it =XBOOLE-0R4 boolZFMISC-1K1 (rngFUNCT-1K2 f) & ( for Y be setHIDDENM2 holds Y c=TARSKIR1 rngFUNCT-1K2 f implies it .FUNCT-1K1 Y =XBOOLE-0R4 f \<inverse>FUNCT-1K6 Y)"
sorry
  (*uniqueness*)
    show " for it1 be FunctionFUNCT-1M1 holds  for it2 be FunctionFUNCT-1M1 holds (domRELAT-1K1 it1 =XBOOLE-0R4 boolZFMISC-1K1 (rngFUNCT-1K2 f) & ( for Y be setHIDDENM2 holds Y c=TARSKIR1 rngFUNCT-1K2 f implies it1 .FUNCT-1K1 Y =XBOOLE-0R4 f \<inverse>FUNCT-1K6 Y)) & (domRELAT-1K1 it2 =XBOOLE-0R4 boolZFMISC-1K1 (rngFUNCT-1K2 f) & ( for Y be setHIDDENM2 holds Y c=TARSKIR1 rngFUNCT-1K2 f implies it2 .FUNCT-1K1 Y =XBOOLE-0R4 f \<inverse>FUNCT-1K6 Y)) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mtheorem funct_3_th_21:
" for Y be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds Y inTARSKIR2 domRELAT-1K1 (\<inverse>FUNCT-3K3 f) implies \<inverse>FUNCT-3K3 f .FUNCT-1K1 Y =XBOOLE-0R4 f \<inverse>FUNCT-1K6 Y"
sorry

mtheorem funct_3_th_22:
" for f be FunctionFUNCT-1M1 holds rngFUNCT-1K2 (\<inverse>FUNCT-3K3 f) c=TARSKIR1 boolZFMISC-1K1 (domRELAT-1K1 f)"
sorry

mtheorem funct_3_th_23:
" for B be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds \<inverse>FUNCT-3K3 f .:FUNCT-1K5 B c=TARSKIR1 boolZFMISC-1K1 (domRELAT-1K1 f)"
sorry

mtheorem funct_3_th_24:
" for A be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds (\<inverse>FUNCT-3K3 f)\<inverse>FUNCT-1K6 A c=TARSKIR1 boolZFMISC-1K1 (rngFUNCT-1K2 f)"
sorry

mtheorem funct_3_th_25:
" for B be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds unionTARSKIK3 (\<inverse>FUNCT-3K3 f .:FUNCT-1K5 B) c=TARSKIR1 f \<inverse>FUNCT-1K6 (unionTARSKIK3 B)"
sorry

mtheorem funct_3_th_26:
" for B be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds B c=TARSKIR1 boolZFMISC-1K1 (rngFUNCT-1K2 f) implies unionTARSKIK3 (\<inverse>FUNCT-3K3 f .:FUNCT-1K5 B) =XBOOLE-0R4 f \<inverse>FUNCT-1K6 (unionTARSKIK3 B)"
sorry

mtheorem funct_3_th_27:
" for A be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds unionTARSKIK3 ((\<inverse>FUNCT-3K3 f)\<inverse>FUNCT-1K6 A) c=TARSKIR1 f .:FUNCT-1K5 unionTARSKIK3 A"
sorry

mtheorem funct_3_th_28:
" for A be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds A c=TARSKIR1 boolZFMISC-1K1 (domRELAT-1K1 f) & f be one-to-oneFUNCT-1V2 implies unionTARSKIK3 ((\<inverse>FUNCT-3K3 f)\<inverse>FUNCT-1K6 A) =XBOOLE-0R4 f .:FUNCT-1K5 unionTARSKIK3 A"
sorry

mtheorem funct_3_th_29:
" for B be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds \<inverse>FUNCT-3K3 f .:FUNCT-1K5 B c=TARSKIR1 (.:FUNCT-3K1 f)\<inverse>FUNCT-1K6 B"
sorry

mtheorem funct_3_th_30:
" for B be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds f be one-to-oneFUNCT-1V2 implies \<inverse>FUNCT-3K3 f .:FUNCT-1K5 B =XBOOLE-0R4 (.:FUNCT-3K1 f)\<inverse>FUNCT-1K6 B"
sorry

mtheorem funct_3_th_31:
" for f be FunctionFUNCT-1M1 holds  for A be setHIDDENM2 holds A c=TARSKIR1 boolZFMISC-1K1 (domRELAT-1K1 f) implies (\<inverse>FUNCT-3K3 f)\<inverse>FUNCT-1K6 A c=TARSKIR1 (.:FUNCT-3K1 f).:FUNCT-1K5 A"
sorry

mtheorem funct_3_th_32:
" for f be FunctionFUNCT-1M1 holds  for A be setHIDDENM2 holds f be one-to-oneFUNCT-1V2 implies (.:FUNCT-3K1 f).:FUNCT-1K5 A c=TARSKIR1 (\<inverse>FUNCT-3K3 f)\<inverse>FUNCT-1K6 A"
sorry

mtheorem funct_3_th_33:
" for f be FunctionFUNCT-1M1 holds  for A be setHIDDENM2 holds f be one-to-oneFUNCT-1V2 & A c=TARSKIR1 boolZFMISC-1K1 (domRELAT-1K1 f) implies (\<inverse>FUNCT-3K3 f)\<inverse>FUNCT-1K6 A =XBOOLE-0R4 (.:FUNCT-3K1 f).:FUNCT-1K5 A"
sorry

mtheorem funct_3_th_34:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds g be one-to-oneFUNCT-1V2 implies \<inverse>FUNCT-3K3 (g *FUNCT-1K3 f) =FUNCT-1R1 \<inverse>FUNCT-3K3 f *FUNCT-1K3 \<inverse>FUNCT-3K3 g"
sorry

mtheorem funct_3_th_35:
" for f be FunctionFUNCT-1M1 holds \<inverse>FUNCT-3K3 f be FunctionFUNCT-2M1-of(boolZFMISC-1K1 (rngFUNCT-1K2 f),boolZFMISC-1K1 (domRELAT-1K1 f))"
sorry

mdef funct_3_def_3 ("chiFUNCT-3K4'( _ , _ ')" [0,0]228 ) where
  mlet "A be setHIDDENM2", "X be setHIDDENM2"
"func chiFUNCT-3K4(A,X) \<rightarrow> FunctionFUNCT-1M1 means
  \<lambda>it. domRELAT-1K1 it =XBOOLE-0R4 X & ( for x be objectHIDDENM1 holds x inHIDDENR3 X implies (x inHIDDENR3 A implies it .FUNCT-1K1 x =XBOOLE-0R4 \<one>\<^sub>M) & ( not x inHIDDENR3 A implies it .FUNCT-1K1 x =XBOOLE-0R4 0ORDINAL1K5))"
proof-
  (*existence*)
    show " ex it be FunctionFUNCT-1M1 st domRELAT-1K1 it =XBOOLE-0R4 X & ( for x be objectHIDDENM1 holds x inHIDDENR3 X implies (x inHIDDENR3 A implies it .FUNCT-1K1 x =XBOOLE-0R4 \<one>\<^sub>M) & ( not x inHIDDENR3 A implies it .FUNCT-1K1 x =XBOOLE-0R4 0ORDINAL1K5))"
sorry
  (*uniqueness*)
    show " for it1 be FunctionFUNCT-1M1 holds  for it2 be FunctionFUNCT-1M1 holds (domRELAT-1K1 it1 =XBOOLE-0R4 X & ( for x be objectHIDDENM1 holds x inHIDDENR3 X implies (x inHIDDENR3 A implies it1 .FUNCT-1K1 x =XBOOLE-0R4 \<one>\<^sub>M) & ( not x inHIDDENR3 A implies it1 .FUNCT-1K1 x =XBOOLE-0R4 0ORDINAL1K5))) & (domRELAT-1K1 it2 =XBOOLE-0R4 X & ( for x be objectHIDDENM1 holds x inHIDDENR3 X implies (x inHIDDENR3 A implies it2 .FUNCT-1K1 x =XBOOLE-0R4 \<one>\<^sub>M) & ( not x inHIDDENR3 A implies it2 .FUNCT-1K1 x =XBOOLE-0R4 0ORDINAL1K5))) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mtheorem funct_3_th_36:
" for A be setHIDDENM2 holds  for X be setHIDDENM2 holds  for x be objectHIDDENM1 holds chiFUNCT-3K4(A,X) .FUNCT-1K1 x =XBOOLE-0R4 \<one>\<^sub>M implies x inHIDDENR3 A"
sorry

mtheorem funct_3_th_37:
" for x be setHIDDENM2 holds  for A be setHIDDENM2 holds  for X be setHIDDENM2 holds x inTARSKIR2 X \\SUBSET-1K6 A implies chiFUNCT-3K4(A,X) .FUNCT-1K1 x =XBOOLE-0R4 0ORDINAL1K5"
sorry

mtheorem funct_3_th_38:
" for A be setHIDDENM2 holds  for B be setHIDDENM2 holds  for X be setHIDDENM2 holds (A c=TARSKIR1 X & B c=TARSKIR1 X) & chiFUNCT-3K4(A,X) =FUNCT-1R1 chiFUNCT-3K4(B,X) implies A =XBOOLE-0R4 B"
sorry

mtheorem funct_3_th_39:
" for A be setHIDDENM2 holds  for X be setHIDDENM2 holds rngFUNCT-1K2 (chiFUNCT-3K4(A,X)) c=TARSKIR1 {TARSKIK2 0ORDINAL1K5,\<one>\<^sub>M }"
sorry

mtheorem funct_3_th_40:
" for X be setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(X,{TARSKIK2 0ORDINAL1K5,\<one>\<^sub>M }) holds f =FUNCT-1R1 chiFUNCT-3K4(f \<inverse>FUNCT-1K6 {TARSKIK1 \<one>\<^sub>M},X)"
sorry

abbreviation(input) FUNCT_3K5("chiFUNCT-3K5'( _ , _ ')" [0,0]228) where
  "chiFUNCT-3K5(A,X) \<equiv> chiFUNCT-3K4(A,X)"

mtheorem funct_3_add_2:
  mlet "A be setHIDDENM2", "X be setHIDDENM2"
"cluster chiFUNCT-3K4(A,X) as-term-is FunctionFUNCT-2M1-of(X,{TARSKIK2 0ORDINAL1K5,\<one>\<^sub>M })"
proof
(*coherence*)
  show "chiFUNCT-3K4(A,X) be FunctionFUNCT-2M1-of(X,{TARSKIK2 0ORDINAL1K5,\<one>\<^sub>M })"
sorry
qed "sorry"

syntax FUNCT_3K6 :: " Set \<Rightarrow>  Set \<Rightarrow> Set" ("inclFUNCT-3K6\<^bsub>'( _ ')\<^esub>  _ " [0,228]228)
translations "inclFUNCT-3K6\<^bsub>(Y)\<^esub> A" \<rightharpoonup> "idRELAT-1K7 A"

syntax FUNCT_3K7 :: " Set \<Rightarrow>  Set \<Rightarrow> Set" ("inclFUNCT-3K7\<^bsub>'( _ ')\<^esub>  _ " [0,228]228)
translations "inclFUNCT-3K7\<^bsub>(Y)\<^esub> A" \<rightharpoonup> "idRELAT-1K7 A"

mtheorem funct_3_add_3:
  mlet "Y be setHIDDENM2", "A be SubsetSUBSET-1M2-of Y"
"cluster idRELAT-1K7 A as-term-is FunctionFUNCT-2M1-of(A,Y)"
proof
(*coherence*)
  show "idRELAT-1K7 A be FunctionFUNCT-2M1-of(A,Y)"
sorry
qed "sorry"

mtheorem funct_3_th_41:
" for Y be setHIDDENM2 holds  for A be SubsetSUBSET-1M2-of Y holds inclFUNCT-3K7\<^bsub>(Y)\<^esub> A =FUNCT-1R1 idRELAT-1K7 Y |RELAT-1K8 A"
  using funct_3_th_1 sorry

mtheorem funct_3_th_42:
" for x be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for A be SubsetSUBSET-1M2-of Y holds x inTARSKIR2 A implies inclFUNCT-3K7\<^bsub>(Y)\<^esub> A .FUNCT-1K1 x inTARSKIR2 Y"
sorry

mdef funct_3_def_4 ("pr1FUNCT-3K8'( _ , _ ')" [0,0]228 ) where
  mlet "X be setHIDDENM2", "Y be setHIDDENM2"
"func pr1FUNCT-3K8(X,Y) \<rightarrow> FunctionFUNCT-1M1 means
  \<lambda>it. domRELAT-1K1 it =XBOOLE-0R4 [:ZFMISC-1K2 X,Y :] & ( for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds x inHIDDENR3 X & y inHIDDENR3 Y implies it .BINOP-1K1(x,y) =HIDDENR1 x)"
proof-
  (*existence*)
    show " ex it be FunctionFUNCT-1M1 st domRELAT-1K1 it =XBOOLE-0R4 [:ZFMISC-1K2 X,Y :] & ( for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds x inHIDDENR3 X & y inHIDDENR3 Y implies it .BINOP-1K1(x,y) =HIDDENR1 x)"
sorry
  (*uniqueness*)
    show " for it1 be FunctionFUNCT-1M1 holds  for it2 be FunctionFUNCT-1M1 holds (domRELAT-1K1 it1 =XBOOLE-0R4 [:ZFMISC-1K2 X,Y :] & ( for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds x inHIDDENR3 X & y inHIDDENR3 Y implies it1 .BINOP-1K1(x,y) =HIDDENR1 x)) & (domRELAT-1K1 it2 =XBOOLE-0R4 [:ZFMISC-1K2 X,Y :] & ( for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds x inHIDDENR3 X & y inHIDDENR3 Y implies it2 .BINOP-1K1(x,y) =HIDDENR1 x)) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mdef funct_3_def_5 ("pr2FUNCT-3K9'( _ , _ ')" [0,0]228 ) where
  mlet "X be setHIDDENM2", "Y be setHIDDENM2"
"func pr2FUNCT-3K9(X,Y) \<rightarrow> FunctionFUNCT-1M1 means
  \<lambda>it. domRELAT-1K1 it =XBOOLE-0R4 [:ZFMISC-1K2 X,Y :] & ( for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds x inHIDDENR3 X & y inHIDDENR3 Y implies it .BINOP-1K1(x,y) =HIDDENR1 y)"
proof-
  (*existence*)
    show " ex it be FunctionFUNCT-1M1 st domRELAT-1K1 it =XBOOLE-0R4 [:ZFMISC-1K2 X,Y :] & ( for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds x inHIDDENR3 X & y inHIDDENR3 Y implies it .BINOP-1K1(x,y) =HIDDENR1 y)"
sorry
  (*uniqueness*)
    show " for it1 be FunctionFUNCT-1M1 holds  for it2 be FunctionFUNCT-1M1 holds (domRELAT-1K1 it1 =XBOOLE-0R4 [:ZFMISC-1K2 X,Y :] & ( for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds x inHIDDENR3 X & y inHIDDENR3 Y implies it1 .BINOP-1K1(x,y) =HIDDENR1 y)) & (domRELAT-1K1 it2 =XBOOLE-0R4 [:ZFMISC-1K2 X,Y :] & ( for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds x inHIDDENR3 X & y inHIDDENR3 Y implies it2 .BINOP-1K1(x,y) =HIDDENR1 y)) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mtheorem funct_3_th_43:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds rngFUNCT-1K2 (pr1FUNCT-3K8(X,Y)) c=TARSKIR1 X"
sorry

mtheorem funct_3_th_44:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds Y <>HIDDENR2 {}XBOOLE-0K1 implies rngFUNCT-1K2 (pr1FUNCT-3K8(X,Y)) =XBOOLE-0R4 X"
sorry

mtheorem funct_3_th_45:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds rngFUNCT-1K2 (pr2FUNCT-3K9(X,Y)) c=TARSKIR1 Y"
sorry

mtheorem funct_3_th_46:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X <>HIDDENR2 {}XBOOLE-0K1 implies rngFUNCT-1K2 (pr2FUNCT-3K9(X,Y)) =XBOOLE-0R4 Y"
sorry

abbreviation(input) FUNCT_3K10("pr1FUNCT-3K10'( _ , _ ')" [0,0]228) where
  "pr1FUNCT-3K10(X,Y) \<equiv> pr1FUNCT-3K8(X,Y)"

mtheorem funct_3_add_4:
  mlet "X be setHIDDENM2", "Y be setHIDDENM2"
"cluster pr1FUNCT-3K8(X,Y) as-term-is FunctionFUNCT-2M1-of([:ZFMISC-1K2 X,Y :],X)"
proof
(*coherence*)
  show "pr1FUNCT-3K8(X,Y) be FunctionFUNCT-2M1-of([:ZFMISC-1K2 X,Y :],X)"
sorry
qed "sorry"

abbreviation(input) FUNCT_3K11("pr2FUNCT-3K11'( _ , _ ')" [0,0]228) where
  "pr2FUNCT-3K11(X,Y) \<equiv> pr2FUNCT-3K9(X,Y)"

mtheorem funct_3_add_5:
  mlet "X be setHIDDENM2", "Y be setHIDDENM2"
"cluster pr2FUNCT-3K9(X,Y) as-term-is FunctionFUNCT-2M1-of([:ZFMISC-1K2 X,Y :],Y)"
proof
(*coherence*)
  show "pr2FUNCT-3K9(X,Y) be FunctionFUNCT-2M1-of([:ZFMISC-1K2 X,Y :],Y)"
sorry
qed "sorry"

mdef funct_3_def_6 ("deltaFUNCT-3K12  _ " [228]228 ) where
  mlet "X be setHIDDENM2"
"func deltaFUNCT-3K12 X \<rightarrow> FunctionFUNCT-1M1 means
  \<lambda>it. domRELAT-1K1 it =XBOOLE-0R4 X & ( for x be objectHIDDENM1 holds x inHIDDENR3 X implies it .FUNCT-1K1 x =HIDDENR1 [TARSKIK4 x,x ])"
proof-
  (*existence*)
    show " ex it be FunctionFUNCT-1M1 st domRELAT-1K1 it =XBOOLE-0R4 X & ( for x be objectHIDDENM1 holds x inHIDDENR3 X implies it .FUNCT-1K1 x =HIDDENR1 [TARSKIK4 x,x ])"
sorry
  (*uniqueness*)
    show " for it1 be FunctionFUNCT-1M1 holds  for it2 be FunctionFUNCT-1M1 holds (domRELAT-1K1 it1 =XBOOLE-0R4 X & ( for x be objectHIDDENM1 holds x inHIDDENR3 X implies it1 .FUNCT-1K1 x =HIDDENR1 [TARSKIK4 x,x ])) & (domRELAT-1K1 it2 =XBOOLE-0R4 X & ( for x be objectHIDDENM1 holds x inHIDDENR3 X implies it2 .FUNCT-1K1 x =HIDDENR1 [TARSKIK4 x,x ])) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mtheorem funct_3_th_47:
" for X be setHIDDENM2 holds rngFUNCT-1K2 (deltaFUNCT-3K12 X) c=TARSKIR1 [:ZFMISC-1K2 X,X :]"
sorry

abbreviation(input) FUNCT_3K13("deltaFUNCT-3K13  _ " [228]228) where
  "deltaFUNCT-3K13 X \<equiv> deltaFUNCT-3K12 X"

mtheorem funct_3_add_6:
  mlet "X be setHIDDENM2"
"cluster deltaFUNCT-3K12 X as-term-is FunctionFUNCT-2M1-of(X,[:ZFMISC-1K2 X,X :])"
proof
(*coherence*)
  show "deltaFUNCT-3K12 X be FunctionFUNCT-2M1-of(X,[:ZFMISC-1K2 X,X :])"
sorry
qed "sorry"

mdef funct_3_def_7 ("<:FUNCT-3K14 _ , _ :>" [0,0]164 ) where
  mlet "f be FunctionFUNCT-1M1", "g be FunctionFUNCT-1M1"
"func <:FUNCT-3K14 f,g :> \<rightarrow> FunctionFUNCT-1M1 means
  \<lambda>it. domRELAT-1K1 it =XBOOLE-0R4 domRELAT-1K1 f /\\XBOOLE-0K3 domRELAT-1K1 g & ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 it implies it .FUNCT-1K1 x =HIDDENR1 [TARSKIK4 f .FUNCT-1K1 x,g .FUNCT-1K1 x ])"
proof-
  (*existence*)
    show " ex it be FunctionFUNCT-1M1 st domRELAT-1K1 it =XBOOLE-0R4 domRELAT-1K1 f /\\XBOOLE-0K3 domRELAT-1K1 g & ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 it implies it .FUNCT-1K1 x =HIDDENR1 [TARSKIK4 f .FUNCT-1K1 x,g .FUNCT-1K1 x ])"
sorry
  (*uniqueness*)
    show " for it1 be FunctionFUNCT-1M1 holds  for it2 be FunctionFUNCT-1M1 holds (domRELAT-1K1 it1 =XBOOLE-0R4 domRELAT-1K1 f /\\XBOOLE-0K3 domRELAT-1K1 g & ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 it1 implies it1 .FUNCT-1K1 x =HIDDENR1 [TARSKIK4 f .FUNCT-1K1 x,g .FUNCT-1K1 x ])) & (domRELAT-1K1 it2 =XBOOLE-0R4 domRELAT-1K1 f /\\XBOOLE-0K3 domRELAT-1K1 g & ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 it2 implies it2 .FUNCT-1K1 x =HIDDENR1 [TARSKIK4 f .FUNCT-1K1 x,g .FUNCT-1K1 x ])) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mtheorem funct_3_cl_1:
  mlet "f be emptyXBOOLE-0V1\<bar>FunctionFUNCT-1M1", "g be FunctionFUNCT-1M1"
"cluster <:FUNCT-3K14 f,g :> as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "<:FUNCT-3K14 f,g :> be emptyXBOOLE-0V1"
sorry
qed "sorry"

mtheorem funct_3_cl_2:
  mlet "f be emptyXBOOLE-0V1\<bar>FunctionFUNCT-1M1", "g be FunctionFUNCT-1M1"
"cluster <:FUNCT-3K14 g,f :> as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "<:FUNCT-3K14 g,f :> be emptyXBOOLE-0V1"
sorry
qed "sorry"

mtheorem funct_3_th_48:
" for x be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds x inTARSKIR2 domRELAT-1K1 f /\\XBOOLE-0K3 domRELAT-1K1 g implies (<:FUNCT-3K14 f,g :>).FUNCT-1K1 x =HIDDENR1 [TARSKIK4 f .FUNCT-1K1 x,g .FUNCT-1K1 x ]"
sorry

mtheorem funct_3_th_49:
" for x be setHIDDENM2 holds  for X be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds (domRELAT-1K1 f =XBOOLE-0R4 X & domRELAT-1K1 g =XBOOLE-0R4 X) & x inTARSKIR2 X implies (<:FUNCT-3K14 f,g :>).FUNCT-1K1 x =HIDDENR1 [TARSKIK4 f .FUNCT-1K1 x,g .FUNCT-1K1 x ]"
sorry

mtheorem funct_3_th_50:
" for X be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds domRELAT-1K1 f =XBOOLE-0R4 X & domRELAT-1K1 g =XBOOLE-0R4 X implies domRELAT-1K1 (<:FUNCT-3K14 f,g :>) =XBOOLE-0R4 X"
sorry

mtheorem funct_3_th_51:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds rngFUNCT-1K2 (<:FUNCT-3K14 f,g :>) c=TARSKIR1 [:ZFMISC-1K2 rngFUNCT-1K2 f,rngFUNCT-1K2 g :]"
sorry

mtheorem funct_3_th_52:
" for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds (domRELAT-1K1 f =XBOOLE-0R4 domRELAT-1K1 g & rngFUNCT-1K2 f c=TARSKIR1 Y) & rngFUNCT-1K2 g c=TARSKIR1 Z implies pr1FUNCT-3K10(Y,Z) *FUNCT-1K3 (<:FUNCT-3K14 f,g :>) =FUNCT-1R1 f & pr2FUNCT-3K11(Y,Z) *FUNCT-1K3 (<:FUNCT-3K14 f,g :>) =FUNCT-1R1 g"
sorry

mtheorem funct_3_th_53:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds <:FUNCT-3K14 pr1FUNCT-3K10(X,Y),pr2FUNCT-3K11(X,Y) :> =FUNCT-1R1 idRELAT-1K7 ([:ZFMISC-1K2 X,Y :])"
sorry

mtheorem funct_3_th_54:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds  for h be FunctionFUNCT-1M1 holds  for k be FunctionFUNCT-1M1 holds (domRELAT-1K1 f =XBOOLE-0R4 domRELAT-1K1 g & domRELAT-1K1 k =XBOOLE-0R4 domRELAT-1K1 h) & <:FUNCT-3K14 f,g :> =FUNCT-1R1 <:FUNCT-3K14 k,h :> implies f =FUNCT-1R1 k & g =FUNCT-1R1 h"
sorry

mtheorem funct_3_th_55:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds  for h be FunctionFUNCT-1M1 holds <:FUNCT-3K14 f *FUNCT-1K3 h,g *FUNCT-1K3 h :> =FUNCT-1R1 (<:FUNCT-3K14 f,g :>)*FUNCT-1K3 h"
sorry

mtheorem funct_3_th_56:
" for A be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds (<:FUNCT-3K14 f,g :>).:FUNCT-1K5 A c=TARSKIR1 [:ZFMISC-1K2 f .:FUNCT-1K5 A,g .:FUNCT-1K5 A :]"
sorry

mtheorem funct_3_th_57:
" for B be setHIDDENM2 holds  for C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds (<:FUNCT-3K14 f,g :>)\<inverse>FUNCT-1K6 ([:ZFMISC-1K2 B,C :]) =XBOOLE-0R4 f \<inverse>FUNCT-1K6 B /\\XBOOLE-0K3 g \<inverse>FUNCT-1K6 C"
sorry

mtheorem funct_3_th_58:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(X,Y) holds  for g be FunctionFUNCT-2M1-of(X,Z) holds (Y =XBOOLE-0R4 {}XBOOLE-0K1 implies X =XBOOLE-0R4 {}XBOOLE-0K1) & (Z =XBOOLE-0R4 {}XBOOLE-0K1 implies X =XBOOLE-0R4 {}XBOOLE-0K1) implies <:FUNCT-3K14 f,g :> be FunctionFUNCT-2M1-of(X,[:ZFMISC-1K2 Y,Z :])"
sorry

syntax FUNCT_3K15 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" ("<:FUNCT-3K15\<^bsub>'( _ , _ , _ ')\<^esub> _ , _ :>" [0,0,0,0,0]164)
translations "<:FUNCT-3K15\<^bsub>(X,D1,D2)\<^esub> f1,f2 :>" \<rightharpoonup> "<:FUNCT-3K14 f1,f2 :>"

mtheorem funct_3_add_7:
  mlet "X be setHIDDENM2", "D1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "D2 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "f1 be FunctionFUNCT-2M1-of(X,D1)", "f2 be FunctionFUNCT-2M1-of(X,D2)"
"cluster <:FUNCT-3K14 f1,f2 :> as-term-is FunctionFUNCT-2M1-of(X,[:ZFMISC-1K2 D1,D2 :])"
proof
(*coherence*)
  show "<:FUNCT-3K14 f1,f2 :> be FunctionFUNCT-2M1-of(X,[:ZFMISC-1K2 D1,D2 :])"
    using funct_3_th_58 sorry
qed "sorry"

mtheorem funct_3_th_59:
" for C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D2 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for f1 be FunctionFUNCT-2M1-of(C,D1) holds  for f2 be FunctionFUNCT-2M1-of(C,D2) holds  for c be ElementSUBSET-1M1-of C holds (<:FUNCT-3K15\<^bsub>(C,D1,D2)\<^esub> f1,f2 :>).FUNCT-2K3\<^bsub>(C,[:ZFMISC-1K2 D1,D2 :])\<^esub> c =HIDDENR1 [TARSKIK4 f1 .FUNCT-2K3\<^bsub>(C,D1)\<^esub> c,f2 .FUNCT-2K3\<^bsub>(C,D2)\<^esub> c ]"
sorry

mtheorem funct_3_th_60:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(X,Y) holds  for g be FunctionFUNCT-2M1-of(X,Z) holds rngFUNCT-1K2 (<:FUNCT-3K14 f,g :>) c=TARSKIR1 [:ZFMISC-1K2 Y,Z :]"
sorry

mtheorem funct_3_th_61:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(X,Y) holds  for g be FunctionFUNCT-2M1-of(X,Z) holds (Y =XBOOLE-0R4 {}XBOOLE-0K1 implies X =XBOOLE-0R4 {}XBOOLE-0K1) & (Z =XBOOLE-0R4 {}XBOOLE-0K1 implies X =XBOOLE-0R4 {}XBOOLE-0K1) implies pr1FUNCT-3K10(Y,Z) *FUNCT-1K3 (<:FUNCT-3K14 f,g :>) =FUNCT-1R1 f & pr2FUNCT-3K11(Y,Z) *FUNCT-1K3 (<:FUNCT-3K14 f,g :>) =FUNCT-1R1 g"
sorry

mtheorem funct_3_th_62:
" for X be setHIDDENM2 holds  for D1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D2 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(X,D1) holds  for g be FunctionFUNCT-2M1-of(X,D2) holds pr1FUNCT-3K10(D1,D2) *FUNCT-1K3 (<:FUNCT-3K15\<^bsub>(X,D1,D2)\<^esub> f,g :>) =FUNCT-1R1 f & pr2FUNCT-3K11(D1,D2) *FUNCT-1K3 (<:FUNCT-3K15\<^bsub>(X,D1,D2)\<^esub> f,g :>) =FUNCT-1R1 g"
  using funct_3_th_61 sorry

mtheorem funct_3_th_63:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds  for f1 be FunctionFUNCT-2M1-of(X,Y) holds  for f2 be FunctionFUNCT-2M1-of(X,Y) holds  for g1 be FunctionFUNCT-2M1-of(X,Z) holds  for g2 be FunctionFUNCT-2M1-of(X,Z) holds ((Y =XBOOLE-0R4 {}XBOOLE-0K1 implies X =XBOOLE-0R4 {}XBOOLE-0K1) & (Z =XBOOLE-0R4 {}XBOOLE-0K1 implies X =XBOOLE-0R4 {}XBOOLE-0K1)) & <:FUNCT-3K14 f1,g1 :> =FUNCT-1R1 <:FUNCT-3K14 f2,g2 :> implies f1 =FUNCT-2R2\<^bsub>(X,Y)\<^esub> f2 & g1 =FUNCT-2R2\<^bsub>(X,Z)\<^esub> g2"
sorry

mtheorem funct_3_th_64:
" for X be setHIDDENM2 holds  for D1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D2 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for f1 be FunctionFUNCT-2M1-of(X,D1) holds  for f2 be FunctionFUNCT-2M1-of(X,D1) holds  for g1 be FunctionFUNCT-2M1-of(X,D2) holds  for g2 be FunctionFUNCT-2M1-of(X,D2) holds <:FUNCT-3K15\<^bsub>(X,D1,D2)\<^esub> f1,g1 :> =FUNCT-2R2\<^bsub>(X,[:ZFMISC-1K2 D1,D2 :])\<^esub> <:FUNCT-3K15\<^bsub>(X,D1,D2)\<^esub> f2,g2 :> implies f1 =FUNCT-2R2\<^bsub>(X,D1)\<^esub> f2 & g1 =FUNCT-2R2\<^bsub>(X,D2)\<^esub> g2"
sorry

mdef funct_3_def_8 ("[:FUNCT-3K16 _ , _ :]" [0,0]164 ) where
  mlet "f be FunctionFUNCT-1M1", "g be FunctionFUNCT-1M1"
"func [:FUNCT-3K16 f,g :] \<rightarrow> FunctionFUNCT-1M1 means
  \<lambda>it. domRELAT-1K1 it =XBOOLE-0R4 [:ZFMISC-1K2 domRELAT-1K1 f,domRELAT-1K1 g :] & ( for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 f & y inHIDDENR3 domRELAT-1K1 g implies it .BINOP-1K1(x,y) =HIDDENR1 [TARSKIK4 f .FUNCT-1K1 x,g .FUNCT-1K1 y ])"
proof-
  (*existence*)
    show " ex it be FunctionFUNCT-1M1 st domRELAT-1K1 it =XBOOLE-0R4 [:ZFMISC-1K2 domRELAT-1K1 f,domRELAT-1K1 g :] & ( for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 f & y inHIDDENR3 domRELAT-1K1 g implies it .BINOP-1K1(x,y) =HIDDENR1 [TARSKIK4 f .FUNCT-1K1 x,g .FUNCT-1K1 y ])"
sorry
  (*uniqueness*)
    show " for it1 be FunctionFUNCT-1M1 holds  for it2 be FunctionFUNCT-1M1 holds (domRELAT-1K1 it1 =XBOOLE-0R4 [:ZFMISC-1K2 domRELAT-1K1 f,domRELAT-1K1 g :] & ( for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 f & y inHIDDENR3 domRELAT-1K1 g implies it1 .BINOP-1K1(x,y) =HIDDENR1 [TARSKIK4 f .FUNCT-1K1 x,g .FUNCT-1K1 y ])) & (domRELAT-1K1 it2 =XBOOLE-0R4 [:ZFMISC-1K2 domRELAT-1K1 f,domRELAT-1K1 g :] & ( for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 f & y inHIDDENR3 domRELAT-1K1 g implies it2 .BINOP-1K1(x,y) =HIDDENR1 [TARSKIK4 f .FUNCT-1K1 x,g .FUNCT-1K1 y ])) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mtheorem funct_3_th_65:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds  for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds [TARSKIK4 x,y ] inHIDDENR3 [:ZFMISC-1K2 domRELAT-1K1 f,domRELAT-1K1 g :] implies ([:FUNCT-3K16 f,g :]).BINOP-1K1(x,y) =HIDDENR1 [TARSKIK4 f .FUNCT-1K1 x,g .FUNCT-1K1 y ]"
sorry

mtheorem funct_3_th_66:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds [:FUNCT-3K16 f,g :] =FUNCT-1R1 <:FUNCT-3K14 f *FUNCT-1K3 pr1FUNCT-3K10(domRELAT-1K1 f,domRELAT-1K1 g),g *FUNCT-1K3 pr2FUNCT-3K11(domRELAT-1K1 f,domRELAT-1K1 g) :>"
sorry

mtheorem funct_3_th_67:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds rngFUNCT-1K2 ([:FUNCT-3K16 f,g :]) =XBOOLE-0R4 [:ZFMISC-1K2 rngFUNCT-1K2 f,rngFUNCT-1K2 g :]"
sorry

mtheorem funct_3_th_68:
" for X be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds domRELAT-1K1 f =XBOOLE-0R4 X & domRELAT-1K1 g =XBOOLE-0R4 X implies <:FUNCT-3K14 f,g :> =FUNCT-1R1 ([:FUNCT-3K16 f,g :])*FUNCT-1K3 deltaFUNCT-3K13 X"
sorry

mtheorem funct_3_th_69:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds [:FUNCT-3K16 idRELAT-1K7 X,idRELAT-1K7 Y :] =FUNCT-1R1 idRELAT-1K7 ([:ZFMISC-1K2 X,Y :])"
sorry

mtheorem funct_3_th_70:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds  for h be FunctionFUNCT-1M1 holds  for k be FunctionFUNCT-1M1 holds ([:FUNCT-3K16 f,h :])*FUNCT-1K3 (<:FUNCT-3K14 g,k :>) =FUNCT-1R1 <:FUNCT-3K14 f *FUNCT-1K3 g,h *FUNCT-1K3 k :>"
sorry

mtheorem funct_3_th_71:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds  for h be FunctionFUNCT-1M1 holds  for k be FunctionFUNCT-1M1 holds ([:FUNCT-3K16 f,h :])*FUNCT-1K3 ([:FUNCT-3K16 g,k :]) =FUNCT-1R1 [:FUNCT-3K16 f *FUNCT-1K3 g,h *FUNCT-1K3 k :]"
sorry

mtheorem funct_3_th_72:
" for A be setHIDDENM2 holds  for B be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds ([:FUNCT-3K16 f,g :]).:FUNCT-1K5 ([:ZFMISC-1K2 B,A :]) =XBOOLE-0R4 [:ZFMISC-1K2 f .:FUNCT-1K5 B,g .:FUNCT-1K5 A :]"
sorry

mtheorem funct_3_th_73:
" for A be setHIDDENM2 holds  for B be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds ([:FUNCT-3K16 f,g :])\<inverse>FUNCT-1K6 ([:ZFMISC-1K2 B,A :]) =XBOOLE-0R4 [:ZFMISC-1K2 f \<inverse>FUNCT-1K6 B,g \<inverse>FUNCT-1K6 A :]"
sorry

mtheorem funct_3_th_74:
" for V be setHIDDENM2 holds  for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(X,Y) holds  for g be FunctionFUNCT-2M1-of(V,Z) holds [:FUNCT-3K16 f,g :] be FunctionFUNCT-2M1-of([:ZFMISC-1K2 X,V :],[:ZFMISC-1K2 Y,Z :])"
sorry

syntax FUNCT_3K17 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" ("[:FUNCT-3K17\<^bsub>'( _ , _ , _ , _ ')\<^esub> _ , _ :]" [0,0,0,0,0,0]164)
translations "[:FUNCT-3K17\<^bsub>(X1,X2,Y1,Y2)\<^esub> f1,f2 :]" \<rightharpoonup> "[:FUNCT-3K16 f1,f2 :]"

mtheorem funct_3_add_8:
  mlet "X1 be setHIDDENM2", "X2 be setHIDDENM2", "Y1 be setHIDDENM2", "Y2 be setHIDDENM2", "f1 be FunctionFUNCT-2M1-of(X1,Y1)", "f2 be FunctionFUNCT-2M1-of(X2,Y2)"
"cluster [:FUNCT-3K16 f1,f2 :] as-term-is FunctionFUNCT-2M1-of([:ZFMISC-1K2 X1,X2 :],[:ZFMISC-1K2 Y1,Y2 :])"
proof
(*coherence*)
  show "[:FUNCT-3K16 f1,f2 :] be FunctionFUNCT-2M1-of([:ZFMISC-1K2 X1,X2 :],[:ZFMISC-1K2 Y1,Y2 :])"
    using funct_3_th_74 sorry
qed "sorry"

mtheorem funct_3_th_75:
" for C1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for C2 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D2 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for f1 be FunctionFUNCT-2M1-of(C1,D1) holds  for f2 be FunctionFUNCT-2M1-of(C2,D2) holds  for c1 be ElementSUBSET-1M1-of C1 holds  for c2 be ElementSUBSET-1M1-of C2 holds ([:FUNCT-3K17\<^bsub>(C1,C2,D1,D2)\<^esub> f1,f2 :]).BINOP-1K2\<^bsub>(C1,C2,[:ZFMISC-1K2 D1,D2 :])\<^esub>(c1,c2) =HIDDENR1 [TARSKIK4 f1 .FUNCT-2K3\<^bsub>(C1,D1)\<^esub> c1,f2 .FUNCT-2K3\<^bsub>(C2,D2)\<^esub> c2 ]"
sorry

mtheorem funct_3_th_76:
" for X1 be setHIDDENM2 holds  for X2 be setHIDDENM2 holds  for Y1 be setHIDDENM2 holds  for Y2 be setHIDDENM2 holds  for f1 be FunctionFUNCT-2M1-of(X1,Y1) holds  for f2 be FunctionFUNCT-2M1-of(X2,Y2) holds (Y1 =XBOOLE-0R4 {}XBOOLE-0K1 implies X1 =XBOOLE-0R4 {}XBOOLE-0K1) & (Y2 =XBOOLE-0R4 {}XBOOLE-0K1 implies X2 =XBOOLE-0R4 {}XBOOLE-0K1) implies [:FUNCT-3K17\<^bsub>(X1,X2,Y1,Y2)\<^esub> f1,f2 :] =FUNCT-1R1 <:FUNCT-3K14 f1 *FUNCT-1K3 pr1FUNCT-3K10(X1,X2),f2 *FUNCT-1K3 pr2FUNCT-3K11(X1,X2) :>"
sorry

mtheorem funct_3_th_77:
" for X1 be setHIDDENM2 holds  for X2 be setHIDDENM2 holds  for D1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D2 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for f1 be FunctionFUNCT-2M1-of(X1,D1) holds  for f2 be FunctionFUNCT-2M1-of(X2,D2) holds [:FUNCT-3K17\<^bsub>(X1,X2,D1,D2)\<^esub> f1,f2 :] =FUNCT-1R1 <:FUNCT-3K14 f1 *FUNCT-1K3 pr1FUNCT-3K10(X1,X2),f2 *FUNCT-1K3 pr2FUNCT-3K11(X1,X2) :>"
sorry

mtheorem funct_3_th_78:
" for X be setHIDDENM2 holds  for Y1 be setHIDDENM2 holds  for Y2 be setHIDDENM2 holds  for f1 be FunctionFUNCT-2M1-of(X,Y1) holds  for f2 be FunctionFUNCT-2M1-of(X,Y2) holds <:FUNCT-3K14 f1,f2 :> =FUNCT-1R1 ([:FUNCT-3K17\<^bsub>(X,X,Y1,Y2)\<^esub> f1,f2 :])*FUNCT-1K3 deltaFUNCT-3K13 X"
sorry

(*begin*)
mtheorem funct_3_th_79:
" for f be FunctionFUNCT-1M1 holds pr1FUNCT-3K10(domRELAT-1K1 f,rngFUNCT-1K2 f) .:FUNCT-1K5 f =XBOOLE-0R4 domRELAT-1K1 f"
sorry

mtheorem funct_3_th_80:
" for A be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for B be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(A,[:ZFMISC-1K2 B,C :]) holds  for g be FunctionFUNCT-2M1-of(A,[:ZFMISC-1K2 B,C :]) holds pr1FUNCT-3K10(B,C) *FUNCT-1K3 f =FUNCT-1R1 pr1FUNCT-3K10(B,C) *FUNCT-1K3 g & pr2FUNCT-3K11(B,C) *FUNCT-1K3 f =FUNCT-1R1 pr2FUNCT-3K11(B,C) *FUNCT-1K3 g implies f =FUNCT-2R2\<^bsub>(A,[:ZFMISC-1K2 B,C :])\<^esub> g"
sorry

mtheorem funct_3_cl_3:
  mlet "F be one-to-oneFUNCT-1V2\<bar>FunctionFUNCT-1M1", "G be one-to-oneFUNCT-1V2\<bar>FunctionFUNCT-1M1"
"cluster [:FUNCT-3K16 F,G :] as-term-is one-to-oneFUNCT-1V2"
proof
(*coherence*)
  show "[:FUNCT-3K16 F,G :] be one-to-oneFUNCT-1V2"
sorry
qed "sorry"

mtheorem funct_3_cl_4:
  mlet "A be setHIDDENM2"
"cluster idempotentBINOP-1V3\<^bsub>(A)\<^esub> for BinOpBINOP-1M2-of A"
proof
(*existence*)
  show " ex it be BinOpBINOP-1M2-of A st it be idempotentBINOP-1V3\<^bsub>(A)\<^esub>"
sorry
qed "sorry"

mtheorem funct_3_reduce_1:
  mlet "A be setHIDDENM2", "b be idempotentBINOP-1V3\<^bsub>(A)\<^esub>\<bar>BinOpBINOP-1M2-of A", "a be ElementSUBSET-1M1-of A"
"reduce b .BINOP-1K4\<^bsub>(A)\<^esub>(a,a) to a"
proof
(*reducibility*)
  show "b .BINOP-1K4\<^bsub>(A)\<^esub>(a,a) =HIDDENR1 a"
    using binop_1_def_4 sorry
qed "sorry"

reserve A1, A2, B1, B2 for " non emptyXBOOLE-0V1\<bar>setHIDDENM2"
reserve f for "FunctionFUNCT-2M1-of(A1,B1)"
reserve g for "FunctionFUNCT-2M1-of(A2,B2)"
reserve Y1 for " non emptyXBOOLE-0V1\<bar>SubsetSUBSET-1M2-of A1"
reserve Y2 for " non emptyXBOOLE-0V1\<bar>SubsetSUBSET-1M2-of A2"
syntax FUNCT_3K18 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ |FUNCT-3K18\<^bsub>'( _ , _ ')\<^esub>  _ " [200,0,0,200]200)
translations "f |FUNCT-3K18\<^bsub>(A1,B1)\<^esub> Y1" \<rightharpoonup> "f |RELAT-1K8 Y1"

mtheorem funct_3_add_9:
  mlet "A1 be setHIDDENM2", "B1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "f be FunctionFUNCT-2M1-of(A1,B1)", "Y1 be SubsetSUBSET-1M2-of A1"
"cluster f |RELAT-1K8 Y1 as-term-is FunctionFUNCT-2M1-of(Y1,B1)"
proof
(*coherence*)
  show "f |RELAT-1K8 Y1 be FunctionFUNCT-2M1-of(Y1,B1)"
    using funct_2_th_32 sorry
qed "sorry"

mtheorem funct_3_th_81:
" for A1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for A2 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for B1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for B2 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(A1,B1) holds  for g be FunctionFUNCT-2M1-of(A2,B2) holds  for Y1 be  non emptyXBOOLE-0V1\<bar>SubsetSUBSET-1M2-of A1 holds  for Y2 be  non emptyXBOOLE-0V1\<bar>SubsetSUBSET-1M2-of A2 holds ([:FUNCT-3K17\<^bsub>(A1,A2,B1,B2)\<^esub> f,g :])|FUNCT-3K18\<^bsub>([:ZFMISC-1K2 A1,A2 :],[:ZFMISC-1K2 B1,B2 :])\<^esub> ([:MCART-1K8\<^bsub>(A1,A2)\<^esub> Y1,Y2 :]) =BINOP-1R13\<^bsub>(Y1,Y2,[:ZFMISC-1K2 B1,B2 :])\<^esub> [:FUNCT-3K17\<^bsub>(Y1,Y2,B1,B2)\<^esub> f |FUNCT-3K18\<^bsub>(A1,B1)\<^esub> Y1,g |FUNCT-3K18\<^bsub>(A2,B2)\<^esub> Y2 :]"
sorry

end
