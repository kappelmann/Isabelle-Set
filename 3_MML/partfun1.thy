theory partfun1
  imports relat_2 relset_1 grfunc_1
begin
(*begin*)
reserve x, x1, x2, y, y9, y1, y2, z, z1, z2 for "objectHIDDENM1"
reserve P, X, X1, X2, Y, Y1, Y2, V, Z for "setHIDDENM2"
mtheorem partfun1_th_1:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 f /\\XBOOLE-0K3 domRELAT-1K1 g implies f .FUNCT-1K1 x =XBOOLE-0R4 g .FUNCT-1K1 x) implies f \\/XBOOLE-0K2 g be FunctionFUNCT-1M1"
sorry

mtheorem partfun1_th_2:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds  for h be FunctionFUNCT-1M1 holds f \\/XBOOLE-0K2 g =RELAT-1R1 h implies ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 f /\\XBOOLE-0K3 domRELAT-1K1 g implies f .FUNCT-1K1 x =XBOOLE-0R4 g .FUNCT-1K1 x)"
sorry

theorem partfun1_sch_1:
  fixes Af0 Ff1 Gf1 Cp1 
  assumes
[ty]: "Af0 be setHIDDENM2" and
  [ty_func]: "\<And> x1. x1 be objectHIDDENM1 \<Longrightarrow> Ff1(x1) be objectHIDDENM1" and
  [ty_func]: "\<And> x1. x1 be objectHIDDENM1 \<Longrightarrow> Gf1(x1) be objectHIDDENM1"
  shows " ex f be FunctionFUNCT-1M1 st domRELAT-1K1 f =XBOOLE-0R4 Af0 & ( for x be objectHIDDENM1 holds x inHIDDENR3 Af0 implies (Cp1(x) implies f .FUNCT-1K1 x =HIDDENR1 Ff1(x)) & ( not Cp1(x) implies f .FUNCT-1K1 x =HIDDENR1 Gf1(x)))"
sorry

mlemma partfun1_lm_1:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  ex E be setHIDDENM2 st domRELAT-1K1 E c=RELAT-1R2 X & rngFUNCT-1K2 E c=RELAT-1R2 Y"
sorry

mtheorem partfun1_cl_1:
  mlet "X be setHIDDENM2", "Y be setHIDDENM2"
"cluster Function-likeFUNCT-1V1 for RelationRELSET-1M1-of(X,Y)"
proof
(*existence*)
  show " ex it be RelationRELSET-1M1-of(X,Y) st it be Function-likeFUNCT-1V1"
sorry
qed "sorry"

abbreviation(input) PARTFUN1M1("PartFuncPARTFUN1M1-of'( _ , _ ')" [0,0]70) where
  "PartFuncPARTFUN1M1-of(X,Y) \<equiv> Function-likeFUNCT-1V1\<bar>RelationRELSET-1M1-of(X,Y)"

mtheorem partfun1_th_3:
" for y be objectHIDDENM1 holds  for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be PartFuncPARTFUN1M1-of(X,Y) holds y inHIDDENR3 rngFUNCT-1K2 f implies ( ex x be ElementSUBSET-1M1-of X st x inTARSKIR2 domRELSET-1K1\<^bsub>(X)\<^esub> f & y =HIDDENR1 f .FUNCT-1K1 x)"
sorry

mtheorem partfun1_th_4:
" for x be objectHIDDENM1 holds  for Y be setHIDDENM2 holds  for f be Y -valuedRELAT-1V5\<bar>FunctionFUNCT-1M1 holds x inHIDDENR3 domRELAT-1K1 f implies f .FUNCT-1K1 x inTARSKIR2 Y"
sorry

mtheorem partfun1_th_5:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f1 be PartFuncPARTFUN1M1-of(X,Y) holds  for f2 be PartFuncPARTFUN1M1-of(X,Y) holds domRELSET-1K1\<^bsub>(X)\<^esub> f1 =XBOOLE-0R4 domRELSET-1K1\<^bsub>(X)\<^esub> f2 & ( for x be ElementSUBSET-1M1-of X holds x inTARSKIR2 domRELSET-1K1\<^bsub>(X)\<^esub> f1 implies f1 .FUNCT-1K1 x =XBOOLE-0R4 f2 .FUNCT-1K1 x) implies f1 =FUNCT-1R1 f2"
   sorry

theorem partfun1_sch_2:
  fixes Xf0 Yf0 Pp2 
  assumes
[ty]: "Xf0 be setHIDDENM2" and
  [ty]: "Yf0 be setHIDDENM2" and
   A1: " for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds x inHIDDENR3 Xf0 & Pp2(x,y) implies y inHIDDENR3 Yf0" and
   A2: " for x be objectHIDDENM1 holds  for y1 be objectHIDDENM1 holds  for y2 be objectHIDDENM1 holds (x inHIDDENR3 Xf0 & Pp2(x,y1)) & Pp2(x,y2) implies y1 =HIDDENR1 y2"
  shows " ex f be PartFuncPARTFUN1M1-of(Xf0,Yf0) st ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELSET-1K1\<^bsub>(Xf0)\<^esub> f iff x inHIDDENR3 Xf0 & ( ex y be objectHIDDENM1 st Pp2(x,y))) & ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELSET-1K1\<^bsub>(Xf0)\<^esub> f implies Pp2(x,f .FUNCT-1K1 x))"
sorry

theorem partfun1_sch_3:
  fixes Xf0 Yf0 Ff1 Pp1 
  assumes
[ty]: "Xf0 be setHIDDENM2" and
  [ty]: "Yf0 be setHIDDENM2" and
  [ty_func]: "\<And> x1. x1 be objectHIDDENM1 \<Longrightarrow> Ff1(x1) be objectHIDDENM1" and
   A1: " for x be objectHIDDENM1 holds Pp1(x) implies Ff1(x) inHIDDENR3 Yf0"
  shows " ex f be PartFuncPARTFUN1M1-of(Xf0,Yf0) st ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELSET-1K1\<^bsub>(Xf0)\<^esub> f iff x inHIDDENR3 Xf0 & Pp1(x)) & ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELSET-1K1\<^bsub>(Xf0)\<^esub> f implies f .FUNCT-1K1 x =HIDDENR1 Ff1(x))"
sorry

syntax PARTFUN1K1 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ *PARTFUN1K1\<^bsub>'( _ , _ , _ , _ ')\<^esub>  _ " [164,0,0,0,0,164]164)
translations "g *PARTFUN1K1\<^bsub>(X,Y,V,Z)\<^esub> f" \<rightharpoonup> "f *RELAT-1K6 g"

mtheorem partfun1_add_1:
  mlet "X be setHIDDENM2", "Y be setHIDDENM2", "V be setHIDDENM2", "Z be setHIDDENM2", "f be PartFuncPARTFUN1M1-of(X,Y)", "g be PartFuncPARTFUN1M1-of(V,Z)"
"cluster f *RELAT-1K6 g as-term-is PartFuncPARTFUN1M1-of(X,Z)"
proof
(*coherence*)
  show "f *RELAT-1K6 g be PartFuncPARTFUN1M1-of(X,Z)"
sorry
qed "sorry"

mtheorem partfun1_th_6:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be RelationRELSET-1M1-of(X,Y) holds idRELAT-1K7 X *RELAT-1K6 f =RELAT-1R1 f"
sorry

mtheorem partfun1_th_7:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be RelationRELSET-1M1-of(X,Y) holds f *RELAT-1K6 idRELAT-1K7 Y =RELAT-1R1 f"
sorry

mtheorem partfun1_th_8:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be PartFuncPARTFUN1M1-of(X,Y) holds ( for x1 be ElementSUBSET-1M1-of X holds  for x2 be ElementSUBSET-1M1-of X holds (x1 inTARSKIR2 domRELSET-1K1\<^bsub>(X)\<^esub> f & x2 inTARSKIR2 domRELSET-1K1\<^bsub>(X)\<^esub> f) & f .FUNCT-1K1 x1 =XBOOLE-0R4 f .FUNCT-1K1 x2 implies x1 =XBOOLE-0R4 x2) implies f be one-to-oneFUNCT-1V2"
   sorry

mtheorem partfun1_th_9:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be PartFuncPARTFUN1M1-of(X,Y) holds f be one-to-oneFUNCT-1V2 implies f \<inverse>FUNCT-1K4 be PartFuncPARTFUN1M1-of(Y,X)"
sorry

mtheorem partfun1_th_10:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds  for f be PartFuncPARTFUN1M1-of(X,Y) holds f |RELSET-1K5\<^bsub>(X,Y)\<^esub> Z be PartFuncPARTFUN1M1-of(Z,Y)"
sorry

mtheorem partfun1_th_11:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds  for f be PartFuncPARTFUN1M1-of(X,Y) holds f |RELSET-1K5\<^bsub>(X,Y)\<^esub> Z be PartFuncPARTFUN1M1-of(X,Y)"
   sorry

syntax PARTFUN1K2 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ |PARTFUN1K2\<^bsub>'( _ , _ ')\<^esub>  _ " [200,0,0,200]200)
translations "f |PARTFUN1K2\<^bsub>(X,Y)\<^esub> Z" \<rightharpoonup> "f |RELAT-1K8 Z"

mtheorem partfun1_add_2:
  mlet "X be setHIDDENM2", "Y be setHIDDENM2", "f be PartFuncPARTFUN1M1-of(X,Y)", "Z be setHIDDENM2"
"cluster f |RELAT-1K8 Z as-term-is PartFuncPARTFUN1M1-of(X,Y)"
proof
(*coherence*)
  show "f |RELAT-1K8 Z be PartFuncPARTFUN1M1-of(X,Y)"
    using partfun1_th_11 sorry
qed "sorry"

mtheorem partfun1_th_12:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds  for f be PartFuncPARTFUN1M1-of(X,Y) holds Z |`RELSET-1K6\<^bsub>(X,Y)\<^esub> f be PartFuncPARTFUN1M1-of(X,Z)"
sorry

mtheorem partfun1_th_13:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds  for f be PartFuncPARTFUN1M1-of(X,Y) holds Z |`RELSET-1K6\<^bsub>(X,Y)\<^esub> f be PartFuncPARTFUN1M1-of(X,Y)"
   sorry

mtheorem partfun1_th_14:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds (Y |`RELAT-1K9 f)|RELAT-1K8 X be PartFuncPARTFUN1M1-of(X,Y)"
sorry

mtheorem partfun1_th_15:
" for y be objectHIDDENM1 holds  for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be PartFuncPARTFUN1M1-of(X,Y) holds y inHIDDENR3 f .:FUNCT-1K5 X implies ( ex x be ElementSUBSET-1M1-of X st x inTARSKIR2 domRELSET-1K1\<^bsub>(X)\<^esub> f & y =HIDDENR1 f .FUNCT-1K1 x)"
sorry

mtheorem partfun1_th_16:
" for x be objectHIDDENM1 holds  for Y be setHIDDENM2 holds  for f be PartFuncPARTFUN1M1-of({TARSKIK1 x},Y) holds rngFUNCT-1K2 f c=TARSKIR1 {TARSKIK1 f .FUNCT-1K1 x }"
sorry

mtheorem partfun1_th_17:
" for x be objectHIDDENM1 holds  for Y be setHIDDENM2 holds  for f be PartFuncPARTFUN1M1-of({TARSKIK1 x},Y) holds f be one-to-oneFUNCT-1V2"
sorry

mtheorem partfun1_th_18:
" for x be objectHIDDENM1 holds  for P be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be PartFuncPARTFUN1M1-of({TARSKIK1 x},Y) holds f .:FUNCT-1K5 P c=TARSKIR1 {TARSKIK1 f .FUNCT-1K1 x }"
sorry

mtheorem partfun1_th_19:
" for x be objectHIDDENM1 holds  for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds (domRELAT-1K1 f =XBOOLE-0R4 {TARSKIK1 x} & x inHIDDENR3 X) & f .FUNCT-1K1 x inTARSKIR2 Y implies f be PartFuncPARTFUN1M1-of(X,Y)"
sorry

mtheorem partfun1_th_20:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for X be setHIDDENM2 holds  for f be PartFuncPARTFUN1M1-of(X,{TARSKIK1 y}) holds x inHIDDENR3 domRELSET-1K1\<^bsub>(X)\<^esub> f implies f .FUNCT-1K1 x =HIDDENR1 y"
sorry

mtheorem partfun1_th_21:
" for y be objectHIDDENM1 holds  for X be setHIDDENM2 holds  for f1 be PartFuncPARTFUN1M1-of(X,{TARSKIK1 y}) holds  for f2 be PartFuncPARTFUN1M1-of(X,{TARSKIK1 y}) holds domRELSET-1K1\<^bsub>(X)\<^esub> f1 =XBOOLE-0R4 domRELSET-1K1\<^bsub>(X)\<^esub> f2 implies f1 =FUNCT-1R1 f2"
sorry

mdef partfun1_def_1 ("<:PARTFUN1K3 _ , _ , _ :>" [0,0,0]164 ) where
  mlet "f be FunctionFUNCT-1M1", "X be setHIDDENM2", "Y be setHIDDENM2"
"func <:PARTFUN1K3 f,X,Y :> \<rightarrow> PartFuncPARTFUN1M1-of(X,Y) equals
  (Y |`RELAT-1K9 f)|RELAT-1K8 X"
proof-
  (*coherence*)
    show "(Y |`RELAT-1K9 f)|RELAT-1K8 X be PartFuncPARTFUN1M1-of(X,Y)"
      using partfun1_th_14 sorry
qed "sorry"

mtheorem partfun1_th_22:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds <:PARTFUN1K3 f,X,Y :> c=RELSET-1R1\<^bsub>(X,Y)\<^esub> f"
sorry

mtheorem partfun1_th_23:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds domRELSET-1K1\<^bsub>(X)\<^esub> (<:PARTFUN1K3 f,X,Y :>) c=TARSKIR1 domRELAT-1K1 f & rngFUNCT-1K2 (<:PARTFUN1K3 f,X,Y :>) c=TARSKIR1 rngFUNCT-1K2 f"
sorry

mtheorem partfun1_th_24:
" for x be objectHIDDENM1 holds  for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds x inHIDDENR3 domRELSET-1K1\<^bsub>(X)\<^esub> (<:PARTFUN1K3 f,X,Y :>) iff (x inHIDDENR3 domRELAT-1K1 f & x inHIDDENR3 X) & f .FUNCT-1K1 x inTARSKIR2 Y"
sorry

mtheorem partfun1_th_25:
" for x be objectHIDDENM1 holds  for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds (x inHIDDENR3 domRELAT-1K1 f & x inHIDDENR3 X) & f .FUNCT-1K1 x inTARSKIR2 Y implies (<:PARTFUN1K3 f,X,Y :>).FUNCT-1K1 x =XBOOLE-0R4 f .FUNCT-1K1 x"
sorry

mtheorem partfun1_th_26:
" for x be objectHIDDENM1 holds  for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds x inHIDDENR3 domRELSET-1K1\<^bsub>(X)\<^esub> (<:PARTFUN1K3 f,X,Y :>) implies (<:PARTFUN1K3 f,X,Y :>).FUNCT-1K1 x =XBOOLE-0R4 f .FUNCT-1K1 x"
sorry

mtheorem partfun1_th_27:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds f c=RELAT-1R2 g implies <:PARTFUN1K3 f,X,Y :> c=RELSET-1R1\<^bsub>(X,Y)\<^esub> <:PARTFUN1K3 g,X,Y :>"
sorry

mtheorem partfun1_th_28:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds Z c=TARSKIR1 X implies <:PARTFUN1K3 f,Z,Y :> c=RELSET-1R1\<^bsub>(Z,Y)\<^esub> <:PARTFUN1K3 f,X,Y :>"
sorry

mtheorem partfun1_th_29:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds Z c=TARSKIR1 Y implies <:PARTFUN1K3 f,X,Z :> c=RELSET-1R1\<^bsub>(X,Z)\<^esub> <:PARTFUN1K3 f,X,Y :>"
sorry

mtheorem partfun1_th_30:
" for X1 be setHIDDENM2 holds  for X2 be setHIDDENM2 holds  for Y1 be setHIDDENM2 holds  for Y2 be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds X1 c=TARSKIR1 X2 & Y1 c=TARSKIR1 Y2 implies <:PARTFUN1K3 f,X1,Y1 :> c=RELSET-1R1\<^bsub>(X1,Y1)\<^esub> <:PARTFUN1K3 f,X2,Y2 :>"
sorry

mtheorem partfun1_th_31:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds domRELAT-1K1 f c=TARSKIR1 X & rngFUNCT-1K2 f c=TARSKIR1 Y implies f =FUNCT-1R1 <:PARTFUN1K3 f,X,Y :>"
sorry

mtheorem partfun1_th_32:
" for f be FunctionFUNCT-1M1 holds f =FUNCT-1R1 <:PARTFUN1K3 f,domRELAT-1K1 f,rngFUNCT-1K2 f :>"
   sorry

mtheorem partfun1_th_33:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be PartFuncPARTFUN1M1-of(X,Y) holds <:PARTFUN1K3 f,X,Y :> =FUNCT-1R1 f"
   sorry

mtheorem partfun1_th_34:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds <:PARTFUN1K3 {}XBOOLE-0K1,X,Y :> =FUNCT-1R1 {}XBOOLE-0K1"
sorry

mtheorem partfun1_th_35:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds (<:PARTFUN1K3 g,Y,Z :>)*PARTFUN1K1\<^bsub>(X,Y,Y,Z)\<^esub> (<:PARTFUN1K3 f,X,Y :>) c=RELSET-1R1\<^bsub>(X,Z)\<^esub> <:PARTFUN1K3 g *FUNCT-1K3 f,X,Z :>"
sorry

mtheorem partfun1_th_36:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds rngFUNCT-1K2 f /\\XBOOLE-0K3 domRELAT-1K1 g c=TARSKIR1 Y implies (<:PARTFUN1K3 g,Y,Z :>)*PARTFUN1K1\<^bsub>(X,Y,Y,Z)\<^esub> (<:PARTFUN1K3 f,X,Y :>) =FUNCT-1R1 <:PARTFUN1K3 g *FUNCT-1K3 f,X,Z :>"
sorry

mtheorem partfun1_th_37:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds f be one-to-oneFUNCT-1V2 implies <:PARTFUN1K3 f,X,Y :> be one-to-oneFUNCT-1V2"
sorry

mtheorem partfun1_th_38:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds f be one-to-oneFUNCT-1V2 implies (<:PARTFUN1K3 f,X,Y :>)\<inverse>FUNCT-1K4 =FUNCT-1R1 <:PARTFUN1K3 f \<inverse>FUNCT-1K4,Y,X :>"
sorry

mtheorem partfun1_th_39:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds Z |`RELSET-1K6\<^bsub>(X,Y)\<^esub> (<:PARTFUN1K3 f,X,Y :>) =FUNCT-1R1 <:PARTFUN1K3 f,X,Z /\\XBOOLE-0K3 Y :>"
sorry

mdef partfun1_def_2 ("totalPARTFUN1V1\<^bsub>'( _ ')\<^esub>" [0]70 ) where
  mlet "X be setHIDDENM2"
"attr totalPARTFUN1V1\<^bsub>(X)\<^esub> for X -definedRELAT-1V4\<bar>RelationRELAT-1M1 means
  (\<lambda>f. domRELSET-1K1\<^bsub>(X)\<^esub> f =XBOOLE-0R4 X)"..

mtheorem partfun1_cl_2:
  mlet "X be emptyXBOOLE-0V1\<bar>setHIDDENM2", "Y be setHIDDENM2"
"cluster note-that totalPARTFUN1V1\<^bsub>(X)\<^esub> for RelationRELSET-1M1-of(X,Y)"
proof
(*coherence*)
  show " for it be RelationRELSET-1M1-of(X,Y) holds it be totalPARTFUN1V1\<^bsub>(X)\<^esub>"
     sorry
qed "sorry"

mtheorem partfun1_cl_3:
  mlet "X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "Y be emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster note-that  non totalPARTFUN1V1\<^bsub>(X)\<^esub> for RelationRELSET-1M1-of(X,Y)"
proof
(*coherence*)
  show " for it be RelationRELSET-1M1-of(X,Y) holds it be  non totalPARTFUN1V1\<^bsub>(X)\<^esub>"
     sorry
qed "sorry"

mtheorem partfun1_th_40:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds <:PARTFUN1K3 f,X,Y :> be totalPARTFUN1V1\<^bsub>(X)\<^esub> implies X c=TARSKIR1 domRELAT-1K1 f"
  using partfun1_th_23 sorry

mtheorem partfun1_th_41:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds <:PARTFUN1K3 {}XBOOLE-0K1,X,Y :> be totalPARTFUN1V1\<^bsub>(X)\<^esub> implies X =XBOOLE-0R4 {}XBOOLE-0K1"
sorry

mtheorem partfun1_th_42:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds X c=TARSKIR1 domRELAT-1K1 f & rngFUNCT-1K2 f c=TARSKIR1 Y implies <:PARTFUN1K3 f,X,Y :> be totalPARTFUN1V1\<^bsub>(X)\<^esub>"
sorry

mtheorem partfun1_th_43:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds <:PARTFUN1K3 f,X,Y :> be totalPARTFUN1V1\<^bsub>(X)\<^esub> implies f .:FUNCT-1K5 X c=TARSKIR1 Y"
sorry

mtheorem partfun1_th_44:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds X c=TARSKIR1 domRELAT-1K1 f & f .:FUNCT-1K5 X c=TARSKIR1 Y implies <:PARTFUN1K3 f,X,Y :> be totalPARTFUN1V1\<^bsub>(X)\<^esub>"
sorry

mdef partfun1_def_3 ("PFuncsPARTFUN1K4'( _ , _ ')" [0,0]228 ) where
  mlet "X be setHIDDENM2", "Y be setHIDDENM2"
"func PFuncsPARTFUN1K4(X,Y) \<rightarrow> setHIDDENM2 means
  \<lambda>it.  for x be objectHIDDENM1 holds x inHIDDENR3 it iff ( ex f be FunctionFUNCT-1M1 st (x =HIDDENR1 f & domRELAT-1K1 f c=TARSKIR1 X) & rngFUNCT-1K2 f c=TARSKIR1 Y)"
proof-
  (*existence*)
    show " ex it be setHIDDENM2 st  for x be objectHIDDENM1 holds x inHIDDENR3 it iff ( ex f be FunctionFUNCT-1M1 st (x =HIDDENR1 f & domRELAT-1K1 f c=TARSKIR1 X) & rngFUNCT-1K2 f c=TARSKIR1 Y)"
sorry
  (*uniqueness*)
    show " for it1 be setHIDDENM2 holds  for it2 be setHIDDENM2 holds ( for x be objectHIDDENM1 holds x inHIDDENR3 it1 iff ( ex f be FunctionFUNCT-1M1 st (x =HIDDENR1 f & domRELAT-1K1 f c=TARSKIR1 X) & rngFUNCT-1K2 f c=TARSKIR1 Y)) & ( for x be objectHIDDENM1 holds x inHIDDENR3 it2 iff ( ex f be FunctionFUNCT-1M1 st (x =HIDDENR1 f & domRELAT-1K1 f c=TARSKIR1 X) & rngFUNCT-1K2 f c=TARSKIR1 Y)) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mtheorem partfun1_cl_4:
  mlet "X be setHIDDENM2", "Y be setHIDDENM2"
"cluster PFuncsPARTFUN1K4(X,Y) as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "PFuncsPARTFUN1K4(X,Y) be  non emptyXBOOLE-0V1"
sorry
qed "sorry"

mtheorem partfun1_th_45:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be PartFuncPARTFUN1M1-of(X,Y) holds f inTARSKIR2 PFuncsPARTFUN1K4(X,Y)"
sorry

mtheorem partfun1_th_46:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be setHIDDENM2 holds f inTARSKIR2 PFuncsPARTFUN1K4(X,Y) implies f be PartFuncPARTFUN1M1-of(X,Y)"
sorry

mtheorem partfun1_th_47:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be ElementSUBSET-1M1-of PFuncsPARTFUN1K4(X,Y) holds f be PartFuncPARTFUN1M1-of(X,Y)"
  using partfun1_th_46 sorry

mtheorem partfun1_th_48:
" for Y be setHIDDENM2 holds PFuncsPARTFUN1K4({}XBOOLE-0K1,Y) =XBOOLE-0R4 {TARSKIK1 {}XBOOLE-0K1 }"
sorry

mtheorem partfun1_th_49:
" for X be setHIDDENM2 holds PFuncsPARTFUN1K4(X,{}XBOOLE-0K1) =XBOOLE-0R4 {TARSKIK1 {}XBOOLE-0K1 }"
sorry

mtheorem partfun1_th_50:
" for X1 be setHIDDENM2 holds  for X2 be setHIDDENM2 holds  for Y1 be setHIDDENM2 holds  for Y2 be setHIDDENM2 holds X1 c=TARSKIR1 X2 & Y1 c=TARSKIR1 Y2 implies PFuncsPARTFUN1K4(X1,Y1) c=TARSKIR1 PFuncsPARTFUN1K4(X2,Y2)"
sorry

mdef partfun1_def_4 (" _ toleratesPARTFUN1R1  _ " [50,50]50 ) where
  mlet "f be FunctionFUNCT-1M1", "g be FunctionFUNCT-1M1"
"pred f toleratesPARTFUN1R1 g means
   for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 f /\\XBOOLE-0K3 domRELAT-1K1 g implies f .FUNCT-1K1 x =XBOOLE-0R4 g .FUNCT-1K1 x"..

mtheorem PARTFUN1R1_reflexivity:
" for g be FunctionFUNCT-1M1 holds g toleratesPARTFUN1R1 g"
sorry

mtheorem PARTFUN1R1_symmetry:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds f toleratesPARTFUN1R1 g implies g toleratesPARTFUN1R1 f"
sorry

mtheorem partfun1_th_51:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds f toleratesPARTFUN1R1 g iff f \\/XBOOLE-0K2 g be FunctionFUNCT-1M1"
  using partfun1_th_1 partfun1_th_2 sorry

mtheorem partfun1_th_52:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds f toleratesPARTFUN1R1 g iff ( ex h be FunctionFUNCT-1M1 st f c=RELAT-1R2 h & g c=RELAT-1R2 h)"
sorry

mtheorem partfun1_th_53:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds domRELAT-1K1 f c=TARSKIR1 domRELAT-1K1 g implies (f toleratesPARTFUN1R1 g iff ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 f implies f .FUNCT-1K1 x =XBOOLE-0R4 g .FUNCT-1K1 x))"
sorry

mtheorem partfun1_th_54:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds f c=RELAT-1R2 g implies f toleratesPARTFUN1R1 g"
  using partfun1_th_52 sorry

mtheorem partfun1_th_55:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds domRELAT-1K1 f =XBOOLE-0R4 domRELAT-1K1 g & f toleratesPARTFUN1R1 g implies f =FUNCT-1R1 g"
   sorry

mtheorem partfun1_th_56:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds domRELAT-1K1 f missesXBOOLE-0R1 domRELAT-1K1 g implies f toleratesPARTFUN1R1 g"
   sorry

mtheorem partfun1_th_57:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds  for h be FunctionFUNCT-1M1 holds f c=RELAT-1R2 h & g c=RELAT-1R2 h implies f toleratesPARTFUN1R1 g"
  using partfun1_th_52 sorry

mtheorem partfun1_th_58:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be PartFuncPARTFUN1M1-of(X,Y) holds  for g be PartFuncPARTFUN1M1-of(X,Y) holds  for h be FunctionFUNCT-1M1 holds f toleratesPARTFUN1R1 h & g c=RELSET-1R1\<^bsub>(X,Y)\<^esub> f implies g toleratesPARTFUN1R1 h"
sorry

mtheorem partfun1_th_59:
" for f be FunctionFUNCT-1M1 holds {}XBOOLE-0K1 toleratesPARTFUN1R1 f"
   sorry

mtheorem partfun1_th_60:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds <:PARTFUN1K3 {}XBOOLE-0K1,X,Y :> toleratesPARTFUN1R1 f"
sorry

mtheorem partfun1_th_61:
" for y be objectHIDDENM1 holds  for X be setHIDDENM2 holds  for f be PartFuncPARTFUN1M1-of(X,{TARSKIK1 y}) holds  for g be PartFuncPARTFUN1M1-of(X,{TARSKIK1 y}) holds f toleratesPARTFUN1R1 g"
sorry

mtheorem partfun1_th_62:
" for X be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds f |RELAT-1K8 X toleratesPARTFUN1R1 f"
sorry

mtheorem partfun1_th_63:
" for Y be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds Y |`RELAT-1K9 f toleratesPARTFUN1R1 f"
sorry

mtheorem partfun1_th_64:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds (Y |`RELAT-1K9 f)|RELAT-1K8 X toleratesPARTFUN1R1 f"
sorry

mtheorem partfun1_th_65:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds <:PARTFUN1K3 f,X,Y :> toleratesPARTFUN1R1 f"
  using partfun1_th_64 sorry

mtheorem partfun1_th_66:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be PartFuncPARTFUN1M1-of(X,Y) holds  for g be PartFuncPARTFUN1M1-of(X,Y) holds (f be totalPARTFUN1V1\<^bsub>(X)\<^esub> & g be totalPARTFUN1V1\<^bsub>(X)\<^esub>) & f toleratesPARTFUN1R1 g implies f =FUNCT-1R1 g"
   sorry

mtheorem partfun1_th_67:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be PartFuncPARTFUN1M1-of(X,Y) holds  for g be PartFuncPARTFUN1M1-of(X,Y) holds  for h be PartFuncPARTFUN1M1-of(X,Y) holds (f toleratesPARTFUN1R1 h & g toleratesPARTFUN1R1 h) & h be totalPARTFUN1V1\<^bsub>(X)\<^esub> implies f toleratesPARTFUN1R1 g"
sorry

mtheorem partfun1_th_68:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be PartFuncPARTFUN1M1-of(X,Y) holds  for g be PartFuncPARTFUN1M1-of(X,Y) holds (Y =XBOOLE-0R4 {}XBOOLE-0K1 implies X =XBOOLE-0R4 {}XBOOLE-0K1) & f toleratesPARTFUN1R1 g implies ( ex h be PartFuncPARTFUN1M1-of(X,Y) st (h be totalPARTFUN1V1\<^bsub>(X)\<^esub> & f toleratesPARTFUN1R1 h) & g toleratesPARTFUN1R1 h)"
sorry

mdef partfun1_def_5 ("TotFuncsPARTFUN1K5\<^bsub>'( _ , _ ')\<^esub>  _ " [0,0,228]228 ) where
  mlet "X be setHIDDENM2", "Y be setHIDDENM2", "f be PartFuncPARTFUN1M1-of(X,Y)"
"func TotFuncsPARTFUN1K5\<^bsub>(X,Y)\<^esub> f \<rightarrow> setHIDDENM2 means
  \<lambda>it.  for x be objectHIDDENM1 holds x inHIDDENR3 it iff ( ex g be PartFuncPARTFUN1M1-of(X,Y) st (g =HIDDENR1 x & g be totalPARTFUN1V1\<^bsub>(X)\<^esub>) & f toleratesPARTFUN1R1 g)"
proof-
  (*existence*)
    show " ex it be setHIDDENM2 st  for x be objectHIDDENM1 holds x inHIDDENR3 it iff ( ex g be PartFuncPARTFUN1M1-of(X,Y) st (g =HIDDENR1 x & g be totalPARTFUN1V1\<^bsub>(X)\<^esub>) & f toleratesPARTFUN1R1 g)"
sorry
  (*uniqueness*)
    show " for it1 be setHIDDENM2 holds  for it2 be setHIDDENM2 holds ( for x be objectHIDDENM1 holds x inHIDDENR3 it1 iff ( ex g be PartFuncPARTFUN1M1-of(X,Y) st (g =HIDDENR1 x & g be totalPARTFUN1V1\<^bsub>(X)\<^esub>) & f toleratesPARTFUN1R1 g)) & ( for x be objectHIDDENM1 holds x inHIDDENR3 it2 iff ( ex g be PartFuncPARTFUN1M1-of(X,Y) st (g =HIDDENR1 x & g be totalPARTFUN1V1\<^bsub>(X)\<^esub>) & f toleratesPARTFUN1R1 g)) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mtheorem partfun1_th_69:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be PartFuncPARTFUN1M1-of(X,Y) holds  for g be setHIDDENM2 holds g inTARSKIR2 TotFuncsPARTFUN1K5\<^bsub>(X,Y)\<^esub> f implies g be PartFuncPARTFUN1M1-of(X,Y)"
sorry

mtheorem partfun1_th_70:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be PartFuncPARTFUN1M1-of(X,Y) holds  for g be PartFuncPARTFUN1M1-of(X,Y) holds g inTARSKIR2 TotFuncsPARTFUN1K5\<^bsub>(X,Y)\<^esub> f implies g be totalPARTFUN1V1\<^bsub>(X)\<^esub>"
sorry

mtheorem partfun1_th_71:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be PartFuncPARTFUN1M1-of(X,Y) holds  for g be FunctionFUNCT-1M1 holds g inTARSKIR2 TotFuncsPARTFUN1K5\<^bsub>(X,Y)\<^esub> f implies f toleratesPARTFUN1R1 g"
sorry

mtheorem partfun1_cl_5:
  mlet "X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "Y be emptyXBOOLE-0V1\<bar>setHIDDENM2", "f be PartFuncPARTFUN1M1-of(X,Y)"
"cluster TotFuncsPARTFUN1K5\<^bsub>(X,Y)\<^esub> f as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "TotFuncsPARTFUN1K5\<^bsub>(X,Y)\<^esub> f be emptyXBOOLE-0V1"
sorry
qed "sorry"

mtheorem partfun1_th_72:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be PartFuncPARTFUN1M1-of(X,Y) holds f be totalPARTFUN1V1\<^bsub>(X)\<^esub> iff TotFuncsPARTFUN1K5\<^bsub>(X,Y)\<^esub> f =XBOOLE-0R4 {TARSKIK1 f}"
sorry

mtheorem partfun1_th_73:
" for Y be setHIDDENM2 holds  for f be PartFuncPARTFUN1M1-of({}XBOOLE-0K1,Y) holds TotFuncsPARTFUN1K5\<^bsub>({}XBOOLE-0K1,Y)\<^esub> f =XBOOLE-0R4 {TARSKIK1 f}"
  using partfun1_th_72 sorry

mtheorem partfun1_th_74:
" for Y be setHIDDENM2 holds  for f be PartFuncPARTFUN1M1-of({}XBOOLE-0K1,Y) holds TotFuncsPARTFUN1K5\<^bsub>({}XBOOLE-0K1,Y)\<^esub> f =XBOOLE-0R4 {TARSKIK1 {}XBOOLE-0K1 }"
  using partfun1_th_72 sorry

mtheorem partfun1_th_75:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be PartFuncPARTFUN1M1-of(X,Y) holds  for g be PartFuncPARTFUN1M1-of(X,Y) holds TotFuncsPARTFUN1K5\<^bsub>(X,Y)\<^esub> f meetsXBOOLE-0R5 TotFuncsPARTFUN1K5\<^bsub>(X,Y)\<^esub> g implies f toleratesPARTFUN1R1 g"
sorry

mtheorem partfun1_th_76:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be PartFuncPARTFUN1M1-of(X,Y) holds  for g be PartFuncPARTFUN1M1-of(X,Y) holds (Y =XBOOLE-0R4 {}XBOOLE-0K1 implies X =XBOOLE-0R4 {}XBOOLE-0K1) & f toleratesPARTFUN1R1 g implies TotFuncsPARTFUN1K5\<^bsub>(X,Y)\<^esub> f meetsXBOOLE-0R5 TotFuncsPARTFUN1K5\<^bsub>(X,Y)\<^esub> g"
sorry

(*begin*)
mlemma partfun1_lm_2:
" for X be setHIDDENM2 holds  for R be RelationRELSET-1M2-of X holds R =RELAT-1R1 idRELAT-1K7 X implies R be totalPARTFUN1V1\<^bsub>(X)\<^esub>"
   sorry

mlemma partfun1_lm_3:
" for X be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds R =RELAT-1R1 idRELAT-1K7 X implies R be reflexiveRELAT-2V1\<bar>symmetricRELAT-2V3\<bar>antisymmetricRELAT-2V4\<bar>transitiveRELAT-2V8"
sorry

mlemma partfun1_lm_4:
" for X be setHIDDENM2 holds idRELAT-1K7 X be RelationRELSET-1M2-of X"
sorry

mtheorem partfun1_cl_6:
  mlet "X be setHIDDENM2"
"cluster totalPARTFUN1V1\<^bsub>(X)\<^esub>\<bar>reflexiveRELAT-2V1\<bar>symmetricRELAT-2V3\<bar>antisymmetricRELAT-2V4\<bar>transitiveRELAT-2V8 for RelationRELSET-1M2-of X"
proof
(*existence*)
  show " ex it be RelationRELSET-1M2-of X st it be totalPARTFUN1V1\<^bsub>(X)\<^esub>\<bar>reflexiveRELAT-2V1\<bar>symmetricRELAT-2V3\<bar>antisymmetricRELAT-2V4\<bar>transitiveRELAT-2V8"
sorry
qed "sorry"

mtheorem partfun1_cl_7:
"cluster symmetricRELAT-2V3\<bar>transitiveRELAT-2V8 also-is reflexiveRELAT-2V1 for RelationRELAT-1M1"
proof
(*coherence*)
  show " for it be RelationRELAT-1M1 holds it be symmetricRELAT-2V3\<bar>transitiveRELAT-2V8 implies it be reflexiveRELAT-2V1"
sorry
qed "sorry"

mtheorem partfun1_cl_8:
  mlet "X be setHIDDENM2"
"cluster idRELAT-1K7 X as-term-is symmetricRELAT-2V3\<bar>antisymmetricRELAT-2V4\<bar>transitiveRELAT-2V8"
proof
(*coherence*)
  show "idRELAT-1K7 X be symmetricRELAT-2V3\<bar>antisymmetricRELAT-2V4\<bar>transitiveRELAT-2V8"
    using partfun1_lm_3 sorry
qed "sorry"

abbreviation(input) PARTFUN1K6("idPARTFUN1K6  _ " [228]228) where
  "idPARTFUN1K6 X \<equiv> idRELAT-1K7 X"

mtheorem partfun1_add_3:
  mlet "X be setHIDDENM2"
"cluster idRELAT-1K7 X as-term-is totalPARTFUN1V1\<^bsub>(X)\<^esub>\<bar>RelationRELSET-1M2-of X"
proof
(*coherence*)
  show "idRELAT-1K7 X be totalPARTFUN1V1\<^bsub>(X)\<^esub>\<bar>RelationRELSET-1M2-of X"
    using partfun1_lm_2 partfun1_lm_4 sorry
qed "sorry"

theorem partfun1_sch_4:
  fixes Af0 Ff1 Gf1 Cp1 
  assumes
[ty]: "Af0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
  [ty_func]: "\<And> x1. x1 be objectHIDDENM1 \<Longrightarrow> Ff1(x1) be objectHIDDENM1" and
  [ty_func]: "\<And> x1. x1 be objectHIDDENM1 \<Longrightarrow> Gf1(x1) be objectHIDDENM1"
  shows " ex f be FunctionFUNCT-1M1 st domRELAT-1K1 f =XBOOLE-0R4 Af0 & ( for x be ElementSUBSET-1M1-of Af0 holds (Cp1(x) implies f .FUNCT-1K1 x =HIDDENR1 Ff1(x)) & ( not Cp1(x) implies f .FUNCT-1K1 x =HIDDENR1 Gf1(x)))"
sorry

(*begin*)
reserve A for "setHIDDENM2"
reserve f, g, h for "FunctionFUNCT-1M1"
mtheorem partfun1_th_77:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds  for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for z be objectHIDDENM1 holds (f toleratesPARTFUN1R1 g & [TARSKIK4 x,y ] inHIDDENR3 f) & [TARSKIK4 x,z ] inHIDDENR3 g implies y =HIDDENR1 z"
sorry

mtheorem partfun1_th_78:
" for A be setHIDDENM2 holds A be functionalFUNCT-1V6 & ( for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds f inTARSKIR2 A & g inTARSKIR2 A implies f toleratesPARTFUN1R1 g) implies unionTARSKIK3 A be FunctionFUNCT-1M1"
sorry

mdef partfun1_def_6 (" _ '/.PARTFUN1K7\<^bsub>'( _ ')\<^esub>  _ " [200,0,200]200 ) where
  mlet "D be setHIDDENM2", "p be D -valuedRELAT-1V5\<bar>FunctionFUNCT-1M1", "i be objectHIDDENM1"
"assume i inHIDDENR3 domRELAT-1K1 p func p /.PARTFUN1K7\<^bsub>(D)\<^esub> i \<rightarrow> ElementSUBSET-1M1-of D equals
  p .FUNCT-1K1 i"
proof-
  (*coherence*)
    show "i inHIDDENR3 domRELAT-1K1 p implies p .FUNCT-1K1 i be ElementSUBSET-1M1-of D"
sorry
qed "sorry"

mtheorem partfun1_cl_9:
  mlet "X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "Y be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster  non emptyXBOOLE-0V1 for PartFuncPARTFUN1M1-of(X,Y)"
proof
(*existence*)
  show " ex it be PartFuncPARTFUN1M1-of(X,Y) st it be  non emptyXBOOLE-0V1"
sorry
qed "sorry"

mtheorem partfun1_cl_10:
  mlet "A be setHIDDENM2", "B be setHIDDENM2"
"cluster PFuncsPARTFUN1K4(A,B) as-term-is functionalFUNCT-1V6"
proof
(*coherence*)
  show "PFuncsPARTFUN1K4(A,B) be functionalFUNCT-1V6"
sorry
qed "sorry"

mtheorem partfun1_th_79:
" for f1 be FunctionFUNCT-1M1 holds  for f2 be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds (rngFUNCT-1K2 g c=TARSKIR1 domRELAT-1K1 f1 & rngFUNCT-1K2 g c=TARSKIR1 domRELAT-1K1 f2) & f1 toleratesPARTFUN1R1 f2 implies f1 *FUNCT-1K3 g =FUNCT-1R1 f2 *FUNCT-1K3 g"
sorry

mtheorem partfun1_th_80:
" for x be objectHIDDENM1 holds  for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be Y -valuedRELAT-1V5\<bar>FunctionFUNCT-1M1 holds x inHIDDENR3 domRELAT-1K1 (f |RELAT-1K8 X) implies (f |RELAT-1K8 X)/.PARTFUN1K7\<^bsub>(Y)\<^esub> x =XBOOLE-0R4 f /.PARTFUN1K7\<^bsub>(Y)\<^esub> x"
sorry

theorem partfun1_sch_5:
  fixes Af0 Ff1 Gf1 Cp1 
  assumes
[ty]: "Af0 be setHIDDENM2" and
  [ty_func]: "\<And> x1. x1 be objectHIDDENM1 \<Longrightarrow> Ff1(x1) be objectHIDDENM1" and
  [ty_func]: "\<And> x1. x1 be objectHIDDENM1 \<Longrightarrow> Gf1(x1) be objectHIDDENM1"
  shows " ex f be FunctionFUNCT-1M1 st domRELAT-1K1 f =XBOOLE-0R4 Af0 & ( for x be setHIDDENM2 holds x inTARSKIR2 Af0 implies (Cp1(x) implies f .FUNCT-1K1 x =HIDDENR1 Ff1(x)) & ( not Cp1(x) implies f .FUNCT-1K1 x =HIDDENR1 Gf1(x)))"
sorry

mtheorem partfun1_th_81:
" for x be objectHIDDENM1 holds  for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds f .FUNCT-1K1 x =XBOOLE-0R4 g .FUNCT-1K1 x implies f |RELAT-1K8 {TARSKIK1 x} toleratesPARTFUN1R1 g |RELAT-1K8 {TARSKIK1 x}"
sorry

mtheorem partfun1_th_82:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds f .FUNCT-1K1 x =XBOOLE-0R4 g .FUNCT-1K1 x & f .FUNCT-1K1 y =XBOOLE-0R4 g .FUNCT-1K1 y implies f |RELAT-1K8 {TARSKIK2 x,y } toleratesPARTFUN1R1 g |RELAT-1K8 {TARSKIK2 x,y }"
sorry

end
