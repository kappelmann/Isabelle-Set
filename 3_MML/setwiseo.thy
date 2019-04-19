theory setwiseo
  imports finsub_1
begin
(*begin*)
reserve x, y, z, X, Y for "setHIDDENM2"
mtheorem setwiseo_th_1:
" for x be setHIDDENM2 holds  for y be setHIDDENM2 holds  for z be setHIDDENM2 holds {TARSKIK1 x} c=TARSKIR1 {ENUMSET1K1 x,y,z }"
sorry

mtheorem setwiseo_th_2:
" for x be setHIDDENM2 holds  for y be setHIDDENM2 holds  for z be setHIDDENM2 holds {TARSKIK2 x,y } c=TARSKIR1 {ENUMSET1K1 x,y,z }"
sorry

(*\$CT 3*)
mtheorem setwiseo_th_6:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds f .:FUNCT-1K5 (Y \\SUBSET-1K6 f \<inverse>FUNCT-1K6 X) =XBOOLE-0R4 f .:FUNCT-1K5 Y \\SUBSET-1K6 X"
sorry

reserve X, Y for " non emptyXBOOLE-0V1\<bar>setHIDDENM2"
reserve f for "FunctionFUNCT-2M1-of(X,Y)"
mtheorem setwiseo_th_7:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for Y be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(X,Y) holds  for x be ElementSUBSET-1M1-of X holds x inTARSKIR2 f \<inverse>RELSET-1K8\<^bsub>(X,Y)\<^esub> {TARSKIK1 f .FUNCT-2K3\<^bsub>(X,Y)\<^esub> x }"
sorry

mtheorem setwiseo_th_8:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for Y be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(X,Y) holds  for x be ElementSUBSET-1M1-of X holds ImRELAT-1K12(f,x) =XBOOLE-0R4 {TARSKIK1 f .FUNCT-2K3\<^bsub>(X,Y)\<^esub> x }"
sorry

mtheorem setwiseo_th_9:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for B be ElementSUBSET-1M1-of FinFINSUB-1K5 X holds  for x be setHIDDENM2 holds x inTARSKIR2 B implies x be ElementSUBSET-1M1-of X"
sorry

mtheorem setwiseo_th_10:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for Y be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for A be ElementSUBSET-1M1-of FinFINSUB-1K5 X holds  for B be setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(X,Y) holds ( for x be ElementSUBSET-1M1-of X holds x inTARSKIR2 A implies f .FUNCT-2K3\<^bsub>(X,Y)\<^esub> x inTARSKIR2 B) implies f .:RELSET-1K7\<^bsub>(X,Y)\<^esub> A c=TARSKIR1 B"
sorry

mtheorem setwiseo_th_11:
" for X be setHIDDENM2 holds  for B be ElementSUBSET-1M1-of FinFINSUB-1K5 X holds  for A be setHIDDENM2 holds A c=TARSKIR1 B implies A be ElementSUBSET-1M1-of FinFINSUB-1K5 X"
sorry

mlemma setwiseo_lm_1:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for Y be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(X,Y) holds  for A be ElementSUBSET-1M1-of FinFINSUB-1K5 X holds f .:RELSET-1K7\<^bsub>(X,Y)\<^esub> A be ElementSUBSET-1M1-of FinFINSUB-1K5 Y"
  using finsub_1_def_5 sorry

mtheorem setwiseo_th_12:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for B be ElementSUBSET-1M1-of FinFINSUB-1K5 X holds B <>HIDDENR2 {}XBOOLE-0K1 implies ( ex x be ElementSUBSET-1M1-of X st x inTARSKIR2 B)"
sorry

mtheorem setwiseo_th_13:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for Y be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(X,Y) holds  for A be ElementSUBSET-1M1-of FinFINSUB-1K5 X holds f .:RELSET-1K7\<^bsub>(X,Y)\<^esub> A =XBOOLE-0R4 {}XBOOLE-0K1 implies A =XBOOLE-0R4 {}XBOOLE-0K1"
sorry

mtheorem setwiseo_cl_1:
  mlet "X be setHIDDENM2"
"cluster emptyXBOOLE-0V1 for ElementSUBSET-1M1-of FinFINSUB-1K5 X"
proof
(*existence*)
  show " ex it be ElementSUBSET-1M1-of FinFINSUB-1K5 X st it be emptyXBOOLE-0V1"
sorry
qed "sorry"

mdef setwiseo_def_1 ("{}.SETWISEOK1  _ " [250]250 ) where
  mlet "X be setHIDDENM2"
"func {}.SETWISEOK1 X \<rightarrow> emptyXBOOLE-0V1\<bar>ElementSUBSET-1M1-of FinFINSUB-1K5 X equals
  {}XBOOLE-0K1"
proof-
  (*coherence*)
    show "{}XBOOLE-0K1 be emptyXBOOLE-0V1\<bar>ElementSUBSET-1M1-of FinFINSUB-1K5 X"
      using finsub_1_th_7 sorry
qed "sorry"

theorem setwiseo_sch_1:
  fixes Af0 Bf0 Pp2 
  assumes
[ty]: "Af0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
  [ty]: "Bf0 be ElementSUBSET-1M1-of FinFINSUB-1K5 Af0"
  shows " ex f be FunctionFUNCT-2M1-of(Af0,FinFINSUB-1K5 Af0) st  for b be ElementSUBSET-1M1-of Af0 holds  for a be ElementSUBSET-1M1-of Af0 holds a inTARSKIR2 f .FUNCT-2K3\<^bsub>(Af0,FinFINSUB-1K5 Af0)\<^esub> b iff a inTARSKIR2 Bf0 & Pp2(a,b)"
sorry

mdef setwiseo_def_2 ("having-a-unitySETWISEOV1\<^bsub>'( _ ')\<^esub>" [0]70 ) where
  mlet "X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
"attr having-a-unitySETWISEOV1\<^bsub>(X)\<^esub> for BinOpBINOP-1M2-of X means
  (\<lambda>F.  ex x be ElementSUBSET-1M1-of X st x is-a-unity-wrtBINOP-1R3\<^bsub>(X)\<^esub> F)"..

mtheorem setwiseo_th_14:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for F be BinOpBINOP-1M2-of X holds F be having-a-unitySETWISEOV1\<^bsub>(X)\<^esub> iff the-unity-wrtBINOP-1K3\<^bsub>(X)\<^esub> F is-a-unity-wrtBINOP-1R3\<^bsub>(X)\<^esub> F"
  using binop_1_def_8 sorry

mtheorem setwiseo_th_15:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for F be BinOpBINOP-1M2-of X holds F be having-a-unitySETWISEOV1\<^bsub>(X)\<^esub> implies ( for x be ElementSUBSET-1M1-of X holds F .BINOP-1K4\<^bsub>(X)\<^esub>(the-unity-wrtBINOP-1K3\<^bsub>(X)\<^esub> F,x) =XBOOLE-0R4 x & F .BINOP-1K4\<^bsub>(X)\<^esub>(x,the-unity-wrtBINOP-1K3\<^bsub>(X)\<^esub> F) =XBOOLE-0R4 x)"
sorry

mtheorem setwiseo_cl_2:
  mlet "X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster  non emptyXBOOLE-0V1 for ElementSUBSET-1M1-of FinFINSUB-1K5 X"
proof
(*existence*)
  show " ex it be ElementSUBSET-1M1-of FinFINSUB-1K5 X st it be  non emptyXBOOLE-0V1"
sorry
qed "sorry"

syntax SETWISEOK2 :: " Set \<Rightarrow>  Set \<Rightarrow> Set" ("{.SETWISEOK2\<^bsub>'( _ ')\<^esub>  _ .}" [0,0]164)
translations "{.SETWISEOK2\<^bsub>(X)\<^esub> x.}" \<rightharpoonup> "{TARSKIK1 x}"

syntax SETWISEOK3 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" ("{.SETWISEOK3\<^bsub>'( _ ')\<^esub> _ , _ .}" [0,0,0]164)
translations "{.SETWISEOK3\<^bsub>(X)\<^esub> x,y .}" \<rightharpoonup> "{TARSKIK2 x,y }"

syntax SETWISEOK4 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" ("{.SETWISEOK4\<^bsub>'( _ ')\<^esub> _ , _ , _ .}" [0,0,0,0]164)
translations "{.SETWISEOK4\<^bsub>(X)\<^esub> x,y,z .}" \<rightharpoonup> "{ENUMSET1K1 x,y,z }"

syntax SETWISEOK5 :: " Set \<Rightarrow>  Set \<Rightarrow> Set" ("{.SETWISEOK5\<^bsub>'( _ ')\<^esub>  _ .}" [0,0]164)
translations "{.SETWISEOK5\<^bsub>(X)\<^esub> x.}" \<rightharpoonup> "{TARSKIK1 x}"

mtheorem setwiseo_add_1:
  mlet "X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "x be ElementSUBSET-1M1-of X"
"cluster {TARSKIK1 x} as-term-is ElementSUBSET-1M1-of FinFINSUB-1K5 X"
proof
(*coherence*)
  show "{TARSKIK1 x} be ElementSUBSET-1M1-of FinFINSUB-1K5 X"
sorry
qed "sorry"

syntax SETWISEOK6 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" ("{.SETWISEOK6\<^bsub>'( _ ')\<^esub> _ , _ .}" [0,0,0]164)
translations "{.SETWISEOK6\<^bsub>(X)\<^esub> x,y .}" \<rightharpoonup> "{TARSKIK2 x,y }"

mtheorem setwiseo_add_2:
  mlet "X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "x be ElementSUBSET-1M1-of X", "y be ElementSUBSET-1M1-of X"
"cluster {TARSKIK2 x,y } as-term-is ElementSUBSET-1M1-of FinFINSUB-1K5 X"
proof
(*coherence*)
  show "{TARSKIK2 x,y } be ElementSUBSET-1M1-of FinFINSUB-1K5 X"
sorry
qed "sorry"

syntax SETWISEOK7 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" ("{.SETWISEOK7\<^bsub>'( _ ')\<^esub> _ , _ , _ .}" [0,0,0,0]164)
translations "{.SETWISEOK7\<^bsub>(X)\<^esub> x,y,z .}" \<rightharpoonup> "{ENUMSET1K1 x,y,z }"

mtheorem setwiseo_add_3:
  mlet "X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "x be ElementSUBSET-1M1-of X", "y be ElementSUBSET-1M1-of X", "z be ElementSUBSET-1M1-of X"
"cluster {ENUMSET1K1 x,y,z } as-term-is ElementSUBSET-1M1-of FinFINSUB-1K5 X"
proof
(*coherence*)
  show "{ENUMSET1K1 x,y,z } be ElementSUBSET-1M1-of FinFINSUB-1K5 X"
sorry
qed "sorry"

syntax SETWISEOK8 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ '\\'/SETWISEOK8\<^bsub>'( _ ')\<^esub>  _ " [132,0,132]132)
translations "A \\/SETWISEOK8\<^bsub>(X)\<^esub> B" \<rightharpoonup> "A \\/XBOOLE-0K2 B"

mtheorem setwiseo_add_4:
  mlet "X be setHIDDENM2", "A be ElementSUBSET-1M1-of FinFINSUB-1K5 X", "B be ElementSUBSET-1M1-of FinFINSUB-1K5 X"
"cluster A \\/XBOOLE-0K2 B as-term-is ElementSUBSET-1M1-of FinFINSUB-1K5 X"
proof
(*coherence*)
  show "A \\/XBOOLE-0K2 B be ElementSUBSET-1M1-of FinFINSUB-1K5 X"
    using finsub_1_th_1 sorry
qed "sorry"

syntax SETWISEOK9 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ '\\SETWISEOK9\<^bsub>'( _ ')\<^esub>  _ " [132,0,132]132)
translations "A \\SETWISEOK9\<^bsub>(X)\<^esub> B" \<rightharpoonup> "A \\XBOOLE-0K4 B"

mtheorem setwiseo_add_5:
  mlet "X be setHIDDENM2", "A be ElementSUBSET-1M1-of FinFINSUB-1K5 X", "B be ElementSUBSET-1M1-of FinFINSUB-1K5 X"
"cluster A \\XBOOLE-0K4 B as-term-is ElementSUBSET-1M1-of FinFINSUB-1K5 X"
proof
(*coherence*)
  show "A \\XBOOLE-0K4 B be ElementSUBSET-1M1-of FinFINSUB-1K5 X"
    using finsub_1_th_1 sorry
qed "sorry"

theorem setwiseo_sch_2:
  fixes Xf0 Pp1 
  assumes
[ty]: "Xf0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
   A1: "Pp1({}.SETWISEOK1 Xf0)" and
   A2: " for B9 be ElementSUBSET-1M1-of FinFINSUB-1K5 Xf0 holds  for b be ElementSUBSET-1M1-of Xf0 holds Pp1(B9) &  not b inTARSKIR2 B9 implies Pp1(B9 \\/XBOOLE-0K2 {TARSKIK1 b})"
  shows " for B be ElementSUBSET-1M1-of FinFINSUB-1K5 Xf0 holds Pp1(B)"
sorry

theorem setwiseo_sch_3:
  fixes Xf0 Pp1 
  assumes
[ty]: "Xf0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
   A1: " for x be ElementSUBSET-1M1-of Xf0 holds Pp1({.SETWISEOK5\<^bsub>(Xf0)\<^esub> x.})" and
   A2: " for B1 be  non emptyXBOOLE-0V1\<bar>ElementSUBSET-1M1-of FinFINSUB-1K5 Xf0 holds  for B2 be  non emptyXBOOLE-0V1\<bar>ElementSUBSET-1M1-of FinFINSUB-1K5 Xf0 holds Pp1(B1) & Pp1(B2) implies Pp1(B1 \\/SETWISEOK8\<^bsub>(Xf0)\<^esub> B2)"
  shows " for B be  non emptyXBOOLE-0V1\<bar>ElementSUBSET-1M1-of FinFINSUB-1K5 Xf0 holds Pp1(B)"
sorry

theorem setwiseo_sch_4:
  fixes Xf0 Pp1 
  assumes
[ty]: "Xf0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
   A1: "Pp1({}.SETWISEOK1 Xf0)" and
   A2: " for B9 be ElementSUBSET-1M1-of FinFINSUB-1K5 Xf0 holds  for b be ElementSUBSET-1M1-of Xf0 holds Pp1(B9) implies Pp1(B9 \\/XBOOLE-0K2 {TARSKIK1 b})"
  shows " for B be ElementSUBSET-1M1-of FinFINSUB-1K5 Xf0 holds Pp1(B)"
sorry

mdef setwiseo_def_3 (" _ $$SETWISEOK10\<^bsub>'( _ , _ ')\<^esub>'( _ , _ ')" [180,0,0,0,0]180 ) where
  mlet "X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "Y be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "F be BinOpBINOP-1M2-of Y", "B be ElementSUBSET-1M1-of FinFINSUB-1K5 X", "f be FunctionFUNCT-2M1-of(X,Y)"
"assume (B <>HIDDENR2 {}XBOOLE-0K1 or F be having-a-unitySETWISEOV1\<^bsub>(Y)\<^esub>) & (F be commutativeBINOP-1V1\<^bsub>(Y)\<^esub> & F be associativeBINOP-1V2\<^bsub>(Y)\<^esub>) func F $$SETWISEOK10\<^bsub>(X,Y)\<^esub>(B,f) \<rightarrow> ElementSUBSET-1M1-of Y means
  \<lambda>it.  ex G be FunctionFUNCT-2M1-of(FinFINSUB-1K5 X,Y) st ((it =XBOOLE-0R4 G .FUNCT-2K3\<^bsub>(FinFINSUB-1K5 X,Y)\<^esub> B & ( for e be ElementSUBSET-1M1-of Y holds e is-a-unity-wrtBINOP-1R3\<^bsub>(Y)\<^esub> F implies G .FUNCT-1K1 {}XBOOLE-0K1 =XBOOLE-0R4 e)) & ( for x be ElementSUBSET-1M1-of X holds G .FUNCT-1K1 {TARSKIK1 x} =XBOOLE-0R4 f .FUNCT-2K3\<^bsub>(X,Y)\<^esub> x)) & ( for B9 be ElementSUBSET-1M1-of FinFINSUB-1K5 X holds B9 c=TARSKIR1 B & B9 <>HIDDENR2 {}XBOOLE-0K1 implies ( for x be ElementSUBSET-1M1-of X holds x inTARSKIR2 B \\SETWISEOK9\<^bsub>(X)\<^esub> B9 implies G .FUNCT-1K1 (B9 \\/XBOOLE-0K2 {TARSKIK1 x}) =XBOOLE-0R4 F .BINOP-1K4\<^bsub>(Y)\<^esub>(G .FUNCT-2K3\<^bsub>(FinFINSUB-1K5 X,Y)\<^esub> B9,f .FUNCT-2K3\<^bsub>(X,Y)\<^esub> x)))"
proof-
  (*existence*)
    show "(B <>HIDDENR2 {}XBOOLE-0K1 or F be having-a-unitySETWISEOV1\<^bsub>(Y)\<^esub>) & (F be commutativeBINOP-1V1\<^bsub>(Y)\<^esub> & F be associativeBINOP-1V2\<^bsub>(Y)\<^esub>) implies ( ex it be ElementSUBSET-1M1-of Y st  ex G be FunctionFUNCT-2M1-of(FinFINSUB-1K5 X,Y) st ((it =XBOOLE-0R4 G .FUNCT-2K3\<^bsub>(FinFINSUB-1K5 X,Y)\<^esub> B & ( for e be ElementSUBSET-1M1-of Y holds e is-a-unity-wrtBINOP-1R3\<^bsub>(Y)\<^esub> F implies G .FUNCT-1K1 {}XBOOLE-0K1 =XBOOLE-0R4 e)) & ( for x be ElementSUBSET-1M1-of X holds G .FUNCT-1K1 {TARSKIK1 x} =XBOOLE-0R4 f .FUNCT-2K3\<^bsub>(X,Y)\<^esub> x)) & ( for B9 be ElementSUBSET-1M1-of FinFINSUB-1K5 X holds B9 c=TARSKIR1 B & B9 <>HIDDENR2 {}XBOOLE-0K1 implies ( for x be ElementSUBSET-1M1-of X holds x inTARSKIR2 B \\SETWISEOK9\<^bsub>(X)\<^esub> B9 implies G .FUNCT-1K1 (B9 \\/XBOOLE-0K2 {TARSKIK1 x}) =XBOOLE-0R4 F .BINOP-1K4\<^bsub>(Y)\<^esub>(G .FUNCT-2K3\<^bsub>(FinFINSUB-1K5 X,Y)\<^esub> B9,f .FUNCT-2K3\<^bsub>(X,Y)\<^esub> x))))"
sorry
  (*uniqueness*)
    show "(B <>HIDDENR2 {}XBOOLE-0K1 or F be having-a-unitySETWISEOV1\<^bsub>(Y)\<^esub>) & (F be commutativeBINOP-1V1\<^bsub>(Y)\<^esub> & F be associativeBINOP-1V2\<^bsub>(Y)\<^esub>) implies ( for it1 be ElementSUBSET-1M1-of Y holds  for it2 be ElementSUBSET-1M1-of Y holds ( ex G be FunctionFUNCT-2M1-of(FinFINSUB-1K5 X,Y) st ((it1 =XBOOLE-0R4 G .FUNCT-2K3\<^bsub>(FinFINSUB-1K5 X,Y)\<^esub> B & ( for e be ElementSUBSET-1M1-of Y holds e is-a-unity-wrtBINOP-1R3\<^bsub>(Y)\<^esub> F implies G .FUNCT-1K1 {}XBOOLE-0K1 =XBOOLE-0R4 e)) & ( for x be ElementSUBSET-1M1-of X holds G .FUNCT-1K1 {TARSKIK1 x} =XBOOLE-0R4 f .FUNCT-2K3\<^bsub>(X,Y)\<^esub> x)) & ( for B9 be ElementSUBSET-1M1-of FinFINSUB-1K5 X holds B9 c=TARSKIR1 B & B9 <>HIDDENR2 {}XBOOLE-0K1 implies ( for x be ElementSUBSET-1M1-of X holds x inTARSKIR2 B \\SETWISEOK9\<^bsub>(X)\<^esub> B9 implies G .FUNCT-1K1 (B9 \\/XBOOLE-0K2 {TARSKIK1 x}) =XBOOLE-0R4 F .BINOP-1K4\<^bsub>(Y)\<^esub>(G .FUNCT-2K3\<^bsub>(FinFINSUB-1K5 X,Y)\<^esub> B9,f .FUNCT-2K3\<^bsub>(X,Y)\<^esub> x)))) & ( ex G be FunctionFUNCT-2M1-of(FinFINSUB-1K5 X,Y) st ((it2 =XBOOLE-0R4 G .FUNCT-2K3\<^bsub>(FinFINSUB-1K5 X,Y)\<^esub> B & ( for e be ElementSUBSET-1M1-of Y holds e is-a-unity-wrtBINOP-1R3\<^bsub>(Y)\<^esub> F implies G .FUNCT-1K1 {}XBOOLE-0K1 =XBOOLE-0R4 e)) & ( for x be ElementSUBSET-1M1-of X holds G .FUNCT-1K1 {TARSKIK1 x} =XBOOLE-0R4 f .FUNCT-2K3\<^bsub>(X,Y)\<^esub> x)) & ( for B9 be ElementSUBSET-1M1-of FinFINSUB-1K5 X holds B9 c=TARSKIR1 B & B9 <>HIDDENR2 {}XBOOLE-0K1 implies ( for x be ElementSUBSET-1M1-of X holds x inTARSKIR2 B \\SETWISEOK9\<^bsub>(X)\<^esub> B9 implies G .FUNCT-1K1 (B9 \\/XBOOLE-0K2 {TARSKIK1 x}) =XBOOLE-0R4 F .BINOP-1K4\<^bsub>(Y)\<^esub>(G .FUNCT-2K3\<^bsub>(FinFINSUB-1K5 X,Y)\<^esub> B9,f .FUNCT-2K3\<^bsub>(X,Y)\<^esub> x)))) implies it1 =HIDDENR1 it2)"
sorry
qed "sorry"

mtheorem setwiseo_th_16:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for Y be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for F be BinOpBINOP-1M2-of Y holds  for B be ElementSUBSET-1M1-of FinFINSUB-1K5 X holds  for f be FunctionFUNCT-2M1-of(X,Y) holds (((B <>HIDDENR2 {}XBOOLE-0K1 or F be having-a-unitySETWISEOV1\<^bsub>(Y)\<^esub>) & F be idempotentBINOP-1V3\<^bsub>(Y)\<^esub>) & F be commutativeBINOP-1V1\<^bsub>(Y)\<^esub>) & F be associativeBINOP-1V2\<^bsub>(Y)\<^esub> implies ( for IT be ElementSUBSET-1M1-of Y holds IT =XBOOLE-0R4 F $$SETWISEOK10\<^bsub>(X,Y)\<^esub>(B,f) iff ( ex G be FunctionFUNCT-2M1-of(FinFINSUB-1K5 X,Y) st ((IT =XBOOLE-0R4 G .FUNCT-2K3\<^bsub>(FinFINSUB-1K5 X,Y)\<^esub> B & ( for e be ElementSUBSET-1M1-of Y holds e is-a-unity-wrtBINOP-1R3\<^bsub>(Y)\<^esub> F implies G .FUNCT-1K1 {}XBOOLE-0K1 =XBOOLE-0R4 e)) & ( for x be ElementSUBSET-1M1-of X holds G .FUNCT-1K1 {TARSKIK1 x} =XBOOLE-0R4 f .FUNCT-2K3\<^bsub>(X,Y)\<^esub> x)) & ( for B9 be ElementSUBSET-1M1-of FinFINSUB-1K5 X holds B9 c=TARSKIR1 B & B9 <>HIDDENR2 {}XBOOLE-0K1 implies ( for x be ElementSUBSET-1M1-of X holds x inTARSKIR2 B implies G .FUNCT-1K1 (B9 \\/XBOOLE-0K2 {TARSKIK1 x}) =XBOOLE-0R4 F .BINOP-1K4\<^bsub>(Y)\<^esub>(G .FUNCT-2K3\<^bsub>(FinFINSUB-1K5 X,Y)\<^esub> B9,f .FUNCT-2K3\<^bsub>(X,Y)\<^esub> x)))))"
sorry

reserve X, Y for " non emptyXBOOLE-0V1\<bar>setHIDDENM2"
reserve F for "BinOpBINOP-1M2-of Y"
reserve B for "ElementSUBSET-1M1-of FinFINSUB-1K5 X"
reserve f for "FunctionFUNCT-2M1-of(X,Y)"
mtheorem setwiseo_th_17:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for Y be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for F be BinOpBINOP-1M2-of Y holds  for f be FunctionFUNCT-2M1-of(X,Y) holds F be commutativeBINOP-1V1\<^bsub>(Y)\<^esub> & F be associativeBINOP-1V2\<^bsub>(Y)\<^esub> implies ( for b be ElementSUBSET-1M1-of X holds F $$SETWISEOK10\<^bsub>(X,Y)\<^esub>({.SETWISEOK5\<^bsub>(X)\<^esub> b.},f) =XBOOLE-0R4 f .FUNCT-2K3\<^bsub>(X,Y)\<^esub> b)"
sorry

mtheorem setwiseo_th_18:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for Y be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for F be BinOpBINOP-1M2-of Y holds  for f be FunctionFUNCT-2M1-of(X,Y) holds (F be idempotentBINOP-1V3\<^bsub>(Y)\<^esub> & F be commutativeBINOP-1V1\<^bsub>(Y)\<^esub>) & F be associativeBINOP-1V2\<^bsub>(Y)\<^esub> implies ( for a be ElementSUBSET-1M1-of X holds  for b be ElementSUBSET-1M1-of X holds F $$SETWISEOK10\<^bsub>(X,Y)\<^esub>({.SETWISEOK6\<^bsub>(X)\<^esub> a,b .},f) =XBOOLE-0R4 F .BINOP-1K4\<^bsub>(Y)\<^esub>(f .FUNCT-2K3\<^bsub>(X,Y)\<^esub> a,f .FUNCT-2K3\<^bsub>(X,Y)\<^esub> b))"
sorry

mtheorem setwiseo_th_19:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for Y be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for F be BinOpBINOP-1M2-of Y holds  for f be FunctionFUNCT-2M1-of(X,Y) holds (F be idempotentBINOP-1V3\<^bsub>(Y)\<^esub> & F be commutativeBINOP-1V1\<^bsub>(Y)\<^esub>) & F be associativeBINOP-1V2\<^bsub>(Y)\<^esub> implies ( for a be ElementSUBSET-1M1-of X holds  for b be ElementSUBSET-1M1-of X holds  for c be ElementSUBSET-1M1-of X holds F $$SETWISEOK10\<^bsub>(X,Y)\<^esub>({.SETWISEOK7\<^bsub>(X)\<^esub> a,b,c .},f) =XBOOLE-0R4 F .BINOP-1K4\<^bsub>(Y)\<^esub>(F .BINOP-1K4\<^bsub>(Y)\<^esub>(f .FUNCT-2K3\<^bsub>(X,Y)\<^esub> a,f .FUNCT-2K3\<^bsub>(X,Y)\<^esub> b),f .FUNCT-2K3\<^bsub>(X,Y)\<^esub> c))"
sorry

mtheorem setwiseo_th_20:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for Y be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for F be BinOpBINOP-1M2-of Y holds  for B be ElementSUBSET-1M1-of FinFINSUB-1K5 X holds  for f be FunctionFUNCT-2M1-of(X,Y) holds ((F be idempotentBINOP-1V3\<^bsub>(Y)\<^esub> & F be commutativeBINOP-1V1\<^bsub>(Y)\<^esub>) & F be associativeBINOP-1V2\<^bsub>(Y)\<^esub>) & B <>HIDDENR2 {}XBOOLE-0K1 implies ( for x be ElementSUBSET-1M1-of X holds F $$SETWISEOK10\<^bsub>(X,Y)\<^esub>(B \\/SETWISEOK8\<^bsub>(X)\<^esub> {.SETWISEOK5\<^bsub>(X)\<^esub> x.},f) =XBOOLE-0R4 F .BINOP-1K4\<^bsub>(Y)\<^esub>(F $$SETWISEOK10\<^bsub>(X,Y)\<^esub>(B,f),f .FUNCT-2K3\<^bsub>(X,Y)\<^esub> x))"
sorry

mtheorem setwiseo_th_21:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for Y be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for F be BinOpBINOP-1M2-of Y holds  for f be FunctionFUNCT-2M1-of(X,Y) holds (F be idempotentBINOP-1V3\<^bsub>(Y)\<^esub> & F be commutativeBINOP-1V1\<^bsub>(Y)\<^esub>) & F be associativeBINOP-1V2\<^bsub>(Y)\<^esub> implies ( for B1 be ElementSUBSET-1M1-of FinFINSUB-1K5 X holds  for B2 be ElementSUBSET-1M1-of FinFINSUB-1K5 X holds B1 <>HIDDENR2 {}XBOOLE-0K1 & B2 <>HIDDENR2 {}XBOOLE-0K1 implies F $$SETWISEOK10\<^bsub>(X,Y)\<^esub>(B1 \\/SETWISEOK8\<^bsub>(X)\<^esub> B2,f) =XBOOLE-0R4 F .BINOP-1K4\<^bsub>(Y)\<^esub>(F $$SETWISEOK10\<^bsub>(X,Y)\<^esub>(B1,f),F $$SETWISEOK10\<^bsub>(X,Y)\<^esub>(B2,f)))"
sorry

mtheorem setwiseo_th_22:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for Y be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for F be BinOpBINOP-1M2-of Y holds  for B be ElementSUBSET-1M1-of FinFINSUB-1K5 X holds  for f be FunctionFUNCT-2M1-of(X,Y) holds (F be commutativeBINOP-1V1\<^bsub>(Y)\<^esub> & F be associativeBINOP-1V2\<^bsub>(Y)\<^esub>) & F be idempotentBINOP-1V3\<^bsub>(Y)\<^esub> implies ( for x be ElementSUBSET-1M1-of X holds x inTARSKIR2 B implies F .BINOP-1K4\<^bsub>(Y)\<^esub>(f .FUNCT-2K3\<^bsub>(X,Y)\<^esub> x,F $$SETWISEOK10\<^bsub>(X,Y)\<^esub>(B,f)) =XBOOLE-0R4 F $$SETWISEOK10\<^bsub>(X,Y)\<^esub>(B,f))"
sorry

mtheorem setwiseo_th_23:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for Y be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for F be BinOpBINOP-1M2-of Y holds  for f be FunctionFUNCT-2M1-of(X,Y) holds (F be commutativeBINOP-1V1\<^bsub>(Y)\<^esub> & F be associativeBINOP-1V2\<^bsub>(Y)\<^esub>) & F be idempotentBINOP-1V3\<^bsub>(Y)\<^esub> implies ( for B be ElementSUBSET-1M1-of FinFINSUB-1K5 X holds  for C be ElementSUBSET-1M1-of FinFINSUB-1K5 X holds B <>HIDDENR2 {}XBOOLE-0K1 & B c=TARSKIR1 C implies F .BINOP-1K4\<^bsub>(Y)\<^esub>(F $$SETWISEOK10\<^bsub>(X,Y)\<^esub>(B,f),F $$SETWISEOK10\<^bsub>(X,Y)\<^esub>(C,f)) =XBOOLE-0R4 F $$SETWISEOK10\<^bsub>(X,Y)\<^esub>(C,f))"
sorry

mtheorem setwiseo_th_24:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for Y be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for F be BinOpBINOP-1M2-of Y holds  for B be ElementSUBSET-1M1-of FinFINSUB-1K5 X holds  for f be FunctionFUNCT-2M1-of(X,Y) holds ((B <>HIDDENR2 {}XBOOLE-0K1 & F be commutativeBINOP-1V1\<^bsub>(Y)\<^esub>) & F be associativeBINOP-1V2\<^bsub>(Y)\<^esub>) & F be idempotentBINOP-1V3\<^bsub>(Y)\<^esub> implies ( for a be ElementSUBSET-1M1-of Y holds ( for b be ElementSUBSET-1M1-of X holds b inTARSKIR2 B implies f .FUNCT-2K3\<^bsub>(X,Y)\<^esub> b =XBOOLE-0R4 a) implies F $$SETWISEOK10\<^bsub>(X,Y)\<^esub>(B,f) =XBOOLE-0R4 a)"
sorry

mtheorem setwiseo_th_25:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for Y be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for F be BinOpBINOP-1M2-of Y holds  for B be ElementSUBSET-1M1-of FinFINSUB-1K5 X holds  for f be FunctionFUNCT-2M1-of(X,Y) holds (F be commutativeBINOP-1V1\<^bsub>(Y)\<^esub> & F be associativeBINOP-1V2\<^bsub>(Y)\<^esub>) & F be idempotentBINOP-1V3\<^bsub>(Y)\<^esub> implies ( for a be ElementSUBSET-1M1-of Y holds f .:RELSET-1K7\<^bsub>(X,Y)\<^esub> B =XBOOLE-0R4 {TARSKIK1 a} implies F $$SETWISEOK10\<^bsub>(X,Y)\<^esub>(B,f) =XBOOLE-0R4 a)"
sorry

mtheorem setwiseo_th_26:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for Y be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for F be BinOpBINOP-1M2-of Y holds (F be commutativeBINOP-1V1\<^bsub>(Y)\<^esub> & F be associativeBINOP-1V2\<^bsub>(Y)\<^esub>) & F be idempotentBINOP-1V3\<^bsub>(Y)\<^esub> implies ( for f be FunctionFUNCT-2M1-of(X,Y) holds  for g be FunctionFUNCT-2M1-of(X,Y) holds  for A be ElementSUBSET-1M1-of FinFINSUB-1K5 X holds  for B be ElementSUBSET-1M1-of FinFINSUB-1K5 X holds A <>HIDDENR2 {}XBOOLE-0K1 & f .:RELSET-1K7\<^bsub>(X,Y)\<^esub> A =XBOOLE-0R4 g .:RELSET-1K7\<^bsub>(X,Y)\<^esub> B implies F $$SETWISEOK10\<^bsub>(X,Y)\<^esub>(A,f) =XBOOLE-0R4 F $$SETWISEOK10\<^bsub>(X,Y)\<^esub>(B,g))"
sorry

mtheorem setwiseo_th_27:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for Y be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for F be BinOpBINOP-1M2-of Y holds  for G be BinOpBINOP-1M2-of Y holds ((F be idempotentBINOP-1V3\<^bsub>(Y)\<^esub> & F be commutativeBINOP-1V1\<^bsub>(Y)\<^esub>) & F be associativeBINOP-1V2\<^bsub>(Y)\<^esub>) & G is-distributive-wrtBINOP-1R6\<^bsub>(Y)\<^esub> F implies ( for B be ElementSUBSET-1M1-of FinFINSUB-1K5 X holds B <>HIDDENR2 {}XBOOLE-0K1 implies ( for f be FunctionFUNCT-2M1-of(X,Y) holds  for a be ElementSUBSET-1M1-of Y holds G .BINOP-1K4\<^bsub>(Y)\<^esub>(a,F $$SETWISEOK10\<^bsub>(X,Y)\<^esub>(B,f)) =XBOOLE-0R4 F $$SETWISEOK10\<^bsub>(X,Y)\<^esub>(B,G [;]FUNCOP-1K10\<^bsub>(Y,X)\<^esub>(a,f))))"
sorry

mtheorem setwiseo_th_28:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for Y be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for F be BinOpBINOP-1M2-of Y holds  for G be BinOpBINOP-1M2-of Y holds ((F be idempotentBINOP-1V3\<^bsub>(Y)\<^esub> & F be commutativeBINOP-1V1\<^bsub>(Y)\<^esub>) & F be associativeBINOP-1V2\<^bsub>(Y)\<^esub>) & G is-distributive-wrtBINOP-1R6\<^bsub>(Y)\<^esub> F implies ( for B be ElementSUBSET-1M1-of FinFINSUB-1K5 X holds B <>HIDDENR2 {}XBOOLE-0K1 implies ( for f be FunctionFUNCT-2M1-of(X,Y) holds  for a be ElementSUBSET-1M1-of Y holds G .BINOP-1K4\<^bsub>(Y)\<^esub>(F $$SETWISEOK10\<^bsub>(X,Y)\<^esub>(B,f),a) =XBOOLE-0R4 F $$SETWISEOK10\<^bsub>(X,Y)\<^esub>(B,G [:]FUNCOP-1K9\<^bsub>(Y,X)\<^esub>(f,a))))"
sorry

syntax SETWISEOK11 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ .:SETWISEOK11\<^bsub>'( _ , _ ')\<^esub>  _ " [200,0,0,200]200)
translations "f .:SETWISEOK11\<^bsub>(X,Y)\<^esub> A" \<rightharpoonup> "f .:RELAT-1K10 A"

mtheorem setwiseo_add_6:
  mlet "X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "Y be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "f be FunctionFUNCT-2M1-of(X,Y)", "A be ElementSUBSET-1M1-of FinFINSUB-1K5 X"
"cluster f .:RELAT-1K10 A as-term-is ElementSUBSET-1M1-of FinFINSUB-1K5 Y"
proof
(*coherence*)
  show "f .:RELAT-1K10 A be ElementSUBSET-1M1-of FinFINSUB-1K5 Y"
    using setwiseo_lm_1 sorry
qed "sorry"

mtheorem setwiseo_th_29:
" for A be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for Y be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for F be BinOpBINOP-1M2-of A holds (F be idempotentBINOP-1V3\<^bsub>(A)\<^esub> & F be commutativeBINOP-1V1\<^bsub>(A)\<^esub>) & F be associativeBINOP-1V2\<^bsub>(A)\<^esub> implies ( for B be ElementSUBSET-1M1-of FinFINSUB-1K5 X holds B <>HIDDENR2 {}XBOOLE-0K1 implies ( for f be FunctionFUNCT-2M1-of(X,Y) holds  for g be FunctionFUNCT-2M1-of(Y,A) holds F $$SETWISEOK10\<^bsub>(Y,A)\<^esub>(f .:SETWISEOK11\<^bsub>(X,Y)\<^esub> B,g) =XBOOLE-0R4 F $$SETWISEOK10\<^bsub>(X,A)\<^esub>(B,g *PARTFUN1K1\<^bsub>(X,Y,Y,A)\<^esub> f)))"
sorry

mtheorem setwiseo_th_30:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for Y be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for F be BinOpBINOP-1M2-of Y holds (F be commutativeBINOP-1V1\<^bsub>(Y)\<^esub> & F be associativeBINOP-1V2\<^bsub>(Y)\<^esub>) & F be idempotentBINOP-1V3\<^bsub>(Y)\<^esub> implies ( for Z be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for G be BinOpBINOP-1M2-of Z holds (G be commutativeBINOP-1V1\<^bsub>(Z)\<^esub> & G be associativeBINOP-1V2\<^bsub>(Z)\<^esub>) & G be idempotentBINOP-1V3\<^bsub>(Z)\<^esub> implies ( for f be FunctionFUNCT-2M1-of(X,Y) holds  for g be FunctionFUNCT-2M1-of(Y,Z) holds ( for x be ElementSUBSET-1M1-of Y holds  for y be ElementSUBSET-1M1-of Y holds g .FUNCT-2K3\<^bsub>(Y,Z)\<^esub> (F .BINOP-1K4\<^bsub>(Y)\<^esub>(x,y)) =XBOOLE-0R4 G .BINOP-1K4\<^bsub>(Z)\<^esub>(g .FUNCT-2K3\<^bsub>(Y,Z)\<^esub> x,g .FUNCT-2K3\<^bsub>(Y,Z)\<^esub> y)) implies ( for B be ElementSUBSET-1M1-of FinFINSUB-1K5 X holds B <>HIDDENR2 {}XBOOLE-0K1 implies g .FUNCT-2K3\<^bsub>(Y,Z)\<^esub> (F $$SETWISEOK10\<^bsub>(X,Y)\<^esub>(B,f)) =XBOOLE-0R4 G $$SETWISEOK10\<^bsub>(X,Z)\<^esub>(B,g *PARTFUN1K1\<^bsub>(X,Y,Y,Z)\<^esub> f))))"
sorry

mtheorem setwiseo_th_31:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for Y be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for F be BinOpBINOP-1M2-of Y holds (F be commutativeBINOP-1V1\<^bsub>(Y)\<^esub> & F be associativeBINOP-1V2\<^bsub>(Y)\<^esub>) & F be having-a-unitySETWISEOV1\<^bsub>(Y)\<^esub> implies ( for f be FunctionFUNCT-2M1-of(X,Y) holds F $$SETWISEOK10\<^bsub>(X,Y)\<^esub>({}.SETWISEOK1 X,f) =XBOOLE-0R4 the-unity-wrtBINOP-1K3\<^bsub>(Y)\<^esub> F)"
sorry

mtheorem setwiseo_th_32:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for Y be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for F be BinOpBINOP-1M2-of Y holds  for B be ElementSUBSET-1M1-of FinFINSUB-1K5 X holds  for f be FunctionFUNCT-2M1-of(X,Y) holds ((F be idempotentBINOP-1V3\<^bsub>(Y)\<^esub> & F be commutativeBINOP-1V1\<^bsub>(Y)\<^esub>) & F be associativeBINOP-1V2\<^bsub>(Y)\<^esub>) & F be having-a-unitySETWISEOV1\<^bsub>(Y)\<^esub> implies ( for x be ElementSUBSET-1M1-of X holds F $$SETWISEOK10\<^bsub>(X,Y)\<^esub>(B \\/SETWISEOK8\<^bsub>(X)\<^esub> {.SETWISEOK5\<^bsub>(X)\<^esub> x.},f) =XBOOLE-0R4 F .BINOP-1K4\<^bsub>(Y)\<^esub>(F $$SETWISEOK10\<^bsub>(X,Y)\<^esub>(B,f),f .FUNCT-2K3\<^bsub>(X,Y)\<^esub> x))"
sorry

mtheorem setwiseo_th_33:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for Y be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for F be BinOpBINOP-1M2-of Y holds  for f be FunctionFUNCT-2M1-of(X,Y) holds ((F be idempotentBINOP-1V3\<^bsub>(Y)\<^esub> & F be commutativeBINOP-1V1\<^bsub>(Y)\<^esub>) & F be associativeBINOP-1V2\<^bsub>(Y)\<^esub>) & F be having-a-unitySETWISEOV1\<^bsub>(Y)\<^esub> implies ( for B1 be ElementSUBSET-1M1-of FinFINSUB-1K5 X holds  for B2 be ElementSUBSET-1M1-of FinFINSUB-1K5 X holds F $$SETWISEOK10\<^bsub>(X,Y)\<^esub>(B1 \\/SETWISEOK8\<^bsub>(X)\<^esub> B2,f) =XBOOLE-0R4 F .BINOP-1K4\<^bsub>(Y)\<^esub>(F $$SETWISEOK10\<^bsub>(X,Y)\<^esub>(B1,f),F $$SETWISEOK10\<^bsub>(X,Y)\<^esub>(B2,f)))"
sorry

mtheorem setwiseo_th_34:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for Y be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for F be BinOpBINOP-1M2-of Y holds ((F be commutativeBINOP-1V1\<^bsub>(Y)\<^esub> & F be associativeBINOP-1V2\<^bsub>(Y)\<^esub>) & F be idempotentBINOP-1V3\<^bsub>(Y)\<^esub>) & F be having-a-unitySETWISEOV1\<^bsub>(Y)\<^esub> implies ( for f be FunctionFUNCT-2M1-of(X,Y) holds  for g be FunctionFUNCT-2M1-of(X,Y) holds  for A be ElementSUBSET-1M1-of FinFINSUB-1K5 X holds  for B be ElementSUBSET-1M1-of FinFINSUB-1K5 X holds f .:SETWISEOK11\<^bsub>(X,Y)\<^esub> A =XBOOLE-0R4 g .:SETWISEOK11\<^bsub>(X,Y)\<^esub> B implies F $$SETWISEOK10\<^bsub>(X,Y)\<^esub>(A,f) =XBOOLE-0R4 F $$SETWISEOK10\<^bsub>(X,Y)\<^esub>(B,g))"
sorry

mtheorem setwiseo_th_35:
" for A be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for Y be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for F be BinOpBINOP-1M2-of A holds ((F be idempotentBINOP-1V3\<^bsub>(A)\<^esub> & F be commutativeBINOP-1V1\<^bsub>(A)\<^esub>) & F be associativeBINOP-1V2\<^bsub>(A)\<^esub>) & F be having-a-unitySETWISEOV1\<^bsub>(A)\<^esub> implies ( for B be ElementSUBSET-1M1-of FinFINSUB-1K5 X holds  for f be FunctionFUNCT-2M1-of(X,Y) holds  for g be FunctionFUNCT-2M1-of(Y,A) holds F $$SETWISEOK10\<^bsub>(Y,A)\<^esub>(f .:SETWISEOK11\<^bsub>(X,Y)\<^esub> B,g) =XBOOLE-0R4 F $$SETWISEOK10\<^bsub>(X,A)\<^esub>(B,g *PARTFUN1K1\<^bsub>(X,Y,Y,A)\<^esub> f))"
sorry

mtheorem setwiseo_th_36:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for Y be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for F be BinOpBINOP-1M2-of Y holds ((F be commutativeBINOP-1V1\<^bsub>(Y)\<^esub> & F be associativeBINOP-1V2\<^bsub>(Y)\<^esub>) & F be idempotentBINOP-1V3\<^bsub>(Y)\<^esub>) & F be having-a-unitySETWISEOV1\<^bsub>(Y)\<^esub> implies ( for Z be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for G be BinOpBINOP-1M2-of Z holds ((G be commutativeBINOP-1V1\<^bsub>(Z)\<^esub> & G be associativeBINOP-1V2\<^bsub>(Z)\<^esub>) & G be idempotentBINOP-1V3\<^bsub>(Z)\<^esub>) & G be having-a-unitySETWISEOV1\<^bsub>(Z)\<^esub> implies ( for f be FunctionFUNCT-2M1-of(X,Y) holds  for g be FunctionFUNCT-2M1-of(Y,Z) holds g .FUNCT-2K3\<^bsub>(Y,Z)\<^esub> the-unity-wrtBINOP-1K3\<^bsub>(Y)\<^esub> F =XBOOLE-0R4 the-unity-wrtBINOP-1K3\<^bsub>(Z)\<^esub> G & ( for x be ElementSUBSET-1M1-of Y holds  for y be ElementSUBSET-1M1-of Y holds g .FUNCT-2K3\<^bsub>(Y,Z)\<^esub> (F .BINOP-1K4\<^bsub>(Y)\<^esub>(x,y)) =XBOOLE-0R4 G .BINOP-1K4\<^bsub>(Z)\<^esub>(g .FUNCT-2K3\<^bsub>(Y,Z)\<^esub> x,g .FUNCT-2K3\<^bsub>(Y,Z)\<^esub> y)) implies ( for B be ElementSUBSET-1M1-of FinFINSUB-1K5 X holds g .FUNCT-2K3\<^bsub>(Y,Z)\<^esub> (F $$SETWISEOK10\<^bsub>(X,Y)\<^esub>(B,f)) =XBOOLE-0R4 G $$SETWISEOK10\<^bsub>(X,Z)\<^esub>(B,g *PARTFUN1K1\<^bsub>(X,Y,Y,Z)\<^esub> f))))"
sorry

mdef setwiseo_def_4 ("FinUnionSETWISEOK12  _ " [250]250 ) where
  mlet "A be setHIDDENM2"
"func FinUnionSETWISEOK12 A \<rightarrow> BinOpBINOP-1M2-of FinFINSUB-1K5 A means
  \<lambda>it.  for x be ElementSUBSET-1M1-of FinFINSUB-1K5 A holds  for y be ElementSUBSET-1M1-of FinFINSUB-1K5 A holds it .BINOP-1K4\<^bsub>(FinFINSUB-1K5 A)\<^esub>(x,y) =XBOOLE-0R4 x \\/SETWISEOK8\<^bsub>(A)\<^esub> y"
proof-
  (*existence*)
    show " ex it be BinOpBINOP-1M2-of FinFINSUB-1K5 A st  for x be ElementSUBSET-1M1-of FinFINSUB-1K5 A holds  for y be ElementSUBSET-1M1-of FinFINSUB-1K5 A holds it .BINOP-1K4\<^bsub>(FinFINSUB-1K5 A)\<^esub>(x,y) =XBOOLE-0R4 x \\/SETWISEOK8\<^bsub>(A)\<^esub> y"
sorry
  (*uniqueness*)
    show " for it1 be BinOpBINOP-1M2-of FinFINSUB-1K5 A holds  for it2 be BinOpBINOP-1M2-of FinFINSUB-1K5 A holds ( for x be ElementSUBSET-1M1-of FinFINSUB-1K5 A holds  for y be ElementSUBSET-1M1-of FinFINSUB-1K5 A holds it1 .BINOP-1K4\<^bsub>(FinFINSUB-1K5 A)\<^esub>(x,y) =XBOOLE-0R4 x \\/SETWISEOK8\<^bsub>(A)\<^esub> y) & ( for x be ElementSUBSET-1M1-of FinFINSUB-1K5 A holds  for y be ElementSUBSET-1M1-of FinFINSUB-1K5 A holds it2 .BINOP-1K4\<^bsub>(FinFINSUB-1K5 A)\<^esub>(x,y) =XBOOLE-0R4 x \\/SETWISEOK8\<^bsub>(A)\<^esub> y) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

reserve A for "setHIDDENM2"
reserve x, y, z for "ElementSUBSET-1M1-of FinFINSUB-1K5 A"
mtheorem setwiseo_th_37:
" for A be setHIDDENM2 holds FinUnionSETWISEOK12 A be idempotentBINOP-1V3\<^bsub>(FinFINSUB-1K5 A)\<^esub>"
sorry

mtheorem setwiseo_th_38:
" for A be setHIDDENM2 holds FinUnionSETWISEOK12 A be commutativeBINOP-1V1\<^bsub>(FinFINSUB-1K5 A)\<^esub>"
sorry

mtheorem setwiseo_th_39:
" for A be setHIDDENM2 holds FinUnionSETWISEOK12 A be associativeBINOP-1V2\<^bsub>(FinFINSUB-1K5 A)\<^esub>"
sorry

mtheorem setwiseo_th_40:
" for A be setHIDDENM2 holds {}.SETWISEOK1 A is-a-unity-wrtBINOP-1R3\<^bsub>(FinFINSUB-1K5 A)\<^esub> FinUnionSETWISEOK12 A"
sorry

mtheorem setwiseo_th_41:
" for A be setHIDDENM2 holds FinUnionSETWISEOK12 A be having-a-unitySETWISEOV1\<^bsub>(FinFINSUB-1K5 A)\<^esub>"
sorry

mtheorem setwiseo_th_42:
" for A be setHIDDENM2 holds the-unity-wrtBINOP-1K3\<^bsub>(FinFINSUB-1K5 A)\<^esub> FinUnionSETWISEOK12 A is-a-unity-wrtBINOP-1R3\<^bsub>(FinFINSUB-1K5 A)\<^esub> FinUnionSETWISEOK12 A"
  using setwiseo_th_14 setwiseo_th_41 sorry

mtheorem setwiseo_th_43:
" for A be setHIDDENM2 holds the-unity-wrtBINOP-1K3\<^bsub>(FinFINSUB-1K5 A)\<^esub> FinUnionSETWISEOK12 A =XBOOLE-0R4 {}XBOOLE-0K1"
sorry

reserve X, Y for " non emptyXBOOLE-0V1\<bar>setHIDDENM2"
reserve A for "setHIDDENM2"
reserve f for "FunctionFUNCT-2M1-of(X,FinFINSUB-1K5 A)"
reserve i, j, k for "ElementSUBSET-1M1-of X"
mdef setwiseo_def_5 ("FinUnionSETWISEOK13\<^bsub>'( _ , _ ')\<^esub>'( _ , _ ')" [0,0,0,0]250 ) where
  mlet "X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "A be setHIDDENM2", "B be ElementSUBSET-1M1-of FinFINSUB-1K5 X", "f be FunctionFUNCT-2M1-of(X,FinFINSUB-1K5 A)"
"func FinUnionSETWISEOK13\<^bsub>(X,A)\<^esub>(B,f) \<rightarrow> ElementSUBSET-1M1-of FinFINSUB-1K5 A equals
  FinUnionSETWISEOK12 A $$SETWISEOK10\<^bsub>(X,FinFINSUB-1K5 A)\<^esub>(B,f)"
proof-
  (*coherence*)
    show "FinUnionSETWISEOK12 A $$SETWISEOK10\<^bsub>(X,FinFINSUB-1K5 A)\<^esub>(B,f) be ElementSUBSET-1M1-of FinFINSUB-1K5 A"
       sorry
qed "sorry"

mtheorem setwiseo_th_44:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for A be setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(X,FinFINSUB-1K5 A) holds  for i be ElementSUBSET-1M1-of X holds FinUnionSETWISEOK13\<^bsub>(X,A)\<^esub>({.SETWISEOK5\<^bsub>(X)\<^esub> i.},f) =XBOOLE-0R4 f .FUNCT-2K3\<^bsub>(X,FinFINSUB-1K5 A)\<^esub> i"
sorry

mtheorem setwiseo_th_45:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for A be setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(X,FinFINSUB-1K5 A) holds  for i be ElementSUBSET-1M1-of X holds  for j be ElementSUBSET-1M1-of X holds FinUnionSETWISEOK13\<^bsub>(X,A)\<^esub>({.SETWISEOK6\<^bsub>(X)\<^esub> i,j .},f) =XBOOLE-0R4 f .FUNCT-2K3\<^bsub>(X,FinFINSUB-1K5 A)\<^esub> i \\/SETWISEOK8\<^bsub>(A)\<^esub> f .FUNCT-2K3\<^bsub>(X,FinFINSUB-1K5 A)\<^esub> j"
sorry

mtheorem setwiseo_th_46:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for A be setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(X,FinFINSUB-1K5 A) holds  for i be ElementSUBSET-1M1-of X holds  for j be ElementSUBSET-1M1-of X holds  for k be ElementSUBSET-1M1-of X holds FinUnionSETWISEOK13\<^bsub>(X,A)\<^esub>({.SETWISEOK7\<^bsub>(X)\<^esub> i,j,k .},f) =XBOOLE-0R4 (f .FUNCT-2K3\<^bsub>(X,FinFINSUB-1K5 A)\<^esub> i \\/SETWISEOK8\<^bsub>(A)\<^esub> f .FUNCT-2K3\<^bsub>(X,FinFINSUB-1K5 A)\<^esub> j)\\/SETWISEOK8\<^bsub>(A)\<^esub> f .FUNCT-2K3\<^bsub>(X,FinFINSUB-1K5 A)\<^esub> k"
sorry

mtheorem setwiseo_th_47:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for A be setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(X,FinFINSUB-1K5 A) holds FinUnionSETWISEOK13\<^bsub>(X,A)\<^esub>({}.SETWISEOK1 X,f) =XBOOLE-0R4 {}XBOOLE-0K1"
sorry

mtheorem setwiseo_th_48:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for A be setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(X,FinFINSUB-1K5 A) holds  for i be ElementSUBSET-1M1-of X holds  for B be ElementSUBSET-1M1-of FinFINSUB-1K5 X holds FinUnionSETWISEOK13\<^bsub>(X,A)\<^esub>(B \\/SETWISEOK8\<^bsub>(X)\<^esub> {.SETWISEOK5\<^bsub>(X)\<^esub> i.},f) =XBOOLE-0R4 FinUnionSETWISEOK13\<^bsub>(X,A)\<^esub>(B,f) \\/SETWISEOK8\<^bsub>(A)\<^esub> f .FUNCT-2K3\<^bsub>(X,FinFINSUB-1K5 A)\<^esub> i"
sorry

mtheorem setwiseo_th_49:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for A be setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(X,FinFINSUB-1K5 A) holds  for B be ElementSUBSET-1M1-of FinFINSUB-1K5 X holds FinUnionSETWISEOK13\<^bsub>(X,A)\<^esub>(B,f) =XBOOLE-0R4 unionTARSKIK3 (f .:SETWISEOK11\<^bsub>(X,FinFINSUB-1K5 A)\<^esub> B)"
sorry

mtheorem setwiseo_th_50:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for A be setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(X,FinFINSUB-1K5 A) holds  for B1 be ElementSUBSET-1M1-of FinFINSUB-1K5 X holds  for B2 be ElementSUBSET-1M1-of FinFINSUB-1K5 X holds FinUnionSETWISEOK13\<^bsub>(X,A)\<^esub>(B1 \\/SETWISEOK8\<^bsub>(X)\<^esub> B2,f) =XBOOLE-0R4 FinUnionSETWISEOK13\<^bsub>(X,A)\<^esub>(B1,f) \\/SETWISEOK8\<^bsub>(A)\<^esub> FinUnionSETWISEOK13\<^bsub>(X,A)\<^esub>(B2,f)"
sorry

mtheorem setwiseo_th_51:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for Y be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for A be setHIDDENM2 holds  for B be ElementSUBSET-1M1-of FinFINSUB-1K5 X holds  for f be FunctionFUNCT-2M1-of(X,Y) holds  for g be FunctionFUNCT-2M1-of(Y,FinFINSUB-1K5 A) holds FinUnionSETWISEOK13\<^bsub>(Y,A)\<^esub>(f .:SETWISEOK11\<^bsub>(X,Y)\<^esub> B,g) =XBOOLE-0R4 FinUnionSETWISEOK13\<^bsub>(X,A)\<^esub>(B,g *PARTFUN1K1\<^bsub>(X,Y,Y,FinFINSUB-1K5 A)\<^esub> f)"
sorry

mtheorem setwiseo_th_52:
" for A be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for Y be setHIDDENM2 holds  for G be BinOpBINOP-1M2-of A holds (G be commutativeBINOP-1V1\<^bsub>(A)\<^esub> & G be associativeBINOP-1V2\<^bsub>(A)\<^esub>) & G be idempotentBINOP-1V3\<^bsub>(A)\<^esub> implies ( for B be ElementSUBSET-1M1-of FinFINSUB-1K5 X holds B <>HIDDENR2 {}XBOOLE-0K1 implies ( for f be FunctionFUNCT-2M1-of(X,FinFINSUB-1K5 Y) holds  for g be FunctionFUNCT-2M1-of(FinFINSUB-1K5 Y,A) holds ( for x be ElementSUBSET-1M1-of FinFINSUB-1K5 Y holds  for y be ElementSUBSET-1M1-of FinFINSUB-1K5 Y holds g .FUNCT-2K3\<^bsub>(FinFINSUB-1K5 Y,A)\<^esub> (x \\/SETWISEOK8\<^bsub>(Y)\<^esub> y) =XBOOLE-0R4 G .BINOP-1K4\<^bsub>(A)\<^esub>(g .FUNCT-2K3\<^bsub>(FinFINSUB-1K5 Y,A)\<^esub> x,g .FUNCT-2K3\<^bsub>(FinFINSUB-1K5 Y,A)\<^esub> y)) implies g .FUNCT-2K3\<^bsub>(FinFINSUB-1K5 Y,A)\<^esub> FinUnionSETWISEOK13\<^bsub>(X,Y)\<^esub>(B,f) =XBOOLE-0R4 G $$SETWISEOK10\<^bsub>(X,A)\<^esub>(B,g *PARTFUN1K1\<^bsub>(X,FinFINSUB-1K5 Y,FinFINSUB-1K5 Y,A)\<^esub> f)))"
sorry

mtheorem setwiseo_th_53:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for Z be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for Y be setHIDDENM2 holds  for G be BinOpBINOP-1M2-of Z holds ((G be commutativeBINOP-1V1\<^bsub>(Z)\<^esub> & G be associativeBINOP-1V2\<^bsub>(Z)\<^esub>) & G be idempotentBINOP-1V3\<^bsub>(Z)\<^esub>) & G be having-a-unitySETWISEOV1\<^bsub>(Z)\<^esub> implies ( for f be FunctionFUNCT-2M1-of(X,FinFINSUB-1K5 Y) holds  for g be FunctionFUNCT-2M1-of(FinFINSUB-1K5 Y,Z) holds g .FUNCT-2K3\<^bsub>(FinFINSUB-1K5 Y,Z)\<^esub> {}.SETWISEOK1 Y =XBOOLE-0R4 the-unity-wrtBINOP-1K3\<^bsub>(Z)\<^esub> G & ( for x be ElementSUBSET-1M1-of FinFINSUB-1K5 Y holds  for y be ElementSUBSET-1M1-of FinFINSUB-1K5 Y holds g .FUNCT-2K3\<^bsub>(FinFINSUB-1K5 Y,Z)\<^esub> (x \\/SETWISEOK8\<^bsub>(Y)\<^esub> y) =XBOOLE-0R4 G .BINOP-1K4\<^bsub>(Z)\<^esub>(g .FUNCT-2K3\<^bsub>(FinFINSUB-1K5 Y,Z)\<^esub> x,g .FUNCT-2K3\<^bsub>(FinFINSUB-1K5 Y,Z)\<^esub> y)) implies ( for B be ElementSUBSET-1M1-of FinFINSUB-1K5 X holds g .FUNCT-2K3\<^bsub>(FinFINSUB-1K5 Y,Z)\<^esub> FinUnionSETWISEOK13\<^bsub>(X,Y)\<^esub>(B,f) =XBOOLE-0R4 G $$SETWISEOK10\<^bsub>(X,Z)\<^esub>(B,g *PARTFUN1K1\<^bsub>(X,FinFINSUB-1K5 Y,FinFINSUB-1K5 Y,Z)\<^esub> f)))"
sorry

mdef setwiseo_def_6 ("singletonSETWISEOK14  _ " [250]250 ) where
  mlet "A be setHIDDENM2"
"func singletonSETWISEOK14 A \<rightarrow> FunctionFUNCT-2M1-of(A,FinFINSUB-1K5 A) means
  \<lambda>it.  for x be objectHIDDENM1 holds x inHIDDENR3 A implies it .FUNCT-1K1 x =XBOOLE-0R4 {TARSKIK1 x}"
proof-
  (*existence*)
    show " ex it be FunctionFUNCT-2M1-of(A,FinFINSUB-1K5 A) st  for x be objectHIDDENM1 holds x inHIDDENR3 A implies it .FUNCT-1K1 x =XBOOLE-0R4 {TARSKIK1 x}"
sorry
  (*uniqueness*)
    show " for it1 be FunctionFUNCT-2M1-of(A,FinFINSUB-1K5 A) holds  for it2 be FunctionFUNCT-2M1-of(A,FinFINSUB-1K5 A) holds ( for x be objectHIDDENM1 holds x inHIDDENR3 A implies it1 .FUNCT-1K1 x =XBOOLE-0R4 {TARSKIK1 x}) & ( for x be objectHIDDENM1 holds x inHIDDENR3 A implies it2 .FUNCT-1K1 x =XBOOLE-0R4 {TARSKIK1 x}) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mtheorem setwiseo_th_54:
" for A be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(A,FinFINSUB-1K5 A) holds f =FUNCT-2R2\<^bsub>(A,FinFINSUB-1K5 A)\<^esub> singletonSETWISEOK14 A iff ( for x be ElementSUBSET-1M1-of A holds f .FUNCT-2K3\<^bsub>(A,FinFINSUB-1K5 A)\<^esub> x =XBOOLE-0R4 {TARSKIK1 x})"
sorry

mtheorem setwiseo_th_55:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for x be setHIDDENM2 holds  for y be ElementSUBSET-1M1-of X holds x inTARSKIR2 singletonSETWISEOK14 X .FUNCT-2K3\<^bsub>(X,FinFINSUB-1K5 X)\<^esub> y iff x =XBOOLE-0R4 y"
sorry

mtheorem setwiseo_th_56:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for x be ElementSUBSET-1M1-of X holds  for y be ElementSUBSET-1M1-of X holds  for z be ElementSUBSET-1M1-of X holds x inTARSKIR2 singletonSETWISEOK14 X .FUNCT-2K3\<^bsub>(X,FinFINSUB-1K5 X)\<^esub> z & y inTARSKIR2 singletonSETWISEOK14 X .FUNCT-2K3\<^bsub>(X,FinFINSUB-1K5 X)\<^esub> z implies x =XBOOLE-0R4 y"
sorry

mlemma setwiseo_lm_2:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X be setHIDDENM2 holds  for P be setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(X,D) holds f .:RELSET-1K7\<^bsub>(X,D)\<^esub> P c=TARSKIR1 D"
   sorry

mtheorem setwiseo_th_57:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for A be setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(X,FinFINSUB-1K5 A) holds  for B be ElementSUBSET-1M1-of FinFINSUB-1K5 X holds  for x be setHIDDENM2 holds x inTARSKIR2 FinUnionSETWISEOK13\<^bsub>(X,A)\<^esub>(B,f) iff ( ex i be ElementSUBSET-1M1-of X st i inTARSKIR2 B & x inTARSKIR2 f .FUNCT-2K3\<^bsub>(X,FinFINSUB-1K5 A)\<^esub> i)"
sorry

mtheorem setwiseo_th_58:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for B be ElementSUBSET-1M1-of FinFINSUB-1K5 X holds FinUnionSETWISEOK13\<^bsub>(X,X)\<^esub>(B,singletonSETWISEOK14 X) =XBOOLE-0R4 B"
sorry

mtheorem setwiseo_th_59:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(X,FinFINSUB-1K5 Y) holds  for g be FunctionFUNCT-2M1-of(FinFINSUB-1K5 Y,FinFINSUB-1K5 Z) holds g .FUNCT-2K3\<^bsub>(FinFINSUB-1K5 Y,FinFINSUB-1K5 Z)\<^esub> {}.SETWISEOK1 Y =XBOOLE-0R4 {}.SETWISEOK1 Z & ( for x be ElementSUBSET-1M1-of FinFINSUB-1K5 Y holds  for y be ElementSUBSET-1M1-of FinFINSUB-1K5 Y holds g .FUNCT-2K3\<^bsub>(FinFINSUB-1K5 Y,FinFINSUB-1K5 Z)\<^esub> (x \\/SETWISEOK8\<^bsub>(Y)\<^esub> y) =XBOOLE-0R4 g .FUNCT-2K3\<^bsub>(FinFINSUB-1K5 Y,FinFINSUB-1K5 Z)\<^esub> x \\/SETWISEOK8\<^bsub>(Z)\<^esub> g .FUNCT-2K3\<^bsub>(FinFINSUB-1K5 Y,FinFINSUB-1K5 Z)\<^esub> y) implies ( for B be ElementSUBSET-1M1-of FinFINSUB-1K5 X holds g .FUNCT-2K3\<^bsub>(FinFINSUB-1K5 Y,FinFINSUB-1K5 Z)\<^esub> FinUnionSETWISEOK13\<^bsub>(X,Y)\<^esub>(B,f) =XBOOLE-0R4 FinUnionSETWISEOK13\<^bsub>(X,Z)\<^esub>(B,g *PARTFUN1K1\<^bsub>(X,FinFINSUB-1K5 Y,FinFINSUB-1K5 Y,FinFINSUB-1K5 Z)\<^esub> f))"
sorry

end
