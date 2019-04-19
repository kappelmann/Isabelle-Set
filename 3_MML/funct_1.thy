theory funct_1
  imports relat_1 setfam_1
begin
(*begin*)
reserve X, X1, X2, Y, Y1, Y2 for "setHIDDENM2"
reserve p, x, x1, x2, y, y1, y2, z, z1, z2 for "objectHIDDENM1"
mdef funct_1_def_1 ("Function-likeFUNCT-1V1" 70 ) where
"attr Function-likeFUNCT-1V1 for setHIDDENM2 means
  (\<lambda>X.  for x be objectHIDDENM1 holds  for y1 be objectHIDDENM1 holds  for y2 be objectHIDDENM1 holds [TARSKIK4 x,y1 ] inHIDDENR3 X & [TARSKIK4 x,y2 ] inHIDDENR3 X implies y1 =HIDDENR1 y2)"..

mtheorem funct_1_cl_1:
"cluster emptyXBOOLE-0V1 also-is Function-likeFUNCT-1V1 for setHIDDENM2"
proof
(*coherence*)
  show " for it be setHIDDENM2 holds it be emptyXBOOLE-0V1 implies it be Function-likeFUNCT-1V1"
     sorry
qed "sorry"

mtheorem funct_1_cl_2:
"cluster Function-likeFUNCT-1V1 for RelationRELAT-1M1"
proof
(*existence*)
  show " ex it be RelationRELAT-1M1 st it be Function-likeFUNCT-1V1"
sorry
qed "sorry"

syntax FUNCT_1M1 :: "Ty" ("FunctionFUNCT-1M1" 70)
translations "FunctionFUNCT-1M1" \<rightharpoonup> "Function-likeFUNCT-1V1\<bar>RelationRELAT-1M1"

mtheorem funct_1_cl_3:
  mlet "a be objectHIDDENM1", "b be objectHIDDENM1"
"cluster {TARSKIK1 [TARSKIK4 a,b ] } as-term-is Function-likeFUNCT-1V1"
proof
(*coherence*)
  show "{TARSKIK1 [TARSKIK4 a,b ] } be Function-likeFUNCT-1V1"
sorry
qed "sorry"

reserve f, g, g1, g2, h for "FunctionFUNCT-1M1"
reserve R, S for "RelationRELAT-1M1"
theorem funct_1_sch_1:
  fixes Af0 Pp2 
  assumes
[ty]: "Af0 be setHIDDENM2" and
   A1: " for x be objectHIDDENM1 holds  for y1 be objectHIDDENM1 holds  for y2 be objectHIDDENM1 holds Pp2(x,y1) & Pp2(x,y2) implies y1 =HIDDENR1 y2"
  shows " ex f be FunctionFUNCT-1M1 st  for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds [TARSKIK4 x,y ] inHIDDENR3 f iff x inHIDDENR3 Af0 & Pp2(x,y)"
sorry

mdef funct_1_def_2 (" _ .FUNCT-1K1  _ " [200,200]200 ) where
  mlet "f be FunctionFUNCT-1M1", "x be objectHIDDENM1"
"func f .FUNCT-1K1 x \<rightarrow> setHIDDENM2 means
  \<lambda>it. [TARSKIK4 x,it ] inHIDDENR3 f if x inHIDDENR3 domRELAT-1K1 f otherwise \<lambda>it. it =XBOOLE-0R4 {}XBOOLE-0K1"
proof-
  (*existence*)
    show "(x inHIDDENR3 domRELAT-1K1 f implies ( ex it be setHIDDENM2 st [TARSKIK4 x,it ] inHIDDENR3 f)) & ( not x inHIDDENR3 domRELAT-1K1 f implies ( ex it be setHIDDENM2 st it =XBOOLE-0R4 {}XBOOLE-0K1))"
sorry
  (*uniqueness*)
    show " for it1 be setHIDDENM2 holds  for it2 be setHIDDENM2 holds (x inHIDDENR3 domRELAT-1K1 f implies ([TARSKIK4 x,it1 ] inHIDDENR3 f & [TARSKIK4 x,it2 ] inHIDDENR3 f implies it1 =HIDDENR1 it2)) & ( not x inHIDDENR3 domRELAT-1K1 f implies (it1 =XBOOLE-0R4 {}XBOOLE-0K1 & it2 =XBOOLE-0R4 {}XBOOLE-0K1 implies it1 =HIDDENR1 it2))"
      using funct_1_def_1 sorry
  (*consistency*)
    show " for it be setHIDDENM2 holds  True "
       sorry
qed "sorry"

mtheorem funct_1_th_1:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for f be FunctionFUNCT-1M1 holds [TARSKIK4 x,y ] inHIDDENR3 f iff x inHIDDENR3 domRELAT-1K1 f & y =HIDDENR1 f .FUNCT-1K1 x"
sorry

mtheorem funct_1_th_2:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds domRELAT-1K1 f =XBOOLE-0R4 domRELAT-1K1 g & ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 f implies f .FUNCT-1K1 x =XBOOLE-0R4 g .FUNCT-1K1 x) implies f =RELAT-1R1 g"
sorry

abbreviation(input) FUNCT_1K2("rngFUNCT-1K2  _ " [228]228) where
  "rngFUNCT-1K2 f \<equiv> rngRELAT-1K2 f"

mtheorem funct_1_def_3:
  mlet "f be FunctionFUNCT-1M1"
"redefine func rngFUNCT-1K2 f \<rightarrow> setHIDDENM2 means
  \<lambda>it.  for y be objectHIDDENM1 holds y inHIDDENR3 it iff ( ex x be objectHIDDENM1 st x inHIDDENR3 domRELAT-1K1 f & y =HIDDENR1 f .FUNCT-1K1 x)"
proof
(*compatibility*)
  show " for it be setHIDDENM2 holds it =HIDDENR1 rngFUNCT-1K2 f iff ( for y be objectHIDDENM1 holds y inHIDDENR3 it iff ( ex x be objectHIDDENM1 st x inHIDDENR3 domRELAT-1K1 f & y =HIDDENR1 f .FUNCT-1K1 x))"
sorry
qed "sorry"

mtheorem funct_1_th_3:
" for x be objectHIDDENM1 holds  for f be FunctionFUNCT-1M1 holds x inHIDDENR3 domRELAT-1K1 f implies f .FUNCT-1K1 x inTARSKIR2 rngFUNCT-1K2 f"
  using funct_1_def_3 sorry

mtheorem funct_1_th_4:
" for x be objectHIDDENM1 holds  for f be FunctionFUNCT-1M1 holds domRELAT-1K1 f =XBOOLE-0R4 {TARSKIK1 x} implies rngFUNCT-1K2 f =XBOOLE-0R4 {TARSKIK1 f .FUNCT-1K1 x }"
sorry

theorem funct_1_sch_2:
  fixes Af0 Pp2 
  assumes
[ty]: "Af0 be setHIDDENM2" and
   A1: " for x be objectHIDDENM1 holds  for y1 be objectHIDDENM1 holds  for y2 be objectHIDDENM1 holds (x inHIDDENR3 Af0 & Pp2(x,y1)) & Pp2(x,y2) implies y1 =HIDDENR1 y2" and
   A2: " for x be objectHIDDENM1 holds x inHIDDENR3 Af0 implies ( ex y be objectHIDDENM1 st Pp2(x,y))"
  shows " ex f be FunctionFUNCT-1M1 st domRELAT-1K1 f =XBOOLE-0R4 Af0 & ( for x be objectHIDDENM1 holds x inHIDDENR3 Af0 implies Pp2(x,f .FUNCT-1K1 x))"
sorry

theorem funct_1_sch_3:
  fixes Af0 Ff1 
  assumes
[ty]: "Af0 be setHIDDENM2" and
  [ty_func]: "\<And> x1. x1 be objectHIDDENM1 \<Longrightarrow> Ff1(x1) be objectHIDDENM1"
  shows " ex f be FunctionFUNCT-1M1 st domRELAT-1K1 f =XBOOLE-0R4 Af0 & ( for x be objectHIDDENM1 holds x inHIDDENR3 Af0 implies f .FUNCT-1K1 x =HIDDENR1 Ff1(x))"
sorry

mtheorem funct_1_th_5:
" for X be setHIDDENM2 holds X <>HIDDENR2 {}XBOOLE-0K1 implies ( for y be objectHIDDENM1 holds  ex f be FunctionFUNCT-1M1 st domRELAT-1K1 f =XBOOLE-0R4 X & rngFUNCT-1K2 f =XBOOLE-0R4 {TARSKIK1 y})"
sorry

mtheorem funct_1_th_6:
" for X be setHIDDENM2 holds ( for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds domRELAT-1K1 f =XBOOLE-0R4 X & domRELAT-1K1 g =XBOOLE-0R4 X implies f =RELAT-1R1 g) implies X =XBOOLE-0R4 {}XBOOLE-0K1"
sorry

mtheorem funct_1_th_7:
" for y be objectHIDDENM1 holds  for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds (domRELAT-1K1 f =XBOOLE-0R4 domRELAT-1K1 g & rngFUNCT-1K2 f =XBOOLE-0R4 {TARSKIK1 y}) & rngFUNCT-1K2 g =XBOOLE-0R4 {TARSKIK1 y} implies f =RELAT-1R1 g"
sorry

mtheorem funct_1_th_8:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds Y <>HIDDENR2 {}XBOOLE-0K1 or X =XBOOLE-0R4 {}XBOOLE-0K1 implies ( ex f be FunctionFUNCT-1M1 st X =XBOOLE-0R4 domRELAT-1K1 f & rngFUNCT-1K2 f c=TARSKIR1 Y)"
sorry

mtheorem funct_1_th_9:
" for Y be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds ( for y be objectHIDDENM1 holds y inHIDDENR3 Y implies ( ex x be objectHIDDENM1 st x inHIDDENR3 domRELAT-1K1 f & y =HIDDENR1 f .FUNCT-1K1 x)) implies Y c=TARSKIR1 rngFUNCT-1K2 f"
sorry

abbreviation(input) FUNCT_1K3(" _ *FUNCT-1K3  _ " [164,164]164) where
  "g *FUNCT-1K3 f \<equiv> f *RELAT-1K6 g"

mtheorem funct_1_cl_4:
  mlet "f be FunctionFUNCT-1M1", "g be FunctionFUNCT-1M1"
"cluster g *FUNCT-1K3 f as-term-is Function-likeFUNCT-1V1"
proof
(*coherence*)
  show "g *FUNCT-1K3 f be Function-likeFUNCT-1V1"
sorry
qed "sorry"

mtheorem funct_1_th_10:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds  for h be FunctionFUNCT-1M1 holds ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 h iff x inHIDDENR3 domRELAT-1K1 f & f .FUNCT-1K1 x inTARSKIR2 domRELAT-1K1 g) & ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 h implies h .FUNCT-1K1 x =XBOOLE-0R4 g .FUNCT-1K1 (f .FUNCT-1K1 x)) implies h =RELAT-1R1 g *FUNCT-1K3 f"
sorry

mtheorem funct_1_th_11:
" for x be objectHIDDENM1 holds  for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds x inHIDDENR3 domRELAT-1K1 (g *FUNCT-1K3 f) iff x inHIDDENR3 domRELAT-1K1 f & f .FUNCT-1K1 x inTARSKIR2 domRELAT-1K1 g"
sorry

mtheorem funct_1_th_12:
" for x be objectHIDDENM1 holds  for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds x inHIDDENR3 domRELAT-1K1 (g *FUNCT-1K3 f) implies (g *FUNCT-1K3 f).FUNCT-1K1 x =XBOOLE-0R4 g .FUNCT-1K1 (f .FUNCT-1K1 x)"
sorry

mtheorem funct_1_th_13:
" for x be objectHIDDENM1 holds  for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds x inHIDDENR3 domRELAT-1K1 f implies (g *FUNCT-1K3 f).FUNCT-1K1 x =XBOOLE-0R4 g .FUNCT-1K1 (f .FUNCT-1K1 x)"
sorry

mtheorem funct_1_th_14:
" for z be objectHIDDENM1 holds  for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds z inHIDDENR3 rngFUNCT-1K2 (g *FUNCT-1K3 f) implies z inHIDDENR3 rngFUNCT-1K2 g"
sorry

mtheorem funct_1_th_15:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds domRELAT-1K1 (g *FUNCT-1K3 f) =XBOOLE-0R4 domRELAT-1K1 f implies rngFUNCT-1K2 f c=TARSKIR1 domRELAT-1K1 g"
sorry

mtheorem funct_1_th_16:
" for Y be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds rngFUNCT-1K2 f c=TARSKIR1 Y & ( for g be FunctionFUNCT-1M1 holds  for h be FunctionFUNCT-1M1 holds (domRELAT-1K1 g =XBOOLE-0R4 Y & domRELAT-1K1 h =XBOOLE-0R4 Y) & g *FUNCT-1K3 f =RELAT-1R1 h *FUNCT-1K3 f implies g =RELAT-1R1 h) implies Y =XBOOLE-0R4 rngFUNCT-1K2 f"
sorry

mtheorem funct_1_cl_5:
  mlet "X be setHIDDENM2"
"cluster idRELAT-1K7 X as-term-is Function-likeFUNCT-1V1"
proof
(*coherence*)
  show "idRELAT-1K7 X be Function-likeFUNCT-1V1"
sorry
qed "sorry"

mtheorem funct_1_th_17:
" for X be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds f =RELAT-1R1 idRELAT-1K7 X iff domRELAT-1K1 f =XBOOLE-0R4 X & ( for x be objectHIDDENM1 holds x inHIDDENR3 X implies f .FUNCT-1K1 x =HIDDENR1 x)"
sorry

mtheorem funct_1_th_18:
" for X be setHIDDENM2 holds  for x be objectHIDDENM1 holds x inHIDDENR3 X implies idRELAT-1K7 X .FUNCT-1K1 x =HIDDENR1 x"
  using funct_1_th_17 sorry

mtheorem funct_1_th_19:
" for X be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds domRELAT-1K1 (f *FUNCT-1K3 idRELAT-1K7 X) =XBOOLE-0R4 domRELAT-1K1 f /\\XBOOLE-0K3 X"
sorry

mtheorem funct_1_th_20:
" for X be setHIDDENM2 holds  for x be objectHIDDENM1 holds  for f be FunctionFUNCT-1M1 holds x inHIDDENR3 domRELAT-1K1 f /\\XBOOLE-0K3 X implies f .FUNCT-1K1 x =XBOOLE-0R4 (f *FUNCT-1K3 idRELAT-1K7 X).FUNCT-1K1 x"
sorry

mtheorem funct_1_th_21:
" for Y be setHIDDENM2 holds  for x be objectHIDDENM1 holds  for f be FunctionFUNCT-1M1 holds x inHIDDENR3 domRELAT-1K1 (idRELAT-1K7 Y *FUNCT-1K3 f) iff x inHIDDENR3 domRELAT-1K1 f & f .FUNCT-1K1 x inTARSKIR2 Y"
sorry

mtheorem funct_1_th_22:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds idRELAT-1K7 X *FUNCT-1K3 idRELAT-1K7 Y =RELAT-1R1 idRELAT-1K7 (X /\\XBOOLE-0K3 Y)"
sorry

mtheorem funct_1_th_23:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds rngFUNCT-1K2 f =XBOOLE-0R4 domRELAT-1K1 g & g *FUNCT-1K3 f =RELAT-1R1 f implies g =RELAT-1R1 idRELAT-1K7 (domRELAT-1K1 g)"
sorry

mdef funct_1_def_4 ("one-to-oneFUNCT-1V2" 70 ) where
"attr one-to-oneFUNCT-1V2 for FunctionFUNCT-1M1 means
  (\<lambda>f.  for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds (x1 inHIDDENR3 domRELAT-1K1 f & x2 inHIDDENR3 domRELAT-1K1 f) & f .FUNCT-1K1 x1 =XBOOLE-0R4 f .FUNCT-1K1 x2 implies x1 =HIDDENR1 x2)"..

mtheorem funct_1_th_24:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds f be one-to-oneFUNCT-1V2 & g be one-to-oneFUNCT-1V2 implies g *FUNCT-1K3 f be one-to-oneFUNCT-1V2"
sorry

mtheorem funct_1_th_25:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds g *FUNCT-1K3 f be one-to-oneFUNCT-1V2 & rngFUNCT-1K2 f c=TARSKIR1 domRELAT-1K1 g implies f be one-to-oneFUNCT-1V2"
sorry

mtheorem funct_1_th_26:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds g *FUNCT-1K3 f be one-to-oneFUNCT-1V2 & rngFUNCT-1K2 f =XBOOLE-0R4 domRELAT-1K1 g implies f be one-to-oneFUNCT-1V2 & g be one-to-oneFUNCT-1V2"
sorry

mtheorem funct_1_th_27:
" for f be FunctionFUNCT-1M1 holds f be one-to-oneFUNCT-1V2 iff ( for g be FunctionFUNCT-1M1 holds  for h be FunctionFUNCT-1M1 holds ((rngFUNCT-1K2 g c=TARSKIR1 domRELAT-1K1 f & rngFUNCT-1K2 h c=TARSKIR1 domRELAT-1K1 f) & domRELAT-1K1 g =XBOOLE-0R4 domRELAT-1K1 h) & f *FUNCT-1K3 g =RELAT-1R1 f *FUNCT-1K3 h implies g =RELAT-1R1 h)"
sorry

mtheorem funct_1_th_28:
" for X be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds (((domRELAT-1K1 f =XBOOLE-0R4 X & domRELAT-1K1 g =XBOOLE-0R4 X) & rngFUNCT-1K2 g c=TARSKIR1 X) & f be one-to-oneFUNCT-1V2) & f *FUNCT-1K3 g =RELAT-1R1 f implies g =RELAT-1R1 idRELAT-1K7 X"
sorry

mtheorem funct_1_th_29:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds rngFUNCT-1K2 (g *FUNCT-1K3 f) =XBOOLE-0R4 rngFUNCT-1K2 g & g be one-to-oneFUNCT-1V2 implies domRELAT-1K1 g c=TARSKIR1 rngFUNCT-1K2 f"
sorry

mtheorem funct_1_cl_6:
  mlet "X be setHIDDENM2"
"cluster idRELAT-1K7 X as-term-is one-to-oneFUNCT-1V2"
proof
(*coherence*)
  show "idRELAT-1K7 X be one-to-oneFUNCT-1V2"
sorry
qed "sorry"

(*\$CT*)
mtheorem funct_1_th_31:
" for f be FunctionFUNCT-1M1 holds ( ex g be FunctionFUNCT-1M1 st g *FUNCT-1K3 f =RELAT-1R1 idRELAT-1K7 (domRELAT-1K1 f)) implies f be one-to-oneFUNCT-1V2"
sorry

mtheorem funct_1_cl_7:
"cluster emptyXBOOLE-0V1 also-is one-to-oneFUNCT-1V2 for FunctionFUNCT-1M1"
proof
(*coherence*)
  show " for it be FunctionFUNCT-1M1 holds it be emptyXBOOLE-0V1 implies it be one-to-oneFUNCT-1V2"
     sorry
qed "sorry"

mtheorem funct_1_cl_8:
"cluster one-to-oneFUNCT-1V2 for FunctionFUNCT-1M1"
proof
(*existence*)
  show " ex it be FunctionFUNCT-1M1 st it be one-to-oneFUNCT-1V2"
sorry
qed "sorry"

mtheorem funct_1_cl_9:
  mlet "f be one-to-oneFUNCT-1V2\<bar>FunctionFUNCT-1M1"
"cluster f ~RELAT-1K4 as-term-is Function-likeFUNCT-1V1"
proof
(*coherence*)
  show "f ~RELAT-1K4 be Function-likeFUNCT-1V1"
sorry
qed "sorry"

mdef funct_1_def_5 (" _ \<inverse>FUNCT-1K4" [228]228 ) where
  mlet "f be FunctionFUNCT-1M1"
"assume f be one-to-oneFUNCT-1V2 func f \<inverse>FUNCT-1K4 \<rightarrow> FunctionFUNCT-1M1 equals
  f ~RELAT-1K4"
proof-
  (*coherence*)
    show "f be one-to-oneFUNCT-1V2 implies f ~RELAT-1K4 be FunctionFUNCT-1M1"
sorry
qed "sorry"

mtheorem funct_1_th_32:
" for f be FunctionFUNCT-1M1 holds f be one-to-oneFUNCT-1V2 implies ( for g be FunctionFUNCT-1M1 holds g =RELAT-1R1 f \<inverse>FUNCT-1K4 iff domRELAT-1K1 g =XBOOLE-0R4 rngFUNCT-1K2 f & ( for y be objectHIDDENM1 holds  for x be objectHIDDENM1 holds y inHIDDENR3 rngFUNCT-1K2 f & x =HIDDENR1 g .FUNCT-1K1 y iff x inHIDDENR3 domRELAT-1K1 f & y =HIDDENR1 f .FUNCT-1K1 x))"
sorry

mtheorem funct_1_th_33:
" for f be FunctionFUNCT-1M1 holds f be one-to-oneFUNCT-1V2 implies rngFUNCT-1K2 f =XBOOLE-0R4 domRELAT-1K1 (f \<inverse>FUNCT-1K4) & domRELAT-1K1 f =XBOOLE-0R4 rngFUNCT-1K2 (f \<inverse>FUNCT-1K4)"
sorry

mtheorem funct_1_th_34:
" for x be objectHIDDENM1 holds  for f be FunctionFUNCT-1M1 holds f be one-to-oneFUNCT-1V2 & x inHIDDENR3 domRELAT-1K1 f implies x =HIDDENR1 f \<inverse>FUNCT-1K4 .FUNCT-1K1 (f .FUNCT-1K1 x) & x =HIDDENR1 (f \<inverse>FUNCT-1K4 *FUNCT-1K3 f).FUNCT-1K1 x"
sorry

mtheorem funct_1_th_35:
" for y be objectHIDDENM1 holds  for f be FunctionFUNCT-1M1 holds f be one-to-oneFUNCT-1V2 & y inHIDDENR3 rngFUNCT-1K2 f implies y =HIDDENR1 f .FUNCT-1K1 (f \<inverse>FUNCT-1K4 .FUNCT-1K1 y) & y =HIDDENR1 (f *FUNCT-1K3 f \<inverse>FUNCT-1K4).FUNCT-1K1 y"
sorry

mtheorem funct_1_th_36:
" for f be FunctionFUNCT-1M1 holds f be one-to-oneFUNCT-1V2 implies domRELAT-1K1 (f \<inverse>FUNCT-1K4 *FUNCT-1K3 f) =XBOOLE-0R4 domRELAT-1K1 f & rngFUNCT-1K2 (f \<inverse>FUNCT-1K4 *FUNCT-1K3 f) =XBOOLE-0R4 domRELAT-1K1 f"
sorry

mtheorem funct_1_th_37:
" for f be FunctionFUNCT-1M1 holds f be one-to-oneFUNCT-1V2 implies domRELAT-1K1 (f *FUNCT-1K3 f \<inverse>FUNCT-1K4) =XBOOLE-0R4 rngFUNCT-1K2 f & rngFUNCT-1K2 (f *FUNCT-1K3 f \<inverse>FUNCT-1K4) =XBOOLE-0R4 rngFUNCT-1K2 f"
sorry

mtheorem funct_1_th_38:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds ((f be one-to-oneFUNCT-1V2 & domRELAT-1K1 f =XBOOLE-0R4 rngFUNCT-1K2 g) & rngFUNCT-1K2 f =XBOOLE-0R4 domRELAT-1K1 g) & ( for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 f & y inHIDDENR3 domRELAT-1K1 g implies (f .FUNCT-1K1 x =HIDDENR1 y iff g .FUNCT-1K1 y =HIDDENR1 x)) implies g =RELAT-1R1 f \<inverse>FUNCT-1K4"
sorry

mtheorem funct_1_th_39:
" for f be FunctionFUNCT-1M1 holds f be one-to-oneFUNCT-1V2 implies f \<inverse>FUNCT-1K4 *FUNCT-1K3 f =RELAT-1R1 idRELAT-1K7 (domRELAT-1K1 f) & f *FUNCT-1K3 f \<inverse>FUNCT-1K4 =RELAT-1R1 idRELAT-1K7 (rngFUNCT-1K2 f)"
sorry

mtheorem funct_1_th_40:
" for f be FunctionFUNCT-1M1 holds f be one-to-oneFUNCT-1V2 implies f \<inverse>FUNCT-1K4 be one-to-oneFUNCT-1V2"
sorry

mtheorem funct_1_cl_10:
  mlet "f be one-to-oneFUNCT-1V2\<bar>FunctionFUNCT-1M1"
"cluster f \<inverse>FUNCT-1K4 as-term-is one-to-oneFUNCT-1V2"
proof
(*coherence*)
  show "f \<inverse>FUNCT-1K4 be one-to-oneFUNCT-1V2"
    using funct_1_th_40 sorry
qed "sorry"

mtheorem funct_1_cl_11:
  mlet "f be one-to-oneFUNCT-1V2\<bar>FunctionFUNCT-1M1", "g be one-to-oneFUNCT-1V2\<bar>FunctionFUNCT-1M1"
"cluster g *FUNCT-1K3 f as-term-is one-to-oneFUNCT-1V2"
proof
(*coherence*)
  show "g *FUNCT-1K3 f be one-to-oneFUNCT-1V2"
    using funct_1_th_24 sorry
qed "sorry"

mlemma funct_1_lm_1:
" for X be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds  for g1 be FunctionFUNCT-1M1 holds  for g2 be FunctionFUNCT-1M1 holds (rngFUNCT-1K2 g2 =XBOOLE-0R4 X & f *FUNCT-1K3 g2 =RELAT-1R1 idRELAT-1K7 (domRELAT-1K1 g1)) & g1 *FUNCT-1K3 f =RELAT-1R1 idRELAT-1K7 X implies g1 =RELAT-1R1 g2"
sorry

mtheorem funct_1_th_41:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds (f be one-to-oneFUNCT-1V2 & rngFUNCT-1K2 f =XBOOLE-0R4 domRELAT-1K1 g) & g *FUNCT-1K3 f =RELAT-1R1 idRELAT-1K7 (domRELAT-1K1 f) implies g =RELAT-1R1 f \<inverse>FUNCT-1K4"
sorry

mtheorem funct_1_th_42:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds (f be one-to-oneFUNCT-1V2 & rngFUNCT-1K2 g =XBOOLE-0R4 domRELAT-1K1 f) & f *FUNCT-1K3 g =RELAT-1R1 idRELAT-1K7 (rngFUNCT-1K2 f) implies g =RELAT-1R1 f \<inverse>FUNCT-1K4"
sorry

mtheorem funct_1_th_43:
" for f be FunctionFUNCT-1M1 holds f be one-to-oneFUNCT-1V2 implies (f \<inverse>FUNCT-1K4)\<inverse>FUNCT-1K4 =RELAT-1R1 f"
sorry

mtheorem funct_1_th_44:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds f be one-to-oneFUNCT-1V2 & g be one-to-oneFUNCT-1V2 implies (g *FUNCT-1K3 f)\<inverse>FUNCT-1K4 =RELAT-1R1 f \<inverse>FUNCT-1K4 *FUNCT-1K3 g \<inverse>FUNCT-1K4"
sorry

mtheorem funct_1_th_45:
" for X be setHIDDENM2 holds (idRELAT-1K7 X)\<inverse>FUNCT-1K4 =RELAT-1R1 idRELAT-1K7 X"
sorry

mtheorem funct_1_cl_12:
  mlet "f be FunctionFUNCT-1M1", "X be setHIDDENM2"
"cluster f |RELAT-1K8 X as-term-is Function-likeFUNCT-1V1"
proof
(*coherence*)
  show "f |RELAT-1K8 X be Function-likeFUNCT-1V1"
sorry
qed "sorry"

mtheorem funct_1_th_46:
" for X be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds domRELAT-1K1 g =XBOOLE-0R4 domRELAT-1K1 f /\\XBOOLE-0K3 X & ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 g implies g .FUNCT-1K1 x =XBOOLE-0R4 f .FUNCT-1K1 x) implies g =RELAT-1R1 f |RELAT-1K8 X"
sorry

mtheorem funct_1_th_47:
" for X be setHIDDENM2 holds  for x be objectHIDDENM1 holds  for f be FunctionFUNCT-1M1 holds x inHIDDENR3 domRELAT-1K1 (f |RELAT-1K8 X) implies (f |RELAT-1K8 X).FUNCT-1K1 x =XBOOLE-0R4 f .FUNCT-1K1 x"
sorry

mtheorem funct_1_th_48:
" for X be setHIDDENM2 holds  for x be objectHIDDENM1 holds  for f be FunctionFUNCT-1M1 holds x inHIDDENR3 domRELAT-1K1 f /\\XBOOLE-0K3 X implies (f |RELAT-1K8 X).FUNCT-1K1 x =XBOOLE-0R4 f .FUNCT-1K1 x"
sorry

mtheorem funct_1_th_49:
" for X be setHIDDENM2 holds  for x be objectHIDDENM1 holds  for f be FunctionFUNCT-1M1 holds x inHIDDENR3 X implies (f |RELAT-1K8 X).FUNCT-1K1 x =XBOOLE-0R4 f .FUNCT-1K1 x"
sorry

mtheorem funct_1_th_50:
" for X be setHIDDENM2 holds  for x be objectHIDDENM1 holds  for f be FunctionFUNCT-1M1 holds x inHIDDENR3 domRELAT-1K1 f & x inHIDDENR3 X implies f .FUNCT-1K1 x inTARSKIR2 rngFUNCT-1K2 (f |RELAT-1K8 X)"
sorry

mtheorem funct_1_th_51:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds X c=TARSKIR1 Y implies (f |RELAT-1K8 X)|RELAT-1K8 Y =RELAT-1R1 f |RELAT-1K8 X & (f |RELAT-1K8 Y)|RELAT-1K8 X =RELAT-1R1 f |RELAT-1K8 X"
  using relat_1_th_73 relat_1_th_74 sorry

mtheorem funct_1_th_52:
" for X be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds f be one-to-oneFUNCT-1V2 implies f |RELAT-1K8 X be one-to-oneFUNCT-1V2"
sorry

mtheorem funct_1_cl_13:
  mlet "Y be setHIDDENM2", "f be FunctionFUNCT-1M1"
"cluster Y |`RELAT-1K9 f as-term-is Function-likeFUNCT-1V1"
proof
(*coherence*)
  show "Y |`RELAT-1K9 f be Function-likeFUNCT-1V1"
sorry
qed "sorry"

mtheorem funct_1_th_53:
" for Y be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds g =RELAT-1R1 Y |`RELAT-1K9 f iff ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 g iff x inHIDDENR3 domRELAT-1K1 f & f .FUNCT-1K1 x inTARSKIR2 Y) & ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 g implies g .FUNCT-1K1 x =XBOOLE-0R4 f .FUNCT-1K1 x)"
sorry

mtheorem funct_1_th_54:
" for Y be setHIDDENM2 holds  for x be objectHIDDENM1 holds  for f be FunctionFUNCT-1M1 holds x inHIDDENR3 domRELAT-1K1 (Y |`RELAT-1K9 f) iff x inHIDDENR3 domRELAT-1K1 f & f .FUNCT-1K1 x inTARSKIR2 Y"
  using funct_1_th_53 sorry

mtheorem funct_1_th_55:
" for Y be setHIDDENM2 holds  for x be objectHIDDENM1 holds  for f be FunctionFUNCT-1M1 holds x inHIDDENR3 domRELAT-1K1 (Y |`RELAT-1K9 f) implies (Y |`RELAT-1K9 f).FUNCT-1K1 x =XBOOLE-0R4 f .FUNCT-1K1 x"
  using funct_1_th_53 sorry

mtheorem funct_1_th_56:
" for Y be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds domRELAT-1K1 (Y |`RELAT-1K9 f) c=TARSKIR1 domRELAT-1K1 f"
  using funct_1_th_53 sorry

mtheorem funct_1_th_57:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds X c=TARSKIR1 Y implies Y |`RELAT-1K9 (X |`RELAT-1K9 f) =RELAT-1R1 X |`RELAT-1K9 f & X |`RELAT-1K9 (Y |`RELAT-1K9 f) =RELAT-1R1 X |`RELAT-1K9 f"
  using relat_1_th_98 relat_1_th_99 sorry

mtheorem funct_1_th_58:
" for Y be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds f be one-to-oneFUNCT-1V2 implies Y |`RELAT-1K9 f be one-to-oneFUNCT-1V2"
sorry

abbreviation(input) FUNCT_1K5(" _ .:FUNCT-1K5  _ " [200,200]200) where
  "f .:FUNCT-1K5 X \<equiv> f .:RELAT-1K10 X"

mtheorem funct_1_def_6:
  mlet "f be FunctionFUNCT-1M1", "X be setHIDDENM2"
"redefine func f .:FUNCT-1K5 X \<rightarrow> setHIDDENM2 means
  \<lambda>it.  for y be objectHIDDENM1 holds y inHIDDENR3 it iff ( ex x be objectHIDDENM1 st (x inHIDDENR3 domRELAT-1K1 f & x inHIDDENR3 X) & y =HIDDENR1 f .FUNCT-1K1 x)"
proof
(*compatibility*)
  show " for it be setHIDDENM2 holds it =HIDDENR1 f .:FUNCT-1K5 X iff ( for y be objectHIDDENM1 holds y inHIDDENR3 it iff ( ex x be objectHIDDENM1 st (x inHIDDENR3 domRELAT-1K1 f & x inHIDDENR3 X) & y =HIDDENR1 f .FUNCT-1K1 x))"
sorry
qed "sorry"

mtheorem funct_1_th_59:
" for x be objectHIDDENM1 holds  for f be FunctionFUNCT-1M1 holds x inHIDDENR3 domRELAT-1K1 f implies ImRELAT-1K12(f,x) =XBOOLE-0R4 {TARSKIK1 f .FUNCT-1K1 x }"
sorry

mtheorem funct_1_th_60:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for f be FunctionFUNCT-1M1 holds x1 inHIDDENR3 domRELAT-1K1 f & x2 inHIDDENR3 domRELAT-1K1 f implies f .:FUNCT-1K5 {TARSKIK2 x1,x2 } =XBOOLE-0R4 {TARSKIK2 f .FUNCT-1K1 x1,f .FUNCT-1K1 x2 }"
sorry

mtheorem funct_1_th_61:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds (Y |`RELAT-1K9 f).:FUNCT-1K5 X c=TARSKIR1 f .:FUNCT-1K5 X"
sorry

mtheorem funct_1_th_62:
" for X1 be setHIDDENM2 holds  for X2 be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds f be one-to-oneFUNCT-1V2 implies f .:FUNCT-1K5 (X1 /\\XBOOLE-0K3 X2) =XBOOLE-0R4 f .:FUNCT-1K5 X1 /\\XBOOLE-0K3 f .:FUNCT-1K5 X2"
sorry

mtheorem funct_1_th_63:
" for f be FunctionFUNCT-1M1 holds ( for X1 be setHIDDENM2 holds  for X2 be setHIDDENM2 holds f .:FUNCT-1K5 (X1 /\\XBOOLE-0K3 X2) =XBOOLE-0R4 f .:FUNCT-1K5 X1 /\\XBOOLE-0K3 f .:FUNCT-1K5 X2) implies f be one-to-oneFUNCT-1V2"
sorry

mtheorem funct_1_th_64:
" for X1 be setHIDDENM2 holds  for X2 be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds f be one-to-oneFUNCT-1V2 implies f .:FUNCT-1K5 (X1 \\SUBSET-1K6 X2) =XBOOLE-0R4 f .:FUNCT-1K5 X1 \\SUBSET-1K6 f .:FUNCT-1K5 X2"
sorry

mtheorem funct_1_th_65:
" for f be FunctionFUNCT-1M1 holds ( for X1 be setHIDDENM2 holds  for X2 be setHIDDENM2 holds f .:FUNCT-1K5 (X1 \\SUBSET-1K6 X2) =XBOOLE-0R4 f .:FUNCT-1K5 X1 \\SUBSET-1K6 f .:FUNCT-1K5 X2) implies f be one-to-oneFUNCT-1V2"
sorry

mtheorem funct_1_th_66:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds X missesXBOOLE-0R1 Y & f be one-to-oneFUNCT-1V2 implies f .:FUNCT-1K5 X missesXBOOLE-0R1 f .:FUNCT-1K5 Y"
sorry

mtheorem funct_1_th_67:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds (Y |`RELAT-1K9 f).:FUNCT-1K5 X =XBOOLE-0R4 Y /\\XBOOLE-0K3 f .:FUNCT-1K5 X"
sorry

abbreviation(input) FUNCT_1K6(" _ \<inverse>FUNCT-1K6  _ " [228,228]228) where
  "f \<inverse>FUNCT-1K6 Y \<equiv> f \<inverse>RELAT-1K11 Y"

mtheorem funct_1_def_7:
  mlet "f be FunctionFUNCT-1M1", "Y be setHIDDENM2"
"redefine func f \<inverse>FUNCT-1K6 Y \<rightarrow> setHIDDENM2 means
  \<lambda>it.  for x be objectHIDDENM1 holds x inHIDDENR3 it iff x inHIDDENR3 domRELAT-1K1 f & f .FUNCT-1K1 x inTARSKIR2 Y"
proof
(*compatibility*)
  show " for it be setHIDDENM2 holds it =HIDDENR1 f \<inverse>FUNCT-1K6 Y iff ( for x be objectHIDDENM1 holds x inHIDDENR3 it iff x inHIDDENR3 domRELAT-1K1 f & f .FUNCT-1K1 x inTARSKIR2 Y)"
sorry
qed "sorry"

mtheorem funct_1_th_68:
" for Y1 be setHIDDENM2 holds  for Y2 be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds f \<inverse>FUNCT-1K6 (Y1 /\\XBOOLE-0K3 Y2) =XBOOLE-0R4 f \<inverse>FUNCT-1K6 Y1 /\\XBOOLE-0K3 f \<inverse>FUNCT-1K6 Y2"
sorry

mtheorem funct_1_th_69:
" for Y1 be setHIDDENM2 holds  for Y2 be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds f \<inverse>FUNCT-1K6 (Y1 \\SUBSET-1K6 Y2) =XBOOLE-0R4 f \<inverse>FUNCT-1K6 Y1 \\SUBSET-1K6 f \<inverse>FUNCT-1K6 Y2"
sorry

mtheorem funct_1_th_70:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds (R |RELAT-1K8 X)\<inverse>RELAT-1K11 Y =XBOOLE-0R4 X /\\XBOOLE-0K3 R \<inverse>RELAT-1K11 Y"
sorry

mtheorem funct_1_th_71:
" for f be FunctionFUNCT-1M1 holds  for A be setHIDDENM2 holds  for B be setHIDDENM2 holds A missesXBOOLE-0R1 B implies f \<inverse>FUNCT-1K6 A missesXBOOLE-0R1 f \<inverse>FUNCT-1K6 B"
sorry

mtheorem funct_1_th_72:
" for y be objectHIDDENM1 holds  for R be RelationRELAT-1M1 holds y inHIDDENR3 rngRELAT-1K2 R iff R \<inverse>RELAT-1K11 {TARSKIK1 y} <>HIDDENR2 {}XBOOLE-0K1"
sorry

mtheorem funct_1_th_73:
" for Y be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds ( for y be objectHIDDENM1 holds y inHIDDENR3 Y implies R \<inverse>RELAT-1K11 {TARSKIK1 y} <>HIDDENR2 {}XBOOLE-0K1) implies Y c=TARSKIR1 rngRELAT-1K2 R"
sorry

mtheorem funct_1_th_74:
" for f be FunctionFUNCT-1M1 holds ( for y be objectHIDDENM1 holds y inHIDDENR3 rngFUNCT-1K2 f implies ( ex x be objectHIDDENM1 st f \<inverse>FUNCT-1K6 {TARSKIK1 y} =XBOOLE-0R4 {TARSKIK1 x})) iff f be one-to-oneFUNCT-1V2"
sorry

mtheorem funct_1_th_75:
" for Y be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds f .:FUNCT-1K5 f \<inverse>FUNCT-1K6 Y c=TARSKIR1 Y"
sorry

mtheorem funct_1_th_76:
" for X be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds X c=TARSKIR1 domRELAT-1K1 R implies X c=TARSKIR1 R \<inverse>RELAT-1K11 (R .:RELAT-1K10 X)"
sorry

mtheorem funct_1_th_77:
" for Y be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds Y c=TARSKIR1 rngFUNCT-1K2 f implies f .:FUNCT-1K5 f \<inverse>FUNCT-1K6 Y =XBOOLE-0R4 Y"
sorry

mtheorem funct_1_th_78:
" for Y be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds f .:FUNCT-1K5 f \<inverse>FUNCT-1K6 Y =XBOOLE-0R4 Y /\\XBOOLE-0K3 f .:FUNCT-1K5 domRELAT-1K1 f"
sorry

mtheorem funct_1_th_79:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds f .:FUNCT-1K5 (X /\\XBOOLE-0K3 f \<inverse>FUNCT-1K6 Y) c=TARSKIR1 f .:FUNCT-1K5 X /\\XBOOLE-0K3 Y"
sorry

mtheorem funct_1_th_80:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds f .:FUNCT-1K5 (X /\\XBOOLE-0K3 f \<inverse>FUNCT-1K6 Y) =XBOOLE-0R4 f .:FUNCT-1K5 X /\\XBOOLE-0K3 Y"
sorry

mtheorem funct_1_th_81:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds X /\\XBOOLE-0K3 R \<inverse>RELAT-1K11 Y c=TARSKIR1 R \<inverse>RELAT-1K11 (R .:RELAT-1K10 X /\\XBOOLE-0K3 Y)"
sorry

mtheorem funct_1_th_82:
" for X be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds f be one-to-oneFUNCT-1V2 implies f \<inverse>FUNCT-1K6 (f .:FUNCT-1K5 X) c=TARSKIR1 X"
sorry

mtheorem funct_1_th_83:
" for f be FunctionFUNCT-1M1 holds ( for X be setHIDDENM2 holds f \<inverse>FUNCT-1K6 (f .:FUNCT-1K5 X) c=TARSKIR1 X) implies f be one-to-oneFUNCT-1V2"
sorry

mtheorem funct_1_th_84:
" for X be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds f be one-to-oneFUNCT-1V2 implies f .:FUNCT-1K5 X =XBOOLE-0R4 (f \<inverse>FUNCT-1K4)\<inverse>FUNCT-1K6 X"
sorry

mtheorem funct_1_th_85:
" for Y be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds f be one-to-oneFUNCT-1V2 implies f \<inverse>FUNCT-1K6 Y =XBOOLE-0R4 f \<inverse>FUNCT-1K4 .:FUNCT-1K5 Y"
sorry

mtheorem funct_1_th_86:
" for Y be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds  for h be FunctionFUNCT-1M1 holds ((Y =XBOOLE-0R4 rngFUNCT-1K2 f & domRELAT-1K1 g =XBOOLE-0R4 Y) & domRELAT-1K1 h =XBOOLE-0R4 Y) & g *FUNCT-1K3 f =RELAT-1R1 h *FUNCT-1K3 f implies g =RELAT-1R1 h"
sorry

mtheorem funct_1_th_87:
" for X1 be setHIDDENM2 holds  for X2 be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds (f .:FUNCT-1K5 X1 c=TARSKIR1 f .:FUNCT-1K5 X2 & X1 c=TARSKIR1 domRELAT-1K1 f) & f be one-to-oneFUNCT-1V2 implies X1 c=TARSKIR1 X2"
sorry

mtheorem funct_1_th_88:
" for Y1 be setHIDDENM2 holds  for Y2 be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds f \<inverse>FUNCT-1K6 Y1 c=TARSKIR1 f \<inverse>FUNCT-1K6 Y2 & Y1 c=TARSKIR1 rngFUNCT-1K2 f implies Y1 c=TARSKIR1 Y2"
sorry

mtheorem funct_1_th_89:
" for f be FunctionFUNCT-1M1 holds f be one-to-oneFUNCT-1V2 iff ( for y be objectHIDDENM1 holds  ex x be objectHIDDENM1 st f \<inverse>FUNCT-1K6 {TARSKIK1 y} c=TARSKIR1 {TARSKIK1 x})"
sorry

mtheorem funct_1_th_90:
" for X be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds  for S be RelationRELAT-1M1 holds rngRELAT-1K2 R c=TARSKIR1 domRELAT-1K1 S implies R \<inverse>RELAT-1K11 X c=TARSKIR1 (R *RELAT-1K6 S)\<inverse>RELAT-1K11 (S .:RELAT-1K10 X)"
sorry

mtheorem funct_1_th_91:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds (f \<inverse>FUNCT-1K6 X =XBOOLE-0R4 f \<inverse>FUNCT-1K6 Y & X c=TARSKIR1 rngFUNCT-1K2 f) & Y c=TARSKIR1 rngFUNCT-1K2 f implies X =XBOOLE-0R4 Y"
  using funct_1_th_88 sorry

(*begin*)
reserve A for "SubsetSUBSET-1M2-of X"
mtheorem funct_1_th_92:
" for X be setHIDDENM2 holds  for A be SubsetSUBSET-1M2-of X holds idRELAT-1K7 X .:FUNCT-1K5 A =XBOOLE-0R4 A"
sorry

abbreviation(input) FUNCT_1V3("empty-yieldingFUNCT-1V3" 70) where
  "empty-yieldingFUNCT-1V3 \<equiv> empty-yieldingRELAT-1V3"

mtheorem funct_1_def_8:
  mlet "f be FunctionFUNCT-1M1"
"redefine attr empty-yieldingFUNCT-1V3 for FunctionFUNCT-1M1 means
  (\<lambda>f.  for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 f implies f .FUNCT-1K1 x be emptyXBOOLE-0V1)"
proof
(*compatibility*)
  show " for f be FunctionFUNCT-1M1 holds f be empty-yieldingFUNCT-1V3 iff ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 f implies f .FUNCT-1K1 x be emptyXBOOLE-0V1)"
sorry
qed "sorry"

abbreviation(input) FUNCT_1V4("non-emptyFUNCT-1V4" 70) where
  "non-emptyFUNCT-1V4 \<equiv> non-emptyRELAT-1V2"

mtheorem funct_1_def_9:
  mlet "F be FunctionFUNCT-1M1"
"redefine attr non-emptyFUNCT-1V4 for FunctionFUNCT-1M1 means
  (\<lambda>F.  for n be objectHIDDENM1 holds n inHIDDENR3 domRELAT-1K1 F implies F .FUNCT-1K1 n be  non emptyXBOOLE-0V1)"
proof
(*compatibility*)
  show " for F be FunctionFUNCT-1M1 holds F be non-emptyFUNCT-1V4 iff ( for n be objectHIDDENM1 holds n inHIDDENR3 domRELAT-1K1 F implies F .FUNCT-1K1 n be  non emptyXBOOLE-0V1)"
sorry
qed "sorry"

mtheorem funct_1_cl_14:
"cluster non-emptyFUNCT-1V4 for FunctionFUNCT-1M1"
proof
(*existence*)
  show " ex it be FunctionFUNCT-1M1 st it be non-emptyFUNCT-1V4"
sorry
qed "sorry"

theorem funct_1_sch_4:
  fixes Df0 Ff1 
  assumes
[ty]: "Df0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
  [ty_func]: "\<And> x1. x1 be objectHIDDENM1 \<Longrightarrow> Ff1(x1) be objectHIDDENM1"
  shows " ex f be FunctionFUNCT-1M1 st domRELAT-1K1 f =XBOOLE-0R4 Df0 & ( for d be ElementSUBSET-1M1-of Df0 holds f .FUNCT-1K1 d =HIDDENR1 Ff1(d))"
sorry

mtheorem funct_1_cl_15:
  mlet "f be non-emptyFUNCT-1V4\<bar>FunctionFUNCT-1M1"
"cluster rngFUNCT-1K2 f as-term-is with-non-empty-elementsSETFAM-1V1"
proof
(*coherence*)
  show "rngFUNCT-1K2 f be with-non-empty-elementsSETFAM-1V1"
sorry
qed "sorry"

mdef funct_1_def_10 ("constantFUNCT-1V5" 70 ) where
"attr constantFUNCT-1V5 for FunctionFUNCT-1M1 means
  (\<lambda>f.  for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 f & y inHIDDENR3 domRELAT-1K1 f implies f .FUNCT-1K1 x =XBOOLE-0R4 f .FUNCT-1K1 y)"..

mtheorem funct_1_th_93:
" for A be setHIDDENM2 holds  for B be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds A c=TARSKIR1 domRELAT-1K1 f & f .:FUNCT-1K5 A c=TARSKIR1 B implies A c=TARSKIR1 f \<inverse>FUNCT-1K6 B"
sorry

mtheorem funct_1_th_94:
" for X be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds X c=TARSKIR1 domRELAT-1K1 f & f be one-to-oneFUNCT-1V2 implies f \<inverse>FUNCT-1K6 (f .:FUNCT-1K5 X) =XBOOLE-0R4 X"
sorry

abbreviation(input) FUNCT_1R1(" _ =FUNCT-1R1  _ " [50,50]50) where
  "f =FUNCT-1R1 g \<equiv> f =HIDDENR1 g"

mtheorem funct_1_def_11:
  mlet "f be FunctionFUNCT-1M1", "g be FunctionFUNCT-1M1"
"redefine pred f =FUNCT-1R1 g means
  domRELAT-1K1 f =XBOOLE-0R4 domRELAT-1K1 g & ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 f implies f .FUNCT-1K1 x =XBOOLE-0R4 g .FUNCT-1K1 x)"
proof
(*compatibility*)
  show "f =FUNCT-1R1 g iff domRELAT-1K1 f =XBOOLE-0R4 domRELAT-1K1 g & ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 f implies f .FUNCT-1K1 x =XBOOLE-0R4 g .FUNCT-1K1 x)"
    using funct_1_th_2 sorry
qed "sorry"

mtheorem funct_1_cl_16:
"cluster non-emptyFUNCT-1V4\<bar> non emptyXBOOLE-0V1 for FunctionFUNCT-1M1"
proof
(*existence*)
  show " ex it be FunctionFUNCT-1M1 st it be non-emptyFUNCT-1V4\<bar> non emptyXBOOLE-0V1"
sorry
qed "sorry"

mtheorem funct_1_cl_17:
  mlet "a be non-emptyFUNCT-1V4\<bar> non emptyXBOOLE-0V1\<bar>FunctionFUNCT-1M1", "i be ElementSUBSET-1M1-of domRELAT-1K1 a"
"cluster a .FUNCT-1K1 i as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "a .FUNCT-1K1 i be  non emptyXBOOLE-0V1"
sorry
qed "sorry"

mtheorem funct_1_cl_18:
  mlet "f be FunctionFUNCT-1M1"
"cluster note-that Function-likeFUNCT-1V1 for SubsetSUBSET-1M2-of f"
proof
(*coherence*)
  show " for it be SubsetSUBSET-1M2-of f holds it be Function-likeFUNCT-1V1"
    using funct_1_def_1 sorry
qed "sorry"

mtheorem funct_1_th_95:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds  for D be setHIDDENM2 holds D c=TARSKIR1 domRELAT-1K1 f & D c=TARSKIR1 domRELAT-1K1 g implies (f |RELAT-1K8 D =FUNCT-1R1 g |RELAT-1K8 D iff ( for x be setHIDDENM2 holds x inTARSKIR2 D implies f .FUNCT-1K1 x =XBOOLE-0R4 g .FUNCT-1K1 x))"
sorry

mtheorem funct_1_th_96:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds  for X be setHIDDENM2 holds domRELAT-1K1 f =XBOOLE-0R4 domRELAT-1K1 g & ( for x be setHIDDENM2 holds x inTARSKIR2 X implies f .FUNCT-1K1 x =XBOOLE-0R4 g .FUNCT-1K1 x) implies f |RELAT-1K8 X =FUNCT-1R1 g |RELAT-1K8 X"
sorry

mtheorem funct_1_th_97:
" for X be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds rngFUNCT-1K2 (f |RELAT-1K8 {TARSKIK1 X}) c=TARSKIR1 {TARSKIK1 f .FUNCT-1K1 X }"
sorry

mtheorem funct_1_th_98:
" for X be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds X inTARSKIR2 domRELAT-1K1 f implies rngFUNCT-1K2 (f |RELAT-1K8 {TARSKIK1 X}) =XBOOLE-0R4 {TARSKIK1 f .FUNCT-1K1 X }"
sorry

mtheorem funct_1_cl_19:
"cluster emptyXBOOLE-0V1 also-is constantFUNCT-1V5 for FunctionFUNCT-1M1"
proof
(*coherence*)
  show " for it be FunctionFUNCT-1M1 holds it be emptyXBOOLE-0V1 implies it be constantFUNCT-1V5"
     sorry
qed "sorry"

mtheorem funct_1_cl_20:
  mlet "f be constantFUNCT-1V5\<bar>FunctionFUNCT-1M1"
"cluster rngFUNCT-1K2 f as-term-is trivialSUBSET-1V2"
proof
(*coherence*)
  show "rngFUNCT-1K2 f be trivialSUBSET-1V2"
sorry
qed "sorry"

mtheorem funct_1_cl_21:
"cluster  non constantFUNCT-1V5 for FunctionFUNCT-1M1"
proof
(*existence*)
  show " ex it be FunctionFUNCT-1M1 st it be  non constantFUNCT-1V5"
sorry
qed "sorry"

mtheorem funct_1_cl_22:
  mlet "f be  non constantFUNCT-1V5\<bar>FunctionFUNCT-1M1"
"cluster rngFUNCT-1K2 f as-term-is  non trivialSUBSET-1V2"
proof
(*coherence*)
  show "rngFUNCT-1K2 f be  non trivialSUBSET-1V2"
sorry
qed "sorry"

mtheorem funct_1_cl_23:
"cluster  non constantFUNCT-1V5 also-is  non trivialSUBSET-1V2 for FunctionFUNCT-1M1"
proof
(*coherence*)
  show " for it be FunctionFUNCT-1M1 holds it be  non constantFUNCT-1V5 implies it be  non trivialSUBSET-1V2"
sorry
qed "sorry"

mtheorem funct_1_cl_24:
"cluster trivialSUBSET-1V2 also-is constantFUNCT-1V5 for FunctionFUNCT-1M1"
proof
(*coherence*)
  show " for it be FunctionFUNCT-1M1 holds it be trivialSUBSET-1V2 implies it be constantFUNCT-1V5"
     sorry
qed "sorry"

mtheorem funct_1_th_99:
" for F be FunctionFUNCT-1M1 holds  for G be FunctionFUNCT-1M1 holds  for X be setHIDDENM2 holds G |RELAT-1K8 (F .:FUNCT-1K5 X) *FUNCT-1K3 F |RELAT-1K8 X =FUNCT-1R1 (G *FUNCT-1K3 F)|RELAT-1K8 X"
sorry

mtheorem funct_1_th_100:
" for F be FunctionFUNCT-1M1 holds  for G be FunctionFUNCT-1M1 holds  for X be setHIDDENM2 holds  for X1 be setHIDDENM2 holds G |RELAT-1K8 X1 *FUNCT-1K3 F |RELAT-1K8 X =FUNCT-1R1 (G *FUNCT-1K3 F)|RELAT-1K8 (X /\\XBOOLE-0K3 F \<inverse>FUNCT-1K6 X1)"
sorry

mtheorem funct_1_th_101:
" for F be FunctionFUNCT-1M1 holds  for G be FunctionFUNCT-1M1 holds  for X be setHIDDENM2 holds X c=TARSKIR1 domRELAT-1K1 (G *FUNCT-1K3 F) iff X c=TARSKIR1 domRELAT-1K1 F & F .:FUNCT-1K5 X c=TARSKIR1 domRELAT-1K1 G"
sorry

mdef funct_1_def_12 ("the-value-ofFUNCT-1K7  _ " [164]164 ) where
  mlet "f be FunctionFUNCT-1M1"
"assume f be  non emptyXBOOLE-0V1\<bar>constantFUNCT-1V5 func the-value-ofFUNCT-1K7 f \<rightarrow> objectHIDDENM1 means
  \<lambda>it.  ex x be setHIDDENM2 st x inTARSKIR2 domRELAT-1K1 f & it =HIDDENR1 f .FUNCT-1K1 x"
proof-
  (*existence*)
    show "f be  non emptyXBOOLE-0V1\<bar>constantFUNCT-1V5 implies ( ex it be objectHIDDENM1 st  ex x be setHIDDENM2 st x inTARSKIR2 domRELAT-1K1 f & it =HIDDENR1 f .FUNCT-1K1 x)"
sorry
  (*uniqueness*)
    show "f be  non emptyXBOOLE-0V1\<bar>constantFUNCT-1V5 implies ( for it1 be objectHIDDENM1 holds  for it2 be objectHIDDENM1 holds ( ex x be setHIDDENM2 st x inTARSKIR2 domRELAT-1K1 f & it1 =HIDDENR1 f .FUNCT-1K1 x) & ( ex x be setHIDDENM2 st x inTARSKIR2 domRELAT-1K1 f & it2 =HIDDENR1 f .FUNCT-1K1 x) implies it1 =HIDDENR1 it2)"
sorry
qed "sorry"

mtheorem funct_1_cl_25:
  mlet "X be setHIDDENM2", "Y be setHIDDENM2"
"cluster X -definedRELAT-1V4\<bar>Y -valuedRELAT-1V5 for FunctionFUNCT-1M1"
proof
(*existence*)
  show " ex it be FunctionFUNCT-1M1 st it be X -definedRELAT-1V4\<bar>Y -valuedRELAT-1V5"
sorry
qed "sorry"

mtheorem funct_1_th_102:
" for X be setHIDDENM2 holds  for f be X -valuedRELAT-1V5\<bar>FunctionFUNCT-1M1 holds  for x be setHIDDENM2 holds x inTARSKIR2 domRELAT-1K1 f implies f .FUNCT-1K1 x inTARSKIR2 X"
sorry

mdef funct_1_def_13 ("functionalFUNCT-1V6" 70 ) where
"attr functionalFUNCT-1V6 for setHIDDENM2 means
  (\<lambda>IT.  for x be objectHIDDENM1 holds x inHIDDENR3 IT implies x be FunctionFUNCT-1M1)"..

mtheorem funct_1_cl_26:
"cluster emptyXBOOLE-0V1 also-is functionalFUNCT-1V6 for setHIDDENM2"
proof
(*coherence*)
  show " for it be setHIDDENM2 holds it be emptyXBOOLE-0V1 implies it be functionalFUNCT-1V6"
     sorry
qed "sorry"

mtheorem funct_1_cl_27:
  mlet "f be FunctionFUNCT-1M1"
"cluster {TARSKIK1 f} as-term-is functionalFUNCT-1V6"
proof
(*coherence*)
  show "{TARSKIK1 f} be functionalFUNCT-1V6"
    using tarski_def_1 sorry
qed "sorry"

mtheorem funct_1_cl_28:
  mlet "f be FunctionFUNCT-1M1", "g be FunctionFUNCT-1M1"
"cluster {TARSKIK2 f,g } as-term-is functionalFUNCT-1V6"
proof
(*coherence*)
  show "{TARSKIK2 f,g } be functionalFUNCT-1V6"
    using tarski_def_2 sorry
qed "sorry"

mtheorem funct_1_cl_29:
"cluster  non emptyXBOOLE-0V1\<bar>functionalFUNCT-1V6 for setHIDDENM2"
proof
(*existence*)
  show " ex it be setHIDDENM2 st it be  non emptyXBOOLE-0V1\<bar>functionalFUNCT-1V6"
sorry
qed "sorry"

mtheorem funct_1_cl_30:
  mlet "P be functionalFUNCT-1V6\<bar>setHIDDENM2"
"cluster note-that Function-likeFUNCT-1V1\<bar>Relation-likeRELAT-1V1 for ElementSUBSET-1M1-of P"
proof
(*coherence*)
  show " for it be ElementSUBSET-1M1-of P holds it be Function-likeFUNCT-1V1\<bar>Relation-likeRELAT-1V1"
sorry
qed "sorry"

mtheorem funct_1_cl_31:
  mlet "A be functionalFUNCT-1V6\<bar>setHIDDENM2"
"cluster note-that functionalFUNCT-1V6 for SubsetSUBSET-1M2-of A"
proof
(*coherence*)
  show " for it be SubsetSUBSET-1M2-of A holds it be functionalFUNCT-1V6"
     sorry
qed "sorry"

mdef funct_1_def_14 (" _ -compatibleFUNCT-1V7" [70]70 ) where
  mlet "g be FunctionFUNCT-1M1"
"attr g -compatibleFUNCT-1V7 for FunctionFUNCT-1M1 means
  (\<lambda>f.  for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 f implies f .FUNCT-1K1 x inTARSKIR2 g .FUNCT-1K1 x)"..

mtheorem funct_1_th_103:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds f be g -compatibleFUNCT-1V7 & domRELAT-1K1 f =XBOOLE-0R4 domRELAT-1K1 g implies g be non-emptyFUNCT-1V4"
   sorry

mtheorem funct_1_th_104:
" for f be FunctionFUNCT-1M1 holds {}XBOOLE-0K1 be f -compatibleFUNCT-1V7"
   sorry

mtheorem funct_1_cl_32:
  mlet "I be setHIDDENM2", "f be FunctionFUNCT-1M1"
"cluster emptyXBOOLE-0V1\<bar>I -definedRELAT-1V4\<bar>f -compatibleFUNCT-1V7 for FunctionFUNCT-1M1"
proof
(*existence*)
  show " ex it be FunctionFUNCT-1M1 st it be emptyXBOOLE-0V1\<bar>I -definedRELAT-1V4\<bar>f -compatibleFUNCT-1V7"
sorry
qed "sorry"

mtheorem funct_1_cl_33:
  mlet "X be setHIDDENM2", "f be FunctionFUNCT-1M1", "g be f -compatibleFUNCT-1V7\<bar>FunctionFUNCT-1M1"
"cluster g |RELAT-1K8 X as-term-is f -compatibleFUNCT-1V7"
proof
(*coherence*)
  show "g |RELAT-1K8 X be f -compatibleFUNCT-1V7"
sorry
qed "sorry"

mtheorem funct_1_cl_34:
  mlet "I be setHIDDENM2"
"cluster non-emptyFUNCT-1V4\<bar>I -definedRELAT-1V4 for FunctionFUNCT-1M1"
proof
(*existence*)
  show " ex it be FunctionFUNCT-1M1 st it be non-emptyFUNCT-1V4\<bar>I -definedRELAT-1V4"
sorry
qed "sorry"

mtheorem funct_1_th_105:
" for f be FunctionFUNCT-1M1 holds  for g be f -compatibleFUNCT-1V7\<bar>FunctionFUNCT-1M1 holds domRELAT-1K1 g c=TARSKIR1 domRELAT-1K1 f"
sorry

mtheorem funct_1_cl_35:
  mlet "X be setHIDDENM2", "f be X -definedRELAT-1V4\<bar>FunctionFUNCT-1M1"
"cluster f -compatibleFUNCT-1V7 also-is X -definedRELAT-1V4 for FunctionFUNCT-1M1"
proof
(*coherence*)
  show " for it be FunctionFUNCT-1M1 holds it be f -compatibleFUNCT-1V7 implies it be X -definedRELAT-1V4"
sorry
qed "sorry"

mtheorem funct_1_th_106:
" for X be setHIDDENM2 holds  for x be objectHIDDENM1 holds  for f be X -valuedRELAT-1V5\<bar>FunctionFUNCT-1M1 holds x inHIDDENR3 domRELAT-1K1 f implies f .FUNCT-1K1 x be ElementSUBSET-1M1-of X"
sorry

mtheorem funct_1_th_107:
" for f be FunctionFUNCT-1M1 holds  for A be setHIDDENM2 holds f be one-to-oneFUNCT-1V2 & A c=TARSKIR1 domRELAT-1K1 f implies f \<inverse>FUNCT-1K4 .:FUNCT-1K5 (f .:FUNCT-1K5 A) =XBOOLE-0R4 A"
sorry

mtheorem funct_1_cl_36:
  mlet "A be functionalFUNCT-1V6\<bar>setHIDDENM2", "x be objectHIDDENM1", "F be A -valuedRELAT-1V5\<bar>FunctionFUNCT-1M1"
"cluster F .FUNCT-1K1 x as-term-is Function-likeFUNCT-1V1\<bar>Relation-likeRELAT-1V1"
proof
(*coherence*)
  show "F .FUNCT-1K1 x be Function-likeFUNCT-1V1\<bar>Relation-likeRELAT-1V1"
sorry
qed "sorry"

mtheorem funct_1_th_108:
" for X be setHIDDENM2 holds  for x be objectHIDDENM1 holds  for f be FunctionFUNCT-1M1 holds x inHIDDENR3 X & x inHIDDENR3 domRELAT-1K1 f implies f .FUNCT-1K1 x inTARSKIR2 f .:FUNCT-1K5 X"
sorry

mtheorem funct_1_th_109:
" for X be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds X <>HIDDENR2 {}XBOOLE-0K1 & X c=TARSKIR1 domRELAT-1K1 f implies f .:FUNCT-1K5 X <>HIDDENR2 {}XBOOLE-0K1"
sorry

mtheorem funct_1_cl_37:
  mlet "f be  non trivialSUBSET-1V2\<bar>FunctionFUNCT-1M1"
"cluster domRELAT-1K1 f as-term-is  non trivialSUBSET-1V2"
proof
(*coherence*)
  show "domRELAT-1K1 f be  non trivialSUBSET-1V2"
sorry
qed "sorry"

mtheorem funct_1_th_110:
" for B be  non emptyXBOOLE-0V1\<bar>functionalFUNCT-1V6\<bar>setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds f =XBOOLE-0R4 unionTARSKIK3 B implies domRELAT-1K1 f =XBOOLE-0R4 unionTARSKIK3 ({domRELAT-1K1 g where g be ElementSUBSET-1M1-of B :  True  }) & rngFUNCT-1K2 f =XBOOLE-0R4 unionTARSKIK3 ({rngFUNCT-1K2 g where g be ElementSUBSET-1M1-of B :  True  })"
sorry

theorem funct_1_sch_5:
  fixes Af0 Ff1 
  assumes
[ty]: "Af0 be setHIDDENM2" and
  [ty_func]: "\<And> x1. x1 be objectHIDDENM1 \<Longrightarrow> Ff1(x1) be objectHIDDENM1"
  shows " ex f be FunctionFUNCT-1M1 st domRELAT-1K1 f =XBOOLE-0R4 Af0 & ( for X be setHIDDENM2 holds X inTARSKIR2 Af0 implies f .FUNCT-1K1 X =HIDDENR1 Ff1(X))"
sorry

mtheorem funct_1_th_111:
" for M be setHIDDENM2 holds ( for X be setHIDDENM2 holds X inTARSKIR2 M implies X <>HIDDENR2 {}XBOOLE-0K1) implies ( ex f be FunctionFUNCT-1M1 st domRELAT-1K1 f =XBOOLE-0R4 M & ( for X be setHIDDENM2 holds X inTARSKIR2 M implies f .FUNCT-1K1 X inTARSKIR2 X))"
sorry

theorem funct_1_sch_6:
  fixes Xf0 Yf0 Pp2 
  assumes
[ty]: "Xf0 be setHIDDENM2" and
  [ty]: "Yf0 be setHIDDENM2" and
   A1: " for x be objectHIDDENM1 holds x inHIDDENR3 Xf0 implies ( ex y be objectHIDDENM1 st y inHIDDENR3 Yf0 & Pp2(x,y))"
  shows " ex f be FunctionFUNCT-1M1 st (domRELAT-1K1 f =XBOOLE-0R4 Xf0 & rngFUNCT-1K2 f c=TARSKIR1 Yf0) & ( for x be objectHIDDENM1 holds x inHIDDENR3 Xf0 implies Pp2(x,f .FUNCT-1K1 x))"
sorry

mtheorem funct_1_cl_38:
  mlet "f be empty-yieldingFUNCT-1V3\<bar>FunctionFUNCT-1M1", "x be objectHIDDENM1"
"cluster f .FUNCT-1K1 x as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "f .FUNCT-1K1 x be emptyXBOOLE-0V1"
sorry
qed "sorry"

mtheorem funct_1_th_112:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds  for h be FunctionFUNCT-1M1 holds (f c=RELAT-1R2 h & g c=RELAT-1R2 h) & f missesXBOOLE-0R1 g implies domRELAT-1K1 f missesXBOOLE-0R1 domRELAT-1K1 g"
sorry

mtheorem funct_1_th_113:
" for Y be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds Y |`RELAT-1K9 f =FUNCT-1R1 f |RELAT-1K8 f \<inverse>FUNCT-1K6 Y"
sorry

mtheorem funct_1_reduce_1:
  mlet "X be setHIDDENM2", "x be ElementSUBSET-1M1-of X"
"reduce idRELAT-1K7 X .FUNCT-1K1 x to x"
proof
(*reducibility*)
  show "idRELAT-1K7 X .FUNCT-1K1 x =HIDDENR1 x"
sorry
qed "sorry"

mtheorem funct_1_th_114:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds rngFUNCT-1K2 f c=TARSKIR1 rngFUNCT-1K2 g implies ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 f implies ( ex y be objectHIDDENM1 st y inHIDDENR3 domRELAT-1K1 g & f .FUNCT-1K1 x =XBOOLE-0R4 g .FUNCT-1K1 y))"
sorry

end
