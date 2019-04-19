theory funct_5
  imports funct_3 card_1
begin
(*begin*)
reserve X, Y, Z, X1, X2, Y1, Y2 for "setHIDDENM2"
reserve x, y, z, t, x1, x2 for "objectHIDDENM1"
reserve f, g, h, f1, f2, g1, g2 for "FunctionFUNCT-1M1"
theorem funct_5_sch_1:
  fixes FSf0 ff1 
  assumes
[ty]: "FSf0 be setHIDDENM2" and
  [ty_func]: "\<And> x1. x1 be objectHIDDENM1 \<Longrightarrow> ff1(x1) be objectHIDDENM1"
  shows " ex f be FunctionFUNCT-1M1 st domRELAT-1K1 f =XBOOLE-0R4 FSf0 & ( for g be FunctionFUNCT-1M1 holds g inTARSKIR2 FSf0 implies f .FUNCT-1K1 g =HIDDENR1 ff1(g))"
sorry

mtheorem funct_5_th_1:
"~FUNCT-4K2 ({}XBOOLE-0K1) =FUNCT-1R1 {}XBOOLE-0K1"
sorry

(*\$CT 6*)
mtheorem funct_5_th_8:
"proj1XTUPLE-0K12 ({}XBOOLE-0K1) =FUNCT-1R1 {}XBOOLE-0K1 & proj2XTUPLE-0K13 ({}XBOOLE-0K1) =FUNCT-1R1 {}XBOOLE-0K1"
   sorry

mtheorem funct_5_th_9:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds (Y <>HIDDENR2 {}XBOOLE-0K1 or [:ZFMISC-1K2 X,Y :] <>HIDDENR2 {}XBOOLE-0K1) or [:ZFMISC-1K2 Y,X :] <>HIDDENR2 {}XBOOLE-0K1 implies proj1XTUPLE-0K12 ([:ZFMISC-1K2 X,Y :]) =XBOOLE-0R4 X & proj2XTUPLE-0K13 ([:ZFMISC-1K2 Y,X :]) =XBOOLE-0R4 X"
sorry

mtheorem funct_5_th_10:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds proj1XTUPLE-0K12 ([:ZFMISC-1K2 X,Y :]) c=TARSKIR1 X & proj2XTUPLE-0K13 ([:ZFMISC-1K2 X,Y :]) c=TARSKIR1 Y"
sorry

mtheorem funct_5_th_11:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds Z c=TARSKIR1 [:ZFMISC-1K2 X,Y :] implies proj1XTUPLE-0K12 Z c=TARSKIR1 X & proj2XTUPLE-0K13 Z c=TARSKIR1 Y"
sorry

mtheorem funct_5_th_12:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds proj1XTUPLE-0K12 {TARSKIK1 [TARSKIK4 x,y ] } =XBOOLE-0R4 {TARSKIK1 x} & proj2XTUPLE-0K13 {TARSKIK1 [TARSKIK4 x,y ] } =XBOOLE-0R4 {TARSKIK1 y}"
sorry

mtheorem funct_5_th_13:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for z be objectHIDDENM1 holds  for t be objectHIDDENM1 holds proj1XTUPLE-0K12 {TARSKIK2 [TARSKIK4 x,y ],[TARSKIK4 z,t ] } =XBOOLE-0R4 {TARSKIK2 x,z } & proj2XTUPLE-0K13 {TARSKIK2 [TARSKIK4 x,y ],[TARSKIK4 z,t ] } =XBOOLE-0R4 {TARSKIK2 y,t }"
sorry

mtheorem funct_5_th_14:
" for X be setHIDDENM2 holds  not ( ex x be objectHIDDENM1 st  ex y be objectHIDDENM1 st [TARSKIK4 x,y ] inHIDDENR3 X) implies proj1XTUPLE-0K12 X =XBOOLE-0R4 {}XBOOLE-0K1 & proj2XTUPLE-0K13 X =XBOOLE-0R4 {}XBOOLE-0K1"
sorry

mtheorem funct_5_th_15:
" for X be setHIDDENM2 holds proj1XTUPLE-0K12 X =XBOOLE-0R4 {}XBOOLE-0K1 or proj2XTUPLE-0K13 X =XBOOLE-0R4 {}XBOOLE-0K1 implies  not ( ex x be objectHIDDENM1 st  ex y be objectHIDDENM1 st [TARSKIK4 x,y ] inHIDDENR3 X)"
  using xtuple_0_def_12 xtuple_0_def_13 sorry

mtheorem funct_5_th_16:
" for X be setHIDDENM2 holds proj1XTUPLE-0K12 X =XBOOLE-0R4 {}XBOOLE-0K1 iff proj2XTUPLE-0K13 X =XBOOLE-0R4 {}XBOOLE-0K1"
sorry

mtheorem funct_5_th_17:
" for f be FunctionFUNCT-1M1 holds proj1XTUPLE-0K12 (domRELAT-1K1 f) =XBOOLE-0R4 proj2XTUPLE-0K13 (domRELAT-1K1 (~FUNCT-4K2 f)) & proj2XTUPLE-0K13 (domRELAT-1K1 f) =XBOOLE-0R4 proj1XTUPLE-0K12 (domRELAT-1K1 (~FUNCT-4K2 f))"
sorry

mdef funct_5_def_1 ("curryFUNCT-5K1  _ " [228]228 ) where
  mlet "f be FunctionFUNCT-1M1"
"func curryFUNCT-5K1 f \<rightarrow> FunctionFUNCT-1M1 means
  \<lambda>it. domRELAT-1K1 it =XBOOLE-0R4 proj1XTUPLE-0K12 (domRELAT-1K1 f) & ( for x be objectHIDDENM1 holds x inHIDDENR3 proj1XTUPLE-0K12 (domRELAT-1K1 f) implies ( ex g be FunctionFUNCT-1M1 st (it .FUNCT-1K1 x =XBOOLE-0R4 g & domRELAT-1K1 g =XBOOLE-0R4 proj2XTUPLE-0K13 (domRELAT-1K1 f /\\XBOOLE-0K3 ([:ZFMISC-1K2 {TARSKIK1 x},proj2XTUPLE-0K13 (domRELAT-1K1 f) :]))) & ( for y be objectHIDDENM1 holds y inHIDDENR3 domRELAT-1K1 g implies g .FUNCT-1K1 y =XBOOLE-0R4 f .BINOP-1K1(x,y))))"
proof-
  (*existence*)
    show " ex it be FunctionFUNCT-1M1 st domRELAT-1K1 it =XBOOLE-0R4 proj1XTUPLE-0K12 (domRELAT-1K1 f) & ( for x be objectHIDDENM1 holds x inHIDDENR3 proj1XTUPLE-0K12 (domRELAT-1K1 f) implies ( ex g be FunctionFUNCT-1M1 st (it .FUNCT-1K1 x =XBOOLE-0R4 g & domRELAT-1K1 g =XBOOLE-0R4 proj2XTUPLE-0K13 (domRELAT-1K1 f /\\XBOOLE-0K3 ([:ZFMISC-1K2 {TARSKIK1 x},proj2XTUPLE-0K13 (domRELAT-1K1 f) :]))) & ( for y be objectHIDDENM1 holds y inHIDDENR3 domRELAT-1K1 g implies g .FUNCT-1K1 y =XBOOLE-0R4 f .BINOP-1K1(x,y))))"
sorry
  (*uniqueness*)
    show " for it1 be FunctionFUNCT-1M1 holds  for it2 be FunctionFUNCT-1M1 holds (domRELAT-1K1 it1 =XBOOLE-0R4 proj1XTUPLE-0K12 (domRELAT-1K1 f) & ( for x be objectHIDDENM1 holds x inHIDDENR3 proj1XTUPLE-0K12 (domRELAT-1K1 f) implies ( ex g be FunctionFUNCT-1M1 st (it1 .FUNCT-1K1 x =XBOOLE-0R4 g & domRELAT-1K1 g =XBOOLE-0R4 proj2XTUPLE-0K13 (domRELAT-1K1 f /\\XBOOLE-0K3 ([:ZFMISC-1K2 {TARSKIK1 x},proj2XTUPLE-0K13 (domRELAT-1K1 f) :]))) & ( for y be objectHIDDENM1 holds y inHIDDENR3 domRELAT-1K1 g implies g .FUNCT-1K1 y =XBOOLE-0R4 f .BINOP-1K1(x,y))))) & (domRELAT-1K1 it2 =XBOOLE-0R4 proj1XTUPLE-0K12 (domRELAT-1K1 f) & ( for x be objectHIDDENM1 holds x inHIDDENR3 proj1XTUPLE-0K12 (domRELAT-1K1 f) implies ( ex g be FunctionFUNCT-1M1 st (it2 .FUNCT-1K1 x =XBOOLE-0R4 g & domRELAT-1K1 g =XBOOLE-0R4 proj2XTUPLE-0K13 (domRELAT-1K1 f /\\XBOOLE-0K3 ([:ZFMISC-1K2 {TARSKIK1 x},proj2XTUPLE-0K13 (domRELAT-1K1 f) :]))) & ( for y be objectHIDDENM1 holds y inHIDDENR3 domRELAT-1K1 g implies g .FUNCT-1K1 y =XBOOLE-0R4 f .BINOP-1K1(x,y))))) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mdef funct_5_def_2 ("uncurryFUNCT-5K2  _ " [228]228 ) where
  mlet "f be FunctionFUNCT-1M1"
"func uncurryFUNCT-5K2 f \<rightarrow> FunctionFUNCT-1M1 means
  \<lambda>it. ( for t be objectHIDDENM1 holds t inHIDDENR3 domRELAT-1K1 it iff ( ex x be objectHIDDENM1 st  ex g be FunctionFUNCT-1M1 st  ex y be objectHIDDENM1 st ((t =HIDDENR1 [TARSKIK4 x,y ] & x inHIDDENR3 domRELAT-1K1 f) & g =XBOOLE-0R4 f .FUNCT-1K1 x) & y inHIDDENR3 domRELAT-1K1 g)) & ( for x be objectHIDDENM1 holds  for g be FunctionFUNCT-1M1 holds x inHIDDENR3 domRELAT-1K1 it & g =XBOOLE-0R4 f .FUNCT-1K1 x `1XTUPLE-0K1 implies it .FUNCT-1K1 x =XBOOLE-0R4 g .FUNCT-1K1 x `2XTUPLE-0K2)"
proof-
  (*existence*)
    show " ex it be FunctionFUNCT-1M1 st ( for t be objectHIDDENM1 holds t inHIDDENR3 domRELAT-1K1 it iff ( ex x be objectHIDDENM1 st  ex g be FunctionFUNCT-1M1 st  ex y be objectHIDDENM1 st ((t =HIDDENR1 [TARSKIK4 x,y ] & x inHIDDENR3 domRELAT-1K1 f) & g =XBOOLE-0R4 f .FUNCT-1K1 x) & y inHIDDENR3 domRELAT-1K1 g)) & ( for x be objectHIDDENM1 holds  for g be FunctionFUNCT-1M1 holds x inHIDDENR3 domRELAT-1K1 it & g =XBOOLE-0R4 f .FUNCT-1K1 x `1XTUPLE-0K1 implies it .FUNCT-1K1 x =XBOOLE-0R4 g .FUNCT-1K1 x `2XTUPLE-0K2)"
sorry
  (*uniqueness*)
    show " for it1 be FunctionFUNCT-1M1 holds  for it2 be FunctionFUNCT-1M1 holds (( for t be objectHIDDENM1 holds t inHIDDENR3 domRELAT-1K1 it1 iff ( ex x be objectHIDDENM1 st  ex g be FunctionFUNCT-1M1 st  ex y be objectHIDDENM1 st ((t =HIDDENR1 [TARSKIK4 x,y ] & x inHIDDENR3 domRELAT-1K1 f) & g =XBOOLE-0R4 f .FUNCT-1K1 x) & y inHIDDENR3 domRELAT-1K1 g)) & ( for x be objectHIDDENM1 holds  for g be FunctionFUNCT-1M1 holds x inHIDDENR3 domRELAT-1K1 it1 & g =XBOOLE-0R4 f .FUNCT-1K1 x `1XTUPLE-0K1 implies it1 .FUNCT-1K1 x =XBOOLE-0R4 g .FUNCT-1K1 x `2XTUPLE-0K2)) & (( for t be objectHIDDENM1 holds t inHIDDENR3 domRELAT-1K1 it2 iff ( ex x be objectHIDDENM1 st  ex g be FunctionFUNCT-1M1 st  ex y be objectHIDDENM1 st ((t =HIDDENR1 [TARSKIK4 x,y ] & x inHIDDENR3 domRELAT-1K1 f) & g =XBOOLE-0R4 f .FUNCT-1K1 x) & y inHIDDENR3 domRELAT-1K1 g)) & ( for x be objectHIDDENM1 holds  for g be FunctionFUNCT-1M1 holds x inHIDDENR3 domRELAT-1K1 it2 & g =XBOOLE-0R4 f .FUNCT-1K1 x `1XTUPLE-0K1 implies it2 .FUNCT-1K1 x =XBOOLE-0R4 g .FUNCT-1K1 x `2XTUPLE-0K2)) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mdef funct_5_def_3 ("curry''FUNCT-5K3  _ " [228]228 ) where
  mlet "f be FunctionFUNCT-1M1"
"func curry'FUNCT-5K3 f \<rightarrow> FunctionFUNCT-1M1 equals
  curryFUNCT-5K1 (~FUNCT-4K2 f)"
proof-
  (*coherence*)
    show "curryFUNCT-5K1 (~FUNCT-4K2 f) be FunctionFUNCT-1M1"
       sorry
qed "sorry"

mdef funct_5_def_4 ("uncurry''FUNCT-5K4  _ " [228]228 ) where
  mlet "f be FunctionFUNCT-1M1"
"func uncurry'FUNCT-5K4 f \<rightarrow> FunctionFUNCT-1M1 equals
  ~FUNCT-4K2 (uncurryFUNCT-5K2 f)"
proof-
  (*coherence*)
    show "~FUNCT-4K2 (uncurryFUNCT-5K2 f) be FunctionFUNCT-1M1"
       sorry
qed "sorry"

(*\$CT*)
mtheorem funct_5_cl_1:
  mlet "f be FunctionFUNCT-1M1"
"cluster curryFUNCT-5K1 f as-term-is Function-yieldingFUNCOP-1V1"
proof
(*coherence*)
  show "curryFUNCT-5K1 f be Function-yieldingFUNCOP-1V1"
sorry
qed "sorry"

mtheorem funct_5_th_19:
" for f be FunctionFUNCT-1M1 holds  for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds [TARSKIK4 x,y ] inHIDDENR3 domRELAT-1K1 f implies x inHIDDENR3 domRELAT-1K1 (curryFUNCT-5K1 f)"
sorry

mtheorem funct_5_th_20:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds  for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds [TARSKIK4 x,y ] inHIDDENR3 domRELAT-1K1 f & g =XBOOLE-0R4 curryFUNCT-5K1 f .FUNCT-1K1 x implies y inHIDDENR3 domRELAT-1K1 g & g .FUNCT-1K1 y =XBOOLE-0R4 f .BINOP-1K1(x,y)"
sorry

mtheorem funct_5_cl_2:
  mlet "f be FunctionFUNCT-1M1"
"cluster curry'FUNCT-5K3 f as-term-is Function-yieldingFUNCOP-1V1"
proof
(*coherence*)
  show "curry'FUNCT-5K3 f be Function-yieldingFUNCOP-1V1"
     sorry
qed "sorry"

mtheorem funct_5_th_21:
" for f be FunctionFUNCT-1M1 holds  for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds [TARSKIK4 x,y ] inHIDDENR3 domRELAT-1K1 f implies y inHIDDENR3 domRELAT-1K1 (curry'FUNCT-5K3 f)"
sorry

mtheorem funct_5_th_22:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds  for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds [TARSKIK4 x,y ] inHIDDENR3 domRELAT-1K1 f & g =XBOOLE-0R4 curry'FUNCT-5K3 f .FUNCT-1K1 y implies x inHIDDENR3 domRELAT-1K1 g & g .FUNCT-1K1 x =XBOOLE-0R4 f .BINOP-1K1(x,y)"
sorry

mtheorem funct_5_th_23:
" for f be FunctionFUNCT-1M1 holds domRELAT-1K1 (curry'FUNCT-5K3 f) =XBOOLE-0R4 proj2XTUPLE-0K13 (domRELAT-1K1 f)"
sorry

mtheorem funct_5_th_24:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds [:ZFMISC-1K2 X,Y :] <>HIDDENR2 {}XBOOLE-0K1 & domRELAT-1K1 f =XBOOLE-0R4 [:ZFMISC-1K2 X,Y :] implies domRELAT-1K1 (curryFUNCT-5K1 f) =XBOOLE-0R4 X & domRELAT-1K1 (curry'FUNCT-5K3 f) =XBOOLE-0R4 Y"
sorry

mtheorem funct_5_th_25:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds domRELAT-1K1 f c=TARSKIR1 [:ZFMISC-1K2 X,Y :] implies domRELAT-1K1 (curryFUNCT-5K1 f) c=TARSKIR1 X & domRELAT-1K1 (curry'FUNCT-5K3 f) c=TARSKIR1 Y"
sorry

mtheorem funct_5_th_26:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds rngFUNCT-1K2 f c=TARSKIR1 FuncsFUNCT-2K1(X,Y) implies domRELAT-1K1 (uncurryFUNCT-5K2 f) =XBOOLE-0R4 [:ZFMISC-1K2 domRELAT-1K1 f,X :] & domRELAT-1K1 (uncurry'FUNCT-5K4 f) =XBOOLE-0R4 [:ZFMISC-1K2 X,domRELAT-1K1 f :]"
sorry

mtheorem funct_5_th_27:
" for f be FunctionFUNCT-1M1 holds  not ( ex x be objectHIDDENM1 st  ex y be objectHIDDENM1 st [TARSKIK4 x,y ] inHIDDENR3 domRELAT-1K1 f) implies curryFUNCT-5K1 f =FUNCT-1R1 {}XBOOLE-0K1 & curry'FUNCT-5K3 f =FUNCT-1R1 {}XBOOLE-0K1"
sorry

mtheorem funct_5_th_28:
" for f be FunctionFUNCT-1M1 holds  not ( ex x be objectHIDDENM1 st x inHIDDENR3 domRELAT-1K1 f & f .FUNCT-1K1 x be FunctionFUNCT-1M1) implies uncurryFUNCT-5K2 f =FUNCT-1R1 {}XBOOLE-0K1 & uncurry'FUNCT-5K4 f =FUNCT-1R1 {}XBOOLE-0K1"
sorry

mtheorem funct_5_th_29:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for x be objectHIDDENM1 holds  for f be FunctionFUNCT-1M1 holds ([:ZFMISC-1K2 X,Y :] <>HIDDENR2 {}XBOOLE-0K1 & domRELAT-1K1 f =XBOOLE-0R4 [:ZFMISC-1K2 X,Y :]) & x inHIDDENR3 X implies ( ex g be FunctionFUNCT-1M1 st ((curryFUNCT-5K1 f .FUNCT-1K1 x =XBOOLE-0R4 g & domRELAT-1K1 g =XBOOLE-0R4 Y) & rngFUNCT-1K2 g c=TARSKIR1 rngFUNCT-1K2 f) & ( for y be objectHIDDENM1 holds y inHIDDENR3 Y implies g .FUNCT-1K1 y =XBOOLE-0R4 f .BINOP-1K1(x,y)))"
sorry

mtheorem funct_5_th_30:
" for x be objectHIDDENM1 holds  for f be FunctionFUNCT-1M1 holds x inHIDDENR3 domRELAT-1K1 (curryFUNCT-5K1 f) implies curryFUNCT-5K1 f .FUNCT-1K1 x be FunctionFUNCT-1M1"
sorry

mtheorem funct_5_th_31:
" for x be objectHIDDENM1 holds  for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds x inHIDDENR3 domRELAT-1K1 (curryFUNCT-5K1 f) & g =XBOOLE-0R4 curryFUNCT-5K1 f .FUNCT-1K1 x implies ((domRELAT-1K1 g =XBOOLE-0R4 proj2XTUPLE-0K13 (domRELAT-1K1 f /\\XBOOLE-0K3 ([:ZFMISC-1K2 {TARSKIK1 x},proj2XTUPLE-0K13 (domRELAT-1K1 f) :])) & domRELAT-1K1 g c=TARSKIR1 proj2XTUPLE-0K13 (domRELAT-1K1 f)) & rngFUNCT-1K2 g c=TARSKIR1 rngFUNCT-1K2 f) & ( for y be objectHIDDENM1 holds y inHIDDENR3 domRELAT-1K1 g implies g .FUNCT-1K1 y =XBOOLE-0R4 f .BINOP-1K1(x,y) & [TARSKIK4 x,y ] inHIDDENR3 domRELAT-1K1 f)"
sorry

mtheorem funct_5_th_32:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for y be objectHIDDENM1 holds  for f be FunctionFUNCT-1M1 holds ([:ZFMISC-1K2 X,Y :] <>HIDDENR2 {}XBOOLE-0K1 & domRELAT-1K1 f =XBOOLE-0R4 [:ZFMISC-1K2 X,Y :]) & y inHIDDENR3 Y implies ( ex g be FunctionFUNCT-1M1 st ((curry'FUNCT-5K3 f .FUNCT-1K1 y =XBOOLE-0R4 g & domRELAT-1K1 g =XBOOLE-0R4 X) & rngFUNCT-1K2 g c=TARSKIR1 rngFUNCT-1K2 f) & ( for x be objectHIDDENM1 holds x inHIDDENR3 X implies g .FUNCT-1K1 x =XBOOLE-0R4 f .BINOP-1K1(x,y)))"
sorry

mtheorem funct_5_th_33:
" for x be objectHIDDENM1 holds  for f be FunctionFUNCT-1M1 holds x inHIDDENR3 domRELAT-1K1 (curry'FUNCT-5K3 f) implies curry'FUNCT-5K3 f .FUNCT-1K1 x be FunctionFUNCT-1M1"
  using funct_5_th_30 sorry

mtheorem funct_5_th_34:
" for x be objectHIDDENM1 holds  for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds x inHIDDENR3 domRELAT-1K1 (curry'FUNCT-5K3 f) & g =XBOOLE-0R4 curry'FUNCT-5K3 f .FUNCT-1K1 x implies ((domRELAT-1K1 g =XBOOLE-0R4 proj1XTUPLE-0K12 (domRELAT-1K1 f /\\XBOOLE-0K3 ([:ZFMISC-1K2 proj1XTUPLE-0K12 (domRELAT-1K1 f),{TARSKIK1 x} :])) & domRELAT-1K1 g c=TARSKIR1 proj1XTUPLE-0K12 (domRELAT-1K1 f)) & rngFUNCT-1K2 g c=TARSKIR1 rngFUNCT-1K2 f) & ( for y be objectHIDDENM1 holds y inHIDDENR3 domRELAT-1K1 g implies g .FUNCT-1K1 y =XBOOLE-0R4 f .BINOP-1K1(y,x) & [TARSKIK4 y,x ] inHIDDENR3 domRELAT-1K1 f)"
sorry

mtheorem funct_5_th_35:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds domRELAT-1K1 f =XBOOLE-0R4 [:ZFMISC-1K2 X,Y :] implies rngFUNCT-1K2 (curryFUNCT-5K1 f) c=TARSKIR1 FuncsFUNCT-2K1(Y,rngFUNCT-1K2 f) & rngFUNCT-1K2 (curry'FUNCT-5K3 f) c=TARSKIR1 FuncsFUNCT-2K1(X,rngFUNCT-1K2 f)"
sorry

mtheorem funct_5_th_36:
" for f be FunctionFUNCT-1M1 holds rngFUNCT-1K2 (curryFUNCT-5K1 f) c=TARSKIR1 PFuncsPARTFUN1K4(proj2XTUPLE-0K13 (domRELAT-1K1 f),rngFUNCT-1K2 f) & rngFUNCT-1K2 (curry'FUNCT-5K3 f) c=TARSKIR1 PFuncsPARTFUN1K4(proj1XTUPLE-0K12 (domRELAT-1K1 f),rngFUNCT-1K2 f)"
sorry

mtheorem funct_5_th_37:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds rngFUNCT-1K2 f c=TARSKIR1 PFuncsPARTFUN1K4(X,Y) implies domRELAT-1K1 (uncurryFUNCT-5K2 f) c=TARSKIR1 [:ZFMISC-1K2 domRELAT-1K1 f,X :] & domRELAT-1K1 (uncurry'FUNCT-5K4 f) c=TARSKIR1 [:ZFMISC-1K2 X,domRELAT-1K1 f :]"
sorry

mtheorem funct_5_th_38:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds (x inHIDDENR3 domRELAT-1K1 f & g =XBOOLE-0R4 f .FUNCT-1K1 x) & y inHIDDENR3 domRELAT-1K1 g implies ([TARSKIK4 x,y ] inHIDDENR3 domRELAT-1K1 (uncurryFUNCT-5K2 f) & uncurryFUNCT-5K2 f .BINOP-1K1(x,y) =XBOOLE-0R4 g .FUNCT-1K1 y) & g .FUNCT-1K1 y inTARSKIR2 rngFUNCT-1K2 (uncurryFUNCT-5K2 f)"
sorry

mtheorem funct_5_th_39:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds (x inHIDDENR3 domRELAT-1K1 f & g =XBOOLE-0R4 f .FUNCT-1K1 x) & y inHIDDENR3 domRELAT-1K1 g implies ([TARSKIK4 y,x ] inHIDDENR3 domRELAT-1K1 (uncurry'FUNCT-5K4 f) & uncurry'FUNCT-5K4 f .BINOP-1K1(y,x) =XBOOLE-0R4 g .FUNCT-1K1 y) & g .FUNCT-1K1 y inTARSKIR2 rngFUNCT-1K2 (uncurry'FUNCT-5K4 f)"
sorry

mtheorem funct_5_th_40:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds rngFUNCT-1K2 f c=TARSKIR1 PFuncsPARTFUN1K4(X,Y) implies rngFUNCT-1K2 (uncurryFUNCT-5K2 f) c=TARSKIR1 Y & rngFUNCT-1K2 (uncurry'FUNCT-5K4 f) c=TARSKIR1 Y"
sorry

mtheorem funct_5_th_41:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds rngFUNCT-1K2 f c=TARSKIR1 FuncsFUNCT-2K1(X,Y) implies rngFUNCT-1K2 (uncurryFUNCT-5K2 f) c=TARSKIR1 Y & rngFUNCT-1K2 (uncurry'FUNCT-5K4 f) c=TARSKIR1 Y"
sorry

mtheorem funct_5_th_42:
"curryFUNCT-5K1 ({}XBOOLE-0K1) =FUNCT-1R1 {}XBOOLE-0K1 & curry'FUNCT-5K3 ({}XBOOLE-0K1) =FUNCT-1R1 {}XBOOLE-0K1"
  using funct_5_def_1 funct_5_th_1 sorry

mtheorem funct_5_th_43:
"uncurryFUNCT-5K2 ({}XBOOLE-0K1) =FUNCT-1R1 {}XBOOLE-0K1 & uncurry'FUNCT-5K4 ({}XBOOLE-0K1) =FUNCT-1R1 {}XBOOLE-0K1"
sorry

mtheorem funct_5_th_44:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f1 be FunctionFUNCT-1M1 holds  for f2 be FunctionFUNCT-1M1 holds (domRELAT-1K1 f1 =XBOOLE-0R4 [:ZFMISC-1K2 X,Y :] & domRELAT-1K1 f2 =XBOOLE-0R4 [:ZFMISC-1K2 X,Y :]) & curryFUNCT-5K1 f1 =FUNCT-1R1 curryFUNCT-5K1 f2 implies f1 =FUNCT-1R1 f2"
sorry

mtheorem funct_5_th_45:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f1 be FunctionFUNCT-1M1 holds  for f2 be FunctionFUNCT-1M1 holds (domRELAT-1K1 f1 =XBOOLE-0R4 [:ZFMISC-1K2 X,Y :] & domRELAT-1K1 f2 =XBOOLE-0R4 [:ZFMISC-1K2 X,Y :]) & curry'FUNCT-5K3 f1 =FUNCT-1R1 curry'FUNCT-5K3 f2 implies f1 =FUNCT-1R1 f2"
sorry

mtheorem funct_5_th_46:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f1 be FunctionFUNCT-1M1 holds  for f2 be FunctionFUNCT-1M1 holds ((rngFUNCT-1K2 f1 c=TARSKIR1 FuncsFUNCT-2K1(X,Y) & rngFUNCT-1K2 f2 c=TARSKIR1 FuncsFUNCT-2K1(X,Y)) & X <>HIDDENR2 {}XBOOLE-0K1) & uncurryFUNCT-5K2 f1 =FUNCT-1R1 uncurryFUNCT-5K2 f2 implies f1 =FUNCT-1R1 f2"
sorry

mtheorem funct_5_th_47:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f1 be FunctionFUNCT-1M1 holds  for f2 be FunctionFUNCT-1M1 holds ((rngFUNCT-1K2 f1 c=TARSKIR1 FuncsFUNCT-2K1(X,Y) & rngFUNCT-1K2 f2 c=TARSKIR1 FuncsFUNCT-2K1(X,Y)) & X <>HIDDENR2 {}XBOOLE-0K1) & uncurry'FUNCT-5K4 f1 =FUNCT-1R1 uncurry'FUNCT-5K4 f2 implies f1 =FUNCT-1R1 f2"
sorry

mtheorem funct_5_th_48:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds rngFUNCT-1K2 f c=TARSKIR1 FuncsFUNCT-2K1(X,Y) & X <>HIDDENR2 {}XBOOLE-0K1 implies curryFUNCT-5K1 (uncurryFUNCT-5K2 f) =FUNCT-1R1 f & curry'FUNCT-5K3 (uncurry'FUNCT-5K4 f) =FUNCT-1R1 f"
sorry

mtheorem funct_5_th_49:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds domRELAT-1K1 f =XBOOLE-0R4 [:ZFMISC-1K2 X,Y :] implies uncurryFUNCT-5K2 (curryFUNCT-5K1 f) =FUNCT-1R1 f & uncurry'FUNCT-5K4 (curry'FUNCT-5K3 f) =FUNCT-1R1 f"
sorry

mtheorem funct_5_th_50:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds domRELAT-1K1 f c=TARSKIR1 [:ZFMISC-1K2 X,Y :] implies uncurryFUNCT-5K2 (curryFUNCT-5K1 f) =FUNCT-1R1 f & uncurry'FUNCT-5K4 (curry'FUNCT-5K3 f) =FUNCT-1R1 f"
sorry

mtheorem funct_5_th_51:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds rngFUNCT-1K2 f c=TARSKIR1 PFuncsPARTFUN1K4(X,Y) &  not {}XBOOLE-0K1 inTARSKIR2 rngFUNCT-1K2 f implies curryFUNCT-5K1 (uncurryFUNCT-5K2 f) =FUNCT-1R1 f & curry'FUNCT-5K3 (uncurry'FUNCT-5K4 f) =FUNCT-1R1 f"
sorry

mtheorem funct_5_th_52:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f1 be FunctionFUNCT-1M1 holds  for f2 be FunctionFUNCT-1M1 holds (domRELAT-1K1 f1 c=TARSKIR1 [:ZFMISC-1K2 X,Y :] & domRELAT-1K1 f2 c=TARSKIR1 [:ZFMISC-1K2 X,Y :]) & curryFUNCT-5K1 f1 =FUNCT-1R1 curryFUNCT-5K1 f2 implies f1 =FUNCT-1R1 f2"
sorry

mtheorem funct_5_th_53:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f1 be FunctionFUNCT-1M1 holds  for f2 be FunctionFUNCT-1M1 holds (domRELAT-1K1 f1 c=TARSKIR1 [:ZFMISC-1K2 X,Y :] & domRELAT-1K1 f2 c=TARSKIR1 [:ZFMISC-1K2 X,Y :]) & curry'FUNCT-5K3 f1 =FUNCT-1R1 curry'FUNCT-5K3 f2 implies f1 =FUNCT-1R1 f2"
sorry

mtheorem funct_5_th_54:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f1 be FunctionFUNCT-1M1 holds  for f2 be FunctionFUNCT-1M1 holds (((rngFUNCT-1K2 f1 c=TARSKIR1 PFuncsPARTFUN1K4(X,Y) & rngFUNCT-1K2 f2 c=TARSKIR1 PFuncsPARTFUN1K4(X,Y)) &  not {}XBOOLE-0K1 inTARSKIR2 rngFUNCT-1K2 f1) &  not {}XBOOLE-0K1 inTARSKIR2 rngFUNCT-1K2 f2) & uncurryFUNCT-5K2 f1 =FUNCT-1R1 uncurryFUNCT-5K2 f2 implies f1 =FUNCT-1R1 f2"
sorry

mtheorem funct_5_th_55:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f1 be FunctionFUNCT-1M1 holds  for f2 be FunctionFUNCT-1M1 holds (((rngFUNCT-1K2 f1 c=TARSKIR1 PFuncsPARTFUN1K4(X,Y) & rngFUNCT-1K2 f2 c=TARSKIR1 PFuncsPARTFUN1K4(X,Y)) &  not {}XBOOLE-0K1 inTARSKIR2 rngFUNCT-1K2 f1) &  not {}XBOOLE-0K1 inTARSKIR2 rngFUNCT-1K2 f2) & uncurry'FUNCT-5K4 f1 =FUNCT-1R1 uncurry'FUNCT-5K4 f2 implies f1 =FUNCT-1R1 f2"
sorry

mtheorem funct_5_th_56:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds X c=TARSKIR1 Y implies FuncsFUNCT-2K1(Z,X) c=TARSKIR1 FuncsFUNCT-2K1(Z,Y)"
sorry

mtheorem funct_5_th_57:
" for X be setHIDDENM2 holds FuncsFUNCT-2K1({}XBOOLE-0K1,X) =XBOOLE-0R4 {TARSKIK1 {}XBOOLE-0K1 }"
sorry

mtheorem funct_5_th_58:
" for X be setHIDDENM2 holds  for x be objectHIDDENM1 holds (X,FuncsFUNCT-2K1({TARSKIK1 x},X))are-equipotentWELLORD2R2 & cardCARD-1K1 X =XBOOLE-0R4 cardCARD-1K1 (FuncsFUNCT-2K1({TARSKIK1 x},X))"
sorry

mtheorem funct_5_th_59:
" for X be setHIDDENM2 holds  for x be objectHIDDENM1 holds FuncsFUNCT-2K9(X,{TARSKIK1 x}) =XBOOLE-0R4 {DOMAIN-1K6\<^bsub>(boolZFMISC-1K1 ([:ZFMISC-1K2 X,{TARSKIK1 x} :]))\<^esub> X -->FUNCOP-1K7 x }"
sorry

mtheorem funct_5_th_60:
" for X1 be setHIDDENM2 holds  for X2 be setHIDDENM2 holds  for Y1 be setHIDDENM2 holds  for Y2 be setHIDDENM2 holds (X1,Y1)are-equipotentWELLORD2R2 & (X2,Y2)are-equipotentWELLORD2R2 implies (FuncsFUNCT-2K1(X1,X2),FuncsFUNCT-2K1(Y1,Y2))are-equipotentWELLORD2R2 & cardCARD-1K1 (FuncsFUNCT-2K1(X1,X2)) =XBOOLE-0R4 cardCARD-1K1 (FuncsFUNCT-2K1(Y1,Y2))"
sorry

mtheorem funct_5_th_61:
" for X1 be setHIDDENM2 holds  for X2 be setHIDDENM2 holds  for Y1 be setHIDDENM2 holds  for Y2 be setHIDDENM2 holds cardCARD-1K1 X1 =XBOOLE-0R4 cardCARD-1K1 Y1 & cardCARD-1K1 X2 =XBOOLE-0R4 cardCARD-1K1 Y2 implies cardCARD-1K1 (FuncsFUNCT-2K1(X1,X2)) =XBOOLE-0R4 cardCARD-1K1 (FuncsFUNCT-2K1(Y1,Y2))"
sorry

mtheorem funct_5_th_62:
" for X be setHIDDENM2 holds  for X1 be setHIDDENM2 holds  for X2 be setHIDDENM2 holds X1 missesXBOOLE-0R1 X2 implies (FuncsFUNCT-2K1(X1 \\/XBOOLE-0K2 X2,X),[:ZFMISC-1K2 FuncsFUNCT-2K1(X1,X),FuncsFUNCT-2K1(X2,X) :])are-equipotentWELLORD2R2 & cardCARD-1K1 (FuncsFUNCT-2K1(X1 \\/XBOOLE-0K2 X2,X)) =XBOOLE-0R4 cardCARD-1K1 ([:ZFMISC-1K2 FuncsFUNCT-2K1(X1,X),FuncsFUNCT-2K1(X2,X) :])"
sorry

mtheorem funct_5_th_63:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds (FuncsFUNCT-2K1([:ZFMISC-1K2 X,Y :],Z),FuncsFUNCT-2K1(X,FuncsFUNCT-2K1(Y,Z)))are-equipotentWELLORD2R2 & cardCARD-1K1 (FuncsFUNCT-2K1([:ZFMISC-1K2 X,Y :],Z)) =XBOOLE-0R4 cardCARD-1K1 (FuncsFUNCT-2K1(X,FuncsFUNCT-2K1(Y,Z)))"
sorry

mtheorem funct_5_th_64:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds (FuncsFUNCT-2K1(Z,[:ZFMISC-1K2 X,Y :]),[:ZFMISC-1K2 FuncsFUNCT-2K1(Z,X),FuncsFUNCT-2K1(Z,Y) :])are-equipotentWELLORD2R2 & cardCARD-1K1 (FuncsFUNCT-2K1(Z,[:ZFMISC-1K2 X,Y :])) =XBOOLE-0R4 cardCARD-1K1 ([:ZFMISC-1K2 FuncsFUNCT-2K1(Z,X),FuncsFUNCT-2K1(Z,Y) :])"
sorry

mtheorem funct_5_th_65:
" for X be setHIDDENM2 holds  for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds x <>HIDDENR2 y implies (FuncsFUNCT-2K9(X,{TARSKIK2 x,y }),boolZFMISC-1K1 X)are-equipotentWELLORD2R2 & cardCARD-1K1 (FuncsFUNCT-2K9(X,{TARSKIK2 x,y })) =XBOOLE-0R4 cardCARD-1K1 (boolZFMISC-1K1 X)"
sorry

mtheorem funct_5_th_66:
" for X be setHIDDENM2 holds  for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds x <>HIDDENR2 y implies (FuncsFUNCT-2K1({TARSKIK2 x,y },X),[:ZFMISC-1K2 X,X :])are-equipotentWELLORD2R2 & cardCARD-1K1 (FuncsFUNCT-2K1({TARSKIK2 x,y },X)) =XBOOLE-0R4 cardCARD-1K1 ([:ZFMISC-1K2 X,X :])"
sorry

(*begin*)
abbreviation(input) FUNCT_5K5("op0FUNCT-5K5" 210) where
  "op0FUNCT-5K5 \<equiv> 0ORDINAL1K5"

abbreviation(input) FUNCT_5K6("op0FUNCT-5K6" 210) where
  "op0FUNCT-5K6 \<equiv> 0ORDINAL1K5"

mtheorem funct_5_add_1:
"cluster 0ORDINAL1K5 as-term-is ElementSUBSET-1M1-of {TARSKIK1 0ORDINAL1K5 }"
proof
(*coherence*)
  show "0ORDINAL1K5 be ElementSUBSET-1M1-of {TARSKIK1 0ORDINAL1K5 }"
    using tarski_def_1 sorry
qed "sorry"

mdef funct_5_def_5 ("op1FUNCT-5K7" 210 ) where
"func op1FUNCT-5K7 \<rightarrow> setHIDDENM2 equals
  (0ORDINAL1K5).-->FUNCOP-1K17 (0ORDINAL1K5)"
proof-
  (*coherence*)
    show "(0ORDINAL1K5).-->FUNCOP-1K17 (0ORDINAL1K5) be setHIDDENM2"
       sorry
qed "sorry"

mdef funct_5_def_6 ("op2FUNCT-5K8" 210 ) where
"func op2FUNCT-5K8 \<rightarrow> setHIDDENM2 equals
  (0ORDINAL1K5,0ORDINAL1K5):->FUNCOP-1K19 (0ORDINAL1K5)"
proof-
  (*coherence*)
    show "(0ORDINAL1K5,0ORDINAL1K5):->FUNCOP-1K19 (0ORDINAL1K5) be setHIDDENM2"
       sorry
qed "sorry"

abbreviation(input) FUNCT_5K9("op1FUNCT-5K9" 210) where
  "op1FUNCT-5K9 \<equiv> op1FUNCT-5K7"

mtheorem funct_5_add_2:
"cluster op1FUNCT-5K7 as-term-is UnOpBINOP-1M1-of {TARSKIK1 0ORDINAL1K5 }"
proof
(*coherence*)
  show "op1FUNCT-5K7 be UnOpBINOP-1M1-of {TARSKIK1 0ORDINAL1K5 }"
     sorry
qed "sorry"

abbreviation(input) FUNCT_5K10("op2FUNCT-5K10" 210) where
  "op2FUNCT-5K10 \<equiv> op2FUNCT-5K8"

mtheorem funct_5_add_3:
"cluster op2FUNCT-5K8 as-term-is BinOpBINOP-1M2-of {TARSKIK1 0ORDINAL1K5 }"
proof
(*coherence*)
  show "op2FUNCT-5K8 be BinOpBINOP-1M2-of {TARSKIK1 0ORDINAL1K5 }"
     sorry
qed "sorry"

reserve C, D, E for " non emptyXBOOLE-0V1\<bar>setHIDDENM2"
reserve c for "ElementSUBSET-1M1-of C"
reserve d for "ElementSUBSET-1M1-of D"
syntax FUNCT_5K11 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ .FUNCT-5K11\<^bsub>'( _ , _ , _ , _ ')\<^esub>  _ " [200,0,0,0,0,200]200)
translations "f .FUNCT-5K11\<^bsub>(D,X,E,F)\<^esub> d" \<rightharpoonup> "f .FUNCT-1K1 d"

mtheorem funct_5_add_4:
  mlet "D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "X be setHIDDENM2", "E be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "F be FUNCTION-DOMAINFUNCT-2M3-of(X,E)", "f be FunctionFUNCT-2M1-of(D,F)", "d be ElementSUBSET-1M1-of D"
"cluster f .FUNCT-1K1 d as-term-is ElementFUNCT-2M4\<^bsub>(X,E)\<^esub>-of F"
proof
(*coherence*)
  show "f .FUNCT-1K1 d be ElementFUNCT-2M4\<^bsub>(X,E)\<^esub>-of F"
sorry
qed "sorry"

reserve f for "FunctionFUNCT-2M1-of([:ZFMISC-1K2 C,D :],E)"
mtheorem funct_5_th_67:
" for C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for E be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of([:ZFMISC-1K2 C,D :],E) holds curryFUNCT-5K1 f be FunctionFUNCT-2M1-of(C,FuncsFUNCT-2K9(D,E))"
sorry

mtheorem funct_5_th_68:
" for C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for E be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of([:ZFMISC-1K2 C,D :],E) holds curry'FUNCT-5K3 f be FunctionFUNCT-2M1-of(D,FuncsFUNCT-2K9(C,E))"
sorry

syntax FUNCT_5K12 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" ("curryFUNCT-5K12\<^bsub>'( _ , _ , _ ')\<^esub>  _ " [0,0,0,228]228)
translations "curryFUNCT-5K12\<^bsub>(C,D,E)\<^esub> f" \<rightharpoonup> "curryFUNCT-5K1 f"

mtheorem funct_5_add_5:
  mlet "C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "E be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "f be FunctionFUNCT-2M1-of([:ZFMISC-1K2 C,D :],E)"
"cluster curryFUNCT-5K1 f as-term-is FunctionFUNCT-2M1-of(C,FuncsFUNCT-2K9(D,E))"
proof
(*coherence*)
  show "curryFUNCT-5K1 f be FunctionFUNCT-2M1-of(C,FuncsFUNCT-2K9(D,E))"
    using funct_5_th_67 sorry
qed "sorry"

syntax FUNCT_5K13 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" ("curry''FUNCT-5K13\<^bsub>'( _ , _ , _ ')\<^esub>  _ " [0,0,0,228]228)
translations "curry'FUNCT-5K13\<^bsub>(C,D,E)\<^esub> f" \<rightharpoonup> "curry'FUNCT-5K3 f"

mtheorem funct_5_add_6:
  mlet "C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "E be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "f be FunctionFUNCT-2M1-of([:ZFMISC-1K2 C,D :],E)"
"cluster curry'FUNCT-5K3 f as-term-is FunctionFUNCT-2M1-of(D,FuncsFUNCT-2K9(C,E))"
proof
(*coherence*)
  show "curry'FUNCT-5K3 f be FunctionFUNCT-2M1-of(D,FuncsFUNCT-2K9(C,E))"
    using funct_5_th_68 sorry
qed "sorry"

mtheorem funct_5_th_69:
" for C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for E be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for c be ElementSUBSET-1M1-of C holds  for d be ElementSUBSET-1M1-of D holds  for f be FunctionFUNCT-2M1-of([:ZFMISC-1K2 C,D :],E) holds f .BINOP-1K2\<^bsub>(C,D,E)\<^esub>(c,d) =XBOOLE-0R4 (curryFUNCT-5K12\<^bsub>(C,D,E)\<^esub> f .FUNCT-5K11\<^bsub>(C,D,E,FuncsFUNCT-2K9(D,E))\<^esub> c).FUNCT-2K3\<^bsub>(D,E)\<^esub> d"
sorry

mtheorem funct_5_th_70:
" for C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for E be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for c be ElementSUBSET-1M1-of C holds  for d be ElementSUBSET-1M1-of D holds  for f be FunctionFUNCT-2M1-of([:ZFMISC-1K2 C,D :],E) holds f .BINOP-1K2\<^bsub>(C,D,E)\<^esub>(c,d) =XBOOLE-0R4 (curry'FUNCT-5K13\<^bsub>(C,D,E)\<^esub> f .FUNCT-5K11\<^bsub>(D,C,E,FuncsFUNCT-2K9(C,E))\<^esub> d).FUNCT-2K3\<^bsub>(C,E)\<^esub> c"
sorry

syntax FUNCT_5K14 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" ("uncurryFUNCT-5K14\<^bsub>'( _ , _ , _ ')\<^esub>  _ " [0,0,0,228]228)
translations "uncurryFUNCT-5K14\<^bsub>(A,B,C)\<^esub> f" \<rightharpoonup> "uncurryFUNCT-5K2 f"

mtheorem funct_5_add_7:
  mlet "A be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "B be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "f be FunctionFUNCT-2M1-of(A,FuncsFUNCT-2K9(B,C))"
"cluster uncurryFUNCT-5K2 f as-term-is FunctionFUNCT-2M1-of([:ZFMISC-1K2 A,B :],C)"
proof
(*coherence*)
  show "uncurryFUNCT-5K2 f be FunctionFUNCT-2M1-of([:ZFMISC-1K2 A,B :],C)"
sorry
qed "sorry"

mtheorem funct_5_th_71:
" for A be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for B be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(A,FuncsFUNCT-2K9(B,C)) holds curryFUNCT-5K12\<^bsub>(A,B,C)\<^esub> (uncurryFUNCT-5K14\<^bsub>(A,B,C)\<^esub> f) =FUNCT-2R2\<^bsub>(A,FuncsFUNCT-2K9(B,C))\<^esub> f"
sorry

mtheorem funct_5_th_72:
" for A be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for B be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(A,FuncsFUNCT-2K9(B,C)) holds  for a be ElementSUBSET-1M1-of A holds  for b be ElementSUBSET-1M1-of B holds uncurryFUNCT-5K14\<^bsub>(A,B,C)\<^esub> f .BINOP-1K2\<^bsub>(A,B,C)\<^esub>(a,b) =XBOOLE-0R4 (f .FUNCT-5K11\<^bsub>(A,B,C,FuncsFUNCT-2K9(B,C))\<^esub> a).FUNCT-2K3\<^bsub>(B,C)\<^esub> b"
sorry

end
