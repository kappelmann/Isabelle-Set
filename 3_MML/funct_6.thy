theory funct_6
  imports binop_1 card_3
begin
(*begin*)
reserve x, y, y1, y2, z, a, b for "objectHIDDENM1"
reserve X, Y, Z, V1, V2 for "setHIDDENM2"
reserve f, g, h, h9, f1, f2 for "FunctionFUNCT-1M1"
reserve P for "PermutationFUNCT-2M2-of X"
mtheorem funct_6_th_1:
" for f be FunctionFUNCT-1M1 holds productCARD-3K4 f c=TARSKIR1 FuncsFUNCT-2K1(domRELAT-1K1 f,UnionCARD-3K3 f)"
sorry

(*begin*)
mtheorem funct_6_th_2:
" for x be objectHIDDENM1 holds  for f be FunctionFUNCT-1M1 holds x inHIDDENR3 domRELAT-1K1 (~FUNCT-4K2 f) implies ( ex y be objectHIDDENM1 st  ex z be objectHIDDENM1 st x =HIDDENR1 [TARSKIK4 y,z ])"
sorry

mtheorem funct_6_th_3:
" for z be objectHIDDENM1 holds  for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds ~FUNCT-4K4\<^bsub>(X,Y,{TARSKIK1 z})\<^esub> ([:ZFMISC-1K2 X,Y :] -->FUNCOP-1K7 z) =BINOP-1R13\<^bsub>(Y,X,{TARSKIK1 z})\<^esub> [:ZFMISC-1K2 Y,X :] -->FUNCOP-1K7 z"
sorry

mtheorem funct_6_th_4:
" for f be FunctionFUNCT-1M1 holds curryFUNCT-5K1 f =FUNCT-1R1 curry'FUNCT-5K3 (~FUNCT-4K2 f) & uncurryFUNCT-5K2 f =FUNCT-1R1 ~FUNCT-4K2 (uncurry'FUNCT-5K4 f)"
sorry

mtheorem funct_6_th_5:
" for z be objectHIDDENM1 holds  for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds [:ZFMISC-1K2 X,Y :] <>HIDDENR2 {}XBOOLE-0K1 implies curryFUNCT-5K1 ([:ZFMISC-1K2 X,Y :] -->FUNCOP-1K7 z) =FUNCT-1R1 X -->FUNCOP-1K7 (Y -->FUNCOP-1K7 z) & curry'FUNCT-5K3 ([:ZFMISC-1K2 X,Y :] -->FUNCOP-1K7 z) =FUNCT-1R1 Y -->FUNCOP-1K7 (X -->FUNCOP-1K7 z)"
sorry

mtheorem funct_6_th_6:
" for z be objectHIDDENM1 holds  for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds uncurryFUNCT-5K2 (X -->FUNCOP-1K7 (Y -->FUNCOP-1K7 z)) =FUNCT-1R1 [:ZFMISC-1K2 X,Y :] -->FUNCOP-1K7 z & uncurry'FUNCT-5K4 (X -->FUNCOP-1K7 (Y -->FUNCOP-1K7 z)) =FUNCT-1R1 [:ZFMISC-1K2 Y,X :] -->FUNCOP-1K7 z"
sorry

mtheorem funct_6_th_7:
" for x be objectHIDDENM1 holds  for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds x inHIDDENR3 domRELAT-1K1 f & g =XBOOLE-0R4 f .FUNCT-1K1 x implies rngFUNCT-1K2 g c=TARSKIR1 rngFUNCT-1K2 (uncurryFUNCT-5K2 f) & rngFUNCT-1K2 g c=TARSKIR1 rngFUNCT-1K2 (uncurry'FUNCT-5K4 f)"
sorry

mtheorem funct_6_th_8:
" for X be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds ((domRELAT-1K1 (uncurryFUNCT-5K2 (X -->FUNCOP-1K7 f)) =XBOOLE-0R4 [:ZFMISC-1K2 X,domRELAT-1K1 f :] & rngFUNCT-1K2 (uncurryFUNCT-5K2 (X -->FUNCOP-1K7 f)) c=TARSKIR1 rngFUNCT-1K2 f) & domRELAT-1K1 (uncurry'FUNCT-5K4 (X -->FUNCOP-1K7 f)) =XBOOLE-0R4 [:ZFMISC-1K2 domRELAT-1K1 f,X :]) & rngFUNCT-1K2 (uncurry'FUNCT-5K4 (X -->FUNCOP-1K7 f)) c=TARSKIR1 rngFUNCT-1K2 f"
sorry

mtheorem funct_6_th_9:
" for X be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds X <>HIDDENR2 {}XBOOLE-0K1 implies rngFUNCT-1K2 (uncurryFUNCT-5K2 (X -->FUNCOP-1K7 f)) =XBOOLE-0R4 rngFUNCT-1K2 f & rngFUNCT-1K2 (uncurry'FUNCT-5K4 (X -->FUNCOP-1K7 f)) =XBOOLE-0R4 rngFUNCT-1K2 f"
sorry

mtheorem funct_6_th_10:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds [:ZFMISC-1K2 X,Y :] <>HIDDENR2 {}XBOOLE-0K1 & f inTARSKIR2 FuncsFUNCT-2K1([:ZFMISC-1K2 X,Y :],Z) implies curryFUNCT-5K1 f inTARSKIR2 FuncsFUNCT-2K1(X,FuncsFUNCT-2K1(Y,Z)) & curry'FUNCT-5K3 f inTARSKIR2 FuncsFUNCT-2K1(Y,FuncsFUNCT-2K1(X,Z))"
sorry

mtheorem funct_6_th_11:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds f inTARSKIR2 FuncsFUNCT-2K1(X,FuncsFUNCT-2K1(Y,Z)) implies uncurryFUNCT-5K2 f inTARSKIR2 FuncsFUNCT-2K1([:ZFMISC-1K2 X,Y :],Z) & uncurry'FUNCT-5K4 f inTARSKIR2 FuncsFUNCT-2K1([:ZFMISC-1K2 Y,X :],Z)"
sorry

mtheorem funct_6_th_12:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds  for V1 be setHIDDENM2 holds  for V2 be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds (curryFUNCT-5K1 f inTARSKIR2 FuncsFUNCT-2K1(X,FuncsFUNCT-2K1(Y,Z)) or curry'FUNCT-5K3 f inTARSKIR2 FuncsFUNCT-2K1(Y,FuncsFUNCT-2K1(X,Z))) & domRELAT-1K1 f c=TARSKIR1 [:ZFMISC-1K2 V1,V2 :] implies f inTARSKIR2 FuncsFUNCT-2K1([:ZFMISC-1K2 X,Y :],Z)"
sorry

mtheorem funct_6_th_13:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds  for V1 be setHIDDENM2 holds  for V2 be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds ((uncurryFUNCT-5K2 f inTARSKIR2 FuncsFUNCT-2K1([:ZFMISC-1K2 X,Y :],Z) or uncurry'FUNCT-5K4 f inTARSKIR2 FuncsFUNCT-2K1([:ZFMISC-1K2 Y,X :],Z)) & rngFUNCT-1K2 f c=TARSKIR1 PFuncsPARTFUN1K4(V1,V2)) & domRELAT-1K1 f =XBOOLE-0R4 X implies f inTARSKIR2 FuncsFUNCT-2K1(X,FuncsFUNCT-2K1(Y,Z))"
sorry

mtheorem funct_6_th_14:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds f inTARSKIR2 PFuncsPARTFUN1K4([:ZFMISC-1K2 X,Y :],Z) implies curryFUNCT-5K1 f inTARSKIR2 PFuncsPARTFUN1K4(X,PFuncsPARTFUN1K4(Y,Z)) & curry'FUNCT-5K3 f inTARSKIR2 PFuncsPARTFUN1K4(Y,PFuncsPARTFUN1K4(X,Z))"
sorry

mtheorem funct_6_th_15:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds f inTARSKIR2 PFuncsPARTFUN1K4(X,PFuncsPARTFUN1K4(Y,Z)) implies uncurryFUNCT-5K2 f inTARSKIR2 PFuncsPARTFUN1K4([:ZFMISC-1K2 X,Y :],Z) & uncurry'FUNCT-5K4 f inTARSKIR2 PFuncsPARTFUN1K4([:ZFMISC-1K2 Y,X :],Z)"
sorry

mtheorem funct_6_th_16:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds  for V1 be setHIDDENM2 holds  for V2 be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds (curryFUNCT-5K1 f inTARSKIR2 PFuncsPARTFUN1K4(X,PFuncsPARTFUN1K4(Y,Z)) or curry'FUNCT-5K3 f inTARSKIR2 PFuncsPARTFUN1K4(Y,PFuncsPARTFUN1K4(X,Z))) & domRELAT-1K1 f c=TARSKIR1 [:ZFMISC-1K2 V1,V2 :] implies f inTARSKIR2 PFuncsPARTFUN1K4([:ZFMISC-1K2 X,Y :],Z)"
sorry

mtheorem funct_6_th_17:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds  for V1 be setHIDDENM2 holds  for V2 be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds ((uncurryFUNCT-5K2 f inTARSKIR2 PFuncsPARTFUN1K4([:ZFMISC-1K2 X,Y :],Z) or uncurry'FUNCT-5K4 f inTARSKIR2 PFuncsPARTFUN1K4([:ZFMISC-1K2 Y,X :],Z)) & rngFUNCT-1K2 f c=TARSKIR1 PFuncsPARTFUN1K4(V1,V2)) & domRELAT-1K1 f c=TARSKIR1 X implies f inTARSKIR2 PFuncsPARTFUN1K4(X,PFuncsPARTFUN1K4(Y,Z))"
sorry

(*begin*)
(*\$CD*)
(*\$CT 4*)
mdef funct_6_def_2 ("domsFUNCT-6K1  _ " [228]228 ) where
  mlet "f be Function-yieldingFUNCOP-1V1\<bar>FunctionFUNCT-1M1"
"func domsFUNCT-6K1 f \<rightarrow> FunctionFUNCT-1M1 means
  \<lambda>it. domRELAT-1K1 it =XBOOLE-0R4 domRELAT-1K1 f & ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 f implies it .FUNCT-1K1 x =XBOOLE-0R4 proj1XTUPLE-0K12 (f .FUNCT-1K1 x))"
proof-
  (*existence*)
    show " ex it be FunctionFUNCT-1M1 st domRELAT-1K1 it =XBOOLE-0R4 domRELAT-1K1 f & ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 f implies it .FUNCT-1K1 x =XBOOLE-0R4 proj1XTUPLE-0K12 (f .FUNCT-1K1 x))"
sorry
  (*uniqueness*)
    show " for it1 be FunctionFUNCT-1M1 holds  for it2 be FunctionFUNCT-1M1 holds (domRELAT-1K1 it1 =XBOOLE-0R4 domRELAT-1K1 f & ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 f implies it1 .FUNCT-1K1 x =XBOOLE-0R4 proj1XTUPLE-0K12 (f .FUNCT-1K1 x))) & (domRELAT-1K1 it2 =XBOOLE-0R4 domRELAT-1K1 f & ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 f implies it2 .FUNCT-1K1 x =XBOOLE-0R4 proj1XTUPLE-0K12 (f .FUNCT-1K1 x))) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mdef funct_6_def_3 ("rngsFUNCT-6K2  _ " [228]228 ) where
  mlet "f be Function-yieldingFUNCOP-1V1\<bar>FunctionFUNCT-1M1"
"func rngsFUNCT-6K2 f \<rightarrow> FunctionFUNCT-1M1 means
  \<lambda>it. domRELAT-1K1 it =XBOOLE-0R4 domRELAT-1K1 f & ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 f implies it .FUNCT-1K1 x =XBOOLE-0R4 proj2XTUPLE-0K13 (f .FUNCT-1K1 x))"
proof-
  (*existence*)
    show " ex it be FunctionFUNCT-1M1 st domRELAT-1K1 it =XBOOLE-0R4 domRELAT-1K1 f & ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 f implies it .FUNCT-1K1 x =XBOOLE-0R4 proj2XTUPLE-0K13 (f .FUNCT-1K1 x))"
sorry
  (*uniqueness*)
    show " for it1 be FunctionFUNCT-1M1 holds  for it2 be FunctionFUNCT-1M1 holds (domRELAT-1K1 it1 =XBOOLE-0R4 domRELAT-1K1 f & ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 f implies it1 .FUNCT-1K1 x =XBOOLE-0R4 proj2XTUPLE-0K13 (f .FUNCT-1K1 x))) & (domRELAT-1K1 it2 =XBOOLE-0R4 domRELAT-1K1 f & ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 f implies it2 .FUNCT-1K1 x =XBOOLE-0R4 proj2XTUPLE-0K13 (f .FUNCT-1K1 x))) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mdef funct_6_def_4 ("meetFUNCT-6K3  _ " [228]228 ) where
  mlet "f be FunctionFUNCT-1M1"
"func meetFUNCT-6K3 f \<rightarrow> setHIDDENM2 equals
  meetSETFAM-1K1 (rngFUNCT-1K2 f)"
proof-
  (*coherence*)
    show "meetSETFAM-1K1 (rngFUNCT-1K2 f) be setHIDDENM2"
       sorry
qed "sorry"

mtheorem funct_6_th_22:
" for x be objectHIDDENM1 holds  for g be FunctionFUNCT-1M1 holds  for f be Function-yieldingFUNCOP-1V1\<bar>FunctionFUNCT-1M1 holds x inHIDDENR3 domRELAT-1K1 f & g =FUNCT-1R1 f .FUNCT-1K1 x implies ((x inHIDDENR3 domRELAT-1K1 (domsFUNCT-6K1 f) & domsFUNCT-6K1 f .FUNCT-1K1 x =XBOOLE-0R4 domRELAT-1K1 g) & x inHIDDENR3 domRELAT-1K1 (rngsFUNCT-6K2 f)) & rngsFUNCT-6K2 f .FUNCT-1K1 x =XBOOLE-0R4 rngFUNCT-1K2 g"
  using funct_6_def_2 funct_6_def_3 sorry

mtheorem funct_6_th_23:
"domsFUNCT-6K1 ({}XBOOLE-0K1) =FUNCT-1R1 {}XBOOLE-0K1 & rngsFUNCT-6K2 ({}XBOOLE-0K1) =FUNCT-1R1 {}XBOOLE-0K1"
  using funct_6_def_2 funct_6_def_3 relat_1_th_38 sorry

mtheorem funct_6_th_24:
" for X be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds domsFUNCT-6K1 (X -->FUNCOP-1K7 f) =FUNCT-1R1 X -->FUNCOP-1K7 domRELAT-1K1 f & rngsFUNCT-6K2 (X -->FUNCOP-1K7 f) =FUNCT-1R1 X -->FUNCOP-1K7 rngFUNCT-1K2 f"
sorry

mtheorem funct_6_th_25:
" for f be FunctionFUNCT-1M1 holds f <>HIDDENR2 {}XBOOLE-0K1 implies ( for x be objectHIDDENM1 holds x inHIDDENR3 meetFUNCT-6K3 f iff ( for y be objectHIDDENM1 holds y inHIDDENR3 domRELAT-1K1 f implies x inHIDDENR3 f .FUNCT-1K1 y))"
sorry

mtheorem funct_6_th_26:
" for Y be setHIDDENM2 holds UnionCARD-3K3 ({}XBOOLE-0K1 -->FUNCOP-1K7 Y) =XBOOLE-0R4 {}XBOOLE-0K1 & meetFUNCT-6K3 ({}XBOOLE-0K1 -->FUNCOP-1K7 Y) =XBOOLE-0R4 {}XBOOLE-0K1"
sorry

mtheorem funct_6_th_27:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X <>HIDDENR2 {}XBOOLE-0K1 implies UnionCARD-3K3 (X -->FUNCOP-1K7 Y) =XBOOLE-0R4 Y & meetFUNCT-6K3 (X -->FUNCOP-1K7 Y) =XBOOLE-0R4 Y"
sorry

mdef funct_6_def_5 (" _ ..FUNCT-6K4'( _ , _ ')" [200,0,0]200 ) where
  mlet "f be FunctionFUNCT-1M1", "x be objectHIDDENM1", "y be objectHIDDENM1"
"func f ..FUNCT-6K4(x,y) \<rightarrow> setHIDDENM2 equals
  uncurryFUNCT-5K2 f .BINOP-1K1(x,y)"
proof-
  (*coherence*)
    show "uncurryFUNCT-5K2 f .BINOP-1K1(x,y) be setHIDDENM2"
       sorry
qed "sorry"

mtheorem funct_6_th_28:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for X be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds x inHIDDENR3 X & y inHIDDENR3 domRELAT-1K1 f implies (X -->FUNCOP-1K7 f)..FUNCT-6K4(x,y) =XBOOLE-0R4 f .FUNCT-1K1 y"
sorry

(*begin*)
mdef funct_6_def_6 ("<:FUNCT-6K5  _ :>" [0]164 ) where
  mlet "f be Function-yieldingFUNCOP-1V1\<bar>FunctionFUNCT-1M1"
"func <:FUNCT-6K5 f:> \<rightarrow> FunctionFUNCT-1M1 equals
  curryFUNCT-5K1 (uncurry'FUNCT-5K4 f |RELAT-1K8 ([:ZFMISC-1K2 meetFUNCT-6K3 (domsFUNCT-6K1 f),domRELAT-1K1 f :]))"
proof-
  (*coherence*)
    show "curryFUNCT-5K1 (uncurry'FUNCT-5K4 f |RELAT-1K8 ([:ZFMISC-1K2 meetFUNCT-6K3 (domsFUNCT-6K1 f),domRELAT-1K1 f :])) be FunctionFUNCT-1M1"
       sorry
qed "sorry"

mtheorem funct_6_th_29:
" for f be Function-yieldingFUNCOP-1V1\<bar>FunctionFUNCT-1M1 holds domRELAT-1K1 (<:FUNCT-6K5 f:>) =XBOOLE-0R4 meetFUNCT-6K3 (domsFUNCT-6K1 f) & rngFUNCT-1K2 (<:FUNCT-6K5 f:>) c=TARSKIR1 productCARD-3K4 (rngsFUNCT-6K2 f)"
sorry

mtheorem funct_6_cl_1:
  mlet "f be Function-yieldingFUNCOP-1V1\<bar>FunctionFUNCT-1M1"
"cluster <:FUNCT-6K5 f:> as-term-is Function-yieldingFUNCOP-1V1"
proof
(*coherence*)
  show "<:FUNCT-6K5 f:> be Function-yieldingFUNCOP-1V1"
     sorry
qed "sorry"

(*\$CT*)
mtheorem funct_6_th_31:
" for x be objectHIDDENM1 holds  for g be FunctionFUNCT-1M1 holds  for f be Function-yieldingFUNCOP-1V1\<bar>FunctionFUNCT-1M1 holds x inHIDDENR3 domRELAT-1K1 (<:FUNCT-6K5 f:>) & g =FUNCT-1R1 (<:FUNCT-6K5 f:>).FUNCT-1K1 x implies domRELAT-1K1 g =XBOOLE-0R4 domRELAT-1K1 f & ( for y be objectHIDDENM1 holds y inHIDDENR3 domRELAT-1K1 g implies [TARSKIK4 y,x ] inHIDDENR3 domRELAT-1K1 (uncurryFUNCT-5K2 f) & g .FUNCT-1K1 y =XBOOLE-0R4 uncurryFUNCT-5K2 f .BINOP-1K1(y,x))"
sorry

mtheorem funct_6_th_32:
" for x be objectHIDDENM1 holds  for f be Function-yieldingFUNCOP-1V1\<bar>FunctionFUNCT-1M1 holds x inHIDDENR3 domRELAT-1K1 (<:FUNCT-6K5 f:>) implies ( for g be FunctionFUNCT-1M1 holds g inTARSKIR2 rngFUNCT-1K2 f implies x inHIDDENR3 domRELAT-1K1 g)"
sorry

mtheorem funct_6_th_33:
" for g be FunctionFUNCT-1M1 holds  for x be objectHIDDENM1 holds  for f be Function-yieldingFUNCOP-1V1\<bar>FunctionFUNCT-1M1 holds g inTARSKIR2 rngFUNCT-1K2 f & ( for g be FunctionFUNCT-1M1 holds g inTARSKIR2 rngFUNCT-1K2 f implies x inHIDDENR3 domRELAT-1K1 g) implies x inHIDDENR3 domRELAT-1K1 (<:FUNCT-6K5 f:>)"
sorry

mtheorem funct_6_th_34:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for g be FunctionFUNCT-1M1 holds  for h be FunctionFUNCT-1M1 holds  for f be Function-yieldingFUNCOP-1V1\<bar>FunctionFUNCT-1M1 holds ((x inHIDDENR3 domRELAT-1K1 f & g =FUNCT-1R1 f .FUNCT-1K1 x) & y inHIDDENR3 domRELAT-1K1 (<:FUNCT-6K5 f:>)) & h =FUNCT-1R1 (<:FUNCT-6K5 f:>).FUNCT-1K1 y implies g .FUNCT-1K1 y =XBOOLE-0R4 h .FUNCT-1K1 x"
sorry

mtheorem funct_6_th_35:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for f be Function-yieldingFUNCOP-1V1\<bar>FunctionFUNCT-1M1 holds (x inHIDDENR3 domRELAT-1K1 f & f .FUNCT-1K1 x be FunctionFUNCT-1M1) & y inHIDDENR3 domRELAT-1K1 (<:FUNCT-6K5 f:>) implies f ..FUNCT-6K4(x,y) =XBOOLE-0R4 (<:FUNCT-6K5 f:>)..FUNCT-6K4(y,x)"
sorry

mdef funct_6_def_7 ("FregeFUNCT-6K6  _ " [164]164 ) where
  mlet "f be Function-yieldingFUNCOP-1V1\<bar>FunctionFUNCT-1M1"
"func FregeFUNCT-6K6 f \<rightarrow> FunctionFUNCT-1M1 means
  \<lambda>it. domRELAT-1K1 it =XBOOLE-0R4 productCARD-3K4 (domsFUNCT-6K1 f) & ( for g be FunctionFUNCT-1M1 holds g inTARSKIR2 productCARD-3K4 (domsFUNCT-6K1 f) implies ( ex h be FunctionFUNCT-1M1 st (it .FUNCT-1K1 g =XBOOLE-0R4 h & domRELAT-1K1 h =XBOOLE-0R4 domRELAT-1K1 f) & ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 h implies h .FUNCT-1K1 x =XBOOLE-0R4 uncurryFUNCT-5K2 f .BINOP-1K1(x,g .FUNCT-1K1 x))))"
proof-
  (*existence*)
    show " ex it be FunctionFUNCT-1M1 st domRELAT-1K1 it =XBOOLE-0R4 productCARD-3K4 (domsFUNCT-6K1 f) & ( for g be FunctionFUNCT-1M1 holds g inTARSKIR2 productCARD-3K4 (domsFUNCT-6K1 f) implies ( ex h be FunctionFUNCT-1M1 st (it .FUNCT-1K1 g =XBOOLE-0R4 h & domRELAT-1K1 h =XBOOLE-0R4 domRELAT-1K1 f) & ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 h implies h .FUNCT-1K1 x =XBOOLE-0R4 uncurryFUNCT-5K2 f .BINOP-1K1(x,g .FUNCT-1K1 x))))"
sorry
  (*uniqueness*)
    show " for it1 be FunctionFUNCT-1M1 holds  for it2 be FunctionFUNCT-1M1 holds (domRELAT-1K1 it1 =XBOOLE-0R4 productCARD-3K4 (domsFUNCT-6K1 f) & ( for g be FunctionFUNCT-1M1 holds g inTARSKIR2 productCARD-3K4 (domsFUNCT-6K1 f) implies ( ex h be FunctionFUNCT-1M1 st (it1 .FUNCT-1K1 g =XBOOLE-0R4 h & domRELAT-1K1 h =XBOOLE-0R4 domRELAT-1K1 f) & ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 h implies h .FUNCT-1K1 x =XBOOLE-0R4 uncurryFUNCT-5K2 f .BINOP-1K1(x,g .FUNCT-1K1 x))))) & (domRELAT-1K1 it2 =XBOOLE-0R4 productCARD-3K4 (domsFUNCT-6K1 f) & ( for g be FunctionFUNCT-1M1 holds g inTARSKIR2 productCARD-3K4 (domsFUNCT-6K1 f) implies ( ex h be FunctionFUNCT-1M1 st (it2 .FUNCT-1K1 g =XBOOLE-0R4 h & domRELAT-1K1 h =XBOOLE-0R4 domRELAT-1K1 f) & ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 h implies h .FUNCT-1K1 x =XBOOLE-0R4 uncurryFUNCT-5K2 f .BINOP-1K1(x,g .FUNCT-1K1 x))))) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mtheorem funct_6_th_36:
" for x be objectHIDDENM1 holds  for g be FunctionFUNCT-1M1 holds  for f be Function-yieldingFUNCOP-1V1\<bar>FunctionFUNCT-1M1 holds g inTARSKIR2 productCARD-3K4 (domsFUNCT-6K1 f) & x inHIDDENR3 domRELAT-1K1 g implies (FregeFUNCT-6K6 f)..FUNCT-6K4(g,x) =XBOOLE-0R4 f ..FUNCT-6K4(x,g .FUNCT-1K1 x)"
sorry

mlemma funct_6_lm_1:
" for f be Function-yieldingFUNCOP-1V1\<bar>FunctionFUNCT-1M1 holds rngFUNCT-1K2 (FregeFUNCT-6K6 f) c=TARSKIR1 productCARD-3K4 (rngsFUNCT-6K2 f)"
sorry

mtheorem funct_6_th_37:
" for x be objectHIDDENM1 holds  for g be FunctionFUNCT-1M1 holds  for h be FunctionFUNCT-1M1 holds  for h9 be FunctionFUNCT-1M1 holds  for f be Function-yieldingFUNCOP-1V1\<bar>FunctionFUNCT-1M1 holds ((x inHIDDENR3 domRELAT-1K1 f & g =FUNCT-1R1 f .FUNCT-1K1 x) & h inTARSKIR2 productCARD-3K4 (domsFUNCT-6K1 f)) & h9 =XBOOLE-0R4 (FregeFUNCT-6K6 f).FUNCT-1K1 h implies (h .FUNCT-1K1 x inTARSKIR2 domRELAT-1K1 g & h9 .FUNCT-1K1 x =XBOOLE-0R4 g .FUNCT-1K1 (h .FUNCT-1K1 x)) & h9 inTARSKIR2 productCARD-3K4 (rngsFUNCT-6K2 f)"
sorry

mlemma funct_6_lm_2:
" for f be Function-yieldingFUNCOP-1V1\<bar>FunctionFUNCT-1M1 holds productCARD-3K4 (rngsFUNCT-6K2 f) c=TARSKIR1 rngFUNCT-1K2 (FregeFUNCT-6K6 f)"
sorry

mtheorem funct_6_th_38:
" for f be Function-yieldingFUNCOP-1V1\<bar>FunctionFUNCT-1M1 holds rngFUNCT-1K2 (FregeFUNCT-6K6 f) =XBOOLE-0R4 productCARD-3K4 (rngsFUNCT-6K2 f)"
  using funct_6_lm_1 funct_6_lm_2 sorry

mtheorem funct_6_th_39:
" for f be Function-yieldingFUNCOP-1V1\<bar>FunctionFUNCT-1M1 holds  not {}XBOOLE-0K1 inTARSKIR2 rngFUNCT-1K2 f implies (FregeFUNCT-6K6 f be one-to-oneFUNCT-1V2 iff ( for g be FunctionFUNCT-1M1 holds g inTARSKIR2 rngFUNCT-1K2 f implies g be one-to-oneFUNCT-1V2))"
sorry

(*begin*)
mtheorem funct_6_th_40:
"<:FUNCT-6K5 {}XBOOLE-0K1:> =FUNCT-1R1 {}XBOOLE-0K1 & FregeFUNCT-6K6 {}XBOOLE-0K1 =FUNCT-1R1 {}XBOOLE-0K1 .-->FUNCOP-1K17 {}XBOOLE-0K1"
sorry

mtheorem funct_6_th_41:
" for X be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds X <>HIDDENR2 {}XBOOLE-0K1 implies domRELAT-1K1 (<:FUNCT-6K5 X -->FUNCOP-1K7 f :>) =XBOOLE-0R4 domRELAT-1K1 f & ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 f implies (<:FUNCT-6K5 X -->FUNCOP-1K7 f :>).FUNCT-1K1 x =FUNCT-1R1 X -->FUNCOP-1K7 f .FUNCT-1K1 x)"
sorry

mtheorem funct_6_th_42:
" for X be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds (domRELAT-1K1 (FregeFUNCT-6K6 (X -->FUNCOP-1K7 f)) =XBOOLE-0R4 FuncsFUNCT-2K1(X,domRELAT-1K1 f) & rngFUNCT-1K2 (FregeFUNCT-6K6 (X -->FUNCOP-1K7 f)) =XBOOLE-0R4 FuncsFUNCT-2K1(X,rngFUNCT-1K2 f)) & ( for g be FunctionFUNCT-1M1 holds g inTARSKIR2 FuncsFUNCT-2K1(X,domRELAT-1K1 f) implies (FregeFUNCT-6K6 (X -->FUNCOP-1K7 f)).FUNCT-1K1 g =XBOOLE-0R4 f *FUNCT-1K3 g)"
sorry

mtheorem funct_6_th_43:
" for X be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds (domRELAT-1K1 f =XBOOLE-0R4 X & domRELAT-1K1 g =XBOOLE-0R4 X) & ( for x be objectHIDDENM1 holds x inHIDDENR3 X implies (f .FUNCT-1K1 x,g .FUNCT-1K1 x)are-equipotentWELLORD2R2) implies (productCARD-3K4 f,productCARD-3K4 g)are-equipotentWELLORD2R2"
sorry

mtheorem funct_6_th_44:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds  for h be FunctionFUNCT-1M1 holds ((domRELAT-1K1 f =XBOOLE-0R4 domRELAT-1K1 h & domRELAT-1K1 g =XBOOLE-0R4 rngFUNCT-1K2 h) & h be one-to-oneFUNCT-1V2) & ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 h implies (f .FUNCT-1K1 x,g .FUNCT-1K1 (h .FUNCT-1K1 x))are-equipotentWELLORD2R2) implies (productCARD-3K4 f,productCARD-3K4 g)are-equipotentWELLORD2R2"
sorry

mtheorem funct_6_th_45:
" for X be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds  for P be PermutationFUNCT-2M2-of X holds domRELAT-1K1 f =XBOOLE-0R4 X implies (productCARD-3K4 f,productCARD-3K4 (f *FUNCT-1K3 P))are-equipotentWELLORD2R2"
sorry

(*begin*)
mdef funct_6_def_8 ("FuncsFUNCT-6K7'( _ , _ ')" [0,0]228 ) where
  mlet "f be FunctionFUNCT-1M1", "X be setHIDDENM2"
"func FuncsFUNCT-6K7(f,X) \<rightarrow> FunctionFUNCT-1M1 means
  \<lambda>it. domRELAT-1K1 it =XBOOLE-0R4 domRELAT-1K1 f & ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 f implies it .FUNCT-1K1 x =XBOOLE-0R4 FuncsFUNCT-2K1(f .FUNCT-1K1 x,X))"
proof-
  (*existence*)
    show " ex it be FunctionFUNCT-1M1 st domRELAT-1K1 it =XBOOLE-0R4 domRELAT-1K1 f & ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 f implies it .FUNCT-1K1 x =XBOOLE-0R4 FuncsFUNCT-2K1(f .FUNCT-1K1 x,X))"
sorry
  (*uniqueness*)
    show " for it1 be FunctionFUNCT-1M1 holds  for it2 be FunctionFUNCT-1M1 holds (domRELAT-1K1 it1 =XBOOLE-0R4 domRELAT-1K1 f & ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 f implies it1 .FUNCT-1K1 x =XBOOLE-0R4 FuncsFUNCT-2K1(f .FUNCT-1K1 x,X))) & (domRELAT-1K1 it2 =XBOOLE-0R4 domRELAT-1K1 f & ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 f implies it2 .FUNCT-1K1 x =XBOOLE-0R4 FuncsFUNCT-2K1(f .FUNCT-1K1 x,X))) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mtheorem funct_6_th_46:
" for f be FunctionFUNCT-1M1 holds  not {}XBOOLE-0K1 inTARSKIR2 rngFUNCT-1K2 f implies FuncsFUNCT-6K7(f,{}XBOOLE-0K1) =FUNCT-1R1 domRELAT-1K1 f -->FUNCOP-1K7 {}XBOOLE-0K1"
sorry

mtheorem funct_6_th_47:
" for X be setHIDDENM2 holds FuncsFUNCT-6K7({}XBOOLE-0K1,X) =FUNCT-1R1 {}XBOOLE-0K1"
sorry

mtheorem funct_6_th_48:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds FuncsFUNCT-6K7(X -->FUNCOP-1K7 Y,Z) =FUNCT-1R1 X -->FUNCOP-1K7 FuncsFUNCT-2K1(Y,Z)"
sorry

mlemma funct_6_lm_3:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds  for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for z be objectHIDDENM1 holds ([TARSKIK4 x,y ] inHIDDENR3 domRELAT-1K1 f & g =FUNCT-1R1 curryFUNCT-5K1 f .FUNCT-1K1 x) & z inHIDDENR3 domRELAT-1K1 g implies [TARSKIK4 x,z ] inHIDDENR3 domRELAT-1K1 f"
sorry

mtheorem funct_6_th_49:
" for X be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds (FuncsFUNCT-2K1(UnionCARD-3K3 disjoinCARD-3K2 f,X),productCARD-3K4 (FuncsFUNCT-6K7(f,X)))are-equipotentWELLORD2R2"
sorry

mdef funct_6_def_9 ("FuncsFUNCT-6K8'( _ , _ ')" [0,0]228 ) where
  mlet "X be setHIDDENM2", "f be FunctionFUNCT-1M1"
"func FuncsFUNCT-6K8(X,f) \<rightarrow> FunctionFUNCT-1M1 means
  \<lambda>it. domRELAT-1K1 it =XBOOLE-0R4 domRELAT-1K1 f & ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 f implies it .FUNCT-1K1 x =XBOOLE-0R4 FuncsFUNCT-2K1(X,f .FUNCT-1K1 x))"
proof-
  (*existence*)
    show " ex it be FunctionFUNCT-1M1 st domRELAT-1K1 it =XBOOLE-0R4 domRELAT-1K1 f & ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 f implies it .FUNCT-1K1 x =XBOOLE-0R4 FuncsFUNCT-2K1(X,f .FUNCT-1K1 x))"
sorry
  (*uniqueness*)
    show " for it1 be FunctionFUNCT-1M1 holds  for it2 be FunctionFUNCT-1M1 holds (domRELAT-1K1 it1 =XBOOLE-0R4 domRELAT-1K1 f & ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 f implies it1 .FUNCT-1K1 x =XBOOLE-0R4 FuncsFUNCT-2K1(X,f .FUNCT-1K1 x))) & (domRELAT-1K1 it2 =XBOOLE-0R4 domRELAT-1K1 f & ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 f implies it2 .FUNCT-1K1 x =XBOOLE-0R4 FuncsFUNCT-2K1(X,f .FUNCT-1K1 x))) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mlemma funct_6_lm_4:
" for X be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds f <>HIDDENR2 {}XBOOLE-0K1 & X <>HIDDENR2 {}XBOOLE-0K1 implies (productCARD-3K4 (FuncsFUNCT-6K8(X,f)),FuncsFUNCT-2K1(X,productCARD-3K4 f))are-equipotentWELLORD2R2"
sorry

mtheorem funct_6_th_50:
" for f be FunctionFUNCT-1M1 holds FuncsFUNCT-6K8({}XBOOLE-0K1,f) =FUNCT-1R1 domRELAT-1K1 f -->FUNCOP-1K7 {TARSKIK1 {}XBOOLE-0K1 }"
sorry

mtheorem funct_6_th_51:
" for X be setHIDDENM2 holds FuncsFUNCT-6K8(X,{}XBOOLE-0K1) =FUNCT-1R1 {}XBOOLE-0K1"
sorry

mtheorem funct_6_th_52:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds FuncsFUNCT-6K8(X,Y -->FUNCOP-1K7 Z) =FUNCT-1R1 Y -->FUNCOP-1K7 FuncsFUNCT-2K1(X,Z)"
sorry

mtheorem funct_6_th_53:
" for X be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds (productCARD-3K4 (FuncsFUNCT-6K8(X,f)),FuncsFUNCT-2K1(X,productCARD-3K4 f))are-equipotentWELLORD2R2"
sorry

(*begin*)
mdef funct_6_def_10 ("commuteFUNCT-6K9  _ " [164]164 ) where
  mlet "f be FunctionFUNCT-1M1"
"func commuteFUNCT-6K9 f \<rightarrow> Function-yieldingFUNCOP-1V1\<bar>FunctionFUNCT-1M1 equals
  curry'FUNCT-5K3 (uncurryFUNCT-5K2 f)"
proof-
  (*coherence*)
    show "curry'FUNCT-5K3 (uncurryFUNCT-5K2 f) be Function-yieldingFUNCOP-1V1\<bar>FunctionFUNCT-1M1"
       sorry
qed "sorry"

mtheorem funct_6_th_54:
" for f be FunctionFUNCT-1M1 holds  for x be setHIDDENM2 holds x inTARSKIR2 domRELAT-1K1 (commuteFUNCT-6K9 f) implies (commuteFUNCT-6K9 f).FUNCT-1K1 x be FunctionFUNCT-1M1"
   sorry

mtheorem funct_6_th_55:
" for A be setHIDDENM2 holds  for B be setHIDDENM2 holds  for C be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds (A <>HIDDENR2 {}XBOOLE-0K1 & B <>HIDDENR2 {}XBOOLE-0K1) & f inTARSKIR2 FuncsFUNCT-2K1(A,FuncsFUNCT-2K1(B,C)) implies commuteFUNCT-6K9 f inTARSKIR2 FuncsFUNCT-2K1(B,FuncsFUNCT-2K1(A,C))"
sorry

mtheorem funct_6_th_56:
" for A be setHIDDENM2 holds  for B be setHIDDENM2 holds  for C be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds (A <>HIDDENR2 {}XBOOLE-0K1 & B <>HIDDENR2 {}XBOOLE-0K1) & f inTARSKIR2 FuncsFUNCT-2K1(A,FuncsFUNCT-2K1(B,C)) implies ( for g be FunctionFUNCT-1M1 holds  for h be FunctionFUNCT-1M1 holds  for x be setHIDDENM2 holds  for y be setHIDDENM2 holds ((x inTARSKIR2 A & y inTARSKIR2 B) & f .FUNCT-1K1 x =XBOOLE-0R4 g) & (commuteFUNCT-6K9 f).FUNCT-1K1 y =FUNCT-1R1 h implies (((h .FUNCT-1K1 x =XBOOLE-0R4 g .FUNCT-1K1 y & domRELAT-1K1 h =XBOOLE-0R4 A) & domRELAT-1K1 g =XBOOLE-0R4 B) & rngFUNCT-1K2 h c=TARSKIR1 C) & rngFUNCT-1K2 g c=TARSKIR1 C)"
sorry

mtheorem funct_6_th_57:
" for A be setHIDDENM2 holds  for B be setHIDDENM2 holds  for C be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds (A <>HIDDENR2 {}XBOOLE-0K1 & B <>HIDDENR2 {}XBOOLE-0K1) & f inTARSKIR2 FuncsFUNCT-2K1(A,FuncsFUNCT-2K1(B,C)) implies commuteFUNCT-6K9 (commuteFUNCT-6K9 f) =FUNCT-1R1 f"
sorry

mtheorem funct_6_th_58:
"commuteFUNCT-6K9 {}XBOOLE-0K1 =FUNCT-1R1 {}XBOOLE-0K1"
  using funct_5_th_42 funct_5_th_43 sorry

mtheorem funct_6_th_59:
" for f be Function-yieldingFUNCOP-1V1\<bar>FunctionFUNCT-1M1 holds domRELAT-1K1 (domsFUNCT-6K1 f) =XBOOLE-0R4 domRELAT-1K1 f"
  using funct_6_def_2 sorry

mtheorem funct_6_th_60:
" for f be Function-yieldingFUNCOP-1V1\<bar>FunctionFUNCT-1M1 holds domRELAT-1K1 (rngsFUNCT-6K2 f) =XBOOLE-0R4 domRELAT-1K1 f"
  using funct_6_def_3 sorry

end
