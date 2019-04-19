theory funct_4
  imports ordinal1 realset1
begin
(*begin*)
reserve a, b, p, x, x9, x1, x19, x2, y, y9, y1, y19, y2, z, z9, z1, z2 for "objectHIDDENM1"
reserve X, X9, Y, Y9, Z, Z9 for "setHIDDENM2"
reserve A, D, D9 for " non emptyXBOOLE-0V1\<bar>setHIDDENM2"
reserve f, g, h for "FunctionFUNCT-1M1"
mlemma funct_4_lm_1:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for x1 be objectHIDDENM1 holds  for y1 be objectHIDDENM1 holds  for x9 be objectHIDDENM1 holds  for y9 be objectHIDDENM1 holds  for x19 be objectHIDDENM1 holds  for y19 be objectHIDDENM1 holds [TARSKIK4 [TARSKIK4 x,x9 ],[TARSKIK4 y,y9 ] ] =HIDDENR1 [TARSKIK4 [TARSKIK4 x1,x19 ],[TARSKIK4 y1,y19 ] ] implies ((x =HIDDENR1 x1 & y =HIDDENR1 y1) & x9 =HIDDENR1 x19) & y9 =HIDDENR1 y19"
sorry

mtheorem funct_4_th_1:
" for Z be setHIDDENM2 holds ( for z be objectHIDDENM1 holds z inHIDDENR3 Z implies ( ex x be objectHIDDENM1 st  ex y be objectHIDDENM1 st z =HIDDENR1 [TARSKIK4 x,y ])) implies ( ex X be setHIDDENM2 st  ex Y be setHIDDENM2 st Z c=TARSKIR1 [:ZFMISC-1K2 X,Y :])"
sorry

mtheorem funct_4_th_2:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds g *FUNCT-1K3 f =FUNCT-1R1 g |RELAT-1K8 rngFUNCT-1K2 f *FUNCT-1K3 f"
sorry

mtheorem funct_4_th_3:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds idPARTFUN1K6 X c=RELSET-1R1\<^bsub>(X,X)\<^esub> idPARTFUN1K6 Y iff X c=TARSKIR1 Y"
sorry

mtheorem funct_4_th_4:
" for a be objectHIDDENM1 holds  for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X c=TARSKIR1 Y implies X -->FUNCOP-1K7 a c=RELSET-1R1\<^bsub>(X,{TARSKIK1 a})\<^esub> Y -->FUNCOP-1K7 a"
sorry

mtheorem funct_4_th_5:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for a be objectHIDDENM1 holds  for b be objectHIDDENM1 holds X -->FUNCOP-1K7 a c=RELSET-1R1\<^bsub>(X,{TARSKIK1 a})\<^esub> Y -->FUNCOP-1K7 b implies X c=TARSKIR1 Y"
sorry

mtheorem funct_4_th_6:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for a be objectHIDDENM1 holds  for b be objectHIDDENM1 holds X <>HIDDENR2 {}XBOOLE-0K1 & X -->FUNCOP-1K7 a c=RELSET-1R1\<^bsub>(X,{TARSKIK1 a})\<^esub> Y -->FUNCOP-1K7 b implies a =HIDDENR1 b"
sorry

mtheorem funct_4_th_7:
" for x be objectHIDDENM1 holds  for f be FunctionFUNCT-1M1 holds x inHIDDENR3 domRELAT-1K1 f implies x .-->FUNCOP-1K17 f .FUNCT-1K1 x c=RELAT-1R2 f"
sorry

mtheorem funct_4_th_8:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds (Y |`RELAT-1K9 f)|RELAT-1K8 X c=RELAT-1R2 f"
sorry

mtheorem funct_4_th_9:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds f c=RELAT-1R2 g implies (Y |`RELAT-1K9 f)|RELAT-1K8 X c=RELAT-1R2 (Y |`RELAT-1K9 g)|RELAT-1K8 X"
sorry

mdef funct_4_def_1 (" _ +*FUNCT-4K1  _ " [164,164]164 ) where
  mlet "f be FunctionFUNCT-1M1", "g be FunctionFUNCT-1M1"
"func f +*FUNCT-4K1 g \<rightarrow> FunctionFUNCT-1M1 means
  \<lambda>it. domRELAT-1K1 it =XBOOLE-0R4 domRELAT-1K1 f \\/XBOOLE-0K2 domRELAT-1K1 g & ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 f \\/XBOOLE-0K2 domRELAT-1K1 g implies (x inHIDDENR3 domRELAT-1K1 g implies it .FUNCT-1K1 x =XBOOLE-0R4 g .FUNCT-1K1 x) & ( not x inHIDDENR3 domRELAT-1K1 g implies it .FUNCT-1K1 x =XBOOLE-0R4 f .FUNCT-1K1 x))"
proof-
  (*existence*)
    show " ex it be FunctionFUNCT-1M1 st domRELAT-1K1 it =XBOOLE-0R4 domRELAT-1K1 f \\/XBOOLE-0K2 domRELAT-1K1 g & ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 f \\/XBOOLE-0K2 domRELAT-1K1 g implies (x inHIDDENR3 domRELAT-1K1 g implies it .FUNCT-1K1 x =XBOOLE-0R4 g .FUNCT-1K1 x) & ( not x inHIDDENR3 domRELAT-1K1 g implies it .FUNCT-1K1 x =XBOOLE-0R4 f .FUNCT-1K1 x))"
sorry
  (*uniqueness*)
    show " for it1 be FunctionFUNCT-1M1 holds  for it2 be FunctionFUNCT-1M1 holds (domRELAT-1K1 it1 =XBOOLE-0R4 domRELAT-1K1 f \\/XBOOLE-0K2 domRELAT-1K1 g & ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 f \\/XBOOLE-0K2 domRELAT-1K1 g implies (x inHIDDENR3 domRELAT-1K1 g implies it1 .FUNCT-1K1 x =XBOOLE-0R4 g .FUNCT-1K1 x) & ( not x inHIDDENR3 domRELAT-1K1 g implies it1 .FUNCT-1K1 x =XBOOLE-0R4 f .FUNCT-1K1 x))) & (domRELAT-1K1 it2 =XBOOLE-0R4 domRELAT-1K1 f \\/XBOOLE-0K2 domRELAT-1K1 g & ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 f \\/XBOOLE-0K2 domRELAT-1K1 g implies (x inHIDDENR3 domRELAT-1K1 g implies it2 .FUNCT-1K1 x =XBOOLE-0R4 g .FUNCT-1K1 x) & ( not x inHIDDENR3 domRELAT-1K1 g implies it2 .FUNCT-1K1 x =XBOOLE-0R4 f .FUNCT-1K1 x))) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mtheorem FUNCT_4K1_idempotence:
" for g be FunctionFUNCT-1M1 holds g =HIDDENR1 g +*FUNCT-4K1 g"
sorry

mtheorem funct_4_th_10:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds domRELAT-1K1 f c=TARSKIR1 domRELAT-1K1 (f +*FUNCT-4K1 g) & domRELAT-1K1 g c=TARSKIR1 domRELAT-1K1 (f +*FUNCT-4K1 g)"
sorry

mtheorem funct_4_th_11:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds  for x be objectHIDDENM1 holds  not x inHIDDENR3 domRELAT-1K1 g implies (f +*FUNCT-4K1 g).FUNCT-1K1 x =XBOOLE-0R4 f .FUNCT-1K1 x"
sorry

mtheorem funct_4_th_12:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds  for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 (f +*FUNCT-4K1 g) iff x inHIDDENR3 domRELAT-1K1 f or x inHIDDENR3 domRELAT-1K1 g"
sorry

mtheorem funct_4_th_13:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds  for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 g implies (f +*FUNCT-4K1 g).FUNCT-1K1 x =XBOOLE-0R4 g .FUNCT-1K1 x"
sorry

mtheorem funct_4_th_14:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds  for h be FunctionFUNCT-1M1 holds (f +*FUNCT-4K1 g)+*FUNCT-4K1 h =FUNCT-1R1 f +*FUNCT-4K1 (g +*FUNCT-4K1 h)"
sorry

mtheorem funct_4_th_15:
" for x be objectHIDDENM1 holds  for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds f toleratesPARTFUN1R1 g & x inHIDDENR3 domRELAT-1K1 f implies (f +*FUNCT-4K1 g).FUNCT-1K1 x =XBOOLE-0R4 f .FUNCT-1K1 x"
sorry

mtheorem funct_4_th_16:
" for x be objectHIDDENM1 holds  for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds domRELAT-1K1 f missesXBOOLE-0R1 domRELAT-1K1 g & x inHIDDENR3 domRELAT-1K1 f implies (f +*FUNCT-4K1 g).FUNCT-1K1 x =XBOOLE-0R4 f .FUNCT-1K1 x"
sorry

mtheorem funct_4_th_17:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds rngFUNCT-1K2 (f +*FUNCT-4K1 g) c=TARSKIR1 rngFUNCT-1K2 f \\/XBOOLE-0K2 rngFUNCT-1K2 g"
sorry

mtheorem funct_4_th_18:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds rngFUNCT-1K2 g c=TARSKIR1 rngFUNCT-1K2 (f +*FUNCT-4K1 g)"
sorry

mtheorem funct_4_th_19:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds domRELAT-1K1 f c=TARSKIR1 domRELAT-1K1 g implies f +*FUNCT-4K1 g =FUNCT-1R1 g"
sorry

mtheorem funct_4_reduce_1:
  mlet "f be FunctionFUNCT-1M1", "g be emptyXBOOLE-0V1\<bar>FunctionFUNCT-1M1"
"reduce g +*FUNCT-4K1 f to f"
proof
(*reducibility*)
  show "g +*FUNCT-4K1 f =HIDDENR1 f"
sorry
qed "sorry"

mtheorem funct_4_reduce_2:
  mlet "f be FunctionFUNCT-1M1", "g be emptyXBOOLE-0V1\<bar>FunctionFUNCT-1M1"
"reduce f +*FUNCT-4K1 g to f"
proof
(*reducibility*)
  show "f +*FUNCT-4K1 g =HIDDENR1 f"
sorry
qed "sorry"

mtheorem funct_4_th_20:
" for f be FunctionFUNCT-1M1 holds {}XBOOLE-0K1 +*FUNCT-4K1 f =FUNCT-1R1 f"
   sorry

mtheorem funct_4_th_21:
" for f be FunctionFUNCT-1M1 holds f +*FUNCT-4K1 {}XBOOLE-0K1 =FUNCT-1R1 f"
   sorry

mtheorem funct_4_th_22:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds idPARTFUN1K6 X +*FUNCT-4K1 idPARTFUN1K6 Y =FUNCT-1R1 idPARTFUN1K6 (X \\/XBOOLE-0K2 Y)"
sorry

mtheorem funct_4_th_23:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds (f +*FUNCT-4K1 g)|RELAT-1K8 domRELAT-1K1 g =FUNCT-1R1 g"
sorry

mtheorem funct_4_th_24:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds (f +*FUNCT-4K1 g)|RELAT-1K8 (domRELAT-1K1 f \\SUBSET-1K6 domRELAT-1K1 g) c=RELAT-1R2 f"
sorry

mtheorem funct_4_th_25:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds g c=RELAT-1R2 f +*FUNCT-4K1 g"
sorry

mtheorem funct_4_th_26:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds  for h be FunctionFUNCT-1M1 holds f toleratesPARTFUN1R1 g +*FUNCT-4K1 h implies f |RELAT-1K8 (domRELAT-1K1 f \\SUBSET-1K6 domRELAT-1K1 h) toleratesPARTFUN1R1 g"
sorry

mtheorem funct_4_th_27:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds  for h be FunctionFUNCT-1M1 holds f toleratesPARTFUN1R1 g +*FUNCT-4K1 h implies f toleratesPARTFUN1R1 h"
sorry

mtheorem funct_4_th_28:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds f toleratesPARTFUN1R1 g iff f c=RELAT-1R2 f +*FUNCT-4K1 g"
sorry

mtheorem funct_4_th_29:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds f +*FUNCT-4K1 g c=RELAT-1R2 f \\/XBOOLE-0K2 g"
sorry

mtheorem funct_4_th_30:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds f toleratesPARTFUN1R1 g iff f \\/XBOOLE-0K2 g =RELAT-1R1 f +*FUNCT-4K1 g"
sorry

mtheorem funct_4_th_31:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds domRELAT-1K1 f missesXBOOLE-0R1 domRELAT-1K1 g implies f \\/XBOOLE-0K2 g =RELAT-1R1 f +*FUNCT-4K1 g"
  using funct_4_th_30 partfun1_th_56 sorry

mtheorem funct_4_th_32:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds domRELAT-1K1 f missesXBOOLE-0R1 domRELAT-1K1 g implies f c=RELAT-1R2 f +*FUNCT-4K1 g"
sorry

mtheorem funct_4_th_33:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds domRELAT-1K1 f missesXBOOLE-0R1 domRELAT-1K1 g implies (f +*FUNCT-4K1 g)|RELAT-1K8 domRELAT-1K1 f =FUNCT-1R1 f"
sorry

mtheorem funct_4_th_34:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds f toleratesPARTFUN1R1 g iff f +*FUNCT-4K1 g =FUNCT-1R1 g +*FUNCT-4K1 f"
sorry

mtheorem funct_4_th_35:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds domRELAT-1K1 f missesXBOOLE-0R1 domRELAT-1K1 g implies f +*FUNCT-4K1 g =FUNCT-1R1 g +*FUNCT-4K1 f"
  using funct_4_th_34 partfun1_th_56 sorry

mtheorem funct_4_th_36:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be PartFuncPARTFUN1M1-of(X,Y) holds  for g be PartFuncPARTFUN1M1-of(X,Y) holds g be totalPARTFUN1V1\<^bsub>(X)\<^esub> implies f +*FUNCT-4K1 g =FUNCT-1R1 g"
sorry

mtheorem funct_4_th_37:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(X,Y) holds  for g be FunctionFUNCT-2M1-of(X,Y) holds f +*FUNCT-4K1 g =FUNCT-1R1 g"
sorry

mtheorem funct_4_th_38:
" for X be setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(X,X) holds  for g be FunctionFUNCT-2M1-of(X,X) holds f +*FUNCT-4K1 g =FUNCT-1R1 g"
  using funct_4_th_37 sorry

mtheorem funct_4_th_39:
" for X be setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(X,D) holds  for g be FunctionFUNCT-2M1-of(X,D) holds f +*FUNCT-4K1 g =FUNCT-1R1 g"
  using funct_4_th_37 sorry

mtheorem funct_4_th_40:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be PartFuncPARTFUN1M1-of(X,Y) holds  for g be PartFuncPARTFUN1M1-of(X,Y) holds f +*FUNCT-4K1 g be PartFuncPARTFUN1M1-of(X,Y)"
sorry

mdef funct_4_def_2 ("~FUNCT-4K2  _ " [228]228 ) where
  mlet "f be FunctionFUNCT-1M1"
"func ~FUNCT-4K2 f \<rightarrow> FunctionFUNCT-1M1 means
  \<lambda>it. ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 it iff ( ex y be objectHIDDENM1 st  ex z be objectHIDDENM1 st x =HIDDENR1 [TARSKIK4 z,y ] & [TARSKIK4 y,z ] inHIDDENR3 domRELAT-1K1 f)) & ( for y be objectHIDDENM1 holds  for z be objectHIDDENM1 holds [TARSKIK4 y,z ] inHIDDENR3 domRELAT-1K1 f implies it .BINOP-1K1(z,y) =XBOOLE-0R4 f .BINOP-1K1(y,z))"
proof-
  (*existence*)
    show " ex it be FunctionFUNCT-1M1 st ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 it iff ( ex y be objectHIDDENM1 st  ex z be objectHIDDENM1 st x =HIDDENR1 [TARSKIK4 z,y ] & [TARSKIK4 y,z ] inHIDDENR3 domRELAT-1K1 f)) & ( for y be objectHIDDENM1 holds  for z be objectHIDDENM1 holds [TARSKIK4 y,z ] inHIDDENR3 domRELAT-1K1 f implies it .BINOP-1K1(z,y) =XBOOLE-0R4 f .BINOP-1K1(y,z))"
sorry
  (*uniqueness*)
    show " for it1 be FunctionFUNCT-1M1 holds  for it2 be FunctionFUNCT-1M1 holds (( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 it1 iff ( ex y be objectHIDDENM1 st  ex z be objectHIDDENM1 st x =HIDDENR1 [TARSKIK4 z,y ] & [TARSKIK4 y,z ] inHIDDENR3 domRELAT-1K1 f)) & ( for y be objectHIDDENM1 holds  for z be objectHIDDENM1 holds [TARSKIK4 y,z ] inHIDDENR3 domRELAT-1K1 f implies it1 .BINOP-1K1(z,y) =XBOOLE-0R4 f .BINOP-1K1(y,z))) & (( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 it2 iff ( ex y be objectHIDDENM1 st  ex z be objectHIDDENM1 st x =HIDDENR1 [TARSKIK4 z,y ] & [TARSKIK4 y,z ] inHIDDENR3 domRELAT-1K1 f)) & ( for y be objectHIDDENM1 holds  for z be objectHIDDENM1 holds [TARSKIK4 y,z ] inHIDDENR3 domRELAT-1K1 f implies it2 .BINOP-1K1(z,y) =XBOOLE-0R4 f .BINOP-1K1(y,z))) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mtheorem funct_4_th_41:
" for f be FunctionFUNCT-1M1 holds rngFUNCT-1K2 (~FUNCT-4K2 f) c=TARSKIR1 rngFUNCT-1K2 f"
sorry

mtheorem funct_4_th_42:
" for f be FunctionFUNCT-1M1 holds  for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds [TARSKIK4 x,y ] inHIDDENR3 domRELAT-1K1 f iff [TARSKIK4 y,x ] inHIDDENR3 domRELAT-1K1 (~FUNCT-4K2 f)"
sorry

mtheorem funct_4_cl_1:
  mlet "f be emptyXBOOLE-0V1\<bar>FunctionFUNCT-1M1"
"cluster ~FUNCT-4K2 f as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "~FUNCT-4K2 f be emptyXBOOLE-0V1"
sorry
qed "sorry"

mtheorem funct_4_th_43:
" for f be FunctionFUNCT-1M1 holds  for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds [TARSKIK4 y,x ] inHIDDENR3 domRELAT-1K1 (~FUNCT-4K2 f) implies ~FUNCT-4K2 f .BINOP-1K1(y,x) =XBOOLE-0R4 f .BINOP-1K1(x,y)"
sorry

mtheorem funct_4_th_44:
" for f be FunctionFUNCT-1M1 holds  ex X be setHIDDENM2 st  ex Y be setHIDDENM2 st domRELAT-1K1 (~FUNCT-4K2 f) c=TARSKIR1 [:ZFMISC-1K2 X,Y :]"
sorry

mtheorem funct_4_th_45:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds domRELAT-1K1 f c=TARSKIR1 [:ZFMISC-1K2 X,Y :] implies domRELAT-1K1 (~FUNCT-4K2 f) c=TARSKIR1 [:ZFMISC-1K2 Y,X :]"
sorry

mtheorem funct_4_th_46:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds domRELAT-1K1 f =XBOOLE-0R4 [:ZFMISC-1K2 X,Y :] implies domRELAT-1K1 (~FUNCT-4K2 f) =XBOOLE-0R4 [:ZFMISC-1K2 Y,X :]"
sorry

mtheorem funct_4_th_47:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds domRELAT-1K1 f c=TARSKIR1 [:ZFMISC-1K2 X,Y :] implies rngFUNCT-1K2 (~FUNCT-4K2 f) =XBOOLE-0R4 rngFUNCT-1K2 f"
sorry

mtheorem funct_4_th_48:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds  for f be PartFuncPARTFUN1M1-of([:ZFMISC-1K2 X,Y :],Z) holds ~FUNCT-4K2 f be PartFuncPARTFUN1M1-of([:ZFMISC-1K2 Y,X :],Z)"
sorry

syntax FUNCT_4K3 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" ("~FUNCT-4K3\<^bsub>'( _ , _ , _ ')\<^esub>  _ " [0,0,0,228]228)
translations "~FUNCT-4K3\<^bsub>(X,Y,Z)\<^esub> f" \<rightharpoonup> "~FUNCT-4K2 f"

mtheorem funct_4_add_1:
  mlet "X be setHIDDENM2", "Y be setHIDDENM2", "Z be setHIDDENM2", "f be PartFuncPARTFUN1M1-of([:ZFMISC-1K2 X,Y :],Z)"
"cluster ~FUNCT-4K2 f as-term-is PartFuncPARTFUN1M1-of([:ZFMISC-1K2 Y,X :],Z)"
proof
(*coherence*)
  show "~FUNCT-4K2 f be PartFuncPARTFUN1M1-of([:ZFMISC-1K2 Y,X :],Z)"
    using funct_4_th_48 sorry
qed "sorry"

mtheorem funct_4_th_49:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of([:ZFMISC-1K2 X,Y :],Z) holds ~FUNCT-4K3\<^bsub>(X,Y,Z)\<^esub> f be FunctionFUNCT-2M1-of([:ZFMISC-1K2 Y,X :],Z)"
sorry

syntax FUNCT_4K4 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" ("~FUNCT-4K4\<^bsub>'( _ , _ , _ ')\<^esub>  _ " [0,0,0,228]228)
translations "~FUNCT-4K4\<^bsub>(X,Y,Z)\<^esub> f" \<rightharpoonup> "~FUNCT-4K2 f"

mtheorem funct_4_add_2:
  mlet "X be setHIDDENM2", "Y be setHIDDENM2", "Z be setHIDDENM2", "f be FunctionFUNCT-2M1-of([:ZFMISC-1K2 X,Y :],Z)"
"cluster ~FUNCT-4K2 f as-term-is FunctionFUNCT-2M1-of([:ZFMISC-1K2 Y,X :],Z)"
proof
(*coherence*)
  show "~FUNCT-4K2 f be FunctionFUNCT-2M1-of([:ZFMISC-1K2 Y,X :],Z)"
    using funct_4_th_49 sorry
qed "sorry"

mtheorem funct_4_th_50:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of([:ZFMISC-1K2 X,Y :],Z) holds ~FUNCT-4K4\<^bsub>(X,Y,Z)\<^esub> f be FunctionFUNCT-2M1-of([:ZFMISC-1K2 Y,X :],Z)"
   sorry

mtheorem funct_4_th_51:
" for f be FunctionFUNCT-1M1 holds ~FUNCT-4K2 (~FUNCT-4K2 f) c=RELAT-1R2 f"
sorry

mtheorem funct_4_th_52:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds domRELAT-1K1 f c=TARSKIR1 [:ZFMISC-1K2 X,Y :] implies ~FUNCT-4K2 (~FUNCT-4K2 f) =FUNCT-1R1 f"
sorry

mtheorem funct_4_th_53:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds  for f be PartFuncPARTFUN1M1-of([:ZFMISC-1K2 X,Y :],Z) holds ~FUNCT-4K3\<^bsub>(Y,X,Z)\<^esub> (~FUNCT-4K3\<^bsub>(X,Y,Z)\<^esub> f) =RELSET-1R2\<^bsub>([:ZFMISC-1K2 X,Y :],Z)\<^esub> f"
sorry

mdef funct_4_def_3 ("|:FUNCT-4K5 _ , _ :|" [0,0]164 ) where
  mlet "f be FunctionFUNCT-1M1", "g be FunctionFUNCT-1M1"
"func |:FUNCT-4K5 f,g :| \<rightarrow> FunctionFUNCT-1M1 means
  \<lambda>it. ( for z be objectHIDDENM1 holds z inHIDDENR3 domRELAT-1K1 it iff ( ex x be objectHIDDENM1 st  ex y be objectHIDDENM1 st  ex x9 be objectHIDDENM1 st  ex y9 be objectHIDDENM1 st (z =HIDDENR1 [TARSKIK4 [TARSKIK4 x,x9 ],[TARSKIK4 y,y9 ] ] & [TARSKIK4 x,y ] inHIDDENR3 domRELAT-1K1 f) & [TARSKIK4 x9,y9 ] inHIDDENR3 domRELAT-1K1 g)) & ( for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for x9 be objectHIDDENM1 holds  for y9 be objectHIDDENM1 holds [TARSKIK4 x,y ] inHIDDENR3 domRELAT-1K1 f & [TARSKIK4 x9,y9 ] inHIDDENR3 domRELAT-1K1 g implies it .BINOP-1K1([TARSKIK4 x,x9 ],[TARSKIK4 y,y9 ]) =HIDDENR1 [TARSKIK4 f .BINOP-1K1(x,y),g .BINOP-1K1(x9,y9) ])"
proof-
  (*existence*)
    show " ex it be FunctionFUNCT-1M1 st ( for z be objectHIDDENM1 holds z inHIDDENR3 domRELAT-1K1 it iff ( ex x be objectHIDDENM1 st  ex y be objectHIDDENM1 st  ex x9 be objectHIDDENM1 st  ex y9 be objectHIDDENM1 st (z =HIDDENR1 [TARSKIK4 [TARSKIK4 x,x9 ],[TARSKIK4 y,y9 ] ] & [TARSKIK4 x,y ] inHIDDENR3 domRELAT-1K1 f) & [TARSKIK4 x9,y9 ] inHIDDENR3 domRELAT-1K1 g)) & ( for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for x9 be objectHIDDENM1 holds  for y9 be objectHIDDENM1 holds [TARSKIK4 x,y ] inHIDDENR3 domRELAT-1K1 f & [TARSKIK4 x9,y9 ] inHIDDENR3 domRELAT-1K1 g implies it .BINOP-1K1([TARSKIK4 x,x9 ],[TARSKIK4 y,y9 ]) =HIDDENR1 [TARSKIK4 f .BINOP-1K1(x,y),g .BINOP-1K1(x9,y9) ])"
sorry
  (*uniqueness*)
    show " for it1 be FunctionFUNCT-1M1 holds  for it2 be FunctionFUNCT-1M1 holds (( for z be objectHIDDENM1 holds z inHIDDENR3 domRELAT-1K1 it1 iff ( ex x be objectHIDDENM1 st  ex y be objectHIDDENM1 st  ex x9 be objectHIDDENM1 st  ex y9 be objectHIDDENM1 st (z =HIDDENR1 [TARSKIK4 [TARSKIK4 x,x9 ],[TARSKIK4 y,y9 ] ] & [TARSKIK4 x,y ] inHIDDENR3 domRELAT-1K1 f) & [TARSKIK4 x9,y9 ] inHIDDENR3 domRELAT-1K1 g)) & ( for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for x9 be objectHIDDENM1 holds  for y9 be objectHIDDENM1 holds [TARSKIK4 x,y ] inHIDDENR3 domRELAT-1K1 f & [TARSKIK4 x9,y9 ] inHIDDENR3 domRELAT-1K1 g implies it1 .BINOP-1K1([TARSKIK4 x,x9 ],[TARSKIK4 y,y9 ]) =HIDDENR1 [TARSKIK4 f .BINOP-1K1(x,y),g .BINOP-1K1(x9,y9) ])) & (( for z be objectHIDDENM1 holds z inHIDDENR3 domRELAT-1K1 it2 iff ( ex x be objectHIDDENM1 st  ex y be objectHIDDENM1 st  ex x9 be objectHIDDENM1 st  ex y9 be objectHIDDENM1 st (z =HIDDENR1 [TARSKIK4 [TARSKIK4 x,x9 ],[TARSKIK4 y,y9 ] ] & [TARSKIK4 x,y ] inHIDDENR3 domRELAT-1K1 f) & [TARSKIK4 x9,y9 ] inHIDDENR3 domRELAT-1K1 g)) & ( for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for x9 be objectHIDDENM1 holds  for y9 be objectHIDDENM1 holds [TARSKIK4 x,y ] inHIDDENR3 domRELAT-1K1 f & [TARSKIK4 x9,y9 ] inHIDDENR3 domRELAT-1K1 g implies it2 .BINOP-1K1([TARSKIK4 x,x9 ],[TARSKIK4 y,y9 ]) =HIDDENR1 [TARSKIK4 f .BINOP-1K1(x,y),g .BINOP-1K1(x9,y9) ])) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mtheorem funct_4_th_54:
" for x be objectHIDDENM1 holds  for x9 be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for y9 be objectHIDDENM1 holds  for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds [TARSKIK4 [TARSKIK4 x,x9 ],[TARSKIK4 y,y9 ] ] inHIDDENR3 domRELAT-1K1 (|:FUNCT-4K5 f,g :|) iff [TARSKIK4 x,y ] inHIDDENR3 domRELAT-1K1 f & [TARSKIK4 x9,y9 ] inHIDDENR3 domRELAT-1K1 g"
sorry

mtheorem funct_4_th_55:
" for x be objectHIDDENM1 holds  for x9 be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for y9 be objectHIDDENM1 holds  for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds [TARSKIK4 [TARSKIK4 x,x9 ],[TARSKIK4 y,y9 ] ] inHIDDENR3 domRELAT-1K1 (|:FUNCT-4K5 f,g :|) implies (|:FUNCT-4K5 f,g :|).BINOP-1K1([TARSKIK4 x,x9 ],[TARSKIK4 y,y9 ]) =HIDDENR1 [TARSKIK4 f .BINOP-1K1(x,y),g .BINOP-1K1(x9,y9) ]"
sorry

mtheorem funct_4_th_56:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds rngFUNCT-1K2 (|:FUNCT-4K5 f,g :|) c=TARSKIR1 [:ZFMISC-1K2 rngFUNCT-1K2 f,rngFUNCT-1K2 g :]"
sorry

mtheorem funct_4_th_57:
" for X be setHIDDENM2 holds  for X9 be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Y9 be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds domRELAT-1K1 f c=TARSKIR1 [:ZFMISC-1K2 X,Y :] & domRELAT-1K1 g c=TARSKIR1 [:ZFMISC-1K2 X9,Y9 :] implies domRELAT-1K1 (|:FUNCT-4K5 f,g :|) c=TARSKIR1 [:ZFMISC-1K2 [:ZFMISC-1K2 X,X9 :],[:ZFMISC-1K2 Y,Y9 :] :]"
sorry

mtheorem funct_4_th_58:
" for X be setHIDDENM2 holds  for X9 be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Y9 be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds domRELAT-1K1 f =XBOOLE-0R4 [:ZFMISC-1K2 X,Y :] & domRELAT-1K1 g =XBOOLE-0R4 [:ZFMISC-1K2 X9,Y9 :] implies domRELAT-1K1 (|:FUNCT-4K5 f,g :|) =XBOOLE-0R4 [:ZFMISC-1K2 [:ZFMISC-1K2 X,X9 :],[:ZFMISC-1K2 Y,Y9 :] :]"
sorry

mtheorem funct_4_th_59:
" for X be setHIDDENM2 holds  for X9 be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Y9 be setHIDDENM2 holds  for Z be setHIDDENM2 holds  for Z9 be setHIDDENM2 holds  for f be PartFuncPARTFUN1M1-of([:ZFMISC-1K2 X,Y :],Z) holds  for g be PartFuncPARTFUN1M1-of([:ZFMISC-1K2 X9,Y9 :],Z9) holds |:FUNCT-4K5 f,g :| be PartFuncPARTFUN1M1-of([:ZFMISC-1K2 [:ZFMISC-1K2 X,X9 :],[:ZFMISC-1K2 Y,Y9 :] :],[:ZFMISC-1K2 Z,Z9 :])"
sorry

mtheorem funct_4_th_60:
" for X be setHIDDENM2 holds  for X9 be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Y9 be setHIDDENM2 holds  for Z be setHIDDENM2 holds  for Z9 be setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of([:ZFMISC-1K2 X,Y :],Z) holds  for g be FunctionFUNCT-2M1-of([:ZFMISC-1K2 X9,Y9 :],Z9) holds Z <>HIDDENR2 {}XBOOLE-0K1 & Z9 <>HIDDENR2 {}XBOOLE-0K1 implies |:FUNCT-4K5 f,g :| be FunctionFUNCT-2M1-of([:ZFMISC-1K2 [:ZFMISC-1K2 X,X9 :],[:ZFMISC-1K2 Y,Y9 :] :],[:ZFMISC-1K2 Z,Z9 :])"
sorry

mtheorem funct_4_th_61:
" for X be setHIDDENM2 holds  for X9 be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Y9 be setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D9 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of([:ZFMISC-1K2 X,Y :],D) holds  for g be FunctionFUNCT-2M1-of([:ZFMISC-1K2 X9,Y9 :],D9) holds |:FUNCT-4K5 f,g :| be FunctionFUNCT-2M1-of([:ZFMISC-1K2 [:ZFMISC-1K2 X,X9 :],[:ZFMISC-1K2 Y,Y9 :] :],[:ZFMISC-1K2 D,D9 :])"
  using funct_4_th_60 sorry

mdef funct_4_def_4 ("'( _ , _ ')-->FUNCT-4K6'( _ , _ ')" [0,0,0,0]116 ) where
  mlet "x be objectHIDDENM1", "y be objectHIDDENM1", "a be objectHIDDENM1", "b be objectHIDDENM1"
"func (x,y)-->FUNCT-4K6(a,b) \<rightarrow> setHIDDENM2 equals
  (x .-->FUNCOP-1K17 a)+*FUNCT-4K1 (y .-->FUNCOP-1K17 b)"
proof-
  (*coherence*)
    show "(x .-->FUNCOP-1K17 a)+*FUNCT-4K1 (y .-->FUNCOP-1K17 b) be setHIDDENM2"
       sorry
qed "sorry"

mtheorem funct_4_cl_2:
  mlet "x be objectHIDDENM1", "y be objectHIDDENM1", "a be objectHIDDENM1", "b be objectHIDDENM1"
"cluster (x,y)-->FUNCT-4K6(a,b) as-term-is Function-likeFUNCT-1V1\<bar>Relation-likeRELAT-1V1"
proof
(*coherence*)
  show "(x,y)-->FUNCT-4K6(a,b) be Function-likeFUNCT-1V1\<bar>Relation-likeRELAT-1V1"
     sorry
qed "sorry"

mtheorem funct_4_th_62:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for y1 be objectHIDDENM1 holds  for y2 be objectHIDDENM1 holds domRELAT-1K1 ((x1,x2)-->FUNCT-4K6(y1,y2)) =XBOOLE-0R4 {TARSKIK2 x1,x2 } & rngFUNCT-1K2 ((x1,x2)-->FUNCT-4K6(y1,y2)) c=TARSKIR1 {TARSKIK2 y1,y2 }"
sorry

mtheorem funct_4_th_63:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for y1 be objectHIDDENM1 holds  for y2 be objectHIDDENM1 holds (x1 <>HIDDENR2 x2 implies ((x1,x2)-->FUNCT-4K6(y1,y2)).FUNCT-1K1 x1 =HIDDENR1 y1) & ((x1,x2)-->FUNCT-4K6(y1,y2)).FUNCT-1K1 x2 =HIDDENR1 y2"
sorry

mtheorem funct_4_th_64:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for y1 be objectHIDDENM1 holds  for y2 be objectHIDDENM1 holds x1 <>HIDDENR2 x2 implies rngFUNCT-1K2 ((x1,x2)-->FUNCT-4K6(y1,y2)) =XBOOLE-0R4 {TARSKIK2 y1,y2 }"
sorry

mtheorem funct_4_th_65:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for y be objectHIDDENM1 holds (x1,x2)-->FUNCT-4K6(y,y) =FUNCT-1R1 {TARSKIK2 x1,x2 } -->FUNCOP-1K7 y"
sorry

syntax FUNCT_4K7 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" ("'( _ , _ ')-->FUNCT-4K7\<^bsub>'( _ ')\<^esub>'( _ , _ ')" [0,0,0,0,0]116)
translations "(x1,x2)-->FUNCT-4K7\<^bsub>(A)\<^esub>(y1,y2)" \<rightharpoonup> "(x1,x2)-->FUNCT-4K6(y1,y2)"

mtheorem funct_4_add_3:
  mlet "A be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "x1 be objectHIDDENM1", "x2 be objectHIDDENM1", "y1 be ElementSUBSET-1M1-of A", "y2 be ElementSUBSET-1M1-of A"
"cluster (x1,x2)-->FUNCT-4K6(y1,y2) as-term-is FunctionFUNCT-2M1-of({TARSKIK2 x1,x2 },A)"
proof
(*coherence*)
  show "(x1,x2)-->FUNCT-4K6(y1,y2) be FunctionFUNCT-2M1-of({TARSKIK2 x1,x2 },A)"
sorry
qed "sorry"

mtheorem funct_4_th_66:
" for a be objectHIDDENM1 holds  for b be objectHIDDENM1 holds  for c be objectHIDDENM1 holds  for d be objectHIDDENM1 holds  for g be FunctionFUNCT-1M1 holds (domRELAT-1K1 g =XBOOLE-0R4 {TARSKIK2 a,b } & g .FUNCT-1K1 a =HIDDENR1 c) & g .FUNCT-1K1 b =HIDDENR1 d implies g =FUNCT-1R1 (a,b)-->FUNCT-4K6(c,d)"
sorry

mtheorem funct_4_th_67:
" for a be objectHIDDENM1 holds  for b be objectHIDDENM1 holds  for c be objectHIDDENM1 holds  for d be objectHIDDENM1 holds a <>HIDDENR2 c implies (a,c)-->FUNCT-4K6(b,d) =RELAT-1R1 {TARSKIK2 [TARSKIK4 a,b ],[TARSKIK4 c,d ] }"
sorry

mtheorem funct_4_th_68:
" for a be objectHIDDENM1 holds  for b be objectHIDDENM1 holds  for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for x9 be objectHIDDENM1 holds  for y9 be objectHIDDENM1 holds a <>HIDDENR2 b & (a,b)-->FUNCT-4K6(x,y) =FUNCT-1R1 (a,b)-->FUNCT-4K6(x9,y9) implies x =HIDDENR1 x9 & y =HIDDENR1 y9"
sorry

(*begin*)
mtheorem funct_4_th_69:
" for f1 be FunctionFUNCT-1M1 holds  for f2 be FunctionFUNCT-1M1 holds  for g1 be FunctionFUNCT-1M1 holds  for g2 be FunctionFUNCT-1M1 holds (rngFUNCT-1K2 g1 c=TARSKIR1 domRELAT-1K1 f1 & rngFUNCT-1K2 g2 c=TARSKIR1 domRELAT-1K1 f2) & f1 toleratesPARTFUN1R1 f2 implies (f1 +*FUNCT-4K1 f2)*FUNCT-1K3 (g1 +*FUNCT-4K1 g2) =FUNCT-1R1 (f1 *FUNCT-1K3 g1)+*FUNCT-4K1 (f2 *FUNCT-1K3 g2)"
sorry

reserve A, B for "setHIDDENM2"
mtheorem funct_4_th_70:
" for f be FunctionFUNCT-1M1 holds  for A be setHIDDENM2 holds  for B be setHIDDENM2 holds domRELAT-1K1 f c=TARSKIR1 A \\/XBOOLE-0K2 B implies f |RELAT-1K8 A +*FUNCT-4K1 f |RELAT-1K8 B =FUNCT-1R1 f"
sorry

mtheorem funct_4_th_71:
" for p be FunctionFUNCT-1M1 holds  for q be FunctionFUNCT-1M1 holds  for A be setHIDDENM2 holds (p +*FUNCT-4K1 q)|RELAT-1K8 A =FUNCT-1R1 p |RELAT-1K8 A +*FUNCT-4K1 q |RELAT-1K8 A"
sorry

mtheorem funct_4_th_72:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds  for A be setHIDDENM2 holds A missesXBOOLE-0R1 domRELAT-1K1 g implies (f +*FUNCT-4K1 g)|RELAT-1K8 A =FUNCT-1R1 f |RELAT-1K8 A"
sorry

mtheorem funct_4_th_73:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds  for A be setHIDDENM2 holds domRELAT-1K1 f missesXBOOLE-0R1 A implies (f +*FUNCT-4K1 g)|RELAT-1K8 A =FUNCT-1R1 g |RELAT-1K8 A"
sorry

mtheorem funct_4_th_74:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds  for h be FunctionFUNCT-1M1 holds domRELAT-1K1 g =XBOOLE-0R4 domRELAT-1K1 h implies (f +*FUNCT-4K1 g)+*FUNCT-4K1 h =FUNCT-1R1 f +*FUNCT-4K1 h"
sorry

mlemma funct_4_lm_2:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds f c=RELAT-1R2 g implies g +*FUNCT-4K1 f =FUNCT-1R1 g"
sorry

mtheorem funct_4_th_75:
" for f be FunctionFUNCT-1M1 holds  for A be setHIDDENM2 holds f +*FUNCT-4K1 f |RELAT-1K8 A =FUNCT-1R1 f"
  using funct_4_lm_2 relat_1_th_59 sorry

mtheorem funct_4_th_76:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds  for B be setHIDDENM2 holds  for C be setHIDDENM2 holds (domRELAT-1K1 f c=TARSKIR1 B & domRELAT-1K1 g c=TARSKIR1 C) & B missesXBOOLE-0R1 C implies (f +*FUNCT-4K1 g)|RELAT-1K8 B =FUNCT-1R1 f & (f +*FUNCT-4K1 g)|RELAT-1K8 C =FUNCT-1R1 g"
sorry

mtheorem funct_4_th_77:
" for p be FunctionFUNCT-1M1 holds  for q be FunctionFUNCT-1M1 holds  for A be setHIDDENM2 holds domRELAT-1K1 p c=TARSKIR1 A & domRELAT-1K1 q missesXBOOLE-0R1 A implies (p +*FUNCT-4K1 q)|RELAT-1K8 A =FUNCT-1R1 p"
sorry

mtheorem funct_4_th_78:
" for f be FunctionFUNCT-1M1 holds  for A be setHIDDENM2 holds  for B be setHIDDENM2 holds f |RELAT-1K8 (A \\/XBOOLE-0K2 B) =FUNCT-1R1 f |RELAT-1K8 A +*FUNCT-4K1 f |RELAT-1K8 B"
sorry

reserve x, y, i, j, k for "objectHIDDENM1"
mtheorem funct_4_th_79:
" for i be objectHIDDENM1 holds  for j be objectHIDDENM1 holds  for k be objectHIDDENM1 holds (i,j):->FUNCOP-1K19 k =FUNCT-1R1 [TARSKIK4 i,j ] .-->FUNCOP-1K17 k"
   sorry

mtheorem funct_4_th_80:
" for i be objectHIDDENM1 holds  for j be objectHIDDENM1 holds  for k be objectHIDDENM1 holds (i,j):->FUNCOP-1K19 k .BINOP-1K1(i,j) =HIDDENR1 k"
  using funcop_1_th_71 sorry

mtheorem funct_4_th_81:
" for a be objectHIDDENM1 holds  for b be objectHIDDENM1 holds  for c be objectHIDDENM1 holds (a,a)-->FUNCT-4K6(b,c) =FUNCT-1R1 a .-->FUNCOP-1K17 c"
sorry

mtheorem funct_4_th_82:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds x .-->FUNCOP-1K17 y =FUNCT-1R1 {TARSKIK1 [TARSKIK4 x,y ] }"
  using zfmisc_1_th_29 sorry

mtheorem funct_4_th_83:
" for f be FunctionFUNCT-1M1 holds  for a be objectHIDDENM1 holds  for b be objectHIDDENM1 holds  for c be objectHIDDENM1 holds a <>HIDDENR2 c implies (f +*FUNCT-4K1 (a .-->FUNCOP-1K17 b)).FUNCT-1K1 c =XBOOLE-0R4 f .FUNCT-1K1 c"
sorry

mtheorem funct_4_th_84:
" for f be FunctionFUNCT-1M1 holds  for a be objectHIDDENM1 holds  for b be objectHIDDENM1 holds  for c be objectHIDDENM1 holds  for d be objectHIDDENM1 holds a <>HIDDENR2 b implies (f +*FUNCT-4K1 ((a,b)-->FUNCT-4K6(c,d))).FUNCT-1K1 a =HIDDENR1 c & (f +*FUNCT-4K1 ((a,b)-->FUNCT-4K6(c,d))).FUNCT-1K1 b =HIDDENR1 d"
sorry

mtheorem funct_4_th_85:
" for a be setHIDDENM2 holds  for b be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds a inTARSKIR2 domRELAT-1K1 f & f .FUNCT-1K1 a =XBOOLE-0R4 b implies a .-->FUNCOP-1K17 b c=RELAT-1R2 f"
sorry

mtheorem funct_4_th_86:
" for a be setHIDDENM2 holds  for b be setHIDDENM2 holds  for c be setHIDDENM2 holds  for d be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds ((a inTARSKIR2 domRELAT-1K1 f & c inTARSKIR2 domRELAT-1K1 f) & f .FUNCT-1K1 a =XBOOLE-0R4 b) & f .FUNCT-1K1 c =XBOOLE-0R4 d implies (a,c)-->FUNCT-4K6(b,d) c=RELAT-1R2 f"
sorry

mtheorem funct_4_th_87:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds  for h be FunctionFUNCT-1M1 holds f c=RELAT-1R2 h & g c=RELAT-1R2 h implies f +*FUNCT-4K1 g c=RELAT-1R2 h"
sorry

mtheorem funct_4_th_88:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds  for A be setHIDDENM2 holds A /\\XBOOLE-0K3 domRELAT-1K1 f c=TARSKIR1 A /\\XBOOLE-0K3 domRELAT-1K1 g implies (f +*FUNCT-4K1 g |RELAT-1K8 A)|RELAT-1K8 A =FUNCT-1R1 g |RELAT-1K8 A"
sorry

mtheorem funct_4_th_89:
" for f be FunctionFUNCT-1M1 holds  for a be objectHIDDENM1 holds  for b be objectHIDDENM1 holds  for n be objectHIDDENM1 holds  for m be objectHIDDENM1 holds ((f +*FUNCT-4K1 (a .-->FUNCOP-1K17 b))+*FUNCT-4K1 (m .-->FUNCOP-1K17 n)).FUNCT-1K1 m =HIDDENR1 n"
sorry

mtheorem funct_4_th_90:
" for f be FunctionFUNCT-1M1 holds  for n be objectHIDDENM1 holds  for m be objectHIDDENM1 holds ((f +*FUNCT-4K1 (n .-->FUNCOP-1K17 m))+*FUNCT-4K1 (m .-->FUNCOP-1K17 n)).FUNCT-1K1 n =HIDDENR1 m"
sorry

mtheorem funct_4_th_91:
" for f be FunctionFUNCT-1M1 holds  for a be objectHIDDENM1 holds  for b be objectHIDDENM1 holds  for n be objectHIDDENM1 holds  for m be objectHIDDENM1 holds  for x be objectHIDDENM1 holds x <>HIDDENR2 m & x <>HIDDENR2 a implies ((f +*FUNCT-4K1 (a .-->FUNCOP-1K17 b))+*FUNCT-4K1 (m .-->FUNCOP-1K17 n)).FUNCT-1K1 x =XBOOLE-0R4 f .FUNCT-1K1 x"
sorry

mtheorem funct_4_th_92:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds (f be one-to-oneFUNCT-1V2 & g be one-to-oneFUNCT-1V2) & rngFUNCT-1K2 f missesXBOOLE-0R1 rngFUNCT-1K2 g implies f +*FUNCT-4K1 g be one-to-oneFUNCT-1V2"
sorry

mtheorem funct_4_reduce_3:
  mlet "f be FunctionFUNCT-1M1", "g be FunctionFUNCT-1M1"
"reduce (f +*FUNCT-4K1 g)+*FUNCT-4K1 g to f +*FUNCT-4K1 g"
proof
(*reducibility*)
  show "(f +*FUNCT-4K1 g)+*FUNCT-4K1 g =HIDDENR1 f +*FUNCT-4K1 g"
sorry
qed "sorry"

mtheorem funct_4_th_93:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds (f +*FUNCT-4K1 g)+*FUNCT-4K1 g =FUNCT-1R1 f +*FUNCT-4K1 g"
   sorry

mtheorem funct_4_th_94:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds  for h be FunctionFUNCT-1M1 holds  for D be setHIDDENM2 holds (f +*FUNCT-4K1 g)|RELAT-1K8 D =FUNCT-1R1 h |RELAT-1K8 D implies (h +*FUNCT-4K1 g)|RELAT-1K8 D =FUNCT-1R1 (f +*FUNCT-4K1 g)|RELAT-1K8 D"
sorry

mtheorem funct_4_th_95:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds  for h be FunctionFUNCT-1M1 holds  for D be setHIDDENM2 holds f |RELAT-1K8 D =FUNCT-1R1 h |RELAT-1K8 D implies (h +*FUNCT-4K1 g)|RELAT-1K8 D =FUNCT-1R1 (f +*FUNCT-4K1 g)|RELAT-1K8 D"
sorry

mtheorem funct_4_th_96:
" for x be objectHIDDENM1 holds x .-->FUNCOP-1K17 x =FUNCT-1R1 idPARTFUN1K6 {TARSKIK1 x}"
sorry

mtheorem funct_4_th_97:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds f c=RELAT-1R2 g implies f +*FUNCT-4K1 g =FUNCT-1R1 g"
sorry

mtheorem funct_4_th_98:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds f c=RELAT-1R2 g implies g +*FUNCT-4K1 f =FUNCT-1R1 g"
sorry

(*begin*)
mdef funct_4_def_5 (" _ +~FUNCT-4K8'( _ , _ ')" [164,0,0]164 ) where
  mlet "f be FunctionFUNCT-1M1", "x be objectHIDDENM1", "y be objectHIDDENM1"
"func f +~FUNCT-4K8(x,y) \<rightarrow> setHIDDENM2 equals
  f +*FUNCT-4K1 ((x .-->FUNCOP-1K17 y)*FUNCT-1K3 f)"
proof-
  (*coherence*)
    show "f +*FUNCT-4K1 ((x .-->FUNCOP-1K17 y)*FUNCT-1K3 f) be setHIDDENM2"
       sorry
qed "sorry"

mtheorem funct_4_cl_3:
  mlet "f be FunctionFUNCT-1M1", "x be objectHIDDENM1", "y be objectHIDDENM1"
"cluster f +~FUNCT-4K8(x,y) as-term-is Relation-likeRELAT-1V1\<bar>Function-likeFUNCT-1V1"
proof
(*coherence*)
  show "f +~FUNCT-4K8(x,y) be Relation-likeRELAT-1V1\<bar>Function-likeFUNCT-1V1"
     sorry
qed "sorry"

mtheorem funct_4_th_99:
" for f be FunctionFUNCT-1M1 holds  for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds domRELAT-1K1 (f +~FUNCT-4K8(x,y)) =XBOOLE-0R4 domRELAT-1K1 f"
sorry

mtheorem funct_4_th_100:
" for f be FunctionFUNCT-1M1 holds  for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds x <>HIDDENR2 y implies  not x inHIDDENR3 rngFUNCT-1K2 (f +~FUNCT-4K8(x,y))"
sorry

mtheorem funct_4_th_101:
" for f be FunctionFUNCT-1M1 holds  for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds x inHIDDENR3 rngFUNCT-1K2 f implies y inHIDDENR3 rngFUNCT-1K2 (f +~FUNCT-4K8(x,y))"
sorry

mtheorem funct_4_th_102:
" for f be FunctionFUNCT-1M1 holds  for x be objectHIDDENM1 holds f +~FUNCT-4K8(x,x) =FUNCT-1R1 f"
sorry

mtheorem funct_4_th_103:
" for f be FunctionFUNCT-1M1 holds  for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  not x inHIDDENR3 rngFUNCT-1K2 f implies f +~FUNCT-4K8(x,y) =FUNCT-1R1 f"
sorry

mtheorem funct_4_th_104:
" for f be FunctionFUNCT-1M1 holds  for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds rngFUNCT-1K2 (f +~FUNCT-4K8(x,y)) c=TARSKIR1 (rngFUNCT-1K2 f \\SUBSET-1K6 {TARSKIK1 x})\\/XBOOLE-0K2 {TARSKIK1 y}"
sorry

mtheorem funct_4_th_105:
" for f be FunctionFUNCT-1M1 holds  for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for z be objectHIDDENM1 holds f .FUNCT-1K1 z <>HIDDENR2 x implies (f +~FUNCT-4K8(x,y)).FUNCT-1K1 z =XBOOLE-0R4 f .FUNCT-1K1 z"
sorry

mtheorem funct_4_th_106:
" for z be objectHIDDENM1 holds  for f be FunctionFUNCT-1M1 holds  for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds z inHIDDENR3 domRELAT-1K1 f & f .FUNCT-1K1 z =HIDDENR1 x implies (f +~FUNCT-4K8(x,y)).FUNCT-1K1 z =HIDDENR1 y"
sorry

mtheorem funct_4_th_107:
" for f be FunctionFUNCT-1M1 holds  for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  not x inHIDDENR3 domRELAT-1K1 f implies f c=RELAT-1R2 f +*FUNCT-4K1 (x .-->FUNCOP-1K17 y)"
sorry

mtheorem funct_4_th_108:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be PartFuncPARTFUN1M1-of(X,Y) holds  for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds x inHIDDENR3 X & y inHIDDENR3 Y implies f +*FUNCT-4K1 (x .-->FUNCOP-1K17 y) be PartFuncPARTFUN1M1-of(X,Y)"
sorry

mtheorem funct_4_cl_4:
  mlet "f be FunctionFUNCT-1M1", "g be  non emptyXBOOLE-0V1\<bar>FunctionFUNCT-1M1"
"cluster f +*FUNCT-4K1 g as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "f +*FUNCT-4K1 g be  non emptyXBOOLE-0V1"
sorry
qed "sorry"

mtheorem funct_4_cl_5:
  mlet "f be FunctionFUNCT-1M1", "g be  non emptyXBOOLE-0V1\<bar>FunctionFUNCT-1M1"
"cluster g +*FUNCT-4K1 f as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "g +*FUNCT-4K1 f be  non emptyXBOOLE-0V1"
sorry
qed "sorry"

mtheorem funct_4_cl_6:
  mlet "f be non-emptyFUNCT-1V4\<bar>FunctionFUNCT-1M1", "g be non-emptyFUNCT-1V4\<bar>FunctionFUNCT-1M1"
"cluster f +*FUNCT-4K1 g as-term-is non-emptyFUNCT-1V4"
proof
(*coherence*)
  show "f +*FUNCT-4K1 g be non-emptyFUNCT-1V4"
sorry
qed "sorry"

syntax FUNCT_4K9 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ +*FUNCT-4K9\<^bsub>'( _ , _ ')\<^esub>  _ " [164,0,0,164]164)
translations "f +*FUNCT-4K9\<^bsub>(X,Y)\<^esub> g" \<rightharpoonup> "f +*FUNCT-4K1 g"

mtheorem funct_4_add_4:
  mlet "X be setHIDDENM2", "Y be setHIDDENM2", "f be PartFuncPARTFUN1M1-of(X,Y)", "g be PartFuncPARTFUN1M1-of(X,Y)"
"cluster f +*FUNCT-4K1 g as-term-is PartFuncPARTFUN1M1-of(X,Y)"
proof
(*coherence*)
  show "f +*FUNCT-4K1 g be PartFuncPARTFUN1M1-of(X,Y)"
sorry
qed "sorry"

reserve x for "setHIDDENM2"
mtheorem funct_4_th_109:
" for z be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for x be setHIDDENM2 holds domRELAT-1K1 ((x -->FUNCOP-1K7 y)+*FUNCT-4K1 (x .-->FUNCOP-1K17 z)) =XBOOLE-0R4 succORDINAL1K1 x"
sorry

mtheorem funct_4_th_110:
" for z be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for x be setHIDDENM2 holds domRELAT-1K1 (((x -->FUNCOP-1K7 y)+*FUNCT-4K1 (x .-->FUNCOP-1K17 z))+*FUNCT-4K1 (succORDINAL1K1 x .-->FUNCOP-1K17 z)) =XBOOLE-0R4 succORDINAL1K1 (succORDINAL1K1 x)"
sorry

reserve x for "objectHIDDENM1"
mtheorem funct_4_cl_7:
  mlet "f be Function-yieldingFUNCOP-1V1\<bar>FunctionFUNCT-1M1", "g be Function-yieldingFUNCOP-1V1\<bar>FunctionFUNCT-1M1"
"cluster f +*FUNCT-4K1 g as-term-is Function-yieldingFUNCOP-1V1"
proof
(*coherence*)
  show "f +*FUNCT-4K1 g be Function-yieldingFUNCOP-1V1"
sorry
qed "sorry"

mtheorem funct_4_cl_8:
  mlet "I be setHIDDENM2", "f be I -definedRELAT-1V4\<bar>FunctionFUNCT-1M1", "g be I -definedRELAT-1V4\<bar>FunctionFUNCT-1M1"
"cluster f +*FUNCT-4K1 g as-term-is I -definedRELAT-1V4"
proof
(*coherence*)
  show "f +*FUNCT-4K1 g be I -definedRELAT-1V4"
sorry
qed "sorry"

mtheorem funct_4_cl_9:
  mlet "I be setHIDDENM2", "f be totalPARTFUN1V1\<^bsub>(I)\<^esub>\<bar>I -definedRELAT-1V4\<bar>FunctionFUNCT-1M1", "g be I -definedRELAT-1V4\<bar>FunctionFUNCT-1M1"
"cluster f +*FUNCT-4K1 g as-term-is totalPARTFUN1V1\<^bsub>(I)\<^esub> for I -definedRELAT-1V4\<bar>FunctionFUNCT-1M1"
proof
(*coherence*)
  show " for it be I -definedRELAT-1V4\<bar>FunctionFUNCT-1M1 holds it =HIDDENR1 f +*FUNCT-4K1 g implies it be totalPARTFUN1V1\<^bsub>(I)\<^esub>"
sorry
qed "sorry"

mtheorem funct_4_cl_10:
  mlet "I be setHIDDENM2", "f be totalPARTFUN1V1\<^bsub>(I)\<^esub>\<bar>I -definedRELAT-1V4\<bar>FunctionFUNCT-1M1", "g be I -definedRELAT-1V4\<bar>FunctionFUNCT-1M1"
"cluster g +*FUNCT-4K1 f as-term-is totalPARTFUN1V1\<^bsub>(I)\<^esub> for I -definedRELAT-1V4\<bar>FunctionFUNCT-1M1"
proof
(*coherence*)
  show " for it be I -definedRELAT-1V4\<bar>FunctionFUNCT-1M1 holds it =HIDDENR1 g +*FUNCT-4K1 f implies it be totalPARTFUN1V1\<^bsub>(I)\<^esub>"
sorry
qed "sorry"

mtheorem funct_4_cl_11:
  mlet "I be setHIDDENM2", "g be I -valuedRELAT-1V5\<bar>FunctionFUNCT-1M1", "h be I -valuedRELAT-1V5\<bar>FunctionFUNCT-1M1"
"cluster g +*FUNCT-4K1 h as-term-is I -valuedRELAT-1V5"
proof
(*coherence*)
  show "g +*FUNCT-4K1 h be I -valuedRELAT-1V5"
sorry
qed "sorry"

mtheorem funct_4_cl_12:
  mlet "f be FunctionFUNCT-1M1", "g be f -compatibleFUNCT-1V7\<bar>FunctionFUNCT-1M1", "h be f -compatibleFUNCT-1V7\<bar>FunctionFUNCT-1M1"
"cluster g +*FUNCT-4K1 h as-term-is f -compatibleFUNCT-1V7"
proof
(*coherence*)
  show "g +*FUNCT-4K1 h be f -compatibleFUNCT-1V7"
sorry
qed "sorry"

mtheorem funct_4_th_111:
" for f be FunctionFUNCT-1M1 holds  for A be setHIDDENM2 holds f |RELAT-1K8 A +*FUNCT-4K1 f =FUNCT-1R1 f"
  using funct_4_th_97 relat_1_th_59 sorry

mtheorem funct_4_th_112:
" for y be objectHIDDENM1 holds  for x be objectHIDDENM1 holds  for R be RelationRELAT-1M1 holds domRELAT-1K1 R =XBOOLE-0R4 {TARSKIK1 x} & rngRELAT-1K2 R =XBOOLE-0R4 {TARSKIK1 y} implies R =RELAT-1R1 x .-->FUNCOP-1K17 y"
sorry

mtheorem funct_4_th_113:
" for f be FunctionFUNCT-1M1 holds  for y be objectHIDDENM1 holds  for x be objectHIDDENM1 holds (f +*FUNCT-4K1 (x .-->FUNCOP-1K17 y)).FUNCT-1K1 x =HIDDENR1 y"
sorry

mtheorem funct_4_th_114:
" for z1 be objectHIDDENM1 holds  for z2 be objectHIDDENM1 holds  for f be FunctionFUNCT-1M1 holds  for x be objectHIDDENM1 holds (f +*FUNCT-4K1 (x .-->FUNCOP-1K17 z1))+*FUNCT-4K1 (x .-->FUNCOP-1K17 z2) =FUNCT-1R1 f +*FUNCT-4K1 (x .-->FUNCOP-1K17 z2)"
sorry

mtheorem funct_4_cl_13:
  mlet "A be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "a be ElementSUBSET-1M1-of A", "b be ElementSUBSET-1M1-of A", "x be setHIDDENM2", "y be setHIDDENM2"
"cluster (a,b)-->FUNCT-4K6(x,y) as-term-is A -definedRELAT-1V4"
proof
(*coherence*)
  show "(a,b)-->FUNCT-4K6(x,y) be A -definedRELAT-1V4"
     sorry
qed "sorry"

mtheorem funct_4_th_115:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds  for h be FunctionFUNCT-1M1 holds domRELAT-1K1 g missesXBOOLE-0R1 domRELAT-1K1 h implies ((f +*FUNCT-4K1 g)+*FUNCT-4K1 h)+*FUNCT-4K1 g =FUNCT-1R1 (f +*FUNCT-4K1 g)+*FUNCT-4K1 h"
sorry

mtheorem funct_4_th_116:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds  for h be FunctionFUNCT-1M1 holds domRELAT-1K1 f missesXBOOLE-0R1 domRELAT-1K1 h & f c=RELAT-1R2 g +*FUNCT-4K1 h implies f c=RELAT-1R2 g"
sorry

mtheorem funct_4_th_117:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds  for h be FunctionFUNCT-1M1 holds domRELAT-1K1 f missesXBOOLE-0R1 domRELAT-1K1 h & f c=RELAT-1R2 g implies f c=RELAT-1R2 g +*FUNCT-4K1 h"
sorry

mtheorem funct_4_th_118:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds  for h be FunctionFUNCT-1M1 holds domRELAT-1K1 g missesXBOOLE-0R1 domRELAT-1K1 h implies (f +*FUNCT-4K1 g)+*FUNCT-4K1 h =FUNCT-1R1 (f +*FUNCT-4K1 h)+*FUNCT-4K1 g"
sorry

mtheorem funct_4_th_119:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds domRELAT-1K1 f missesXBOOLE-0R1 domRELAT-1K1 g implies f +*FUNCT-4K1 g \\SUBSET-1K6 g =FUNCT-1R1 f"
sorry

mtheorem funct_4_th_120:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds domRELAT-1K1 f missesXBOOLE-0R1 domRELAT-1K1 g implies f \\SUBSET-1K6 g =FUNCT-1R1 f"
  using relat_1_th_179 xboole_1_th_83 sorry

mtheorem funct_4_th_121:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds  for h be FunctionFUNCT-1M1 holds domRELAT-1K1 g missesXBOOLE-0R1 domRELAT-1K1 h implies (f \\SUBSET-1K6 g)+*FUNCT-4K1 h =FUNCT-1R1 f +*FUNCT-4K1 h \\SUBSET-1K6 g"
sorry

mtheorem funct_4_th_122:
" for f1 be FunctionFUNCT-1M1 holds  for f2 be FunctionFUNCT-1M1 holds  for g1 be FunctionFUNCT-1M1 holds  for g2 be FunctionFUNCT-1M1 holds (f1 c=RELAT-1R2 g1 & f2 c=RELAT-1R2 g2) & domRELAT-1K1 f1 missesXBOOLE-0R1 domRELAT-1K1 g2 implies f1 +*FUNCT-4K1 f2 c=RELAT-1R2 g1 +*FUNCT-4K1 g2"
sorry

mtheorem funct_4_th_123:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds  for h be FunctionFUNCT-1M1 holds f c=RELAT-1R2 g implies f +*FUNCT-4K1 h c=RELAT-1R2 g +*FUNCT-4K1 h"
sorry

mtheorem funct_4_th_124:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds  for h be FunctionFUNCT-1M1 holds f c=RELAT-1R2 g & domRELAT-1K1 f missesXBOOLE-0R1 domRELAT-1K1 h implies f c=RELAT-1R2 g +*FUNCT-4K1 h"
sorry

mtheorem funct_4_cl_14:
  mlet "x be setHIDDENM2", "y be setHIDDENM2"
"cluster x .-->FUNCOP-1K17 y as-term-is trivialSUBSET-1V2"
proof
(*coherence*)
  show "x .-->FUNCOP-1K17 y be trivialSUBSET-1V2"
     sorry
qed "sorry"

mtheorem funct_4_th_125:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds  for h be FunctionFUNCT-1M1 holds (f toleratesPARTFUN1R1 g & g toleratesPARTFUN1R1 h) & h toleratesPARTFUN1R1 f implies f +*FUNCT-4K1 g toleratesPARTFUN1R1 h"
sorry

reserve A1, A2, B1, B2 for " non emptyXBOOLE-0V1\<bar>setHIDDENM2"
reserve Y1 for " non emptyXBOOLE-0V1\<bar>SubsetSUBSET-1M2-of A1"
reserve Y2 for " non emptyXBOOLE-0V1\<bar>SubsetSUBSET-1M2-of A2"
syntax FUNCT_4K10 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" ("|:FUNCT-4K10\<^bsub>'( _ , _ ')\<^esub> _ , _ :|" [0,0,0,0]164)
translations "|:FUNCT-4K10\<^bsub>(A,B)\<^esub> f,g :|" \<rightharpoonup> "|:FUNCT-4K5 f,g :|"

mtheorem funct_4_add_5:
  mlet "A be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "B be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "f be PartFuncPARTFUN1M1-of([:ZFMISC-1K2 A,A :],A)", "g be PartFuncPARTFUN1M1-of([:ZFMISC-1K2 B,B :],B)"
"cluster |:FUNCT-4K5 f,g :| as-term-is PartFuncPARTFUN1M1-of([:ZFMISC-1K2 [:ZFMISC-1K2 A,B :],[:ZFMISC-1K2 A,B :] :],[:ZFMISC-1K2 A,B :])"
proof
(*coherence*)
  show "|:FUNCT-4K5 f,g :| be PartFuncPARTFUN1M1-of([:ZFMISC-1K2 [:ZFMISC-1K2 A,B :],[:ZFMISC-1K2 A,B :] :],[:ZFMISC-1K2 A,B :])"
    using funct_4_th_59 sorry
qed "sorry"

mtheorem funct_4_th_126:
" for A1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for A2 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for Y1 be  non emptyXBOOLE-0V1\<bar>SubsetSUBSET-1M2-of A1 holds  for Y2 be  non emptyXBOOLE-0V1\<bar>SubsetSUBSET-1M2-of A2 holds  for f be PartFuncPARTFUN1M1-of([:ZFMISC-1K2 A1,A1 :],A1) holds  for g be PartFuncPARTFUN1M1-of([:ZFMISC-1K2 A2,A2 :],A2) holds  for F be PartFuncPARTFUN1M1-of([:ZFMISC-1K2 Y1,Y1 :],Y1) holds F =FUNCT-1R1 f ||REALSET1K1 Y1 implies ( for G be PartFuncPARTFUN1M1-of([:ZFMISC-1K2 Y2,Y2 :],Y2) holds G =FUNCT-1R1 g ||REALSET1K1 Y2 implies |:FUNCT-4K10\<^bsub>(Y1,Y2)\<^esub> F,G :| =FUNCT-1R1 (|:FUNCT-4K10\<^bsub>(A1,A2)\<^esub> f,g :|)||REALSET1K1 ([:ZFMISC-1K2 Y1,Y2 :]))"
sorry

mtheorem funct_4_th_127:
" for z be objectHIDDENM1 holds  for f be FunctionFUNCT-1M1 holds  for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds x <>HIDDENR2 y implies (f +~FUNCT-4K8(x,y))+~FUNCT-4K8(x,z) =FUNCT-1R1 f +~FUNCT-4K8(x,y)"
sorry

reserve a, b, c, x, y, z, w, d for "objectHIDDENM1"
mdef funct_4_def_6 ("'( _ , _ , _ ')-->FUNCT-4K11'( _ , _ , _ ')" [0,0,0,0,0,0]116 ) where
  mlet "a be objectHIDDENM1", "b be objectHIDDENM1", "c be objectHIDDENM1", "x be objectHIDDENM1", "y be objectHIDDENM1", "z be objectHIDDENM1"
"func (a,b,c)-->FUNCT-4K11(x,y,z) \<rightarrow> setHIDDENM2 equals
  ((a,b)-->FUNCT-4K6(x,y))+*FUNCT-4K1 (c .-->FUNCOP-1K17 z)"
proof-
  (*coherence*)
    show "((a,b)-->FUNCT-4K6(x,y))+*FUNCT-4K1 (c .-->FUNCOP-1K17 z) be setHIDDENM2"
       sorry
qed "sorry"

mtheorem funct_4_cl_15:
  mlet "a be objectHIDDENM1", "b be objectHIDDENM1", "c be objectHIDDENM1", "x be objectHIDDENM1", "y be objectHIDDENM1", "z be objectHIDDENM1"
"cluster (a,b,c)-->FUNCT-4K11(x,y,z) as-term-is Function-likeFUNCT-1V1\<bar>Relation-likeRELAT-1V1"
proof
(*coherence*)
  show "(a,b,c)-->FUNCT-4K11(x,y,z) be Function-likeFUNCT-1V1\<bar>Relation-likeRELAT-1V1"
     sorry
qed "sorry"

mtheorem funct_4_th_128:
" for a be objectHIDDENM1 holds  for b be objectHIDDENM1 holds  for c be objectHIDDENM1 holds  for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for z be objectHIDDENM1 holds domRELAT-1K1 ((a,b,c)-->FUNCT-4K11(x,y,z)) =XBOOLE-0R4 {ENUMSET1K1 a,b,c }"
sorry

mtheorem funct_4_th_129:
" for a be objectHIDDENM1 holds  for b be objectHIDDENM1 holds  for c be objectHIDDENM1 holds  for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for z be objectHIDDENM1 holds rngFUNCT-1K2 ((a,b,c)-->FUNCT-4K11(x,y,z)) c=TARSKIR1 {ENUMSET1K1 x,y,z }"
sorry

mtheorem funct_4_th_130:
" for a be objectHIDDENM1 holds  for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for z be objectHIDDENM1 holds (a,a,a)-->FUNCT-4K11(x,y,z) =FUNCT-1R1 a .-->FUNCOP-1K17 z"
sorry

mtheorem funct_4_th_131:
" for a be objectHIDDENM1 holds  for b be objectHIDDENM1 holds  for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for z be objectHIDDENM1 holds (a,a,b)-->FUNCT-4K11(x,y,z) =FUNCT-1R1 (a,b)-->FUNCT-4K6(y,z)"
  using funct_4_th_81 sorry

mtheorem funct_4_th_132:
" for a be objectHIDDENM1 holds  for b be objectHIDDENM1 holds  for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for z be objectHIDDENM1 holds a <>HIDDENR2 b implies (a,b,a)-->FUNCT-4K11(x,y,z) =FUNCT-1R1 (a,b)-->FUNCT-4K6(z,y)"
sorry

mtheorem funct_4_th_133:
" for a be objectHIDDENM1 holds  for b be objectHIDDENM1 holds  for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for z be objectHIDDENM1 holds (a,b,b)-->FUNCT-4K11(x,y,z) =FUNCT-1R1 (a,b)-->FUNCT-4K6(x,z)"
sorry

mtheorem funct_4_th_134:
" for a be objectHIDDENM1 holds  for b be objectHIDDENM1 holds  for c be objectHIDDENM1 holds  for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for z be objectHIDDENM1 holds a <>HIDDENR2 b & a <>HIDDENR2 c implies ((a,b,c)-->FUNCT-4K11(x,y,z)).FUNCT-1K1 a =HIDDENR1 x"
sorry

mtheorem funct_4_th_135:
" for a be objectHIDDENM1 holds  for b be objectHIDDENM1 holds  for c be objectHIDDENM1 holds  for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for z be objectHIDDENM1 holds (b <>HIDDENR2 c implies ((a,b,c)-->FUNCT-4K11(x,y,z)).FUNCT-1K1 b =HIDDENR1 y) & ((a,b,c)-->FUNCT-4K11(x,y,z)).FUNCT-1K1 c =HIDDENR1 z"
sorry

mtheorem funct_4_th_136:
" for a be objectHIDDENM1 holds  for b be objectHIDDENM1 holds  for c be objectHIDDENM1 holds  for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for z be objectHIDDENM1 holds  for f be FunctionFUNCT-1M1 holds ((domRELAT-1K1 f =XBOOLE-0R4 {ENUMSET1K1 a,b,c } & f .FUNCT-1K1 a =HIDDENR1 x) & f .FUNCT-1K1 b =HIDDENR1 y) & f .FUNCT-1K1 c =HIDDENR1 z implies f =FUNCT-1R1 (a,b,c)-->FUNCT-4K11(x,y,z)"
sorry

mdef funct_4_def_7 ("'( _ , _ , _ , _ ')-->FUNCT-4K12'( _ , _ , _ , _ ')" [0,0,0,0,0,0,0,0]116 ) where
  mlet "x be objectHIDDENM1", "y be objectHIDDENM1", "w be objectHIDDENM1", "z be objectHIDDENM1", "a be objectHIDDENM1", "b be objectHIDDENM1", "c be objectHIDDENM1", "d be objectHIDDENM1"
"func (x,y,w,z)-->FUNCT-4K12(a,b,c,d) \<rightarrow> setHIDDENM2 equals
  ((x,y)-->FUNCT-4K6(a,b))+*FUNCT-4K1 ((w,z)-->FUNCT-4K6(c,d))"
proof-
  (*coherence*)
    show "((x,y)-->FUNCT-4K6(a,b))+*FUNCT-4K1 ((w,z)-->FUNCT-4K6(c,d)) be setHIDDENM2"
       sorry
qed "sorry"

mtheorem funct_4_cl_16:
  mlet "x be objectHIDDENM1", "y be objectHIDDENM1", "w be objectHIDDENM1", "z be objectHIDDENM1", "a be objectHIDDENM1", "b be objectHIDDENM1", "c be objectHIDDENM1", "d be objectHIDDENM1"
"cluster (x,y,w,z)-->FUNCT-4K12(a,b,c,d) as-term-is Function-likeFUNCT-1V1\<bar>Relation-likeRELAT-1V1"
proof
(*coherence*)
  show "(x,y,w,z)-->FUNCT-4K12(a,b,c,d) be Function-likeFUNCT-1V1\<bar>Relation-likeRELAT-1V1"
     sorry
qed "sorry"

mtheorem funct_4_th_137:
" for a be objectHIDDENM1 holds  for b be objectHIDDENM1 holds  for c be objectHIDDENM1 holds  for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for z be objectHIDDENM1 holds  for w be objectHIDDENM1 holds  for d be objectHIDDENM1 holds domRELAT-1K1 ((x,y,w,z)-->FUNCT-4K12(a,b,c,d)) =XBOOLE-0R4 {ENUMSET1K2 x,y,w,z }"
sorry

mtheorem funct_4_th_138:
" for a be objectHIDDENM1 holds  for b be objectHIDDENM1 holds  for c be objectHIDDENM1 holds  for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for z be objectHIDDENM1 holds  for w be objectHIDDENM1 holds  for d be objectHIDDENM1 holds rngFUNCT-1K2 ((x,y,w,z)-->FUNCT-4K12(a,b,c,d)) c=TARSKIR1 {ENUMSET1K2 a,b,c,d }"
sorry

mtheorem funct_4_th_139:
" for a be objectHIDDENM1 holds  for b be objectHIDDENM1 holds  for c be objectHIDDENM1 holds  for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for z be objectHIDDENM1 holds  for w be objectHIDDENM1 holds  for d be objectHIDDENM1 holds ((x,y,w,z)-->FUNCT-4K12(a,b,c,d)).FUNCT-1K1 z =HIDDENR1 d"
sorry

mtheorem funct_4_th_140:
" for a be objectHIDDENM1 holds  for b be objectHIDDENM1 holds  for c be objectHIDDENM1 holds  for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for z be objectHIDDENM1 holds  for w be objectHIDDENM1 holds  for d be objectHIDDENM1 holds w <>HIDDENR2 z implies ((x,y,w,z)-->FUNCT-4K12(a,b,c,d)).FUNCT-1K1 w =HIDDENR1 c"
sorry

mtheorem funct_4_th_141:
" for a be objectHIDDENM1 holds  for b be objectHIDDENM1 holds  for c be objectHIDDENM1 holds  for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for z be objectHIDDENM1 holds  for w be objectHIDDENM1 holds  for d be objectHIDDENM1 holds y <>HIDDENR2 w & y <>HIDDENR2 z implies ((x,y,w,z)-->FUNCT-4K12(a,b,c,d)).FUNCT-1K1 y =HIDDENR1 b"
sorry

mtheorem funct_4_th_142:
" for a be objectHIDDENM1 holds  for b be objectHIDDENM1 holds  for c be objectHIDDENM1 holds  for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for z be objectHIDDENM1 holds  for w be objectHIDDENM1 holds  for d be objectHIDDENM1 holds (x <>HIDDENR2 y & x <>HIDDENR2 w) & x <>HIDDENR2 z implies ((x,y,w,z)-->FUNCT-4K12(a,b,c,d)).FUNCT-1K1 x =HIDDENR1 a"
sorry

mtheorem funct_4_th_143:
" for a be objectHIDDENM1 holds  for b be objectHIDDENM1 holds  for c be objectHIDDENM1 holds  for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for z be objectHIDDENM1 holds  for w be objectHIDDENM1 holds  for d be objectHIDDENM1 holds (x,y,w,z)are-mutually-distinctZFMISC-1R2 implies rngFUNCT-1K2 ((x,y,w,z)-->FUNCT-4K12(a,b,c,d)) =XBOOLE-0R4 {ENUMSET1K2 a,b,c,d }"
sorry

mtheorem funct_4_th_144:
" for a be objectHIDDENM1 holds  for b be objectHIDDENM1 holds  for c be objectHIDDENM1 holds  for d be objectHIDDENM1 holds  for e be objectHIDDENM1 holds  for i be objectHIDDENM1 holds  for j be objectHIDDENM1 holds  for k be objectHIDDENM1 holds  for g be FunctionFUNCT-1M1 holds (((domRELAT-1K1 g =XBOOLE-0R4 {ENUMSET1K2 a,b,c,d } & g .FUNCT-1K1 a =HIDDENR1 e) & g .FUNCT-1K1 b =HIDDENR1 i) & g .FUNCT-1K1 c =HIDDENR1 j) & g .FUNCT-1K1 d =HIDDENR1 k implies g =FUNCT-1R1 (a,b,c,d)-->FUNCT-4K12(e,i,j,k)"
sorry

mtheorem funct_4_th_145:
" for a be objectHIDDENM1 holds  for c be objectHIDDENM1 holds  for b be objectHIDDENM1 holds  for d be objectHIDDENM1 holds  for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for z be objectHIDDENM1 holds  for w be objectHIDDENM1 holds (a,c,x,w)are-mutually-distinctZFMISC-1R2 implies (a,c,x,w)-->FUNCT-4K12(b,d,y,z) =XBOOLE-0R4 {ENUMSET1K2 [TARSKIK4 a,b ],[TARSKIK4 c,d ],[TARSKIK4 x,y ],[TARSKIK4 w,z ] }"
sorry

mtheorem funct_4_th_146:
" for a be objectHIDDENM1 holds  for b be objectHIDDENM1 holds  for c be objectHIDDENM1 holds  for d be objectHIDDENM1 holds  for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for z be objectHIDDENM1 holds  for w be objectHIDDENM1 holds  for x9 be objectHIDDENM1 holds  for y9 be objectHIDDENM1 holds  for z9 be objectHIDDENM1 holds  for w9 be objectHIDDENM1 holds (a,b,c,d)are-mutually-distinctZFMISC-1R2 & (a,b,c,d)-->FUNCT-4K12(x,y,z,w) =FUNCT-1R1 (a,b,c,d)-->FUNCT-4K12(x9,y9,z9,w9) implies ((x =HIDDENR1 x9 & y =HIDDENR1 y9) & z =HIDDENR1 z9) & w =HIDDENR1 w9"
sorry

mtheorem funct_4_th_147:
" for a1 be objectHIDDENM1 holds  for a2 be objectHIDDENM1 holds  for a3 be objectHIDDENM1 holds  for b1 be objectHIDDENM1 holds  for b2 be objectHIDDENM1 holds  for b3 be objectHIDDENM1 holds (a1,a2,a3)are-mutually-distinctZFMISC-1R1 implies rngFUNCT-1K2 ((a1,a2,a3)-->FUNCT-4K11(b1,b2,b3)) =XBOOLE-0R4 {ENUMSET1K1 b1,b2,b3 }"
sorry

syntax FUNCT_4K13 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" ("~FUNCT-4K13\<^bsub>'( _ , _ , _ ')\<^esub>  _ " [0,0,0,228]228)
translations "~FUNCT-4K13\<^bsub>(C,D,E)\<^esub> f" \<rightharpoonup> "~FUNCT-4K2 f"

mtheorem funct_4_def_8:
  mlet "C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "E be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "f be FunctionFUNCT-2M1-of([:ZFMISC-1K2 C,D :],E)"
"redefine func ~FUNCT-4K13\<^bsub>(C,D,E)\<^esub> f \<rightarrow> FunctionFUNCT-2M1-of([:ZFMISC-1K2 D,C :],E) means
  \<lambda>it.  for d be ElementSUBSET-1M1-of D holds  for c be ElementSUBSET-1M1-of C holds it .BINOP-1K2\<^bsub>(D,C,E)\<^esub>(d,c) =XBOOLE-0R4 f .BINOP-1K2\<^bsub>(C,D,E)\<^esub>(c,d)"
proof
(*compatibility*)
  show " for it be FunctionFUNCT-2M1-of([:ZFMISC-1K2 D,C :],E) holds it =HIDDENR1 ~FUNCT-4K13\<^bsub>(C,D,E)\<^esub> f iff ( for d be ElementSUBSET-1M1-of D holds  for c be ElementSUBSET-1M1-of C holds it .BINOP-1K2\<^bsub>(D,C,E)\<^esub>(d,c) =XBOOLE-0R4 f .BINOP-1K2\<^bsub>(C,D,E)\<^esub>(c,d))"
sorry
qed "sorry"

mtheorem funct_4_add_6:
  mlet "C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "E be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "f be FunctionFUNCT-2M1-of([:ZFMISC-1K2 C,D :],E)"
"cluster ~FUNCT-4K2 f as-term-is FunctionFUNCT-2M1-of([:ZFMISC-1K2 D,C :],E)"
proof
(*coherence*)
  show "~FUNCT-4K2 f be FunctionFUNCT-2M1-of([:ZFMISC-1K2 D,C :],E)"
sorry
qed "sorry"

end
