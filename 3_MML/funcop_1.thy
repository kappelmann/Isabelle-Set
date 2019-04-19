theory funcop_1
  imports funct_3 wellord1 grfunc_1
begin
(*begin*)
reserve f, g, h for "FunctionFUNCT-1M1"
reserve A for "setHIDDENM2"
mtheorem funcop_1_th_1:
" for A be setHIDDENM2 holds deltaFUNCT-3K13 A =FUNCT-1R1 <:FUNCT-3K14 idPARTFUN1K6 A,idPARTFUN1K6 A :>"
sorry

reserve F for "FunctionFUNCT-1M1"
reserve B, x, y, y1, y2, z for "setHIDDENM2"
mdef funcop_1_def_1 (" _ ~FUNCOP-1K1" [228]228 ) where
  mlet "f be FunctionFUNCT-1M1"
"func f ~FUNCOP-1K1 \<rightarrow> FunctionFUNCT-1M1 means
  \<lambda>it. domRELAT-1K1 it =XBOOLE-0R4 domRELAT-1K1 f & ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 f implies ( for y be objectHIDDENM1 holds  for z be objectHIDDENM1 holds f .FUNCT-1K1 x =HIDDENR1 [TARSKIK4 y,z ] implies it .FUNCT-1K1 x =HIDDENR1 [TARSKIK4 z,y ]) & (f .FUNCT-1K1 x =XBOOLE-0R4 it .FUNCT-1K1 x or ( ex y be objectHIDDENM1 st  ex z be objectHIDDENM1 st f .FUNCT-1K1 x =HIDDENR1 [TARSKIK4 y,z ])))"
proof-
  (*existence*)
    show " ex it be FunctionFUNCT-1M1 st domRELAT-1K1 it =XBOOLE-0R4 domRELAT-1K1 f & ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 f implies ( for y be objectHIDDENM1 holds  for z be objectHIDDENM1 holds f .FUNCT-1K1 x =HIDDENR1 [TARSKIK4 y,z ] implies it .FUNCT-1K1 x =HIDDENR1 [TARSKIK4 z,y ]) & (f .FUNCT-1K1 x =XBOOLE-0R4 it .FUNCT-1K1 x or ( ex y be objectHIDDENM1 st  ex z be objectHIDDENM1 st f .FUNCT-1K1 x =HIDDENR1 [TARSKIK4 y,z ])))"
sorry
  (*uniqueness*)
    show " for it1 be FunctionFUNCT-1M1 holds  for it2 be FunctionFUNCT-1M1 holds (domRELAT-1K1 it1 =XBOOLE-0R4 domRELAT-1K1 f & ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 f implies ( for y be objectHIDDENM1 holds  for z be objectHIDDENM1 holds f .FUNCT-1K1 x =HIDDENR1 [TARSKIK4 y,z ] implies it1 .FUNCT-1K1 x =HIDDENR1 [TARSKIK4 z,y ]) & (f .FUNCT-1K1 x =XBOOLE-0R4 it1 .FUNCT-1K1 x or ( ex y be objectHIDDENM1 st  ex z be objectHIDDENM1 st f .FUNCT-1K1 x =HIDDENR1 [TARSKIK4 y,z ])))) & (domRELAT-1K1 it2 =XBOOLE-0R4 domRELAT-1K1 f & ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 f implies ( for y be objectHIDDENM1 holds  for z be objectHIDDENM1 holds f .FUNCT-1K1 x =HIDDENR1 [TARSKIK4 y,z ] implies it2 .FUNCT-1K1 x =HIDDENR1 [TARSKIK4 z,y ]) & (f .FUNCT-1K1 x =XBOOLE-0R4 it2 .FUNCT-1K1 x or ( ex y be objectHIDDENM1 st  ex z be objectHIDDENM1 st f .FUNCT-1K1 x =HIDDENR1 [TARSKIK4 y,z ])))) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mtheorem FUNCOP_1K1_involutiveness:
" for f be FunctionFUNCT-1M1 holds (f ~FUNCOP-1K1)~FUNCOP-1K1 =HIDDENR1 f"
sorry

mtheorem funcop_1_th_2:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds <:FUNCT-3K14 f,g :> =FUNCT-1R1 (<:FUNCT-3K14 g,f :>)~FUNCOP-1K1"
sorry

mtheorem funcop_1_th_3:
" for f be FunctionFUNCT-1M1 holds  for A be setHIDDENM2 holds (f |RELAT-1K8 A)~FUNCOP-1K1 =FUNCT-1R1 f ~FUNCOP-1K1 |RELAT-1K8 A"
sorry

mtheorem funcop_1_th_4:
" for A be setHIDDENM2 holds (deltaFUNCT-3K13 A)~FUNCOP-1K1 =FUNCT-1R1 deltaFUNCT-3K13 A"
sorry

mtheorem funcop_1_th_5:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds  for A be setHIDDENM2 holds (<:FUNCT-3K14 f,g :>)|RELAT-1K8 A =FUNCT-1R1 <:FUNCT-3K14 f |RELAT-1K8 A,g :>"
sorry

mtheorem funcop_1_th_6:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds  for A be setHIDDENM2 holds (<:FUNCT-3K14 f,g :>)|RELAT-1K8 A =FUNCT-1R1 <:FUNCT-3K14 f,g |RELAT-1K8 A :>"
sorry

mdef funcop_1_def_2 (" _ -->FUNCOP-1K2  _ " [116,116]116 ) where
  mlet "A be setHIDDENM2", "z be objectHIDDENM1"
"func A -->FUNCOP-1K2 z \<rightarrow> setHIDDENM2 equals
  [:ZFMISC-1K2 A,{TARSKIK1 z} :]"
proof-
  (*coherence*)
    show "[:ZFMISC-1K2 A,{TARSKIK1 z} :] be setHIDDENM2"
       sorry
qed "sorry"

mtheorem funcop_1_cl_1:
  mlet "A be setHIDDENM2", "z be objectHIDDENM1"
"cluster A -->FUNCOP-1K2 z as-term-is Function-likeFUNCT-1V1\<bar>Relation-likeRELAT-1V1"
proof
(*coherence*)
  show "A -->FUNCOP-1K2 z be Function-likeFUNCT-1V1\<bar>Relation-likeRELAT-1V1"
sorry
qed "sorry"

reserve x, z for "objectHIDDENM1"
mtheorem funcop_1_th_7:
" for A be setHIDDENM2 holds  for x be objectHIDDENM1 holds  for z be objectHIDDENM1 holds x inHIDDENR3 A implies (A -->FUNCOP-1K2 z).FUNCT-1K1 x =HIDDENR1 z"
sorry

mtheorem funcop_1_th_8:
" for A be setHIDDENM2 holds  for x be objectHIDDENM1 holds A <>HIDDENR2 {}XBOOLE-0K1 implies rngFUNCT-1K2 (A -->FUNCOP-1K2 x) =XBOOLE-0R4 {TARSKIK1 x}"
  using relat_1_th_160 sorry

mtheorem funcop_1_th_9:
" for f be FunctionFUNCT-1M1 holds  for x be objectHIDDENM1 holds rngFUNCT-1K2 f =XBOOLE-0R4 {TARSKIK1 x} implies f =FUNCT-1R1 domRELAT-1K1 f -->FUNCOP-1K2 x"
sorry

mtheorem funcop_1_cl_2:
  mlet "x be objectHIDDENM1"
"cluster {}XBOOLE-0K1 -->FUNCOP-1K2 x as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "{}XBOOLE-0K1 -->FUNCOP-1K2 x be emptyXBOOLE-0V1"
    using zfmisc_1_th_90 sorry
qed "sorry"

mtheorem funcop_1_cl_3:
  mlet "x be objectHIDDENM1", "A be emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster A -->FUNCOP-1K2 x as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "A -->FUNCOP-1K2 x be emptyXBOOLE-0V1"
     sorry
qed "sorry"

mtheorem funcop_1_cl_4:
  mlet "x be objectHIDDENM1", "A be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster A -->FUNCOP-1K2 x as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "A -->FUNCOP-1K2 x be  non emptyXBOOLE-0V1"
     sorry
qed "sorry"

mtheorem funcop_1_th_10:
" for x be objectHIDDENM1 holds domRELAT-1K1 ({}XBOOLE-0K1 -->FUNCOP-1K2 x) =FUNCT-1R1 {}XBOOLE-0K1 & rngFUNCT-1K2 ({}XBOOLE-0K1 -->FUNCOP-1K2 x) =FUNCT-1R1 {}XBOOLE-0K1"
   sorry

mtheorem funcop_1_th_11:
" for f be FunctionFUNCT-1M1 holds  for x be objectHIDDENM1 holds ( for z be objectHIDDENM1 holds z inHIDDENR3 domRELAT-1K1 f implies f .FUNCT-1K1 z =HIDDENR1 x) implies f =FUNCT-1R1 domRELAT-1K1 f -->FUNCOP-1K2 x"
sorry

mtheorem funcop_1_th_12:
" for A be setHIDDENM2 holds  for B be setHIDDENM2 holds  for x be objectHIDDENM1 holds (A -->FUNCOP-1K2 x)|RELAT-1K8 B =FUNCT-1R1 A /\\XBOOLE-0K3 B -->FUNCOP-1K2 x"
sorry

mtheorem funcop_1_th_13:
" for A be setHIDDENM2 holds  for x be objectHIDDENM1 holds domRELAT-1K1 (A -->FUNCOP-1K2 x) =XBOOLE-0R4 A & rngFUNCT-1K2 (A -->FUNCOP-1K2 x) c=TARSKIR1 {TARSKIK1 x}"
sorry

mtheorem funcop_1_th_14:
" for A be setHIDDENM2 holds  for B be setHIDDENM2 holds  for x be objectHIDDENM1 holds x inHIDDENR3 B implies (A -->FUNCOP-1K2 x)\<inverse>FUNCT-1K6 B =XBOOLE-0R4 A"
sorry

mtheorem funcop_1_th_15:
" for A be setHIDDENM2 holds  for x be objectHIDDENM1 holds (A -->FUNCOP-1K2 x)\<inverse>FUNCT-1K6 {TARSKIK1 x} =XBOOLE-0R4 A"
sorry

mtheorem funcop_1_th_16:
" for A be setHIDDENM2 holds  for B be setHIDDENM2 holds  for x be objectHIDDENM1 holds  not x inHIDDENR3 B implies (A -->FUNCOP-1K2 x)\<inverse>FUNCT-1K6 B =XBOOLE-0R4 {}XBOOLE-0K1"
sorry

mtheorem funcop_1_th_17:
" for h be FunctionFUNCT-1M1 holds  for A be setHIDDENM2 holds  for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 h implies h *FUNCT-1K3 (A -->FUNCOP-1K2 x) =FUNCT-1R1 A -->FUNCOP-1K2 h .FUNCT-1K1 x"
sorry

mtheorem funcop_1_th_18:
" for h be FunctionFUNCT-1M1 holds  for A be setHIDDENM2 holds  for x be objectHIDDENM1 holds A <>HIDDENR2 {}XBOOLE-0K1 & x inHIDDENR3 domRELAT-1K1 h implies domRELAT-1K1 (h *FUNCT-1K3 (A -->FUNCOP-1K2 x)) <>HIDDENR2 {}XBOOLE-0K1"
sorry

mtheorem funcop_1_th_19:
" for h be FunctionFUNCT-1M1 holds  for A be setHIDDENM2 holds  for x be objectHIDDENM1 holds (A -->FUNCOP-1K2 x)*FUNCT-1K3 h =FUNCT-1R1 h \<inverse>FUNCT-1K6 A -->FUNCOP-1K2 x"
sorry

mtheorem funcop_1_th_20:
" for A be setHIDDENM2 holds  for y be setHIDDENM2 holds  for x be objectHIDDENM1 holds (A -->FUNCOP-1K2 [TARSKIK4 x,y ])~FUNCOP-1K1 =FUNCT-1R1 A -->FUNCOP-1K2 [TARSKIK4 y,x ]"
sorry

mdef funcop_1_def_3 (" _ .:FUNCOP-1K3'( _ , _ ')" [200,0,0]200 ) where
  mlet "F be FunctionFUNCT-1M1", "f be FunctionFUNCT-1M1", "g be FunctionFUNCT-1M1"
"func F .:FUNCOP-1K3(f,g) \<rightarrow> setHIDDENM2 equals
  F *FUNCT-1K3 (<:FUNCT-3K14 f,g :>)"
proof-
  (*coherence*)
    show "F *FUNCT-1K3 (<:FUNCT-3K14 f,g :>) be setHIDDENM2"
       sorry
qed "sorry"

mtheorem funcop_1_cl_5:
  mlet "F be FunctionFUNCT-1M1", "f be FunctionFUNCT-1M1", "g be FunctionFUNCT-1M1"
"cluster F .:FUNCOP-1K3(f,g) as-term-is Function-likeFUNCT-1V1\<bar>Relation-likeRELAT-1V1"
proof
(*coherence*)
  show "F .:FUNCOP-1K3(f,g) be Function-likeFUNCT-1V1\<bar>Relation-likeRELAT-1V1"
     sorry
qed "sorry"

mlemma funcop_1_lm_1:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds  for F be FunctionFUNCT-1M1 holds  for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 (F *FUNCT-1K3 (<:FUNCT-3K14 f,g :>)) implies (F *FUNCT-1K3 (<:FUNCT-3K14 f,g :>)).FUNCT-1K1 x =XBOOLE-0R4 F .BINOP-1K1(f .FUNCT-1K1 x,g .FUNCT-1K1 x)"
sorry

mtheorem funcop_1_th_21:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds  for F be FunctionFUNCT-1M1 holds  for h be FunctionFUNCT-1M1 holds domRELAT-1K1 h =XBOOLE-0R4 domRELAT-1K1 (F .:FUNCOP-1K3(f,g)) & ( for z be setHIDDENM2 holds z inTARSKIR2 domRELAT-1K1 (F .:FUNCOP-1K3(f,g)) implies h .FUNCT-1K1 z =XBOOLE-0R4 F .BINOP-1K1(f .FUNCT-1K1 z,g .FUNCT-1K1 z)) implies h =FUNCT-1R1 F .:FUNCOP-1K3(f,g)"
sorry

mtheorem funcop_1_th_22:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds  for F be FunctionFUNCT-1M1 holds  for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 (F .:FUNCOP-1K3(f,g)) implies (F .:FUNCOP-1K3(f,g)).FUNCT-1K1 x =XBOOLE-0R4 F .BINOP-1K1(f .FUNCT-1K1 x,g .FUNCT-1K1 x)"
  using funcop_1_lm_1 sorry

mtheorem funcop_1_th_23:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds  for h be FunctionFUNCT-1M1 holds  for A be setHIDDENM2 holds  for F be FunctionFUNCT-1M1 holds f |RELAT-1K8 A =FUNCT-1R1 g |RELAT-1K8 A implies (F .:FUNCOP-1K3(f,h))|RELAT-1K8 A =FUNCT-1R1 (F .:FUNCOP-1K3(g,h))|RELAT-1K8 A"
sorry

mtheorem funcop_1_th_24:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds  for h be FunctionFUNCT-1M1 holds  for A be setHIDDENM2 holds  for F be FunctionFUNCT-1M1 holds f |RELAT-1K8 A =FUNCT-1R1 g |RELAT-1K8 A implies (F .:FUNCOP-1K3(h,f))|RELAT-1K8 A =FUNCT-1R1 (F .:FUNCOP-1K3(h,g))|RELAT-1K8 A"
sorry

mtheorem funcop_1_th_25:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds  for h be FunctionFUNCT-1M1 holds  for F be FunctionFUNCT-1M1 holds F .:FUNCOP-1K3(f,g) *FUNCT-1K3 h =FUNCT-1R1 F .:FUNCOP-1K3(f *FUNCT-1K3 h,g *FUNCT-1K3 h)"
sorry

mdef funcop_1_def_4 (" _ [:]FUNCOP-1K4'( _ , _ ')" [180,0,0]180 ) where
  mlet "F be FunctionFUNCT-1M1", "f be FunctionFUNCT-1M1", "x be objectHIDDENM1"
"func F [:]FUNCOP-1K4(f,x) \<rightarrow> setHIDDENM2 equals
  F *FUNCT-1K3 (<:FUNCT-3K14 f,domRELAT-1K1 f -->FUNCOP-1K2 x :>)"
proof-
  (*coherence*)
    show "F *FUNCT-1K3 (<:FUNCT-3K14 f,domRELAT-1K1 f -->FUNCOP-1K2 x :>) be setHIDDENM2"
       sorry
qed "sorry"

mtheorem funcop_1_cl_6:
  mlet "F be FunctionFUNCT-1M1", "f be FunctionFUNCT-1M1", "x be objectHIDDENM1"
"cluster F [:]FUNCOP-1K4(f,x) as-term-is Function-likeFUNCT-1V1\<bar>Relation-likeRELAT-1V1"
proof
(*coherence*)
  show "F [:]FUNCOP-1K4(f,x) be Function-likeFUNCT-1V1\<bar>Relation-likeRELAT-1V1"
     sorry
qed "sorry"

mtheorem funcop_1_th_26:
" for f be FunctionFUNCT-1M1 holds  for F be FunctionFUNCT-1M1 holds  for x be objectHIDDENM1 holds F [:]FUNCOP-1K4(f,x) =FUNCT-1R1 F .:FUNCOP-1K3(f,domRELAT-1K1 f -->FUNCOP-1K2 x)"
   sorry

mtheorem funcop_1_th_27:
" for f be FunctionFUNCT-1M1 holds  for F be FunctionFUNCT-1M1 holds  for x be objectHIDDENM1 holds  for z be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 (F [:]FUNCOP-1K4(f,z)) implies (F [:]FUNCOP-1K4(f,z)).FUNCT-1K1 x =XBOOLE-0R4 F .BINOP-1K1(f .FUNCT-1K1 x,z)"
sorry

mtheorem funcop_1_th_28:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds  for A be setHIDDENM2 holds  for F be FunctionFUNCT-1M1 holds  for x be objectHIDDENM1 holds f |RELAT-1K8 A =FUNCT-1R1 g |RELAT-1K8 A implies (F [:]FUNCOP-1K4(f,x))|RELAT-1K8 A =FUNCT-1R1 (F [:]FUNCOP-1K4(g,x))|RELAT-1K8 A"
sorry

mtheorem funcop_1_th_29:
" for f be FunctionFUNCT-1M1 holds  for h be FunctionFUNCT-1M1 holds  for F be FunctionFUNCT-1M1 holds  for x be objectHIDDENM1 holds F [:]FUNCOP-1K4(f,x) *FUNCT-1K3 h =FUNCT-1R1 F [:]FUNCOP-1K4(f *FUNCT-1K3 h,x)"
sorry

mtheorem funcop_1_th_30:
" for f be FunctionFUNCT-1M1 holds  for A be setHIDDENM2 holds  for F be FunctionFUNCT-1M1 holds  for x be objectHIDDENM1 holds F [:]FUNCOP-1K4(f,x) *FUNCT-1K3 idPARTFUN1K6 A =FUNCT-1R1 F [:]FUNCOP-1K4(f |RELAT-1K8 A,x)"
sorry

mdef funcop_1_def_5 (" _ [;]FUNCOP-1K5'( _ , _ ')" [180,0,0]180 ) where
  mlet "F be FunctionFUNCT-1M1", "x be objectHIDDENM1", "g be FunctionFUNCT-1M1"
"func F [;]FUNCOP-1K5(x,g) \<rightarrow> setHIDDENM2 equals
  F *FUNCT-1K3 (<:FUNCT-3K14 domRELAT-1K1 g -->FUNCOP-1K2 x,g :>)"
proof-
  (*coherence*)
    show "F *FUNCT-1K3 (<:FUNCT-3K14 domRELAT-1K1 g -->FUNCOP-1K2 x,g :>) be setHIDDENM2"
       sorry
qed "sorry"

mtheorem funcop_1_cl_7:
  mlet "F be FunctionFUNCT-1M1", "x be objectHIDDENM1", "g be FunctionFUNCT-1M1"
"cluster F [;]FUNCOP-1K5(x,g) as-term-is Function-likeFUNCT-1V1\<bar>Relation-likeRELAT-1V1"
proof
(*coherence*)
  show "F [;]FUNCOP-1K5(x,g) be Function-likeFUNCT-1V1\<bar>Relation-likeRELAT-1V1"
     sorry
qed "sorry"

mtheorem funcop_1_th_31:
" for g be FunctionFUNCT-1M1 holds  for F be FunctionFUNCT-1M1 holds  for x be objectHIDDENM1 holds F [;]FUNCOP-1K5(x,g) =FUNCT-1R1 F .:FUNCOP-1K3(domRELAT-1K1 g -->FUNCOP-1K2 x,g)"
   sorry

mtheorem funcop_1_th_32:
" for f be FunctionFUNCT-1M1 holds  for F be FunctionFUNCT-1M1 holds  for x be objectHIDDENM1 holds  for z be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 (F [;]FUNCOP-1K5(z,f)) implies (F [;]FUNCOP-1K5(z,f)).FUNCT-1K1 x =XBOOLE-0R4 F .BINOP-1K1(z,f .FUNCT-1K1 x)"
sorry

mtheorem funcop_1_th_33:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds  for A be setHIDDENM2 holds  for F be FunctionFUNCT-1M1 holds  for x be objectHIDDENM1 holds f |RELAT-1K8 A =FUNCT-1R1 g |RELAT-1K8 A implies (F [;]FUNCOP-1K5(x,f))|RELAT-1K8 A =FUNCT-1R1 (F [;]FUNCOP-1K5(x,g))|RELAT-1K8 A"
sorry

mtheorem funcop_1_th_34:
" for f be FunctionFUNCT-1M1 holds  for h be FunctionFUNCT-1M1 holds  for F be FunctionFUNCT-1M1 holds  for x be objectHIDDENM1 holds F [;]FUNCOP-1K5(x,f) *FUNCT-1K3 h =FUNCT-1R1 F [;]FUNCOP-1K5(x,f *FUNCT-1K3 h)"
sorry

mtheorem funcop_1_th_35:
" for f be FunctionFUNCT-1M1 holds  for A be setHIDDENM2 holds  for F be FunctionFUNCT-1M1 holds  for x be objectHIDDENM1 holds F [;]FUNCOP-1K5(x,f) *FUNCT-1K3 idPARTFUN1K6 A =FUNCT-1R1 F [;]FUNCOP-1K5(x,f |RELAT-1K8 A)"
sorry

reserve X for " non emptyXBOOLE-0V1\<bar>setHIDDENM2"
reserve Y for "setHIDDENM2"
reserve F for "BinOpBINOP-1M2-of X"
reserve f, g, h for "FunctionFUNCT-2M1-of(Y,X)"
mtheorem funcop_1_th_36:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for Y be setHIDDENM2 holds  for F be BinOpBINOP-1M2-of X holds  for f be FunctionFUNCT-2M1-of(Y,X) holds  for g be FunctionFUNCT-2M1-of(Y,X) holds F .:FUNCOP-1K3(f,g) be FunctionFUNCT-2M1-of(Y,X)"
sorry

syntax FUNCOP_1K6 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ .:FUNCOP-1K6\<^bsub>'( _ , _ ')\<^esub>'( _ , _ ')" [200,0,0,0,0]200)
translations "F .:FUNCOP-1K6\<^bsub>(X,Z)\<^esub>(f,g)" \<rightharpoonup> "F .:FUNCOP-1K3(f,g)"

mtheorem funcop_1_add_1:
  mlet "X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "Z be setHIDDENM2", "F be BinOpBINOP-1M2-of X", "f be FunctionFUNCT-2M1-of(Z,X)", "g be FunctionFUNCT-2M1-of(Z,X)"
"cluster F .:FUNCOP-1K3(f,g) as-term-is FunctionFUNCT-2M1-of(Z,X)"
proof
(*coherence*)
  show "F .:FUNCOP-1K3(f,g) be FunctionFUNCT-2M1-of(Z,X)"
    using funcop_1_th_36 sorry
qed "sorry"

reserve Y for " non emptyXBOOLE-0V1\<bar>setHIDDENM2"
reserve F for "BinOpBINOP-1M2-of X"
reserve f, g, h for "FunctionFUNCT-2M1-of(Y,X)"
reserve x, x1, x2 for "ElementSUBSET-1M1-of X"
mtheorem funcop_1_th_37:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for Y be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for F be BinOpBINOP-1M2-of X holds  for f be FunctionFUNCT-2M1-of(Y,X) holds  for g be FunctionFUNCT-2M1-of(Y,X) holds  for z be ElementSUBSET-1M1-of Y holds (F .:FUNCOP-1K6\<^bsub>(X,Y)\<^esub>(f,g)).FUNCT-2K3\<^bsub>(Y,X)\<^esub> z =XBOOLE-0R4 F .BINOP-1K4\<^bsub>(X)\<^esub>(f .FUNCT-2K3\<^bsub>(Y,X)\<^esub> z,g .FUNCT-2K3\<^bsub>(Y,X)\<^esub> z)"
sorry

mtheorem funcop_1_th_38:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for Y be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for F be BinOpBINOP-1M2-of X holds  for f be FunctionFUNCT-2M1-of(Y,X) holds  for g be FunctionFUNCT-2M1-of(Y,X) holds  for h be FunctionFUNCT-2M1-of(Y,X) holds ( for z be ElementSUBSET-1M1-of Y holds h .FUNCT-2K3\<^bsub>(Y,X)\<^esub> z =XBOOLE-0R4 F .BINOP-1K4\<^bsub>(X)\<^esub>(f .FUNCT-2K3\<^bsub>(Y,X)\<^esub> z,g .FUNCT-2K3\<^bsub>(Y,X)\<^esub> z)) implies h =FUNCT-2R2\<^bsub>(Y,X)\<^esub> F .:FUNCOP-1K6\<^bsub>(X,Y)\<^esub>(f,g)"
sorry

mtheorem funcop_1_th_39:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for Y be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for F be BinOpBINOP-1M2-of X holds  for f be FunctionFUNCT-2M1-of(Y,X) holds  for g be FunctionFUNCT-2M1-of(X,X) holds F .:FUNCOP-1K6\<^bsub>(X,X)\<^esub>(idPARTFUN1K6 X,g) *PARTFUN1K1\<^bsub>(Y,X,X,X)\<^esub> f =FUNCT-2R2\<^bsub>(Y,X)\<^esub> F .:FUNCOP-1K6\<^bsub>(X,Y)\<^esub>(f,g *PARTFUN1K1\<^bsub>(Y,X,X,X)\<^esub> f)"
sorry

mtheorem funcop_1_th_40:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for Y be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for F be BinOpBINOP-1M2-of X holds  for f be FunctionFUNCT-2M1-of(Y,X) holds  for g be FunctionFUNCT-2M1-of(X,X) holds F .:FUNCOP-1K6\<^bsub>(X,X)\<^esub>(g,idPARTFUN1K6 X) *PARTFUN1K1\<^bsub>(Y,X,X,X)\<^esub> f =FUNCT-2R2\<^bsub>(Y,X)\<^esub> F .:FUNCOP-1K6\<^bsub>(X,Y)\<^esub>(g *PARTFUN1K1\<^bsub>(Y,X,X,X)\<^esub> f,f)"
sorry

mtheorem funcop_1_th_41:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for Y be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for F be BinOpBINOP-1M2-of X holds  for f be FunctionFUNCT-2M1-of(Y,X) holds F .:FUNCOP-1K6\<^bsub>(X,X)\<^esub>(idPARTFUN1K6 X,idPARTFUN1K6 X) *PARTFUN1K1\<^bsub>(Y,X,X,X)\<^esub> f =FUNCT-2R2\<^bsub>(Y,X)\<^esub> F .:FUNCOP-1K6\<^bsub>(X,Y)\<^esub>(f,f)"
sorry

mtheorem funcop_1_th_42:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for F be BinOpBINOP-1M2-of X holds  for x be ElementSUBSET-1M1-of X holds  for g be FunctionFUNCT-2M1-of(X,X) holds (F .:FUNCOP-1K6\<^bsub>(X,X)\<^esub>(idPARTFUN1K6 X,g)).FUNCT-2K3\<^bsub>(X,X)\<^esub> x =XBOOLE-0R4 F .BINOP-1K4\<^bsub>(X)\<^esub>(x,g .FUNCT-2K3\<^bsub>(X,X)\<^esub> x)"
sorry

mtheorem funcop_1_th_43:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for F be BinOpBINOP-1M2-of X holds  for x be ElementSUBSET-1M1-of X holds  for g be FunctionFUNCT-2M1-of(X,X) holds (F .:FUNCOP-1K6\<^bsub>(X,X)\<^esub>(g,idPARTFUN1K6 X)).FUNCT-2K3\<^bsub>(X,X)\<^esub> x =XBOOLE-0R4 F .BINOP-1K4\<^bsub>(X)\<^esub>(g .FUNCT-2K3\<^bsub>(X,X)\<^esub> x,x)"
sorry

mtheorem funcop_1_th_44:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for F be BinOpBINOP-1M2-of X holds  for x be ElementSUBSET-1M1-of X holds (F .:FUNCOP-1K6\<^bsub>(X,X)\<^esub>(idPARTFUN1K6 X,idPARTFUN1K6 X)).FUNCT-2K3\<^bsub>(X,X)\<^esub> x =XBOOLE-0R4 F .BINOP-1K4\<^bsub>(X)\<^esub>(x,x)"
sorry

mtheorem funcop_1_th_45:
" for A be setHIDDENM2 holds  for B be setHIDDENM2 holds  for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for x be ElementSUBSET-1M1-of X holds x inTARSKIR2 B implies A -->FUNCOP-1K2 x be FunctionFUNCT-2M1-of(A,B)"
sorry

abbreviation(input) FUNCOP_1K7(" _ -->FUNCOP-1K7  _ " [116,116]116) where
  "I -->FUNCOP-1K7 i \<equiv> I -->FUNCOP-1K2 i"

mtheorem funcop_1_add_2:
  mlet "I be setHIDDENM2", "i be objectHIDDENM1"
"cluster I -->FUNCOP-1K2 i as-term-is FunctionFUNCT-2M1-of(I,{TARSKIK1 i})"
proof
(*coherence*)
  show "I -->FUNCOP-1K2 i be FunctionFUNCT-2M1-of(I,{TARSKIK1 i})"
sorry
qed "sorry"

syntax FUNCOP_1K8 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ -->FUNCOP-1K8\<^bsub>'( _ ')\<^esub>  _ " [116,0,116]116)
translations "A -->FUNCOP-1K8\<^bsub>(B)\<^esub> b" \<rightharpoonup> "A -->FUNCOP-1K2 b"

mtheorem funcop_1_add_3:
  mlet "B be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "A be setHIDDENM2", "b be ElementSUBSET-1M1-of B"
"cluster A -->FUNCOP-1K2 b as-term-is FunctionFUNCT-2M1-of(A,B)"
proof
(*coherence*)
  show "A -->FUNCOP-1K2 b be FunctionFUNCT-2M1-of(A,B)"
    using funcop_1_th_45 sorry
qed "sorry"

mtheorem funcop_1_th_46:
" for A be setHIDDENM2 holds  for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for x be ElementSUBSET-1M1-of X holds A -->FUNCOP-1K8\<^bsub>(X)\<^esub> x be FunctionFUNCT-2M1-of(A,X)"
   sorry

reserve Y for "setHIDDENM2"
reserve F for "BinOpBINOP-1M2-of X"
reserve f, g, h for "FunctionFUNCT-2M1-of(Y,X)"
reserve x, x1, x2 for "ElementSUBSET-1M1-of X"
mtheorem funcop_1_th_47:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for Y be setHIDDENM2 holds  for F be BinOpBINOP-1M2-of X holds  for f be FunctionFUNCT-2M1-of(Y,X) holds  for x be ElementSUBSET-1M1-of X holds F [:]FUNCOP-1K4(f,x) be FunctionFUNCT-2M1-of(Y,X)"
sorry

syntax FUNCOP_1K9 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ [:]FUNCOP-1K9\<^bsub>'( _ , _ ')\<^esub>'( _ , _ ')" [180,0,0,0,0]180)
translations "F [:]FUNCOP-1K9\<^bsub>(X,Z)\<^esub>(f,x)" \<rightharpoonup> "F [:]FUNCOP-1K4(f,x)"

mtheorem funcop_1_add_4:
  mlet "X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "Z be setHIDDENM2", "F be BinOpBINOP-1M2-of X", "f be FunctionFUNCT-2M1-of(Z,X)", "x be ElementSUBSET-1M1-of X"
"cluster F [:]FUNCOP-1K4(f,x) as-term-is FunctionFUNCT-2M1-of(Z,X)"
proof
(*coherence*)
  show "F [:]FUNCOP-1K4(f,x) be FunctionFUNCT-2M1-of(Z,X)"
    using funcop_1_th_47 sorry
qed "sorry"

reserve Y for " non emptyXBOOLE-0V1\<bar>setHIDDENM2"
reserve F for "BinOpBINOP-1M2-of X"
reserve f, g, h for "FunctionFUNCT-2M1-of(Y,X)"
reserve x, x1, x2 for "ElementSUBSET-1M1-of X"
mtheorem funcop_1_th_48:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for Y be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for F be BinOpBINOP-1M2-of X holds  for f be FunctionFUNCT-2M1-of(Y,X) holds  for x be ElementSUBSET-1M1-of X holds  for y be ElementSUBSET-1M1-of Y holds (F [:]FUNCOP-1K9\<^bsub>(X,Y)\<^esub>(f,x)).FUNCT-2K3\<^bsub>(Y,X)\<^esub> y =XBOOLE-0R4 F .BINOP-1K4\<^bsub>(X)\<^esub>(f .FUNCT-2K3\<^bsub>(Y,X)\<^esub> y,x)"
sorry

mtheorem funcop_1_th_49:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for Y be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for F be BinOpBINOP-1M2-of X holds  for f be FunctionFUNCT-2M1-of(Y,X) holds  for g be FunctionFUNCT-2M1-of(Y,X) holds  for x be ElementSUBSET-1M1-of X holds ( for y be ElementSUBSET-1M1-of Y holds g .FUNCT-2K3\<^bsub>(Y,X)\<^esub> y =XBOOLE-0R4 F .BINOP-1K4\<^bsub>(X)\<^esub>(f .FUNCT-2K3\<^bsub>(Y,X)\<^esub> y,x)) implies g =FUNCT-2R2\<^bsub>(Y,X)\<^esub> F [:]FUNCOP-1K9\<^bsub>(X,Y)\<^esub>(f,x)"
sorry

mtheorem funcop_1_th_50:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for Y be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for F be BinOpBINOP-1M2-of X holds  for f be FunctionFUNCT-2M1-of(Y,X) holds  for x be ElementSUBSET-1M1-of X holds F [:]FUNCOP-1K9\<^bsub>(X,X)\<^esub>(idPARTFUN1K6 X,x) *PARTFUN1K1\<^bsub>(Y,X,X,X)\<^esub> f =FUNCT-2R2\<^bsub>(Y,X)\<^esub> F [:]FUNCOP-1K9\<^bsub>(X,Y)\<^esub>(f,x)"
sorry

mtheorem funcop_1_th_51:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for F be BinOpBINOP-1M2-of X holds  for x be ElementSUBSET-1M1-of X holds (F [:]FUNCOP-1K9\<^bsub>(X,X)\<^esub>(idPARTFUN1K6 X,x)).FUNCT-2K3\<^bsub>(X,X)\<^esub> x =XBOOLE-0R4 F .BINOP-1K4\<^bsub>(X)\<^esub>(x,x)"
sorry

reserve Y for "setHIDDENM2"
reserve F for "BinOpBINOP-1M2-of X"
reserve f, g, h for "FunctionFUNCT-2M1-of(Y,X)"
reserve x, x1, x2 for "ElementSUBSET-1M1-of X"
mtheorem funcop_1_th_52:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for Y be setHIDDENM2 holds  for F be BinOpBINOP-1M2-of X holds  for g be FunctionFUNCT-2M1-of(Y,X) holds  for x be ElementSUBSET-1M1-of X holds F [;]FUNCOP-1K5(x,g) be FunctionFUNCT-2M1-of(Y,X)"
sorry

syntax FUNCOP_1K10 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ [;]FUNCOP-1K10\<^bsub>'( _ , _ ')\<^esub>'( _ , _ ')" [180,0,0,0,0]180)
translations "F [;]FUNCOP-1K10\<^bsub>(X,Z)\<^esub>(x,g)" \<rightharpoonup> "F [;]FUNCOP-1K5(x,g)"

mtheorem funcop_1_add_5:
  mlet "X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "Z be setHIDDENM2", "F be BinOpBINOP-1M2-of X", "x be ElementSUBSET-1M1-of X", "g be FunctionFUNCT-2M1-of(Z,X)"
"cluster F [;]FUNCOP-1K5(x,g) as-term-is FunctionFUNCT-2M1-of(Z,X)"
proof
(*coherence*)
  show "F [;]FUNCOP-1K5(x,g) be FunctionFUNCT-2M1-of(Z,X)"
    using funcop_1_th_52 sorry
qed "sorry"

reserve Y for " non emptyXBOOLE-0V1\<bar>setHIDDENM2"
reserve F for "BinOpBINOP-1M2-of X"
reserve f, g, h for "FunctionFUNCT-2M1-of(Y,X)"
reserve x, x1, x2 for "ElementSUBSET-1M1-of X"
mtheorem funcop_1_th_53:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for Y be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for F be BinOpBINOP-1M2-of X holds  for f be FunctionFUNCT-2M1-of(Y,X) holds  for x be ElementSUBSET-1M1-of X holds  for y be ElementSUBSET-1M1-of Y holds (F [;]FUNCOP-1K10\<^bsub>(X,Y)\<^esub>(x,f)).FUNCT-2K3\<^bsub>(Y,X)\<^esub> y =XBOOLE-0R4 F .BINOP-1K4\<^bsub>(X)\<^esub>(x,f .FUNCT-2K3\<^bsub>(Y,X)\<^esub> y)"
sorry

mtheorem funcop_1_th_54:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for Y be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for F be BinOpBINOP-1M2-of X holds  for f be FunctionFUNCT-2M1-of(Y,X) holds  for g be FunctionFUNCT-2M1-of(Y,X) holds  for x be ElementSUBSET-1M1-of X holds ( for y be ElementSUBSET-1M1-of Y holds g .FUNCT-2K3\<^bsub>(Y,X)\<^esub> y =XBOOLE-0R4 F .BINOP-1K4\<^bsub>(X)\<^esub>(x,f .FUNCT-2K3\<^bsub>(Y,X)\<^esub> y)) implies g =FUNCT-2R2\<^bsub>(Y,X)\<^esub> F [;]FUNCOP-1K10\<^bsub>(X,Y)\<^esub>(x,f)"
sorry

reserve Y for "setHIDDENM2"
reserve F for "BinOpBINOP-1M2-of X"
reserve f, g, h for "FunctionFUNCT-2M1-of(Y,X)"
reserve x, x1, x2 for "ElementSUBSET-1M1-of X"
mtheorem funcop_1_th_55:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for Y be setHIDDENM2 holds  for F be BinOpBINOP-1M2-of X holds  for f be FunctionFUNCT-2M1-of(Y,X) holds  for x be ElementSUBSET-1M1-of X holds F [;]FUNCOP-1K10\<^bsub>(X,X)\<^esub>(x,idPARTFUN1K6 X) *PARTFUN1K1\<^bsub>(Y,X,X,X)\<^esub> f =FUNCT-2R2\<^bsub>(Y,X)\<^esub> F [;]FUNCOP-1K10\<^bsub>(X,Y)\<^esub>(x,f)"
sorry

mtheorem funcop_1_th_56:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for F be BinOpBINOP-1M2-of X holds  for x be ElementSUBSET-1M1-of X holds (F [;]FUNCOP-1K10\<^bsub>(X,X)\<^esub>(x,idPARTFUN1K6 X)).FUNCT-2K3\<^bsub>(X,X)\<^esub> x =XBOOLE-0R4 F .BINOP-1K4\<^bsub>(X)\<^esub>(x,x)"
sorry

mtheorem funcop_1_th_57:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for Y be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for Z be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(X,[:ZFMISC-1K2 Y,Z :]) holds  for x be ElementSUBSET-1M1-of X holds f ~FUNCOP-1K1 .FUNCT-1K1 x =HIDDENR1 [TARSKIK4 (f .FUNCT-2K3\<^bsub>(X,[:ZFMISC-1K2 Y,Z :])\<^esub> x)`2XTUPLE-0K2,(f .FUNCT-2K3\<^bsub>(X,[:ZFMISC-1K2 Y,Z :])\<^esub> x)`1XTUPLE-0K1 ]"
sorry

syntax FUNCOP_1K11 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" ("rngFUNCOP-1K11\<^bsub>'( _ , _ , _ ')\<^esub>  _ " [0,0,0,228]228)
translations "rngFUNCOP-1K11\<^bsub>(X,Y,Z)\<^esub> f" \<rightharpoonup> "proj2XTUPLE-0K13 f"

mtheorem funcop_1_add_6:
  mlet "X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "Y be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "Z be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "f be FunctionFUNCT-2M1-of(X,[:ZFMISC-1K2 Y,Z :])"
"cluster proj2XTUPLE-0K13 f as-term-is RelationRELSET-1M1-of(Y,Z)"
proof
(*coherence*)
  show "proj2XTUPLE-0K13 f be RelationRELSET-1M1-of(Y,Z)"
    using relat_1_def_19 sorry
qed "sorry"

syntax FUNCOP_1K12 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ ~FUNCOP-1K12\<^bsub>'( _ , _ , _ ')\<^esub>" [228,0,0,0]228)
translations "f ~FUNCOP-1K12\<^bsub>(X,Y,Z)\<^esub>" \<rightharpoonup> "f ~FUNCOP-1K1"

mtheorem funcop_1_add_7:
  mlet "X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "Y be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "Z be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "f be FunctionFUNCT-2M1-of(X,[:ZFMISC-1K2 Y,Z :])"
"cluster f ~FUNCOP-1K1 as-term-is FunctionFUNCT-2M1-of(X,[:ZFMISC-1K2 Z,Y :])"
proof
(*coherence*)
  show "f ~FUNCOP-1K1 be FunctionFUNCT-2M1-of(X,[:ZFMISC-1K2 Z,Y :])"
sorry
qed "sorry"

mtheorem funcop_1_th_58:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for Y be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for Z be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(X,[:ZFMISC-1K2 Y,Z :]) holds rngFUNCOP-1K11\<^bsub>(X,Z,Y)\<^esub> (f ~FUNCOP-1K12\<^bsub>(X,Y,Z)\<^esub>) =RELSET-1R2\<^bsub>(Z,Y)\<^esub> (rngFUNCOP-1K11\<^bsub>(X,Y,Z)\<^esub> f)~RELSET-1K3\<^bsub>(Y,Z)\<^esub>"
sorry

reserve y for "ElementSUBSET-1M1-of Y"
mtheorem funcop_1_th_59:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for Y be setHIDDENM2 holds  for F be BinOpBINOP-1M2-of X holds  for f be FunctionFUNCT-2M1-of(Y,X) holds  for x1 be ElementSUBSET-1M1-of X holds  for x2 be ElementSUBSET-1M1-of X holds F be associativeBINOP-1V2\<^bsub>(X)\<^esub> implies F [:]FUNCOP-1K9\<^bsub>(X,Y)\<^esub>(F [;]FUNCOP-1K10\<^bsub>(X,Y)\<^esub>(x1,f),x2) =FUNCT-2R2\<^bsub>(Y,X)\<^esub> F [;]FUNCOP-1K10\<^bsub>(X,Y)\<^esub>(x1,F [:]FUNCOP-1K9\<^bsub>(X,Y)\<^esub>(f,x2))"
sorry

mtheorem funcop_1_th_60:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for Y be setHIDDENM2 holds  for F be BinOpBINOP-1M2-of X holds  for f be FunctionFUNCT-2M1-of(Y,X) holds  for g be FunctionFUNCT-2M1-of(Y,X) holds  for x be ElementSUBSET-1M1-of X holds F be associativeBINOP-1V2\<^bsub>(X)\<^esub> implies F .:FUNCOP-1K6\<^bsub>(X,Y)\<^esub>(F [:]FUNCOP-1K9\<^bsub>(X,Y)\<^esub>(f,x),g) =FUNCT-2R2\<^bsub>(Y,X)\<^esub> F .:FUNCOP-1K6\<^bsub>(X,Y)\<^esub>(f,F [;]FUNCOP-1K10\<^bsub>(X,Y)\<^esub>(x,g))"
sorry

mtheorem funcop_1_th_61:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for Y be setHIDDENM2 holds  for F be BinOpBINOP-1M2-of X holds  for f be FunctionFUNCT-2M1-of(Y,X) holds  for g be FunctionFUNCT-2M1-of(Y,X) holds  for h be FunctionFUNCT-2M1-of(Y,X) holds F be associativeBINOP-1V2\<^bsub>(X)\<^esub> implies F .:FUNCOP-1K6\<^bsub>(X,Y)\<^esub>(F .:FUNCOP-1K6\<^bsub>(X,Y)\<^esub>(f,g),h) =FUNCT-2R2\<^bsub>(Y,X)\<^esub> F .:FUNCOP-1K6\<^bsub>(X,Y)\<^esub>(f,F .:FUNCOP-1K6\<^bsub>(X,Y)\<^esub>(g,h))"
sorry

mtheorem funcop_1_th_62:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for Y be setHIDDENM2 holds  for F be BinOpBINOP-1M2-of X holds  for f be FunctionFUNCT-2M1-of(Y,X) holds  for x1 be ElementSUBSET-1M1-of X holds  for x2 be ElementSUBSET-1M1-of X holds F be associativeBINOP-1V2\<^bsub>(X)\<^esub> implies F [;]FUNCOP-1K10\<^bsub>(X,Y)\<^esub>(F .BINOP-1K4\<^bsub>(X)\<^esub>(x1,x2),f) =FUNCT-2R2\<^bsub>(Y,X)\<^esub> F [;]FUNCOP-1K10\<^bsub>(X,Y)\<^esub>(x1,F [;]FUNCOP-1K10\<^bsub>(X,Y)\<^esub>(x2,f))"
sorry

mtheorem funcop_1_th_63:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for Y be setHIDDENM2 holds  for F be BinOpBINOP-1M2-of X holds  for f be FunctionFUNCT-2M1-of(Y,X) holds  for x1 be ElementSUBSET-1M1-of X holds  for x2 be ElementSUBSET-1M1-of X holds F be associativeBINOP-1V2\<^bsub>(X)\<^esub> implies F [:]FUNCOP-1K9\<^bsub>(X,Y)\<^esub>(f,F .BINOP-1K4\<^bsub>(X)\<^esub>(x1,x2)) =FUNCT-2R2\<^bsub>(Y,X)\<^esub> F [:]FUNCOP-1K9\<^bsub>(X,Y)\<^esub>(F [:]FUNCOP-1K9\<^bsub>(X,Y)\<^esub>(f,x1),x2)"
sorry

mtheorem funcop_1_th_64:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for Y be setHIDDENM2 holds  for F be BinOpBINOP-1M2-of X holds  for f be FunctionFUNCT-2M1-of(Y,X) holds  for x be ElementSUBSET-1M1-of X holds F be commutativeBINOP-1V1\<^bsub>(X)\<^esub> implies F [;]FUNCOP-1K10\<^bsub>(X,Y)\<^esub>(x,f) =FUNCT-2R2\<^bsub>(Y,X)\<^esub> F [:]FUNCOP-1K9\<^bsub>(X,Y)\<^esub>(f,x)"
sorry

mtheorem funcop_1_th_65:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for Y be setHIDDENM2 holds  for F be BinOpBINOP-1M2-of X holds  for f be FunctionFUNCT-2M1-of(Y,X) holds  for g be FunctionFUNCT-2M1-of(Y,X) holds F be commutativeBINOP-1V1\<^bsub>(X)\<^esub> implies F .:FUNCOP-1K6\<^bsub>(X,Y)\<^esub>(f,g) =FUNCT-2R2\<^bsub>(Y,X)\<^esub> F .:FUNCOP-1K6\<^bsub>(X,Y)\<^esub>(g,f)"
sorry

mtheorem funcop_1_th_66:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for Y be setHIDDENM2 holds  for F be BinOpBINOP-1M2-of X holds  for f be FunctionFUNCT-2M1-of(Y,X) holds F be idempotentBINOP-1V3\<^bsub>(X)\<^esub> implies F .:FUNCOP-1K6\<^bsub>(X,Y)\<^esub>(f,f) =FUNCT-2R2\<^bsub>(Y,X)\<^esub> f"
sorry

reserve Y for " non emptyXBOOLE-0V1\<bar>setHIDDENM2"
reserve F for "BinOpBINOP-1M2-of X"
reserve f for "FunctionFUNCT-2M1-of(Y,X)"
reserve x for "ElementSUBSET-1M1-of X"
reserve y for "ElementSUBSET-1M1-of Y"
mtheorem funcop_1_th_67:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for Y be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for F be BinOpBINOP-1M2-of X holds  for f be FunctionFUNCT-2M1-of(Y,X) holds  for y be ElementSUBSET-1M1-of Y holds F be idempotentBINOP-1V3\<^bsub>(X)\<^esub> implies (F [;]FUNCOP-1K10\<^bsub>(X,Y)\<^esub>(f .FUNCT-2K3\<^bsub>(Y,X)\<^esub> y,f)).FUNCT-2K3\<^bsub>(Y,X)\<^esub> y =XBOOLE-0R4 f .FUNCT-2K3\<^bsub>(Y,X)\<^esub> y"
sorry

mtheorem funcop_1_th_68:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for Y be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for F be BinOpBINOP-1M2-of X holds  for f be FunctionFUNCT-2M1-of(Y,X) holds  for y be ElementSUBSET-1M1-of Y holds F be idempotentBINOP-1V3\<^bsub>(X)\<^esub> implies (F [:]FUNCOP-1K9\<^bsub>(X,Y)\<^esub>(f,f .FUNCT-2K3\<^bsub>(Y,X)\<^esub> y)).FUNCT-2K3\<^bsub>(Y,X)\<^esub> y =XBOOLE-0R4 f .FUNCT-2K3\<^bsub>(Y,X)\<^esub> y"
sorry

mtheorem funcop_1_th_69:
" for F be FunctionFUNCT-1M1 holds  for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds [:ZFMISC-1K2 rngFUNCT-1K2 f,rngFUNCT-1K2 g :] c=RELAT-1R2 domRELAT-1K1 F implies domRELAT-1K1 (F .:FUNCOP-1K3(f,g)) =XBOOLE-0R4 domRELAT-1K1 f /\\XBOOLE-0K3 domRELAT-1K1 g"
sorry

mdef funcop_1_def_6 ("Function-yieldingFUNCOP-1V1" 70 ) where
"attr Function-yieldingFUNCOP-1V1 for FunctionFUNCT-1M1 means
  (\<lambda>IT.  for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 IT implies IT .FUNCT-1K1 x be FunctionFUNCT-1M1)"..

mtheorem funcop_1_cl_8:
"cluster Function-yieldingFUNCOP-1V1 for FunctionFUNCT-1M1"
proof
(*existence*)
  show " ex it be FunctionFUNCT-1M1 st it be Function-yieldingFUNCOP-1V1"
sorry
qed "sorry"

mtheorem funcop_1_cl_9:
  mlet "B be Function-yieldingFUNCOP-1V1\<bar>FunctionFUNCT-1M1", "j be objectHIDDENM1"
"cluster B .FUNCT-1K1 j as-term-is Function-likeFUNCT-1V1\<bar>Relation-likeRELAT-1V1"
proof
(*coherence*)
  show "B .FUNCT-1K1 j be Function-likeFUNCT-1V1\<bar>Relation-likeRELAT-1V1"
sorry
qed "sorry"

mtheorem funcop_1_cl_10:
  mlet "F be Function-yieldingFUNCOP-1V1\<bar>FunctionFUNCT-1M1", "f be FunctionFUNCT-1M1"
"cluster F *FUNCT-1K3 f as-term-is Function-yieldingFUNCOP-1V1"
proof
(*coherence*)
  show "F *FUNCT-1K3 f be Function-yieldingFUNCOP-1V1"
sorry
qed "sorry"

mtheorem funcop_1_cl_11:
  mlet "B be setHIDDENM2", "c be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster B -->FUNCOP-1K7 c as-term-is non-emptyFUNCT-1V4"
proof
(*coherence*)
  show "B -->FUNCOP-1K7 c be non-emptyFUNCT-1V4"
sorry
qed "sorry"

mtheorem funcop_1_th_70:
" for z be objectHIDDENM1 holds  for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for Y be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for x be ElementSUBSET-1M1-of X holds  for y be ElementSUBSET-1M1-of Y holds ([:ZFMISC-1K2 X,Y :] -->FUNCOP-1K7 z).BINOP-1K2\<^bsub>(X,Y,{TARSKIK1 z})\<^esub>(x,y) =HIDDENR1 z"
  using funcop_1_th_7 zfmisc_1_th_87 sorry

reserve a, b, c for "setHIDDENM2"
mdef funcop_1_def_7 ("'( _ , _ ').-->FUNCOP-1K13  _ " [0,0,164]164 ) where
  mlet "a be objectHIDDENM1", "b be objectHIDDENM1", "c be objectHIDDENM1"
"func (a,b).-->FUNCOP-1K13 c \<rightarrow> FunctionFUNCT-1M1 equals
  {TARSKIK1 [TARSKIK4 a,b ] } -->FUNCOP-1K7 c"
proof-
  (*coherence*)
    show "{TARSKIK1 [TARSKIK4 a,b ] } -->FUNCOP-1K7 c be FunctionFUNCT-1M1"
       sorry
qed "sorry"

mtheorem funcop_1_th_71:
" for a be objectHIDDENM1 holds  for b be objectHIDDENM1 holds  for c be objectHIDDENM1 holds ((a,b).-->FUNCOP-1K13 c).BINOP-1K1(a,b) =HIDDENR1 c"
sorry

mdef funcop_1_def_8 ("IFEQFUNCOP-1K14'( _ , _ , _ , _ ')" [0,0,0,0]164 ) where
  mlet "x be objectHIDDENM1", "y be objectHIDDENM1", "a be objectHIDDENM1", "b be objectHIDDENM1"
"func IFEQFUNCOP-1K14(x,y,a,b) \<rightarrow> objectHIDDENM1 equals
  a if x =HIDDENR1 y otherwise b"
proof-
  (*coherence*)
    show "(x =HIDDENR1 y implies a be objectHIDDENM1) & ( not x =HIDDENR1 y implies b be objectHIDDENM1)"
       sorry
  (*consistency*)
    show " for it be objectHIDDENM1 holds  True "
       sorry
qed "sorry"

abbreviation(input) FUNCOP_1K15("IFEQFUNCOP-1K15'( _ , _ , _ , _ ')" [0,0,0,0]164) where
  "IFEQFUNCOP-1K15(x,y,a,b) \<equiv> IFEQFUNCOP-1K14(x,y,a,b)"

mtheorem funcop_1_add_8:
  mlet "x be objectHIDDENM1", "y be objectHIDDENM1", "a be setHIDDENM2", "b be setHIDDENM2"
"cluster IFEQFUNCOP-1K14(x,y,a,b) as-term-is setHIDDENM2"
proof
(*coherence*)
  show "IFEQFUNCOP-1K14(x,y,a,b) be setHIDDENM2"
sorry
qed "sorry"

syntax FUNCOP_1K16 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" ("IFEQFUNCOP-1K16\<^bsub>'( _ ')\<^esub>'( _ , _ , _ , _ ')" [0,0,0,0,0]164)
translations "IFEQFUNCOP-1K16\<^bsub>(D)\<^esub>(x,y,a,b)" \<rightharpoonup> "IFEQFUNCOP-1K14(x,y,a,b)"

mtheorem funcop_1_add_9:
  mlet "D be setHIDDENM2", "x be objectHIDDENM1", "y be objectHIDDENM1", "a be ElementSUBSET-1M1-of D", "b be ElementSUBSET-1M1-of D"
"cluster IFEQFUNCOP-1K14(x,y,a,b) as-term-is ElementSUBSET-1M1-of D"
proof
(*coherence*)
  show "IFEQFUNCOP-1K14(x,y,a,b) be ElementSUBSET-1M1-of D"
sorry
qed "sorry"

mdef funcop_1_def_9 (" _ .-->FUNCOP-1K17  _ " [164,164]164 ) where
  mlet "x be objectHIDDENM1", "y be objectHIDDENM1"
"func x .-->FUNCOP-1K17 y \<rightarrow> setHIDDENM2 equals
  {TARSKIK1 x} -->FUNCOP-1K7 y"
proof-
  (*coherence*)
    show "{TARSKIK1 x} -->FUNCOP-1K7 y be setHIDDENM2"
       sorry
qed "sorry"

mtheorem funcop_1_cl_12:
  mlet "x be objectHIDDENM1", "y be objectHIDDENM1"
"cluster x .-->FUNCOP-1K17 y as-term-is Function-likeFUNCT-1V1\<bar>Relation-likeRELAT-1V1"
proof
(*coherence*)
  show "x .-->FUNCOP-1K17 y be Function-likeFUNCT-1V1\<bar>Relation-likeRELAT-1V1"
     sorry
qed "sorry"

mtheorem funcop_1_cl_13:
  mlet "x be objectHIDDENM1", "y be objectHIDDENM1"
"cluster x .-->FUNCOP-1K17 y as-term-is one-to-oneFUNCT-1V2"
proof
(*coherence*)
  show "x .-->FUNCOP-1K17 y be one-to-oneFUNCT-1V2"
sorry
qed "sorry"

mtheorem funcop_1_th_72:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds (x .-->FUNCOP-1K17 y).FUNCT-1K1 x =HIDDENR1 y"
sorry

mtheorem funcop_1_th_73:
" for a be objectHIDDENM1 holds  for b be objectHIDDENM1 holds  for f be FunctionFUNCT-1M1 holds a .-->FUNCOP-1K17 b c=RELAT-1R2 f iff a inHIDDENR3 domRELAT-1K1 f & f .FUNCT-1K1 a =HIDDENR1 b"
sorry

abbreviation(input) FUNCOP_1K18("'( _ , _ '):->FUNCOP-1K18  _ " [0,0,228]228) where
  "(o,m):->FUNCOP-1K18 r \<equiv> (o,m).-->FUNCOP-1K13 r"

mlemma funcop_1_lm_2:
" for o be objectHIDDENM1 holds  for m be objectHIDDENM1 holds  for r be objectHIDDENM1 holds (o,m):->FUNCOP-1K18 r be FunctionFUNCT-2M1-of([:ZFMISC-1K2 {TARSKIK1 o},{TARSKIK1 m} :],{TARSKIK1 r})"
sorry

abbreviation(input) FUNCOP_1K19("'( _ , _ '):->FUNCOP-1K19  _ " [0,0,228]228) where
  "(o,m):->FUNCOP-1K19 r \<equiv> (o,m).-->FUNCOP-1K13 r"

mtheorem funcop_1_def_10:
  mlet "o be objectHIDDENM1", "m be objectHIDDENM1", "r be objectHIDDENM1"
"redefine func (o,m):->FUNCOP-1K19 r \<rightarrow> FunctionFUNCT-2M1-of([:ZFMISC-1K2 {TARSKIK1 o},{TARSKIK1 m} :],{TARSKIK1 r}) means
  \<lambda>it.  not  False "
proof
(*compatibility*)
  show " for it be FunctionFUNCT-2M1-of([:ZFMISC-1K2 {TARSKIK1 o},{TARSKIK1 m} :],{TARSKIK1 r}) holds it =HIDDENR1 (o,m):->FUNCOP-1K19 r iff  not  False "
sorry
qed "sorry"

mtheorem funcop_1_add_10:
  mlet "o be objectHIDDENM1", "m be objectHIDDENM1", "r be objectHIDDENM1"
"cluster (o,m).-->FUNCOP-1K13 r as-term-is FunctionFUNCT-2M1-of([:ZFMISC-1K2 {TARSKIK1 o},{TARSKIK1 m} :],{TARSKIK1 r})"
proof
(*coherence*)
  show "(o,m).-->FUNCOP-1K13 r be FunctionFUNCT-2M1-of([:ZFMISC-1K2 {TARSKIK1 o},{TARSKIK1 m} :],{TARSKIK1 r})"
    using funcop_1_lm_2 sorry
qed "sorry"

reserve x, y, z for "objectHIDDENM1"
mtheorem funcop_1_th_74:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 (x .-->FUNCOP-1K17 y)"
sorry

mtheorem funcop_1_th_75:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for z be objectHIDDENM1 holds z inHIDDENR3 domRELAT-1K1 (x .-->FUNCOP-1K17 y) implies z =HIDDENR1 x"
sorry

mtheorem funcop_1_th_76:
" for A be setHIDDENM2 holds  for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  not x inHIDDENR3 A implies (x .-->FUNCOP-1K17 y)|RELAT-1K8 A =FUNCT-1R1 {}XBOOLE-0K1"
sorry

abbreviation(input) FUNCOP_1K20(" _ :->FUNCOP-1K20  _ " [228,228]228) where
  "x :->FUNCOP-1K20 y \<equiv> x .-->FUNCOP-1K17 y"

abbreviation(input) FUNCOP_1K21(" _ :->FUNCOP-1K21  _ " [228,228]228) where
  "m :->FUNCOP-1K21 o \<equiv> m .-->FUNCOP-1K17 o"

mtheorem funcop_1_add_11:
  mlet "m be objectHIDDENM1", "o be objectHIDDENM1"
"cluster m .-->FUNCOP-1K17 o as-term-is FunctionFUNCT-2M1-of({TARSKIK1 m},{TARSKIK1 o})"
proof
(*coherence*)
  show "m .-->FUNCOP-1K17 o be FunctionFUNCT-2M1-of({TARSKIK1 m},{TARSKIK1 o})"
     sorry
qed "sorry"

mtheorem funcop_1_th_77:
" for a be setHIDDENM2 holds  for b be setHIDDENM2 holds  for c be setHIDDENM2 holds  for x be ElementSUBSET-1M1-of {TARSKIK1 a} holds  for y be ElementSUBSET-1M1-of {TARSKIK1 b} holds (a,b):->FUNCOP-1K19 c .BINOP-1K2\<^bsub>({TARSKIK1 a},{TARSKIK1 b},{TARSKIK1 c})\<^esub>(x,y) =XBOOLE-0R4 c"
  using tarski_def_1 sorry

mtheorem funcop_1_cl_14:
  mlet "f be Function-yieldingFUNCOP-1V1\<bar>FunctionFUNCT-1M1", "C be setHIDDENM2"
"cluster f |RELAT-1K8 C as-term-is Function-yieldingFUNCOP-1V1"
proof
(*coherence*)
  show "f |RELAT-1K8 C be Function-yieldingFUNCOP-1V1"
sorry
qed "sorry"

mtheorem funcop_1_cl_15:
  mlet "A be setHIDDENM2", "f be FunctionFUNCT-1M1"
"cluster A -->FUNCOP-1K7 f as-term-is Function-yieldingFUNCOP-1V1"
proof
(*coherence*)
  show "A -->FUNCOP-1K7 f be Function-yieldingFUNCOP-1V1"
     sorry
qed "sorry"

mtheorem funcop_1_cl_16:
  mlet "X be setHIDDENM2", "a be objectHIDDENM1"
"cluster X -->FUNCOP-1K7 a as-term-is constantFUNCT-1V5"
proof
(*coherence*)
  show "X -->FUNCOP-1K7 a be constantFUNCT-1V5"
sorry
qed "sorry"

mtheorem funcop_1_cl_17:
"cluster  non emptyXBOOLE-0V1\<bar>constantFUNCT-1V5 for FunctionFUNCT-1M1"
proof
(*existence*)
  show " ex it be FunctionFUNCT-1M1 st it be  non emptyXBOOLE-0V1\<bar>constantFUNCT-1V5"
sorry
qed "sorry"

mtheorem funcop_1_cl_18:
  mlet "X be setHIDDENM2", "Y be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster constantFUNCT-1V5 for FunctionFUNCT-2M1-of(X,Y)"
proof
(*existence*)
  show " ex it be FunctionFUNCT-2M1-of(X,Y) st it be constantFUNCT-1V5"
sorry
qed "sorry"

mtheorem funcop_1_cl_19:
  mlet "f be constantFUNCT-1V5\<bar>FunctionFUNCT-1M1", "X be setHIDDENM2"
"cluster f |RELAT-1K8 X as-term-is constantFUNCT-1V5"
proof
(*coherence*)
  show "f |RELAT-1K8 X be constantFUNCT-1V5"
sorry
qed "sorry"

mtheorem funcop_1_th_78:
" for f be  non emptyXBOOLE-0V1\<bar>constantFUNCT-1V5\<bar>FunctionFUNCT-1M1 holds  ex y be objectHIDDENM1 st  for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 f implies f .FUNCT-1K1 x =HIDDENR1 y"
sorry

mtheorem funcop_1_th_79:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for x be setHIDDENM2 holds the-value-ofFUNCT-1K7 (X -->FUNCOP-1K7 x) =HIDDENR1 x"
sorry

mtheorem funcop_1_th_80:
" for f be constantFUNCT-1V5\<bar>FunctionFUNCT-1M1 holds f =FUNCT-1R1 domRELAT-1K1 f -->FUNCOP-1K7 the-value-ofFUNCT-1K7 f"
sorry

mtheorem funcop_1_cl_20:
  mlet "X be setHIDDENM2", "Y be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster totalPARTFUN1V1\<^bsub>(X)\<^esub> for PartFuncPARTFUN1M1-of(X,Y)"
proof
(*existence*)
  show " ex it be PartFuncPARTFUN1M1-of(X,Y) st it be totalPARTFUN1V1\<^bsub>(X)\<^esub>"
sorry
qed "sorry"

mtheorem funcop_1_cl_21:
  mlet "I be setHIDDENM2", "A be objectHIDDENM1"
"cluster I -->FUNCOP-1K7 A as-term-is I -definedRELAT-1V4"
proof
(*coherence*)
  show "I -->FUNCOP-1K7 A be I -definedRELAT-1V4"
     sorry
qed "sorry"

mtheorem funcop_1_cl_22:
  mlet "I be objectHIDDENM1", "A be objectHIDDENM1"
"cluster I .-->FUNCOP-1K17 A as-term-is {TARSKIK1 I} -definedRELAT-1V4"
proof
(*coherence*)
  show "I .-->FUNCOP-1K17 A be {TARSKIK1 I} -definedRELAT-1V4"
     sorry
qed "sorry"

mtheorem funcop_1_th_81:
" for A be setHIDDENM2 holds  for B be setHIDDENM2 holds  for x be objectHIDDENM1 holds (A -->FUNCOP-1K7 x).:RELSET-1K7\<^bsub>(A,{TARSKIK1 x})\<^esub> B c=TARSKIR1 {TARSKIK1 x}"
   sorry

mtheorem funcop_1_cl_23:
  mlet "I be setHIDDENM2", "f be FunctionFUNCT-1M1"
"cluster I .-->FUNCOP-1K17 f as-term-is Function-yieldingFUNCOP-1V1"
proof
(*coherence*)
  show "I .-->FUNCOP-1K17 f be Function-yieldingFUNCOP-1V1"
     sorry
qed "sorry"

mtheorem funcop_1_cl_24:
  mlet "I be setHIDDENM2"
"cluster totalPARTFUN1V1\<^bsub>(I)\<^esub> for I -definedRELAT-1V4\<bar>non-emptyFUNCT-1V4\<bar>FunctionFUNCT-1M1"
proof
(*existence*)
  show " ex it be I -definedRELAT-1V4\<bar>non-emptyFUNCT-1V4\<bar>FunctionFUNCT-1M1 st it be totalPARTFUN1V1\<^bsub>(I)\<^esub>"
sorry
qed "sorry"

mtheorem funcop_1_th_82:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds x .-->FUNCOP-1K17 y is-isomorphism-ofWELLORD1R3({TARSKIK1 [TARSKIK4 x,x ] },{TARSKIK1 [TARSKIK4 y,y ] })"
sorry

mtheorem funcop_1_th_83:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds ({TARSKIK1 [TARSKIK4 x,x ] },{TARSKIK1 [TARSKIK4 y,y ] })are-isomorphicWELLORD1R4"
sorry

mtheorem funcop_1_cl_25:
  mlet "I be setHIDDENM2", "A be objectHIDDENM1"
"cluster I -->FUNCOP-1K7 A as-term-is totalPARTFUN1V1\<^bsub>(I)\<^esub> for I -definedRELAT-1V4\<bar>FunctionFUNCT-1M1"
proof
(*coherence*)
  show " for it be I -definedRELAT-1V4\<bar>FunctionFUNCT-1M1 holds it =HIDDENR1 I -->FUNCOP-1K7 A implies it be totalPARTFUN1V1\<^bsub>(I)\<^esub>"
     sorry
qed "sorry"

mtheorem funcop_1_th_84:
" for x be objectHIDDENM1 holds  for f be FunctionFUNCT-1M1 holds x inHIDDENR3 domRELAT-1K1 f implies x .-->FUNCOP-1K17 f .FUNCT-1K1 x c=RELAT-1R2 f"
sorry

mtheorem funcop_1_cl_26:
  mlet "A be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "x be setHIDDENM2", "i be ElementSUBSET-1M1-of A"
"cluster x .-->FUNCOP-1K17 i as-term-is A -valuedRELAT-1V5"
proof
(*coherence*)
  show "x .-->FUNCOP-1K17 i be A -valuedRELAT-1V5"
sorry
qed "sorry"

reserve Y for "setHIDDENM2"
reserve f, g for "FunctionFUNCT-2M1-of(Y,X)"
reserve x for "ElementSUBSET-1M1-of X"
reserve y for "ElementSUBSET-1M1-of Y"
mtheorem funcop_1_th_85:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for F be BinOpBINOP-1M2-of X holds  for Y be setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(Y,X) holds  for g be FunctionFUNCT-2M1-of(Y,X) holds  for x be ElementSUBSET-1M1-of X holds F be associativeBINOP-1V2\<^bsub>(X)\<^esub> implies F .:FUNCOP-1K6\<^bsub>(X,Y)\<^esub>(F [;]FUNCOP-1K10\<^bsub>(X,Y)\<^esub>(x,f),g) =FUNCT-2R2\<^bsub>(Y,X)\<^esub> F [;]FUNCOP-1K10\<^bsub>(X,Y)\<^esub>(x,F .:FUNCOP-1K6\<^bsub>(X,Y)\<^esub>(f,g))"
sorry

mtheorem funcop_1_cl_27:
  mlet "A be setHIDDENM2", "B be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "x be ElementSUBSET-1M1-of B"
"cluster A -->FUNCOP-1K8\<^bsub>(B)\<^esub> x as-term-is B -valuedRELAT-1V5"
proof
(*coherence*)
  show "A -->FUNCOP-1K8\<^bsub>(B)\<^esub> x be B -valuedRELAT-1V5"
     sorry
qed "sorry"

mtheorem funcop_1_cl_28:
  mlet "A be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "x be ElementSUBSET-1M1-of A", "y be objectHIDDENM1"
"cluster x .-->FUNCOP-1K17 y as-term-is A -definedRELAT-1V4"
proof
(*coherence*)
  show "x .-->FUNCOP-1K17 y be A -definedRELAT-1V4"
sorry
qed "sorry"

mtheorem funcop_1_th_86:
" for x be setHIDDENM2 holds  for y be setHIDDENM2 holds  for A be setHIDDENM2 holds x inTARSKIR2 A implies (x .-->FUNCOP-1K17 y)|RELAT-1K8 A =FUNCT-1R1 x .-->FUNCOP-1K17 y"
sorry

mtheorem funcop_1_cl_29:
  mlet "Y be functionalFUNCT-1V6\<bar>setHIDDENM2"
"cluster Y -valuedRELAT-1V5 also-is Function-yieldingFUNCOP-1V1 for FunctionFUNCT-1M1"
proof
(*coherence*)
  show " for it be FunctionFUNCT-1M1 holds it be Y -valuedRELAT-1V5 implies it be Function-yieldingFUNCOP-1V1"
     sorry
qed "sorry"

mdef funcop_1_def_11 ("Relation-yieldingFUNCOP-1V2" 70 ) where
"attr Relation-yieldingFUNCOP-1V2 for FunctionFUNCT-1M1 means
  (\<lambda>IT.  for x be setHIDDENM2 holds x inTARSKIR2 domRELAT-1K1 IT implies IT .FUNCT-1K1 x be RelationRELAT-1M1)"..

mtheorem funcop_1_cl_30:
"cluster Function-yieldingFUNCOP-1V1 also-is Relation-yieldingFUNCOP-1V2 for FunctionFUNCT-1M1"
proof
(*coherence*)
  show " for it be FunctionFUNCT-1M1 holds it be Function-yieldingFUNCOP-1V1 implies it be Relation-yieldingFUNCOP-1V2"
     sorry
qed "sorry"

mtheorem funcop_1_cl_31:
"cluster emptyXBOOLE-0V1 also-is Function-yieldingFUNCOP-1V1 for FunctionFUNCT-1M1"
proof
(*coherence*)
  show " for it be FunctionFUNCT-1M1 holds it be emptyXBOOLE-0V1 implies it be Function-yieldingFUNCOP-1V1"
     sorry
qed "sorry"

mtheorem funcop_1_th_87:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds X -->FUNCOP-1K7 x toleratesPARTFUN1R1 Y -->FUNCOP-1K7 y iff x =HIDDENR1 y or X missesXBOOLE-0R1 Y"
sorry

reserve x, y, z, A for "setHIDDENM2"
mtheorem funcop_1_th_88:
" for x be setHIDDENM2 holds  for y be setHIDDENM2 holds rngFUNCT-1K2 (x .-->FUNCOP-1K17 y) =XBOOLE-0R4 {TARSKIK1 y}"
sorry

mtheorem funcop_1_th_89:
" for x be setHIDDENM2 holds  for y be setHIDDENM2 holds  for z be setHIDDENM2 holds  for A be setHIDDENM2 holds z inTARSKIR2 A implies (A -->FUNCOP-1K7 x)*FUNCT-1K3 (y .-->FUNCOP-1K17 z) =FUNCT-1R1 y .-->FUNCOP-1K17 x"
sorry

mtheorem funcop_1_cl_32:
  mlet "f be Function-yieldingFUNCOP-1V1\<bar>FunctionFUNCT-1M1", "a be objectHIDDENM1", "b be objectHIDDENM1"
"cluster f .BINOP-1K1(a,b) as-term-is Function-likeFUNCT-1V1\<bar>Relation-likeRELAT-1V1"
proof
(*coherence*)
  show "f .BINOP-1K1(a,b) be Function-likeFUNCT-1V1\<bar>Relation-likeRELAT-1V1"
     sorry
qed "sorry"

mtheorem funcop_1_cl_33:
  mlet "Y be setHIDDENM2", "X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "Z be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster note-that Function-yieldingFUNCOP-1V1 for FunctionFUNCT-2M1-of(X,FuncsFUNCT-2K9(Y,Z))"
proof
(*coherence*)
  show " for it be FunctionFUNCT-2M1-of(X,FuncsFUNCT-2K9(Y,Z)) holds it be Function-yieldingFUNCOP-1V1"
     sorry
qed "sorry"

end
