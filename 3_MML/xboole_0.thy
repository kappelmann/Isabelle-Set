theory xboole_0
imports "../2_Mizar/mizar_fraenkel"

begin

reserve X, Y, Z for set
reserve x, y, z for object

theorem xboole_0_sch_1:
  fixes Af0 Pp1 
  assumes
  [ty]: "Af0 be setHIDDENM2"
  shows "ex X be set st for x be object holds x inHIDDENR3 X iff x inHIDDENR3 Af0 & Pp1(x)"
sorry

mdef xboole_0_def_1 ("emptyXBOOLE-0V1" 70 ) where
"attr emptyXBOOLE-0V1 for setHIDDENM2 means

  (\<lambda>X.  not ( ex x be objectHIDDENM1 st x inHIDDENR3 X))"..

mtheorem xboole_0_cl_1:
"cluster emptyXBOOLE-0V1 for setHIDDENM2"
proof
(*existence*)
  show " ex it be setHIDDENM2 st it be emptyXBOOLE-0V1"
sorry
qed "sorry"

mdef xboole_0_def_2 ("{}XBOOLE-0K1" 228 ) where
"func {}XBOOLE-0K1 \<rightarrow> setHIDDENM2 equals

  the emptyXBOOLE-0V1\<bar>setHIDDENM2"
proof-
  (*coherence*)
    show "the emptyXBOOLE-0V1\<bar>setHIDDENM2 be setHIDDENM2"
       sorry
qed "sorry"

mdef xboole_0_def_3 (" _ '\\'/XBOOLE-0K2  _ " [132,132]132 ) where
  mlet "X be setHIDDENM2", "Y be setHIDDENM2"
"func X \\/XBOOLE-0K2 Y \<rightarrow> setHIDDENM2 means

  \<lambda>it.  for x be objectHIDDENM1 holds x inHIDDENR3 it iff x inHIDDENR3 X or x inHIDDENR3 Y"
proof-
  (*existence*)
    show " ex it be setHIDDENM2 st  for x be objectHIDDENM1 holds x inHIDDENR3 it iff x inHIDDENR3 X or x inHIDDENR3 Y"
sorry
  (*uniqueness*)
    show " for it1 be setHIDDENM2 holds  for it2 be setHIDDENM2 holds ( for x be objectHIDDENM1 holds x inHIDDENR3 it1 iff x inHIDDENR3 X or x inHIDDENR3 Y) & ( for x be objectHIDDENM1 holds x inHIDDENR3 it2 iff x inHIDDENR3 X or x inHIDDENR3 Y) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mtheorem XBOOLE_0K2_commutativity:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X \\/XBOOLE-0K2 Y =HIDDENR1 Y \\/XBOOLE-0K2 X"
sorry

mtheorem XBOOLE_0K2_idempotence:
" for Y be setHIDDENM2 holds Y =HIDDENR1 Y \\/XBOOLE-0K2 Y"
sorry

mdef xboole_0_def_4 (" _ '/'\\XBOOLE-0K3  _ " [164,164]164 ) where
  mlet "X be setHIDDENM2", "Y be setHIDDENM2"
"func X /\\XBOOLE-0K3 Y \<rightarrow> setHIDDENM2 means

  \<lambda>it.  for x be objectHIDDENM1 holds x inHIDDENR3 it iff x inHIDDENR3 X & x inHIDDENR3 Y"
proof-
  (*existence*)
    show " ex it be setHIDDENM2 st  for x be objectHIDDENM1 holds x inHIDDENR3 it iff x inHIDDENR3 X & x inHIDDENR3 Y"
sorry
  (*uniqueness*)
    show " for it1 be setHIDDENM2 holds  for it2 be setHIDDENM2 holds ( for x be objectHIDDENM1 holds x inHIDDENR3 it1 iff x inHIDDENR3 X & x inHIDDENR3 Y) & ( for x be objectHIDDENM1 holds x inHIDDENR3 it2 iff x inHIDDENR3 X & x inHIDDENR3 Y) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mtheorem XBOOLE_0K3_commutativity:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X /\\XBOOLE-0K3 Y =HIDDENR1 Y /\\XBOOLE-0K3 X"
sorry

mtheorem XBOOLE_0K3_idempotence:
" for Y be setHIDDENM2 holds Y =HIDDENR1 Y /\\XBOOLE-0K3 Y"
sorry

mdef xboole_0_def_5 (" _ '\\XBOOLE-0K4  _ " [132,132]132 ) where
  mlet "X be setHIDDENM2", "Y be setHIDDENM2"
"func X \\XBOOLE-0K4 Y \<rightarrow> setHIDDENM2 means

  \<lambda>it.  for x be objectHIDDENM1 holds x inHIDDENR3 it iff x inHIDDENR3 X &  not x inHIDDENR3 Y"
proof-
  (*existence*)
    show " ex it be setHIDDENM2 st  for x be objectHIDDENM1 holds x inHIDDENR3 it iff x inHIDDENR3 X &  not x inHIDDENR3 Y"
sorry
  (*uniqueness*)
    show " for it1 be setHIDDENM2 holds  for it2 be setHIDDENM2 holds ( for x be objectHIDDENM1 holds x inHIDDENR3 it1 iff x inHIDDENR3 X &  not x inHIDDENR3 Y) & ( for x be objectHIDDENM1 holds x inHIDDENR3 it2 iff x inHIDDENR3 X &  not x inHIDDENR3 Y) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mdef xboole_0_def_6 (" _ '\\+'\\XBOOLE-0K5  _ " [130,130]130 ) where
  mlet "X be setHIDDENM2", "Y be setHIDDENM2"
"func X \\+\\XBOOLE-0K5 Y \<rightarrow> setHIDDENM2 equals

  (X \\XBOOLE-0K4 Y)\\/XBOOLE-0K2 (Y \\XBOOLE-0K4 X)"
proof-
  (*coherence*)
    show "(X \\XBOOLE-0K4 Y)\\/XBOOLE-0K2 (Y \\XBOOLE-0K4 X) be setHIDDENM2"
       sorry
qed "sorry"

mtheorem XBOOLE_0K5_commutativity:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X \\+\\XBOOLE-0K5 Y =HIDDENR1 Y \\+\\XBOOLE-0K5 X"
sorry

mdef xboole_0_def_7 (" _ missesXBOOLE-0R1  _ " [50,50]50 ) where
  mlet "X be setHIDDENM2", "Y be setHIDDENM2"
"pred X missesXBOOLE-0R1 Y means

  X /\\XBOOLE-0K3 Y =HIDDENR1 {}XBOOLE-0K1"..

mtheorem XBOOLE_0R1_symmetry:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X missesXBOOLE-0R1 Y implies Y missesXBOOLE-0R1 X"
sorry

mdef xboole_0_def_8 (" _ c<XBOOLE-0R2  _ " [50,50]50 ) where
  mlet "X be setHIDDENM2", "Y be setHIDDENM2"
"pred X c<XBOOLE-0R2 Y means

  X c=TARSKIR1 Y & X <>HIDDENR2 Y"..

mtheorem XBOOLE_0R2_irreflexivity:
" for Y be setHIDDENM2 holds  not Y c<XBOOLE-0R2 Y"
sorry

mtheorem XBOOLE_0R2_asymmetry:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X c<XBOOLE-0R2 Y implies  not Y c<XBOOLE-0R2 X"
sorry

mdef xboole_0_def_9 ("'( _ , _ ')are-c=-comparableXBOOLE-0R3" [0,0]50 ) where
  mlet "X be setHIDDENM2", "Y be setHIDDENM2"
"pred (X,Y)are-c=-comparableXBOOLE-0R3 means

  X c=TARSKIR1 Y or Y c=TARSKIR1 X"..

mtheorem XBOOLE_0R3_reflexivity:
" for Y be setHIDDENM2 holds (Y,Y)are-c=-comparableXBOOLE-0R3"
sorry

mtheorem XBOOLE_0R3_symmetry:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds (X,Y)are-c=-comparableXBOOLE-0R3 implies (Y,X)are-c=-comparableXBOOLE-0R3"
sorry

abbreviation(input) XBOOLE_0R4(" _ =XBOOLE-0R4  _ " [50,50]50) where
  "X =XBOOLE-0R4 Y \<equiv> X =HIDDENR1 Y"

mtheorem xboole_0_def_10:
  mlet "X be setHIDDENM2", "Y be setHIDDENM2"
"redefine pred X =XBOOLE-0R4 Y means

  X c=TARSKIR1 Y & Y c=TARSKIR1 X"
proof
(*compatibility*)
  show "X =XBOOLE-0R4 Y iff X c=TARSKIR1 Y & Y c=TARSKIR1 X"
    using tarski_th_2 sorry
qed "sorry"

syntax XBOOLE_0R5 :: " Set \<Rightarrow>  Set \<Rightarrow> o" (" _ meetsXBOOLE-0R5  _ " [50,50]50)
translations "X meetsXBOOLE-0R5 Y" \<rightharpoonup> " not X missesXBOOLE-0R1 Y"

mtheorem xboole_0_th_1:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for x be objectHIDDENM1 holds x inHIDDENR3 X \\+\\XBOOLE-0K5 Y iff  not (x inHIDDENR3 X iff x inHIDDENR3 Y)"
sorry

mtheorem xboole_0_th_2:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds ( for x be objectHIDDENM1 holds  not x inHIDDENR3 X iff (x inHIDDENR3 Y iff x inHIDDENR3 Z)) implies X =XBOOLE-0R4 Y \\+\\XBOOLE-0K5 Z"
sorry

mtheorem xboole_0_cl_2:
"cluster {}XBOOLE-0K1 as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "{}XBOOLE-0K1 be emptyXBOOLE-0V1"
     sorry
qed "sorry"

mtheorem xboole_0_cl_3:
  mlet "x be objectHIDDENM1"
"cluster {TARSKIK1 x} as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "{TARSKIK1 x} be  non emptyXBOOLE-0V1"
sorry
qed "sorry"

mtheorem xboole_0_cl_4:
  mlet "x be objectHIDDENM1", "y be objectHIDDENM1"
"cluster {TARSKIK2 x,y } as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "{TARSKIK2 x,y } be  non emptyXBOOLE-0V1"
sorry
qed "sorry"

mtheorem xboole_0_cl_5:
"cluster  non emptyXBOOLE-0V1 for setHIDDENM2"
proof
(*existence*)
  show " ex it be setHIDDENM2 st it be  non emptyXBOOLE-0V1"
sorry
qed "sorry"

mtheorem xboole_0_cl_6:
  mlet "D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "X be setHIDDENM2"
"cluster D \\/XBOOLE-0K2 X as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "D \\/XBOOLE-0K2 X be  non emptyXBOOLE-0V1"
sorry
qed "sorry"

mtheorem xboole_0_cl_7:
  mlet "D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "X be setHIDDENM2"
"cluster X \\/XBOOLE-0K2 D as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "X \\/XBOOLE-0K2 D be  non emptyXBOOLE-0V1"
     sorry
qed "sorry"

mlemma xboole_0_lm_1:
" for X be setHIDDENM2 holds X be emptyXBOOLE-0V1 implies X =XBOOLE-0R4 {}XBOOLE-0K1"
sorry

mtheorem xboole_0_th_3:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X meetsXBOOLE-0R5 Y iff ( ex x be objectHIDDENM1 st x inHIDDENR3 X & x inHIDDENR3 Y)"
sorry

mtheorem xboole_0_th_4:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X meetsXBOOLE-0R5 Y iff ( ex x be objectHIDDENM1 st x inHIDDENR3 X /\\XBOOLE-0K3 Y)"
sorry

mtheorem xboole_0_th_5:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for x be objectHIDDENM1 holds X missesXBOOLE-0R1 Y & x inHIDDENR3 X \\/XBOOLE-0K2 Y implies x inHIDDENR3 X &  not x inHIDDENR3 Y or x inHIDDENR3 Y &  not x inHIDDENR3 X"
  using xboole_0_def_3 xboole_0_th_3 sorry

theorem xboole_0_sch_2:
  fixes Xf0 Yf0 Pp1 
  assumes
[ty]: "Xf0 be setHIDDENM2" and
  [ty]: "Yf0 be setHIDDENM2" and
   A1: " for x be objectHIDDENM1 holds x inHIDDENR3 Xf0 iff Pp1(x)" and
   A2: " for x be objectHIDDENM1 holds x inHIDDENR3 Yf0 iff Pp1(x)"
  shows "Xf0 =XBOOLE-0R4 Yf0"
sorry

theorem xboole_0_sch_3:
  fixes Pp1 
  shows " for X1 be setHIDDENM2 holds  for X2 be setHIDDENM2 holds ( for x be objectHIDDENM1 holds x inHIDDENR3 X1 iff Pp1(x)) & ( for x be objectHIDDENM1 holds x inHIDDENR3 X2 iff Pp1(x)) implies X1 =XBOOLE-0R4 X2"
sorry

(*begin*)
mtheorem xboole_0_th_6:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X c<XBOOLE-0R2 Y implies ( ex x be objectHIDDENM1 st x inHIDDENR3 Y &  not x inHIDDENR3 X)"
  using xboole_0_def_8 tarski_def_3 sorry

mtheorem xboole_0_th_7:
" for X be setHIDDENM2 holds X <>HIDDENR2 {}XBOOLE-0K1 implies ( ex x be objectHIDDENM1 st x inHIDDENR3 X)"
  using xboole_0_def_1 xboole_0_lm_1 sorry

mtheorem xboole_0_th_8:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X c<XBOOLE-0R2 Y implies ( ex x be objectHIDDENM1 st x inHIDDENR3 Y & X c=TARSKIR1 Y \\XBOOLE-0K4 {TARSKIK1 x})"
sorry

syntax XBOOLE_0R6 :: " Set \<Rightarrow>  Set \<Rightarrow> o" (" _ c'/=XBOOLE-0R6  _ " [50,50]50)
translations "x c/=XBOOLE-0R6 y" \<rightharpoonup> " not x c=TARSKIR1 y"

syntax XBOOLE_0R7 :: " Set \<Rightarrow>  Set \<Rightarrow> o" (" _ ninXBOOLE-0R7  _ " [50,50]50)
translations "x ninXBOOLE-0R7 y" \<rightharpoonup> " not x inHIDDENR3 y"

end
