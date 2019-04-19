theory binop_1
  imports funct_2
begin
(*begin*)
mdef binop_1_def_1 (" _ .BINOP-1K1'( _ , _ ')" [200,0,0]200 ) where
  mlet "f be FunctionFUNCT-1M1", "a be objectHIDDENM1", "b be objectHIDDENM1"
"func f .BINOP-1K1(a,b) \<rightarrow> setHIDDENM2 equals
  f .FUNCT-1K1 [TARSKIK4 a,b ]"
proof-
  (*coherence*)
    show "f .FUNCT-1K1 [TARSKIK4 a,b ] be setHIDDENM2"
       sorry
qed "sorry"

reserve A for "setHIDDENM2"
syntax BINOP_1K2 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ .BINOP-1K2\<^bsub>'( _ , _ , _ ')\<^esub>'( _ , _ ')" [200,0,0,0,0,0]200)
translations "f .BINOP-1K2\<^bsub>(A,B,C)\<^esub>(a,b)" \<rightharpoonup> "f .BINOP-1K1(a,b)"

mtheorem binop_1_add_1:
  mlet "A be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "B be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "C be setHIDDENM2", "f be FunctionFUNCT-2M1-of([:ZFMISC-1K2 A,B :],C)", "a be ElementSUBSET-1M1-of A", "b be ElementSUBSET-1M1-of B"
"cluster f .BINOP-1K1(a,b) as-term-is ElementSUBSET-1M1-of C"
proof
(*coherence*)
  show "f .BINOP-1K1(a,b) be ElementSUBSET-1M1-of C"
sorry
qed "sorry"

reserve X, Y, Z for "setHIDDENM2"
reserve x, x1, x2, y, y1, y2, z, z1, z2 for "objectHIDDENM1"
mtheorem binop_1_th_1:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds  for f1 be FunctionFUNCT-2M1-of([:ZFMISC-1K2 X,Y :],Z) holds  for f2 be FunctionFUNCT-2M1-of([:ZFMISC-1K2 X,Y :],Z) holds ( for x be setHIDDENM2 holds  for y be setHIDDENM2 holds x inTARSKIR2 X & y inTARSKIR2 Y implies f1 .BINOP-1K1(x,y) =XBOOLE-0R4 f2 .BINOP-1K1(x,y)) implies f1 =FUNCT-2R2\<^bsub>([:ZFMISC-1K2 X,Y :],Z)\<^esub> f2"
sorry

mtheorem binop_1_th_2:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds  for f1 be FunctionFUNCT-2M1-of([:ZFMISC-1K2 X,Y :],Z) holds  for f2 be FunctionFUNCT-2M1-of([:ZFMISC-1K2 X,Y :],Z) holds ( for a be ElementSUBSET-1M1-of X holds  for b be ElementSUBSET-1M1-of Y holds f1 .BINOP-1K1(a,b) =XBOOLE-0R4 f2 .BINOP-1K1(a,b)) implies f1 =FUNCT-2R2\<^bsub>([:ZFMISC-1K2 X,Y :],Z)\<^esub> f2"
sorry

syntax BINOP_1M1 :: " Set \<Rightarrow> Ty" ("UnOpBINOP-1M1-of  _ " [70]70)
translations "UnOpBINOP-1M1-of A" \<rightharpoonup> "FunctionFUNCT-2M1-of(A,A)"

syntax BINOP_1M2 :: " Set \<Rightarrow> Ty" ("BinOpBINOP-1M2-of  _ " [70]70)
translations "BinOpBINOP-1M2-of A" \<rightharpoonup> "FunctionFUNCT-2M1-of([:ZFMISC-1K2 A,A :],A)"

reserve u for "UnOpBINOP-1M1-of A"
reserve o, o9 for "BinOpBINOP-1M2-of A"
reserve a, b, c, e, e1, e2 for "ElementSUBSET-1M1-of A"
theorem binop_1_sch_1:
  fixes Xf0 Yf0 Zf0 Pp3 
  assumes
[ty]: "Xf0 be setHIDDENM2" and
  [ty]: "Yf0 be setHIDDENM2" and
  [ty]: "Zf0 be setHIDDENM2" and
   A1: " for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds x inHIDDENR3 Xf0 & y inHIDDENR3 Yf0 implies ( ex z be objectHIDDENM1 st z inHIDDENR3 Zf0 & Pp3(x,y,z))"
  shows " ex f be FunctionFUNCT-2M1-of([:ZFMISC-1K2 Xf0,Yf0 :],Zf0) st  for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds x inHIDDENR3 Xf0 & y inHIDDENR3 Yf0 implies Pp3(x,y,f .BINOP-1K1(x,y))"
sorry

theorem binop_1_sch_2:
  fixes Xf0 Yf0 Zf0 Ff2 
  assumes
[ty]: "Xf0 be setHIDDENM2" and
  [ty]: "Yf0 be setHIDDENM2" and
  [ty]: "Zf0 be setHIDDENM2" and
  [ty_func]: "\<And> x1 x2. x1 be objectHIDDENM1 \<Longrightarrow> x2 be objectHIDDENM1 \<Longrightarrow> Ff2(x1,x2) be objectHIDDENM1" and
   A1: " for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds x inHIDDENR3 Xf0 & y inHIDDENR3 Yf0 implies Ff2(x,y) inHIDDENR3 Zf0"
  shows " ex f be FunctionFUNCT-2M1-of([:ZFMISC-1K2 Xf0,Yf0 :],Zf0) st  for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds x inHIDDENR3 Xf0 & y inHIDDENR3 Yf0 implies f .BINOP-1K1(x,y) =HIDDENR1 Ff2(x,y)"
sorry

theorem binop_1_sch_3:
  fixes Xf0 Yf0 Zf0 Pp3 
  assumes
[ty]: "Xf0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
  [ty]: "Yf0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
  [ty]: "Zf0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
   A1: " for x be ElementSUBSET-1M1-of Xf0 holds  for y be ElementSUBSET-1M1-of Yf0 holds  ex z be ElementSUBSET-1M1-of Zf0 st Pp3(x,y,z)"
  shows " ex f be FunctionFUNCT-2M1-of([:ZFMISC-1K2 Xf0,Yf0 :],Zf0) st  for x be ElementSUBSET-1M1-of Xf0 holds  for y be ElementSUBSET-1M1-of Yf0 holds Pp3(x,y,f .BINOP-1K2\<^bsub>(Xf0,Yf0,Zf0)\<^esub>(x,y))"
sorry

theorem binop_1_sch_4:
  fixes Xf0 Yf0 Zf0 Ff2 
  assumes
[ty]: "Xf0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
  [ty]: "Yf0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
  [ty]: "Zf0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
  [ty_func]: "\<And> x1 x2. x1 be ElementSUBSET-1M1-of Xf0 \<Longrightarrow> x2 be ElementSUBSET-1M1-of Yf0 \<Longrightarrow> Ff2(x1,x2) be ElementSUBSET-1M1-of Zf0"
  shows " ex f be FunctionFUNCT-2M1-of([:ZFMISC-1K2 Xf0,Yf0 :],Zf0) st  for x be ElementSUBSET-1M1-of Xf0 holds  for y be ElementSUBSET-1M1-of Yf0 holds f .BINOP-1K2\<^bsub>(Xf0,Yf0,Zf0)\<^esub>(x,y) =XBOOLE-0R4 Ff2(x,y)"
sorry

mdef binop_1_def_2 ("commutativeBINOP-1V1\<^bsub>'( _ ')\<^esub>" [0]70 ) where
  mlet "A be setHIDDENM2"
"attr commutativeBINOP-1V1\<^bsub>(A)\<^esub> for BinOpBINOP-1M2-of A means
  (\<lambda>o.  for a be ElementSUBSET-1M1-of A holds  for b be ElementSUBSET-1M1-of A holds o .BINOP-1K1(a,b) =XBOOLE-0R4 o .BINOP-1K1(b,a))"..

mdef binop_1_def_3 ("associativeBINOP-1V2\<^bsub>'( _ ')\<^esub>" [0]70 ) where
  mlet "A be setHIDDENM2"
"attr associativeBINOP-1V2\<^bsub>(A)\<^esub> for BinOpBINOP-1M2-of A means
  (\<lambda>o.  for a be ElementSUBSET-1M1-of A holds  for b be ElementSUBSET-1M1-of A holds  for c be ElementSUBSET-1M1-of A holds o .BINOP-1K1(a,o .BINOP-1K1(b,c)) =XBOOLE-0R4 o .BINOP-1K1(o .BINOP-1K1(a,b),c))"..

mdef binop_1_def_4 ("idempotentBINOP-1V3\<^bsub>'( _ ')\<^esub>" [0]70 ) where
  mlet "A be setHIDDENM2"
"attr idempotentBINOP-1V3\<^bsub>(A)\<^esub> for BinOpBINOP-1M2-of A means
  (\<lambda>o.  for a be ElementSUBSET-1M1-of A holds o .BINOP-1K1(a,a) =XBOOLE-0R4 a)"..

mtheorem binop_1_cl_1:
"cluster note-that emptyXBOOLE-0V1\<bar>associativeBINOP-1V2\<^bsub>({}XBOOLE-0K1)\<^esub>\<bar>commutativeBINOP-1V1\<^bsub>({}XBOOLE-0K1)\<^esub> for BinOpBINOP-1M2-of {}XBOOLE-0K1"
proof
(*coherence*)
  show " for it be BinOpBINOP-1M2-of {}XBOOLE-0K1 holds it be emptyXBOOLE-0V1\<bar>associativeBINOP-1V2\<^bsub>({}XBOOLE-0K1)\<^esub>\<bar>commutativeBINOP-1V1\<^bsub>({}XBOOLE-0K1)\<^esub>"
sorry
qed "sorry"

mdef binop_1_def_5 (" _ is-a-left-unity-wrtBINOP-1R1\<^bsub>'( _ ')\<^esub>  _ " [50,0,50]50 ) where
  mlet "A be setHIDDENM2", "e be objectHIDDENM1", "o be BinOpBINOP-1M2-of A"
"pred e is-a-left-unity-wrtBINOP-1R1\<^bsub>(A)\<^esub> o means
   for a be ElementSUBSET-1M1-of A holds o .BINOP-1K1(e,a) =XBOOLE-0R4 a"..

mdef binop_1_def_6 (" _ is-a-right-unity-wrtBINOP-1R2\<^bsub>'( _ ')\<^esub>  _ " [50,0,50]50 ) where
  mlet "A be setHIDDENM2", "e be objectHIDDENM1", "o be BinOpBINOP-1M2-of A"
"pred e is-a-right-unity-wrtBINOP-1R2\<^bsub>(A)\<^esub> o means
   for a be ElementSUBSET-1M1-of A holds o .BINOP-1K1(a,e) =XBOOLE-0R4 a"..

mdef binop_1_def_7 (" _ is-a-unity-wrtBINOP-1R3\<^bsub>'( _ ')\<^esub>  _ " [50,0,50]50 ) where
  mlet "A be setHIDDENM2", "e be objectHIDDENM1", "o be BinOpBINOP-1M2-of A"
"pred e is-a-unity-wrtBINOP-1R3\<^bsub>(A)\<^esub> o means
  e is-a-left-unity-wrtBINOP-1R1\<^bsub>(A)\<^esub> o & e is-a-right-unity-wrtBINOP-1R2\<^bsub>(A)\<^esub> o"..

mtheorem binop_1_th_3:
" for A be setHIDDENM2 holds  for o be BinOpBINOP-1M2-of A holds  for e be ElementSUBSET-1M1-of A holds e is-a-unity-wrtBINOP-1R3\<^bsub>(A)\<^esub> o iff ( for a be ElementSUBSET-1M1-of A holds o .BINOP-1K1(e,a) =XBOOLE-0R4 a & o .BINOP-1K1(a,e) =XBOOLE-0R4 a)"
sorry

mtheorem binop_1_th_4:
" for A be setHIDDENM2 holds  for o be BinOpBINOP-1M2-of A holds  for e be ElementSUBSET-1M1-of A holds o be commutativeBINOP-1V1\<^bsub>(A)\<^esub> implies (e is-a-unity-wrtBINOP-1R3\<^bsub>(A)\<^esub> o iff ( for a be ElementSUBSET-1M1-of A holds o .BINOP-1K1(e,a) =XBOOLE-0R4 a))"
sorry

mtheorem binop_1_th_5:
" for A be setHIDDENM2 holds  for o be BinOpBINOP-1M2-of A holds  for e be ElementSUBSET-1M1-of A holds o be commutativeBINOP-1V1\<^bsub>(A)\<^esub> implies (e is-a-unity-wrtBINOP-1R3\<^bsub>(A)\<^esub> o iff ( for a be ElementSUBSET-1M1-of A holds o .BINOP-1K1(a,e) =XBOOLE-0R4 a))"
sorry

mtheorem binop_1_th_6:
" for A be setHIDDENM2 holds  for o be BinOpBINOP-1M2-of A holds  for e be ElementSUBSET-1M1-of A holds o be commutativeBINOP-1V1\<^bsub>(A)\<^esub> implies (e is-a-unity-wrtBINOP-1R3\<^bsub>(A)\<^esub> o iff e is-a-left-unity-wrtBINOP-1R1\<^bsub>(A)\<^esub> o)"
  using binop_1_th_4 sorry

mtheorem binop_1_th_7:
" for A be setHIDDENM2 holds  for o be BinOpBINOP-1M2-of A holds  for e be ElementSUBSET-1M1-of A holds o be commutativeBINOP-1V1\<^bsub>(A)\<^esub> implies (e is-a-unity-wrtBINOP-1R3\<^bsub>(A)\<^esub> o iff e is-a-right-unity-wrtBINOP-1R2\<^bsub>(A)\<^esub> o)"
  using binop_1_th_5 sorry

mtheorem binop_1_th_8:
" for A be setHIDDENM2 holds  for o be BinOpBINOP-1M2-of A holds  for e be ElementSUBSET-1M1-of A holds o be commutativeBINOP-1V1\<^bsub>(A)\<^esub> implies (e is-a-left-unity-wrtBINOP-1R1\<^bsub>(A)\<^esub> o iff e is-a-right-unity-wrtBINOP-1R2\<^bsub>(A)\<^esub> o)"
sorry

mtheorem binop_1_th_9:
" for A be setHIDDENM2 holds  for o be BinOpBINOP-1M2-of A holds  for e1 be ElementSUBSET-1M1-of A holds  for e2 be ElementSUBSET-1M1-of A holds e1 is-a-left-unity-wrtBINOP-1R1\<^bsub>(A)\<^esub> o & e2 is-a-right-unity-wrtBINOP-1R2\<^bsub>(A)\<^esub> o implies e1 =XBOOLE-0R4 e2"
sorry

mtheorem binop_1_th_10:
" for A be setHIDDENM2 holds  for o be BinOpBINOP-1M2-of A holds  for e1 be ElementSUBSET-1M1-of A holds  for e2 be ElementSUBSET-1M1-of A holds e1 is-a-unity-wrtBINOP-1R3\<^bsub>(A)\<^esub> o & e2 is-a-unity-wrtBINOP-1R3\<^bsub>(A)\<^esub> o implies e1 =XBOOLE-0R4 e2"
  using binop_1_th_9 sorry

mdef binop_1_def_8 ("the-unity-wrtBINOP-1K3\<^bsub>'( _ ')\<^esub>  _ " [0,228]228 ) where
  mlet "A be setHIDDENM2", "o be BinOpBINOP-1M2-of A"
"assume  ex e be ElementSUBSET-1M1-of A st e is-a-unity-wrtBINOP-1R3\<^bsub>(A)\<^esub> o func the-unity-wrtBINOP-1K3\<^bsub>(A)\<^esub> o \<rightarrow> ElementSUBSET-1M1-of A means
  \<lambda>it. it is-a-unity-wrtBINOP-1R3\<^bsub>(A)\<^esub> o"
proof-
  (*existence*)
    show "( ex e be ElementSUBSET-1M1-of A st e is-a-unity-wrtBINOP-1R3\<^bsub>(A)\<^esub> o) implies ( ex it be ElementSUBSET-1M1-of A st it is-a-unity-wrtBINOP-1R3\<^bsub>(A)\<^esub> o)"
sorry
  (*uniqueness*)
    show "( ex e be ElementSUBSET-1M1-of A st e is-a-unity-wrtBINOP-1R3\<^bsub>(A)\<^esub> o) implies ( for it1 be ElementSUBSET-1M1-of A holds  for it2 be ElementSUBSET-1M1-of A holds it1 is-a-unity-wrtBINOP-1R3\<^bsub>(A)\<^esub> o & it2 is-a-unity-wrtBINOP-1R3\<^bsub>(A)\<^esub> o implies it1 =HIDDENR1 it2)"
sorry
qed "sorry"

mdef binop_1_def_9 (" _ is-left-distributive-wrtBINOP-1R4\<^bsub>'( _ ')\<^esub>  _ " [50,0,50]50 ) where
  mlet "A be setHIDDENM2", "o9 be BinOpBINOP-1M2-of A", "o be BinOpBINOP-1M2-of A"
"pred o9 is-left-distributive-wrtBINOP-1R4\<^bsub>(A)\<^esub> o means
   for a be ElementSUBSET-1M1-of A holds  for b be ElementSUBSET-1M1-of A holds  for c be ElementSUBSET-1M1-of A holds o9 .BINOP-1K1(a,o .BINOP-1K1(b,c)) =XBOOLE-0R4 o .BINOP-1K1(o9 .BINOP-1K1(a,b),o9 .BINOP-1K1(a,c))"..

mdef binop_1_def_10 (" _ is-right-distributive-wrtBINOP-1R5\<^bsub>'( _ ')\<^esub>  _ " [50,0,50]50 ) where
  mlet "A be setHIDDENM2", "o9 be BinOpBINOP-1M2-of A", "o be BinOpBINOP-1M2-of A"
"pred o9 is-right-distributive-wrtBINOP-1R5\<^bsub>(A)\<^esub> o means
   for a be ElementSUBSET-1M1-of A holds  for b be ElementSUBSET-1M1-of A holds  for c be ElementSUBSET-1M1-of A holds o9 .BINOP-1K1(o .BINOP-1K1(a,b),c) =XBOOLE-0R4 o .BINOP-1K1(o9 .BINOP-1K1(a,c),o9 .BINOP-1K1(b,c))"..

mdef binop_1_def_11 (" _ is-distributive-wrtBINOP-1R6\<^bsub>'( _ ')\<^esub>  _ " [50,0,50]50 ) where
  mlet "A be setHIDDENM2", "o9 be BinOpBINOP-1M2-of A", "o be BinOpBINOP-1M2-of A"
"pred o9 is-distributive-wrtBINOP-1R6\<^bsub>(A)\<^esub> o means
  o9 is-left-distributive-wrtBINOP-1R4\<^bsub>(A)\<^esub> o & o9 is-right-distributive-wrtBINOP-1R5\<^bsub>(A)\<^esub> o"..

mtheorem binop_1_th_11:
" for A be setHIDDENM2 holds  for o be BinOpBINOP-1M2-of A holds  for o9 be BinOpBINOP-1M2-of A holds o9 is-distributive-wrtBINOP-1R6\<^bsub>(A)\<^esub> o iff ( for a be ElementSUBSET-1M1-of A holds  for b be ElementSUBSET-1M1-of A holds  for c be ElementSUBSET-1M1-of A holds o9 .BINOP-1K1(a,o .BINOP-1K1(b,c)) =XBOOLE-0R4 o .BINOP-1K1(o9 .BINOP-1K1(a,b),o9 .BINOP-1K1(a,c)) & o9 .BINOP-1K1(o .BINOP-1K1(a,b),c) =XBOOLE-0R4 o .BINOP-1K1(o9 .BINOP-1K1(a,c),o9 .BINOP-1K1(b,c)))"
sorry

mtheorem binop_1_th_12:
" for A be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for o be BinOpBINOP-1M2-of A holds  for o9 be BinOpBINOP-1M2-of A holds o9 be commutativeBINOP-1V1\<^bsub>(A)\<^esub> implies (o9 is-distributive-wrtBINOP-1R6\<^bsub>(A)\<^esub> o iff ( for a be ElementSUBSET-1M1-of A holds  for b be ElementSUBSET-1M1-of A holds  for c be ElementSUBSET-1M1-of A holds o9 .BINOP-1K2\<^bsub>(A,A,A)\<^esub>(a,o .BINOP-1K2\<^bsub>(A,A,A)\<^esub>(b,c)) =XBOOLE-0R4 o .BINOP-1K2\<^bsub>(A,A,A)\<^esub>(o9 .BINOP-1K2\<^bsub>(A,A,A)\<^esub>(a,b),o9 .BINOP-1K2\<^bsub>(A,A,A)\<^esub>(a,c))))"
sorry

mtheorem binop_1_th_13:
" for A be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for o be BinOpBINOP-1M2-of A holds  for o9 be BinOpBINOP-1M2-of A holds o9 be commutativeBINOP-1V1\<^bsub>(A)\<^esub> implies (o9 is-distributive-wrtBINOP-1R6\<^bsub>(A)\<^esub> o iff ( for a be ElementSUBSET-1M1-of A holds  for b be ElementSUBSET-1M1-of A holds  for c be ElementSUBSET-1M1-of A holds o9 .BINOP-1K2\<^bsub>(A,A,A)\<^esub>(o .BINOP-1K2\<^bsub>(A,A,A)\<^esub>(a,b),c) =XBOOLE-0R4 o .BINOP-1K2\<^bsub>(A,A,A)\<^esub>(o9 .BINOP-1K2\<^bsub>(A,A,A)\<^esub>(a,c),o9 .BINOP-1K2\<^bsub>(A,A,A)\<^esub>(b,c))))"
sorry

mtheorem binop_1_th_14:
" for A be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for o be BinOpBINOP-1M2-of A holds  for o9 be BinOpBINOP-1M2-of A holds o9 be commutativeBINOP-1V1\<^bsub>(A)\<^esub> implies (o9 is-distributive-wrtBINOP-1R6\<^bsub>(A)\<^esub> o iff o9 is-left-distributive-wrtBINOP-1R4\<^bsub>(A)\<^esub> o)"
  using binop_1_th_12 sorry

mtheorem binop_1_th_15:
" for A be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for o be BinOpBINOP-1M2-of A holds  for o9 be BinOpBINOP-1M2-of A holds o9 be commutativeBINOP-1V1\<^bsub>(A)\<^esub> implies (o9 is-distributive-wrtBINOP-1R6\<^bsub>(A)\<^esub> o iff o9 is-right-distributive-wrtBINOP-1R5\<^bsub>(A)\<^esub> o)"
  using binop_1_th_13 sorry

mtheorem binop_1_th_16:
" for A be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for o be BinOpBINOP-1M2-of A holds  for o9 be BinOpBINOP-1M2-of A holds o9 be commutativeBINOP-1V1\<^bsub>(A)\<^esub> implies (o9 is-right-distributive-wrtBINOP-1R5\<^bsub>(A)\<^esub> o iff o9 is-left-distributive-wrtBINOP-1R4\<^bsub>(A)\<^esub> o)"
sorry

mdef binop_1_def_12 (" _ is-distributive-wrtBINOP-1R7\<^bsub>'( _ ')\<^esub>  _ " [50,0,50]50 ) where
  mlet "A be setHIDDENM2", "u be UnOpBINOP-1M1-of A", "o be BinOpBINOP-1M2-of A"
"pred u is-distributive-wrtBINOP-1R7\<^bsub>(A)\<^esub> o means
   for a be ElementSUBSET-1M1-of A holds  for b be ElementSUBSET-1M1-of A holds u .FUNCT-1K1 (o .BINOP-1K1(a,b)) =XBOOLE-0R4 o .BINOP-1K1(u .FUNCT-1K1 a,u .FUNCT-1K1 b)"..

(*\$CD 3*)
abbreviation(input) BINOP_1R8(" _ is-a-left-unity-wrtBINOP-1R8\<^bsub>'( _ ')\<^esub>  _ " [50,0,50]50) where
  "e is-a-left-unity-wrtBINOP-1R8\<^bsub>(A)\<^esub> o \<equiv> e is-a-left-unity-wrtBINOP-1R1\<^bsub>(A)\<^esub> o"

mtheorem binop_1_def_16:
  mlet "A be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "e be objectHIDDENM1", "o be BinOpBINOP-1M2-of A"
"redefine pred e is-a-left-unity-wrtBINOP-1R8\<^bsub>(A)\<^esub> o means
   for a be ElementSUBSET-1M1-of A holds o .BINOP-1K1(e,a) =XBOOLE-0R4 a"
proof
(*compatibility*)
  show "e is-a-left-unity-wrtBINOP-1R8\<^bsub>(A)\<^esub> o iff ( for a be ElementSUBSET-1M1-of A holds o .BINOP-1K1(e,a) =XBOOLE-0R4 a)"
     sorry
qed "sorry"

abbreviation(input) BINOP_1R9(" _ is-a-right-unity-wrtBINOP-1R9\<^bsub>'( _ ')\<^esub>  _ " [50,0,50]50) where
  "e is-a-right-unity-wrtBINOP-1R9\<^bsub>(A)\<^esub> o \<equiv> e is-a-right-unity-wrtBINOP-1R2\<^bsub>(A)\<^esub> o"

mtheorem binop_1_def_17:
  mlet "A be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "e be objectHIDDENM1", "o be BinOpBINOP-1M2-of A"
"redefine pred e is-a-right-unity-wrtBINOP-1R9\<^bsub>(A)\<^esub> o means
   for a be ElementSUBSET-1M1-of A holds o .BINOP-1K1(a,e) =XBOOLE-0R4 a"
proof
(*compatibility*)
  show "e is-a-right-unity-wrtBINOP-1R9\<^bsub>(A)\<^esub> o iff ( for a be ElementSUBSET-1M1-of A holds o .BINOP-1K1(a,e) =XBOOLE-0R4 a)"
     sorry
qed "sorry"

abbreviation(input) BINOP_1R10(" _ is-left-distributive-wrtBINOP-1R10\<^bsub>'( _ ')\<^esub>  _ " [50,0,50]50) where
  "o9 is-left-distributive-wrtBINOP-1R10\<^bsub>(A)\<^esub> o \<equiv> o9 is-left-distributive-wrtBINOP-1R4\<^bsub>(A)\<^esub> o"

mtheorem binop_1_def_18:
  mlet "A be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "o9 be BinOpBINOP-1M2-of A", "o be BinOpBINOP-1M2-of A"
"redefine pred o9 is-left-distributive-wrtBINOP-1R10\<^bsub>(A)\<^esub> o means
   for a be ElementSUBSET-1M1-of A holds  for b be ElementSUBSET-1M1-of A holds  for c be ElementSUBSET-1M1-of A holds o9 .BINOP-1K2\<^bsub>(A,A,A)\<^esub>(a,o .BINOP-1K2\<^bsub>(A,A,A)\<^esub>(b,c)) =XBOOLE-0R4 o .BINOP-1K2\<^bsub>(A,A,A)\<^esub>(o9 .BINOP-1K2\<^bsub>(A,A,A)\<^esub>(a,b),o9 .BINOP-1K2\<^bsub>(A,A,A)\<^esub>(a,c))"
proof
(*compatibility*)
  show "o9 is-left-distributive-wrtBINOP-1R10\<^bsub>(A)\<^esub> o iff ( for a be ElementSUBSET-1M1-of A holds  for b be ElementSUBSET-1M1-of A holds  for c be ElementSUBSET-1M1-of A holds o9 .BINOP-1K2\<^bsub>(A,A,A)\<^esub>(a,o .BINOP-1K2\<^bsub>(A,A,A)\<^esub>(b,c)) =XBOOLE-0R4 o .BINOP-1K2\<^bsub>(A,A,A)\<^esub>(o9 .BINOP-1K2\<^bsub>(A,A,A)\<^esub>(a,b),o9 .BINOP-1K2\<^bsub>(A,A,A)\<^esub>(a,c)))"
     sorry
qed "sorry"

abbreviation(input) BINOP_1R11(" _ is-right-distributive-wrtBINOP-1R11\<^bsub>'( _ ')\<^esub>  _ " [50,0,50]50) where
  "o9 is-right-distributive-wrtBINOP-1R11\<^bsub>(A)\<^esub> o \<equiv> o9 is-right-distributive-wrtBINOP-1R5\<^bsub>(A)\<^esub> o"

mtheorem binop_1_def_19:
  mlet "A be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "o9 be BinOpBINOP-1M2-of A", "o be BinOpBINOP-1M2-of A"
"redefine pred o9 is-right-distributive-wrtBINOP-1R11\<^bsub>(A)\<^esub> o means
   for a be ElementSUBSET-1M1-of A holds  for b be ElementSUBSET-1M1-of A holds  for c be ElementSUBSET-1M1-of A holds o9 .BINOP-1K2\<^bsub>(A,A,A)\<^esub>(o .BINOP-1K2\<^bsub>(A,A,A)\<^esub>(a,b),c) =XBOOLE-0R4 o .BINOP-1K2\<^bsub>(A,A,A)\<^esub>(o9 .BINOP-1K2\<^bsub>(A,A,A)\<^esub>(a,c),o9 .BINOP-1K2\<^bsub>(A,A,A)\<^esub>(b,c))"
proof
(*compatibility*)
  show "o9 is-right-distributive-wrtBINOP-1R11\<^bsub>(A)\<^esub> o iff ( for a be ElementSUBSET-1M1-of A holds  for b be ElementSUBSET-1M1-of A holds  for c be ElementSUBSET-1M1-of A holds o9 .BINOP-1K2\<^bsub>(A,A,A)\<^esub>(o .BINOP-1K2\<^bsub>(A,A,A)\<^esub>(a,b),c) =XBOOLE-0R4 o .BINOP-1K2\<^bsub>(A,A,A)\<^esub>(o9 .BINOP-1K2\<^bsub>(A,A,A)\<^esub>(a,c),o9 .BINOP-1K2\<^bsub>(A,A,A)\<^esub>(b,c)))"
     sorry
qed "sorry"

abbreviation(input) BINOP_1R12(" _ is-distributive-wrtBINOP-1R12\<^bsub>'( _ ')\<^esub>  _ " [50,0,50]50) where
  "u is-distributive-wrtBINOP-1R12\<^bsub>(A)\<^esub> o \<equiv> u is-distributive-wrtBINOP-1R7\<^bsub>(A)\<^esub> o"

mtheorem binop_1_def_20:
  mlet "A be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "u be UnOpBINOP-1M1-of A", "o be BinOpBINOP-1M2-of A"
"redefine pred u is-distributive-wrtBINOP-1R12\<^bsub>(A)\<^esub> o means
   for a be ElementSUBSET-1M1-of A holds  for b be ElementSUBSET-1M1-of A holds u .FUNCT-2K3\<^bsub>(A,A)\<^esub> (o .BINOP-1K2\<^bsub>(A,A,A)\<^esub>(a,b)) =XBOOLE-0R4 o .BINOP-1K2\<^bsub>(A,A,A)\<^esub>(u .FUNCT-2K3\<^bsub>(A,A)\<^esub> a,u .FUNCT-2K3\<^bsub>(A,A)\<^esub> b)"
proof
(*compatibility*)
  show "u is-distributive-wrtBINOP-1R12\<^bsub>(A)\<^esub> o iff ( for a be ElementSUBSET-1M1-of A holds  for b be ElementSUBSET-1M1-of A holds u .FUNCT-2K3\<^bsub>(A,A)\<^esub> (o .BINOP-1K2\<^bsub>(A,A,A)\<^esub>(a,b)) =XBOOLE-0R4 o .BINOP-1K2\<^bsub>(A,A,A)\<^esub>(u .FUNCT-2K3\<^bsub>(A,A)\<^esub> a,u .FUNCT-2K3\<^bsub>(A,A)\<^esub> b))"
     sorry
qed "sorry"

mtheorem binop_1_th_17:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds  for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for f be FunctionFUNCT-2M1-of([:ZFMISC-1K2 X,Y :],Z) holds (x inHIDDENR3 X & y inHIDDENR3 Y) & Z <>HIDDENR2 {}XBOOLE-0K1 implies f .BINOP-1K1(x,y) inTARSKIR2 Z"
sorry

mtheorem binop_1_th_18:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of([:ZFMISC-1K2 X,Y :],Z) holds  for g be FunctionFUNCT-1M1 holds (Z <>HIDDENR2 {}XBOOLE-0K1 & x inHIDDENR3 X) & y inHIDDENR3 Y implies (g *FUNCT-1K3 f).BINOP-1K1(x,y) =XBOOLE-0R4 g .FUNCT-1K1 (f .BINOP-1K1(x,y))"
  using funct_2_th_15 zfmisc_1_th_87 sorry

mtheorem binop_1_th_19:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds domRELAT-1K1 f =XBOOLE-0R4 [:ZFMISC-1K2 X,Y :] implies (f be constantFUNCT-1V5 iff ( for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for y1 be objectHIDDENM1 holds  for y2 be objectHIDDENM1 holds ((x1 inHIDDENR3 X & x2 inHIDDENR3 X) & y1 inHIDDENR3 Y) & y2 inHIDDENR3 Y implies f .BINOP-1K1(x1,y1) =XBOOLE-0R4 f .BINOP-1K1(x2,y2)))"
sorry

mtheorem binop_1_th_20:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds  for f1 be PartFuncPARTFUN1M1-of([:ZFMISC-1K2 X,Y :],Z) holds  for f2 be PartFuncPARTFUN1M1-of([:ZFMISC-1K2 X,Y :],Z) holds domRELSET-1K1\<^bsub>([:ZFMISC-1K2 X,Y :])\<^esub> f1 =RELSET-1R2\<^bsub>(X,Y)\<^esub> domRELSET-1K1\<^bsub>([:ZFMISC-1K2 X,Y :])\<^esub> f2 & ( for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds [TARSKIK4 x,y ] inHIDDENR3 domRELSET-1K1\<^bsub>([:ZFMISC-1K2 X,Y :])\<^esub> f1 implies f1 .BINOP-1K1(x,y) =XBOOLE-0R4 f2 .BINOP-1K1(x,y)) implies f1 =RELSET-1R2\<^bsub>([:ZFMISC-1K2 X,Y :],Z)\<^esub> f2"
sorry

theorem binop_1_sch_5:
  fixes Xf0 Yf0 Zf0 Pp3 
  assumes
[ty]: "Xf0 be setHIDDENM2" and
  [ty]: "Yf0 be setHIDDENM2" and
  [ty]: "Zf0 be setHIDDENM2" and
   A1: " for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for z be objectHIDDENM1 holds (x inHIDDENR3 Xf0 & y inHIDDENR3 Yf0) & Pp3(x,y,z) implies z inHIDDENR3 Zf0" and
   A2: " for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for z1 be objectHIDDENM1 holds  for z2 be objectHIDDENM1 holds ((x inHIDDENR3 Xf0 & y inHIDDENR3 Yf0) & Pp3(x,y,z1)) & Pp3(x,y,z2) implies z1 =HIDDENR1 z2"
  shows " ex f be PartFuncPARTFUN1M1-of([:ZFMISC-1K2 Xf0,Yf0 :],Zf0) st ( for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds [TARSKIK4 x,y ] inHIDDENR3 domRELSET-1K1\<^bsub>([:ZFMISC-1K2 Xf0,Yf0 :])\<^esub> f iff (x inHIDDENR3 Xf0 & y inHIDDENR3 Yf0) & ( ex z be objectHIDDENM1 st Pp3(x,y,z))) & ( for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds [TARSKIK4 x,y ] inHIDDENR3 domRELSET-1K1\<^bsub>([:ZFMISC-1K2 Xf0,Yf0 :])\<^esub> f implies Pp3(x,y,f .BINOP-1K1(x,y)))"
sorry

theorem binop_1_sch_6:
  fixes Xf0 Yf0 Zf0 Ff2 Pp2 
  assumes
[ty]: "Xf0 be setHIDDENM2" and
  [ty]: "Yf0 be setHIDDENM2" and
  [ty]: "Zf0 be setHIDDENM2" and
  [ty_func]: "\<And> x1 x2. x1 be objectHIDDENM1 \<Longrightarrow> x2 be objectHIDDENM1 \<Longrightarrow> Ff2(x1,x2) be objectHIDDENM1" and
   A1: " for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds Pp2(x,y) implies Ff2(x,y) inHIDDENR3 Zf0"
  shows " ex f be PartFuncPARTFUN1M1-of([:ZFMISC-1K2 Xf0,Yf0 :],Zf0) st ( for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds [TARSKIK4 x,y ] inHIDDENR3 domRELSET-1K1\<^bsub>([:ZFMISC-1K2 Xf0,Yf0 :])\<^esub> f iff (x inHIDDENR3 Xf0 & y inHIDDENR3 Yf0) & Pp2(x,y)) & ( for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds [TARSKIK4 x,y ] inHIDDENR3 domRELSET-1K1\<^bsub>([:ZFMISC-1K2 Xf0,Yf0 :])\<^esub> f implies f .BINOP-1K1(x,y) =HIDDENR1 Ff2(x,y))"
sorry

theorem binop_1_sch_7:
  fixes Xf0 Yf0 Zf0 Ff2 Pp2 
  assumes
[ty]: "Xf0 be setHIDDENM2" and
  [ty]: "Yf0 be setHIDDENM2" and
  [ty]: "Zf0 be setHIDDENM2" and
  [ty_func]: "\<And> x1 x2. x1 be objectHIDDENM1 \<Longrightarrow> x2 be objectHIDDENM1 \<Longrightarrow> Ff2(x1,x2) be objectHIDDENM1" and
   A1: " for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds (x inHIDDENR3 Xf0 & y inHIDDENR3 Yf0) & Pp2(x,y) implies Ff2(x,y) inHIDDENR3 Zf0"
  shows " ex f be PartFuncPARTFUN1M1-of([:ZFMISC-1K2 Xf0,Yf0 :],Zf0) st ( for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds [TARSKIK4 x,y ] inHIDDENR3 domRELSET-1K1\<^bsub>([:ZFMISC-1K2 Xf0,Yf0 :])\<^esub> f iff (x inHIDDENR3 Xf0 & y inHIDDENR3 Yf0) & Pp2(x,y)) & ( for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds [TARSKIK4 x,y ] inHIDDENR3 domRELSET-1K1\<^bsub>([:ZFMISC-1K2 Xf0,Yf0 :])\<^esub> f implies f .BINOP-1K1(x,y) =HIDDENR1 Ff2(x,y))"
sorry

theorem binop_1_sch_8:
  fixes Xf0 Yf0 Zf0 Ff2 Pp2 
  assumes
[ty]: "Xf0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
  [ty]: "Yf0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
  [ty]: "Zf0 be setHIDDENM2" and
  [ty_func]: "\<And> x1 x2. x1 be objectHIDDENM1 \<Longrightarrow> x2 be objectHIDDENM1 \<Longrightarrow> Ff2(x1,x2) be objectHIDDENM1" and
   A1: " for x be ElementSUBSET-1M1-of Xf0 holds  for y be ElementSUBSET-1M1-of Yf0 holds Pp2(x,y) implies Ff2(x,y) inHIDDENR3 Zf0"
  shows " ex f be PartFuncPARTFUN1M1-of([:ZFMISC-1K2 Xf0,Yf0 :],Zf0) st ( for x be ElementSUBSET-1M1-of Xf0 holds  for y be ElementSUBSET-1M1-of Yf0 holds [TARSKIK4 x,y ] inHIDDENR3 domRELSET-1K1\<^bsub>([:ZFMISC-1K2 Xf0,Yf0 :])\<^esub> f iff Pp2(x,y)) & ( for x be ElementSUBSET-1M1-of Xf0 holds  for y be ElementSUBSET-1M1-of Yf0 holds [TARSKIK4 x,y ] inHIDDENR3 domRELSET-1K1\<^bsub>([:ZFMISC-1K2 Xf0,Yf0 :])\<^esub> f implies f .BINOP-1K1(x,y) =HIDDENR1 Ff2(x,y))"
sorry

syntax BINOP_1K4 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ .BINOP-1K4\<^bsub>'( _ ')\<^esub>'( _ , _ ')" [200,0,0,0]200)
translations "f .BINOP-1K4\<^bsub>(A)\<^esub>(a,b)" \<rightharpoonup> "f .BINOP-1K1(a,b)"

mtheorem binop_1_add_2:
  mlet "A be setHIDDENM2", "f be BinOpBINOP-1M2-of A", "a be ElementSUBSET-1M1-of A", "b be ElementSUBSET-1M1-of A"
"cluster f .BINOP-1K1(a,b) as-term-is ElementSUBSET-1M1-of A"
proof
(*coherence*)
  show "f .BINOP-1K1(a,b) be ElementSUBSET-1M1-of A"
sorry
qed "sorry"

syntax BINOP_1R13 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> o" (" _ =BINOP-1R13\<^bsub>'( _ , _ , _ ')\<^esub>  _ " [50,0,0,0,50]50)
translations "f1 =BINOP-1R13\<^bsub>(X,Y,Z)\<^esub> f2" \<rightharpoonup> "f1 =HIDDENR1 f2"

mtheorem binop_1_def_21:
  mlet "X be setHIDDENM2", "Y be setHIDDENM2", "Z be setHIDDENM2", "f1 be FunctionFUNCT-2M1-of([:ZFMISC-1K2 X,Y :],Z)", "f2 be FunctionFUNCT-2M1-of([:ZFMISC-1K2 X,Y :],Z)"
"redefine pred f1 =BINOP-1R13\<^bsub>(X,Y,Z)\<^esub> f2 means
   for x be setHIDDENM2 holds  for y be setHIDDENM2 holds x inTARSKIR2 X & y inTARSKIR2 Y implies f1 .BINOP-1K1(x,y) =XBOOLE-0R4 f2 .BINOP-1K1(x,y)"
proof
(*compatibility*)
  show "f1 =BINOP-1R13\<^bsub>(X,Y,Z)\<^esub> f2 iff ( for x be setHIDDENM2 holds  for y be setHIDDENM2 holds x inTARSKIR2 X & y inTARSKIR2 Y implies f1 .BINOP-1K1(x,y) =XBOOLE-0R4 f2 .BINOP-1K1(x,y))"
    using binop_1_th_1 sorry
qed "sorry"

theorem binop_1_sch_9:
  fixes Xf0 Yf0 Zf0 Pp3 
  assumes
[ty]: "Xf0 be setHIDDENM2" and
  [ty]: "Yf0 be setHIDDENM2" and
  [ty]: "Zf0 be setHIDDENM2" and
   A1: " for x be setHIDDENM2 holds  for y be setHIDDENM2 holds x inTARSKIR2 Xf0 & y inTARSKIR2 Yf0 implies ( ex z be setHIDDENM2 st z inTARSKIR2 Zf0 & Pp3(x,y,z))"
  shows " ex f be FunctionFUNCT-2M1-of([:ZFMISC-1K2 Xf0,Yf0 :],Zf0) st  for x be setHIDDENM2 holds  for y be setHIDDENM2 holds x inTARSKIR2 Xf0 & y inTARSKIR2 Yf0 implies Pp3(x,y,f .BINOP-1K1(x,y))"
sorry

end
