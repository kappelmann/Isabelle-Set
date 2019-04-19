theory multop_1
  imports funct_2 domain_1
begin
(*begin*)
mdef multop_1_def_1 (" _ .MULTOP-1K1'( _ , _ , _ ')" [200,0,0,0]200 ) where
  mlet "f be FunctionFUNCT-1M1", "a be objectHIDDENM1", "b be objectHIDDENM1", "c be objectHIDDENM1"
"func f .MULTOP-1K1(a,b,c) \<rightarrow> setHIDDENM2 equals
  f .FUNCT-1K1 [XTUPLE-0K3 a,b,c ]"
proof-
  (*coherence*)
    show "f .FUNCT-1K1 [XTUPLE-0K3 a,b,c ] be setHIDDENM2"
       sorry
qed "sorry"

reserve A, B, C, D, E for " non emptyXBOOLE-0V1\<bar>setHIDDENM2"
reserve a for "ElementSUBSET-1M1-of A"
reserve b for "ElementSUBSET-1M1-of B"
reserve c for "ElementSUBSET-1M1-of C"
reserve d for "ElementSUBSET-1M1-of D"
reserve X, Y, Z, S for "setHIDDENM2"
reserve x, y, z, s, t for "objectHIDDENM1"
syntax MULTOP_1K2 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ .MULTOP-1K2\<^bsub>'( _ , _ , _ , _ ')\<^esub>'( _ , _ , _ ')" [200,0,0,0,0,0,0,0]200)
translations "f .MULTOP-1K2\<^bsub>(A,B,C,D)\<^esub>(a,b,c)" \<rightharpoonup> "f .MULTOP-1K1(a,b,c)"

mtheorem multop_1_add_1:
  mlet "A be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "B be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "f be FunctionFUNCT-2M1-of([:ZFMISC-1K3 A,B,C :],D)", "a be ElementSUBSET-1M1-of A", "b be ElementSUBSET-1M1-of B", "c be ElementSUBSET-1M1-of C"
"cluster f .MULTOP-1K1(a,b,c) as-term-is ElementSUBSET-1M1-of D"
proof
(*coherence*)
  show "f .MULTOP-1K1(a,b,c) be ElementSUBSET-1M1-of D"
sorry
qed "sorry"

mtheorem multop_1_th_1:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds  for f1 be FunctionFUNCT-2M1-of([:ZFMISC-1K3 X,Y,Z :],D) holds  for f2 be FunctionFUNCT-2M1-of([:ZFMISC-1K3 X,Y,Z :],D) holds ( for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for z be objectHIDDENM1 holds (x inHIDDENR3 X & y inHIDDENR3 Y) & z inHIDDENR3 Z implies f1 .FUNCT-1K1 [XTUPLE-0K3 x,y,z ] =XBOOLE-0R4 f2 .FUNCT-1K1 [XTUPLE-0K3 x,y,z ]) implies f1 =FUNCT-2R2\<^bsub>([:ZFMISC-1K3 X,Y,Z :],D)\<^esub> f2"
sorry

mtheorem multop_1_th_2:
" for A be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for B be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for f1 be FunctionFUNCT-2M1-of([:ZFMISC-1K3 A,B,C :],D) holds  for f2 be FunctionFUNCT-2M1-of([:ZFMISC-1K3 A,B,C :],D) holds ( for a be ElementSUBSET-1M1-of A holds  for b be ElementSUBSET-1M1-of B holds  for c be ElementSUBSET-1M1-of C holds f1 .FUNCT-2K3\<^bsub>([:ZFMISC-1K3 A,B,C :],D)\<^esub> [DOMAIN-1K4\<^bsub>(A,B,C)\<^esub> a,b,c ] =XBOOLE-0R4 f2 .FUNCT-2K3\<^bsub>([:ZFMISC-1K3 A,B,C :],D)\<^esub> [DOMAIN-1K4\<^bsub>(A,B,C)\<^esub> a,b,c ]) implies f1 =FUNCT-2R2\<^bsub>([:ZFMISC-1K3 A,B,C :],D)\<^esub> f2"
sorry

mtheorem multop_1_th_3:
" for A be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for B be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for f1 be FunctionFUNCT-2M1-of([:ZFMISC-1K3 A,B,C :],D) holds  for f2 be FunctionFUNCT-2M1-of([:ZFMISC-1K3 A,B,C :],D) holds ( for a be ElementSUBSET-1M1-of A holds  for b be ElementSUBSET-1M1-of B holds  for c be ElementSUBSET-1M1-of C holds f1 .MULTOP-1K2\<^bsub>(A,B,C,D)\<^esub>(a,b,c) =XBOOLE-0R4 f2 .MULTOP-1K2\<^bsub>(A,B,C,D)\<^esub>(a,b,c)) implies f1 =FUNCT-2R2\<^bsub>([:ZFMISC-1K3 A,B,C :],D)\<^esub> f2"
sorry

syntax MULTOP_1M1 :: " Set \<Rightarrow> Ty" ("TriOpMULTOP-1M1-of  _ " [70]70)
translations "TriOpMULTOP-1M1-of A" \<rightharpoonup> "FunctionFUNCT-2M1-of([:ZFMISC-1K3 A,A,A :],A)"

theorem multop_1_sch_1:
  fixes Xf0 Yf0 Zf0 Tf0 Pp4 
  assumes
[ty]: "Xf0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
  [ty]: "Yf0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
  [ty]: "Zf0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
  [ty]: "Tf0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
   A1: " for x be ElementSUBSET-1M1-of Xf0 holds  for y be ElementSUBSET-1M1-of Yf0 holds  for z be ElementSUBSET-1M1-of Zf0 holds  ex t be ElementSUBSET-1M1-of Tf0 st Pp4(x,y,z,t)"
  shows " ex f be FunctionFUNCT-2M1-of([:ZFMISC-1K3 Xf0,Yf0,Zf0 :],Tf0) st  for x be ElementSUBSET-1M1-of Xf0 holds  for y be ElementSUBSET-1M1-of Yf0 holds  for z be ElementSUBSET-1M1-of Zf0 holds Pp4(x,y,z,f .FUNCT-2K3\<^bsub>([:ZFMISC-1K3 Xf0,Yf0,Zf0 :],Tf0)\<^esub> [DOMAIN-1K4\<^bsub>(Xf0,Yf0,Zf0)\<^esub> x,y,z ])"
sorry

theorem multop_1_sch_2:
  fixes Af0 Pp4 
  assumes
[ty]: "Af0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
   A1: " for x be ElementSUBSET-1M1-of Af0 holds  for y be ElementSUBSET-1M1-of Af0 holds  for z be ElementSUBSET-1M1-of Af0 holds  ex t be ElementSUBSET-1M1-of Af0 st Pp4(x,y,z,t)"
  shows " ex o be TriOpMULTOP-1M1-of Af0 st  for a be ElementSUBSET-1M1-of Af0 holds  for b be ElementSUBSET-1M1-of Af0 holds  for c be ElementSUBSET-1M1-of Af0 holds Pp4(a,b,c,o .MULTOP-1K2\<^bsub>(Af0,Af0,Af0,Af0)\<^esub>(a,b,c))"
sorry

theorem multop_1_sch_3:
  fixes Xf0 Yf0 Zf0 Tf0 Ff3 
  assumes
[ty]: "Xf0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
  [ty]: "Yf0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
  [ty]: "Zf0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
  [ty]: "Tf0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
  [ty_func]: "\<And> x1 x2 x3. x1 be ElementSUBSET-1M1-of Xf0 \<Longrightarrow> x2 be ElementSUBSET-1M1-of Yf0 \<Longrightarrow> x3 be ElementSUBSET-1M1-of Zf0 \<Longrightarrow> Ff3(x1,x2,x3) be ElementSUBSET-1M1-of Tf0"
  shows " ex f be FunctionFUNCT-2M1-of([:ZFMISC-1K3 Xf0,Yf0,Zf0 :],Tf0) st  for x be ElementSUBSET-1M1-of Xf0 holds  for y be ElementSUBSET-1M1-of Yf0 holds  for z be ElementSUBSET-1M1-of Zf0 holds f .FUNCT-2K3\<^bsub>([:ZFMISC-1K3 Xf0,Yf0,Zf0 :],Tf0)\<^esub> [DOMAIN-1K4\<^bsub>(Xf0,Yf0,Zf0)\<^esub> x,y,z ] =XBOOLE-0R4 Ff3(x,y,z)"
sorry

theorem multop_1_sch_4:
  fixes Af0 Bf0 Cf0 Df0 Of3 
  assumes
[ty]: "Af0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
  [ty]: "Bf0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
  [ty]: "Cf0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
  [ty]: "Df0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
  [ty_func]: "\<And> x1 x2 x3. x1 be ElementSUBSET-1M1-of Af0 \<Longrightarrow> x2 be ElementSUBSET-1M1-of Bf0 \<Longrightarrow> x3 be ElementSUBSET-1M1-of Cf0 \<Longrightarrow> Of3(x1,x2,x3) be ElementSUBSET-1M1-of Df0"
  shows " ex o be FunctionFUNCT-2M1-of([:ZFMISC-1K3 Af0,Bf0,Cf0 :],Df0) st  for a be ElementSUBSET-1M1-of Af0 holds  for b be ElementSUBSET-1M1-of Bf0 holds  for c be ElementSUBSET-1M1-of Cf0 holds o .MULTOP-1K2\<^bsub>(Af0,Bf0,Cf0,Df0)\<^esub>(a,b,c) =XBOOLE-0R4 Of3(a,b,c)"
sorry

mdef multop_1_def_2 (" _ .MULTOP-1K3'( _ , _ , _ , _ ')" [200,0,0,0,0]200 ) where
  mlet "f be FunctionFUNCT-1M1", "a be setHIDDENM2", "b be setHIDDENM2", "c be setHIDDENM2", "d be setHIDDENM2"
"func f .MULTOP-1K3(a,b,c,d) \<rightarrow> setHIDDENM2 equals
  f .FUNCT-1K1 [XTUPLE-0K7 a,b,c,d ]"
proof-
  (*coherence*)
    show "f .FUNCT-1K1 [XTUPLE-0K7 a,b,c,d ] be setHIDDENM2"
       sorry
qed "sorry"

syntax MULTOP_1K4 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ .MULTOP-1K4\<^bsub>'( _ , _ , _ , _ , _ ')\<^esub>'( _ , _ , _ , _ ')" [200,0,0,0,0,0,0,0,0,0]200)
translations "f .MULTOP-1K4\<^bsub>(A,B,C,D,E)\<^esub>(a,b,c,d)" \<rightharpoonup> "f .MULTOP-1K3(a,b,c,d)"

mtheorem multop_1_add_2:
  mlet "A be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "B be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "E be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "f be FunctionFUNCT-2M1-of([:ZFMISC-1K4 A,B,C,D :],E)", "a be ElementSUBSET-1M1-of A", "b be ElementSUBSET-1M1-of B", "c be ElementSUBSET-1M1-of C", "d be ElementSUBSET-1M1-of D"
"cluster f .MULTOP-1K3(a,b,c,d) as-term-is ElementSUBSET-1M1-of E"
proof
(*coherence*)
  show "f .MULTOP-1K3(a,b,c,d) be ElementSUBSET-1M1-of E"
sorry
qed "sorry"

mtheorem multop_1_th_4:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds  for S be setHIDDENM2 holds  for f1 be FunctionFUNCT-2M1-of([:ZFMISC-1K4 X,Y,Z,S :],D) holds  for f2 be FunctionFUNCT-2M1-of([:ZFMISC-1K4 X,Y,Z,S :],D) holds ( for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for z be objectHIDDENM1 holds  for s be objectHIDDENM1 holds ((x inHIDDENR3 X & y inHIDDENR3 Y) & z inHIDDENR3 Z) & s inHIDDENR3 S implies f1 .FUNCT-1K1 [XTUPLE-0K7 x,y,z,s ] =XBOOLE-0R4 f2 .FUNCT-1K1 [XTUPLE-0K7 x,y,z,s ]) implies f1 =FUNCT-2R2\<^bsub>([:ZFMISC-1K4 X,Y,Z,S :],D)\<^esub> f2"
sorry

mtheorem multop_1_th_5:
" for A be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for B be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for E be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for f1 be FunctionFUNCT-2M1-of([:ZFMISC-1K4 A,B,C,D :],E) holds  for f2 be FunctionFUNCT-2M1-of([:ZFMISC-1K4 A,B,C,D :],E) holds ( for a be ElementSUBSET-1M1-of A holds  for b be ElementSUBSET-1M1-of B holds  for c be ElementSUBSET-1M1-of C holds  for d be ElementSUBSET-1M1-of D holds f1 .FUNCT-2K3\<^bsub>([:ZFMISC-1K4 A,B,C,D :],E)\<^esub> [DOMAIN-1K5\<^bsub>(A,B,C,D)\<^esub> a,b,c,d ] =XBOOLE-0R4 f2 .FUNCT-2K3\<^bsub>([:ZFMISC-1K4 A,B,C,D :],E)\<^esub> [DOMAIN-1K5\<^bsub>(A,B,C,D)\<^esub> a,b,c,d ]) implies f1 =FUNCT-2R2\<^bsub>([:ZFMISC-1K4 A,B,C,D :],E)\<^esub> f2"
sorry

mtheorem multop_1_th_6:
" for A be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for B be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for E be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for f1 be FunctionFUNCT-2M1-of([:ZFMISC-1K4 A,B,C,D :],E) holds  for f2 be FunctionFUNCT-2M1-of([:ZFMISC-1K4 A,B,C,D :],E) holds ( for a be ElementSUBSET-1M1-of A holds  for b be ElementSUBSET-1M1-of B holds  for c be ElementSUBSET-1M1-of C holds  for d be ElementSUBSET-1M1-of D holds f1 .MULTOP-1K4\<^bsub>(A,B,C,D,E)\<^esub>(a,b,c,d) =XBOOLE-0R4 f2 .MULTOP-1K4\<^bsub>(A,B,C,D,E)\<^esub>(a,b,c,d)) implies f1 =FUNCT-2R2\<^bsub>([:ZFMISC-1K4 A,B,C,D :],E)\<^esub> f2"
sorry

syntax MULTOP_1M2 :: " Set \<Rightarrow> Ty" ("QuaOpMULTOP-1M2-of  _ " [70]70)
translations "QuaOpMULTOP-1M2-of A" \<rightharpoonup> "FunctionFUNCT-2M1-of([:ZFMISC-1K4 A,A,A,A :],A)"

theorem multop_1_sch_5:
  fixes Xf0 Yf0 Zf0 Sf0 Tf0 Pp5 
  assumes
[ty]: "Xf0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
  [ty]: "Yf0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
  [ty]: "Zf0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
  [ty]: "Sf0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
  [ty]: "Tf0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
   A1: " for x be ElementSUBSET-1M1-of Xf0 holds  for y be ElementSUBSET-1M1-of Yf0 holds  for z be ElementSUBSET-1M1-of Zf0 holds  for s be ElementSUBSET-1M1-of Sf0 holds  ex t be ElementSUBSET-1M1-of Tf0 st Pp5(x,y,z,s,t)"
  shows " ex f be FunctionFUNCT-2M1-of([:ZFMISC-1K4 Xf0,Yf0,Zf0,Sf0 :],Tf0) st  for x be ElementSUBSET-1M1-of Xf0 holds  for y be ElementSUBSET-1M1-of Yf0 holds  for z be ElementSUBSET-1M1-of Zf0 holds  for s be ElementSUBSET-1M1-of Sf0 holds Pp5(x,y,z,s,f .FUNCT-2K3\<^bsub>([:ZFMISC-1K4 Xf0,Yf0,Zf0,Sf0 :],Tf0)\<^esub> [DOMAIN-1K5\<^bsub>(Xf0,Yf0,Zf0,Sf0)\<^esub> x,y,z,s ])"
sorry

theorem multop_1_sch_6:
  fixes Af0 Pp5 
  assumes
[ty]: "Af0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
   A1: " for x be ElementSUBSET-1M1-of Af0 holds  for y be ElementSUBSET-1M1-of Af0 holds  for z be ElementSUBSET-1M1-of Af0 holds  for s be ElementSUBSET-1M1-of Af0 holds  ex t be ElementSUBSET-1M1-of Af0 st Pp5(x,y,z,s,t)"
  shows " ex o be QuaOpMULTOP-1M2-of Af0 st  for a be ElementSUBSET-1M1-of Af0 holds  for b be ElementSUBSET-1M1-of Af0 holds  for c be ElementSUBSET-1M1-of Af0 holds  for d be ElementSUBSET-1M1-of Af0 holds Pp5(a,b,c,d,o .MULTOP-1K4\<^bsub>(Af0,Af0,Af0,Af0,Af0)\<^esub>(a,b,c,d))"
sorry

theorem multop_1_sch_7:
  fixes Xf0 Yf0 Zf0 Sf0 Tf0 Ff4 
  assumes
[ty]: "Xf0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
  [ty]: "Yf0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
  [ty]: "Zf0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
  [ty]: "Sf0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
  [ty]: "Tf0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
  [ty_func]: "\<And> x1 x2 x3 x4. x1 be ElementSUBSET-1M1-of Xf0 \<Longrightarrow> x2 be ElementSUBSET-1M1-of Yf0 \<Longrightarrow> x3 be ElementSUBSET-1M1-of Zf0 \<Longrightarrow> x4 be ElementSUBSET-1M1-of Sf0 \<Longrightarrow> Ff4(x1,x2,x3,x4) be ElementSUBSET-1M1-of Tf0"
  shows " ex f be FunctionFUNCT-2M1-of([:ZFMISC-1K4 Xf0,Yf0,Zf0,Sf0 :],Tf0) st  for x be ElementSUBSET-1M1-of Xf0 holds  for y be ElementSUBSET-1M1-of Yf0 holds  for z be ElementSUBSET-1M1-of Zf0 holds  for s be ElementSUBSET-1M1-of Sf0 holds f .FUNCT-2K3\<^bsub>([:ZFMISC-1K4 Xf0,Yf0,Zf0,Sf0 :],Tf0)\<^esub> [DOMAIN-1K5\<^bsub>(Xf0,Yf0,Zf0,Sf0)\<^esub> x,y,z,s ] =XBOOLE-0R4 Ff4(x,y,z,s)"
sorry

theorem multop_1_sch_8:
  fixes Af0 Of4 
  assumes
[ty]: "Af0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
  [ty_func]: "\<And> x1 x2 x3 x4. x1 be ElementSUBSET-1M1-of Af0 \<Longrightarrow> x2 be ElementSUBSET-1M1-of Af0 \<Longrightarrow> x3 be ElementSUBSET-1M1-of Af0 \<Longrightarrow> x4 be ElementSUBSET-1M1-of Af0 \<Longrightarrow> Of4(x1,x2,x3,x4) be ElementSUBSET-1M1-of Af0"
  shows " ex o be QuaOpMULTOP-1M2-of Af0 st  for a be ElementSUBSET-1M1-of Af0 holds  for b be ElementSUBSET-1M1-of Af0 holds  for c be ElementSUBSET-1M1-of Af0 holds  for d be ElementSUBSET-1M1-of Af0 holds o .MULTOP-1K4\<^bsub>(Af0,Af0,Af0,Af0,Af0)\<^esub>(a,b,c,d) =XBOOLE-0R4 Of4(a,b,c,d)"
sorry

end
