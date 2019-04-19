theory fraenkel
  imports domain_1 setwiseo
begin
(*begin*)
reserve B for " non emptyXBOOLE-0V1\<bar>setHIDDENM2"
reserve A, X, x for "setHIDDENM2"
theorem fraenkel_sch_1:
  fixes Af0 Ff1 Pp1 Qp1 
  assumes
[ty]: "Af0 be setHIDDENM2" and
  [ty_func]: "\<And> x1. x1 be objectHIDDENM1 \<Longrightarrow> Ff1(x1) be objectHIDDENM1" and
   A1: " for v be ElementSUBSET-1M1-of Af0 holds Pp1(v) implies Qp1(v)"
  shows "{Ff1(v) where v be ElementSUBSET-1M1-of Af0 : Pp1(v) } c=TARSKIR1 {Ff1(u) where u be ElementSUBSET-1M1-of Af0 : Qp1(u) }"
sorry

theorem fraenkel_sch_2:
  fixes Af0 Bf0 Ff2 Pp2 Qp2 
  assumes
[ty]: "Af0 be setHIDDENM2" and
  [ty]: "Bf0 be setHIDDENM2" and
  [ty_func]: "\<And> x1 x2. x1 be objectHIDDENM1 \<Longrightarrow> x2 be objectHIDDENM1 \<Longrightarrow> Ff2(x1,x2) be objectHIDDENM1" and
   A1: " for u be ElementSUBSET-1M1-of Af0 holds  for v be ElementSUBSET-1M1-of Bf0 holds Pp2(u,v) implies Qp2(u,v)"
  shows "{Ff2(u1,v1) where u1 be ElementSUBSET-1M1-of Af0, v1 be ElementSUBSET-1M1-of Bf0 : Pp2(u1,v1) } c=TARSKIR1 {Ff2(u2,v2) where u2 be ElementSUBSET-1M1-of Af0, v2 be ElementSUBSET-1M1-of Bf0 : Qp2(u2,v2) }"
sorry

theorem fraenkel_sch_3:
  fixes Bf0 Ff1 Pp1 Qp1 
  assumes
[ty]: "Bf0 be setHIDDENM2" and
  [ty_func]: "\<And> x1. x1 be objectHIDDENM1 \<Longrightarrow> Ff1(x1) be objectHIDDENM1" and
   A1: " for v be ElementSUBSET-1M1-of Bf0 holds Pp1(v) iff Qp1(v)"
  shows "{Ff1(v1) where v1 be ElementSUBSET-1M1-of Bf0 : Pp1(v1) } =XBOOLE-0R4 {Ff1(v2) where v2 be ElementSUBSET-1M1-of Bf0 : Qp1(v2) }"
sorry

theorem fraenkel_sch_4:
  fixes Af0 Bf0 Ff2 Pp2 Qp2 
  assumes
[ty]: "Af0 be setHIDDENM2" and
  [ty]: "Bf0 be setHIDDENM2" and
  [ty_func]: "\<And> x1 x2. x1 be objectHIDDENM1 \<Longrightarrow> x2 be objectHIDDENM1 \<Longrightarrow> Ff2(x1,x2) be objectHIDDENM1" and
   A1: " for u be ElementSUBSET-1M1-of Af0 holds  for v be ElementSUBSET-1M1-of Bf0 holds Pp2(u,v) iff Qp2(u,v)"
  shows "{Ff2(u1,v1) where u1 be ElementSUBSET-1M1-of Af0, v1 be ElementSUBSET-1M1-of Bf0 : Pp2(u1,v1) } =XBOOLE-0R4 {Ff2(u2,v2) where u2 be ElementSUBSET-1M1-of Af0, v2 be ElementSUBSET-1M1-of Bf0 : Qp2(u2,v2) }"
sorry

theorem fraenkel_sch_5:
  fixes Bf0 Ff1 Gf1 Pp1 
  assumes
[ty]: "Bf0 be setHIDDENM2" and
  [ty_func]: "\<And> x1. x1 be objectHIDDENM1 \<Longrightarrow> Ff1(x1) be objectHIDDENM1" and
  [ty_func]: "\<And> x1. x1 be objectHIDDENM1 \<Longrightarrow> Gf1(x1) be objectHIDDENM1" and
   A1: " for v be ElementSUBSET-1M1-of Bf0 holds Ff1(v) =HIDDENR1 Gf1(v)"
  shows "{Ff1(v1) where v1 be ElementSUBSET-1M1-of Bf0 : Pp1(v1) } =XBOOLE-0R4 {Gf1(v2) where v2 be ElementSUBSET-1M1-of Bf0 : Pp1(v2) }"
sorry

theorem fraenkel_sch_6:
  fixes Bf0 Ff1 Gf1 Pp1 
  assumes
[ty]: "Bf0 be setHIDDENM2" and
  [ty_func]: "\<And> x1. x1 be objectHIDDENM1 \<Longrightarrow> Ff1(x1) be objectHIDDENM1" and
  [ty_func]: "\<And> x1. x1 be objectHIDDENM1 \<Longrightarrow> Gf1(x1) be objectHIDDENM1" and
   A1: " for v be ElementSUBSET-1M1-of Bf0 holds Pp1(v) implies Ff1(v) =HIDDENR1 Gf1(v)"
  shows "{Ff1(v1) where v1 be ElementSUBSET-1M1-of Bf0 : Pp1(v1) } =XBOOLE-0R4 {Gf1(v2) where v2 be ElementSUBSET-1M1-of Bf0 : Pp1(v2) }"
sorry

theorem fraenkel_sch_7:
  fixes Af0 Bf0 Ff2 Gf2 Pp2 
  assumes
[ty]: "Af0 be setHIDDENM2" and
  [ty]: "Bf0 be setHIDDENM2" and
  [ty_func]: "\<And> x1 x2. x1 be objectHIDDENM1 \<Longrightarrow> x2 be objectHIDDENM1 \<Longrightarrow> Ff2(x1,x2) be objectHIDDENM1" and
  [ty_func]: "\<And> x1 x2. x1 be objectHIDDENM1 \<Longrightarrow> x2 be objectHIDDENM1 \<Longrightarrow> Gf2(x1,x2) be objectHIDDENM1" and
   A1: " for u be ElementSUBSET-1M1-of Af0 holds  for v be ElementSUBSET-1M1-of Bf0 holds Ff2(u,v) =HIDDENR1 Gf2(u,v)"
  shows "{Ff2(u1,v1) where u1 be ElementSUBSET-1M1-of Af0, v1 be ElementSUBSET-1M1-of Bf0 : Pp2(u1,v1) } =XBOOLE-0R4 {Gf2(u2,v2) where u2 be ElementSUBSET-1M1-of Af0, v2 be ElementSUBSET-1M1-of Bf0 : Pp2(u2,v2) }"
sorry

theorem fraenkel_sch_8:
  fixes Af0 Bf0 Ff2 Pp2 Qp2 
  assumes
[ty]: "Af0 be setHIDDENM2" and
  [ty]: "Bf0 be setHIDDENM2" and
  [ty_func]: "\<And> x1 x2. x1 be objectHIDDENM1 \<Longrightarrow> x2 be objectHIDDENM1 \<Longrightarrow> Ff2(x1,x2) be objectHIDDENM1" and
   A1: " for u be ElementSUBSET-1M1-of Af0 holds  for v be ElementSUBSET-1M1-of Bf0 holds Pp2(u,v) iff Qp2(u,v)" and
   A2: " for u be ElementSUBSET-1M1-of Af0 holds  for v be ElementSUBSET-1M1-of Bf0 holds Ff2(u,v) =HIDDENR1 Ff2(v,u)"
  shows "{Ff2(u1,v1) where u1 be ElementSUBSET-1M1-of Af0, v1 be ElementSUBSET-1M1-of Bf0 : Pp2(u1,v1) } =XBOOLE-0R4 {Ff2(v2,u2) where u2 be ElementSUBSET-1M1-of Af0, v2 be ElementSUBSET-1M1-of Bf0 : Qp2(u2,v2) }"
sorry

mtheorem fraenkel_th_1:
" for A be setHIDDENM2 holds  for B be setHIDDENM2 holds  for F be FunctionFUNCT-2M1-of(A,B) holds  for G be FunctionFUNCT-2M1-of(A,B) holds  for X be setHIDDENM2 holds F |PARTFUN1K2\<^bsub>(A,B)\<^esub> X =RELSET-1R2\<^bsub>(A,B)\<^esub> G |PARTFUN1K2\<^bsub>(A,B)\<^esub> X implies ( for x be ElementSUBSET-1M1-of A holds x inTARSKIR2 X implies F .FUNCT-1K1 x =XBOOLE-0R4 G .FUNCT-1K1 x)"
sorry

mtheorem fraenkel_th_2:
" for A be setHIDDENM2 holds  for B be setHIDDENM2 holds FuncsFUNCT-2K1(A,B) c=TARSKIR1 boolZFMISC-1K1 ([:ZFMISC-1K2 A,B :])"
sorry

mtheorem fraenkel_th_3:
" for B be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for A be setHIDDENM2 holds  for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds (FuncsFUNCT-2K1(X,Y) <>HIDDENR2 {}XBOOLE-0K1 & X c=TARSKIR1 A) & Y c=TARSKIR1 B implies ( for f be ElementSUBSET-1M1-of FuncsFUNCT-2K1(X,Y) holds f be PartFuncPARTFUN1M1-of(A,B))"
sorry

theorem fraenkel_sch_9:
  fixes Af0 Bf0 Xf0 ff0 gf0 Pp1 Qp1 
  assumes
[ty]: "Af0 be setHIDDENM2" and
  [ty]: "Bf0 be setHIDDENM2" and
  [ty]: "Xf0 be setHIDDENM2" and
  [ty]: "ff0 be FunctionFUNCT-2M1-of(Af0,Bf0)" and
  [ty]: "gf0 be FunctionFUNCT-2M1-of(Af0,Bf0)" and
   A1: "ff0 |PARTFUN1K2\<^bsub>(Af0,Bf0)\<^esub> Xf0 =RELSET-1R2\<^bsub>(Af0,Bf0)\<^esub> gf0 |PARTFUN1K2\<^bsub>(Af0,Bf0)\<^esub> Xf0" and
   A2: " for u be ElementSUBSET-1M1-of Af0 holds u inTARSKIR2 Xf0 implies (Pp1(u) iff Qp1(u))"
  shows "{ff0 .FUNCT-1K1 u9 where u9 be ElementSUBSET-1M1-of Af0 : Pp1(u9) & u9 inTARSKIR2 Xf0 } =XBOOLE-0R4 {gf0 .FUNCT-1K1 v9 where v9 be ElementSUBSET-1M1-of Af0 : Qp1(v9) & v9 inTARSKIR2 Xf0 }"
sorry

theorem fraenkel_sch_10:
  fixes Af0 Pp1 
  assumes
[ty]: "Af0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
  shows "{x where x be ElementSUBSET-1M1-of Af0 : Pp1(x) } c=TARSKIR1 Af0"
sorry

theorem fraenkel_sch_11:
  fixes Af0 Bf0 Ff2 Pp2 Qp1 
  assumes
[ty]: "Af0 be setHIDDENM2" and
  [ty]: "Bf0 be setHIDDENM2" and
  [ty_func]: "\<And> x1 x2. x1 be objectHIDDENM1 \<Longrightarrow> x2 be objectHIDDENM1 \<Longrightarrow> Ff2(x1,x2) be objectHIDDENM1" and
   A1: " for st1 be setHIDDENM2 holds st1 inTARSKIR2 {Ff2(s1,t1) where s1 be ElementSUBSET-1M1-of Af0, t1 be ElementSUBSET-1M1-of Bf0 : Pp2(s1,t1) } implies Qp1(st1)"
  shows " for s be ElementSUBSET-1M1-of Af0 holds  for t be ElementSUBSET-1M1-of Bf0 holds Pp2(s,t) implies Qp1(Ff2(s,t))"
sorry

theorem fraenkel_sch_12:
  fixes Af0 Bf0 Ff2 Pp2 Qp1 
  assumes
[ty]: "Af0 be setHIDDENM2" and
  [ty]: "Bf0 be setHIDDENM2" and
  [ty_func]: "\<And> x1 x2. x1 be objectHIDDENM1 \<Longrightarrow> x2 be objectHIDDENM1 \<Longrightarrow> Ff2(x1,x2) be objectHIDDENM1" and
   A1: " for s be ElementSUBSET-1M1-of Af0 holds  for t be ElementSUBSET-1M1-of Bf0 holds Pp2(s,t) implies Qp1(Ff2(s,t))"
  shows " for st1 be setHIDDENM2 holds st1 inTARSKIR2 {Ff2(s1,t1) where s1 be ElementSUBSET-1M1-of Af0, t1 be ElementSUBSET-1M1-of Bf0 : Pp2(s1,t1) } implies Qp1(st1)"
sorry

theorem fraenkel_sch_13:
  fixes Af0 Bf0 Cf0 Ff2 Pp2 Qp1 
  assumes
[ty]: "Af0 be setHIDDENM2" and
  [ty]: "Bf0 be setHIDDENM2" and
  [ty]: "Cf0 be setHIDDENM2" and
  [ty_func]: "\<And> x1 x2. x1 be objectHIDDENM1 \<Longrightarrow> x2 be objectHIDDENM1 \<Longrightarrow> Ff2(x1,x2) be ElementSUBSET-1M1-of Cf0"
  shows "{st1 where st1 be ElementSUBSET-1M1-of Cf0 : st1 inTARSKIR2 {Ff2(s1,t1) where s1 be ElementSUBSET-1M1-of Af0, t1 be ElementSUBSET-1M1-of Bf0 : Pp2(s1,t1) } & Qp1(st1) } =XBOOLE-0R4 {Ff2(s2,t2) where s2 be ElementSUBSET-1M1-of Af0, t2 be ElementSUBSET-1M1-of Bf0 : Pp2(s2,t2) & Qp1(Ff2(s2,t2)) }"
sorry

theorem fraenkel_sch_14:
  fixes Af0 Ff1 Pp1 Qp1 
  assumes
[ty]: "Af0 be setHIDDENM2" and
  [ty_func]: "\<And> x1. x1 be objectHIDDENM1 \<Longrightarrow> Ff1(x1) be objectHIDDENM1"
  shows "{Ff1(s) where s be ElementSUBSET-1M1-of Af0 : s inTARSKIR2 {s1 where s1 be ElementSUBSET-1M1-of Af0 : Qp1(s1) } & Pp1(s) } =XBOOLE-0R4 {Ff1(s2) where s2 be ElementSUBSET-1M1-of Af0 : Qp1(s2) & Pp1(s2) }"
sorry

theorem fraenkel_sch_15:
  fixes Af0 Bf0 Ff2 Pp2 Qp1 
  assumes
[ty]: "Af0 be setHIDDENM2" and
  [ty]: "Bf0 be setHIDDENM2" and
  [ty_func]: "\<And> x1 x2. x1 be objectHIDDENM1 \<Longrightarrow> x2 be objectHIDDENM1 \<Longrightarrow> Ff2(x1,x2) be objectHIDDENM1"
  shows "{Ff2(s,t) where s be ElementSUBSET-1M1-of Af0, t be ElementSUBSET-1M1-of Bf0 : s inTARSKIR2 {s1 where s1 be ElementSUBSET-1M1-of Af0 : Qp1(s1) } & Pp2(s,t) } =XBOOLE-0R4 {Ff2(s2,t2) where s2 be ElementSUBSET-1M1-of Af0, t2 be ElementSUBSET-1M1-of Bf0 : Qp1(s2) & Pp2(s2,t2) }"
sorry

theorem fraenkel_sch_16:
  fixes Af0 Bf0 Ff2 Pp2 Qp2 
  assumes
[ty]: "Af0 be setHIDDENM2" and
  [ty]: "Bf0 be setHIDDENM2" and
  [ty_func]: "\<And> x1 x2. x1 be objectHIDDENM1 \<Longrightarrow> x2 be objectHIDDENM1 \<Longrightarrow> Ff2(x1,x2) be objectHIDDENM1" and
   A1: " for s be ElementSUBSET-1M1-of Af0 holds  for t be ElementSUBSET-1M1-of Bf0 holds Pp2(s,t) implies ( ex s9 be ElementSUBSET-1M1-of Af0 st Qp2(s9,t) & Ff2(s,t) =HIDDENR1 Ff2(s9,t))"
  shows "{Ff2(s,t) where s be ElementSUBSET-1M1-of Af0, t be ElementSUBSET-1M1-of Bf0 : Pp2(s,t) } c=TARSKIR1 {Ff2(s1,t1) where s1 be ElementSUBSET-1M1-of Af0, t1 be ElementSUBSET-1M1-of Bf0 : Qp2(s1,t1) }"
sorry

theorem fraenkel_sch_17:
  fixes Df0 Af0 Ff1 Pp1 
  assumes
[ty]: "Df0 be setHIDDENM2" and
  [ty]: "Af0 be setHIDDENM2" and
  [ty_func]: "\<And> x1. x1 be objectHIDDENM1 \<Longrightarrow> Ff1(x1) be objectHIDDENM1"
  shows "{Ff1(y) where y be ElementSUBSET-1M1-of Df0 : Ff1(y) inHIDDENR3 Af0 & Pp1(y) } c=TARSKIR1 Af0"
sorry

theorem fraenkel_sch_18:
  fixes Df0 Af0 Ff1 Qp1 
  assumes
[ty]: "Df0 be setHIDDENM2" and
  [ty]: "Af0 be setHIDDENM2" and
  [ty_func]: "\<And> x1. x1 be objectHIDDENM1 \<Longrightarrow> Ff1(x1) be objectHIDDENM1"
  shows "{Ff1(y) where y be ElementSUBSET-1M1-of Df0 : Qp1(y) &  not Ff1(y) inHIDDENR3 Af0 } missesXBOOLE-0R1 Af0"
sorry

theorem fraenkel_sch_19:
  fixes Af0 Bf0 Ff2 xf0 Pp2 Qp2 
  assumes
[ty]: "Af0 be setHIDDENM2" and
  [ty]: "Bf0 be setHIDDENM2" and
  [ty_func]: "\<And> x1 x2. x1 be objectHIDDENM1 \<Longrightarrow> x2 be objectHIDDENM1 \<Longrightarrow> Ff2(x1,x2) be objectHIDDENM1" and
  [ty]: "xf0 be ElementSUBSET-1M1-of Bf0" and
   A1: " for s be ElementSUBSET-1M1-of Af0 holds  for t be ElementSUBSET-1M1-of Bf0 holds Qp2(s,t) iff t =XBOOLE-0R4 xf0 & Pp2(s,t)"
  shows "{Ff2(s,t) where s be ElementSUBSET-1M1-of Af0, t be ElementSUBSET-1M1-of Bf0 : Qp2(s,t) } =XBOOLE-0R4 {Ff2(s9,xf0) where s9 be ElementSUBSET-1M1-of Af0 : Pp2(s9,xf0) }"
sorry

theorem fraenkel_sch_20:
  fixes Af0 Bf0 Ff2 xf0 Pp2 
  assumes
[ty]: "Af0 be setHIDDENM2" and
  [ty]: "Bf0 be setHIDDENM2" and
  [ty_func]: "\<And> x1 x2. x1 be objectHIDDENM1 \<Longrightarrow> x2 be objectHIDDENM1 \<Longrightarrow> Ff2(x1,x2) be objectHIDDENM1" and
  [ty]: "xf0 be ElementSUBSET-1M1-of Bf0"
  shows "{Ff2(s,t) where s be ElementSUBSET-1M1-of Af0, t be ElementSUBSET-1M1-of Bf0 : t =XBOOLE-0R4 xf0 & Pp2(s,t) } =XBOOLE-0R4 {Ff2(s9,xf0) where s9 be ElementSUBSET-1M1-of Af0 : Pp2(s9,xf0) }"
sorry

reserve phi for "ElementFUNCT-2M4\<^bsub>(A,B)\<^esub>-of FuncsFUNCT-2K9(A,B)"
mtheorem fraenkel_th_4:
" for B be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for A be setHIDDENM2 holds  for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds (FuncsFUNCT-2K1(X,Y) <>HIDDENR2 {}XBOOLE-0K1 & X c=TARSKIR1 A) & Y c=TARSKIR1 B implies ( for f be ElementSUBSET-1M1-of FuncsFUNCT-2K1(X,Y) holds  ex phi be ElementFUNCT-2M4\<^bsub>(A,B)\<^esub>-of FuncsFUNCT-2K9(A,B) st phi |PARTFUN1K2\<^bsub>(A,B)\<^esub> X =XBOOLE-0R4 f)"
sorry

mtheorem fraenkel_th_5:
" for B be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for A be setHIDDENM2 holds  for X be setHIDDENM2 holds  for phi be ElementFUNCT-2M4\<^bsub>(A,B)\<^esub>-of FuncsFUNCT-2K9(A,B) holds phi |PARTFUN1K2\<^bsub>(A,B)\<^esub> X =RELSET-1R2\<^bsub>(A,B)\<^esub> phi |PARTFUN1K2\<^bsub>(A,B)\<^esub> (A /\\XBOOLE-0K3 X)"
sorry

theorem fraenkel_sch_21:
  fixes Af0 Xf0 Ff1 
  assumes
[ty]: "Af0 be setHIDDENM2" and
  [ty]: "Xf0 be setHIDDENM2" and
  [ty_func]: "\<And> x1. x1 be objectHIDDENM1 \<Longrightarrow> Ff1(x1) be objectHIDDENM1" and
   A1: "Xf0 be finiteFINSET-1V1"
  shows "{Ff1(w) where w be ElementSUBSET-1M1-of Af0 : w inTARSKIR2 Xf0 } be finiteFINSET-1V1"
sorry

theorem fraenkel_sch_22:
  fixes Af0 Bf0 Xf0 Yf0 Ff2 
  assumes
[ty]: "Af0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
  [ty]: "Bf0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
  [ty]: "Xf0 be setHIDDENM2" and
  [ty]: "Yf0 be setHIDDENM2" and
  [ty_func]: "\<And> x1 x2. x1 be objectHIDDENM1 \<Longrightarrow> x2 be objectHIDDENM1 \<Longrightarrow> Ff2(x1,x2) be objectHIDDENM1" and
   A1: "Xf0 be finiteFINSET-1V1" and
   A2: "Yf0 be finiteFINSET-1V1"
  shows "{Ff2(u,v) where u be ElementSUBSET-1M1-of Af0, v be ElementSUBSET-1M1-of Bf0 : u inTARSKIR2 Xf0 & v inTARSKIR2 Yf0 } be finiteFINSET-1V1"
sorry

theorem fraenkel_sch_23:
  fixes Af0 Bf0 Pp2 
  assumes
[ty]: "Af0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
  [ty]: "Bf0 be ElementSUBSET-1M1-of FinFINSUB-1K5 Af0" and
   A1: " for x be ElementSUBSET-1M1-of Af0 holds Pp2(x,x)" and
   A2: " for x be ElementSUBSET-1M1-of Af0 holds  for y be ElementSUBSET-1M1-of Af0 holds  for z be ElementSUBSET-1M1-of Af0 holds Pp2(x,y) & Pp2(y,z) implies Pp2(x,z)"
  shows " for x be ElementSUBSET-1M1-of Af0 holds x inTARSKIR2 Bf0 implies ( ex y be ElementSUBSET-1M1-of Af0 st (y inTARSKIR2 Bf0 & Pp2(y,x)) & ( for z be ElementSUBSET-1M1-of Af0 holds z inTARSKIR2 Bf0 & Pp2(z,y) implies Pp2(y,z)))"
sorry

theorem fraenkel_sch_24:
  fixes Af0 Bf0 xf0 Ff1 Pp2 
  assumes
[ty]: "Af0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
  [ty]: "Bf0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
  [ty]: "xf0 be ElementSUBSET-1M1-of FinFINSUB-1K5 Bf0" and
  [ty_func]: "\<And> x1. x1 be objectHIDDENM1 \<Longrightarrow> Ff1(x1) be ElementSUBSET-1M1-of Af0"
  shows " ex c1 be ElementSUBSET-1M1-of FinFINSUB-1K5 Af0 st  for t be ElementSUBSET-1M1-of Af0 holds t inTARSKIR2 c1 iff ( ex t9 be ElementSUBSET-1M1-of Bf0 st (t9 inTARSKIR2 xf0 & t =XBOOLE-0R4 Ff1(t9)) & Pp2(t,t9))"
sorry

mtheorem fraenkel_cl_1:
  mlet "A be finiteFINSET-1V1\<bar>setHIDDENM2", "B be finiteFINSET-1V1\<bar>setHIDDENM2"
"cluster FuncsFUNCT-2K1(A,B) as-term-is finiteFINSET-1V1"
proof
(*coherence*)
  show "FuncsFUNCT-2K1(A,B) be finiteFINSET-1V1"
sorry
qed "sorry"

mtheorem fraenkel_th_6:
" for A be setHIDDENM2 holds  for B be setHIDDENM2 holds A be finiteFINSET-1V1 & B be finiteFINSET-1V1 implies FuncsFUNCT-2K1(A,B) be finiteFINSET-1V1"
   sorry

theorem fraenkel_sch_25:
  fixes Af0 Bf0 Xf0 Yf0 Ff1 
  assumes
[ty]: "Af0 be setHIDDENM2" and
  [ty]: "Bf0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
  [ty]: "Xf0 be setHIDDENM2" and
  [ty]: "Yf0 be setHIDDENM2" and
  [ty_func]: "\<And> x1. x1 be objectHIDDENM1 \<Longrightarrow> Ff1(x1) be objectHIDDENM1" and
   A1: "Xf0 be finiteFINSET-1V1" and
   A2: "Yf0 be finiteFINSET-1V1" and
   A3: " for phi be ElementFUNCT-2M4\<^bsub>(Af0,Bf0)\<^esub>-of FuncsFUNCT-2K9(Af0,Bf0) holds  for psi be ElementFUNCT-2M4\<^bsub>(Af0,Bf0)\<^esub>-of FuncsFUNCT-2K9(Af0,Bf0) holds phi |PARTFUN1K2\<^bsub>(Af0,Bf0)\<^esub> Xf0 =RELSET-1R2\<^bsub>(Af0,Bf0)\<^esub> psi |PARTFUN1K2\<^bsub>(Af0,Bf0)\<^esub> Xf0 implies Ff1(phi) =HIDDENR1 Ff1(psi)"
  shows "{Ff1(phi9) where phi9 be ElementFUNCT-2M4\<^bsub>(Af0,Bf0)\<^esub>-of FuncsFUNCT-2K9(Af0,Bf0) : phi9 .:RELSET-1K7\<^bsub>(Af0,Bf0)\<^esub> Xf0 c=TARSKIR1 Yf0 } be finiteFINSET-1V1"
sorry

theorem fraenkel_sch_26:
  fixes Af0 Bf0 xf0 Pp2 
  assumes
[ty]: "Af0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
  [ty]: "Bf0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
  [ty]: "xf0 be ElementSUBSET-1M1-of FinFINSUB-1K5 Af0" and
   A1: " for t be ElementSUBSET-1M1-of Af0 holds t inTARSKIR2 xf0 implies ( ex ff be ElementSUBSET-1M1-of Bf0 st Pp2(t,ff))"
  shows " ex ff be FunctionFUNCT-2M1-of(Af0,Bf0) st  for t be ElementSUBSET-1M1-of Af0 holds t inTARSKIR2 xf0 implies Pp2(t,ff .FUNCT-2K3\<^bsub>(Af0,Bf0)\<^esub> t)"
sorry

theorem fraenkel_sch_27:
  fixes Af0 Bf0 xf0 Pp2 
  assumes
[ty]: "Af0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
  [ty]: "Bf0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
  [ty]: "xf0 be ElementSUBSET-1M1-of FinFINSUB-1K5 Af0" and
   A1: " for t be ElementSUBSET-1M1-of Af0 holds t inTARSKIR2 xf0 implies ( ex ff be ElementSUBSET-1M1-of Bf0 st Pp2(t,ff))"
  shows " ex ff be ElementFUNCT-2M4\<^bsub>(Af0,Bf0)\<^esub>-of FuncsFUNCT-2K9(Af0,Bf0) st  for t be ElementSUBSET-1M1-of Af0 holds t inTARSKIR2 xf0 implies Pp2(t,ff .FUNCT-2K3\<^bsub>(Af0,Bf0)\<^esub> t)"
sorry

theorem fraenkel_sch_28:
  fixes Af0 Bf0 Xf0 Pp2 
  assumes
[ty]: "Af0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
  [ty]: "Bf0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
  [ty]: "Xf0 be setHIDDENM2" and
   A1: "Xf0 be finiteFINSET-1V1" and
   A2: " for w be ElementSUBSET-1M1-of Af0 holds  for x be ElementSUBSET-1M1-of Bf0 holds  for y be ElementSUBSET-1M1-of Bf0 holds Pp2(w,x) & Pp2(w,y) implies x =XBOOLE-0R4 y"
  shows "{x where x be ElementSUBSET-1M1-of Bf0 :  ex w be ElementSUBSET-1M1-of Af0 st Pp2(w,x) & w inTARSKIR2 Xf0 } be finiteFINSET-1V1"
sorry

end
