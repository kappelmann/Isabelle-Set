theory binop_2
  imports setwiseo valued_0
   "../mizar_extension/E_number"
begin
(*begin*)
theorem binop_2_sch_1:
  fixes Cf0 Df0 Ff1 
  assumes
[ty]: "Cf0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
  [ty]: "Df0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
  [ty_func]: "\<And> x1. x1 be ElementSUBSET-1M1-of Cf0 \<Longrightarrow> Ff1(x1) be objectHIDDENM1"
  shows " for f1 be FunctionFUNCT-2M1-of(Cf0,Df0) holds  for f2 be FunctionFUNCT-2M1-of(Cf0,Df0) holds ( for x be ElementSUBSET-1M1-of Cf0 holds f1 .FUNCT-2K3\<^bsub>(Cf0,Df0)\<^esub> x =HIDDENR1 Ff1(x)) & ( for x be ElementSUBSET-1M1-of Cf0 holds f2 .FUNCT-2K3\<^bsub>(Cf0,Df0)\<^esub> x =HIDDENR1 Ff1(x)) implies f1 =FUNCT-2R2\<^bsub>(Cf0,Df0)\<^esub> f2"
sorry

theorem binop_2_sch_2:
  fixes Af0 Of2 
  assumes
[ty]: "Af0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
  [ty_func]: "\<And> x1 x2. x1 be ElementSUBSET-1M1-of Af0 \<Longrightarrow> x2 be ElementSUBSET-1M1-of Af0 \<Longrightarrow> Of2(x1,x2) be objectHIDDENM1"
  shows " for o1 be BinOpBINOP-1M2-of Af0 holds  for o2 be BinOpBINOP-1M2-of Af0 holds ( for a be ElementSUBSET-1M1-of Af0 holds  for b be ElementSUBSET-1M1-of Af0 holds o1 .BINOP-1K4\<^bsub>(Af0)\<^esub>(a,b) =HIDDENR1 Of2(a,b)) & ( for a be ElementSUBSET-1M1-of Af0 holds  for b be ElementSUBSET-1M1-of Af0 holds o2 .BINOP-1K4\<^bsub>(Af0)\<^esub>(a,b) =HIDDENR1 Of2(a,b)) implies o1 =BINOP-1R13\<^bsub>(Af0,Af0,Af0)\<^esub> o2"
sorry

theorem binop_2_sch_3:
  fixes Ff1 
  assumes
[ty_func]: "\<And> x1. x1 be objectHIDDENM1 \<Longrightarrow> Ff1(x1) be objectHIDDENM1"
  shows " for f1 be FunctionFUNCT-2M1-of(COMPLEXNUMBERSK3,COMPLEXNUMBERSK3) holds  for f2 be FunctionFUNCT-2M1-of(COMPLEXNUMBERSK3,COMPLEXNUMBERSK3) holds ( for x be ComplexXCMPLX-0M1 holds f1 .FUNCT-1K1 x =HIDDENR1 Ff1(x)) & ( for x be ComplexXCMPLX-0M1 holds f2 .FUNCT-1K1 x =HIDDENR1 Ff1(x)) implies f1 =FUNCT-2R2\<^bsub>(COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> f2"
sorry

theorem binop_2_sch_4:
  fixes Ff1 
  assumes
[ty_func]: "\<And> x1. x1 be RealXREAL-0M1 \<Longrightarrow> Ff1(x1) be objectHIDDENM1"
  shows " for f1 be FunctionFUNCT-2M1-of(REALNUMBERSK2,REALNUMBERSK2) holds  for f2 be FunctionFUNCT-2M1-of(REALNUMBERSK2,REALNUMBERSK2) holds ( for x be RealXREAL-0M1 holds f1 .FUNCT-1K1 x =HIDDENR1 Ff1(x)) & ( for x be RealXREAL-0M1 holds f2 .FUNCT-1K1 x =HIDDENR1 Ff1(x)) implies f1 =FUNCT-2R2\<^bsub>(REALNUMBERSK2,REALNUMBERSK2)\<^esub> f2"
sorry

mtheorem binop_2_cl_1:
"cluster note-that rationalRAT-1V1 for ElementSUBSET-1M1-of RATRAT-1K1"
proof
(*coherence*)
  show " for it be ElementSUBSET-1M1-of RATRAT-1K1 holds it be rationalRAT-1V1"
    using rat_1_def_2 sorry
qed "sorry"

theorem binop_2_sch_5:
  fixes Ff1 
  assumes
[ty_func]: "\<And> x1. x1 be RationalRAT-1M1 \<Longrightarrow> Ff1(x1) be objectHIDDENM1"
  shows " for f1 be FunctionFUNCT-2M1-of(RATRAT-1K1,RATRAT-1K1) holds  for f2 be FunctionFUNCT-2M1-of(RATRAT-1K1,RATRAT-1K1) holds ( for x be RationalRAT-1M1 holds f1 .FUNCT-1K1 x =HIDDENR1 Ff1(x)) & ( for x be RationalRAT-1M1 holds f2 .FUNCT-1K1 x =HIDDENR1 Ff1(x)) implies f1 =FUNCT-2R2\<^bsub>(RATRAT-1K1,RATRAT-1K1)\<^esub> f2"
sorry

theorem binop_2_sch_6:
  fixes Ff1 
  assumes
[ty_func]: "\<And> x1. x1 be IntegerINT-1M1 \<Longrightarrow> Ff1(x1) be objectHIDDENM1"
  shows " for f1 be FunctionFUNCT-2M1-of(INTNUMBERSK5,INTNUMBERSK5) holds  for f2 be FunctionFUNCT-2M1-of(INTNUMBERSK5,INTNUMBERSK5) holds ( for x be IntegerINT-1M1 holds f1 .FUNCT-1K1 x =HIDDENR1 Ff1(x)) & ( for x be IntegerINT-1M1 holds f2 .FUNCT-1K1 x =HIDDENR1 Ff1(x)) implies f1 =FUNCT-2R2\<^bsub>(INTNUMBERSK5,INTNUMBERSK5)\<^esub> f2"
sorry

theorem binop_2_sch_7:
  fixes Ff1 
  assumes
[ty_func]: "\<And> x1. x1 be NatNAT-1M1 \<Longrightarrow> Ff1(x1) be objectHIDDENM1"
  shows " for f1 be sequenceNAT-1M2-of NATNUMBERSK1 holds  for f2 be sequenceNAT-1M2-of NATNUMBERSK1 holds ( for x be NatNAT-1M1 holds f1 .NAT-1K8\<^bsub>(NATNUMBERSK1)\<^esub> x =HIDDENR1 Ff1(x)) & ( for x be NatNAT-1M1 holds f2 .NAT-1K8\<^bsub>(NATNUMBERSK1)\<^esub> x =HIDDENR1 Ff1(x)) implies f1 =FUNCT-2R2\<^bsub>(NATNUMBERSK1,NATNUMBERSK1)\<^esub> f2"
sorry

theorem binop_2_sch_8:
  fixes Of2 
  assumes
[ty_func]: "\<And> x1 x2. x1 be ComplexXCMPLX-0M1 \<Longrightarrow> x2 be ComplexXCMPLX-0M1 \<Longrightarrow> Of2(x1,x2) be objectHIDDENM1"
  shows " for o1 be BinOpBINOP-1M2-of COMPLEXNUMBERSK3 holds  for o2 be BinOpBINOP-1M2-of COMPLEXNUMBERSK3 holds ( for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds o1 .BINOP-1K1(a,b) =HIDDENR1 Of2(a,b)) & ( for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds o2 .BINOP-1K1(a,b) =HIDDENR1 Of2(a,b)) implies o1 =BINOP-1R13\<^bsub>(COMPLEXNUMBERSK3,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> o2"
sorry

theorem binop_2_sch_9:
  fixes Of2 
  assumes
[ty_func]: "\<And> x1 x2. x1 be RealXREAL-0M1 \<Longrightarrow> x2 be RealXREAL-0M1 \<Longrightarrow> Of2(x1,x2) be objectHIDDENM1"
  shows " for o1 be BinOpBINOP-1M2-of REALNUMBERSK2 holds  for o2 be BinOpBINOP-1M2-of REALNUMBERSK2 holds ( for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds o1 .BINOP-1K1(a,b) =HIDDENR1 Of2(a,b)) & ( for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds o2 .BINOP-1K1(a,b) =HIDDENR1 Of2(a,b)) implies o1 =BINOP-1R13\<^bsub>(REALNUMBERSK2,REALNUMBERSK2,REALNUMBERSK2)\<^esub> o2"
sorry

theorem binop_2_sch_10:
  fixes Of2 
  assumes
[ty_func]: "\<And> x1 x2. x1 be RationalRAT-1M1 \<Longrightarrow> x2 be RationalRAT-1M1 \<Longrightarrow> Of2(x1,x2) be objectHIDDENM1"
  shows " for o1 be BinOpBINOP-1M2-of RATRAT-1K1 holds  for o2 be BinOpBINOP-1M2-of RATRAT-1K1 holds ( for a be RationalRAT-1M1 holds  for b be RationalRAT-1M1 holds o1 .BINOP-1K1(a,b) =HIDDENR1 Of2(a,b)) & ( for a be RationalRAT-1M1 holds  for b be RationalRAT-1M1 holds o2 .BINOP-1K1(a,b) =HIDDENR1 Of2(a,b)) implies o1 =BINOP-1R13\<^bsub>(RATRAT-1K1,RATRAT-1K1,RATRAT-1K1)\<^esub> o2"
sorry

theorem binop_2_sch_11:
  fixes Of2 
  assumes
[ty_func]: "\<And> x1 x2. x1 be IntegerINT-1M1 \<Longrightarrow> x2 be IntegerINT-1M1 \<Longrightarrow> Of2(x1,x2) be objectHIDDENM1"
  shows " for o1 be BinOpBINOP-1M2-of INTNUMBERSK5 holds  for o2 be BinOpBINOP-1M2-of INTNUMBERSK5 holds ( for a be IntegerINT-1M1 holds  for b be IntegerINT-1M1 holds o1 .BINOP-1K1(a,b) =HIDDENR1 Of2(a,b)) & ( for a be IntegerINT-1M1 holds  for b be IntegerINT-1M1 holds o2 .BINOP-1K1(a,b) =HIDDENR1 Of2(a,b)) implies o1 =BINOP-1R13\<^bsub>(INTNUMBERSK5,INTNUMBERSK5,INTNUMBERSK5)\<^esub> o2"
sorry

theorem binop_2_sch_12:
  fixes Of2 
  assumes
[ty_func]: "\<And> x1 x2. x1 be NatNAT-1M1 \<Longrightarrow> x2 be NatNAT-1M1 \<Longrightarrow> Of2(x1,x2) be objectHIDDENM1"
  shows " for o1 be BinOpBINOP-1M2-of NATNUMBERSK1 holds  for o2 be BinOpBINOP-1M2-of NATNUMBERSK1 holds ( for a be NatNAT-1M1 holds  for b be NatNAT-1M1 holds o1 .BINOP-1K1(a,b) =HIDDENR1 Of2(a,b)) & ( for a be NatNAT-1M1 holds  for b be NatNAT-1M1 holds o2 .BINOP-1K1(a,b) =HIDDENR1 Of2(a,b)) implies o1 =BINOP-1R13\<^bsub>(NATNUMBERSK1,NATNUMBERSK1,NATNUMBERSK1)\<^esub> o2"
sorry

theorem binop_2_sch_13:
  fixes Ff2 
  assumes
[ty_func]: "\<And> x1 x2. x1 be ComplexXCMPLX-0M1 \<Longrightarrow> x2 be ComplexXCMPLX-0M1 \<Longrightarrow> Ff2(x1,x2) be ComplexXCMPLX-0M1"
  shows " ex f be FunctionFUNCT-2M1-of([:ZFMISC-1K2 COMPLEXNUMBERSK3,COMPLEXNUMBERSK3 :],COMPLEXNUMBERSK3) st  for x be ComplexXCMPLX-0M1 holds  for y be ComplexXCMPLX-0M1 holds f .BINOP-1K1(x,y) =HIDDENR1 Ff2(x,y)"
sorry

theorem binop_2_sch_14:
  fixes Ff2 
  assumes
[ty_func]: "\<And> x1 x2. x1 be RealXREAL-0M1 \<Longrightarrow> x2 be RealXREAL-0M1 \<Longrightarrow> Ff2(x1,x2) be RealXREAL-0M1"
  shows " ex f be FunctionFUNCT-2M1-of([:ZFMISC-1K2 REALNUMBERSK2,REALNUMBERSK2 :],REALNUMBERSK2) st  for x be RealXREAL-0M1 holds  for y be RealXREAL-0M1 holds f .BINOP-1K1(x,y) =HIDDENR1 Ff2(x,y)"
sorry

theorem binop_2_sch_15:
  fixes Ff2 
  assumes
[ty_func]: "\<And> x1 x2. x1 be RationalRAT-1M1 \<Longrightarrow> x2 be RationalRAT-1M1 \<Longrightarrow> Ff2(x1,x2) be RationalRAT-1M1"
  shows " ex f be FunctionFUNCT-2M1-of([:ZFMISC-1K2 RATRAT-1K1,RATRAT-1K1 :],RATRAT-1K1) st  for x be RationalRAT-1M1 holds  for y be RationalRAT-1M1 holds f .BINOP-1K1(x,y) =HIDDENR1 Ff2(x,y)"
sorry

theorem binop_2_sch_16:
  fixes Ff2 
  assumes
[ty_func]: "\<And> x1 x2. x1 be IntegerINT-1M1 \<Longrightarrow> x2 be IntegerINT-1M1 \<Longrightarrow> Ff2(x1,x2) be IntegerINT-1M1"
  shows " ex f be FunctionFUNCT-2M1-of([:ZFMISC-1K2 INTNUMBERSK5,INTNUMBERSK5 :],INTNUMBERSK5) st  for x be IntegerINT-1M1 holds  for y be IntegerINT-1M1 holds f .BINOP-1K1(x,y) =HIDDENR1 Ff2(x,y)"
sorry

theorem binop_2_sch_17:
  fixes Ff2 
  assumes
[ty_func]: "\<And> x1 x2. x1 be NatNAT-1M1 \<Longrightarrow> x2 be NatNAT-1M1 \<Longrightarrow> Ff2(x1,x2) be NatNAT-1M1"
  shows " ex f be FunctionFUNCT-2M1-of([:ZFMISC-1K2 NATNUMBERSK1,NATNUMBERSK1 :],NATNUMBERSK1) st  for x be NatNAT-1M1 holds  for y be NatNAT-1M1 holds f .BINOP-1K1(x,y) =XBOOLE-0R4 Ff2(x,y)"
sorry

theorem binop_2_sch_18:
  fixes Ff1 
  assumes
[ty_func]: "\<And> x1. x1 be ComplexXCMPLX-0M1 \<Longrightarrow> Ff1(x1) be ComplexXCMPLX-0M1"
  shows " ex f be FunctionFUNCT-2M1-of(COMPLEXNUMBERSK3,COMPLEXNUMBERSK3) st  for x be ComplexXCMPLX-0M1 holds f .FUNCT-1K1 x =HIDDENR1 Ff1(x)"
sorry

theorem binop_2_sch_19:
  fixes Ff1 
  assumes
[ty_func]: "\<And> x1. x1 be RealXREAL-0M1 \<Longrightarrow> Ff1(x1) be RealXREAL-0M1"
  shows " ex f be FunctionFUNCT-2M1-of(REALNUMBERSK2,REALNUMBERSK2) st  for x be RealXREAL-0M1 holds f .FUNCT-1K1 x =HIDDENR1 Ff1(x)"
sorry

theorem binop_2_sch_20:
  fixes Ff1 
  assumes
[ty_func]: "\<And> x1. x1 be RationalRAT-1M1 \<Longrightarrow> Ff1(x1) be RationalRAT-1M1"
  shows " ex f be FunctionFUNCT-2M1-of(RATRAT-1K1,RATRAT-1K1) st  for x be RationalRAT-1M1 holds f .FUNCT-1K1 x =HIDDENR1 Ff1(x)"
sorry

theorem binop_2_sch_21:
  fixes Ff1 
  assumes
[ty_func]: "\<And> x1. x1 be IntegerINT-1M1 \<Longrightarrow> Ff1(x1) be IntegerINT-1M1"
  shows " ex f be FunctionFUNCT-2M1-of(INTNUMBERSK5,INTNUMBERSK5) st  for x be IntegerINT-1M1 holds f .FUNCT-1K1 x =HIDDENR1 Ff1(x)"
sorry

theorem binop_2_sch_22:
  fixes Ff1 
  assumes
[ty_func]: "\<And> x1. x1 be NatNAT-1M1 \<Longrightarrow> Ff1(x1) be NatNAT-1M1"
  shows " ex f be sequenceNAT-1M2-of NATNUMBERSK1 st  for x be NatNAT-1M1 holds f .NAT-1K8\<^bsub>(NATNUMBERSK1)\<^esub> x =XBOOLE-0R4 Ff1(x)"
sorry

reserve c, c1, c2 for "ComplexXCMPLX-0M1"
reserve r, r1, r2 for "RealXREAL-0M1"
reserve w, w1, w2 for "RationalRAT-1M1"
reserve i, i1, i2 for "IntegerINT-1M1"
reserve n1, n2 for "NatNAT-1M1"
mdef binop_2_def_1 ("compcomplexBINOP-2K1" 228 ) where
"func compcomplexBINOP-2K1 \<rightarrow> UnOpBINOP-1M1-of COMPLEXNUMBERSK3 means
  \<lambda>it.  for c be ComplexXCMPLX-0M1 holds it .FUNCT-1K1 c =HIDDENR1 -XCMPLX-0K4 c"
proof-
  (*existence*)
    show " ex it be UnOpBINOP-1M1-of COMPLEXNUMBERSK3 st  for c be ComplexXCMPLX-0M1 holds it .FUNCT-1K1 c =HIDDENR1 -XCMPLX-0K4 c"
      using binop_2_sch_18 sorry
  (*uniqueness*)
    show " for it1 be UnOpBINOP-1M1-of COMPLEXNUMBERSK3 holds  for it2 be UnOpBINOP-1M1-of COMPLEXNUMBERSK3 holds ( for c be ComplexXCMPLX-0M1 holds it1 .FUNCT-1K1 c =HIDDENR1 -XCMPLX-0K4 c) & ( for c be ComplexXCMPLX-0M1 holds it2 .FUNCT-1K1 c =HIDDENR1 -XCMPLX-0K4 c) implies it1 =HIDDENR1 it2"
      using binop_2_sch_3 sorry
qed "sorry"

mdef binop_2_def_2 ("invcomplexBINOP-2K2" 164 ) where
"func invcomplexBINOP-2K2 \<rightarrow> UnOpBINOP-1M1-of COMPLEXNUMBERSK3 means
  \<lambda>it.  for c be ComplexXCMPLX-0M1 holds it .FUNCT-1K1 c =HIDDENR1 c \<inverse>XCMPLX-0K5"
proof-
  (*existence*)
    show " ex it be UnOpBINOP-1M1-of COMPLEXNUMBERSK3 st  for c be ComplexXCMPLX-0M1 holds it .FUNCT-1K1 c =HIDDENR1 c \<inverse>XCMPLX-0K5"
      using binop_2_sch_18 sorry
  (*uniqueness*)
    show " for it1 be UnOpBINOP-1M1-of COMPLEXNUMBERSK3 holds  for it2 be UnOpBINOP-1M1-of COMPLEXNUMBERSK3 holds ( for c be ComplexXCMPLX-0M1 holds it1 .FUNCT-1K1 c =HIDDENR1 c \<inverse>XCMPLX-0K5) & ( for c be ComplexXCMPLX-0M1 holds it2 .FUNCT-1K1 c =HIDDENR1 c \<inverse>XCMPLX-0K5) implies it1 =HIDDENR1 it2"
      using binop_2_sch_3 sorry
qed "sorry"

mdef binop_2_def_3 ("addcomplexBINOP-2K3" 228 ) where
"func addcomplexBINOP-2K3 \<rightarrow> BinOpBINOP-1M2-of COMPLEXNUMBERSK3 means
  \<lambda>it.  for c1 be ComplexXCMPLX-0M1 holds  for c2 be ComplexXCMPLX-0M1 holds it .BINOP-1K1(c1,c2) =XBOOLE-0R4 c1 +XCMPLX-0K2 c2"
proof-
  (*existence*)
    show " ex it be BinOpBINOP-1M2-of COMPLEXNUMBERSK3 st  for c1 be ComplexXCMPLX-0M1 holds  for c2 be ComplexXCMPLX-0M1 holds it .BINOP-1K1(c1,c2) =XBOOLE-0R4 c1 +XCMPLX-0K2 c2"
      using binop_2_sch_13 sorry
  (*uniqueness*)
    show " for it1 be BinOpBINOP-1M2-of COMPLEXNUMBERSK3 holds  for it2 be BinOpBINOP-1M2-of COMPLEXNUMBERSK3 holds ( for c1 be ComplexXCMPLX-0M1 holds  for c2 be ComplexXCMPLX-0M1 holds it1 .BINOP-1K1(c1,c2) =XBOOLE-0R4 c1 +XCMPLX-0K2 c2) & ( for c1 be ComplexXCMPLX-0M1 holds  for c2 be ComplexXCMPLX-0M1 holds it2 .BINOP-1K1(c1,c2) =XBOOLE-0R4 c1 +XCMPLX-0K2 c2) implies it1 =HIDDENR1 it2"
      using binop_2_sch_8 sorry
qed "sorry"

mdef binop_2_def_4 ("diffcomplexBINOP-2K4" 228 ) where
"func diffcomplexBINOP-2K4 \<rightarrow> BinOpBINOP-1M2-of COMPLEXNUMBERSK3 means
  \<lambda>it.  for c1 be ComplexXCMPLX-0M1 holds  for c2 be ComplexXCMPLX-0M1 holds it .BINOP-1K1(c1,c2) =XBOOLE-0R4 c1 -XCMPLX-0K6 c2"
proof-
  (*existence*)
    show " ex it be BinOpBINOP-1M2-of COMPLEXNUMBERSK3 st  for c1 be ComplexXCMPLX-0M1 holds  for c2 be ComplexXCMPLX-0M1 holds it .BINOP-1K1(c1,c2) =XBOOLE-0R4 c1 -XCMPLX-0K6 c2"
      using binop_2_sch_13 sorry
  (*uniqueness*)
    show " for it1 be BinOpBINOP-1M2-of COMPLEXNUMBERSK3 holds  for it2 be BinOpBINOP-1M2-of COMPLEXNUMBERSK3 holds ( for c1 be ComplexXCMPLX-0M1 holds  for c2 be ComplexXCMPLX-0M1 holds it1 .BINOP-1K1(c1,c2) =XBOOLE-0R4 c1 -XCMPLX-0K6 c2) & ( for c1 be ComplexXCMPLX-0M1 holds  for c2 be ComplexXCMPLX-0M1 holds it2 .BINOP-1K1(c1,c2) =XBOOLE-0R4 c1 -XCMPLX-0K6 c2) implies it1 =HIDDENR1 it2"
      using binop_2_sch_8 sorry
qed "sorry"

mdef binop_2_def_5 ("multcomplexBINOP-2K5" 228 ) where
"func multcomplexBINOP-2K5 \<rightarrow> BinOpBINOP-1M2-of COMPLEXNUMBERSK3 means
  \<lambda>it.  for c1 be ComplexXCMPLX-0M1 holds  for c2 be ComplexXCMPLX-0M1 holds it .BINOP-1K1(c1,c2) =XBOOLE-0R4 c1 *XCMPLX-0K3 c2"
proof-
  (*existence*)
    show " ex it be BinOpBINOP-1M2-of COMPLEXNUMBERSK3 st  for c1 be ComplexXCMPLX-0M1 holds  for c2 be ComplexXCMPLX-0M1 holds it .BINOP-1K1(c1,c2) =XBOOLE-0R4 c1 *XCMPLX-0K3 c2"
      using binop_2_sch_13 sorry
  (*uniqueness*)
    show " for it1 be BinOpBINOP-1M2-of COMPLEXNUMBERSK3 holds  for it2 be BinOpBINOP-1M2-of COMPLEXNUMBERSK3 holds ( for c1 be ComplexXCMPLX-0M1 holds  for c2 be ComplexXCMPLX-0M1 holds it1 .BINOP-1K1(c1,c2) =XBOOLE-0R4 c1 *XCMPLX-0K3 c2) & ( for c1 be ComplexXCMPLX-0M1 holds  for c2 be ComplexXCMPLX-0M1 holds it2 .BINOP-1K1(c1,c2) =XBOOLE-0R4 c1 *XCMPLX-0K3 c2) implies it1 =HIDDENR1 it2"
      using binop_2_sch_8 sorry
qed "sorry"

mdef binop_2_def_6 ("divcomplexBINOP-2K6" 164 ) where
"func divcomplexBINOP-2K6 \<rightarrow> BinOpBINOP-1M2-of COMPLEXNUMBERSK3 means
  \<lambda>it.  for c1 be ComplexXCMPLX-0M1 holds  for c2 be ComplexXCMPLX-0M1 holds it .BINOP-1K1(c1,c2) =XBOOLE-0R4 c1 /XCMPLX-0K7 c2"
proof-
  (*existence*)
    show " ex it be BinOpBINOP-1M2-of COMPLEXNUMBERSK3 st  for c1 be ComplexXCMPLX-0M1 holds  for c2 be ComplexXCMPLX-0M1 holds it .BINOP-1K1(c1,c2) =XBOOLE-0R4 c1 /XCMPLX-0K7 c2"
      using binop_2_sch_13 sorry
  (*uniqueness*)
    show " for it1 be BinOpBINOP-1M2-of COMPLEXNUMBERSK3 holds  for it2 be BinOpBINOP-1M2-of COMPLEXNUMBERSK3 holds ( for c1 be ComplexXCMPLX-0M1 holds  for c2 be ComplexXCMPLX-0M1 holds it1 .BINOP-1K1(c1,c2) =XBOOLE-0R4 c1 /XCMPLX-0K7 c2) & ( for c1 be ComplexXCMPLX-0M1 holds  for c2 be ComplexXCMPLX-0M1 holds it2 .BINOP-1K1(c1,c2) =XBOOLE-0R4 c1 /XCMPLX-0K7 c2) implies it1 =HIDDENR1 it2"
      using binop_2_sch_8 sorry
qed "sorry"

mdef binop_2_def_7 ("comprealBINOP-2K7" 164 ) where
"func comprealBINOP-2K7 \<rightarrow> UnOpBINOP-1M1-of REALNUMBERSK2 means
  \<lambda>it.  for r be RealXREAL-0M1 holds it .FUNCT-1K1 r =HIDDENR1 -XCMPLX-0K4 r"
proof-
  (*existence*)
    show " ex it be UnOpBINOP-1M1-of REALNUMBERSK2 st  for r be RealXREAL-0M1 holds it .FUNCT-1K1 r =HIDDENR1 -XCMPLX-0K4 r"
      using binop_2_sch_19 sorry
  (*uniqueness*)
    show " for it1 be UnOpBINOP-1M1-of REALNUMBERSK2 holds  for it2 be UnOpBINOP-1M1-of REALNUMBERSK2 holds ( for r be RealXREAL-0M1 holds it1 .FUNCT-1K1 r =HIDDENR1 -XCMPLX-0K4 r) & ( for r be RealXREAL-0M1 holds it2 .FUNCT-1K1 r =HIDDENR1 -XCMPLX-0K4 r) implies it1 =HIDDENR1 it2"
      using binop_2_sch_4 sorry
qed "sorry"

mdef binop_2_def_8 ("invrealBINOP-2K8" 164 ) where
"func invrealBINOP-2K8 \<rightarrow> UnOpBINOP-1M1-of REALNUMBERSK2 means
  \<lambda>it.  for r be RealXREAL-0M1 holds it .FUNCT-1K1 r =HIDDENR1 r \<inverse>XCMPLX-0K5"
proof-
  (*existence*)
    show " ex it be UnOpBINOP-1M1-of REALNUMBERSK2 st  for r be RealXREAL-0M1 holds it .FUNCT-1K1 r =HIDDENR1 r \<inverse>XCMPLX-0K5"
      using binop_2_sch_19 sorry
  (*uniqueness*)
    show " for it1 be UnOpBINOP-1M1-of REALNUMBERSK2 holds  for it2 be UnOpBINOP-1M1-of REALNUMBERSK2 holds ( for r be RealXREAL-0M1 holds it1 .FUNCT-1K1 r =HIDDENR1 r \<inverse>XCMPLX-0K5) & ( for r be RealXREAL-0M1 holds it2 .FUNCT-1K1 r =HIDDENR1 r \<inverse>XCMPLX-0K5) implies it1 =HIDDENR1 it2"
      using binop_2_sch_4 sorry
qed "sorry"

mdef binop_2_def_9 ("addrealBINOP-2K9" 164 ) where
"func addrealBINOP-2K9 \<rightarrow> BinOpBINOP-1M2-of REALNUMBERSK2 means
  \<lambda>it.  for r1 be RealXREAL-0M1 holds  for r2 be RealXREAL-0M1 holds it .BINOP-1K1(r1,r2) =XBOOLE-0R4 r1 +XCMPLX-0K2 r2"
proof-
  (*existence*)
    show " ex it be BinOpBINOP-1M2-of REALNUMBERSK2 st  for r1 be RealXREAL-0M1 holds  for r2 be RealXREAL-0M1 holds it .BINOP-1K1(r1,r2) =XBOOLE-0R4 r1 +XCMPLX-0K2 r2"
      using binop_2_sch_14 sorry
  (*uniqueness*)
    show " for it1 be BinOpBINOP-1M2-of REALNUMBERSK2 holds  for it2 be BinOpBINOP-1M2-of REALNUMBERSK2 holds ( for r1 be RealXREAL-0M1 holds  for r2 be RealXREAL-0M1 holds it1 .BINOP-1K1(r1,r2) =XBOOLE-0R4 r1 +XCMPLX-0K2 r2) & ( for r1 be RealXREAL-0M1 holds  for r2 be RealXREAL-0M1 holds it2 .BINOP-1K1(r1,r2) =XBOOLE-0R4 r1 +XCMPLX-0K2 r2) implies it1 =HIDDENR1 it2"
      using binop_2_sch_9 sorry
qed "sorry"

mdef binop_2_def_10 ("diffrealBINOP-2K10" 228 ) where
"func diffrealBINOP-2K10 \<rightarrow> BinOpBINOP-1M2-of REALNUMBERSK2 means
  \<lambda>it.  for r1 be RealXREAL-0M1 holds  for r2 be RealXREAL-0M1 holds it .BINOP-1K1(r1,r2) =XBOOLE-0R4 r1 -XCMPLX-0K6 r2"
proof-
  (*existence*)
    show " ex it be BinOpBINOP-1M2-of REALNUMBERSK2 st  for r1 be RealXREAL-0M1 holds  for r2 be RealXREAL-0M1 holds it .BINOP-1K1(r1,r2) =XBOOLE-0R4 r1 -XCMPLX-0K6 r2"
      using binop_2_sch_14 sorry
  (*uniqueness*)
    show " for it1 be BinOpBINOP-1M2-of REALNUMBERSK2 holds  for it2 be BinOpBINOP-1M2-of REALNUMBERSK2 holds ( for r1 be RealXREAL-0M1 holds  for r2 be RealXREAL-0M1 holds it1 .BINOP-1K1(r1,r2) =XBOOLE-0R4 r1 -XCMPLX-0K6 r2) & ( for r1 be RealXREAL-0M1 holds  for r2 be RealXREAL-0M1 holds it2 .BINOP-1K1(r1,r2) =XBOOLE-0R4 r1 -XCMPLX-0K6 r2) implies it1 =HIDDENR1 it2"
      using binop_2_sch_9 sorry
qed "sorry"

mdef binop_2_def_11 ("multrealBINOP-2K11" 164 ) where
"func multrealBINOP-2K11 \<rightarrow> BinOpBINOP-1M2-of REALNUMBERSK2 means
  \<lambda>it.  for r1 be RealXREAL-0M1 holds  for r2 be RealXREAL-0M1 holds it .BINOP-1K1(r1,r2) =XBOOLE-0R4 r1 *XCMPLX-0K3 r2"
proof-
  (*existence*)
    show " ex it be BinOpBINOP-1M2-of REALNUMBERSK2 st  for r1 be RealXREAL-0M1 holds  for r2 be RealXREAL-0M1 holds it .BINOP-1K1(r1,r2) =XBOOLE-0R4 r1 *XCMPLX-0K3 r2"
      using binop_2_sch_14 sorry
  (*uniqueness*)
    show " for it1 be BinOpBINOP-1M2-of REALNUMBERSK2 holds  for it2 be BinOpBINOP-1M2-of REALNUMBERSK2 holds ( for r1 be RealXREAL-0M1 holds  for r2 be RealXREAL-0M1 holds it1 .BINOP-1K1(r1,r2) =XBOOLE-0R4 r1 *XCMPLX-0K3 r2) & ( for r1 be RealXREAL-0M1 holds  for r2 be RealXREAL-0M1 holds it2 .BINOP-1K1(r1,r2) =XBOOLE-0R4 r1 *XCMPLX-0K3 r2) implies it1 =HIDDENR1 it2"
      using binop_2_sch_9 sorry
qed "sorry"

mdef binop_2_def_12 ("divrealBINOP-2K12" 164 ) where
"func divrealBINOP-2K12 \<rightarrow> BinOpBINOP-1M2-of REALNUMBERSK2 means
  \<lambda>it.  for r1 be RealXREAL-0M1 holds  for r2 be RealXREAL-0M1 holds it .BINOP-1K1(r1,r2) =XBOOLE-0R4 r1 /XCMPLX-0K7 r2"
proof-
  (*existence*)
    show " ex it be BinOpBINOP-1M2-of REALNUMBERSK2 st  for r1 be RealXREAL-0M1 holds  for r2 be RealXREAL-0M1 holds it .BINOP-1K1(r1,r2) =XBOOLE-0R4 r1 /XCMPLX-0K7 r2"
      using binop_2_sch_14 sorry
  (*uniqueness*)
    show " for it1 be BinOpBINOP-1M2-of REALNUMBERSK2 holds  for it2 be BinOpBINOP-1M2-of REALNUMBERSK2 holds ( for r1 be RealXREAL-0M1 holds  for r2 be RealXREAL-0M1 holds it1 .BINOP-1K1(r1,r2) =XBOOLE-0R4 r1 /XCMPLX-0K7 r2) & ( for r1 be RealXREAL-0M1 holds  for r2 be RealXREAL-0M1 holds it2 .BINOP-1K1(r1,r2) =XBOOLE-0R4 r1 /XCMPLX-0K7 r2) implies it1 =HIDDENR1 it2"
      using binop_2_sch_9 sorry
qed "sorry"

mdef binop_2_def_13 ("compratBINOP-2K13" 164 ) where
"func compratBINOP-2K13 \<rightarrow> UnOpBINOP-1M1-of RATRAT-1K1 means
  \<lambda>it.  for w be RationalRAT-1M1 holds it .FUNCT-1K1 w =HIDDENR1 -XCMPLX-0K4 w"
proof-
  (*existence*)
    show " ex it be UnOpBINOP-1M1-of RATRAT-1K1 st  for w be RationalRAT-1M1 holds it .FUNCT-1K1 w =HIDDENR1 -XCMPLX-0K4 w"
      using binop_2_sch_20 sorry
  (*uniqueness*)
    show " for it1 be UnOpBINOP-1M1-of RATRAT-1K1 holds  for it2 be UnOpBINOP-1M1-of RATRAT-1K1 holds ( for w be RationalRAT-1M1 holds it1 .FUNCT-1K1 w =HIDDENR1 -XCMPLX-0K4 w) & ( for w be RationalRAT-1M1 holds it2 .FUNCT-1K1 w =HIDDENR1 -XCMPLX-0K4 w) implies it1 =HIDDENR1 it2"
      using binop_2_sch_5 sorry
qed "sorry"

mdef binop_2_def_14 ("invratBINOP-2K14" 164 ) where
"func invratBINOP-2K14 \<rightarrow> UnOpBINOP-1M1-of RATRAT-1K1 means
  \<lambda>it.  for w be RationalRAT-1M1 holds it .FUNCT-1K1 w =HIDDENR1 w \<inverse>XCMPLX-0K5"
proof-
  (*existence*)
    show " ex it be UnOpBINOP-1M1-of RATRAT-1K1 st  for w be RationalRAT-1M1 holds it .FUNCT-1K1 w =HIDDENR1 w \<inverse>XCMPLX-0K5"
      using binop_2_sch_20 sorry
  (*uniqueness*)
    show " for it1 be UnOpBINOP-1M1-of RATRAT-1K1 holds  for it2 be UnOpBINOP-1M1-of RATRAT-1K1 holds ( for w be RationalRAT-1M1 holds it1 .FUNCT-1K1 w =HIDDENR1 w \<inverse>XCMPLX-0K5) & ( for w be RationalRAT-1M1 holds it2 .FUNCT-1K1 w =HIDDENR1 w \<inverse>XCMPLX-0K5) implies it1 =HIDDENR1 it2"
      using binop_2_sch_5 sorry
qed "sorry"

mdef binop_2_def_15 ("addratBINOP-2K15" 164 ) where
"func addratBINOP-2K15 \<rightarrow> BinOpBINOP-1M2-of RATRAT-1K1 means
  \<lambda>it.  for w1 be RationalRAT-1M1 holds  for w2 be RationalRAT-1M1 holds it .BINOP-1K1(w1,w2) =XBOOLE-0R4 w1 +XCMPLX-0K2 w2"
proof-
  (*existence*)
    show " ex it be BinOpBINOP-1M2-of RATRAT-1K1 st  for w1 be RationalRAT-1M1 holds  for w2 be RationalRAT-1M1 holds it .BINOP-1K1(w1,w2) =XBOOLE-0R4 w1 +XCMPLX-0K2 w2"
      using binop_2_sch_15 sorry
  (*uniqueness*)
    show " for it1 be BinOpBINOP-1M2-of RATRAT-1K1 holds  for it2 be BinOpBINOP-1M2-of RATRAT-1K1 holds ( for w1 be RationalRAT-1M1 holds  for w2 be RationalRAT-1M1 holds it1 .BINOP-1K1(w1,w2) =XBOOLE-0R4 w1 +XCMPLX-0K2 w2) & ( for w1 be RationalRAT-1M1 holds  for w2 be RationalRAT-1M1 holds it2 .BINOP-1K1(w1,w2) =XBOOLE-0R4 w1 +XCMPLX-0K2 w2) implies it1 =HIDDENR1 it2"
      using binop_2_sch_10 sorry
qed "sorry"

mdef binop_2_def_16 ("diffratBINOP-2K16" 164 ) where
"func diffratBINOP-2K16 \<rightarrow> BinOpBINOP-1M2-of RATRAT-1K1 means
  \<lambda>it.  for w1 be RationalRAT-1M1 holds  for w2 be RationalRAT-1M1 holds it .BINOP-1K1(w1,w2) =XBOOLE-0R4 w1 -XCMPLX-0K6 w2"
proof-
  (*existence*)
    show " ex it be BinOpBINOP-1M2-of RATRAT-1K1 st  for w1 be RationalRAT-1M1 holds  for w2 be RationalRAT-1M1 holds it .BINOP-1K1(w1,w2) =XBOOLE-0R4 w1 -XCMPLX-0K6 w2"
      using binop_2_sch_15 sorry
  (*uniqueness*)
    show " for it1 be BinOpBINOP-1M2-of RATRAT-1K1 holds  for it2 be BinOpBINOP-1M2-of RATRAT-1K1 holds ( for w1 be RationalRAT-1M1 holds  for w2 be RationalRAT-1M1 holds it1 .BINOP-1K1(w1,w2) =XBOOLE-0R4 w1 -XCMPLX-0K6 w2) & ( for w1 be RationalRAT-1M1 holds  for w2 be RationalRAT-1M1 holds it2 .BINOP-1K1(w1,w2) =XBOOLE-0R4 w1 -XCMPLX-0K6 w2) implies it1 =HIDDENR1 it2"
      using binop_2_sch_10 sorry
qed "sorry"

mdef binop_2_def_17 ("multratBINOP-2K17" 164 ) where
"func multratBINOP-2K17 \<rightarrow> BinOpBINOP-1M2-of RATRAT-1K1 means
  \<lambda>it.  for w1 be RationalRAT-1M1 holds  for w2 be RationalRAT-1M1 holds it .BINOP-1K1(w1,w2) =XBOOLE-0R4 w1 *XCMPLX-0K3 w2"
proof-
  (*existence*)
    show " ex it be BinOpBINOP-1M2-of RATRAT-1K1 st  for w1 be RationalRAT-1M1 holds  for w2 be RationalRAT-1M1 holds it .BINOP-1K1(w1,w2) =XBOOLE-0R4 w1 *XCMPLX-0K3 w2"
      using binop_2_sch_15 sorry
  (*uniqueness*)
    show " for it1 be BinOpBINOP-1M2-of RATRAT-1K1 holds  for it2 be BinOpBINOP-1M2-of RATRAT-1K1 holds ( for w1 be RationalRAT-1M1 holds  for w2 be RationalRAT-1M1 holds it1 .BINOP-1K1(w1,w2) =XBOOLE-0R4 w1 *XCMPLX-0K3 w2) & ( for w1 be RationalRAT-1M1 holds  for w2 be RationalRAT-1M1 holds it2 .BINOP-1K1(w1,w2) =XBOOLE-0R4 w1 *XCMPLX-0K3 w2) implies it1 =HIDDENR1 it2"
      using binop_2_sch_10 sorry
qed "sorry"

mdef binop_2_def_18 ("divratBINOP-2K18" 164 ) where
"func divratBINOP-2K18 \<rightarrow> BinOpBINOP-1M2-of RATRAT-1K1 means
  \<lambda>it.  for w1 be RationalRAT-1M1 holds  for w2 be RationalRAT-1M1 holds it .BINOP-1K1(w1,w2) =XBOOLE-0R4 w1 /XCMPLX-0K7 w2"
proof-
  (*existence*)
    show " ex it be BinOpBINOP-1M2-of RATRAT-1K1 st  for w1 be RationalRAT-1M1 holds  for w2 be RationalRAT-1M1 holds it .BINOP-1K1(w1,w2) =XBOOLE-0R4 w1 /XCMPLX-0K7 w2"
      using binop_2_sch_15 sorry
  (*uniqueness*)
    show " for it1 be BinOpBINOP-1M2-of RATRAT-1K1 holds  for it2 be BinOpBINOP-1M2-of RATRAT-1K1 holds ( for w1 be RationalRAT-1M1 holds  for w2 be RationalRAT-1M1 holds it1 .BINOP-1K1(w1,w2) =XBOOLE-0R4 w1 /XCMPLX-0K7 w2) & ( for w1 be RationalRAT-1M1 holds  for w2 be RationalRAT-1M1 holds it2 .BINOP-1K1(w1,w2) =XBOOLE-0R4 w1 /XCMPLX-0K7 w2) implies it1 =HIDDENR1 it2"
      using binop_2_sch_10 sorry
qed "sorry"

mdef binop_2_def_19 ("compintBINOP-2K19" 164 ) where
"func compintBINOP-2K19 \<rightarrow> UnOpBINOP-1M1-of INTNUMBERSK5 means
  \<lambda>it.  for i be IntegerINT-1M1 holds it .FUNCT-1K1 i =HIDDENR1 -XCMPLX-0K4 i"
proof-
  (*existence*)
    show " ex it be UnOpBINOP-1M1-of INTNUMBERSK5 st  for i be IntegerINT-1M1 holds it .FUNCT-1K1 i =HIDDENR1 -XCMPLX-0K4 i"
      using binop_2_sch_21 sorry
  (*uniqueness*)
    show " for it1 be UnOpBINOP-1M1-of INTNUMBERSK5 holds  for it2 be UnOpBINOP-1M1-of INTNUMBERSK5 holds ( for i be IntegerINT-1M1 holds it1 .FUNCT-1K1 i =HIDDENR1 -XCMPLX-0K4 i) & ( for i be IntegerINT-1M1 holds it2 .FUNCT-1K1 i =HIDDENR1 -XCMPLX-0K4 i) implies it1 =HIDDENR1 it2"
      using binop_2_sch_6 sorry
qed "sorry"

mdef binop_2_def_20 ("addintBINOP-2K20" 164 ) where
"func addintBINOP-2K20 \<rightarrow> BinOpBINOP-1M2-of INTNUMBERSK5 means
  \<lambda>it.  for i1 be IntegerINT-1M1 holds  for i2 be IntegerINT-1M1 holds it .BINOP-1K1(i1,i2) =XBOOLE-0R4 i1 +XCMPLX-0K2 i2"
proof-
  (*existence*)
    show " ex it be BinOpBINOP-1M2-of INTNUMBERSK5 st  for i1 be IntegerINT-1M1 holds  for i2 be IntegerINT-1M1 holds it .BINOP-1K1(i1,i2) =XBOOLE-0R4 i1 +XCMPLX-0K2 i2"
      using binop_2_sch_16 sorry
  (*uniqueness*)
    show " for it1 be BinOpBINOP-1M2-of INTNUMBERSK5 holds  for it2 be BinOpBINOP-1M2-of INTNUMBERSK5 holds ( for i1 be IntegerINT-1M1 holds  for i2 be IntegerINT-1M1 holds it1 .BINOP-1K1(i1,i2) =XBOOLE-0R4 i1 +XCMPLX-0K2 i2) & ( for i1 be IntegerINT-1M1 holds  for i2 be IntegerINT-1M1 holds it2 .BINOP-1K1(i1,i2) =XBOOLE-0R4 i1 +XCMPLX-0K2 i2) implies it1 =HIDDENR1 it2"
      using binop_2_sch_11 sorry
qed "sorry"

mdef binop_2_def_21 ("diffintBINOP-2K21" 164 ) where
"func diffintBINOP-2K21 \<rightarrow> BinOpBINOP-1M2-of INTNUMBERSK5 means
  \<lambda>it.  for i1 be IntegerINT-1M1 holds  for i2 be IntegerINT-1M1 holds it .BINOP-1K1(i1,i2) =XBOOLE-0R4 i1 -XCMPLX-0K6 i2"
proof-
  (*existence*)
    show " ex it be BinOpBINOP-1M2-of INTNUMBERSK5 st  for i1 be IntegerINT-1M1 holds  for i2 be IntegerINT-1M1 holds it .BINOP-1K1(i1,i2) =XBOOLE-0R4 i1 -XCMPLX-0K6 i2"
      using binop_2_sch_16 sorry
  (*uniqueness*)
    show " for it1 be BinOpBINOP-1M2-of INTNUMBERSK5 holds  for it2 be BinOpBINOP-1M2-of INTNUMBERSK5 holds ( for i1 be IntegerINT-1M1 holds  for i2 be IntegerINT-1M1 holds it1 .BINOP-1K1(i1,i2) =XBOOLE-0R4 i1 -XCMPLX-0K6 i2) & ( for i1 be IntegerINT-1M1 holds  for i2 be IntegerINT-1M1 holds it2 .BINOP-1K1(i1,i2) =XBOOLE-0R4 i1 -XCMPLX-0K6 i2) implies it1 =HIDDENR1 it2"
      using binop_2_sch_11 sorry
qed "sorry"

mdef binop_2_def_22 ("multintBINOP-2K22" 164 ) where
"func multintBINOP-2K22 \<rightarrow> BinOpBINOP-1M2-of INTNUMBERSK5 means
  \<lambda>it.  for i1 be IntegerINT-1M1 holds  for i2 be IntegerINT-1M1 holds it .BINOP-1K1(i1,i2) =XBOOLE-0R4 i1 *XCMPLX-0K3 i2"
proof-
  (*existence*)
    show " ex it be BinOpBINOP-1M2-of INTNUMBERSK5 st  for i1 be IntegerINT-1M1 holds  for i2 be IntegerINT-1M1 holds it .BINOP-1K1(i1,i2) =XBOOLE-0R4 i1 *XCMPLX-0K3 i2"
      using binop_2_sch_16 sorry
  (*uniqueness*)
    show " for it1 be BinOpBINOP-1M2-of INTNUMBERSK5 holds  for it2 be BinOpBINOP-1M2-of INTNUMBERSK5 holds ( for i1 be IntegerINT-1M1 holds  for i2 be IntegerINT-1M1 holds it1 .BINOP-1K1(i1,i2) =XBOOLE-0R4 i1 *XCMPLX-0K3 i2) & ( for i1 be IntegerINT-1M1 holds  for i2 be IntegerINT-1M1 holds it2 .BINOP-1K1(i1,i2) =XBOOLE-0R4 i1 *XCMPLX-0K3 i2) implies it1 =HIDDENR1 it2"
      using binop_2_sch_11 sorry
qed "sorry"

mdef binop_2_def_23 ("addnatBINOP-2K23" 164 ) where
"func addnatBINOP-2K23 \<rightarrow> BinOpBINOP-1M2-of NATNUMBERSK1 means
  \<lambda>it.  for n1 be NatNAT-1M1 holds  for n2 be NatNAT-1M1 holds it .BINOP-1K1(n1,n2) =XBOOLE-0R4 n1 +XCMPLX-0K2 n2"
proof-
  (*existence*)
    show " ex it be BinOpBINOP-1M2-of NATNUMBERSK1 st  for n1 be NatNAT-1M1 holds  for n2 be NatNAT-1M1 holds it .BINOP-1K1(n1,n2) =XBOOLE-0R4 n1 +XCMPLX-0K2 n2"
      using binop_2_sch_17 sorry
  (*uniqueness*)
    show " for it1 be BinOpBINOP-1M2-of NATNUMBERSK1 holds  for it2 be BinOpBINOP-1M2-of NATNUMBERSK1 holds ( for n1 be NatNAT-1M1 holds  for n2 be NatNAT-1M1 holds it1 .BINOP-1K1(n1,n2) =XBOOLE-0R4 n1 +XCMPLX-0K2 n2) & ( for n1 be NatNAT-1M1 holds  for n2 be NatNAT-1M1 holds it2 .BINOP-1K1(n1,n2) =XBOOLE-0R4 n1 +XCMPLX-0K2 n2) implies it1 =HIDDENR1 it2"
      using binop_2_sch_12 sorry
qed "sorry"

mdef binop_2_def_24 ("multnatBINOP-2K24" 164 ) where
"func multnatBINOP-2K24 \<rightarrow> BinOpBINOP-1M2-of NATNUMBERSK1 means
  \<lambda>it.  for n1 be NatNAT-1M1 holds  for n2 be NatNAT-1M1 holds it .BINOP-1K1(n1,n2) =XBOOLE-0R4 n1 *XCMPLX-0K3 n2"
proof-
  (*existence*)
    show " ex it be BinOpBINOP-1M2-of NATNUMBERSK1 st  for n1 be NatNAT-1M1 holds  for n2 be NatNAT-1M1 holds it .BINOP-1K1(n1,n2) =XBOOLE-0R4 n1 *XCMPLX-0K3 n2"
      using binop_2_sch_17 sorry
  (*uniqueness*)
    show " for it1 be BinOpBINOP-1M2-of NATNUMBERSK1 holds  for it2 be BinOpBINOP-1M2-of NATNUMBERSK1 holds ( for n1 be NatNAT-1M1 holds  for n2 be NatNAT-1M1 holds it1 .BINOP-1K1(n1,n2) =XBOOLE-0R4 n1 *XCMPLX-0K3 n2) & ( for n1 be NatNAT-1M1 holds  for n2 be NatNAT-1M1 holds it2 .BINOP-1K1(n1,n2) =XBOOLE-0R4 n1 *XCMPLX-0K3 n2) implies it1 =HIDDENR1 it2"
      using binop_2_sch_12 sorry
qed "sorry"

mtheorem binop_2_cl_2:
"cluster addcomplexBINOP-2K3 as-term-is commutativeBINOP-1V1\<^bsub>(COMPLEXNUMBERSK3)\<^esub>\<bar>associativeBINOP-1V2\<^bsub>(COMPLEXNUMBERSK3)\<^esub>"
proof
(*coherence*)
  show "addcomplexBINOP-2K3 be commutativeBINOP-1V1\<^bsub>(COMPLEXNUMBERSK3)\<^esub>\<bar>associativeBINOP-1V2\<^bsub>(COMPLEXNUMBERSK3)\<^esub>"
sorry
qed "sorry"

mtheorem binop_2_cl_3:
"cluster multcomplexBINOP-2K5 as-term-is commutativeBINOP-1V1\<^bsub>(COMPLEXNUMBERSK3)\<^esub>\<bar>associativeBINOP-1V2\<^bsub>(COMPLEXNUMBERSK3)\<^esub>"
proof
(*coherence*)
  show "multcomplexBINOP-2K5 be commutativeBINOP-1V1\<^bsub>(COMPLEXNUMBERSK3)\<^esub>\<bar>associativeBINOP-1V2\<^bsub>(COMPLEXNUMBERSK3)\<^esub>"
sorry
qed "sorry"

mtheorem binop_2_cl_4:
"cluster addrealBINOP-2K9 as-term-is commutativeBINOP-1V1\<^bsub>(REALNUMBERSK2)\<^esub>\<bar>associativeBINOP-1V2\<^bsub>(REALNUMBERSK2)\<^esub>"
proof
(*coherence*)
  show "addrealBINOP-2K9 be commutativeBINOP-1V1\<^bsub>(REALNUMBERSK2)\<^esub>\<bar>associativeBINOP-1V2\<^bsub>(REALNUMBERSK2)\<^esub>"
sorry
qed "sorry"

mtheorem binop_2_cl_5:
"cluster multrealBINOP-2K11 as-term-is commutativeBINOP-1V1\<^bsub>(REALNUMBERSK2)\<^esub>\<bar>associativeBINOP-1V2\<^bsub>(REALNUMBERSK2)\<^esub>"
proof
(*coherence*)
  show "multrealBINOP-2K11 be commutativeBINOP-1V1\<^bsub>(REALNUMBERSK2)\<^esub>\<bar>associativeBINOP-1V2\<^bsub>(REALNUMBERSK2)\<^esub>"
sorry
qed "sorry"

mtheorem binop_2_cl_6:
"cluster addratBINOP-2K15 as-term-is commutativeBINOP-1V1\<^bsub>(RATRAT-1K1)\<^esub>\<bar>associativeBINOP-1V2\<^bsub>(RATRAT-1K1)\<^esub>"
proof
(*coherence*)
  show "addratBINOP-2K15 be commutativeBINOP-1V1\<^bsub>(RATRAT-1K1)\<^esub>\<bar>associativeBINOP-1V2\<^bsub>(RATRAT-1K1)\<^esub>"
sorry
qed "sorry"

mtheorem binop_2_cl_7:
"cluster multratBINOP-2K17 as-term-is commutativeBINOP-1V1\<^bsub>(RATRAT-1K1)\<^esub>\<bar>associativeBINOP-1V2\<^bsub>(RATRAT-1K1)\<^esub>"
proof
(*coherence*)
  show "multratBINOP-2K17 be commutativeBINOP-1V1\<^bsub>(RATRAT-1K1)\<^esub>\<bar>associativeBINOP-1V2\<^bsub>(RATRAT-1K1)\<^esub>"
sorry
qed "sorry"

mtheorem binop_2_cl_8:
"cluster addintBINOP-2K20 as-term-is commutativeBINOP-1V1\<^bsub>(INTNUMBERSK5)\<^esub>\<bar>associativeBINOP-1V2\<^bsub>(INTNUMBERSK5)\<^esub>"
proof
(*coherence*)
  show "addintBINOP-2K20 be commutativeBINOP-1V1\<^bsub>(INTNUMBERSK5)\<^esub>\<bar>associativeBINOP-1V2\<^bsub>(INTNUMBERSK5)\<^esub>"
sorry
qed "sorry"

mtheorem binop_2_cl_9:
"cluster multintBINOP-2K22 as-term-is commutativeBINOP-1V1\<^bsub>(INTNUMBERSK5)\<^esub>\<bar>associativeBINOP-1V2\<^bsub>(INTNUMBERSK5)\<^esub>"
proof
(*coherence*)
  show "multintBINOP-2K22 be commutativeBINOP-1V1\<^bsub>(INTNUMBERSK5)\<^esub>\<bar>associativeBINOP-1V2\<^bsub>(INTNUMBERSK5)\<^esub>"
sorry
qed "sorry"

mtheorem binop_2_cl_10:
"cluster addnatBINOP-2K23 as-term-is commutativeBINOP-1V1\<^bsub>(NATNUMBERSK1)\<^esub>\<bar>associativeBINOP-1V2\<^bsub>(NATNUMBERSK1)\<^esub>"
proof
(*coherence*)
  show "addnatBINOP-2K23 be commutativeBINOP-1V1\<^bsub>(NATNUMBERSK1)\<^esub>\<bar>associativeBINOP-1V2\<^bsub>(NATNUMBERSK1)\<^esub>"
sorry
qed "sorry"

mtheorem binop_2_cl_11:
"cluster multnatBINOP-2K24 as-term-is commutativeBINOP-1V1\<^bsub>(NATNUMBERSK1)\<^esub>\<bar>associativeBINOP-1V2\<^bsub>(NATNUMBERSK1)\<^esub>"
proof
(*coherence*)
  show "multnatBINOP-2K24 be commutativeBINOP-1V1\<^bsub>(NATNUMBERSK1)\<^esub>\<bar>associativeBINOP-1V2\<^bsub>(NATNUMBERSK1)\<^esub>"
sorry
qed "sorry"

mlemma binop_2_lm_1:
"0NUMBERSK6 inHIDDENR3 NATNUMBERSK1"
   sorry

mlemma binop_2_lm_2:
"0NUMBERSK6 is-a-unity-wrtBINOP-1R3\<^bsub>(COMPLEXNUMBERSK3)\<^esub> addcomplexBINOP-2K3"
sorry

mlemma binop_2_lm_3:
"InSUBSET-1K10(0NUMBERSK6,REALNUMBERSK2) is-a-unity-wrtBINOP-1R3\<^bsub>(REALNUMBERSK2)\<^esub> addrealBINOP-2K9"
sorry

mlemma binop_2_lm_4:
"0NUMBERSK6 is-a-unity-wrtBINOP-1R3\<^bsub>(RATRAT-1K1)\<^esub> addratBINOP-2K15"
sorry

mlemma binop_2_lm_5:
"0NUMBERSK6 is-a-unity-wrtBINOP-1R3\<^bsub>(INTNUMBERSK5)\<^esub> addintBINOP-2K20"
sorry

mlemma binop_2_lm_6:
"0NUMBERSK6 is-a-unity-wrtBINOP-1R3\<^bsub>(NATNUMBERSK1)\<^esub> addnatBINOP-2K23"
sorry

mlemma binop_2_lm_7:
"\<one>\<^sub>M inHIDDENR3 NATNUMBERSK1"
   sorry

mlemma binop_2_lm_8:
"\<one>\<^sub>M is-a-unity-wrtBINOP-1R3\<^bsub>(COMPLEXNUMBERSK3)\<^esub> multcomplexBINOP-2K5"
sorry

mlemma binop_2_lm_9:
"\<one>\<^sub>M is-a-unity-wrtBINOP-1R3\<^bsub>(REALNUMBERSK2)\<^esub> multrealBINOP-2K11"
sorry

mlemma binop_2_lm_10:
"\<one>\<^sub>M is-a-unity-wrtBINOP-1R3\<^bsub>(RATRAT-1K1)\<^esub> multratBINOP-2K17"
sorry

mlemma binop_2_lm_11:
"\<one>\<^sub>M is-a-unity-wrtBINOP-1R3\<^bsub>(INTNUMBERSK5)\<^esub> multintBINOP-2K22"
sorry

mlemma binop_2_lm_12:
"\<one>\<^sub>M is-a-unity-wrtBINOP-1R3\<^bsub>(NATNUMBERSK1)\<^esub> multnatBINOP-2K24"
sorry

mtheorem binop_2_cl_12:
"cluster addcomplexBINOP-2K3 as-term-is having-a-unitySETWISEOV1\<^bsub>(COMPLEXNUMBERSK3)\<^esub>"
proof
(*coherence*)
  show "addcomplexBINOP-2K3 be having-a-unitySETWISEOV1\<^bsub>(COMPLEXNUMBERSK3)\<^esub>"
    using binop_2_lm_1 numbers_th_20 binop_2_lm_2 setwiseo_def_2 sorry
qed "sorry"

mtheorem binop_2_cl_13:
"cluster addrealBINOP-2K9 as-term-is having-a-unitySETWISEOV1\<^bsub>(REALNUMBERSK2)\<^esub>"
proof
(*coherence*)
  show "addrealBINOP-2K9 be having-a-unitySETWISEOV1\<^bsub>(REALNUMBERSK2)\<^esub>"
    using binop_2_lm_3 setwiseo_def_2 sorry
qed "sorry"

mtheorem binop_2_cl_14:
"cluster addratBINOP-2K15 as-term-is having-a-unitySETWISEOV1\<^bsub>(RATRAT-1K1)\<^esub>"
proof
(*coherence*)
  show "addratBINOP-2K15 be having-a-unitySETWISEOV1\<^bsub>(RATRAT-1K1)\<^esub>"
    using binop_2_lm_1 numbers_th_18 binop_2_lm_4 setwiseo_def_2 sorry
qed "sorry"

mtheorem binop_2_cl_15:
"cluster addintBINOP-2K20 as-term-is having-a-unitySETWISEOV1\<^bsub>(INTNUMBERSK5)\<^esub>"
proof
(*coherence*)
  show "addintBINOP-2K20 be having-a-unitySETWISEOV1\<^bsub>(INTNUMBERSK5)\<^esub>"
    using binop_2_lm_1 numbers_th_17 binop_2_lm_5 setwiseo_def_2 sorry
qed "sorry"

mtheorem binop_2_cl_16:
"cluster addnatBINOP-2K23 as-term-is having-a-unitySETWISEOV1\<^bsub>(NATNUMBERSK1)\<^esub>"
proof
(*coherence*)
  show "addnatBINOP-2K23 be having-a-unitySETWISEOV1\<^bsub>(NATNUMBERSK1)\<^esub>"
    using binop_2_lm_6 setwiseo_def_2 sorry
qed "sorry"

mtheorem binop_2_cl_17:
"cluster multcomplexBINOP-2K5 as-term-is having-a-unitySETWISEOV1\<^bsub>(COMPLEXNUMBERSK3)\<^esub>"
proof
(*coherence*)
  show "multcomplexBINOP-2K5 be having-a-unitySETWISEOV1\<^bsub>(COMPLEXNUMBERSK3)\<^esub>"
    using binop_2_lm_7 numbers_th_20 binop_2_lm_8 setwiseo_def_2 sorry
qed "sorry"

mtheorem binop_2_cl_18:
"cluster multrealBINOP-2K11 as-term-is having-a-unitySETWISEOV1\<^bsub>(REALNUMBERSK2)\<^esub>"
proof
(*coherence*)
  show "multrealBINOP-2K11 be having-a-unitySETWISEOV1\<^bsub>(REALNUMBERSK2)\<^esub>"
    using binop_2_lm_7 numbers_th_19 binop_2_lm_9 setwiseo_def_2 sorry
qed "sorry"

mtheorem binop_2_cl_19:
"cluster multratBINOP-2K17 as-term-is having-a-unitySETWISEOV1\<^bsub>(RATRAT-1K1)\<^esub>"
proof
(*coherence*)
  show "multratBINOP-2K17 be having-a-unitySETWISEOV1\<^bsub>(RATRAT-1K1)\<^esub>"
    using binop_2_lm_7 numbers_th_18 binop_2_lm_10 setwiseo_def_2 sorry
qed "sorry"

mtheorem binop_2_cl_20:
"cluster multintBINOP-2K22 as-term-is having-a-unitySETWISEOV1\<^bsub>(INTNUMBERSK5)\<^esub>"
proof
(*coherence*)
  show "multintBINOP-2K22 be having-a-unitySETWISEOV1\<^bsub>(INTNUMBERSK5)\<^esub>"
    using binop_2_lm_7 numbers_th_17 binop_2_lm_11 setwiseo_def_2 sorry
qed "sorry"

mtheorem binop_2_cl_21:
"cluster multnatBINOP-2K24 as-term-is having-a-unitySETWISEOV1\<^bsub>(NATNUMBERSK1)\<^esub>"
proof
(*coherence*)
  show "multnatBINOP-2K24 be having-a-unitySETWISEOV1\<^bsub>(NATNUMBERSK1)\<^esub>"
    using binop_2_lm_12 setwiseo_def_2 sorry
qed "sorry"

mtheorem binop_2_th_1:
"the-unity-wrtBINOP-1K3\<^bsub>(COMPLEXNUMBERSK3)\<^esub> (addcomplexBINOP-2K3) =XBOOLE-0R4 0NUMBERSK6"
  using binop_2_lm_1 numbers_th_20 binop_2_lm_2 binop_1_def_8 sorry

mtheorem binop_2_th_2:
"the-unity-wrtBINOP-1K3\<^bsub>(REALNUMBERSK2)\<^esub> (addrealBINOP-2K9) =XBOOLE-0R4 0NUMBERSK6"
  using binop_2_lm_3 binop_1_def_8 sorry

mtheorem binop_2_th_3:
"the-unity-wrtBINOP-1K3\<^bsub>(RATRAT-1K1)\<^esub> (addratBINOP-2K15) =XBOOLE-0R4 0NUMBERSK6"
  using binop_2_lm_1 numbers_th_18 binop_2_lm_4 binop_1_def_8 sorry

mtheorem binop_2_th_4:
"the-unity-wrtBINOP-1K3\<^bsub>(INTNUMBERSK5)\<^esub> (addintBINOP-2K20) =XBOOLE-0R4 0NUMBERSK6"
  using binop_2_lm_1 numbers_th_17 binop_2_lm_5 binop_1_def_8 sorry

mtheorem binop_2_th_5:
"the-unity-wrtBINOP-1K3\<^bsub>(NATNUMBERSK1)\<^esub> (addnatBINOP-2K23) =XBOOLE-0R4 0NUMBERSK6"
  using binop_2_lm_6 binop_1_def_8 sorry

mtheorem binop_2_th_6:
"the-unity-wrtBINOP-1K3\<^bsub>(COMPLEXNUMBERSK3)\<^esub> (multcomplexBINOP-2K5) =XBOOLE-0R4 \<one>\<^sub>M"
  using binop_2_lm_7 numbers_th_20 binop_2_lm_8 binop_1_def_8 sorry

mtheorem binop_2_th_7:
"the-unity-wrtBINOP-1K3\<^bsub>(REALNUMBERSK2)\<^esub> (multrealBINOP-2K11) =XBOOLE-0R4 \<one>\<^sub>M"
  using binop_2_lm_7 numbers_th_19 binop_2_lm_9 binop_1_def_8 sorry

mtheorem binop_2_th_8:
"the-unity-wrtBINOP-1K3\<^bsub>(RATRAT-1K1)\<^esub> (multratBINOP-2K17) =XBOOLE-0R4 \<one>\<^sub>M"
  using binop_2_lm_7 numbers_th_18 binop_2_lm_10 binop_1_def_8 sorry

mtheorem binop_2_th_9:
"the-unity-wrtBINOP-1K3\<^bsub>(INTNUMBERSK5)\<^esub> (multintBINOP-2K22) =XBOOLE-0R4 \<one>\<^sub>M"
  using binop_2_lm_7 numbers_th_17 binop_2_lm_11 binop_1_def_8 sorry

mtheorem binop_2_th_10:
"the-unity-wrtBINOP-1K3\<^bsub>(NATNUMBERSK1)\<^esub> (multnatBINOP-2K24) =XBOOLE-0R4 \<one>\<^sub>M"
  using binop_2_lm_12 binop_1_def_8 sorry

mtheorem binop_2_cl_22:
  mlet "f be real-valuedVALUED-0V7\<bar>FunctionFUNCT-1M1", "a be objectHIDDENM1", "b be objectHIDDENM1"
"cluster f .BINOP-1K1(a,b) as-term-is realXREAL-0V1"
proof
(*coherence*)
  show "f .BINOP-1K1(a,b) be realXREAL-0V1"
     sorry
qed "sorry"

end
