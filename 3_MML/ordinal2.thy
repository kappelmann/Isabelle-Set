theory ordinal2
  imports ordinal1 funcop_1
   "../mizar_extension/E_number"
begin
(*begin*)
reserve A, A1, A2, B, C, D for "OrdinalORDINAL1M3"
reserve X, Y for "setHIDDENM2"
reserve x, y, a, b, c for "objectHIDDENM1"
reserve L, L1, L2, L3 for "SequenceORDINAL1M4"
reserve f for "FunctionFUNCT-1M1"
theorem ordinal2_sch_1:
  fixes Pp1 
  assumes
    A1: "Pp1(0ORDINAL1K5)" and
   A2: " for A be OrdinalORDINAL1M3 holds Pp1(A) implies Pp1(succORDINAL1K1 A)" and
   A3: " for A be OrdinalORDINAL1M3 holds (A <>HIDDENR2 0ORDINAL1K5 & A be limit-ordinalORDINAL1V4) & ( for B be OrdinalORDINAL1M3 holds B inTARSKIR2 A implies Pp1(B)) implies Pp1(A)"
  shows " for A be OrdinalORDINAL1M3 holds Pp1(A)"
sorry

mtheorem ordinal2_th_1:
" for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds A c=ORDINAL1R1 B iff succORDINAL1K1 A c=ORDINAL1R1 succORDINAL1K1 B"
sorry

mtheorem ordinal2_th_2:
" for A be OrdinalORDINAL1M3 holds unionTARSKIK3 (succORDINAL1K1 A) =XBOOLE-0R4 A"
sorry

mtheorem ordinal2_th_3:
" for A be OrdinalORDINAL1M3 holds succORDINAL1K1 A c=TARSKIR1 boolSETFAM-1K9 A"
sorry

mtheorem ordinal2_th_4:
"0ORDINAL1K5 be limit-ordinalORDINAL1V4"
  using zfmisc_1_th_2 sorry

mtheorem ordinal2_th_5:
" for A be OrdinalORDINAL1M3 holds unionTARSKIK3 A c=ORDINAL1R1 A"
sorry

mdef ordinal2_def_1 ("lastORDINAL2K1  _ " [228]228 ) where
  mlet "L be SequenceORDINAL1M4"
"func lastORDINAL2K1 L \<rightarrow> setHIDDENM2 equals
  L .FUNCT-1K1 unionTARSKIK3 (domRELAT-1K1 L)"
proof-
  (*coherence*)
    show "L .FUNCT-1K1 unionTARSKIK3 (domRELAT-1K1 L) be setHIDDENM2"
       sorry
qed "sorry"

mtheorem ordinal2_th_6:
" for A be OrdinalORDINAL1M3 holds  for L be SequenceORDINAL1M4 holds domRELAT-1K1 L =XBOOLE-0R4 succORDINAL1K1 A implies lastORDINAL2K1 L =XBOOLE-0R4 L .FUNCT-1K1 A"
  using ordinal2_th_2 sorry

mtheorem ordinal2_th_7:
" for X be setHIDDENM2 holds OnORDINAL1K2 X c=TARSKIR1 X"
  using ordinal1_def_9 sorry

mtheorem ordinal2_th_8:
" for A be OrdinalORDINAL1M3 holds OnORDINAL1K2 A =XBOOLE-0R4 A"
sorry

mtheorem ordinal2_th_9:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X c=TARSKIR1 Y implies OnORDINAL1K2 X c=TARSKIR1 OnORDINAL1K2 Y"
sorry

mtheorem ordinal2_th_10:
" for X be setHIDDENM2 holds LimORDINAL1K3 X c=TARSKIR1 X"
  using ordinal1_def_10 sorry

mtheorem ordinal2_th_11:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X c=TARSKIR1 Y implies LimORDINAL1K3 X c=TARSKIR1 LimORDINAL1K3 Y"
sorry

mtheorem ordinal2_th_12:
" for X be setHIDDENM2 holds LimORDINAL1K3 X c=TARSKIR1 OnORDINAL1K2 X"
sorry

mtheorem ordinal2_th_13:
" for X be setHIDDENM2 holds ( for x be objectHIDDENM1 holds x inHIDDENR3 X implies x be OrdinalORDINAL1M3) implies meetSETFAM-1K1 X be OrdinalORDINAL1M3"
sorry

mtheorem ordinal2_cl_1:
"cluster limit-ordinalORDINAL1V4 for OrdinalORDINAL1M3"
proof
(*existence*)
  show " ex it be OrdinalORDINAL1M3 st it be limit-ordinalORDINAL1V4"
sorry
qed "sorry"

mdef ordinal2_def_2 ("infORDINAL2K2  _ " [228]228 ) where
  mlet "X be setHIDDENM2"
"func infORDINAL2K2 X \<rightarrow> OrdinalORDINAL1M3 equals
  meetSETFAM-1K1 (OnORDINAL1K2 X)"
proof-
  (*coherence*)
    show "meetSETFAM-1K1 (OnORDINAL1K2 X) be OrdinalORDINAL1M3"
sorry
qed "sorry"

mdef ordinal2_def_3 ("supORDINAL2K3  _ " [300]300 ) where
  mlet "X be setHIDDENM2"
"func supORDINAL2K3 X \<rightarrow> OrdinalORDINAL1M3 means
  \<lambda>it. OnORDINAL1K2 X c=TARSKIR1 it & ( for A be OrdinalORDINAL1M3 holds OnORDINAL1K2 X c=TARSKIR1 A implies it c=ORDINAL1R1 A)"
proof-
  (*existence*)
    show " ex it be OrdinalORDINAL1M3 st OnORDINAL1K2 X c=TARSKIR1 it & ( for A be OrdinalORDINAL1M3 holds OnORDINAL1K2 X c=TARSKIR1 A implies it c=ORDINAL1R1 A)"
sorry
  (*uniqueness*)
    show " for it1 be OrdinalORDINAL1M3 holds  for it2 be OrdinalORDINAL1M3 holds (OnORDINAL1K2 X c=TARSKIR1 it1 & ( for A be OrdinalORDINAL1M3 holds OnORDINAL1K2 X c=TARSKIR1 A implies it1 c=ORDINAL1R1 A)) & (OnORDINAL1K2 X c=TARSKIR1 it2 & ( for A be OrdinalORDINAL1M3 holds OnORDINAL1K2 X c=TARSKIR1 A implies it2 c=ORDINAL1R1 A)) implies it1 =HIDDENR1 it2"
       sorry
qed "sorry"

mtheorem ordinal2_th_14:
" for A be OrdinalORDINAL1M3 holds  for X be setHIDDENM2 holds A inTARSKIR2 X implies infORDINAL2K2 X c=ORDINAL1R1 A"
sorry

mtheorem ordinal2_th_15:
" for D be OrdinalORDINAL1M3 holds  for X be setHIDDENM2 holds OnORDINAL1K2 X <>HIDDENR2 0ORDINAL1K5 & ( for A be OrdinalORDINAL1M3 holds A inTARSKIR2 X implies D c=ORDINAL1R1 A) implies D c=ORDINAL1R1 infORDINAL2K2 X"
sorry

mtheorem ordinal2_th_16:
" for A be OrdinalORDINAL1M3 holds  for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds A inTARSKIR2 X & X c=TARSKIR1 Y implies infORDINAL2K2 Y c=ORDINAL1R1 infORDINAL2K2 X"
sorry

mtheorem ordinal2_th_17:
" for A be OrdinalORDINAL1M3 holds  for X be setHIDDENM2 holds A inTARSKIR2 X implies infORDINAL2K2 X inTARSKIR2 X"
sorry

mtheorem ordinal2_th_18:
" for A be OrdinalORDINAL1M3 holds supORDINAL2K3 A =XBOOLE-0R4 A"
sorry

mtheorem ordinal2_th_19:
" for A be OrdinalORDINAL1M3 holds  for X be setHIDDENM2 holds A inTARSKIR2 X implies A inTARSKIR2 supORDINAL2K3 X"
sorry

mtheorem ordinal2_th_20:
" for D be OrdinalORDINAL1M3 holds  for X be setHIDDENM2 holds ( for A be OrdinalORDINAL1M3 holds A inTARSKIR2 X implies A inTARSKIR2 D) implies supORDINAL2K3 X c=ORDINAL1R1 D"
sorry

mtheorem ordinal2_th_21:
" for A be OrdinalORDINAL1M3 holds  for X be setHIDDENM2 holds A inTARSKIR2 supORDINAL2K3 X implies ( ex B be OrdinalORDINAL1M3 st B inTARSKIR2 X & A c=ORDINAL1R1 B)"
sorry

mtheorem ordinal2_th_22:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X c=TARSKIR1 Y implies supORDINAL2K3 X c=ORDINAL1R1 supORDINAL2K3 Y"
sorry

mtheorem ordinal2_th_23:
" for A be OrdinalORDINAL1M3 holds supORDINAL2K3 {TARSKIK1 A} =XBOOLE-0R4 succORDINAL1K1 A"
sorry

mtheorem ordinal2_th_24:
" for X be setHIDDENM2 holds infORDINAL2K2 X c=ORDINAL1R1 supORDINAL2K3 X"
sorry

theorem ordinal2_sch_2:
  fixes Af0 Ff1 
  assumes
[ty]: "Af0 be OrdinalORDINAL1M3" and
  [ty_func]: "\<And> x1. x1 be OrdinalORDINAL1M3 \<Longrightarrow> Ff1(x1) be setHIDDENM2"
  shows " ex L be SequenceORDINAL1M4 st domRELAT-1K1 L =XBOOLE-0R4 Af0 & ( for A be OrdinalORDINAL1M3 holds A inTARSKIR2 Af0 implies L .FUNCT-1K1 A =XBOOLE-0R4 Ff1(A))"
sorry

mdef ordinal2_def_4 ("Ordinal-yieldingORDINAL2V1" 70 ) where
"attr Ordinal-yieldingORDINAL2V1 for FunctionFUNCT-1M1 means
  (\<lambda>f.  ex A be OrdinalORDINAL1M3 st rngFUNCT-1K2 f c=TARSKIR1 A)"..

mtheorem ordinal2_cl_2:
"cluster Ordinal-yieldingORDINAL2V1 for SequenceORDINAL1M4"
proof
(*existence*)
  show " ex it be SequenceORDINAL1M4 st it be Ordinal-yieldingORDINAL2V1"
sorry
qed "sorry"

syntax ORDINAL2M1 :: "Ty" ("Ordinal-SequenceORDINAL2M1" 70)
translations "Ordinal-SequenceORDINAL2M1" \<rightharpoonup> "Ordinal-yieldingORDINAL2V1\<bar>SequenceORDINAL1M4"

mtheorem ordinal2_cl_3:
  mlet "A be OrdinalORDINAL1M3"
"cluster note-that Ordinal-yieldingORDINAL2V1 for SequenceORDINAL1M5-of A"
proof
(*coherence*)
  show " for it be SequenceORDINAL1M5-of A holds it be Ordinal-yieldingORDINAL2V1"
    using relat_1_def_19 sorry
qed "sorry"

mtheorem ordinal2_cl_4:
  mlet "L be Ordinal-SequenceORDINAL2M1", "A be OrdinalORDINAL1M3"
"cluster L |RELAT-1K8 A as-term-is Ordinal-yieldingORDINAL2V1"
proof
(*coherence*)
  show "L |RELAT-1K8 A be Ordinal-yieldingORDINAL2V1"
sorry
qed "sorry"

reserve fi, psi for "Ordinal-SequenceORDINAL2M1"
mtheorem ordinal2_th_25:
" for A be OrdinalORDINAL1M3 holds  for fi be Ordinal-SequenceORDINAL2M1 holds A inTARSKIR2 domRELAT-1K1 fi implies fi .FUNCT-1K1 A be OrdinalORDINAL1M3"
sorry

mtheorem ordinal2_cl_5:
  mlet "f be Ordinal-SequenceORDINAL2M1", "a be objectHIDDENM1"
"cluster f .FUNCT-1K1 a as-term-is ordinalORDINAL1V3"
proof
(*coherence*)
  show "f .FUNCT-1K1 a be ordinalORDINAL1V3"
sorry
qed "sorry"

theorem ordinal2_sch_3:
  fixes Af0 Ff1 
  assumes
[ty]: "Af0 be OrdinalORDINAL1M3" and
  [ty_func]: "\<And> x1. x1 be OrdinalORDINAL1M3 \<Longrightarrow> Ff1(x1) be OrdinalORDINAL1M3"
  shows " ex fi be Ordinal-SequenceORDINAL2M1 st domRELAT-1K1 fi =XBOOLE-0R4 Af0 & ( for A be OrdinalORDINAL1M3 holds A inTARSKIR2 Af0 implies fi .FUNCT-1K1 A =XBOOLE-0R4 Ff1(A))"
sorry

theorem ordinal2_sch_4:
  fixes Af0 Bf0 Cf2 Df2 L1f0 L2f0 
  assumes
[ty]: "Af0 be OrdinalORDINAL1M3" and
  [ty]: "Bf0 be objectHIDDENM1" and
  [ty_func]: "\<And> x1 x2. x1 be OrdinalORDINAL1M3 \<Longrightarrow> x2 be setHIDDENM2 \<Longrightarrow> Cf2(x1,x2) be objectHIDDENM1" and
  [ty_func]: "\<And> x1 x2. x1 be OrdinalORDINAL1M3 \<Longrightarrow> x2 be SequenceORDINAL1M4 \<Longrightarrow> Df2(x1,x2) be objectHIDDENM1" and
  [ty]: "L1f0 be SequenceORDINAL1M4" and
  [ty]: "L2f0 be SequenceORDINAL1M4" and
   A1: "domRELAT-1K1 L1f0 =XBOOLE-0R4 Af0" and
   A2: "0ORDINAL1K5 inTARSKIR2 Af0 implies L1f0 .FUNCT-1K1 (0ORDINAL1K5) =HIDDENR1 Bf0" and
   A3: " for A be OrdinalORDINAL1M3 holds succORDINAL1K1 A inTARSKIR2 Af0 implies L1f0 .FUNCT-1K1 succORDINAL1K1 A =HIDDENR1 Cf2(A,L1f0 .FUNCT-1K1 A)" and
   A4: " for A be OrdinalORDINAL1M3 holds (A inTARSKIR2 Af0 & A <>HIDDENR2 0ORDINAL1K5) & A be limit-ordinalORDINAL1V4 implies L1f0 .FUNCT-1K1 A =HIDDENR1 Df2(A,L1f0 |RELAT-1K8 A)" and
   A5: "domRELAT-1K1 L2f0 =XBOOLE-0R4 Af0" and
   A6: "0ORDINAL1K5 inTARSKIR2 Af0 implies L2f0 .FUNCT-1K1 (0ORDINAL1K5) =HIDDENR1 Bf0" and
   A7: " for A be OrdinalORDINAL1M3 holds succORDINAL1K1 A inTARSKIR2 Af0 implies L2f0 .FUNCT-1K1 succORDINAL1K1 A =HIDDENR1 Cf2(A,L2f0 .FUNCT-1K1 A)" and
   A8: " for A be OrdinalORDINAL1M3 holds (A inTARSKIR2 Af0 & A <>HIDDENR2 0ORDINAL1K5) & A be limit-ordinalORDINAL1V4 implies L2f0 .FUNCT-1K1 A =HIDDENR1 Df2(A,L2f0 |RELAT-1K8 A)"
  shows "L1f0 =FUNCT-1R1 L2f0"
sorry

theorem ordinal2_sch_5:
  fixes Af0 Bf0 Cf2 Df2 
  assumes
[ty]: "Af0 be OrdinalORDINAL1M3" and
  [ty]: "Bf0 be objectHIDDENM1" and
  [ty_func]: "\<And> x1 x2. x1 be OrdinalORDINAL1M3 \<Longrightarrow> x2 be setHIDDENM2 \<Longrightarrow> Cf2(x1,x2) be objectHIDDENM1" and
  [ty_func]: "\<And> x1 x2. x1 be OrdinalORDINAL1M3 \<Longrightarrow> x2 be SequenceORDINAL1M4 \<Longrightarrow> Df2(x1,x2) be objectHIDDENM1"
  shows " ex L be SequenceORDINAL1M4 st ((domRELAT-1K1 L =XBOOLE-0R4 Af0 & (0ORDINAL1K5 inTARSKIR2 Af0 implies L .FUNCT-1K1 (0ORDINAL1K5) =HIDDENR1 Bf0)) & ( for A be OrdinalORDINAL1M3 holds succORDINAL1K1 A inTARSKIR2 Af0 implies L .FUNCT-1K1 succORDINAL1K1 A =HIDDENR1 Cf2(A,L .FUNCT-1K1 A))) & ( for A be OrdinalORDINAL1M3 holds (A inTARSKIR2 Af0 & A <>HIDDENR2 0ORDINAL1K5) & A be limit-ordinalORDINAL1V4 implies L .FUNCT-1K1 A =HIDDENR1 Df2(A,L |RELAT-1K8 A))"
sorry

theorem ordinal2_sch_6:
  fixes Lf0 Ff1 Af0 Bf0 Cf2 Df2 
  assumes
[ty]: "Lf0 be SequenceORDINAL1M4" and
  [ty_func]: "\<And> x1. x1 be OrdinalORDINAL1M3 \<Longrightarrow> Ff1(x1) be setHIDDENM2" and
  [ty]: "Af0 be OrdinalORDINAL1M3" and
  [ty]: "Bf0 be setHIDDENM2" and
  [ty_func]: "\<And> x1 x2. x1 be OrdinalORDINAL1M3 \<Longrightarrow> x2 be setHIDDENM2 \<Longrightarrow> Cf2(x1,x2) be setHIDDENM2" and
  [ty_func]: "\<And> x1 x2. x1 be OrdinalORDINAL1M3 \<Longrightarrow> x2 be SequenceORDINAL1M4 \<Longrightarrow> Df2(x1,x2) be setHIDDENM2" and
   A1: " for A be OrdinalORDINAL1M3 holds  for x be objectHIDDENM1 holds x =HIDDENR1 Ff1(A) iff ( ex L be SequenceORDINAL1M4 st (((x =HIDDENR1 lastORDINAL2K1 L & domRELAT-1K1 L =XBOOLE-0R4 succORDINAL1K1 A) & L .FUNCT-1K1 (0ORDINAL1K5) =XBOOLE-0R4 Bf0) & ( for C be OrdinalORDINAL1M3 holds succORDINAL1K1 C inTARSKIR2 succORDINAL1K1 A implies L .FUNCT-1K1 succORDINAL1K1 C =XBOOLE-0R4 Cf2(C,L .FUNCT-1K1 C))) & ( for C be OrdinalORDINAL1M3 holds (C inTARSKIR2 succORDINAL1K1 A & C <>HIDDENR2 0ORDINAL1K5) & C be limit-ordinalORDINAL1V4 implies L .FUNCT-1K1 C =XBOOLE-0R4 Df2(C,L |RELAT-1K8 C)))" and
   A2: "domRELAT-1K1 Lf0 =XBOOLE-0R4 Af0" and
   A3: "0ORDINAL1K5 inTARSKIR2 Af0 implies Lf0 .FUNCT-1K1 (0ORDINAL1K5) =XBOOLE-0R4 Bf0" and
   A4: " for A be OrdinalORDINAL1M3 holds succORDINAL1K1 A inTARSKIR2 Af0 implies Lf0 .FUNCT-1K1 succORDINAL1K1 A =XBOOLE-0R4 Cf2(A,Lf0 .FUNCT-1K1 A)" and
   A5: " for A be OrdinalORDINAL1M3 holds (A inTARSKIR2 Af0 & A <>HIDDENR2 0ORDINAL1K5) & A be limit-ordinalORDINAL1V4 implies Lf0 .FUNCT-1K1 A =XBOOLE-0R4 Df2(A,Lf0 |RELAT-1K8 A)"
  shows " for A be OrdinalORDINAL1M3 holds A inTARSKIR2 domRELAT-1K1 Lf0 implies Lf0 .FUNCT-1K1 A =XBOOLE-0R4 Ff1(A)"
sorry

theorem ordinal2_sch_7:
  fixes Af0 Bf0 Cf2 Df2 
  assumes
[ty]: "Af0 be OrdinalORDINAL1M3" and
  [ty]: "Bf0 be setHIDDENM2" and
  [ty_func]: "\<And> x1 x2. x1 be OrdinalORDINAL1M3 \<Longrightarrow> x2 be setHIDDENM2 \<Longrightarrow> Cf2(x1,x2) be setHIDDENM2" and
  [ty_func]: "\<And> x1 x2. x1 be OrdinalORDINAL1M3 \<Longrightarrow> x2 be SequenceORDINAL1M4 \<Longrightarrow> Df2(x1,x2) be setHIDDENM2"
  shows "( ex x be objectHIDDENM1 st  ex L be SequenceORDINAL1M4 st (((x =HIDDENR1 lastORDINAL2K1 L & domRELAT-1K1 L =XBOOLE-0R4 succORDINAL1K1 Af0) & L .FUNCT-1K1 (0ORDINAL1K5) =XBOOLE-0R4 Bf0) & ( for C be OrdinalORDINAL1M3 holds succORDINAL1K1 C inTARSKIR2 succORDINAL1K1 Af0 implies L .FUNCT-1K1 succORDINAL1K1 C =XBOOLE-0R4 Cf2(C,L .FUNCT-1K1 C))) & ( for C be OrdinalORDINAL1M3 holds (C inTARSKIR2 succORDINAL1K1 Af0 & C <>HIDDENR2 0ORDINAL1K5) & C be limit-ordinalORDINAL1V4 implies L .FUNCT-1K1 C =XBOOLE-0R4 Df2(C,L |RELAT-1K8 C))) & ( for x1 be setHIDDENM2 holds  for x2 be setHIDDENM2 holds ( ex L be SequenceORDINAL1M4 st (((x1 =XBOOLE-0R4 lastORDINAL2K1 L & domRELAT-1K1 L =XBOOLE-0R4 succORDINAL1K1 Af0) & L .FUNCT-1K1 (0ORDINAL1K5) =XBOOLE-0R4 Bf0) & ( for C be OrdinalORDINAL1M3 holds succORDINAL1K1 C inTARSKIR2 succORDINAL1K1 Af0 implies L .FUNCT-1K1 succORDINAL1K1 C =XBOOLE-0R4 Cf2(C,L .FUNCT-1K1 C))) & ( for C be OrdinalORDINAL1M3 holds (C inTARSKIR2 succORDINAL1K1 Af0 & C <>HIDDENR2 0ORDINAL1K5) & C be limit-ordinalORDINAL1V4 implies L .FUNCT-1K1 C =XBOOLE-0R4 Df2(C,L |RELAT-1K8 C))) & ( ex L be SequenceORDINAL1M4 st (((x2 =XBOOLE-0R4 lastORDINAL2K1 L & domRELAT-1K1 L =XBOOLE-0R4 succORDINAL1K1 Af0) & L .FUNCT-1K1 (0ORDINAL1K5) =XBOOLE-0R4 Bf0) & ( for C be OrdinalORDINAL1M3 holds succORDINAL1K1 C inTARSKIR2 succORDINAL1K1 Af0 implies L .FUNCT-1K1 succORDINAL1K1 C =XBOOLE-0R4 Cf2(C,L .FUNCT-1K1 C))) & ( for C be OrdinalORDINAL1M3 holds (C inTARSKIR2 succORDINAL1K1 Af0 & C <>HIDDENR2 0ORDINAL1K5) & C be limit-ordinalORDINAL1V4 implies L .FUNCT-1K1 C =XBOOLE-0R4 Df2(C,L |RELAT-1K8 C))) implies x1 =XBOOLE-0R4 x2)"
sorry

theorem ordinal2_sch_8:
  fixes Ff1 Bf0 Cf2 Df2 
  assumes
[ty_func]: "\<And> x1. x1 be OrdinalORDINAL1M3 \<Longrightarrow> Ff1(x1) be setHIDDENM2" and
  [ty]: "Bf0 be setHIDDENM2" and
  [ty_func]: "\<And> x1 x2. x1 be OrdinalORDINAL1M3 \<Longrightarrow> x2 be setHIDDENM2 \<Longrightarrow> Cf2(x1,x2) be setHIDDENM2" and
  [ty_func]: "\<And> x1 x2. x1 be OrdinalORDINAL1M3 \<Longrightarrow> x2 be SequenceORDINAL1M4 \<Longrightarrow> Df2(x1,x2) be setHIDDENM2" and
   A1: " for A be OrdinalORDINAL1M3 holds  for x be objectHIDDENM1 holds x =HIDDENR1 Ff1(A) iff ( ex L be SequenceORDINAL1M4 st (((x =HIDDENR1 lastORDINAL2K1 L & domRELAT-1K1 L =XBOOLE-0R4 succORDINAL1K1 A) & L .FUNCT-1K1 (0ORDINAL1K5) =XBOOLE-0R4 Bf0) & ( for C be OrdinalORDINAL1M3 holds succORDINAL1K1 C inTARSKIR2 succORDINAL1K1 A implies L .FUNCT-1K1 succORDINAL1K1 C =XBOOLE-0R4 Cf2(C,L .FUNCT-1K1 C))) & ( for C be OrdinalORDINAL1M3 holds (C inTARSKIR2 succORDINAL1K1 A & C <>HIDDENR2 0ORDINAL1K5) & C be limit-ordinalORDINAL1V4 implies L .FUNCT-1K1 C =XBOOLE-0R4 Df2(C,L |RELAT-1K8 C)))"
  shows "Ff1(0ORDINAL1K5) =XBOOLE-0R4 Bf0"
sorry

theorem ordinal2_sch_9:
  fixes Bf0 Cf2 Df2 Ff1 
  assumes
[ty]: "Bf0 be setHIDDENM2" and
  [ty_func]: "\<And> x1 x2. x1 be OrdinalORDINAL1M3 \<Longrightarrow> x2 be setHIDDENM2 \<Longrightarrow> Cf2(x1,x2) be setHIDDENM2" and
  [ty_func]: "\<And> x1 x2. x1 be OrdinalORDINAL1M3 \<Longrightarrow> x2 be SequenceORDINAL1M4 \<Longrightarrow> Df2(x1,x2) be setHIDDENM2" and
  [ty_func]: "\<And> x1. x1 be OrdinalORDINAL1M3 \<Longrightarrow> Ff1(x1) be setHIDDENM2" and
   A1: " for A be OrdinalORDINAL1M3 holds  for x be objectHIDDENM1 holds x =HIDDENR1 Ff1(A) iff ( ex L be SequenceORDINAL1M4 st (((x =HIDDENR1 lastORDINAL2K1 L & domRELAT-1K1 L =XBOOLE-0R4 succORDINAL1K1 A) & L .FUNCT-1K1 (0ORDINAL1K5) =XBOOLE-0R4 Bf0) & ( for C be OrdinalORDINAL1M3 holds succORDINAL1K1 C inTARSKIR2 succORDINAL1K1 A implies L .FUNCT-1K1 succORDINAL1K1 C =XBOOLE-0R4 Cf2(C,L .FUNCT-1K1 C))) & ( for C be OrdinalORDINAL1M3 holds (C inTARSKIR2 succORDINAL1K1 A & C <>HIDDENR2 0ORDINAL1K5) & C be limit-ordinalORDINAL1V4 implies L .FUNCT-1K1 C =XBOOLE-0R4 Df2(C,L |RELAT-1K8 C)))"
  shows " for A be OrdinalORDINAL1M3 holds Ff1(succORDINAL1K1 A) =XBOOLE-0R4 Cf2(A,Ff1(A))"
sorry

theorem ordinal2_sch_10:
  fixes Lf0 Af0 Ff1 Bf0 Cf2 Df2 
  assumes
[ty]: "Lf0 be SequenceORDINAL1M4" and
  [ty]: "Af0 be OrdinalORDINAL1M3" and
  [ty_func]: "\<And> x1. x1 be OrdinalORDINAL1M3 \<Longrightarrow> Ff1(x1) be setHIDDENM2" and
  [ty]: "Bf0 be setHIDDENM2" and
  [ty_func]: "\<And> x1 x2. x1 be OrdinalORDINAL1M3 \<Longrightarrow> x2 be setHIDDENM2 \<Longrightarrow> Cf2(x1,x2) be setHIDDENM2" and
  [ty_func]: "\<And> x1 x2. x1 be OrdinalORDINAL1M3 \<Longrightarrow> x2 be SequenceORDINAL1M4 \<Longrightarrow> Df2(x1,x2) be setHIDDENM2" and
   A1: " for A be OrdinalORDINAL1M3 holds  for x be objectHIDDENM1 holds x =HIDDENR1 Ff1(A) iff ( ex L be SequenceORDINAL1M4 st (((x =HIDDENR1 lastORDINAL2K1 L & domRELAT-1K1 L =XBOOLE-0R4 succORDINAL1K1 A) & L .FUNCT-1K1 (0ORDINAL1K5) =XBOOLE-0R4 Bf0) & ( for C be OrdinalORDINAL1M3 holds succORDINAL1K1 C inTARSKIR2 succORDINAL1K1 A implies L .FUNCT-1K1 succORDINAL1K1 C =XBOOLE-0R4 Cf2(C,L .FUNCT-1K1 C))) & ( for C be OrdinalORDINAL1M3 holds (C inTARSKIR2 succORDINAL1K1 A & C <>HIDDENR2 0ORDINAL1K5) & C be limit-ordinalORDINAL1V4 implies L .FUNCT-1K1 C =XBOOLE-0R4 Df2(C,L |RELAT-1K8 C)))" and
   A2: "Af0 <>HIDDENR2 0ORDINAL1K5 & Af0 be limit-ordinalORDINAL1V4" and
   A3: "domRELAT-1K1 Lf0 =XBOOLE-0R4 Af0" and
   A4: " for A be OrdinalORDINAL1M3 holds A inTARSKIR2 Af0 implies Lf0 .FUNCT-1K1 A =XBOOLE-0R4 Ff1(A)"
  shows "Ff1(Af0) =XBOOLE-0R4 Df2(Af0,Lf0)"
sorry

theorem ordinal2_sch_11:
  fixes Af0 Bf0 Cf2 Df2 
  assumes
[ty]: "Af0 be OrdinalORDINAL1M3" and
  [ty]: "Bf0 be OrdinalORDINAL1M3" and
  [ty_func]: "\<And> x1 x2. x1 be OrdinalORDINAL1M3 \<Longrightarrow> x2 be OrdinalORDINAL1M3 \<Longrightarrow> Cf2(x1,x2) be OrdinalORDINAL1M3" and
  [ty_func]: "\<And> x1 x2. x1 be OrdinalORDINAL1M3 \<Longrightarrow> x2 be SequenceORDINAL1M4 \<Longrightarrow> Df2(x1,x2) be OrdinalORDINAL1M3"
  shows " ex fi be Ordinal-SequenceORDINAL2M1 st ((domRELAT-1K1 fi =XBOOLE-0R4 Af0 & (0ORDINAL1K5 inTARSKIR2 Af0 implies fi .FUNCT-1K1 (0ORDINAL1K5) =XBOOLE-0R4 Bf0)) & ( for A be OrdinalORDINAL1M3 holds succORDINAL1K1 A inTARSKIR2 Af0 implies fi .FUNCT-1K1 succORDINAL1K1 A =XBOOLE-0R4 Cf2(A,fi .FUNCT-1K1 A))) & ( for A be OrdinalORDINAL1M3 holds (A inTARSKIR2 Af0 & A <>HIDDENR2 0ORDINAL1K5) & A be limit-ordinalORDINAL1V4 implies fi .FUNCT-1K1 A =XBOOLE-0R4 Df2(A,fi |RELAT-1K8 A))"
sorry

theorem ordinal2_sch_12:
  fixes fif0 Ff1 Af0 Bf0 Cf2 Df2 
  assumes
[ty]: "fif0 be Ordinal-SequenceORDINAL2M1" and
  [ty_func]: "\<And> x1. x1 be OrdinalORDINAL1M3 \<Longrightarrow> Ff1(x1) be OrdinalORDINAL1M3" and
  [ty]: "Af0 be OrdinalORDINAL1M3" and
  [ty]: "Bf0 be OrdinalORDINAL1M3" and
  [ty_func]: "\<And> x1 x2. x1 be OrdinalORDINAL1M3 \<Longrightarrow> x2 be OrdinalORDINAL1M3 \<Longrightarrow> Cf2(x1,x2) be OrdinalORDINAL1M3" and
  [ty_func]: "\<And> x1 x2. x1 be OrdinalORDINAL1M3 \<Longrightarrow> x2 be SequenceORDINAL1M4 \<Longrightarrow> Df2(x1,x2) be OrdinalORDINAL1M3" and
   A1: " for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds B =XBOOLE-0R4 Ff1(A) iff ( ex fi be Ordinal-SequenceORDINAL2M1 st (((B =XBOOLE-0R4 lastORDINAL2K1 fi & domRELAT-1K1 fi =XBOOLE-0R4 succORDINAL1K1 A) & fi .FUNCT-1K1 (0ORDINAL1K5) =XBOOLE-0R4 Bf0) & ( for C be OrdinalORDINAL1M3 holds succORDINAL1K1 C inTARSKIR2 succORDINAL1K1 A implies fi .FUNCT-1K1 succORDINAL1K1 C =XBOOLE-0R4 Cf2(C,fi .FUNCT-1K1 C))) & ( for C be OrdinalORDINAL1M3 holds (C inTARSKIR2 succORDINAL1K1 A & C <>HIDDENR2 0ORDINAL1K5) & C be limit-ordinalORDINAL1V4 implies fi .FUNCT-1K1 C =XBOOLE-0R4 Df2(C,fi |RELAT-1K8 C)))" and
   A2: "domRELAT-1K1 fif0 =XBOOLE-0R4 Af0" and
   A3: "0ORDINAL1K5 inTARSKIR2 Af0 implies fif0 .FUNCT-1K1 (0ORDINAL1K5) =XBOOLE-0R4 Bf0" and
   A4: " for A be OrdinalORDINAL1M3 holds succORDINAL1K1 A inTARSKIR2 Af0 implies fif0 .FUNCT-1K1 succORDINAL1K1 A =XBOOLE-0R4 Cf2(A,fif0 .FUNCT-1K1 A)" and
   A5: " for A be OrdinalORDINAL1M3 holds (A inTARSKIR2 Af0 & A <>HIDDENR2 0ORDINAL1K5) & A be limit-ordinalORDINAL1V4 implies fif0 .FUNCT-1K1 A =XBOOLE-0R4 Df2(A,fif0 |RELAT-1K8 A)"
  shows " for A be OrdinalORDINAL1M3 holds A inTARSKIR2 domRELAT-1K1 fif0 implies fif0 .FUNCT-1K1 A =XBOOLE-0R4 Ff1(A)"
sorry

theorem ordinal2_sch_13:
  fixes Af0 Bf0 Cf2 Df2 
  assumes
[ty]: "Af0 be OrdinalORDINAL1M3" and
  [ty]: "Bf0 be OrdinalORDINAL1M3" and
  [ty_func]: "\<And> x1 x2. x1 be OrdinalORDINAL1M3 \<Longrightarrow> x2 be OrdinalORDINAL1M3 \<Longrightarrow> Cf2(x1,x2) be OrdinalORDINAL1M3" and
  [ty_func]: "\<And> x1 x2. x1 be OrdinalORDINAL1M3 \<Longrightarrow> x2 be SequenceORDINAL1M4 \<Longrightarrow> Df2(x1,x2) be OrdinalORDINAL1M3"
  shows "( ex A be OrdinalORDINAL1M3 st  ex fi be Ordinal-SequenceORDINAL2M1 st (((A =XBOOLE-0R4 lastORDINAL2K1 fi & domRELAT-1K1 fi =XBOOLE-0R4 succORDINAL1K1 Af0) & fi .FUNCT-1K1 (0ORDINAL1K5) =XBOOLE-0R4 Bf0) & ( for C be OrdinalORDINAL1M3 holds succORDINAL1K1 C inTARSKIR2 succORDINAL1K1 Af0 implies fi .FUNCT-1K1 succORDINAL1K1 C =XBOOLE-0R4 Cf2(C,fi .FUNCT-1K1 C))) & ( for C be OrdinalORDINAL1M3 holds (C inTARSKIR2 succORDINAL1K1 Af0 & C <>HIDDENR2 0ORDINAL1K5) & C be limit-ordinalORDINAL1V4 implies fi .FUNCT-1K1 C =XBOOLE-0R4 Df2(C,fi |RELAT-1K8 C))) & ( for A1 be OrdinalORDINAL1M3 holds  for A2 be OrdinalORDINAL1M3 holds ( ex fi be Ordinal-SequenceORDINAL2M1 st (((A1 =XBOOLE-0R4 lastORDINAL2K1 fi & domRELAT-1K1 fi =XBOOLE-0R4 succORDINAL1K1 Af0) & fi .FUNCT-1K1 (0ORDINAL1K5) =XBOOLE-0R4 Bf0) & ( for C be OrdinalORDINAL1M3 holds succORDINAL1K1 C inTARSKIR2 succORDINAL1K1 Af0 implies fi .FUNCT-1K1 succORDINAL1K1 C =XBOOLE-0R4 Cf2(C,fi .FUNCT-1K1 C))) & ( for C be OrdinalORDINAL1M3 holds (C inTARSKIR2 succORDINAL1K1 Af0 & C <>HIDDENR2 0ORDINAL1K5) & C be limit-ordinalORDINAL1V4 implies fi .FUNCT-1K1 C =XBOOLE-0R4 Df2(C,fi |RELAT-1K8 C))) & ( ex fi be Ordinal-SequenceORDINAL2M1 st (((A2 =XBOOLE-0R4 lastORDINAL2K1 fi & domRELAT-1K1 fi =XBOOLE-0R4 succORDINAL1K1 Af0) & fi .FUNCT-1K1 (0ORDINAL1K5) =XBOOLE-0R4 Bf0) & ( for C be OrdinalORDINAL1M3 holds succORDINAL1K1 C inTARSKIR2 succORDINAL1K1 Af0 implies fi .FUNCT-1K1 succORDINAL1K1 C =XBOOLE-0R4 Cf2(C,fi .FUNCT-1K1 C))) & ( for C be OrdinalORDINAL1M3 holds (C inTARSKIR2 succORDINAL1K1 Af0 & C <>HIDDENR2 0ORDINAL1K5) & C be limit-ordinalORDINAL1V4 implies fi .FUNCT-1K1 C =XBOOLE-0R4 Df2(C,fi |RELAT-1K8 C))) implies A1 =XBOOLE-0R4 A2)"
sorry

theorem ordinal2_sch_14:
  fixes Ff1 Bf0 Cf2 Df2 
  assumes
[ty_func]: "\<And> x1. x1 be OrdinalORDINAL1M3 \<Longrightarrow> Ff1(x1) be OrdinalORDINAL1M3" and
  [ty]: "Bf0 be OrdinalORDINAL1M3" and
  [ty_func]: "\<And> x1 x2. x1 be OrdinalORDINAL1M3 \<Longrightarrow> x2 be OrdinalORDINAL1M3 \<Longrightarrow> Cf2(x1,x2) be OrdinalORDINAL1M3" and
  [ty_func]: "\<And> x1 x2. x1 be OrdinalORDINAL1M3 \<Longrightarrow> x2 be SequenceORDINAL1M4 \<Longrightarrow> Df2(x1,x2) be OrdinalORDINAL1M3" and
   A1: " for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds B =XBOOLE-0R4 Ff1(A) iff ( ex fi be Ordinal-SequenceORDINAL2M1 st (((B =XBOOLE-0R4 lastORDINAL2K1 fi & domRELAT-1K1 fi =XBOOLE-0R4 succORDINAL1K1 A) & fi .FUNCT-1K1 (0ORDINAL1K5) =XBOOLE-0R4 Bf0) & ( for C be OrdinalORDINAL1M3 holds succORDINAL1K1 C inTARSKIR2 succORDINAL1K1 A implies fi .FUNCT-1K1 succORDINAL1K1 C =XBOOLE-0R4 Cf2(C,fi .FUNCT-1K1 C))) & ( for C be OrdinalORDINAL1M3 holds (C inTARSKIR2 succORDINAL1K1 A & C <>HIDDENR2 0ORDINAL1K5) & C be limit-ordinalORDINAL1V4 implies fi .FUNCT-1K1 C =XBOOLE-0R4 Df2(C,fi |RELAT-1K8 C)))"
  shows "Ff1(0ORDINAL1K5) =XBOOLE-0R4 Bf0"
sorry

theorem ordinal2_sch_15:
  fixes Bf0 Cf2 Df2 Ff1 
  assumes
[ty]: "Bf0 be OrdinalORDINAL1M3" and
  [ty_func]: "\<And> x1 x2. x1 be OrdinalORDINAL1M3 \<Longrightarrow> x2 be OrdinalORDINAL1M3 \<Longrightarrow> Cf2(x1,x2) be OrdinalORDINAL1M3" and
  [ty_func]: "\<And> x1 x2. x1 be OrdinalORDINAL1M3 \<Longrightarrow> x2 be SequenceORDINAL1M4 \<Longrightarrow> Df2(x1,x2) be OrdinalORDINAL1M3" and
  [ty_func]: "\<And> x1. x1 be OrdinalORDINAL1M3 \<Longrightarrow> Ff1(x1) be OrdinalORDINAL1M3" and
   A1: " for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds B =XBOOLE-0R4 Ff1(A) iff ( ex fi be Ordinal-SequenceORDINAL2M1 st (((B =XBOOLE-0R4 lastORDINAL2K1 fi & domRELAT-1K1 fi =XBOOLE-0R4 succORDINAL1K1 A) & fi .FUNCT-1K1 (0ORDINAL1K5) =XBOOLE-0R4 Bf0) & ( for C be OrdinalORDINAL1M3 holds succORDINAL1K1 C inTARSKIR2 succORDINAL1K1 A implies fi .FUNCT-1K1 succORDINAL1K1 C =XBOOLE-0R4 Cf2(C,fi .FUNCT-1K1 C))) & ( for C be OrdinalORDINAL1M3 holds (C inTARSKIR2 succORDINAL1K1 A & C <>HIDDENR2 0ORDINAL1K5) & C be limit-ordinalORDINAL1V4 implies fi .FUNCT-1K1 C =XBOOLE-0R4 Df2(C,fi |RELAT-1K8 C)))"
  shows " for A be OrdinalORDINAL1M3 holds Ff1(succORDINAL1K1 A) =XBOOLE-0R4 Cf2(A,Ff1(A))"
sorry

theorem ordinal2_sch_16:
  fixes fif0 Af0 Ff1 Bf0 Cf2 Df2 
  assumes
[ty]: "fif0 be Ordinal-SequenceORDINAL2M1" and
  [ty]: "Af0 be OrdinalORDINAL1M3" and
  [ty_func]: "\<And> x1. x1 be OrdinalORDINAL1M3 \<Longrightarrow> Ff1(x1) be OrdinalORDINAL1M3" and
  [ty]: "Bf0 be OrdinalORDINAL1M3" and
  [ty_func]: "\<And> x1 x2. x1 be OrdinalORDINAL1M3 \<Longrightarrow> x2 be OrdinalORDINAL1M3 \<Longrightarrow> Cf2(x1,x2) be OrdinalORDINAL1M3" and
  [ty_func]: "\<And> x1 x2. x1 be OrdinalORDINAL1M3 \<Longrightarrow> x2 be SequenceORDINAL1M4 \<Longrightarrow> Df2(x1,x2) be OrdinalORDINAL1M3" and
   A1: " for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds B =XBOOLE-0R4 Ff1(A) iff ( ex fi be Ordinal-SequenceORDINAL2M1 st (((B =XBOOLE-0R4 lastORDINAL2K1 fi & domRELAT-1K1 fi =XBOOLE-0R4 succORDINAL1K1 A) & fi .FUNCT-1K1 (0ORDINAL1K5) =XBOOLE-0R4 Bf0) & ( for C be OrdinalORDINAL1M3 holds succORDINAL1K1 C inTARSKIR2 succORDINAL1K1 A implies fi .FUNCT-1K1 succORDINAL1K1 C =XBOOLE-0R4 Cf2(C,fi .FUNCT-1K1 C))) & ( for C be OrdinalORDINAL1M3 holds (C inTARSKIR2 succORDINAL1K1 A & C <>HIDDENR2 0ORDINAL1K5) & C be limit-ordinalORDINAL1V4 implies fi .FUNCT-1K1 C =XBOOLE-0R4 Df2(C,fi |RELAT-1K8 C)))" and
   A2: "Af0 <>HIDDENR2 0ORDINAL1K5 & Af0 be limit-ordinalORDINAL1V4" and
   A3: "domRELAT-1K1 fif0 =XBOOLE-0R4 Af0" and
   A4: " for A be OrdinalORDINAL1M3 holds A inTARSKIR2 Af0 implies fif0 .FUNCT-1K1 A =XBOOLE-0R4 Ff1(A)"
  shows "Ff1(Af0) =XBOOLE-0R4 Df2(Af0,fif0)"
sorry

mdef ordinal2_def_5 ("supORDINAL2K4  _ " [300]300 ) where
  mlet "L be SequenceORDINAL1M4"
"func supORDINAL2K4 L \<rightarrow> OrdinalORDINAL1M3 equals
  supORDINAL2K3 (rngFUNCT-1K2 L)"
proof-
  (*coherence*)
    show "supORDINAL2K3 (rngFUNCT-1K2 L) be OrdinalORDINAL1M3"
       sorry
qed "sorry"

mdef ordinal2_def_6 ("infORDINAL2K5  _ " [228]228 ) where
  mlet "L be SequenceORDINAL1M4"
"func infORDINAL2K5 L \<rightarrow> OrdinalORDINAL1M3 equals
  infORDINAL2K2 (rngFUNCT-1K2 L)"
proof-
  (*coherence*)
    show "infORDINAL2K2 (rngFUNCT-1K2 L) be OrdinalORDINAL1M3"
       sorry
qed "sorry"

mtheorem ordinal2_th_26:
" for L be SequenceORDINAL1M4 holds supORDINAL2K4 L =XBOOLE-0R4 supORDINAL2K3 (rngFUNCT-1K2 L) & infORDINAL2K5 L =XBOOLE-0R4 infORDINAL2K2 (rngFUNCT-1K2 L)"
   sorry

mdef ordinal2_def_7 ("lim-supORDINAL2K6  _ " [228]228 ) where
  mlet "L be SequenceORDINAL1M4"
"func lim-supORDINAL2K6 L \<rightarrow> OrdinalORDINAL1M3 means
  \<lambda>it.  ex fi be Ordinal-SequenceORDINAL2M1 st (it =XBOOLE-0R4 infORDINAL2K5 fi & domRELAT-1K1 fi =XBOOLE-0R4 domRELAT-1K1 L) & ( for A be OrdinalORDINAL1M3 holds A inTARSKIR2 domRELAT-1K1 L implies fi .FUNCT-1K1 A =XBOOLE-0R4 supORDINAL2K3 (rngFUNCT-1K2 (L |RELAT-1K8 (domRELAT-1K1 L \\SUBSET-1K6 A))))"
proof-
  (*existence*)
    show " ex it be OrdinalORDINAL1M3 st  ex fi be Ordinal-SequenceORDINAL2M1 st (it =XBOOLE-0R4 infORDINAL2K5 fi & domRELAT-1K1 fi =XBOOLE-0R4 domRELAT-1K1 L) & ( for A be OrdinalORDINAL1M3 holds A inTARSKIR2 domRELAT-1K1 L implies fi .FUNCT-1K1 A =XBOOLE-0R4 supORDINAL2K3 (rngFUNCT-1K2 (L |RELAT-1K8 (domRELAT-1K1 L \\SUBSET-1K6 A))))"
sorry
  (*uniqueness*)
    show " for it1 be OrdinalORDINAL1M3 holds  for it2 be OrdinalORDINAL1M3 holds ( ex fi be Ordinal-SequenceORDINAL2M1 st (it1 =XBOOLE-0R4 infORDINAL2K5 fi & domRELAT-1K1 fi =XBOOLE-0R4 domRELAT-1K1 L) & ( for A be OrdinalORDINAL1M3 holds A inTARSKIR2 domRELAT-1K1 L implies fi .FUNCT-1K1 A =XBOOLE-0R4 supORDINAL2K3 (rngFUNCT-1K2 (L |RELAT-1K8 (domRELAT-1K1 L \\SUBSET-1K6 A))))) & ( ex fi be Ordinal-SequenceORDINAL2M1 st (it2 =XBOOLE-0R4 infORDINAL2K5 fi & domRELAT-1K1 fi =XBOOLE-0R4 domRELAT-1K1 L) & ( for A be OrdinalORDINAL1M3 holds A inTARSKIR2 domRELAT-1K1 L implies fi .FUNCT-1K1 A =XBOOLE-0R4 supORDINAL2K3 (rngFUNCT-1K2 (L |RELAT-1K8 (domRELAT-1K1 L \\SUBSET-1K6 A))))) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mdef ordinal2_def_8 ("lim-infORDINAL2K7  _ " [228]228 ) where
  mlet "L be SequenceORDINAL1M4"
"func lim-infORDINAL2K7 L \<rightarrow> OrdinalORDINAL1M3 means
  \<lambda>it.  ex fi be Ordinal-SequenceORDINAL2M1 st (it =XBOOLE-0R4 supORDINAL2K4 fi & domRELAT-1K1 fi =XBOOLE-0R4 domRELAT-1K1 L) & ( for A be OrdinalORDINAL1M3 holds A inTARSKIR2 domRELAT-1K1 L implies fi .FUNCT-1K1 A =XBOOLE-0R4 infORDINAL2K2 (rngFUNCT-1K2 (L |RELAT-1K8 (domRELAT-1K1 L \\SUBSET-1K6 A))))"
proof-
  (*existence*)
    show " ex it be OrdinalORDINAL1M3 st  ex fi be Ordinal-SequenceORDINAL2M1 st (it =XBOOLE-0R4 supORDINAL2K4 fi & domRELAT-1K1 fi =XBOOLE-0R4 domRELAT-1K1 L) & ( for A be OrdinalORDINAL1M3 holds A inTARSKIR2 domRELAT-1K1 L implies fi .FUNCT-1K1 A =XBOOLE-0R4 infORDINAL2K2 (rngFUNCT-1K2 (L |RELAT-1K8 (domRELAT-1K1 L \\SUBSET-1K6 A))))"
sorry
  (*uniqueness*)
    show " for it1 be OrdinalORDINAL1M3 holds  for it2 be OrdinalORDINAL1M3 holds ( ex fi be Ordinal-SequenceORDINAL2M1 st (it1 =XBOOLE-0R4 supORDINAL2K4 fi & domRELAT-1K1 fi =XBOOLE-0R4 domRELAT-1K1 L) & ( for A be OrdinalORDINAL1M3 holds A inTARSKIR2 domRELAT-1K1 L implies fi .FUNCT-1K1 A =XBOOLE-0R4 infORDINAL2K2 (rngFUNCT-1K2 (L |RELAT-1K8 (domRELAT-1K1 L \\SUBSET-1K6 A))))) & ( ex fi be Ordinal-SequenceORDINAL2M1 st (it2 =XBOOLE-0R4 supORDINAL2K4 fi & domRELAT-1K1 fi =XBOOLE-0R4 domRELAT-1K1 L) & ( for A be OrdinalORDINAL1M3 holds A inTARSKIR2 domRELAT-1K1 L implies fi .FUNCT-1K1 A =XBOOLE-0R4 infORDINAL2K2 (rngFUNCT-1K2 (L |RELAT-1K8 (domRELAT-1K1 L \\SUBSET-1K6 A))))) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mdef ordinal2_def_9 (" _ is-limes-ofORDINAL2R1  _ " [50,50]50 ) where
  mlet "A be OrdinalORDINAL1M3", "fi be Ordinal-SequenceORDINAL2M1"
"pred A is-limes-ofORDINAL2R1 fi means
   ex B be OrdinalORDINAL1M3 st B inTARSKIR2 domRELAT-1K1 fi & ( for C be OrdinalORDINAL1M3 holds B c=ORDINAL1R1 C & C inTARSKIR2 domRELAT-1K1 fi implies fi .FUNCT-1K1 C =XBOOLE-0R4 0ORDINAL1K5) if A =XBOOLE-0R4 0ORDINAL1K5 otherwise  for B be OrdinalORDINAL1M3 holds  for C be OrdinalORDINAL1M3 holds B inTARSKIR2 A & A inTARSKIR2 C implies ( ex D be OrdinalORDINAL1M3 st D inTARSKIR2 domRELAT-1K1 fi & ( for E be OrdinalORDINAL1M3 holds D c=ORDINAL1R1 E & E inTARSKIR2 domRELAT-1K1 fi implies B inTARSKIR2 fi .FUNCT-1K1 E & fi .FUNCT-1K1 E inTARSKIR2 C))"
proof-
  (*consistency*)
    show " True "
       sorry
qed "sorry"

mdef ordinal2_def_10 ("limORDINAL2K8  _ " [164]164 ) where
  mlet "fi be Ordinal-SequenceORDINAL2M1"
"assume  ex A be OrdinalORDINAL1M3 st A is-limes-ofORDINAL2R1 fi func limORDINAL2K8 fi \<rightarrow> OrdinalORDINAL1M3 means
  \<lambda>it. it is-limes-ofORDINAL2R1 fi"
proof-
  (*existence*)
    show "( ex A be OrdinalORDINAL1M3 st A is-limes-ofORDINAL2R1 fi) implies ( ex it be OrdinalORDINAL1M3 st it is-limes-ofORDINAL2R1 fi)"
sorry
  (*uniqueness*)
    show "( ex A be OrdinalORDINAL1M3 st A is-limes-ofORDINAL2R1 fi) implies ( for it1 be OrdinalORDINAL1M3 holds  for it2 be OrdinalORDINAL1M3 holds it1 is-limes-ofORDINAL2R1 fi & it2 is-limes-ofORDINAL2R1 fi implies it1 =HIDDENR1 it2)"
sorry
qed "sorry"

mdef ordinal2_def_11 ("limORDINAL2K9'( _ , _ ')" [0,0]164 ) where
  mlet "A be OrdinalORDINAL1M3", "fi be Ordinal-SequenceORDINAL2M1"
"func limORDINAL2K9(A,fi) \<rightarrow> OrdinalORDINAL1M3 equals
  limORDINAL2K8 fi |RELAT-1K8 A"
proof-
  (*coherence*)
    show "limORDINAL2K8 fi |RELAT-1K8 A be OrdinalORDINAL1M3"
       sorry
qed "sorry"

mdef ordinal2_def_12 ("increasingORDINAL2V2" 70 ) where
"attr increasingORDINAL2V2 for Ordinal-SequenceORDINAL2M1 means
  (\<lambda>L.  for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds A inTARSKIR2 B & B inTARSKIR2 domRELAT-1K1 L implies L .FUNCT-1K1 A inTARSKIR2 L .FUNCT-1K1 B)"..

mdef ordinal2_def_13 ("continuousORDINAL2V3" 70 ) where
"attr continuousORDINAL2V3 for Ordinal-SequenceORDINAL2M1 means
  (\<lambda>L.  for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds ((A inTARSKIR2 domRELAT-1K1 L & A <>HIDDENR2 0ORDINAL1K5) & A be limit-ordinalORDINAL1V4) & B =XBOOLE-0R4 L .FUNCT-1K1 A implies B is-limes-ofORDINAL2R1 L |RELAT-1K8 A)"..

mdef ordinal2_def_14 (" _ +^ORDINAL2K10  _ " [132,132]132 ) where
  mlet "A be OrdinalORDINAL1M3", "B be OrdinalORDINAL1M3"
"func A +^ORDINAL2K10 B \<rightarrow> OrdinalORDINAL1M3 means
  \<lambda>it.  ex fi be Ordinal-SequenceORDINAL2M1 st (((it =XBOOLE-0R4 lastORDINAL2K1 fi & domRELAT-1K1 fi =XBOOLE-0R4 succORDINAL1K1 B) & fi .FUNCT-1K1 (0ORDINAL1K5) =XBOOLE-0R4 A) & ( for C be OrdinalORDINAL1M3 holds succORDINAL1K1 C inTARSKIR2 succORDINAL1K1 B implies fi .FUNCT-1K1 succORDINAL1K1 C =XBOOLE-0R4 succORDINAL1K1 (fi .FUNCT-1K1 C))) & ( for C be OrdinalORDINAL1M3 holds (C inTARSKIR2 succORDINAL1K1 B & C <>HIDDENR2 0ORDINAL1K5) & C be limit-ordinalORDINAL1V4 implies fi .FUNCT-1K1 C =XBOOLE-0R4 supORDINAL2K4 (fi |RELAT-1K8 C))"
proof-
  (*existence*)
    show " ex it be OrdinalORDINAL1M3 st  ex fi be Ordinal-SequenceORDINAL2M1 st (((it =XBOOLE-0R4 lastORDINAL2K1 fi & domRELAT-1K1 fi =XBOOLE-0R4 succORDINAL1K1 B) & fi .FUNCT-1K1 (0ORDINAL1K5) =XBOOLE-0R4 A) & ( for C be OrdinalORDINAL1M3 holds succORDINAL1K1 C inTARSKIR2 succORDINAL1K1 B implies fi .FUNCT-1K1 succORDINAL1K1 C =XBOOLE-0R4 succORDINAL1K1 (fi .FUNCT-1K1 C))) & ( for C be OrdinalORDINAL1M3 holds (C inTARSKIR2 succORDINAL1K1 B & C <>HIDDENR2 0ORDINAL1K5) & C be limit-ordinalORDINAL1V4 implies fi .FUNCT-1K1 C =XBOOLE-0R4 supORDINAL2K4 (fi |RELAT-1K8 C))"
sorry
  (*uniqueness*)
    show " for it1 be OrdinalORDINAL1M3 holds  for it2 be OrdinalORDINAL1M3 holds ( ex fi be Ordinal-SequenceORDINAL2M1 st (((it1 =XBOOLE-0R4 lastORDINAL2K1 fi & domRELAT-1K1 fi =XBOOLE-0R4 succORDINAL1K1 B) & fi .FUNCT-1K1 (0ORDINAL1K5) =XBOOLE-0R4 A) & ( for C be OrdinalORDINAL1M3 holds succORDINAL1K1 C inTARSKIR2 succORDINAL1K1 B implies fi .FUNCT-1K1 succORDINAL1K1 C =XBOOLE-0R4 succORDINAL1K1 (fi .FUNCT-1K1 C))) & ( for C be OrdinalORDINAL1M3 holds (C inTARSKIR2 succORDINAL1K1 B & C <>HIDDENR2 0ORDINAL1K5) & C be limit-ordinalORDINAL1V4 implies fi .FUNCT-1K1 C =XBOOLE-0R4 supORDINAL2K4 (fi |RELAT-1K8 C))) & ( ex fi be Ordinal-SequenceORDINAL2M1 st (((it2 =XBOOLE-0R4 lastORDINAL2K1 fi & domRELAT-1K1 fi =XBOOLE-0R4 succORDINAL1K1 B) & fi .FUNCT-1K1 (0ORDINAL1K5) =XBOOLE-0R4 A) & ( for C be OrdinalORDINAL1M3 holds succORDINAL1K1 C inTARSKIR2 succORDINAL1K1 B implies fi .FUNCT-1K1 succORDINAL1K1 C =XBOOLE-0R4 succORDINAL1K1 (fi .FUNCT-1K1 C))) & ( for C be OrdinalORDINAL1M3 holds (C inTARSKIR2 succORDINAL1K1 B & C <>HIDDENR2 0ORDINAL1K5) & C be limit-ordinalORDINAL1V4 implies fi .FUNCT-1K1 C =XBOOLE-0R4 supORDINAL2K4 (fi |RELAT-1K8 C))) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mdef ordinal2_def_15 (" _ *^ORDINAL2K11  _ " [164,164]164 ) where
  mlet "A be OrdinalORDINAL1M3", "B be OrdinalORDINAL1M3"
"func A *^ORDINAL2K11 B \<rightarrow> OrdinalORDINAL1M3 means
  \<lambda>it.  ex fi be Ordinal-SequenceORDINAL2M1 st (((it =XBOOLE-0R4 lastORDINAL2K1 fi & domRELAT-1K1 fi =XBOOLE-0R4 succORDINAL1K1 A) & fi .FUNCT-1K1 (0ORDINAL1K5) =XBOOLE-0R4 0ORDINAL1K5) & ( for C be OrdinalORDINAL1M3 holds succORDINAL1K1 C inTARSKIR2 succORDINAL1K1 A implies fi .FUNCT-1K1 succORDINAL1K1 C =XBOOLE-0R4 fi .FUNCT-1K1 C +^ORDINAL2K10 B)) & ( for C be OrdinalORDINAL1M3 holds (C inTARSKIR2 succORDINAL1K1 A & C <>HIDDENR2 0ORDINAL1K5) & C be limit-ordinalORDINAL1V4 implies fi .FUNCT-1K1 C =XBOOLE-0R4 unionTARSKIK3 supORDINAL2K4 (fi |RELAT-1K8 C))"
proof-
  (*existence*)
    show " ex it be OrdinalORDINAL1M3 st  ex fi be Ordinal-SequenceORDINAL2M1 st (((it =XBOOLE-0R4 lastORDINAL2K1 fi & domRELAT-1K1 fi =XBOOLE-0R4 succORDINAL1K1 A) & fi .FUNCT-1K1 (0ORDINAL1K5) =XBOOLE-0R4 0ORDINAL1K5) & ( for C be OrdinalORDINAL1M3 holds succORDINAL1K1 C inTARSKIR2 succORDINAL1K1 A implies fi .FUNCT-1K1 succORDINAL1K1 C =XBOOLE-0R4 fi .FUNCT-1K1 C +^ORDINAL2K10 B)) & ( for C be OrdinalORDINAL1M3 holds (C inTARSKIR2 succORDINAL1K1 A & C <>HIDDENR2 0ORDINAL1K5) & C be limit-ordinalORDINAL1V4 implies fi .FUNCT-1K1 C =XBOOLE-0R4 unionTARSKIK3 supORDINAL2K4 (fi |RELAT-1K8 C))"
sorry
  (*uniqueness*)
    show " for it1 be OrdinalORDINAL1M3 holds  for it2 be OrdinalORDINAL1M3 holds ( ex fi be Ordinal-SequenceORDINAL2M1 st (((it1 =XBOOLE-0R4 lastORDINAL2K1 fi & domRELAT-1K1 fi =XBOOLE-0R4 succORDINAL1K1 A) & fi .FUNCT-1K1 (0ORDINAL1K5) =XBOOLE-0R4 0ORDINAL1K5) & ( for C be OrdinalORDINAL1M3 holds succORDINAL1K1 C inTARSKIR2 succORDINAL1K1 A implies fi .FUNCT-1K1 succORDINAL1K1 C =XBOOLE-0R4 fi .FUNCT-1K1 C +^ORDINAL2K10 B)) & ( for C be OrdinalORDINAL1M3 holds (C inTARSKIR2 succORDINAL1K1 A & C <>HIDDENR2 0ORDINAL1K5) & C be limit-ordinalORDINAL1V4 implies fi .FUNCT-1K1 C =XBOOLE-0R4 unionTARSKIK3 supORDINAL2K4 (fi |RELAT-1K8 C))) & ( ex fi be Ordinal-SequenceORDINAL2M1 st (((it2 =XBOOLE-0R4 lastORDINAL2K1 fi & domRELAT-1K1 fi =XBOOLE-0R4 succORDINAL1K1 A) & fi .FUNCT-1K1 (0ORDINAL1K5) =XBOOLE-0R4 0ORDINAL1K5) & ( for C be OrdinalORDINAL1M3 holds succORDINAL1K1 C inTARSKIR2 succORDINAL1K1 A implies fi .FUNCT-1K1 succORDINAL1K1 C =XBOOLE-0R4 fi .FUNCT-1K1 C +^ORDINAL2K10 B)) & ( for C be OrdinalORDINAL1M3 holds (C inTARSKIR2 succORDINAL1K1 A & C <>HIDDENR2 0ORDINAL1K5) & C be limit-ordinalORDINAL1V4 implies fi .FUNCT-1K1 C =XBOOLE-0R4 unionTARSKIK3 supORDINAL2K4 (fi |RELAT-1K8 C))) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mtheorem ordinal2_cl_6:
  mlet "O be OrdinalORDINAL1M3"
"cluster note-that ordinalORDINAL1V3 for ElementSUBSET-1M1-of O"
proof
(*coherence*)
  show " for it be ElementSUBSET-1M1-of O holds it be ordinalORDINAL1V3"
     sorry
qed "sorry"

mdef ordinal2_def_16 ("expORDINAL2K12'( _ , _ ')" [0,0]164 ) where
  mlet "A be OrdinalORDINAL1M3", "B be OrdinalORDINAL1M3"
"func expORDINAL2K12(A,B) \<rightarrow> OrdinalORDINAL1M3 means
  \<lambda>it.  ex fi be Ordinal-SequenceORDINAL2M1 st (((it =XBOOLE-0R4 lastORDINAL2K1 fi & domRELAT-1K1 fi =XBOOLE-0R4 succORDINAL1K1 B) & fi .FUNCT-1K1 (0ORDINAL1K5) =XBOOLE-0R4 \<one>\<^sub>M) & ( for C be OrdinalORDINAL1M3 holds succORDINAL1K1 C inTARSKIR2 succORDINAL1K1 B implies fi .FUNCT-1K1 succORDINAL1K1 C =XBOOLE-0R4 A *^ORDINAL2K11 fi .FUNCT-1K1 C)) & ( for C be OrdinalORDINAL1M3 holds (C inTARSKIR2 succORDINAL1K1 B & C <>HIDDENR2 0ORDINAL1K5) & C be limit-ordinalORDINAL1V4 implies fi .FUNCT-1K1 C =XBOOLE-0R4 limORDINAL2K8 fi |RELAT-1K8 C)"
proof-
  (*existence*)
    show " ex it be OrdinalORDINAL1M3 st  ex fi be Ordinal-SequenceORDINAL2M1 st (((it =XBOOLE-0R4 lastORDINAL2K1 fi & domRELAT-1K1 fi =XBOOLE-0R4 succORDINAL1K1 B) & fi .FUNCT-1K1 (0ORDINAL1K5) =XBOOLE-0R4 \<one>\<^sub>M) & ( for C be OrdinalORDINAL1M3 holds succORDINAL1K1 C inTARSKIR2 succORDINAL1K1 B implies fi .FUNCT-1K1 succORDINAL1K1 C =XBOOLE-0R4 A *^ORDINAL2K11 fi .FUNCT-1K1 C)) & ( for C be OrdinalORDINAL1M3 holds (C inTARSKIR2 succORDINAL1K1 B & C <>HIDDENR2 0ORDINAL1K5) & C be limit-ordinalORDINAL1V4 implies fi .FUNCT-1K1 C =XBOOLE-0R4 limORDINAL2K8 fi |RELAT-1K8 C)"
sorry
  (*uniqueness*)
    show " for it1 be OrdinalORDINAL1M3 holds  for it2 be OrdinalORDINAL1M3 holds ( ex fi be Ordinal-SequenceORDINAL2M1 st (((it1 =XBOOLE-0R4 lastORDINAL2K1 fi & domRELAT-1K1 fi =XBOOLE-0R4 succORDINAL1K1 B) & fi .FUNCT-1K1 (0ORDINAL1K5) =XBOOLE-0R4 \<one>\<^sub>M) & ( for C be OrdinalORDINAL1M3 holds succORDINAL1K1 C inTARSKIR2 succORDINAL1K1 B implies fi .FUNCT-1K1 succORDINAL1K1 C =XBOOLE-0R4 A *^ORDINAL2K11 fi .FUNCT-1K1 C)) & ( for C be OrdinalORDINAL1M3 holds (C inTARSKIR2 succORDINAL1K1 B & C <>HIDDENR2 0ORDINAL1K5) & C be limit-ordinalORDINAL1V4 implies fi .FUNCT-1K1 C =XBOOLE-0R4 limORDINAL2K8 fi |RELAT-1K8 C)) & ( ex fi be Ordinal-SequenceORDINAL2M1 st (((it2 =XBOOLE-0R4 lastORDINAL2K1 fi & domRELAT-1K1 fi =XBOOLE-0R4 succORDINAL1K1 B) & fi .FUNCT-1K1 (0ORDINAL1K5) =XBOOLE-0R4 \<one>\<^sub>M) & ( for C be OrdinalORDINAL1M3 holds succORDINAL1K1 C inTARSKIR2 succORDINAL1K1 B implies fi .FUNCT-1K1 succORDINAL1K1 C =XBOOLE-0R4 A *^ORDINAL2K11 fi .FUNCT-1K1 C)) & ( for C be OrdinalORDINAL1M3 holds (C inTARSKIR2 succORDINAL1K1 B & C <>HIDDENR2 0ORDINAL1K5) & C be limit-ordinalORDINAL1V4 implies fi .FUNCT-1K1 C =XBOOLE-0R4 limORDINAL2K8 fi |RELAT-1K8 C)) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mtheorem ordinal2_th_27:
" for A be OrdinalORDINAL1M3 holds A +^ORDINAL2K10 0ORDINAL1K5 =XBOOLE-0R4 A"
sorry

mtheorem ordinal2_th_28:
" for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds A +^ORDINAL2K10 succORDINAL1K1 B =XBOOLE-0R4 succORDINAL1K1 (A +^ORDINAL2K10 B)"
sorry

mtheorem ordinal2_th_29:
" for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds B <>HIDDENR2 0ORDINAL1K5 & B be limit-ordinalORDINAL1V4 implies ( for fi be Ordinal-SequenceORDINAL2M1 holds domRELAT-1K1 fi =XBOOLE-0R4 B & ( for C be OrdinalORDINAL1M3 holds C inTARSKIR2 B implies fi .FUNCT-1K1 C =XBOOLE-0R4 A +^ORDINAL2K10 C) implies A +^ORDINAL2K10 B =XBOOLE-0R4 supORDINAL2K4 fi)"
sorry

mtheorem ordinal2_th_30:
" for A be OrdinalORDINAL1M3 holds 0ORDINAL1K5 +^ORDINAL2K10 A =XBOOLE-0R4 A"
sorry

mlemma ordinal2_lm_1:
"\<one>\<^sub>M =XBOOLE-0R4 succORDINAL1K1 (0ORDINAL1K5)"
   sorry

mtheorem ordinal2_th_31:
" for A be OrdinalORDINAL1M3 holds A +^ORDINAL2K10 \<one>\<^sub>M =XBOOLE-0R4 succORDINAL1K1 A"
sorry

mtheorem ordinal2_th_32:
" for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds  for C be OrdinalORDINAL1M3 holds A inTARSKIR2 B implies C +^ORDINAL2K10 A inTARSKIR2 C +^ORDINAL2K10 B"
sorry

mtheorem ordinal2_th_33:
" for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds  for C be OrdinalORDINAL1M3 holds A c=ORDINAL1R1 B implies C +^ORDINAL2K10 A c=ORDINAL1R1 C +^ORDINAL2K10 B"
sorry

mtheorem ordinal2_th_34:
" for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds  for C be OrdinalORDINAL1M3 holds A c=ORDINAL1R1 B implies A +^ORDINAL2K10 C c=ORDINAL1R1 B +^ORDINAL2K10 C"
sorry

mtheorem ordinal2_th_35:
" for A be OrdinalORDINAL1M3 holds (0ORDINAL1K5)*^ORDINAL2K11 A =XBOOLE-0R4 0ORDINAL1K5"
sorry

mtheorem ordinal2_th_36:
" for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds succORDINAL1K1 B *^ORDINAL2K11 A =XBOOLE-0R4 B *^ORDINAL2K11 A +^ORDINAL2K10 A"
sorry

mtheorem ordinal2_th_37:
" for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds B <>HIDDENR2 0ORDINAL1K5 & B be limit-ordinalORDINAL1V4 implies ( for fi be Ordinal-SequenceORDINAL2M1 holds domRELAT-1K1 fi =XBOOLE-0R4 B & ( for C be OrdinalORDINAL1M3 holds C inTARSKIR2 B implies fi .FUNCT-1K1 C =XBOOLE-0R4 C *^ORDINAL2K11 A) implies B *^ORDINAL2K11 A =XBOOLE-0R4 unionTARSKIK3 supORDINAL2K4 fi)"
sorry

mtheorem ordinal2_th_38:
" for A be OrdinalORDINAL1M3 holds A *^ORDINAL2K11 (0ORDINAL1K5) =XBOOLE-0R4 0ORDINAL1K5"
sorry

mtheorem ordinal2_th_39:
" for A be OrdinalORDINAL1M3 holds \<one>\<^sub>M *^ORDINAL2K11 A =XBOOLE-0R4 A & A *^ORDINAL2K11 \<one>\<^sub>M =XBOOLE-0R4 A"
sorry

mtheorem ordinal2_th_40:
" for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds  for C be OrdinalORDINAL1M3 holds C <>HIDDENR2 0ORDINAL1K5 & A inTARSKIR2 B implies A *^ORDINAL2K11 C inTARSKIR2 B *^ORDINAL2K11 C"
sorry

mtheorem ordinal2_th_41:
" for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds  for C be OrdinalORDINAL1M3 holds A c=ORDINAL1R1 B implies A *^ORDINAL2K11 C c=ORDINAL1R1 B *^ORDINAL2K11 C"
sorry

mtheorem ordinal2_th_42:
" for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds  for C be OrdinalORDINAL1M3 holds A c=ORDINAL1R1 B implies C *^ORDINAL2K11 A c=ORDINAL1R1 C *^ORDINAL2K11 B"
sorry

mtheorem ordinal2_th_43:
" for A be OrdinalORDINAL1M3 holds expORDINAL2K12(A,0ORDINAL1K5) =XBOOLE-0R4 \<one>\<^sub>M"
sorry

mtheorem ordinal2_th_44:
" for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds expORDINAL2K12(A,succORDINAL1K1 B) =XBOOLE-0R4 A *^ORDINAL2K11 (expORDINAL2K12(A,B))"
sorry

mtheorem ordinal2_th_45:
" for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds B <>HIDDENR2 0ORDINAL1K5 & B be limit-ordinalORDINAL1V4 implies ( for fi be Ordinal-SequenceORDINAL2M1 holds domRELAT-1K1 fi =XBOOLE-0R4 B & ( for C be OrdinalORDINAL1M3 holds C inTARSKIR2 B implies fi .FUNCT-1K1 C =XBOOLE-0R4 expORDINAL2K12(A,C)) implies expORDINAL2K12(A,B) =XBOOLE-0R4 limORDINAL2K8 fi)"
sorry

mtheorem ordinal2_th_46:
" for A be OrdinalORDINAL1M3 holds expORDINAL2K12(A,\<one>\<^sub>M) =XBOOLE-0R4 A & expORDINAL2K12(\<one>\<^sub>M,A) =XBOOLE-0R4 \<one>\<^sub>M"
sorry

mtheorem ordinal2_th_47:
" for A be OrdinalORDINAL1M3 holds  ex B be OrdinalORDINAL1M3 st  ex C be OrdinalORDINAL1M3 st (B be limit-ordinalORDINAL1V4 & C be naturalORDINAL1V7) & A =XBOOLE-0R4 B +^ORDINAL2K10 C"
sorry

mtheorem ordinal2_cl_7:
  mlet "X be setHIDDENM2", "o be OrdinalORDINAL1M3"
"cluster X -->FUNCOP-1K7 o as-term-is Ordinal-yieldingORDINAL2V1"
proof
(*coherence*)
  show "X -->FUNCOP-1K7 o be Ordinal-yieldingORDINAL2V1"
sorry
qed "sorry"

mtheorem ordinal2_cl_8:
  mlet "O be OrdinalORDINAL1M3", "x be objectHIDDENM1"
"cluster O -->FUNCOP-1K7 x as-term-is Sequence-likeORDINAL1V5"
proof
(*coherence*)
  show "O -->FUNCOP-1K7 x be Sequence-likeORDINAL1V5"
    using funcop_1_th_13 sorry
qed "sorry"

mdef ordinal2_def_17 (" _ is-cofinal-withORDINAL2R2  _ " [50,50]50 ) where
  mlet "A be OrdinalORDINAL1M3", "B be OrdinalORDINAL1M3"
"pred A is-cofinal-withORDINAL2R2 B means
   ex xi be Ordinal-SequenceORDINAL2M1 st ((domRELAT-1K1 xi =XBOOLE-0R4 B & rngFUNCT-1K2 xi c=TARSKIR1 A) & xi be increasingORDINAL2V2) & A =XBOOLE-0R4 supORDINAL2K4 xi"..

mtheorem ORDINAL2R2_reflexivity:
" for B be OrdinalORDINAL1M3 holds B is-cofinal-withORDINAL2R2 B"
sorry

reserve e, u for "setHIDDENM2"
mtheorem ordinal2_th_48:
" for psi be Ordinal-SequenceORDINAL2M1 holds  for e be setHIDDENM2 holds e inTARSKIR2 rngFUNCT-1K2 psi implies e be OrdinalORDINAL1M3"
sorry

mtheorem ordinal2_th_49:
" for psi be Ordinal-SequenceORDINAL2M1 holds rngFUNCT-1K2 psi c=TARSKIR1 supORDINAL2K4 psi"
sorry

mtheorem ordinal2_th_50:
" for A be OrdinalORDINAL1M3 holds A is-cofinal-withORDINAL2R2 0ORDINAL1K5 implies A =XBOOLE-0R4 0ORDINAL1K5"
sorry

theorem ordinal2_sch_17:
  fixes af0 Pp1 
  assumes
[ty]: "af0 be NatORDINAL1M6" and
   A1: "Pp1(0ORDINAL1K5)" and
   A2: " for a be NatORDINAL1M6 holds Pp1(a) implies Pp1(succORDINAL1K1 a)"
  shows "Pp1(af0)"
sorry

mtheorem ordinal2_cl_9:
  mlet "a be NatORDINAL1M6", "b be NatORDINAL1M6"
"cluster a +^ORDINAL2K10 b as-term-is naturalORDINAL1V7"
proof
(*coherence*)
  show "a +^ORDINAL2K10 b be naturalORDINAL1V7"
sorry
qed "sorry"

mtheorem ordinal2_cl_10:
  mlet "x be setHIDDENM2", "y be setHIDDENM2", "a be NatORDINAL1M6", "b be NatORDINAL1M6"
"cluster IFEQFUNCOP-1K15(x,y,a,b) as-term-is naturalORDINAL1V7"
proof
(*coherence*)
  show "IFEQFUNCOP-1K15(x,y,a,b) be naturalORDINAL1V7"
sorry
qed "sorry"

theorem ordinal2_sch_18:
  fixes Af0 Gf2 
  assumes
[ty]: "Af0 be setHIDDENM2" and
  [ty_func]: "\<And> x1 x2. x1 be setHIDDENM2 \<Longrightarrow> x2 be setHIDDENM2 \<Longrightarrow> Gf2(x1,x2) be setHIDDENM2"
  shows " ex f be FunctionFUNCT-1M1 st (domRELAT-1K1 f =XBOOLE-0R4 omegaORDINAL1K4 & f .FUNCT-1K1 (0ORDINAL1K5) =XBOOLE-0R4 Af0) & ( for n be NatORDINAL1M6 holds f .FUNCT-1K1 succORDINAL1K1 n =XBOOLE-0R4 Gf2(n,f .FUNCT-1K1 n))"
sorry

reserve n for "NatORDINAL1M6"
theorem ordinal2_sch_19:
  fixes Af0 Ff0 Gf0 Pp3 
  assumes
[ty]: "Af0 be setHIDDENM2" and
  [ty]: "Ff0 be FunctionFUNCT-1M1" and
  [ty]: "Gf0 be FunctionFUNCT-1M1" and
   A1: "domRELAT-1K1 Ff0 =XBOOLE-0R4 omegaORDINAL1K4" and
   A2: "Ff0 .FUNCT-1K1 (0ORDINAL1K5) =XBOOLE-0R4 Af0" and
   A3: " for n be NatORDINAL1M6 holds Pp3(n,Ff0 .FUNCT-1K1 n,Ff0 .FUNCT-1K1 succORDINAL1K1 n)" and
   A4: "domRELAT-1K1 Gf0 =XBOOLE-0R4 omegaORDINAL1K4" and
   A5: "Gf0 .FUNCT-1K1 (0ORDINAL1K5) =XBOOLE-0R4 Af0" and
   A6: " for n be NatORDINAL1M6 holds Pp3(n,Gf0 .FUNCT-1K1 n,Gf0 .FUNCT-1K1 succORDINAL1K1 n)" and
   A7: " for n be NatORDINAL1M6 holds  for x be setHIDDENM2 holds  for y1 be setHIDDENM2 holds  for y2 be setHIDDENM2 holds Pp3(n,x,y1) & Pp3(n,x,y2) implies y1 =XBOOLE-0R4 y2"
  shows "Ff0 =FUNCT-1R1 Gf0"
sorry

theorem ordinal2_sch_20:
  fixes Af0 Ff2 Ff0 Gf0 
  assumes
[ty]: "Af0 be setHIDDENM2" and
  [ty_func]: "\<And> x1 x2. x1 be setHIDDENM2 \<Longrightarrow> x2 be setHIDDENM2 \<Longrightarrow> Ff2(x1,x2) be setHIDDENM2" and
  [ty]: "Ff0 be FunctionFUNCT-1M1" and
  [ty]: "Gf0 be FunctionFUNCT-1M1" and
   A1: "domRELAT-1K1 Ff0 =XBOOLE-0R4 omegaORDINAL1K4" and
   A2: "Ff0 .FUNCT-1K1 (0ORDINAL1K5) =XBOOLE-0R4 Af0" and
   A3: " for n be NatORDINAL1M6 holds Ff0 .FUNCT-1K1 succORDINAL1K1 n =XBOOLE-0R4 Ff2(n,Ff0 .FUNCT-1K1 n)" and
   A4: "domRELAT-1K1 Gf0 =XBOOLE-0R4 omegaORDINAL1K4" and
   A5: "Gf0 .FUNCT-1K1 (0ORDINAL1K5) =XBOOLE-0R4 Af0" and
   A6: " for n be NatORDINAL1M6 holds Gf0 .FUNCT-1K1 succORDINAL1K1 n =XBOOLE-0R4 Ff2(n,Gf0 .FUNCT-1K1 n)"
  shows "Ff0 =FUNCT-1R1 Gf0"
sorry

end
