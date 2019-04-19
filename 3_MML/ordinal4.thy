theory ordinal4
  imports classes2
   "../mizar_extension/E_number"
begin
(*begin*)
reserve phi, fi, psi for "Ordinal-SequenceORDINAL2M1"
reserve A, A1, B, C, D for "OrdinalORDINAL1M3"
reserve f, g for "FunctionFUNCT-1M1"
reserve X for "setHIDDENM2"
reserve x, y, z for "objectHIDDENM1"
mlemma ordinal4_lm_1:
"{}XBOOLE-0K1 inTARSKIR2 omegaORDINAL1K4"
  using ordinal1_def_11 sorry

mlemma ordinal4_lm_2:
"omegaORDINAL1K4 be limit-ordinalORDINAL1V4"
  using ordinal1_def_11 sorry

mlemma ordinal4_lm_3:
"\<one>\<^sub>M =XBOOLE-0R4 succORDINAL1K1 ({}XBOOLE-0K1)"
   sorry

mtheorem ordinal4_cl_1:
  mlet "L be Ordinal-SequenceORDINAL2M1"
"cluster lastORDINAL2K1 L as-term-is ordinalORDINAL1V3"
proof
(*coherence*)
  show "lastORDINAL2K1 L be ordinalORDINAL1V3"
     sorry
qed "sorry"

mtheorem ordinal4_th_1:
" for fi be Ordinal-SequenceORDINAL2M1 holds  for A be OrdinalORDINAL1M3 holds domRELAT-1K1 fi =XBOOLE-0R4 succORDINAL1K1 A implies lastORDINAL2K1 fi is-limes-ofORDINAL2R1 fi & limORDINAL2K8 fi =XBOOLE-0R4 lastORDINAL2K1 fi"
sorry

mdef ordinal4_def_1 (" _ ^ORDINAL4K1  _ " [164,164]164 ) where
  mlet "fi be SequenceORDINAL1M4", "psi be SequenceORDINAL1M4"
"func fi ^ORDINAL4K1 psi \<rightarrow> SequenceORDINAL1M4 means
  \<lambda>it. (domRELAT-1K1 it =XBOOLE-0R4 domRELAT-1K1 fi +^ORDINAL2K10 domRELAT-1K1 psi & ( for A be OrdinalORDINAL1M3 holds A inTARSKIR2 domRELAT-1K1 fi implies it .FUNCT-1K1 A =XBOOLE-0R4 fi .FUNCT-1K1 A)) & ( for A be OrdinalORDINAL1M3 holds A inTARSKIR2 domRELAT-1K1 psi implies it .FUNCT-1K1 (domRELAT-1K1 fi +^ORDINAL2K10 A) =XBOOLE-0R4 psi .FUNCT-1K1 A)"
proof-
  (*existence*)
    show " ex it be SequenceORDINAL1M4 st (domRELAT-1K1 it =XBOOLE-0R4 domRELAT-1K1 fi +^ORDINAL2K10 domRELAT-1K1 psi & ( for A be OrdinalORDINAL1M3 holds A inTARSKIR2 domRELAT-1K1 fi implies it .FUNCT-1K1 A =XBOOLE-0R4 fi .FUNCT-1K1 A)) & ( for A be OrdinalORDINAL1M3 holds A inTARSKIR2 domRELAT-1K1 psi implies it .FUNCT-1K1 (domRELAT-1K1 fi +^ORDINAL2K10 A) =XBOOLE-0R4 psi .FUNCT-1K1 A)"
sorry
  (*uniqueness*)
    show " for it1 be SequenceORDINAL1M4 holds  for it2 be SequenceORDINAL1M4 holds ((domRELAT-1K1 it1 =XBOOLE-0R4 domRELAT-1K1 fi +^ORDINAL2K10 domRELAT-1K1 psi & ( for A be OrdinalORDINAL1M3 holds A inTARSKIR2 domRELAT-1K1 fi implies it1 .FUNCT-1K1 A =XBOOLE-0R4 fi .FUNCT-1K1 A)) & ( for A be OrdinalORDINAL1M3 holds A inTARSKIR2 domRELAT-1K1 psi implies it1 .FUNCT-1K1 (domRELAT-1K1 fi +^ORDINAL2K10 A) =XBOOLE-0R4 psi .FUNCT-1K1 A)) & ((domRELAT-1K1 it2 =XBOOLE-0R4 domRELAT-1K1 fi +^ORDINAL2K10 domRELAT-1K1 psi & ( for A be OrdinalORDINAL1M3 holds A inTARSKIR2 domRELAT-1K1 fi implies it2 .FUNCT-1K1 A =XBOOLE-0R4 fi .FUNCT-1K1 A)) & ( for A be OrdinalORDINAL1M3 holds A inTARSKIR2 domRELAT-1K1 psi implies it2 .FUNCT-1K1 (domRELAT-1K1 fi +^ORDINAL2K10 A) =XBOOLE-0R4 psi .FUNCT-1K1 A)) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mtheorem ordinal4_th_2:
" for fi be Ordinal-SequenceORDINAL2M1 holds  for psi be Ordinal-SequenceORDINAL2M1 holds rngFUNCT-1K2 (fi ^ORDINAL4K1 psi) c=TARSKIR1 rngFUNCT-1K2 fi \\/XBOOLE-0K2 rngFUNCT-1K2 psi"
sorry

mtheorem ordinal4_cl_2:
  mlet "fi be Ordinal-SequenceORDINAL2M1", "psi be Ordinal-SequenceORDINAL2M1"
"cluster fi ^ORDINAL4K1 psi as-term-is Ordinal-yieldingORDINAL2V1"
proof
(*coherence*)
  show "fi ^ORDINAL4K1 psi be Ordinal-yieldingORDINAL2V1"
sorry
qed "sorry"

mtheorem ordinal4_th_3:
" for fi be Ordinal-SequenceORDINAL2M1 holds  for psi be Ordinal-SequenceORDINAL2M1 holds  for A be OrdinalORDINAL1M3 holds A is-limes-ofORDINAL2R1 psi implies A is-limes-ofORDINAL2R1 fi ^ORDINAL4K1 psi"
sorry

mtheorem ordinal4_th_4:
" for fi be Ordinal-SequenceORDINAL2M1 holds  for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds A is-limes-ofORDINAL2R1 fi implies B +^ORDINAL2K10 A is-limes-ofORDINAL2R1 B +^ORDINAL3K1 fi"
sorry

mlemma ordinal4_lm_4:
" for fi be Ordinal-SequenceORDINAL2M1 holds  for A be OrdinalORDINAL1M3 holds A is-limes-ofORDINAL2R1 fi implies domRELAT-1K1 fi <>HIDDENR2 {}XBOOLE-0K1"
sorry

mtheorem ordinal4_th_5:
" for fi be Ordinal-SequenceORDINAL2M1 holds  for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds A is-limes-ofORDINAL2R1 fi implies A *^ORDINAL2K11 B is-limes-ofORDINAL2R1 fi *^ORDINAL3K4 B"
sorry

mtheorem ordinal4_th_6:
" for fi be Ordinal-SequenceORDINAL2M1 holds  for psi be Ordinal-SequenceORDINAL2M1 holds  for B be OrdinalORDINAL1M3 holds  for C be OrdinalORDINAL1M3 holds ((domRELAT-1K1 fi =XBOOLE-0R4 domRELAT-1K1 psi & B is-limes-ofORDINAL2R1 fi) & C is-limes-ofORDINAL2R1 psi) & (( for A be OrdinalORDINAL1M3 holds A inTARSKIR2 domRELAT-1K1 fi implies fi .FUNCT-1K1 A c=ORDINAL1R1 psi .FUNCT-1K1 A) or ( for A be OrdinalORDINAL1M3 holds A inTARSKIR2 domRELAT-1K1 fi implies fi .FUNCT-1K1 A inTARSKIR2 psi .FUNCT-1K1 A)) implies B c=ORDINAL1R1 C"
sorry

reserve f1, f2 for "Ordinal-SequenceORDINAL2M1"
mtheorem ordinal4_th_7:
" for fi be Ordinal-SequenceORDINAL2M1 holds  for A be OrdinalORDINAL1M3 holds  for f1 be Ordinal-SequenceORDINAL2M1 holds  for f2 be Ordinal-SequenceORDINAL2M1 holds (((domRELAT-1K1 f1 =XBOOLE-0R4 domRELAT-1K1 fi & domRELAT-1K1 fi =XBOOLE-0R4 domRELAT-1K1 f2) & A is-limes-ofORDINAL2R1 f1) & A is-limes-ofORDINAL2R1 f2) & ( for A be OrdinalORDINAL1M3 holds A inTARSKIR2 domRELAT-1K1 fi implies f1 .FUNCT-1K1 A c=ORDINAL1R1 fi .FUNCT-1K1 A & fi .FUNCT-1K1 A c=ORDINAL1R1 f2 .FUNCT-1K1 A) implies A is-limes-ofORDINAL2R1 fi"
sorry

mtheorem ordinal4_th_8:
" for fi be Ordinal-SequenceORDINAL2M1 holds (domRELAT-1K1 fi <>HIDDENR2 {}XBOOLE-0K1 & domRELAT-1K1 fi be limit-ordinalORDINAL1V4) & fi be increasingORDINAL2V2 implies supORDINAL2K4 fi is-limes-ofORDINAL2R1 fi & limORDINAL2K8 fi =XBOOLE-0R4 supORDINAL2K4 fi"
sorry

mtheorem ordinal4_th_9:
" for fi be Ordinal-SequenceORDINAL2M1 holds  for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds (fi be increasingORDINAL2V2 & A c=ORDINAL1R1 B) & B inTARSKIR2 domRELAT-1K1 fi implies fi .FUNCT-1K1 A c=ORDINAL1R1 fi .FUNCT-1K1 B"
sorry

mtheorem ordinal4_th_10:
" for fi be Ordinal-SequenceORDINAL2M1 holds  for A be OrdinalORDINAL1M3 holds fi be increasingORDINAL2V2 & A inTARSKIR2 domRELAT-1K1 fi implies A c=ORDINAL1R1 fi .FUNCT-1K1 A"
sorry

mtheorem ordinal4_th_11:
" for phi be Ordinal-SequenceORDINAL2M1 holds  for A be OrdinalORDINAL1M3 holds phi be increasingORDINAL2V2 implies phi \<inverse>FUNCT-1K6 A be epsilon-transitiveORDINAL1V1\<bar>epsilon-connectedORDINAL1V2\<bar>setHIDDENM2"
sorry

mtheorem ordinal4_th_12:
" for f1 be Ordinal-SequenceORDINAL2M1 holds  for f2 be Ordinal-SequenceORDINAL2M1 holds f1 be increasingORDINAL2V2 implies f2 *FUNCT-1K3 f1 be Ordinal-SequenceORDINAL2M1"
sorry

mtheorem ordinal4_th_13:
" for f1 be Ordinal-SequenceORDINAL2M1 holds  for f2 be Ordinal-SequenceORDINAL2M1 holds f1 be increasingORDINAL2V2 & f2 be increasingORDINAL2V2 implies ( ex phi be Ordinal-SequenceORDINAL2M1 st phi =FUNCT-1R1 f1 *FUNCT-1K3 f2 & phi be increasingORDINAL2V2)"
sorry

mtheorem ordinal4_th_14:
" for fi be Ordinal-SequenceORDINAL2M1 holds  for A be OrdinalORDINAL1M3 holds  for f1 be Ordinal-SequenceORDINAL2M1 holds  for f2 be Ordinal-SequenceORDINAL2M1 holds ((f1 be increasingORDINAL2V2 & A is-limes-ofORDINAL2R1 f2) & supORDINAL2K3 (rngFUNCT-1K2 f1) =XBOOLE-0R4 domRELAT-1K1 f2) & fi =FUNCT-1R1 f2 *FUNCT-1K3 f1 implies A is-limes-ofORDINAL2R1 fi"
sorry

mtheorem ordinal4_th_15:
" for phi be Ordinal-SequenceORDINAL2M1 holds  for A be OrdinalORDINAL1M3 holds phi be increasingORDINAL2V2 implies phi |RELAT-1K8 A be increasingORDINAL2V2"
sorry

mtheorem ordinal4_th_16:
" for phi be Ordinal-SequenceORDINAL2M1 holds phi be increasingORDINAL2V2 & domRELAT-1K1 phi be limit-ordinalORDINAL1V4 implies supORDINAL2K4 phi be limit-ordinalORDINAL1V4"
sorry

mlemma ordinal4_lm_5:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds  for X be setHIDDENM2 holds rngFUNCT-1K2 f c=TARSKIR1 X implies g |RELAT-1K8 X *FUNCT-1K3 f =FUNCT-1R1 g *FUNCT-1K3 f"
sorry

mtheorem ordinal4_th_17:
" for phi be Ordinal-SequenceORDINAL2M1 holds  for fi be Ordinal-SequenceORDINAL2M1 holds  for psi be Ordinal-SequenceORDINAL2M1 holds ((fi be increasingORDINAL2V2 & fi be continuousORDINAL2V3) & psi be continuousORDINAL2V3) & phi =FUNCT-1R1 psi *FUNCT-1K3 fi implies phi be continuousORDINAL2V3"
sorry

mtheorem ordinal4_th_18:
" for fi be Ordinal-SequenceORDINAL2M1 holds  for C be OrdinalORDINAL1M3 holds ( for A be OrdinalORDINAL1M3 holds A inTARSKIR2 domRELAT-1K1 fi implies fi .FUNCT-1K1 A =XBOOLE-0R4 C +^ORDINAL2K10 A) implies fi be increasingORDINAL2V2"
sorry

mtheorem ordinal4_th_19:
" for fi be Ordinal-SequenceORDINAL2M1 holds  for C be OrdinalORDINAL1M3 holds C <>HIDDENR2 {}XBOOLE-0K1 & ( for A be OrdinalORDINAL1M3 holds A inTARSKIR2 domRELAT-1K1 fi implies fi .FUNCT-1K1 A =XBOOLE-0R4 A *^ORDINAL2K11 C) implies fi be increasingORDINAL2V2"
sorry

mtheorem ordinal4_th_20:
" for A be OrdinalORDINAL1M3 holds A <>HIDDENR2 {}XBOOLE-0K1 implies expORDINAL2K12({}XBOOLE-0K1,A) =XBOOLE-0R4 {}XBOOLE-0K1"
sorry

mlemma ordinal4_lm_6:
" for A be OrdinalORDINAL1M3 holds A <>HIDDENR2 {}XBOOLE-0K1 & A be limit-ordinalORDINAL1V4 implies ( for fi be Ordinal-SequenceORDINAL2M1 holds domRELAT-1K1 fi =XBOOLE-0R4 A & ( for B be OrdinalORDINAL1M3 holds B inTARSKIR2 A implies fi .FUNCT-1K1 B =XBOOLE-0R4 expORDINAL2K12({}XBOOLE-0K1,B)) implies 0ORDINAL1K5 is-limes-ofORDINAL2R1 fi)"
sorry

mlemma ordinal4_lm_7:
" for A be OrdinalORDINAL1M3 holds A <>HIDDENR2 {}XBOOLE-0K1 implies ( for fi be Ordinal-SequenceORDINAL2M1 holds domRELAT-1K1 fi =XBOOLE-0R4 A & ( for B be OrdinalORDINAL1M3 holds B inTARSKIR2 A implies fi .FUNCT-1K1 B =XBOOLE-0R4 expORDINAL2K12(\<one>\<^sub>M,B)) implies \<one>\<^sub>M is-limes-ofORDINAL2R1 fi)"
sorry

mlemma ordinal4_lm_8:
" for C be OrdinalORDINAL1M3 holds  for A be OrdinalORDINAL1M3 holds A <>HIDDENR2 {}XBOOLE-0K1 & A be limit-ordinalORDINAL1V4 implies ( ex fi be Ordinal-SequenceORDINAL2M1 st (domRELAT-1K1 fi =XBOOLE-0R4 A & ( for B be OrdinalORDINAL1M3 holds B inTARSKIR2 A implies fi .FUNCT-1K1 B =XBOOLE-0R4 expORDINAL2K12(C,B))) & ( ex D be OrdinalORDINAL1M3 st D is-limes-ofORDINAL2R1 fi))"
sorry

mtheorem ordinal4_th_21:
" for A be OrdinalORDINAL1M3 holds  for C be OrdinalORDINAL1M3 holds A <>HIDDENR2 {}XBOOLE-0K1 & A be limit-ordinalORDINAL1V4 implies ( for fi be Ordinal-SequenceORDINAL2M1 holds domRELAT-1K1 fi =XBOOLE-0R4 A & ( for B be OrdinalORDINAL1M3 holds B inTARSKIR2 A implies fi .FUNCT-1K1 B =XBOOLE-0R4 expORDINAL2K12(C,B)) implies expORDINAL2K12(C,A) is-limes-ofORDINAL2R1 fi)"
sorry

mtheorem ordinal4_th_22:
" for A be OrdinalORDINAL1M3 holds  for C be OrdinalORDINAL1M3 holds C <>HIDDENR2 {}XBOOLE-0K1 implies expORDINAL2K12(C,A) <>HIDDENR2 {}XBOOLE-0K1"
sorry

mtheorem ordinal4_th_23:
" for A be OrdinalORDINAL1M3 holds  for C be OrdinalORDINAL1M3 holds \<one>\<^sub>M inTARSKIR2 C implies expORDINAL2K12(C,A) inTARSKIR2 expORDINAL2K12(C,succORDINAL1K1 A)"
sorry

mtheorem ordinal4_th_24:
" for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds  for C be OrdinalORDINAL1M3 holds \<one>\<^sub>M inTARSKIR2 C & A inTARSKIR2 B implies expORDINAL2K12(C,A) inTARSKIR2 expORDINAL2K12(C,B)"
sorry

mtheorem ordinal4_th_25:
" for fi be Ordinal-SequenceORDINAL2M1 holds  for C be OrdinalORDINAL1M3 holds \<one>\<^sub>M inTARSKIR2 C & ( for A be OrdinalORDINAL1M3 holds A inTARSKIR2 domRELAT-1K1 fi implies fi .FUNCT-1K1 A =XBOOLE-0R4 expORDINAL2K12(C,A)) implies fi be increasingORDINAL2V2"
sorry

mtheorem ordinal4_th_26:
" for A be OrdinalORDINAL1M3 holds  for C be OrdinalORDINAL1M3 holds (\<one>\<^sub>M inTARSKIR2 C & A <>HIDDENR2 {}XBOOLE-0K1) & A be limit-ordinalORDINAL1V4 implies ( for fi be Ordinal-SequenceORDINAL2M1 holds domRELAT-1K1 fi =XBOOLE-0R4 A & ( for B be OrdinalORDINAL1M3 holds B inTARSKIR2 A implies fi .FUNCT-1K1 B =XBOOLE-0R4 expORDINAL2K12(C,B)) implies expORDINAL2K12(C,A) =XBOOLE-0R4 supORDINAL2K4 fi)"
sorry

mtheorem ordinal4_th_27:
" for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds  for C be OrdinalORDINAL1M3 holds C <>HIDDENR2 {}XBOOLE-0K1 & A c=ORDINAL1R1 B implies expORDINAL2K12(C,A) c=ORDINAL1R1 expORDINAL2K12(C,B)"
sorry

mtheorem ordinal4_th_28:
" for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds  for C be OrdinalORDINAL1M3 holds A c=ORDINAL1R1 B implies expORDINAL2K12(A,C) c=ORDINAL1R1 expORDINAL2K12(B,C)"
sorry

mtheorem ordinal4_th_29:
" for A be OrdinalORDINAL1M3 holds  for C be OrdinalORDINAL1M3 holds \<one>\<^sub>M inTARSKIR2 C & A <>HIDDENR2 {}XBOOLE-0K1 implies \<one>\<^sub>M inTARSKIR2 expORDINAL2K12(C,A)"
sorry

mtheorem ordinal4_th_30:
" for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds  for C be OrdinalORDINAL1M3 holds expORDINAL2K12(C,A +^ORDINAL2K10 B) =XBOOLE-0R4 (expORDINAL2K12(C,B))*^ORDINAL2K11 (expORDINAL2K12(C,A))"
sorry

mtheorem ordinal4_th_31:
" for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds  for C be OrdinalORDINAL1M3 holds expORDINAL2K12(expORDINAL2K12(C,A),B) =XBOOLE-0R4 expORDINAL2K12(C,B *^ORDINAL2K11 A)"
sorry

mtheorem ordinal4_th_32:
" for A be OrdinalORDINAL1M3 holds  for C be OrdinalORDINAL1M3 holds \<one>\<^sub>M inTARSKIR2 C implies A c=ORDINAL1R1 expORDINAL2K12(C,A)"
sorry

(*\$N Fixed-point lemma for normal functions*)
theorem ordinal4_sch_1:
  fixes phif1 
  assumes
[ty_func]: "\<And> x1. x1 be OrdinalORDINAL1M3 \<Longrightarrow> phif1(x1) be OrdinalORDINAL1M3" and
   A1: " for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds A inTARSKIR2 B implies phif1(A) inTARSKIR2 phif1(B)" and
   A2: " for A be OrdinalORDINAL1M3 holds A <>HIDDENR2 {}XBOOLE-0K1 & A be limit-ordinalORDINAL1V4 implies ( for phi be Ordinal-SequenceORDINAL2M1 holds domRELAT-1K1 phi =XBOOLE-0R4 A & ( for B be OrdinalORDINAL1M3 holds B inTARSKIR2 A implies phi .FUNCT-1K1 B =XBOOLE-0R4 phif1(B)) implies phif1(A) is-limes-ofORDINAL2R1 phi)"
  shows " ex A be OrdinalORDINAL1M3 st phif1(A) =XBOOLE-0R4 A"
sorry

reserve W for "UniverseCLASSES2M1"
mtheorem ordinal4_cl_3:
  mlet "W be UniverseCLASSES2M1"
"cluster ordinalORDINAL1V3 for ElementSUBSET-1M1-of W"
proof
(*existence*)
  show " ex it be ElementSUBSET-1M1-of W st it be ordinalORDINAL1V3"
sorry
qed "sorry"

syntax ORDINAL4M1 :: " Set \<Rightarrow> Ty" ("OrdinalORDINAL4M1-of  _ " [70]70)
translations "OrdinalORDINAL4M1-of W" \<rightharpoonup> "ordinalORDINAL1V3\<bar>ElementSUBSET-1M1-of W"

syntax ORDINAL4M2 :: " Set \<Rightarrow> Ty" ("Ordinal-SequenceORDINAL4M2-of  _ " [70]70)
translations "Ordinal-SequenceORDINAL4M2-of W" \<rightharpoonup> "FunctionFUNCT-2M1-of(OnORDINAL1K2 W,OnORDINAL1K2 W)"

mlemma ordinal4_lm_9:
"0ORDINAL1K5 =XBOOLE-0R4 {}XBOOLE-0K1"
   sorry

mtheorem ordinal4_cl_4:
  mlet "W be UniverseCLASSES2M1"
"cluster  non emptyXBOOLE-0V1 for OrdinalORDINAL4M1-of W"
proof
(*existence*)
  show " ex it be OrdinalORDINAL4M1-of W st it be  non emptyXBOOLE-0V1"
sorry
qed "sorry"

mtheorem ordinal4_cl_5:
  mlet "W be UniverseCLASSES2M1"
"cluster OnORDINAL1K2 W as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "OnORDINAL1K2 W be  non emptyXBOOLE-0V1"
    using classes2_th_51 sorry
qed "sorry"

mtheorem ordinal4_cl_6:
  mlet "W be UniverseCLASSES2M1"
"cluster note-that Sequence-likeORDINAL1V5\<bar>Ordinal-yieldingORDINAL2V1 for Ordinal-SequenceORDINAL4M2-of W"
proof
(*coherence*)
  show " for it be Ordinal-SequenceORDINAL4M2-of W holds it be Sequence-likeORDINAL1V5\<bar>Ordinal-yieldingORDINAL2V1"
sorry
qed "sorry"

reserve A1, B1 for "OrdinalORDINAL4M1-of W"
reserve phi for "Ordinal-SequenceORDINAL4M2-of W"
theorem ordinal4_sch_2:
  fixes Wf0 Ff1 
  assumes
[ty]: "Wf0 be UniverseCLASSES2M1" and
  [ty_func]: "\<And> x1. x1 be setHIDDENM2 \<Longrightarrow> Ff1(x1) be OrdinalORDINAL4M1-of Wf0"
  shows " ex phi be Ordinal-SequenceORDINAL4M2-of Wf0 st  for a be OrdinalORDINAL4M1-of Wf0 holds phi .FUNCT-1K1 a =XBOOLE-0R4 Ff1(a)"
sorry

mdef ordinal4_def_2 ("0-element-ofORDINAL4K2  _ " [228]228 ) where
  mlet "W be UniverseCLASSES2M1"
"func 0-element-ofORDINAL4K2 W \<rightarrow> OrdinalORDINAL4M1-of W equals
  {}XBOOLE-0K1"
proof-
  (*coherence*)
    show "{}XBOOLE-0K1 be OrdinalORDINAL4M1-of W"
sorry
qed "sorry"

mdef ordinal4_def_3 ("1-element-ofORDINAL4K3  _ " [228]228 ) where
  mlet "W be UniverseCLASSES2M1"
"func 1-element-ofORDINAL4K3 W \<rightarrow>  non emptyXBOOLE-0V1\<bar>OrdinalORDINAL4M1-of W equals
  \<one>\<^sub>M"
proof-
  (*coherence*)
    show "\<one>\<^sub>M be  non emptyXBOOLE-0V1\<bar>OrdinalORDINAL4M1-of W"
sorry
qed "sorry"

syntax ORDINAL4K4 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ .ORDINAL4K4\<^bsub>'( _ ')\<^esub>  _ " [200,0,200]200)
translations "phi .ORDINAL4K4\<^bsub>(W)\<^esub> A1" \<rightharpoonup> "phi .FUNCT-1K1 A1"

mtheorem ordinal4_add_1:
  mlet "W be UniverseCLASSES2M1", "phi be Ordinal-SequenceORDINAL4M2-of W", "A1 be OrdinalORDINAL4M1-of W"
"cluster phi .FUNCT-1K1 A1 as-term-is OrdinalORDINAL4M1-of W"
proof
(*coherence*)
  show "phi .FUNCT-1K1 A1 be OrdinalORDINAL4M1-of W"
sorry
qed "sorry"

syntax ORDINAL4K5 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ *ORDINAL4K5\<^bsub>'( _ ')\<^esub>  _ " [164,0,164]164)
translations "p1 *ORDINAL4K5\<^bsub>(W)\<^esub> p2" \<rightharpoonup> "p2 *RELAT-1K6 p1"

mtheorem ordinal4_add_2:
  mlet "W be UniverseCLASSES2M1", "p2 be Ordinal-SequenceORDINAL4M2-of W", "p1 be Ordinal-SequenceORDINAL4M2-of W"
"cluster p2 *RELAT-1K6 p1 as-term-is Ordinal-SequenceORDINAL4M2-of W"
proof
(*coherence*)
  show "p2 *RELAT-1K6 p1 be Ordinal-SequenceORDINAL4M2-of W"
sorry
qed "sorry"

mtheorem ordinal4_th_33:
" for W be UniverseCLASSES2M1 holds 0-element-ofORDINAL4K2 W =XBOOLE-0R4 {}XBOOLE-0K1 & 1-element-ofORDINAL4K3 W =XBOOLE-0R4 \<one>\<^sub>M"
   sorry

syntax ORDINAL4K6 :: " Set \<Rightarrow>  Set \<Rightarrow> Set" ("succORDINAL4K6\<^bsub>'( _ ')\<^esub>  _ " [0,228]228)
translations "succORDINAL4K6\<^bsub>(W)\<^esub> A1" \<rightharpoonup> "succORDINAL1K1 A1"

mtheorem ordinal4_add_3:
  mlet "W be UniverseCLASSES2M1", "A1 be OrdinalORDINAL4M1-of W"
"cluster succORDINAL1K1 A1 as-term-is  non emptyXBOOLE-0V1\<bar>OrdinalORDINAL4M1-of W"
proof
(*coherence*)
  show "succORDINAL1K1 A1 be  non emptyXBOOLE-0V1\<bar>OrdinalORDINAL4M1-of W"
    using classes2_th_5 sorry
qed "sorry"

syntax ORDINAL4K7 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ +^ORDINAL4K7\<^bsub>'( _ ')\<^esub>  _ " [132,0,132]132)
translations "A1 +^ORDINAL4K7\<^bsub>(W)\<^esub> B1" \<rightharpoonup> "A1 +^ORDINAL2K10 B1"

mtheorem ordinal4_add_4:
  mlet "W be UniverseCLASSES2M1", "A1 be OrdinalORDINAL4M1-of W", "B1 be OrdinalORDINAL4M1-of W"
"cluster A1 +^ORDINAL2K10 B1 as-term-is OrdinalORDINAL4M1-of W"
proof
(*coherence*)
  show "A1 +^ORDINAL2K10 B1 be OrdinalORDINAL4M1-of W"
sorry
qed "sorry"

syntax ORDINAL4K8 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ *^ORDINAL4K8\<^bsub>'( _ ')\<^esub>  _ " [164,0,164]164)
translations "A1 *^ORDINAL4K8\<^bsub>(W)\<^esub> B1" \<rightharpoonup> "A1 *^ORDINAL2K11 B1"

mtheorem ordinal4_add_5:
  mlet "W be UniverseCLASSES2M1", "A1 be OrdinalORDINAL4M1-of W", "B1 be OrdinalORDINAL4M1-of W"
"cluster A1 *^ORDINAL2K11 B1 as-term-is OrdinalORDINAL4M1-of W"
proof
(*coherence*)
  show "A1 *^ORDINAL2K11 B1 be OrdinalORDINAL4M1-of W"
sorry
qed "sorry"

mtheorem ordinal4_th_34:
" for W be UniverseCLASSES2M1 holds  for A1 be OrdinalORDINAL4M1-of W holds  for phi be Ordinal-SequenceORDINAL4M2-of W holds A1 inTARSKIR2 domRELAT-1K1 phi"
sorry

mtheorem ordinal4_th_35:
" for fi be Ordinal-SequenceORDINAL2M1 holds  for W be UniverseCLASSES2M1 holds domRELAT-1K1 fi inTARSKIR2 W & rngFUNCT-1K2 fi c=TARSKIR1 W implies supORDINAL2K4 fi inTARSKIR2 W"
sorry

reserve L for "SequenceORDINAL1M4"
mtheorem ordinal4_th_36:
" for W be UniverseCLASSES2M1 holds  for phi be Ordinal-SequenceORDINAL4M2-of W holds (phi be increasingORDINAL2V2 & phi be continuousORDINAL2V3) & omegaORDINAL1K4 inTARSKIR2 W implies ( ex A be OrdinalORDINAL1M3 st A inTARSKIR2 domRELAT-1K1 phi & phi .FUNCT-1K1 A =XBOOLE-0R4 A)"
sorry

(*begin*)
mtheorem ordinal4_th_37:
" for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds  for C be OrdinalORDINAL1M3 holds A is-cofinal-withORDINAL2R2 B & B is-cofinal-withORDINAL2R2 C implies A is-cofinal-withORDINAL2R2 C"
sorry

mtheorem ordinal4_th_38:
" for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds A is-cofinal-withORDINAL2R2 B implies (A be limit-ordinalORDINAL1V4 iff B be limit-ordinalORDINAL1V4)"
sorry

mtheorem ordinal4_cl_7:
  mlet "D be OrdinalORDINAL1M3", "f be SequenceORDINAL1M5-of D", "g be SequenceORDINAL1M5-of D"
"cluster f ^ORDINAL4K1 g as-term-is D -valuedRELAT-1V5"
proof
(*coherence*)
  show "f ^ORDINAL4K1 g be D -valuedRELAT-1V5"
sorry
qed "sorry"

end
