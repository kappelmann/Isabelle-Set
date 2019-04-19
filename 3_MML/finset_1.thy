theory finset_1
  imports ordinal3 funct_3 funct_4 xfamily
begin
(*begin*)
mdef finset_1_def_1 ("finiteFINSET-1V1" 70 ) where
"attr finiteFINSET-1V1 for setHIDDENM2 means
  (\<lambda>IT.  ex p be FunctionFUNCT-1M1 st rngFUNCT-1K2 p =XBOOLE-0R4 IT & domRELAT-1K1 p inTARSKIR2 omegaORDINAL1K4)"..

syntax FINSET_1V2 :: "Ty" ("infiniteFINSET-1V2" 70)
translations "infiniteFINSET-1V2" \<rightharpoonup> " non finiteFINSET-1V1"

reserve A, B, X, Y, Z, x, y for "setHIDDENM2"
reserve f for "FunctionFUNCT-1M1"
mlemma finset_1_lm_1:
" for x be objectHIDDENM1 holds {TARSKIK1 x} be finiteFINSET-1V1"
sorry

mtheorem finset_1_cl_1:
"cluster  non emptyXBOOLE-0V1\<bar>finiteFINSET-1V1 for setHIDDENM2"
proof
(*existence*)
  show " ex it be setHIDDENM2 st it be  non emptyXBOOLE-0V1\<bar>finiteFINSET-1V1"
sorry
qed "sorry"

mtheorem finset_1_cl_2:
"cluster emptyXBOOLE-0V1 also-is finiteFINSET-1V1 for setHIDDENM2"
proof
(*coherence*)
  show " for it be setHIDDENM2 holds it be emptyXBOOLE-0V1 implies it be finiteFINSET-1V1"
sorry
qed "sorry"

theorem finset_1_sch_1:
  fixes Af0 Ff1 Gf1 Cp1 
  assumes
[ty]: "Af0 be setHIDDENM2" and
  [ty_func]: "\<And> x1. x1 be objectHIDDENM1 \<Longrightarrow> Ff1(x1) be objectHIDDENM1" and
  [ty_func]: "\<And> x1. x1 be objectHIDDENM1 \<Longrightarrow> Gf1(x1) be objectHIDDENM1"
  shows " ex f be FunctionFUNCT-1M1 st domRELAT-1K1 f =XBOOLE-0R4 Af0 & ( for x be OrdinalORDINAL1M3 holds x inTARSKIR2 Af0 implies (Cp1(x) implies f .FUNCT-1K1 x =HIDDENR1 Ff1(x)) & ( not Cp1(x) implies f .FUNCT-1K1 x =HIDDENR1 Gf1(x)))"
sorry

mlemma finset_1_lm_2:
" for A be setHIDDENM2 holds  for B be setHIDDENM2 holds A be finiteFINSET-1V1 & B be finiteFINSET-1V1 implies A \\/XBOOLE-0K2 B be finiteFINSET-1V1"
sorry

mtheorem finset_1_cl_3:
  mlet "x be objectHIDDENM1"
"cluster {TARSKIK1 x} as-term-is finiteFINSET-1V1"
proof
(*coherence*)
  show "{TARSKIK1 x} be finiteFINSET-1V1"
    using finset_1_lm_1 sorry
qed "sorry"

mtheorem finset_1_cl_4:
  mlet "x be objectHIDDENM1", "y be objectHIDDENM1"
"cluster {TARSKIK2 x,y } as-term-is finiteFINSET-1V1"
proof
(*coherence*)
  show "{TARSKIK2 x,y } be finiteFINSET-1V1"
sorry
qed "sorry"

mtheorem finset_1_cl_5:
  mlet "x be objectHIDDENM1", "y be objectHIDDENM1", "z be objectHIDDENM1"
"cluster {ENUMSET1K1 x,y,z } as-term-is finiteFINSET-1V1"
proof
(*coherence*)
  show "{ENUMSET1K1 x,y,z } be finiteFINSET-1V1"
sorry
qed "sorry"

mtheorem finset_1_cl_6:
  mlet "x1 be objectHIDDENM1", "x2 be objectHIDDENM1", "x3 be objectHIDDENM1", "x4 be objectHIDDENM1"
"cluster {ENUMSET1K2 x1,x2,x3,x4 } as-term-is finiteFINSET-1V1"
proof
(*coherence*)
  show "{ENUMSET1K2 x1,x2,x3,x4 } be finiteFINSET-1V1"
sorry
qed "sorry"

mtheorem finset_1_cl_7:
  mlet "x1 be objectHIDDENM1", "x2 be objectHIDDENM1", "x3 be objectHIDDENM1", "x4 be objectHIDDENM1", "x5 be objectHIDDENM1"
"cluster {ENUMSET1K3 x1,x2,x3,x4,x5 } as-term-is finiteFINSET-1V1"
proof
(*coherence*)
  show "{ENUMSET1K3 x1,x2,x3,x4,x5 } be finiteFINSET-1V1"
sorry
qed "sorry"

mtheorem finset_1_cl_8:
  mlet "x1 be objectHIDDENM1", "x2 be objectHIDDENM1", "x3 be objectHIDDENM1", "x4 be objectHIDDENM1", "x5 be objectHIDDENM1", "x6 be objectHIDDENM1"
"cluster {ENUMSET1K4 x1,x2,x3,x4,x5,x6 } as-term-is finiteFINSET-1V1"
proof
(*coherence*)
  show "{ENUMSET1K4 x1,x2,x3,x4,x5,x6 } be finiteFINSET-1V1"
sorry
qed "sorry"

mtheorem finset_1_cl_9:
  mlet "x1 be objectHIDDENM1", "x2 be objectHIDDENM1", "x3 be objectHIDDENM1", "x4 be objectHIDDENM1", "x5 be objectHIDDENM1", "x6 be objectHIDDENM1", "x7 be objectHIDDENM1"
"cluster {ENUMSET1K5 x1,x2,x3,x4,x5,x6,x7 } as-term-is finiteFINSET-1V1"
proof
(*coherence*)
  show "{ENUMSET1K5 x1,x2,x3,x4,x5,x6,x7 } be finiteFINSET-1V1"
sorry
qed "sorry"

mtheorem finset_1_cl_10:
  mlet "x1 be objectHIDDENM1", "x2 be objectHIDDENM1", "x3 be objectHIDDENM1", "x4 be objectHIDDENM1", "x5 be objectHIDDENM1", "x6 be objectHIDDENM1", "x7 be objectHIDDENM1", "x8 be objectHIDDENM1"
"cluster {ENUMSET1K6 x1,x2,x3,x4,x5,x6,x7,x8 } as-term-is finiteFINSET-1V1"
proof
(*coherence*)
  show "{ENUMSET1K6 x1,x2,x3,x4,x5,x6,x7,x8 } be finiteFINSET-1V1"
sorry
qed "sorry"

mtheorem finset_1_cl_11:
  mlet "B be finiteFINSET-1V1\<bar>setHIDDENM2"
"cluster note-that finiteFINSET-1V1 for SubsetSUBSET-1M2-of B"
proof
(*coherence*)
  show " for it be SubsetSUBSET-1M2-of B holds it be finiteFINSET-1V1"
sorry
qed "sorry"

mtheorem finset_1_cl_12:
  mlet "X be finiteFINSET-1V1\<bar>setHIDDENM2", "Y be finiteFINSET-1V1\<bar>setHIDDENM2"
"cluster X \\/XBOOLE-0K2 Y as-term-is finiteFINSET-1V1"
proof
(*coherence*)
  show "X \\/XBOOLE-0K2 Y be finiteFINSET-1V1"
    using finset_1_lm_2 sorry
qed "sorry"

mtheorem finset_1_th_1:
" for A be setHIDDENM2 holds  for B be setHIDDENM2 holds A c=TARSKIR1 B & B be finiteFINSET-1V1 implies A be finiteFINSET-1V1"
   sorry

mtheorem finset_1_th_2:
" for A be setHIDDENM2 holds  for B be setHIDDENM2 holds A be finiteFINSET-1V1 & B be finiteFINSET-1V1 implies A \\/XBOOLE-0K2 B be finiteFINSET-1V1"
   sorry

mtheorem finset_1_cl_13:
  mlet "A be setHIDDENM2", "B be finiteFINSET-1V1\<bar>setHIDDENM2"
"cluster A /\\XBOOLE-0K3 B as-term-is finiteFINSET-1V1"
proof
(*coherence*)
  show "A /\\XBOOLE-0K3 B be finiteFINSET-1V1"
sorry
qed "sorry"

mtheorem finset_1_cl_14:
  mlet "A be finiteFINSET-1V1\<bar>setHIDDENM2", "B be setHIDDENM2"
"cluster A /\\XBOOLE-0K3 B as-term-is finiteFINSET-1V1"
proof
(*coherence*)
  show "A /\\XBOOLE-0K3 B be finiteFINSET-1V1"
     sorry
qed "sorry"

mtheorem finset_1_cl_15:
  mlet "A be finiteFINSET-1V1\<bar>setHIDDENM2", "B be setHIDDENM2"
"cluster A \\SUBSET-1K6 B as-term-is finiteFINSET-1V1"
proof
(*coherence*)
  show "A \\SUBSET-1K6 B be finiteFINSET-1V1"
     sorry
qed "sorry"

mtheorem finset_1_th_3:
" for A be setHIDDENM2 holds  for B be setHIDDENM2 holds A be finiteFINSET-1V1 implies A /\\XBOOLE-0K3 B be finiteFINSET-1V1"
   sorry

mtheorem finset_1_th_4:
" for A be setHIDDENM2 holds  for B be setHIDDENM2 holds A be finiteFINSET-1V1 implies A \\SUBSET-1K6 B be finiteFINSET-1V1"
   sorry

mtheorem finset_1_cl_16:
  mlet "f be FunctionFUNCT-1M1", "A be finiteFINSET-1V1\<bar>setHIDDENM2"
"cluster f .:FUNCT-1K5 A as-term-is finiteFINSET-1V1"
proof
(*coherence*)
  show "f .:FUNCT-1K5 A be finiteFINSET-1V1"
sorry
qed "sorry"

mtheorem finset_1_th_5:
" for A be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds A be finiteFINSET-1V1 implies f .:FUNCT-1K5 A be finiteFINSET-1V1"
   sorry

reserve O for "OrdinalORDINAL1M3"
mtheorem finset_1_th_6:
" for A be setHIDDENM2 holds A be finiteFINSET-1V1 implies ( for X be Subset-FamilySETFAM-1M1-of A holds X <>HIDDENR2 {}XBOOLE-0K1 implies ( ex x be setHIDDENM2 st x inTARSKIR2 X & ( for B be setHIDDENM2 holds B inTARSKIR2 X implies (x c=TARSKIR1 B implies B =XBOOLE-0R4 x))))"
sorry

theorem finset_1_sch_2:
  fixes Af0 Pp1 
  assumes
[ty]: "Af0 be setHIDDENM2" and
   A1: "Af0 be finiteFINSET-1V1" and
   A2: "Pp1({}XBOOLE-0K1)" and
   A3: " for x be setHIDDENM2 holds  for B be setHIDDENM2 holds (x inTARSKIR2 Af0 & B c=TARSKIR1 Af0) & Pp1(B) implies Pp1(B \\/XBOOLE-0K2 {TARSKIK1 x})"
  shows "Pp1(Af0)"
sorry

mlemma finset_1_lm_3:
" for A be setHIDDENM2 holds A be finiteFINSET-1V1 & ( for X be setHIDDENM2 holds X inTARSKIR2 A implies X be finiteFINSET-1V1) implies unionTARSKIK3 A be finiteFINSET-1V1"
sorry

mtheorem finset_1_cl_17:
  mlet "A be finiteFINSET-1V1\<bar>setHIDDENM2", "B be finiteFINSET-1V1\<bar>setHIDDENM2"
"cluster [:ZFMISC-1K2 A,B :] as-term-is finiteFINSET-1V1"
proof
(*coherence*)
  show "[:ZFMISC-1K2 A,B :] be finiteFINSET-1V1"
sorry
qed "sorry"

mtheorem finset_1_cl_18:
  mlet "A be finiteFINSET-1V1\<bar>setHIDDENM2", "B be finiteFINSET-1V1\<bar>setHIDDENM2", "C be finiteFINSET-1V1\<bar>setHIDDENM2"
"cluster [:ZFMISC-1K3 A,B,C :] as-term-is finiteFINSET-1V1"
proof
(*coherence*)
  show "[:ZFMISC-1K3 A,B,C :] be finiteFINSET-1V1"
sorry
qed "sorry"

mtheorem finset_1_cl_19:
  mlet "A be finiteFINSET-1V1\<bar>setHIDDENM2", "B be finiteFINSET-1V1\<bar>setHIDDENM2", "C be finiteFINSET-1V1\<bar>setHIDDENM2", "D be finiteFINSET-1V1\<bar>setHIDDENM2"
"cluster [:ZFMISC-1K4 A,B,C,D :] as-term-is finiteFINSET-1V1"
proof
(*coherence*)
  show "[:ZFMISC-1K4 A,B,C,D :] be finiteFINSET-1V1"
sorry
qed "sorry"

mtheorem finset_1_cl_20:
  mlet "A be finiteFINSET-1V1\<bar>setHIDDENM2"
"cluster boolSETFAM-1K9 A as-term-is finiteFINSET-1V1"
proof
(*coherence*)
  show "boolSETFAM-1K9 A be finiteFINSET-1V1"
sorry
qed "sorry"

mtheorem finset_1_th_7:
" for A be setHIDDENM2 holds A be finiteFINSET-1V1 & ( for X be setHIDDENM2 holds X inTARSKIR2 A implies X be finiteFINSET-1V1) iff unionTARSKIK3 A be finiteFINSET-1V1"
sorry

mtheorem finset_1_th_8:
" for f be FunctionFUNCT-1M1 holds domRELAT-1K1 f be finiteFINSET-1V1 implies rngFUNCT-1K2 f be finiteFINSET-1V1"
sorry

mtheorem finset_1_th_9:
" for Y be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds Y c=TARSKIR1 rngFUNCT-1K2 f & f \<inverse>FUNCT-1K6 Y be finiteFINSET-1V1 implies Y be finiteFINSET-1V1"
sorry

mtheorem finset_1_cl_21:
  mlet "X be finiteFINSET-1V1\<bar>setHIDDENM2", "Y be finiteFINSET-1V1\<bar>setHIDDENM2"
"cluster X \\+\\XBOOLE-0K5 Y as-term-is finiteFINSET-1V1"
proof
(*coherence*)
  show "X \\+\\XBOOLE-0K5 Y be finiteFINSET-1V1"
     sorry
qed "sorry"

mtheorem finset_1_cl_22:
  mlet "X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster finiteFINSET-1V1\<bar> non emptyXBOOLE-0V1 for SubsetSUBSET-1M2-of X"
proof
(*existence*)
  show " ex it be SubsetSUBSET-1M2-of X st it be finiteFINSET-1V1\<bar> non emptyXBOOLE-0V1"
sorry
qed "sorry"

(*begin*)
mtheorem finset_1_th_10:
" for f be FunctionFUNCT-1M1 holds domRELAT-1K1 f be finiteFINSET-1V1 iff f be finiteFINSET-1V1"
sorry

mtheorem finset_1_th_11:
" for F be setHIDDENM2 holds (F be finiteFINSET-1V1 & F <>HIDDENR2 {}XBOOLE-0K1) & F be c=-linearORDINAL1V6 implies ( ex m be setHIDDENM2 st m inTARSKIR2 F & ( for C be setHIDDENM2 holds C inTARSKIR2 F implies m c=TARSKIR1 C))"
sorry

mtheorem finset_1_th_12:
" for F be setHIDDENM2 holds (F be finiteFINSET-1V1 & F <>HIDDENR2 {}XBOOLE-0K1) & F be c=-linearORDINAL1V6 implies ( ex m be setHIDDENM2 st m inTARSKIR2 F & ( for C be setHIDDENM2 holds C inTARSKIR2 F implies C c=TARSKIR1 m))"
sorry

mdef finset_1_def_2 ("finite-yieldingFINSET-1V3" 70 ) where
"attr finite-yieldingFINSET-1V3 for RelationRELAT-1M1 means
  (\<lambda>R.  for x be setHIDDENM2 holds x inTARSKIR2 rngRELAT-1K2 R implies x be finiteFINSET-1V1)"..

mtheorem finset_1_th_13:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds X be finiteFINSET-1V1 & X c=TARSKIR1 [:ZFMISC-1K2 Y,Z :] implies ( ex A be setHIDDENM2 st  ex B be setHIDDENM2 st (((A be finiteFINSET-1V1 & A c=TARSKIR1 Y) & B be finiteFINSET-1V1) & B c=TARSKIR1 Z) & X c=TARSKIR1 [:ZFMISC-1K2 A,B :])"
sorry

mtheorem finset_1_th_14:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds X be finiteFINSET-1V1 & X c=TARSKIR1 [:ZFMISC-1K2 Y,Z :] implies ( ex A be setHIDDENM2 st (A be finiteFINSET-1V1 & A c=TARSKIR1 Y) & X c=TARSKIR1 [:ZFMISC-1K2 A,Z :])"
sorry

mtheorem finset_1_cl_23:
"cluster finiteFINSET-1V1\<bar> non emptyXBOOLE-0V1 for FunctionFUNCT-1M1"
proof
(*existence*)
  show " ex it be FunctionFUNCT-1M1 st it be finiteFINSET-1V1\<bar> non emptyXBOOLE-0V1"
sorry
qed "sorry"

mtheorem finset_1_cl_24:
  mlet "R be finiteFINSET-1V1\<bar>RelationRELAT-1M1"
"cluster domRELAT-1K1 R as-term-is finiteFINSET-1V1"
proof
(*coherence*)
  show "domRELAT-1K1 R be finiteFINSET-1V1"
sorry
qed "sorry"

mtheorem finset_1_cl_25:
  mlet "f be FunctionFUNCT-1M1", "g be finiteFINSET-1V1\<bar>FunctionFUNCT-1M1"
"cluster f *FUNCT-1K3 g as-term-is finiteFINSET-1V1"
proof
(*coherence*)
  show "f *FUNCT-1K3 g be finiteFINSET-1V1"
sorry
qed "sorry"

mtheorem finset_1_cl_26:
  mlet "A be finiteFINSET-1V1\<bar>setHIDDENM2", "B be setHIDDENM2"
"cluster note-that finiteFINSET-1V1 for FunctionFUNCT-2M1-of(A,B)"
proof
(*coherence*)
  show " for it be FunctionFUNCT-2M1-of(A,B) holds it be finiteFINSET-1V1"
sorry
qed "sorry"

mtheorem finset_1_cl_27:
  mlet "x be objectHIDDENM1", "y be objectHIDDENM1"
"cluster x .-->FUNCOP-1K17 y as-term-is finiteFINSET-1V1"
proof
(*coherence*)
  show "x .-->FUNCOP-1K17 y be finiteFINSET-1V1"
     sorry
qed "sorry"

mtheorem finset_1_cl_28:
  mlet "R be finiteFINSET-1V1\<bar>RelationRELAT-1M1"
"cluster rngRELAT-1K2 R as-term-is finiteFINSET-1V1"
proof
(*coherence*)
  show "rngRELAT-1K2 R be finiteFINSET-1V1"
sorry
qed "sorry"

mtheorem finset_1_cl_29:
  mlet "f be finiteFINSET-1V1\<bar>FunctionFUNCT-1M1", "x be setHIDDENM2"
"cluster f \<inverse>FUNCT-1K6 x as-term-is finiteFINSET-1V1"
proof
(*coherence*)
  show "f \<inverse>FUNCT-1K6 x be finiteFINSET-1V1"
sorry
qed "sorry"

mtheorem finset_1_cl_30:
  mlet "f be finiteFINSET-1V1\<bar>FunctionFUNCT-1M1", "g be finiteFINSET-1V1\<bar>FunctionFUNCT-1M1"
"cluster f +*FUNCT-4K1 g as-term-is finiteFINSET-1V1"
proof
(*coherence*)
  show "f +*FUNCT-4K1 g be finiteFINSET-1V1"
sorry
qed "sorry"

mdef finset_1_def_3 ("centeredFINSET-1V4" 70 ) where
"attr centeredFINSET-1V4 for setHIDDENM2 means
  (\<lambda>F. F <>HIDDENR2 {}XBOOLE-0K1 & ( for G be setHIDDENM2 holds (G <>HIDDENR2 {}XBOOLE-0K1 & G c=TARSKIR1 F) & G be finiteFINSET-1V1 implies meetSETFAM-1K1 G <>HIDDENR2 {}XBOOLE-0K1))"..

abbreviation(input) FINSET_1V5("finite-yieldingFINSET-1V5" 70) where
  "finite-yieldingFINSET-1V5 \<equiv> finite-yieldingFINSET-1V3"

mtheorem finset_1_def_4:
  mlet "f be FunctionFUNCT-1M1"
"redefine attr finite-yieldingFINSET-1V5 for FunctionFUNCT-1M1 means
  (\<lambda>f.  for i be objectHIDDENM1 holds i inHIDDENR3 domRELAT-1K1 f implies f .FUNCT-1K1 i be finiteFINSET-1V1)"
proof
(*compatibility*)
  show " for f be FunctionFUNCT-1M1 holds f be finite-yieldingFINSET-1V5 iff ( for i be objectHIDDENM1 holds i inHIDDENR3 domRELAT-1K1 f implies f .FUNCT-1K1 i be finiteFINSET-1V1)"
sorry
qed "sorry"

syntax FINSET_1V6 :: " Set \<Rightarrow> Ty" ("finite-yieldingFINSET-1V6\<^bsub>'( _ ')\<^esub>" [0]70)
translations "finite-yieldingFINSET-1V6\<^bsub>(I)\<^esub>" \<rightharpoonup> "finite-yieldingFINSET-1V3"

mtheorem finset_1_def_5:
  mlet "I be setHIDDENM2", "IT be I -definedRELAT-1V4\<bar>FunctionFUNCT-1M1"
"redefine attr finite-yieldingFINSET-1V6\<^bsub>(I)\<^esub> for I -definedRELAT-1V4\<bar>FunctionFUNCT-1M1 means
  (\<lambda>IT.  for i be objectHIDDENM1 holds i inHIDDENR3 I implies IT .FUNCT-1K1 i be finiteFINSET-1V1)"
proof
(*compatibility*)
  show " for IT be I -definedRELAT-1V4\<bar>FunctionFUNCT-1M1 holds IT be finite-yieldingFINSET-1V6\<^bsub>(I)\<^esub> iff ( for i be objectHIDDENM1 holds i inHIDDENR3 I implies IT .FUNCT-1K1 i be finiteFINSET-1V1)"
sorry
qed "sorry"

mtheorem finset_1_th_15:
" for A be setHIDDENM2 holds  for B be setHIDDENM2 holds B be infiniteFINSET-1V2 implies  not B inTARSKIR2 [:ZFMISC-1K2 A,B :]"
sorry

mtheorem finset_1_cl_31:
  mlet "I be setHIDDENM2", "f be I -definedRELAT-1V4\<bar>FunctionFUNCT-1M1"
"cluster finiteFINSET-1V1\<bar>I -definedRELAT-1V4\<bar>f -compatibleFUNCT-1V7 for FunctionFUNCT-1M1"
proof
(*existence*)
  show " ex it be FunctionFUNCT-1M1 st it be finiteFINSET-1V1\<bar>I -definedRELAT-1V4\<bar>f -compatibleFUNCT-1V7"
sorry
qed "sorry"

mtheorem finset_1_cl_32:
  mlet "X be setHIDDENM2", "Y be setHIDDENM2"
"cluster finiteFINSET-1V1\<bar>X -definedRELAT-1V4\<bar>Y -valuedRELAT-1V5 for FunctionFUNCT-1M1"
proof
(*existence*)
  show " ex it be FunctionFUNCT-1M1 st it be finiteFINSET-1V1\<bar>X -definedRELAT-1V4\<bar>Y -valuedRELAT-1V5"
sorry
qed "sorry"

mtheorem finset_1_cl_33:
  mlet "X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "Y be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster X -definedRELAT-1V4\<bar>Y -valuedRELAT-1V5\<bar> non emptyXBOOLE-0V1\<bar>finiteFINSET-1V1 for FunctionFUNCT-1M1"
proof
(*existence*)
  show " ex it be FunctionFUNCT-1M1 st it be X -definedRELAT-1V4\<bar>Y -valuedRELAT-1V5\<bar> non emptyXBOOLE-0V1\<bar>finiteFINSET-1V1"
sorry
qed "sorry"

mtheorem finset_1_cl_34:
  mlet "A be setHIDDENM2", "F be finiteFINSET-1V1\<bar>RelationRELAT-1M1"
"cluster A |`RELAT-1K9 F as-term-is finiteFINSET-1V1"
proof
(*coherence*)
  show "A |`RELAT-1K9 F be finiteFINSET-1V1"
sorry
qed "sorry"

mtheorem finset_1_cl_35:
  mlet "A be setHIDDENM2", "F be finiteFINSET-1V1\<bar>RelationRELAT-1M1"
"cluster F |RELAT-1K8 A as-term-is finiteFINSET-1V1"
proof
(*coherence*)
  show "F |RELAT-1K8 A be finiteFINSET-1V1"
sorry
qed "sorry"

mtheorem finset_1_cl_36:
  mlet "A be finiteFINSET-1V1\<bar>setHIDDENM2", "F be FunctionFUNCT-1M1"
"cluster F |RELAT-1K8 A as-term-is finiteFINSET-1V1"
proof
(*coherence*)
  show "F |RELAT-1K8 A be finiteFINSET-1V1"
sorry
qed "sorry"

mtheorem finset_1_cl_37:
  mlet "R be finiteFINSET-1V1\<bar>RelationRELAT-1M1"
"cluster fieldRELAT-1K3 R as-term-is finiteFINSET-1V1"
proof
(*coherence*)
  show "fieldRELAT-1K3 R be finiteFINSET-1V1"
     sorry
qed "sorry"

mtheorem finset_1_cl_38:
"cluster trivialSUBSET-1V2 also-is finiteFINSET-1V1 for setHIDDENM2"
proof
(*coherence*)
  show " for it be setHIDDENM2 holds it be trivialSUBSET-1V2 implies it be finiteFINSET-1V1"
sorry
qed "sorry"

mtheorem finset_1_cl_39:
"cluster infiniteFINSET-1V2 also-is  non trivialSUBSET-1V2 for setHIDDENM2"
proof
(*coherence*)
  show " for it be setHIDDENM2 holds it be infiniteFINSET-1V2 implies it be  non trivialSUBSET-1V2"
     sorry
qed "sorry"

mtheorem finset_1_cl_40:
  mlet "X be  non trivialSUBSET-1V2\<bar>setHIDDENM2"
"cluster finiteFINSET-1V1\<bar> non trivialSUBSET-1V2 for SubsetSUBSET-1M2-of X"
proof
(*existence*)
  show " ex it be SubsetSUBSET-1M2-of X st it be finiteFINSET-1V1\<bar> non trivialSUBSET-1V2"
sorry
qed "sorry"

mtheorem finset_1_cl_41:
  mlet "x be objectHIDDENM1", "y be objectHIDDENM1", "a be objectHIDDENM1", "b be objectHIDDENM1"
"cluster (x,y)-->FUNCT-4K6(a,b) as-term-is finiteFINSET-1V1"
proof
(*coherence*)
  show "(x,y)-->FUNCT-4K6(a,b) be finiteFINSET-1V1"
     sorry
qed "sorry"

mdef finset_1_def_6 ("finite-memberedFINSET-1V7" 70 ) where
"attr finite-memberedFINSET-1V7 for setHIDDENM2 means
  (\<lambda>A.  for B be setHIDDENM2 holds B inTARSKIR2 A implies B be finiteFINSET-1V1)"..

mtheorem finset_1_cl_42:
"cluster emptyXBOOLE-0V1 also-is finite-memberedFINSET-1V7 for setHIDDENM2"
proof
(*coherence*)
  show " for it be setHIDDENM2 holds it be emptyXBOOLE-0V1 implies it be finite-memberedFINSET-1V7"
     sorry
qed "sorry"

mtheorem finset_1_cl_43:
  mlet "A be finite-memberedFINSET-1V7\<bar>setHIDDENM2"
"cluster note-that finiteFINSET-1V1 for ElementSUBSET-1M1-of A"
proof
(*coherence*)
  show " for it be ElementSUBSET-1M1-of A holds it be finiteFINSET-1V1"
sorry
qed "sorry"

mtheorem finset_1_cl_44:
"cluster  non emptyXBOOLE-0V1\<bar>finiteFINSET-1V1\<bar>finite-memberedFINSET-1V7 for setHIDDENM2"
proof
(*existence*)
  show " ex it be setHIDDENM2 st it be  non emptyXBOOLE-0V1\<bar>finiteFINSET-1V1\<bar>finite-memberedFINSET-1V7"
sorry
qed "sorry"

mtheorem finset_1_cl_45:
  mlet "X be finiteFINSET-1V1\<bar>setHIDDENM2"
"cluster {TARSKIK1 X} as-term-is finite-memberedFINSET-1V7"
proof
(*coherence*)
  show "{TARSKIK1 X} be finite-memberedFINSET-1V7"
    using tarski_def_1 sorry
qed "sorry"

mtheorem finset_1_cl_46:
  mlet "X be finiteFINSET-1V1\<bar>setHIDDENM2"
"cluster boolSETFAM-1K9 X as-term-is finite-memberedFINSET-1V7"
proof
(*coherence*)
  show "boolSETFAM-1K9 X be finite-memberedFINSET-1V7"
     sorry
qed "sorry"

mtheorem finset_1_cl_47:
  mlet "X be finiteFINSET-1V1\<bar>setHIDDENM2", "Y be finiteFINSET-1V1\<bar>setHIDDENM2"
"cluster {TARSKIK2 X,Y } as-term-is finite-memberedFINSET-1V7"
proof
(*coherence*)
  show "{TARSKIK2 X,Y } be finite-memberedFINSET-1V7"
    using tarski_def_2 sorry
qed "sorry"

mtheorem finset_1_cl_48:
  mlet "X be finite-memberedFINSET-1V7\<bar>setHIDDENM2"
"cluster note-that finite-memberedFINSET-1V7 for SubsetSUBSET-1M2-of X"
proof
(*coherence*)
  show " for it be SubsetSUBSET-1M2-of X holds it be finite-memberedFINSET-1V7"
     sorry
qed "sorry"

mtheorem finset_1_cl_49:
  mlet "X be finite-memberedFINSET-1V7\<bar>setHIDDENM2", "Y be finite-memberedFINSET-1V7\<bar>setHIDDENM2"
"cluster X \\/XBOOLE-0K2 Y as-term-is finite-memberedFINSET-1V7"
proof
(*coherence*)
  show "X \\/XBOOLE-0K2 Y be finite-memberedFINSET-1V7"
sorry
qed "sorry"

mtheorem finset_1_cl_50:
  mlet "X be finiteFINSET-1V1\<bar>finite-memberedFINSET-1V7\<bar>setHIDDENM2"
"cluster unionTARSKIK3 X as-term-is finiteFINSET-1V1"
proof
(*coherence*)
  show "unionTARSKIK3 X be finiteFINSET-1V1"
sorry
qed "sorry"

mtheorem finset_1_cl_51:
"cluster  non emptyXBOOLE-0V1\<bar>finite-yieldingFINSET-1V5 for FunctionFUNCT-1M1"
proof
(*existence*)
  show " ex it be FunctionFUNCT-1M1 st it be  non emptyXBOOLE-0V1\<bar>finite-yieldingFINSET-1V5"
sorry
qed "sorry"

mtheorem finset_1_cl_52:
"cluster emptyXBOOLE-0V1 also-is finite-yieldingFINSET-1V3 for RelationRELAT-1M1"
proof
(*coherence*)
  show " for it be RelationRELAT-1M1 holds it be emptyXBOOLE-0V1 implies it be finite-yieldingFINSET-1V3"
     sorry
qed "sorry"

mtheorem finset_1_cl_53:
  mlet "F be finite-yieldingFINSET-1V5\<bar>FunctionFUNCT-1M1", "x be objectHIDDENM1"
"cluster F .FUNCT-1K1 x as-term-is finiteFINSET-1V1"
proof
(*coherence*)
  show "F .FUNCT-1K1 x be finiteFINSET-1V1"
sorry
qed "sorry"

mtheorem finset_1_cl_54:
  mlet "F be finite-yieldingFINSET-1V3\<bar>RelationRELAT-1M1"
"cluster rngRELAT-1K2 F as-term-is finite-memberedFINSET-1V7"
proof
(*coherence*)
  show "rngRELAT-1K2 F be finite-memberedFINSET-1V7"
    using finset_1_def_2 sorry
qed "sorry"

end
