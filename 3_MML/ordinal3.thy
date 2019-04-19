theory ordinal3
  imports ordinal2
   "../mizar_extension/E_number"
begin
(*begin*)
reserve fi, psi for "Ordinal-SequenceORDINAL2M1"
reserve A, A1, B, C, D for "OrdinalORDINAL1M3"
reserve X, Y for "setHIDDENM2"
reserve x, y for "objectHIDDENM1"
mtheorem ordinal3_th_1:
" for X be setHIDDENM2 holds X c=TARSKIR1 succORDINAL1K1 X"
  using xboole_1_th_7 sorry

mtheorem ordinal3_th_2:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds succORDINAL1K1 X c=TARSKIR1 Y implies X c=TARSKIR1 Y"
sorry

mtheorem ordinal3_th_3:
" for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds A inTARSKIR2 B iff succORDINAL1K1 A inTARSKIR2 succORDINAL1K1 B"
sorry

mtheorem ordinal3_th_4:
" for A be OrdinalORDINAL1M3 holds  for X be setHIDDENM2 holds X c=TARSKIR1 A implies unionTARSKIK3 X be epsilon-transitiveORDINAL1V1\<bar>epsilon-connectedORDINAL1V2\<bar>setHIDDENM2"
sorry

mtheorem ordinal3_th_5:
" for X be setHIDDENM2 holds unionTARSKIK3 (OnORDINAL1K2 X) be epsilon-transitiveORDINAL1V1\<bar>epsilon-connectedORDINAL1V2\<bar>setHIDDENM2"
sorry

mtheorem ordinal3_th_6:
" for A be OrdinalORDINAL1M3 holds  for X be setHIDDENM2 holds X c=TARSKIR1 A implies OnORDINAL1K2 X =XBOOLE-0R4 X"
sorry

mtheorem ordinal3_th_7:
" for A be OrdinalORDINAL1M3 holds OnORDINAL1K2 {TARSKIK1 A} =XBOOLE-0R4 {TARSKIK1 A}"
sorry

mtheorem ordinal3_th_8:
" for A be OrdinalORDINAL1M3 holds A <>HIDDENR2 {}XBOOLE-0K1 implies {}XBOOLE-0K1 inTARSKIR2 A"
sorry

mtheorem ordinal3_th_9:
" for A be OrdinalORDINAL1M3 holds infORDINAL2K2 A =XBOOLE-0R4 {}XBOOLE-0K1"
sorry

mtheorem ordinal3_th_10:
" for A be OrdinalORDINAL1M3 holds infORDINAL2K2 {TARSKIK1 A} =XBOOLE-0R4 A"
sorry

mtheorem ordinal3_th_11:
" for A be OrdinalORDINAL1M3 holds  for X be setHIDDENM2 holds X c=TARSKIR1 A implies meetSETFAM-1K1 X be OrdinalORDINAL1M3"
sorry

mtheorem ordinal3_cl_1:
  mlet "A be OrdinalORDINAL1M3", "B be OrdinalORDINAL1M3"
"cluster A \\/XBOOLE-0K2 B as-term-is ordinalORDINAL1V3"
proof
(*coherence*)
  show "A \\/XBOOLE-0K2 B be ordinalORDINAL1V3"
sorry
qed "sorry"

mtheorem ordinal3_cl_2:
  mlet "A be OrdinalORDINAL1M3", "B be OrdinalORDINAL1M3"
"cluster A /\\XBOOLE-0K3 B as-term-is ordinalORDINAL1V3"
proof
(*coherence*)
  show "A /\\XBOOLE-0K3 B be ordinalORDINAL1V3"
sorry
qed "sorry"

mtheorem ordinal3_th_12:
" for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds A \\/XBOOLE-0K2 B =XBOOLE-0R4 A or A \\/XBOOLE-0K2 B =XBOOLE-0R4 B"
sorry

mtheorem ordinal3_th_13:
" for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds A /\\XBOOLE-0K3 B =XBOOLE-0R4 A or A /\\XBOOLE-0K3 B =XBOOLE-0R4 B"
sorry

mlemma ordinal3_lm_1:
"\<one>\<^sub>M =XBOOLE-0R4 succORDINAL1K1 (0ORDINAL1K5)"
   sorry

mtheorem ordinal3_th_14:
" for A be OrdinalORDINAL1M3 holds A inTARSKIR2 \<one>\<^sub>M implies A =XBOOLE-0R4 {}XBOOLE-0K1"
sorry

mtheorem ordinal3_th_15:
"\<one>\<^sub>M =XBOOLE-0R4 {TARSKIK1 {}XBOOLE-0K1 }"
  using ordinal3_lm_1 sorry

mtheorem ordinal3_th_16:
" for A be OrdinalORDINAL1M3 holds A c=ORDINAL1R1 \<one>\<^sub>M implies A =XBOOLE-0R4 {}XBOOLE-0K1 or A =XBOOLE-0R4 \<one>\<^sub>M"
sorry

mtheorem ordinal3_th_17:
" for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds  for C be OrdinalORDINAL1M3 holds  for D be OrdinalORDINAL1M3 holds (A c=ORDINAL1R1 B or A inTARSKIR2 B) & C inTARSKIR2 D implies A +^ORDINAL2K10 C inTARSKIR2 B +^ORDINAL2K10 D"
sorry

mtheorem ordinal3_th_18:
" for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds  for C be OrdinalORDINAL1M3 holds  for D be OrdinalORDINAL1M3 holds A c=ORDINAL1R1 B & C c=ORDINAL1R1 D implies A +^ORDINAL2K10 C c=ORDINAL1R1 B +^ORDINAL2K10 D"
sorry

mtheorem ordinal3_th_19:
" for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds  for C be OrdinalORDINAL1M3 holds  for D be OrdinalORDINAL1M3 holds A inTARSKIR2 B & (C c=ORDINAL1R1 D & D <>HIDDENR2 {}XBOOLE-0K1 or C inTARSKIR2 D) implies A *^ORDINAL2K11 C inTARSKIR2 B *^ORDINAL2K11 D"
sorry

mtheorem ordinal3_th_20:
" for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds  for C be OrdinalORDINAL1M3 holds  for D be OrdinalORDINAL1M3 holds A c=ORDINAL1R1 B & C c=ORDINAL1R1 D implies A *^ORDINAL2K11 C c=ORDINAL1R1 B *^ORDINAL2K11 D"
sorry

mtheorem ordinal3_th_21:
" for B be OrdinalORDINAL1M3 holds  for C be OrdinalORDINAL1M3 holds  for D be OrdinalORDINAL1M3 holds B +^ORDINAL2K10 C =XBOOLE-0R4 B +^ORDINAL2K10 D implies C =XBOOLE-0R4 D"
sorry

mtheorem ordinal3_th_22:
" for B be OrdinalORDINAL1M3 holds  for C be OrdinalORDINAL1M3 holds  for D be OrdinalORDINAL1M3 holds B +^ORDINAL2K10 C inTARSKIR2 B +^ORDINAL2K10 D implies C inTARSKIR2 D"
sorry

mtheorem ordinal3_th_23:
" for B be OrdinalORDINAL1M3 holds  for C be OrdinalORDINAL1M3 holds  for D be OrdinalORDINAL1M3 holds B +^ORDINAL2K10 C c=ORDINAL1R1 B +^ORDINAL2K10 D implies C c=ORDINAL1R1 D"
sorry

mtheorem ordinal3_th_24:
" for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds A c=ORDINAL1R1 A +^ORDINAL2K10 B & B c=ORDINAL1R1 A +^ORDINAL2K10 B"
sorry

mtheorem ordinal3_th_25:
" for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds  for C be OrdinalORDINAL1M3 holds A inTARSKIR2 B implies A inTARSKIR2 B +^ORDINAL2K10 C & A inTARSKIR2 C +^ORDINAL2K10 B"
sorry

mtheorem ordinal3_th_26:
" for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds A +^ORDINAL2K10 B =XBOOLE-0R4 {}XBOOLE-0K1 implies A =XBOOLE-0R4 {}XBOOLE-0K1 & B =XBOOLE-0R4 {}XBOOLE-0K1"
  using ordinal3_th_24 xboole_1_th_3 sorry

mtheorem ordinal3_th_27:
" for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds A c=ORDINAL1R1 B implies ( ex C be OrdinalORDINAL1M3 st B =XBOOLE-0R4 A +^ORDINAL2K10 C)"
sorry

mtheorem ordinal3_th_28:
" for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds A inTARSKIR2 B implies ( ex C be OrdinalORDINAL1M3 st B =XBOOLE-0R4 A +^ORDINAL2K10 C & C <>HIDDENR2 {}XBOOLE-0K1)"
sorry

mtheorem ordinal3_th_29:
" for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds A <>HIDDENR2 {}XBOOLE-0K1 & A be limit-ordinalORDINAL1V4 implies B +^ORDINAL2K10 A be limit-ordinalORDINAL1V4"
sorry

mtheorem ordinal3_th_30:
" for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds  for C be OrdinalORDINAL1M3 holds (A +^ORDINAL2K10 B)+^ORDINAL2K10 C =XBOOLE-0R4 A +^ORDINAL2K10 (B +^ORDINAL2K10 C)"
sorry

mtheorem ordinal3_th_31:
" for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds A *^ORDINAL2K11 B =XBOOLE-0R4 {}XBOOLE-0K1 implies A =XBOOLE-0R4 {}XBOOLE-0K1 or B =XBOOLE-0R4 {}XBOOLE-0K1"
sorry

mtheorem ordinal3_th_32:
" for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds  for C be OrdinalORDINAL1M3 holds A inTARSKIR2 B & C <>HIDDENR2 {}XBOOLE-0K1 implies A inTARSKIR2 B *^ORDINAL2K11 C & A inTARSKIR2 C *^ORDINAL2K11 B"
sorry

mtheorem ordinal3_th_33:
" for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds  for C be OrdinalORDINAL1M3 holds B *^ORDINAL2K11 A =XBOOLE-0R4 C *^ORDINAL2K11 A & A <>HIDDENR2 {}XBOOLE-0K1 implies B =XBOOLE-0R4 C"
sorry

mtheorem ordinal3_th_34:
" for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds  for C be OrdinalORDINAL1M3 holds B *^ORDINAL2K11 A inTARSKIR2 C *^ORDINAL2K11 A implies B inTARSKIR2 C"
sorry

mtheorem ordinal3_th_35:
" for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds  for C be OrdinalORDINAL1M3 holds B *^ORDINAL2K11 A c=ORDINAL1R1 C *^ORDINAL2K11 A & A <>HIDDENR2 {}XBOOLE-0K1 implies B c=ORDINAL1R1 C"
sorry

mtheorem ordinal3_th_36:
" for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds B <>HIDDENR2 {}XBOOLE-0K1 implies A c=ORDINAL1R1 A *^ORDINAL2K11 B & A c=ORDINAL1R1 B *^ORDINAL2K11 A"
sorry

mtheorem ordinal3_th_37:
" for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds A *^ORDINAL2K11 B =XBOOLE-0R4 \<one>\<^sub>M implies A =XBOOLE-0R4 \<one>\<^sub>M & B =XBOOLE-0R4 \<one>\<^sub>M"
sorry

mtheorem ordinal3_th_38:
" for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds  for C be OrdinalORDINAL1M3 holds A inTARSKIR2 B +^ORDINAL2K10 C implies A inTARSKIR2 B or ( ex D be OrdinalORDINAL1M3 st D inTARSKIR2 C & A =XBOOLE-0R4 B +^ORDINAL2K10 D)"
sorry

mdef ordinal3_def_1 (" _ +^ORDINAL3K1  _ " [132,132]132 ) where
  mlet "C be OrdinalORDINAL1M3", "fi be Ordinal-SequenceORDINAL2M1"
"func C +^ORDINAL3K1 fi \<rightarrow> Ordinal-SequenceORDINAL2M1 means
  \<lambda>it. domRELAT-1K1 it =XBOOLE-0R4 domRELAT-1K1 fi & ( for A be OrdinalORDINAL1M3 holds A inTARSKIR2 domRELAT-1K1 fi implies it .FUNCT-1K1 A =XBOOLE-0R4 C +^ORDINAL2K10 fi .FUNCT-1K1 A)"
proof-
  (*existence*)
    show " ex it be Ordinal-SequenceORDINAL2M1 st domRELAT-1K1 it =XBOOLE-0R4 domRELAT-1K1 fi & ( for A be OrdinalORDINAL1M3 holds A inTARSKIR2 domRELAT-1K1 fi implies it .FUNCT-1K1 A =XBOOLE-0R4 C +^ORDINAL2K10 fi .FUNCT-1K1 A)"
sorry
  (*uniqueness*)
    show " for it1 be Ordinal-SequenceORDINAL2M1 holds  for it2 be Ordinal-SequenceORDINAL2M1 holds (domRELAT-1K1 it1 =XBOOLE-0R4 domRELAT-1K1 fi & ( for A be OrdinalORDINAL1M3 holds A inTARSKIR2 domRELAT-1K1 fi implies it1 .FUNCT-1K1 A =XBOOLE-0R4 C +^ORDINAL2K10 fi .FUNCT-1K1 A)) & (domRELAT-1K1 it2 =XBOOLE-0R4 domRELAT-1K1 fi & ( for A be OrdinalORDINAL1M3 holds A inTARSKIR2 domRELAT-1K1 fi implies it2 .FUNCT-1K1 A =XBOOLE-0R4 C +^ORDINAL2K10 fi .FUNCT-1K1 A)) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mdef ordinal3_def_2 (" _ +^ORDINAL3K2  _ " [132,132]132 ) where
  mlet "C be OrdinalORDINAL1M3", "fi be Ordinal-SequenceORDINAL2M1"
"func fi +^ORDINAL3K2 C \<rightarrow> Ordinal-SequenceORDINAL2M1 means
  \<lambda>it. domRELAT-1K1 it =XBOOLE-0R4 domRELAT-1K1 fi & ( for A be OrdinalORDINAL1M3 holds A inTARSKIR2 domRELAT-1K1 fi implies it .FUNCT-1K1 A =XBOOLE-0R4 fi .FUNCT-1K1 A +^ORDINAL2K10 C)"
proof-
  (*existence*)
    show " ex it be Ordinal-SequenceORDINAL2M1 st domRELAT-1K1 it =XBOOLE-0R4 domRELAT-1K1 fi & ( for A be OrdinalORDINAL1M3 holds A inTARSKIR2 domRELAT-1K1 fi implies it .FUNCT-1K1 A =XBOOLE-0R4 fi .FUNCT-1K1 A +^ORDINAL2K10 C)"
sorry
  (*uniqueness*)
    show " for it1 be Ordinal-SequenceORDINAL2M1 holds  for it2 be Ordinal-SequenceORDINAL2M1 holds (domRELAT-1K1 it1 =XBOOLE-0R4 domRELAT-1K1 fi & ( for A be OrdinalORDINAL1M3 holds A inTARSKIR2 domRELAT-1K1 fi implies it1 .FUNCT-1K1 A =XBOOLE-0R4 fi .FUNCT-1K1 A +^ORDINAL2K10 C)) & (domRELAT-1K1 it2 =XBOOLE-0R4 domRELAT-1K1 fi & ( for A be OrdinalORDINAL1M3 holds A inTARSKIR2 domRELAT-1K1 fi implies it2 .FUNCT-1K1 A =XBOOLE-0R4 fi .FUNCT-1K1 A +^ORDINAL2K10 C)) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mdef ordinal3_def_3 (" _ *^ORDINAL3K3  _ " [164,164]164 ) where
  mlet "C be OrdinalORDINAL1M3", "fi be Ordinal-SequenceORDINAL2M1"
"func C *^ORDINAL3K3 fi \<rightarrow> Ordinal-SequenceORDINAL2M1 means
  \<lambda>it. domRELAT-1K1 it =XBOOLE-0R4 domRELAT-1K1 fi & ( for A be OrdinalORDINAL1M3 holds A inTARSKIR2 domRELAT-1K1 fi implies it .FUNCT-1K1 A =XBOOLE-0R4 C *^ORDINAL2K11 fi .FUNCT-1K1 A)"
proof-
  (*existence*)
    show " ex it be Ordinal-SequenceORDINAL2M1 st domRELAT-1K1 it =XBOOLE-0R4 domRELAT-1K1 fi & ( for A be OrdinalORDINAL1M3 holds A inTARSKIR2 domRELAT-1K1 fi implies it .FUNCT-1K1 A =XBOOLE-0R4 C *^ORDINAL2K11 fi .FUNCT-1K1 A)"
sorry
  (*uniqueness*)
    show " for it1 be Ordinal-SequenceORDINAL2M1 holds  for it2 be Ordinal-SequenceORDINAL2M1 holds (domRELAT-1K1 it1 =XBOOLE-0R4 domRELAT-1K1 fi & ( for A be OrdinalORDINAL1M3 holds A inTARSKIR2 domRELAT-1K1 fi implies it1 .FUNCT-1K1 A =XBOOLE-0R4 C *^ORDINAL2K11 fi .FUNCT-1K1 A)) & (domRELAT-1K1 it2 =XBOOLE-0R4 domRELAT-1K1 fi & ( for A be OrdinalORDINAL1M3 holds A inTARSKIR2 domRELAT-1K1 fi implies it2 .FUNCT-1K1 A =XBOOLE-0R4 C *^ORDINAL2K11 fi .FUNCT-1K1 A)) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mdef ordinal3_def_4 (" _ *^ORDINAL3K4  _ " [164,164]164 ) where
  mlet "C be OrdinalORDINAL1M3", "fi be Ordinal-SequenceORDINAL2M1"
"func fi *^ORDINAL3K4 C \<rightarrow> Ordinal-SequenceORDINAL2M1 means
  \<lambda>it. domRELAT-1K1 it =XBOOLE-0R4 domRELAT-1K1 fi & ( for A be OrdinalORDINAL1M3 holds A inTARSKIR2 domRELAT-1K1 fi implies it .FUNCT-1K1 A =XBOOLE-0R4 fi .FUNCT-1K1 A *^ORDINAL2K11 C)"
proof-
  (*existence*)
    show " ex it be Ordinal-SequenceORDINAL2M1 st domRELAT-1K1 it =XBOOLE-0R4 domRELAT-1K1 fi & ( for A be OrdinalORDINAL1M3 holds A inTARSKIR2 domRELAT-1K1 fi implies it .FUNCT-1K1 A =XBOOLE-0R4 fi .FUNCT-1K1 A *^ORDINAL2K11 C)"
sorry
  (*uniqueness*)
    show " for it1 be Ordinal-SequenceORDINAL2M1 holds  for it2 be Ordinal-SequenceORDINAL2M1 holds (domRELAT-1K1 it1 =XBOOLE-0R4 domRELAT-1K1 fi & ( for A be OrdinalORDINAL1M3 holds A inTARSKIR2 domRELAT-1K1 fi implies it1 .FUNCT-1K1 A =XBOOLE-0R4 fi .FUNCT-1K1 A *^ORDINAL2K11 C)) & (domRELAT-1K1 it2 =XBOOLE-0R4 domRELAT-1K1 fi & ( for A be OrdinalORDINAL1M3 holds A inTARSKIR2 domRELAT-1K1 fi implies it2 .FUNCT-1K1 A =XBOOLE-0R4 fi .FUNCT-1K1 A *^ORDINAL2K11 C)) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mtheorem ordinal3_th_39:
" for fi be Ordinal-SequenceORDINAL2M1 holds  for psi be Ordinal-SequenceORDINAL2M1 holds  for C be OrdinalORDINAL1M3 holds ({}XBOOLE-0K1 <>HIDDENR2 domRELAT-1K1 fi & domRELAT-1K1 fi =XBOOLE-0R4 domRELAT-1K1 psi) & ( for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds A inTARSKIR2 domRELAT-1K1 fi & B =XBOOLE-0R4 fi .FUNCT-1K1 A implies psi .FUNCT-1K1 A =XBOOLE-0R4 C +^ORDINAL2K10 B) implies supORDINAL2K4 psi =XBOOLE-0R4 C +^ORDINAL2K10 supORDINAL2K4 fi"
sorry

mtheorem ordinal3_th_40:
" for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds A be limit-ordinalORDINAL1V4 implies A *^ORDINAL2K11 B be limit-ordinalORDINAL1V4"
sorry

mtheorem ordinal3_th_41:
" for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds  for C be OrdinalORDINAL1M3 holds A inTARSKIR2 B *^ORDINAL2K11 C & B be limit-ordinalORDINAL1V4 implies ( ex D be OrdinalORDINAL1M3 st D inTARSKIR2 B & A inTARSKIR2 D *^ORDINAL2K11 C)"
sorry

mtheorem ordinal3_th_42:
" for fi be Ordinal-SequenceORDINAL2M1 holds  for psi be Ordinal-SequenceORDINAL2M1 holds  for C be OrdinalORDINAL1M3 holds ((domRELAT-1K1 fi =XBOOLE-0R4 domRELAT-1K1 psi & C <>HIDDENR2 {}XBOOLE-0K1) & supORDINAL2K4 fi be limit-ordinalORDINAL1V4) & ( for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds A inTARSKIR2 domRELAT-1K1 fi & B =XBOOLE-0R4 fi .FUNCT-1K1 A implies psi .FUNCT-1K1 A =XBOOLE-0R4 B *^ORDINAL2K11 C) implies supORDINAL2K4 psi =XBOOLE-0R4 supORDINAL2K4 fi *^ORDINAL2K11 C"
sorry

mtheorem ordinal3_th_43:
" for fi be Ordinal-SequenceORDINAL2M1 holds  for C be OrdinalORDINAL1M3 holds {}XBOOLE-0K1 <>HIDDENR2 domRELAT-1K1 fi implies supORDINAL2K4 (C +^ORDINAL3K1 fi) =XBOOLE-0R4 C +^ORDINAL2K10 supORDINAL2K4 fi"
sorry

mtheorem ordinal3_th_44:
" for fi be Ordinal-SequenceORDINAL2M1 holds  for C be OrdinalORDINAL1M3 holds ({}XBOOLE-0K1 <>HIDDENR2 domRELAT-1K1 fi & C <>HIDDENR2 {}XBOOLE-0K1) & supORDINAL2K4 fi be limit-ordinalORDINAL1V4 implies supORDINAL2K4 (fi *^ORDINAL3K4 C) =XBOOLE-0R4 supORDINAL2K4 fi *^ORDINAL2K11 C"
sorry

mtheorem ordinal3_th_45:
" for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds B <>HIDDENR2 {}XBOOLE-0K1 implies unionTARSKIK3 (A +^ORDINAL2K10 B) =XBOOLE-0R4 A +^ORDINAL2K10 unionTARSKIK3 B"
sorry

mtheorem ordinal3_th_46:
" for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds  for C be OrdinalORDINAL1M3 holds (A +^ORDINAL2K10 B)*^ORDINAL2K11 C =XBOOLE-0R4 A *^ORDINAL2K11 C +^ORDINAL2K10 B *^ORDINAL2K11 C"
sorry

mtheorem ordinal3_th_47:
" for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds A <>HIDDENR2 {}XBOOLE-0K1 implies ( ex C be OrdinalORDINAL1M3 st  ex D be OrdinalORDINAL1M3 st B =XBOOLE-0R4 C *^ORDINAL2K11 A +^ORDINAL2K10 D & D inTARSKIR2 A)"
sorry

mtheorem ordinal3_th_48:
" for A be OrdinalORDINAL1M3 holds  for C1 be OrdinalORDINAL1M3 holds  for D1 be OrdinalORDINAL1M3 holds  for C2 be OrdinalORDINAL1M3 holds  for D2 be OrdinalORDINAL1M3 holds (C1 *^ORDINAL2K11 A +^ORDINAL2K10 D1 =XBOOLE-0R4 C2 *^ORDINAL2K11 A +^ORDINAL2K10 D2 & D1 inTARSKIR2 A) & D2 inTARSKIR2 A implies C1 =XBOOLE-0R4 C2 & D1 =XBOOLE-0R4 D2"
sorry

mtheorem ordinal3_th_49:
" for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds (\<one>\<^sub>M inTARSKIR2 B & A <>HIDDENR2 {}XBOOLE-0K1) & A be limit-ordinalORDINAL1V4 implies ( for fi be Ordinal-SequenceORDINAL2M1 holds domRELAT-1K1 fi =XBOOLE-0R4 A & ( for C be OrdinalORDINAL1M3 holds C inTARSKIR2 A implies fi .FUNCT-1K1 C =XBOOLE-0R4 C *^ORDINAL2K11 B) implies A *^ORDINAL2K11 B =XBOOLE-0R4 supORDINAL2K4 fi)"
sorry

mtheorem ordinal3_th_50:
" for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds  for C be OrdinalORDINAL1M3 holds (A *^ORDINAL2K11 B)*^ORDINAL2K11 C =XBOOLE-0R4 A *^ORDINAL2K11 (B *^ORDINAL2K11 C)"
sorry

mdef ordinal3_def_5 (" _ -^ORDINAL3K5  _ " [132,132]132 ) where
  mlet "A be OrdinalORDINAL1M3", "B be OrdinalORDINAL1M3"
"func A -^ORDINAL3K5 B \<rightarrow> OrdinalORDINAL1M3 means
  \<lambda>it. A =XBOOLE-0R4 B +^ORDINAL2K10 it if B c=ORDINAL1R1 A otherwise \<lambda>it. it =XBOOLE-0R4 {}XBOOLE-0K1"
proof-
  (*existence*)
    show "(B c=ORDINAL1R1 A implies ( ex it be OrdinalORDINAL1M3 st A =XBOOLE-0R4 B +^ORDINAL2K10 it)) & ( not B c=ORDINAL1R1 A implies ( ex it be OrdinalORDINAL1M3 st it =XBOOLE-0R4 {}XBOOLE-0K1))"
      using ordinal3_th_27 sorry
  (*uniqueness*)
    show " for it1 be OrdinalORDINAL1M3 holds  for it2 be OrdinalORDINAL1M3 holds (B c=ORDINAL1R1 A implies (A =XBOOLE-0R4 B +^ORDINAL2K10 it1 & A =XBOOLE-0R4 B +^ORDINAL2K10 it2 implies it1 =HIDDENR1 it2)) & ( not B c=ORDINAL1R1 A implies (it1 =XBOOLE-0R4 {}XBOOLE-0K1 & it2 =XBOOLE-0R4 {}XBOOLE-0K1 implies it1 =HIDDENR1 it2))"
      using ordinal3_th_21 sorry
  (*consistency*)
    show " for it be OrdinalORDINAL1M3 holds  True "
       sorry
qed "sorry"

mdef ordinal3_def_6 (" _ div^ORDINAL3K6  _ " [132,132]132 ) where
  mlet "A be OrdinalORDINAL1M3", "B be OrdinalORDINAL1M3"
"func A div^ORDINAL3K6 B \<rightarrow> OrdinalORDINAL1M3 means
  \<lambda>it.  ex C be OrdinalORDINAL1M3 st A =XBOOLE-0R4 it *^ORDINAL2K11 B +^ORDINAL2K10 C & C inTARSKIR2 B if B <>HIDDENR2 {}XBOOLE-0K1 otherwise \<lambda>it. it =XBOOLE-0R4 {}XBOOLE-0K1"
proof-
  (*consistency*)
    show " for it be OrdinalORDINAL1M3 holds  True "
       sorry
  (*existence*)
    show "(B <>HIDDENR2 {}XBOOLE-0K1 implies ( ex it be OrdinalORDINAL1M3 st  ex C be OrdinalORDINAL1M3 st A =XBOOLE-0R4 it *^ORDINAL2K11 B +^ORDINAL2K10 C & C inTARSKIR2 B)) & ( not B <>HIDDENR2 {}XBOOLE-0K1 implies ( ex it be OrdinalORDINAL1M3 st it =XBOOLE-0R4 {}XBOOLE-0K1))"
      using ordinal3_th_47 sorry
  (*uniqueness*)
    show " for it1 be OrdinalORDINAL1M3 holds  for it2 be OrdinalORDINAL1M3 holds (B <>HIDDENR2 {}XBOOLE-0K1 implies (( ex C be OrdinalORDINAL1M3 st A =XBOOLE-0R4 it1 *^ORDINAL2K11 B +^ORDINAL2K10 C & C inTARSKIR2 B) & ( ex C be OrdinalORDINAL1M3 st A =XBOOLE-0R4 it2 *^ORDINAL2K11 B +^ORDINAL2K10 C & C inTARSKIR2 B) implies it1 =HIDDENR1 it2)) & ( not B <>HIDDENR2 {}XBOOLE-0K1 implies (it1 =XBOOLE-0R4 {}XBOOLE-0K1 & it2 =XBOOLE-0R4 {}XBOOLE-0K1 implies it1 =HIDDENR1 it2))"
      using ordinal3_th_48 sorry
qed "sorry"

mdef ordinal3_def_7 (" _ mod^ORDINAL3K7  _ " [132,132]132 ) where
  mlet "A be OrdinalORDINAL1M3", "B be OrdinalORDINAL1M3"
"func A mod^ORDINAL3K7 B \<rightarrow> OrdinalORDINAL1M3 equals
  A -^ORDINAL3K5 (A div^ORDINAL3K6 B)*^ORDINAL2K11 B"
proof-
  (*coherence*)
    show "A -^ORDINAL3K5 (A div^ORDINAL3K6 B)*^ORDINAL2K11 B be OrdinalORDINAL1M3"
       sorry
qed "sorry"

mtheorem ordinal3_th_51:
" for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds A inTARSKIR2 B implies B =XBOOLE-0R4 A +^ORDINAL2K10 (B -^ORDINAL3K5 A)"
sorry

mtheorem ordinal3_th_52:
" for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds (A +^ORDINAL2K10 B)-^ORDINAL3K5 A =XBOOLE-0R4 B"
sorry

mtheorem ordinal3_th_53:
" for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds  for C be OrdinalORDINAL1M3 holds A inTARSKIR2 B & (C c=ORDINAL1R1 A or C inTARSKIR2 A) implies A -^ORDINAL3K5 C inTARSKIR2 B -^ORDINAL3K5 C"
sorry

mtheorem ordinal3_th_54:
" for A be OrdinalORDINAL1M3 holds A -^ORDINAL3K5 A =XBOOLE-0R4 {}XBOOLE-0K1"
sorry

mtheorem ordinal3_th_55:
" for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds A inTARSKIR2 B implies B -^ORDINAL3K5 A <>HIDDENR2 {}XBOOLE-0K1 & {}XBOOLE-0K1 inTARSKIR2 B -^ORDINAL3K5 A"
sorry

mtheorem ordinal3_th_56:
" for A be OrdinalORDINAL1M3 holds A -^ORDINAL3K5 {}XBOOLE-0K1 =XBOOLE-0R4 A & {}XBOOLE-0K1 -^ORDINAL3K5 A =XBOOLE-0R4 {}XBOOLE-0K1"
sorry

mtheorem ordinal3_th_57:
" for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds  for C be OrdinalORDINAL1M3 holds A -^ORDINAL3K5 (B +^ORDINAL2K10 C) =XBOOLE-0R4 (A -^ORDINAL3K5 B)-^ORDINAL3K5 C"
sorry

mtheorem ordinal3_th_58:
" for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds  for C be OrdinalORDINAL1M3 holds A c=ORDINAL1R1 B implies C -^ORDINAL3K5 B c=ORDINAL1R1 C -^ORDINAL3K5 A"
sorry

mtheorem ordinal3_th_59:
" for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds  for C be OrdinalORDINAL1M3 holds A c=ORDINAL1R1 B implies A -^ORDINAL3K5 C c=ORDINAL1R1 B -^ORDINAL3K5 C"
sorry

mtheorem ordinal3_th_60:
" for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds  for C be OrdinalORDINAL1M3 holds C <>HIDDENR2 {}XBOOLE-0K1 & A inTARSKIR2 B +^ORDINAL2K10 C implies A -^ORDINAL3K5 B inTARSKIR2 C"
sorry

mtheorem ordinal3_th_61:
" for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds  for C be OrdinalORDINAL1M3 holds A +^ORDINAL2K10 B inTARSKIR2 C implies B inTARSKIR2 C -^ORDINAL3K5 A"
sorry

mtheorem ordinal3_th_62:
" for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds A c=ORDINAL1R1 B +^ORDINAL2K10 (A -^ORDINAL3K5 B)"
sorry

mtheorem ordinal3_th_63:
" for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds  for C be OrdinalORDINAL1M3 holds A *^ORDINAL2K11 C -^ORDINAL3K5 B *^ORDINAL2K11 C =XBOOLE-0R4 (A -^ORDINAL3K5 B)*^ORDINAL2K11 C"
sorry

mtheorem ordinal3_th_64:
" for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds (A div^ORDINAL3K6 B)*^ORDINAL2K11 B c=ORDINAL1R1 A"
sorry

mtheorem ordinal3_th_65:
" for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds A =XBOOLE-0R4 (A div^ORDINAL3K6 B)*^ORDINAL2K11 B +^ORDINAL2K10 (A mod^ORDINAL3K7 B)"
sorry

mtheorem ordinal3_th_66:
" for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds  for C be OrdinalORDINAL1M3 holds  for D be OrdinalORDINAL1M3 holds A =XBOOLE-0R4 B *^ORDINAL2K11 C +^ORDINAL2K10 D & D inTARSKIR2 C implies B =XBOOLE-0R4 A div^ORDINAL3K6 C & D =XBOOLE-0R4 A mod^ORDINAL3K7 C"
sorry

mtheorem ordinal3_th_67:
" for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds  for C be OrdinalORDINAL1M3 holds A inTARSKIR2 B *^ORDINAL2K11 C implies A div^ORDINAL3K6 C inTARSKIR2 B & A mod^ORDINAL3K7 C inTARSKIR2 C"
sorry

mtheorem ordinal3_th_68:
" for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds B <>HIDDENR2 {}XBOOLE-0K1 implies A *^ORDINAL2K11 B div^ORDINAL3K6 B =XBOOLE-0R4 A"
sorry

mtheorem ordinal3_th_69:
" for A be OrdinalORDINAL1M3 holds  for B be OrdinalORDINAL1M3 holds A *^ORDINAL2K11 B mod^ORDINAL3K7 B =XBOOLE-0R4 {}XBOOLE-0K1"
sorry

mtheorem ordinal3_th_70:
" for A be OrdinalORDINAL1M3 holds ({}XBOOLE-0K1 div^ORDINAL3K6 A =XBOOLE-0R4 {}XBOOLE-0K1 & {}XBOOLE-0K1 mod^ORDINAL3K7 A =XBOOLE-0R4 {}XBOOLE-0K1) & A mod^ORDINAL3K7 {}XBOOLE-0K1 =XBOOLE-0R4 A"
sorry

mtheorem ordinal3_th_71:
" for A be OrdinalORDINAL1M3 holds A div^ORDINAL3K6 \<one>\<^sub>M =XBOOLE-0R4 A & A mod^ORDINAL3K7 \<one>\<^sub>M =XBOOLE-0R4 {}XBOOLE-0K1"
sorry

(*begin*)
mtheorem ordinal3_th_72:
" for X be setHIDDENM2 holds supORDINAL2K3 X c=TARSKIR1 succORDINAL1K1 (unionTARSKIK3 (OnORDINAL1K2 X))"
sorry

mtheorem ordinal3_th_73:
" for A be OrdinalORDINAL1M3 holds succORDINAL1K1 A is-cofinal-withORDINAL2R2 \<one>\<^sub>M"
sorry

mtheorem ordinal3_th_74:
" for a be OrdinalORDINAL1M3 holds  for b be OrdinalORDINAL1M3 holds a +^ORDINAL2K10 b be naturalORDINAL1V7 implies a inTARSKIR2 omegaORDINAL1K4 & b inTARSKIR2 omegaORDINAL1K4"
  using ordinal3_th_24 ordinal1_th_12 sorry

mtheorem ordinal3_cl_3:
  mlet "a be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3", "b be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3"
"cluster a -^ORDINAL3K5 b as-term-is naturalORDINAL1V7"
proof
(*coherence*)
  show "a -^ORDINAL3K5 b be naturalORDINAL1V7"
sorry
qed "sorry"

mtheorem ordinal3_cl_4:
  mlet "a be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3", "b be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3"
"cluster a *^ORDINAL2K11 b as-term-is naturalORDINAL1V7"
proof
(*coherence*)
  show "a *^ORDINAL2K11 b be naturalORDINAL1V7"
sorry
qed "sorry"

mtheorem ordinal3_th_75:
" for a be OrdinalORDINAL1M3 holds  for b be OrdinalORDINAL1M3 holds a *^ORDINAL2K11 b be naturalORDINAL1V7\<bar> non emptyXBOOLE-0V1 implies a inTARSKIR2 omegaORDINAL1K4 & b inTARSKIR2 omegaORDINAL1K4"
sorry

abbreviation(input) ORDINAL3K8(" _ +^ORDINAL3K8  _ " [132,132]132) where
  "a +^ORDINAL3K8 b \<equiv> a +^ORDINAL2K10 b"

mtheorem ORDINAL3K8_commutativity:
" for a be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 holds  for b be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 holds a +^ORDINAL3K8 b =HIDDENR1 b +^ORDINAL3K8 a"
sorry

abbreviation(input) ORDINAL3K9(" _ *^ORDINAL3K9  _ " [164,164]164) where
  "a *^ORDINAL3K9 b \<equiv> a *^ORDINAL2K11 b"

mtheorem ORDINAL3K9_commutativity:
" for a be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 holds  for b be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 holds a *^ORDINAL3K9 b =HIDDENR1 b *^ORDINAL3K9 a"
sorry

end
