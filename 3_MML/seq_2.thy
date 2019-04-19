theory seq_2
  imports seq_1 comseq_2
   "../mizar_extension/E_number"
begin
(*begin*)
reserve n, n1, n2, m for "NatNAT-1M1"
reserve r, r1, r2, p, g1, g2, g for "RealXREAL-0M1"
reserve seq, seq9, seq1 for "Real-SequenceSEQ-1M1"
reserve y for "setHIDDENM2"
mtheorem seq_2_th_1:
" for r be RealXREAL-0M1 holds  for g be RealXREAL-0M1 holds -XCMPLX-0K4 g <XXREAL-0R3 r & r <XXREAL-0R3 g iff |.COMPLEX1K10 r.| <XXREAL-0R3 g"
sorry

mtheorem seq_2_th_2:
" for r be RealXREAL-0M1 holds  for g be RealXREAL-0M1 holds g <>HIDDENR2 0NUMBERSK6 & r <>HIDDENR2 0NUMBERSK6 implies |.COMPLEX1K10 g \<inverse>XCMPLX-0K5 -XCMPLX-0K6 r \<inverse>XCMPLX-0K5 .| =COMPLEX1R1 (|.COMPLEX1K10 g -XCMPLX-0K6 r .|)/XCMPLX-0K7 ((|.COMPLEX1K10 g.|)*XCMPLX-0K3 (|.COMPLEX1K10 r.|))"
sorry

mdef seq_2_def_1 ("bounded-aboveSEQ-2V1" 70 ) where
"attr bounded-aboveSEQ-2V1 for real-valuedVALUED-0V7\<bar>FunctionFUNCT-1M1 means
  (\<lambda>f.  ex r be RealXREAL-0M1 st  for y be objectHIDDENM1 holds y inHIDDENR3 domRELAT-1K1 f implies f .FUNCT-1K1 y <XXREAL-0R3 r)"..

mdef seq_2_def_2 ("bounded-belowSEQ-2V2" 70 ) where
"attr bounded-belowSEQ-2V2 for real-valuedVALUED-0V7\<bar>FunctionFUNCT-1M1 means
  (\<lambda>f.  ex r be RealXREAL-0M1 st  for y be objectHIDDENM1 holds y inHIDDENR3 domRELAT-1K1 f implies r <XXREAL-0R3 f .FUNCT-1K1 y)"..

abbreviation(input) SEQ_2V3("bounded-aboveSEQ-2V3" 70) where
  "bounded-aboveSEQ-2V3 \<equiv> bounded-aboveSEQ-2V1"

mtheorem seq_2_def_3:
  mlet "seq be Real-SequenceSEQ-1M1"
"redefine attr bounded-aboveSEQ-2V3 for Real-SequenceSEQ-1M1 means
  (\<lambda>seq.  ex r be RealXREAL-0M1 st  for n be NatNAT-1M1 holds seq .FUNCT-1K1 n <XXREAL-0R3 r)"
proof
(*compatibility*)
  show " for seq be Real-SequenceSEQ-1M1 holds seq be bounded-aboveSEQ-2V3 iff ( ex r be RealXREAL-0M1 st  for n be NatNAT-1M1 holds seq .FUNCT-1K1 n <XXREAL-0R3 r)"
sorry
qed "sorry"

abbreviation(input) SEQ_2V4("bounded-belowSEQ-2V4" 70) where
  "bounded-belowSEQ-2V4 \<equiv> bounded-belowSEQ-2V2"

mtheorem seq_2_def_4:
  mlet "seq be Real-SequenceSEQ-1M1"
"redefine attr bounded-belowSEQ-2V4 for Real-SequenceSEQ-1M1 means
  (\<lambda>seq.  ex r be RealXREAL-0M1 st  for n be NatNAT-1M1 holds r <XXREAL-0R3 seq .FUNCT-1K1 n)"
proof
(*compatibility*)
  show " for seq be Real-SequenceSEQ-1M1 holds seq be bounded-belowSEQ-2V4 iff ( ex r be RealXREAL-0M1 st  for n be NatNAT-1M1 holds r <XXREAL-0R3 seq .FUNCT-1K1 n)"
sorry
qed "sorry"

mtheorem seq_2_cl_1:
"cluster boundedCOMSEQ-2V1 also-is bounded-aboveSEQ-2V1\<bar>bounded-belowSEQ-2V2 for real-valuedVALUED-0V7\<bar>FunctionFUNCT-1M1"
proof
(*coherence*)
  show " for it be real-valuedVALUED-0V7\<bar>FunctionFUNCT-1M1 holds it be boundedCOMSEQ-2V1 implies it be bounded-aboveSEQ-2V1\<bar>bounded-belowSEQ-2V2"
sorry
qed "sorry"

mtheorem seq_2_cl_2:
"cluster bounded-aboveSEQ-2V1\<bar>bounded-belowSEQ-2V2 also-is boundedCOMSEQ-2V1 for real-valuedVALUED-0V7\<bar>FunctionFUNCT-1M1"
proof
(*coherence*)
  show " for it be real-valuedVALUED-0V7\<bar>FunctionFUNCT-1M1 holds it be bounded-aboveSEQ-2V1\<bar>bounded-belowSEQ-2V2 implies it be boundedCOMSEQ-2V1"
sorry
qed "sorry"

mtheorem seq_2_th_3:
" for seq be Real-SequenceSEQ-1M1 holds seq be boundedCOMSEQ-2V1 iff ( ex r be RealXREAL-0M1 st 0NUMBERSK6 <XXREAL-0R3 r & ( for n be NatNAT-1M1 holds |.COMPLEX1K10 seq .FUNCT-1K1 n.| <XXREAL-0R3 r))"
sorry

mtheorem seq_2_th_4:
" for seq be Real-SequenceSEQ-1M1 holds  for n be NatNAT-1M1 holds  ex r be RealXREAL-0M1 st 0NUMBERSK6 <XXREAL-0R3 r & ( for m be NatNAT-1M1 holds m <=XXREAL-0R1 n implies |.COMPLEX1K10 seq .FUNCT-1K1 m.| <XXREAL-0R3 r)"
sorry

(*\$CD*)
abbreviation(input) SEQ_2V5("convergentSEQ-2V5" 70) where
  "convergentSEQ-2V5 \<equiv> convergentCOMSEQ-2V3"

mtheorem seq_2_def_6:
  mlet "seq be Real-SequenceSEQ-1M1"
"redefine attr convergentSEQ-2V5 for Real-SequenceSEQ-1M1 means
  (\<lambda>seq.  ex g be RealXREAL-0M1 st  for p be RealXREAL-0M1 holds 0NUMBERSK6 <XXREAL-0R3 p implies ( ex n be NatNAT-1M1 st  for m be NatNAT-1M1 holds n <=XXREAL-0R1 m implies |.COMPLEX1K10 seq .FUNCT-1K1 m -XCMPLX-0K6 g .| <XXREAL-0R3 p))"
proof
(*compatibility*)
  show " for seq be Real-SequenceSEQ-1M1 holds seq be convergentSEQ-2V5 iff ( ex g be RealXREAL-0M1 st  for p be RealXREAL-0M1 holds 0NUMBERSK6 <XXREAL-0R3 p implies ( ex n be NatNAT-1M1 st  for m be NatNAT-1M1 holds n <=XXREAL-0R1 m implies |.COMPLEX1K10 seq .FUNCT-1K1 m -XCMPLX-0K6 g .| <XXREAL-0R3 p))"
sorry
qed "sorry"

mdef seq_2_def_7 ("limSEQ-2K1  _ " [164]164 ) where
  mlet "seq be Real-SequenceSEQ-1M1"
"assume seq be convergentSEQ-2V5 func limSEQ-2K1 seq \<rightarrow> RealXREAL-0M1 means
  \<lambda>it.  for p be RealXREAL-0M1 holds 0NUMBERSK6 <XXREAL-0R3 p implies ( ex n be NatNAT-1M1 st  for m be NatNAT-1M1 holds n <=XXREAL-0R1 m implies |.COMPLEX1K10 seq .FUNCT-1K1 m -XCMPLX-0K6 it .| <XXREAL-0R3 p)"
proof-
  (*existence*)
    show "seq be convergentSEQ-2V5 implies ( ex it be RealXREAL-0M1 st  for p be RealXREAL-0M1 holds 0NUMBERSK6 <XXREAL-0R3 p implies ( ex n be NatNAT-1M1 st  for m be NatNAT-1M1 holds n <=XXREAL-0R1 m implies |.COMPLEX1K10 seq .FUNCT-1K1 m -XCMPLX-0K6 it .| <XXREAL-0R3 p))"
sorry
  (*uniqueness*)
    show "seq be convergentSEQ-2V5 implies ( for it1 be RealXREAL-0M1 holds  for it2 be RealXREAL-0M1 holds ( for p be RealXREAL-0M1 holds 0NUMBERSK6 <XXREAL-0R3 p implies ( ex n be NatNAT-1M1 st  for m be NatNAT-1M1 holds n <=XXREAL-0R1 m implies |.COMPLEX1K10 seq .FUNCT-1K1 m -XCMPLX-0K6 it1 .| <XXREAL-0R3 p)) & ( for p be RealXREAL-0M1 holds 0NUMBERSK6 <XXREAL-0R3 p implies ( ex n be NatNAT-1M1 st  for m be NatNAT-1M1 holds n <=XXREAL-0R1 m implies |.COMPLEX1K10 seq .FUNCT-1K1 m -XCMPLX-0K6 it2 .| <XXREAL-0R3 p)) implies it1 =HIDDENR1 it2)"
sorry
qed "sorry"

abbreviation(input) SEQ_2V6("boundedSEQ-2V6" 70) where
  "boundedSEQ-2V6 \<equiv> boundedCOMSEQ-2V1"

mtheorem seq_2_def_8:
  mlet "f be real-valuedVALUED-0V7\<bar>FunctionFUNCT-1M1"
"redefine attr boundedSEQ-2V6 for real-valuedVALUED-0V7\<bar>FunctionFUNCT-1M1 means
  (\<lambda>f. f be bounded-aboveSEQ-2V1\<bar>bounded-belowSEQ-2V2)"
proof
(*compatibility*)
  show " for f be real-valuedVALUED-0V7\<bar>FunctionFUNCT-1M1 holds f be boundedSEQ-2V6 iff f be bounded-aboveSEQ-2V1\<bar>bounded-belowSEQ-2V2"
sorry
qed "sorry"

mtheorem seq_2_cl_3:
"cluster constantVALUED-0V15 also-is convergentSEQ-2V5 for Real-SequenceSEQ-1M1"
proof
(*coherence*)
  show " for it be Real-SequenceSEQ-1M1 holds it be constantVALUED-0V15 implies it be convergentSEQ-2V5"
sorry
qed "sorry"

mtheorem seq_2_th_5:
" for seq be Real-SequenceSEQ-1M1 holds  for seq9 be Real-SequenceSEQ-1M1 holds seq be convergentSEQ-2V5 & seq9 be convergentSEQ-2V5 implies seq +VALUED-1K3\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq9 be convergentSEQ-2V5"
sorry

mtheorem seq_2_cl_4:
  mlet "seq1 be convergentSEQ-2V5\<bar>Real-SequenceSEQ-1M1", "seq2 be convergentSEQ-2V5\<bar>Real-SequenceSEQ-1M1"
"cluster seq1 +VALUED-1K3\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq2 as-term-is convergentSEQ-2V5 for Real-SequenceSEQ-1M1"
proof
(*coherence*)
  show " for it be Real-SequenceSEQ-1M1 holds it =HIDDENR1 seq1 +VALUED-1K3\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq2 implies it be convergentSEQ-2V5"
    using seq_2_th_5 sorry
qed "sorry"

mtheorem seq_2_th_6:
" for seq be Real-SequenceSEQ-1M1 holds  for seq9 be Real-SequenceSEQ-1M1 holds seq be convergentSEQ-2V5 & seq9 be convergentSEQ-2V5 implies limSEQ-2K1 (seq +VALUED-1K3\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq9) =COMPLEX1R1 limSEQ-2K1 seq +XCMPLX-0K2 limSEQ-2K1 seq9"
sorry

mtheorem seq_2_th_7:
" for r be RealXREAL-0M1 holds  for seq be Real-SequenceSEQ-1M1 holds seq be convergentSEQ-2V5 implies r (#)VALUED-1K28\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> seq be convergentSEQ-2V5"
sorry

mtheorem seq_2_cl_5:
  mlet "r be RealXREAL-0M1", "seq be convergentSEQ-2V5\<bar>Real-SequenceSEQ-1M1"
"cluster r (#)VALUED-1K28\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> seq as-term-is convergentSEQ-2V5 for Real-SequenceSEQ-1M1"
proof
(*coherence*)
  show " for it be Real-SequenceSEQ-1M1 holds it =HIDDENR1 r (#)VALUED-1K28\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> seq implies it be convergentSEQ-2V5"
    using seq_2_th_7 sorry
qed "sorry"

mtheorem seq_2_th_8:
" for r be RealXREAL-0M1 holds  for seq be Real-SequenceSEQ-1M1 holds seq be convergentSEQ-2V5 implies limSEQ-2K1 (r (#)VALUED-1K28\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> seq) =COMPLEX1R1 r *XCMPLX-0K3 (limSEQ-2K1 seq)"
sorry

mtheorem seq_2_th_9:
" for seq be Real-SequenceSEQ-1M1 holds seq be convergentSEQ-2V5 implies -VALUED-1K34\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> seq be convergentSEQ-2V5"
   sorry

mtheorem seq_2_cl_6:
  mlet "seq be convergentSEQ-2V5\<bar>Real-SequenceSEQ-1M1"
"cluster -VALUED-1K34\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> seq as-term-is convergentSEQ-2V5 for Real-SequenceSEQ-1M1"
proof
(*coherence*)
  show " for it be Real-SequenceSEQ-1M1 holds it =HIDDENR1 -VALUED-1K34\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> seq implies it be convergentSEQ-2V5"
     sorry
qed "sorry"

mtheorem seq_2_th_10:
" for seq be Real-SequenceSEQ-1M1 holds seq be convergentSEQ-2V5 implies limSEQ-2K1 (-VALUED-1K34\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> seq) =COMPLEX1R1 -XCMPLX-0K4 limSEQ-2K1 seq"
sorry

mtheorem seq_2_th_11:
" for seq be Real-SequenceSEQ-1M1 holds  for seq9 be Real-SequenceSEQ-1M1 holds seq be convergentSEQ-2V5 & seq9 be convergentSEQ-2V5 implies seq -VALUED-1K49\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq9 be convergentSEQ-2V5"
sorry

mtheorem seq_2_cl_7:
  mlet "seq1 be convergentSEQ-2V5\<bar>Real-SequenceSEQ-1M1", "seq2 be convergentSEQ-2V5\<bar>Real-SequenceSEQ-1M1"
"cluster seq1 -VALUED-1K49\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq2 as-term-is convergentSEQ-2V5 for Real-SequenceSEQ-1M1"
proof
(*coherence*)
  show " for it be Real-SequenceSEQ-1M1 holds it =HIDDENR1 seq1 -VALUED-1K49\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq2 implies it be convergentSEQ-2V5"
    using seq_2_th_11 sorry
qed "sorry"

mtheorem seq_2_th_12:
" for seq be Real-SequenceSEQ-1M1 holds  for seq9 be Real-SequenceSEQ-1M1 holds seq be convergentSEQ-2V5 & seq9 be convergentSEQ-2V5 implies limSEQ-2K1 (seq -VALUED-1K49\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq9) =COMPLEX1R1 limSEQ-2K1 seq -XCMPLX-0K6 limSEQ-2K1 seq9"
sorry

mtheorem seq_2_th_13:
" for seq be Real-SequenceSEQ-1M1 holds seq be convergentSEQ-2V5 implies seq be boundedSEQ-2V6"
sorry

mtheorem seq_2_cl_8:
"cluster convergentSEQ-2V5 also-is boundedSEQ-2V6 for Real-SequenceSEQ-1M1"
proof
(*coherence*)
  show " for it be Real-SequenceSEQ-1M1 holds it be convergentSEQ-2V5 implies it be boundedSEQ-2V6"
    using seq_2_th_13 sorry
qed "sorry"

mtheorem seq_2_th_14:
" for seq be Real-SequenceSEQ-1M1 holds  for seq9 be Real-SequenceSEQ-1M1 holds seq be convergentSEQ-2V5 & seq9 be convergentSEQ-2V5 implies seq (#)VALUED-1K21\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq9 be convergentSEQ-2V5"
sorry

mtheorem seq_2_cl_9:
  mlet "seq1 be convergentSEQ-2V5\<bar>Real-SequenceSEQ-1M1", "seq2 be convergentSEQ-2V5\<bar>Real-SequenceSEQ-1M1"
"cluster seq1 (#)VALUED-1K21\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq2 as-term-is convergentSEQ-2V5 for Real-SequenceSEQ-1M1"
proof
(*coherence*)
  show " for it be Real-SequenceSEQ-1M1 holds it =HIDDENR1 seq1 (#)VALUED-1K21\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq2 implies it be convergentSEQ-2V5"
    using seq_2_th_14 sorry
qed "sorry"

mtheorem seq_2_th_15:
" for seq be Real-SequenceSEQ-1M1 holds  for seq9 be Real-SequenceSEQ-1M1 holds seq be convergentSEQ-2V5 & seq9 be convergentSEQ-2V5 implies limSEQ-2K1 (seq (#)VALUED-1K21\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq9) =COMPLEX1R1 (limSEQ-2K1 seq)*XCMPLX-0K3 (limSEQ-2K1 seq9)"
sorry

mtheorem seq_2_th_16:
" for seq be Real-SequenceSEQ-1M1 holds seq be convergentSEQ-2V5 implies (limSEQ-2K1 seq <>HIDDENR2 0NUMBERSK6 implies ( ex n be NatNAT-1M1 st  for m be NatNAT-1M1 holds n <=XXREAL-0R1 m implies (|.COMPLEX1K10 limSEQ-2K1 seq .|)/XCMPLX-0K7 \<two>\<^sub>M <XXREAL-0R3 |.COMPLEX1K10 seq .FUNCT-1K1 m.|))"
sorry

mtheorem seq_2_th_17:
" for seq be Real-SequenceSEQ-1M1 holds seq be convergentSEQ-2V5 & ( for n be NatNAT-1M1 holds 0NUMBERSK6 <=XXREAL-0R1 seq .FUNCT-1K1 n) implies 0NUMBERSK6 <=XXREAL-0R1 limSEQ-2K1 seq"
sorry

mtheorem seq_2_th_18:
" for seq be Real-SequenceSEQ-1M1 holds  for seq9 be Real-SequenceSEQ-1M1 holds (seq be convergentSEQ-2V5 & seq9 be convergentSEQ-2V5) & ( for n be NatNAT-1M1 holds seq .FUNCT-1K1 n <=XXREAL-0R1 seq9 .FUNCT-1K1 n) implies limSEQ-2K1 seq <=XXREAL-0R1 limSEQ-2K1 seq9"
sorry

mtheorem seq_2_th_19:
" for seq be Real-SequenceSEQ-1M1 holds  for seq9 be Real-SequenceSEQ-1M1 holds  for seq1 be Real-SequenceSEQ-1M1 holds ((seq be convergentSEQ-2V5 & seq9 be convergentSEQ-2V5) & ( for n be NatNAT-1M1 holds seq .FUNCT-1K1 n <=XXREAL-0R1 seq1 .FUNCT-1K1 n & seq1 .FUNCT-1K1 n <=XXREAL-0R1 seq9 .FUNCT-1K1 n)) & limSEQ-2K1 seq =COMPLEX1R1 limSEQ-2K1 seq9 implies seq1 be convergentSEQ-2V5"
sorry

mtheorem seq_2_th_20:
" for seq be Real-SequenceSEQ-1M1 holds  for seq9 be Real-SequenceSEQ-1M1 holds  for seq1 be Real-SequenceSEQ-1M1 holds ((seq be convergentSEQ-2V5 & seq9 be convergentSEQ-2V5) & ( for n be NatNAT-1M1 holds seq .FUNCT-1K1 n <=XXREAL-0R1 seq1 .FUNCT-1K1 n & seq1 .FUNCT-1K1 n <=XXREAL-0R1 seq9 .FUNCT-1K1 n)) & limSEQ-2K1 seq =COMPLEX1R1 limSEQ-2K1 seq9 implies limSEQ-2K1 seq1 =COMPLEX1R1 limSEQ-2K1 seq"
sorry

mtheorem seq_2_th_21:
" for seq be Real-SequenceSEQ-1M1 holds (seq be convergentSEQ-2V5 & limSEQ-2K1 seq <>HIDDENR2 0NUMBERSK6) & seq be non-zeroORDINAL1V9 implies seq \<inverse>VALUED-1K39\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> be convergentSEQ-2V5"
sorry

mtheorem seq_2_th_22:
" for seq be Real-SequenceSEQ-1M1 holds (seq be convergentSEQ-2V5 & limSEQ-2K1 seq <>HIDDENR2 0NUMBERSK6) & seq be non-zeroORDINAL1V9 implies limSEQ-2K1 seq \<inverse>VALUED-1K39\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> =COMPLEX1R1 (limSEQ-2K1 seq)\<inverse>XCMPLX-0K5"
sorry

mtheorem seq_2_th_23:
" for seq be Real-SequenceSEQ-1M1 holds  for seq9 be Real-SequenceSEQ-1M1 holds ((seq9 be convergentSEQ-2V5 & seq be convergentSEQ-2V5) & limSEQ-2K1 seq <>HIDDENR2 0NUMBERSK6) & seq be non-zeroORDINAL1V9 implies seq9 /\<inverse>VALUED-1K54\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq be convergentSEQ-2V5"
sorry

mtheorem seq_2_th_24:
" for seq be Real-SequenceSEQ-1M1 holds  for seq9 be Real-SequenceSEQ-1M1 holds ((seq9 be convergentSEQ-2V5 & seq be convergentSEQ-2V5) & limSEQ-2K1 seq <>HIDDENR2 0NUMBERSK6) & seq be non-zeroORDINAL1V9 implies limSEQ-2K1 (seq9 /\<inverse>VALUED-1K54\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq) =COMPLEX1R1 (limSEQ-2K1 seq9)/XCMPLX-0K7 (limSEQ-2K1 seq)"
sorry

mtheorem seq_2_th_25:
" for seq be Real-SequenceSEQ-1M1 holds  for seq1 be Real-SequenceSEQ-1M1 holds (seq be convergentSEQ-2V5 & seq1 be boundedSEQ-2V6) & limSEQ-2K1 seq =COMPLEX1R1 0NUMBERSK6 implies seq (#)VALUED-1K21\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq1 be convergentSEQ-2V5"
sorry

mtheorem seq_2_th_26:
" for seq be Real-SequenceSEQ-1M1 holds  for seq1 be Real-SequenceSEQ-1M1 holds (seq be convergentSEQ-2V5 & seq1 be boundedSEQ-2V6) & limSEQ-2K1 seq =COMPLEX1R1 0NUMBERSK6 implies limSEQ-2K1 (seq (#)VALUED-1K21\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> seq1) =COMPLEX1R1 0NUMBERSK6"
sorry

reserve g for "ComplexXCMPLX-0M1"
mtheorem seq_2_cl_10:
  mlet "s be convergentCOMSEQ-2V3\<bar>Complex-SequenceCOMSEQ-1M1"
"cluster |.VALUED-1K58\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> s.| as-term-is convergentSEQ-2V5 for Real-SequenceSEQ-1M1"
proof
(*coherence*)
  show " for it be Real-SequenceSEQ-1M1 holds it =HIDDENR1 |.VALUED-1K58\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> s.| implies it be convergentSEQ-2V5"
sorry
qed "sorry"

reserve s, s1, s9 for "Complex-SequenceCOMSEQ-1M1"
mtheorem seq_2_th_27:
" for s be Complex-SequenceCOMSEQ-1M1 holds s be convergentCOMSEQ-2V3 implies limSEQ-2K1 (|.VALUED-1K58\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> s.|) =COMPLEX1R1 |.COMPLEX1K10 limCOMSEQ-2K3 s .|"
sorry

mtheorem seq_2_th_28:
" for s be convergentCOMSEQ-2V3\<bar>Complex-SequenceCOMSEQ-1M1 holds  for s9 be convergentCOMSEQ-2V3\<bar>Complex-SequenceCOMSEQ-1M1 holds limSEQ-2K1 (|.VALUED-1K58\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> s +VALUED-1K2\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> s9 .|) =COMPLEX1R1 |.COMPLEX1K10 limCOMSEQ-2K3 s +XCMPLX-0K2 limCOMSEQ-2K3 s9 .|"
sorry

mtheorem seq_2_th_29:
" for r be RealXREAL-0M1 holds  for s be convergentCOMSEQ-2V3\<bar>Complex-SequenceCOMSEQ-1M1 holds limSEQ-2K1 (|.VALUED-1K58\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> r (#)VALUED-1K27\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> s .|) =COMPLEX1R1 (|.COMPLEX1K10 r.|)*XCMPLX-0K3 (|.COMPLEX1K10 limCOMSEQ-2K3 s .|)"
sorry

mtheorem seq_2_th_30:
" for s be convergentCOMSEQ-2V3\<bar>Complex-SequenceCOMSEQ-1M1 holds limSEQ-2K1 (|.VALUED-1K58\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> -VALUED-1K33\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> s .|) =COMPLEX1R1 |.COMPLEX1K10 limCOMSEQ-2K3 s .|"
sorry

mtheorem seq_2_th_31:
" for s be convergentCOMSEQ-2V3\<bar>Complex-SequenceCOMSEQ-1M1 holds  for s9 be convergentCOMSEQ-2V3\<bar>Complex-SequenceCOMSEQ-1M1 holds limSEQ-2K1 (|.VALUED-1K58\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> s -VALUED-1K48\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> s9 .|) =COMPLEX1R1 |.COMPLEX1K10 limCOMSEQ-2K3 s -XCMPLX-0K6 limCOMSEQ-2K3 s9 .|"
sorry

mtheorem seq_2_th_32:
" for s be convergentCOMSEQ-2V3\<bar>Complex-SequenceCOMSEQ-1M1 holds  for s9 be convergentCOMSEQ-2V3\<bar>Complex-SequenceCOMSEQ-1M1 holds limSEQ-2K1 (|.VALUED-1K58\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> s (#)VALUED-1K20\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> s9 .|) =COMPLEX1R1 (|.COMPLEX1K10 limCOMSEQ-2K3 s .|)*XCMPLX-0K3 (|.COMPLEX1K10 limCOMSEQ-2K3 s9 .|)"
sorry

mtheorem seq_2_th_33:
" for s be Complex-SequenceCOMSEQ-1M1 holds (s be convergentCOMSEQ-2V3 & limCOMSEQ-2K3 s <>HIDDENR2 0cCOMPLEX1K6) & s be non-zeroORDINAL1V9 implies limSEQ-2K1 (|.VALUED-1K58\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> s \<inverse>VALUED-1K38\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub>.|) =COMPLEX1R1 (|.COMPLEX1K10 limCOMSEQ-2K3 s .|)\<inverse>XCMPLX-0K5"
sorry

mtheorem seq_2_th_34:
" for s be Complex-SequenceCOMSEQ-1M1 holds  for s9 be Complex-SequenceCOMSEQ-1M1 holds ((s9 be convergentCOMSEQ-2V3 & s be convergentCOMSEQ-2V3) & limCOMSEQ-2K3 s <>HIDDENR2 0cCOMPLEX1K6) & s be non-zeroORDINAL1V9 implies limSEQ-2K1 (|.VALUED-1K58\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> s9 /\<inverse>VALUED-1K53\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> s .|) =COMPLEX1R1 (|.COMPLEX1K10 limCOMSEQ-2K3 s9 .|)/XCMPLX-0K7 (|.COMPLEX1K10 limCOMSEQ-2K3 s .|)"
sorry

mtheorem seq_2_th_35:
" for s be Complex-SequenceCOMSEQ-1M1 holds  for s1 be Complex-SequenceCOMSEQ-1M1 holds (s be convergentCOMSEQ-2V3 & s1 be boundedCOMSEQ-2V2) & limCOMSEQ-2K3 s =COMPLEX1R1 0cCOMPLEX1K6 implies limSEQ-2K1 (|.VALUED-1K58\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> s (#)VALUED-1K20\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> s1 .|) =COMPLEX1R1 0NUMBERSK6"
sorry

end
