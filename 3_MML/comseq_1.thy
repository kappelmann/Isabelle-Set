theory comseq_1
  imports valued_1 xcmplx_1
   "../mizar_extension/E_number"
begin
(*begin*)
reserve f for "FunctionFUNCT-1M1"
reserve n, k, n1 for "ElementSUBSET-1M1-of NATNUMBERSK1"
reserve r, p for "ComplexXCMPLX-0M1"
reserve x, y for "setHIDDENM2"
syntax COMSEQ_1M1 :: "Ty" ("Complex-SequenceCOMSEQ-1M1" 70)
translations "Complex-SequenceCOMSEQ-1M1" \<rightharpoonup> "sequenceNAT-1M2-of COMPLEXNUMBERSK3"

reserve seq, seq1, seq2, seq3, seq9, seq19 for "Complex-SequenceCOMSEQ-1M1"
mtheorem comseq_1_th_1:
" for f be FunctionFUNCT-1M1 holds f be Complex-SequenceCOMSEQ-1M1 iff domRELAT-1K1 f =XBOOLE-0R4 NATNUMBERSK1 & ( for x be setHIDDENM2 holds x inTARSKIR2 NATNUMBERSK1 implies f .FUNCT-1K1 x be ElementSUBSET-1M1-of COMPLEXNUMBERSK3)"
sorry

mtheorem comseq_1_th_2:
" for f be FunctionFUNCT-1M1 holds f be Complex-SequenceCOMSEQ-1M1 iff domRELAT-1K1 f =XBOOLE-0R4 NATNUMBERSK1 & ( for n be ElementSUBSET-1M1-of NATNUMBERSK1 holds f .FUNCT-1K1 n be ElementSUBSET-1M1-of COMPLEXNUMBERSK3)"
sorry

theorem comseq_1_sch_1:
  fixes Ff1 
  assumes
[ty_func]: "\<And> x1. x1 be setHIDDENM2 \<Longrightarrow> Ff1(x1) be ComplexXCMPLX-0M1"
  shows " ex seq be Complex-SequenceCOMSEQ-1M1 st  for n be NatNAT-1M1 holds seq .NAT-1K8\<^bsub>(COMPLEXNUMBERSK3)\<^esub> n =COMPLEX1R1 Ff1(n)"
sorry

mtheorem comseq_1_cl_1:
"cluster non-zeroORDINAL1V9 for Complex-SequenceCOMSEQ-1M1"
proof
(*existence*)
  show " ex it be Complex-SequenceCOMSEQ-1M1 st it be non-zeroORDINAL1V9"
sorry
qed "sorry"

mtheorem comseq_1_th_3:
" for seq be Complex-SequenceCOMSEQ-1M1 holds seq be non-zeroORDINAL1V9 iff ( for x be setHIDDENM2 holds x inTARSKIR2 NATNUMBERSK1 implies seq .FUNCT-1K1 x <>HIDDENR2 0cCOMPLEX1K6)"
sorry

mtheorem comseq_1_th_4:
" for seq be Complex-SequenceCOMSEQ-1M1 holds seq be non-zeroORDINAL1V9 iff ( for n be ElementSUBSET-1M1-of NATNUMBERSK1 holds seq .NAT-1K8\<^bsub>(COMPLEXNUMBERSK3)\<^esub> n <>HIDDENR2 0cCOMPLEX1K6)"
sorry

mtheorem comseq_1_th_5:
" for IT be non-zeroORDINAL1V9\<bar>Complex-SequenceCOMSEQ-1M1 holds rngRELSET-1K2\<^bsub>(COMPLEXNUMBERSK3)\<^esub> IT c=TARSKIR1 COMPLEXNUMBERSK3 \\SUBSET-1K6 {TARSKIK1 0cCOMPLEX1K6 }"
  using ordinal1_def_15 zfmisc_1_th_34 sorry

mtheorem comseq_1_th_6:
" for r be ComplexXCMPLX-0M1 holds  ex seq be Complex-SequenceCOMSEQ-1M1 st rngRELSET-1K2\<^bsub>(COMPLEXNUMBERSK3)\<^esub> seq =XBOOLE-0R4 {TARSKIK1 r}"
sorry

mtheorem comseq_1_th_7:
" for seq1 be Complex-SequenceCOMSEQ-1M1 holds  for seq2 be Complex-SequenceCOMSEQ-1M1 holds  for seq3 be Complex-SequenceCOMSEQ-1M1 holds (seq1 +VALUED-1K2\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq2)+VALUED-1K2\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq3 =RELSET-1R2\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> seq1 +VALUED-1K2\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> (seq2 +VALUED-1K2\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq3)"
sorry

mtheorem comseq_1_th_8:
" for seq1 be Complex-SequenceCOMSEQ-1M1 holds  for seq2 be Complex-SequenceCOMSEQ-1M1 holds  for seq3 be Complex-SequenceCOMSEQ-1M1 holds (seq1 (#)VALUED-1K20\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq2)(#)VALUED-1K20\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq3 =RELSET-1R2\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> seq1 (#)VALUED-1K20\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> (seq2 (#)VALUED-1K20\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq3)"
sorry

mtheorem comseq_1_th_9:
" for seq1 be Complex-SequenceCOMSEQ-1M1 holds  for seq2 be Complex-SequenceCOMSEQ-1M1 holds  for seq3 be Complex-SequenceCOMSEQ-1M1 holds (seq1 +VALUED-1K2\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq2)(#)VALUED-1K20\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq3 =RELSET-1R2\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> seq1 (#)VALUED-1K20\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq3 +VALUED-1K2\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq2 (#)VALUED-1K20\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq3"
sorry

mtheorem comseq_1_th_10:
" for seq1 be Complex-SequenceCOMSEQ-1M1 holds  for seq2 be Complex-SequenceCOMSEQ-1M1 holds  for seq3 be Complex-SequenceCOMSEQ-1M1 holds seq3 (#)VALUED-1K20\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> (seq1 +VALUED-1K2\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq2) =RELSET-1R2\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> seq3 (#)VALUED-1K20\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq1 +VALUED-1K2\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq3 (#)VALUED-1K20\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq2"
  using comseq_1_th_9 sorry

mtheorem comseq_1_th_11:
" for seq be Complex-SequenceCOMSEQ-1M1 holds -VALUED-1K33\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> seq =RELSET-1R2\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> (-XCMPLX-0K4 1rCOMPLEX1K7)(#)VALUED-1K27\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> seq"
   sorry

mtheorem comseq_1_th_12:
" for r be ComplexXCMPLX-0M1 holds  for seq1 be Complex-SequenceCOMSEQ-1M1 holds  for seq2 be Complex-SequenceCOMSEQ-1M1 holds r (#)VALUED-1K27\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> (seq1 (#)VALUED-1K20\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq2) =RELSET-1R2\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> (r (#)VALUED-1K27\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> seq1)(#)VALUED-1K20\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq2"
sorry

mtheorem comseq_1_th_13:
" for r be ComplexXCMPLX-0M1 holds  for seq1 be Complex-SequenceCOMSEQ-1M1 holds  for seq2 be Complex-SequenceCOMSEQ-1M1 holds r (#)VALUED-1K27\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> (seq1 (#)VALUED-1K20\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq2) =RELSET-1R2\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> seq1 (#)VALUED-1K20\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> (r (#)VALUED-1K27\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> seq2)"
sorry

mtheorem comseq_1_th_14:
" for seq1 be Complex-SequenceCOMSEQ-1M1 holds  for seq2 be Complex-SequenceCOMSEQ-1M1 holds  for seq3 be Complex-SequenceCOMSEQ-1M1 holds (seq1 -VALUED-1K48\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq2)(#)VALUED-1K20\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq3 =RELSET-1R2\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> seq1 (#)VALUED-1K20\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq3 -VALUED-1K48\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq2 (#)VALUED-1K20\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq3"
sorry

mtheorem comseq_1_th_15:
" for seq1 be Complex-SequenceCOMSEQ-1M1 holds  for seq2 be Complex-SequenceCOMSEQ-1M1 holds  for seq3 be Complex-SequenceCOMSEQ-1M1 holds seq3 (#)VALUED-1K20\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq1 -VALUED-1K48\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq3 (#)VALUED-1K20\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq2 =RELSET-1R2\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> seq3 (#)VALUED-1K20\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> (seq1 -VALUED-1K48\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq2)"
  using comseq_1_th_14 sorry

mtheorem comseq_1_th_16:
" for r be ComplexXCMPLX-0M1 holds  for seq1 be Complex-SequenceCOMSEQ-1M1 holds  for seq2 be Complex-SequenceCOMSEQ-1M1 holds r (#)VALUED-1K27\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> (seq1 +VALUED-1K2\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq2) =RELSET-1R2\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> r (#)VALUED-1K27\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> seq1 +VALUED-1K2\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> r (#)VALUED-1K27\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> seq2"
sorry

mtheorem comseq_1_th_17:
" for r be ComplexXCMPLX-0M1 holds  for p be ComplexXCMPLX-0M1 holds  for seq be Complex-SequenceCOMSEQ-1M1 holds (r *XCMPLX-0K3 p)(#)VALUED-1K27\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> seq =RELSET-1R2\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> r (#)VALUED-1K27\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> (p (#)VALUED-1K27\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> seq)"
sorry

mtheorem comseq_1_th_18:
" for r be ComplexXCMPLX-0M1 holds  for seq1 be Complex-SequenceCOMSEQ-1M1 holds  for seq2 be Complex-SequenceCOMSEQ-1M1 holds r (#)VALUED-1K27\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> (seq1 -VALUED-1K48\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq2) =RELSET-1R2\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> r (#)VALUED-1K27\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> seq1 -VALUED-1K48\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> r (#)VALUED-1K27\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> seq2"
sorry

mtheorem comseq_1_th_19:
" for r be ComplexXCMPLX-0M1 holds  for seq be Complex-SequenceCOMSEQ-1M1 holds  for seq1 be Complex-SequenceCOMSEQ-1M1 holds r (#)VALUED-1K27\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> (seq1 /\<inverse>VALUED-1K53\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq) =RELSET-1R2\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> (r (#)VALUED-1K27\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> seq1)/\<inverse>VALUED-1K53\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq"
sorry

mtheorem comseq_1_th_20:
" for seq1 be Complex-SequenceCOMSEQ-1M1 holds  for seq2 be Complex-SequenceCOMSEQ-1M1 holds  for seq3 be Complex-SequenceCOMSEQ-1M1 holds seq1 -VALUED-1K48\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> (seq2 +VALUED-1K2\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq3) =RELSET-1R2\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> (seq1 -VALUED-1K48\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq2)-VALUED-1K48\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq3"
sorry

mtheorem comseq_1_th_21:
" for seq be Complex-SequenceCOMSEQ-1M1 holds 1rCOMPLEX1K7 (#)VALUED-1K27\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> seq =RELSET-1R2\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> seq"
sorry

mtheorem comseq_1_th_22:
" for seq be Complex-SequenceCOMSEQ-1M1 holds -VALUED-1K33\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> (-VALUED-1K33\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> seq) =RELSET-1R2\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> seq"
   sorry

mtheorem comseq_1_th_23:
" for seq1 be Complex-SequenceCOMSEQ-1M1 holds  for seq2 be Complex-SequenceCOMSEQ-1M1 holds seq1 -VALUED-1K48\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> (-VALUED-1K33\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> seq2) =RELSET-1R2\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> seq1 +VALUED-1K2\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq2"
   sorry

mtheorem comseq_1_th_24:
" for seq1 be Complex-SequenceCOMSEQ-1M1 holds  for seq2 be Complex-SequenceCOMSEQ-1M1 holds  for seq3 be Complex-SequenceCOMSEQ-1M1 holds seq1 -VALUED-1K48\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> (seq2 -VALUED-1K48\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq3) =RELSET-1R2\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> (seq1 -VALUED-1K48\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq2)+VALUED-1K2\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq3"
sorry

mtheorem comseq_1_th_25:
" for seq1 be Complex-SequenceCOMSEQ-1M1 holds  for seq2 be Complex-SequenceCOMSEQ-1M1 holds  for seq3 be Complex-SequenceCOMSEQ-1M1 holds seq1 +VALUED-1K2\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> (seq2 -VALUED-1K48\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq3) =RELSET-1R2\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> (seq1 +VALUED-1K2\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq2)-VALUED-1K48\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq3"
sorry

mtheorem comseq_1_th_26:
" for seq1 be Complex-SequenceCOMSEQ-1M1 holds  for seq2 be Complex-SequenceCOMSEQ-1M1 holds (-VALUED-1K33\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> seq1)(#)VALUED-1K20\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq2 =RELSET-1R2\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> -VALUED-1K33\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> seq1 (#)VALUED-1K20\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq2 & seq1 (#)VALUED-1K20\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> (-VALUED-1K33\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> seq2) =RELSET-1R2\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> -VALUED-1K33\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> seq1 (#)VALUED-1K20\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq2"
  using comseq_1_th_12 sorry

mtheorem comseq_1_th_27:
" for seq be Complex-SequenceCOMSEQ-1M1 holds seq be non-zeroORDINAL1V9 implies seq \<inverse>VALUED-1K38\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> be non-zeroORDINAL1V9"
sorry

(*\$CT*)
mtheorem comseq_1_th_29:
" for seq be Complex-SequenceCOMSEQ-1M1 holds  for seq1 be Complex-SequenceCOMSEQ-1M1 holds seq be non-zeroORDINAL1V9 & seq1 be non-zeroORDINAL1V9 iff seq (#)VALUED-1K20\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq1 be non-zeroORDINAL1V9"
sorry

mtheorem comseq_1_th_30:
" for seq be Complex-SequenceCOMSEQ-1M1 holds  for seq1 be Complex-SequenceCOMSEQ-1M1 holds seq \<inverse>VALUED-1K38\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> (#)VALUED-1K20\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq1 \<inverse>VALUED-1K38\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> =RELSET-1R2\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> (seq (#)VALUED-1K20\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq1)\<inverse>VALUED-1K38\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub>"
sorry

mtheorem comseq_1_th_31:
" for seq be Complex-SequenceCOMSEQ-1M1 holds  for seq1 be Complex-SequenceCOMSEQ-1M1 holds seq be non-zeroORDINAL1V9 implies (seq1 /\<inverse>VALUED-1K53\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq)(#)VALUED-1K20\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq =RELSET-1R2\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> seq1"
sorry

mtheorem comseq_1_th_32:
" for seq be Complex-SequenceCOMSEQ-1M1 holds  for seq1 be Complex-SequenceCOMSEQ-1M1 holds  for seq9 be Complex-SequenceCOMSEQ-1M1 holds  for seq19 be Complex-SequenceCOMSEQ-1M1 holds (seq9 /\<inverse>VALUED-1K53\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq)(#)VALUED-1K20\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> (seq19 /\<inverse>VALUED-1K53\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq1) =RELSET-1R2\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> (seq9 (#)VALUED-1K20\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq19)/\<inverse>VALUED-1K53\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> (seq (#)VALUED-1K20\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq1)"
sorry

mtheorem comseq_1_th_33:
" for seq be Complex-SequenceCOMSEQ-1M1 holds  for seq1 be Complex-SequenceCOMSEQ-1M1 holds seq be non-zeroORDINAL1V9 & seq1 be non-zeroORDINAL1V9 implies seq /\<inverse>VALUED-1K53\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq1 be non-zeroORDINAL1V9"
sorry

mtheorem comseq_1_th_34:
" for seq be Complex-SequenceCOMSEQ-1M1 holds  for seq1 be Complex-SequenceCOMSEQ-1M1 holds (seq /\<inverse>VALUED-1K53\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq1)\<inverse>VALUED-1K38\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> =RELSET-1R2\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> seq1 /\<inverse>VALUED-1K53\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq"
sorry

mtheorem comseq_1_th_35:
" for seq be Complex-SequenceCOMSEQ-1M1 holds  for seq1 be Complex-SequenceCOMSEQ-1M1 holds  for seq2 be Complex-SequenceCOMSEQ-1M1 holds seq2 (#)VALUED-1K20\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> (seq1 /\<inverse>VALUED-1K53\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq) =RELSET-1R2\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> (seq2 (#)VALUED-1K20\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq1)/\<inverse>VALUED-1K53\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq"
sorry

mtheorem comseq_1_th_36:
" for seq be Complex-SequenceCOMSEQ-1M1 holds  for seq1 be Complex-SequenceCOMSEQ-1M1 holds  for seq2 be Complex-SequenceCOMSEQ-1M1 holds seq2 /\<inverse>VALUED-1K53\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> (seq /\<inverse>VALUED-1K53\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq1) =RELSET-1R2\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> (seq2 (#)VALUED-1K20\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq1)/\<inverse>VALUED-1K53\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq"
sorry

mtheorem comseq_1_th_37:
" for seq be Complex-SequenceCOMSEQ-1M1 holds  for seq1 be Complex-SequenceCOMSEQ-1M1 holds  for seq2 be Complex-SequenceCOMSEQ-1M1 holds seq1 be non-zeroORDINAL1V9 implies seq2 /\<inverse>VALUED-1K53\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq =RELSET-1R2\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> (seq2 (#)VALUED-1K20\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq1)/\<inverse>VALUED-1K53\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> (seq (#)VALUED-1K20\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq1)"
sorry

mtheorem comseq_1_th_38:
" for r be ComplexXCMPLX-0M1 holds  for seq be Complex-SequenceCOMSEQ-1M1 holds r <>HIDDENR2 0cCOMPLEX1K6 & seq be non-zeroORDINAL1V9 implies r (#)VALUED-1K27\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> seq be non-zeroORDINAL1V9"
sorry

mtheorem comseq_1_th_39:
" for seq be Complex-SequenceCOMSEQ-1M1 holds seq be non-zeroORDINAL1V9 implies -VALUED-1K33\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> seq be non-zeroORDINAL1V9"
  using comseq_1_th_38 sorry

mtheorem comseq_1_th_40:
" for r be ComplexXCMPLX-0M1 holds  for seq be Complex-SequenceCOMSEQ-1M1 holds (r (#)VALUED-1K27\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> seq)\<inverse>VALUED-1K38\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> =RELSET-1R2\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> r \<inverse>XCMPLX-0K5 (#)VALUED-1K27\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> seq \<inverse>VALUED-1K38\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub>"
sorry

mtheorem comseq_1_th_41:
" for seq be Complex-SequenceCOMSEQ-1M1 holds seq be non-zeroORDINAL1V9 implies (-VALUED-1K33\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> seq)\<inverse>VALUED-1K38\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> =RELSET-1R2\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> (-XCMPLX-0K4 1rCOMPLEX1K7)(#)VALUED-1K27\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> seq \<inverse>VALUED-1K38\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub>"
sorry

mtheorem comseq_1_th_42:
" for seq be Complex-SequenceCOMSEQ-1M1 holds  for seq1 be Complex-SequenceCOMSEQ-1M1 holds seq be non-zeroORDINAL1V9 implies -VALUED-1K33\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> seq1 /\<inverse>VALUED-1K53\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq =RELSET-1R2\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> (-VALUED-1K33\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> seq1)/\<inverse>VALUED-1K53\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq & seq1 /\<inverse>VALUED-1K53\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> (-VALUED-1K33\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> seq) =RELSET-1R2\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> -VALUED-1K33\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> seq1 /\<inverse>VALUED-1K53\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq"
sorry

mtheorem comseq_1_th_43:
" for seq be Complex-SequenceCOMSEQ-1M1 holds  for seq1 be Complex-SequenceCOMSEQ-1M1 holds  for seq19 be Complex-SequenceCOMSEQ-1M1 holds seq1 /\<inverse>VALUED-1K53\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq +VALUED-1K2\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq19 /\<inverse>VALUED-1K53\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq =RELSET-1R2\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> (seq1 +VALUED-1K2\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq19)/\<inverse>VALUED-1K53\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq & seq1 /\<inverse>VALUED-1K53\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq -VALUED-1K48\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq19 /\<inverse>VALUED-1K53\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq =RELSET-1R2\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> (seq1 -VALUED-1K48\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq19)/\<inverse>VALUED-1K53\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq"
sorry

mtheorem comseq_1_th_44:
" for seq be Complex-SequenceCOMSEQ-1M1 holds  for seq1 be Complex-SequenceCOMSEQ-1M1 holds  for seq9 be Complex-SequenceCOMSEQ-1M1 holds  for seq19 be Complex-SequenceCOMSEQ-1M1 holds seq be non-zeroORDINAL1V9 & seq9 be non-zeroORDINAL1V9 implies seq1 /\<inverse>VALUED-1K53\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq +VALUED-1K2\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq19 /\<inverse>VALUED-1K53\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq9 =RELSET-1R2\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> (seq1 (#)VALUED-1K20\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq9 +VALUED-1K2\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq19 (#)VALUED-1K20\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq)/\<inverse>VALUED-1K53\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> (seq (#)VALUED-1K20\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq9) & seq1 /\<inverse>VALUED-1K53\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq -VALUED-1K48\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq19 /\<inverse>VALUED-1K53\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq9 =RELSET-1R2\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> (seq1 (#)VALUED-1K20\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq9 -VALUED-1K48\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq19 (#)VALUED-1K20\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq)/\<inverse>VALUED-1K53\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> (seq (#)VALUED-1K20\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq9)"
sorry

mtheorem comseq_1_th_45:
" for seq be Complex-SequenceCOMSEQ-1M1 holds  for seq1 be Complex-SequenceCOMSEQ-1M1 holds  for seq9 be Complex-SequenceCOMSEQ-1M1 holds  for seq19 be Complex-SequenceCOMSEQ-1M1 holds (seq19 /\<inverse>VALUED-1K53\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq)/\<inverse>VALUED-1K53\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> (seq9 /\<inverse>VALUED-1K53\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq1) =RELSET-1R2\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> (seq19 (#)VALUED-1K20\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq1)/\<inverse>VALUED-1K53\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> (seq (#)VALUED-1K20\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq9)"
sorry

mtheorem comseq_1_th_46:
" for seq be Complex-SequenceCOMSEQ-1M1 holds  for seq9 be Complex-SequenceCOMSEQ-1M1 holds |.VALUED-1K58\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> seq (#)VALUED-1K20\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq9 .| =RELSET-1R2\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> (|.VALUED-1K58\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> seq.|)(#)VALUED-1K21\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> (|.VALUED-1K58\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> seq9.|)"
sorry

(*\$CT*)
mtheorem comseq_1_th_48:
" for seq be Complex-SequenceCOMSEQ-1M1 holds (|.VALUED-1K58\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> seq.|)\<inverse>VALUED-1K39\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> =RELSET-1R2\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> |.VALUED-1K58\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> seq \<inverse>VALUED-1K38\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub>.|"
sorry

mtheorem comseq_1_th_49:
" for seq be Complex-SequenceCOMSEQ-1M1 holds  for seq9 be Complex-SequenceCOMSEQ-1M1 holds |.VALUED-1K58\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> seq9 /\<inverse>VALUED-1K53\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> seq .| =RELSET-1R2\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> (|.VALUED-1K58\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> seq9.|)/\<inverse>VALUED-1K54\<^bsub>(NATNUMBERSK1,REALNUMBERSK2,REALNUMBERSK2)\<^esub> (|.VALUED-1K58\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> seq.|)"
sorry

mtheorem comseq_1_th_50:
" for r be ComplexXCMPLX-0M1 holds  for seq be Complex-SequenceCOMSEQ-1M1 holds |.VALUED-1K58\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> r (#)VALUED-1K27\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> seq .| =RELSET-1R2\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> (|.COMPLEX1K10 r.|)(#)VALUED-1K28\<^bsub>(NATNUMBERSK1,REALNUMBERSK2)\<^esub> (|.VALUED-1K58\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> seq.|)"
sorry

end
