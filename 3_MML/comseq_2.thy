theory comseq_2
  imports pboole comseq_1 square_1
   "../mizar_extension/E_number"
begin
(*begin*)
reserve n, n1, n2, m for "NatNAT-1M1"
reserve r, g1, g2, g, g9 for "ComplexXCMPLX-0M1"
reserve R, R2 for "RealXREAL-0M1"
reserve s, s9, s1 for "Complex-SequenceCOMSEQ-1M1"
mtheorem comseq_2_th_1:
" for r be ComplexXCMPLX-0M1 holds  for g be ComplexXCMPLX-0M1 holds g <>HIDDENR2 0cCOMPLEX1K6 & r <>HIDDENR2 0cCOMPLEX1K6 implies |.COMPLEX1K10 g \<inverse>XCMPLX-0K5 -XCMPLX-0K6 r \<inverse>XCMPLX-0K5 .| =COMPLEX1R1 (|.COMPLEX1K10 g -XCMPLX-0K6 r .|)/XCMPLX-0K7 ((|.COMPLEX1K10 g.|)*XCMPLX-0K3 (|.COMPLEX1K10 r.|))"
sorry

mtheorem comseq_2_th_2:
" for s be Complex-SequenceCOMSEQ-1M1 holds  for n be NatNAT-1M1 holds  ex r be RealXREAL-0M1 st 0NUMBERSK6 <XXREAL-0R3 r & ( for m be NatNAT-1M1 holds m <=XXREAL-0R1 n implies |.COMPLEX1K10 s .NAT-1K8\<^bsub>(COMPLEXNUMBERSK3)\<^esub> m.| <XXREAL-0R3 r)"
sorry

(*begin*)
mdef comseq_2_def_1 (" _ *''COMSEQ-2K1" [228]228 ) where
  mlet "f be complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1"
"func f *'COMSEQ-2K1 \<rightarrow> complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1 means
  \<lambda>it. domRELAT-1K1 it =XBOOLE-0R4 domRELAT-1K1 f & ( for c be setHIDDENM2 holds c inTARSKIR2 domRELAT-1K1 it implies it .FUNCT-1K1 c =COMPLEX1R1 (f .FUNCT-1K1 c)*'COMPLEX1K9)"
proof-
  (*existence*)
    show " ex it be complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1 st domRELAT-1K1 it =XBOOLE-0R4 domRELAT-1K1 f & ( for c be setHIDDENM2 holds c inTARSKIR2 domRELAT-1K1 it implies it .FUNCT-1K1 c =COMPLEX1R1 (f .FUNCT-1K1 c)*'COMPLEX1K9)"
sorry
  (*uniqueness*)
    show " for it1 be complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1 holds  for it2 be complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1 holds (domRELAT-1K1 it1 =XBOOLE-0R4 domRELAT-1K1 f & ( for c be setHIDDENM2 holds c inTARSKIR2 domRELAT-1K1 it1 implies it1 .FUNCT-1K1 c =COMPLEX1R1 (f .FUNCT-1K1 c)*'COMPLEX1K9)) & (domRELAT-1K1 it2 =XBOOLE-0R4 domRELAT-1K1 f & ( for c be setHIDDENM2 holds c inTARSKIR2 domRELAT-1K1 it2 implies it2 .FUNCT-1K1 c =COMPLEX1R1 (f .FUNCT-1K1 c)*'COMPLEX1K9)) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mtheorem COMSEQ_2K1_involutiveness:
" for f be complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1 holds (f *'COMSEQ-2K1)*'COMSEQ-2K1 =HIDDENR1 f"
sorry

syntax COMSEQ_2K2 :: " Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ *''COMSEQ-2K2\<^bsub>'( _ ')\<^esub>" [228,0]228)
translations "f *'COMSEQ-2K2\<^bsub>(C)\<^esub>" \<rightharpoonup> "f *'COMSEQ-2K1"

mtheorem comseq_2_def_2:
  mlet "C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "f be FunctionFUNCT-2M1-of(C,COMPLEXNUMBERSK3)"
"redefine func f *'COMSEQ-2K2\<^bsub>(C)\<^esub> \<rightarrow> FunctionFUNCT-2M1-of(C,COMPLEXNUMBERSK3) means
  \<lambda>it.  for n be ElementSUBSET-1M1-of C holds it .FUNCT-2K3\<^bsub>(C,COMPLEXNUMBERSK3)\<^esub> n =COMPLEX1R1 (f .FUNCT-2K3\<^bsub>(C,COMPLEXNUMBERSK3)\<^esub> n)*'COMPLEX1K9"
proof
(*compatibility*)
  show " for it be FunctionFUNCT-2M1-of(C,COMPLEXNUMBERSK3) holds it =HIDDENR1 f *'COMSEQ-2K2\<^bsub>(C)\<^esub> iff ( for n be ElementSUBSET-1M1-of C holds it .FUNCT-2K3\<^bsub>(C,COMPLEXNUMBERSK3)\<^esub> n =COMPLEX1R1 (f .FUNCT-2K3\<^bsub>(C,COMPLEXNUMBERSK3)\<^esub> n)*'COMPLEX1K9)"
sorry
qed "sorry"

mtheorem comseq_2_add_1:
  mlet "C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "f be FunctionFUNCT-2M1-of(C,COMPLEXNUMBERSK3)"
"cluster f *'COMSEQ-2K1 as-term-is FunctionFUNCT-2M1-of(C,COMPLEXNUMBERSK3)"
proof
(*coherence*)
  show "f *'COMSEQ-2K1 be FunctionFUNCT-2M1-of(C,COMPLEXNUMBERSK3)"
sorry
qed "sorry"

mtheorem comseq_2_cl_1:
  mlet "C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "s be complex-valuedVALUED-0V5\<bar>ManySortedSetPBOOLEM1-of C"
"cluster s *'COMSEQ-2K1 as-term-is C -definedRELAT-1V4"
proof
(*coherence*)
  show "s *'COMSEQ-2K1 be C -definedRELAT-1V4"
sorry
qed "sorry"

mtheorem comseq_2_cl_2:
  mlet "C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "seq be complex-valuedVALUED-0V5\<bar>ManySortedSetPBOOLEM1-of C"
"cluster seq *'COMSEQ-2K1 as-term-is totalPARTFUN1V1\<^bsub>(C)\<^esub> for C -definedRELAT-1V4\<bar>FunctionFUNCT-1M1"
proof
(*coherence*)
  show " for it be C -definedRELAT-1V4\<bar>FunctionFUNCT-1M1 holds it =HIDDENR1 seq *'COMSEQ-2K1 implies it be totalPARTFUN1V1\<^bsub>(C)\<^esub>"
sorry
qed "sorry"

mtheorem comseq_2_th_3:
" for s be Complex-SequenceCOMSEQ-1M1 holds s be non-zeroORDINAL1V9 implies s *'COMSEQ-2K2\<^bsub>(NATNUMBERSK1)\<^esub> be non-zeroORDINAL1V9"
sorry

mtheorem comseq_2_th_4:
" for r be ComplexXCMPLX-0M1 holds  for s be Complex-SequenceCOMSEQ-1M1 holds (r (#)VALUED-1K27\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> s)*'COMSEQ-2K2\<^bsub>(NATNUMBERSK1)\<^esub> =FUNCT-2R2\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> r *'COMPLEX1K9 (#)VALUED-1K27\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> s *'COMSEQ-2K2\<^bsub>(NATNUMBERSK1)\<^esub>"
sorry

mtheorem comseq_2_th_5:
" for s be Complex-SequenceCOMSEQ-1M1 holds  for s9 be Complex-SequenceCOMSEQ-1M1 holds (s (#)VALUED-1K20\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> s9)*'COMSEQ-2K2\<^bsub>(NATNUMBERSK1)\<^esub> =FUNCT-2R2\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> s *'COMSEQ-2K2\<^bsub>(NATNUMBERSK1)\<^esub> (#)VALUED-1K20\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> s9 *'COMSEQ-2K2\<^bsub>(NATNUMBERSK1)\<^esub>"
sorry

mtheorem comseq_2_th_6:
" for s be Complex-SequenceCOMSEQ-1M1 holds (s *'COMSEQ-2K2\<^bsub>(NATNUMBERSK1)\<^esub>)\<inverse>VALUED-1K38\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> =FUNCT-2R2\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> (s \<inverse>VALUED-1K38\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub>)*'COMSEQ-2K2\<^bsub>(NATNUMBERSK1)\<^esub>"
sorry

mtheorem comseq_2_th_7:
" for s be Complex-SequenceCOMSEQ-1M1 holds  for s9 be Complex-SequenceCOMSEQ-1M1 holds (s9 /\<inverse>VALUED-1K53\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> s)*'COMSEQ-2K2\<^bsub>(NATNUMBERSK1)\<^esub> =FUNCT-2R2\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> s9 *'COMSEQ-2K2\<^bsub>(NATNUMBERSK1)\<^esub> /\<inverse>VALUED-1K53\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> s *'COMSEQ-2K2\<^bsub>(NATNUMBERSK1)\<^esub>"
sorry

(*begin*)
mdef comseq_2_def_3 ("boundedCOMSEQ-2V1" 70 ) where
"attr boundedCOMSEQ-2V1 for complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1 means
  (\<lambda>f.  ex r be RealXREAL-0M1 st  for y be setHIDDENM2 holds y inTARSKIR2 domRELAT-1K1 f implies |.COMPLEX1K10 f .FUNCT-1K1 y.| <XXREAL-0R3 r)"..

abbreviation(input) COMSEQ_2V2("boundedCOMSEQ-2V2" 70) where
  "boundedCOMSEQ-2V2 \<equiv> boundedCOMSEQ-2V1"

mtheorem comseq_2_def_4:
  mlet "s be Complex-SequenceCOMSEQ-1M1"
"redefine attr boundedCOMSEQ-2V2 for Complex-SequenceCOMSEQ-1M1 means
  (\<lambda>s.  ex r be RealXREAL-0M1 st  for n be NatNAT-1M1 holds |.COMPLEX1K10 s .NAT-1K8\<^bsub>(COMPLEXNUMBERSK3)\<^esub> n.| <XXREAL-0R3 r)"
proof
(*compatibility*)
  show " for s be Complex-SequenceCOMSEQ-1M1 holds s be boundedCOMSEQ-2V2 iff ( ex r be RealXREAL-0M1 st  for n be NatNAT-1M1 holds |.COMPLEX1K10 s .NAT-1K8\<^bsub>(COMPLEXNUMBERSK3)\<^esub> n.| <XXREAL-0R3 r)"
sorry
qed "sorry"

mtheorem comseq_2_cl_3:
"cluster boundedCOMSEQ-2V2 for Complex-SequenceCOMSEQ-1M1"
proof
(*existence*)
  show " ex it be Complex-SequenceCOMSEQ-1M1 st it be boundedCOMSEQ-2V2"
sorry
qed "sorry"

mtheorem comseq_2_th_8:
" for s be Complex-SequenceCOMSEQ-1M1 holds s be boundedCOMSEQ-2V2 iff ( ex r be RealXREAL-0M1 st 0NUMBERSK6 <XXREAL-0R3 r & ( for n be NatNAT-1M1 holds |.COMPLEX1K10 s .NAT-1K8\<^bsub>(COMPLEXNUMBERSK3)\<^esub> n.| <XXREAL-0R3 r))"
sorry

(*begin*)
mdef comseq_2_def_5 ("convergentCOMSEQ-2V3" 70 ) where
"attr convergentCOMSEQ-2V3 for complex-valuedVALUED-0V5\<bar>ManySortedSetPBOOLEM1-of NATNUMBERSK1 means
  (\<lambda>s.  ex g be ComplexXCMPLX-0M1 st  for p be RealXREAL-0M1 holds 0NUMBERSK6 <XXREAL-0R3 p implies ( ex n be NatNAT-1M1 st  for m be NatNAT-1M1 holds n <=XXREAL-0R1 m implies |.COMPLEX1K10 s .FUNCT-1K1 m -XCMPLX-0K6 g .| <XXREAL-0R3 p))"..

mdef comseq_2_def_6 ("limCOMSEQ-2K3  _ " [164]164 ) where
  mlet "s be Complex-SequenceCOMSEQ-1M1"
"assume s be convergentCOMSEQ-2V3 func limCOMSEQ-2K3 s \<rightarrow> ComplexXCMPLX-0M1 means
  \<lambda>it.  for p be RealXREAL-0M1 holds 0NUMBERSK6 <XXREAL-0R3 p implies ( ex n be NatNAT-1M1 st  for m be NatNAT-1M1 holds n <=XXREAL-0R1 m implies |.COMPLEX1K10 s .NAT-1K8\<^bsub>(COMPLEXNUMBERSK3)\<^esub> m -XCMPLX-0K6 it .| <XXREAL-0R3 p)"
proof-
  (*existence*)
    show "s be convergentCOMSEQ-2V3 implies ( ex it be ComplexXCMPLX-0M1 st  for p be RealXREAL-0M1 holds 0NUMBERSK6 <XXREAL-0R3 p implies ( ex n be NatNAT-1M1 st  for m be NatNAT-1M1 holds n <=XXREAL-0R1 m implies |.COMPLEX1K10 s .NAT-1K8\<^bsub>(COMPLEXNUMBERSK3)\<^esub> m -XCMPLX-0K6 it .| <XXREAL-0R3 p))"
sorry
  (*uniqueness*)
    show "s be convergentCOMSEQ-2V3 implies ( for it1 be ComplexXCMPLX-0M1 holds  for it2 be ComplexXCMPLX-0M1 holds ( for p be RealXREAL-0M1 holds 0NUMBERSK6 <XXREAL-0R3 p implies ( ex n be NatNAT-1M1 st  for m be NatNAT-1M1 holds n <=XXREAL-0R1 m implies |.COMPLEX1K10 s .NAT-1K8\<^bsub>(COMPLEXNUMBERSK3)\<^esub> m -XCMPLX-0K6 it1 .| <XXREAL-0R3 p)) & ( for p be RealXREAL-0M1 holds 0NUMBERSK6 <XXREAL-0R3 p implies ( ex n be NatNAT-1M1 st  for m be NatNAT-1M1 holds n <=XXREAL-0R1 m implies |.COMPLEX1K10 s .NAT-1K8\<^bsub>(COMPLEXNUMBERSK3)\<^esub> m -XCMPLX-0K6 it2 .| <XXREAL-0R3 p)) implies it1 =HIDDENR1 it2)"
sorry
qed "sorry"

mtheorem comseq_2_th_9:
" for s be Complex-SequenceCOMSEQ-1M1 holds ( ex g be ComplexXCMPLX-0M1 st  for n be NatNAT-1M1 holds s .NAT-1K8\<^bsub>(COMPLEXNUMBERSK3)\<^esub> n =COMPLEX1R1 g) implies s be convergentCOMSEQ-2V3"
sorry

mtheorem comseq_2_th_10:
" for s be Complex-SequenceCOMSEQ-1M1 holds  for g be ComplexXCMPLX-0M1 holds ( for n be NatNAT-1M1 holds s .NAT-1K8\<^bsub>(COMPLEXNUMBERSK3)\<^esub> n =COMPLEX1R1 g) implies limCOMSEQ-2K3 s =COMPLEX1R1 g"
sorry

mtheorem comseq_2_cl_4:
"cluster convergentCOMSEQ-2V3 for Complex-SequenceCOMSEQ-1M1"
proof
(*existence*)
  show " ex it be Complex-SequenceCOMSEQ-1M1 st it be convergentCOMSEQ-2V3"
sorry
qed "sorry"

mtheorem comseq_2_cl_5:
  mlet "s be convergentCOMSEQ-2V3\<bar>Complex-SequenceCOMSEQ-1M1"
"cluster s *'COMSEQ-2K2\<^bsub>(NATNUMBERSK1)\<^esub> as-term-is convergentCOMSEQ-2V3 for Complex-SequenceCOMSEQ-1M1"
proof
(*coherence*)
  show " for it be Complex-SequenceCOMSEQ-1M1 holds it =HIDDENR1 s *'COMSEQ-2K2\<^bsub>(NATNUMBERSK1)\<^esub> implies it be convergentCOMSEQ-2V3"
sorry
qed "sorry"

(*\$CT*)
mtheorem comseq_2_th_12:
" for s be Complex-SequenceCOMSEQ-1M1 holds s be convergentCOMSEQ-2V3 implies limCOMSEQ-2K3 s *'COMSEQ-2K2\<^bsub>(NATNUMBERSK1)\<^esub> =COMPLEX1R1 (limCOMSEQ-2K3 s)*'COMPLEX1K9"
sorry

(*begin*)
mtheorem comseq_2_cl_6:
  mlet "s1 be convergentCOMSEQ-2V3\<bar>Complex-SequenceCOMSEQ-1M1", "s2 be convergentCOMSEQ-2V3\<bar>Complex-SequenceCOMSEQ-1M1"
"cluster s1 +VALUED-1K2\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> s2 as-term-is convergentCOMSEQ-2V3 for Complex-SequenceCOMSEQ-1M1"
proof
(*coherence*)
  show " for it be Complex-SequenceCOMSEQ-1M1 holds it =HIDDENR1 s1 +VALUED-1K2\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> s2 implies it be convergentCOMSEQ-2V3"
sorry
qed "sorry"

(*\$CT*)
mtheorem comseq_2_th_14:
" for s be convergentCOMSEQ-2V3\<bar>Complex-SequenceCOMSEQ-1M1 holds  for s9 be convergentCOMSEQ-2V3\<bar>Complex-SequenceCOMSEQ-1M1 holds limCOMSEQ-2K3 (s +VALUED-1K2\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> s9) =COMPLEX1R1 limCOMSEQ-2K3 s +XCMPLX-0K2 limCOMSEQ-2K3 s9"
sorry

(*\$CT*)
mtheorem comseq_2_th_16:
" for s be convergentCOMSEQ-2V3\<bar>Complex-SequenceCOMSEQ-1M1 holds  for s9 be convergentCOMSEQ-2V3\<bar>Complex-SequenceCOMSEQ-1M1 holds limCOMSEQ-2K3 (s +VALUED-1K2\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> s9)*'COMSEQ-2K2\<^bsub>(NATNUMBERSK1)\<^esub> =COMPLEX1R1 (limCOMSEQ-2K3 s)*'COMPLEX1K9 +XCMPLX-0K2 (limCOMSEQ-2K3 s9)*'COMPLEX1K9"
sorry

mtheorem comseq_2_cl_7:
  mlet "s be convergentCOMSEQ-2V3\<bar>Complex-SequenceCOMSEQ-1M1", "c be ComplexXCMPLX-0M1"
"cluster c (#)VALUED-1K27\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> s as-term-is convergentCOMSEQ-2V3 for Complex-SequenceCOMSEQ-1M1"
proof
(*coherence*)
  show " for it be Complex-SequenceCOMSEQ-1M1 holds it =HIDDENR1 c (#)VALUED-1K27\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> s implies it be convergentCOMSEQ-2V3"
sorry
qed "sorry"

(*\$CT*)
mtheorem comseq_2_th_18:
" for s be convergentCOMSEQ-2V3\<bar>Complex-SequenceCOMSEQ-1M1 holds  for r be ComplexXCMPLX-0M1 holds limCOMSEQ-2K3 (r (#)VALUED-1K27\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> s) =COMPLEX1R1 r *XCMPLX-0K3 (limCOMSEQ-2K3 s)"
sorry

(*\$CT*)
mtheorem comseq_2_th_20:
" for r be ComplexXCMPLX-0M1 holds  for s be convergentCOMSEQ-2V3\<bar>Complex-SequenceCOMSEQ-1M1 holds limCOMSEQ-2K3 (r (#)VALUED-1K27\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> s)*'COMSEQ-2K2\<^bsub>(NATNUMBERSK1)\<^esub> =COMPLEX1R1 r *'COMPLEX1K9 *XCMPLX-0K3 (limCOMSEQ-2K3 s)*'COMPLEX1K9"
sorry

mtheorem comseq_2_cl_8:
  mlet "s be convergentCOMSEQ-2V3\<bar>Complex-SequenceCOMSEQ-1M1"
"cluster -VALUED-1K33\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> s as-term-is convergentCOMSEQ-2V3 for Complex-SequenceCOMSEQ-1M1"
proof
(*coherence*)
  show " for it be Complex-SequenceCOMSEQ-1M1 holds it =HIDDENR1 -VALUED-1K33\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> s implies it be convergentCOMSEQ-2V3"
     sorry
qed "sorry"

(*\$CT*)
mtheorem comseq_2_th_22:
" for s be convergentCOMSEQ-2V3\<bar>Complex-SequenceCOMSEQ-1M1 holds limCOMSEQ-2K3 (-VALUED-1K33\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> s) =COMPLEX1R1 -XCMPLX-0K4 limCOMSEQ-2K3 s"
sorry

(*\$CT*)
mtheorem comseq_2_th_24:
" for s be convergentCOMSEQ-2V3\<bar>Complex-SequenceCOMSEQ-1M1 holds limCOMSEQ-2K3 (-VALUED-1K33\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> s)*'COMSEQ-2K2\<^bsub>(NATNUMBERSK1)\<^esub> =COMPLEX1R1 -XCMPLX-0K4 (limCOMSEQ-2K3 s)*'COMPLEX1K9"
sorry

mtheorem comseq_2_cl_9:
  mlet "s1 be convergentCOMSEQ-2V3\<bar>Complex-SequenceCOMSEQ-1M1", "s2 be convergentCOMSEQ-2V3\<bar>Complex-SequenceCOMSEQ-1M1"
"cluster s1 -VALUED-1K48\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> s2 as-term-is convergentCOMSEQ-2V3 for Complex-SequenceCOMSEQ-1M1"
proof
(*coherence*)
  show " for it be Complex-SequenceCOMSEQ-1M1 holds it =HIDDENR1 s1 -VALUED-1K48\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> s2 implies it be convergentCOMSEQ-2V3"
sorry
qed "sorry"

(*\$CT*)
mtheorem comseq_2_th_26:
" for s be convergentCOMSEQ-2V3\<bar>Complex-SequenceCOMSEQ-1M1 holds  for s9 be convergentCOMSEQ-2V3\<bar>Complex-SequenceCOMSEQ-1M1 holds limCOMSEQ-2K3 (s -VALUED-1K48\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> s9) =COMPLEX1R1 limCOMSEQ-2K3 s -XCMPLX-0K6 limCOMSEQ-2K3 s9"
sorry

(*\$CT*)
mtheorem comseq_2_th_28:
" for s be convergentCOMSEQ-2V3\<bar>Complex-SequenceCOMSEQ-1M1 holds  for s9 be convergentCOMSEQ-2V3\<bar>Complex-SequenceCOMSEQ-1M1 holds limCOMSEQ-2K3 (s -VALUED-1K48\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> s9)*'COMSEQ-2K2\<^bsub>(NATNUMBERSK1)\<^esub> =COMPLEX1R1 (limCOMSEQ-2K3 s)*'COMPLEX1K9 -XCMPLX-0K6 (limCOMSEQ-2K3 s9)*'COMPLEX1K9"
sorry

mtheorem comseq_2_cl_10:
"cluster convergentCOMSEQ-2V3 also-is boundedCOMSEQ-2V2 for Complex-SequenceCOMSEQ-1M1"
proof
(*coherence*)
  show " for it be Complex-SequenceCOMSEQ-1M1 holds it be convergentCOMSEQ-2V3 implies it be boundedCOMSEQ-2V2"
sorry
qed "sorry"

mtheorem comseq_2_cl_11:
"cluster  non boundedCOMSEQ-2V2 also-is  non convergentCOMSEQ-2V3 for Complex-SequenceCOMSEQ-1M1"
proof
(*coherence*)
  show " for it be Complex-SequenceCOMSEQ-1M1 holds it be  non boundedCOMSEQ-2V2 implies it be  non convergentCOMSEQ-2V3"
     sorry
qed "sorry"

mtheorem comseq_2_cl_12:
  mlet "s1 be convergentCOMSEQ-2V3\<bar>Complex-SequenceCOMSEQ-1M1", "s2 be convergentCOMSEQ-2V3\<bar>Complex-SequenceCOMSEQ-1M1"
"cluster s1 (#)VALUED-1K20\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> s2 as-term-is convergentCOMSEQ-2V3 for Complex-SequenceCOMSEQ-1M1"
proof
(*coherence*)
  show " for it be Complex-SequenceCOMSEQ-1M1 holds it =HIDDENR1 s1 (#)VALUED-1K20\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> s2 implies it be convergentCOMSEQ-2V3"
sorry
qed "sorry"

(*\$CT*)
mtheorem comseq_2_th_30:
" for s be convergentCOMSEQ-2V3\<bar>Complex-SequenceCOMSEQ-1M1 holds  for s9 be convergentCOMSEQ-2V3\<bar>Complex-SequenceCOMSEQ-1M1 holds limCOMSEQ-2K3 (s (#)VALUED-1K20\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> s9) =COMPLEX1R1 (limCOMSEQ-2K3 s)*XCMPLX-0K3 (limCOMSEQ-2K3 s9)"
sorry

(*\$CT*)
mtheorem comseq_2_th_32:
" for s be convergentCOMSEQ-2V3\<bar>Complex-SequenceCOMSEQ-1M1 holds  for s9 be convergentCOMSEQ-2V3\<bar>Complex-SequenceCOMSEQ-1M1 holds limCOMSEQ-2K3 (s (#)VALUED-1K20\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> s9)*'COMSEQ-2K2\<^bsub>(NATNUMBERSK1)\<^esub> =COMPLEX1R1 (limCOMSEQ-2K3 s)*'COMPLEX1K9 *XCMPLX-0K3 (limCOMSEQ-2K3 s9)*'COMPLEX1K9"
sorry

mtheorem comseq_2_th_33:
" for s be convergentCOMSEQ-2V3\<bar>Complex-SequenceCOMSEQ-1M1 holds limCOMSEQ-2K3 s <>HIDDENR2 0cCOMPLEX1K6 implies ( ex n be NatNAT-1M1 st  for m be NatNAT-1M1 holds n <=XXREAL-0R1 m implies (|.COMPLEX1K10 limCOMSEQ-2K3 s .|)/XCMPLX-0K7 \<two>\<^sub>M <XXREAL-0R3 |.COMPLEX1K10 s .NAT-1K8\<^bsub>(COMPLEXNUMBERSK3)\<^esub> m.|)"
sorry

mtheorem comseq_2_th_34:
" for s be convergentCOMSEQ-2V3\<bar>Complex-SequenceCOMSEQ-1M1 holds limCOMSEQ-2K3 s <>HIDDENR2 0cCOMPLEX1K6 & s be non-zeroORDINAL1V9 implies s \<inverse>VALUED-1K38\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> be convergentCOMSEQ-2V3"
sorry

mtheorem comseq_2_th_35:
" for s be Complex-SequenceCOMSEQ-1M1 holds (s be convergentCOMSEQ-2V3 & limCOMSEQ-2K3 s <>HIDDENR2 0cCOMPLEX1K6) & s be non-zeroORDINAL1V9 implies limCOMSEQ-2K3 s \<inverse>VALUED-1K38\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub> =COMPLEX1R1 (limCOMSEQ-2K3 s)\<inverse>XCMPLX-0K5"
sorry

(*\$CT*)
mtheorem comseq_2_th_37:
" for s be Complex-SequenceCOMSEQ-1M1 holds (s be convergentCOMSEQ-2V3 & limCOMSEQ-2K3 s <>HIDDENR2 0cCOMPLEX1K6) & s be non-zeroORDINAL1V9 implies limCOMSEQ-2K3 (s \<inverse>VALUED-1K38\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3)\<^esub>)*'COMSEQ-2K2\<^bsub>(NATNUMBERSK1)\<^esub> =COMPLEX1R1 ((limCOMSEQ-2K3 s)*'COMPLEX1K9)\<inverse>XCMPLX-0K5"
sorry

mtheorem comseq_2_th_38:
" for s be Complex-SequenceCOMSEQ-1M1 holds  for s9 be Complex-SequenceCOMSEQ-1M1 holds ((s9 be convergentCOMSEQ-2V3 & s be convergentCOMSEQ-2V3) & limCOMSEQ-2K3 s <>HIDDENR2 0cCOMPLEX1K6) & s be non-zeroORDINAL1V9 implies s9 /\<inverse>VALUED-1K53\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> s be convergentCOMSEQ-2V3"
sorry

mtheorem comseq_2_th_39:
" for s be Complex-SequenceCOMSEQ-1M1 holds  for s9 be Complex-SequenceCOMSEQ-1M1 holds ((s9 be convergentCOMSEQ-2V3 & s be convergentCOMSEQ-2V3) & limCOMSEQ-2K3 s <>HIDDENR2 0cCOMPLEX1K6) & s be non-zeroORDINAL1V9 implies limCOMSEQ-2K3 (s9 /\<inverse>VALUED-1K53\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> s) =COMPLEX1R1 (limCOMSEQ-2K3 s9)/XCMPLX-0K7 (limCOMSEQ-2K3 s)"
sorry

(*\$CT*)
mtheorem comseq_2_th_41:
" for s be Complex-SequenceCOMSEQ-1M1 holds  for s9 be Complex-SequenceCOMSEQ-1M1 holds ((s9 be convergentCOMSEQ-2V3 & s be convergentCOMSEQ-2V3) & limCOMSEQ-2K3 s <>HIDDENR2 0cCOMPLEX1K6) & s be non-zeroORDINAL1V9 implies limCOMSEQ-2K3 (s9 /\<inverse>VALUED-1K53\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> s)*'COMSEQ-2K2\<^bsub>(NATNUMBERSK1)\<^esub> =COMPLEX1R1 (limCOMSEQ-2K3 s9)*'COMPLEX1K9 /XCMPLX-0K7 (limCOMSEQ-2K3 s)*'COMPLEX1K9"
sorry

mtheorem comseq_2_th_42:
" for s be Complex-SequenceCOMSEQ-1M1 holds  for s1 be Complex-SequenceCOMSEQ-1M1 holds (s be convergentCOMSEQ-2V3 & s1 be boundedCOMSEQ-2V2) & limCOMSEQ-2K3 s =COMPLEX1R1 0cCOMPLEX1K6 implies s (#)VALUED-1K20\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> s1 be convergentCOMSEQ-2V3"
sorry

mtheorem comseq_2_th_43:
" for s be Complex-SequenceCOMSEQ-1M1 holds  for s1 be Complex-SequenceCOMSEQ-1M1 holds (s be convergentCOMSEQ-2V3 & s1 be boundedCOMSEQ-2V2) & limCOMSEQ-2K3 s =COMPLEX1R1 0cCOMPLEX1K6 implies limCOMSEQ-2K3 (s (#)VALUED-1K20\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> s1) =COMPLEX1R1 0cCOMPLEX1K6"
sorry

(*\$CT*)
mtheorem comseq_2_th_45:
" for s be Complex-SequenceCOMSEQ-1M1 holds  for s1 be Complex-SequenceCOMSEQ-1M1 holds (s be convergentCOMSEQ-2V3 & s1 be boundedCOMSEQ-2V2) & limCOMSEQ-2K3 s =COMPLEX1R1 0cCOMPLEX1K6 implies limCOMSEQ-2K3 (s (#)VALUED-1K20\<^bsub>(NATNUMBERSK1,COMPLEXNUMBERSK3,COMPLEXNUMBERSK3)\<^esub> s1)*'COMSEQ-2K2\<^bsub>(NATNUMBERSK1)\<^esub> =COMPLEX1R1 0cCOMPLEX1K6"
sorry

end
