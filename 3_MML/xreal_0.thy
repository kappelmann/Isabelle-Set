theory xreal_0
  imports xcmplx_0 xxreal_0 arytm_3
   "../mizar_extension/E_number"
begin
(*begin*)
mdef xreal_0_def_1 ("realXREAL-0V1" 70 ) where
"attr realXREAL-0V1 for objectHIDDENM1 means
  (\<lambda>r. r inHIDDENR3 REALNUMBERSK2)"..

mtheorem xreal_0_cl_1:
"cluster note-that realXREAL-0V1 for ElementSUBSET-1M1-of REALNUMBERSK2"
proof
(*coherence*)
  show " for it be ElementSUBSET-1M1-of REALNUMBERSK2 holds it be realXREAL-0V1"
     sorry
qed "sorry"

mtheorem xreal_0_cl_2:
"cluster -inftyXXREAL-0K2 as-term-is  non realXREAL-0V1"
proof
(*coherence*)
  show "-inftyXXREAL-0K2 be  non realXREAL-0V1"
sorry
qed "sorry"

mtheorem xreal_0_cl_3:
"cluster +inftyXXREAL-0K1 as-term-is  non realXREAL-0V1"
proof
(*coherence*)
  show "+inftyXXREAL-0K1 be  non realXREAL-0V1"
sorry
qed "sorry"

mtheorem xreal_0_cl_4:
"cluster naturalORDINAL1V7 also-is realXREAL-0V1 for objectHIDDENM1"
proof
(*coherence*)
  show " for it be objectHIDDENM1 holds it be naturalORDINAL1V7 implies it be realXREAL-0V1"
    using numbers_th_19 sorry
qed "sorry"

mtheorem xreal_0_cl_5:
"cluster realXREAL-0V1 also-is complexXCMPLX-0V1 for objectHIDDENM1"
proof
(*coherence*)
  show " for it be objectHIDDENM1 holds it be realXREAL-0V1 implies it be complexXCMPLX-0V1"
     sorry
qed "sorry"

mtheorem xreal_0_cl_6:
"cluster realXREAL-0V1 for objectHIDDENM1"
proof
(*existence*)
  show " ex it be objectHIDDENM1 st it be realXREAL-0V1"
sorry
qed "sorry"

mtheorem xreal_0_cl_7:
"cluster realXREAL-0V1 for numberORDINAL1M2"
proof
(*existence*)
  show " ex it be numberORDINAL1M2 st it be realXREAL-0V1"
sorry
qed "sorry"

mtheorem xreal_0_cl_8:
"cluster realXREAL-0V1 also-is ext-realXXREAL-0V1 for objectHIDDENM1"
proof
(*coherence*)
  show " for it be objectHIDDENM1 holds it be realXREAL-0V1 implies it be ext-realXXREAL-0V1"
sorry
qed "sorry"

syntax XREAL_0M1 :: "Ty" ("RealXREAL-0M1" 70)
translations "RealXREAL-0M1" \<rightharpoonup> "realXREAL-0V1\<bar>NumberORDINAL1M1"

mlemma xreal_0_lm_1:
" for x be RealXREAL-0M1 holds  for x1 be ElementSUBSET-1M1-of REALNUMBERSK2 holds  for x2 be ElementSUBSET-1M1-of REALNUMBERSK2 holds x =HIDDENR1 [*ARYTM-0K5 x1,x2 *] implies x2 =XBOOLE-0R4 0NUMBERSK6 & x =HIDDENR1 x1"
sorry

mtheorem xreal_0_cl_9:
  mlet "x be RealXREAL-0M1"
"cluster -XCMPLX-0K4 x as-term-is realXREAL-0V1"
proof
(*coherence*)
  show "-XCMPLX-0K4 x be realXREAL-0V1"
sorry
qed "sorry"

mtheorem xreal_0_cl_10:
  mlet "x be RealXREAL-0M1"
"cluster x \<inverse>XCMPLX-0K5 as-term-is realXREAL-0V1"
proof
(*coherence*)
  show "x \<inverse>XCMPLX-0K5 be realXREAL-0V1"
sorry
qed "sorry"

mtheorem xreal_0_cl_11:
  mlet "x be RealXREAL-0M1", "y be RealXREAL-0M1"
"cluster x +XCMPLX-0K2 y as-term-is realXREAL-0V1"
proof
(*coherence*)
  show "x +XCMPLX-0K2 y be realXREAL-0V1"
sorry
qed "sorry"

mtheorem xreal_0_cl_12:
  mlet "x be RealXREAL-0M1", "y be RealXREAL-0M1"
"cluster x *XCMPLX-0K3 y as-term-is realXREAL-0V1"
proof
(*coherence*)
  show "x *XCMPLX-0K3 y be realXREAL-0V1"
sorry
qed "sorry"

mtheorem xreal_0_cl_13:
  mlet "x be RealXREAL-0M1", "y be RealXREAL-0M1"
"cluster x -XCMPLX-0K6 y as-term-is realXREAL-0V1"
proof
(*coherence*)
  show "x -XCMPLX-0K6 y be realXREAL-0V1"
     sorry
qed "sorry"

mtheorem xreal_0_cl_14:
  mlet "x be RealXREAL-0M1", "y be RealXREAL-0M1"
"cluster x /XCMPLX-0K7 y as-term-is realXREAL-0V1"
proof
(*coherence*)
  show "x /XCMPLX-0K7 y be realXREAL-0V1"
     sorry
qed "sorry"

(*begin*)
reserve r, s, t for "RealXREAL-0M1"
mlemma xreal_0_lm_2:
" for r be RealXREAL-0M1 holds  for s be RealXREAL-0M1 holds ((r inHIDDENR3 REAL+ARYTM-2K2 & s inHIDDENR3 REAL+ARYTM-2K2) & ( ex x9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st  ex y9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st (r =HIDDENR1 x9 & s =HIDDENR1 y9) & x9 <='ARYTM-2R1 y9) or (r inHIDDENR3 [:ZFMISC-1K2 {TARSKIK1 0NUMBERSK6 },REAL+ARYTM-2K2 :] & s inHIDDENR3 [:ZFMISC-1K2 {TARSKIK1 0NUMBERSK6 },REAL+ARYTM-2K2 :]) & ( ex x9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st  ex y9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st (r =HIDDENR1 [TARSKIK4 0NUMBERSK6,x9 ] & s =HIDDENR1 [TARSKIK4 0NUMBERSK6,y9 ]) & y9 <='ARYTM-2R1 x9)) or s inHIDDENR3 REAL+ARYTM-2K2 & r inHIDDENR3 [:ZFMISC-1K2 {TARSKIK1 0NUMBERSK6 },REAL+ARYTM-2K2 :] implies r <=XXREAL-0R1 s"
sorry

mlemma xreal_0_lm_3:
"{}XBOOLE-0K1 inTARSKIR2 {TARSKIK1 {}XBOOLE-0K1 }"
  using tarski_def_1 sorry

mlemma xreal_0_lm_4:
" for r be RealXREAL-0M1 holds  for s be RealXREAL-0M1 holds r <=XXREAL-0R1 s & s <=XXREAL-0R1 r implies r =HIDDENR1 s"
sorry

mlemma xreal_0_lm_5:
" for r be RealXREAL-0M1 holds  for s be RealXREAL-0M1 holds  for t be RealXREAL-0M1 holds r <=XXREAL-0R1 s implies r +XCMPLX-0K2 t <=XXREAL-0R1 s +XCMPLX-0K2 t"
sorry

mlemma xreal_0_lm_6:
" for r be RealXREAL-0M1 holds  for s be RealXREAL-0M1 holds  for t be RealXREAL-0M1 holds r <=XXREAL-0R1 s & s <=XXREAL-0R1 t implies r <=XXREAL-0R1 t"
sorry

mlemma xreal_0_lm_7:
" not 0NUMBERSK6 inTARSKIR2 [:ZFMISC-1K2 {TARSKIK1 0NUMBERSK6 },REAL+ARYTM-2K2 :]"
  using arytm_0_th_5 arytm_2_th_20 xboole_0_th_3 sorry

mlemma xreal_0_lm_8:
"0NUMBERSK6 <=XXREAL-0R1 \<one>\<^sub>M"
sorry

mlemma xreal_0_lm_9:
" for r be RealXREAL-0M1 holds  for s be RealXREAL-0M1 holds r >=XXREAL-0R2 0NUMBERSK6 & s >XXREAL-0R4 0NUMBERSK6 implies r +XCMPLX-0K2 s >XXREAL-0R4 0NUMBERSK6"
sorry

mlemma xreal_0_lm_10:
" for r be RealXREAL-0M1 holds  for s be RealXREAL-0M1 holds r <=XXREAL-0R1 0NUMBERSK6 & s <XXREAL-0R3 0NUMBERSK6 implies r +XCMPLX-0K2 s <XXREAL-0R3 0NUMBERSK6"
sorry

mlemma xreal_0_lm_11:
" for r be RealXREAL-0M1 holds  for s be RealXREAL-0M1 holds  for t be RealXREAL-0M1 holds r <=XXREAL-0R1 s & 0NUMBERSK6 <=XXREAL-0R1 t implies r *XCMPLX-0K3 t <=XXREAL-0R1 s *XCMPLX-0K3 t"
sorry

mlemma xreal_0_lm_12:
" for r be RealXREAL-0M1 holds  for s be RealXREAL-0M1 holds r >XXREAL-0R4 0NUMBERSK6 & s >XXREAL-0R4 0NUMBERSK6 implies r *XCMPLX-0K3 s >XXREAL-0R4 0NUMBERSK6"
sorry

mlemma xreal_0_lm_13:
" for r be RealXREAL-0M1 holds  for s be RealXREAL-0M1 holds r >XXREAL-0R4 0NUMBERSK6 & s <XXREAL-0R3 0NUMBERSK6 implies r *XCMPLX-0K3 s <XXREAL-0R3 0NUMBERSK6"
sorry

mlemma xreal_0_lm_14:
" for s be RealXREAL-0M1 holds  for t be RealXREAL-0M1 holds s <=XXREAL-0R1 t implies -XCMPLX-0K4 t <=XXREAL-0R1 -XCMPLX-0K4 s"
sorry

mlemma xreal_0_lm_15:
" for r be RealXREAL-0M1 holds  for s be RealXREAL-0M1 holds r <=XXREAL-0R1 0NUMBERSK6 & s >=XXREAL-0R2 0NUMBERSK6 implies r *XCMPLX-0K3 s <=XXREAL-0R1 0NUMBERSK6"
sorry

mtheorem xreal_0_cl_15:
"cluster positiveXXREAL-0V2 for RealXREAL-0M1"
proof
(*existence*)
  show " ex it be RealXREAL-0M1 st it be positiveXXREAL-0V2"
sorry
qed "sorry"

mtheorem xreal_0_cl_16:
"cluster negativeXXREAL-0V3 for RealXREAL-0M1"
proof
(*existence*)
  show " ex it be RealXREAL-0M1 st it be negativeXXREAL-0V3"
sorry
qed "sorry"

mtheorem xreal_0_cl_17:
"cluster zeroORDINAL1V8 for RealXREAL-0M1"
proof
(*existence*)
  show " ex it be RealXREAL-0M1 st it be zeroORDINAL1V8"
sorry
qed "sorry"

mtheorem xreal_0_cl_18:
  mlet "r be  non negativeXXREAL-0V3\<bar>RealXREAL-0M1", "s be  non negativeXXREAL-0V3\<bar>RealXREAL-0M1"
"cluster r +XCMPLX-0K2 s as-term-is  non negativeXXREAL-0V3"
proof
(*coherence*)
  show "r +XCMPLX-0K2 s be  non negativeXXREAL-0V3"
sorry
qed "sorry"

mtheorem xreal_0_cl_19:
  mlet "r be  non positiveXXREAL-0V2\<bar>RealXREAL-0M1", "s be  non positiveXXREAL-0V2\<bar>RealXREAL-0M1"
"cluster r +XCMPLX-0K2 s as-term-is  non positiveXXREAL-0V2"
proof
(*coherence*)
  show "r +XCMPLX-0K2 s be  non positiveXXREAL-0V2"
sorry
qed "sorry"

mtheorem xreal_0_cl_20:
  mlet "r be positiveXXREAL-0V2\<bar>RealXREAL-0M1", "s be  non negativeXXREAL-0V3\<bar>RealXREAL-0M1"
"cluster r +XCMPLX-0K2 s as-term-is positiveXXREAL-0V2"
proof
(*coherence*)
  show "r +XCMPLX-0K2 s be positiveXXREAL-0V2"
sorry
qed "sorry"

mtheorem xreal_0_cl_21:
  mlet "r be positiveXXREAL-0V2\<bar>RealXREAL-0M1", "s be  non negativeXXREAL-0V3\<bar>RealXREAL-0M1"
"cluster s +XCMPLX-0K2 r as-term-is positiveXXREAL-0V2"
proof
(*coherence*)
  show "s +XCMPLX-0K2 r be positiveXXREAL-0V2"
     sorry
qed "sorry"

mtheorem xreal_0_cl_22:
  mlet "r be negativeXXREAL-0V3\<bar>RealXREAL-0M1", "s be  non positiveXXREAL-0V2\<bar>RealXREAL-0M1"
"cluster r +XCMPLX-0K2 s as-term-is negativeXXREAL-0V3"
proof
(*coherence*)
  show "r +XCMPLX-0K2 s be negativeXXREAL-0V3"
sorry
qed "sorry"

mtheorem xreal_0_cl_23:
  mlet "r be negativeXXREAL-0V3\<bar>RealXREAL-0M1", "s be  non positiveXXREAL-0V2\<bar>RealXREAL-0M1"
"cluster s +XCMPLX-0K2 r as-term-is negativeXXREAL-0V3"
proof
(*coherence*)
  show "s +XCMPLX-0K2 r be negativeXXREAL-0V3"
     sorry
qed "sorry"

mtheorem xreal_0_cl_24:
  mlet "r be  non positiveXXREAL-0V2\<bar>RealXREAL-0M1"
"cluster -XCMPLX-0K4 r as-term-is  non negativeXXREAL-0V3"
proof
(*coherence*)
  show "-XCMPLX-0K4 r be  non negativeXXREAL-0V3"
sorry
qed "sorry"

mtheorem xreal_0_cl_25:
  mlet "r be  non negativeXXREAL-0V3\<bar>RealXREAL-0M1"
"cluster -XCMPLX-0K4 r as-term-is  non positiveXXREAL-0V2"
proof
(*coherence*)
  show "-XCMPLX-0K4 r be  non positiveXXREAL-0V2"
sorry
qed "sorry"

mtheorem xreal_0_cl_26:
  mlet "r be  non negativeXXREAL-0V3\<bar>RealXREAL-0M1", "s be  non positiveXXREAL-0V2\<bar>RealXREAL-0M1"
"cluster r -XCMPLX-0K6 s as-term-is  non negativeXXREAL-0V3"
proof
(*coherence*)
  show "r -XCMPLX-0K6 s be  non negativeXXREAL-0V3"
     sorry
qed "sorry"

mtheorem xreal_0_cl_27:
  mlet "r be  non negativeXXREAL-0V3\<bar>RealXREAL-0M1", "s be  non positiveXXREAL-0V2\<bar>RealXREAL-0M1"
"cluster s -XCMPLX-0K6 r as-term-is  non positiveXXREAL-0V2"
proof
(*coherence*)
  show "s -XCMPLX-0K6 r be  non positiveXXREAL-0V2"
     sorry
qed "sorry"

mtheorem xreal_0_cl_28:
  mlet "r be positiveXXREAL-0V2\<bar>RealXREAL-0M1", "s be  non positiveXXREAL-0V2\<bar>RealXREAL-0M1"
"cluster r -XCMPLX-0K6 s as-term-is positiveXXREAL-0V2"
proof
(*coherence*)
  show "r -XCMPLX-0K6 s be positiveXXREAL-0V2"
     sorry
qed "sorry"

mtheorem xreal_0_cl_29:
  mlet "r be positiveXXREAL-0V2\<bar>RealXREAL-0M1", "s be  non positiveXXREAL-0V2\<bar>RealXREAL-0M1"
"cluster s -XCMPLX-0K6 r as-term-is negativeXXREAL-0V3"
proof
(*coherence*)
  show "s -XCMPLX-0K6 r be negativeXXREAL-0V3"
     sorry
qed "sorry"

mtheorem xreal_0_cl_30:
  mlet "r be negativeXXREAL-0V3\<bar>RealXREAL-0M1", "s be  non negativeXXREAL-0V3\<bar>RealXREAL-0M1"
"cluster r -XCMPLX-0K6 s as-term-is negativeXXREAL-0V3"
proof
(*coherence*)
  show "r -XCMPLX-0K6 s be negativeXXREAL-0V3"
     sorry
qed "sorry"

mtheorem xreal_0_cl_31:
  mlet "r be negativeXXREAL-0V3\<bar>RealXREAL-0M1", "s be  non negativeXXREAL-0V3\<bar>RealXREAL-0M1"
"cluster s -XCMPLX-0K6 r as-term-is positiveXXREAL-0V2"
proof
(*coherence*)
  show "s -XCMPLX-0K6 r be positiveXXREAL-0V2"
     sorry
qed "sorry"

mtheorem xreal_0_cl_32:
  mlet "r be  non positiveXXREAL-0V2\<bar>RealXREAL-0M1", "s be  non negativeXXREAL-0V3\<bar>RealXREAL-0M1"
"cluster r *XCMPLX-0K3 s as-term-is  non positiveXXREAL-0V2"
proof
(*coherence*)
  show "r *XCMPLX-0K3 s be  non positiveXXREAL-0V2"
sorry
qed "sorry"

mtheorem xreal_0_cl_33:
  mlet "r be  non positiveXXREAL-0V2\<bar>RealXREAL-0M1", "s be  non negativeXXREAL-0V3\<bar>RealXREAL-0M1"
"cluster s *XCMPLX-0K3 r as-term-is  non positiveXXREAL-0V2"
proof
(*coherence*)
  show "s *XCMPLX-0K3 r be  non positiveXXREAL-0V2"
     sorry
qed "sorry"

mtheorem xreal_0_cl_34:
  mlet "r be  non positiveXXREAL-0V2\<bar>RealXREAL-0M1", "s be  non positiveXXREAL-0V2\<bar>RealXREAL-0M1"
"cluster r *XCMPLX-0K3 s as-term-is  non negativeXXREAL-0V3"
proof
(*coherence*)
  show "r *XCMPLX-0K3 s be  non negativeXXREAL-0V3"
sorry
qed "sorry"

mtheorem xreal_0_cl_35:
  mlet "r be  non negativeXXREAL-0V3\<bar>RealXREAL-0M1", "s be  non negativeXXREAL-0V3\<bar>RealXREAL-0M1"
"cluster r *XCMPLX-0K3 s as-term-is  non negativeXXREAL-0V3"
proof
(*coherence*)
  show "r *XCMPLX-0K3 s be  non negativeXXREAL-0V3"
sorry
qed "sorry"

mtheorem xreal_0_cl_36:
  mlet "r be positiveXXREAL-0V2\<bar>RealXREAL-0M1"
"cluster r \<inverse>XCMPLX-0K5 as-term-is positiveXXREAL-0V2"
proof
(*coherence*)
  show "r \<inverse>XCMPLX-0K5 be positiveXXREAL-0V2"
sorry
qed "sorry"

mtheorem xreal_0_cl_37:
  mlet "r be  non positiveXXREAL-0V2\<bar>RealXREAL-0M1"
"cluster r \<inverse>XCMPLX-0K5 as-term-is  non positiveXXREAL-0V2"
proof
(*coherence*)
  show "r \<inverse>XCMPLX-0K5 be  non positiveXXREAL-0V2"
sorry
qed "sorry"

mtheorem xreal_0_cl_38:
  mlet "r be negativeXXREAL-0V3\<bar>RealXREAL-0M1"
"cluster r \<inverse>XCMPLX-0K5 as-term-is negativeXXREAL-0V3"
proof
(*coherence*)
  show "r \<inverse>XCMPLX-0K5 be negativeXXREAL-0V3"
     sorry
qed "sorry"

mtheorem xreal_0_cl_39:
  mlet "r be  non negativeXXREAL-0V3\<bar>RealXREAL-0M1"
"cluster r \<inverse>XCMPLX-0K5 as-term-is  non negativeXXREAL-0V3"
proof
(*coherence*)
  show "r \<inverse>XCMPLX-0K5 be  non negativeXXREAL-0V3"
sorry
qed "sorry"

mtheorem xreal_0_cl_40:
  mlet "r be  non negativeXXREAL-0V3\<bar>RealXREAL-0M1", "s be  non positiveXXREAL-0V2\<bar>RealXREAL-0M1"
"cluster r /XCMPLX-0K7 s as-term-is  non positiveXXREAL-0V2"
proof
(*coherence*)
  show "r /XCMPLX-0K7 s be  non positiveXXREAL-0V2"
     sorry
qed "sorry"

mtheorem xreal_0_cl_41:
  mlet "r be  non negativeXXREAL-0V3\<bar>RealXREAL-0M1", "s be  non positiveXXREAL-0V2\<bar>RealXREAL-0M1"
"cluster s /XCMPLX-0K7 r as-term-is  non positiveXXREAL-0V2"
proof
(*coherence*)
  show "s /XCMPLX-0K7 r be  non positiveXXREAL-0V2"
     sorry
qed "sorry"

mtheorem xreal_0_cl_42:
  mlet "r be  non negativeXXREAL-0V3\<bar>RealXREAL-0M1", "s be  non negativeXXREAL-0V3\<bar>RealXREAL-0M1"
"cluster r /XCMPLX-0K7 s as-term-is  non negativeXXREAL-0V3"
proof
(*coherence*)
  show "r /XCMPLX-0K7 s be  non negativeXXREAL-0V3"
     sorry
qed "sorry"

mtheorem xreal_0_cl_43:
  mlet "r be  non positiveXXREAL-0V2\<bar>RealXREAL-0M1", "s be  non positiveXXREAL-0V2\<bar>RealXREAL-0M1"
"cluster r /XCMPLX-0K7 s as-term-is  non negativeXXREAL-0V3"
proof
(*coherence*)
  show "r /XCMPLX-0K7 s be  non negativeXXREAL-0V3"
     sorry
qed "sorry"

(*begin*)
mtheorem xreal_0_cl_44:
  mlet "r be RealXREAL-0M1", "s be RealXREAL-0M1"
"cluster minXXREAL-0K4(r,s) as-term-is realXREAL-0V1"
proof
(*coherence*)
  show "minXXREAL-0K4(r,s) be realXREAL-0V1"
    using xxreal_0_th_15 sorry
qed "sorry"

mtheorem xreal_0_cl_45:
  mlet "r be RealXREAL-0M1", "s be RealXREAL-0M1"
"cluster maxXXREAL-0K5(r,s) as-term-is realXREAL-0V1"
proof
(*coherence*)
  show "maxXXREAL-0K5(r,s) be realXREAL-0V1"
    using xxreal_0_th_16 sorry
qed "sorry"

mdef xreal_0_def_2 (" _ -''XREAL-0K1  _ " [132,132]132 ) where
  mlet "r be RealXREAL-0M1", "s be RealXREAL-0M1"
"func r -'XREAL-0K1 s \<rightarrow> setHIDDENM2 equals
  r -XCMPLX-0K6 s if r -XCMPLX-0K6 s >=XXREAL-0R2 0NUMBERSK6 otherwise 0NUMBERSK6"
proof-
  (*coherence*)
    show "(r -XCMPLX-0K6 s >=XXREAL-0R2 0NUMBERSK6 implies r -XCMPLX-0K6 s be setHIDDENM2) & ( not r -XCMPLX-0K6 s >=XXREAL-0R2 0NUMBERSK6 implies 0NUMBERSK6 be setHIDDENM2)"
       sorry
  (*consistency*)
    show " for it be setHIDDENM2 holds  True "
       sorry
qed "sorry"

mtheorem xreal_0_cl_46:
  mlet "r be RealXREAL-0M1", "s be RealXREAL-0M1"
"cluster r -'XREAL-0K1 s as-term-is realXREAL-0V1"
proof
(*coherence*)
  show "r -'XREAL-0K1 s be realXREAL-0V1"
sorry
qed "sorry"

mtheorem xreal_0_cl_47:
  mlet "r be RealXREAL-0M1", "s be RealXREAL-0M1"
"cluster r -'XREAL-0K1 s as-term-is  non negativeXXREAL-0V3 for RealXREAL-0M1"
proof
(*coherence*)
  show " for it be RealXREAL-0M1 holds it =HIDDENR1 r -'XREAL-0K1 s implies it be  non negativeXXREAL-0V3"
sorry
qed "sorry"

mtheorem
"cluster sethood of RealXREAL-0M1"
proof
(*sethood*)
  show " ex cover be setHIDDENM2 st  for it be RealXREAL-0M1 holds it inHIDDENR3 cover"
sorry
qed "sorry"

mtheorem xreal_0_reduce_1:
  mlet "i be RealXREAL-0M1"
"reduce InSUBSET-1K10(i,REALNUMBERSK2) to i"
proof
(*reducibility*)
  show "InSUBSET-1K10(i,REALNUMBERSK2) =HIDDENR1 i"
    using xreal_0_def_1 subset_1_def_8 sorry
qed "sorry"

end
