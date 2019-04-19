theory axioms
  imports xreal_0
   "../mizar_extension/E_number"
begin
(*begin*)
reserve r, s for "RealXREAL-0M1"
mlemma axioms_lm_1:
" for r be RealXREAL-0M1 holds  for s be RealXREAL-0M1 holds ((r inHIDDENR3 REAL+ARYTM-2K2 & s inHIDDENR3 REAL+ARYTM-2K2) & ( ex x9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st  ex y9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st (r =HIDDENR1 x9 & s =HIDDENR1 y9) & x9 <='ARYTM-2R1 y9) or (r inHIDDENR3 [:ZFMISC-1K2 {TARSKIK1 0NUMBERSK6 },REAL+ARYTM-2K2 :] & s inHIDDENR3 [:ZFMISC-1K2 {TARSKIK1 0NUMBERSK6 },REAL+ARYTM-2K2 :]) & ( ex x9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st  ex y9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st (r =HIDDENR1 [TARSKIK4 0NUMBERSK6,x9 ] & s =HIDDENR1 [TARSKIK4 0NUMBERSK6,y9 ]) & y9 <='ARYTM-2R1 x9)) or s inHIDDENR3 REAL+ARYTM-2K2 & r inHIDDENR3 [:ZFMISC-1K2 {TARSKIK1 0NUMBERSK6 },REAL+ARYTM-2K2 :] implies r <=XXREAL-0R1 s"
sorry

reserve x, y, z for "RealXREAL-0M1"
mlemma axioms_lm_2:
" for x be RealXREAL-0M1 holds  for x1 be ElementSUBSET-1M1-of REALNUMBERSK2 holds  for x2 be ElementSUBSET-1M1-of REALNUMBERSK2 holds x =HIDDENR1 [*ARYTM-0K5 x1,x2 *] implies x2 =XBOOLE-0R4 0NUMBERSK6 & x =HIDDENR1 x1"
sorry

mlemma axioms_lm_3:
" for x9 be ElementSUBSET-1M1-of REALNUMBERSK2 holds  for y9 be ElementSUBSET-1M1-of REALNUMBERSK2 holds  for x be RealXREAL-0M1 holds  for y be RealXREAL-0M1 holds x9 =HIDDENR1 x & y9 =HIDDENR1 y implies +ARYTM-0K1(x9,y9) =XBOOLE-0R4 x +XCMPLX-0K2 y"
sorry

mlemma axioms_lm_4:
"{}XBOOLE-0K1 inTARSKIR2 {TARSKIK1 {}XBOOLE-0K1 }"
  using tarski_def_1 sorry

reserve r, r1, r2 for "ElementSUBSET-1M1-of REAL+ARYTM-2K2"
mtheorem axioms_th_1:
" for X be SubsetSUBSET-1M2-of REALNUMBERSK2 holds  for Y be SubsetSUBSET-1M2-of REALNUMBERSK2 holds ( for x be RealXREAL-0M1 holds  for y be RealXREAL-0M1 holds x inHIDDENR3 X & y inHIDDENR3 Y implies x <=XXREAL-0R1 y) implies ( ex z be RealXREAL-0M1 st  for x be RealXREAL-0M1 holds  for y be RealXREAL-0M1 holds x inHIDDENR3 X & y inHIDDENR3 Y implies x <=XXREAL-0R1 z & z <=XXREAL-0R1 y)"
sorry

mtheorem axioms_th_2:
" for x be RealXREAL-0M1 holds  for y be RealXREAL-0M1 holds x inHIDDENR3 NATNUMBERSK1 & y inHIDDENR3 NATNUMBERSK1 implies x +XCMPLX-0K2 y inTARSKIR2 NATNUMBERSK1"
sorry

mtheorem axioms_th_3:
" for A be SubsetSUBSET-1M2-of REALNUMBERSK2 holds 0NUMBERSK6 inTARSKIR2 A & ( for x be RealXREAL-0M1 holds x inHIDDENR3 A implies x +XCMPLX-0K2 \<one>\<^sub>M inTARSKIR2 A) implies NATNUMBERSK1 c=TARSKIR1 A"
sorry

mtheorem axioms_th_4:
" for k be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds k =HIDDENR1 {i where i be NatORDINAL1M6 : i <XXREAL-0R3 k }"
sorry

end
