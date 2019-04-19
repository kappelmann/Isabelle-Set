theory xreal_1
  imports arytm_0 xcmplx_1
   "../mizar_extension/E_number"
begin
(*begin*)
reserve a, b, c, d for "RealXREAL-0M1"
reserve r, s for "RealXREAL-0M1"
mlemma xreal_1_lm_1:
" for r be RealXREAL-0M1 holds  for s be RealXREAL-0M1 holds ((r inHIDDENR3 REAL+ARYTM-2K2 & s inHIDDENR3 REAL+ARYTM-2K2) & ( ex x9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st  ex y9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st (r =HIDDENR1 x9 & s =HIDDENR1 y9) & x9 <='ARYTM-2R1 y9) or (r inHIDDENR3 [:ZFMISC-1K2 {TARSKIK1 0NUMBERSK6 },REAL+ARYTM-2K2 :] & s inHIDDENR3 [:ZFMISC-1K2 {TARSKIK1 0NUMBERSK6 },REAL+ARYTM-2K2 :]) & ( ex x9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st  ex y9 be ElementSUBSET-1M1-of REAL+ARYTM-2K2 st (r =HIDDENR1 [TARSKIK4 0NUMBERSK6,x9 ] & s =HIDDENR1 [TARSKIK4 0NUMBERSK6,y9 ]) & y9 <='ARYTM-2R1 x9)) or s inHIDDENR3 REAL+ARYTM-2K2 & r inHIDDENR3 [:ZFMISC-1K2 {TARSKIK1 0NUMBERSK6 },REAL+ARYTM-2K2 :] implies r <=XXREAL-0R1 s"
sorry

mlemma xreal_1_lm_2:
" for a be RealXREAL-0M1 holds  for x1 be ElementSUBSET-1M1-of REALNUMBERSK2 holds  for x2 be ElementSUBSET-1M1-of REALNUMBERSK2 holds a =HIDDENR1 [*ARYTM-0K5 x1,x2 *] implies x2 =XBOOLE-0R4 0NUMBERSK6 & a =HIDDENR1 x1"
sorry

mlemma xreal_1_lm_3:
" for a9 be ElementSUBSET-1M1-of REALNUMBERSK2 holds  for b9 be ElementSUBSET-1M1-of REALNUMBERSK2 holds  for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds a9 =HIDDENR1 a & b9 =HIDDENR1 b implies +ARYTM-0K1(a9,b9) =XBOOLE-0R4 a +XCMPLX-0K2 b"
sorry

mlemma xreal_1_lm_4:
"{}XBOOLE-0K1 inTARSKIR2 {TARSKIK1 {}XBOOLE-0K1 }"
  using tarski_def_1 sorry

mlemma xreal_1_lm_5:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds a <=XXREAL-0R1 b implies a +XCMPLX-0K2 c <=XXREAL-0R1 b +XCMPLX-0K2 c"
sorry

mlemma xreal_1_lm_6:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds  for d be RealXREAL-0M1 holds a <=XXREAL-0R1 b & c <=XXREAL-0R1 d implies a +XCMPLX-0K2 c <=XXREAL-0R1 b +XCMPLX-0K2 d"
sorry

mlemma xreal_1_lm_7:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds a <=XXREAL-0R1 b implies a -XCMPLX-0K6 c <=XXREAL-0R1 b -XCMPLX-0K6 c"
sorry

mlemma xreal_1_lm_8:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds  for d be RealXREAL-0M1 holds a <XXREAL-0R3 b & c <=XXREAL-0R1 d implies a +XCMPLX-0K2 c <XXREAL-0R3 b +XCMPLX-0K2 d"
sorry

mlemma xreal_1_lm_9:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds 0NUMBERSK6 <XXREAL-0R3 a implies b <XXREAL-0R3 b +XCMPLX-0K2 a"
sorry

mtheorem xreal_1_th_1:
" for a be RealXREAL-0M1 holds  ex b be RealXREAL-0M1 st a <XXREAL-0R3 b"
sorry

mtheorem xreal_1_th_2:
" for a be RealXREAL-0M1 holds  ex b be RealXREAL-0M1 st b <XXREAL-0R3 a"
sorry

mtheorem xreal_1_th_3:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  ex c be RealXREAL-0M1 st a <XXREAL-0R3 c & b <XXREAL-0R3 c"
sorry

mlemma xreal_1_lm_10:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds a +XCMPLX-0K2 c <=XXREAL-0R1 b +XCMPLX-0K2 c implies a <=XXREAL-0R1 b"
sorry

mtheorem xreal_1_th_4:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  ex c be RealXREAL-0M1 st c <XXREAL-0R3 a & c <XXREAL-0R3 b"
sorry

mlemma xreal_1_lm_11:
" for a9 be ElementSUBSET-1M1-of REALNUMBERSK2 holds  for b9 be ElementSUBSET-1M1-of REALNUMBERSK2 holds  for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds a9 =HIDDENR1 a & b9 =HIDDENR1 b implies  *ARYTM-0K2(a9,b9) =XBOOLE-0R4 a *XCMPLX-0K3 b"
sorry

mlemma xreal_1_lm_12:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds a <=XXREAL-0R1 b & 0NUMBERSK6 <=XXREAL-0R1 c implies a *XCMPLX-0K3 c <=XXREAL-0R1 b *XCMPLX-0K3 c"
sorry

mlemma xreal_1_lm_13:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds 0NUMBERSK6 <XXREAL-0R3 c & a <XXREAL-0R3 b implies a *XCMPLX-0K3 c <XXREAL-0R3 b *XCMPLX-0K3 c"
sorry

mtheorem xreal_1_th_5:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds a <XXREAL-0R3 b implies ( ex c be RealXREAL-0M1 st a <XXREAL-0R3 c & c <XXREAL-0R3 b)"
sorry

(*begin*)
mtheorem xreal_1_th_6:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds a <=XXREAL-0R1 b iff a +XCMPLX-0K2 c <=XXREAL-0R1 b +XCMPLX-0K2 c"
  using xreal_1_lm_5 xreal_1_lm_10 sorry

mtheorem xreal_1_th_7:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds  for d be RealXREAL-0M1 holds a <=XXREAL-0R1 b & c <=XXREAL-0R1 d implies a +XCMPLX-0K2 c <=XXREAL-0R1 b +XCMPLX-0K2 d"
  using xreal_1_lm_6 sorry

mtheorem xreal_1_th_8:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds  for d be RealXREAL-0M1 holds a <XXREAL-0R3 b & c <=XXREAL-0R1 d implies a +XCMPLX-0K2 c <XXREAL-0R3 b +XCMPLX-0K2 d"
  using xreal_1_lm_8 sorry

mlemma xreal_1_lm_14:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds a <=XXREAL-0R1 b implies -XCMPLX-0K4 b <=XXREAL-0R1 -XCMPLX-0K4 a"
sorry

mlemma xreal_1_lm_15:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds -XCMPLX-0K4 b <=XXREAL-0R1 -XCMPLX-0K4 a implies a <=XXREAL-0R1 b"
sorry

(*begin*)
mtheorem xreal_1_th_9:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds a <=XXREAL-0R1 b iff a -XCMPLX-0K6 c <=XXREAL-0R1 b -XCMPLX-0K6 c"
sorry

mtheorem xreal_1_th_10:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds a <=XXREAL-0R1 b iff c -XCMPLX-0K6 b <=XXREAL-0R1 c -XCMPLX-0K6 a"
sorry

mlemma xreal_1_lm_16:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds a +XCMPLX-0K2 b <=XXREAL-0R1 c implies a <=XXREAL-0R1 c -XCMPLX-0K6 b"
sorry

mlemma xreal_1_lm_17:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds a <=XXREAL-0R1 b -XCMPLX-0K6 c implies a +XCMPLX-0K2 c <=XXREAL-0R1 b"
sorry

mlemma xreal_1_lm_18:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds a <=XXREAL-0R1 b +XCMPLX-0K2 c implies a -XCMPLX-0K6 b <=XXREAL-0R1 c"
sorry

mlemma xreal_1_lm_19:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds a -XCMPLX-0K6 b <=XXREAL-0R1 c implies a <=XXREAL-0R1 b +XCMPLX-0K2 c"
sorry

mtheorem xreal_1_th_11:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds a <=XXREAL-0R1 b -XCMPLX-0K6 c implies c <=XXREAL-0R1 b -XCMPLX-0K6 a"
sorry

mtheorem xreal_1_th_12:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds a -XCMPLX-0K6 b <=XXREAL-0R1 c implies a -XCMPLX-0K6 c <=XXREAL-0R1 b"
sorry

mtheorem xreal_1_th_13:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds  for d be RealXREAL-0M1 holds a <=XXREAL-0R1 b & c <=XXREAL-0R1 d implies a -XCMPLX-0K6 d <=XXREAL-0R1 b -XCMPLX-0K6 c"
sorry

mtheorem xreal_1_th_14:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds  for d be RealXREAL-0M1 holds a <XXREAL-0R3 b & c <=XXREAL-0R1 d implies a -XCMPLX-0K6 d <XXREAL-0R3 b -XCMPLX-0K6 c"
sorry

mtheorem xreal_1_th_15:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds  for d be RealXREAL-0M1 holds a <=XXREAL-0R1 b & c <XXREAL-0R3 d implies a -XCMPLX-0K6 d <XXREAL-0R3 b -XCMPLX-0K6 c"
sorry

mlemma xreal_1_lm_20:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds  for d be RealXREAL-0M1 holds a +XCMPLX-0K2 b <=XXREAL-0R1 c +XCMPLX-0K2 d implies a -XCMPLX-0K6 c <=XXREAL-0R1 d -XCMPLX-0K6 b"
sorry

mtheorem xreal_1_th_16:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds  for d be RealXREAL-0M1 holds a -XCMPLX-0K6 b <=XXREAL-0R1 c -XCMPLX-0K6 d implies a -XCMPLX-0K6 c <=XXREAL-0R1 b -XCMPLX-0K6 d"
sorry

mtheorem xreal_1_th_17:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds  for d be RealXREAL-0M1 holds a -XCMPLX-0K6 b <=XXREAL-0R1 c -XCMPLX-0K6 d implies d -XCMPLX-0K6 b <=XXREAL-0R1 c -XCMPLX-0K6 a"
sorry

mtheorem xreal_1_th_18:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds  for d be RealXREAL-0M1 holds a -XCMPLX-0K6 b <=XXREAL-0R1 c -XCMPLX-0K6 d implies d -XCMPLX-0K6 c <=XXREAL-0R1 b -XCMPLX-0K6 a"
sorry

(*begin*)
mtheorem xreal_1_th_19:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds a +XCMPLX-0K2 b <=XXREAL-0R1 c iff a <=XXREAL-0R1 c -XCMPLX-0K6 b"
  using xreal_1_lm_16 xreal_1_lm_17 sorry

mtheorem xreal_1_th_20:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds a <=XXREAL-0R1 b +XCMPLX-0K2 c iff a -XCMPLX-0K6 b <=XXREAL-0R1 c"
  using xreal_1_lm_18 xreal_1_lm_19 sorry

mtheorem xreal_1_th_21:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds  for d be RealXREAL-0M1 holds a +XCMPLX-0K2 b <=XXREAL-0R1 c +XCMPLX-0K2 d iff a -XCMPLX-0K6 c <=XXREAL-0R1 d -XCMPLX-0K6 b"
sorry

mtheorem xreal_1_th_22:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds  for d be RealXREAL-0M1 holds a +XCMPLX-0K2 b <=XXREAL-0R1 c -XCMPLX-0K6 d implies a +XCMPLX-0K2 d <=XXREAL-0R1 c -XCMPLX-0K6 b"
sorry

mtheorem xreal_1_th_23:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds  for d be RealXREAL-0M1 holds a -XCMPLX-0K6 b <=XXREAL-0R1 c +XCMPLX-0K2 d implies a -XCMPLX-0K6 d <=XXREAL-0R1 c +XCMPLX-0K2 b"
sorry

(*begin*)
mtheorem xreal_1_th_24:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds a <=XXREAL-0R1 b iff -XCMPLX-0K4 b <=XXREAL-0R1 -XCMPLX-0K4 a"
  using xreal_1_lm_14 xreal_1_lm_15 sorry

mlemma xreal_1_lm_21:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds a <XXREAL-0R3 b implies 0NUMBERSK6 <XXREAL-0R3 b -XCMPLX-0K6 a"
sorry

mtheorem xreal_1_th_25:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds a <=XXREAL-0R1 -XCMPLX-0K4 b implies b <=XXREAL-0R1 -XCMPLX-0K4 a"
sorry

mlemma xreal_1_lm_22:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds a <=XXREAL-0R1 b implies 0NUMBERSK6 <=XXREAL-0R1 b -XCMPLX-0K6 a"
sorry

mtheorem xreal_1_th_26:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds -XCMPLX-0K4 b <=XXREAL-0R1 a implies -XCMPLX-0K4 a <=XXREAL-0R1 b"
sorry

(*begin*)
mtheorem xreal_1_th_27:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds (0NUMBERSK6 <=XXREAL-0R1 a & 0NUMBERSK6 <=XXREAL-0R1 b) & a +XCMPLX-0K2 b =XBOOLE-0R4 0NUMBERSK6 implies a =HIDDENR1 0NUMBERSK6"
   sorry

mtheorem xreal_1_th_28:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds (a <=XXREAL-0R1 0NUMBERSK6 & b <=XXREAL-0R1 0NUMBERSK6) & a +XCMPLX-0K2 b =XBOOLE-0R4 0NUMBERSK6 implies a =HIDDENR1 0NUMBERSK6"
   sorry

(*begin*)
mtheorem xreal_1_th_29:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds 0NUMBERSK6 <XXREAL-0R3 a implies b <XXREAL-0R3 b +XCMPLX-0K2 a"
  using xreal_1_lm_9 sorry

mtheorem xreal_1_th_30:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds a <XXREAL-0R3 0NUMBERSK6 implies a +XCMPLX-0K2 b <XXREAL-0R3 b"
sorry

mlemma xreal_1_lm_23:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds a <XXREAL-0R3 b implies a -XCMPLX-0K6 b <XXREAL-0R3 0NUMBERSK6"
sorry

mtheorem xreal_1_th_31:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds 0NUMBERSK6 <=XXREAL-0R1 a implies b <=XXREAL-0R1 a +XCMPLX-0K2 b"
sorry

mtheorem xreal_1_th_32:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds a <=XXREAL-0R1 0NUMBERSK6 implies a +XCMPLX-0K2 b <=XXREAL-0R1 b"
sorry

(*begin*)
mtheorem xreal_1_th_33:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds 0NUMBERSK6 <=XXREAL-0R1 a & 0NUMBERSK6 <=XXREAL-0R1 b implies 0NUMBERSK6 <=XXREAL-0R1 a +XCMPLX-0K2 b"
   sorry

mtheorem xreal_1_th_34:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds 0NUMBERSK6 <=XXREAL-0R1 a & 0NUMBERSK6 <XXREAL-0R3 b implies 0NUMBERSK6 <XXREAL-0R3 a +XCMPLX-0K2 b"
   sorry

mtheorem xreal_1_th_35:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds a <=XXREAL-0R1 0NUMBERSK6 & c <=XXREAL-0R1 b implies c +XCMPLX-0K2 a <=XXREAL-0R1 b"
sorry

mtheorem xreal_1_th_36:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds a <=XXREAL-0R1 0NUMBERSK6 & c <XXREAL-0R3 b implies c +XCMPLX-0K2 a <XXREAL-0R3 b"
sorry

mtheorem xreal_1_th_37:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds a <XXREAL-0R3 0NUMBERSK6 & c <=XXREAL-0R1 b implies c +XCMPLX-0K2 a <XXREAL-0R3 b"
sorry

mtheorem xreal_1_th_38:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds 0NUMBERSK6 <=XXREAL-0R1 a & b <=XXREAL-0R1 c implies b <=XXREAL-0R1 a +XCMPLX-0K2 c"
sorry

mtheorem xreal_1_th_39:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds 0NUMBERSK6 <XXREAL-0R3 a & b <=XXREAL-0R1 c implies b <XXREAL-0R3 a +XCMPLX-0K2 c"
sorry

mtheorem xreal_1_th_40:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds 0NUMBERSK6 <=XXREAL-0R1 a & b <XXREAL-0R3 c implies b <XXREAL-0R3 a +XCMPLX-0K2 c"
sorry

mlemma xreal_1_lm_24:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds c <XXREAL-0R3 0NUMBERSK6 & a <XXREAL-0R3 b implies b *XCMPLX-0K3 c <XXREAL-0R3 a *XCMPLX-0K3 c"
sorry

mlemma xreal_1_lm_25:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds 0NUMBERSK6 <=XXREAL-0R1 c & b <=XXREAL-0R1 a implies b /XCMPLX-0K7 c <=XXREAL-0R1 a /XCMPLX-0K7 c"
sorry

mlemma xreal_1_lm_26:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds 0NUMBERSK6 <XXREAL-0R3 c & a <XXREAL-0R3 b implies a /XCMPLX-0K7 c <XXREAL-0R3 b /XCMPLX-0K7 c"
sorry

mlemma xreal_1_lm_27:
" for a be RealXREAL-0M1 holds 0NUMBERSK6 <XXREAL-0R3 a implies a /XCMPLX-0K7 \<two>\<^sub>M <XXREAL-0R3 a"
sorry

(*begin*)
mtheorem xreal_1_th_41:
" for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds ( for a be RealXREAL-0M1 holds a >XXREAL-0R4 0NUMBERSK6 implies c <=XXREAL-0R1 b +XCMPLX-0K2 a) implies c <=XXREAL-0R1 b"
sorry

mtheorem xreal_1_th_42:
" for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds ( for a be RealXREAL-0M1 holds a <XXREAL-0R3 0NUMBERSK6 implies b +XCMPLX-0K2 a <=XXREAL-0R1 c) implies b <=XXREAL-0R1 c"
sorry

(*begin*)
mtheorem xreal_1_th_43:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds 0NUMBERSK6 <=XXREAL-0R1 a implies b -XCMPLX-0K6 a <=XXREAL-0R1 b"
sorry

mtheorem xreal_1_th_44:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds 0NUMBERSK6 <XXREAL-0R3 a implies b -XCMPLX-0K6 a <XXREAL-0R3 b"
sorry

mtheorem xreal_1_th_45:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds a <=XXREAL-0R1 0NUMBERSK6 implies b <=XXREAL-0R1 b -XCMPLX-0K6 a"
sorry

mtheorem xreal_1_th_46:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds a <XXREAL-0R3 0NUMBERSK6 implies b <XXREAL-0R3 b -XCMPLX-0K6 a"
sorry

mtheorem xreal_1_th_47:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds a <=XXREAL-0R1 b implies a -XCMPLX-0K6 b <=XXREAL-0R1 0NUMBERSK6"
sorry

mtheorem xreal_1_th_48:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds a <=XXREAL-0R1 b implies 0NUMBERSK6 <=XXREAL-0R1 b -XCMPLX-0K6 a"
sorry

mtheorem xreal_1_th_49:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds a <XXREAL-0R3 b implies a -XCMPLX-0K6 b <XXREAL-0R3 0NUMBERSK6"
  using xreal_1_lm_23 sorry

mtheorem xreal_1_th_50:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds a <XXREAL-0R3 b implies 0NUMBERSK6 <XXREAL-0R3 b -XCMPLX-0K6 a"
  using xreal_1_lm_21 sorry

mtheorem xreal_1_th_51:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds 0NUMBERSK6 <=XXREAL-0R1 a & b <XXREAL-0R3 c implies b -XCMPLX-0K6 a <XXREAL-0R3 c"
sorry

mtheorem xreal_1_th_52:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds a <=XXREAL-0R1 0NUMBERSK6 & b <=XXREAL-0R1 c implies b <=XXREAL-0R1 c -XCMPLX-0K6 a"
sorry

mtheorem xreal_1_th_53:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds a <=XXREAL-0R1 0NUMBERSK6 & b <XXREAL-0R3 c implies b <XXREAL-0R3 c -XCMPLX-0K6 a"
sorry

mtheorem xreal_1_th_54:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds a <XXREAL-0R3 0NUMBERSK6 & b <=XXREAL-0R1 c implies b <XXREAL-0R3 c -XCMPLX-0K6 a"
sorry

mtheorem xreal_1_th_55:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds a <>HIDDENR2 b implies 0NUMBERSK6 <XXREAL-0R3 a -XCMPLX-0K6 b or 0NUMBERSK6 <XXREAL-0R3 b -XCMPLX-0K6 a"
sorry

(*begin*)
mtheorem xreal_1_th_56:
" for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds ( for a be RealXREAL-0M1 holds a <XXREAL-0R3 0NUMBERSK6 implies c <=XXREAL-0R1 b -XCMPLX-0K6 a) implies b >=XXREAL-0R2 c"
sorry

mtheorem xreal_1_th_57:
" for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds ( for a be RealXREAL-0M1 holds a >XXREAL-0R4 0NUMBERSK6 implies b -XCMPLX-0K6 a <=XXREAL-0R1 c) implies b <=XXREAL-0R1 c"
sorry

(*begin*)
mtheorem xreal_1_th_58:
" for a be RealXREAL-0M1 holds a <XXREAL-0R3 0NUMBERSK6 iff 0NUMBERSK6 <XXREAL-0R3 -XCMPLX-0K4 a"
   sorry

mtheorem xreal_1_th_59:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds a <=XXREAL-0R1 -XCMPLX-0K4 b implies a +XCMPLX-0K2 b <=XXREAL-0R1 0NUMBERSK6"
sorry

mtheorem xreal_1_th_60:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds -XCMPLX-0K4 a <=XXREAL-0R1 b implies 0NUMBERSK6 <=XXREAL-0R1 a +XCMPLX-0K2 b"
sorry

mtheorem xreal_1_th_61:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds a <XXREAL-0R3 -XCMPLX-0K4 b implies a +XCMPLX-0K2 b <XXREAL-0R3 0NUMBERSK6"
sorry

mtheorem xreal_1_th_62:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds -XCMPLX-0K4 b <XXREAL-0R3 a implies 0NUMBERSK6 <XXREAL-0R3 a +XCMPLX-0K2 b"
sorry

mlemma xreal_1_lm_28:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds a <=XXREAL-0R1 b & c <=XXREAL-0R1 0NUMBERSK6 implies b *XCMPLX-0K3 c <=XXREAL-0R1 a *XCMPLX-0K3 c"
sorry

(*begin*)
mtheorem xreal_1_th_63:
" for a be RealXREAL-0M1 holds 0NUMBERSK6 <=XXREAL-0R1 a *XCMPLX-0K3 a"
sorry

mtheorem xreal_1_th_64:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds a <=XXREAL-0R1 b & 0NUMBERSK6 <=XXREAL-0R1 c implies a *XCMPLX-0K3 c <=XXREAL-0R1 b *XCMPLX-0K3 c"
  using xreal_1_lm_12 sorry

mtheorem xreal_1_th_65:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds a <=XXREAL-0R1 b & c <=XXREAL-0R1 0NUMBERSK6 implies b *XCMPLX-0K3 c <=XXREAL-0R1 a *XCMPLX-0K3 c"
  using xreal_1_lm_28 sorry

mtheorem xreal_1_th_66:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds  for d be RealXREAL-0M1 holds ((0NUMBERSK6 <=XXREAL-0R1 a & a <=XXREAL-0R1 b) & 0NUMBERSK6 <=XXREAL-0R1 c) & c <=XXREAL-0R1 d implies a *XCMPLX-0K3 c <=XXREAL-0R1 b *XCMPLX-0K3 d"
sorry

mtheorem xreal_1_th_67:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds  for d be RealXREAL-0M1 holds ((a <=XXREAL-0R1 0NUMBERSK6 & b <=XXREAL-0R1 a) & c <=XXREAL-0R1 0NUMBERSK6) & d <=XXREAL-0R1 c implies a *XCMPLX-0K3 c <=XXREAL-0R1 b *XCMPLX-0K3 d"
sorry

mtheorem xreal_1_th_68:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds 0NUMBERSK6 <XXREAL-0R3 c & a <XXREAL-0R3 b implies a *XCMPLX-0K3 c <XXREAL-0R3 b *XCMPLX-0K3 c"
  using xreal_1_lm_13 sorry

mtheorem xreal_1_th_69:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds c <XXREAL-0R3 0NUMBERSK6 & a <XXREAL-0R3 b implies b *XCMPLX-0K3 c <XXREAL-0R3 a *XCMPLX-0K3 c"
  using xreal_1_lm_24 sorry

mtheorem xreal_1_th_70:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds  for d be RealXREAL-0M1 holds ((a <XXREAL-0R3 0NUMBERSK6 & b <=XXREAL-0R1 a) & c <XXREAL-0R3 0NUMBERSK6) & d <XXREAL-0R3 c implies a *XCMPLX-0K3 c <XXREAL-0R3 b *XCMPLX-0K3 d"
sorry

(*begin*)
mtheorem xreal_1_th_71:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds  for d be RealXREAL-0M1 holds (((0NUMBERSK6 <=XXREAL-0R1 a & 0NUMBERSK6 <=XXREAL-0R1 b) & 0NUMBERSK6 <=XXREAL-0R1 c) & 0NUMBERSK6 <=XXREAL-0R1 d) & a *XCMPLX-0K3 c +XCMPLX-0K2 b *XCMPLX-0K3 d =XBOOLE-0R4 0NUMBERSK6 implies a =HIDDENR1 0NUMBERSK6 or c =HIDDENR1 0NUMBERSK6"
   sorry

mlemma xreal_1_lm_29:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds c <XXREAL-0R3 0NUMBERSK6 & a <XXREAL-0R3 b implies b /XCMPLX-0K7 c <XXREAL-0R3 a /XCMPLX-0K7 c"
sorry

mlemma xreal_1_lm_30:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds c <=XXREAL-0R1 0NUMBERSK6 & b /XCMPLX-0K7 c <XXREAL-0R3 a /XCMPLX-0K7 c implies a <XXREAL-0R3 b"
sorry

(*begin*)
mtheorem xreal_1_th_72:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds 0NUMBERSK6 <=XXREAL-0R1 c & b <=XXREAL-0R1 a implies b /XCMPLX-0K7 c <=XXREAL-0R1 a /XCMPLX-0K7 c"
  using xreal_1_lm_25 sorry

mtheorem xreal_1_th_73:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds c <=XXREAL-0R1 0NUMBERSK6 & a <=XXREAL-0R1 b implies b /XCMPLX-0K7 c <=XXREAL-0R1 a /XCMPLX-0K7 c"
  using xreal_1_lm_30 sorry

mtheorem xreal_1_th_74:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds 0NUMBERSK6 <XXREAL-0R3 c & a <XXREAL-0R3 b implies a /XCMPLX-0K7 c <XXREAL-0R3 b /XCMPLX-0K7 c"
  using xreal_1_lm_26 sorry

mtheorem xreal_1_th_75:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds c <XXREAL-0R3 0NUMBERSK6 & a <XXREAL-0R3 b implies b /XCMPLX-0K7 c <XXREAL-0R3 a /XCMPLX-0K7 c"
  using xreal_1_lm_29 sorry

mtheorem xreal_1_th_76:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds (0NUMBERSK6 <XXREAL-0R3 c & 0NUMBERSK6 <XXREAL-0R3 a) & a <XXREAL-0R3 b implies c /XCMPLX-0K7 b <XXREAL-0R3 c /XCMPLX-0K7 a"
sorry

mlemma xreal_1_lm_31:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds b <XXREAL-0R3 0NUMBERSK6 & a <XXREAL-0R3 b implies b \<inverse>XCMPLX-0K5 <XXREAL-0R3 a \<inverse>XCMPLX-0K5"
sorry

(*begin*)
mtheorem xreal_1_th_77:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds 0NUMBERSK6 <XXREAL-0R3 b & a *XCMPLX-0K3 b <=XXREAL-0R1 c implies a <=XXREAL-0R1 c /XCMPLX-0K7 b"
sorry

mtheorem xreal_1_th_78:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds b <XXREAL-0R3 0NUMBERSK6 & a *XCMPLX-0K3 b <=XXREAL-0R1 c implies c /XCMPLX-0K7 b <=XXREAL-0R1 a"
sorry

mtheorem xreal_1_th_79:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds 0NUMBERSK6 <XXREAL-0R3 b & c <=XXREAL-0R1 a *XCMPLX-0K3 b implies c /XCMPLX-0K7 b <=XXREAL-0R1 a"
sorry

mtheorem xreal_1_th_80:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds b <XXREAL-0R3 0NUMBERSK6 & c <=XXREAL-0R1 a *XCMPLX-0K3 b implies a <=XXREAL-0R1 c /XCMPLX-0K7 b"
sorry

mtheorem xreal_1_th_81:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds 0NUMBERSK6 <XXREAL-0R3 b & a *XCMPLX-0K3 b <XXREAL-0R3 c implies a <XXREAL-0R3 c /XCMPLX-0K7 b"
sorry

mtheorem xreal_1_th_82:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds b <XXREAL-0R3 0NUMBERSK6 & a *XCMPLX-0K3 b <XXREAL-0R3 c implies c /XCMPLX-0K7 b <XXREAL-0R3 a"
sorry

mtheorem xreal_1_th_83:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds 0NUMBERSK6 <XXREAL-0R3 b & c <XXREAL-0R3 a *XCMPLX-0K3 b implies c /XCMPLX-0K7 b <XXREAL-0R3 a"
sorry

mtheorem xreal_1_th_84:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds b <XXREAL-0R3 0NUMBERSK6 & c <XXREAL-0R3 a *XCMPLX-0K3 b implies a <XXREAL-0R3 c /XCMPLX-0K7 b"
sorry

mlemma xreal_1_lm_32:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds 0NUMBERSK6 <XXREAL-0R3 a & a <=XXREAL-0R1 b implies b \<inverse>XCMPLX-0K5 <=XXREAL-0R1 a \<inverse>XCMPLX-0K5"
sorry

mlemma xreal_1_lm_33:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds b <XXREAL-0R3 0NUMBERSK6 & a <=XXREAL-0R1 b implies b \<inverse>XCMPLX-0K5 <=XXREAL-0R1 a \<inverse>XCMPLX-0K5"
sorry

(*begin*)
mtheorem xreal_1_th_85:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds 0NUMBERSK6 <XXREAL-0R3 a & a <=XXREAL-0R1 b implies b \<inverse>XCMPLX-0K5 <=XXREAL-0R1 a \<inverse>XCMPLX-0K5"
  using xreal_1_lm_32 sorry

mtheorem xreal_1_th_86:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds b <XXREAL-0R3 0NUMBERSK6 & a <=XXREAL-0R1 b implies b \<inverse>XCMPLX-0K5 <=XXREAL-0R1 a \<inverse>XCMPLX-0K5"
  using xreal_1_lm_33 sorry

mtheorem xreal_1_th_87:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds b <XXREAL-0R3 0NUMBERSK6 & a <XXREAL-0R3 b implies b \<inverse>XCMPLX-0K5 <XXREAL-0R3 a \<inverse>XCMPLX-0K5"
  using xreal_1_lm_31 sorry

mlemma xreal_1_lm_34:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds 0NUMBERSK6 <XXREAL-0R3 a & a <XXREAL-0R3 b implies b \<inverse>XCMPLX-0K5 <XXREAL-0R3 a \<inverse>XCMPLX-0K5"
sorry

mtheorem xreal_1_th_88:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds 0NUMBERSK6 <XXREAL-0R3 a & a <XXREAL-0R3 b implies b \<inverse>XCMPLX-0K5 <XXREAL-0R3 a \<inverse>XCMPLX-0K5"
  using xreal_1_lm_34 sorry

mtheorem xreal_1_th_89:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds 0NUMBERSK6 <XXREAL-0R3 b \<inverse>XCMPLX-0K5 & b \<inverse>XCMPLX-0K5 <=XXREAL-0R1 a \<inverse>XCMPLX-0K5 implies a <=XXREAL-0R1 b"
sorry

mtheorem xreal_1_th_90:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds a \<inverse>XCMPLX-0K5 <XXREAL-0R3 0NUMBERSK6 & b \<inverse>XCMPLX-0K5 <=XXREAL-0R1 a \<inverse>XCMPLX-0K5 implies a <=XXREAL-0R1 b"
sorry

mtheorem xreal_1_th_91:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds 0NUMBERSK6 <XXREAL-0R3 b \<inverse>XCMPLX-0K5 & b \<inverse>XCMPLX-0K5 <XXREAL-0R3 a \<inverse>XCMPLX-0K5 implies a <XXREAL-0R3 b"
sorry

mtheorem xreal_1_th_92:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds a \<inverse>XCMPLX-0K5 <XXREAL-0R3 0NUMBERSK6 & b \<inverse>XCMPLX-0K5 <XXREAL-0R3 a \<inverse>XCMPLX-0K5 implies a <XXREAL-0R3 b"
sorry

mlemma xreal_1_lm_35:
" for b be RealXREAL-0M1 holds  for a be  non negativeXXREAL-0V3\<bar> non positiveXXREAL-0V2\<bar>RealXREAL-0M1 holds 0NUMBERSK6 =XBOOLE-0R4 a *XCMPLX-0K3 b"
   sorry

(*begin*)
mtheorem xreal_1_th_93:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds 0NUMBERSK6 <=XXREAL-0R1 a & (b -XCMPLX-0K6 a)*XCMPLX-0K3 (b +XCMPLX-0K2 a) <=XXREAL-0R1 0NUMBERSK6 implies -XCMPLX-0K4 a <=XXREAL-0R1 b & b <=XXREAL-0R1 a"
sorry

mtheorem xreal_1_th_94:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds 0NUMBERSK6 <=XXREAL-0R1 a & (b -XCMPLX-0K6 a)*XCMPLX-0K3 (b +XCMPLX-0K2 a) <XXREAL-0R3 0NUMBERSK6 implies -XCMPLX-0K4 a <XXREAL-0R3 b & b <XXREAL-0R3 a"
sorry

mtheorem xreal_1_th_95:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds 0NUMBERSK6 <=XXREAL-0R1 (b -XCMPLX-0K6 a)*XCMPLX-0K3 (b +XCMPLX-0K2 a) implies b <=XXREAL-0R1 -XCMPLX-0K4 a or a <=XXREAL-0R1 b"
sorry

mtheorem xreal_1_th_96:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds  for d be RealXREAL-0M1 holds ((0NUMBERSK6 <=XXREAL-0R1 a & 0NUMBERSK6 <=XXREAL-0R1 c) & a <XXREAL-0R3 b) & c <XXREAL-0R3 d implies a *XCMPLX-0K3 c <XXREAL-0R3 b *XCMPLX-0K3 d"
sorry

mtheorem xreal_1_th_97:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds  for d be RealXREAL-0M1 holds ((0NUMBERSK6 <=XXREAL-0R1 a & 0NUMBERSK6 <XXREAL-0R3 c) & a <XXREAL-0R3 b) & c <=XXREAL-0R1 d implies a *XCMPLX-0K3 c <XXREAL-0R3 b *XCMPLX-0K3 d"
sorry

mtheorem xreal_1_th_98:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds  for d be RealXREAL-0M1 holds ((0NUMBERSK6 <XXREAL-0R3 a & 0NUMBERSK6 <XXREAL-0R3 c) & a <=XXREAL-0R1 b) & c <XXREAL-0R3 d implies a *XCMPLX-0K3 c <XXREAL-0R3 b *XCMPLX-0K3 d"
sorry

mtheorem xreal_1_th_99:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds (0NUMBERSK6 <XXREAL-0R3 c & b <XXREAL-0R3 0NUMBERSK6) & a <XXREAL-0R3 b implies c /XCMPLX-0K7 b <XXREAL-0R3 c /XCMPLX-0K7 a"
sorry

mtheorem xreal_1_th_100:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds (c <XXREAL-0R3 0NUMBERSK6 & 0NUMBERSK6 <XXREAL-0R3 a) & a <XXREAL-0R3 b implies c /XCMPLX-0K7 a <XXREAL-0R3 c /XCMPLX-0K7 b"
sorry

mtheorem xreal_1_th_101:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds (c <XXREAL-0R3 0NUMBERSK6 & b <XXREAL-0R3 0NUMBERSK6) & a <XXREAL-0R3 b implies c /XCMPLX-0K7 a <XXREAL-0R3 c /XCMPLX-0K7 b"
sorry

mtheorem xreal_1_th_102:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds  for d be RealXREAL-0M1 holds (0NUMBERSK6 <XXREAL-0R3 b & 0NUMBERSK6 <XXREAL-0R3 d) & a *XCMPLX-0K3 d <=XXREAL-0R1 c *XCMPLX-0K3 b implies a /XCMPLX-0K7 b <=XXREAL-0R1 c /XCMPLX-0K7 d"
sorry

mtheorem xreal_1_th_103:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds  for d be RealXREAL-0M1 holds (b <XXREAL-0R3 0NUMBERSK6 & d <XXREAL-0R3 0NUMBERSK6) & a *XCMPLX-0K3 d <=XXREAL-0R1 c *XCMPLX-0K3 b implies a /XCMPLX-0K7 b <=XXREAL-0R1 c /XCMPLX-0K7 d"
sorry

mtheorem xreal_1_th_104:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds  for d be RealXREAL-0M1 holds (0NUMBERSK6 <XXREAL-0R3 b & d <XXREAL-0R3 0NUMBERSK6) & a *XCMPLX-0K3 d <=XXREAL-0R1 c *XCMPLX-0K3 b implies c /XCMPLX-0K7 d <=XXREAL-0R1 a /XCMPLX-0K7 b"
sorry

mtheorem xreal_1_th_105:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds  for d be RealXREAL-0M1 holds (b <XXREAL-0R3 0NUMBERSK6 & 0NUMBERSK6 <XXREAL-0R3 d) & a *XCMPLX-0K3 d <=XXREAL-0R1 c *XCMPLX-0K3 b implies c /XCMPLX-0K7 d <=XXREAL-0R1 a /XCMPLX-0K7 b"
sorry

mtheorem xreal_1_th_106:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds  for d be RealXREAL-0M1 holds (0NUMBERSK6 <XXREAL-0R3 b & 0NUMBERSK6 <XXREAL-0R3 d) & a *XCMPLX-0K3 d <XXREAL-0R3 c *XCMPLX-0K3 b implies a /XCMPLX-0K7 b <XXREAL-0R3 c /XCMPLX-0K7 d"
sorry

mtheorem xreal_1_th_107:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds  for d be RealXREAL-0M1 holds (b <XXREAL-0R3 0NUMBERSK6 & d <XXREAL-0R3 0NUMBERSK6) & a *XCMPLX-0K3 d <XXREAL-0R3 c *XCMPLX-0K3 b implies a /XCMPLX-0K7 b <XXREAL-0R3 c /XCMPLX-0K7 d"
sorry

mtheorem xreal_1_th_108:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds  for d be RealXREAL-0M1 holds (0NUMBERSK6 <XXREAL-0R3 b & d <XXREAL-0R3 0NUMBERSK6) & a *XCMPLX-0K3 d <XXREAL-0R3 c *XCMPLX-0K3 b implies c /XCMPLX-0K7 d <XXREAL-0R3 a /XCMPLX-0K7 b"
sorry

mtheorem xreal_1_th_109:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds  for d be RealXREAL-0M1 holds (b <XXREAL-0R3 0NUMBERSK6 & 0NUMBERSK6 <XXREAL-0R3 d) & a *XCMPLX-0K3 d <XXREAL-0R3 c *XCMPLX-0K3 b implies c /XCMPLX-0K7 d <XXREAL-0R3 a /XCMPLX-0K7 b"
sorry

mtheorem xreal_1_th_110:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds  for d be RealXREAL-0M1 holds (b <XXREAL-0R3 0NUMBERSK6 & d <XXREAL-0R3 0NUMBERSK6) & a *XCMPLX-0K3 b <XXREAL-0R3 c /XCMPLX-0K7 d implies a *XCMPLX-0K3 d <XXREAL-0R3 c /XCMPLX-0K7 b"
sorry

mtheorem xreal_1_th_111:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds  for d be RealXREAL-0M1 holds (0NUMBERSK6 <XXREAL-0R3 b & 0NUMBERSK6 <XXREAL-0R3 d) & a *XCMPLX-0K3 b <XXREAL-0R3 c /XCMPLX-0K7 d implies a *XCMPLX-0K3 d <XXREAL-0R3 c /XCMPLX-0K7 b"
sorry

mtheorem xreal_1_th_112:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds  for d be RealXREAL-0M1 holds (b <XXREAL-0R3 0NUMBERSK6 & d <XXREAL-0R3 0NUMBERSK6) & c /XCMPLX-0K7 d <XXREAL-0R3 a *XCMPLX-0K3 b implies c /XCMPLX-0K7 b <XXREAL-0R3 a *XCMPLX-0K3 d"
sorry

mtheorem xreal_1_th_113:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds  for d be RealXREAL-0M1 holds (0NUMBERSK6 <XXREAL-0R3 b & 0NUMBERSK6 <XXREAL-0R3 d) & c /XCMPLX-0K7 d <XXREAL-0R3 a *XCMPLX-0K3 b implies c /XCMPLX-0K7 b <XXREAL-0R3 a *XCMPLX-0K3 d"
sorry

mtheorem xreal_1_th_114:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds  for d be RealXREAL-0M1 holds (b <XXREAL-0R3 0NUMBERSK6 & 0NUMBERSK6 <XXREAL-0R3 d) & a *XCMPLX-0K3 b <XXREAL-0R3 c /XCMPLX-0K7 d implies c /XCMPLX-0K7 b <XXREAL-0R3 a *XCMPLX-0K3 d"
sorry

mtheorem xreal_1_th_115:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds  for d be RealXREAL-0M1 holds (0NUMBERSK6 <XXREAL-0R3 b & d <XXREAL-0R3 0NUMBERSK6) & a *XCMPLX-0K3 b <XXREAL-0R3 c /XCMPLX-0K7 d implies c /XCMPLX-0K7 b <XXREAL-0R3 a *XCMPLX-0K3 d"
sorry

mtheorem xreal_1_th_116:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds  for d be RealXREAL-0M1 holds (b <XXREAL-0R3 0NUMBERSK6 & 0NUMBERSK6 <XXREAL-0R3 d) & c /XCMPLX-0K7 d <XXREAL-0R3 a *XCMPLX-0K3 b implies a *XCMPLX-0K3 d <XXREAL-0R3 c /XCMPLX-0K7 b"
sorry

mtheorem xreal_1_th_117:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds  for d be RealXREAL-0M1 holds (0NUMBERSK6 <XXREAL-0R3 b & d <XXREAL-0R3 0NUMBERSK6) & c /XCMPLX-0K7 d <XXREAL-0R3 a *XCMPLX-0K3 b implies a *XCMPLX-0K3 d <XXREAL-0R3 c /XCMPLX-0K7 b"
sorry

mtheorem xreal_1_th_118:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds (0NUMBERSK6 <XXREAL-0R3 a & 0NUMBERSK6 <=XXREAL-0R1 c) & a <=XXREAL-0R1 b implies c /XCMPLX-0K7 b <=XXREAL-0R1 c /XCMPLX-0K7 a"
sorry

mtheorem xreal_1_th_119:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds (0NUMBERSK6 <=XXREAL-0R1 c & b <XXREAL-0R3 0NUMBERSK6) & a <=XXREAL-0R1 b implies c /XCMPLX-0K7 b <=XXREAL-0R1 c /XCMPLX-0K7 a"
sorry

mtheorem xreal_1_th_120:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds (c <=XXREAL-0R1 0NUMBERSK6 & 0NUMBERSK6 <XXREAL-0R3 a) & a <=XXREAL-0R1 b implies c /XCMPLX-0K7 a <=XXREAL-0R1 c /XCMPLX-0K7 b"
sorry

mtheorem xreal_1_th_121:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds (c <=XXREAL-0R1 0NUMBERSK6 & b <XXREAL-0R3 0NUMBERSK6) & a <=XXREAL-0R1 b implies c /XCMPLX-0K7 a <=XXREAL-0R1 c /XCMPLX-0K7 b"
sorry

mtheorem xreal_1_th_122:
" for a be RealXREAL-0M1 holds 0NUMBERSK6 <XXREAL-0R3 a iff 0NUMBERSK6 <XXREAL-0R3 a \<inverse>XCMPLX-0K5"
   sorry

mtheorem xreal_1_th_123:
" for a be RealXREAL-0M1 holds a <XXREAL-0R3 0NUMBERSK6 iff a \<inverse>XCMPLX-0K5 <XXREAL-0R3 0NUMBERSK6"
   sorry

mtheorem xreal_1_th_124:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds a <XXREAL-0R3 0NUMBERSK6 & 0NUMBERSK6 <XXREAL-0R3 b implies a \<inverse>XCMPLX-0K5 <XXREAL-0R3 b \<inverse>XCMPLX-0K5"
sorry

mtheorem xreal_1_th_125:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds a \<inverse>XCMPLX-0K5 <XXREAL-0R3 0NUMBERSK6 & 0NUMBERSK6 <XXREAL-0R3 b \<inverse>XCMPLX-0K5 implies a <XXREAL-0R3 b"
sorry

(*begin*)
mtheorem xreal_1_th_126:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds a <=XXREAL-0R1 0NUMBERSK6 & 0NUMBERSK6 <=XXREAL-0R1 a implies 0NUMBERSK6 =XBOOLE-0R4 a *XCMPLX-0K3 b"
  using xreal_1_lm_35 sorry

mtheorem xreal_1_th_127:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds 0NUMBERSK6 <=XXREAL-0R1 a & 0NUMBERSK6 <=XXREAL-0R1 b implies 0NUMBERSK6 <=XXREAL-0R1 a *XCMPLX-0K3 b"
   sorry

mtheorem xreal_1_th_128:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds a <=XXREAL-0R1 0NUMBERSK6 & b <=XXREAL-0R1 0NUMBERSK6 implies 0NUMBERSK6 <=XXREAL-0R1 a *XCMPLX-0K3 b"
   sorry

mtheorem xreal_1_th_129:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds 0NUMBERSK6 <XXREAL-0R3 a & 0NUMBERSK6 <XXREAL-0R3 b implies 0NUMBERSK6 <XXREAL-0R3 a *XCMPLX-0K3 b"
   sorry

mtheorem xreal_1_th_130:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds a <XXREAL-0R3 0NUMBERSK6 & b <XXREAL-0R3 0NUMBERSK6 implies 0NUMBERSK6 <XXREAL-0R3 a *XCMPLX-0K3 b"
   sorry

mtheorem xreal_1_th_131:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds 0NUMBERSK6 <=XXREAL-0R1 a & b <=XXREAL-0R1 0NUMBERSK6 implies a *XCMPLX-0K3 b <=XXREAL-0R1 0NUMBERSK6"
   sorry

mtheorem xreal_1_th_132:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds 0NUMBERSK6 <XXREAL-0R3 a & b <XXREAL-0R3 0NUMBERSK6 implies a *XCMPLX-0K3 b <XXREAL-0R3 0NUMBERSK6"
   sorry

mtheorem xreal_1_th_133:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds a *XCMPLX-0K3 b <XXREAL-0R3 0NUMBERSK6 implies a >XXREAL-0R4 0NUMBERSK6 & b <XXREAL-0R3 0NUMBERSK6 or a <XXREAL-0R3 0NUMBERSK6 & b >XXREAL-0R4 0NUMBERSK6"
sorry

mtheorem xreal_1_th_134:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds a *XCMPLX-0K3 b >XXREAL-0R4 0NUMBERSK6 implies a >XXREAL-0R4 0NUMBERSK6 & b >XXREAL-0R4 0NUMBERSK6 or a <XXREAL-0R3 0NUMBERSK6 & b <XXREAL-0R3 0NUMBERSK6"
sorry

mtheorem xreal_1_th_135:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds a <=XXREAL-0R1 0NUMBERSK6 & b <=XXREAL-0R1 0NUMBERSK6 implies 0NUMBERSK6 <=XXREAL-0R1 a /XCMPLX-0K7 b"
   sorry

mtheorem xreal_1_th_136:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds 0NUMBERSK6 <=XXREAL-0R1 a & 0NUMBERSK6 <=XXREAL-0R1 b implies 0NUMBERSK6 <=XXREAL-0R1 a /XCMPLX-0K7 b"
   sorry

mtheorem xreal_1_th_137:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds 0NUMBERSK6 <=XXREAL-0R1 a & b <=XXREAL-0R1 0NUMBERSK6 implies a /XCMPLX-0K7 b <=XXREAL-0R1 0NUMBERSK6"
   sorry

mtheorem xreal_1_th_138:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds a <=XXREAL-0R1 0NUMBERSK6 & 0NUMBERSK6 <=XXREAL-0R1 b implies a /XCMPLX-0K7 b <=XXREAL-0R1 0NUMBERSK6"
   sorry

mtheorem xreal_1_th_139:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds 0NUMBERSK6 <XXREAL-0R3 a & 0NUMBERSK6 <XXREAL-0R3 b implies 0NUMBERSK6 <XXREAL-0R3 a /XCMPLX-0K7 b"
   sorry

mtheorem xreal_1_th_140:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds a <XXREAL-0R3 0NUMBERSK6 & b <XXREAL-0R3 0NUMBERSK6 implies 0NUMBERSK6 <XXREAL-0R3 a /XCMPLX-0K7 b"
   sorry

mtheorem xreal_1_th_141:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds a <XXREAL-0R3 0NUMBERSK6 & 0NUMBERSK6 <XXREAL-0R3 b implies a /XCMPLX-0K7 b <XXREAL-0R3 0NUMBERSK6"
   sorry

mtheorem xreal_1_th_142:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds a <XXREAL-0R3 0NUMBERSK6 & 0NUMBERSK6 <XXREAL-0R3 b implies b /XCMPLX-0K7 a <XXREAL-0R3 0NUMBERSK6"
   sorry

mtheorem xreal_1_th_143:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds a /XCMPLX-0K7 b <XXREAL-0R3 0NUMBERSK6 implies b <XXREAL-0R3 0NUMBERSK6 & a >XXREAL-0R4 0NUMBERSK6 or b >XXREAL-0R4 0NUMBERSK6 & a <XXREAL-0R3 0NUMBERSK6"
sorry

mtheorem xreal_1_th_144:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds a /XCMPLX-0K7 b >XXREAL-0R4 0NUMBERSK6 implies b >XXREAL-0R4 0NUMBERSK6 & a >XXREAL-0R4 0NUMBERSK6 or b <XXREAL-0R3 0NUMBERSK6 & a <XXREAL-0R3 0NUMBERSK6"
sorry

(*begin*)
mtheorem xreal_1_th_145:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds a <=XXREAL-0R1 b implies a <XXREAL-0R3 b +XCMPLX-0K2 \<one>\<^sub>M"
sorry

mtheorem xreal_1_th_146:
" for a be RealXREAL-0M1 holds a -XCMPLX-0K6 \<one>\<^sub>M <XXREAL-0R3 a"
sorry

mtheorem xreal_1_th_147:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds a <=XXREAL-0R1 b implies a -XCMPLX-0K6 \<one>\<^sub>M <XXREAL-0R3 b"
sorry

mtheorem xreal_1_th_148:
" for a be RealXREAL-0M1 holds -XCMPLX-0K4 \<one>\<^sub>M <XXREAL-0R3 a implies 0NUMBERSK6 <XXREAL-0R3 \<one>\<^sub>M +XCMPLX-0K2 a"
sorry

mtheorem xreal_1_th_149:
" for a be RealXREAL-0M1 holds a <XXREAL-0R3 \<one>\<^sub>M implies \<one>\<^sub>M -XCMPLX-0K6 a >XXREAL-0R4 0NUMBERSK6"
  using xreal_1_lm_21 sorry

(*begin*)
mtheorem xreal_1_th_150:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds ((a <=XXREAL-0R1 \<one>\<^sub>M & 0NUMBERSK6 <=XXREAL-0R1 b) & b <=XXREAL-0R1 \<one>\<^sub>M) & a *XCMPLX-0K3 b =XBOOLE-0R4 \<one>\<^sub>M implies a =HIDDENR1 \<one>\<^sub>M"
sorry

mtheorem xreal_1_th_151:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds 0NUMBERSK6 <=XXREAL-0R1 a & \<one>\<^sub>M <=XXREAL-0R1 b implies a <=XXREAL-0R1 a *XCMPLX-0K3 b"
sorry

mtheorem xreal_1_th_152:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds a <=XXREAL-0R1 0NUMBERSK6 & b <=XXREAL-0R1 \<one>\<^sub>M implies a <=XXREAL-0R1 a *XCMPLX-0K3 b"
sorry

mtheorem xreal_1_th_153:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds 0NUMBERSK6 <=XXREAL-0R1 a & b <=XXREAL-0R1 \<one>\<^sub>M implies a *XCMPLX-0K3 b <=XXREAL-0R1 a"
sorry

mtheorem xreal_1_th_154:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds a <=XXREAL-0R1 0NUMBERSK6 & \<one>\<^sub>M <=XXREAL-0R1 b implies a *XCMPLX-0K3 b <=XXREAL-0R1 a"
sorry

mtheorem xreal_1_th_155:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds 0NUMBERSK6 <XXREAL-0R3 a & \<one>\<^sub>M <XXREAL-0R3 b implies a <XXREAL-0R3 a *XCMPLX-0K3 b"
sorry

mtheorem xreal_1_th_156:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds a <XXREAL-0R3 0NUMBERSK6 & b <XXREAL-0R3 \<one>\<^sub>M implies a <XXREAL-0R3 a *XCMPLX-0K3 b"
sorry

mtheorem xreal_1_th_157:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds 0NUMBERSK6 <XXREAL-0R3 a & b <XXREAL-0R3 \<one>\<^sub>M implies a *XCMPLX-0K3 b <XXREAL-0R3 a"
sorry

mtheorem xreal_1_th_158:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds a <XXREAL-0R3 0NUMBERSK6 & \<one>\<^sub>M <XXREAL-0R3 b implies a *XCMPLX-0K3 b <XXREAL-0R3 a"
sorry

mtheorem xreal_1_th_159:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds \<one>\<^sub>M <=XXREAL-0R1 a & \<one>\<^sub>M <=XXREAL-0R1 b implies \<one>\<^sub>M <=XXREAL-0R1 a *XCMPLX-0K3 b"
sorry

mtheorem xreal_1_th_160:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds (0NUMBERSK6 <=XXREAL-0R1 a & a <=XXREAL-0R1 \<one>\<^sub>M) & b <=XXREAL-0R1 \<one>\<^sub>M implies a *XCMPLX-0K3 b <=XXREAL-0R1 \<one>\<^sub>M"
sorry

mtheorem xreal_1_th_161:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds \<one>\<^sub>M <XXREAL-0R3 a & \<one>\<^sub>M <=XXREAL-0R1 b implies \<one>\<^sub>M <XXREAL-0R3 a *XCMPLX-0K3 b"
sorry

mtheorem xreal_1_th_162:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds (0NUMBERSK6 <=XXREAL-0R1 a & a <XXREAL-0R3 \<one>\<^sub>M) & b <=XXREAL-0R1 \<one>\<^sub>M implies a *XCMPLX-0K3 b <XXREAL-0R3 \<one>\<^sub>M"
sorry

mtheorem xreal_1_th_163:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds a <=XXREAL-0R1 -XCMPLX-0K4 \<one>\<^sub>M & b <=XXREAL-0R1 -XCMPLX-0K4 \<one>\<^sub>M implies \<one>\<^sub>M <=XXREAL-0R1 a *XCMPLX-0K3 b"
sorry

mtheorem xreal_1_th_164:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds a <XXREAL-0R3 -XCMPLX-0K4 \<one>\<^sub>M & b <=XXREAL-0R1 -XCMPLX-0K4 \<one>\<^sub>M implies \<one>\<^sub>M <XXREAL-0R3 a *XCMPLX-0K3 b"
sorry

mtheorem xreal_1_th_165:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds (a <=XXREAL-0R1 0NUMBERSK6 & -XCMPLX-0K4 \<one>\<^sub>M <=XXREAL-0R1 a) & -XCMPLX-0K4 \<one>\<^sub>M <=XXREAL-0R1 b implies a *XCMPLX-0K3 b <=XXREAL-0R1 \<one>\<^sub>M"
sorry

mtheorem xreal_1_th_166:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds (a <=XXREAL-0R1 0NUMBERSK6 & -XCMPLX-0K4 \<one>\<^sub>M <XXREAL-0R3 a) & -XCMPLX-0K4 \<one>\<^sub>M <=XXREAL-0R1 b implies a *XCMPLX-0K3 b <XXREAL-0R3 \<one>\<^sub>M"
sorry

(*begin*)
mtheorem xreal_1_th_167:
" for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds ( for a be RealXREAL-0M1 holds \<one>\<^sub>M <XXREAL-0R3 a implies c <=XXREAL-0R1 b *XCMPLX-0K3 a) implies c <=XXREAL-0R1 b"
sorry

mlemma xreal_1_lm_36:
" for a be RealXREAL-0M1 holds \<one>\<^sub>M <XXREAL-0R3 a implies a \<inverse>XCMPLX-0K5 <XXREAL-0R3 \<one>\<^sub>M"
sorry

mtheorem xreal_1_th_168:
" for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds ( for a be RealXREAL-0M1 holds 0NUMBERSK6 <XXREAL-0R3 a & a <XXREAL-0R3 \<one>\<^sub>M implies b *XCMPLX-0K3 a <=XXREAL-0R1 c) implies b <=XXREAL-0R1 c"
sorry

mlemma xreal_1_lm_37:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds a <=XXREAL-0R1 b & 0NUMBERSK6 <=XXREAL-0R1 a implies a /XCMPLX-0K7 b <=XXREAL-0R1 \<one>\<^sub>M"
sorry

mlemma xreal_1_lm_38:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds b <=XXREAL-0R1 a & 0NUMBERSK6 <=XXREAL-0R1 a implies b /XCMPLX-0K7 a <=XXREAL-0R1 \<one>\<^sub>M"
sorry

mtheorem xreal_1_th_169:
" for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds ( for a be RealXREAL-0M1 holds 0NUMBERSK6 <XXREAL-0R3 a & a <XXREAL-0R3 \<one>\<^sub>M implies b <=XXREAL-0R1 a *XCMPLX-0K3 c) implies b <=XXREAL-0R1 0NUMBERSK6"
sorry

mtheorem xreal_1_th_170:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for d be RealXREAL-0M1 holds (((0NUMBERSK6 <=XXREAL-0R1 d & d <=XXREAL-0R1 \<one>\<^sub>M) & 0NUMBERSK6 <=XXREAL-0R1 a) & 0NUMBERSK6 <=XXREAL-0R1 b) & d *XCMPLX-0K3 a +XCMPLX-0K2 (\<one>\<^sub>M -XCMPLX-0K6 d)*XCMPLX-0K3 b =XBOOLE-0R4 0NUMBERSK6 implies (d =HIDDENR1 0NUMBERSK6 & b =HIDDENR1 0NUMBERSK6 or d =HIDDENR1 \<one>\<^sub>M & a =HIDDENR1 0NUMBERSK6) or a =HIDDENR1 0NUMBERSK6 & b =HIDDENR1 0NUMBERSK6"
sorry

mtheorem xreal_1_th_171:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for d be RealXREAL-0M1 holds 0NUMBERSK6 <=XXREAL-0R1 d & a <=XXREAL-0R1 b implies a <=XXREAL-0R1 (\<one>\<^sub>M -XCMPLX-0K6 d)*XCMPLX-0K3 a +XCMPLX-0K2 d *XCMPLX-0K3 b"
sorry

mtheorem xreal_1_th_172:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for d be RealXREAL-0M1 holds d <=XXREAL-0R1 \<one>\<^sub>M & a <=XXREAL-0R1 b implies (\<one>\<^sub>M -XCMPLX-0K6 d)*XCMPLX-0K3 a +XCMPLX-0K2 d *XCMPLX-0K3 b <=XXREAL-0R1 b"
sorry

mtheorem xreal_1_th_173:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds  for d be RealXREAL-0M1 holds ((0NUMBERSK6 <=XXREAL-0R1 d & d <=XXREAL-0R1 \<one>\<^sub>M) & a <=XXREAL-0R1 b) & a <=XXREAL-0R1 c implies a <=XXREAL-0R1 (\<one>\<^sub>M -XCMPLX-0K6 d)*XCMPLX-0K3 b +XCMPLX-0K2 d *XCMPLX-0K3 c"
sorry

mtheorem xreal_1_th_174:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds  for d be RealXREAL-0M1 holds ((0NUMBERSK6 <=XXREAL-0R1 d & d <=XXREAL-0R1 \<one>\<^sub>M) & b <=XXREAL-0R1 a) & c <=XXREAL-0R1 a implies (\<one>\<^sub>M -XCMPLX-0K6 d)*XCMPLX-0K3 b +XCMPLX-0K2 d *XCMPLX-0K3 c <=XXREAL-0R1 a"
sorry

mtheorem xreal_1_th_175:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds  for d be RealXREAL-0M1 holds ((0NUMBERSK6 <=XXREAL-0R1 d & d <=XXREAL-0R1 \<one>\<^sub>M) & a <XXREAL-0R3 b) & a <XXREAL-0R3 c implies a <XXREAL-0R3 (\<one>\<^sub>M -XCMPLX-0K6 d)*XCMPLX-0K3 b +XCMPLX-0K2 d *XCMPLX-0K3 c"
sorry

mtheorem xreal_1_th_176:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds  for d be RealXREAL-0M1 holds ((0NUMBERSK6 <=XXREAL-0R1 d & d <=XXREAL-0R1 \<one>\<^sub>M) & b <XXREAL-0R3 a) & c <XXREAL-0R3 a implies (\<one>\<^sub>M -XCMPLX-0K6 d)*XCMPLX-0K3 b +XCMPLX-0K2 d *XCMPLX-0K3 c <XXREAL-0R3 a"
sorry

mtheorem xreal_1_th_177:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds  for d be RealXREAL-0M1 holds ((0NUMBERSK6 <XXREAL-0R3 d & d <XXREAL-0R3 \<one>\<^sub>M) & a <=XXREAL-0R1 b) & a <XXREAL-0R3 c implies a <XXREAL-0R3 (\<one>\<^sub>M -XCMPLX-0K6 d)*XCMPLX-0K3 b +XCMPLX-0K2 d *XCMPLX-0K3 c"
sorry

mtheorem xreal_1_th_178:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds  for d be RealXREAL-0M1 holds ((0NUMBERSK6 <XXREAL-0R3 d & d <XXREAL-0R3 \<one>\<^sub>M) & b <XXREAL-0R3 a) & c <=XXREAL-0R1 a implies (\<one>\<^sub>M -XCMPLX-0K6 d)*XCMPLX-0K3 b +XCMPLX-0K2 d *XCMPLX-0K3 c <XXREAL-0R3 a"
sorry

mtheorem xreal_1_th_179:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for d be RealXREAL-0M1 holds ((0NUMBERSK6 <=XXREAL-0R1 d & d <=XXREAL-0R1 \<one>\<^sub>M) & a <=XXREAL-0R1 (\<one>\<^sub>M -XCMPLX-0K6 d)*XCMPLX-0K3 a +XCMPLX-0K2 d *XCMPLX-0K3 b) & b <XXREAL-0R3 (\<one>\<^sub>M -XCMPLX-0K6 d)*XCMPLX-0K3 a +XCMPLX-0K2 d *XCMPLX-0K3 b implies d =HIDDENR1 0NUMBERSK6"
sorry

mtheorem xreal_1_th_180:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for d be RealXREAL-0M1 holds ((0NUMBERSK6 <=XXREAL-0R1 d & d <=XXREAL-0R1 \<one>\<^sub>M) & (\<one>\<^sub>M -XCMPLX-0K6 d)*XCMPLX-0K3 a +XCMPLX-0K2 d *XCMPLX-0K3 b <=XXREAL-0R1 a) & (\<one>\<^sub>M -XCMPLX-0K6 d)*XCMPLX-0K3 a +XCMPLX-0K2 d *XCMPLX-0K3 b <XXREAL-0R3 b implies d =HIDDENR1 0NUMBERSK6"
sorry

(*begin*)
mtheorem xreal_1_th_181:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds 0NUMBERSK6 <XXREAL-0R3 a & a <=XXREAL-0R1 b implies \<one>\<^sub>M <=XXREAL-0R1 b /XCMPLX-0K7 a"
sorry

mtheorem xreal_1_th_182:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds a <XXREAL-0R3 0NUMBERSK6 & b <=XXREAL-0R1 a implies \<one>\<^sub>M <=XXREAL-0R1 b /XCMPLX-0K7 a"
sorry

mtheorem xreal_1_th_183:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds 0NUMBERSK6 <=XXREAL-0R1 a & a <=XXREAL-0R1 b implies a /XCMPLX-0K7 b <=XXREAL-0R1 \<one>\<^sub>M"
  using xreal_1_lm_37 sorry

mtheorem xreal_1_th_184:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds b <=XXREAL-0R1 a & a <=XXREAL-0R1 0NUMBERSK6 implies a /XCMPLX-0K7 b <=XXREAL-0R1 \<one>\<^sub>M"
sorry

mtheorem xreal_1_th_185:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds 0NUMBERSK6 <=XXREAL-0R1 a & b <=XXREAL-0R1 a implies b /XCMPLX-0K7 a <=XXREAL-0R1 \<one>\<^sub>M"
  using xreal_1_lm_38 sorry

mtheorem xreal_1_th_186:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds a <=XXREAL-0R1 0NUMBERSK6 & a <=XXREAL-0R1 b implies b /XCMPLX-0K7 a <=XXREAL-0R1 \<one>\<^sub>M"
sorry

mtheorem xreal_1_th_187:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds 0NUMBERSK6 <XXREAL-0R3 a & a <XXREAL-0R3 b implies \<one>\<^sub>M <XXREAL-0R3 b /XCMPLX-0K7 a"
sorry

mtheorem xreal_1_th_188:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds a <XXREAL-0R3 0NUMBERSK6 & b <XXREAL-0R3 a implies \<one>\<^sub>M <XXREAL-0R3 b /XCMPLX-0K7 a"
sorry

mtheorem xreal_1_th_189:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds 0NUMBERSK6 <=XXREAL-0R1 a & a <XXREAL-0R3 b implies a /XCMPLX-0K7 b <XXREAL-0R3 \<one>\<^sub>M"
sorry

mtheorem xreal_1_th_190:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds a <=XXREAL-0R1 0NUMBERSK6 & b <XXREAL-0R3 a implies a /XCMPLX-0K7 b <XXREAL-0R3 \<one>\<^sub>M"
sorry

mtheorem xreal_1_th_191:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds 0NUMBERSK6 <XXREAL-0R3 a & b <XXREAL-0R3 a implies b /XCMPLX-0K7 a <XXREAL-0R3 \<one>\<^sub>M"
sorry

mtheorem xreal_1_th_192:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds a <XXREAL-0R3 0NUMBERSK6 & a <XXREAL-0R3 b implies b /XCMPLX-0K7 a <XXREAL-0R3 \<one>\<^sub>M"
sorry

(*begin*)
mtheorem xreal_1_th_193:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds 0NUMBERSK6 <=XXREAL-0R1 b & -XCMPLX-0K4 b <=XXREAL-0R1 a implies -XCMPLX-0K4 \<one>\<^sub>M <=XXREAL-0R1 a /XCMPLX-0K7 b"
sorry

mtheorem xreal_1_th_194:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds 0NUMBERSK6 <=XXREAL-0R1 b & -XCMPLX-0K4 a <=XXREAL-0R1 b implies -XCMPLX-0K4 \<one>\<^sub>M <=XXREAL-0R1 a /XCMPLX-0K7 b"
sorry

mtheorem xreal_1_th_195:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds b <=XXREAL-0R1 0NUMBERSK6 & a <=XXREAL-0R1 -XCMPLX-0K4 b implies -XCMPLX-0K4 \<one>\<^sub>M <=XXREAL-0R1 a /XCMPLX-0K7 b"
sorry

mtheorem xreal_1_th_196:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds b <=XXREAL-0R1 0NUMBERSK6 & b <=XXREAL-0R1 -XCMPLX-0K4 a implies -XCMPLX-0K4 \<one>\<^sub>M <=XXREAL-0R1 a /XCMPLX-0K7 b"
sorry

mtheorem xreal_1_th_197:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds 0NUMBERSK6 <XXREAL-0R3 b & -XCMPLX-0K4 b <XXREAL-0R3 a implies -XCMPLX-0K4 \<one>\<^sub>M <XXREAL-0R3 a /XCMPLX-0K7 b"
sorry

mtheorem xreal_1_th_198:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds 0NUMBERSK6 <XXREAL-0R3 b & -XCMPLX-0K4 a <XXREAL-0R3 b implies -XCMPLX-0K4 \<one>\<^sub>M <XXREAL-0R3 a /XCMPLX-0K7 b"
sorry

mtheorem xreal_1_th_199:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds b <XXREAL-0R3 0NUMBERSK6 & a <XXREAL-0R3 -XCMPLX-0K4 b implies -XCMPLX-0K4 \<one>\<^sub>M <XXREAL-0R3 a /XCMPLX-0K7 b"
sorry

mtheorem xreal_1_th_200:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds b <XXREAL-0R3 0NUMBERSK6 & b <XXREAL-0R3 -XCMPLX-0K4 a implies -XCMPLX-0K4 \<one>\<^sub>M <XXREAL-0R3 a /XCMPLX-0K7 b"
sorry

mtheorem xreal_1_th_201:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds 0NUMBERSK6 <XXREAL-0R3 b & a <=XXREAL-0R1 -XCMPLX-0K4 b implies a /XCMPLX-0K7 b <=XXREAL-0R1 -XCMPLX-0K4 \<one>\<^sub>M"
sorry

mtheorem xreal_1_th_202:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds 0NUMBERSK6 <XXREAL-0R3 b & b <=XXREAL-0R1 -XCMPLX-0K4 a implies a /XCMPLX-0K7 b <=XXREAL-0R1 -XCMPLX-0K4 \<one>\<^sub>M"
sorry

mtheorem xreal_1_th_203:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds b <XXREAL-0R3 0NUMBERSK6 & -XCMPLX-0K4 b <=XXREAL-0R1 a implies a /XCMPLX-0K7 b <=XXREAL-0R1 -XCMPLX-0K4 \<one>\<^sub>M"
sorry

mtheorem xreal_1_th_204:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds b <XXREAL-0R3 0NUMBERSK6 & -XCMPLX-0K4 a <=XXREAL-0R1 b implies a /XCMPLX-0K7 b <=XXREAL-0R1 -XCMPLX-0K4 \<one>\<^sub>M"
sorry

mtheorem xreal_1_th_205:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds 0NUMBERSK6 <XXREAL-0R3 b & a <XXREAL-0R3 -XCMPLX-0K4 b implies a /XCMPLX-0K7 b <XXREAL-0R3 -XCMPLX-0K4 \<one>\<^sub>M"
sorry

mtheorem xreal_1_th_206:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds 0NUMBERSK6 <XXREAL-0R3 b & b <XXREAL-0R3 -XCMPLX-0K4 a implies a /XCMPLX-0K7 b <XXREAL-0R3 -XCMPLX-0K4 \<one>\<^sub>M"
sorry

mtheorem xreal_1_th_207:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds b <XXREAL-0R3 0NUMBERSK6 & -XCMPLX-0K4 b <XXREAL-0R3 a implies a /XCMPLX-0K7 b <XXREAL-0R3 -XCMPLX-0K4 \<one>\<^sub>M"
sorry

mtheorem xreal_1_th_208:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds b <XXREAL-0R3 0NUMBERSK6 & -XCMPLX-0K4 a <XXREAL-0R3 b implies a /XCMPLX-0K7 b <XXREAL-0R3 -XCMPLX-0K4 \<one>\<^sub>M"
sorry

(*begin*)
mtheorem xreal_1_th_209:
" for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds ( for a be RealXREAL-0M1 holds 0NUMBERSK6 <XXREAL-0R3 a & a <XXREAL-0R3 \<one>\<^sub>M implies c <=XXREAL-0R1 b /XCMPLX-0K7 a) implies c <=XXREAL-0R1 b"
sorry

mtheorem xreal_1_th_210:
" for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds ( for a be RealXREAL-0M1 holds \<one>\<^sub>M <XXREAL-0R3 a implies b /XCMPLX-0K7 a <=XXREAL-0R1 c) implies b <=XXREAL-0R1 c"
sorry

mtheorem xreal_1_th_211:
" for a be RealXREAL-0M1 holds \<one>\<^sub>M <=XXREAL-0R1 a implies a \<inverse>XCMPLX-0K5 <=XXREAL-0R1 \<one>\<^sub>M"
sorry

mtheorem xreal_1_th_212:
" for a be RealXREAL-0M1 holds \<one>\<^sub>M <XXREAL-0R3 a implies a \<inverse>XCMPLX-0K5 <XXREAL-0R3 \<one>\<^sub>M"
  using xreal_1_lm_36 sorry

mtheorem xreal_1_th_213:
" for a be RealXREAL-0M1 holds a <=XXREAL-0R1 -XCMPLX-0K4 \<one>\<^sub>M implies -XCMPLX-0K4 \<one>\<^sub>M <=XXREAL-0R1 a \<inverse>XCMPLX-0K5"
sorry

mtheorem xreal_1_th_214:
" for a be RealXREAL-0M1 holds a <XXREAL-0R3 -XCMPLX-0K4 \<one>\<^sub>M implies -XCMPLX-0K4 \<one>\<^sub>M <XXREAL-0R3 a \<inverse>XCMPLX-0K5"
sorry

(*begin*)
mtheorem xreal_1_th_215:
" for a be RealXREAL-0M1 holds 0NUMBERSK6 <XXREAL-0R3 a implies 0NUMBERSK6 <XXREAL-0R3 a /XCMPLX-0K7 \<two>\<^sub>M"
   sorry

mtheorem xreal_1_th_216:
" for a be RealXREAL-0M1 holds 0NUMBERSK6 <XXREAL-0R3 a implies a /XCMPLX-0K7 \<two>\<^sub>M <XXREAL-0R3 a"
  using xreal_1_lm_27 sorry

mtheorem xreal_1_th_217:
" for a be RealXREAL-0M1 holds a <=XXREAL-0R1 \<one>\<^sub>M /XCMPLX-0K7 \<two>\<^sub>M implies \<two>\<^sub>M *XCMPLX-0K3 a -XCMPLX-0K6 \<one>\<^sub>M <=XXREAL-0R1 0NUMBERSK6"
sorry

mtheorem xreal_1_th_218:
" for a be RealXREAL-0M1 holds a <=XXREAL-0R1 \<one>\<^sub>M /XCMPLX-0K7 \<two>\<^sub>M implies 0NUMBERSK6 <=XXREAL-0R1 \<one>\<^sub>M -XCMPLX-0K6 \<two>\<^sub>M *XCMPLX-0K3 a"
sorry

mtheorem xreal_1_th_219:
" for a be RealXREAL-0M1 holds a >=XXREAL-0R2 \<one>\<^sub>M /XCMPLX-0K7 \<two>\<^sub>M implies \<two>\<^sub>M *XCMPLX-0K3 a -XCMPLX-0K6 \<one>\<^sub>M >=XXREAL-0R2 0NUMBERSK6"
sorry

mtheorem xreal_1_th_220:
" for a be RealXREAL-0M1 holds a >=XXREAL-0R2 \<one>\<^sub>M /XCMPLX-0K7 \<two>\<^sub>M implies 0NUMBERSK6 >=XXREAL-0R2 \<one>\<^sub>M -XCMPLX-0K6 \<two>\<^sub>M *XCMPLX-0K3 a"
sorry

(*begin*)
mtheorem xreal_1_th_221:
" for a be RealXREAL-0M1 holds 0NUMBERSK6 <XXREAL-0R3 a implies a /XCMPLX-0K7 \<three>\<^sub>M <XXREAL-0R3 a"
sorry

mtheorem xreal_1_th_222:
" for a be RealXREAL-0M1 holds 0NUMBERSK6 <XXREAL-0R3 a implies 0NUMBERSK6 <XXREAL-0R3 a /XCMPLX-0K7 \<three>\<^sub>M"
   sorry

(*begin*)
mtheorem xreal_1_th_223:
" for a be RealXREAL-0M1 holds 0NUMBERSK6 <XXREAL-0R3 a implies a /XCMPLX-0K7 \<four>\<^sub>M <XXREAL-0R3 a"
sorry

mtheorem xreal_1_th_224:
" for a be RealXREAL-0M1 holds 0NUMBERSK6 <XXREAL-0R3 a implies 0NUMBERSK6 <XXREAL-0R3 a /XCMPLX-0K7 \<four>\<^sub>M"
   sorry

mtheorem xreal_1_th_225:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds b <>HIDDENR2 0NUMBERSK6 implies ( ex c be RealXREAL-0M1 st a =HIDDENR1 b /XCMPLX-0K7 c)"
sorry

(*begin*)
mtheorem xreal_1_th_226:
" for r be RealXREAL-0M1 holds  for s be RealXREAL-0M1 holds r <XXREAL-0R3 s implies r <XXREAL-0R3 (r +XCMPLX-0K2 s)/XCMPLX-0K7 \<two>\<^sub>M & (r +XCMPLX-0K2 s)/XCMPLX-0K7 \<two>\<^sub>M <XXREAL-0R3 s"
sorry

mtheorem xreal_1_cl_1:
"cluster note-that ext-realXXREAL-0V1 for ElementSUBSET-1M1-of REALNUMBERSK2"
proof
(*coherence*)
  show " for it be ElementSUBSET-1M1-of REALNUMBERSK2 holds it be ext-realXXREAL-0V1"
     sorry
qed "sorry"

reserve p, q, r, s, t for "ExtRealXXREAL-0M1"
mtheorem xreal_1_th_227:
" for r be ExtRealXXREAL-0M1 holds  for t be ExtRealXXREAL-0M1 holds r <XXREAL-0R3 t implies ( ex s be ExtRealXXREAL-0M1 st r <XXREAL-0R3 s & s <XXREAL-0R3 t)"
sorry

mtheorem xreal_1_th_228:
" for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds  for t be ExtRealXXREAL-0M1 holds r <XXREAL-0R3 s & ( for q be ExtRealXXREAL-0M1 holds r <XXREAL-0R3 q & q <XXREAL-0R3 s implies t <=XXREAL-0R1 q) implies t <=XXREAL-0R1 r"
sorry

mtheorem xreal_1_th_229:
" for r be ExtRealXXREAL-0M1 holds  for s be ExtRealXXREAL-0M1 holds  for t be ExtRealXXREAL-0M1 holds r <XXREAL-0R3 s & ( for q be ExtRealXXREAL-0M1 holds r <XXREAL-0R3 q & q <XXREAL-0R3 s implies q <=XXREAL-0R1 t) implies s <=XXREAL-0R1 t"
sorry

mtheorem xreal_1_th_230:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds 0NUMBERSK6 <=XXREAL-0R1 a & b <=XXREAL-0R1 c implies b -XCMPLX-0K6 a <=XXREAL-0R1 c"
sorry

mtheorem xreal_1_th_231:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds 0NUMBERSK6 <XXREAL-0R3 a & b <=XXREAL-0R1 c implies b -XCMPLX-0K6 a <XXREAL-0R3 c"
sorry

(*begin*)
mtheorem xreal_1_th_232:
" for a be RealXREAL-0M1 holds a -'XREAL-0K1 a =XBOOLE-0R4 0NUMBERSK6"
sorry

mtheorem xreal_1_th_233:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds b <=XXREAL-0R1 a implies a -'XREAL-0K1 b =XBOOLE-0R4 a -XCMPLX-0K6 b"
  using xreal_1_th_48 xreal_0_def_2 sorry

mtheorem xreal_1_th_234:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds (c <=XXREAL-0R1 a & c <=XXREAL-0R1 b) & a -'XREAL-0K1 c =XBOOLE-0R4 b -'XREAL-0K1 c implies a =HIDDENR1 b"
sorry

mtheorem xreal_1_th_235:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds a >=XXREAL-0R2 b implies (a -'XREAL-0K1 b)+XCMPLX-0K2 b =HIDDENR1 a"
sorry

mtheorem xreal_1_th_236:
" for a be RealXREAL-0M1 holds  for b be RealXREAL-0M1 holds  for c be RealXREAL-0M1 holds a <=XXREAL-0R1 b & c <XXREAL-0R3 a implies b -'XREAL-0K1 a <XXREAL-0R3 b -'XREAL-0K1 c"
sorry

mtheorem xreal_1_th_237:
" for a be RealXREAL-0M1 holds \<one>\<^sub>M <=XXREAL-0R1 a implies a -'XREAL-0K1 \<one>\<^sub>M <XXREAL-0R3 a"
sorry

end
