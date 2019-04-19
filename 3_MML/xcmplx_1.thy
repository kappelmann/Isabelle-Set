theory xcmplx_1
  imports xreal_0
   "../mizar_extension/E_number"
begin
(*begin*)
reserve a, b, c, d, e for "ComplexXCMPLX-0M1"
mtheorem xcmplx_1_th_1:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds a +XCMPLX-0K2 (b +XCMPLX-0K2 c) =HIDDENR1 (a +XCMPLX-0K2 b)+XCMPLX-0K2 c"
   sorry

mtheorem xcmplx_1_th_2:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds a +XCMPLX-0K2 c =HIDDENR1 b +XCMPLX-0K2 c implies a =HIDDENR1 b"
   sorry

mtheorem xcmplx_1_th_3:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds a =HIDDENR1 a +XCMPLX-0K2 b implies b =HIDDENR1 0NUMBERSK6"
   sorry

mtheorem xcmplx_1_th_4:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds a *XCMPLX-0K3 (b *XCMPLX-0K3 c) =HIDDENR1 (a *XCMPLX-0K3 b)*XCMPLX-0K3 c"
   sorry

mtheorem xcmplx_1_th_5:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds c <>HIDDENR2 0NUMBERSK6 & a *XCMPLX-0K3 c =HIDDENR1 b *XCMPLX-0K3 c implies a =HIDDENR1 b"
sorry

mtheorem xcmplx_1_th_6:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds a *XCMPLX-0K3 b =HIDDENR1 0NUMBERSK6 implies a =HIDDENR1 0NUMBERSK6 or b =HIDDENR1 0NUMBERSK6"
   sorry

mtheorem xcmplx_1_th_7:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds b <>HIDDENR2 0NUMBERSK6 & a *XCMPLX-0K3 b =HIDDENR1 b implies a =HIDDENR1 \<one>\<^sub>M"
sorry

mtheorem xcmplx_1_th_8:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds a *XCMPLX-0K3 (b +XCMPLX-0K2 c) =HIDDENR1 a *XCMPLX-0K3 b +XCMPLX-0K2 a *XCMPLX-0K3 c"
   sorry

mtheorem xcmplx_1_th_9:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds  for d be ComplexXCMPLX-0M1 holds ((a +XCMPLX-0K2 b)+XCMPLX-0K2 c)*XCMPLX-0K3 d =HIDDENR1 (a *XCMPLX-0K3 d +XCMPLX-0K2 b *XCMPLX-0K3 d)+XCMPLX-0K2 c *XCMPLX-0K3 d"
   sorry

mtheorem xcmplx_1_th_10:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds  for d be ComplexXCMPLX-0M1 holds (a +XCMPLX-0K2 b)*XCMPLX-0K3 (c +XCMPLX-0K2 d) =HIDDENR1 ((a *XCMPLX-0K3 c +XCMPLX-0K2 a *XCMPLX-0K3 d)+XCMPLX-0K2 b *XCMPLX-0K3 c)+XCMPLX-0K2 b *XCMPLX-0K3 d"
   sorry

mtheorem xcmplx_1_th_11:
" for a be ComplexXCMPLX-0M1 holds \<two>\<^sub>M *XCMPLX-0K3 a =HIDDENR1 a +XCMPLX-0K2 a"
   sorry

mtheorem xcmplx_1_th_12:
" for a be ComplexXCMPLX-0M1 holds \<three>\<^sub>M *XCMPLX-0K3 a =HIDDENR1 (a +XCMPLX-0K2 a)+XCMPLX-0K2 a"
   sorry

mtheorem xcmplx_1_th_13:
" for a be ComplexXCMPLX-0M1 holds \<four>\<^sub>M *XCMPLX-0K3 a =HIDDENR1 ((a +XCMPLX-0K2 a)+XCMPLX-0K2 a)+XCMPLX-0K2 a"
   sorry

mtheorem xcmplx_1_th_14:
" for a be ComplexXCMPLX-0M1 holds a -XCMPLX-0K6 a =HIDDENR1 0NUMBERSK6"
   sorry

mtheorem xcmplx_1_th_15:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds a -XCMPLX-0K6 b =HIDDENR1 0NUMBERSK6 implies a =HIDDENR1 b"
   sorry

mtheorem xcmplx_1_th_16:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds b -XCMPLX-0K6 a =HIDDENR1 b implies a =HIDDENR1 0NUMBERSK6"
   sorry

mtheorem xcmplx_1_th_17:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds a =HIDDENR1 a -XCMPLX-0K6 (b -XCMPLX-0K6 b)"
   sorry

mtheorem xcmplx_1_th_18:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds a -XCMPLX-0K6 (a -XCMPLX-0K6 b) =HIDDENR1 b"
   sorry

mtheorem xcmplx_1_th_19:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds a -XCMPLX-0K6 c =HIDDENR1 b -XCMPLX-0K6 c implies a =HIDDENR1 b"
   sorry

mtheorem xcmplx_1_th_20:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds c -XCMPLX-0K6 a =HIDDENR1 c -XCMPLX-0K6 b implies a =HIDDENR1 b"
   sorry

mtheorem xcmplx_1_th_21:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds (a -XCMPLX-0K6 b)-XCMPLX-0K6 c =HIDDENR1 (a -XCMPLX-0K6 c)-XCMPLX-0K6 b"
   sorry

mtheorem xcmplx_1_th_22:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds a -XCMPLX-0K6 c =HIDDENR1 (a -XCMPLX-0K6 b)-XCMPLX-0K6 (c -XCMPLX-0K6 b)"
   sorry

mtheorem xcmplx_1_th_23:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds (c -XCMPLX-0K6 a)-XCMPLX-0K6 (c -XCMPLX-0K6 b) =HIDDENR1 b -XCMPLX-0K6 a"
   sorry

mtheorem xcmplx_1_th_24:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds  for d be ComplexXCMPLX-0M1 holds a -XCMPLX-0K6 b =HIDDENR1 c -XCMPLX-0K6 d implies a -XCMPLX-0K6 c =HIDDENR1 b -XCMPLX-0K6 d"
   sorry

mlemma xcmplx_1_lm_1:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds a \<inverse>XCMPLX-0K5 *XCMPLX-0K3 b \<inverse>XCMPLX-0K5 =HIDDENR1 (a *XCMPLX-0K3 b)\<inverse>XCMPLX-0K5"
sorry

mlemma xcmplx_1_lm_2:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds a /XCMPLX-0K7 (b /XCMPLX-0K7 c) =HIDDENR1 (a *XCMPLX-0K3 c)/XCMPLX-0K7 b"
sorry

mlemma xcmplx_1_lm_3:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds b <>HIDDENR2 0NUMBERSK6 implies (a /XCMPLX-0K7 b)*XCMPLX-0K3 b =HIDDENR1 a"
sorry

mlemma xcmplx_1_lm_4:
" for a be ComplexXCMPLX-0M1 holds \<one>\<^sub>M /XCMPLX-0K7 a =HIDDENR1 a \<inverse>XCMPLX-0K5"
sorry

mlemma xcmplx_1_lm_5:
" for a be ComplexXCMPLX-0M1 holds a <>HIDDENR2 0NUMBERSK6 implies a /XCMPLX-0K7 a =HIDDENR1 \<one>\<^sub>M"
sorry

mtheorem xcmplx_1_th_25:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds a =HIDDENR1 a +XCMPLX-0K2 (b -XCMPLX-0K6 b)"
   sorry

mtheorem xcmplx_1_th_26:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds a =HIDDENR1 (a +XCMPLX-0K2 b)-XCMPLX-0K6 b"
   sorry

mtheorem xcmplx_1_th_27:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds a =HIDDENR1 (a -XCMPLX-0K6 b)+XCMPLX-0K2 b"
   sorry

mtheorem xcmplx_1_th_28:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds a +XCMPLX-0K2 c =HIDDENR1 (a +XCMPLX-0K2 b)+XCMPLX-0K2 (c -XCMPLX-0K6 b)"
   sorry

mtheorem xcmplx_1_th_29:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds (a +XCMPLX-0K2 b)-XCMPLX-0K6 c =HIDDENR1 (a -XCMPLX-0K6 c)+XCMPLX-0K2 b"
   sorry

mtheorem xcmplx_1_th_30:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds (a -XCMPLX-0K6 b)+XCMPLX-0K2 c =HIDDENR1 (c -XCMPLX-0K6 b)+XCMPLX-0K2 a"
   sorry

mtheorem xcmplx_1_th_31:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds a +XCMPLX-0K2 c =HIDDENR1 (a +XCMPLX-0K2 b)-XCMPLX-0K6 (b -XCMPLX-0K6 c)"
   sorry

mtheorem xcmplx_1_th_32:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds a -XCMPLX-0K6 c =HIDDENR1 (a +XCMPLX-0K2 b)-XCMPLX-0K6 (c +XCMPLX-0K2 b)"
   sorry

mtheorem xcmplx_1_th_33:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds  for d be ComplexXCMPLX-0M1 holds a +XCMPLX-0K2 b =HIDDENR1 c +XCMPLX-0K2 d implies a -XCMPLX-0K6 c =HIDDENR1 d -XCMPLX-0K6 b"
   sorry

mtheorem xcmplx_1_th_34:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds  for d be ComplexXCMPLX-0M1 holds a -XCMPLX-0K6 c =HIDDENR1 d -XCMPLX-0K6 b implies a +XCMPLX-0K2 b =HIDDENR1 c +XCMPLX-0K2 d"
   sorry

mtheorem xcmplx_1_th_35:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds  for d be ComplexXCMPLX-0M1 holds a +XCMPLX-0K2 b =HIDDENR1 c -XCMPLX-0K6 d implies a +XCMPLX-0K2 d =HIDDENR1 c -XCMPLX-0K6 b"
   sorry

mtheorem xcmplx_1_th_36:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds a -XCMPLX-0K6 (b +XCMPLX-0K2 c) =HIDDENR1 (a -XCMPLX-0K6 b)-XCMPLX-0K6 c"
   sorry

mtheorem xcmplx_1_th_37:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds a -XCMPLX-0K6 (b -XCMPLX-0K6 c) =HIDDENR1 (a -XCMPLX-0K6 b)+XCMPLX-0K2 c"
   sorry

mtheorem xcmplx_1_th_38:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds a -XCMPLX-0K6 (b -XCMPLX-0K6 c) =HIDDENR1 a +XCMPLX-0K2 (c -XCMPLX-0K6 b)"
   sorry

mtheorem xcmplx_1_th_39:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds a -XCMPLX-0K6 c =HIDDENR1 (a -XCMPLX-0K6 b)+XCMPLX-0K2 (b -XCMPLX-0K6 c)"
   sorry

mtheorem xcmplx_1_th_40:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds a *XCMPLX-0K3 (b -XCMPLX-0K6 c) =HIDDENR1 a *XCMPLX-0K3 b -XCMPLX-0K6 a *XCMPLX-0K3 c"
   sorry

mtheorem xcmplx_1_th_41:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds  for d be ComplexXCMPLX-0M1 holds (a -XCMPLX-0K6 b)*XCMPLX-0K3 (c -XCMPLX-0K6 d) =HIDDENR1 (b -XCMPLX-0K6 a)*XCMPLX-0K3 (d -XCMPLX-0K6 c)"
   sorry

mtheorem xcmplx_1_th_42:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds  for d be ComplexXCMPLX-0M1 holds ((a -XCMPLX-0K6 b)-XCMPLX-0K6 c)*XCMPLX-0K3 d =HIDDENR1 (a *XCMPLX-0K3 d -XCMPLX-0K6 b *XCMPLX-0K3 d)-XCMPLX-0K6 c *XCMPLX-0K3 d"
   sorry

mtheorem xcmplx_1_th_43:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds  for d be ComplexXCMPLX-0M1 holds ((a +XCMPLX-0K2 b)-XCMPLX-0K6 c)*XCMPLX-0K3 d =HIDDENR1 (a *XCMPLX-0K3 d +XCMPLX-0K2 b *XCMPLX-0K3 d)-XCMPLX-0K6 c *XCMPLX-0K3 d"
   sorry

mtheorem xcmplx_1_th_44:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds  for d be ComplexXCMPLX-0M1 holds ((a -XCMPLX-0K6 b)+XCMPLX-0K2 c)*XCMPLX-0K3 d =HIDDENR1 (a *XCMPLX-0K3 d -XCMPLX-0K6 b *XCMPLX-0K3 d)+XCMPLX-0K2 c *XCMPLX-0K3 d"
   sorry

mtheorem xcmplx_1_th_45:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds  for d be ComplexXCMPLX-0M1 holds (a +XCMPLX-0K2 b)*XCMPLX-0K3 (c -XCMPLX-0K6 d) =HIDDENR1 ((a *XCMPLX-0K3 c -XCMPLX-0K6 a *XCMPLX-0K3 d)+XCMPLX-0K2 b *XCMPLX-0K3 c)-XCMPLX-0K6 b *XCMPLX-0K3 d"
   sorry

mtheorem xcmplx_1_th_46:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds  for d be ComplexXCMPLX-0M1 holds (a -XCMPLX-0K6 b)*XCMPLX-0K3 (c +XCMPLX-0K2 d) =HIDDENR1 ((a *XCMPLX-0K3 c +XCMPLX-0K2 a *XCMPLX-0K3 d)-XCMPLX-0K6 b *XCMPLX-0K3 c)-XCMPLX-0K6 b *XCMPLX-0K3 d"
   sorry

mtheorem xcmplx_1_th_47:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for d be ComplexXCMPLX-0M1 holds  for e be ComplexXCMPLX-0M1 holds (a -XCMPLX-0K6 b)*XCMPLX-0K3 (e -XCMPLX-0K6 d) =HIDDENR1 ((a *XCMPLX-0K3 e -XCMPLX-0K6 a *XCMPLX-0K3 d)-XCMPLX-0K6 b *XCMPLX-0K3 e)+XCMPLX-0K2 b *XCMPLX-0K3 d"
   sorry

mtheorem xcmplx_1_th_48:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds (a /XCMPLX-0K7 b)/XCMPLX-0K7 c =HIDDENR1 (a /XCMPLX-0K7 c)/XCMPLX-0K7 b"
sorry

mtheorem xcmplx_1_th_49:
" for a be ComplexXCMPLX-0M1 holds a /XCMPLX-0K7 (0NUMBERSK6) =HIDDENR1 0NUMBERSK6"
sorry

mtheorem xcmplx_1_th_50:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds a <>HIDDENR2 0NUMBERSK6 & b <>HIDDENR2 0NUMBERSK6 implies a /XCMPLX-0K7 b <>HIDDENR2 0NUMBERSK6"
   sorry

mtheorem xcmplx_1_th_51:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds b <>HIDDENR2 0NUMBERSK6 implies a =HIDDENR1 a /XCMPLX-0K7 (b /XCMPLX-0K7 b)"
sorry

mlemma xcmplx_1_lm_6:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds  for d be ComplexXCMPLX-0M1 holds (a /XCMPLX-0K7 b)*XCMPLX-0K3 (c /XCMPLX-0K7 d) =HIDDENR1 (a *XCMPLX-0K3 c)/XCMPLX-0K7 (b *XCMPLX-0K3 d)"
sorry

mlemma xcmplx_1_lm_7:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds (a /XCMPLX-0K7 b)\<inverse>XCMPLX-0K5 =HIDDENR1 b /XCMPLX-0K7 a"
sorry

mlemma xcmplx_1_lm_8:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds a *XCMPLX-0K3 (b /XCMPLX-0K7 c) =HIDDENR1 (a *XCMPLX-0K3 b)/XCMPLX-0K7 c"
sorry

mtheorem xcmplx_1_th_52:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds a <>HIDDENR2 0NUMBERSK6 implies a /XCMPLX-0K7 (a /XCMPLX-0K7 b) =HIDDENR1 b"
sorry

mtheorem xcmplx_1_th_53:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds c <>HIDDENR2 0NUMBERSK6 & a /XCMPLX-0K7 c =HIDDENR1 b /XCMPLX-0K7 c implies a =HIDDENR1 b"
sorry

mlemma xcmplx_1_lm_9:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds b <>HIDDENR2 0NUMBERSK6 implies a =HIDDENR1 (a *XCMPLX-0K3 b)/XCMPLX-0K7 b"
sorry

mtheorem xcmplx_1_th_54:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds a /XCMPLX-0K7 b <>HIDDENR2 0NUMBERSK6 implies b =HIDDENR1 a /XCMPLX-0K7 (a /XCMPLX-0K7 b)"
sorry

mlemma xcmplx_1_lm_10:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds c <>HIDDENR2 0NUMBERSK6 implies a /XCMPLX-0K7 b =HIDDENR1 (a *XCMPLX-0K3 c)/XCMPLX-0K7 (b *XCMPLX-0K3 c)"
sorry

mtheorem xcmplx_1_th_55:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds c <>HIDDENR2 0NUMBERSK6 implies a /XCMPLX-0K7 b =HIDDENR1 (a /XCMPLX-0K7 c)/XCMPLX-0K7 (b /XCMPLX-0K7 c)"
sorry

mtheorem xcmplx_1_th_56:
" for a be ComplexXCMPLX-0M1 holds \<one>\<^sub>M /XCMPLX-0K7 (\<one>\<^sub>M /XCMPLX-0K7 a) =HIDDENR1 a"
sorry

mlemma xcmplx_1_lm_11:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds (a *XCMPLX-0K3 b \<inverse>XCMPLX-0K5)\<inverse>XCMPLX-0K5 =HIDDENR1 a \<inverse>XCMPLX-0K5 *XCMPLX-0K3 b"
sorry

mtheorem xcmplx_1_th_57:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds \<one>\<^sub>M /XCMPLX-0K7 (a /XCMPLX-0K7 b) =HIDDENR1 b /XCMPLX-0K7 a"
sorry

mtheorem xcmplx_1_th_58:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds a /XCMPLX-0K7 b =HIDDENR1 \<one>\<^sub>M implies a =HIDDENR1 b"
sorry

mlemma xcmplx_1_lm_12:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds a \<inverse>XCMPLX-0K5 =HIDDENR1 b \<inverse>XCMPLX-0K5 implies a =HIDDENR1 b"
sorry

mtheorem xcmplx_1_th_59:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds \<one>\<^sub>M /XCMPLX-0K7 a =HIDDENR1 \<one>\<^sub>M /XCMPLX-0K7 b implies a =HIDDENR1 b"
sorry

mtheorem xcmplx_1_th_60:
" for a be ComplexXCMPLX-0M1 holds a <>HIDDENR2 0NUMBERSK6 implies a /XCMPLX-0K7 a =HIDDENR1 \<one>\<^sub>M"
  using xcmplx_1_lm_5 sorry

mtheorem xcmplx_1_th_61:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds b <>HIDDENR2 0NUMBERSK6 & b /XCMPLX-0K7 a =HIDDENR1 b implies a =HIDDENR1 \<one>\<^sub>M"
sorry

mtheorem xcmplx_1_th_62:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds a /XCMPLX-0K7 c +XCMPLX-0K2 b /XCMPLX-0K7 c =HIDDENR1 (a +XCMPLX-0K2 b)/XCMPLX-0K7 c"
sorry

mtheorem xcmplx_1_th_63:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for d be ComplexXCMPLX-0M1 holds  for e be ComplexXCMPLX-0M1 holds ((a +XCMPLX-0K2 b)+XCMPLX-0K2 e)/XCMPLX-0K7 d =HIDDENR1 (a /XCMPLX-0K7 d +XCMPLX-0K2 b /XCMPLX-0K7 d)+XCMPLX-0K2 e /XCMPLX-0K7 d"
sorry

mtheorem xcmplx_1_th_64:
" for a be ComplexXCMPLX-0M1 holds (a +XCMPLX-0K2 a)/XCMPLX-0K7 \<two>\<^sub>M =HIDDENR1 a"
   sorry

mtheorem xcmplx_1_th_65:
" for a be ComplexXCMPLX-0M1 holds a /XCMPLX-0K7 \<two>\<^sub>M +XCMPLX-0K2 a /XCMPLX-0K7 \<two>\<^sub>M =HIDDENR1 a"
   sorry

mtheorem xcmplx_1_th_66:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds a =HIDDENR1 (a +XCMPLX-0K2 b)/XCMPLX-0K7 \<two>\<^sub>M implies a =HIDDENR1 b"
   sorry

mtheorem xcmplx_1_th_67:
" for a be ComplexXCMPLX-0M1 holds ((a +XCMPLX-0K2 a)+XCMPLX-0K2 a)/XCMPLX-0K7 \<three>\<^sub>M =HIDDENR1 a"
   sorry

mtheorem xcmplx_1_th_68:
" for a be ComplexXCMPLX-0M1 holds (a /XCMPLX-0K7 \<three>\<^sub>M +XCMPLX-0K2 a /XCMPLX-0K7 \<three>\<^sub>M)+XCMPLX-0K2 a /XCMPLX-0K7 \<three>\<^sub>M =HIDDENR1 a"
   sorry

mtheorem xcmplx_1_th_69:
" for a be ComplexXCMPLX-0M1 holds (((a +XCMPLX-0K2 a)+XCMPLX-0K2 a)+XCMPLX-0K2 a)/XCMPLX-0K7 \<four>\<^sub>M =HIDDENR1 a"
   sorry

mtheorem xcmplx_1_th_70:
" for a be ComplexXCMPLX-0M1 holds ((a /XCMPLX-0K7 \<four>\<^sub>M +XCMPLX-0K2 a /XCMPLX-0K7 \<four>\<^sub>M)+XCMPLX-0K2 a /XCMPLX-0K7 \<four>\<^sub>M)+XCMPLX-0K2 a /XCMPLX-0K7 \<four>\<^sub>M =HIDDENR1 a"
   sorry

mtheorem xcmplx_1_th_71:
" for a be ComplexXCMPLX-0M1 holds a /XCMPLX-0K7 \<four>\<^sub>M +XCMPLX-0K2 a /XCMPLX-0K7 \<four>\<^sub>M =HIDDENR1 a /XCMPLX-0K7 \<two>\<^sub>M"
   sorry

mtheorem xcmplx_1_th_72:
" for a be ComplexXCMPLX-0M1 holds (a +XCMPLX-0K2 a)/XCMPLX-0K7 \<four>\<^sub>M =HIDDENR1 a /XCMPLX-0K7 \<two>\<^sub>M"
   sorry

mtheorem xcmplx_1_th_73:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds a *XCMPLX-0K3 b =HIDDENR1 \<one>\<^sub>M implies a =HIDDENR1 \<one>\<^sub>M /XCMPLX-0K7 b"
sorry

mtheorem xcmplx_1_th_74:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds a *XCMPLX-0K3 (b /XCMPLX-0K7 c) =HIDDENR1 (a *XCMPLX-0K3 b)/XCMPLX-0K7 c"
  using xcmplx_1_lm_8 sorry

mtheorem xcmplx_1_th_75:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for e be ComplexXCMPLX-0M1 holds (a /XCMPLX-0K7 b)*XCMPLX-0K3 e =HIDDENR1 (e /XCMPLX-0K7 b)*XCMPLX-0K3 a"
sorry

mtheorem xcmplx_1_th_76:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds  for d be ComplexXCMPLX-0M1 holds (a /XCMPLX-0K7 b)*XCMPLX-0K3 (c /XCMPLX-0K7 d) =HIDDENR1 (a *XCMPLX-0K3 c)/XCMPLX-0K7 (b *XCMPLX-0K3 d)"
  using xcmplx_1_lm_6 sorry

mtheorem xcmplx_1_th_77:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds a /XCMPLX-0K7 (b /XCMPLX-0K7 c) =HIDDENR1 (a *XCMPLX-0K3 c)/XCMPLX-0K7 b"
  using xcmplx_1_lm_2 sorry

mlemma xcmplx_1_lm_13:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds  for d be ComplexXCMPLX-0M1 holds (a /XCMPLX-0K7 b)/XCMPLX-0K7 (c /XCMPLX-0K7 d) =HIDDENR1 (a *XCMPLX-0K3 d)/XCMPLX-0K7 (b *XCMPLX-0K3 c)"
sorry

mtheorem xcmplx_1_th_78:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds a /XCMPLX-0K7 (b *XCMPLX-0K3 c) =HIDDENR1 (a /XCMPLX-0K7 b)/XCMPLX-0K7 c"
sorry

mtheorem xcmplx_1_th_79:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds a /XCMPLX-0K7 (b /XCMPLX-0K7 c) =HIDDENR1 a *XCMPLX-0K3 (c /XCMPLX-0K7 b)"
sorry

mtheorem xcmplx_1_th_80:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds a /XCMPLX-0K7 (b /XCMPLX-0K7 c) =HIDDENR1 (c /XCMPLX-0K7 b)*XCMPLX-0K3 a"
sorry

mtheorem xcmplx_1_th_81:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for e be ComplexXCMPLX-0M1 holds a /XCMPLX-0K7 (b /XCMPLX-0K7 e) =HIDDENR1 e *XCMPLX-0K3 (a /XCMPLX-0K7 b)"
sorry

mtheorem xcmplx_1_th_82:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds a /XCMPLX-0K7 (b /XCMPLX-0K7 c) =HIDDENR1 (a /XCMPLX-0K7 b)*XCMPLX-0K3 c"
sorry

mlemma xcmplx_1_lm_14:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds a *XCMPLX-0K3 (\<one>\<^sub>M /XCMPLX-0K7 b) =HIDDENR1 a /XCMPLX-0K7 b"
sorry

mlemma xcmplx_1_lm_15:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds (\<one>\<^sub>M /XCMPLX-0K7 c)*XCMPLX-0K3 (a /XCMPLX-0K7 b) =HIDDENR1 a /XCMPLX-0K7 (b *XCMPLX-0K3 c)"
sorry

mtheorem xcmplx_1_th_83:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds  for d be ComplexXCMPLX-0M1 holds (a *XCMPLX-0K3 b)/XCMPLX-0K7 (c *XCMPLX-0K3 d) =HIDDENR1 ((a /XCMPLX-0K7 c)*XCMPLX-0K3 b)/XCMPLX-0K7 d"
sorry

mtheorem xcmplx_1_th_84:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds  for d be ComplexXCMPLX-0M1 holds (a /XCMPLX-0K7 b)/XCMPLX-0K7 (c /XCMPLX-0K7 d) =HIDDENR1 (a *XCMPLX-0K3 d)/XCMPLX-0K7 (b *XCMPLX-0K3 c)"
  using xcmplx_1_lm_13 sorry

mtheorem xcmplx_1_th_85:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds  for d be ComplexXCMPLX-0M1 holds (a /XCMPLX-0K7 c)*XCMPLX-0K3 (b /XCMPLX-0K7 d) =HIDDENR1 (a /XCMPLX-0K7 d)*XCMPLX-0K3 (b /XCMPLX-0K7 c)"
sorry

mtheorem xcmplx_1_th_86:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds  for d be ComplexXCMPLX-0M1 holds  for e be ComplexXCMPLX-0M1 holds a /XCMPLX-0K7 ((b *XCMPLX-0K3 c)*XCMPLX-0K3 (d /XCMPLX-0K7 e)) =HIDDENR1 (e /XCMPLX-0K7 c)*XCMPLX-0K3 (a /XCMPLX-0K7 (b *XCMPLX-0K3 d))"
sorry

mtheorem xcmplx_1_th_87:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds b <>HIDDENR2 0NUMBERSK6 implies (a /XCMPLX-0K7 b)*XCMPLX-0K3 b =HIDDENR1 a"
  using xcmplx_1_lm_3 sorry

mtheorem xcmplx_1_th_88:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds b <>HIDDENR2 0NUMBERSK6 implies a =HIDDENR1 a *XCMPLX-0K3 (b /XCMPLX-0K7 b)"
sorry

mtheorem xcmplx_1_th_89:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds b <>HIDDENR2 0NUMBERSK6 implies a =HIDDENR1 (a *XCMPLX-0K3 b)/XCMPLX-0K7 b"
  using xcmplx_1_lm_9 sorry

mtheorem xcmplx_1_th_90:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds b <>HIDDENR2 0NUMBERSK6 implies a *XCMPLX-0K3 c =HIDDENR1 (a *XCMPLX-0K3 b)*XCMPLX-0K3 (c /XCMPLX-0K7 b)"
sorry

mtheorem xcmplx_1_th_91:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds c <>HIDDENR2 0NUMBERSK6 implies a /XCMPLX-0K7 b =HIDDENR1 (a *XCMPLX-0K3 c)/XCMPLX-0K7 (b *XCMPLX-0K3 c)"
  using xcmplx_1_lm_10 sorry

mtheorem xcmplx_1_th_92:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds c <>HIDDENR2 0NUMBERSK6 implies a /XCMPLX-0K7 b =HIDDENR1 (a /XCMPLX-0K7 (b *XCMPLX-0K3 c))*XCMPLX-0K3 c"
sorry

mtheorem xcmplx_1_th_93:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds b <>HIDDENR2 0NUMBERSK6 implies a *XCMPLX-0K3 c =HIDDENR1 (a *XCMPLX-0K3 b)/XCMPLX-0K7 (b /XCMPLX-0K7 c)"
sorry

mtheorem xcmplx_1_th_94:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds  for d be ComplexXCMPLX-0M1 holds (c <>HIDDENR2 0NUMBERSK6 & d <>HIDDENR2 0NUMBERSK6) & a *XCMPLX-0K3 c =HIDDENR1 b *XCMPLX-0K3 d implies a /XCMPLX-0K7 d =HIDDENR1 b /XCMPLX-0K7 c"
sorry

mtheorem xcmplx_1_th_95:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds  for d be ComplexXCMPLX-0M1 holds (c <>HIDDENR2 0NUMBERSK6 & d <>HIDDENR2 0NUMBERSK6) & a /XCMPLX-0K7 d =HIDDENR1 b /XCMPLX-0K7 c implies a *XCMPLX-0K3 c =HIDDENR1 b *XCMPLX-0K3 d"
sorry

mtheorem xcmplx_1_th_96:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds  for d be ComplexXCMPLX-0M1 holds (c <>HIDDENR2 0NUMBERSK6 & d <>HIDDENR2 0NUMBERSK6) & a *XCMPLX-0K3 c =HIDDENR1 b /XCMPLX-0K7 d implies a *XCMPLX-0K3 d =HIDDENR1 b /XCMPLX-0K7 c"
sorry

mtheorem xcmplx_1_th_97:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds c <>HIDDENR2 0NUMBERSK6 implies a /XCMPLX-0K7 b =HIDDENR1 c *XCMPLX-0K3 ((a /XCMPLX-0K7 c)/XCMPLX-0K7 b)"
sorry

mtheorem xcmplx_1_th_98:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds c <>HIDDENR2 0NUMBERSK6 implies a /XCMPLX-0K7 b =HIDDENR1 (a /XCMPLX-0K7 c)*XCMPLX-0K3 (c /XCMPLX-0K7 b)"
sorry

mtheorem xcmplx_1_th_99:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds a *XCMPLX-0K3 (\<one>\<^sub>M /XCMPLX-0K7 b) =HIDDENR1 a /XCMPLX-0K7 b"
  using xcmplx_1_lm_14 sorry

mlemma xcmplx_1_lm_16:
" for a be ComplexXCMPLX-0M1 holds \<one>\<^sub>M /XCMPLX-0K7 a \<inverse>XCMPLX-0K5 =HIDDENR1 a"
sorry

mtheorem xcmplx_1_th_100:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds a /XCMPLX-0K7 (\<one>\<^sub>M /XCMPLX-0K7 b) =HIDDENR1 a *XCMPLX-0K3 b"
sorry

mtheorem xcmplx_1_th_101:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds (a /XCMPLX-0K7 b)*XCMPLX-0K3 c =HIDDENR1 ((\<one>\<^sub>M /XCMPLX-0K7 b)*XCMPLX-0K3 c)*XCMPLX-0K3 a"
sorry

mtheorem xcmplx_1_th_102:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds (\<one>\<^sub>M /XCMPLX-0K7 a)*XCMPLX-0K3 (\<one>\<^sub>M /XCMPLX-0K7 b) =HIDDENR1 \<one>\<^sub>M /XCMPLX-0K7 (a *XCMPLX-0K3 b)"
sorry

mtheorem xcmplx_1_th_103:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds (\<one>\<^sub>M /XCMPLX-0K7 c)*XCMPLX-0K3 (a /XCMPLX-0K7 b) =HIDDENR1 a /XCMPLX-0K7 (b *XCMPLX-0K3 c)"
  using xcmplx_1_lm_15 sorry

mtheorem xcmplx_1_th_104:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds (a /XCMPLX-0K7 b)/XCMPLX-0K7 c =HIDDENR1 (\<one>\<^sub>M /XCMPLX-0K7 b)*XCMPLX-0K3 (a /XCMPLX-0K7 c)"
sorry

mtheorem xcmplx_1_th_105:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds (a /XCMPLX-0K7 b)/XCMPLX-0K7 c =HIDDENR1 (\<one>\<^sub>M /XCMPLX-0K7 c)*XCMPLX-0K3 (a /XCMPLX-0K7 b)"
sorry

mtheorem xcmplx_1_th_106:
" for a be ComplexXCMPLX-0M1 holds a <>HIDDENR2 0NUMBERSK6 implies a *XCMPLX-0K3 (\<one>\<^sub>M /XCMPLX-0K7 a) =HIDDENR1 \<one>\<^sub>M"
sorry

mtheorem xcmplx_1_th_107:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds b <>HIDDENR2 0NUMBERSK6 implies a =HIDDENR1 (a *XCMPLX-0K3 b)*XCMPLX-0K3 (\<one>\<^sub>M /XCMPLX-0K7 b)"
sorry

mtheorem xcmplx_1_th_108:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds b <>HIDDENR2 0NUMBERSK6 implies a =HIDDENR1 a *XCMPLX-0K3 ((\<one>\<^sub>M /XCMPLX-0K7 b)*XCMPLX-0K3 b)"
sorry

mtheorem xcmplx_1_th_109:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds b <>HIDDENR2 0NUMBERSK6 implies a =HIDDENR1 (a *XCMPLX-0K3 (\<one>\<^sub>M /XCMPLX-0K7 b))*XCMPLX-0K3 b"
sorry

mtheorem xcmplx_1_th_110:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds b <>HIDDENR2 0NUMBERSK6 implies a =HIDDENR1 a /XCMPLX-0K7 (b *XCMPLX-0K3 (\<one>\<^sub>M /XCMPLX-0K7 b))"
sorry

mtheorem xcmplx_1_th_111:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds a <>HIDDENR2 0NUMBERSK6 & b <>HIDDENR2 0NUMBERSK6 implies \<one>\<^sub>M /XCMPLX-0K7 (a *XCMPLX-0K3 b) <>HIDDENR2 0NUMBERSK6"
   sorry

mtheorem xcmplx_1_th_112:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds a <>HIDDENR2 0NUMBERSK6 & b <>HIDDENR2 0NUMBERSK6 implies (a /XCMPLX-0K7 b)*XCMPLX-0K3 (b /XCMPLX-0K7 a) =HIDDENR1 \<one>\<^sub>M"
sorry

mtheorem xcmplx_1_th_113:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds b <>HIDDENR2 0NUMBERSK6 implies a /XCMPLX-0K7 b +XCMPLX-0K2 c =HIDDENR1 (a +XCMPLX-0K2 b *XCMPLX-0K3 c)/XCMPLX-0K7 b"
sorry

mtheorem xcmplx_1_th_114:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds c <>HIDDENR2 0NUMBERSK6 implies a +XCMPLX-0K2 b =HIDDENR1 c *XCMPLX-0K3 (a /XCMPLX-0K7 c +XCMPLX-0K2 b /XCMPLX-0K7 c)"
sorry

mtheorem xcmplx_1_th_115:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds c <>HIDDENR2 0NUMBERSK6 implies a +XCMPLX-0K2 b =HIDDENR1 (a *XCMPLX-0K3 c +XCMPLX-0K2 b *XCMPLX-0K3 c)/XCMPLX-0K7 c"
sorry

mtheorem xcmplx_1_th_116:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds  for d be ComplexXCMPLX-0M1 holds b <>HIDDENR2 0NUMBERSK6 & d <>HIDDENR2 0NUMBERSK6 implies a /XCMPLX-0K7 b +XCMPLX-0K2 c /XCMPLX-0K7 d =HIDDENR1 (a *XCMPLX-0K3 d +XCMPLX-0K2 c *XCMPLX-0K3 b)/XCMPLX-0K7 (b *XCMPLX-0K3 d)"
sorry

mtheorem xcmplx_1_th_117:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds a <>HIDDENR2 0NUMBERSK6 implies a +XCMPLX-0K2 b =HIDDENR1 a *XCMPLX-0K3 (\<one>\<^sub>M +XCMPLX-0K2 b /XCMPLX-0K7 a)"
sorry

mtheorem xcmplx_1_th_118:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds a /XCMPLX-0K7 (\<two>\<^sub>M *XCMPLX-0K3 b) +XCMPLX-0K2 a /XCMPLX-0K7 (\<two>\<^sub>M *XCMPLX-0K3 b) =HIDDENR1 a /XCMPLX-0K7 b"
sorry

mtheorem xcmplx_1_th_119:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds (a /XCMPLX-0K7 (\<three>\<^sub>M *XCMPLX-0K3 b) +XCMPLX-0K2 a /XCMPLX-0K7 (\<three>\<^sub>M *XCMPLX-0K3 b))+XCMPLX-0K2 a /XCMPLX-0K7 (\<three>\<^sub>M *XCMPLX-0K3 b) =HIDDENR1 a /XCMPLX-0K7 b"
sorry

mlemma xcmplx_1_lm_17:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds -XCMPLX-0K4 a /XCMPLX-0K7 b =HIDDENR1 (-XCMPLX-0K4 a)/XCMPLX-0K7 b"
sorry

mtheorem xcmplx_1_th_120:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds a /XCMPLX-0K7 c -XCMPLX-0K6 b /XCMPLX-0K7 c =HIDDENR1 (a -XCMPLX-0K6 b)/XCMPLX-0K7 c"
sorry

mtheorem xcmplx_1_th_121:
" for a be ComplexXCMPLX-0M1 holds a -XCMPLX-0K6 a /XCMPLX-0K7 \<two>\<^sub>M =HIDDENR1 a /XCMPLX-0K7 \<two>\<^sub>M"
   sorry

mtheorem xcmplx_1_th_122:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds  for d be ComplexXCMPLX-0M1 holds ((a -XCMPLX-0K6 b)-XCMPLX-0K6 c)/XCMPLX-0K7 d =HIDDENR1 (a /XCMPLX-0K7 d -XCMPLX-0K6 b /XCMPLX-0K7 d)-XCMPLX-0K6 c /XCMPLX-0K7 d"
sorry

mtheorem xcmplx_1_th_123:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for d be ComplexXCMPLX-0M1 holds  for e be ComplexXCMPLX-0M1 holds ((b <>HIDDENR2 0NUMBERSK6 & d <>HIDDENR2 0NUMBERSK6) & b <>HIDDENR2 d) & a /XCMPLX-0K7 b =HIDDENR1 e /XCMPLX-0K7 d implies a /XCMPLX-0K7 b =HIDDENR1 (a -XCMPLX-0K6 e)/XCMPLX-0K7 (b -XCMPLX-0K6 d)"
sorry

mtheorem xcmplx_1_th_124:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for d be ComplexXCMPLX-0M1 holds  for e be ComplexXCMPLX-0M1 holds ((a +XCMPLX-0K2 b)-XCMPLX-0K6 e)/XCMPLX-0K7 d =HIDDENR1 (a /XCMPLX-0K7 d +XCMPLX-0K2 b /XCMPLX-0K7 d)-XCMPLX-0K6 e /XCMPLX-0K7 d"
sorry

mtheorem xcmplx_1_th_125:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for d be ComplexXCMPLX-0M1 holds  for e be ComplexXCMPLX-0M1 holds ((a -XCMPLX-0K6 b)+XCMPLX-0K2 e)/XCMPLX-0K7 d =HIDDENR1 (a /XCMPLX-0K7 d -XCMPLX-0K6 b /XCMPLX-0K7 d)+XCMPLX-0K2 e /XCMPLX-0K7 d"
sorry

mtheorem xcmplx_1_th_126:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for e be ComplexXCMPLX-0M1 holds b <>HIDDENR2 0NUMBERSK6 implies a /XCMPLX-0K7 b -XCMPLX-0K6 e =HIDDENR1 (a -XCMPLX-0K6 e *XCMPLX-0K3 b)/XCMPLX-0K7 b"
sorry

mtheorem xcmplx_1_th_127:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds b <>HIDDENR2 0NUMBERSK6 implies c -XCMPLX-0K6 a /XCMPLX-0K7 b =HIDDENR1 (c *XCMPLX-0K3 b -XCMPLX-0K6 a)/XCMPLX-0K7 b"
sorry

mtheorem xcmplx_1_th_128:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds c <>HIDDENR2 0NUMBERSK6 implies a -XCMPLX-0K6 b =HIDDENR1 c *XCMPLX-0K3 (a /XCMPLX-0K7 c -XCMPLX-0K6 b /XCMPLX-0K7 c)"
sorry

mtheorem xcmplx_1_th_129:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds c <>HIDDENR2 0NUMBERSK6 implies a -XCMPLX-0K6 b =HIDDENR1 (a *XCMPLX-0K3 c -XCMPLX-0K6 b *XCMPLX-0K3 c)/XCMPLX-0K7 c"
sorry

mtheorem xcmplx_1_th_130:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds  for d be ComplexXCMPLX-0M1 holds b <>HIDDENR2 0NUMBERSK6 & d <>HIDDENR2 0NUMBERSK6 implies a /XCMPLX-0K7 b -XCMPLX-0K6 c /XCMPLX-0K7 d =HIDDENR1 (a *XCMPLX-0K3 d -XCMPLX-0K6 c *XCMPLX-0K3 b)/XCMPLX-0K7 (b *XCMPLX-0K3 d)"
sorry

mtheorem xcmplx_1_th_131:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds a <>HIDDENR2 0NUMBERSK6 implies a -XCMPLX-0K6 b =HIDDENR1 a *XCMPLX-0K3 (\<one>\<^sub>M -XCMPLX-0K6 b /XCMPLX-0K7 a)"
sorry

mtheorem xcmplx_1_th_132:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds a <>HIDDENR2 0NUMBERSK6 implies c =HIDDENR1 ((a *XCMPLX-0K3 c +XCMPLX-0K2 b)-XCMPLX-0K6 b)/XCMPLX-0K7 a"
  using xcmplx_1_lm_9 sorry

mtheorem xcmplx_1_th_133:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds -XCMPLX-0K4 a =HIDDENR1 -XCMPLX-0K4 b implies a =HIDDENR1 b"
   sorry

mtheorem xcmplx_1_th_134:
" for a be ComplexXCMPLX-0M1 holds -XCMPLX-0K4 a =HIDDENR1 0NUMBERSK6 implies a =HIDDENR1 0NUMBERSK6"
   sorry

mtheorem xcmplx_1_th_135:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds a +XCMPLX-0K2 (-XCMPLX-0K4 b) =HIDDENR1 0NUMBERSK6 implies a =HIDDENR1 b"
   sorry

mtheorem xcmplx_1_th_136:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds a =HIDDENR1 (a +XCMPLX-0K2 b)+XCMPLX-0K2 (-XCMPLX-0K4 b)"
   sorry

mtheorem xcmplx_1_th_137:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds a =HIDDENR1 a +XCMPLX-0K2 (b +XCMPLX-0K2 (-XCMPLX-0K4 b))"
   sorry

mtheorem xcmplx_1_th_138:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds a =HIDDENR1 ((-XCMPLX-0K4 b)+XCMPLX-0K2 a)+XCMPLX-0K2 b"
   sorry

mtheorem xcmplx_1_th_139:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds -XCMPLX-0K4 (a +XCMPLX-0K2 b) =HIDDENR1 (-XCMPLX-0K4 a)+XCMPLX-0K2 (-XCMPLX-0K4 b)"
   sorry

mtheorem xcmplx_1_th_140:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds -XCMPLX-0K4 ((-XCMPLX-0K4 a)+XCMPLX-0K2 b) =HIDDENR1 a +XCMPLX-0K2 (-XCMPLX-0K4 b)"
   sorry

mtheorem xcmplx_1_th_141:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds a +XCMPLX-0K2 b =HIDDENR1 -XCMPLX-0K4 ((-XCMPLX-0K4 a)+XCMPLX-0K2 (-XCMPLX-0K4 b))"
   sorry

mtheorem xcmplx_1_th_142:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds -XCMPLX-0K4 (a -XCMPLX-0K6 b) =HIDDENR1 b -XCMPLX-0K6 a"
   sorry

mtheorem xcmplx_1_th_143:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds (-XCMPLX-0K4 a)-XCMPLX-0K6 b =HIDDENR1 (-XCMPLX-0K4 b)-XCMPLX-0K6 a"
   sorry

mtheorem xcmplx_1_th_144:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds a =HIDDENR1 (-XCMPLX-0K4 b)-XCMPLX-0K6 ((-XCMPLX-0K4 a)-XCMPLX-0K6 b)"
   sorry

mtheorem xcmplx_1_th_145:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds ((-XCMPLX-0K4 a)-XCMPLX-0K6 b)-XCMPLX-0K6 c =HIDDENR1 ((-XCMPLX-0K4 a)-XCMPLX-0K6 c)-XCMPLX-0K6 b"
   sorry

mtheorem xcmplx_1_th_146:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds ((-XCMPLX-0K4 a)-XCMPLX-0K6 b)-XCMPLX-0K6 c =HIDDENR1 ((-XCMPLX-0K4 b)-XCMPLX-0K6 c)-XCMPLX-0K6 a"
   sorry

mtheorem xcmplx_1_th_147:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds ((-XCMPLX-0K4 a)-XCMPLX-0K6 b)-XCMPLX-0K6 c =HIDDENR1 ((-XCMPLX-0K4 c)-XCMPLX-0K6 b)-XCMPLX-0K6 a"
   sorry

mtheorem xcmplx_1_th_148:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds (c -XCMPLX-0K6 a)-XCMPLX-0K6 (c -XCMPLX-0K6 b) =HIDDENR1 -XCMPLX-0K4 (a -XCMPLX-0K6 b)"
   sorry

mtheorem xcmplx_1_th_149:
" for a be ComplexXCMPLX-0M1 holds 0NUMBERSK6 -XCMPLX-0K6 a =HIDDENR1 -XCMPLX-0K4 a"
   sorry

mtheorem xcmplx_1_th_150:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds a +XCMPLX-0K2 b =HIDDENR1 a -XCMPLX-0K6 (-XCMPLX-0K4 b)"
   sorry

mtheorem xcmplx_1_th_151:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds a =HIDDENR1 a -XCMPLX-0K6 (b +XCMPLX-0K2 (-XCMPLX-0K4 b))"
   sorry

mtheorem xcmplx_1_th_152:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds a -XCMPLX-0K6 c =HIDDENR1 b +XCMPLX-0K2 (-XCMPLX-0K4 c) implies a =HIDDENR1 b"
   sorry

mtheorem xcmplx_1_th_153:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds c -XCMPLX-0K6 a =HIDDENR1 c +XCMPLX-0K2 (-XCMPLX-0K4 b) implies a =HIDDENR1 b"
   sorry

mtheorem xcmplx_1_th_154:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds (a +XCMPLX-0K2 b)-XCMPLX-0K6 c =HIDDENR1 ((-XCMPLX-0K4 c)+XCMPLX-0K2 a)+XCMPLX-0K2 b"
   sorry

mtheorem xcmplx_1_th_155:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds (a -XCMPLX-0K6 b)+XCMPLX-0K2 c =HIDDENR1 ((-XCMPLX-0K4 b)+XCMPLX-0K2 c)+XCMPLX-0K2 a"
   sorry

mtheorem xcmplx_1_th_156:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds a -XCMPLX-0K6 ((-XCMPLX-0K4 b)-XCMPLX-0K6 c) =HIDDENR1 (a +XCMPLX-0K2 b)+XCMPLX-0K2 c"
   sorry

mtheorem xcmplx_1_th_157:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds (a -XCMPLX-0K6 b)-XCMPLX-0K6 c =HIDDENR1 ((-XCMPLX-0K4 b)-XCMPLX-0K6 c)+XCMPLX-0K2 a"
   sorry

mtheorem xcmplx_1_th_158:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds (a -XCMPLX-0K6 b)-XCMPLX-0K6 c =HIDDENR1 ((-XCMPLX-0K4 c)+XCMPLX-0K2 a)-XCMPLX-0K6 b"
   sorry

mtheorem xcmplx_1_th_159:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds (a -XCMPLX-0K6 b)-XCMPLX-0K6 c =HIDDENR1 ((-XCMPLX-0K4 c)-XCMPLX-0K6 b)+XCMPLX-0K2 a"
   sorry

mtheorem xcmplx_1_th_160:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds -XCMPLX-0K4 (a +XCMPLX-0K2 b) =HIDDENR1 (-XCMPLX-0K4 b)-XCMPLX-0K6 a"
   sorry

mtheorem xcmplx_1_th_161:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds -XCMPLX-0K4 (a -XCMPLX-0K6 b) =HIDDENR1 (-XCMPLX-0K4 a)+XCMPLX-0K2 b"
   sorry

mtheorem xcmplx_1_th_162:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds -XCMPLX-0K4 ((-XCMPLX-0K4 a)+XCMPLX-0K2 b) =HIDDENR1 a -XCMPLX-0K6 b"
   sorry

mtheorem xcmplx_1_th_163:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds a +XCMPLX-0K2 b =HIDDENR1 -XCMPLX-0K4 ((-XCMPLX-0K4 a)-XCMPLX-0K6 b)"
   sorry

mtheorem xcmplx_1_th_164:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds ((-XCMPLX-0K4 a)+XCMPLX-0K2 b)-XCMPLX-0K6 c =HIDDENR1 ((-XCMPLX-0K4 c)+XCMPLX-0K2 b)-XCMPLX-0K6 a"
   sorry

mtheorem xcmplx_1_th_165:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds ((-XCMPLX-0K4 a)+XCMPLX-0K2 b)-XCMPLX-0K6 c =HIDDENR1 ((-XCMPLX-0K4 c)-XCMPLX-0K6 a)+XCMPLX-0K2 b"
   sorry

mtheorem xcmplx_1_th_166:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds -XCMPLX-0K4 ((a +XCMPLX-0K2 b)+XCMPLX-0K2 c) =HIDDENR1 ((-XCMPLX-0K4 a)-XCMPLX-0K6 b)-XCMPLX-0K6 c"
   sorry

mtheorem xcmplx_1_th_167:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds -XCMPLX-0K4 ((a +XCMPLX-0K2 b)-XCMPLX-0K6 c) =HIDDENR1 ((-XCMPLX-0K4 a)-XCMPLX-0K6 b)+XCMPLX-0K2 c"
   sorry

mtheorem xcmplx_1_th_168:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds -XCMPLX-0K4 ((a -XCMPLX-0K6 b)+XCMPLX-0K2 c) =HIDDENR1 ((-XCMPLX-0K4 a)+XCMPLX-0K2 b)-XCMPLX-0K6 c"
   sorry

mtheorem xcmplx_1_th_169:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds -XCMPLX-0K4 ((a -XCMPLX-0K6 b)-XCMPLX-0K6 c) =HIDDENR1 ((-XCMPLX-0K4 a)+XCMPLX-0K2 b)+XCMPLX-0K2 c"
   sorry

mtheorem xcmplx_1_th_170:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds -XCMPLX-0K4 (((-XCMPLX-0K4 a)+XCMPLX-0K2 b)+XCMPLX-0K2 c) =HIDDENR1 (a -XCMPLX-0K6 b)-XCMPLX-0K6 c"
   sorry

mtheorem xcmplx_1_th_171:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds -XCMPLX-0K4 (((-XCMPLX-0K4 a)+XCMPLX-0K2 b)-XCMPLX-0K6 c) =HIDDENR1 (a -XCMPLX-0K6 b)+XCMPLX-0K2 c"
   sorry

mtheorem xcmplx_1_th_172:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds -XCMPLX-0K4 (((-XCMPLX-0K4 a)-XCMPLX-0K6 b)+XCMPLX-0K2 c) =HIDDENR1 (a +XCMPLX-0K2 b)-XCMPLX-0K6 c"
   sorry

mtheorem xcmplx_1_th_173:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds -XCMPLX-0K4 (((-XCMPLX-0K4 a)-XCMPLX-0K6 b)-XCMPLX-0K6 c) =HIDDENR1 (a +XCMPLX-0K2 b)+XCMPLX-0K2 c"
   sorry

mtheorem xcmplx_1_th_174:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds (-XCMPLX-0K4 a)*XCMPLX-0K3 b =HIDDENR1 -XCMPLX-0K4 a *XCMPLX-0K3 b"
   sorry

mtheorem xcmplx_1_th_175:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds (-XCMPLX-0K4 a)*XCMPLX-0K3 b =HIDDENR1 a *XCMPLX-0K3 (-XCMPLX-0K4 b)"
   sorry

mtheorem xcmplx_1_th_176:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds (-XCMPLX-0K4 a)*XCMPLX-0K3 (-XCMPLX-0K4 b) =HIDDENR1 a *XCMPLX-0K3 b"
   sorry

mtheorem xcmplx_1_th_177:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds -XCMPLX-0K4 a *XCMPLX-0K3 (-XCMPLX-0K4 b) =HIDDENR1 a *XCMPLX-0K3 b"
   sorry

mtheorem xcmplx_1_th_178:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds -XCMPLX-0K4 (-XCMPLX-0K4 a)*XCMPLX-0K3 b =HIDDENR1 a *XCMPLX-0K3 b"
   sorry

mtheorem xcmplx_1_th_179:
" for a be ComplexXCMPLX-0M1 holds (-XCMPLX-0K4 \<one>\<^sub>M)*XCMPLX-0K3 a =HIDDENR1 -XCMPLX-0K4 a"
   sorry

mtheorem xcmplx_1_th_180:
" for a be ComplexXCMPLX-0M1 holds (-XCMPLX-0K4 a)*XCMPLX-0K3 (-XCMPLX-0K4 \<one>\<^sub>M) =HIDDENR1 a"
   sorry

mtheorem xcmplx_1_th_181:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds b <>HIDDENR2 0NUMBERSK6 & a *XCMPLX-0K3 b =HIDDENR1 -XCMPLX-0K4 b implies a =HIDDENR1 -XCMPLX-0K4 \<one>\<^sub>M"
sorry

mtheorem xcmplx_1_th_182:
" for a be ComplexXCMPLX-0M1 holds a *XCMPLX-0K3 a =HIDDENR1 \<one>\<^sub>M implies a =HIDDENR1 \<one>\<^sub>M or a =HIDDENR1 -XCMPLX-0K4 \<one>\<^sub>M"
sorry

mtheorem xcmplx_1_th_183:
" for a be ComplexXCMPLX-0M1 holds (-XCMPLX-0K4 a)+XCMPLX-0K2 \<two>\<^sub>M *XCMPLX-0K3 a =HIDDENR1 a"
   sorry

mtheorem xcmplx_1_th_184:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds (a -XCMPLX-0K6 b)*XCMPLX-0K3 c =HIDDENR1 (b -XCMPLX-0K6 a)*XCMPLX-0K3 (-XCMPLX-0K4 c)"
   sorry

mtheorem xcmplx_1_th_185:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds (a -XCMPLX-0K6 b)*XCMPLX-0K3 c =HIDDENR1 -XCMPLX-0K4 (b -XCMPLX-0K6 a)*XCMPLX-0K3 c"
   sorry

mtheorem xcmplx_1_th_186:
" for a be ComplexXCMPLX-0M1 holds a -XCMPLX-0K6 \<two>\<^sub>M *XCMPLX-0K3 a =HIDDENR1 -XCMPLX-0K4 a"
   sorry

mtheorem xcmplx_1_th_187:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds -XCMPLX-0K4 a /XCMPLX-0K7 b =HIDDENR1 (-XCMPLX-0K4 a)/XCMPLX-0K7 b"
  using xcmplx_1_lm_17 sorry

mtheorem xcmplx_1_th_188:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds a /XCMPLX-0K7 (-XCMPLX-0K4 b) =HIDDENR1 -XCMPLX-0K4 a /XCMPLX-0K7 b"
sorry

mtheorem xcmplx_1_th_189:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds -XCMPLX-0K4 a /XCMPLX-0K7 (-XCMPLX-0K4 b) =HIDDENR1 a /XCMPLX-0K7 b"
sorry

mtheorem xcmplx_1_th_190:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds -XCMPLX-0K4 (-XCMPLX-0K4 a)/XCMPLX-0K7 b =HIDDENR1 a /XCMPLX-0K7 b"
sorry

mtheorem xcmplx_1_th_191:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds (-XCMPLX-0K4 a)/XCMPLX-0K7 (-XCMPLX-0K4 b) =HIDDENR1 a /XCMPLX-0K7 b"
sorry

mtheorem xcmplx_1_th_192:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds (-XCMPLX-0K4 a)/XCMPLX-0K7 b =HIDDENR1 a /XCMPLX-0K7 (-XCMPLX-0K4 b)"
sorry

mtheorem xcmplx_1_th_193:
" for a be ComplexXCMPLX-0M1 holds -XCMPLX-0K4 a =HIDDENR1 a /XCMPLX-0K7 (-XCMPLX-0K4 \<one>\<^sub>M)"
   sorry

mtheorem xcmplx_1_th_194:
" for a be ComplexXCMPLX-0M1 holds a =HIDDENR1 (-XCMPLX-0K4 a)/XCMPLX-0K7 (-XCMPLX-0K4 \<one>\<^sub>M)"
   sorry

mtheorem xcmplx_1_th_195:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds a /XCMPLX-0K7 b =HIDDENR1 -XCMPLX-0K4 \<one>\<^sub>M implies a =HIDDENR1 -XCMPLX-0K4 b & b =HIDDENR1 -XCMPLX-0K4 a"
sorry

mtheorem xcmplx_1_th_196:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds b <>HIDDENR2 0NUMBERSK6 & b /XCMPLX-0K7 a =HIDDENR1 -XCMPLX-0K4 b implies a =HIDDENR1 -XCMPLX-0K4 \<one>\<^sub>M"
sorry

mtheorem xcmplx_1_th_197:
" for a be ComplexXCMPLX-0M1 holds a <>HIDDENR2 0NUMBERSK6 implies (-XCMPLX-0K4 a)/XCMPLX-0K7 a =HIDDENR1 -XCMPLX-0K4 \<one>\<^sub>M"
sorry

mtheorem xcmplx_1_th_198:
" for a be ComplexXCMPLX-0M1 holds a <>HIDDENR2 0NUMBERSK6 implies a /XCMPLX-0K7 (-XCMPLX-0K4 a) =HIDDENR1 -XCMPLX-0K4 \<one>\<^sub>M"
sorry

mlemma xcmplx_1_lm_18:
" for a be ComplexXCMPLX-0M1 holds a <>HIDDENR2 0NUMBERSK6 & a =HIDDENR1 a \<inverse>XCMPLX-0K5 implies a =HIDDENR1 \<one>\<^sub>M or a =HIDDENR1 -XCMPLX-0K4 \<one>\<^sub>M"
sorry

mtheorem xcmplx_1_th_199:
" for a be ComplexXCMPLX-0M1 holds a <>HIDDENR2 0NUMBERSK6 & a =HIDDENR1 \<one>\<^sub>M /XCMPLX-0K7 a implies a =HIDDENR1 \<one>\<^sub>M or a =HIDDENR1 -XCMPLX-0K4 \<one>\<^sub>M"
sorry

mtheorem xcmplx_1_th_200:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for d be ComplexXCMPLX-0M1 holds  for e be ComplexXCMPLX-0M1 holds ((b <>HIDDENR2 0NUMBERSK6 & d <>HIDDENR2 0NUMBERSK6) & b <>HIDDENR2 -XCMPLX-0K4 d) & a /XCMPLX-0K7 b =HIDDENR1 e /XCMPLX-0K7 d implies a /XCMPLX-0K7 b =HIDDENR1 (a +XCMPLX-0K2 e)/XCMPLX-0K7 (b +XCMPLX-0K2 d)"
sorry

mtheorem xcmplx_1_th_201:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds a \<inverse>XCMPLX-0K5 =HIDDENR1 b \<inverse>XCMPLX-0K5 implies a =HIDDENR1 b"
  using xcmplx_1_lm_12 sorry

mtheorem xcmplx_1_th_202:
"(0NUMBERSK6)\<inverse>XCMPLX-0K5 =HIDDENR1 0NUMBERSK6"
   sorry

mtheorem xcmplx_1_th_203:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds b <>HIDDENR2 0NUMBERSK6 implies a =HIDDENR1 (a *XCMPLX-0K3 b)*XCMPLX-0K3 b \<inverse>XCMPLX-0K5"
sorry

mtheorem xcmplx_1_th_204:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds a \<inverse>XCMPLX-0K5 *XCMPLX-0K3 b \<inverse>XCMPLX-0K5 =HIDDENR1 (a *XCMPLX-0K3 b)\<inverse>XCMPLX-0K5"
  using xcmplx_1_lm_1 sorry

mtheorem xcmplx_1_th_205:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds (a *XCMPLX-0K3 b \<inverse>XCMPLX-0K5)\<inverse>XCMPLX-0K5 =HIDDENR1 a \<inverse>XCMPLX-0K5 *XCMPLX-0K3 b"
  using xcmplx_1_lm_11 sorry

mtheorem xcmplx_1_th_206:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds (a \<inverse>XCMPLX-0K5 *XCMPLX-0K3 b \<inverse>XCMPLX-0K5)\<inverse>XCMPLX-0K5 =HIDDENR1 a *XCMPLX-0K3 b"
sorry

mtheorem xcmplx_1_th_207:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds a <>HIDDENR2 0NUMBERSK6 & b <>HIDDENR2 0NUMBERSK6 implies a *XCMPLX-0K3 b \<inverse>XCMPLX-0K5 <>HIDDENR2 0NUMBERSK6"
   sorry

mtheorem xcmplx_1_th_208:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds a <>HIDDENR2 0NUMBERSK6 & b <>HIDDENR2 0NUMBERSK6 implies a \<inverse>XCMPLX-0K5 *XCMPLX-0K3 b \<inverse>XCMPLX-0K5 <>HIDDENR2 0NUMBERSK6"
   sorry

mtheorem xcmplx_1_th_209:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds a *XCMPLX-0K3 b \<inverse>XCMPLX-0K5 =HIDDENR1 \<one>\<^sub>M implies a =HIDDENR1 b"
sorry

mtheorem xcmplx_1_th_210:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds a *XCMPLX-0K3 b =HIDDENR1 \<one>\<^sub>M implies a =HIDDENR1 b \<inverse>XCMPLX-0K5"
sorry

mtheorem xcmplx_1_th_211:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds a <>HIDDENR2 0NUMBERSK6 & b <>HIDDENR2 0NUMBERSK6 implies a \<inverse>XCMPLX-0K5 +XCMPLX-0K2 b \<inverse>XCMPLX-0K5 =HIDDENR1 (a +XCMPLX-0K2 b)*XCMPLX-0K3 (a *XCMPLX-0K3 b)\<inverse>XCMPLX-0K5"
sorry

mlemma xcmplx_1_lm_19:
" for a be ComplexXCMPLX-0M1 holds (-XCMPLX-0K4 a)\<inverse>XCMPLX-0K5 =HIDDENR1 -XCMPLX-0K4 a \<inverse>XCMPLX-0K5"
sorry

mtheorem xcmplx_1_th_212:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds a <>HIDDENR2 0NUMBERSK6 & b <>HIDDENR2 0NUMBERSK6 implies a \<inverse>XCMPLX-0K5 -XCMPLX-0K6 b \<inverse>XCMPLX-0K5 =HIDDENR1 (b -XCMPLX-0K6 a)*XCMPLX-0K3 (a *XCMPLX-0K3 b)\<inverse>XCMPLX-0K5"
sorry

mtheorem xcmplx_1_th_213:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds (a /XCMPLX-0K7 b)\<inverse>XCMPLX-0K5 =HIDDENR1 b /XCMPLX-0K7 a"
  using xcmplx_1_lm_7 sorry

mtheorem xcmplx_1_th_214:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds a \<inverse>XCMPLX-0K5 /XCMPLX-0K7 b \<inverse>XCMPLX-0K5 =HIDDENR1 b /XCMPLX-0K7 a"
sorry

mtheorem xcmplx_1_th_215:
" for a be ComplexXCMPLX-0M1 holds \<one>\<^sub>M /XCMPLX-0K7 a =HIDDENR1 a \<inverse>XCMPLX-0K5"
  using xcmplx_1_lm_4 sorry

mtheorem xcmplx_1_th_216:
" for a be ComplexXCMPLX-0M1 holds \<one>\<^sub>M /XCMPLX-0K7 a \<inverse>XCMPLX-0K5 =HIDDENR1 a"
  using xcmplx_1_lm_16 sorry

mtheorem xcmplx_1_th_217:
" for a be ComplexXCMPLX-0M1 holds (\<one>\<^sub>M /XCMPLX-0K7 a)\<inverse>XCMPLX-0K5 =HIDDENR1 a"
sorry

mtheorem xcmplx_1_th_218:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds \<one>\<^sub>M /XCMPLX-0K7 a =HIDDENR1 b \<inverse>XCMPLX-0K5 implies a =HIDDENR1 b"
sorry

mtheorem xcmplx_1_th_219:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds a /XCMPLX-0K7 b \<inverse>XCMPLX-0K5 =HIDDENR1 a *XCMPLX-0K3 b"
sorry

mtheorem xcmplx_1_th_220:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds a \<inverse>XCMPLX-0K5 *XCMPLX-0K3 (c /XCMPLX-0K7 b) =HIDDENR1 c /XCMPLX-0K7 (a *XCMPLX-0K3 b)"
sorry

mtheorem xcmplx_1_th_221:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds a \<inverse>XCMPLX-0K5 /XCMPLX-0K7 b =HIDDENR1 (a *XCMPLX-0K3 b)\<inverse>XCMPLX-0K5"
sorry

mtheorem xcmplx_1_th_222:
" for a be ComplexXCMPLX-0M1 holds (-XCMPLX-0K4 a)\<inverse>XCMPLX-0K5 =HIDDENR1 -XCMPLX-0K4 a \<inverse>XCMPLX-0K5"
  using xcmplx_1_lm_19 sorry

mtheorem xcmplx_1_th_223:
" for a be ComplexXCMPLX-0M1 holds a <>HIDDENR2 0NUMBERSK6 & a =HIDDENR1 a \<inverse>XCMPLX-0K5 implies a =HIDDENR1 \<one>\<^sub>M or a =HIDDENR1 -XCMPLX-0K4 \<one>\<^sub>M"
  using xcmplx_1_lm_18 sorry

(*begin*)
mtheorem xcmplx_1_th_224:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds ((a +XCMPLX-0K2 b)+XCMPLX-0K2 c)-XCMPLX-0K6 b =HIDDENR1 a +XCMPLX-0K2 c"
   sorry

mtheorem xcmplx_1_th_225:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds ((a -XCMPLX-0K6 b)+XCMPLX-0K2 c)+XCMPLX-0K2 b =HIDDENR1 a +XCMPLX-0K2 c"
   sorry

mtheorem xcmplx_1_th_226:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds ((a +XCMPLX-0K2 b)-XCMPLX-0K6 c)-XCMPLX-0K6 b =HIDDENR1 a -XCMPLX-0K6 c"
   sorry

mtheorem xcmplx_1_th_227:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds ((a -XCMPLX-0K6 b)-XCMPLX-0K6 c)+XCMPLX-0K2 b =HIDDENR1 a -XCMPLX-0K6 c"
   sorry

mtheorem xcmplx_1_th_228:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds (a -XCMPLX-0K6 a)-XCMPLX-0K6 b =HIDDENR1 -XCMPLX-0K4 b"
   sorry

mtheorem xcmplx_1_th_229:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds ((-XCMPLX-0K4 a)+XCMPLX-0K2 a)-XCMPLX-0K6 b =HIDDENR1 -XCMPLX-0K4 b"
   sorry

mtheorem xcmplx_1_th_230:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds (a -XCMPLX-0K6 b)-XCMPLX-0K6 a =HIDDENR1 -XCMPLX-0K4 b"
   sorry

mtheorem xcmplx_1_th_231:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds ((-XCMPLX-0K4 a)-XCMPLX-0K6 b)+XCMPLX-0K2 a =HIDDENR1 -XCMPLX-0K4 b"
   sorry

(*begin*)
mtheorem xcmplx_1_th_232:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds b <>HIDDENR2 0NUMBERSK6 implies ( ex e be ComplexXCMPLX-0M1 st a =HIDDENR1 b /XCMPLX-0K7 e)"
sorry

mtheorem xcmplx_1_th_233:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds  for d be ComplexXCMPLX-0M1 holds  for e be ComplexXCMPLX-0M1 holds a /XCMPLX-0K7 ((b *XCMPLX-0K3 c)*XCMPLX-0K3 (d /XCMPLX-0K7 e)) =HIDDENR1 (e /XCMPLX-0K7 c)*XCMPLX-0K3 (a /XCMPLX-0K7 (b *XCMPLX-0K3 d))"
sorry

mtheorem xcmplx_1_th_234:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds  for d be ComplexXCMPLX-0M1 holds ((d -XCMPLX-0K6 c)/XCMPLX-0K7 b)*XCMPLX-0K3 a +XCMPLX-0K2 c =HIDDENR1 (\<one>\<^sub>M -XCMPLX-0K6 a /XCMPLX-0K7 b)*XCMPLX-0K3 c +XCMPLX-0K2 (a /XCMPLX-0K7 b)*XCMPLX-0K3 d"
sorry

mtheorem xcmplx_1_th_235:
" for a be ComplexXCMPLX-0M1 holds  for b be ComplexXCMPLX-0M1 holds  for c be ComplexXCMPLX-0M1 holds a <>HIDDENR2 0NUMBERSK6 implies a *XCMPLX-0K3 b +XCMPLX-0K2 c =HIDDENR1 a *XCMPLX-0K3 (b +XCMPLX-0K2 c /XCMPLX-0K7 a)"
sorry

end
