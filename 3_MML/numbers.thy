theory numbers
  imports funct_2 arytm_2 domain_1 card_1
   "../mizar_extension/E_number"
begin
(*begin*)
mlemma numbers_lm_1:
"omegaORDINAL1K4 c=TARSKIR1 (({[TARSKIK4 c,d ] where c be ElementSUBSET-1M1-of omegaORDINAL1K4, d be ElementSUBSET-1M1-of omegaORDINAL1K4 : (c,d)are-coprimeARYTM-3R1 & d <>HIDDENR2 {}ARYTM-3K12 })\\SUBSET-1K6 ({[TARSKIK4 k,\<one>\<^sub>M ] where k be ElementSUBSET-1M1-of omegaORDINAL1K4 :  True  }))\\/XBOOLE-0K2 omegaORDINAL1K4"
  using xboole_1_th_7 sorry

abbreviation(input) NUMBERSK1("NATNUMBERSK1" 355) where
  "NATNUMBERSK1 \<equiv> omegaORDINAL1K4"

mlemma numbers_lm_2:
"\<one>\<^sub>M =XBOOLE-0R4 succORDINAL1K1 (0ORDINAL1K5)"
   sorry

mdef numbers_def_1 ("REALNUMBERSK2" 355 ) where
"func REALNUMBERSK2 \<rightarrow> setHIDDENM2 equals
  (REAL+ARYTM-2K2 \\/XBOOLE-0K2 [:ZFMISC-1K2 {TARSKIK1 0ORDINAL1K5 },REAL+ARYTM-2K2 :])\\SUBSET-1K6 {TARSKIK1 [TARSKIK4 0ORDINAL1K5,0ORDINAL1K5 ] }"
proof-
  (*coherence*)
    show "(REAL+ARYTM-2K2 \\/XBOOLE-0K2 [:ZFMISC-1K2 {TARSKIK1 0ORDINAL1K5 },REAL+ARYTM-2K2 :])\\SUBSET-1K6 {TARSKIK1 [TARSKIK4 0ORDINAL1K5,0ORDINAL1K5 ] } be setHIDDENM2"
       sorry
qed "sorry"

mlemma numbers_lm_3:
"REAL+ARYTM-2K2 c=TARSKIR1 REALNUMBERSK2"
sorry

mtheorem numbers_cl_1:
"cluster REALNUMBERSK2 as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "REALNUMBERSK2 be  non emptyXBOOLE-0V1"
    using numbers_lm_3 xboole_1_th_3 sorry
qed "sorry"

mdef numbers_def_2 ("COMPLEXNUMBERSK3" 228 ) where
"func COMPLEXNUMBERSK3 \<rightarrow> setHIDDENM2 equals
  (FuncsFUNCT-2K9({TARSKIK2 0ORDINAL1K5,\<one>\<^sub>M },REALNUMBERSK2) \\SUBSET-1K6 ({x where x be ElementFUNCT-2M4\<^bsub>({TARSKIK2 0ORDINAL1K5,\<one>\<^sub>M },REALNUMBERSK2)\<^esub>-of FuncsFUNCT-2K9({TARSKIK2 0ORDINAL1K5,\<one>\<^sub>M },REALNUMBERSK2) : x .FUNCT-1K1 \<one>\<^sub>M =XBOOLE-0R4 0ORDINAL1K5 }))\\/XBOOLE-0K2 REALNUMBERSK2"
proof-
  (*coherence*)
    show "(FuncsFUNCT-2K9({TARSKIK2 0ORDINAL1K5,\<one>\<^sub>M },REALNUMBERSK2) \\SUBSET-1K6 ({x where x be ElementFUNCT-2M4\<^bsub>({TARSKIK2 0ORDINAL1K5,\<one>\<^sub>M },REALNUMBERSK2)\<^esub>-of FuncsFUNCT-2K9({TARSKIK2 0ORDINAL1K5,\<one>\<^sub>M },REALNUMBERSK2) : x .FUNCT-1K1 \<one>\<^sub>M =XBOOLE-0R4 0ORDINAL1K5 }))\\/XBOOLE-0K2 REALNUMBERSK2 be setHIDDENM2"
       sorry
qed "sorry"

mdef numbers_def_3 ("RATNUMBERSK4" 355 ) where
"func RATNUMBERSK4 \<rightarrow> setHIDDENM2 equals
  (RAT+ARYTM-3K5 \\/XBOOLE-0K2 [:ZFMISC-1K2 {TARSKIK1 0ORDINAL1K5 },RAT+ARYTM-3K5 :])\\SUBSET-1K6 {TARSKIK1 [TARSKIK4 0ORDINAL1K5,0ORDINAL1K5 ] }"
proof-
  (*coherence*)
    show "(RAT+ARYTM-3K5 \\/XBOOLE-0K2 [:ZFMISC-1K2 {TARSKIK1 0ORDINAL1K5 },RAT+ARYTM-3K5 :])\\SUBSET-1K6 {TARSKIK1 [TARSKIK4 0ORDINAL1K5,0ORDINAL1K5 ] } be setHIDDENM2"
       sorry
qed "sorry"

mdef numbers_def_4 ("INTNUMBERSK5" 355 ) where
"func INTNUMBERSK5 \<rightarrow> setHIDDENM2 equals
  (NATNUMBERSK1 \\/XBOOLE-0K2 [:ZFMISC-1K2 {TARSKIK1 0ORDINAL1K5 },NATNUMBERSK1 :])\\SUBSET-1K6 {TARSKIK1 [TARSKIK4 0ORDINAL1K5,0ORDINAL1K5 ] }"
proof-
  (*coherence*)
    show "(NATNUMBERSK1 \\/XBOOLE-0K2 [:ZFMISC-1K2 {TARSKIK1 0ORDINAL1K5 },NATNUMBERSK1 :])\\SUBSET-1K6 {TARSKIK1 [TARSKIK4 0ORDINAL1K5,0ORDINAL1K5 ] } be setHIDDENM2"
       sorry
qed "sorry"

mlemma numbers_lm_4:
"RAT+ARYTM-3K5 c=TARSKIR1 RATNUMBERSK4"
sorry

mlemma numbers_lm_5:
"NATNUMBERSK1 c=TARSKIR1 INTNUMBERSK5"
sorry

mtheorem numbers_cl_2:
"cluster COMPLEXNUMBERSK3 as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "COMPLEXNUMBERSK3 be  non emptyXBOOLE-0V1"
     sorry
qed "sorry"

mtheorem numbers_cl_3:
"cluster RATNUMBERSK4 as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "RATNUMBERSK4 be  non emptyXBOOLE-0V1"
    using numbers_lm_4 xboole_1_th_3 sorry
qed "sorry"

mtheorem numbers_cl_4:
"cluster INTNUMBERSK5 as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "INTNUMBERSK5 be  non emptyXBOOLE-0V1"
    using numbers_lm_5 xboole_1_th_3 sorry
qed "sorry"

reserve i, j, k for "ElementSUBSET-1M1-of NATNUMBERSK1"
reserve a, b for "ElementSUBSET-1M1-of REALNUMBERSK2"
mlemma numbers_lm_6:
" for x be setHIDDENM2 holds  for y be setHIDDENM2 holds  for z be setHIDDENM2 holds [TARSKIK4 x,y ] =HIDDENR1 {TARSKIK1 z} implies z =XBOOLE-0R4 {TARSKIK1 x} & x =XBOOLE-0R4 y"
sorry

mlemma numbers_lm_7:
" for a be ElementSUBSET-1M1-of REALNUMBERSK2 holds  for b be ElementSUBSET-1M1-of REALNUMBERSK2 holds  not (0ORDINAL1K5,oneARYTM-3K13)-->FUNCT-4K7\<^bsub>(REALNUMBERSK2)\<^esub>(a,b) inTARSKIR2 REALNUMBERSK2"
sorry

abbreviation(input) NUMBERSK6("0NUMBERSK6" 164) where
  "0NUMBERSK6 \<equiv> 0ORDINAL1K5"

mtheorem numbers_add_1:
"cluster 0ORDINAL1K5 as-term-is ElementSUBSET-1M1-of omegaORDINAL1K4"
proof
(*coherence*)
  show "0ORDINAL1K5 be ElementSUBSET-1M1-of omegaORDINAL1K4"
    using ordinal1_def_11 sorry
qed "sorry"

mtheorem numbers_th_1:
"REALNUMBERSK2 c<XBOOLE-0R2 COMPLEXNUMBERSK3"
sorry

mlemma numbers_lm_8:
"RATNUMBERSK4 c=TARSKIR1 REALNUMBERSK2"
sorry

reserve r, s, t for "ElementSUBSET-1M1-of RAT+ARYTM-3K5"
reserve i, j, k for "ElementSUBSET-1M1-of omegaORDINAL1K4"
mlemma numbers_lm_9:
" for i be ordinalORDINAL1V3\<bar>ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds  for j be ordinalORDINAL1V3\<bar>ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds i inTARSKIR2 j implies i <ARYTM-3R4 j"
sorry

mlemma numbers_lm_10:
" for i be ordinalORDINAL1V3\<bar>ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds  for j be ordinalORDINAL1V3\<bar>ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds i c=ORDINAL1R1 j implies i <='ARYTM-3R3 j"
sorry

mlemma numbers_lm_11:
"\<two>\<^sub>M =XBOOLE-0R4 {TARSKIK2 0NUMBERSK6,\<one>\<^sub>M }"
sorry

mlemma numbers_lm_12:
" for i be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 holds  for k be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 holds i *^ORDINAL3K9 i =XBOOLE-0R4 \<two>\<^sub>M *^ORDINAL3K9 k implies ( ex k be naturalORDINAL1V7\<bar>OrdinalORDINAL1M3 st i =XBOOLE-0R4 \<two>\<^sub>M *^ORDINAL3K9 k)"
sorry

mlemma numbers_lm_13:
"oneARYTM-3K13 +ARYTM-3K10 oneARYTM-3K13 =XBOOLE-0R4 \<two>\<^sub>M"
sorry

mlemma numbers_lm_14:
" for two be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds  for i be ElementSUBSET-1M1-of RAT+ARYTM-3K5 holds two =XBOOLE-0R4 \<two>\<^sub>M implies i +ARYTM-3K10 i =XBOOLE-0R4 two *'ARYTM-3K11 i"
sorry

mtheorem numbers_th_2:
"RATNUMBERSK4 c<XBOOLE-0R2 REALNUMBERSK2"
sorry

mtheorem numbers_th_3:
"RATNUMBERSK4 c<XBOOLE-0R2 COMPLEXNUMBERSK3"
  using numbers_th_1 numbers_th_2 xboole_1_th_56 sorry

mlemma numbers_lm_15:
"INTNUMBERSK5 c=TARSKIR1 RATNUMBERSK4"
sorry

mtheorem numbers_th_4:
"INTNUMBERSK5 c<XBOOLE-0R2 RATNUMBERSK4"
sorry

mtheorem numbers_th_5:
"INTNUMBERSK5 c<XBOOLE-0R2 REALNUMBERSK2"
  using numbers_th_2 numbers_th_4 xboole_1_th_56 sorry

mtheorem numbers_th_6:
"INTNUMBERSK5 c<XBOOLE-0R2 COMPLEXNUMBERSK3"
  using numbers_th_1 numbers_th_5 xboole_1_th_56 sorry

mtheorem numbers_th_7:
"NATNUMBERSK1 c<XBOOLE-0R2 INTNUMBERSK5"
sorry

mtheorem numbers_th_8:
"NATNUMBERSK1 c<XBOOLE-0R2 RATNUMBERSK4"
  using numbers_th_4 numbers_th_7 xboole_1_th_56 sorry

mtheorem numbers_th_9:
"NATNUMBERSK1 c<XBOOLE-0R2 REALNUMBERSK2"
  using numbers_th_2 numbers_th_8 xboole_1_th_56 sorry

mtheorem numbers_th_10:
"NATNUMBERSK1 c<XBOOLE-0R2 COMPLEXNUMBERSK3"
  using numbers_th_1 numbers_th_9 xboole_1_th_56 sorry

(*begin*)
mtheorem numbers_th_11:
"REALNUMBERSK2 c=TARSKIR1 COMPLEXNUMBERSK3"
  using numbers_th_1 sorry

mtheorem numbers_th_12:
"RATNUMBERSK4 c=TARSKIR1 REALNUMBERSK2"
  using numbers_th_2 sorry

mtheorem numbers_th_13:
"RATNUMBERSK4 c=TARSKIR1 COMPLEXNUMBERSK3"
  using numbers_th_3 sorry

mtheorem numbers_th_14:
"INTNUMBERSK5 c=TARSKIR1 RATNUMBERSK4"
  using numbers_th_4 sorry

mtheorem numbers_th_15:
"INTNUMBERSK5 c=TARSKIR1 REALNUMBERSK2"
  using numbers_th_5 sorry

mtheorem numbers_th_16:
"INTNUMBERSK5 c=TARSKIR1 COMPLEXNUMBERSK3"
  using numbers_th_6 sorry

mtheorem numbers_th_17:
"NATNUMBERSK1 c=TARSKIR1 INTNUMBERSK5"
  using numbers_lm_5 sorry

mtheorem numbers_th_18:
"NATNUMBERSK1 c=TARSKIR1 RATNUMBERSK4"
  using numbers_th_8 sorry

mtheorem numbers_th_19:
"NATNUMBERSK1 c=TARSKIR1 REALNUMBERSK2"
  using numbers_th_9 sorry

mtheorem numbers_th_20:
"NATNUMBERSK1 c=TARSKIR1 COMPLEXNUMBERSK3"
  using numbers_th_10 sorry

mtheorem numbers_th_21:
"REALNUMBERSK2 <>HIDDENR2 COMPLEXNUMBERSK3"
  using numbers_th_1 sorry

mtheorem numbers_th_22:
"RATNUMBERSK4 <>HIDDENR2 REALNUMBERSK2"
  using numbers_th_2 sorry

mtheorem numbers_th_23:
"RATNUMBERSK4 <>HIDDENR2 COMPLEXNUMBERSK3"
  using numbers_th_1 numbers_th_2 sorry

mtheorem numbers_th_24:
"INTNUMBERSK5 <>HIDDENR2 RATNUMBERSK4"
  using numbers_th_4 sorry

mtheorem numbers_th_25:
"INTNUMBERSK5 <>HIDDENR2 REALNUMBERSK2"
  using numbers_th_2 numbers_th_4 sorry

mtheorem numbers_th_26:
"INTNUMBERSK5 <>HIDDENR2 COMPLEXNUMBERSK3"
  using numbers_th_1 numbers_th_2 numbers_th_4 xboole_1_th_56 sorry

mtheorem numbers_th_27:
"NATNUMBERSK1 <>HIDDENR2 INTNUMBERSK5"
  using numbers_th_7 sorry

mtheorem numbers_th_28:
"NATNUMBERSK1 <>HIDDENR2 RATNUMBERSK4"
  using numbers_th_4 numbers_th_7 sorry

mtheorem numbers_th_29:
"NATNUMBERSK1 <>HIDDENR2 REALNUMBERSK2"
  using numbers_th_2 numbers_th_4 numbers_th_7 xboole_1_th_56 sorry

mtheorem numbers_th_30:
"NATNUMBERSK1 <>HIDDENR2 COMPLEXNUMBERSK3"
  using numbers_th_1 numbers_th_2 numbers_th_8 xboole_1_th_56 sorry

mdef numbers_def_5 ("ExtREALNUMBERSK7" 164 ) where
"func ExtREALNUMBERSK7 \<rightarrow> setHIDDENM2 equals
  REALNUMBERSK2 \\/XBOOLE-0K2 {TARSKIK2 REALNUMBERSK2,[TARSKIK4 0NUMBERSK6,REALNUMBERSK2 ] }"
proof-
  (*coherence*)
    show "REALNUMBERSK2 \\/XBOOLE-0K2 {TARSKIK2 REALNUMBERSK2,[TARSKIK4 0NUMBERSK6,REALNUMBERSK2 ] } be setHIDDENM2"
       sorry
qed "sorry"

mtheorem numbers_cl_5:
"cluster ExtREALNUMBERSK7 as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "ExtREALNUMBERSK7 be  non emptyXBOOLE-0V1"
     sorry
qed "sorry"

mtheorem numbers_th_31:
"REALNUMBERSK2 c=TARSKIR1 ExtREALNUMBERSK7"
  using xboole_1_th_7 sorry

mtheorem numbers_th_32:
"REALNUMBERSK2 <>HIDDENR2 ExtREALNUMBERSK7"
sorry

mtheorem numbers_th_33:
"REALNUMBERSK2 c<XBOOLE-0R2 ExtREALNUMBERSK7"
  using numbers_th_31 numbers_th_32 sorry

mtheorem numbers_cl_6:
"cluster INTNUMBERSK5 as-term-is infiniteFINSET-1V2"
proof
(*coherence*)
  show "INTNUMBERSK5 be infiniteFINSET-1V2"
    using numbers_lm_5 finset_1_th_1 sorry
qed "sorry"

mtheorem numbers_cl_7:
"cluster RATNUMBERSK4 as-term-is infiniteFINSET-1V2"
proof
(*coherence*)
  show "RATNUMBERSK4 be infiniteFINSET-1V2"
    using numbers_th_18 finset_1_th_1 sorry
qed "sorry"

mtheorem numbers_cl_8:
"cluster REALNUMBERSK2 as-term-is infiniteFINSET-1V2"
proof
(*coherence*)
  show "REALNUMBERSK2 be infiniteFINSET-1V2"
    using numbers_th_19 finset_1_th_1 sorry
qed "sorry"

mtheorem numbers_cl_9:
"cluster COMPLEXNUMBERSK3 as-term-is infiniteFINSET-1V2"
proof
(*coherence*)
  show "COMPLEXNUMBERSK3 be infiniteFINSET-1V2"
    using numbers_th_20 finset_1_th_1 sorry
qed "sorry"

end
