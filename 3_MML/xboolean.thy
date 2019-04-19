theory xboolean
  imports xcmplx_0
   "../mizar_extension/E_number"
begin
(*begin*)
mdef xboolean_def_1 ("FALSEXBOOLEANK1" 164 ) where
"func FALSEXBOOLEANK1 \<rightarrow> objectHIDDENM1 equals
  0NUMBERSK6"
proof-
  (*coherence*)
    show "0NUMBERSK6 be objectHIDDENM1"
       sorry
qed "sorry"

mdef xboolean_def_2 ("TRUEXBOOLEANK2" 164 ) where
"func TRUEXBOOLEANK2 \<rightarrow> objectHIDDENM1 equals
  \<one>\<^sub>M"
proof-
  (*coherence*)
    show "\<one>\<^sub>M be objectHIDDENM1"
       sorry
qed "sorry"

mdef xboolean_def_3 ("booleanXBOOLEANV1" 70 ) where
"attr booleanXBOOLEANV1 for objectHIDDENM1 means
  (\<lambda>p. p =HIDDENR1 FALSEXBOOLEANK1 or p =HIDDENR1 TRUEXBOOLEANK2)"..

mtheorem xboolean_cl_1:
"cluster FALSEXBOOLEANK1 as-term-is booleanXBOOLEANV1"
proof
(*coherence*)
  show "FALSEXBOOLEANK1 be booleanXBOOLEANV1"
     sorry
qed "sorry"

mtheorem xboolean_cl_2:
"cluster TRUEXBOOLEANK2 as-term-is booleanXBOOLEANV1"
proof
(*coherence*)
  show "TRUEXBOOLEANK2 be booleanXBOOLEANV1"
     sorry
qed "sorry"

mtheorem xboolean_cl_3:
"cluster booleanXBOOLEANV1 for objectHIDDENM1"
proof
(*existence*)
  show " ex it be objectHIDDENM1 st it be booleanXBOOLEANV1"
    using xboolean_def_3 sorry
qed "sorry"

mtheorem xboolean_cl_4:
"cluster booleanXBOOLEANV1 also-is naturalORDINAL1V7 for objectHIDDENM1"
proof
(*coherence*)
  show " for it be objectHIDDENM1 holds it be booleanXBOOLEANV1 implies it be naturalORDINAL1V7"
     sorry
qed "sorry"

reserve p, q, r, s for "booleanXBOOLEANV1\<bar>objectHIDDENM1"
mdef xboolean_def_4 ("''not''XBOOLEANK3  _ " [182]182 ) where
  mlet "p be booleanXBOOLEANV1\<bar>objectHIDDENM1"
"func 'not'XBOOLEANK3 p \<rightarrow> booleanXBOOLEANV1\<bar>objectHIDDENM1 equals
  \<one>\<^sub>M -XCMPLX-0K6 p"
proof-
  (*coherence*)
    show "\<one>\<^sub>M -XCMPLX-0K6 p be booleanXBOOLEANV1\<bar>objectHIDDENM1"
sorry
qed "sorry"

mtheorem XBOOLEANK3_involutiveness:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds 'not'XBOOLEANK3 ('not'XBOOLEANK3 p) =HIDDENR1 p"
sorry

mdef xboolean_def_5 (" _ ''&''XBOOLEANK4  _ " [180,180]180 ) where
  mlet "p be booleanXBOOLEANV1\<bar>objectHIDDENM1", "q be booleanXBOOLEANV1\<bar>objectHIDDENM1"
"func p '&'XBOOLEANK4 q \<rightarrow> objectHIDDENM1 equals
  p *XCMPLX-0K3 q"
proof-
  (*coherence*)
    show "p *XCMPLX-0K3 q be objectHIDDENM1"
       sorry
qed "sorry"

mtheorem XBOOLEANK4_commutativity:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p '&'XBOOLEANK4 q =HIDDENR1 q '&'XBOOLEANK4 p"
sorry

mtheorem XBOOLEANK4_idempotence:
" for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds q =HIDDENR1 q '&'XBOOLEANK4 q"
sorry

mtheorem xboolean_cl_5:
  mlet "p be booleanXBOOLEANV1\<bar>objectHIDDENM1", "q be booleanXBOOLEANV1\<bar>objectHIDDENM1"
"cluster p '&'XBOOLEANK4 q as-term-is booleanXBOOLEANV1"
proof
(*coherence*)
  show "p '&'XBOOLEANK4 q be booleanXBOOLEANV1"
sorry
qed "sorry"

mdef xboolean_def_6 (" _ ''or''XBOOLEANK5  _ " [170,170]170 ) where
  mlet "p be booleanXBOOLEANV1\<bar>objectHIDDENM1", "q be booleanXBOOLEANV1\<bar>objectHIDDENM1"
"func p 'or'XBOOLEANK5 q \<rightarrow> objectHIDDENM1 equals
  'not'XBOOLEANK3 ('not'XBOOLEANK3 p '&'XBOOLEANK4 'not'XBOOLEANK3 q)"
proof-
  (*coherence*)
    show "'not'XBOOLEANK3 ('not'XBOOLEANK3 p '&'XBOOLEANK4 'not'XBOOLEANK3 q) be objectHIDDENM1"
       sorry
qed "sorry"

mtheorem XBOOLEANK5_commutativity:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p 'or'XBOOLEANK5 q =HIDDENR1 q 'or'XBOOLEANK5 p"
sorry

mtheorem XBOOLEANK5_idempotence:
" for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds q =HIDDENR1 q 'or'XBOOLEANK5 q"
sorry

mdef xboolean_def_7 (" _ =>XBOOLEANK6  _ " [169,169]169 ) where
  mlet "p be booleanXBOOLEANV1\<bar>objectHIDDENM1", "q be booleanXBOOLEANV1\<bar>objectHIDDENM1"
"func p =>XBOOLEANK6 q \<rightarrow> objectHIDDENM1 equals
  'not'XBOOLEANK3 p 'or'XBOOLEANK5 q"
proof-
  (*coherence*)
    show "'not'XBOOLEANK3 p 'or'XBOOLEANK5 q be objectHIDDENM1"
       sorry
qed "sorry"

mtheorem xboolean_cl_6:
  mlet "p be booleanXBOOLEANV1\<bar>objectHIDDENM1", "q be booleanXBOOLEANV1\<bar>objectHIDDENM1"
"cluster p 'or'XBOOLEANK5 q as-term-is booleanXBOOLEANV1"
proof
(*coherence*)
  show "p 'or'XBOOLEANK5 q be booleanXBOOLEANV1"
     sorry
qed "sorry"

mtheorem xboolean_cl_7:
  mlet "p be booleanXBOOLEANV1\<bar>objectHIDDENM1", "q be booleanXBOOLEANV1\<bar>objectHIDDENM1"
"cluster p =>XBOOLEANK6 q as-term-is booleanXBOOLEANV1"
proof
(*coherence*)
  show "p =>XBOOLEANK6 q be booleanXBOOLEANV1"
     sorry
qed "sorry"

mdef xboolean_def_8 (" _ <=>XBOOLEANK7  _ " [169,169]169 ) where
  mlet "p be booleanXBOOLEANV1\<bar>objectHIDDENM1", "q be booleanXBOOLEANV1\<bar>objectHIDDENM1"
"func p <=>XBOOLEANK7 q \<rightarrow> objectHIDDENM1 equals
  (p =>XBOOLEANK6 q)'&'XBOOLEANK4 (q =>XBOOLEANK6 p)"
proof-
  (*coherence*)
    show "(p =>XBOOLEANK6 q)'&'XBOOLEANK4 (q =>XBOOLEANK6 p) be objectHIDDENM1"
       sorry
qed "sorry"

mtheorem XBOOLEANK7_commutativity:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p <=>XBOOLEANK7 q =HIDDENR1 q <=>XBOOLEANK7 p"
sorry

mtheorem xboolean_cl_8:
  mlet "p be booleanXBOOLEANV1\<bar>objectHIDDENM1", "q be booleanXBOOLEANV1\<bar>objectHIDDENM1"
"cluster p <=>XBOOLEANK7 q as-term-is booleanXBOOLEANV1"
proof
(*coherence*)
  show "p <=>XBOOLEANK7 q be booleanXBOOLEANV1"
     sorry
qed "sorry"

mdef xboolean_def_9 (" _ ''nand''XBOOLEANK8  _ " [164,164]164 ) where
  mlet "p be booleanXBOOLEANV1\<bar>objectHIDDENM1", "q be booleanXBOOLEANV1\<bar>objectHIDDENM1"
"func p 'nand'XBOOLEANK8 q \<rightarrow> objectHIDDENM1 equals
  'not'XBOOLEANK3 (p '&'XBOOLEANK4 q)"
proof-
  (*coherence*)
    show "'not'XBOOLEANK3 (p '&'XBOOLEANK4 q) be objectHIDDENM1"
       sorry
qed "sorry"

mtheorem XBOOLEANK8_commutativity:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p 'nand'XBOOLEANK8 q =HIDDENR1 q 'nand'XBOOLEANK8 p"
sorry

mdef xboolean_def_10 (" _ ''nor''XBOOLEANK9  _ " [164,164]164 ) where
  mlet "p be booleanXBOOLEANV1\<bar>objectHIDDENM1", "q be booleanXBOOLEANV1\<bar>objectHIDDENM1"
"func p 'nor'XBOOLEANK9 q \<rightarrow> objectHIDDENM1 equals
  'not'XBOOLEANK3 (p 'or'XBOOLEANK5 q)"
proof-
  (*coherence*)
    show "'not'XBOOLEANK3 (p 'or'XBOOLEANK5 q) be objectHIDDENM1"
       sorry
qed "sorry"

mtheorem XBOOLEANK9_commutativity:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p 'nor'XBOOLEANK9 q =HIDDENR1 q 'nor'XBOOLEANK9 p"
sorry

mdef xboolean_def_11 (" _ ''xor''XBOOLEANK10  _ " [164,164]164 ) where
  mlet "p be booleanXBOOLEANV1\<bar>objectHIDDENM1", "q be booleanXBOOLEANV1\<bar>objectHIDDENM1"
"func p 'xor'XBOOLEANK10 q \<rightarrow> objectHIDDENM1 equals
  'not'XBOOLEANK3 (p <=>XBOOLEANK7 q)"
proof-
  (*coherence*)
    show "'not'XBOOLEANK3 (p <=>XBOOLEANK7 q) be objectHIDDENM1"
       sorry
qed "sorry"

mtheorem XBOOLEANK10_commutativity:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p 'xor'XBOOLEANK10 q =HIDDENR1 q 'xor'XBOOLEANK10 p"
sorry

mdef xboolean_def_12 (" _ '''\\''XBOOLEANK11  _ " [164,164]164 ) where
  mlet "p be booleanXBOOLEANV1\<bar>objectHIDDENM1", "q be booleanXBOOLEANV1\<bar>objectHIDDENM1"
"func p '\\'XBOOLEANK11 q \<rightarrow> objectHIDDENM1 equals
  p '&'XBOOLEANK4 'not'XBOOLEANK3 q"
proof-
  (*coherence*)
    show "p '&'XBOOLEANK4 'not'XBOOLEANK3 q be objectHIDDENM1"
       sorry
qed "sorry"

mtheorem xboolean_cl_9:
  mlet "p be booleanXBOOLEANV1\<bar>objectHIDDENM1", "q be booleanXBOOLEANV1\<bar>objectHIDDENM1"
"cluster p 'nand'XBOOLEANK8 q as-term-is booleanXBOOLEANV1"
proof
(*coherence*)
  show "p 'nand'XBOOLEANK8 q be booleanXBOOLEANV1"
     sorry
qed "sorry"

mtheorem xboolean_cl_10:
  mlet "p be booleanXBOOLEANV1\<bar>objectHIDDENM1", "q be booleanXBOOLEANV1\<bar>objectHIDDENM1"
"cluster p 'nor'XBOOLEANK9 q as-term-is booleanXBOOLEANV1"
proof
(*coherence*)
  show "p 'nor'XBOOLEANK9 q be booleanXBOOLEANV1"
     sorry
qed "sorry"

mtheorem xboolean_cl_11:
  mlet "p be booleanXBOOLEANV1\<bar>objectHIDDENM1", "q be booleanXBOOLEANV1\<bar>objectHIDDENM1"
"cluster p 'xor'XBOOLEANK10 q as-term-is booleanXBOOLEANV1"
proof
(*coherence*)
  show "p 'xor'XBOOLEANK10 q be booleanXBOOLEANV1"
     sorry
qed "sorry"

mtheorem xboolean_cl_12:
  mlet "p be booleanXBOOLEANV1\<bar>objectHIDDENM1", "q be booleanXBOOLEANV1\<bar>objectHIDDENM1"
"cluster p '\\'XBOOLEANK11 q as-term-is booleanXBOOLEANV1"
proof
(*coherence*)
  show "p '\\'XBOOLEANK11 q be booleanXBOOLEANV1"
     sorry
qed "sorry"

(*begin*)
mtheorem xboolean_th_1:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p '&'XBOOLEANK4 p =HIDDENR1 p"
   sorry

mtheorem xboolean_th_2:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p '&'XBOOLEANK4 (p '&'XBOOLEANK4 q) =HIDDENR1 p '&'XBOOLEANK4 q"
sorry

mtheorem xboolean_th_3:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p 'or'XBOOLEANK5 p =HIDDENR1 p"
   sorry

mtheorem xboolean_th_4:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p 'or'XBOOLEANK5 (p 'or'XBOOLEANK5 q) =HIDDENR1 p 'or'XBOOLEANK5 q"
sorry

mtheorem xboolean_th_5:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p 'or'XBOOLEANK5 p '&'XBOOLEANK4 q =HIDDENR1 p"
sorry

mtheorem xboolean_th_6:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p '&'XBOOLEANK4 (p 'or'XBOOLEANK5 q) =HIDDENR1 p"
sorry

mtheorem xboolean_th_7:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p '&'XBOOLEANK4 (p 'or'XBOOLEANK5 q) =HIDDENR1 p 'or'XBOOLEANK5 p '&'XBOOLEANK4 q"
sorry

mtheorem xboolean_th_8:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for r be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p '&'XBOOLEANK4 (q 'or'XBOOLEANK5 r) =HIDDENR1 p '&'XBOOLEANK4 q 'or'XBOOLEANK5 p '&'XBOOLEANK4 r"
sorry

mtheorem xboolean_th_9:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for r be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p 'or'XBOOLEANK5 q '&'XBOOLEANK4 r =HIDDENR1 (p 'or'XBOOLEANK5 q)'&'XBOOLEANK4 (p 'or'XBOOLEANK5 r)"
sorry

mtheorem xboolean_th_10:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for r be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds (p '&'XBOOLEANK4 q 'or'XBOOLEANK5 q '&'XBOOLEANK4 r)'or'XBOOLEANK5 r '&'XBOOLEANK4 p =HIDDENR1 ((p 'or'XBOOLEANK5 q)'&'XBOOLEANK4 (q 'or'XBOOLEANK5 r))'&'XBOOLEANK4 (r 'or'XBOOLEANK5 p)"
sorry

mtheorem xboolean_th_11:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p '&'XBOOLEANK4 ('not'XBOOLEANK3 p 'or'XBOOLEANK5 q) =HIDDENR1 p '&'XBOOLEANK4 q"
sorry

mtheorem xboolean_th_12:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p 'or'XBOOLEANK5 'not'XBOOLEANK3 p '&'XBOOLEANK4 q =HIDDENR1 p 'or'XBOOLEANK5 q"
sorry

mtheorem xboolean_th_13:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p =>XBOOLEANK6 (p =>XBOOLEANK6 q) =HIDDENR1 p =>XBOOLEANK6 q"
sorry

mtheorem xboolean_th_14:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p '&'XBOOLEANK4 (p =>XBOOLEANK6 q) =HIDDENR1 p '&'XBOOLEANK4 q"
sorry

mtheorem xboolean_th_15:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p =>XBOOLEANK6 p '&'XBOOLEANK4 q =HIDDENR1 p =>XBOOLEANK6 q"
sorry

mtheorem xboolean_th_16:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p '&'XBOOLEANK4 'not'XBOOLEANK3 (p =>XBOOLEANK6 q) =HIDDENR1 p '&'XBOOLEANK4 'not'XBOOLEANK3 q"
sorry

mtheorem xboolean_th_17:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds 'not'XBOOLEANK3 p 'or'XBOOLEANK5 (p =>XBOOLEANK6 q) =HIDDENR1 p =>XBOOLEANK6 q"
sorry

mtheorem xboolean_th_18:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds 'not'XBOOLEANK3 p '&'XBOOLEANK4 (p =>XBOOLEANK6 q) =HIDDENR1 'not'XBOOLEANK3 p 'or'XBOOLEANK5 'not'XBOOLEANK3 p '&'XBOOLEANK4 q"
sorry

mtheorem xboolean_th_19:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for r be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds (p <=>XBOOLEANK7 q)<=>XBOOLEANK7 r =HIDDENR1 p <=>XBOOLEANK7 (q <=>XBOOLEANK7 r)"
sorry

mtheorem xboolean_th_20:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p '&'XBOOLEANK4 (p <=>XBOOLEANK7 q) =HIDDENR1 p '&'XBOOLEANK4 q"
sorry

mtheorem xboolean_th_21:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds 'not'XBOOLEANK3 p '&'XBOOLEANK4 (p <=>XBOOLEANK7 q) =HIDDENR1 'not'XBOOLEANK3 p '&'XBOOLEANK4 'not'XBOOLEANK3 q"
sorry

mtheorem xboolean_th_22:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for r be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p '&'XBOOLEANK4 (q <=>XBOOLEANK7 r) =HIDDENR1 (p '&'XBOOLEANK4 ('not'XBOOLEANK3 q 'or'XBOOLEANK5 r))'&'XBOOLEANK4 ('not'XBOOLEANK3 r 'or'XBOOLEANK5 q)"
   sorry

mtheorem xboolean_th_23:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for r be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p 'or'XBOOLEANK5 (q <=>XBOOLEANK7 r) =HIDDENR1 ((p 'or'XBOOLEANK5 'not'XBOOLEANK3 q)'or'XBOOLEANK5 r)'&'XBOOLEANK4 ((p 'or'XBOOLEANK5 'not'XBOOLEANK3 r)'or'XBOOLEANK5 q)"
sorry

mtheorem xboolean_th_24:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds 'not'XBOOLEANK3 p '&'XBOOLEANK4 (p <=>XBOOLEANK7 q) =HIDDENR1 ('not'XBOOLEANK3 p '&'XBOOLEANK4 'not'XBOOLEANK3 q)'&'XBOOLEANK4 ('not'XBOOLEANK3 p 'or'XBOOLEANK5 q)"
sorry

mtheorem xboolean_th_25:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for r be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds 'not'XBOOLEANK3 p '&'XBOOLEANK4 (q <=>XBOOLEANK7 r) =HIDDENR1 ('not'XBOOLEANK3 p '&'XBOOLEANK4 ('not'XBOOLEANK3 q 'or'XBOOLEANK5 r))'&'XBOOLEANK4 ('not'XBOOLEANK3 r 'or'XBOOLEANK5 q)"
   sorry

mtheorem xboolean_th_26:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p =>XBOOLEANK6 (p <=>XBOOLEANK7 q) =HIDDENR1 p =>XBOOLEANK6 q"
sorry

mtheorem xboolean_th_27:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p =>XBOOLEANK6 (p <=>XBOOLEANK7 q) =HIDDENR1 p =>XBOOLEANK6 (p =>XBOOLEANK6 q)"
sorry

mtheorem xboolean_th_28:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p 'or'XBOOLEANK5 (p <=>XBOOLEANK7 q) =HIDDENR1 q =>XBOOLEANK6 p"
sorry

mtheorem xboolean_th_29:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds 'not'XBOOLEANK3 p 'or'XBOOLEANK5 (p <=>XBOOLEANK7 q) =HIDDENR1 p =>XBOOLEANK6 q"
sorry

mtheorem xboolean_th_30:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for r be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p =>XBOOLEANK6 (q <=>XBOOLEANK7 r) =HIDDENR1 (('not'XBOOLEANK3 p 'or'XBOOLEANK5 'not'XBOOLEANK3 q)'or'XBOOLEANK5 r)'&'XBOOLEANK4 (('not'XBOOLEANK3 p 'or'XBOOLEANK5 q)'or'XBOOLEANK5 'not'XBOOLEANK3 r)"
sorry

mtheorem xboolean_th_31:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p 'nor'XBOOLEANK9 p =HIDDENR1 'not'XBOOLEANK3 p"
   sorry

mtheorem xboolean_th_32:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p 'nor'XBOOLEANK9 p '&'XBOOLEANK4 q =HIDDENR1 'not'XBOOLEANK3 p"
sorry

mtheorem xboolean_th_33:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p 'nor'XBOOLEANK9 p 'or'XBOOLEANK5 q =HIDDENR1 'not'XBOOLEANK3 p '&'XBOOLEANK4 'not'XBOOLEANK3 q"
sorry

mtheorem xboolean_th_34:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p 'nor'XBOOLEANK9 (p 'nor'XBOOLEANK9 q) =HIDDENR1 'not'XBOOLEANK3 p '&'XBOOLEANK4 q"
sorry

mtheorem xboolean_th_35:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p 'nor'XBOOLEANK9 p '&'XBOOLEANK4 q =HIDDENR1 'not'XBOOLEANK3 p"
sorry

mtheorem xboolean_th_36:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p 'nor'XBOOLEANK9 p 'or'XBOOLEANK5 q =HIDDENR1 p 'nor'XBOOLEANK9 q"
sorry

mtheorem xboolean_th_37:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds 'not'XBOOLEANK3 p '&'XBOOLEANK4 (p 'nor'XBOOLEANK9 q) =HIDDENR1 p 'nor'XBOOLEANK9 q"
sorry

mtheorem xboolean_th_38:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for r be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p 'or'XBOOLEANK5 (q 'nor'XBOOLEANK9 r) =HIDDENR1 (p 'or'XBOOLEANK5 'not'XBOOLEANK3 q)'&'XBOOLEANK4 (p 'or'XBOOLEANK5 'not'XBOOLEANK3 r)"
sorry

mtheorem xboolean_th_39:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for r be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p 'nor'XBOOLEANK9 (q 'nor'XBOOLEANK9 r) =HIDDENR1 'not'XBOOLEANK3 p '&'XBOOLEANK4 q 'or'XBOOLEANK5 'not'XBOOLEANK3 p '&'XBOOLEANK4 r"
sorry

mtheorem xboolean_th_40:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for r be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p 'nor'XBOOLEANK9 q '&'XBOOLEANK4 r =HIDDENR1 'not'XBOOLEANK3 (p 'or'XBOOLEANK5 q) 'or'XBOOLEANK5 'not'XBOOLEANK3 (p 'or'XBOOLEANK5 r)"
sorry

mtheorem xboolean_th_41:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for r be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p '&'XBOOLEANK4 (q 'nor'XBOOLEANK9 r) =HIDDENR1 (p '&'XBOOLEANK4 'not'XBOOLEANK3 q)'&'XBOOLEANK4 'not'XBOOLEANK3 r"
sorry

mtheorem xboolean_th_42:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p =>XBOOLEANK6 (p 'nor'XBOOLEANK9 q) =HIDDENR1 'not'XBOOLEANK3 p"
sorry

mtheorem xboolean_th_43:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for r be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p =>XBOOLEANK6 (q 'nor'XBOOLEANK9 r) =HIDDENR1 (p =>XBOOLEANK6 'not'XBOOLEANK3 q)'&'XBOOLEANK4 (p =>XBOOLEANK6 'not'XBOOLEANK3 r)"
sorry

mtheorem xboolean_th_44:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p 'or'XBOOLEANK5 (p 'nor'XBOOLEANK9 q) =HIDDENR1 q =>XBOOLEANK6 p"
sorry

mtheorem xboolean_th_45:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for r be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p 'or'XBOOLEANK5 (q 'nor'XBOOLEANK9 r) =HIDDENR1 (q =>XBOOLEANK6 p)'&'XBOOLEANK4 (r =>XBOOLEANK6 p)"
sorry

mtheorem xboolean_th_46:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for r be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p =>XBOOLEANK6 (q 'nor'XBOOLEANK9 r) =HIDDENR1 ('not'XBOOLEANK3 p 'or'XBOOLEANK5 'not'XBOOLEANK3 q)'&'XBOOLEANK4 ('not'XBOOLEANK3 p 'or'XBOOLEANK5 'not'XBOOLEANK3 r)"
sorry

mtheorem xboolean_th_47:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p 'nor'XBOOLEANK9 p <=>XBOOLEANK7 q =HIDDENR1 'not'XBOOLEANK3 p '&'XBOOLEANK4 q"
sorry

mtheorem xboolean_th_48:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds 'not'XBOOLEANK3 p '&'XBOOLEANK4 (p <=>XBOOLEANK7 q) =HIDDENR1 p 'nor'XBOOLEANK9 q"
sorry

mtheorem xboolean_th_49:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for r be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p 'nor'XBOOLEANK9 q <=>XBOOLEANK7 r =HIDDENR1 'not'XBOOLEANK3 (((p 'or'XBOOLEANK5 'not'XBOOLEANK3 q)'or'XBOOLEANK5 r)'&'XBOOLEANK4 ((p 'or'XBOOLEANK5 'not'XBOOLEANK3 r)'or'XBOOLEANK5 q))"
sorry

mtheorem xboolean_th_50:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p <=>XBOOLEANK7 q =HIDDENR1 p '&'XBOOLEANK4 q 'or'XBOOLEANK5 (p 'nor'XBOOLEANK9 q)"
sorry

mtheorem xboolean_th_51:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p 'nand'XBOOLEANK8 p =HIDDENR1 'not'XBOOLEANK3 p"
   sorry

mtheorem xboolean_th_52:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p '&'XBOOLEANK4 (p 'nand'XBOOLEANK8 q) =HIDDENR1 p '&'XBOOLEANK4 'not'XBOOLEANK3 q"
sorry

mtheorem xboolean_th_53:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p 'nand'XBOOLEANK8 p '&'XBOOLEANK4 q =HIDDENR1 'not'XBOOLEANK3 (p '&'XBOOLEANK4 q)"
sorry

mtheorem xboolean_th_54:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for r be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p 'nand'XBOOLEANK8 (q 'nand'XBOOLEANK8 r) =HIDDENR1 ('not'XBOOLEANK3 p 'or'XBOOLEANK5 q)'&'XBOOLEANK4 ('not'XBOOLEANK3 p 'or'XBOOLEANK5 r)"
sorry

mtheorem xboolean_th_55:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for r be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p 'nand'XBOOLEANK8 q 'or'XBOOLEANK5 r =HIDDENR1 'not'XBOOLEANK3 (p '&'XBOOLEANK4 q) '&'XBOOLEANK4 'not'XBOOLEANK3 (p '&'XBOOLEANK4 r)"
sorry

mtheorem xboolean_th_56:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p =>XBOOLEANK6 (p 'nand'XBOOLEANK8 q) =HIDDENR1 p 'nand'XBOOLEANK8 q"
sorry

mtheorem xboolean_th_57:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p 'nand'XBOOLEANK8 (p 'nand'XBOOLEANK8 q) =HIDDENR1 p =>XBOOLEANK6 q"
sorry

mtheorem xboolean_th_58:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for r be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p 'nand'XBOOLEANK8 (q 'nand'XBOOLEANK8 r) =HIDDENR1 (p =>XBOOLEANK6 q)'&'XBOOLEANK4 (p =>XBOOLEANK6 r)"
sorry

mtheorem xboolean_th_59:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p 'nand'XBOOLEANK8 p =>XBOOLEANK6 q =HIDDENR1 'not'XBOOLEANK3 (p '&'XBOOLEANK4 q)"
sorry

mtheorem xboolean_th_60:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for r be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p 'nand'XBOOLEANK8 q =>XBOOLEANK6 r =HIDDENR1 (p =>XBOOLEANK6 q)'&'XBOOLEANK4 (p =>XBOOLEANK6 'not'XBOOLEANK3 r)"
sorry

mtheorem xboolean_th_61:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds 'not'XBOOLEANK3 p 'or'XBOOLEANK5 (p 'nand'XBOOLEANK8 q) =HIDDENR1 p 'nand'XBOOLEANK8 q"
sorry

mtheorem xboolean_th_62:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for r be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p 'nand'XBOOLEANK8 q =>XBOOLEANK6 r =HIDDENR1 ('not'XBOOLEANK3 p 'or'XBOOLEANK5 q)'&'XBOOLEANK4 ('not'XBOOLEANK3 p 'or'XBOOLEANK5 'not'XBOOLEANK3 r)"
sorry

mtheorem xboolean_th_63:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds 'not'XBOOLEANK3 p '&'XBOOLEANK4 (p 'nand'XBOOLEANK8 q) =HIDDENR1 'not'XBOOLEANK3 p 'or'XBOOLEANK5 'not'XBOOLEANK3 p '&'XBOOLEANK4 'not'XBOOLEANK3 q"
sorry

mtheorem xboolean_th_64:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for r be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p '&'XBOOLEANK4 (q 'nand'XBOOLEANK8 r) =HIDDENR1 p '&'XBOOLEANK4 'not'XBOOLEANK3 q 'or'XBOOLEANK5 p '&'XBOOLEANK4 'not'XBOOLEANK3 r"
sorry

mtheorem xboolean_th_65:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p 'nand'XBOOLEANK8 p <=>XBOOLEANK7 q =HIDDENR1 'not'XBOOLEANK3 (p '&'XBOOLEANK4 q)"
sorry

mtheorem xboolean_th_66:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for r be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p 'nand'XBOOLEANK8 q <=>XBOOLEANK7 r =HIDDENR1 'not'XBOOLEANK3 ((p '&'XBOOLEANK4 ('not'XBOOLEANK3 q 'or'XBOOLEANK5 r))'&'XBOOLEANK4 ('not'XBOOLEANK3 r 'or'XBOOLEANK5 q))"
   sorry

mtheorem xboolean_th_67:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for r be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p 'nand'XBOOLEANK8 (q 'nor'XBOOLEANK9 r) =HIDDENR1 ('not'XBOOLEANK3 p 'or'XBOOLEANK5 q)'or'XBOOLEANK5 r"
sorry

mtheorem xboolean_th_68:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds (p '\\'XBOOLEANK11 q)'\\'XBOOLEANK11 q =HIDDENR1 p '\\'XBOOLEANK11 q"
sorry

mtheorem xboolean_th_69:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p '&'XBOOLEANK4 (p '\\'XBOOLEANK11 q) =HIDDENR1 p '\\'XBOOLEANK11 q"
sorry

mtheorem xboolean_th_70:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p 'nor'XBOOLEANK9 p <=>XBOOLEANK7 q =HIDDENR1 q '\\'XBOOLEANK11 p"
sorry

mtheorem xboolean_th_71:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p 'nor'XBOOLEANK9 (p 'nor'XBOOLEANK9 q) =HIDDENR1 q '\\'XBOOLEANK11 p"
sorry

mtheorem xboolean_th_72:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p 'xor'XBOOLEANK10 (p 'xor'XBOOLEANK10 q) =HIDDENR1 q"
sorry

mtheorem xboolean_th_73:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for r be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds (p 'xor'XBOOLEANK10 q)'xor'XBOOLEANK10 r =HIDDENR1 p 'xor'XBOOLEANK10 (q 'xor'XBOOLEANK10 r)"
sorry

mtheorem xboolean_th_74:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds 'not'XBOOLEANK3 (p 'xor'XBOOLEANK10 q) =HIDDENR1 'not'XBOOLEANK3 p 'xor'XBOOLEANK10 q"
sorry

mtheorem xboolean_th_75:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for r be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p '&'XBOOLEANK4 (q 'xor'XBOOLEANK10 r) =HIDDENR1 p '&'XBOOLEANK4 q 'xor'XBOOLEANK10 p '&'XBOOLEANK4 r"
sorry

mtheorem xboolean_th_76:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p '&'XBOOLEANK4 (p 'xor'XBOOLEANK10 q) =HIDDENR1 p '&'XBOOLEANK4 'not'XBOOLEANK3 q"
sorry

mtheorem xboolean_th_77:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p 'xor'XBOOLEANK10 p '&'XBOOLEANK4 q =HIDDENR1 p '&'XBOOLEANK4 'not'XBOOLEANK3 q"
sorry

mtheorem xboolean_th_78:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds 'not'XBOOLEANK3 p '&'XBOOLEANK4 (p 'xor'XBOOLEANK10 q) =HIDDENR1 'not'XBOOLEANK3 p '&'XBOOLEANK4 q"
sorry

mtheorem xboolean_th_79:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p 'or'XBOOLEANK5 (p 'xor'XBOOLEANK10 q) =HIDDENR1 p 'or'XBOOLEANK5 q"
sorry

mtheorem xboolean_th_80:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p 'or'XBOOLEANK5 ('not'XBOOLEANK3 p 'xor'XBOOLEANK10 q) =HIDDENR1 p 'or'XBOOLEANK5 'not'XBOOLEANK3 q"
sorry

mtheorem xboolean_th_81:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p 'xor'XBOOLEANK10 'not'XBOOLEANK3 p '&'XBOOLEANK4 q =HIDDENR1 p 'or'XBOOLEANK5 q"
sorry

mtheorem xboolean_th_82:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p 'xor'XBOOLEANK10 p 'or'XBOOLEANK5 q =HIDDENR1 'not'XBOOLEANK3 p '&'XBOOLEANK4 q"
sorry

mtheorem xboolean_th_83:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for r be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p 'xor'XBOOLEANK10 q '&'XBOOLEANK4 r =HIDDENR1 (p 'or'XBOOLEANK5 q '&'XBOOLEANK4 r)'&'XBOOLEANK4 ('not'XBOOLEANK3 p 'or'XBOOLEANK5 'not'XBOOLEANK3 (q '&'XBOOLEANK4 r))"
sorry

mtheorem xboolean_th_84:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds 'not'XBOOLEANK3 p 'xor'XBOOLEANK10 p =>XBOOLEANK6 q =HIDDENR1 p '&'XBOOLEANK4 q"
sorry

mtheorem xboolean_th_85:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p =>XBOOLEANK6 (p 'xor'XBOOLEANK10 q) =HIDDENR1 'not'XBOOLEANK3 p 'or'XBOOLEANK5 'not'XBOOLEANK3 q"
sorry

mtheorem xboolean_th_86:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p 'xor'XBOOLEANK10 p =>XBOOLEANK6 q =HIDDENR1 'not'XBOOLEANK3 p 'or'XBOOLEANK5 'not'XBOOLEANK3 q"
sorry

mtheorem xboolean_th_87:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds 'not'XBOOLEANK3 p 'xor'XBOOLEANK10 q =>XBOOLEANK6 p =HIDDENR1 p '&'XBOOLEANK4 (p 'or'XBOOLEANK5 'not'XBOOLEANK3 q) 'or'XBOOLEANK5 'not'XBOOLEANK3 p '&'XBOOLEANK4 q"
sorry

mtheorem xboolean_th_88:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p 'xor'XBOOLEANK10 p <=>XBOOLEANK7 q =HIDDENR1 'not'XBOOLEANK3 q"
sorry

mtheorem xboolean_th_89:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds 'not'XBOOLEANK3 p 'xor'XBOOLEANK10 p <=>XBOOLEANK7 q =HIDDENR1 q"
sorry

mtheorem xboolean_th_90:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p 'nor'XBOOLEANK9 (p 'xor'XBOOLEANK10 q) =HIDDENR1 'not'XBOOLEANK3 p '&'XBOOLEANK4 'not'XBOOLEANK3 q"
sorry

mtheorem xboolean_th_91:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p 'nor'XBOOLEANK9 (p 'xor'XBOOLEANK10 q) =HIDDENR1 p 'nor'XBOOLEANK9 q"
sorry

mtheorem xboolean_th_92:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p 'xor'XBOOLEANK10 (p 'nor'XBOOLEANK9 q) =HIDDENR1 q =>XBOOLEANK6 p"
sorry

mtheorem xboolean_th_93:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p 'nand'XBOOLEANK8 (p 'xor'XBOOLEANK10 q) =HIDDENR1 p =>XBOOLEANK6 q"
sorry

mtheorem xboolean_th_94:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p 'xor'XBOOLEANK10 (p 'nand'XBOOLEANK8 q) =HIDDENR1 p =>XBOOLEANK6 q"
sorry

mtheorem xboolean_th_95:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p 'xor'XBOOLEANK10 p =>XBOOLEANK6 q =HIDDENR1 p 'nand'XBOOLEANK8 q"
sorry

mtheorem xboolean_th_96:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for r be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p 'nand'XBOOLEANK8 (q 'xor'XBOOLEANK10 r) =HIDDENR1 p '&'XBOOLEANK4 q <=>XBOOLEANK7 p '&'XBOOLEANK4 r"
sorry

mtheorem xboolean_th_97:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p 'xor'XBOOLEANK10 p '&'XBOOLEANK4 q =HIDDENR1 p '\\'XBOOLEANK11 q"
sorry

mtheorem xboolean_th_98:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p '&'XBOOLEANK4 (p 'xor'XBOOLEANK10 q) =HIDDENR1 p '\\'XBOOLEANK11 q"
sorry

mtheorem xboolean_th_99:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds 'not'XBOOLEANK3 p '&'XBOOLEANK4 (p 'xor'XBOOLEANK10 q) =HIDDENR1 q '\\'XBOOLEANK11 p"
sorry

mtheorem xboolean_th_100:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p 'xor'XBOOLEANK10 p 'or'XBOOLEANK5 q =HIDDENR1 q '\\'XBOOLEANK11 p"
sorry

(*begin*)
mtheorem xboolean_th_101:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p '&'XBOOLEANK4 q =HIDDENR1 TRUEXBOOLEANK2 implies p =HIDDENR1 TRUEXBOOLEANK2 & q =HIDDENR1 TRUEXBOOLEANK2"
sorry

mtheorem xboolean_th_102:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds 'not'XBOOLEANK3 (p '&'XBOOLEANK4 'not'XBOOLEANK3 p) =HIDDENR1 TRUEXBOOLEANK2"
sorry

mtheorem xboolean_th_103:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p =>XBOOLEANK6 p =HIDDENR1 TRUEXBOOLEANK2"
sorry

mtheorem xboolean_th_104:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p =>XBOOLEANK6 (q =>XBOOLEANK6 p) =HIDDENR1 TRUEXBOOLEANK2"
sorry

mtheorem xboolean_th_105:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p =>XBOOLEANK6 ((p =>XBOOLEANK6 q)=>XBOOLEANK6 q) =HIDDENR1 TRUEXBOOLEANK2"
sorry

mtheorem xboolean_th_106:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for r be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds (p =>XBOOLEANK6 q)=>XBOOLEANK6 ((q =>XBOOLEANK6 r)=>XBOOLEANK6 (p =>XBOOLEANK6 r)) =HIDDENR1 TRUEXBOOLEANK2"
sorry

mtheorem xboolean_th_107:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for r be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds (p =>XBOOLEANK6 q)=>XBOOLEANK6 ((r =>XBOOLEANK6 p)=>XBOOLEANK6 (r =>XBOOLEANK6 q)) =HIDDENR1 TRUEXBOOLEANK2"
sorry

mtheorem xboolean_th_108:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds (p =>XBOOLEANK6 (p =>XBOOLEANK6 q))=>XBOOLEANK6 (p =>XBOOLEANK6 q) =HIDDENR1 TRUEXBOOLEANK2"
sorry

mtheorem xboolean_th_109:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for r be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds (p =>XBOOLEANK6 (q =>XBOOLEANK6 r))=>XBOOLEANK6 ((p =>XBOOLEANK6 q)=>XBOOLEANK6 (p =>XBOOLEANK6 r)) =HIDDENR1 TRUEXBOOLEANK2"
sorry

mtheorem xboolean_th_110:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for r be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds (p =>XBOOLEANK6 (q =>XBOOLEANK6 r))=>XBOOLEANK6 (q =>XBOOLEANK6 (p =>XBOOLEANK6 r)) =HIDDENR1 TRUEXBOOLEANK2"
sorry

mtheorem xboolean_th_111:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for r be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds ((p =>XBOOLEANK6 q)=>XBOOLEANK6 r)=>XBOOLEANK6 (q =>XBOOLEANK6 r) =HIDDENR1 TRUEXBOOLEANK2"
sorry

mtheorem xboolean_th_112:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds ((TRUEXBOOLEANK2)=>XBOOLEANK6 p)=>XBOOLEANK6 p =HIDDENR1 TRUEXBOOLEANK2"
sorry

mtheorem xboolean_th_113:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for r be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p =>XBOOLEANK6 q =HIDDENR1 TRUEXBOOLEANK2 implies (q =>XBOOLEANK6 r)=>XBOOLEANK6 (p =>XBOOLEANK6 r) =HIDDENR1 TRUEXBOOLEANK2"
sorry

mtheorem xboolean_th_114:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p =>XBOOLEANK6 (p =>XBOOLEANK6 q) =HIDDENR1 TRUEXBOOLEANK2 implies p =>XBOOLEANK6 q =HIDDENR1 TRUEXBOOLEANK2"
sorry

mtheorem xboolean_th_115:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for r be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p =>XBOOLEANK6 (q =>XBOOLEANK6 r) =HIDDENR1 TRUEXBOOLEANK2 implies (p =>XBOOLEANK6 q)=>XBOOLEANK6 (p =>XBOOLEANK6 r) =HIDDENR1 TRUEXBOOLEANK2"
sorry

mtheorem xboolean_th_116:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p =>XBOOLEANK6 q =HIDDENR1 TRUEXBOOLEANK2 & q =>XBOOLEANK6 p =HIDDENR1 TRUEXBOOLEANK2 implies p =HIDDENR1 q"
sorry

mtheorem xboolean_th_117:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for r be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p =>XBOOLEANK6 q =HIDDENR1 TRUEXBOOLEANK2 & q =>XBOOLEANK6 r =HIDDENR1 TRUEXBOOLEANK2 implies p =>XBOOLEANK6 r =HIDDENR1 TRUEXBOOLEANK2"
sorry

mtheorem xboolean_th_118:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds ('not'XBOOLEANK3 p =>XBOOLEANK6 p)=>XBOOLEANK6 p =HIDDENR1 TRUEXBOOLEANK2"
sorry

mtheorem xboolean_th_119:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds 'not'XBOOLEANK3 p =HIDDENR1 TRUEXBOOLEANK2 implies p =>XBOOLEANK6 q =HIDDENR1 TRUEXBOOLEANK2"
   sorry

mtheorem xboolean_th_120:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p =>XBOOLEANK6 q =HIDDENR1 TRUEXBOOLEANK2 & p =>XBOOLEANK6 'not'XBOOLEANK3 q =HIDDENR1 TRUEXBOOLEANK2 implies 'not'XBOOLEANK3 p =HIDDENR1 TRUEXBOOLEANK2"
sorry

mtheorem xboolean_th_121:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for r be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds (p =>XBOOLEANK6 q)=>XBOOLEANK6 ('not'XBOOLEANK3 (q '&'XBOOLEANK4 r) =>XBOOLEANK6 'not'XBOOLEANK3 (p '&'XBOOLEANK4 r)) =HIDDENR1 TRUEXBOOLEANK2"
sorry

mtheorem xboolean_th_122:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p 'or'XBOOLEANK5 (p =>XBOOLEANK6 q) =HIDDENR1 TRUEXBOOLEANK2"
sorry

mtheorem xboolean_th_123:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p =>XBOOLEANK6 p 'or'XBOOLEANK5 q =HIDDENR1 TRUEXBOOLEANK2"
sorry

mtheorem xboolean_th_124:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds 'not'XBOOLEANK3 q 'or'XBOOLEANK5 ((q =>XBOOLEANK6 p)=>XBOOLEANK6 p) =HIDDENR1 TRUEXBOOLEANK2"
sorry

mtheorem xboolean_th_125:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p <=>XBOOLEANK7 p =HIDDENR1 TRUEXBOOLEANK2"
sorry

mtheorem xboolean_th_126:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for r be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds (((p <=>XBOOLEANK7 q)<=>XBOOLEANK7 r)<=>XBOOLEANK7 p)<=>XBOOLEANK7 (q <=>XBOOLEANK7 r) =HIDDENR1 TRUEXBOOLEANK2"
sorry

mtheorem xboolean_th_127:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for r be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p <=>XBOOLEANK7 q =HIDDENR1 TRUEXBOOLEANK2 & q <=>XBOOLEANK7 r =HIDDENR1 TRUEXBOOLEANK2 implies p <=>XBOOLEANK7 r =HIDDENR1 TRUEXBOOLEANK2"
sorry

mtheorem xboolean_th_128:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for r be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for s be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p <=>XBOOLEANK7 q =HIDDENR1 TRUEXBOOLEANK2 & r <=>XBOOLEANK7 s =HIDDENR1 TRUEXBOOLEANK2 implies (p <=>XBOOLEANK7 r)<=>XBOOLEANK7 (q <=>XBOOLEANK7 s) =HIDDENR1 TRUEXBOOLEANK2"
sorry

mtheorem xboolean_th_129:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds 'not'XBOOLEANK3 (p <=>XBOOLEANK7 'not'XBOOLEANK3 p) =HIDDENR1 TRUEXBOOLEANK2"
sorry

mtheorem xboolean_th_130:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for r be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for s be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p <=>XBOOLEANK7 q =HIDDENR1 TRUEXBOOLEANK2 & r <=>XBOOLEANK7 s =HIDDENR1 TRUEXBOOLEANK2 implies p '&'XBOOLEANK4 r <=>XBOOLEANK7 q '&'XBOOLEANK4 s =HIDDENR1 TRUEXBOOLEANK2"
sorry

mtheorem xboolean_th_131:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for r be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for s be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p <=>XBOOLEANK7 q =HIDDENR1 TRUEXBOOLEANK2 & r <=>XBOOLEANK7 s =HIDDENR1 TRUEXBOOLEANK2 implies p 'or'XBOOLEANK5 r <=>XBOOLEANK7 q 'or'XBOOLEANK5 s =HIDDENR1 TRUEXBOOLEANK2"
sorry

mtheorem xboolean_th_132:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p <=>XBOOLEANK7 q =HIDDENR1 TRUEXBOOLEANK2 iff p =>XBOOLEANK6 q =HIDDENR1 TRUEXBOOLEANK2 & q =>XBOOLEANK6 p =HIDDENR1 TRUEXBOOLEANK2"
sorry

mtheorem xboolean_th_133:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for r be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for s be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p <=>XBOOLEANK7 q =HIDDENR1 TRUEXBOOLEANK2 & r <=>XBOOLEANK7 s =HIDDENR1 TRUEXBOOLEANK2 implies (p =>XBOOLEANK6 r)<=>XBOOLEANK7 (q =>XBOOLEANK6 s) =HIDDENR1 TRUEXBOOLEANK2"
sorry

mtheorem xboolean_th_134:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds 'not'XBOOLEANK3 (p 'nor'XBOOLEANK9 'not'XBOOLEANK3 p) =HIDDENR1 TRUEXBOOLEANK2"
sorry

mtheorem xboolean_th_135:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p 'nand'XBOOLEANK8 'not'XBOOLEANK3 p =HIDDENR1 TRUEXBOOLEANK2"
sorry

mtheorem xboolean_th_136:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p 'or'XBOOLEANK5 (p 'nand'XBOOLEANK8 q) =HIDDENR1 TRUEXBOOLEANK2"
sorry

mtheorem xboolean_th_137:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p 'nand'XBOOLEANK8 (p 'nor'XBOOLEANK9 q) =HIDDENR1 TRUEXBOOLEANK2"
sorry

mtheorem xboolean_th_138:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p '&'XBOOLEANK4 'not'XBOOLEANK3 p =HIDDENR1 FALSEXBOOLEANK1"
sorry

mtheorem xboolean_th_139:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p '&'XBOOLEANK4 p =HIDDENR1 FALSEXBOOLEANK1 implies p =HIDDENR1 FALSEXBOOLEANK1"
   sorry

mtheorem xboolean_th_140:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p '&'XBOOLEANK4 q =HIDDENR1 FALSEXBOOLEANK1 implies p =HIDDENR1 FALSEXBOOLEANK1 or q =HIDDENR1 FALSEXBOOLEANK1"
   sorry

mtheorem xboolean_th_141:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds 'not'XBOOLEANK3 (p =>XBOOLEANK6 p) =HIDDENR1 FALSEXBOOLEANK1"
sorry

mtheorem xboolean_th_142:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p <=>XBOOLEANK7 'not'XBOOLEANK3 p =HIDDENR1 FALSEXBOOLEANK1"
sorry

mtheorem xboolean_th_143:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds 'not'XBOOLEANK3 (p <=>XBOOLEANK7 p) =HIDDENR1 FALSEXBOOLEANK1"
sorry

mtheorem xboolean_th_144:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p '&'XBOOLEANK4 (p 'nor'XBOOLEANK9 q) =HIDDENR1 FALSEXBOOLEANK1"
sorry

mtheorem xboolean_th_145:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p 'nor'XBOOLEANK9 p =>XBOOLEANK6 q =HIDDENR1 FALSEXBOOLEANK1"
sorry

mtheorem xboolean_th_146:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds  for q be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p 'nor'XBOOLEANK9 (p 'nand'XBOOLEANK8 q) =HIDDENR1 FALSEXBOOLEANK1"
sorry

mtheorem xboolean_th_147:
" for p be booleanXBOOLEANV1\<bar>objectHIDDENM1 holds p 'xor'XBOOLEANK10 p =HIDDENR1 FALSEXBOOLEANK1"
sorry

end
