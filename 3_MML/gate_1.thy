theory gate_1
  imports xboole_0
begin
(*begin*)
mdef gate_1_def_1 ("NOT1GATE-1K1  _ " [164]164 ) where
  mlet "a be setHIDDENM2"
"func NOT1GATE-1K1 a \<rightarrow> setHIDDENM2 equals
  {}XBOOLE-0K1 if a be  non emptyXBOOLE-0V1 otherwise {TARSKIK1 {}XBOOLE-0K1 }"
proof-
  (*coherence*)
    show "(a be  non emptyXBOOLE-0V1 implies {}XBOOLE-0K1 be setHIDDENM2) & ( not a be  non emptyXBOOLE-0V1 implies {TARSKIK1 {}XBOOLE-0K1 } be setHIDDENM2)"
       sorry
  (*consistency*)
    show " for it be setHIDDENM2 holds  True "
       sorry
qed "sorry"

mtheorem gate_1_cl_1:
  mlet "a be emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster NOT1GATE-1K1 a as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "NOT1GATE-1K1 a be  non emptyXBOOLE-0V1"
    using gate_1_def_1 sorry
qed "sorry"

mtheorem gate_1_cl_2:
  mlet "a be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster NOT1GATE-1K1 a as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "NOT1GATE-1K1 a be emptyXBOOLE-0V1"
    using gate_1_def_1 sorry
qed "sorry"

mtheorem gate_1_th_1:
"NOT1GATE-1K1 {TARSKIK1 {}XBOOLE-0K1 } =XBOOLE-0R4 {}XBOOLE-0K1 & NOT1GATE-1K1 {}XBOOLE-0K1 =XBOOLE-0R4 {TARSKIK1 {}XBOOLE-0K1 }"
  using gate_1_def_1 sorry

mtheorem gate_1_th_2:
" for a be setHIDDENM2 holds NOT1GATE-1K1 a be  non emptyXBOOLE-0V1 iff  not a be  non emptyXBOOLE-0V1"
   sorry

reserve a, b, c, d, e, f, g, h for "setHIDDENM2"
mtheorem gate_1_th_3:
"NOT1GATE-1K1 {}XBOOLE-0K1 be  non emptyXBOOLE-0V1"
   sorry

mdef gate_1_def_2 ("AND2GATE-1K2'( _ , _ ')" [0,0]164 ) where
  mlet "a be setHIDDENM2", "b be setHIDDENM2"
"func AND2GATE-1K2(a,b) \<rightarrow> setHIDDENM2 equals
  NOT1GATE-1K1 {}XBOOLE-0K1 if a be  non emptyXBOOLE-0V1 & b be  non emptyXBOOLE-0V1 otherwise {}XBOOLE-0K1"
proof-
  (*coherence*)
    show "(a be  non emptyXBOOLE-0V1 & b be  non emptyXBOOLE-0V1 implies NOT1GATE-1K1 {}XBOOLE-0K1 be setHIDDENM2) & ( not (a be  non emptyXBOOLE-0V1 & b be  non emptyXBOOLE-0V1) implies {}XBOOLE-0K1 be setHIDDENM2)"
       sorry
  (*consistency*)
    show " for it be setHIDDENM2 holds  True "
       sorry
qed "sorry"

mtheorem GATE_1K2_commutativity:
" for a be setHIDDENM2 holds  for b be setHIDDENM2 holds AND2GATE-1K2(a,b) =HIDDENR1 AND2GATE-1K2(b,a)"
sorry

mtheorem gate_1_cl_3:
  mlet "a be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "b be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster AND2GATE-1K2(a,b) as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "AND2GATE-1K2(a,b) be  non emptyXBOOLE-0V1"
    using gate_1_def_2 sorry
qed "sorry"

mtheorem gate_1_cl_4:
  mlet "a be emptyXBOOLE-0V1\<bar>setHIDDENM2", "b be setHIDDENM2"
"cluster AND2GATE-1K2(a,b) as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "AND2GATE-1K2(a,b) be emptyXBOOLE-0V1"
    using gate_1_def_2 sorry
qed "sorry"

mtheorem gate_1_th_4:
" for a be setHIDDENM2 holds  for b be setHIDDENM2 holds AND2GATE-1K2(a,b) be  non emptyXBOOLE-0V1 iff a be  non emptyXBOOLE-0V1 & b be  non emptyXBOOLE-0V1"
   sorry

mdef gate_1_def_3 ("OR2GATE-1K3'( _ , _ ')" [0,0]164 ) where
  mlet "a be setHIDDENM2", "b be setHIDDENM2"
"func OR2GATE-1K3(a,b) \<rightarrow> setHIDDENM2 equals
  NOT1GATE-1K1 {}XBOOLE-0K1 if a be  non emptyXBOOLE-0V1 or b be  non emptyXBOOLE-0V1 otherwise {}XBOOLE-0K1"
proof-
  (*coherence*)
    show "(a be  non emptyXBOOLE-0V1 or b be  non emptyXBOOLE-0V1 implies NOT1GATE-1K1 {}XBOOLE-0K1 be setHIDDENM2) & ( not (a be  non emptyXBOOLE-0V1 or b be  non emptyXBOOLE-0V1) implies {}XBOOLE-0K1 be setHIDDENM2)"
       sorry
  (*consistency*)
    show " for it be setHIDDENM2 holds  True "
       sorry
qed "sorry"

mtheorem GATE_1K3_commutativity:
" for a be setHIDDENM2 holds  for b be setHIDDENM2 holds OR2GATE-1K3(a,b) =HIDDENR1 OR2GATE-1K3(b,a)"
sorry

mtheorem gate_1_cl_5:
  mlet "a be setHIDDENM2", "b be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster OR2GATE-1K3(a,b) as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "OR2GATE-1K3(a,b) be  non emptyXBOOLE-0V1"
    using gate_1_def_3 sorry
qed "sorry"

mtheorem gate_1_cl_6:
  mlet "a be emptyXBOOLE-0V1\<bar>setHIDDENM2", "b be emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster OR2GATE-1K3(a,b) as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "OR2GATE-1K3(a,b) be emptyXBOOLE-0V1"
    using gate_1_def_3 sorry
qed "sorry"

mtheorem gate_1_th_5:
" for a be setHIDDENM2 holds  for b be setHIDDENM2 holds OR2GATE-1K3(a,b) be  non emptyXBOOLE-0V1 iff a be  non emptyXBOOLE-0V1 or b be  non emptyXBOOLE-0V1"
   sorry

mdef gate_1_def_4 ("XOR2GATE-1K4'( _ , _ ')" [0,0]164 ) where
  mlet "a be setHIDDENM2", "b be setHIDDENM2"
"func XOR2GATE-1K4(a,b) \<rightarrow> setHIDDENM2 equals
  NOT1GATE-1K1 {}XBOOLE-0K1 if a be  non emptyXBOOLE-0V1 &  not b be  non emptyXBOOLE-0V1 or  not a be  non emptyXBOOLE-0V1 & b be  non emptyXBOOLE-0V1 otherwise {}XBOOLE-0K1"
proof-
  (*coherence*)
    show "(a be  non emptyXBOOLE-0V1 &  not b be  non emptyXBOOLE-0V1 or  not a be  non emptyXBOOLE-0V1 & b be  non emptyXBOOLE-0V1 implies NOT1GATE-1K1 {}XBOOLE-0K1 be setHIDDENM2) & ( not (a be  non emptyXBOOLE-0V1 &  not b be  non emptyXBOOLE-0V1 or  not a be  non emptyXBOOLE-0V1 & b be  non emptyXBOOLE-0V1) implies {}XBOOLE-0K1 be setHIDDENM2)"
       sorry
  (*consistency*)
    show " for it be setHIDDENM2 holds  True "
       sorry
qed "sorry"

mtheorem GATE_1K4_commutativity:
" for a be setHIDDENM2 holds  for b be setHIDDENM2 holds XOR2GATE-1K4(a,b) =HIDDENR1 XOR2GATE-1K4(b,a)"
sorry

mtheorem gate_1_cl_7:
  mlet "a be emptyXBOOLE-0V1\<bar>setHIDDENM2", "b be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster XOR2GATE-1K4(a,b) as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "XOR2GATE-1K4(a,b) be  non emptyXBOOLE-0V1"
    using gate_1_def_4 sorry
qed "sorry"

mtheorem gate_1_cl_8:
  mlet "a be emptyXBOOLE-0V1\<bar>setHIDDENM2", "b be emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster XOR2GATE-1K4(a,b) as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "XOR2GATE-1K4(a,b) be emptyXBOOLE-0V1"
    using gate_1_def_4 sorry
qed "sorry"

mtheorem gate_1_cl_9:
  mlet "a be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "b be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster XOR2GATE-1K4(a,b) as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "XOR2GATE-1K4(a,b) be emptyXBOOLE-0V1"
    using gate_1_def_4 sorry
qed "sorry"

mtheorem gate_1_th_6:
" for a be setHIDDENM2 holds  for b be setHIDDENM2 holds XOR2GATE-1K4(a,b) be  non emptyXBOOLE-0V1 iff a be  non emptyXBOOLE-0V1 &  not b be  non emptyXBOOLE-0V1 or  not a be  non emptyXBOOLE-0V1 & b be  non emptyXBOOLE-0V1"
   sorry

mtheorem gate_1_th_7:
" for a be setHIDDENM2 holds  not XOR2GATE-1K4(a,a) be  non emptyXBOOLE-0V1"
sorry

mtheorem gate_1_th_8:
" for a be setHIDDENM2 holds XOR2GATE-1K4(a,{}XBOOLE-0K1) be  non emptyXBOOLE-0V1 iff a be  non emptyXBOOLE-0V1"
   sorry

mtheorem gate_1_th_9:
" for a be setHIDDENM2 holds  for b be setHIDDENM2 holds XOR2GATE-1K4(a,b) be  non emptyXBOOLE-0V1 iff XOR2GATE-1K4(b,a) be  non emptyXBOOLE-0V1"
   sorry

mdef gate_1_def_5 ("EQV2GATE-1K5'( _ , _ ')" [0,0]164 ) where
  mlet "a be setHIDDENM2", "b be setHIDDENM2"
"func EQV2GATE-1K5(a,b) \<rightarrow> setHIDDENM2 equals
  NOT1GATE-1K1 {}XBOOLE-0K1 if a be  non emptyXBOOLE-0V1 iff b be  non emptyXBOOLE-0V1 otherwise {}XBOOLE-0K1"
proof-
  (*coherence*)
    show "((a be  non emptyXBOOLE-0V1 iff b be  non emptyXBOOLE-0V1) implies NOT1GATE-1K1 {}XBOOLE-0K1 be setHIDDENM2) & ( not (a be  non emptyXBOOLE-0V1 iff b be  non emptyXBOOLE-0V1) implies {}XBOOLE-0K1 be setHIDDENM2)"
       sorry
  (*consistency*)
    show " for it be setHIDDENM2 holds  True "
       sorry
qed "sorry"

mtheorem GATE_1K5_commutativity:
" for a be setHIDDENM2 holds  for b be setHIDDENM2 holds EQV2GATE-1K5(a,b) =HIDDENR1 EQV2GATE-1K5(b,a)"
sorry

mtheorem gate_1_cl_10:
  mlet "a be emptyXBOOLE-0V1\<bar>setHIDDENM2", "b be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster EQV2GATE-1K5(a,b) as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "EQV2GATE-1K5(a,b) be emptyXBOOLE-0V1"
    using gate_1_def_5 sorry
qed "sorry"

mtheorem gate_1_cl_11:
  mlet "a be emptyXBOOLE-0V1\<bar>setHIDDENM2", "b be emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster EQV2GATE-1K5(a,b) as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "EQV2GATE-1K5(a,b) be  non emptyXBOOLE-0V1"
    using gate_1_def_5 sorry
qed "sorry"

mtheorem gate_1_cl_12:
  mlet "a be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "b be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster EQV2GATE-1K5(a,b) as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "EQV2GATE-1K5(a,b) be  non emptyXBOOLE-0V1"
    using gate_1_def_5 sorry
qed "sorry"

mtheorem gate_1_th_10:
" for a be setHIDDENM2 holds  for b be setHIDDENM2 holds EQV2GATE-1K5(a,b) be  non emptyXBOOLE-0V1 iff (a be  non emptyXBOOLE-0V1 iff b be  non emptyXBOOLE-0V1)"
   sorry

mtheorem gate_1_th_11:
" for a be setHIDDENM2 holds  for b be setHIDDENM2 holds EQV2GATE-1K5(a,b) be  non emptyXBOOLE-0V1 iff  not XOR2GATE-1K4(a,b) be  non emptyXBOOLE-0V1"
sorry

mdef gate_1_def_6 ("NAND2GATE-1K6'( _ , _ ')" [0,0]164 ) where
  mlet "a be setHIDDENM2", "b be setHIDDENM2"
"func NAND2GATE-1K6(a,b) \<rightarrow> setHIDDENM2 equals
  NOT1GATE-1K1 {}XBOOLE-0K1 if  not (a be  non emptyXBOOLE-0V1 & b be  non emptyXBOOLE-0V1) otherwise {}XBOOLE-0K1"
proof-
  (*coherence*)
    show "( not (a be  non emptyXBOOLE-0V1 & b be  non emptyXBOOLE-0V1) implies NOT1GATE-1K1 {}XBOOLE-0K1 be setHIDDENM2) & ( not ( not (a be  non emptyXBOOLE-0V1 & b be  non emptyXBOOLE-0V1)) implies {}XBOOLE-0K1 be setHIDDENM2)"
       sorry
  (*consistency*)
    show " for it be setHIDDENM2 holds  True "
       sorry
qed "sorry"

mtheorem GATE_1K6_commutativity:
" for a be setHIDDENM2 holds  for b be setHIDDENM2 holds NAND2GATE-1K6(a,b) =HIDDENR1 NAND2GATE-1K6(b,a)"
sorry

mtheorem gate_1_cl_13:
  mlet "a be emptyXBOOLE-0V1\<bar>setHIDDENM2", "b be setHIDDENM2"
"cluster NAND2GATE-1K6(a,b) as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "NAND2GATE-1K6(a,b) be  non emptyXBOOLE-0V1"
    using gate_1_def_6 sorry
qed "sorry"

mtheorem gate_1_cl_14:
  mlet "a be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "b be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster NAND2GATE-1K6(a,b) as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "NAND2GATE-1K6(a,b) be emptyXBOOLE-0V1"
    using gate_1_def_6 sorry
qed "sorry"

mtheorem gate_1_th_12:
" for a be setHIDDENM2 holds  for b be setHIDDENM2 holds NAND2GATE-1K6(a,b) be  non emptyXBOOLE-0V1 iff  not (a be  non emptyXBOOLE-0V1 & b be  non emptyXBOOLE-0V1)"
   sorry

mdef gate_1_def_7 ("NOR2GATE-1K7'( _ , _ ')" [0,0]164 ) where
  mlet "a be setHIDDENM2", "b be setHIDDENM2"
"func NOR2GATE-1K7(a,b) \<rightarrow> setHIDDENM2 equals
  NOT1GATE-1K1 {}XBOOLE-0K1 if  not (a be  non emptyXBOOLE-0V1 or b be  non emptyXBOOLE-0V1) otherwise {}XBOOLE-0K1"
proof-
  (*coherence*)
    show "( not (a be  non emptyXBOOLE-0V1 or b be  non emptyXBOOLE-0V1) implies NOT1GATE-1K1 {}XBOOLE-0K1 be setHIDDENM2) & ( not ( not (a be  non emptyXBOOLE-0V1 or b be  non emptyXBOOLE-0V1)) implies {}XBOOLE-0K1 be setHIDDENM2)"
       sorry
  (*consistency*)
    show " for it be setHIDDENM2 holds  True "
       sorry
qed "sorry"

mtheorem GATE_1K7_commutativity:
" for a be setHIDDENM2 holds  for b be setHIDDENM2 holds NOR2GATE-1K7(a,b) =HIDDENR1 NOR2GATE-1K7(b,a)"
sorry

mtheorem gate_1_cl_15:
  mlet "a be emptyXBOOLE-0V1\<bar>setHIDDENM2", "b be emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster NOR2GATE-1K7(a,b) as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "NOR2GATE-1K7(a,b) be  non emptyXBOOLE-0V1"
    using gate_1_def_7 sorry
qed "sorry"

mtheorem gate_1_cl_16:
  mlet "a be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "b be setHIDDENM2"
"cluster NOR2GATE-1K7(a,b) as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "NOR2GATE-1K7(a,b) be emptyXBOOLE-0V1"
    using gate_1_def_7 sorry
qed "sorry"

mtheorem gate_1_th_13:
" for a be setHIDDENM2 holds  for b be setHIDDENM2 holds NOR2GATE-1K7(a,b) be  non emptyXBOOLE-0V1 iff  not (a be  non emptyXBOOLE-0V1 or b be  non emptyXBOOLE-0V1)"
   sorry

mdef gate_1_def_8 ("AND3GATE-1K8'( _ , _ , _ ')" [0,0,0]164 ) where
  mlet "a be setHIDDENM2", "b be setHIDDENM2", "c be setHIDDENM2"
"func AND3GATE-1K8(a,b,c) \<rightarrow> setHIDDENM2 equals
  NOT1GATE-1K1 {}XBOOLE-0K1 if (a be  non emptyXBOOLE-0V1 & b be  non emptyXBOOLE-0V1) & c be  non emptyXBOOLE-0V1 otherwise {}XBOOLE-0K1"
proof-
  (*coherence*)
    show "((a be  non emptyXBOOLE-0V1 & b be  non emptyXBOOLE-0V1) & c be  non emptyXBOOLE-0V1 implies NOT1GATE-1K1 {}XBOOLE-0K1 be setHIDDENM2) & ( not ((a be  non emptyXBOOLE-0V1 & b be  non emptyXBOOLE-0V1) & c be  non emptyXBOOLE-0V1) implies {}XBOOLE-0K1 be setHIDDENM2)"
       sorry
  (*consistency*)
    show " for it be setHIDDENM2 holds  True "
       sorry
qed "sorry"

mtheorem gate_1_cl_17:
  mlet "a be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "b be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "c be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster AND3GATE-1K8(a,b,c) as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "AND3GATE-1K8(a,b,c) be  non emptyXBOOLE-0V1"
    using gate_1_def_8 sorry
qed "sorry"

mtheorem gate_1_cl_18:
  mlet "a be emptyXBOOLE-0V1\<bar>setHIDDENM2", "b be setHIDDENM2", "c be setHIDDENM2"
"cluster AND3GATE-1K8(a,b,c) as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "AND3GATE-1K8(a,b,c) be emptyXBOOLE-0V1"
    using gate_1_def_8 sorry
qed "sorry"

mtheorem gate_1_cl_19:
  mlet "a be emptyXBOOLE-0V1\<bar>setHIDDENM2", "b be setHIDDENM2", "c be setHIDDENM2"
"cluster AND3GATE-1K8(b,a,c) as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "AND3GATE-1K8(b,a,c) be emptyXBOOLE-0V1"
    using gate_1_def_8 sorry
qed "sorry"

mtheorem gate_1_cl_20:
  mlet "a be emptyXBOOLE-0V1\<bar>setHIDDENM2", "b be setHIDDENM2", "c be setHIDDENM2"
"cluster AND3GATE-1K8(b,c,a) as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "AND3GATE-1K8(b,c,a) be emptyXBOOLE-0V1"
    using gate_1_def_8 sorry
qed "sorry"

mtheorem gate_1_th_14:
" for a be setHIDDENM2 holds  for b be setHIDDENM2 holds  for c be setHIDDENM2 holds AND3GATE-1K8(a,b,c) be  non emptyXBOOLE-0V1 iff (a be  non emptyXBOOLE-0V1 & b be  non emptyXBOOLE-0V1) & c be  non emptyXBOOLE-0V1"
   sorry

mdef gate_1_def_9 ("OR3GATE-1K9'( _ , _ , _ ')" [0,0,0]164 ) where
  mlet "a be setHIDDENM2", "b be setHIDDENM2", "c be setHIDDENM2"
"func OR3GATE-1K9(a,b,c) \<rightarrow> setHIDDENM2 equals
  NOT1GATE-1K1 {}XBOOLE-0K1 if (a be  non emptyXBOOLE-0V1 or b be  non emptyXBOOLE-0V1) or c be  non emptyXBOOLE-0V1 otherwise {}XBOOLE-0K1"
proof-
  (*coherence*)
    show "((a be  non emptyXBOOLE-0V1 or b be  non emptyXBOOLE-0V1) or c be  non emptyXBOOLE-0V1 implies NOT1GATE-1K1 {}XBOOLE-0K1 be setHIDDENM2) & ( not ((a be  non emptyXBOOLE-0V1 or b be  non emptyXBOOLE-0V1) or c be  non emptyXBOOLE-0V1) implies {}XBOOLE-0K1 be setHIDDENM2)"
       sorry
  (*consistency*)
    show " for it be setHIDDENM2 holds  True "
       sorry
qed "sorry"

mtheorem gate_1_cl_21:
  mlet "a be emptyXBOOLE-0V1\<bar>setHIDDENM2", "b be emptyXBOOLE-0V1\<bar>setHIDDENM2", "c be emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster OR3GATE-1K9(a,b,c) as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "OR3GATE-1K9(a,b,c) be emptyXBOOLE-0V1"
    using gate_1_def_9 sorry
qed "sorry"

mtheorem gate_1_cl_22:
  mlet "a be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "b be setHIDDENM2", "c be setHIDDENM2"
"cluster OR3GATE-1K9(a,b,c) as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "OR3GATE-1K9(a,b,c) be  non emptyXBOOLE-0V1"
    using gate_1_def_9 sorry
qed "sorry"

mtheorem gate_1_cl_23:
  mlet "a be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "b be setHIDDENM2", "c be setHIDDENM2"
"cluster OR3GATE-1K9(b,a,c) as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "OR3GATE-1K9(b,a,c) be  non emptyXBOOLE-0V1"
    using gate_1_def_9 sorry
qed "sorry"

mtheorem gate_1_cl_24:
  mlet "a be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "b be setHIDDENM2", "c be setHIDDENM2"
"cluster OR3GATE-1K9(b,c,a) as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "OR3GATE-1K9(b,c,a) be  non emptyXBOOLE-0V1"
    using gate_1_def_9 sorry
qed "sorry"

mtheorem gate_1_th_15:
" for a be setHIDDENM2 holds  for b be setHIDDENM2 holds  for c be setHIDDENM2 holds OR3GATE-1K9(a,b,c) be  non emptyXBOOLE-0V1 iff (a be  non emptyXBOOLE-0V1 or b be  non emptyXBOOLE-0V1) or c be  non emptyXBOOLE-0V1"
   sorry

mdef gate_1_def_10 ("XOR3GATE-1K10'( _ , _ , _ ')" [0,0,0]164 ) where
  mlet "a be setHIDDENM2", "b be setHIDDENM2", "c be setHIDDENM2"
"func XOR3GATE-1K10(a,b,c) \<rightarrow> setHIDDENM2 equals
  NOT1GATE-1K1 {}XBOOLE-0K1 if (a be  non emptyXBOOLE-0V1 &  not b be  non emptyXBOOLE-0V1 or  not a be  non emptyXBOOLE-0V1 & b be  non emptyXBOOLE-0V1) &  not c be  non emptyXBOOLE-0V1 or  not (a be  non emptyXBOOLE-0V1 &  not b be  non emptyXBOOLE-0V1 or  not a be  non emptyXBOOLE-0V1 & b be  non emptyXBOOLE-0V1) & c be  non emptyXBOOLE-0V1 otherwise {}XBOOLE-0K1"
proof-
  (*coherence*)
    show "((a be  non emptyXBOOLE-0V1 &  not b be  non emptyXBOOLE-0V1 or  not a be  non emptyXBOOLE-0V1 & b be  non emptyXBOOLE-0V1) &  not c be  non emptyXBOOLE-0V1 or  not (a be  non emptyXBOOLE-0V1 &  not b be  non emptyXBOOLE-0V1 or  not a be  non emptyXBOOLE-0V1 & b be  non emptyXBOOLE-0V1) & c be  non emptyXBOOLE-0V1 implies NOT1GATE-1K1 {}XBOOLE-0K1 be setHIDDENM2) & ( not ((a be  non emptyXBOOLE-0V1 &  not b be  non emptyXBOOLE-0V1 or  not a be  non emptyXBOOLE-0V1 & b be  non emptyXBOOLE-0V1) &  not c be  non emptyXBOOLE-0V1 or  not (a be  non emptyXBOOLE-0V1 &  not b be  non emptyXBOOLE-0V1 or  not a be  non emptyXBOOLE-0V1 & b be  non emptyXBOOLE-0V1) & c be  non emptyXBOOLE-0V1) implies {}XBOOLE-0K1 be setHIDDENM2)"
       sorry
  (*consistency*)
    show " for it be setHIDDENM2 holds  True "
       sorry
qed "sorry"

mtheorem gate_1_cl_25:
  mlet "a be emptyXBOOLE-0V1\<bar>setHIDDENM2", "b be emptyXBOOLE-0V1\<bar>setHIDDENM2", "c be emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster XOR3GATE-1K10(a,b,c) as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "XOR3GATE-1K10(a,b,c) be emptyXBOOLE-0V1"
    using gate_1_def_10 sorry
qed "sorry"

mtheorem gate_1_cl_26:
  mlet "a be emptyXBOOLE-0V1\<bar>setHIDDENM2", "b be emptyXBOOLE-0V1\<bar>setHIDDENM2", "c be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster XOR3GATE-1K10(a,b,c) as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "XOR3GATE-1K10(a,b,c) be  non emptyXBOOLE-0V1"
    using gate_1_def_10 sorry
qed "sorry"

mtheorem gate_1_cl_27:
  mlet "a be emptyXBOOLE-0V1\<bar>setHIDDENM2", "b be emptyXBOOLE-0V1\<bar>setHIDDENM2", "c be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster XOR3GATE-1K10(a,c,b) as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "XOR3GATE-1K10(a,c,b) be  non emptyXBOOLE-0V1"
    using gate_1_def_10 sorry
qed "sorry"

mtheorem gate_1_cl_28:
  mlet "a be emptyXBOOLE-0V1\<bar>setHIDDENM2", "b be emptyXBOOLE-0V1\<bar>setHIDDENM2", "c be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster XOR3GATE-1K10(c,a,b) as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "XOR3GATE-1K10(c,a,b) be  non emptyXBOOLE-0V1"
    using gate_1_def_10 sorry
qed "sorry"

mtheorem gate_1_cl_29:
  mlet "a be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "b be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "c be emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster XOR3GATE-1K10(a,b,c) as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "XOR3GATE-1K10(a,b,c) be emptyXBOOLE-0V1"
    using gate_1_def_10 sorry
qed "sorry"

mtheorem gate_1_cl_30:
  mlet "a be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "b be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "c be emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster XOR3GATE-1K10(a,c,b) as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "XOR3GATE-1K10(a,c,b) be emptyXBOOLE-0V1"
    using gate_1_def_10 sorry
qed "sorry"

mtheorem gate_1_cl_31:
  mlet "a be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "b be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "c be emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster XOR3GATE-1K10(c,a,b) as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "XOR3GATE-1K10(c,a,b) be emptyXBOOLE-0V1"
    using gate_1_def_10 sorry
qed "sorry"

mtheorem gate_1_cl_32:
  mlet "a be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "b be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "c be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster XOR3GATE-1K10(a,b,c) as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "XOR3GATE-1K10(a,b,c) be  non emptyXBOOLE-0V1"
    using gate_1_def_10 sorry
qed "sorry"

mtheorem gate_1_th_16:
" for a be setHIDDENM2 holds  for b be setHIDDENM2 holds  for c be setHIDDENM2 holds XOR3GATE-1K10(a,b,c) be  non emptyXBOOLE-0V1 iff (a be  non emptyXBOOLE-0V1 &  not b be  non emptyXBOOLE-0V1 or  not a be  non emptyXBOOLE-0V1 & b be  non emptyXBOOLE-0V1) &  not c be  non emptyXBOOLE-0V1 or  not (a be  non emptyXBOOLE-0V1 &  not b be  non emptyXBOOLE-0V1 or  not a be  non emptyXBOOLE-0V1 & b be  non emptyXBOOLE-0V1) & c be  non emptyXBOOLE-0V1"
   sorry

mdef gate_1_def_11 ("MAJ3GATE-1K11'( _ , _ , _ ')" [0,0,0]164 ) where
  mlet "a be setHIDDENM2", "b be setHIDDENM2", "c be setHIDDENM2"
"func MAJ3GATE-1K11(a,b,c) \<rightarrow> setHIDDENM2 equals
  NOT1GATE-1K1 {}XBOOLE-0K1 if (a be  non emptyXBOOLE-0V1 & b be  non emptyXBOOLE-0V1 or b be  non emptyXBOOLE-0V1 & c be  non emptyXBOOLE-0V1) or c be  non emptyXBOOLE-0V1 & a be  non emptyXBOOLE-0V1 otherwise {}XBOOLE-0K1"
proof-
  (*coherence*)
    show "((a be  non emptyXBOOLE-0V1 & b be  non emptyXBOOLE-0V1 or b be  non emptyXBOOLE-0V1 & c be  non emptyXBOOLE-0V1) or c be  non emptyXBOOLE-0V1 & a be  non emptyXBOOLE-0V1 implies NOT1GATE-1K1 {}XBOOLE-0K1 be setHIDDENM2) & ( not ((a be  non emptyXBOOLE-0V1 & b be  non emptyXBOOLE-0V1 or b be  non emptyXBOOLE-0V1 & c be  non emptyXBOOLE-0V1) or c be  non emptyXBOOLE-0V1 & a be  non emptyXBOOLE-0V1) implies {}XBOOLE-0K1 be setHIDDENM2)"
       sorry
  (*consistency*)
    show " for it be setHIDDENM2 holds  True "
       sorry
qed "sorry"

mtheorem gate_1_cl_33:
  mlet "a be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "b be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "c be setHIDDENM2"
"cluster MAJ3GATE-1K11(a,b,c) as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "MAJ3GATE-1K11(a,b,c) be  non emptyXBOOLE-0V1"
    using gate_1_def_11 sorry
qed "sorry"

mtheorem gate_1_cl_34:
  mlet "a be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "b be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "c be setHIDDENM2"
"cluster MAJ3GATE-1K11(a,c,b) as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "MAJ3GATE-1K11(a,c,b) be  non emptyXBOOLE-0V1"
    using gate_1_def_11 sorry
qed "sorry"

mtheorem gate_1_cl_35:
  mlet "a be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "b be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "c be setHIDDENM2"
"cluster MAJ3GATE-1K11(c,a,b) as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "MAJ3GATE-1K11(c,a,b) be  non emptyXBOOLE-0V1"
    using gate_1_def_11 sorry
qed "sorry"

mtheorem gate_1_cl_36:
  mlet "a be emptyXBOOLE-0V1\<bar>setHIDDENM2", "b be emptyXBOOLE-0V1\<bar>setHIDDENM2", "c be setHIDDENM2"
"cluster MAJ3GATE-1K11(a,b,c) as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "MAJ3GATE-1K11(a,b,c) be emptyXBOOLE-0V1"
    using gate_1_def_11 sorry
qed "sorry"

mtheorem gate_1_cl_37:
  mlet "a be emptyXBOOLE-0V1\<bar>setHIDDENM2", "b be emptyXBOOLE-0V1\<bar>setHIDDENM2", "c be setHIDDENM2"
"cluster MAJ3GATE-1K11(a,c,b) as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "MAJ3GATE-1K11(a,c,b) be emptyXBOOLE-0V1"
    using gate_1_def_11 sorry
qed "sorry"

mtheorem gate_1_cl_38:
  mlet "a be emptyXBOOLE-0V1\<bar>setHIDDENM2", "b be emptyXBOOLE-0V1\<bar>setHIDDENM2", "c be setHIDDENM2"
"cluster MAJ3GATE-1K11(c,a,b) as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "MAJ3GATE-1K11(c,a,b) be emptyXBOOLE-0V1"
    using gate_1_def_11 sorry
qed "sorry"

mtheorem gate_1_th_17:
" for a be setHIDDENM2 holds  for b be setHIDDENM2 holds  for c be setHIDDENM2 holds MAJ3GATE-1K11(a,b,c) be  non emptyXBOOLE-0V1 iff (a be  non emptyXBOOLE-0V1 & b be  non emptyXBOOLE-0V1 or b be  non emptyXBOOLE-0V1 & c be  non emptyXBOOLE-0V1) or c be  non emptyXBOOLE-0V1 & a be  non emptyXBOOLE-0V1"
   sorry

mdef gate_1_def_12 ("NAND3GATE-1K12'( _ , _ , _ ')" [0,0,0]164 ) where
  mlet "a be setHIDDENM2", "b be setHIDDENM2", "c be setHIDDENM2"
"func NAND3GATE-1K12(a,b,c) \<rightarrow> setHIDDENM2 equals
  NOT1GATE-1K1 {}XBOOLE-0K1 if  not ((a be  non emptyXBOOLE-0V1 & b be  non emptyXBOOLE-0V1) & c be  non emptyXBOOLE-0V1) otherwise {}XBOOLE-0K1"
proof-
  (*coherence*)
    show "( not ((a be  non emptyXBOOLE-0V1 & b be  non emptyXBOOLE-0V1) & c be  non emptyXBOOLE-0V1) implies NOT1GATE-1K1 {}XBOOLE-0K1 be setHIDDENM2) & ( not ( not ((a be  non emptyXBOOLE-0V1 & b be  non emptyXBOOLE-0V1) & c be  non emptyXBOOLE-0V1)) implies {}XBOOLE-0K1 be setHIDDENM2)"
       sorry
  (*consistency*)
    show " for it be setHIDDENM2 holds  True "
       sorry
qed "sorry"

mtheorem gate_1_th_18:
" for a be setHIDDENM2 holds  for b be setHIDDENM2 holds  for c be setHIDDENM2 holds NAND3GATE-1K12(a,b,c) be  non emptyXBOOLE-0V1 iff  not ((a be  non emptyXBOOLE-0V1 & b be  non emptyXBOOLE-0V1) & c be  non emptyXBOOLE-0V1)"
  using gate_1_def_12 sorry

mdef gate_1_def_13 ("NOR3GATE-1K13'( _ , _ , _ ')" [0,0,0]164 ) where
  mlet "a be setHIDDENM2", "b be setHIDDENM2", "c be setHIDDENM2"
"func NOR3GATE-1K13(a,b,c) \<rightarrow> setHIDDENM2 equals
  NOT1GATE-1K1 {}XBOOLE-0K1 if  not ((a be  non emptyXBOOLE-0V1 or b be  non emptyXBOOLE-0V1) or c be  non emptyXBOOLE-0V1) otherwise {}XBOOLE-0K1"
proof-
  (*coherence*)
    show "( not ((a be  non emptyXBOOLE-0V1 or b be  non emptyXBOOLE-0V1) or c be  non emptyXBOOLE-0V1) implies NOT1GATE-1K1 {}XBOOLE-0K1 be setHIDDENM2) & ( not ( not ((a be  non emptyXBOOLE-0V1 or b be  non emptyXBOOLE-0V1) or c be  non emptyXBOOLE-0V1)) implies {}XBOOLE-0K1 be setHIDDENM2)"
       sorry
  (*consistency*)
    show " for it be setHIDDENM2 holds  True "
       sorry
qed "sorry"

mtheorem gate_1_th_19:
" for a be setHIDDENM2 holds  for b be setHIDDENM2 holds  for c be setHIDDENM2 holds NOR3GATE-1K13(a,b,c) be  non emptyXBOOLE-0V1 iff  not ((a be  non emptyXBOOLE-0V1 or b be  non emptyXBOOLE-0V1) or c be  non emptyXBOOLE-0V1)"
  using gate_1_def_13 sorry

mdef gate_1_def_14 ("AND4GATE-1K14'( _ , _ , _ , _ ')" [0,0,0,0]164 ) where
  mlet "a be setHIDDENM2", "b be setHIDDENM2", "c be setHIDDENM2", "d be setHIDDENM2"
"func AND4GATE-1K14(a,b,c,d) \<rightarrow> setHIDDENM2 equals
  NOT1GATE-1K1 {}XBOOLE-0K1 if ((a be  non emptyXBOOLE-0V1 & b be  non emptyXBOOLE-0V1) & c be  non emptyXBOOLE-0V1) & d be  non emptyXBOOLE-0V1 otherwise {}XBOOLE-0K1"
proof-
  (*coherence*)
    show "(((a be  non emptyXBOOLE-0V1 & b be  non emptyXBOOLE-0V1) & c be  non emptyXBOOLE-0V1) & d be  non emptyXBOOLE-0V1 implies NOT1GATE-1K1 {}XBOOLE-0K1 be setHIDDENM2) & ( not (((a be  non emptyXBOOLE-0V1 & b be  non emptyXBOOLE-0V1) & c be  non emptyXBOOLE-0V1) & d be  non emptyXBOOLE-0V1) implies {}XBOOLE-0K1 be setHIDDENM2)"
       sorry
  (*consistency*)
    show " for it be setHIDDENM2 holds  True "
       sorry
qed "sorry"

mtheorem gate_1_th_20:
" for a be setHIDDENM2 holds  for b be setHIDDENM2 holds  for c be setHIDDENM2 holds  for d be setHIDDENM2 holds AND4GATE-1K14(a,b,c,d) be  non emptyXBOOLE-0V1 iff ((a be  non emptyXBOOLE-0V1 & b be  non emptyXBOOLE-0V1) & c be  non emptyXBOOLE-0V1) & d be  non emptyXBOOLE-0V1"
  using gate_1_def_14 sorry

mdef gate_1_def_15 ("OR4GATE-1K15'( _ , _ , _ , _ ')" [0,0,0,0]164 ) where
  mlet "a be setHIDDENM2", "b be setHIDDENM2", "c be setHIDDENM2", "d be setHIDDENM2"
"func OR4GATE-1K15(a,b,c,d) \<rightarrow> setHIDDENM2 equals
  NOT1GATE-1K1 {}XBOOLE-0K1 if ((a be  non emptyXBOOLE-0V1 or b be  non emptyXBOOLE-0V1) or c be  non emptyXBOOLE-0V1) or d be  non emptyXBOOLE-0V1 otherwise {}XBOOLE-0K1"
proof-
  (*coherence*)
    show "(((a be  non emptyXBOOLE-0V1 or b be  non emptyXBOOLE-0V1) or c be  non emptyXBOOLE-0V1) or d be  non emptyXBOOLE-0V1 implies NOT1GATE-1K1 {}XBOOLE-0K1 be setHIDDENM2) & ( not (((a be  non emptyXBOOLE-0V1 or b be  non emptyXBOOLE-0V1) or c be  non emptyXBOOLE-0V1) or d be  non emptyXBOOLE-0V1) implies {}XBOOLE-0K1 be setHIDDENM2)"
       sorry
  (*consistency*)
    show " for it be setHIDDENM2 holds  True "
       sorry
qed "sorry"

mtheorem gate_1_th_21:
" for a be setHIDDENM2 holds  for b be setHIDDENM2 holds  for c be setHIDDENM2 holds  for d be setHIDDENM2 holds OR4GATE-1K15(a,b,c,d) be  non emptyXBOOLE-0V1 iff ((a be  non emptyXBOOLE-0V1 or b be  non emptyXBOOLE-0V1) or c be  non emptyXBOOLE-0V1) or d be  non emptyXBOOLE-0V1"
  using gate_1_def_15 sorry

mdef gate_1_def_16 ("NAND4GATE-1K16'( _ , _ , _ , _ ')" [0,0,0,0]164 ) where
  mlet "a be setHIDDENM2", "b be setHIDDENM2", "c be setHIDDENM2", "d be setHIDDENM2"
"func NAND4GATE-1K16(a,b,c,d) \<rightarrow> setHIDDENM2 equals
  NOT1GATE-1K1 {}XBOOLE-0K1 if  not (((a be  non emptyXBOOLE-0V1 & b be  non emptyXBOOLE-0V1) & c be  non emptyXBOOLE-0V1) & d be  non emptyXBOOLE-0V1) otherwise {}XBOOLE-0K1"
proof-
  (*coherence*)
    show "( not (((a be  non emptyXBOOLE-0V1 & b be  non emptyXBOOLE-0V1) & c be  non emptyXBOOLE-0V1) & d be  non emptyXBOOLE-0V1) implies NOT1GATE-1K1 {}XBOOLE-0K1 be setHIDDENM2) & ( not ( not (((a be  non emptyXBOOLE-0V1 & b be  non emptyXBOOLE-0V1) & c be  non emptyXBOOLE-0V1) & d be  non emptyXBOOLE-0V1)) implies {}XBOOLE-0K1 be setHIDDENM2)"
       sorry
  (*consistency*)
    show " for it be setHIDDENM2 holds  True "
       sorry
qed "sorry"

mtheorem gate_1_th_22:
" for a be setHIDDENM2 holds  for b be setHIDDENM2 holds  for c be setHIDDENM2 holds  for d be setHIDDENM2 holds NAND4GATE-1K16(a,b,c,d) be  non emptyXBOOLE-0V1 iff  not (((a be  non emptyXBOOLE-0V1 & b be  non emptyXBOOLE-0V1) & c be  non emptyXBOOLE-0V1) & d be  non emptyXBOOLE-0V1)"
  using gate_1_def_16 sorry

mdef gate_1_def_17 ("NOR4GATE-1K17'( _ , _ , _ , _ ')" [0,0,0,0]164 ) where
  mlet "a be setHIDDENM2", "b be setHIDDENM2", "c be setHIDDENM2", "d be setHIDDENM2"
"func NOR4GATE-1K17(a,b,c,d) \<rightarrow> setHIDDENM2 equals
  NOT1GATE-1K1 {}XBOOLE-0K1 if  not (((a be  non emptyXBOOLE-0V1 or b be  non emptyXBOOLE-0V1) or c be  non emptyXBOOLE-0V1) or d be  non emptyXBOOLE-0V1) otherwise {}XBOOLE-0K1"
proof-
  (*coherence*)
    show "( not (((a be  non emptyXBOOLE-0V1 or b be  non emptyXBOOLE-0V1) or c be  non emptyXBOOLE-0V1) or d be  non emptyXBOOLE-0V1) implies NOT1GATE-1K1 {}XBOOLE-0K1 be setHIDDENM2) & ( not ( not (((a be  non emptyXBOOLE-0V1 or b be  non emptyXBOOLE-0V1) or c be  non emptyXBOOLE-0V1) or d be  non emptyXBOOLE-0V1)) implies {}XBOOLE-0K1 be setHIDDENM2)"
       sorry
  (*consistency*)
    show " for it be setHIDDENM2 holds  True "
       sorry
qed "sorry"

mtheorem gate_1_th_23:
" for a be setHIDDENM2 holds  for b be setHIDDENM2 holds  for c be setHIDDENM2 holds  for d be setHIDDENM2 holds NOR4GATE-1K17(a,b,c,d) be  non emptyXBOOLE-0V1 iff  not (((a be  non emptyXBOOLE-0V1 or b be  non emptyXBOOLE-0V1) or c be  non emptyXBOOLE-0V1) or d be  non emptyXBOOLE-0V1)"
  using gate_1_def_17 sorry

mdef gate_1_def_18 ("AND5GATE-1K18'( _ , _ , _ , _ , _ ')" [0,0,0,0,0]164 ) where
  mlet "a be setHIDDENM2", "b be setHIDDENM2", "c be setHIDDENM2", "d be setHIDDENM2", "e be setHIDDENM2"
"func AND5GATE-1K18(a,b,c,d,e) \<rightarrow> setHIDDENM2 equals
  NOT1GATE-1K1 {}XBOOLE-0K1 if (((a be  non emptyXBOOLE-0V1 & b be  non emptyXBOOLE-0V1) & c be  non emptyXBOOLE-0V1) & d be  non emptyXBOOLE-0V1) & e be  non emptyXBOOLE-0V1 otherwise {}XBOOLE-0K1"
proof-
  (*coherence*)
    show "((((a be  non emptyXBOOLE-0V1 & b be  non emptyXBOOLE-0V1) & c be  non emptyXBOOLE-0V1) & d be  non emptyXBOOLE-0V1) & e be  non emptyXBOOLE-0V1 implies NOT1GATE-1K1 {}XBOOLE-0K1 be setHIDDENM2) & ( not ((((a be  non emptyXBOOLE-0V1 & b be  non emptyXBOOLE-0V1) & c be  non emptyXBOOLE-0V1) & d be  non emptyXBOOLE-0V1) & e be  non emptyXBOOLE-0V1) implies {}XBOOLE-0K1 be setHIDDENM2)"
       sorry
  (*consistency*)
    show " for it be setHIDDENM2 holds  True "
       sorry
qed "sorry"

mtheorem gate_1_th_24:
" for a be setHIDDENM2 holds  for b be setHIDDENM2 holds  for c be setHIDDENM2 holds  for d be setHIDDENM2 holds  for e be setHIDDENM2 holds AND5GATE-1K18(a,b,c,d,e) be  non emptyXBOOLE-0V1 iff (((a be  non emptyXBOOLE-0V1 & b be  non emptyXBOOLE-0V1) & c be  non emptyXBOOLE-0V1) & d be  non emptyXBOOLE-0V1) & e be  non emptyXBOOLE-0V1"
  using gate_1_def_18 sorry

mdef gate_1_def_19 ("OR5GATE-1K19'( _ , _ , _ , _ , _ ')" [0,0,0,0,0]164 ) where
  mlet "a be setHIDDENM2", "b be setHIDDENM2", "c be setHIDDENM2", "d be setHIDDENM2", "e be setHIDDENM2"
"func OR5GATE-1K19(a,b,c,d,e) \<rightarrow> setHIDDENM2 equals
  NOT1GATE-1K1 {}XBOOLE-0K1 if (((a be  non emptyXBOOLE-0V1 or b be  non emptyXBOOLE-0V1) or c be  non emptyXBOOLE-0V1) or d be  non emptyXBOOLE-0V1) or e be  non emptyXBOOLE-0V1 otherwise {}XBOOLE-0K1"
proof-
  (*coherence*)
    show "((((a be  non emptyXBOOLE-0V1 or b be  non emptyXBOOLE-0V1) or c be  non emptyXBOOLE-0V1) or d be  non emptyXBOOLE-0V1) or e be  non emptyXBOOLE-0V1 implies NOT1GATE-1K1 {}XBOOLE-0K1 be setHIDDENM2) & ( not ((((a be  non emptyXBOOLE-0V1 or b be  non emptyXBOOLE-0V1) or c be  non emptyXBOOLE-0V1) or d be  non emptyXBOOLE-0V1) or e be  non emptyXBOOLE-0V1) implies {}XBOOLE-0K1 be setHIDDENM2)"
       sorry
  (*consistency*)
    show " for it be setHIDDENM2 holds  True "
       sorry
qed "sorry"

mtheorem gate_1_th_25:
" for a be setHIDDENM2 holds  for b be setHIDDENM2 holds  for c be setHIDDENM2 holds  for d be setHIDDENM2 holds  for e be setHIDDENM2 holds OR5GATE-1K19(a,b,c,d,e) be  non emptyXBOOLE-0V1 iff (((a be  non emptyXBOOLE-0V1 or b be  non emptyXBOOLE-0V1) or c be  non emptyXBOOLE-0V1) or d be  non emptyXBOOLE-0V1) or e be  non emptyXBOOLE-0V1"
  using gate_1_def_19 sorry

mdef gate_1_def_20 ("NAND5GATE-1K20'( _ , _ , _ , _ , _ ')" [0,0,0,0,0]164 ) where
  mlet "a be setHIDDENM2", "b be setHIDDENM2", "c be setHIDDENM2", "d be setHIDDENM2", "e be setHIDDENM2"
"func NAND5GATE-1K20(a,b,c,d,e) \<rightarrow> setHIDDENM2 equals
  NOT1GATE-1K1 {}XBOOLE-0K1 if  not ((((a be  non emptyXBOOLE-0V1 & b be  non emptyXBOOLE-0V1) & c be  non emptyXBOOLE-0V1) & d be  non emptyXBOOLE-0V1) & e be  non emptyXBOOLE-0V1) otherwise {}XBOOLE-0K1"
proof-
  (*coherence*)
    show "( not ((((a be  non emptyXBOOLE-0V1 & b be  non emptyXBOOLE-0V1) & c be  non emptyXBOOLE-0V1) & d be  non emptyXBOOLE-0V1) & e be  non emptyXBOOLE-0V1) implies NOT1GATE-1K1 {}XBOOLE-0K1 be setHIDDENM2) & ( not ( not ((((a be  non emptyXBOOLE-0V1 & b be  non emptyXBOOLE-0V1) & c be  non emptyXBOOLE-0V1) & d be  non emptyXBOOLE-0V1) & e be  non emptyXBOOLE-0V1)) implies {}XBOOLE-0K1 be setHIDDENM2)"
       sorry
  (*consistency*)
    show " for it be setHIDDENM2 holds  True "
       sorry
qed "sorry"

mtheorem gate_1_th_26:
" for a be setHIDDENM2 holds  for b be setHIDDENM2 holds  for c be setHIDDENM2 holds  for d be setHIDDENM2 holds  for e be setHIDDENM2 holds NAND5GATE-1K20(a,b,c,d,e) be  non emptyXBOOLE-0V1 iff  not ((((a be  non emptyXBOOLE-0V1 & b be  non emptyXBOOLE-0V1) & c be  non emptyXBOOLE-0V1) & d be  non emptyXBOOLE-0V1) & e be  non emptyXBOOLE-0V1)"
  using gate_1_def_20 sorry

mdef gate_1_def_21 ("NOR5GATE-1K21'( _ , _ , _ , _ , _ ')" [0,0,0,0,0]164 ) where
  mlet "a be setHIDDENM2", "b be setHIDDENM2", "c be setHIDDENM2", "d be setHIDDENM2", "e be setHIDDENM2"
"func NOR5GATE-1K21(a,b,c,d,e) \<rightarrow> setHIDDENM2 equals
  NOT1GATE-1K1 {}XBOOLE-0K1 if  not ((((a be  non emptyXBOOLE-0V1 or b be  non emptyXBOOLE-0V1) or c be  non emptyXBOOLE-0V1) or d be  non emptyXBOOLE-0V1) or e be  non emptyXBOOLE-0V1) otherwise {}XBOOLE-0K1"
proof-
  (*coherence*)
    show "( not ((((a be  non emptyXBOOLE-0V1 or b be  non emptyXBOOLE-0V1) or c be  non emptyXBOOLE-0V1) or d be  non emptyXBOOLE-0V1) or e be  non emptyXBOOLE-0V1) implies NOT1GATE-1K1 {}XBOOLE-0K1 be setHIDDENM2) & ( not ( not ((((a be  non emptyXBOOLE-0V1 or b be  non emptyXBOOLE-0V1) or c be  non emptyXBOOLE-0V1) or d be  non emptyXBOOLE-0V1) or e be  non emptyXBOOLE-0V1)) implies {}XBOOLE-0K1 be setHIDDENM2)"
       sorry
  (*consistency*)
    show " for it be setHIDDENM2 holds  True "
       sorry
qed "sorry"

mtheorem gate_1_th_27:
" for a be setHIDDENM2 holds  for b be setHIDDENM2 holds  for c be setHIDDENM2 holds  for d be setHIDDENM2 holds  for e be setHIDDENM2 holds NOR5GATE-1K21(a,b,c,d,e) be  non emptyXBOOLE-0V1 iff  not ((((a be  non emptyXBOOLE-0V1 or b be  non emptyXBOOLE-0V1) or c be  non emptyXBOOLE-0V1) or d be  non emptyXBOOLE-0V1) or e be  non emptyXBOOLE-0V1)"
  using gate_1_def_21 sorry

mdef gate_1_def_22 ("AND6GATE-1K22'( _ , _ , _ , _ , _ , _ ')" [0,0,0,0,0,0]164 ) where
  mlet "a be setHIDDENM2", "b be setHIDDENM2", "c be setHIDDENM2", "d be setHIDDENM2", "e be setHIDDENM2", "f be setHIDDENM2"
"func AND6GATE-1K22(a,b,c,d,e,f) \<rightarrow> setHIDDENM2 equals
  NOT1GATE-1K1 {}XBOOLE-0K1 if ((((a be  non emptyXBOOLE-0V1 & b be  non emptyXBOOLE-0V1) & c be  non emptyXBOOLE-0V1) & d be  non emptyXBOOLE-0V1) & e be  non emptyXBOOLE-0V1) & f be  non emptyXBOOLE-0V1 otherwise {}XBOOLE-0K1"
proof-
  (*coherence*)
    show "(((((a be  non emptyXBOOLE-0V1 & b be  non emptyXBOOLE-0V1) & c be  non emptyXBOOLE-0V1) & d be  non emptyXBOOLE-0V1) & e be  non emptyXBOOLE-0V1) & f be  non emptyXBOOLE-0V1 implies NOT1GATE-1K1 {}XBOOLE-0K1 be setHIDDENM2) & ( not (((((a be  non emptyXBOOLE-0V1 & b be  non emptyXBOOLE-0V1) & c be  non emptyXBOOLE-0V1) & d be  non emptyXBOOLE-0V1) & e be  non emptyXBOOLE-0V1) & f be  non emptyXBOOLE-0V1) implies {}XBOOLE-0K1 be setHIDDENM2)"
       sorry
  (*consistency*)
    show " for it be setHIDDENM2 holds  True "
       sorry
qed "sorry"

mtheorem gate_1_th_28:
" for a be setHIDDENM2 holds  for b be setHIDDENM2 holds  for c be setHIDDENM2 holds  for d be setHIDDENM2 holds  for e be setHIDDENM2 holds  for f be setHIDDENM2 holds AND6GATE-1K22(a,b,c,d,e,f) be  non emptyXBOOLE-0V1 iff ((((a be  non emptyXBOOLE-0V1 & b be  non emptyXBOOLE-0V1) & c be  non emptyXBOOLE-0V1) & d be  non emptyXBOOLE-0V1) & e be  non emptyXBOOLE-0V1) & f be  non emptyXBOOLE-0V1"
  using gate_1_def_22 sorry

mdef gate_1_def_23 ("OR6GATE-1K23'( _ , _ , _ , _ , _ , _ ')" [0,0,0,0,0,0]164 ) where
  mlet "a be setHIDDENM2", "b be setHIDDENM2", "c be setHIDDENM2", "d be setHIDDENM2", "e be setHIDDENM2", "f be setHIDDENM2"
"func OR6GATE-1K23(a,b,c,d,e,f) \<rightarrow> setHIDDENM2 equals
  NOT1GATE-1K1 {}XBOOLE-0K1 if ((((a be  non emptyXBOOLE-0V1 or b be  non emptyXBOOLE-0V1) or c be  non emptyXBOOLE-0V1) or d be  non emptyXBOOLE-0V1) or e be  non emptyXBOOLE-0V1) or f be  non emptyXBOOLE-0V1 otherwise {}XBOOLE-0K1"
proof-
  (*coherence*)
    show "(((((a be  non emptyXBOOLE-0V1 or b be  non emptyXBOOLE-0V1) or c be  non emptyXBOOLE-0V1) or d be  non emptyXBOOLE-0V1) or e be  non emptyXBOOLE-0V1) or f be  non emptyXBOOLE-0V1 implies NOT1GATE-1K1 {}XBOOLE-0K1 be setHIDDENM2) & ( not (((((a be  non emptyXBOOLE-0V1 or b be  non emptyXBOOLE-0V1) or c be  non emptyXBOOLE-0V1) or d be  non emptyXBOOLE-0V1) or e be  non emptyXBOOLE-0V1) or f be  non emptyXBOOLE-0V1) implies {}XBOOLE-0K1 be setHIDDENM2)"
       sorry
  (*consistency*)
    show " for it be setHIDDENM2 holds  True "
       sorry
qed "sorry"

mtheorem gate_1_th_29:
" for a be setHIDDENM2 holds  for b be setHIDDENM2 holds  for c be setHIDDENM2 holds  for d be setHIDDENM2 holds  for e be setHIDDENM2 holds  for f be setHIDDENM2 holds OR6GATE-1K23(a,b,c,d,e,f) be  non emptyXBOOLE-0V1 iff ((((a be  non emptyXBOOLE-0V1 or b be  non emptyXBOOLE-0V1) or c be  non emptyXBOOLE-0V1) or d be  non emptyXBOOLE-0V1) or e be  non emptyXBOOLE-0V1) or f be  non emptyXBOOLE-0V1"
  using gate_1_def_23 sorry

mdef gate_1_def_24 ("NAND6GATE-1K24'( _ , _ , _ , _ , _ , _ ')" [0,0,0,0,0,0]164 ) where
  mlet "a be setHIDDENM2", "b be setHIDDENM2", "c be setHIDDENM2", "d be setHIDDENM2", "e be setHIDDENM2", "f be setHIDDENM2"
"func NAND6GATE-1K24(a,b,c,d,e,f) \<rightarrow> setHIDDENM2 equals
  NOT1GATE-1K1 {}XBOOLE-0K1 if  not (((((a be  non emptyXBOOLE-0V1 & b be  non emptyXBOOLE-0V1) & c be  non emptyXBOOLE-0V1) & d be  non emptyXBOOLE-0V1) & e be  non emptyXBOOLE-0V1) & f be  non emptyXBOOLE-0V1) otherwise {}XBOOLE-0K1"
proof-
  (*coherence*)
    show "( not (((((a be  non emptyXBOOLE-0V1 & b be  non emptyXBOOLE-0V1) & c be  non emptyXBOOLE-0V1) & d be  non emptyXBOOLE-0V1) & e be  non emptyXBOOLE-0V1) & f be  non emptyXBOOLE-0V1) implies NOT1GATE-1K1 {}XBOOLE-0K1 be setHIDDENM2) & ( not ( not (((((a be  non emptyXBOOLE-0V1 & b be  non emptyXBOOLE-0V1) & c be  non emptyXBOOLE-0V1) & d be  non emptyXBOOLE-0V1) & e be  non emptyXBOOLE-0V1) & f be  non emptyXBOOLE-0V1)) implies {}XBOOLE-0K1 be setHIDDENM2)"
       sorry
  (*consistency*)
    show " for it be setHIDDENM2 holds  True "
       sorry
qed "sorry"

mtheorem gate_1_th_30:
" for a be setHIDDENM2 holds  for b be setHIDDENM2 holds  for c be setHIDDENM2 holds  for d be setHIDDENM2 holds  for e be setHIDDENM2 holds  for f be setHIDDENM2 holds NAND6GATE-1K24(a,b,c,d,e,f) be  non emptyXBOOLE-0V1 iff  not (((((a be  non emptyXBOOLE-0V1 & b be  non emptyXBOOLE-0V1) & c be  non emptyXBOOLE-0V1) & d be  non emptyXBOOLE-0V1) & e be  non emptyXBOOLE-0V1) & f be  non emptyXBOOLE-0V1)"
  using gate_1_def_24 sorry

mdef gate_1_def_25 ("NOR6GATE-1K25'( _ , _ , _ , _ , _ , _ ')" [0,0,0,0,0,0]164 ) where
  mlet "a be setHIDDENM2", "b be setHIDDENM2", "c be setHIDDENM2", "d be setHIDDENM2", "e be setHIDDENM2", "f be setHIDDENM2"
"func NOR6GATE-1K25(a,b,c,d,e,f) \<rightarrow> setHIDDENM2 equals
  NOT1GATE-1K1 {}XBOOLE-0K1 if  not (((((a be  non emptyXBOOLE-0V1 or b be  non emptyXBOOLE-0V1) or c be  non emptyXBOOLE-0V1) or d be  non emptyXBOOLE-0V1) or e be  non emptyXBOOLE-0V1) or f be  non emptyXBOOLE-0V1) otherwise {}XBOOLE-0K1"
proof-
  (*coherence*)
    show "( not (((((a be  non emptyXBOOLE-0V1 or b be  non emptyXBOOLE-0V1) or c be  non emptyXBOOLE-0V1) or d be  non emptyXBOOLE-0V1) or e be  non emptyXBOOLE-0V1) or f be  non emptyXBOOLE-0V1) implies NOT1GATE-1K1 {}XBOOLE-0K1 be setHIDDENM2) & ( not ( not (((((a be  non emptyXBOOLE-0V1 or b be  non emptyXBOOLE-0V1) or c be  non emptyXBOOLE-0V1) or d be  non emptyXBOOLE-0V1) or e be  non emptyXBOOLE-0V1) or f be  non emptyXBOOLE-0V1)) implies {}XBOOLE-0K1 be setHIDDENM2)"
       sorry
  (*consistency*)
    show " for it be setHIDDENM2 holds  True "
       sorry
qed "sorry"

mtheorem gate_1_th_31:
" for a be setHIDDENM2 holds  for b be setHIDDENM2 holds  for c be setHIDDENM2 holds  for d be setHIDDENM2 holds  for e be setHIDDENM2 holds  for f be setHIDDENM2 holds NOR6GATE-1K25(a,b,c,d,e,f) be  non emptyXBOOLE-0V1 iff  not (((((a be  non emptyXBOOLE-0V1 or b be  non emptyXBOOLE-0V1) or c be  non emptyXBOOLE-0V1) or d be  non emptyXBOOLE-0V1) or e be  non emptyXBOOLE-0V1) or f be  non emptyXBOOLE-0V1)"
  using gate_1_def_25 sorry

mdef gate_1_def_26 ("AND7GATE-1K26'( _ , _ , _ , _ , _ , _ , _ ')" [0,0,0,0,0,0,0]164 ) where
  mlet "a be setHIDDENM2", "b be setHIDDENM2", "c be setHIDDENM2", "d be setHIDDENM2", "e be setHIDDENM2", "f be setHIDDENM2", "g be setHIDDENM2"
"func AND7GATE-1K26(a,b,c,d,e,f,g) \<rightarrow> setHIDDENM2 equals
  NOT1GATE-1K1 {}XBOOLE-0K1 if (((((a be  non emptyXBOOLE-0V1 & b be  non emptyXBOOLE-0V1) & c be  non emptyXBOOLE-0V1) & d be  non emptyXBOOLE-0V1) & e be  non emptyXBOOLE-0V1) & f be  non emptyXBOOLE-0V1) & g be  non emptyXBOOLE-0V1 otherwise {}XBOOLE-0K1"
proof-
  (*coherence*)
    show "((((((a be  non emptyXBOOLE-0V1 & b be  non emptyXBOOLE-0V1) & c be  non emptyXBOOLE-0V1) & d be  non emptyXBOOLE-0V1) & e be  non emptyXBOOLE-0V1) & f be  non emptyXBOOLE-0V1) & g be  non emptyXBOOLE-0V1 implies NOT1GATE-1K1 {}XBOOLE-0K1 be setHIDDENM2) & ( not ((((((a be  non emptyXBOOLE-0V1 & b be  non emptyXBOOLE-0V1) & c be  non emptyXBOOLE-0V1) & d be  non emptyXBOOLE-0V1) & e be  non emptyXBOOLE-0V1) & f be  non emptyXBOOLE-0V1) & g be  non emptyXBOOLE-0V1) implies {}XBOOLE-0K1 be setHIDDENM2)"
       sorry
  (*consistency*)
    show " for it be setHIDDENM2 holds  True "
       sorry
qed "sorry"

mtheorem gate_1_th_32:
" for a be setHIDDENM2 holds  for b be setHIDDENM2 holds  for c be setHIDDENM2 holds  for d be setHIDDENM2 holds  for e be setHIDDENM2 holds  for f be setHIDDENM2 holds  for g be setHIDDENM2 holds AND7GATE-1K26(a,b,c,d,e,f,g) be  non emptyXBOOLE-0V1 iff (((((a be  non emptyXBOOLE-0V1 & b be  non emptyXBOOLE-0V1) & c be  non emptyXBOOLE-0V1) & d be  non emptyXBOOLE-0V1) & e be  non emptyXBOOLE-0V1) & f be  non emptyXBOOLE-0V1) & g be  non emptyXBOOLE-0V1"
  using gate_1_def_26 sorry

mdef gate_1_def_27 ("OR7GATE-1K27'( _ , _ , _ , _ , _ , _ , _ ')" [0,0,0,0,0,0,0]164 ) where
  mlet "a be setHIDDENM2", "b be setHIDDENM2", "c be setHIDDENM2", "d be setHIDDENM2", "e be setHIDDENM2", "f be setHIDDENM2", "g be setHIDDENM2"
"func OR7GATE-1K27(a,b,c,d,e,f,g) \<rightarrow> setHIDDENM2 equals
  NOT1GATE-1K1 {}XBOOLE-0K1 if (((((a be  non emptyXBOOLE-0V1 or b be  non emptyXBOOLE-0V1) or c be  non emptyXBOOLE-0V1) or d be  non emptyXBOOLE-0V1) or e be  non emptyXBOOLE-0V1) or f be  non emptyXBOOLE-0V1) or g be  non emptyXBOOLE-0V1 otherwise {}XBOOLE-0K1"
proof-
  (*coherence*)
    show "((((((a be  non emptyXBOOLE-0V1 or b be  non emptyXBOOLE-0V1) or c be  non emptyXBOOLE-0V1) or d be  non emptyXBOOLE-0V1) or e be  non emptyXBOOLE-0V1) or f be  non emptyXBOOLE-0V1) or g be  non emptyXBOOLE-0V1 implies NOT1GATE-1K1 {}XBOOLE-0K1 be setHIDDENM2) & ( not ((((((a be  non emptyXBOOLE-0V1 or b be  non emptyXBOOLE-0V1) or c be  non emptyXBOOLE-0V1) or d be  non emptyXBOOLE-0V1) or e be  non emptyXBOOLE-0V1) or f be  non emptyXBOOLE-0V1) or g be  non emptyXBOOLE-0V1) implies {}XBOOLE-0K1 be setHIDDENM2)"
       sorry
  (*consistency*)
    show " for it be setHIDDENM2 holds  True "
       sorry
qed "sorry"

mtheorem gate_1_th_33:
" for a be setHIDDENM2 holds  for b be setHIDDENM2 holds  for c be setHIDDENM2 holds  for d be setHIDDENM2 holds  for e be setHIDDENM2 holds  for f be setHIDDENM2 holds  for g be setHIDDENM2 holds OR7GATE-1K27(a,b,c,d,e,f,g) be  non emptyXBOOLE-0V1 iff (((((a be  non emptyXBOOLE-0V1 or b be  non emptyXBOOLE-0V1) or c be  non emptyXBOOLE-0V1) or d be  non emptyXBOOLE-0V1) or e be  non emptyXBOOLE-0V1) or f be  non emptyXBOOLE-0V1) or g be  non emptyXBOOLE-0V1"
  using gate_1_def_27 sorry

mdef gate_1_def_28 ("NAND7GATE-1K28'( _ , _ , _ , _ , _ , _ , _ ')" [0,0,0,0,0,0,0]164 ) where
  mlet "a be setHIDDENM2", "b be setHIDDENM2", "c be setHIDDENM2", "d be setHIDDENM2", "e be setHIDDENM2", "f be setHIDDENM2", "g be setHIDDENM2"
"func NAND7GATE-1K28(a,b,c,d,e,f,g) \<rightarrow> setHIDDENM2 equals
  NOT1GATE-1K1 {}XBOOLE-0K1 if  not ((((((a be  non emptyXBOOLE-0V1 & b be  non emptyXBOOLE-0V1) & c be  non emptyXBOOLE-0V1) & d be  non emptyXBOOLE-0V1) & e be  non emptyXBOOLE-0V1) & f be  non emptyXBOOLE-0V1) & g be  non emptyXBOOLE-0V1) otherwise {}XBOOLE-0K1"
proof-
  (*coherence*)
    show "( not ((((((a be  non emptyXBOOLE-0V1 & b be  non emptyXBOOLE-0V1) & c be  non emptyXBOOLE-0V1) & d be  non emptyXBOOLE-0V1) & e be  non emptyXBOOLE-0V1) & f be  non emptyXBOOLE-0V1) & g be  non emptyXBOOLE-0V1) implies NOT1GATE-1K1 {}XBOOLE-0K1 be setHIDDENM2) & ( not ( not ((((((a be  non emptyXBOOLE-0V1 & b be  non emptyXBOOLE-0V1) & c be  non emptyXBOOLE-0V1) & d be  non emptyXBOOLE-0V1) & e be  non emptyXBOOLE-0V1) & f be  non emptyXBOOLE-0V1) & g be  non emptyXBOOLE-0V1)) implies {}XBOOLE-0K1 be setHIDDENM2)"
       sorry
  (*consistency*)
    show " for it be setHIDDENM2 holds  True "
       sorry
qed "sorry"

mtheorem gate_1_th_34:
" for a be setHIDDENM2 holds  for b be setHIDDENM2 holds  for c be setHIDDENM2 holds  for d be setHIDDENM2 holds  for e be setHIDDENM2 holds  for f be setHIDDENM2 holds  for g be setHIDDENM2 holds NAND7GATE-1K28(a,b,c,d,e,f,g) be  non emptyXBOOLE-0V1 iff  not ((((((a be  non emptyXBOOLE-0V1 & b be  non emptyXBOOLE-0V1) & c be  non emptyXBOOLE-0V1) & d be  non emptyXBOOLE-0V1) & e be  non emptyXBOOLE-0V1) & f be  non emptyXBOOLE-0V1) & g be  non emptyXBOOLE-0V1)"
  using gate_1_def_28 sorry

mdef gate_1_def_29 ("NOR7GATE-1K29'( _ , _ , _ , _ , _ , _ , _ ')" [0,0,0,0,0,0,0]164 ) where
  mlet "a be setHIDDENM2", "b be setHIDDENM2", "c be setHIDDENM2", "d be setHIDDENM2", "e be setHIDDENM2", "f be setHIDDENM2", "g be setHIDDENM2"
"func NOR7GATE-1K29(a,b,c,d,e,f,g) \<rightarrow> setHIDDENM2 equals
  NOT1GATE-1K1 {}XBOOLE-0K1 if  not ((((((a be  non emptyXBOOLE-0V1 or b be  non emptyXBOOLE-0V1) or c be  non emptyXBOOLE-0V1) or d be  non emptyXBOOLE-0V1) or e be  non emptyXBOOLE-0V1) or f be  non emptyXBOOLE-0V1) or g be  non emptyXBOOLE-0V1) otherwise {}XBOOLE-0K1"
proof-
  (*coherence*)
    show "( not ((((((a be  non emptyXBOOLE-0V1 or b be  non emptyXBOOLE-0V1) or c be  non emptyXBOOLE-0V1) or d be  non emptyXBOOLE-0V1) or e be  non emptyXBOOLE-0V1) or f be  non emptyXBOOLE-0V1) or g be  non emptyXBOOLE-0V1) implies NOT1GATE-1K1 {}XBOOLE-0K1 be setHIDDENM2) & ( not ( not ((((((a be  non emptyXBOOLE-0V1 or b be  non emptyXBOOLE-0V1) or c be  non emptyXBOOLE-0V1) or d be  non emptyXBOOLE-0V1) or e be  non emptyXBOOLE-0V1) or f be  non emptyXBOOLE-0V1) or g be  non emptyXBOOLE-0V1)) implies {}XBOOLE-0K1 be setHIDDENM2)"
       sorry
  (*consistency*)
    show " for it be setHIDDENM2 holds  True "
       sorry
qed "sorry"

mtheorem gate_1_th_35:
" for a be setHIDDENM2 holds  for b be setHIDDENM2 holds  for c be setHIDDENM2 holds  for d be setHIDDENM2 holds  for e be setHIDDENM2 holds  for f be setHIDDENM2 holds  for g be setHIDDENM2 holds NOR7GATE-1K29(a,b,c,d,e,f,g) be  non emptyXBOOLE-0V1 iff  not ((((((a be  non emptyXBOOLE-0V1 or b be  non emptyXBOOLE-0V1) or c be  non emptyXBOOLE-0V1) or d be  non emptyXBOOLE-0V1) or e be  non emptyXBOOLE-0V1) or f be  non emptyXBOOLE-0V1) or g be  non emptyXBOOLE-0V1)"
  using gate_1_def_29 sorry

mdef gate_1_def_30 ("AND8GATE-1K30'( _ , _ , _ , _ , _ , _ , _ , _ ')" [0,0,0,0,0,0,0,0]164 ) where
  mlet "a be setHIDDENM2", "b be setHIDDENM2", "c be setHIDDENM2", "d be setHIDDENM2", "e be setHIDDENM2", "f be setHIDDENM2", "g be setHIDDENM2", "h be setHIDDENM2"
"func AND8GATE-1K30(a,b,c,d,e,f,g,h) \<rightarrow> setHIDDENM2 equals
  NOT1GATE-1K1 {}XBOOLE-0K1 if ((((((a be  non emptyXBOOLE-0V1 & b be  non emptyXBOOLE-0V1) & c be  non emptyXBOOLE-0V1) & d be  non emptyXBOOLE-0V1) & e be  non emptyXBOOLE-0V1) & f be  non emptyXBOOLE-0V1) & g be  non emptyXBOOLE-0V1) & h be  non emptyXBOOLE-0V1 otherwise {}XBOOLE-0K1"
proof-
  (*coherence*)
    show "(((((((a be  non emptyXBOOLE-0V1 & b be  non emptyXBOOLE-0V1) & c be  non emptyXBOOLE-0V1) & d be  non emptyXBOOLE-0V1) & e be  non emptyXBOOLE-0V1) & f be  non emptyXBOOLE-0V1) & g be  non emptyXBOOLE-0V1) & h be  non emptyXBOOLE-0V1 implies NOT1GATE-1K1 {}XBOOLE-0K1 be setHIDDENM2) & ( not (((((((a be  non emptyXBOOLE-0V1 & b be  non emptyXBOOLE-0V1) & c be  non emptyXBOOLE-0V1) & d be  non emptyXBOOLE-0V1) & e be  non emptyXBOOLE-0V1) & f be  non emptyXBOOLE-0V1) & g be  non emptyXBOOLE-0V1) & h be  non emptyXBOOLE-0V1) implies {}XBOOLE-0K1 be setHIDDENM2)"
       sorry
  (*consistency*)
    show " for it be setHIDDENM2 holds  True "
       sorry
qed "sorry"

mtheorem gate_1_th_36:
" for a be setHIDDENM2 holds  for b be setHIDDENM2 holds  for c be setHIDDENM2 holds  for d be setHIDDENM2 holds  for e be setHIDDENM2 holds  for f be setHIDDENM2 holds  for g be setHIDDENM2 holds  for h be setHIDDENM2 holds AND8GATE-1K30(a,b,c,d,e,f,g,h) be  non emptyXBOOLE-0V1 iff ((((((a be  non emptyXBOOLE-0V1 & b be  non emptyXBOOLE-0V1) & c be  non emptyXBOOLE-0V1) & d be  non emptyXBOOLE-0V1) & e be  non emptyXBOOLE-0V1) & f be  non emptyXBOOLE-0V1) & g be  non emptyXBOOLE-0V1) & h be  non emptyXBOOLE-0V1"
  using gate_1_def_30 sorry

mdef gate_1_def_31 ("OR8GATE-1K31'( _ , _ , _ , _ , _ , _ , _ , _ ')" [0,0,0,0,0,0,0,0]164 ) where
  mlet "a be setHIDDENM2", "b be setHIDDENM2", "c be setHIDDENM2", "d be setHIDDENM2", "e be setHIDDENM2", "f be setHIDDENM2", "g be setHIDDENM2", "h be setHIDDENM2"
"func OR8GATE-1K31(a,b,c,d,e,f,g,h) \<rightarrow> setHIDDENM2 equals
  NOT1GATE-1K1 {}XBOOLE-0K1 if ((((((a be  non emptyXBOOLE-0V1 or b be  non emptyXBOOLE-0V1) or c be  non emptyXBOOLE-0V1) or d be  non emptyXBOOLE-0V1) or e be  non emptyXBOOLE-0V1) or f be  non emptyXBOOLE-0V1) or g be  non emptyXBOOLE-0V1) or h be  non emptyXBOOLE-0V1 otherwise {}XBOOLE-0K1"
proof-
  (*coherence*)
    show "(((((((a be  non emptyXBOOLE-0V1 or b be  non emptyXBOOLE-0V1) or c be  non emptyXBOOLE-0V1) or d be  non emptyXBOOLE-0V1) or e be  non emptyXBOOLE-0V1) or f be  non emptyXBOOLE-0V1) or g be  non emptyXBOOLE-0V1) or h be  non emptyXBOOLE-0V1 implies NOT1GATE-1K1 {}XBOOLE-0K1 be setHIDDENM2) & ( not (((((((a be  non emptyXBOOLE-0V1 or b be  non emptyXBOOLE-0V1) or c be  non emptyXBOOLE-0V1) or d be  non emptyXBOOLE-0V1) or e be  non emptyXBOOLE-0V1) or f be  non emptyXBOOLE-0V1) or g be  non emptyXBOOLE-0V1) or h be  non emptyXBOOLE-0V1) implies {}XBOOLE-0K1 be setHIDDENM2)"
       sorry
  (*consistency*)
    show " for it be setHIDDENM2 holds  True "
       sorry
qed "sorry"

mtheorem gate_1_th_37:
" for a be setHIDDENM2 holds  for b be setHIDDENM2 holds  for c be setHIDDENM2 holds  for d be setHIDDENM2 holds  for e be setHIDDENM2 holds  for f be setHIDDENM2 holds  for g be setHIDDENM2 holds  for h be setHIDDENM2 holds OR8GATE-1K31(a,b,c,d,e,f,g,h) be  non emptyXBOOLE-0V1 iff ((((((a be  non emptyXBOOLE-0V1 or b be  non emptyXBOOLE-0V1) or c be  non emptyXBOOLE-0V1) or d be  non emptyXBOOLE-0V1) or e be  non emptyXBOOLE-0V1) or f be  non emptyXBOOLE-0V1) or g be  non emptyXBOOLE-0V1) or h be  non emptyXBOOLE-0V1"
  using gate_1_def_31 sorry

mdef gate_1_def_32 ("NAND8GATE-1K32'( _ , _ , _ , _ , _ , _ , _ , _ ')" [0,0,0,0,0,0,0,0]164 ) where
  mlet "a be setHIDDENM2", "b be setHIDDENM2", "c be setHIDDENM2", "d be setHIDDENM2", "e be setHIDDENM2", "f be setHIDDENM2", "g be setHIDDENM2", "h be setHIDDENM2"
"func NAND8GATE-1K32(a,b,c,d,e,f,g,h) \<rightarrow> setHIDDENM2 equals
  NOT1GATE-1K1 {}XBOOLE-0K1 if  not (((((((a be  non emptyXBOOLE-0V1 & b be  non emptyXBOOLE-0V1) & c be  non emptyXBOOLE-0V1) & d be  non emptyXBOOLE-0V1) & e be  non emptyXBOOLE-0V1) & f be  non emptyXBOOLE-0V1) & g be  non emptyXBOOLE-0V1) & h be  non emptyXBOOLE-0V1) otherwise {}XBOOLE-0K1"
proof-
  (*coherence*)
    show "( not (((((((a be  non emptyXBOOLE-0V1 & b be  non emptyXBOOLE-0V1) & c be  non emptyXBOOLE-0V1) & d be  non emptyXBOOLE-0V1) & e be  non emptyXBOOLE-0V1) & f be  non emptyXBOOLE-0V1) & g be  non emptyXBOOLE-0V1) & h be  non emptyXBOOLE-0V1) implies NOT1GATE-1K1 {}XBOOLE-0K1 be setHIDDENM2) & ( not ( not (((((((a be  non emptyXBOOLE-0V1 & b be  non emptyXBOOLE-0V1) & c be  non emptyXBOOLE-0V1) & d be  non emptyXBOOLE-0V1) & e be  non emptyXBOOLE-0V1) & f be  non emptyXBOOLE-0V1) & g be  non emptyXBOOLE-0V1) & h be  non emptyXBOOLE-0V1)) implies {}XBOOLE-0K1 be setHIDDENM2)"
       sorry
  (*consistency*)
    show " for it be setHIDDENM2 holds  True "
       sorry
qed "sorry"

mtheorem gate_1_th_38:
" for a be setHIDDENM2 holds  for b be setHIDDENM2 holds  for c be setHIDDENM2 holds  for d be setHIDDENM2 holds  for e be setHIDDENM2 holds  for f be setHIDDENM2 holds  for g be setHIDDENM2 holds  for h be setHIDDENM2 holds NAND8GATE-1K32(a,b,c,d,e,f,g,h) be  non emptyXBOOLE-0V1 iff  not (((((((a be  non emptyXBOOLE-0V1 & b be  non emptyXBOOLE-0V1) & c be  non emptyXBOOLE-0V1) & d be  non emptyXBOOLE-0V1) & e be  non emptyXBOOLE-0V1) & f be  non emptyXBOOLE-0V1) & g be  non emptyXBOOLE-0V1) & h be  non emptyXBOOLE-0V1)"
  using gate_1_def_32 sorry

mdef gate_1_def_33 ("NOR8GATE-1K33'( _ , _ , _ , _ , _ , _ , _ , _ ')" [0,0,0,0,0,0,0,0]164 ) where
  mlet "a be setHIDDENM2", "b be setHIDDENM2", "c be setHIDDENM2", "d be setHIDDENM2", "e be setHIDDENM2", "f be setHIDDENM2", "g be setHIDDENM2", "h be setHIDDENM2"
"func NOR8GATE-1K33(a,b,c,d,e,f,g,h) \<rightarrow> setHIDDENM2 equals
  NOT1GATE-1K1 {}XBOOLE-0K1 if  not (((((((a be  non emptyXBOOLE-0V1 or b be  non emptyXBOOLE-0V1) or c be  non emptyXBOOLE-0V1) or d be  non emptyXBOOLE-0V1) or e be  non emptyXBOOLE-0V1) or f be  non emptyXBOOLE-0V1) or g be  non emptyXBOOLE-0V1) or h be  non emptyXBOOLE-0V1) otherwise {}XBOOLE-0K1"
proof-
  (*coherence*)
    show "( not (((((((a be  non emptyXBOOLE-0V1 or b be  non emptyXBOOLE-0V1) or c be  non emptyXBOOLE-0V1) or d be  non emptyXBOOLE-0V1) or e be  non emptyXBOOLE-0V1) or f be  non emptyXBOOLE-0V1) or g be  non emptyXBOOLE-0V1) or h be  non emptyXBOOLE-0V1) implies NOT1GATE-1K1 {}XBOOLE-0K1 be setHIDDENM2) & ( not ( not (((((((a be  non emptyXBOOLE-0V1 or b be  non emptyXBOOLE-0V1) or c be  non emptyXBOOLE-0V1) or d be  non emptyXBOOLE-0V1) or e be  non emptyXBOOLE-0V1) or f be  non emptyXBOOLE-0V1) or g be  non emptyXBOOLE-0V1) or h be  non emptyXBOOLE-0V1)) implies {}XBOOLE-0K1 be setHIDDENM2)"
       sorry
  (*consistency*)
    show " for it be setHIDDENM2 holds  True "
       sorry
qed "sorry"

mtheorem gate_1_th_39:
" for a be setHIDDENM2 holds  for b be setHIDDENM2 holds  for c be setHIDDENM2 holds  for d be setHIDDENM2 holds  for e be setHIDDENM2 holds  for f be setHIDDENM2 holds  for g be setHIDDENM2 holds  for h be setHIDDENM2 holds NOR8GATE-1K33(a,b,c,d,e,f,g,h) be  non emptyXBOOLE-0V1 iff  not (((((((a be  non emptyXBOOLE-0V1 or b be  non emptyXBOOLE-0V1) or c be  non emptyXBOOLE-0V1) or d be  non emptyXBOOLE-0V1) or e be  non emptyXBOOLE-0V1) or f be  non emptyXBOOLE-0V1) or g be  non emptyXBOOLE-0V1) or h be  non emptyXBOOLE-0V1)"
  using gate_1_def_33 sorry

(*begin*)
mtheorem gate_1_th_40:
" for c1 be setHIDDENM2 holds  for x1 be setHIDDENM2 holds  for x2 be setHIDDENM2 holds  for x3 be setHIDDENM2 holds  for x4 be setHIDDENM2 holds  for y1 be setHIDDENM2 holds  for y2 be setHIDDENM2 holds  for y3 be setHIDDENM2 holds  for y4 be setHIDDENM2 holds  for c2 be setHIDDENM2 holds  for c3 be setHIDDENM2 holds  for c4 be setHIDDENM2 holds  for c5 be setHIDDENM2 holds  for n1 be setHIDDENM2 holds  for n2 be setHIDDENM2 holds  for n3 be setHIDDENM2 holds  for n4 be setHIDDENM2 holds  for n be setHIDDENM2 holds  for c5b be setHIDDENM2 holds (((((((((MAJ3GATE-1K11(x1,y1,c1) be  non emptyXBOOLE-0V1 implies c2 be  non emptyXBOOLE-0V1) & (MAJ3GATE-1K11(x2,y2,c2) be  non emptyXBOOLE-0V1 implies c3 be  non emptyXBOOLE-0V1)) & (MAJ3GATE-1K11(x3,y3,c3) be  non emptyXBOOLE-0V1 implies c4 be  non emptyXBOOLE-0V1)) & (MAJ3GATE-1K11(x4,y4,c4) be  non emptyXBOOLE-0V1 implies c5 be  non emptyXBOOLE-0V1)) & (n1 be  non emptyXBOOLE-0V1 implies OR2GATE-1K3(x1,y1) be  non emptyXBOOLE-0V1)) & (n2 be  non emptyXBOOLE-0V1 implies OR2GATE-1K3(x2,y2) be  non emptyXBOOLE-0V1)) & (n3 be  non emptyXBOOLE-0V1 implies OR2GATE-1K3(x3,y3) be  non emptyXBOOLE-0V1)) & (n4 be  non emptyXBOOLE-0V1 implies OR2GATE-1K3(x4,y4) be  non emptyXBOOLE-0V1)) & (n be  non emptyXBOOLE-0V1 implies AND5GATE-1K18(c1,n1,n2,n3,n4) be  non emptyXBOOLE-0V1)) & (c5b be  non emptyXBOOLE-0V1 iff OR2GATE-1K3(c5,n) be  non emptyXBOOLE-0V1) implies (c5 be  non emptyXBOOLE-0V1 iff c5b be  non emptyXBOOLE-0V1)"
sorry

mdef gate_1_def_34 ("MODADD2GATE-1K34'( _ , _ ')" [0,0]164 ) where
  mlet "a be setHIDDENM2", "b be setHIDDENM2"
"func MODADD2GATE-1K34(a,b) \<rightarrow> setHIDDENM2 equals
  NOT1GATE-1K1 {}XBOOLE-0K1 if (a be  non emptyXBOOLE-0V1 or b be  non emptyXBOOLE-0V1) &  not (a be  non emptyXBOOLE-0V1 & b be  non emptyXBOOLE-0V1) otherwise {}XBOOLE-0K1"
proof-
  (*coherence*)
    show "((a be  non emptyXBOOLE-0V1 or b be  non emptyXBOOLE-0V1) &  not (a be  non emptyXBOOLE-0V1 & b be  non emptyXBOOLE-0V1) implies NOT1GATE-1K1 {}XBOOLE-0K1 be setHIDDENM2) & ( not ((a be  non emptyXBOOLE-0V1 or b be  non emptyXBOOLE-0V1) &  not (a be  non emptyXBOOLE-0V1 & b be  non emptyXBOOLE-0V1)) implies {}XBOOLE-0K1 be setHIDDENM2)"
       sorry
  (*consistency*)
    show " for it be setHIDDENM2 holds  True "
       sorry
qed "sorry"

mtheorem GATE_1K34_commutativity:
" for a be setHIDDENM2 holds  for b be setHIDDENM2 holds MODADD2GATE-1K34(a,b) =HIDDENR1 MODADD2GATE-1K34(b,a)"
sorry

mtheorem gate_1_th_41:
" for a be setHIDDENM2 holds  for b be setHIDDENM2 holds MODADD2GATE-1K34(a,b) be  non emptyXBOOLE-0V1 iff (a be  non emptyXBOOLE-0V1 or b be  non emptyXBOOLE-0V1) &  not (a be  non emptyXBOOLE-0V1 & b be  non emptyXBOOLE-0V1)"
  using gate_1_def_34 sorry

abbreviation(input) GATE_1K35("ADD1GATE-1K35'( _ , _ , _ ')" [0,0,0]164) where
  "ADD1GATE-1K35(a,b,c) \<equiv> XOR3GATE-1K10(a,b,c)"

abbreviation(input) GATE_1K36("CARR1GATE-1K36'( _ , _ , _ ')" [0,0,0]164) where
  "CARR1GATE-1K36(a,b,c) \<equiv> MAJ3GATE-1K11(a,b,c)"

mdef gate_1_def_35 ("ADD2GATE-1K37'( _ , _ , _ , _ , _ ')" [0,0,0,0,0]164 ) where
  mlet "a1 be setHIDDENM2", "b1 be setHIDDENM2", "a2 be setHIDDENM2", "b2 be setHIDDENM2", "c be setHIDDENM2"
"func ADD2GATE-1K37(a2,b2,a1,b1,c) \<rightarrow> setHIDDENM2 equals
  XOR3GATE-1K10(a2,b2,CARR1GATE-1K36(a1,b1,c))"
proof-
  (*coherence*)
    show "XOR3GATE-1K10(a2,b2,CARR1GATE-1K36(a1,b1,c)) be setHIDDENM2"
       sorry
qed "sorry"

mdef gate_1_def_36 ("CARR2GATE-1K38'( _ , _ , _ , _ , _ ')" [0,0,0,0,0]164 ) where
  mlet "a1 be setHIDDENM2", "b1 be setHIDDENM2", "a2 be setHIDDENM2", "b2 be setHIDDENM2", "c be setHIDDENM2"
"func CARR2GATE-1K38(a2,b2,a1,b1,c) \<rightarrow> setHIDDENM2 equals
  MAJ3GATE-1K11(a2,b2,CARR1GATE-1K36(a1,b1,c))"
proof-
  (*coherence*)
    show "MAJ3GATE-1K11(a2,b2,CARR1GATE-1K36(a1,b1,c)) be setHIDDENM2"
       sorry
qed "sorry"

mdef gate_1_def_37 ("ADD3GATE-1K39'( _ , _ , _ , _ , _ , _ , _ ')" [0,0,0,0,0,0,0]164 ) where
  mlet "a1 be setHIDDENM2", "b1 be setHIDDENM2", "a2 be setHIDDENM2", "b2 be setHIDDENM2", "a3 be setHIDDENM2", "b3 be setHIDDENM2", "c be setHIDDENM2"
"func ADD3GATE-1K39(a3,b3,a2,b2,a1,b1,c) \<rightarrow> setHIDDENM2 equals
  XOR3GATE-1K10(a3,b3,CARR2GATE-1K38(a2,b2,a1,b1,c))"
proof-
  (*coherence*)
    show "XOR3GATE-1K10(a3,b3,CARR2GATE-1K38(a2,b2,a1,b1,c)) be setHIDDENM2"
       sorry
qed "sorry"

mdef gate_1_def_38 ("CARR3GATE-1K40'( _ , _ , _ , _ , _ , _ , _ ')" [0,0,0,0,0,0,0]164 ) where
  mlet "a1 be setHIDDENM2", "b1 be setHIDDENM2", "a2 be setHIDDENM2", "b2 be setHIDDENM2", "a3 be setHIDDENM2", "b3 be setHIDDENM2", "c be setHIDDENM2"
"func CARR3GATE-1K40(a3,b3,a2,b2,a1,b1,c) \<rightarrow> setHIDDENM2 equals
  MAJ3GATE-1K11(a3,b3,CARR2GATE-1K38(a2,b2,a1,b1,c))"
proof-
  (*coherence*)
    show "MAJ3GATE-1K11(a3,b3,CARR2GATE-1K38(a2,b2,a1,b1,c)) be setHIDDENM2"
       sorry
qed "sorry"

mdef gate_1_def_39 ("ADD4GATE-1K41'( _ , _ , _ , _ , _ , _ , _ , _ , _ ')" [0,0,0,0,0,0,0,0,0]164 ) where
  mlet "a1 be setHIDDENM2", "b1 be setHIDDENM2", "a2 be setHIDDENM2", "b2 be setHIDDENM2", "a3 be setHIDDENM2", "b3 be setHIDDENM2", "a4 be setHIDDENM2", "b4 be setHIDDENM2", "c be setHIDDENM2"
"func ADD4GATE-1K41(a4,b4,a3,b3,a2,b2,a1,b1,c) \<rightarrow> setHIDDENM2 equals
  XOR3GATE-1K10(a4,b4,CARR3GATE-1K40(a3,b3,a2,b2,a1,b1,c))"
proof-
  (*coherence*)
    show "XOR3GATE-1K10(a4,b4,CARR3GATE-1K40(a3,b3,a2,b2,a1,b1,c)) be setHIDDENM2"
       sorry
qed "sorry"

mdef gate_1_def_40 ("CARR4GATE-1K42'( _ , _ , _ , _ , _ , _ , _ , _ , _ ')" [0,0,0,0,0,0,0,0,0]164 ) where
  mlet "a1 be setHIDDENM2", "b1 be setHIDDENM2", "a2 be setHIDDENM2", "b2 be setHIDDENM2", "a3 be setHIDDENM2", "b3 be setHIDDENM2", "a4 be setHIDDENM2", "b4 be setHIDDENM2", "c be setHIDDENM2"
"func CARR4GATE-1K42(a4,b4,a3,b3,a2,b2,a1,b1,c) \<rightarrow> setHIDDENM2 equals
  MAJ3GATE-1K11(a4,b4,CARR3GATE-1K40(a3,b3,a2,b2,a1,b1,c))"
proof-
  (*coherence*)
    show "MAJ3GATE-1K11(a4,b4,CARR3GATE-1K40(a3,b3,a2,b2,a1,b1,c)) be setHIDDENM2"
       sorry
qed "sorry"

mtheorem gate_1_th_42:
" for c1 be setHIDDENM2 holds  for x1 be setHIDDENM2 holds  for y1 be setHIDDENM2 holds  for x2 be setHIDDENM2 holds  for y2 be setHIDDENM2 holds  for x3 be setHIDDENM2 holds  for y3 be setHIDDENM2 holds  for x4 be setHIDDENM2 holds  for y4 be setHIDDENM2 holds  for c4 be setHIDDENM2 holds  for q1 be setHIDDENM2 holds  for p1 be setHIDDENM2 holds  for sd1 be setHIDDENM2 holds  for q2 be setHIDDENM2 holds  for p2 be setHIDDENM2 holds  for sd2 be setHIDDENM2 holds  for q3 be setHIDDENM2 holds  for p3 be setHIDDENM2 holds  for sd3 be setHIDDENM2 holds  for q4 be setHIDDENM2 holds  for p4 be setHIDDENM2 holds  for sd4 be setHIDDENM2 holds  for cb1 be setHIDDENM2 holds  for cb2 be setHIDDENM2 holds  for l2 be setHIDDENM2 holds  for t2 be setHIDDENM2 holds  for l3 be setHIDDENM2 holds  for m3 be setHIDDENM2 holds  for t3 be setHIDDENM2 holds  for l4 be setHIDDENM2 holds  for m4 be setHIDDENM2 holds  for n4 be setHIDDENM2 holds  for t4 be setHIDDENM2 holds  for l5 be setHIDDENM2 holds  for m5 be setHIDDENM2 holds  for n5 be setHIDDENM2 holds  for o5 be setHIDDENM2 holds  for s1 be setHIDDENM2 holds  for s2 be setHIDDENM2 holds  for s3 be setHIDDENM2 holds  for s4 be setHIDDENM2 holds (((((((((((((((((((((((((((((((q1 be  non emptyXBOOLE-0V1 iff NOR2GATE-1K7(x1,y1) be  non emptyXBOOLE-0V1) & (p1 be  non emptyXBOOLE-0V1 iff NAND2GATE-1K6(x1,y1) be  non emptyXBOOLE-0V1)) & (sd1 be  non emptyXBOOLE-0V1 iff MODADD2GATE-1K34(x1,y1) be  non emptyXBOOLE-0V1)) & (q2 be  non emptyXBOOLE-0V1 iff NOR2GATE-1K7(x2,y2) be  non emptyXBOOLE-0V1)) & (p2 be  non emptyXBOOLE-0V1 iff NAND2GATE-1K6(x2,y2) be  non emptyXBOOLE-0V1)) & (sd2 be  non emptyXBOOLE-0V1 iff MODADD2GATE-1K34(x2,y2) be  non emptyXBOOLE-0V1)) & (q3 be  non emptyXBOOLE-0V1 iff NOR2GATE-1K7(x3,y3) be  non emptyXBOOLE-0V1)) & (p3 be  non emptyXBOOLE-0V1 iff NAND2GATE-1K6(x3,y3) be  non emptyXBOOLE-0V1)) & (sd3 be  non emptyXBOOLE-0V1 iff MODADD2GATE-1K34(x3,y3) be  non emptyXBOOLE-0V1)) & (q4 be  non emptyXBOOLE-0V1 iff NOR2GATE-1K7(x4,y4) be  non emptyXBOOLE-0V1)) & (p4 be  non emptyXBOOLE-0V1 iff NAND2GATE-1K6(x4,y4) be  non emptyXBOOLE-0V1)) & (sd4 be  non emptyXBOOLE-0V1 iff MODADD2GATE-1K34(x4,y4) be  non emptyXBOOLE-0V1)) & (cb1 be  non emptyXBOOLE-0V1 iff NOT1GATE-1K1 c1 be  non emptyXBOOLE-0V1)) & (cb2 be  non emptyXBOOLE-0V1 iff NOT1GATE-1K1 cb1 be  non emptyXBOOLE-0V1)) & (s1 be  non emptyXBOOLE-0V1 iff XOR2GATE-1K4(cb2,sd1) be  non emptyXBOOLE-0V1)) & (l2 be  non emptyXBOOLE-0V1 iff AND2GATE-1K2(cb1,p1) be  non emptyXBOOLE-0V1)) & (t2 be  non emptyXBOOLE-0V1 iff NOR2GATE-1K7(l2,q1) be  non emptyXBOOLE-0V1)) & (s2 be  non emptyXBOOLE-0V1 iff XOR2GATE-1K4(t2,sd2) be  non emptyXBOOLE-0V1)) & (l3 be  non emptyXBOOLE-0V1 iff AND2GATE-1K2(q1,p2) be  non emptyXBOOLE-0V1)) & (m3 be  non emptyXBOOLE-0V1 iff AND3GATE-1K8(p2,p1,cb1) be  non emptyXBOOLE-0V1)) & (t3 be  non emptyXBOOLE-0V1 iff NOR3GATE-1K13(l3,m3,q2) be  non emptyXBOOLE-0V1)) & (s3 be  non emptyXBOOLE-0V1 iff XOR2GATE-1K4(t3,sd3) be  non emptyXBOOLE-0V1)) & (l4 be  non emptyXBOOLE-0V1 iff AND2GATE-1K2(q2,p3) be  non emptyXBOOLE-0V1)) & (m4 be  non emptyXBOOLE-0V1 iff AND3GATE-1K8(q1,p3,p2) be  non emptyXBOOLE-0V1)) & (n4 be  non emptyXBOOLE-0V1 iff AND4GATE-1K14(p3,p2,p1,cb1) be  non emptyXBOOLE-0V1)) & (t4 be  non emptyXBOOLE-0V1 iff NOR4GATE-1K17(l4,m4,n4,q3) be  non emptyXBOOLE-0V1)) & (s4 be  non emptyXBOOLE-0V1 iff XOR2GATE-1K4(t4,sd4) be  non emptyXBOOLE-0V1)) & (l5 be  non emptyXBOOLE-0V1 iff AND2GATE-1K2(q3,p4) be  non emptyXBOOLE-0V1)) & (m5 be  non emptyXBOOLE-0V1 iff AND3GATE-1K8(q2,p4,p3) be  non emptyXBOOLE-0V1)) & (n5 be  non emptyXBOOLE-0V1 iff AND4GATE-1K14(q1,p4,p3,p2) be  non emptyXBOOLE-0V1)) & (o5 be  non emptyXBOOLE-0V1 iff AND5GATE-1K18(p4,p3,p2,p1,cb1) be  non emptyXBOOLE-0V1)) & (c4 be  non emptyXBOOLE-0V1 iff NOR5GATE-1K21(q4,l5,m5,n5,o5) be  non emptyXBOOLE-0V1) implies ((((s1 be  non emptyXBOOLE-0V1 iff ADD1GATE-1K35(x1,y1,c1) be  non emptyXBOOLE-0V1) & (s2 be  non emptyXBOOLE-0V1 iff ADD2GATE-1K37(x2,y2,x1,y1,c1) be  non emptyXBOOLE-0V1)) & (s3 be  non emptyXBOOLE-0V1 iff ADD3GATE-1K39(x3,y3,x2,y2,x1,y1,c1) be  non emptyXBOOLE-0V1)) & (s4 be  non emptyXBOOLE-0V1 iff ADD4GATE-1K41(x4,y4,x3,y3,x2,y2,x1,y1,c1) be  non emptyXBOOLE-0V1)) & (c4 be  non emptyXBOOLE-0V1 iff CARR4GATE-1K42(x4,y4,x3,y3,x2,y2,x1,y1,c1) be  non emptyXBOOLE-0V1)"
sorry

end
