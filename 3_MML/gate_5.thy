theory gate_5
  imports gate_1
begin
(*begin*)
mdef gate_5_def_1 ("MULT210GATE-5K1'( _ , _ , _ , _ ')" [0,0,0,0]164 ) where
  mlet "x0 be setHIDDENM2", "x1 be setHIDDENM2", "y0 be setHIDDENM2", "y1 be setHIDDENM2"
"func MULT210GATE-5K1(x1,y1,x0,y0) \<rightarrow> setHIDDENM2 equals
  AND2GATE-1K2(x0,y0)"
proof-
  (*coherence*)
    show "AND2GATE-1K2(x0,y0) be setHIDDENM2"
       sorry
qed "sorry"

mdef gate_5_def_2 ("MULT211GATE-5K2'( _ , _ , _ , _ ')" [0,0,0,0]164 ) where
  mlet "x0 be setHIDDENM2", "x1 be setHIDDENM2", "y0 be setHIDDENM2", "y1 be setHIDDENM2"
"func MULT211GATE-5K2(x1,y1,x0,y0) \<rightarrow> setHIDDENM2 equals
  ADD1GATE-1K35(AND2GATE-1K2(x1,y0),AND2GATE-1K2(x0,y1),{}XBOOLE-0K1)"
proof-
  (*coherence*)
    show "ADD1GATE-1K35(AND2GATE-1K2(x1,y0),AND2GATE-1K2(x0,y1),{}XBOOLE-0K1) be setHIDDENM2"
       sorry
qed "sorry"

mdef gate_5_def_3 ("MULT212GATE-5K3'( _ , _ , _ , _ ')" [0,0,0,0]164 ) where
  mlet "x0 be setHIDDENM2", "x1 be setHIDDENM2", "y0 be setHIDDENM2", "y1 be setHIDDENM2"
"func MULT212GATE-5K3(x1,y1,x0,y0) \<rightarrow> setHIDDENM2 equals
  ADD2GATE-1K37({}XBOOLE-0K1,AND2GATE-1K2(x1,y1),AND2GATE-1K2(x1,y0),AND2GATE-1K2(x0,y1),{}XBOOLE-0K1)"
proof-
  (*coherence*)
    show "ADD2GATE-1K37({}XBOOLE-0K1,AND2GATE-1K2(x1,y1),AND2GATE-1K2(x1,y0),AND2GATE-1K2(x0,y1),{}XBOOLE-0K1) be setHIDDENM2"
       sorry
qed "sorry"

mdef gate_5_def_4 ("MULT213GATE-5K4'( _ , _ , _ , _ ')" [0,0,0,0]164 ) where
  mlet "x0 be setHIDDENM2", "x1 be setHIDDENM2", "y0 be setHIDDENM2", "y1 be setHIDDENM2"
"func MULT213GATE-5K4(x1,y1,x0,y0) \<rightarrow> setHIDDENM2 equals
  CARR2GATE-1K38({}XBOOLE-0K1,AND2GATE-1K2(x1,y1),AND2GATE-1K2(x1,y0),AND2GATE-1K2(x0,y1),{}XBOOLE-0K1)"
proof-
  (*coherence*)
    show "CARR2GATE-1K38({}XBOOLE-0K1,AND2GATE-1K2(x1,y1),AND2GATE-1K2(x1,y0),AND2GATE-1K2(x0,y1),{}XBOOLE-0K1) be setHIDDENM2"
       sorry
qed "sorry"

mtheorem gate_5_th_1:
" for x0 be setHIDDENM2 holds  for x1 be setHIDDENM2 holds  for y0 be setHIDDENM2 holds  for y1 be setHIDDENM2 holds  for z0 be setHIDDENM2 holds  for z1 be setHIDDENM2 holds  for z2 be setHIDDENM2 holds  for z3 be setHIDDENM2 holds  for q00 be setHIDDENM2 holds  for q01 be setHIDDENM2 holds  for c01 be setHIDDENM2 holds  for q11 be setHIDDENM2 holds  for c11 be setHIDDENM2 holds (((((((( not q00 be emptyXBOOLE-0V1 iff  not AND2GATE-1K2(x0,y0) be emptyXBOOLE-0V1) & ( not q01 be emptyXBOOLE-0V1 iff  not XOR3GATE-1K10(AND2GATE-1K2(x1,y0),AND2GATE-1K2(x0,y1),{}XBOOLE-0K1) be emptyXBOOLE-0V1)) & ( not c01 be emptyXBOOLE-0V1 iff  not MAJ3GATE-1K11(AND2GATE-1K2(x1,y0),AND2GATE-1K2(x0,y1),{}XBOOLE-0K1) be emptyXBOOLE-0V1)) & ( not q11 be emptyXBOOLE-0V1 iff  not XOR3GATE-1K10(AND2GATE-1K2(x1,y1),{}XBOOLE-0K1,c01) be emptyXBOOLE-0V1)) & ( not c11 be emptyXBOOLE-0V1 iff  not MAJ3GATE-1K11(AND2GATE-1K2(x1,y1),{}XBOOLE-0K1,c01) be emptyXBOOLE-0V1)) & ( not z0 be emptyXBOOLE-0V1 iff  not q00 be emptyXBOOLE-0V1)) & ( not z1 be emptyXBOOLE-0V1 iff  not q01 be emptyXBOOLE-0V1)) & ( not z2 be emptyXBOOLE-0V1 iff  not q11 be emptyXBOOLE-0V1)) & ( not z3 be emptyXBOOLE-0V1 iff  not c11 be emptyXBOOLE-0V1) implies ((( not z0 be emptyXBOOLE-0V1 iff  not MULT210GATE-5K1(x1,y1,x0,y0) be emptyXBOOLE-0V1) & ( not z1 be emptyXBOOLE-0V1 iff  not MULT211GATE-5K2(x1,y1,x0,y0) be emptyXBOOLE-0V1)) & ( not z2 be emptyXBOOLE-0V1 iff  not MULT212GATE-5K3(x1,y1,x0,y0) be emptyXBOOLE-0V1)) & ( not z3 be emptyXBOOLE-0V1 iff  not MULT213GATE-5K4(x1,y1,x0,y0) be emptyXBOOLE-0V1)"
sorry

mdef gate_5_def_5 ("MULT310GATE-5K5'( _ , _ , _ , _ , _ ')" [0,0,0,0,0]164 ) where
  mlet "x0 be setHIDDENM2", "x1 be setHIDDENM2", "x2 be setHIDDENM2", "y0 be setHIDDENM2", "y1 be setHIDDENM2"
"func MULT310GATE-5K5(x2,x1,y1,x0,y0) \<rightarrow> setHIDDENM2 equals
  AND2GATE-1K2(x0,y0)"
proof-
  (*coherence*)
    show "AND2GATE-1K2(x0,y0) be setHIDDENM2"
       sorry
qed "sorry"

mdef gate_5_def_6 ("MULT311GATE-5K6'( _ , _ , _ , _ , _ ')" [0,0,0,0,0]164 ) where
  mlet "x0 be setHIDDENM2", "x1 be setHIDDENM2", "x2 be setHIDDENM2", "y0 be setHIDDENM2", "y1 be setHIDDENM2"
"func MULT311GATE-5K6(x2,x1,y1,x0,y0) \<rightarrow> setHIDDENM2 equals
  ADD1GATE-1K35(AND2GATE-1K2(x1,y0),AND2GATE-1K2(x0,y1),{}XBOOLE-0K1)"
proof-
  (*coherence*)
    show "ADD1GATE-1K35(AND2GATE-1K2(x1,y0),AND2GATE-1K2(x0,y1),{}XBOOLE-0K1) be setHIDDENM2"
       sorry
qed "sorry"

mdef gate_5_def_7 ("MULT312GATE-5K7'( _ , _ , _ , _ , _ ')" [0,0,0,0,0]164 ) where
  mlet "x0 be setHIDDENM2", "x1 be setHIDDENM2", "x2 be setHIDDENM2", "y0 be setHIDDENM2", "y1 be setHIDDENM2"
"func MULT312GATE-5K7(x2,x1,y1,x0,y0) \<rightarrow> setHIDDENM2 equals
  ADD2GATE-1K37(AND2GATE-1K2(x2,y0),AND2GATE-1K2(x1,y1),AND2GATE-1K2(x1,y0),AND2GATE-1K2(x0,y1),{}XBOOLE-0K1)"
proof-
  (*coherence*)
    show "ADD2GATE-1K37(AND2GATE-1K2(x2,y0),AND2GATE-1K2(x1,y1),AND2GATE-1K2(x1,y0),AND2GATE-1K2(x0,y1),{}XBOOLE-0K1) be setHIDDENM2"
       sorry
qed "sorry"

mdef gate_5_def_8 ("MULT313GATE-5K8'( _ , _ , _ , _ , _ ')" [0,0,0,0,0]164 ) where
  mlet "x0 be setHIDDENM2", "x1 be setHIDDENM2", "x2 be setHIDDENM2", "y0 be setHIDDENM2", "y1 be setHIDDENM2"
"func MULT313GATE-5K8(x2,x1,y1,x0,y0) \<rightarrow> setHIDDENM2 equals
  ADD3GATE-1K39({}XBOOLE-0K1,AND2GATE-1K2(x2,y1),AND2GATE-1K2(x2,y0),AND2GATE-1K2(x1,y1),AND2GATE-1K2(x1,y0),AND2GATE-1K2(x0,y1),{}XBOOLE-0K1)"
proof-
  (*coherence*)
    show "ADD3GATE-1K39({}XBOOLE-0K1,AND2GATE-1K2(x2,y1),AND2GATE-1K2(x2,y0),AND2GATE-1K2(x1,y1),AND2GATE-1K2(x1,y0),AND2GATE-1K2(x0,y1),{}XBOOLE-0K1) be setHIDDENM2"
       sorry
qed "sorry"

mdef gate_5_def_9 ("MULT314GATE-5K9'( _ , _ , _ , _ , _ ')" [0,0,0,0,0]164 ) where
  mlet "x0 be setHIDDENM2", "x1 be setHIDDENM2", "x2 be setHIDDENM2", "y0 be setHIDDENM2", "y1 be setHIDDENM2"
"func MULT314GATE-5K9(x2,x1,y1,x0,y0) \<rightarrow> setHIDDENM2 equals
  CARR3GATE-1K40({}XBOOLE-0K1,AND2GATE-1K2(x2,y1),AND2GATE-1K2(x2,y0),AND2GATE-1K2(x1,y1),AND2GATE-1K2(x1,y0),AND2GATE-1K2(x0,y1),{}XBOOLE-0K1)"
proof-
  (*coherence*)
    show "CARR3GATE-1K40({}XBOOLE-0K1,AND2GATE-1K2(x2,y1),AND2GATE-1K2(x2,y0),AND2GATE-1K2(x1,y1),AND2GATE-1K2(x1,y0),AND2GATE-1K2(x0,y1),{}XBOOLE-0K1) be setHIDDENM2"
       sorry
qed "sorry"

mdef gate_5_def_10 ("MULT321GATE-5K10'( _ , _ , _ , _ , _ , _ ')" [0,0,0,0,0,0]164 ) where
  mlet "x0 be setHIDDENM2", "x1 be setHIDDENM2", "x2 be setHIDDENM2", "y0 be setHIDDENM2", "y1 be setHIDDENM2", "y2 be setHIDDENM2"
"func MULT321GATE-5K10(x2,y2,x1,y1,x0,y0) \<rightarrow> setHIDDENM2 equals
  ADD1GATE-1K35(MULT312GATE-5K7(x2,x1,y1,x0,y0),AND2GATE-1K2(x0,y2),{}XBOOLE-0K1)"
proof-
  (*coherence*)
    show "ADD1GATE-1K35(MULT312GATE-5K7(x2,x1,y1,x0,y0),AND2GATE-1K2(x0,y2),{}XBOOLE-0K1) be setHIDDENM2"
       sorry
qed "sorry"

mdef gate_5_def_11 ("MULT322GATE-5K11'( _ , _ , _ , _ , _ , _ ')" [0,0,0,0,0,0]164 ) where
  mlet "x0 be setHIDDENM2", "x1 be setHIDDENM2", "x2 be setHIDDENM2", "y0 be setHIDDENM2", "y1 be setHIDDENM2", "y2 be setHIDDENM2"
"func MULT322GATE-5K11(x2,y2,x1,y1,x0,y0) \<rightarrow> setHIDDENM2 equals
  ADD2GATE-1K37(MULT313GATE-5K8(x2,x1,y1,x0,y0),AND2GATE-1K2(x1,y2),MULT312GATE-5K7(x2,x1,y1,x0,y0),AND2GATE-1K2(x0,y2),{}XBOOLE-0K1)"
proof-
  (*coherence*)
    show "ADD2GATE-1K37(MULT313GATE-5K8(x2,x1,y1,x0,y0),AND2GATE-1K2(x1,y2),MULT312GATE-5K7(x2,x1,y1,x0,y0),AND2GATE-1K2(x0,y2),{}XBOOLE-0K1) be setHIDDENM2"
       sorry
qed "sorry"

mdef gate_5_def_12 ("MULT323GATE-5K12'( _ , _ , _ , _ , _ , _ ')" [0,0,0,0,0,0]164 ) where
  mlet "x0 be setHIDDENM2", "x1 be setHIDDENM2", "x2 be setHIDDENM2", "y0 be setHIDDENM2", "y1 be setHIDDENM2", "y2 be setHIDDENM2"
"func MULT323GATE-5K12(x2,y2,x1,y1,x0,y0) \<rightarrow> setHIDDENM2 equals
  ADD3GATE-1K39(MULT314GATE-5K9(x2,x1,y1,x0,y0),AND2GATE-1K2(x2,y2),MULT313GATE-5K8(x2,x1,y1,x0,y0),AND2GATE-1K2(x1,y2),MULT312GATE-5K7(x2,x1,y1,x0,y0),AND2GATE-1K2(x0,y2),{}XBOOLE-0K1)"
proof-
  (*coherence*)
    show "ADD3GATE-1K39(MULT314GATE-5K9(x2,x1,y1,x0,y0),AND2GATE-1K2(x2,y2),MULT313GATE-5K8(x2,x1,y1,x0,y0),AND2GATE-1K2(x1,y2),MULT312GATE-5K7(x2,x1,y1,x0,y0),AND2GATE-1K2(x0,y2),{}XBOOLE-0K1) be setHIDDENM2"
       sorry
qed "sorry"

mdef gate_5_def_13 ("MULT324GATE-5K13'( _ , _ , _ , _ , _ , _ ')" [0,0,0,0,0,0]164 ) where
  mlet "x0 be setHIDDENM2", "x1 be setHIDDENM2", "x2 be setHIDDENM2", "y0 be setHIDDENM2", "y1 be setHIDDENM2", "y2 be setHIDDENM2"
"func MULT324GATE-5K13(x2,y2,x1,y1,x0,y0) \<rightarrow> setHIDDENM2 equals
  CARR3GATE-1K40(MULT314GATE-5K9(x2,x1,y1,x0,y0),AND2GATE-1K2(x2,y2),MULT313GATE-5K8(x2,x1,y1,x0,y0),AND2GATE-1K2(x1,y2),MULT312GATE-5K7(x2,x1,y1,x0,y0),AND2GATE-1K2(x0,y2),{}XBOOLE-0K1)"
proof-
  (*coherence*)
    show "CARR3GATE-1K40(MULT314GATE-5K9(x2,x1,y1,x0,y0),AND2GATE-1K2(x2,y2),MULT313GATE-5K8(x2,x1,y1,x0,y0),AND2GATE-1K2(x1,y2),MULT312GATE-5K7(x2,x1,y1,x0,y0),AND2GATE-1K2(x0,y2),{}XBOOLE-0K1) be setHIDDENM2"
       sorry
qed "sorry"

mtheorem gate_5_th_2:
" for x0 be setHIDDENM2 holds  for x1 be setHIDDENM2 holds  for x2 be setHIDDENM2 holds  for y0 be setHIDDENM2 holds  for y1 be setHIDDENM2 holds  for y2 be setHIDDENM2 holds  for z0 be setHIDDENM2 holds  for z1 be setHIDDENM2 holds  for z2 be setHIDDENM2 holds  for z3 be setHIDDENM2 holds  for z4 be setHIDDENM2 holds  for z5 be setHIDDENM2 holds  for q00 be setHIDDENM2 holds  for q01 be setHIDDENM2 holds  for q02 be setHIDDENM2 holds  for c01 be setHIDDENM2 holds  for c02 be setHIDDENM2 holds  for q11 be setHIDDENM2 holds  for q12 be setHIDDENM2 holds  for c11 be setHIDDENM2 holds  for c12 be setHIDDENM2 holds  for q21 be setHIDDENM2 holds  for q22 be setHIDDENM2 holds  for c21 be setHIDDENM2 holds  for c22 be setHIDDENM2 holds (((((((((((((((((( not q00 be emptyXBOOLE-0V1 iff  not AND2GATE-1K2(x0,y0) be emptyXBOOLE-0V1) & ( not q01 be emptyXBOOLE-0V1 iff  not XOR3GATE-1K10(AND2GATE-1K2(x1,y0),AND2GATE-1K2(x0,y1),{}XBOOLE-0K1) be emptyXBOOLE-0V1)) & ( not c01 be emptyXBOOLE-0V1 iff  not MAJ3GATE-1K11(AND2GATE-1K2(x1,y0),AND2GATE-1K2(x0,y1),{}XBOOLE-0K1) be emptyXBOOLE-0V1)) & ( not q02 be emptyXBOOLE-0V1 iff  not XOR3GATE-1K10(AND2GATE-1K2(x2,y0),AND2GATE-1K2(x1,y1),{}XBOOLE-0K1) be emptyXBOOLE-0V1)) & ( not c02 be emptyXBOOLE-0V1 iff  not MAJ3GATE-1K11(AND2GATE-1K2(x2,y0),AND2GATE-1K2(x1,y1),{}XBOOLE-0K1) be emptyXBOOLE-0V1)) & ( not q11 be emptyXBOOLE-0V1 iff  not XOR3GATE-1K10(q02,AND2GATE-1K2(x0,y2),c01) be emptyXBOOLE-0V1)) & ( not c11 be emptyXBOOLE-0V1 iff  not MAJ3GATE-1K11(q02,AND2GATE-1K2(x0,y2),c01) be emptyXBOOLE-0V1)) & ( not q12 be emptyXBOOLE-0V1 iff  not XOR3GATE-1K10(AND2GATE-1K2(x2,y1),AND2GATE-1K2(x1,y2),c02) be emptyXBOOLE-0V1)) & ( not c12 be emptyXBOOLE-0V1 iff  not MAJ3GATE-1K11(AND2GATE-1K2(x2,y1),AND2GATE-1K2(x1,y2),c02) be emptyXBOOLE-0V1)) & ( not q21 be emptyXBOOLE-0V1 iff  not XOR3GATE-1K10(q12,{}XBOOLE-0K1,c11) be emptyXBOOLE-0V1)) & ( not c21 be emptyXBOOLE-0V1 iff  not MAJ3GATE-1K11(q12,{}XBOOLE-0K1,c11) be emptyXBOOLE-0V1)) & ( not q22 be emptyXBOOLE-0V1 iff  not XOR3GATE-1K10(AND2GATE-1K2(x2,y2),c21,c12) be emptyXBOOLE-0V1)) & ( not c22 be emptyXBOOLE-0V1 iff  not MAJ3GATE-1K11(AND2GATE-1K2(x2,y2),c21,c12) be emptyXBOOLE-0V1)) & ( not z0 be emptyXBOOLE-0V1 iff  not q00 be emptyXBOOLE-0V1)) & ( not z1 be emptyXBOOLE-0V1 iff  not q01 be emptyXBOOLE-0V1)) & ( not z2 be emptyXBOOLE-0V1 iff  not q11 be emptyXBOOLE-0V1)) & ( not z3 be emptyXBOOLE-0V1 iff  not q21 be emptyXBOOLE-0V1)) & ( not z4 be emptyXBOOLE-0V1 iff  not q22 be emptyXBOOLE-0V1)) & ( not z5 be emptyXBOOLE-0V1 iff  not c22 be emptyXBOOLE-0V1) implies ((((( not z0 be emptyXBOOLE-0V1 iff  not MULT310GATE-5K5(x2,x1,y1,x0,y0) be emptyXBOOLE-0V1) & ( not z1 be emptyXBOOLE-0V1 iff  not MULT311GATE-5K6(x2,x1,y1,x0,y0) be emptyXBOOLE-0V1)) & ( not z2 be emptyXBOOLE-0V1 iff  not MULT321GATE-5K10(x2,y2,x1,y1,x0,y0) be emptyXBOOLE-0V1)) & ( not z3 be emptyXBOOLE-0V1 iff  not MULT322GATE-5K11(x2,y2,x1,y1,x0,y0) be emptyXBOOLE-0V1)) & ( not z4 be emptyXBOOLE-0V1 iff  not MULT323GATE-5K12(x2,y2,x1,y1,x0,y0) be emptyXBOOLE-0V1)) & ( not z5 be emptyXBOOLE-0V1 iff  not MULT324GATE-5K13(x2,y2,x1,y1,x0,y0) be emptyXBOOLE-0V1)"
sorry

(*begin*)
mtheorem gate_5_th_3:
" for x0 be setHIDDENM2 holds  for x1 be setHIDDENM2 holds  for x2 be setHIDDENM2 holds  for y0 be setHIDDENM2 holds  for y1 be setHIDDENM2 holds  for y2 be setHIDDENM2 holds  for z0 be setHIDDENM2 holds  for z1 be setHIDDENM2 holds  for z2 be setHIDDENM2 holds  for z3 be setHIDDENM2 holds  for z4 be setHIDDENM2 holds  for z5 be setHIDDENM2 holds  for q00 be setHIDDENM2 holds  for q01 be setHIDDENM2 holds  for q02 be setHIDDENM2 holds  for q03 be setHIDDENM2 holds  for c01 be setHIDDENM2 holds  for c02 be setHIDDENM2 holds  for c03 be setHIDDENM2 holds  for q11 be setHIDDENM2 holds  for q12 be setHIDDENM2 holds  for q13 be setHIDDENM2 holds  for c11 be setHIDDENM2 holds  for c12 be setHIDDENM2 holds  for c13 be setHIDDENM2 holds (((((((((((((((((( not q00 be emptyXBOOLE-0V1 iff  not AND2GATE-1K2(x0,y0) be emptyXBOOLE-0V1) & ( not q01 be emptyXBOOLE-0V1 iff  not XOR3GATE-1K10(AND2GATE-1K2(x1,y0),AND2GATE-1K2(x0,y1),{}XBOOLE-0K1) be emptyXBOOLE-0V1)) & ( not c01 be emptyXBOOLE-0V1 iff  not MAJ3GATE-1K11(AND2GATE-1K2(x1,y0),AND2GATE-1K2(x0,y1),{}XBOOLE-0K1) be emptyXBOOLE-0V1)) & ( not q02 be emptyXBOOLE-0V1 iff  not XOR3GATE-1K10(AND2GATE-1K2(x2,y0),AND2GATE-1K2(x1,y1),AND2GATE-1K2(x0,y2)) be emptyXBOOLE-0V1)) & ( not c02 be emptyXBOOLE-0V1 iff  not MAJ3GATE-1K11(AND2GATE-1K2(x2,y0),AND2GATE-1K2(x1,y1),AND2GATE-1K2(x0,y2)) be emptyXBOOLE-0V1)) & ( not q03 be emptyXBOOLE-0V1 iff  not XOR3GATE-1K10(AND2GATE-1K2(x2,y1),AND2GATE-1K2(x1,y2),{}XBOOLE-0K1) be emptyXBOOLE-0V1)) & ( not c03 be emptyXBOOLE-0V1 iff  not MAJ3GATE-1K11(AND2GATE-1K2(x2,y1),AND2GATE-1K2(x1,y2),{}XBOOLE-0K1) be emptyXBOOLE-0V1)) & ( not q11 be emptyXBOOLE-0V1 iff  not XOR3GATE-1K10(q02,c01,{}XBOOLE-0K1) be emptyXBOOLE-0V1)) & ( not c11 be emptyXBOOLE-0V1 iff  not MAJ3GATE-1K11(q02,c01,{}XBOOLE-0K1) be emptyXBOOLE-0V1)) & ( not q12 be emptyXBOOLE-0V1 iff  not XOR3GATE-1K10(q03,c02,c11) be emptyXBOOLE-0V1)) & ( not c12 be emptyXBOOLE-0V1 iff  not MAJ3GATE-1K11(q03,c02,c11) be emptyXBOOLE-0V1)) & ( not q13 be emptyXBOOLE-0V1 iff  not XOR3GATE-1K10(AND2GATE-1K2(x2,y2),c03,c12) be emptyXBOOLE-0V1)) & ( not c13 be emptyXBOOLE-0V1 iff  not MAJ3GATE-1K11(AND2GATE-1K2(x2,y2),c03,c12) be emptyXBOOLE-0V1)) & ( not z0 be emptyXBOOLE-0V1 iff  not q00 be emptyXBOOLE-0V1)) & ( not z1 be emptyXBOOLE-0V1 iff  not q01 be emptyXBOOLE-0V1)) & ( not z2 be emptyXBOOLE-0V1 iff  not q11 be emptyXBOOLE-0V1)) & ( not z3 be emptyXBOOLE-0V1 iff  not q12 be emptyXBOOLE-0V1)) & ( not z4 be emptyXBOOLE-0V1 iff  not q13 be emptyXBOOLE-0V1)) & ( not z5 be emptyXBOOLE-0V1 iff  not c13 be emptyXBOOLE-0V1) implies ((((( not z0 be emptyXBOOLE-0V1 iff  not MULT310GATE-5K5(x2,x1,y1,x0,y0) be emptyXBOOLE-0V1) & ( not z1 be emptyXBOOLE-0V1 iff  not MULT311GATE-5K6(x2,x1,y1,x0,y0) be emptyXBOOLE-0V1)) & ( not z2 be emptyXBOOLE-0V1 iff  not MULT321GATE-5K10(x2,y2,x1,y1,x0,y0) be emptyXBOOLE-0V1)) & ( not z3 be emptyXBOOLE-0V1 iff  not MULT322GATE-5K11(x2,y2,x1,y1,x0,y0) be emptyXBOOLE-0V1)) & ( not z4 be emptyXBOOLE-0V1 iff  not MULT323GATE-5K12(x2,y2,x1,y1,x0,y0) be emptyXBOOLE-0V1)) & ( not z5 be emptyXBOOLE-0V1 iff  not MULT324GATE-5K13(x2,y2,x1,y1,x0,y0) be emptyXBOOLE-0V1)"
sorry

abbreviation(input) GATE_5K14("CLAADD1GATE-5K14'( _ , _ , _ ')" [0,0,0]164) where
  "CLAADD1GATE-5K14(a1,b1,c) \<equiv> XOR3GATE-1K10(a1,b1,c)"

abbreviation(input) GATE_5K15("CLACARR1GATE-5K15'( _ , _ , _ ')" [0,0,0]164) where
  "CLACARR1GATE-5K15(a1,b1,c) \<equiv> MAJ3GATE-1K11(a1,b1,c)"

mdef gate_5_def_14 ("CLAADD2GATE-5K16'( _ , _ , _ , _ , _ ')" [0,0,0,0,0]164 ) where
  mlet "a1 be setHIDDENM2", "b1 be setHIDDENM2", "a2 be setHIDDENM2", "b2 be setHIDDENM2", "c be setHIDDENM2"
"func CLAADD2GATE-5K16(a2,b2,a1,b1,c) \<rightarrow> setHIDDENM2 equals
  XOR3GATE-1K10(a2,b2,MAJ3GATE-1K11(a1,b1,c))"
proof-
  (*coherence*)
    show "XOR3GATE-1K10(a2,b2,MAJ3GATE-1K11(a1,b1,c)) be setHIDDENM2"
       sorry
qed "sorry"

mdef gate_5_def_15 ("CLACARR2GATE-5K17'( _ , _ , _ , _ , _ ')" [0,0,0,0,0]164 ) where
  mlet "a1 be setHIDDENM2", "b1 be setHIDDENM2", "a2 be setHIDDENM2", "b2 be setHIDDENM2", "c be setHIDDENM2"
"func CLACARR2GATE-5K17(a2,b2,a1,b1,c) \<rightarrow> setHIDDENM2 equals
  OR2GATE-1K3(AND2GATE-1K2(a2,b2),AND2GATE-1K2(OR2GATE-1K3(a2,b2),MAJ3GATE-1K11(a1,b1,c)))"
proof-
  (*coherence*)
    show "OR2GATE-1K3(AND2GATE-1K2(a2,b2),AND2GATE-1K2(OR2GATE-1K3(a2,b2),MAJ3GATE-1K11(a1,b1,c))) be setHIDDENM2"
       sorry
qed "sorry"

mdef gate_5_def_16 ("CLAADD3GATE-5K18'( _ , _ , _ , _ , _ , _ , _ ')" [0,0,0,0,0,0,0]164 ) where
  mlet "a1 be setHIDDENM2", "b1 be setHIDDENM2", "a2 be setHIDDENM2", "b2 be setHIDDENM2", "a3 be setHIDDENM2", "b3 be setHIDDENM2", "c be setHIDDENM2"
"func CLAADD3GATE-5K18(a3,b3,a2,b2,a1,b1,c) \<rightarrow> setHIDDENM2 equals
  XOR3GATE-1K10(a3,b3,CLACARR2GATE-5K17(a2,b2,a1,b1,c))"
proof-
  (*coherence*)
    show "XOR3GATE-1K10(a3,b3,CLACARR2GATE-5K17(a2,b2,a1,b1,c)) be setHIDDENM2"
       sorry
qed "sorry"

mdef gate_5_def_17 ("CLACARR3GATE-5K19'( _ , _ , _ , _ , _ , _ , _ ')" [0,0,0,0,0,0,0]164 ) where
  mlet "a1 be setHIDDENM2", "b1 be setHIDDENM2", "a2 be setHIDDENM2", "b2 be setHIDDENM2", "a3 be setHIDDENM2", "b3 be setHIDDENM2", "c be setHIDDENM2"
"func CLACARR3GATE-5K19(a3,b3,a2,b2,a1,b1,c) \<rightarrow> setHIDDENM2 equals
  OR3GATE-1K9(AND2GATE-1K2(a3,b3),AND2GATE-1K2(OR2GATE-1K3(a3,b3),AND2GATE-1K2(a2,b2)),AND3GATE-1K8(OR2GATE-1K3(a3,b3),OR2GATE-1K3(a2,b2),MAJ3GATE-1K11(a1,b1,c)))"
proof-
  (*coherence*)
    show "OR3GATE-1K9(AND2GATE-1K2(a3,b3),AND2GATE-1K2(OR2GATE-1K3(a3,b3),AND2GATE-1K2(a2,b2)),AND3GATE-1K8(OR2GATE-1K3(a3,b3),OR2GATE-1K3(a2,b2),MAJ3GATE-1K11(a1,b1,c))) be setHIDDENM2"
       sorry
qed "sorry"

mdef gate_5_def_18 ("CLAADD4GATE-5K20'( _ , _ , _ , _ , _ , _ , _ , _ , _ ')" [0,0,0,0,0,0,0,0,0]164 ) where
  mlet "a1 be setHIDDENM2", "b1 be setHIDDENM2", "a2 be setHIDDENM2", "b2 be setHIDDENM2", "a3 be setHIDDENM2", "b3 be setHIDDENM2", "a4 be setHIDDENM2", "b4 be setHIDDENM2", "c be setHIDDENM2"
"func CLAADD4GATE-5K20(a4,b4,a3,b3,a2,b2,a1,b1,c) \<rightarrow> setHIDDENM2 equals
  XOR3GATE-1K10(a4,b4,CLACARR3GATE-5K19(a3,b3,a2,b2,a1,b1,c))"
proof-
  (*coherence*)
    show "XOR3GATE-1K10(a4,b4,CLACARR3GATE-5K19(a3,b3,a2,b2,a1,b1,c)) be setHIDDENM2"
       sorry
qed "sorry"

mdef gate_5_def_19 ("CLACARR4GATE-5K21'( _ , _ , _ , _ , _ , _ , _ , _ , _ ')" [0,0,0,0,0,0,0,0,0]164 ) where
  mlet "a1 be setHIDDENM2", "b1 be setHIDDENM2", "a2 be setHIDDENM2", "b2 be setHIDDENM2", "a3 be setHIDDENM2", "b3 be setHIDDENM2", "a4 be setHIDDENM2", "b4 be setHIDDENM2", "c be setHIDDENM2"
"func CLACARR4GATE-5K21(a4,b4,a3,b3,a2,b2,a1,b1,c) \<rightarrow> setHIDDENM2 equals
  OR4GATE-1K15(AND2GATE-1K2(a4,b4),AND2GATE-1K2(OR2GATE-1K3(a4,b4),AND2GATE-1K2(a3,b3)),AND3GATE-1K8(OR2GATE-1K3(a4,b4),OR2GATE-1K3(a3,b3),AND2GATE-1K2(a2,b2)),AND4GATE-1K14(OR2GATE-1K3(a4,b4),OR2GATE-1K3(a3,b3),OR2GATE-1K3(a2,b2),MAJ3GATE-1K11(a1,b1,c)))"
proof-
  (*coherence*)
    show "OR4GATE-1K15(AND2GATE-1K2(a4,b4),AND2GATE-1K2(OR2GATE-1K3(a4,b4),AND2GATE-1K2(a3,b3)),AND3GATE-1K8(OR2GATE-1K3(a4,b4),OR2GATE-1K3(a3,b3),AND2GATE-1K2(a2,b2)),AND4GATE-1K14(OR2GATE-1K3(a4,b4),OR2GATE-1K3(a3,b3),OR2GATE-1K3(a2,b2),MAJ3GATE-1K11(a1,b1,c))) be setHIDDENM2"
       sorry
qed "sorry"

mtheorem gate_5_th_4:
" for x0 be setHIDDENM2 holds  for x1 be setHIDDENM2 holds  for x2 be setHIDDENM2 holds  for y0 be setHIDDENM2 holds  for y1 be setHIDDENM2 holds  for y2 be setHIDDENM2 holds  for z0 be setHIDDENM2 holds  for z1 be setHIDDENM2 holds  for z2 be setHIDDENM2 holds  for z3 be setHIDDENM2 holds  for z4 be setHIDDENM2 holds  for z5 be setHIDDENM2 holds  for q00 be setHIDDENM2 holds  for q01 be setHIDDENM2 holds  for q02 be setHIDDENM2 holds  for q03 be setHIDDENM2 holds  for c01 be setHIDDENM2 holds  for c02 be setHIDDENM2 holds  for c03 be setHIDDENM2 holds (((((((((((( not q00 be emptyXBOOLE-0V1 iff  not AND2GATE-1K2(x0,y0) be emptyXBOOLE-0V1) & ( not q01 be emptyXBOOLE-0V1 iff  not XOR3GATE-1K10(AND2GATE-1K2(x1,y0),AND2GATE-1K2(x0,y1),{}XBOOLE-0K1) be emptyXBOOLE-0V1)) & ( not c01 be emptyXBOOLE-0V1 iff  not MAJ3GATE-1K11(AND2GATE-1K2(x1,y0),AND2GATE-1K2(x0,y1),{}XBOOLE-0K1) be emptyXBOOLE-0V1)) & ( not q02 be emptyXBOOLE-0V1 iff  not XOR3GATE-1K10(AND2GATE-1K2(x2,y0),AND2GATE-1K2(x1,y1),AND2GATE-1K2(x0,y2)) be emptyXBOOLE-0V1)) & ( not c02 be emptyXBOOLE-0V1 iff  not MAJ3GATE-1K11(AND2GATE-1K2(x2,y0),AND2GATE-1K2(x1,y1),AND2GATE-1K2(x0,y2)) be emptyXBOOLE-0V1)) & ( not q03 be emptyXBOOLE-0V1 iff  not XOR3GATE-1K10(AND2GATE-1K2(x2,y1),AND2GATE-1K2(x1,y2),{}XBOOLE-0K1) be emptyXBOOLE-0V1)) & ( not c03 be emptyXBOOLE-0V1 iff  not MAJ3GATE-1K11(AND2GATE-1K2(x2,y1),AND2GATE-1K2(x1,y2),{}XBOOLE-0K1) be emptyXBOOLE-0V1)) & ( not z0 be emptyXBOOLE-0V1 iff  not q00 be emptyXBOOLE-0V1)) & ( not z1 be emptyXBOOLE-0V1 iff  not q01 be emptyXBOOLE-0V1)) & ( not z2 be emptyXBOOLE-0V1 iff  not CLAADD1GATE-5K14(q02,c01,{}XBOOLE-0K1) be emptyXBOOLE-0V1)) & ( not z3 be emptyXBOOLE-0V1 iff  not CLAADD2GATE-5K16(q03,c02,q02,c01,{}XBOOLE-0K1) be emptyXBOOLE-0V1)) & ( not z4 be emptyXBOOLE-0V1 iff  not CLAADD3GATE-5K18(AND2GATE-1K2(x2,y2),c03,q03,c02,q02,c01,{}XBOOLE-0K1) be emptyXBOOLE-0V1)) & ( not z5 be emptyXBOOLE-0V1 iff  not CLACARR3GATE-5K19(AND2GATE-1K2(x2,y2),c03,q03,c02,q02,c01,{}XBOOLE-0K1) be emptyXBOOLE-0V1) implies ((((( not z0 be emptyXBOOLE-0V1 iff  not MULT310GATE-5K5(x2,x1,y1,x0,y0) be emptyXBOOLE-0V1) & ( not z1 be emptyXBOOLE-0V1 iff  not MULT311GATE-5K6(x2,x1,y1,x0,y0) be emptyXBOOLE-0V1)) & ( not z2 be emptyXBOOLE-0V1 iff  not MULT321GATE-5K10(x2,y2,x1,y1,x0,y0) be emptyXBOOLE-0V1)) & ( not z3 be emptyXBOOLE-0V1 iff  not MULT322GATE-5K11(x2,y2,x1,y1,x0,y0) be emptyXBOOLE-0V1)) & ( not z4 be emptyXBOOLE-0V1 iff  not MULT323GATE-5K12(x2,y2,x1,y1,x0,y0) be emptyXBOOLE-0V1)) & ( not z5 be emptyXBOOLE-0V1 iff  not MULT324GATE-5K13(x2,y2,x1,y1,x0,y0) be emptyXBOOLE-0V1)"
sorry

end
