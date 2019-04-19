theory xfamily
  imports xtuple_0
begin
(*begin*)
theorem xfamily_sch_1:
  fixes Af0 Pp1 
  assumes
[ty]: "Af0 be setHIDDENM2"
  shows " ex X be setHIDDENM2 st  for x be setHIDDENM2 holds x inTARSKIR2 X iff x inTARSKIR2 Af0 & Pp1(x)"
sorry

theorem xfamily_sch_2:
  fixes Xf0 Yf0 Pp1 
  assumes
[ty]: "Xf0 be setHIDDENM2" and
  [ty]: "Yf0 be setHIDDENM2" and
   A1: " for x be setHIDDENM2 holds x inTARSKIR2 Xf0 iff Pp1(x)" and
   A2: " for x be setHIDDENM2 holds x inTARSKIR2 Yf0 iff Pp1(x)"
  shows "Xf0 =HIDDENR1 Yf0"
sorry

theorem xfamily_sch_3:
  fixes Pp1 
  shows " for X1 be setHIDDENM2 holds  for X2 be setHIDDENM2 holds ( for x be setHIDDENM2 holds x inTARSKIR2 X1 iff Pp1(x)) & ( for x be setHIDDENM2 holds x inTARSKIR2 X2 iff Pp1(x)) implies X1 =HIDDENR1 X2"
sorry

abbreviation(input) XFAMILYK1(" _ `1XFAMILYK1" [355]355) where
  "x `1XFAMILYK1 \<equiv> x `1XTUPLE-0K1"

mtheorem xfamily_add_1:
  mlet "x be objectHIDDENM1"
"cluster x `1XTUPLE-0K1 as-term-is setHIDDENM2"
proof
(*coherence*)
  show "x `1XTUPLE-0K1 be setHIDDENM2"
    using tarski_th_1 sorry
qed "sorry"

abbreviation(input) XFAMILYK2(" _ `2XFAMILYK2" [355]355) where
  "x `2XFAMILYK2 \<equiv> x `2XTUPLE-0K2"

mtheorem xfamily_add_2:
  mlet "x be objectHIDDENM1"
"cluster x `2XTUPLE-0K2 as-term-is setHIDDENM2"
proof
(*coherence*)
  show "x `2XTUPLE-0K2 be setHIDDENM2"
    using tarski_th_1 sorry
qed "sorry"

abbreviation(input) XFAMILYK3(" _ `1-3XFAMILYK3" [164]164) where
  "x `1-3XFAMILYK3 \<equiv> x `1-3XTUPLE-0K4"

mtheorem xfamily_add_3:
  mlet "x be objectHIDDENM1"
"cluster x `1-3XTUPLE-0K4 as-term-is setHIDDENM2"
proof
(*coherence*)
  show "x `1-3XTUPLE-0K4 be setHIDDENM2"
    using tarski_th_1 sorry
qed "sorry"

abbreviation(input) XFAMILYK4(" _ `2-3XFAMILYK4" [164]164) where
  "x `2-3XFAMILYK4 \<equiv> x `2-3XTUPLE-0K5"

mtheorem xfamily_add_4:
  mlet "x be objectHIDDENM1"
"cluster x `2-3XTUPLE-0K5 as-term-is setHIDDENM2"
proof
(*coherence*)
  show "x `2-3XTUPLE-0K5 be setHIDDENM2"
    using tarski_th_1 sorry
qed "sorry"

abbreviation(input) XFAMILYK5(" _ `1-4XFAMILYK5" [164]164) where
  "x `1-4XFAMILYK5 \<equiv> x `1-4XTUPLE-0K8"

mtheorem xfamily_add_5:
  mlet "x be objectHIDDENM1"
"cluster x `1-4XTUPLE-0K8 as-term-is setHIDDENM2"
proof
(*coherence*)
  show "x `1-4XTUPLE-0K8 be setHIDDENM2"
    using tarski_th_1 sorry
qed "sorry"

abbreviation(input) XFAMILYK6(" _ `2-4XFAMILYK6" [164]164) where
  "x `2-4XFAMILYK6 \<equiv> x `2-4XTUPLE-0K9"

mtheorem xfamily_add_6:
  mlet "x be objectHIDDENM1"
"cluster x `2-4XTUPLE-0K9 as-term-is setHIDDENM2"
proof
(*coherence*)
  show "x `2-4XTUPLE-0K9 be setHIDDENM2"
    using tarski_th_1 sorry
qed "sorry"

end
