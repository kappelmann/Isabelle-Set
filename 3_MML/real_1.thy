theory real_1
  imports xreal_0
   "../mizar_extension/E_number"
begin
(*begin*)
mtheorem real_1_cl_1:
"cluster note-that realXREAL-0V1 for ElementSUBSET-1M1-of REALNUMBERSK2"
proof
(*coherence*)
  show " for it be ElementSUBSET-1M1-of REALNUMBERSK2 holds it be realXREAL-0V1"
     sorry
qed "sorry"

mtheorem real_1_cl_2:
"cluster positiveXXREAL-0V2 for RealXREAL-0M1"
proof
(*existence*)
  show " ex it be RealXREAL-0M1 st it be positiveXXREAL-0V2"
sorry
qed "sorry"

mtheorem real_1_cl_3:
"cluster positiveXXREAL-0V2 for ElementSUBSET-1M1-of REALNUMBERSK2"
proof
(*existence*)
  show " ex it be ElementSUBSET-1M1-of REALNUMBERSK2 st it be positiveXXREAL-0V2"
sorry
qed "sorry"

abbreviation(input) REAL_1K1("-REAL-1K1  _ " [132]132) where
  "-REAL-1K1 x \<equiv> -XCMPLX-0K4 x"

mtheorem real_1_add_1:
  mlet "x be ElementSUBSET-1M1-of REALNUMBERSK2"
"cluster -XCMPLX-0K4 x as-term-is ElementSUBSET-1M1-of REALNUMBERSK2"
proof
(*coherence*)
  show "-XCMPLX-0K4 x be ElementSUBSET-1M1-of REALNUMBERSK2"
    using xreal_0_def_1 sorry
qed "sorry"

abbreviation(input) REAL_1K2(" _ \<inverse>REAL-1K2" [228]228) where
  "x \<inverse>REAL-1K2 \<equiv> x \<inverse>XCMPLX-0K5"

mtheorem real_1_add_2:
  mlet "x be ElementSUBSET-1M1-of REALNUMBERSK2"
"cluster x \<inverse>XCMPLX-0K5 as-term-is ElementSUBSET-1M1-of REALNUMBERSK2"
proof
(*coherence*)
  show "x \<inverse>XCMPLX-0K5 be ElementSUBSET-1M1-of REALNUMBERSK2"
    using xreal_0_def_1 sorry
qed "sorry"

abbreviation(input) REAL_1K3(" _ +REAL-1K3  _ " [132,132]132) where
  "x +REAL-1K3 y \<equiv> x +XCMPLX-0K2 y"

mtheorem real_1_add_3:
  mlet "x be ElementSUBSET-1M1-of REALNUMBERSK2", "y be ElementSUBSET-1M1-of REALNUMBERSK2"
"cluster x +XCMPLX-0K2 y as-term-is ElementSUBSET-1M1-of REALNUMBERSK2"
proof
(*coherence*)
  show "x +XCMPLX-0K2 y be ElementSUBSET-1M1-of REALNUMBERSK2"
    using xreal_0_def_1 sorry
qed "sorry"

abbreviation(input) REAL_1K4(" _ *REAL-1K4  _ " [164,164]164) where
  "x *REAL-1K4 y \<equiv> x *XCMPLX-0K3 y"

mtheorem real_1_add_4:
  mlet "x be ElementSUBSET-1M1-of REALNUMBERSK2", "y be ElementSUBSET-1M1-of REALNUMBERSK2"
"cluster x *XCMPLX-0K3 y as-term-is ElementSUBSET-1M1-of REALNUMBERSK2"
proof
(*coherence*)
  show "x *XCMPLX-0K3 y be ElementSUBSET-1M1-of REALNUMBERSK2"
    using xreal_0_def_1 sorry
qed "sorry"

abbreviation(input) REAL_1K5(" _ -REAL-1K5  _ " [132,132]132) where
  "x -REAL-1K5 y \<equiv> x -XCMPLX-0K6 y"

mtheorem real_1_add_5:
  mlet "x be ElementSUBSET-1M1-of REALNUMBERSK2", "y be ElementSUBSET-1M1-of REALNUMBERSK2"
"cluster x -XCMPLX-0K6 y as-term-is ElementSUBSET-1M1-of REALNUMBERSK2"
proof
(*coherence*)
  show "x -XCMPLX-0K6 y be ElementSUBSET-1M1-of REALNUMBERSK2"
    using xreal_0_def_1 sorry
qed "sorry"

abbreviation(input) REAL_1K6(" _ '/REAL-1K6  _ " [164,164]164) where
  "x /REAL-1K6 y \<equiv> x /XCMPLX-0K7 y"

mtheorem real_1_add_6:
  mlet "x be ElementSUBSET-1M1-of REALNUMBERSK2", "y be ElementSUBSET-1M1-of REALNUMBERSK2"
"cluster x /XCMPLX-0K7 y as-term-is ElementSUBSET-1M1-of REALNUMBERSK2"
proof
(*coherence*)
  show "x /XCMPLX-0K7 y be ElementSUBSET-1M1-of REALNUMBERSK2"
    using xreal_0_def_1 sorry
qed "sorry"

mtheorem real_1_th_1:
"REAL+ARYTM-2K2 =XBOOLE-0R4 {r where r be RealXREAL-0M1 : 0NUMBERSK6 <=XXREAL-0R1 r }"
sorry

end
