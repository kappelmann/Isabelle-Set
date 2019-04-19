theory real
  imports xreal_0
begin
(*begin*)
reserve x, y, z for "RealXREAL-0M1"
mlemma real_lm_1:
" for x be RealXREAL-0M1 holds  for y be RealXREAL-0M1 holds x <=XXREAL-0R1 y & y <=XXREAL-0R1 x implies x =HIDDENR1 y"
sorry

mlemma real_lm_2:
" for x be RealXREAL-0M1 holds  for y be RealXREAL-0M1 holds  for z be RealXREAL-0M1 holds x <=XXREAL-0R1 y & y <=XXREAL-0R1 z implies x <=XXREAL-0R1 z"
sorry

mtheorem real_th_1:
" for x be RealXREAL-0M1 holds  for y be RealXREAL-0M1 holds x <=XXREAL-0R1 y & x be positiveXXREAL-0V2 implies y be positiveXXREAL-0V2"
sorry

mtheorem real_th_2:
" for x be RealXREAL-0M1 holds  for y be RealXREAL-0M1 holds x <=XXREAL-0R1 y & y be negativeXXREAL-0V3 implies x be negativeXXREAL-0V3"
sorry

mtheorem real_th_3:
" for x be RealXREAL-0M1 holds  for y be RealXREAL-0M1 holds x <=XXREAL-0R1 y & x be  non negativeXXREAL-0V3 implies y be  non negativeXXREAL-0V3"
sorry

mtheorem real_th_4:
" for x be RealXREAL-0M1 holds  for y be RealXREAL-0M1 holds x <=XXREAL-0R1 y & y be  non positiveXXREAL-0V2 implies x be  non positiveXXREAL-0V2"
sorry

mtheorem real_th_5:
" for x be RealXREAL-0M1 holds  for y be RealXREAL-0M1 holds (x <=XXREAL-0R1 y & y be  non zeroORDINAL1V8) & x be  non negativeXXREAL-0V3 implies y be positiveXXREAL-0V2"
sorry

mtheorem real_th_6:
" for x be RealXREAL-0M1 holds  for y be RealXREAL-0M1 holds (x <=XXREAL-0R1 y & x be  non zeroORDINAL1V8) & y be  non positiveXXREAL-0V2 implies x be negativeXXREAL-0V3"
sorry

mtheorem real_th_7:
" for x be RealXREAL-0M1 holds  for y be RealXREAL-0M1 holds  not x <=XXREAL-0R1 y & x be  non positiveXXREAL-0V2 implies y be negativeXXREAL-0V3"
sorry

mtheorem real_th_8:
" for x be RealXREAL-0M1 holds  for y be RealXREAL-0M1 holds  not x <=XXREAL-0R1 y & y be  non negativeXXREAL-0V3 implies x be positiveXXREAL-0V2"
sorry

end
