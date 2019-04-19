theory subset
  imports subset_1
begin
(*begin*)
mtheorem subset_th_1:
" for a be setHIDDENM2 holds  for b be setHIDDENM2 holds a inTARSKIR2 b implies a be ElementSUBSET-1M1-of b"
  using subset_1_def_1 sorry

mtheorem subset_th_2:
" for a be setHIDDENM2 holds  for b be setHIDDENM2 holds a be ElementSUBSET-1M1-of b & b be  non emptyXBOOLE-0V1 implies a inTARSKIR2 b"
  using subset_1_def_1 sorry

mtheorem subset_th_3:
" for a be setHIDDENM2 holds  for b be setHIDDENM2 holds a be SubsetSUBSET-1M2-of b iff a c=TARSKIR1 b"
sorry

mtheorem subset_th_4:
" for a be setHIDDENM2 holds  for b be setHIDDENM2 holds  for c be setHIDDENM2 holds a inTARSKIR2 b & b be SubsetSUBSET-1M2-of c implies a be ElementSUBSET-1M1-of c"
sorry

mtheorem subset_th_5:
" for a be setHIDDENM2 holds  for b be setHIDDENM2 holds  for c be setHIDDENM2 holds a inTARSKIR2 b & b be SubsetSUBSET-1M2-of c implies c be  non emptyXBOOLE-0V1"
   sorry

end
