theory xregular
  imports enumset1 xfamily
begin
(*begin*)
reserve x, y, X1, X2, X3, X4, X5, X6, Y, Y1, Y2, Y3, Y4, Y5, Z, Z1, Z2, Z3, Z4, Z5 for "setHIDDENM2"
reserve X for " non emptyXBOOLE-0V1\<bar>setHIDDENM2"
mtheorem xregular_th_1:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  ex Y be setHIDDENM2 st Y inTARSKIR2 X & Y missesXBOOLE-0R1 X"
sorry

mtheorem xregular_th_2:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  ex Y be setHIDDENM2 st Y inTARSKIR2 X & ( for Y1 be setHIDDENM2 holds Y1 inTARSKIR2 Y implies Y1 missesXBOOLE-0R1 X)"
sorry

mtheorem xregular_th_3:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  ex Y be setHIDDENM2 st Y inTARSKIR2 X & ( for Y1 be setHIDDENM2 holds  for Y2 be setHIDDENM2 holds Y1 inTARSKIR2 Y2 & Y2 inTARSKIR2 Y implies Y1 missesXBOOLE-0R1 X)"
sorry

mtheorem xregular_th_4:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  ex Y be setHIDDENM2 st Y inTARSKIR2 X & ( for Y1 be setHIDDENM2 holds  for Y2 be setHIDDENM2 holds  for Y3 be setHIDDENM2 holds (Y1 inTARSKIR2 Y2 & Y2 inTARSKIR2 Y3) & Y3 inTARSKIR2 Y implies Y1 missesXBOOLE-0R1 X)"
sorry

mtheorem xregular_th_5:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  ex Y be setHIDDENM2 st Y inTARSKIR2 X & ( for Y1 be setHIDDENM2 holds  for Y2 be setHIDDENM2 holds  for Y3 be setHIDDENM2 holds  for Y4 be setHIDDENM2 holds ((Y1 inTARSKIR2 Y2 & Y2 inTARSKIR2 Y3) & Y3 inTARSKIR2 Y4) & Y4 inTARSKIR2 Y implies Y1 missesXBOOLE-0R1 X)"
sorry

mtheorem xregular_th_6:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  ex Y be setHIDDENM2 st Y inTARSKIR2 X & ( for Y1 be setHIDDENM2 holds  for Y2 be setHIDDENM2 holds  for Y3 be setHIDDENM2 holds  for Y4 be setHIDDENM2 holds  for Y5 be setHIDDENM2 holds (((Y1 inTARSKIR2 Y2 & Y2 inTARSKIR2 Y3) & Y3 inTARSKIR2 Y4) & Y4 inTARSKIR2 Y5) & Y5 inTARSKIR2 Y implies Y1 missesXBOOLE-0R1 X)"
sorry

mtheorem xregular_th_7:
" for X1 be setHIDDENM2 holds  for X2 be setHIDDENM2 holds  for X3 be setHIDDENM2 holds  not ((X1 inTARSKIR2 X2 & X2 inTARSKIR2 X3) & X3 inTARSKIR2 X1)"
sorry

mtheorem xregular_th_8:
" for X1 be setHIDDENM2 holds  for X2 be setHIDDENM2 holds  for X3 be setHIDDENM2 holds  for X4 be setHIDDENM2 holds  not (((X1 inTARSKIR2 X2 & X2 inTARSKIR2 X3) & X3 inTARSKIR2 X4) & X4 inTARSKIR2 X1)"
sorry

mtheorem xregular_th_9:
" for X1 be setHIDDENM2 holds  for X2 be setHIDDENM2 holds  for X3 be setHIDDENM2 holds  for X4 be setHIDDENM2 holds  for X5 be setHIDDENM2 holds  not ((((X1 inTARSKIR2 X2 & X2 inTARSKIR2 X3) & X3 inTARSKIR2 X4) & X4 inTARSKIR2 X5) & X5 inTARSKIR2 X1)"
sorry

mtheorem xregular_th_10:
" for X1 be setHIDDENM2 holds  for X2 be setHIDDENM2 holds  for X3 be setHIDDENM2 holds  for X4 be setHIDDENM2 holds  for X5 be setHIDDENM2 holds  for X6 be setHIDDENM2 holds  not (((((X1 inTARSKIR2 X2 & X2 inTARSKIR2 X3) & X3 inTARSKIR2 X4) & X4 inTARSKIR2 X5) & X5 inTARSKIR2 X6) & X6 inTARSKIR2 X1)"
sorry

end
