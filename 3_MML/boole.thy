theory boole
  imports xboole_0
begin
(*begin*)
mtheorem boole_th_1:
" for X be setHIDDENM2 holds X \\/XBOOLE-0K2 {}XBOOLE-0K1 =XBOOLE-0R4 X"
sorry

mtheorem boole_th_2:
" for X be setHIDDENM2 holds X /\\XBOOLE-0K3 {}XBOOLE-0K1 =XBOOLE-0R4 {}XBOOLE-0K1"
sorry

mtheorem boole_th_3:
" for X be setHIDDENM2 holds X \\XBOOLE-0K4 {}XBOOLE-0K1 =XBOOLE-0R4 X"
sorry

mtheorem boole_th_4:
" for X be setHIDDENM2 holds {}XBOOLE-0K1 \\XBOOLE-0K4 X =XBOOLE-0R4 {}XBOOLE-0K1"
sorry

mtheorem boole_th_5:
" for X be setHIDDENM2 holds X \\+\\XBOOLE-0K5 {}XBOOLE-0K1 =XBOOLE-0R4 X"
sorry

reserve x, X for "setHIDDENM2"
mlemma boole_lm_1:
" for X be setHIDDENM2 holds X be emptyXBOOLE-0V1 implies X =XBOOLE-0R4 {}XBOOLE-0K1"
sorry

mtheorem boole_th_6:
" for X be setHIDDENM2 holds X be emptyXBOOLE-0V1 implies X =XBOOLE-0R4 {}XBOOLE-0K1"
  using boole_lm_1 sorry

mtheorem boole_th_7:
" for x be setHIDDENM2 holds  for X be setHIDDENM2 holds x inTARSKIR2 X implies X be  non emptyXBOOLE-0V1"
  using xboole_0_def_1 sorry

mtheorem boole_th_8:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X be emptyXBOOLE-0V1 & X <>HIDDENR2 Y implies Y be  non emptyXBOOLE-0V1"
sorry

end
