theory xboole_1
  imports xboole_0
begin
(*begin*)
reserve x, A, B, X, X9, Y, Y9, Z, V for "setHIDDENM2"
(*\$N Modus Barbara*)
mtheorem xboole_1_th_1:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds X c=TARSKIR1 Y & Y c=TARSKIR1 Z implies X c=TARSKIR1 Z"
   sorry

mtheorem xboole_1_th_2:
" for X be setHIDDENM2 holds {}XBOOLE-0K1 c=TARSKIR1 X"
   sorry

mtheorem xboole_1_th_3:
" for X be setHIDDENM2 holds X c=TARSKIR1 {}XBOOLE-0K1 implies X =XBOOLE-0R4 {}XBOOLE-0K1"
sorry

mtheorem xboole_1_th_4:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds (X \\/XBOOLE-0K2 Y)\\/XBOOLE-0K2 Z =XBOOLE-0R4 X \\/XBOOLE-0K2 (Y \\/XBOOLE-0K2 Z)"
sorry

mtheorem xboole_1_th_5:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds (X \\/XBOOLE-0K2 Y)\\/XBOOLE-0K2 Z =XBOOLE-0R4 (X \\/XBOOLE-0K2 Z)\\/XBOOLE-0K2 (Y \\/XBOOLE-0K2 Z)"
sorry

mtheorem xboole_1_th_6:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X \\/XBOOLE-0K2 (X \\/XBOOLE-0K2 Y) =XBOOLE-0R4 X \\/XBOOLE-0K2 Y"
sorry

mtheorem xboole_1_th_7:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X c=TARSKIR1 X \\/XBOOLE-0K2 Y"
  using xboole_0_def_3 sorry

mtheorem xboole_1_th_8:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds X c=TARSKIR1 Z & Y c=TARSKIR1 Z implies X \\/XBOOLE-0K2 Y c=TARSKIR1 Z"
sorry

mtheorem xboole_1_th_9:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds X c=TARSKIR1 Y implies X \\/XBOOLE-0K2 Z c=TARSKIR1 Y \\/XBOOLE-0K2 Z"
sorry

mtheorem xboole_1_th_10:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds X c=TARSKIR1 Y implies X c=TARSKIR1 Z \\/XBOOLE-0K2 Y"
sorry

mtheorem xboole_1_th_11:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds X \\/XBOOLE-0K2 Y c=TARSKIR1 Z implies X c=TARSKIR1 Z"
sorry

mtheorem xboole_1_th_12:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X c=TARSKIR1 Y implies X \\/XBOOLE-0K2 Y =XBOOLE-0R4 Y"
sorry

mtheorem xboole_1_th_13:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds  for V be setHIDDENM2 holds X c=TARSKIR1 Y & Z c=TARSKIR1 V implies X \\/XBOOLE-0K2 Z c=TARSKIR1 Y \\/XBOOLE-0K2 V"
sorry

mtheorem xboole_1_th_14:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds (Y c=TARSKIR1 X & Z c=TARSKIR1 X) & ( for V be setHIDDENM2 holds Y c=TARSKIR1 V & Z c=TARSKIR1 V implies X c=TARSKIR1 V) implies X =XBOOLE-0R4 Y \\/XBOOLE-0K2 Z"
sorry

mtheorem xboole_1_th_15:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X \\/XBOOLE-0K2 Y =XBOOLE-0R4 {}XBOOLE-0K1 implies X =XBOOLE-0R4 {}XBOOLE-0K1"
   sorry

mtheorem xboole_1_th_16:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds (X /\\XBOOLE-0K3 Y)/\\XBOOLE-0K3 Z =XBOOLE-0R4 X /\\XBOOLE-0K3 (Y /\\XBOOLE-0K3 Z)"
sorry

mtheorem xboole_1_th_17:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X /\\XBOOLE-0K3 Y c=TARSKIR1 X"
  using xboole_0_def_4 sorry

mtheorem xboole_1_th_18:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds X c=TARSKIR1 Y /\\XBOOLE-0K3 Z implies X c=TARSKIR1 Y"
sorry

mtheorem xboole_1_th_19:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds Z c=TARSKIR1 X & Z c=TARSKIR1 Y implies Z c=TARSKIR1 X /\\XBOOLE-0K3 Y"
sorry

mtheorem xboole_1_th_20:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds (X c=TARSKIR1 Y & X c=TARSKIR1 Z) & ( for V be setHIDDENM2 holds V c=TARSKIR1 Y & V c=TARSKIR1 Z implies V c=TARSKIR1 X) implies X =XBOOLE-0R4 Y /\\XBOOLE-0K3 Z"
sorry

mtheorem xboole_1_th_21:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X /\\XBOOLE-0K3 (X \\/XBOOLE-0K2 Y) =XBOOLE-0R4 X"
sorry

mtheorem xboole_1_th_22:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X \\/XBOOLE-0K2 X /\\XBOOLE-0K3 Y =XBOOLE-0R4 X"
sorry

mtheorem xboole_1_th_23:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds X /\\XBOOLE-0K3 (Y \\/XBOOLE-0K2 Z) =XBOOLE-0R4 X /\\XBOOLE-0K3 Y \\/XBOOLE-0K2 X /\\XBOOLE-0K3 Z"
sorry

mtheorem xboole_1_th_24:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds X \\/XBOOLE-0K2 Y /\\XBOOLE-0K3 Z =XBOOLE-0R4 (X \\/XBOOLE-0K2 Y)/\\XBOOLE-0K3 (X \\/XBOOLE-0K2 Z)"
sorry

mtheorem xboole_1_th_25:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds (X /\\XBOOLE-0K3 Y \\/XBOOLE-0K2 Y /\\XBOOLE-0K3 Z)\\/XBOOLE-0K2 Z /\\XBOOLE-0K3 X =XBOOLE-0R4 ((X \\/XBOOLE-0K2 Y)/\\XBOOLE-0K3 (Y \\/XBOOLE-0K2 Z))/\\XBOOLE-0K3 (Z \\/XBOOLE-0K2 X)"
sorry

mtheorem xboole_1_th_26:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds X c=TARSKIR1 Y implies X /\\XBOOLE-0K3 Z c=TARSKIR1 Y /\\XBOOLE-0K3 Z"
sorry

mtheorem xboole_1_th_27:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds  for V be setHIDDENM2 holds X c=TARSKIR1 Y & Z c=TARSKIR1 V implies X /\\XBOOLE-0K3 Z c=TARSKIR1 Y /\\XBOOLE-0K3 V"
sorry

mtheorem xboole_1_th_28:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X c=TARSKIR1 Y implies X /\\XBOOLE-0K3 Y =XBOOLE-0R4 X"
sorry

mtheorem xboole_1_th_29:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds X /\\XBOOLE-0K3 Y c=TARSKIR1 X \\/XBOOLE-0K2 Z"
sorry

mtheorem xboole_1_th_30:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds X c=TARSKIR1 Z implies X \\/XBOOLE-0K2 Y /\\XBOOLE-0K3 Z =XBOOLE-0R4 (X \\/XBOOLE-0K2 Y)/\\XBOOLE-0K3 Z"
sorry

mtheorem xboole_1_th_31:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds X /\\XBOOLE-0K3 Y \\/XBOOLE-0K2 X /\\XBOOLE-0K3 Z c=TARSKIR1 Y \\/XBOOLE-0K2 Z"
sorry

mlemma xboole_1_lm_1:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X \\XBOOLE-0K4 Y =XBOOLE-0R4 {}XBOOLE-0K1 iff X c=TARSKIR1 Y"
sorry

mtheorem xboole_1_th_32:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X \\XBOOLE-0K4 Y =XBOOLE-0R4 Y \\XBOOLE-0K4 X implies X =XBOOLE-0R4 Y"
sorry

mtheorem xboole_1_th_33:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds X c=TARSKIR1 Y implies X \\XBOOLE-0K4 Z c=TARSKIR1 Y \\XBOOLE-0K4 Z"
sorry

mtheorem xboole_1_th_34:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds X c=TARSKIR1 Y implies Z \\XBOOLE-0K4 Y c=TARSKIR1 Z \\XBOOLE-0K4 X"
sorry

mlemma xboole_1_lm_2:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds X \\XBOOLE-0K4 Y /\\XBOOLE-0K3 Z =XBOOLE-0R4 (X \\XBOOLE-0K4 Y)\\/XBOOLE-0K2 (X \\XBOOLE-0K4 Z)"
sorry

mtheorem xboole_1_th_35:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds  for V be setHIDDENM2 holds X c=TARSKIR1 Y & Z c=TARSKIR1 V implies X \\XBOOLE-0K4 V c=TARSKIR1 Y \\XBOOLE-0K4 Z"
sorry

mtheorem xboole_1_th_36:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X \\XBOOLE-0K4 Y c=TARSKIR1 X"
  using xboole_0_def_5 sorry

mtheorem xboole_1_th_37:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X \\XBOOLE-0K4 Y =XBOOLE-0R4 {}XBOOLE-0K1 iff X c=TARSKIR1 Y"
  using xboole_1_lm_1 sorry

mtheorem xboole_1_th_38:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X c=TARSKIR1 Y \\XBOOLE-0K4 X implies X =XBOOLE-0R4 {}XBOOLE-0K1"
sorry

mtheorem xboole_1_th_39:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X \\/XBOOLE-0K2 (Y \\XBOOLE-0K4 X) =XBOOLE-0R4 X \\/XBOOLE-0K2 Y"
sorry

mtheorem xboole_1_th_40:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds (X \\/XBOOLE-0K2 Y)\\XBOOLE-0K4 Y =XBOOLE-0R4 X \\XBOOLE-0K4 Y"
sorry

mtheorem xboole_1_th_41:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds (X \\XBOOLE-0K4 Y)\\XBOOLE-0K4 Z =XBOOLE-0R4 X \\XBOOLE-0K4 (Y \\/XBOOLE-0K2 Z)"
sorry

mtheorem xboole_1_th_42:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds (X \\/XBOOLE-0K2 Y)\\XBOOLE-0K4 Z =XBOOLE-0R4 (X \\XBOOLE-0K4 Z)\\/XBOOLE-0K2 (Y \\XBOOLE-0K4 Z)"
sorry

mtheorem xboole_1_th_43:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds X c=TARSKIR1 Y \\/XBOOLE-0K2 Z implies X \\XBOOLE-0K4 Y c=TARSKIR1 Z"
sorry

mtheorem xboole_1_th_44:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds X \\XBOOLE-0K4 Y c=TARSKIR1 Z implies X c=TARSKIR1 Y \\/XBOOLE-0K2 Z"
sorry

mtheorem xboole_1_th_45:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X c=TARSKIR1 Y implies Y =XBOOLE-0R4 X \\/XBOOLE-0K2 (Y \\XBOOLE-0K4 X)"
sorry

mtheorem xboole_1_th_46:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X \\XBOOLE-0K4 (X \\/XBOOLE-0K2 Y) =XBOOLE-0R4 {}XBOOLE-0K1"
  using xboole_1_th_7 xboole_1_lm_1 sorry

mtheorem xboole_1_th_47:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X \\XBOOLE-0K4 X /\\XBOOLE-0K3 Y =XBOOLE-0R4 X \\XBOOLE-0K4 Y"
sorry

mtheorem xboole_1_th_48:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X \\XBOOLE-0K4 (X \\XBOOLE-0K4 Y) =XBOOLE-0R4 X /\\XBOOLE-0K3 Y"
sorry

mtheorem xboole_1_th_49:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds X /\\XBOOLE-0K3 (Y \\XBOOLE-0K4 Z) =XBOOLE-0R4 X /\\XBOOLE-0K3 Y \\XBOOLE-0K4 Z"
sorry

mtheorem xboole_1_th_50:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds X /\\XBOOLE-0K3 (Y \\XBOOLE-0K4 Z) =XBOOLE-0R4 X /\\XBOOLE-0K3 Y \\XBOOLE-0K4 X /\\XBOOLE-0K3 Z"
sorry

mtheorem xboole_1_th_51:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X /\\XBOOLE-0K3 Y \\/XBOOLE-0K2 (X \\XBOOLE-0K4 Y) =XBOOLE-0R4 X"
sorry

mtheorem xboole_1_th_52:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds X \\XBOOLE-0K4 (Y \\XBOOLE-0K4 Z) =XBOOLE-0R4 (X \\XBOOLE-0K4 Y)\\/XBOOLE-0K2 X /\\XBOOLE-0K3 Z"
sorry

mtheorem xboole_1_th_53:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds X \\XBOOLE-0K4 (Y \\/XBOOLE-0K2 Z) =XBOOLE-0R4 (X \\XBOOLE-0K4 Y)/\\XBOOLE-0K3 (X \\XBOOLE-0K4 Z)"
sorry

mtheorem xboole_1_th_54:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds X \\XBOOLE-0K4 Y /\\XBOOLE-0K3 Z =XBOOLE-0R4 (X \\XBOOLE-0K4 Y)\\/XBOOLE-0K2 (X \\XBOOLE-0K4 Z)"
  using xboole_1_lm_2 sorry

mtheorem xboole_1_th_55:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds (X \\/XBOOLE-0K2 Y)\\XBOOLE-0K4 X /\\XBOOLE-0K3 Y =XBOOLE-0R4 (X \\XBOOLE-0K4 Y)\\/XBOOLE-0K2 (Y \\XBOOLE-0K4 X)"
sorry

mlemma xboole_1_lm_3:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds X c=TARSKIR1 Y & Y c<XBOOLE-0R2 Z implies X c<XBOOLE-0R2 Z"
sorry

mtheorem xboole_1_th_56:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds X c<XBOOLE-0R2 Y & Y c<XBOOLE-0R2 Z implies X c<XBOOLE-0R2 Z"
  using xboole_1_lm_3 sorry

mtheorem xboole_1_th_57:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  not (X c<XBOOLE-0R2 Y & Y c<XBOOLE-0R2 X)"
   sorry

mtheorem xboole_1_th_58:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds X c<XBOOLE-0R2 Y & Y c=TARSKIR1 Z implies X c<XBOOLE-0R2 Z"
sorry

mtheorem xboole_1_th_59:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds X c=TARSKIR1 Y & Y c<XBOOLE-0R2 Z implies X c<XBOOLE-0R2 Z"
  using xboole_1_lm_3 sorry

mtheorem xboole_1_th_60:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X c=TARSKIR1 Y implies  not Y c<XBOOLE-0R2 X"
sorry

mtheorem xboole_1_th_61:
" for X be setHIDDENM2 holds X <>HIDDENR2 {}XBOOLE-0K1 implies {}XBOOLE-0K1 c<XBOOLE-0R2 X"
sorry

mtheorem xboole_1_th_62:
" for X be setHIDDENM2 holds  not X c<XBOOLE-0R2 {}XBOOLE-0K1"
  using xboole_1_th_3 sorry

(*\$N Modus Celarent*)
(*\$N Modus Darii*)
mtheorem xboole_1_th_63:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds X c=TARSKIR1 Y & Y missesXBOOLE-0R1 Z implies X missesXBOOLE-0R1 Z"
  using xboole_1_th_3 xboole_1_th_26 sorry

mtheorem xboole_1_th_64:
" for A be setHIDDENM2 holds  for B be setHIDDENM2 holds  for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds (A c=TARSKIR1 X & B c=TARSKIR1 Y) & X missesXBOOLE-0R1 Y implies A missesXBOOLE-0R1 B"
sorry

mtheorem xboole_1_th_65:
" for X be setHIDDENM2 holds X missesXBOOLE-0R1 {}XBOOLE-0K1"
   sorry

mtheorem xboole_1_th_66:
" for X be setHIDDENM2 holds X meetsXBOOLE-0R5 X iff X <>HIDDENR2 {}XBOOLE-0K1"
   sorry

mtheorem xboole_1_th_67:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds (X c=TARSKIR1 Y & X c=TARSKIR1 Z) & Y missesXBOOLE-0R1 Z implies X =XBOOLE-0R4 {}XBOOLE-0K1"
  using xboole_1_th_3 xboole_1_th_19 sorry

(*\$N Modus Darapti*)
mtheorem xboole_1_th_68:
" for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds  for A be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds A c=TARSKIR1 Y & A c=TARSKIR1 Z implies Y meetsXBOOLE-0R5 Z"
sorry

mtheorem xboole_1_th_69:
" for Y be setHIDDENM2 holds  for A be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds A c=TARSKIR1 Y implies A meetsXBOOLE-0R5 Y"
  using xboole_1_th_68 sorry

mtheorem xboole_1_th_70:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds X meetsXBOOLE-0R5 Y \\/XBOOLE-0K2 Z iff X meetsXBOOLE-0R5 Y or X meetsXBOOLE-0R5 Z"
sorry

mtheorem xboole_1_th_71:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds (X \\/XBOOLE-0K2 Y =XBOOLE-0R4 Z \\/XBOOLE-0K2 Y & X missesXBOOLE-0R1 Y) & Z missesXBOOLE-0R1 Y implies X =XBOOLE-0R4 Z"
sorry

mtheorem xboole_1_th_72:
" for X be setHIDDENM2 holds  for X9 be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Y9 be setHIDDENM2 holds (X9 \\/XBOOLE-0K2 Y9 =XBOOLE-0R4 X \\/XBOOLE-0K2 Y & X missesXBOOLE-0R1 X9) & Y missesXBOOLE-0R1 Y9 implies X =XBOOLE-0R4 Y9"
sorry

mtheorem xboole_1_th_73:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds X c=TARSKIR1 Y \\/XBOOLE-0K2 Z & X missesXBOOLE-0R1 Z implies X c=TARSKIR1 Y"
sorry

mtheorem xboole_1_th_74:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds X meetsXBOOLE-0R5 Y /\\XBOOLE-0K3 Z implies X meetsXBOOLE-0R5 Y"
sorry

mtheorem xboole_1_th_75:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X meetsXBOOLE-0R5 Y implies X /\\XBOOLE-0K3 Y meetsXBOOLE-0R5 Y"
sorry

mtheorem xboole_1_th_76:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds Y missesXBOOLE-0R1 Z implies X /\\XBOOLE-0K3 Y missesXBOOLE-0R1 X /\\XBOOLE-0K3 Z"
sorry

mtheorem xboole_1_th_77:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds X meetsXBOOLE-0R5 Y & X c=TARSKIR1 Z implies X meetsXBOOLE-0R5 Y /\\XBOOLE-0K3 Z"
sorry

mtheorem xboole_1_th_78:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds X missesXBOOLE-0R1 Y implies X /\\XBOOLE-0K3 (Y \\/XBOOLE-0K2 Z) =XBOOLE-0R4 X /\\XBOOLE-0K3 Z"
sorry

mtheorem xboole_1_th_79:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X \\XBOOLE-0K4 Y missesXBOOLE-0R1 Y"
sorry

mtheorem xboole_1_th_80:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds X missesXBOOLE-0R1 Y implies X missesXBOOLE-0R1 Y \\XBOOLE-0K4 Z"
sorry

mtheorem xboole_1_th_81:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds X missesXBOOLE-0R1 Y \\XBOOLE-0K4 Z implies Y missesXBOOLE-0R1 X \\XBOOLE-0K4 Z"
sorry

mtheorem xboole_1_th_82:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X \\XBOOLE-0K4 Y missesXBOOLE-0R1 Y \\XBOOLE-0K4 X"
sorry

mtheorem xboole_1_th_83:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X missesXBOOLE-0R1 Y iff X \\XBOOLE-0K4 Y =XBOOLE-0R4 X"
sorry

mtheorem xboole_1_th_84:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds X meetsXBOOLE-0R5 Y & X missesXBOOLE-0R1 Z implies X meetsXBOOLE-0R5 Y \\XBOOLE-0K4 Z"
sorry

mtheorem xboole_1_th_85:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds X c=TARSKIR1 Y implies X missesXBOOLE-0R1 Z \\XBOOLE-0K4 Y"
sorry

mtheorem xboole_1_th_86:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds X c=TARSKIR1 Y & X missesXBOOLE-0R1 Z implies X c=TARSKIR1 Y \\XBOOLE-0K4 Z"
sorry

mtheorem xboole_1_th_87:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds Y missesXBOOLE-0R1 Z implies (X \\XBOOLE-0K4 Y)\\/XBOOLE-0K2 Z =XBOOLE-0R4 (X \\/XBOOLE-0K2 Z)\\XBOOLE-0K4 Y"
sorry

mtheorem xboole_1_th_88:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X missesXBOOLE-0R1 Y implies (X \\/XBOOLE-0K2 Y)\\XBOOLE-0K4 Y =XBOOLE-0R4 X"
sorry

mtheorem xboole_1_th_89:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X /\\XBOOLE-0K3 Y missesXBOOLE-0R1 X \\XBOOLE-0K4 Y"
sorry

mtheorem xboole_1_th_90:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X \\XBOOLE-0K4 X /\\XBOOLE-0K3 Y missesXBOOLE-0R1 Y"
sorry

mtheorem xboole_1_th_91:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds (X \\+\\XBOOLE-0K5 Y)\\+\\XBOOLE-0K5 Z =XBOOLE-0R4 X \\+\\XBOOLE-0K5 (Y \\+\\XBOOLE-0K5 Z)"
sorry

mtheorem xboole_1_th_92:
" for X be setHIDDENM2 holds X \\+\\XBOOLE-0K5 X =XBOOLE-0R4 {}XBOOLE-0K1"
  using xboole_1_lm_1 sorry

mtheorem xboole_1_th_93:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X \\/XBOOLE-0K2 Y =XBOOLE-0R4 (X \\+\\XBOOLE-0K5 Y)\\/XBOOLE-0K2 X /\\XBOOLE-0K3 Y"
sorry

mlemma xboole_1_lm_4:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X /\\XBOOLE-0K3 Y missesXBOOLE-0R1 X \\+\\XBOOLE-0K5 Y"
sorry

mlemma xboole_1_lm_5:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X \\+\\XBOOLE-0K5 Y =XBOOLE-0R4 (X \\/XBOOLE-0K2 Y)\\XBOOLE-0K4 X /\\XBOOLE-0K3 Y"
sorry

mtheorem xboole_1_th_94:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X \\/XBOOLE-0K2 Y =XBOOLE-0R4 (X \\+\\XBOOLE-0K5 Y)\\+\\XBOOLE-0K5 X /\\XBOOLE-0K3 Y"
sorry

mtheorem xboole_1_th_95:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X /\\XBOOLE-0K3 Y =XBOOLE-0R4 (X \\+\\XBOOLE-0K5 Y)\\+\\XBOOLE-0K5 X \\/XBOOLE-0K2 Y"
sorry

mtheorem xboole_1_th_96:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X \\XBOOLE-0K4 Y c=TARSKIR1 X \\+\\XBOOLE-0K5 Y"
  using xboole_1_th_7 sorry

mtheorem xboole_1_th_97:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds X \\XBOOLE-0K4 Y c=TARSKIR1 Z & Y \\XBOOLE-0K4 X c=TARSKIR1 Z implies X \\+\\XBOOLE-0K5 Y c=TARSKIR1 Z"
  using xboole_1_th_8 sorry

mtheorem xboole_1_th_98:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X \\/XBOOLE-0K2 Y =XBOOLE-0R4 X \\+\\XBOOLE-0K5 Y \\XBOOLE-0K4 X"
sorry

mtheorem xboole_1_th_99:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds (X \\+\\XBOOLE-0K5 Y)\\XBOOLE-0K4 Z =XBOOLE-0R4 (X \\XBOOLE-0K4 (Y \\/XBOOLE-0K2 Z))\\/XBOOLE-0K2 (Y \\XBOOLE-0K4 (X \\/XBOOLE-0K2 Z))"
sorry

mtheorem xboole_1_th_100:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X \\XBOOLE-0K4 Y =XBOOLE-0R4 X \\+\\XBOOLE-0K5 X /\\XBOOLE-0K3 Y"
sorry

mtheorem xboole_1_th_101:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X \\+\\XBOOLE-0K5 Y =XBOOLE-0R4 (X \\/XBOOLE-0K2 Y)\\XBOOLE-0K4 X /\\XBOOLE-0K3 Y"
  using xboole_1_lm_5 sorry

mtheorem xboole_1_th_102:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds X \\XBOOLE-0K4 (Y \\+\\XBOOLE-0K5 Z) =XBOOLE-0R4 (X \\XBOOLE-0K4 (Y \\/XBOOLE-0K2 Z))\\/XBOOLE-0K2 (X /\\XBOOLE-0K3 Y)/\\XBOOLE-0K3 Z"
sorry

mtheorem xboole_1_th_103:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X /\\XBOOLE-0K3 Y missesXBOOLE-0R1 X \\+\\XBOOLE-0K5 Y"
  using xboole_1_lm_4 sorry

mtheorem xboole_1_th_104:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds (X c<XBOOLE-0R2 Y or X =XBOOLE-0R4 Y) or Y c<XBOOLE-0R2 X iff (X,Y)are-c=-comparableXBOOLE-0R3"
   sorry

(*begin*)
mtheorem xboole_1_th_105:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X c<XBOOLE-0R2 Y implies Y \\XBOOLE-0K4 X <>HIDDENR2 {}XBOOLE-0K1"
  using xboole_1_th_60 xboole_1_lm_1 sorry

mtheorem xboole_1_th_106:
" for A be setHIDDENM2 holds  for B be setHIDDENM2 holds  for X be setHIDDENM2 holds X c=TARSKIR1 A \\XBOOLE-0K4 B implies X c=TARSKIR1 A & X missesXBOOLE-0R1 B"
sorry

mtheorem xboole_1_th_107:
" for A be setHIDDENM2 holds  for B be setHIDDENM2 holds  for X be setHIDDENM2 holds X c=TARSKIR1 A \\+\\XBOOLE-0K5 B iff X c=TARSKIR1 A \\/XBOOLE-0K2 B & X missesXBOOLE-0R1 A /\\XBOOLE-0K3 B"
sorry

mtheorem xboole_1_th_108:
" for A be setHIDDENM2 holds  for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X c=TARSKIR1 A implies X /\\XBOOLE-0K3 Y c=TARSKIR1 A"
sorry

mtheorem xboole_1_th_109:
" for A be setHIDDENM2 holds  for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X c=TARSKIR1 A implies X \\XBOOLE-0K4 Y c=TARSKIR1 A"
sorry

mtheorem xboole_1_th_110:
" for A be setHIDDENM2 holds  for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X c=TARSKIR1 A & Y c=TARSKIR1 A implies X \\+\\XBOOLE-0K5 Y c=TARSKIR1 A"
sorry

mtheorem xboole_1_th_111:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds X /\\XBOOLE-0K3 Z \\XBOOLE-0K4 Y /\\XBOOLE-0K3 Z =XBOOLE-0R4 (X \\XBOOLE-0K4 Y)/\\XBOOLE-0K3 Z"
sorry

mtheorem xboole_1_th_112:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds X /\\XBOOLE-0K3 Z \\+\\XBOOLE-0K5 Y /\\XBOOLE-0K3 Z =XBOOLE-0R4 (X \\+\\XBOOLE-0K5 Y)/\\XBOOLE-0K3 Z"
sorry

mtheorem xboole_1_th_113:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds  for V be setHIDDENM2 holds ((X \\/XBOOLE-0K2 Y)\\/XBOOLE-0K2 Z)\\/XBOOLE-0K2 V =XBOOLE-0R4 X \\/XBOOLE-0K2 ((Y \\/XBOOLE-0K2 Z)\\/XBOOLE-0K2 V)"
sorry

mtheorem xboole_1_th_114:
" for A be setHIDDENM2 holds  for B be setHIDDENM2 holds  for C be setHIDDENM2 holds  for D be setHIDDENM2 holds (A missesXBOOLE-0R1 D & B missesXBOOLE-0R1 D) & C missesXBOOLE-0R1 D implies (A \\/XBOOLE-0K2 B)\\/XBOOLE-0K2 C missesXBOOLE-0R1 D"
sorry

(*\$CT*)
mtheorem xboole_1_th_116:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds X /\\XBOOLE-0K3 (Y /\\XBOOLE-0K3 Z) =XBOOLE-0R4 (X /\\XBOOLE-0K3 Y)/\\XBOOLE-0K3 (X /\\XBOOLE-0K3 Z)"
sorry

mtheorem xboole_1_th_117:
" for P be setHIDDENM2 holds  for G be setHIDDENM2 holds  for C be setHIDDENM2 holds C c=TARSKIR1 G implies P \\XBOOLE-0K4 C =XBOOLE-0R4 (P \\XBOOLE-0K4 G)\\/XBOOLE-0K2 P /\\XBOOLE-0K3 (G \\XBOOLE-0K4 C)"
sorry

end
