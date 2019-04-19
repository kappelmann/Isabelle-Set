theory grfunc_1
  imports funct_1
begin
(*begin*)
reserve X, Y for "setHIDDENM2"
reserve p, x, x1, x2, y, y1, y2, z, z1, z2 for "objectHIDDENM1"
reserve f, g, h for "FunctionFUNCT-1M1"
mtheorem grfunc_1_th_1:
" for f be FunctionFUNCT-1M1 holds  for G be setHIDDENM2 holds G c=TARSKIR1 f implies G be FunctionFUNCT-1M1"
   sorry

mtheorem grfunc_1_th_2:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds f c=RELAT-1R2 g iff domRELAT-1K1 f c=TARSKIR1 domRELAT-1K1 g & ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 f implies f .FUNCT-1K1 x =XBOOLE-0R4 g .FUNCT-1K1 x)"
sorry

mtheorem grfunc_1_th_3:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds domRELAT-1K1 f =XBOOLE-0R4 domRELAT-1K1 g & f c=RELAT-1R2 g implies f =FUNCT-1R1 g"
sorry

mlemma grfunc_1_lm_1:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for f be FunctionFUNCT-1M1 holds  for h be FunctionFUNCT-1M1 holds (rngFUNCT-1K2 f /\\XBOOLE-0K3 rngFUNCT-1K2 h =XBOOLE-0R4 {}XBOOLE-0K1 & x inHIDDENR3 domRELAT-1K1 f) & y inHIDDENR3 domRELAT-1K1 h implies f .FUNCT-1K1 x <>HIDDENR2 h .FUNCT-1K1 y"
sorry

mtheorem grfunc_1_th_4:
" for x be objectHIDDENM1 holds  for z be objectHIDDENM1 holds  for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds [TARSKIK4 x,z ] inHIDDENR3 g *FUNCT-1K3 f implies [TARSKIK4 x,f .FUNCT-1K1 x ] inHIDDENR3 f & [TARSKIK4 f .FUNCT-1K1 x,z ] inHIDDENR3 g"
sorry

mtheorem grfunc_1_th_5:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds {TARSKIK1 [TARSKIK4 x,y ] } be FunctionFUNCT-1M1"
   sorry

mlemma grfunc_1_lm_2:
" for x be objectHIDDENM1 holds  for x1 be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for y1 be objectHIDDENM1 holds [TARSKIK4 x,y ] inHIDDENR3 {TARSKIK1 [TARSKIK4 x1,y1 ] } implies x =HIDDENR1 x1 & y =HIDDENR1 y1"
sorry

mtheorem grfunc_1_th_6:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for f be FunctionFUNCT-1M1 holds f =FUNCT-1R1 {TARSKIK1 [TARSKIK4 x,y ] } implies f .FUNCT-1K1 x =HIDDENR1 y"
sorry

mtheorem grfunc_1_th_7:
" for x be objectHIDDENM1 holds  for f be FunctionFUNCT-1M1 holds domRELAT-1K1 f =XBOOLE-0R4 {TARSKIK1 x} implies f =FUNCT-1R1 {TARSKIK1 [TARSKIK4 x,f .FUNCT-1K1 x ] }"
sorry

mtheorem grfunc_1_th_8:
" for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for y1 be objectHIDDENM1 holds  for y2 be objectHIDDENM1 holds {TARSKIK2 [TARSKIK4 x1,y1 ],[TARSKIK4 x2,y2 ] } be FunctionFUNCT-1M1 iff (x1 =HIDDENR1 x2 implies y1 =HIDDENR1 y2)"
sorry

mtheorem grfunc_1_th_9:
" for f be FunctionFUNCT-1M1 holds f be one-to-oneFUNCT-1V2 iff ( for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds  for y be objectHIDDENM1 holds [TARSKIK4 x1,y ] inHIDDENR3 f & [TARSKIK4 x2,y ] inHIDDENR3 f implies x1 =HIDDENR1 x2)"
sorry

mtheorem grfunc_1_th_10:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds g c=RELAT-1R2 f & f be one-to-oneFUNCT-1V2 implies g be one-to-oneFUNCT-1V2"
sorry

mtheorem grfunc_1_cl_1:
  mlet "f be FunctionFUNCT-1M1", "X be setHIDDENM2"
"cluster f /\\XBOOLE-0K3 X as-term-is Function-likeFUNCT-1V1"
proof
(*coherence*)
  show "f /\\XBOOLE-0K3 X be Function-likeFUNCT-1V1"
    using grfunc_1_th_1 xboole_1_th_17 sorry
qed "sorry"

mtheorem grfunc_1_th_11:
" for x be objectHIDDENM1 holds  for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds x inHIDDENR3 domRELAT-1K1 (f /\\XBOOLE-0K3 g) implies (f /\\XBOOLE-0K3 g).FUNCT-1K1 x =XBOOLE-0R4 f .FUNCT-1K1 x"
sorry

mtheorem grfunc_1_th_12:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds f be one-to-oneFUNCT-1V2 implies f /\\XBOOLE-0K3 g be one-to-oneFUNCT-1V2"
  using grfunc_1_th_10 xboole_1_th_17 sorry

mtheorem grfunc_1_th_13:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds domRELAT-1K1 f missesXBOOLE-0R1 domRELAT-1K1 g implies f \\/XBOOLE-0K2 g be FunctionFUNCT-1M1"
sorry

mtheorem grfunc_1_th_14:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds  for h be FunctionFUNCT-1M1 holds f c=RELAT-1R2 h & g c=RELAT-1R2 h implies f \\/XBOOLE-0K2 g be FunctionFUNCT-1M1"
  using grfunc_1_th_1 xboole_1_th_8 sorry

mlemma grfunc_1_lm_3:
" for x be objectHIDDENM1 holds  for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds  for h be FunctionFUNCT-1M1 holds h =RELAT-1R1 f \\/XBOOLE-0K2 g implies (x inHIDDENR3 domRELAT-1K1 h iff x inHIDDENR3 domRELAT-1K1 f or x inHIDDENR3 domRELAT-1K1 g)"
sorry

mtheorem grfunc_1_th_15:
" for x be objectHIDDENM1 holds  for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds  for h be FunctionFUNCT-1M1 holds x inHIDDENR3 domRELAT-1K1 g & h =RELAT-1R1 f \\/XBOOLE-0K2 g implies h .FUNCT-1K1 x =XBOOLE-0R4 g .FUNCT-1K1 x"
sorry

mtheorem grfunc_1_th_16:
" for x be objectHIDDENM1 holds  for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds  for h be FunctionFUNCT-1M1 holds x inHIDDENR3 domRELAT-1K1 h & h =RELAT-1R1 f \\/XBOOLE-0K2 g implies h .FUNCT-1K1 x =XBOOLE-0R4 f .FUNCT-1K1 x or h .FUNCT-1K1 x =XBOOLE-0R4 g .FUNCT-1K1 x"
sorry

mtheorem grfunc_1_th_17:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds  for h be FunctionFUNCT-1M1 holds ((f be one-to-oneFUNCT-1V2 & g be one-to-oneFUNCT-1V2) & h =RELAT-1R1 f \\/XBOOLE-0K2 g) & rngFUNCT-1K2 f missesXBOOLE-0R1 rngFUNCT-1K2 g implies h be one-to-oneFUNCT-1V2"
sorry

(*\$CT 2*)
mtheorem grfunc_1_th_20:
" for f be FunctionFUNCT-1M1 holds f be one-to-oneFUNCT-1V2 implies ( for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds [TARSKIK4 y,x ] inHIDDENR3 f \<inverse>FUNCT-1K4 iff [TARSKIK4 x,y ] inHIDDENR3 f)"
sorry

mtheorem grfunc_1_th_21:
" for f be FunctionFUNCT-1M1 holds f =XBOOLE-0R4 {}XBOOLE-0K1 implies f \<inverse>FUNCT-1K4 =XBOOLE-0R4 {}XBOOLE-0K1"
sorry

mtheorem grfunc_1_th_22:
" for X be setHIDDENM2 holds  for x be objectHIDDENM1 holds  for f be FunctionFUNCT-1M1 holds x inHIDDENR3 domRELAT-1K1 f & x inHIDDENR3 X iff [TARSKIK4 x,f .FUNCT-1K1 x ] inHIDDENR3 f |RELAT-1K8 X"
sorry

mtheorem grfunc_1_th_23:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds g c=RELAT-1R2 f implies f |RELAT-1K8 domRELAT-1K1 g =FUNCT-1R1 g"
sorry

mtheorem grfunc_1_th_24:
" for Y be setHIDDENM2 holds  for x be objectHIDDENM1 holds  for f be FunctionFUNCT-1M1 holds x inHIDDENR3 domRELAT-1K1 f & f .FUNCT-1K1 x inTARSKIR2 Y iff [TARSKIK4 x,f .FUNCT-1K1 x ] inHIDDENR3 Y |`RELAT-1K9 f"
sorry

mtheorem grfunc_1_th_25:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds g c=RELAT-1R2 f & f be one-to-oneFUNCT-1V2 implies rngFUNCT-1K2 g |`RELAT-1K9 f =FUNCT-1R1 g"
sorry

mtheorem grfunc_1_th_26:
" for Y be setHIDDENM2 holds  for x be objectHIDDENM1 holds  for f be FunctionFUNCT-1M1 holds x inHIDDENR3 f \<inverse>FUNCT-1K6 Y iff [TARSKIK4 x,f .FUNCT-1K1 x ] inHIDDENR3 f & f .FUNCT-1K1 x inTARSKIR2 Y"
sorry

(*begin*)
mtheorem grfunc_1_th_27:
" for X be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds X c=TARSKIR1 domRELAT-1K1 f & f c=RELAT-1R2 g implies f |RELAT-1K8 X =FUNCT-1R1 g |RELAT-1K8 X"
sorry

mtheorem grfunc_1_th_28:
" for f be FunctionFUNCT-1M1 holds  for x be setHIDDENM2 holds x inTARSKIR2 domRELAT-1K1 f implies f |RELAT-1K8 {TARSKIK1 x} =FUNCT-1R1 {TARSKIK1 [TARSKIK4 x,f .FUNCT-1K1 x ] }"
sorry

mtheorem grfunc_1_th_29:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds  for x be setHIDDENM2 holds domRELAT-1K1 f =XBOOLE-0R4 domRELAT-1K1 g & f .FUNCT-1K1 x =XBOOLE-0R4 g .FUNCT-1K1 x implies f |RELAT-1K8 {TARSKIK1 x} =FUNCT-1R1 g |RELAT-1K8 {TARSKIK1 x}"
sorry

mtheorem grfunc_1_th_30:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds  for x be setHIDDENM2 holds  for y be setHIDDENM2 holds (domRELAT-1K1 f =XBOOLE-0R4 domRELAT-1K1 g & f .FUNCT-1K1 x =XBOOLE-0R4 g .FUNCT-1K1 x) & f .FUNCT-1K1 y =XBOOLE-0R4 g .FUNCT-1K1 y implies f |RELAT-1K8 {TARSKIK2 x,y } =FUNCT-1R1 g |RELAT-1K8 {TARSKIK2 x,y }"
sorry

mtheorem grfunc_1_th_31:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds  for x be setHIDDENM2 holds  for y be setHIDDENM2 holds  for z be setHIDDENM2 holds ((domRELAT-1K1 f =XBOOLE-0R4 domRELAT-1K1 g & f .FUNCT-1K1 x =XBOOLE-0R4 g .FUNCT-1K1 x) & f .FUNCT-1K1 y =XBOOLE-0R4 g .FUNCT-1K1 y) & f .FUNCT-1K1 z =XBOOLE-0R4 g .FUNCT-1K1 z implies f |RELAT-1K8 {ENUMSET1K1 x,y,z } =FUNCT-1R1 g |RELAT-1K8 {ENUMSET1K1 x,y,z }"
sorry

mtheorem grfunc_1_cl_2:
  mlet "f be FunctionFUNCT-1M1", "A be setHIDDENM2"
"cluster f \\SUBSET-1K6 A as-term-is Function-likeFUNCT-1V1"
proof
(*coherence*)
  show "f \\SUBSET-1K6 A be Function-likeFUNCT-1V1"
     sorry
qed "sorry"

mtheorem grfunc_1_th_32:
" for x be objectHIDDENM1 holds  for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds x inHIDDENR3 domRELAT-1K1 f \\SUBSET-1K6 domRELAT-1K1 g implies (f \\SUBSET-1K6 g).FUNCT-1K1 x =XBOOLE-0R4 f .FUNCT-1K1 x"
sorry

mtheorem grfunc_1_th_33:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds  for h be FunctionFUNCT-1M1 holds f c=RELAT-1R2 g & f c=RELAT-1R2 h implies g |RELAT-1K8 domRELAT-1K1 f =FUNCT-1R1 h |RELAT-1K8 domRELAT-1K1 f"
sorry

mtheorem grfunc_1_cl_3:
  mlet "f be FunctionFUNCT-1M1", "g be SubsetSUBSET-1M2-of f"
"cluster g -compatibleFUNCT-1V7 also-is f -compatibleFUNCT-1V7 for FunctionFUNCT-1M1"
proof
(*coherence*)
  show " for it be FunctionFUNCT-1M1 holds it be g -compatibleFUNCT-1V7 implies it be f -compatibleFUNCT-1V7"
sorry
qed "sorry"

mtheorem grfunc_1_th_34:
" for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds g c=RELAT-1R2 f implies g =FUNCT-1R1 f |RELAT-1K8 domRELAT-1K1 g"
sorry

mtheorem grfunc_1_cl_4:
  mlet "f be FunctionFUNCT-1M1", "g be f -compatibleFUNCT-1V7\<bar>FunctionFUNCT-1M1"
"cluster note-that f -compatibleFUNCT-1V7 for SubsetSUBSET-1M2-of g"
proof
(*coherence*)
  show " for it be SubsetSUBSET-1M2-of g holds it be f -compatibleFUNCT-1V7"
sorry
qed "sorry"

mtheorem grfunc_1_th_35:
" for X be setHIDDENM2 holds  for x be objectHIDDENM1 holds  for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds (g c=RELAT-1R2 f & x inHIDDENR3 X) & X /\\XBOOLE-0K3 domRELAT-1K1 f c=TARSKIR1 domRELAT-1K1 g implies f .FUNCT-1K1 x =XBOOLE-0R4 g .FUNCT-1K1 x"
sorry

end
