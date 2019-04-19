theory wellset1
  imports wellord1 enumset1 xfamily
begin
(*begin*)
reserve a, b, x, y, z, z1, z2, z3, y1, y3, y4, A, B, C, D, G, M, N, X, Y, Z, W0, W00 for "setHIDDENM2"
reserve R, S, T, W, W1, W2 for "RelationRELAT-1M1"
reserve F, H, H1 for "FunctionFUNCT-1M1"
mtheorem wellset1_th_1:
" for R be RelationRELAT-1M1 holds  for x be objectHIDDENM1 holds x inHIDDENR3 fieldRELAT-1K3 R iff ( ex y be objectHIDDENM1 st [TARSKIK4 x,y ] inHIDDENR3 R or [TARSKIK4 y,x ] inHIDDENR3 R)"
sorry

mtheorem wellset1_th_2:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for W be RelationRELAT-1M1 holds (X <>HIDDENR2 {}XBOOLE-0K1 & Y <>HIDDENR2 {}XBOOLE-0K1) & W =RELAT-1R1 [:ZFMISC-1K2 X,Y :] implies fieldRELAT-1K3 W =XBOOLE-0R4 X \\/XBOOLE-0K2 Y"
sorry

theorem wellset1_sch_1:
  fixes Af0 Pp1 
  assumes
[ty]: "Af0 be setHIDDENM2"
  shows " ex B be setHIDDENM2 st  for R be RelationRELAT-1M1 holds R inTARSKIR2 B iff R inTARSKIR2 Af0 & Pp1(R)"
sorry

mtheorem wellset1_th_3:
" for x be setHIDDENM2 holds  for y be setHIDDENM2 holds  for W be RelationRELAT-1M1 holds (x inTARSKIR2 fieldRELAT-1K3 W & y inTARSKIR2 fieldRELAT-1K3 W) & W be well-orderingWELLORD1V2 implies ( not x inTARSKIR2 W -SegWELLORD1K1 y implies [TARSKIK4 y,x ] inHIDDENR3 W)"
sorry

mtheorem wellset1_th_4:
" for x be setHIDDENM2 holds  for y be setHIDDENM2 holds  for W be RelationRELAT-1M1 holds (x inTARSKIR2 fieldRELAT-1K3 W & y inTARSKIR2 fieldRELAT-1K3 W) & W be well-orderingWELLORD1V2 implies (x inTARSKIR2 W -SegWELLORD1K1 y implies  not [TARSKIK4 y,x ] inHIDDENR3 W)"
sorry

mtheorem wellset1_th_5:
" for F be FunctionFUNCT-1M1 holds  for D be setHIDDENM2 holds ( for X be setHIDDENM2 holds X inTARSKIR2 D implies  not F .FUNCT-1K1 X inTARSKIR2 X & F .FUNCT-1K1 X inTARSKIR2 unionTARSKIK3 D) implies ( ex R be RelationRELAT-1M1 st ((fieldRELAT-1K3 R c=TARSKIR1 unionTARSKIK3 D & R be well-orderingWELLORD1V2) &  not fieldRELAT-1K3 R inTARSKIR2 D) & ( for y be setHIDDENM2 holds y inTARSKIR2 fieldRELAT-1K3 R implies R -SegWELLORD1K1 y inTARSKIR2 D & F .FUNCT-1K1 R -SegWELLORD1K1 y =XBOOLE-0R4 y))"
sorry

mtheorem wellset1_th_6:
" for N be setHIDDENM2 holds  ex R be RelationRELAT-1M1 st R be well-orderingWELLORD1V2 & fieldRELAT-1K3 R =XBOOLE-0R4 N"
sorry

end
