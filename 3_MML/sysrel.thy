theory sysrel
  imports relat_1
begin
(*begin*)
reserve x, y, z, t for "objectHIDDENM1"
reserve X, Y, Z, W for "setHIDDENM2"
reserve R, S, T for "RelationRELAT-1M1"
mlemma sysrel_lm_1:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X <>HIDDENR2 {}XBOOLE-0K1 & Y <>HIDDENR2 {}XBOOLE-0K1 implies domRELAT-1K1 ([:ZFMISC-1K2 X,Y :]) =XBOOLE-0R4 X & rngRELAT-1K2 ([:ZFMISC-1K2 X,Y :]) =XBOOLE-0R4 Y"
  using relat_1_th_160 sorry

mtheorem sysrel_th_1:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds domRELAT-1K1 (R /\\XBOOLE-0K3 ([:ZFMISC-1K2 X,Y :])) c=TARSKIR1 X & rngRELAT-1K2 (R /\\XBOOLE-0K3 ([:ZFMISC-1K2 X,Y :])) c=TARSKIR1 Y"
sorry

mtheorem sysrel_th_2:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds X missesXBOOLE-0R1 Y implies domRELAT-1K1 (R /\\XBOOLE-0K3 ([:ZFMISC-1K2 X,Y :])) missesXBOOLE-0R1 rngRELAT-1K2 (R /\\XBOOLE-0K3 ([:ZFMISC-1K2 X,Y :]))"
sorry

mtheorem sysrel_th_3:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds R c=RELAT-1R2 [:ZFMISC-1K2 X,Y :] implies domRELAT-1K1 R c=TARSKIR1 X & rngRELAT-1K2 R c=TARSKIR1 Y"
sorry

mtheorem sysrel_th_4:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds R c=RELAT-1R2 [:ZFMISC-1K2 X,Y :] implies R ~RELAT-1K4 c=RELAT-1R2 [:ZFMISC-1K2 Y,X :]"
sorry

mtheorem sysrel_th_5:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds ([:ZFMISC-1K2 X,Y :])~RELAT-1K4 =RELAT-1R1 [:ZFMISC-1K2 Y,X :]"
sorry

mtheorem sysrel_th_6:
" for R be RelationRELAT-1M1 holds  for S be RelationRELAT-1M1 holds  for T be RelationRELAT-1M1 holds (R \\/XBOOLE-0K2 S)*RELAT-1K6 T =RELAT-1R1 R *RELAT-1K6 T \\/XBOOLE-0K2 S *RELAT-1K6 T"
sorry

mtheorem sysrel_th_7:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds (((((X missesXBOOLE-0R1 Y & R c=RELAT-1R2 [:ZFMISC-1K2 X,Y :] \\/XBOOLE-0K2 [:ZFMISC-1K2 Y,X :]) & [TARSKIK4 x,y ] inHIDDENR3 R) & x inHIDDENR3 X implies ( not x inHIDDENR3 Y &  not y inHIDDENR3 X) & y inHIDDENR3 Y) & (((X missesXBOOLE-0R1 Y & R c=RELAT-1R2 [:ZFMISC-1K2 X,Y :] \\/XBOOLE-0K2 [:ZFMISC-1K2 Y,X :]) & [TARSKIK4 x,y ] inHIDDENR3 R) & y inHIDDENR3 Y implies ( not y inHIDDENR3 X &  not x inHIDDENR3 Y) & x inHIDDENR3 X)) & (((X missesXBOOLE-0R1 Y & R c=RELAT-1R2 [:ZFMISC-1K2 X,Y :] \\/XBOOLE-0K2 [:ZFMISC-1K2 Y,X :]) & [TARSKIK4 x,y ] inHIDDENR3 R) & x inHIDDENR3 Y implies ( not x inHIDDENR3 X &  not y inHIDDENR3 Y) & y inHIDDENR3 X)) & (((X missesXBOOLE-0R1 Y & R c=RELAT-1R2 [:ZFMISC-1K2 X,Y :] \\/XBOOLE-0K2 [:ZFMISC-1K2 Y,X :]) & [TARSKIK4 x,y ] inHIDDENR3 R) & y inHIDDENR3 X implies ( not x inHIDDENR3 X &  not y inHIDDENR3 Y) & x inHIDDENR3 Y)"
sorry

mtheorem sysrel_th_8:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds R c=RELAT-1R2 [:ZFMISC-1K2 X,Y :] implies R |RELAT-1K8 Z =RELAT-1R1 R /\\XBOOLE-0K3 ([:ZFMISC-1K2 Z,Y :]) & Z |`RELAT-1K9 R =RELAT-1R1 R /\\XBOOLE-0K3 ([:ZFMISC-1K2 X,Z :])"
sorry

mtheorem sysrel_th_9:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds  for W be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds R c=RELAT-1R2 [:ZFMISC-1K2 X,Y :] & X =XBOOLE-0R4 Z \\/XBOOLE-0K2 W implies R =RELAT-1R1 R |RELAT-1K8 Z \\/XBOOLE-0K2 R |RELAT-1K8 W"
sorry

mtheorem sysrel_th_10:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds X missesXBOOLE-0R1 Y & R c=RELAT-1R2 [:ZFMISC-1K2 X,Y :] \\/XBOOLE-0K2 [:ZFMISC-1K2 Y,X :] implies R |RELAT-1K8 X c=RELAT-1R2 [:ZFMISC-1K2 X,Y :]"
sorry

mtheorem sysrel_th_11:
" for R be RelationRELAT-1M1 holds  for S be RelationRELAT-1M1 holds R c=RELAT-1R2 S implies R ~RELAT-1K4 c=RELAT-1R2 S ~RELAT-1K4"
sorry

mlemma sysrel_lm_2:
" for X be setHIDDENM2 holds idRELAT-1K7 X c=RELAT-1R2 [:ZFMISC-1K2 X,X :]"
sorry

mtheorem sysrel_th_12:
" for X be setHIDDENM2 holds idRELAT-1K7 X *RELAT-1K6 idRELAT-1K7 X =RELAT-1R1 idRELAT-1K7 X"
sorry

mtheorem sysrel_th_13:
" for x be objectHIDDENM1 holds idRELAT-1K7 {TARSKIK1 x} =RELAT-1R1 {TARSKIK1 [TARSKIK4 x,x ] }"
sorry

mtheorem sysrel_th_14:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds (idRELAT-1K7 (X \\/XBOOLE-0K2 Y) =RELAT-1R1 idRELAT-1K7 X \\/XBOOLE-0K2 idRELAT-1K7 Y & idRELAT-1K7 (X /\\XBOOLE-0K3 Y) =RELAT-1R1 idRELAT-1K7 X /\\XBOOLE-0K3 idRELAT-1K7 Y) & idRELAT-1K7 (X \\SUBSET-1K6 Y) =RELAT-1R1 idRELAT-1K7 X \\SUBSET-1K6 idRELAT-1K7 Y"
sorry

mtheorem sysrel_th_15:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds X c=TARSKIR1 Y implies idRELAT-1K7 X c=RELAT-1R2 idRELAT-1K7 Y"
sorry

mtheorem sysrel_th_16:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds idRELAT-1K7 (X \\SUBSET-1K6 Y) \\SUBSET-1K6 idRELAT-1K7 X =RELAT-1R1 {}XBOOLE-0K1"
  using sysrel_th_15 xboole_1_th_37 sorry

mtheorem sysrel_th_17:
" for R be RelationRELAT-1M1 holds R c=RELAT-1R2 idRELAT-1K7 (domRELAT-1K1 R) implies R =RELAT-1R1 idRELAT-1K7 (domRELAT-1K1 R)"
sorry

mtheorem sysrel_th_18:
" for X be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds idRELAT-1K7 X c=RELAT-1R2 R \\/XBOOLE-0K2 R ~RELAT-1K4 implies idRELAT-1K7 X c=RELAT-1R2 R & idRELAT-1K7 X c=RELAT-1R2 R ~RELAT-1K4"
sorry

mtheorem sysrel_th_19:
" for X be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds idRELAT-1K7 X c=RELAT-1R2 R implies idRELAT-1K7 X c=RELAT-1R2 R ~RELAT-1K4"
sorry

mtheorem sysrel_th_20:
" for X be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds R c=RELAT-1R2 [:ZFMISC-1K2 X,X :] implies R \\SUBSET-1K6 idRELAT-1K7 (domRELAT-1K1 R) =RELAT-1R1 R \\SUBSET-1K6 idRELAT-1K7 X & R \\SUBSET-1K6 idRELAT-1K7 (rngRELAT-1K2 R) =RELAT-1R1 R \\SUBSET-1K6 idRELAT-1K7 X"
sorry

mtheorem sysrel_th_21:
" for X be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds (idRELAT-1K7 X *RELAT-1K6 (R \\SUBSET-1K6 idRELAT-1K7 X) =RELAT-1R1 {}XBOOLE-0K1 implies domRELAT-1K1 (R \\SUBSET-1K6 idRELAT-1K7 X) =XBOOLE-0R4 domRELAT-1K1 R \\SUBSET-1K6 X) & ((R \\SUBSET-1K6 idRELAT-1K7 X)*RELAT-1K6 idRELAT-1K7 X =RELAT-1R1 {}XBOOLE-0K1 implies rngRELAT-1K2 (R \\SUBSET-1K6 idRELAT-1K7 X) =XBOOLE-0R4 rngRELAT-1K2 R \\SUBSET-1K6 X)"
sorry

mtheorem sysrel_th_22:
" for R be RelationRELAT-1M1 holds (R c=RELAT-1R2 R *RELAT-1K6 R & R *RELAT-1K6 (R \\SUBSET-1K6 idRELAT-1K7 (rngRELAT-1K2 R)) =RELAT-1R1 {}XBOOLE-0K1 implies idRELAT-1K7 (rngRELAT-1K2 R) c=RELAT-1R2 R) & (R c=RELAT-1R2 R *RELAT-1K6 R & (R \\SUBSET-1K6 idRELAT-1K7 (domRELAT-1K1 R))*RELAT-1K6 R =RELAT-1R1 {}XBOOLE-0K1 implies idRELAT-1K7 (domRELAT-1K1 R) c=RELAT-1R2 R)"
sorry

mtheorem sysrel_th_23:
" for R be RelationRELAT-1M1 holds (R c=RELAT-1R2 R *RELAT-1K6 R & R *RELAT-1K6 (R \\SUBSET-1K6 idRELAT-1K7 (rngRELAT-1K2 R)) =RELAT-1R1 {}XBOOLE-0K1 implies R /\\XBOOLE-0K3 idRELAT-1K7 (rngRELAT-1K2 R) =RELAT-1R1 idRELAT-1K7 (rngRELAT-1K2 R)) & (R c=RELAT-1R2 R *RELAT-1K6 R & (R \\SUBSET-1K6 idRELAT-1K7 (domRELAT-1K1 R))*RELAT-1K6 R =RELAT-1R1 {}XBOOLE-0K1 implies R /\\XBOOLE-0K3 idRELAT-1K7 (domRELAT-1K1 R) =RELAT-1R1 idRELAT-1K7 (domRELAT-1K1 R))"
  using sysrel_th_22 xboole_1_th_28 sorry

mtheorem sysrel_th_24:
" for X be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds (R *RELAT-1K6 (R \\SUBSET-1K6 idRELAT-1K7 X) =RELAT-1R1 {}XBOOLE-0K1 implies R *RELAT-1K6 (R \\SUBSET-1K6 idRELAT-1K7 (rngRELAT-1K2 R)) =RELAT-1R1 {}XBOOLE-0K1) & ((R \\SUBSET-1K6 idRELAT-1K7 X)*RELAT-1K6 R =RELAT-1R1 {}XBOOLE-0K1 implies (R \\SUBSET-1K6 idRELAT-1K7 (domRELAT-1K1 R))*RELAT-1K6 R =RELAT-1R1 {}XBOOLE-0K1)"
sorry

mdef sysrel_def_1 ("CLSYSRELK1  _ " [164]164 ) where
  mlet "R be RelationRELAT-1M1"
"func CLSYSRELK1 R \<rightarrow> RelationRELAT-1M1 equals
  R /\\XBOOLE-0K3 idRELAT-1K7 (domRELAT-1K1 R)"
proof-
  (*coherence*)
    show "R /\\XBOOLE-0K3 idRELAT-1K7 (domRELAT-1K1 R) be RelationRELAT-1M1"
       sorry
qed "sorry"

mtheorem sysrel_th_25:
" for R be RelationRELAT-1M1 holds  for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds [TARSKIK4 x,y ] inHIDDENR3 CLSYSRELK1 R implies x inHIDDENR3 domRELAT-1K1 (CLSYSRELK1 R) & x =HIDDENR1 y"
sorry

mtheorem sysrel_th_26:
" for R be RelationRELAT-1M1 holds domRELAT-1K1 (CLSYSRELK1 R) =XBOOLE-0R4 rngRELAT-1K2 (CLSYSRELK1 R)"
sorry

mtheorem sysrel_th_27:
" for x be objectHIDDENM1 holds  for R be RelationRELAT-1M1 holds (((x inHIDDENR3 domRELAT-1K1 (CLSYSRELK1 R) iff x inHIDDENR3 domRELAT-1K1 R & [TARSKIK4 x,x ] inHIDDENR3 R) & (x inHIDDENR3 rngRELAT-1K2 (CLSYSRELK1 R) iff x inHIDDENR3 domRELAT-1K1 R & [TARSKIK4 x,x ] inHIDDENR3 R)) & (x inHIDDENR3 rngRELAT-1K2 (CLSYSRELK1 R) iff x inHIDDENR3 rngRELAT-1K2 R & [TARSKIK4 x,x ] inHIDDENR3 R)) & (x inHIDDENR3 domRELAT-1K1 (CLSYSRELK1 R) iff x inHIDDENR3 rngRELAT-1K2 R & [TARSKIK4 x,x ] inHIDDENR3 R)"
sorry

mtheorem sysrel_th_28:
" for R be RelationRELAT-1M1 holds CLSYSRELK1 R =RELAT-1R1 idRELAT-1K7 (domRELAT-1K1 (CLSYSRELK1 R))"
sorry

mtheorem sysrel_th_29:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for R be RelationRELAT-1M1 holds (((R *RELAT-1K6 R =RELAT-1R1 R & R *RELAT-1K6 (R \\SUBSET-1K6 CLSYSRELK1 R) =RELAT-1R1 {}XBOOLE-0K1) & [TARSKIK4 x,y ] inHIDDENR3 R) & x <>HIDDENR2 y implies x inHIDDENR3 domRELAT-1K1 R \\SUBSET-1K6 domRELAT-1K1 (CLSYSRELK1 R) & y inHIDDENR3 domRELAT-1K1 (CLSYSRELK1 R)) & (((R *RELAT-1K6 R =RELAT-1R1 R & (R \\SUBSET-1K6 CLSYSRELK1 R)*RELAT-1K6 R =RELAT-1R1 {}XBOOLE-0K1) & [TARSKIK4 x,y ] inHIDDENR3 R) & x <>HIDDENR2 y implies y inHIDDENR3 rngRELAT-1K2 R \\SUBSET-1K6 domRELAT-1K1 (CLSYSRELK1 R) & x inHIDDENR3 domRELAT-1K1 (CLSYSRELK1 R))"
sorry

mtheorem sysrel_th_30:
" for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for R be RelationRELAT-1M1 holds (((R *RELAT-1K6 R =RELAT-1R1 R & R *RELAT-1K6 (R \\SUBSET-1K6 idRELAT-1K7 (domRELAT-1K1 R)) =RELAT-1R1 {}XBOOLE-0K1) & [TARSKIK4 x,y ] inHIDDENR3 R) & x <>HIDDENR2 y implies x inHIDDENR3 domRELAT-1K1 R \\SUBSET-1K6 domRELAT-1K1 (CLSYSRELK1 R) & y inHIDDENR3 domRELAT-1K1 (CLSYSRELK1 R)) & (((R *RELAT-1K6 R =RELAT-1R1 R & (R \\SUBSET-1K6 idRELAT-1K7 (domRELAT-1K1 R))*RELAT-1K6 R =RELAT-1R1 {}XBOOLE-0K1) & [TARSKIK4 x,y ] inHIDDENR3 R) & x <>HIDDENR2 y implies y inHIDDENR3 rngRELAT-1K2 R \\SUBSET-1K6 domRELAT-1K1 (CLSYSRELK1 R) & x inHIDDENR3 domRELAT-1K1 (CLSYSRELK1 R))"
sorry

mtheorem sysrel_th_31:
" for R be RelationRELAT-1M1 holds (R *RELAT-1K6 R =RELAT-1R1 R & R *RELAT-1K6 (R \\SUBSET-1K6 idRELAT-1K7 (domRELAT-1K1 R)) =RELAT-1R1 {}XBOOLE-0K1 implies domRELAT-1K1 (CLSYSRELK1 R) =XBOOLE-0R4 rngRELAT-1K2 R & rngRELAT-1K2 (CLSYSRELK1 R) =XBOOLE-0R4 rngRELAT-1K2 R) & (R *RELAT-1K6 R =RELAT-1R1 R & (R \\SUBSET-1K6 idRELAT-1K7 (domRELAT-1K1 R))*RELAT-1K6 R =RELAT-1R1 {}XBOOLE-0K1 implies domRELAT-1K1 (CLSYSRELK1 R) =XBOOLE-0R4 domRELAT-1K1 R & rngRELAT-1K2 (CLSYSRELK1 R) =XBOOLE-0R4 domRELAT-1K1 R)"
sorry

mtheorem sysrel_th_32:
" for R be RelationRELAT-1M1 holds ((domRELAT-1K1 (CLSYSRELK1 R) c=TARSKIR1 domRELAT-1K1 R & rngRELAT-1K2 (CLSYSRELK1 R) c=TARSKIR1 rngRELAT-1K2 R) & rngRELAT-1K2 (CLSYSRELK1 R) c=TARSKIR1 domRELAT-1K1 R) & domRELAT-1K1 (CLSYSRELK1 R) c=TARSKIR1 rngRELAT-1K2 R"
sorry

mtheorem sysrel_th_33:
" for R be RelationRELAT-1M1 holds idRELAT-1K7 (domRELAT-1K1 (CLSYSRELK1 R)) c=RELAT-1R2 idRELAT-1K7 (domRELAT-1K1 R) & idRELAT-1K7 (rngRELAT-1K2 (CLSYSRELK1 R)) c=RELAT-1R2 idRELAT-1K7 (domRELAT-1K1 R)"
  using sysrel_th_15 sysrel_th_32 sorry

mtheorem sysrel_th_34:
" for R be RelationRELAT-1M1 holds idRELAT-1K7 (domRELAT-1K1 (CLSYSRELK1 R)) c=RELAT-1R2 R & idRELAT-1K7 (rngRELAT-1K2 (CLSYSRELK1 R)) c=RELAT-1R2 R"
sorry

mtheorem sysrel_th_35:
" for X be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds (idRELAT-1K7 X c=RELAT-1R2 R & idRELAT-1K7 X *RELAT-1K6 (R \\SUBSET-1K6 idRELAT-1K7 X) =RELAT-1R1 {}XBOOLE-0K1 implies R |RELAT-1K8 X =RELAT-1R1 idRELAT-1K7 X) & (idRELAT-1K7 X c=RELAT-1R2 R & (R \\SUBSET-1K6 idRELAT-1K7 X)*RELAT-1K6 idRELAT-1K7 X =RELAT-1R1 {}XBOOLE-0K1 implies X |`RELAT-1K9 R =RELAT-1R1 idRELAT-1K7 X)"
sorry

mtheorem sysrel_th_36:
" for R be RelationRELAT-1M1 holds (idRELAT-1K7 (domRELAT-1K1 (CLSYSRELK1 R)) *RELAT-1K6 (R \\SUBSET-1K6 idRELAT-1K7 (domRELAT-1K1 (CLSYSRELK1 R))) =RELAT-1R1 {}XBOOLE-0K1 implies R |RELAT-1K8 domRELAT-1K1 (CLSYSRELK1 R) =RELAT-1R1 idRELAT-1K7 (domRELAT-1K1 (CLSYSRELK1 R)) & R |RELAT-1K8 rngRELAT-1K2 (CLSYSRELK1 R) =RELAT-1R1 idRELAT-1K7 (domRELAT-1K1 (CLSYSRELK1 R))) & ((R \\SUBSET-1K6 idRELAT-1K7 (rngRELAT-1K2 (CLSYSRELK1 R)))*RELAT-1K6 idRELAT-1K7 (rngRELAT-1K2 (CLSYSRELK1 R)) =RELAT-1R1 {}XBOOLE-0K1 implies domRELAT-1K1 (CLSYSRELK1 R) |`RELAT-1K9 R =RELAT-1R1 idRELAT-1K7 (domRELAT-1K1 (CLSYSRELK1 R)) & rngRELAT-1K2 (CLSYSRELK1 R) |`RELAT-1K9 R =RELAT-1R1 idRELAT-1K7 (rngRELAT-1K2 (CLSYSRELK1 R)))"
sorry

mtheorem sysrel_th_37:
" for R be RelationRELAT-1M1 holds (R *RELAT-1K6 (R \\SUBSET-1K6 idRELAT-1K7 (domRELAT-1K1 R)) =RELAT-1R1 {}XBOOLE-0K1 implies idRELAT-1K7 (domRELAT-1K1 (CLSYSRELK1 R)) *RELAT-1K6 (R \\SUBSET-1K6 idRELAT-1K7 (domRELAT-1K1 (CLSYSRELK1 R))) =RELAT-1R1 {}XBOOLE-0K1) & ((R \\SUBSET-1K6 idRELAT-1K7 (domRELAT-1K1 R))*RELAT-1K6 R =RELAT-1R1 {}XBOOLE-0K1 implies (R \\SUBSET-1K6 idRELAT-1K7 (domRELAT-1K1 (CLSYSRELK1 R)))*RELAT-1K6 idRELAT-1K7 (domRELAT-1K1 (CLSYSRELK1 R)) =RELAT-1R1 {}XBOOLE-0K1)"
sorry

mtheorem sysrel_th_38:
" for R be RelationRELAT-1M1 holds  for S be RelationRELAT-1M1 holds (S *RELAT-1K6 R =RELAT-1R1 S & R *RELAT-1K6 (R \\SUBSET-1K6 idRELAT-1K7 (domRELAT-1K1 R)) =RELAT-1R1 {}XBOOLE-0K1 implies S *RELAT-1K6 (R \\SUBSET-1K6 idRELAT-1K7 (domRELAT-1K1 R)) =RELAT-1R1 {}XBOOLE-0K1) & (R *RELAT-1K6 S =RELAT-1R1 S & (R \\SUBSET-1K6 idRELAT-1K7 (domRELAT-1K1 R))*RELAT-1K6 R =RELAT-1R1 {}XBOOLE-0K1 implies (R \\SUBSET-1K6 idRELAT-1K7 (domRELAT-1K1 R))*RELAT-1K6 S =RELAT-1R1 {}XBOOLE-0K1)"
sorry

mtheorem sysrel_th_39:
" for R be RelationRELAT-1M1 holds  for S be RelationRELAT-1M1 holds (S *RELAT-1K6 R =RELAT-1R1 S & R *RELAT-1K6 (R \\SUBSET-1K6 idRELAT-1K7 (domRELAT-1K1 R)) =RELAT-1R1 {}XBOOLE-0K1 implies CLSYSRELK1 S c=RELAT-1R2 CLSYSRELK1 R) & (R *RELAT-1K6 S =RELAT-1R1 S & (R \\SUBSET-1K6 idRELAT-1K7 (domRELAT-1K1 R))*RELAT-1K6 R =RELAT-1R1 {}XBOOLE-0K1 implies CLSYSRELK1 S c=RELAT-1R2 CLSYSRELK1 R)"
sorry

mtheorem sysrel_th_40:
" for R be RelationRELAT-1M1 holds  for S be RelationRELAT-1M1 holds (((S *RELAT-1K6 R =RELAT-1R1 S & R *RELAT-1K6 (R \\SUBSET-1K6 idRELAT-1K7 (domRELAT-1K1 R)) =RELAT-1R1 {}XBOOLE-0K1) & R *RELAT-1K6 S =RELAT-1R1 R) & S *RELAT-1K6 (S \\SUBSET-1K6 idRELAT-1K7 (domRELAT-1K1 S)) =RELAT-1R1 {}XBOOLE-0K1 implies CLSYSRELK1 S =RELAT-1R1 CLSYSRELK1 R) & (((R *RELAT-1K6 S =RELAT-1R1 S & (R \\SUBSET-1K6 idRELAT-1K7 (domRELAT-1K1 R))*RELAT-1K6 R =RELAT-1R1 {}XBOOLE-0K1) & S *RELAT-1K6 R =RELAT-1R1 R) & (S \\SUBSET-1K6 idRELAT-1K7 (domRELAT-1K1 S))*RELAT-1K6 S =RELAT-1R1 {}XBOOLE-0K1 implies CLSYSRELK1 S =RELAT-1R1 CLSYSRELK1 R)"
  using sysrel_th_39 sorry

end
