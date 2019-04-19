theory relset_1
  imports relat_1
begin
(*begin*)
reserve A, B, X, X1, Y, Y1, Y2, Z for "setHIDDENM2"
reserve a, x, y, z for "objectHIDDENM1"
syntax RELSET_1M1 :: " Set \<Rightarrow>  Set \<Rightarrow> Ty" ("RelationRELSET-1M1-of'( _ , _ ')" [0,0]70)
translations "RelationRELSET-1M1-of(X,Y)" \<rightharpoonup> "SubsetSUBSET-1M2-of [:ZFMISC-1K2 X,Y :]"

mtheorem relset_1_cl_1:
  mlet "X be setHIDDENM2", "Y be setHIDDENM2"
"cluster note-that Relation-likeRELAT-1V1 for SubsetSUBSET-1M2-of [:ZFMISC-1K2 X,Y :]"
proof
(*coherence*)
  show " for it be SubsetSUBSET-1M2-of [:ZFMISC-1K2 X,Y :] holds it be Relation-likeRELAT-1V1"
     sorry
qed "sorry"

mtheorem relset_1_cl_2:
  mlet "X be setHIDDENM2", "Y be setHIDDENM2"
"cluster note-that X -definedRELAT-1V4\<bar>Y -valuedRELAT-1V5 for RelationRELSET-1M1-of(X,Y)"
proof
(*coherence*)
  show " for it be RelationRELSET-1M1-of(X,Y) holds it be X -definedRELAT-1V4\<bar>Y -valuedRELAT-1V5"
sorry
qed "sorry"

reserve P, R for "RelationRELSET-1M1-of(X,Y)"
syntax RELSET_1R1 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> o" (" _ c=RELSET-1R1\<^bsub>'( _ , _ ')\<^esub>  _ " [50,0,0,50]50)
translations "R c=RELSET-1R1\<^bsub>(X,Y)\<^esub> Z" \<rightharpoonup> "R c=TARSKIR1 Z"

mtheorem relset_1_def_1:
  mlet "X be setHIDDENM2", "Y be setHIDDENM2", "R be RelationRELSET-1M1-of(X,Y)", "Z be setHIDDENM2"
"redefine pred R c=RELSET-1R1\<^bsub>(X,Y)\<^esub> Z means
   for x be ElementSUBSET-1M1-of X holds  for y be ElementSUBSET-1M1-of Y holds [TARSKIK4 x,y ] inHIDDENR3 R implies [TARSKIK4 x,y ] inHIDDENR3 Z"
proof
(*compatibility*)
  show "R c=RELSET-1R1\<^bsub>(X,Y)\<^esub> Z iff ( for x be ElementSUBSET-1M1-of X holds  for y be ElementSUBSET-1M1-of Y holds [TARSKIK4 x,y ] inHIDDENR3 R implies [TARSKIK4 x,y ] inHIDDENR3 Z)"
sorry
qed "sorry"

syntax RELSET_1R2 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> o" (" _ =RELSET-1R2\<^bsub>'( _ , _ ')\<^esub>  _ " [50,0,0,50]50)
translations "P =RELSET-1R2\<^bsub>(X,Y)\<^esub> R" \<rightharpoonup> "P =HIDDENR1 R"

mtheorem relset_1_def_2:
  mlet "X be setHIDDENM2", "Y be setHIDDENM2", "P be RelationRELSET-1M1-of(X,Y)", "R be RelationRELSET-1M1-of(X,Y)"
"redefine pred P =RELSET-1R2\<^bsub>(X,Y)\<^esub> R means
   for x be ElementSUBSET-1M1-of X holds  for y be ElementSUBSET-1M1-of Y holds [TARSKIK4 x,y ] inHIDDENR3 P iff [TARSKIK4 x,y ] inHIDDENR3 R"
proof
(*compatibility*)
  show "P =RELSET-1R2\<^bsub>(X,Y)\<^esub> R iff ( for x be ElementSUBSET-1M1-of X holds  for y be ElementSUBSET-1M1-of Y holds [TARSKIK4 x,y ] inHIDDENR3 P iff [TARSKIK4 x,y ] inHIDDENR3 R)"
sorry
qed "sorry"

mtheorem relset_1_th_1:
" for A be setHIDDENM2 holds  for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for R be RelationRELSET-1M1-of(X,Y) holds A c=TARSKIR1 R implies A be RelationRELSET-1M1-of(X,Y)"
  using xboole_1_th_1 sorry

mtheorem relset_1_th_2:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for a be objectHIDDENM1 holds  for R be RelationRELSET-1M1-of(X,Y) holds a inHIDDENR3 R implies ( ex x be objectHIDDENM1 st  ex y be objectHIDDENM1 st (a =HIDDENR1 [TARSKIK4 x,y ] & x inHIDDENR3 X) & y inHIDDENR3 Y)"
sorry

mtheorem relset_1_th_3:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds x inHIDDENR3 X & y inHIDDENR3 Y implies {TARSKIK1 [TARSKIK4 x,y ] } be RelationRELSET-1M1-of(X,Y)"
  using zfmisc_1_th_31 zfmisc_1_th_87 sorry

mtheorem relset_1_th_4:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds domRELAT-1K1 R c=TARSKIR1 X & rngRELAT-1K2 R c=TARSKIR1 Y implies R be RelationRELSET-1M1-of(X,Y)"
sorry

mtheorem relset_1_th_5:
" for X be setHIDDENM2 holds  for X1 be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for R be RelationRELSET-1M1-of(X,Y) holds domRELAT-1K1 R c=TARSKIR1 X1 implies R be RelationRELSET-1M1-of(X1,Y)"
sorry

mtheorem relset_1_th_6:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Y1 be setHIDDENM2 holds  for R be RelationRELSET-1M1-of(X,Y) holds rngRELAT-1K2 R c=TARSKIR1 Y1 implies R be RelationRELSET-1M1-of(X,Y1)"
sorry

mtheorem relset_1_th_7:
" for X be setHIDDENM2 holds  for X1 be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Y1 be setHIDDENM2 holds  for R be RelationRELSET-1M1-of(X,Y) holds X c=TARSKIR1 X1 & Y c=TARSKIR1 Y1 implies R be RelationRELSET-1M1-of(X1,Y1)"
sorry

mtheorem relset_1_cl_3:
  mlet "X be setHIDDENM2", "R be X -definedRELAT-1V4\<bar>RelationRELAT-1M1", "S be X -definedRELAT-1V4\<bar>RelationRELAT-1M1"
"cluster R \\/XBOOLE-0K2 S as-term-is X -definedRELAT-1V4"
proof
(*coherence*)
  show "R \\/XBOOLE-0K2 S be X -definedRELAT-1V4"
sorry
qed "sorry"

mtheorem relset_1_cl_4:
  mlet "X be setHIDDENM2", "R be X -definedRELAT-1V4\<bar>RelationRELAT-1M1", "S be RelationRELAT-1M1"
"cluster R /\\XBOOLE-0K3 S as-term-is X -definedRELAT-1V4"
proof
(*coherence*)
  show "R /\\XBOOLE-0K3 S be X -definedRELAT-1V4"
sorry
qed "sorry"

mtheorem relset_1_cl_5:
  mlet "X be setHIDDENM2", "R be X -definedRELAT-1V4\<bar>RelationRELAT-1M1", "S be RelationRELAT-1M1"
"cluster R \\SUBSET-1K6 S as-term-is X -definedRELAT-1V4"
proof
(*coherence*)
  show "R \\SUBSET-1K6 S be X -definedRELAT-1V4"
     sorry
qed "sorry"

mtheorem relset_1_cl_6:
  mlet "X be setHIDDENM2", "R be X -valuedRELAT-1V5\<bar>RelationRELAT-1M1", "S be X -valuedRELAT-1V5\<bar>RelationRELAT-1M1"
"cluster R \\/XBOOLE-0K2 S as-term-is X -valuedRELAT-1V5"
proof
(*coherence*)
  show "R \\/XBOOLE-0K2 S be X -valuedRELAT-1V5"
sorry
qed "sorry"

mtheorem relset_1_cl_7:
  mlet "X be setHIDDENM2", "R be X -valuedRELAT-1V5\<bar>RelationRELAT-1M1", "S be RelationRELAT-1M1"
"cluster R /\\XBOOLE-0K3 S as-term-is X -valuedRELAT-1V5"
proof
(*coherence*)
  show "R /\\XBOOLE-0K3 S be X -valuedRELAT-1V5"
sorry
qed "sorry"

mtheorem relset_1_cl_8:
  mlet "X be setHIDDENM2", "R be X -valuedRELAT-1V5\<bar>RelationRELAT-1M1", "S be RelationRELAT-1M1"
"cluster R \\SUBSET-1K6 S as-term-is X -valuedRELAT-1V5"
proof
(*coherence*)
  show "R \\SUBSET-1K6 S be X -valuedRELAT-1V5"
     sorry
qed "sorry"

syntax RELSET_1K1 :: " Set \<Rightarrow>  Set \<Rightarrow> Set" ("domRELSET-1K1\<^bsub>'( _ ')\<^esub>  _ " [0,228]228)
translations "domRELSET-1K1\<^bsub>(X)\<^esub> R" \<rightharpoonup> "domRELAT-1K1 R"

mtheorem relset_1_add_1:
  mlet "X be setHIDDENM2", "R be X -definedRELAT-1V4\<bar>RelationRELAT-1M1"
"cluster domRELAT-1K1 R as-term-is SubsetSUBSET-1M2-of X"
proof
(*coherence*)
  show "domRELAT-1K1 R be SubsetSUBSET-1M2-of X"
    using relat_1_def_18 sorry
qed "sorry"

syntax RELSET_1K2 :: " Set \<Rightarrow>  Set \<Rightarrow> Set" ("rngRELSET-1K2\<^bsub>'( _ ')\<^esub>  _ " [0,228]228)
translations "rngRELSET-1K2\<^bsub>(X)\<^esub> R" \<rightharpoonup> "rngRELAT-1K2 R"

mtheorem relset_1_add_2:
  mlet "X be setHIDDENM2", "R be X -valuedRELAT-1V5\<bar>RelationRELAT-1M1"
"cluster rngRELAT-1K2 R as-term-is SubsetSUBSET-1M2-of X"
proof
(*coherence*)
  show "rngRELAT-1K2 R be SubsetSUBSET-1M2-of X"
    using relat_1_def_19 sorry
qed "sorry"

mtheorem relset_1_th_8:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for R be RelationRELSET-1M1-of(X,Y) holds fieldRELAT-1K3 R c=TARSKIR1 X \\/XBOOLE-0K2 Y"
sorry

mtheorem relset_1_th_9:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for R be RelationRELSET-1M1-of(X,Y) holds ( for x be objectHIDDENM1 holds x inHIDDENR3 X implies ( ex y be objectHIDDENM1 st [TARSKIK4 x,y ] inHIDDENR3 R)) iff domRELSET-1K1\<^bsub>(X)\<^esub> R =XBOOLE-0R4 X"
sorry

mtheorem relset_1_th_10:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for R be RelationRELSET-1M1-of(X,Y) holds ( for y be objectHIDDENM1 holds y inHIDDENR3 Y implies ( ex x be objectHIDDENM1 st [TARSKIK4 x,y ] inHIDDENR3 R)) iff rngRELSET-1K2\<^bsub>(Y)\<^esub> R =XBOOLE-0R4 Y"
sorry

syntax RELSET_1K3 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ ~RELSET-1K3\<^bsub>'( _ , _ ')\<^esub>" [228,0,0]228)
translations "R ~RELSET-1K3\<^bsub>(X,Y)\<^esub>" \<rightharpoonup> "R ~RELAT-1K4"

mtheorem relset_1_add_3:
  mlet "X be setHIDDENM2", "Y be setHIDDENM2", "R be RelationRELSET-1M1-of(X,Y)"
"cluster R ~RELAT-1K4 as-term-is RelationRELSET-1M1-of(Y,X)"
proof
(*coherence*)
  show "R ~RELAT-1K4 be RelationRELSET-1M1-of(Y,X)"
sorry
qed "sorry"

syntax RELSET_1K4 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ *RELSET-1K4\<^bsub>'( _ , _ , _ , _ ')\<^esub>  _ " [164,0,0,0,0,164]164)
translations "P *RELSET-1K4\<^bsub>(X,Y1,Y2,Z)\<^esub> R" \<rightharpoonup> "P *RELAT-1K6 R"

mtheorem relset_1_add_4:
  mlet "X be setHIDDENM2", "Y1 be setHIDDENM2", "Y2 be setHIDDENM2", "Z be setHIDDENM2", "P be RelationRELSET-1M1-of(X,Y1)", "R be RelationRELSET-1M1-of(Y2,Z)"
"cluster P *RELAT-1K6 R as-term-is RelationRELSET-1M1-of(X,Z)"
proof
(*coherence*)
  show "P *RELAT-1K6 R be RelationRELSET-1M1-of(X,Z)"
sorry
qed "sorry"

mtheorem relset_1_th_11:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for R be RelationRELSET-1M1-of(X,Y) holds domRELSET-1K1\<^bsub>(Y)\<^esub> (R ~RELSET-1K3\<^bsub>(X,Y)\<^esub>) =XBOOLE-0R4 rngRELSET-1K2\<^bsub>(Y)\<^esub> R & rngRELSET-1K2\<^bsub>(X)\<^esub> (R ~RELSET-1K3\<^bsub>(X,Y)\<^esub>) =XBOOLE-0R4 domRELSET-1K1\<^bsub>(X)\<^esub> R"
sorry

mtheorem relset_1_th_12:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds {}XBOOLE-0K1 be RelationRELSET-1M1-of(X,Y)"
  using xboole_1_th_2 sorry

mtheorem relset_1_cl_9:
  mlet "A be emptyXBOOLE-0V1\<bar>setHIDDENM2", "B be setHIDDENM2"
"cluster note-that emptyXBOOLE-0V1 for RelationRELSET-1M1-of(A,B)"
proof
(*coherence*)
  show " for it be RelationRELSET-1M1-of(A,B) holds it be emptyXBOOLE-0V1"
     sorry
qed "sorry"

mtheorem relset_1_cl_10:
  mlet "A be emptyXBOOLE-0V1\<bar>setHIDDENM2", "B be setHIDDENM2"
"cluster note-that emptyXBOOLE-0V1 for RelationRELSET-1M1-of(B,A)"
proof
(*coherence*)
  show " for it be RelationRELSET-1M1-of(B,A) holds it be emptyXBOOLE-0V1"
     sorry
qed "sorry"

mtheorem relset_1_th_13:
" for X be setHIDDENM2 holds idRELAT-1K7 X c=RELAT-1R2 [:ZFMISC-1K2 X,X :]"
sorry

mtheorem relset_1_th_14:
" for X be setHIDDENM2 holds idRELAT-1K7 X be RelationRELSET-1M1-of(X,X)"
  using relset_1_th_13 sorry

mtheorem relset_1_th_15:
" for A be setHIDDENM2 holds  for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for R be RelationRELSET-1M1-of(X,Y) holds idRELAT-1K7 A c=RELAT-1R2 R implies A c=TARSKIR1 domRELSET-1K1\<^bsub>(X)\<^esub> R & A c=TARSKIR1 rngRELSET-1K2\<^bsub>(Y)\<^esub> R"
sorry

mtheorem relset_1_th_16:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for R be RelationRELSET-1M1-of(X,Y) holds idRELAT-1K7 X c=RELAT-1R2 R implies X =XBOOLE-0R4 domRELSET-1K1\<^bsub>(X)\<^esub> R & X c=TARSKIR1 rngRELSET-1K2\<^bsub>(Y)\<^esub> R"
  using relset_1_th_15 sorry

mtheorem relset_1_th_17:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for R be RelationRELSET-1M1-of(X,Y) holds idRELAT-1K7 Y c=RELAT-1R2 R implies Y c=TARSKIR1 domRELSET-1K1\<^bsub>(X)\<^esub> R & Y =XBOOLE-0R4 rngRELSET-1K2\<^bsub>(Y)\<^esub> R"
  using relset_1_th_15 sorry

syntax RELSET_1K5 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ |RELSET-1K5\<^bsub>'( _ , _ ')\<^esub>  _ " [200,0,0,200]200)
translations "R |RELSET-1K5\<^bsub>(X,Y)\<^esub> A" \<rightharpoonup> "R |RELAT-1K8 A"

mtheorem relset_1_add_5:
  mlet "X be setHIDDENM2", "Y be setHIDDENM2", "R be RelationRELSET-1M1-of(X,Y)", "A be setHIDDENM2"
"cluster R |RELAT-1K8 A as-term-is RelationRELSET-1M1-of(X,Y)"
proof
(*coherence*)
  show "R |RELAT-1K8 A be RelationRELSET-1M1-of(X,Y)"
sorry
qed "sorry"

syntax RELSET_1K6 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ |`RELSET-1K6\<^bsub>'( _ , _ ')\<^esub>  _ " [200,0,0,200]200)
translations "B |`RELSET-1K6\<^bsub>(X,Y)\<^esub> R" \<rightharpoonup> "B |`RELAT-1K9 R"

mtheorem relset_1_add_6:
  mlet "X be setHIDDENM2", "Y be setHIDDENM2", "B be setHIDDENM2", "R be RelationRELSET-1M1-of(X,Y)"
"cluster B |`RELAT-1K9 R as-term-is RelationRELSET-1M1-of(X,Y)"
proof
(*coherence*)
  show "B |`RELAT-1K9 R be RelationRELSET-1M1-of(X,Y)"
sorry
qed "sorry"

mtheorem relset_1_th_18:
" for X be setHIDDENM2 holds  for X1 be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for R be RelationRELSET-1M1-of(X,Y) holds R |RELSET-1K5\<^bsub>(X,Y)\<^esub> X1 be RelationRELSET-1M1-of(X1,Y)"
sorry

mtheorem relset_1_th_19:
" for X be setHIDDENM2 holds  for X1 be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for R be RelationRELSET-1M1-of(X,Y) holds X c=TARSKIR1 X1 implies R |RELSET-1K5\<^bsub>(X,Y)\<^esub> X1 =RELSET-1R2\<^bsub>(X,Y)\<^esub> R"
sorry

mtheorem relset_1_th_20:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Y1 be setHIDDENM2 holds  for R be RelationRELSET-1M1-of(X,Y) holds Y1 |`RELSET-1K6\<^bsub>(X,Y)\<^esub> R be RelationRELSET-1M1-of(X,Y1)"
sorry

mtheorem relset_1_th_21:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Y1 be setHIDDENM2 holds  for R be RelationRELSET-1M1-of(X,Y) holds Y c=TARSKIR1 Y1 implies Y1 |`RELSET-1K6\<^bsub>(X,Y)\<^esub> R =RELSET-1R2\<^bsub>(X,Y)\<^esub> R"
sorry

syntax RELSET_1K7 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ .:RELSET-1K7\<^bsub>'( _ , _ ')\<^esub>  _ " [200,0,0,200]200)
translations "R .:RELSET-1K7\<^bsub>(X,Y)\<^esub> A" \<rightharpoonup> "R .:RELAT-1K10 A"

mtheorem relset_1_add_7:
  mlet "X be setHIDDENM2", "Y be setHIDDENM2", "R be RelationRELSET-1M1-of(X,Y)", "A be setHIDDENM2"
"cluster R .:RELAT-1K10 A as-term-is SubsetSUBSET-1M2-of Y"
proof
(*coherence*)
  show "R .:RELAT-1K10 A be SubsetSUBSET-1M2-of Y"
sorry
qed "sorry"

syntax RELSET_1K8 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ \<inverse>RELSET-1K8\<^bsub>'( _ , _ ')\<^esub>  _ " [228,0,0,228]228)
translations "R \<inverse>RELSET-1K8\<^bsub>(X,Y)\<^esub> A" \<rightharpoonup> "R \<inverse>RELAT-1K11 A"

mtheorem relset_1_add_8:
  mlet "X be setHIDDENM2", "Y be setHIDDENM2", "R be RelationRELSET-1M1-of(X,Y)", "A be setHIDDENM2"
"cluster R \<inverse>RELAT-1K11 A as-term-is SubsetSUBSET-1M2-of X"
proof
(*coherence*)
  show "R \<inverse>RELAT-1K11 A be SubsetSUBSET-1M2-of X"
sorry
qed "sorry"

mtheorem relset_1_th_22:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for R be RelationRELSET-1M1-of(X,Y) holds R .:RELSET-1K7\<^bsub>(X,Y)\<^esub> X =XBOOLE-0R4 rngRELSET-1K2\<^bsub>(Y)\<^esub> R & R \<inverse>RELSET-1K8\<^bsub>(X,Y)\<^esub> Y =XBOOLE-0R4 domRELSET-1K1\<^bsub>(X)\<^esub> R"
sorry

mtheorem relset_1_th_23:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for R be RelationRELSET-1M1-of(X,Y) holds R .:RELSET-1K7\<^bsub>(X,Y)\<^esub> R \<inverse>RELSET-1K8\<^bsub>(X,Y)\<^esub> Y =XBOOLE-0R4 rngRELSET-1K2\<^bsub>(Y)\<^esub> R & R \<inverse>RELSET-1K8\<^bsub>(X,Y)\<^esub> (R .:RELSET-1K7\<^bsub>(X,Y)\<^esub> X) =XBOOLE-0R4 domRELSET-1K1\<^bsub>(X)\<^esub> R"
sorry

theorem relset_1_sch_1:
  fixes Af0 Bf0 Pp2 
  assumes
[ty]: "Af0 be setHIDDENM2" and
  [ty]: "Bf0 be setHIDDENM2"
  shows " ex R be RelationRELSET-1M1-of(Af0,Bf0) st  for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds [TARSKIK4 x,y ] inHIDDENR3 R iff (x inHIDDENR3 Af0 & y inHIDDENR3 Bf0) & Pp2(x,y)"
sorry

syntax RELSET_1M2 :: " Set \<Rightarrow> Ty" ("RelationRELSET-1M2-of  _ " [70]70)
translations "RelationRELSET-1M2-of X" \<rightharpoonup> "RelationRELSET-1M1-of(X,X)"

reserve D, D1, D2, E, F for " non emptyXBOOLE-0V1\<bar>setHIDDENM2"
reserve R for "RelationRELSET-1M1-of(D,E)"
reserve x for "ElementSUBSET-1M1-of D"
reserve y for "ElementSUBSET-1M1-of E"
mtheorem relset_1_cl_11:
  mlet "D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster idRELAT-1K7 D as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "idRELAT-1K7 D be  non emptyXBOOLE-0V1"
sorry
qed "sorry"

mtheorem relset_1_th_24:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for E be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for R be RelationRELSET-1M1-of(D,E) holds  for x be ElementSUBSET-1M1-of D holds x inTARSKIR2 domRELSET-1K1\<^bsub>(D)\<^esub> R iff ( ex y be ElementSUBSET-1M1-of E st [TARSKIK4 x,y ] inHIDDENR3 R)"
sorry

mtheorem relset_1_th_25:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for E be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for R be RelationRELSET-1M1-of(D,E) holds  for y be objectHIDDENM1 holds y inHIDDENR3 rngRELSET-1K2\<^bsub>(E)\<^esub> R iff ( ex x be ElementSUBSET-1M1-of D st [TARSKIK4 x,y ] inHIDDENR3 R)"
sorry

mtheorem relset_1_th_26:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for E be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for R be RelationRELSET-1M1-of(D,E) holds domRELSET-1K1\<^bsub>(D)\<^esub> R <>HIDDENR2 {}XBOOLE-0K1 implies ( ex y be ElementSUBSET-1M1-of E st y inTARSKIR2 rngRELSET-1K2\<^bsub>(E)\<^esub> R)"
sorry

mtheorem relset_1_th_27:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for E be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for R be RelationRELSET-1M1-of(D,E) holds rngRELSET-1K2\<^bsub>(E)\<^esub> R <>HIDDENR2 {}XBOOLE-0K1 implies ( ex x be ElementSUBSET-1M1-of D st x inTARSKIR2 domRELSET-1K1\<^bsub>(D)\<^esub> R)"
sorry

mtheorem relset_1_th_28:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for E be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for F be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for P be RelationRELSET-1M1-of(D,E) holds  for R be RelationRELSET-1M1-of(E,F) holds  for x be objectHIDDENM1 holds  for z be objectHIDDENM1 holds [TARSKIK4 x,z ] inHIDDENR3 P *RELSET-1K4\<^bsub>(D,E,E,F)\<^esub> R iff ( ex y be ElementSUBSET-1M1-of E st [TARSKIK4 x,y ] inHIDDENR3 P & [TARSKIK4 y,z ] inHIDDENR3 R)"
sorry

mtheorem relset_1_th_29:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for E be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for R be RelationRELSET-1M1-of(D,E) holds  for y be ElementSUBSET-1M1-of E holds y inTARSKIR2 R .:RELSET-1K7\<^bsub>(D,E)\<^esub> D1 iff ( ex x be ElementSUBSET-1M1-of D st [TARSKIK4 x,y ] inHIDDENR3 R & x inTARSKIR2 D1)"
sorry

mtheorem relset_1_th_30:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D2 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for E be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for R be RelationRELSET-1M1-of(D,E) holds  for x be ElementSUBSET-1M1-of D holds x inTARSKIR2 R \<inverse>RELSET-1K8\<^bsub>(D,E)\<^esub> D2 iff ( ex y be ElementSUBSET-1M1-of E st [TARSKIK4 x,y ] inHIDDENR3 R & y inTARSKIR2 D2)"
sorry

theorem relset_1_sch_2:
  fixes Af0 Bf0 Pp2 
  assumes
[ty]: "Af0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
  [ty]: "Bf0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
  shows " ex R be RelationRELSET-1M1-of(Af0,Bf0) st  for x be ElementSUBSET-1M1-of Af0 holds  for y be ElementSUBSET-1M1-of Bf0 holds [TARSKIK4 x,y ] inHIDDENR3 R iff Pp2(x,y)"
sorry

(*begin*)
theorem relset_1_sch_3:
  fixes Nf0 Mf0 Ff1 
  assumes
[ty]: "Nf0 be setHIDDENM2" and
  [ty]: "Mf0 be SubsetSUBSET-1M2-of Nf0" and
  [ty_func]: "\<And> x1. x1 be objectHIDDENM1 \<Longrightarrow> Ff1(x1) be setHIDDENM2" and
   A1: " for i be ElementSUBSET-1M1-of Nf0 holds i inTARSKIR2 Mf0 implies Ff1(i) c=TARSKIR1 Mf0"
  shows " ex R be RelationRELSET-1M2-of Mf0 st  for i be ElementSUBSET-1M1-of Nf0 holds i inTARSKIR2 Mf0 implies ImRELAT-1K12(R,i) =XBOOLE-0R4 Ff1(i)"
sorry

mtheorem relset_1_th_31:
" for N be setHIDDENM2 holds  for R be RelationRELSET-1M2-of N holds  for S be RelationRELSET-1M2-of N holds ( for i be setHIDDENM2 holds i inTARSKIR2 N implies ImRELAT-1K12(R,i) =XBOOLE-0R4 ImRELAT-1K12(S,i)) implies R =RELSET-1R2\<^bsub>(N,N)\<^esub> S"
sorry

theorem relset_1_sch_4:
  fixes Af0 Bf0 Pf0 Rf0 Pp2 
  assumes
[ty]: "Af0 be setHIDDENM2" and
  [ty]: "Bf0 be setHIDDENM2" and
  [ty]: "Pf0 be RelationRELSET-1M1-of(Af0,Bf0)" and
  [ty]: "Rf0 be RelationRELSET-1M1-of(Af0,Bf0)" and
   A1: " for p be ElementSUBSET-1M1-of Af0 holds  for q be ElementSUBSET-1M1-of Bf0 holds [TARSKIK4 p,q ] inHIDDENR3 Pf0 iff Pp2(p,q)" and
   A2: " for p be ElementSUBSET-1M1-of Af0 holds  for q be ElementSUBSET-1M1-of Bf0 holds [TARSKIK4 p,q ] inHIDDENR3 Rf0 iff Pp2(p,q)"
  shows "Pf0 =RELSET-1R2\<^bsub>(Af0,Bf0)\<^esub> Rf0"
sorry

mtheorem relset_1_cl_12:
  mlet "X be setHIDDENM2", "Y be setHIDDENM2", "Z be setHIDDENM2", "f be RelationRELSET-1M1-of([:ZFMISC-1K2 X,Y :],Z)"
"cluster domRELSET-1K1\<^bsub>([:ZFMISC-1K2 X,Y :])\<^esub> f as-term-is Relation-likeRELAT-1V1"
proof
(*coherence*)
  show "domRELSET-1K1\<^bsub>([:ZFMISC-1K2 X,Y :])\<^esub> f be Relation-likeRELAT-1V1"
     sorry
qed "sorry"

mtheorem relset_1_cl_13:
  mlet "X be setHIDDENM2", "Y be setHIDDENM2", "Z be setHIDDENM2", "f be RelationRELSET-1M1-of(X,[:ZFMISC-1K2 Y,Z :])"
"cluster rngRELSET-1K2\<^bsub>([:ZFMISC-1K2 Y,Z :])\<^esub> f as-term-is Relation-likeRELAT-1V1"
proof
(*coherence*)
  show "rngRELSET-1K2\<^bsub>([:ZFMISC-1K2 Y,Z :])\<^esub> f be Relation-likeRELAT-1V1"
     sorry
qed "sorry"

mtheorem relset_1_th_32:
" for A be setHIDDENM2 holds  for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for P be RelationRELSET-1M1-of(X,Y) holds A missesXBOOLE-0R1 X implies P |RELSET-1K5\<^bsub>(X,Y)\<^esub> A =RELAT-1R1 {}XBOOLE-0K1"
sorry

mtheorem relset_1_cl_14:
  mlet "R be  non emptyXBOOLE-0V1\<bar>RelationRELAT-1M1", "Y be  non emptyXBOOLE-0V1\<bar>SubsetSUBSET-1M2-of domRELAT-1K1 R"
"cluster R |RELAT-1K8 Y as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "R |RELAT-1K8 Y be  non emptyXBOOLE-0V1"
sorry
qed "sorry"

mtheorem relset_1_cl_15:
  mlet "R be  non emptyXBOOLE-0V1\<bar>RelationRELAT-1M1", "Y be  non emptyXBOOLE-0V1\<bar>SubsetSUBSET-1M2-of domRELAT-1K1 R"
"cluster R .:RELAT-1K10 Y as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "R .:RELAT-1K10 Y be  non emptyXBOOLE-0V1"
sorry
qed "sorry"

mtheorem relset_1_cl_16:
  mlet "X be setHIDDENM2", "Y be setHIDDENM2"
"cluster emptyXBOOLE-0V1 for RelationRELSET-1M1-of(X,Y)"
proof
(*existence*)
  show " ex it be RelationRELSET-1M1-of(X,Y) st it be emptyXBOOLE-0V1"
sorry
qed "sorry"

theorem relset_1_sch_5:
  fixes Af0 Bf0 Pp2 
  assumes
[ty]: "Af0 be setHIDDENM2" and
  [ty]: "Bf0 be setHIDDENM2"
  shows " ex R be RelationRELSET-1M1-of(Af0,Bf0) st  for x be setHIDDENM2 holds  for y be setHIDDENM2 holds [TARSKIK4 x,y ] inHIDDENR3 R iff (x inTARSKIR2 Af0 & y inTARSKIR2 Bf0) & Pp2(x,y)"
sorry

end
