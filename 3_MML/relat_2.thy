theory relat_2
  imports relat_1
begin
(*begin*)
reserve X for "setHIDDENM2"
reserve a, b, c, x, y, z for "objectHIDDENM1"
reserve P, R for "RelationRELAT-1M1"
mdef relat_2_def_1 (" _ is-reflexive-inRELAT-2R1  _ " [50,50]50 ) where
  mlet "R be RelationRELAT-1M1", "X be setHIDDENM2"
"pred R is-reflexive-inRELAT-2R1 X means
   for x be objectHIDDENM1 holds x inHIDDENR3 X implies [TARSKIK4 x,x ] inHIDDENR3 R"..

mdef relat_2_def_2 (" _ is-irreflexive-inRELAT-2R2  _ " [50,50]50 ) where
  mlet "R be RelationRELAT-1M1", "X be setHIDDENM2"
"pred R is-irreflexive-inRELAT-2R2 X means
   for x be objectHIDDENM1 holds x inHIDDENR3 X implies  not [TARSKIK4 x,x ] inHIDDENR3 R"..

mdef relat_2_def_3 (" _ is-symmetric-inRELAT-2R3  _ " [50,50]50 ) where
  mlet "R be RelationRELAT-1M1", "X be setHIDDENM2"
"pred R is-symmetric-inRELAT-2R3 X means
   for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds (x inHIDDENR3 X & y inHIDDENR3 X) & [TARSKIK4 x,y ] inHIDDENR3 R implies [TARSKIK4 y,x ] inHIDDENR3 R"..

mdef relat_2_def_4 (" _ is-antisymmetric-inRELAT-2R4  _ " [50,50]50 ) where
  mlet "R be RelationRELAT-1M1", "X be setHIDDENM2"
"pred R is-antisymmetric-inRELAT-2R4 X means
   for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds ((x inHIDDENR3 X & y inHIDDENR3 X) & [TARSKIK4 x,y ] inHIDDENR3 R) & [TARSKIK4 y,x ] inHIDDENR3 R implies x =HIDDENR1 y"..

mdef relat_2_def_5 (" _ is-asymmetric-inRELAT-2R5  _ " [50,50]50 ) where
  mlet "R be RelationRELAT-1M1", "X be setHIDDENM2"
"pred R is-asymmetric-inRELAT-2R5 X means
   for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds (x inHIDDENR3 X & y inHIDDENR3 X) & [TARSKIK4 x,y ] inHIDDENR3 R implies  not [TARSKIK4 y,x ] inHIDDENR3 R"..

mdef relat_2_def_6 (" _ is-connected-inRELAT-2R6  _ " [50,50]50 ) where
  mlet "R be RelationRELAT-1M1", "X be setHIDDENM2"
"pred R is-connected-inRELAT-2R6 X means
   for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds (x inHIDDENR3 X & y inHIDDENR3 X) & x <>HIDDENR2 y implies [TARSKIK4 x,y ] inHIDDENR3 R or [TARSKIK4 y,x ] inHIDDENR3 R"..

mdef relat_2_def_7 (" _ is-strongly-connected-inRELAT-2R7  _ " [50,50]50 ) where
  mlet "R be RelationRELAT-1M1", "X be setHIDDENM2"
"pred R is-strongly-connected-inRELAT-2R7 X means
   for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds x inHIDDENR3 X & y inHIDDENR3 X implies [TARSKIK4 x,y ] inHIDDENR3 R or [TARSKIK4 y,x ] inHIDDENR3 R"..

mdef relat_2_def_8 (" _ is-transitive-inRELAT-2R8  _ " [50,50]50 ) where
  mlet "R be RelationRELAT-1M1", "X be setHIDDENM2"
"pred R is-transitive-inRELAT-2R8 X means
   for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for z be objectHIDDENM1 holds (((x inHIDDENR3 X & y inHIDDENR3 X) & z inHIDDENR3 X) & [TARSKIK4 x,y ] inHIDDENR3 R) & [TARSKIK4 y,z ] inHIDDENR3 R implies [TARSKIK4 x,z ] inHIDDENR3 R"..

mdef relat_2_def_9 ("reflexiveRELAT-2V1" 70 ) where
"attr reflexiveRELAT-2V1 for RelationRELAT-1M1 means
  (\<lambda>R. R is-reflexive-inRELAT-2R1 fieldRELAT-1K3 R)"..

mdef relat_2_def_10 ("irreflexiveRELAT-2V2" 70 ) where
"attr irreflexiveRELAT-2V2 for RelationRELAT-1M1 means
  (\<lambda>R. R is-irreflexive-inRELAT-2R2 fieldRELAT-1K3 R)"..

mdef relat_2_def_11 ("symmetricRELAT-2V3" 70 ) where
"attr symmetricRELAT-2V3 for RelationRELAT-1M1 means
  (\<lambda>R. R is-symmetric-inRELAT-2R3 fieldRELAT-1K3 R)"..

mdef relat_2_def_12 ("antisymmetricRELAT-2V4" 70 ) where
"attr antisymmetricRELAT-2V4 for RelationRELAT-1M1 means
  (\<lambda>R. R is-antisymmetric-inRELAT-2R4 fieldRELAT-1K3 R)"..

mdef relat_2_def_13 ("asymmetricRELAT-2V5" 70 ) where
"attr asymmetricRELAT-2V5 for RelationRELAT-1M1 means
  (\<lambda>R. R is-asymmetric-inRELAT-2R5 fieldRELAT-1K3 R)"..

mdef relat_2_def_14 ("connectedRELAT-2V6" 70 ) where
"attr connectedRELAT-2V6 for RelationRELAT-1M1 means
  (\<lambda>R. R is-connected-inRELAT-2R6 fieldRELAT-1K3 R)"..

mdef relat_2_def_15 ("strongly-connectedRELAT-2V7" 70 ) where
"attr strongly-connectedRELAT-2V7 for RelationRELAT-1M1 means
  (\<lambda>R. R is-strongly-connected-inRELAT-2R7 fieldRELAT-1K3 R)"..

mdef relat_2_def_16 ("transitiveRELAT-2V8" 70 ) where
"attr transitiveRELAT-2V8 for RelationRELAT-1M1 means
  (\<lambda>R. R is-transitive-inRELAT-2R8 fieldRELAT-1K3 R)"..

mtheorem relat_2_cl_1:
"cluster emptyXBOOLE-0V1 also-is reflexiveRELAT-2V1\<bar>irreflexiveRELAT-2V2\<bar>symmetricRELAT-2V3\<bar>antisymmetricRELAT-2V4\<bar>asymmetricRELAT-2V5\<bar>connectedRELAT-2V6\<bar>strongly-connectedRELAT-2V7\<bar>transitiveRELAT-2V8 for RelationRELAT-1M1"
proof
(*coherence*)
  show " for it be RelationRELAT-1M1 holds it be emptyXBOOLE-0V1 implies it be reflexiveRELAT-2V1\<bar>irreflexiveRELAT-2V2\<bar>symmetricRELAT-2V3\<bar>antisymmetricRELAT-2V4\<bar>asymmetricRELAT-2V5\<bar>connectedRELAT-2V6\<bar>strongly-connectedRELAT-2V7\<bar>transitiveRELAT-2V8"
sorry
qed "sorry"

mtheorem relat_2_th_1:
" for R be RelationRELAT-1M1 holds R be reflexiveRELAT-2V1 iff idRELAT-1K7 (fieldRELAT-1K3 R) c=RELAT-1R2 R"
sorry

mtheorem relat_2_th_2:
" for R be RelationRELAT-1M1 holds R be irreflexiveRELAT-2V2 iff idRELAT-1K7 (fieldRELAT-1K3 R) missesXBOOLE-0R1 R"
sorry

mtheorem relat_2_th_3:
" for X be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds R is-antisymmetric-inRELAT-2R4 X iff R \\XBOOLE-0K4 idRELAT-1K7 X is-asymmetric-inRELAT-2R5 X"
sorry

mtheorem relat_2_th_4:
" for X be setHIDDENM2 holds  for R be RelationRELAT-1M1 holds R is-asymmetric-inRELAT-2R5 X implies R \\/XBOOLE-0K2 idRELAT-1K7 X is-antisymmetric-inRELAT-2R4 X"
sorry

(*\$CT 7*)
mtheorem relat_2_cl_2:
"cluster symmetricRELAT-2V3\<bar>transitiveRELAT-2V8 also-is reflexiveRELAT-2V1 for RelationRELAT-1M1"
proof
(*coherence*)
  show " for it be RelationRELAT-1M1 holds it be symmetricRELAT-2V3\<bar>transitiveRELAT-2V8 implies it be reflexiveRELAT-2V1"
sorry
qed "sorry"

mtheorem relat_2_cl_3:
  mlet "X be setHIDDENM2"
"cluster idRELAT-1K7 X as-term-is symmetricRELAT-2V3\<bar>transitiveRELAT-2V8\<bar>antisymmetricRELAT-2V4"
proof
(*coherence*)
  show "idRELAT-1K7 X be symmetricRELAT-2V3\<bar>transitiveRELAT-2V8\<bar>antisymmetricRELAT-2V4"
sorry
qed "sorry"

mtheorem relat_2_cl_4:
"cluster irreflexiveRELAT-2V2\<bar>transitiveRELAT-2V8 also-is asymmetricRELAT-2V5 for RelationRELAT-1M1"
proof
(*coherence*)
  show " for it be RelationRELAT-1M1 holds it be irreflexiveRELAT-2V2\<bar>transitiveRELAT-2V8 implies it be asymmetricRELAT-2V5"
sorry
qed "sorry"

mtheorem relat_2_cl_5:
"cluster asymmetricRELAT-2V5 also-is irreflexiveRELAT-2V2\<bar>antisymmetricRELAT-2V4 for RelationRELAT-1M1"
proof
(*coherence*)
  show " for it be RelationRELAT-1M1 holds it be asymmetricRELAT-2V5 implies it be irreflexiveRELAT-2V2\<bar>antisymmetricRELAT-2V4"
sorry
qed "sorry"

mtheorem relat_2_cl_6:
  mlet "R be reflexiveRELAT-2V1\<bar>RelationRELAT-1M1"
"cluster R ~RELAT-1K4 as-term-is reflexiveRELAT-2V1"
proof
(*coherence*)
  show "R ~RELAT-1K4 be reflexiveRELAT-2V1"
sorry
qed "sorry"

mtheorem relat_2_cl_7:
  mlet "R be irreflexiveRELAT-2V2\<bar>RelationRELAT-1M1"
"cluster R ~RELAT-1K4 as-term-is irreflexiveRELAT-2V2"
proof
(*coherence*)
  show "R ~RELAT-1K4 be irreflexiveRELAT-2V2"
sorry
qed "sorry"

mtheorem relat_2_th_12:
" for R be RelationRELAT-1M1 holds R be reflexiveRELAT-2V1 implies domRELAT-1K1 R =XBOOLE-0R4 domRELAT-1K1 (R ~RELAT-1K4) & rngRELAT-1K2 R =XBOOLE-0R4 rngRELAT-1K2 (R ~RELAT-1K4)"
sorry

mtheorem relat_2_th_13:
" for R be RelationRELAT-1M1 holds R be symmetricRELAT-2V3 iff R =RELAT-1R1 R ~RELAT-1K4"
sorry

mtheorem relat_2_cl_8:
  mlet "P be reflexiveRELAT-2V1\<bar>RelationRELAT-1M1", "R be reflexiveRELAT-2V1\<bar>RelationRELAT-1M1"
"cluster P \\/XBOOLE-0K2 R as-term-is reflexiveRELAT-2V1"
proof
(*coherence*)
  show "P \\/XBOOLE-0K2 R be reflexiveRELAT-2V1"
sorry
qed "sorry"

mtheorem relat_2_cl_9:
  mlet "P be reflexiveRELAT-2V1\<bar>RelationRELAT-1M1", "R be reflexiveRELAT-2V1\<bar>RelationRELAT-1M1"
"cluster P /\\XBOOLE-0K3 R as-term-is reflexiveRELAT-2V1"
proof
(*coherence*)
  show "P /\\XBOOLE-0K3 R be reflexiveRELAT-2V1"
sorry
qed "sorry"

mtheorem relat_2_cl_10:
  mlet "P be irreflexiveRELAT-2V2\<bar>RelationRELAT-1M1", "R be irreflexiveRELAT-2V2\<bar>RelationRELAT-1M1"
"cluster P \\/XBOOLE-0K2 R as-term-is irreflexiveRELAT-2V2"
proof
(*coherence*)
  show "P \\/XBOOLE-0K2 R be irreflexiveRELAT-2V2"
sorry
qed "sorry"

mtheorem relat_2_cl_11:
  mlet "P be irreflexiveRELAT-2V2\<bar>RelationRELAT-1M1", "R be irreflexiveRELAT-2V2\<bar>RelationRELAT-1M1"
"cluster P /\\XBOOLE-0K3 R as-term-is irreflexiveRELAT-2V2"
proof
(*coherence*)
  show "P /\\XBOOLE-0K3 R be irreflexiveRELAT-2V2"
sorry
qed "sorry"

mtheorem relat_2_cl_12:
  mlet "P be irreflexiveRELAT-2V2\<bar>RelationRELAT-1M1", "R be RelationRELAT-1M1"
"cluster P \\XBOOLE-0K4 R as-term-is irreflexiveRELAT-2V2"
proof
(*coherence*)
  show "P \\XBOOLE-0K4 R be irreflexiveRELAT-2V2"
sorry
qed "sorry"

mtheorem relat_2_cl_13:
  mlet "R be symmetricRELAT-2V3\<bar>RelationRELAT-1M1"
"cluster R ~RELAT-1K4 as-term-is symmetricRELAT-2V3"
proof
(*coherence*)
  show "R ~RELAT-1K4 be symmetricRELAT-2V3"
    using relat_2_th_13 sorry
qed "sorry"

mtheorem relat_2_cl_14:
  mlet "P be symmetricRELAT-2V3\<bar>RelationRELAT-1M1", "R be symmetricRELAT-2V3\<bar>RelationRELAT-1M1"
"cluster P \\/XBOOLE-0K2 R as-term-is symmetricRELAT-2V3"
proof
(*coherence*)
  show "P \\/XBOOLE-0K2 R be symmetricRELAT-2V3"
sorry
qed "sorry"

mtheorem relat_2_cl_15:
  mlet "P be symmetricRELAT-2V3\<bar>RelationRELAT-1M1", "R be symmetricRELAT-2V3\<bar>RelationRELAT-1M1"
"cluster P /\\XBOOLE-0K3 R as-term-is symmetricRELAT-2V3"
proof
(*coherence*)
  show "P /\\XBOOLE-0K3 R be symmetricRELAT-2V3"
sorry
qed "sorry"

mtheorem relat_2_cl_16:
  mlet "P be symmetricRELAT-2V3\<bar>RelationRELAT-1M1", "R be symmetricRELAT-2V3\<bar>RelationRELAT-1M1"
"cluster P \\XBOOLE-0K4 R as-term-is symmetricRELAT-2V3"
proof
(*coherence*)
  show "P \\XBOOLE-0K4 R be symmetricRELAT-2V3"
sorry
qed "sorry"

mtheorem relat_2_cl_17:
  mlet "R be asymmetricRELAT-2V5\<bar>RelationRELAT-1M1"
"cluster R ~RELAT-1K4 as-term-is asymmetricRELAT-2V5"
proof
(*coherence*)
  show "R ~RELAT-1K4 be asymmetricRELAT-2V5"
sorry
qed "sorry"

mtheorem relat_2_cl_18:
  mlet "P be RelationRELAT-1M1", "R be asymmetricRELAT-2V5\<bar>RelationRELAT-1M1"
"cluster P /\\XBOOLE-0K3 R as-term-is asymmetricRELAT-2V5"
proof
(*coherence*)
  show "P /\\XBOOLE-0K3 R be asymmetricRELAT-2V5"
sorry
qed "sorry"

mtheorem relat_2_cl_19:
  mlet "P be RelationRELAT-1M1", "R be asymmetricRELAT-2V5\<bar>RelationRELAT-1M1"
"cluster R /\\XBOOLE-0K3 P as-term-is asymmetricRELAT-2V5"
proof
(*coherence*)
  show "R /\\XBOOLE-0K3 P be asymmetricRELAT-2V5"
     sorry
qed "sorry"

mtheorem relat_2_cl_20:
  mlet "P be asymmetricRELAT-2V5\<bar>RelationRELAT-1M1", "R be RelationRELAT-1M1"
"cluster P \\XBOOLE-0K4 R as-term-is asymmetricRELAT-2V5"
proof
(*coherence*)
  show "P \\XBOOLE-0K4 R be asymmetricRELAT-2V5"
sorry
qed "sorry"

(*\$CT 8*)
mtheorem relat_2_th_22:
" for R be RelationRELAT-1M1 holds R be antisymmetricRELAT-2V4 iff R /\\XBOOLE-0K3 R ~RELAT-1K4 c=RELAT-1R2 idRELAT-1K7 (domRELAT-1K1 R)"
sorry

mtheorem relat_2_cl_21:
  mlet "R be antisymmetricRELAT-2V4\<bar>RelationRELAT-1M1"
"cluster R ~RELAT-1K4 as-term-is antisymmetricRELAT-2V4"
proof
(*coherence*)
  show "R ~RELAT-1K4 be antisymmetricRELAT-2V4"
sorry
qed "sorry"

mtheorem relat_2_cl_22:
  mlet "P be antisymmetricRELAT-2V4\<bar>RelationRELAT-1M1", "R be RelationRELAT-1M1"
"cluster P /\\XBOOLE-0K3 R as-term-is antisymmetricRELAT-2V4"
proof
(*coherence*)
  show "P /\\XBOOLE-0K3 R be antisymmetricRELAT-2V4"
sorry
qed "sorry"

mtheorem relat_2_cl_23:
  mlet "P be antisymmetricRELAT-2V4\<bar>RelationRELAT-1M1", "R be RelationRELAT-1M1"
"cluster R /\\XBOOLE-0K3 P as-term-is antisymmetricRELAT-2V4"
proof
(*coherence*)
  show "R /\\XBOOLE-0K3 P be antisymmetricRELAT-2V4"
     sorry
qed "sorry"

mtheorem relat_2_cl_24:
  mlet "P be antisymmetricRELAT-2V4\<bar>RelationRELAT-1M1", "R be RelationRELAT-1M1"
"cluster P \\XBOOLE-0K4 R as-term-is antisymmetricRELAT-2V4"
proof
(*coherence*)
  show "P \\XBOOLE-0K4 R be antisymmetricRELAT-2V4"
sorry
qed "sorry"

mtheorem relat_2_cl_25:
  mlet "R be transitiveRELAT-2V8\<bar>RelationRELAT-1M1"
"cluster R ~RELAT-1K4 as-term-is transitiveRELAT-2V8"
proof
(*coherence*)
  show "R ~RELAT-1K4 be transitiveRELAT-2V8"
sorry
qed "sorry"

mtheorem relat_2_cl_26:
  mlet "P be transitiveRELAT-2V8\<bar>RelationRELAT-1M1", "R be transitiveRELAT-2V8\<bar>RelationRELAT-1M1"
"cluster P /\\XBOOLE-0K3 R as-term-is transitiveRELAT-2V8"
proof
(*coherence*)
  show "P /\\XBOOLE-0K3 R be transitiveRELAT-2V8"
sorry
qed "sorry"

(*\$CT 4*)
mtheorem relat_2_th_27:
" for R be RelationRELAT-1M1 holds R be transitiveRELAT-2V8 iff R *RELAT-1K6 R c=RELAT-1R2 R"
sorry

mtheorem relat_2_th_28:
" for R be RelationRELAT-1M1 holds R be connectedRELAT-2V6 iff [:ZFMISC-1K2 fieldRELAT-1K3 R,fieldRELAT-1K3 R :] \\XBOOLE-0K4 idRELAT-1K7 (fieldRELAT-1K3 R) c=RELAT-1R2 R \\/XBOOLE-0K2 R ~RELAT-1K4"
sorry

mtheorem relat_2_cl_27:
"cluster strongly-connectedRELAT-2V7 also-is connectedRELAT-2V6\<bar>reflexiveRELAT-2V1 for RelationRELAT-1M1"
proof
(*coherence*)
  show " for it be RelationRELAT-1M1 holds it be strongly-connectedRELAT-2V7 implies it be connectedRELAT-2V6\<bar>reflexiveRELAT-2V1"
sorry
qed "sorry"

(*\$CT*)
mtheorem relat_2_th_30:
" for R be RelationRELAT-1M1 holds R be strongly-connectedRELAT-2V7 iff [:ZFMISC-1K2 fieldRELAT-1K3 R,fieldRELAT-1K3 R :] =RELAT-1R1 R \\/XBOOLE-0K2 R ~RELAT-1K4"
sorry

mtheorem relat_2_th_31:
" for R be RelationRELAT-1M1 holds R be transitiveRELAT-2V8 iff ( for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for z be objectHIDDENM1 holds [TARSKIK4 x,y ] inHIDDENR3 R & [TARSKIK4 y,z ] inHIDDENR3 R implies [TARSKIK4 x,z ] inHIDDENR3 R)"
sorry

end
