theory valued_0
  imports pboole membered partfun2
   "../mizar_extension/E_number"
begin
(*begin*)
mdef valued_0_def_1 ("complex-valuedVALUED-0V1" 70 ) where
"attr complex-valuedVALUED-0V1 for RelationRELAT-1M1 means
  (\<lambda>f. rngRELAT-1K2 f c=TARSKIR1 COMPLEXNUMBERSK3)"..

mdef valued_0_def_2 ("ext-real-valuedVALUED-0V2" 70 ) where
"attr ext-real-valuedVALUED-0V2 for RelationRELAT-1M1 means
  (\<lambda>f. rngRELAT-1K2 f c=TARSKIR1 ExtREALXXREAL-0K3)"..

mdef valued_0_def_3 ("real-valuedVALUED-0V3" 70 ) where
"attr real-valuedVALUED-0V3 for RelationRELAT-1M1 means
  (\<lambda>f. rngRELAT-1K2 f c=TARSKIR1 REALNUMBERSK2)"..

(*\$CD 2*)
mdef valued_0_def_6 ("natural-valuedVALUED-0V4" 70 ) where
"attr natural-valuedVALUED-0V4 for RelationRELAT-1M1 means
  (\<lambda>f. rngRELAT-1K2 f c=TARSKIR1 NATNUMBERSK1)"..

mtheorem valued_0_cl_1:
"cluster natural-valuedVALUED-0V4 also-is INTINT-1K1 -valuedRELAT-1V5 for RelationRELAT-1M1"
proof
(*coherence*)
  show " for it be RelationRELAT-1M1 holds it be natural-valuedVALUED-0V4 implies it be INTINT-1K1 -valuedRELAT-1V5"
sorry
qed "sorry"

mtheorem valued_0_cl_2:
"cluster INTINT-1K1 -valuedRELAT-1V5 also-is RATRAT-1K1 -valuedRELAT-1V5 for RelationRELAT-1M1"
proof
(*coherence*)
  show " for it be RelationRELAT-1M1 holds it be INTINT-1K1 -valuedRELAT-1V5 implies it be RATRAT-1K1 -valuedRELAT-1V5"
sorry
qed "sorry"

mtheorem valued_0_cl_3:
"cluster INTINT-1K1 -valuedRELAT-1V5 also-is real-valuedVALUED-0V3 for RelationRELAT-1M1"
proof
(*coherence*)
  show " for it be RelationRELAT-1M1 holds it be INTINT-1K1 -valuedRELAT-1V5 implies it be real-valuedVALUED-0V3"
sorry
qed "sorry"

mtheorem valued_0_cl_4:
"cluster RATRAT-1K1 -valuedRELAT-1V5 also-is real-valuedVALUED-0V3 for RelationRELAT-1M1"
proof
(*coherence*)
  show " for it be RelationRELAT-1M1 holds it be RATRAT-1K1 -valuedRELAT-1V5 implies it be real-valuedVALUED-0V3"
sorry
qed "sorry"

mtheorem valued_0_cl_5:
"cluster real-valuedVALUED-0V3 also-is ext-real-valuedVALUED-0V2 for RelationRELAT-1M1"
proof
(*coherence*)
  show " for it be RelationRELAT-1M1 holds it be real-valuedVALUED-0V3 implies it be ext-real-valuedVALUED-0V2"
sorry
qed "sorry"

mtheorem valued_0_cl_6:
"cluster real-valuedVALUED-0V3 also-is complex-valuedVALUED-0V1 for RelationRELAT-1M1"
proof
(*coherence*)
  show " for it be RelationRELAT-1M1 holds it be real-valuedVALUED-0V3 implies it be complex-valuedVALUED-0V1"
sorry
qed "sorry"

mtheorem valued_0_cl_7:
"cluster natural-valuedVALUED-0V4 also-is RATRAT-1K1 -valuedRELAT-1V5 for RelationRELAT-1M1"
proof
(*coherence*)
  show " for it be RelationRELAT-1M1 holds it be natural-valuedVALUED-0V4 implies it be RATRAT-1K1 -valuedRELAT-1V5"
sorry
qed "sorry"

mtheorem valued_0_cl_8:
"cluster natural-valuedVALUED-0V4 also-is real-valuedVALUED-0V3 for RelationRELAT-1M1"
proof
(*coherence*)
  show " for it be RelationRELAT-1M1 holds it be natural-valuedVALUED-0V4 implies it be real-valuedVALUED-0V3"
sorry
qed "sorry"

mtheorem valued_0_cl_9:
"cluster emptyXBOOLE-0V1 also-is natural-valuedVALUED-0V4 for RelationRELAT-1M1"
proof
(*coherence*)
  show " for it be RelationRELAT-1M1 holds it be emptyXBOOLE-0V1 implies it be natural-valuedVALUED-0V4"
sorry
qed "sorry"

mtheorem valued_0_cl_10:
"cluster natural-valuedVALUED-0V4 for FunctionFUNCT-1M1"
proof
(*existence*)
  show " ex it be FunctionFUNCT-1M1 st it be natural-valuedVALUED-0V4"
sorry
qed "sorry"

mtheorem valued_0_cl_11:
  mlet "R be complex-valuedVALUED-0V1\<bar>RelationRELAT-1M1"
"cluster rngRELAT-1K2 R as-term-is complex-memberedMEMBEREDV1"
proof
(*coherence*)
  show "rngRELAT-1K2 R be complex-memberedMEMBEREDV1"
sorry
qed "sorry"

mtheorem valued_0_cl_12:
  mlet "R be ext-real-valuedVALUED-0V2\<bar>RelationRELAT-1M1"
"cluster rngRELAT-1K2 R as-term-is ext-real-memberedMEMBEREDV2"
proof
(*coherence*)
  show "rngRELAT-1K2 R be ext-real-memberedMEMBEREDV2"
sorry
qed "sorry"

mtheorem valued_0_cl_13:
  mlet "R be real-valuedVALUED-0V3\<bar>RelationRELAT-1M1"
"cluster rngRELAT-1K2 R as-term-is real-memberedMEMBEREDV3"
proof
(*coherence*)
  show "rngRELAT-1K2 R be real-memberedMEMBEREDV3"
sorry
qed "sorry"

mtheorem valued_0_cl_14:
  mlet "R be RATRAT-1K1 -valuedRELAT-1V5\<bar>RelationRELAT-1M1"
"cluster rngRELSET-1K2\<^bsub>(RATRAT-1K1)\<^esub> R as-term-is rational-memberedMEMBEREDV4"
proof
(*coherence*)
  show "rngRELSET-1K2\<^bsub>(RATRAT-1K1)\<^esub> R be rational-memberedMEMBEREDV4"
     sorry
qed "sorry"

mtheorem valued_0_cl_15:
  mlet "R be INTINT-1K1 -valuedRELAT-1V5\<bar>RelationRELAT-1M1"
"cluster rngRELSET-1K2\<^bsub>(INTINT-1K1)\<^esub> R as-term-is integer-memberedMEMBEREDV5"
proof
(*coherence*)
  show "rngRELSET-1K2\<^bsub>(INTINT-1K1)\<^esub> R be integer-memberedMEMBEREDV5"
     sorry
qed "sorry"

mtheorem valued_0_cl_16:
  mlet "R be natural-valuedVALUED-0V4\<bar>RelationRELAT-1M1"
"cluster rngRELSET-1K2\<^bsub>(RATRAT-1K1)\<^esub> R as-term-is natural-memberedMEMBEREDV6"
proof
(*coherence*)
  show "rngRELSET-1K2\<^bsub>(RATRAT-1K1)\<^esub> R be natural-memberedMEMBEREDV6"
sorry
qed "sorry"

reserve x, y for "objectHIDDENM1"
reserve X for "setHIDDENM2"
reserve f for "FunctionFUNCT-1M1"
reserve R, S for "RelationRELAT-1M1"
mtheorem valued_0_th_1:
" for R be RelationRELAT-1M1 holds  for S be complex-valuedVALUED-0V1\<bar>RelationRELAT-1M1 holds R c=RELAT-1R2 S implies R be complex-valuedVALUED-0V1"
sorry

mtheorem valued_0_th_2:
" for R be RelationRELAT-1M1 holds  for S be ext-real-valuedVALUED-0V2\<bar>RelationRELAT-1M1 holds R c=RELAT-1R2 S implies R be ext-real-valuedVALUED-0V2"
sorry

mtheorem valued_0_th_3:
" for R be RelationRELAT-1M1 holds  for S be real-valuedVALUED-0V3\<bar>RelationRELAT-1M1 holds R c=RELAT-1R2 S implies R be real-valuedVALUED-0V3"
sorry

mtheorem valued_0_th_4:
" for R be RelationRELAT-1M1 holds  for S be RATRAT-1K1 -valuedRELAT-1V5\<bar>RelationRELAT-1M1 holds R c=RELAT-1R2 S implies R be RATRAT-1K1 -valuedRELAT-1V5"
   sorry

mtheorem valued_0_th_5:
" for R be RelationRELAT-1M1 holds  for S be INTINT-1K1 -valuedRELAT-1V5\<bar>RelationRELAT-1M1 holds R c=RELAT-1R2 S implies R be INTINT-1K1 -valuedRELAT-1V5"
   sorry

mtheorem valued_0_th_6:
" for R be RelationRELAT-1M1 holds  for S be natural-valuedVALUED-0V4\<bar>RelationRELAT-1M1 holds R c=RELAT-1R2 S implies R be natural-valuedVALUED-0V4"
sorry

mtheorem valued_0_cl_17:
  mlet "R be complex-valuedVALUED-0V1\<bar>RelationRELAT-1M1"
"cluster note-that complex-valuedVALUED-0V1 for SubsetSUBSET-1M2-of R"
proof
(*coherence*)
  show " for it be SubsetSUBSET-1M2-of R holds it be complex-valuedVALUED-0V1"
    using valued_0_th_1 sorry
qed "sorry"

mtheorem valued_0_cl_18:
  mlet "R be ext-real-valuedVALUED-0V2\<bar>RelationRELAT-1M1"
"cluster note-that ext-real-valuedVALUED-0V2 for SubsetSUBSET-1M2-of R"
proof
(*coherence*)
  show " for it be SubsetSUBSET-1M2-of R holds it be ext-real-valuedVALUED-0V2"
    using valued_0_th_2 sorry
qed "sorry"

mtheorem valued_0_cl_19:
  mlet "R be real-valuedVALUED-0V3\<bar>RelationRELAT-1M1"
"cluster note-that real-valuedVALUED-0V3 for SubsetSUBSET-1M2-of R"
proof
(*coherence*)
  show " for it be SubsetSUBSET-1M2-of R holds it be real-valuedVALUED-0V3"
    using valued_0_th_3 sorry
qed "sorry"

mtheorem valued_0_cl_20:
  mlet "R be RATRAT-1K1 -valuedRELAT-1V5\<bar>RelationRELAT-1M1"
"cluster note-that RATRAT-1K1 -valuedRELAT-1V5 for SubsetSUBSET-1M2-of R"
proof
(*coherence*)
  show " for it be SubsetSUBSET-1M2-of R holds it be RATRAT-1K1 -valuedRELAT-1V5"
     sorry
qed "sorry"

mtheorem valued_0_cl_21:
  mlet "R be INTINT-1K1 -valuedRELAT-1V5\<bar>RelationRELAT-1M1"
"cluster note-that INTINT-1K1 -valuedRELAT-1V5 for SubsetSUBSET-1M2-of R"
proof
(*coherence*)
  show " for it be SubsetSUBSET-1M2-of R holds it be INTINT-1K1 -valuedRELAT-1V5"
     sorry
qed "sorry"

mtheorem valued_0_cl_22:
  mlet "R be natural-valuedVALUED-0V4\<bar>RelationRELAT-1M1"
"cluster note-that natural-valuedVALUED-0V4 for SubsetSUBSET-1M2-of R"
proof
(*coherence*)
  show " for it be SubsetSUBSET-1M2-of R holds it be natural-valuedVALUED-0V4"
    using valued_0_th_6 sorry
qed "sorry"

mtheorem valued_0_cl_23:
  mlet "R be complex-valuedVALUED-0V1\<bar>RelationRELAT-1M1", "S be complex-valuedVALUED-0V1\<bar>RelationRELAT-1M1"
"cluster R \\/XBOOLE-0K2 S as-term-is complex-valuedVALUED-0V1"
proof
(*coherence*)
  show "R \\/XBOOLE-0K2 S be complex-valuedVALUED-0V1"
sorry
qed "sorry"

mtheorem valued_0_cl_24:
  mlet "R be ext-real-valuedVALUED-0V2\<bar>RelationRELAT-1M1", "S be ext-real-valuedVALUED-0V2\<bar>RelationRELAT-1M1"
"cluster R \\/XBOOLE-0K2 S as-term-is ext-real-valuedVALUED-0V2"
proof
(*coherence*)
  show "R \\/XBOOLE-0K2 S be ext-real-valuedVALUED-0V2"
sorry
qed "sorry"

mtheorem valued_0_cl_25:
  mlet "R be real-valuedVALUED-0V3\<bar>RelationRELAT-1M1", "S be real-valuedVALUED-0V3\<bar>RelationRELAT-1M1"
"cluster R \\/XBOOLE-0K2 S as-term-is real-valuedVALUED-0V3"
proof
(*coherence*)
  show "R \\/XBOOLE-0K2 S be real-valuedVALUED-0V3"
sorry
qed "sorry"

mtheorem valued_0_cl_26:
  mlet "R be RATRAT-1K1 -valuedRELAT-1V5\<bar>RelationRELAT-1M1", "S be RATRAT-1K1 -valuedRELAT-1V5\<bar>RelationRELAT-1M1"
"cluster R \\/XBOOLE-0K2 S as-term-is RATRAT-1K1 -valuedRELAT-1V5"
proof
(*coherence*)
  show "R \\/XBOOLE-0K2 S be RATRAT-1K1 -valuedRELAT-1V5"
     sorry
qed "sorry"

mtheorem valued_0_cl_27:
  mlet "R be INTINT-1K1 -valuedRELAT-1V5\<bar>RelationRELAT-1M1", "S be INTINT-1K1 -valuedRELAT-1V5\<bar>RelationRELAT-1M1"
"cluster R \\/XBOOLE-0K2 S as-term-is INTINT-1K1 -valuedRELAT-1V5"
proof
(*coherence*)
  show "R \\/XBOOLE-0K2 S be INTINT-1K1 -valuedRELAT-1V5"
     sorry
qed "sorry"

mtheorem valued_0_cl_28:
  mlet "R be natural-valuedVALUED-0V4\<bar>RelationRELAT-1M1", "S be natural-valuedVALUED-0V4\<bar>RelationRELAT-1M1"
"cluster R \\/XBOOLE-0K2 S as-term-is natural-valuedVALUED-0V4"
proof
(*coherence*)
  show "R \\/XBOOLE-0K2 S be natural-valuedVALUED-0V4"
sorry
qed "sorry"

mtheorem valued_0_cl_29:
  mlet "R be complex-valuedVALUED-0V1\<bar>RelationRELAT-1M1", "S be RelationRELAT-1M1"
"cluster R /\\XBOOLE-0K3 S as-term-is complex-valuedVALUED-0V1"
proof
(*coherence*)
  show "R /\\XBOOLE-0K3 S be complex-valuedVALUED-0V1"
sorry
qed "sorry"

mtheorem valued_0_cl_30:
  mlet "R be complex-valuedVALUED-0V1\<bar>RelationRELAT-1M1", "S be RelationRELAT-1M1"
"cluster R \\SUBSET-1K6 S as-term-is complex-valuedVALUED-0V1"
proof
(*coherence*)
  show "R \\SUBSET-1K6 S be complex-valuedVALUED-0V1"
     sorry
qed "sorry"

mtheorem valued_0_cl_31:
  mlet "R be ext-real-valuedVALUED-0V2\<bar>RelationRELAT-1M1", "S be RelationRELAT-1M1"
"cluster R /\\XBOOLE-0K3 S as-term-is ext-real-valuedVALUED-0V2"
proof
(*coherence*)
  show "R /\\XBOOLE-0K3 S be ext-real-valuedVALUED-0V2"
sorry
qed "sorry"

mtheorem valued_0_cl_32:
  mlet "R be ext-real-valuedVALUED-0V2\<bar>RelationRELAT-1M1", "S be RelationRELAT-1M1"
"cluster R \\SUBSET-1K6 S as-term-is ext-real-valuedVALUED-0V2"
proof
(*coherence*)
  show "R \\SUBSET-1K6 S be ext-real-valuedVALUED-0V2"
     sorry
qed "sorry"

mtheorem valued_0_cl_33:
  mlet "R be real-valuedVALUED-0V3\<bar>RelationRELAT-1M1", "S be RelationRELAT-1M1"
"cluster R /\\XBOOLE-0K3 S as-term-is real-valuedVALUED-0V3"
proof
(*coherence*)
  show "R /\\XBOOLE-0K3 S be real-valuedVALUED-0V3"
sorry
qed "sorry"

mtheorem valued_0_cl_34:
  mlet "R be real-valuedVALUED-0V3\<bar>RelationRELAT-1M1", "S be RelationRELAT-1M1"
"cluster R \\SUBSET-1K6 S as-term-is real-valuedVALUED-0V3"
proof
(*coherence*)
  show "R \\SUBSET-1K6 S be real-valuedVALUED-0V3"
     sorry
qed "sorry"

mtheorem valued_0_cl_35:
  mlet "R be RATRAT-1K1 -valuedRELAT-1V5\<bar>RelationRELAT-1M1", "S be RelationRELAT-1M1"
"cluster R /\\XBOOLE-0K3 S as-term-is RATRAT-1K1 -valuedRELAT-1V5"
proof
(*coherence*)
  show "R /\\XBOOLE-0K3 S be RATRAT-1K1 -valuedRELAT-1V5"
     sorry
qed "sorry"

mtheorem valued_0_cl_36:
  mlet "R be RATRAT-1K1 -valuedRELAT-1V5\<bar>RelationRELAT-1M1", "S be RelationRELAT-1M1"
"cluster R \\SUBSET-1K6 S as-term-is RATRAT-1K1 -valuedRELAT-1V5"
proof
(*coherence*)
  show "R \\SUBSET-1K6 S be RATRAT-1K1 -valuedRELAT-1V5"
     sorry
qed "sorry"

mtheorem valued_0_cl_37:
  mlet "R be INTINT-1K1 -valuedRELAT-1V5\<bar>RelationRELAT-1M1", "S be RelationRELAT-1M1"
"cluster R /\\XBOOLE-0K3 S as-term-is INTINT-1K1 -valuedRELAT-1V5"
proof
(*coherence*)
  show "R /\\XBOOLE-0K3 S be INTINT-1K1 -valuedRELAT-1V5"
     sorry
qed "sorry"

mtheorem valued_0_cl_38:
  mlet "R be INTINT-1K1 -valuedRELAT-1V5\<bar>RelationRELAT-1M1", "S be RelationRELAT-1M1"
"cluster R \\SUBSET-1K6 S as-term-is INTINT-1K1 -valuedRELAT-1V5"
proof
(*coherence*)
  show "R \\SUBSET-1K6 S be INTINT-1K1 -valuedRELAT-1V5"
     sorry
qed "sorry"

mtheorem valued_0_cl_39:
  mlet "R be natural-valuedVALUED-0V4\<bar>RelationRELAT-1M1", "S be RelationRELAT-1M1"
"cluster R /\\XBOOLE-0K3 S as-term-is natural-valuedVALUED-0V4"
proof
(*coherence*)
  show "R /\\XBOOLE-0K3 S be natural-valuedVALUED-0V4"
sorry
qed "sorry"

mtheorem valued_0_cl_40:
  mlet "R be natural-valuedVALUED-0V4\<bar>RelationRELAT-1M1", "S be RelationRELAT-1M1"
"cluster R \\SUBSET-1K6 S as-term-is natural-valuedVALUED-0V4"
proof
(*coherence*)
  show "R \\SUBSET-1K6 S be natural-valuedVALUED-0V4"
     sorry
qed "sorry"

mtheorem valued_0_cl_41:
  mlet "R be complex-valuedVALUED-0V1\<bar>RelationRELAT-1M1", "S be complex-valuedVALUED-0V1\<bar>RelationRELAT-1M1"
"cluster R \\+\\XBOOLE-0K5 S as-term-is complex-valuedVALUED-0V1"
proof
(*coherence*)
  show "R \\+\\XBOOLE-0K5 S be complex-valuedVALUED-0V1"
     sorry
qed "sorry"

mtheorem valued_0_cl_42:
  mlet "R be ext-real-valuedVALUED-0V2\<bar>RelationRELAT-1M1", "S be ext-real-valuedVALUED-0V2\<bar>RelationRELAT-1M1"
"cluster R \\+\\XBOOLE-0K5 S as-term-is ext-real-valuedVALUED-0V2"
proof
(*coherence*)
  show "R \\+\\XBOOLE-0K5 S be ext-real-valuedVALUED-0V2"
     sorry
qed "sorry"

mtheorem valued_0_cl_43:
  mlet "R be real-valuedVALUED-0V3\<bar>RelationRELAT-1M1", "S be real-valuedVALUED-0V3\<bar>RelationRELAT-1M1"
"cluster R \\+\\XBOOLE-0K5 S as-term-is real-valuedVALUED-0V3"
proof
(*coherence*)
  show "R \\+\\XBOOLE-0K5 S be real-valuedVALUED-0V3"
     sorry
qed "sorry"

mtheorem valued_0_cl_44:
  mlet "R be RATRAT-1K1 -valuedRELAT-1V5\<bar>RelationRELAT-1M1", "S be RATRAT-1K1 -valuedRELAT-1V5\<bar>RelationRELAT-1M1"
"cluster R \\+\\XBOOLE-0K5 S as-term-is RATRAT-1K1 -valuedRELAT-1V5"
proof
(*coherence*)
  show "R \\+\\XBOOLE-0K5 S be RATRAT-1K1 -valuedRELAT-1V5"
     sorry
qed "sorry"

mtheorem valued_0_cl_45:
  mlet "R be INTINT-1K1 -valuedRELAT-1V5\<bar>RelationRELAT-1M1", "S be INTINT-1K1 -valuedRELAT-1V5\<bar>RelationRELAT-1M1"
"cluster R \\+\\XBOOLE-0K5 S as-term-is INTINT-1K1 -valuedRELAT-1V5"
proof
(*coherence*)
  show "R \\+\\XBOOLE-0K5 S be INTINT-1K1 -valuedRELAT-1V5"
     sorry
qed "sorry"

mtheorem valued_0_cl_46:
  mlet "R be natural-valuedVALUED-0V4\<bar>RelationRELAT-1M1", "S be natural-valuedVALUED-0V4\<bar>RelationRELAT-1M1"
"cluster R \\+\\XBOOLE-0K5 S as-term-is natural-valuedVALUED-0V4"
proof
(*coherence*)
  show "R \\+\\XBOOLE-0K5 S be natural-valuedVALUED-0V4"
     sorry
qed "sorry"

mtheorem valued_0_cl_47:
  mlet "R be complex-valuedVALUED-0V1\<bar>RelationRELAT-1M1", "X be setHIDDENM2"
"cluster R .:RELAT-1K10 X as-term-is complex-memberedMEMBEREDV1"
proof
(*coherence*)
  show "R .:RELAT-1K10 X be complex-memberedMEMBEREDV1"
sorry
qed "sorry"

mtheorem valued_0_cl_48:
  mlet "R be ext-real-valuedVALUED-0V2\<bar>RelationRELAT-1M1", "X be setHIDDENM2"
"cluster R .:RELAT-1K10 X as-term-is ext-real-memberedMEMBEREDV2"
proof
(*coherence*)
  show "R .:RELAT-1K10 X be ext-real-memberedMEMBEREDV2"
sorry
qed "sorry"

mtheorem valued_0_cl_49:
  mlet "R be real-valuedVALUED-0V3\<bar>RelationRELAT-1M1", "X be setHIDDENM2"
"cluster R .:RELAT-1K10 X as-term-is real-memberedMEMBEREDV3"
proof
(*coherence*)
  show "R .:RELAT-1K10 X be real-memberedMEMBEREDV3"
sorry
qed "sorry"

mtheorem valued_0_cl_50:
  mlet "R be RATRAT-1K1 -valuedRELAT-1V5\<bar>RelationRELAT-1M1", "X be setHIDDENM2"
"cluster R .:RELAT-1K10 X as-term-is rational-memberedMEMBEREDV4"
proof
(*coherence*)
  show "R .:RELAT-1K10 X be rational-memberedMEMBEREDV4"
sorry
qed "sorry"

mtheorem valued_0_cl_51:
  mlet "R be INTINT-1K1 -valuedRELAT-1V5\<bar>RelationRELAT-1M1", "X be setHIDDENM2"
"cluster R .:RELAT-1K10 X as-term-is integer-memberedMEMBEREDV5"
proof
(*coherence*)
  show "R .:RELAT-1K10 X be integer-memberedMEMBEREDV5"
sorry
qed "sorry"

mtheorem valued_0_cl_52:
  mlet "R be natural-valuedVALUED-0V4\<bar>RelationRELAT-1M1", "X be setHIDDENM2"
"cluster R .:RELAT-1K10 X as-term-is natural-memberedMEMBEREDV6"
proof
(*coherence*)
  show "R .:RELAT-1K10 X be natural-memberedMEMBEREDV6"
sorry
qed "sorry"

mtheorem valued_0_cl_53:
  mlet "R be complex-valuedVALUED-0V1\<bar>RelationRELAT-1M1", "x be objectHIDDENM1"
"cluster ImRELAT-1K12(R,x) as-term-is complex-memberedMEMBEREDV1"
proof
(*coherence*)
  show "ImRELAT-1K12(R,x) be complex-memberedMEMBEREDV1"
     sorry
qed "sorry"

mtheorem valued_0_cl_54:
  mlet "R be ext-real-valuedVALUED-0V2\<bar>RelationRELAT-1M1", "x be objectHIDDENM1"
"cluster ImRELAT-1K12(R,x) as-term-is ext-real-memberedMEMBEREDV2"
proof
(*coherence*)
  show "ImRELAT-1K12(R,x) be ext-real-memberedMEMBEREDV2"
     sorry
qed "sorry"

mtheorem valued_0_cl_55:
  mlet "R be real-valuedVALUED-0V3\<bar>RelationRELAT-1M1", "x be objectHIDDENM1"
"cluster ImRELAT-1K12(R,x) as-term-is real-memberedMEMBEREDV3"
proof
(*coherence*)
  show "ImRELAT-1K12(R,x) be real-memberedMEMBEREDV3"
     sorry
qed "sorry"

mtheorem valued_0_cl_56:
  mlet "R be RATRAT-1K1 -valuedRELAT-1V5\<bar>RelationRELAT-1M1", "x be objectHIDDENM1"
"cluster ImRELAT-1K12(R,x) as-term-is rational-memberedMEMBEREDV4"
proof
(*coherence*)
  show "ImRELAT-1K12(R,x) be rational-memberedMEMBEREDV4"
     sorry
qed "sorry"

mtheorem valued_0_cl_57:
  mlet "R be INTINT-1K1 -valuedRELAT-1V5\<bar>RelationRELAT-1M1", "x be objectHIDDENM1"
"cluster ImRELAT-1K12(R,x) as-term-is integer-memberedMEMBEREDV5"
proof
(*coherence*)
  show "ImRELAT-1K12(R,x) be integer-memberedMEMBEREDV5"
     sorry
qed "sorry"

mtheorem valued_0_cl_58:
  mlet "R be natural-valuedVALUED-0V4\<bar>RelationRELAT-1M1", "x be objectHIDDENM1"
"cluster ImRELAT-1K12(R,x) as-term-is natural-memberedMEMBEREDV6"
proof
(*coherence*)
  show "ImRELAT-1K12(R,x) be natural-memberedMEMBEREDV6"
     sorry
qed "sorry"

mtheorem valued_0_cl_59:
  mlet "R be complex-valuedVALUED-0V1\<bar>RelationRELAT-1M1", "X be setHIDDENM2"
"cluster R |RELAT-1K8 X as-term-is complex-valuedVALUED-0V1"
proof
(*coherence*)
  show "R |RELAT-1K8 X be complex-valuedVALUED-0V1"
sorry
qed "sorry"

mtheorem valued_0_cl_60:
  mlet "R be ext-real-valuedVALUED-0V2\<bar>RelationRELAT-1M1", "X be setHIDDENM2"
"cluster R |RELAT-1K8 X as-term-is ext-real-valuedVALUED-0V2"
proof
(*coherence*)
  show "R |RELAT-1K8 X be ext-real-valuedVALUED-0V2"
sorry
qed "sorry"

mtheorem valued_0_cl_61:
  mlet "R be real-valuedVALUED-0V3\<bar>RelationRELAT-1M1", "X be setHIDDENM2"
"cluster R |RELAT-1K8 X as-term-is real-valuedVALUED-0V3"
proof
(*coherence*)
  show "R |RELAT-1K8 X be real-valuedVALUED-0V3"
sorry
qed "sorry"

mtheorem valued_0_cl_62:
  mlet "R be RATRAT-1K1 -valuedRELAT-1V5\<bar>RelationRELAT-1M1", "X be setHIDDENM2"
"cluster R |RELAT-1K8 X as-term-is RATRAT-1K1 -valuedRELAT-1V5"
proof
(*coherence*)
  show "R |RELAT-1K8 X be RATRAT-1K1 -valuedRELAT-1V5"
     sorry
qed "sorry"

mtheorem valued_0_cl_63:
  mlet "R be INTINT-1K1 -valuedRELAT-1V5\<bar>RelationRELAT-1M1", "X be setHIDDENM2"
"cluster R |RELAT-1K8 X as-term-is INTINT-1K1 -valuedRELAT-1V5"
proof
(*coherence*)
  show "R |RELAT-1K8 X be INTINT-1K1 -valuedRELAT-1V5"
     sorry
qed "sorry"

mtheorem valued_0_cl_64:
  mlet "R be natural-valuedVALUED-0V4\<bar>RelationRELAT-1M1", "X be setHIDDENM2"
"cluster R |RELAT-1K8 X as-term-is natural-valuedVALUED-0V4"
proof
(*coherence*)
  show "R |RELAT-1K8 X be natural-valuedVALUED-0V4"
sorry
qed "sorry"

mtheorem valued_0_cl_65:
  mlet "X be complex-memberedMEMBEREDV1\<bar>setHIDDENM2"
"cluster idPARTFUN1K6 X as-term-is complex-valuedVALUED-0V1"
proof
(*coherence*)
  show "idPARTFUN1K6 X be complex-valuedVALUED-0V1"
    using membered_th_1 sorry
qed "sorry"

mtheorem valued_0_cl_66:
  mlet "X be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2"
"cluster idPARTFUN1K6 X as-term-is ext-real-valuedVALUED-0V2"
proof
(*coherence*)
  show "idPARTFUN1K6 X be ext-real-valuedVALUED-0V2"
    using membered_th_2 sorry
qed "sorry"

mtheorem valued_0_cl_67:
  mlet "X be real-memberedMEMBEREDV3\<bar>setHIDDENM2"
"cluster idPARTFUN1K6 X as-term-is real-valuedVALUED-0V3"
proof
(*coherence*)
  show "idPARTFUN1K6 X be real-valuedVALUED-0V3"
    using membered_th_3 sorry
qed "sorry"

mtheorem valued_0_cl_68:
  mlet "X be rational-memberedMEMBEREDV4\<bar>setHIDDENM2"
"cluster idPARTFUN1K6 X as-term-is RATRAT-1K1 -valuedRELAT-1V5"
proof
(*coherence*)
  show "idPARTFUN1K6 X be RATRAT-1K1 -valuedRELAT-1V5"
    using membered_th_4 sorry
qed "sorry"

mtheorem valued_0_cl_69:
  mlet "X be integer-memberedMEMBEREDV5\<bar>setHIDDENM2"
"cluster idPARTFUN1K6 X as-term-is INTINT-1K1 -valuedRELAT-1V5"
proof
(*coherence*)
  show "idPARTFUN1K6 X be INTINT-1K1 -valuedRELAT-1V5"
    using membered_th_5 sorry
qed "sorry"

mtheorem valued_0_cl_70:
  mlet "X be natural-memberedMEMBEREDV6\<bar>setHIDDENM2"
"cluster idPARTFUN1K6 X as-term-is natural-valuedVALUED-0V4"
proof
(*coherence*)
  show "idPARTFUN1K6 X be natural-valuedVALUED-0V4"
    using membered_th_6 sorry
qed "sorry"

mtheorem valued_0_cl_71:
  mlet "R be RelationRELAT-1M1", "S be complex-valuedVALUED-0V1\<bar>RelationRELAT-1M1"
"cluster R *RELAT-1K6 S as-term-is complex-valuedVALUED-0V1"
proof
(*coherence*)
  show "R *RELAT-1K6 S be complex-valuedVALUED-0V1"
sorry
qed "sorry"

mtheorem valued_0_cl_72:
  mlet "R be RelationRELAT-1M1", "S be ext-real-valuedVALUED-0V2\<bar>RelationRELAT-1M1"
"cluster R *RELAT-1K6 S as-term-is ext-real-valuedVALUED-0V2"
proof
(*coherence*)
  show "R *RELAT-1K6 S be ext-real-valuedVALUED-0V2"
sorry
qed "sorry"

mtheorem valued_0_cl_73:
  mlet "R be RelationRELAT-1M1", "S be real-valuedVALUED-0V3\<bar>RelationRELAT-1M1"
"cluster R *RELAT-1K6 S as-term-is real-valuedVALUED-0V3"
proof
(*coherence*)
  show "R *RELAT-1K6 S be real-valuedVALUED-0V3"
sorry
qed "sorry"

mtheorem valued_0_cl_74:
  mlet "R be RelationRELAT-1M1", "S be RATRAT-1K1 -valuedRELAT-1V5\<bar>RelationRELAT-1M1"
"cluster R *RELAT-1K6 S as-term-is RATRAT-1K1 -valuedRELAT-1V5"
proof
(*coherence*)
  show "R *RELAT-1K6 S be RATRAT-1K1 -valuedRELAT-1V5"
     sorry
qed "sorry"

mtheorem valued_0_cl_75:
  mlet "R be RelationRELAT-1M1", "S be INTINT-1K1 -valuedRELAT-1V5\<bar>RelationRELAT-1M1"
"cluster R *RELAT-1K6 S as-term-is INTINT-1K1 -valuedRELAT-1V5"
proof
(*coherence*)
  show "R *RELAT-1K6 S be INTINT-1K1 -valuedRELAT-1V5"
     sorry
qed "sorry"

mtheorem valued_0_cl_76:
  mlet "R be RelationRELAT-1M1", "S be natural-valuedVALUED-0V4\<bar>RelationRELAT-1M1"
"cluster R *RELAT-1K6 S as-term-is natural-valuedVALUED-0V4"
proof
(*coherence*)
  show "R *RELAT-1K6 S be natural-valuedVALUED-0V4"
sorry
qed "sorry"

abbreviation(input) VALUED_0V5("complex-valuedVALUED-0V5" 70) where
  "complex-valuedVALUED-0V5 \<equiv> complex-valuedVALUED-0V1"

mtheorem valued_0_def_7:
  mlet "f be FunctionFUNCT-1M1"
"redefine attr complex-valuedVALUED-0V5 for FunctionFUNCT-1M1 means
  (\<lambda>f.  for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 f implies f .FUNCT-1K1 x be complexXCMPLX-0V1)"
proof
(*compatibility*)
  show " for f be FunctionFUNCT-1M1 holds f be complex-valuedVALUED-0V5 iff ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 f implies f .FUNCT-1K1 x be complexXCMPLX-0V1)"
sorry
qed "sorry"

abbreviation(input) VALUED_0V6("ext-real-valuedVALUED-0V6" 70) where
  "ext-real-valuedVALUED-0V6 \<equiv> ext-real-valuedVALUED-0V2"

mtheorem valued_0_def_8:
  mlet "f be FunctionFUNCT-1M1"
"redefine attr ext-real-valuedVALUED-0V6 for FunctionFUNCT-1M1 means
  (\<lambda>f.  for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 f implies f .FUNCT-1K1 x be ext-realXXREAL-0V1)"
proof
(*compatibility*)
  show " for f be FunctionFUNCT-1M1 holds f be ext-real-valuedVALUED-0V6 iff ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 f implies f .FUNCT-1K1 x be ext-realXXREAL-0V1)"
sorry
qed "sorry"

abbreviation(input) VALUED_0V7("real-valuedVALUED-0V7" 70) where
  "real-valuedVALUED-0V7 \<equiv> real-valuedVALUED-0V3"

mtheorem valued_0_def_9:
  mlet "f be FunctionFUNCT-1M1"
"redefine attr real-valuedVALUED-0V7 for FunctionFUNCT-1M1 means
  (\<lambda>f.  for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 f implies f .FUNCT-1K1 x be realXREAL-0V1)"
proof
(*compatibility*)
  show " for f be FunctionFUNCT-1M1 holds f be real-valuedVALUED-0V7 iff ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 f implies f .FUNCT-1K1 x be realXREAL-0V1)"
sorry
qed "sorry"

(*\$CD 2*)
abbreviation(input) VALUED_0V8("natural-valuedVALUED-0V8" 70) where
  "natural-valuedVALUED-0V8 \<equiv> natural-valuedVALUED-0V4"

mtheorem valued_0_def_12:
  mlet "f be FunctionFUNCT-1M1"
"redefine attr natural-valuedVALUED-0V8 for FunctionFUNCT-1M1 means
  (\<lambda>f.  for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 f implies f .FUNCT-1K1 x be naturalORDINAL1V7)"
proof
(*compatibility*)
  show " for f be FunctionFUNCT-1M1 holds f be natural-valuedVALUED-0V8 iff ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 f implies f .FUNCT-1K1 x be naturalORDINAL1V7)"
sorry
qed "sorry"

mtheorem valued_0_th_7:
" for f be FunctionFUNCT-1M1 holds f be complex-valuedVALUED-0V5 iff ( for x be objectHIDDENM1 holds f .FUNCT-1K1 x be complexXCMPLX-0V1)"
sorry

mtheorem valued_0_th_8:
" for f be FunctionFUNCT-1M1 holds f be ext-real-valuedVALUED-0V6 iff ( for x be objectHIDDENM1 holds f .FUNCT-1K1 x be ext-realXXREAL-0V1)"
sorry

mtheorem valued_0_th_9:
" for f be FunctionFUNCT-1M1 holds f be real-valuedVALUED-0V7 iff ( for x be objectHIDDENM1 holds f .FUNCT-1K1 x be realXREAL-0V1)"
sorry

mtheorem valued_0_th_10:
" for f be FunctionFUNCT-1M1 holds f be RATRAT-1K1 -valuedRELAT-1V5 iff ( for x be objectHIDDENM1 holds f .FUNCT-1K1 x be rationalRAT-1V1)"
sorry

mtheorem valued_0_th_11:
" for f be FunctionFUNCT-1M1 holds f be INTINT-1K1 -valuedRELAT-1V5 iff ( for x be objectHIDDENM1 holds f .FUNCT-1K1 x be integerINT-1V1)"
sorry

mtheorem valued_0_th_12:
" for f be FunctionFUNCT-1M1 holds f be natural-valuedVALUED-0V8 iff ( for x be objectHIDDENM1 holds f .FUNCT-1K1 x be naturalORDINAL1V7)"
sorry

mtheorem valued_0_cl_77:
  mlet "f be complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1", "x be objectHIDDENM1"
"cluster f .FUNCT-1K1 x as-term-is complexXCMPLX-0V1"
proof
(*coherence*)
  show "f .FUNCT-1K1 x be complexXCMPLX-0V1"
    using valued_0_th_7 sorry
qed "sorry"

mtheorem valued_0_cl_78:
  mlet "f be ext-real-valuedVALUED-0V6\<bar>FunctionFUNCT-1M1", "x be objectHIDDENM1"
"cluster f .FUNCT-1K1 x as-term-is ext-realXXREAL-0V1"
proof
(*coherence*)
  show "f .FUNCT-1K1 x be ext-realXXREAL-0V1"
    using valued_0_th_8 sorry
qed "sorry"

mtheorem valued_0_cl_79:
  mlet "f be real-valuedVALUED-0V7\<bar>FunctionFUNCT-1M1", "x be objectHIDDENM1"
"cluster f .FUNCT-1K1 x as-term-is realXREAL-0V1"
proof
(*coherence*)
  show "f .FUNCT-1K1 x be realXREAL-0V1"
    using valued_0_th_9 sorry
qed "sorry"

mtheorem valued_0_cl_80:
  mlet "f be RATRAT-1K1 -valuedRELAT-1V5\<bar>FunctionFUNCT-1M1", "x be objectHIDDENM1"
"cluster f .FUNCT-1K1 x as-term-is rationalRAT-1V1"
proof
(*coherence*)
  show "f .FUNCT-1K1 x be rationalRAT-1V1"
    using valued_0_th_10 sorry
qed "sorry"

mtheorem valued_0_cl_81:
  mlet "f be INTINT-1K1 -valuedRELAT-1V5\<bar>FunctionFUNCT-1M1", "x be objectHIDDENM1"
"cluster f .FUNCT-1K1 x as-term-is integerINT-1V1"
proof
(*coherence*)
  show "f .FUNCT-1K1 x be integerINT-1V1"
    using valued_0_th_11 sorry
qed "sorry"

mtheorem valued_0_cl_82:
  mlet "f be natural-valuedVALUED-0V8\<bar>FunctionFUNCT-1M1", "x be objectHIDDENM1"
"cluster f .FUNCT-1K1 x as-term-is naturalORDINAL1V7"
proof
(*coherence*)
  show "f .FUNCT-1K1 x be naturalORDINAL1V7"
    using valued_0_th_12 sorry
qed "sorry"

mtheorem valued_0_cl_83:
  mlet "X be setHIDDENM2", "x be ComplexXCMPLX-0M1"
"cluster X -->FUNCOP-1K7 x as-term-is complex-valuedVALUED-0V5"
proof
(*coherence*)
  show "X -->FUNCOP-1K7 x be complex-valuedVALUED-0V5"
sorry
qed "sorry"

mtheorem valued_0_cl_84:
  mlet "X be setHIDDENM2", "x be ExtRealXXREAL-0M1"
"cluster X -->FUNCOP-1K7 x as-term-is ext-real-valuedVALUED-0V6"
proof
(*coherence*)
  show "X -->FUNCOP-1K7 x be ext-real-valuedVALUED-0V6"
sorry
qed "sorry"

mtheorem valued_0_cl_85:
  mlet "X be setHIDDENM2", "x be RealXREAL-0M1"
"cluster X -->FUNCOP-1K7 x as-term-is real-valuedVALUED-0V7"
proof
(*coherence*)
  show "X -->FUNCOP-1K7 x be real-valuedVALUED-0V7"
sorry
qed "sorry"

mtheorem valued_0_cl_86:
  mlet "X be setHIDDENM2", "x be RationalRAT-1M1"
"cluster X -->FUNCOP-1K7 x as-term-is RATRAT-1K1 -valuedRELAT-1V5"
proof
(*coherence*)
  show "X -->FUNCOP-1K7 x be RATRAT-1K1 -valuedRELAT-1V5"
sorry
qed "sorry"

mtheorem valued_0_cl_87:
  mlet "X be setHIDDENM2", "x be IntegerINT-1M1"
"cluster X -->FUNCOP-1K7 x as-term-is INTINT-1K1 -valuedRELAT-1V5"
proof
(*coherence*)
  show "X -->FUNCOP-1K7 x be INTINT-1K1 -valuedRELAT-1V5"
sorry
qed "sorry"

mtheorem valued_0_cl_88:
  mlet "X be setHIDDENM2", "x be NatNAT-1M1"
"cluster X -->FUNCOP-1K7 x as-term-is natural-valuedVALUED-0V8"
proof
(*coherence*)
  show "X -->FUNCOP-1K7 x be natural-valuedVALUED-0V8"
sorry
qed "sorry"

mtheorem valued_0_cl_89:
  mlet "f be complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1", "g be complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1"
"cluster f +*FUNCT-4K1 g as-term-is complex-valuedVALUED-0V5"
proof
(*coherence*)
  show "f +*FUNCT-4K1 g be complex-valuedVALUED-0V5"
sorry
qed "sorry"

mtheorem valued_0_cl_90:
  mlet "f be ext-real-valuedVALUED-0V6\<bar>FunctionFUNCT-1M1", "g be ext-real-valuedVALUED-0V6\<bar>FunctionFUNCT-1M1"
"cluster f +*FUNCT-4K1 g as-term-is ext-real-valuedVALUED-0V6"
proof
(*coherence*)
  show "f +*FUNCT-4K1 g be ext-real-valuedVALUED-0V6"
sorry
qed "sorry"

mtheorem valued_0_cl_91:
  mlet "f be real-valuedVALUED-0V7\<bar>FunctionFUNCT-1M1", "g be real-valuedVALUED-0V7\<bar>FunctionFUNCT-1M1"
"cluster f +*FUNCT-4K1 g as-term-is real-valuedVALUED-0V7"
proof
(*coherence*)
  show "f +*FUNCT-4K1 g be real-valuedVALUED-0V7"
sorry
qed "sorry"

mtheorem valued_0_cl_92:
  mlet "f be RATRAT-1K1 -valuedRELAT-1V5\<bar>FunctionFUNCT-1M1", "g be RATRAT-1K1 -valuedRELAT-1V5\<bar>FunctionFUNCT-1M1"
"cluster f +*FUNCT-4K1 g as-term-is RATRAT-1K1 -valuedRELAT-1V5"
proof
(*coherence*)
  show "f +*FUNCT-4K1 g be RATRAT-1K1 -valuedRELAT-1V5"
sorry
qed "sorry"

mtheorem valued_0_cl_93:
  mlet "f be INTINT-1K1 -valuedRELAT-1V5\<bar>FunctionFUNCT-1M1", "g be INTINT-1K1 -valuedRELAT-1V5\<bar>FunctionFUNCT-1M1"
"cluster f +*FUNCT-4K1 g as-term-is INTINT-1K1 -valuedRELAT-1V5"
proof
(*coherence*)
  show "f +*FUNCT-4K1 g be INTINT-1K1 -valuedRELAT-1V5"
sorry
qed "sorry"

mtheorem valued_0_cl_94:
  mlet "f be natural-valuedVALUED-0V8\<bar>FunctionFUNCT-1M1", "g be natural-valuedVALUED-0V8\<bar>FunctionFUNCT-1M1"
"cluster f +*FUNCT-4K1 g as-term-is natural-valuedVALUED-0V8"
proof
(*coherence*)
  show "f +*FUNCT-4K1 g be natural-valuedVALUED-0V8"
sorry
qed "sorry"

mtheorem valued_0_cl_95:
  mlet "x be objectHIDDENM1", "y be ComplexXCMPLX-0M1"
"cluster x .-->FUNCOP-1K17 y as-term-is complex-valuedVALUED-0V5"
proof
(*coherence*)
  show "x .-->FUNCOP-1K17 y be complex-valuedVALUED-0V5"
     sorry
qed "sorry"

mtheorem valued_0_cl_96:
  mlet "x be objectHIDDENM1", "y be ExtRealXXREAL-0M1"
"cluster x .-->FUNCOP-1K17 y as-term-is ext-real-valuedVALUED-0V6"
proof
(*coherence*)
  show "x .-->FUNCOP-1K17 y be ext-real-valuedVALUED-0V6"
     sorry
qed "sorry"

mtheorem valued_0_cl_97:
  mlet "x be objectHIDDENM1", "y be RealXREAL-0M1"
"cluster x .-->FUNCOP-1K17 y as-term-is real-valuedVALUED-0V7"
proof
(*coherence*)
  show "x .-->FUNCOP-1K17 y be real-valuedVALUED-0V7"
     sorry
qed "sorry"

mtheorem valued_0_cl_98:
  mlet "x be objectHIDDENM1", "y be RationalRAT-1M1"
"cluster x .-->FUNCOP-1K17 y as-term-is RATRAT-1K1 -valuedRELAT-1V5"
proof
(*coherence*)
  show "x .-->FUNCOP-1K17 y be RATRAT-1K1 -valuedRELAT-1V5"
     sorry
qed "sorry"

mtheorem valued_0_cl_99:
  mlet "x be objectHIDDENM1", "y be IntegerINT-1M1"
"cluster x .-->FUNCOP-1K17 y as-term-is INTINT-1K1 -valuedRELAT-1V5"
proof
(*coherence*)
  show "x .-->FUNCOP-1K17 y be INTINT-1K1 -valuedRELAT-1V5"
     sorry
qed "sorry"

mtheorem valued_0_cl_100:
  mlet "x be objectHIDDENM1", "y be NatNAT-1M1"
"cluster x .-->FUNCOP-1K17 y as-term-is natural-valuedVALUED-0V8"
proof
(*coherence*)
  show "x .-->FUNCOP-1K17 y be natural-valuedVALUED-0V8"
     sorry
qed "sorry"

mtheorem valued_0_cl_101:
  mlet "X be setHIDDENM2", "Y be complex-memberedMEMBEREDV1\<bar>setHIDDENM2"
"cluster note-that complex-valuedVALUED-0V1 for RelationRELSET-1M1-of(X,Y)"
proof
(*coherence*)
  show " for it be RelationRELSET-1M1-of(X,Y) holds it be complex-valuedVALUED-0V1"
sorry
qed "sorry"

mtheorem valued_0_cl_102:
  mlet "X be setHIDDENM2", "Y be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2"
"cluster note-that ext-real-valuedVALUED-0V2 for RelationRELSET-1M1-of(X,Y)"
proof
(*coherence*)
  show " for it be RelationRELSET-1M1-of(X,Y) holds it be ext-real-valuedVALUED-0V2"
sorry
qed "sorry"

mtheorem valued_0_cl_103:
  mlet "X be setHIDDENM2", "Y be real-memberedMEMBEREDV3\<bar>setHIDDENM2"
"cluster note-that real-valuedVALUED-0V3 for RelationRELSET-1M1-of(X,Y)"
proof
(*coherence*)
  show " for it be RelationRELSET-1M1-of(X,Y) holds it be real-valuedVALUED-0V3"
sorry
qed "sorry"

mtheorem valued_0_cl_104:
  mlet "X be setHIDDENM2", "Y be rational-memberedMEMBEREDV4\<bar>setHIDDENM2"
"cluster note-that RATRAT-1K1 -valuedRELAT-1V5 for RelationRELSET-1M1-of(X,Y)"
proof
(*coherence*)
  show " for it be RelationRELSET-1M1-of(X,Y) holds it be RATRAT-1K1 -valuedRELAT-1V5"
sorry
qed "sorry"

mtheorem valued_0_cl_105:
  mlet "X be setHIDDENM2", "Y be integer-memberedMEMBEREDV5\<bar>setHIDDENM2"
"cluster note-that INTINT-1K1 -valuedRELAT-1V5 for RelationRELSET-1M1-of(X,Y)"
proof
(*coherence*)
  show " for it be RelationRELSET-1M1-of(X,Y) holds it be INTINT-1K1 -valuedRELAT-1V5"
sorry
qed "sorry"

mtheorem valued_0_cl_106:
  mlet "X be setHIDDENM2", "Y be natural-memberedMEMBEREDV6\<bar>setHIDDENM2"
"cluster note-that natural-valuedVALUED-0V4 for RelationRELSET-1M1-of(X,Y)"
proof
(*coherence*)
  show " for it be RelationRELSET-1M1-of(X,Y) holds it be natural-valuedVALUED-0V4"
sorry
qed "sorry"

mtheorem valued_0_cl_107:
  mlet "X be setHIDDENM2", "Y be complex-memberedMEMBEREDV1\<bar>setHIDDENM2"
"cluster [:ZFMISC-1K2 X,Y :] as-term-is complex-valuedVALUED-0V1"
proof
(*coherence*)
  show "[:ZFMISC-1K2 X,Y :] be complex-valuedVALUED-0V1"
sorry
qed "sorry"

mtheorem valued_0_cl_108:
  mlet "X be setHIDDENM2", "Y be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2"
"cluster [:ZFMISC-1K2 X,Y :] as-term-is ext-real-valuedVALUED-0V2"
proof
(*coherence*)
  show "[:ZFMISC-1K2 X,Y :] be ext-real-valuedVALUED-0V2"
sorry
qed "sorry"

mtheorem valued_0_cl_109:
  mlet "X be setHIDDENM2", "Y be real-memberedMEMBEREDV3\<bar>setHIDDENM2"
"cluster [:ZFMISC-1K2 X,Y :] as-term-is real-valuedVALUED-0V3"
proof
(*coherence*)
  show "[:ZFMISC-1K2 X,Y :] be real-valuedVALUED-0V3"
sorry
qed "sorry"

mtheorem valued_0_cl_110:
  mlet "X be setHIDDENM2", "Y be rational-memberedMEMBEREDV4\<bar>setHIDDENM2"
"cluster [:ZFMISC-1K2 X,Y :] as-term-is RATRAT-1K1 -valuedRELAT-1V5"
proof
(*coherence*)
  show "[:ZFMISC-1K2 X,Y :] be RATRAT-1K1 -valuedRELAT-1V5"
sorry
qed "sorry"

mtheorem valued_0_cl_111:
  mlet "X be setHIDDENM2", "Y be integer-memberedMEMBEREDV5\<bar>setHIDDENM2"
"cluster [:ZFMISC-1K2 X,Y :] as-term-is INTINT-1K1 -valuedRELAT-1V5"
proof
(*coherence*)
  show "[:ZFMISC-1K2 X,Y :] be INTINT-1K1 -valuedRELAT-1V5"
sorry
qed "sorry"

mtheorem valued_0_cl_112:
  mlet "X be setHIDDENM2", "Y be natural-memberedMEMBEREDV6\<bar>setHIDDENM2"
"cluster [:ZFMISC-1K2 X,Y :] as-term-is natural-valuedVALUED-0V4"
proof
(*coherence*)
  show "[:ZFMISC-1K2 X,Y :] be natural-valuedVALUED-0V4"
sorry
qed "sorry"

mtheorem valued_0_cl_113:
"cluster  non emptyXBOOLE-0V1\<bar>constantFUNCT-1V5\<bar>natural-valuedVALUED-0V8\<bar>RATRAT-1K1 -valuedRELAT-1V5\<bar>RATRAT-1K1 -valuedRELAT-1V5 for FunctionFUNCT-1M1"
proof
(*existence*)
  show " ex it be FunctionFUNCT-1M1 st it be  non emptyXBOOLE-0V1\<bar>constantFUNCT-1V5\<bar>natural-valuedVALUED-0V8\<bar>RATRAT-1K1 -valuedRELAT-1V5\<bar>RATRAT-1K1 -valuedRELAT-1V5"
sorry
qed "sorry"

mtheorem valued_0_th_13:
" for f be  non emptyXBOOLE-0V1\<bar>constantFUNCT-1V5\<bar>complex-valuedVALUED-0V5\<bar>FunctionFUNCT-1M1 holds  ex r be ComplexXCMPLX-0M1 st  for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 f implies f .FUNCT-1K1 x =HIDDENR1 r"
sorry

mtheorem valued_0_th_14:
" for f be  non emptyXBOOLE-0V1\<bar>constantFUNCT-1V5\<bar>ext-real-valuedVALUED-0V6\<bar>FunctionFUNCT-1M1 holds  ex r be ExtRealXXREAL-0M1 st  for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 f implies f .FUNCT-1K1 x =HIDDENR1 r"
sorry

mtheorem valued_0_th_15:
" for f be  non emptyXBOOLE-0V1\<bar>constantFUNCT-1V5\<bar>real-valuedVALUED-0V7\<bar>FunctionFUNCT-1M1 holds  ex r be RealXREAL-0M1 st  for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 f implies f .FUNCT-1K1 x =HIDDENR1 r"
sorry

mtheorem valued_0_th_16:
" for f be  non emptyXBOOLE-0V1\<bar>constantFUNCT-1V5\<bar>RATRAT-1K1 -valuedRELAT-1V5\<bar>FunctionFUNCT-1M1 holds  ex r be RationalRAT-1M1 st  for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 f implies f .FUNCT-1K1 x =HIDDENR1 r"
sorry

mtheorem valued_0_th_17:
" for f be  non emptyXBOOLE-0V1\<bar>constantFUNCT-1V5\<bar>INTINT-1K1 -valuedRELAT-1V5\<bar>FunctionFUNCT-1M1 holds  ex r be IntegerINT-1M1 st  for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 f implies f .FUNCT-1K1 x =HIDDENR1 r"
sorry

mtheorem valued_0_th_18:
" for f be  non emptyXBOOLE-0V1\<bar>constantFUNCT-1V5\<bar>natural-valuedVALUED-0V8\<bar>FunctionFUNCT-1M1 holds  ex r be NatNAT-1M1 st  for x be objectHIDDENM1 holds x inHIDDENR3 domRELAT-1K1 f implies f .FUNCT-1K1 x =XBOOLE-0R4 r"
sorry

(*begin*)
reserve e1, e2 for "ExtRealXXREAL-0M1"
mdef valued_0_def_13 ("increasingVALUED-0V9" 70 ) where
"attr increasingVALUED-0V9 for ext-real-valuedVALUED-0V6\<bar>FunctionFUNCT-1M1 means
  (\<lambda>f.  for e1 be ExtRealXXREAL-0M1 holds  for e2 be ExtRealXXREAL-0M1 holds (e1 inHIDDENR3 domRELAT-1K1 f & e2 inHIDDENR3 domRELAT-1K1 f) & e1 <XXREAL-0R3 e2 implies f .FUNCT-1K1 e1 <XXREAL-0R3 f .FUNCT-1K1 e2)"..

mdef valued_0_def_14 ("decreasingVALUED-0V10" 70 ) where
"attr decreasingVALUED-0V10 for ext-real-valuedVALUED-0V6\<bar>FunctionFUNCT-1M1 means
  (\<lambda>f.  for e1 be ExtRealXXREAL-0M1 holds  for e2 be ExtRealXXREAL-0M1 holds (e1 inHIDDENR3 domRELAT-1K1 f & e2 inHIDDENR3 domRELAT-1K1 f) & e1 <XXREAL-0R3 e2 implies f .FUNCT-1K1 e1 >XXREAL-0R4 f .FUNCT-1K1 e2)"..

mdef valued_0_def_15 ("non-decreasingVALUED-0V11" 70 ) where
"attr non-decreasingVALUED-0V11 for ext-real-valuedVALUED-0V6\<bar>FunctionFUNCT-1M1 means
  (\<lambda>f.  for e1 be ExtRealXXREAL-0M1 holds  for e2 be ExtRealXXREAL-0M1 holds (e1 inHIDDENR3 domRELAT-1K1 f & e2 inHIDDENR3 domRELAT-1K1 f) & e1 <=XXREAL-0R1 e2 implies f .FUNCT-1K1 e1 <=XXREAL-0R1 f .FUNCT-1K1 e2)"..

mdef valued_0_def_16 ("non-increasingVALUED-0V12" 70 ) where
"attr non-increasingVALUED-0V12 for ext-real-valuedVALUED-0V6\<bar>FunctionFUNCT-1M1 means
  (\<lambda>f.  for e1 be ExtRealXXREAL-0M1 holds  for e2 be ExtRealXXREAL-0M1 holds (e1 inHIDDENR3 domRELAT-1K1 f & e2 inHIDDENR3 domRELAT-1K1 f) & e1 <=XXREAL-0R1 e2 implies f .FUNCT-1K1 e1 >=XXREAL-0R2 f .FUNCT-1K1 e2)"..

mtheorem valued_0_cl_114:
"cluster trivialSUBSET-1V2 also-is increasingVALUED-0V9\<bar>decreasingVALUED-0V10 for ext-real-valuedVALUED-0V6\<bar>FunctionFUNCT-1M1"
proof
(*coherence*)
  show " for it be ext-real-valuedVALUED-0V6\<bar>FunctionFUNCT-1M1 holds it be trivialSUBSET-1V2 implies it be increasingVALUED-0V9\<bar>decreasingVALUED-0V10"
    using zfmisc_1_def_10 sorry
qed "sorry"

mtheorem valued_0_cl_115:
"cluster increasingVALUED-0V9 also-is non-decreasingVALUED-0V11 for ext-real-valuedVALUED-0V6\<bar>FunctionFUNCT-1M1"
proof
(*coherence*)
  show " for it be ext-real-valuedVALUED-0V6\<bar>FunctionFUNCT-1M1 holds it be increasingVALUED-0V9 implies it be non-decreasingVALUED-0V11"
sorry
qed "sorry"

mtheorem valued_0_cl_116:
"cluster decreasingVALUED-0V10 also-is non-increasingVALUED-0V12 for ext-real-valuedVALUED-0V6\<bar>FunctionFUNCT-1M1"
proof
(*coherence*)
  show " for it be ext-real-valuedVALUED-0V6\<bar>FunctionFUNCT-1M1 holds it be decreasingVALUED-0V10 implies it be non-increasingVALUED-0V12"
sorry
qed "sorry"

mtheorem valued_0_cl_117:
  mlet "f be increasingVALUED-0V9\<bar>ext-real-valuedVALUED-0V6\<bar>FunctionFUNCT-1M1", "g be increasingVALUED-0V9\<bar>ext-real-valuedVALUED-0V6\<bar>FunctionFUNCT-1M1"
"cluster g *FUNCT-1K3 f as-term-is increasingVALUED-0V9"
proof
(*coherence*)
  show "g *FUNCT-1K3 f be increasingVALUED-0V9"
sorry
qed "sorry"

mtheorem valued_0_cl_118:
  mlet "f be non-decreasingVALUED-0V11\<bar>ext-real-valuedVALUED-0V6\<bar>FunctionFUNCT-1M1", "g be non-decreasingVALUED-0V11\<bar>ext-real-valuedVALUED-0V6\<bar>FunctionFUNCT-1M1"
"cluster g *FUNCT-1K3 f as-term-is non-decreasingVALUED-0V11"
proof
(*coherence*)
  show "g *FUNCT-1K3 f be non-decreasingVALUED-0V11"
sorry
qed "sorry"

mtheorem valued_0_cl_119:
  mlet "f be decreasingVALUED-0V10\<bar>ext-real-valuedVALUED-0V6\<bar>FunctionFUNCT-1M1", "g be decreasingVALUED-0V10\<bar>ext-real-valuedVALUED-0V6\<bar>FunctionFUNCT-1M1"
"cluster g *FUNCT-1K3 f as-term-is increasingVALUED-0V9"
proof
(*coherence*)
  show "g *FUNCT-1K3 f be increasingVALUED-0V9"
sorry
qed "sorry"

mtheorem valued_0_cl_120:
  mlet "f be non-increasingVALUED-0V12\<bar>ext-real-valuedVALUED-0V6\<bar>FunctionFUNCT-1M1", "g be non-increasingVALUED-0V12\<bar>ext-real-valuedVALUED-0V6\<bar>FunctionFUNCT-1M1"
"cluster g *FUNCT-1K3 f as-term-is non-decreasingVALUED-0V11"
proof
(*coherence*)
  show "g *FUNCT-1K3 f be non-decreasingVALUED-0V11"
sorry
qed "sorry"

mtheorem valued_0_cl_121:
  mlet "f be decreasingVALUED-0V10\<bar>ext-real-valuedVALUED-0V6\<bar>FunctionFUNCT-1M1", "g be increasingVALUED-0V9\<bar>ext-real-valuedVALUED-0V6\<bar>FunctionFUNCT-1M1"
"cluster g *FUNCT-1K3 f as-term-is decreasingVALUED-0V10"
proof
(*coherence*)
  show "g *FUNCT-1K3 f be decreasingVALUED-0V10"
sorry
qed "sorry"

mtheorem valued_0_cl_122:
  mlet "f be decreasingVALUED-0V10\<bar>ext-real-valuedVALUED-0V6\<bar>FunctionFUNCT-1M1", "g be increasingVALUED-0V9\<bar>ext-real-valuedVALUED-0V6\<bar>FunctionFUNCT-1M1"
"cluster f *FUNCT-1K3 g as-term-is decreasingVALUED-0V10"
proof
(*coherence*)
  show "f *FUNCT-1K3 g be decreasingVALUED-0V10"
sorry
qed "sorry"

mtheorem valued_0_cl_123:
  mlet "f be non-increasingVALUED-0V12\<bar>ext-real-valuedVALUED-0V6\<bar>FunctionFUNCT-1M1", "g be non-decreasingVALUED-0V11\<bar>ext-real-valuedVALUED-0V6\<bar>FunctionFUNCT-1M1"
"cluster g *FUNCT-1K3 f as-term-is non-increasingVALUED-0V12"
proof
(*coherence*)
  show "g *FUNCT-1K3 f be non-increasingVALUED-0V12"
sorry
qed "sorry"

mtheorem valued_0_cl_124:
  mlet "f be non-increasingVALUED-0V12\<bar>ext-real-valuedVALUED-0V6\<bar>FunctionFUNCT-1M1", "g be non-decreasingVALUED-0V11\<bar>ext-real-valuedVALUED-0V6\<bar>FunctionFUNCT-1M1"
"cluster f *FUNCT-1K3 g as-term-is non-increasingVALUED-0V12"
proof
(*coherence*)
  show "f *FUNCT-1K3 g be non-increasingVALUED-0V12"
sorry
qed "sorry"

mtheorem valued_0_cl_125:
  mlet "X be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2"
"cluster idPARTFUN1K6 X as-term-is increasingVALUED-0V9 for FunctionFUNCT-2M1-of(X,X)"
proof
(*coherence*)
  show " for it be FunctionFUNCT-2M1-of(X,X) holds it =HIDDENR1 idPARTFUN1K6 X implies it be increasingVALUED-0V9"
sorry
qed "sorry"

mtheorem valued_0_cl_126:
"cluster increasingVALUED-0V9 for sequenceNAT-1M2-of NATNUMBERSK1"
proof
(*existence*)
  show " ex it be sequenceNAT-1M2-of NATNUMBERSK1 st it be increasingVALUED-0V9"
sorry
qed "sorry"

mdef valued_0_def_17 ("subsequenceVALUED-0M1-of  _ " [70]70 ) where
  mlet "s be ManySortedSetPBOOLEM1-of NATNUMBERSK1"
"mode subsequenceVALUED-0M1-of s \<rightarrow> ManySortedSetPBOOLEM1-of NATNUMBERSK1 means
  (\<lambda>it.  ex N be increasingVALUED-0V9\<bar>sequenceNAT-1M2-of NATNUMBERSK1 st it =FUNCT-1R1 s *FUNCT-1K3 N)"
proof-
  (*existence*)
    show " ex it be ManySortedSetPBOOLEM1-of NATNUMBERSK1 st  ex N be increasingVALUED-0V9\<bar>sequenceNAT-1M2-of NATNUMBERSK1 st it =FUNCT-1R1 s *FUNCT-1K3 N"
sorry
qed "sorry"

mlemma valued_0_lm_1:
" for x be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for M be ManySortedSetPBOOLEM1-of NATNUMBERSK1 holds  for s be subsequenceVALUED-0M1-of M holds rngFUNCT-1K2 s c=TARSKIR1 rngFUNCT-1K2 M"
sorry

mtheorem valued_0_cl_127:
  mlet "X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "s be X -valuedRELAT-1V5\<bar>ManySortedSetPBOOLEM1-of NATNUMBERSK1"
"cluster note-that X -valuedRELAT-1V5 for subsequenceVALUED-0M1-of s"
proof
(*coherence*)
  show " for it be subsequenceVALUED-0M1-of s holds it be X -valuedRELAT-1V5"
sorry
qed "sorry"

syntax VALUED_0M2 :: " Set \<Rightarrow>  Set \<Rightarrow> Ty" ("subsequenceVALUED-0M2\<^bsub>'( _ ')\<^esub>-of  _ " [0,70]70)
translations "subsequenceVALUED-0M2\<^bsub>(X)\<^esub>-of s" \<rightharpoonup> "subsequenceVALUED-0M1-of s"

mtheorem valued_0_add_1:
  mlet "X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "s be sequenceNAT-1M2-of X"
"cluster note-that sequenceNAT-1M2-of X for subsequenceVALUED-0M1-of s"
proof
(*coherence*)
  show " for it be subsequenceVALUED-0M1-of s holds it be sequenceNAT-1M2-of X"
sorry
qed "sorry"

syntax VALUED_0K1 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ ^'\\VALUED-0K1\<^bsub>'( _ ')\<^esub>  _ " [164,0,164]164)
translations "s ^\\VALUED-0K1\<^bsub>(X)\<^esub> k" \<rightharpoonup> "s ^\\NAT-1K6 k"

mtheorem valued_0_add_2:
  mlet "X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "s be sequenceNAT-1M2-of X", "k be NatNAT-1M1"
"cluster s ^\\NAT-1K6 k as-term-is subsequenceVALUED-0M2\<^bsub>(X)\<^esub>-of s"
proof
(*coherence*)
  show "s ^\\NAT-1K6 k be subsequenceVALUED-0M2\<^bsub>(X)\<^esub>-of s"
sorry
qed "sorry"

reserve XX for " non emptyXBOOLE-0V1\<bar>setHIDDENM2"
reserve ss, ss1, ss2, ss3 for "sequenceNAT-1M2-of XX"
mtheorem valued_0_th_19:
" for XX be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for ss be sequenceNAT-1M2-of XX holds ss be subsequenceVALUED-0M2\<^bsub>(XX)\<^esub>-of ss"
sorry

mtheorem valued_0_th_20:
" for XX be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for ss1 be sequenceNAT-1M2-of XX holds  for ss2 be sequenceNAT-1M2-of XX holds  for ss3 be sequenceNAT-1M2-of XX holds ss1 be subsequenceVALUED-0M2\<^bsub>(XX)\<^esub>-of ss2 & ss2 be subsequenceVALUED-0M2\<^bsub>(XX)\<^esub>-of ss3 implies ss1 be subsequenceVALUED-0M2\<^bsub>(XX)\<^esub>-of ss3"
sorry

mtheorem valued_0_cl_128:
  mlet "X be setHIDDENM2"
"cluster constantFUNCT-1V5 for sequenceNAT-1M2-of X"
proof
(*existence*)
  show " ex it be sequenceNAT-1M2-of X st it be constantFUNCT-1V5"
sorry
qed "sorry"

mtheorem valued_0_th_21:
" for XX be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for ss be sequenceNAT-1M2-of XX holds  for ss1 be subsequenceVALUED-0M2\<^bsub>(XX)\<^esub>-of ss holds rngRELSET-1K2\<^bsub>(XX)\<^esub> ss1 c=TARSKIR1 rngRELSET-1K2\<^bsub>(XX)\<^esub> ss"
sorry

mtheorem valued_0_cl_129:
  mlet "X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "s be constantFUNCT-1V5\<bar>sequenceNAT-1M2-of X"
"cluster note-that constantFUNCT-1V5 for subsequenceVALUED-0M2\<^bsub>(X)\<^esub>-of s"
proof
(*coherence*)
  show " for it be subsequenceVALUED-0M2\<^bsub>(X)\<^esub>-of s holds it be constantFUNCT-1V5"
sorry
qed "sorry"

syntax VALUED_0K2 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ *VALUED-0K2\<^bsub>'( _ ')\<^esub>  _ " [164,0,164]164)
translations "s *VALUED-0K2\<^bsub>(X)\<^esub> N" \<rightharpoonup> "N *RELAT-1K6 s"

mtheorem valued_0_add_3:
  mlet "X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "N be increasingVALUED-0V9\<bar>sequenceNAT-1M2-of NATNUMBERSK1", "s be sequenceNAT-1M2-of X"
"cluster N *RELAT-1K6 s as-term-is subsequenceVALUED-0M2\<^bsub>(X)\<^esub>-of s"
proof
(*coherence*)
  show "N *RELAT-1K6 s be subsequenceVALUED-0M2\<^bsub>(X)\<^esub>-of s"
    using valued_0_def_17 sorry
qed "sorry"

reserve X, Y for " non emptyXBOOLE-0V1\<bar>setHIDDENM2"
reserve Z for "setHIDDENM2"
reserve s, s1 for "sequenceNAT-1M2-of X"
reserve h, h1 for "PartFuncPARTFUN1M1-of(X,Y)"
reserve h2 for "PartFuncPARTFUN1M1-of(Y,Z)"
reserve N for "increasingVALUED-0V9\<bar>sequenceNAT-1M2-of NATNUMBERSK1"
mtheorem valued_0_th_22:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for Y be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for s be sequenceNAT-1M2-of X holds  for s1 be sequenceNAT-1M2-of X holds  for h be PartFuncPARTFUN1M1-of(X,Y) holds rngRELSET-1K2\<^bsub>(X)\<^esub> s c=TARSKIR1 domRELSET-1K1\<^bsub>(X)\<^esub> h & s1 be subsequenceVALUED-0M2\<^bsub>(X)\<^esub>-of s implies h /*FUNCT-2K8\<^bsub>(omegaORDINAL1K4,Y,X)\<^esub> s1 be subsequenceVALUED-0M2\<^bsub>(Y)\<^esub>-of h /*FUNCT-2K8\<^bsub>(omegaORDINAL1K4,Y,X)\<^esub> s"
sorry

mtheorem valued_0_cl_130:
  mlet "X be with-non-empty-elementSETFAM-1V3\<bar>setHIDDENM2"
"cluster non-emptyFUNCT-1V4 for sequenceNAT-1M2-of X"
proof
(*existence*)
  show " ex it be sequenceNAT-1M2-of X st it be non-emptyFUNCT-1V4"
sorry
qed "sorry"

mtheorem valued_0_cl_131:
  mlet "X be with-non-empty-elementSETFAM-1V3\<bar>setHIDDENM2", "s be non-emptyFUNCT-1V4\<bar>sequenceNAT-1M2-of X"
"cluster note-that non-emptyFUNCT-1V4 for subsequenceVALUED-0M2\<^bsub>(X)\<^esub>-of s"
proof
(*coherence*)
  show " for it be subsequenceVALUED-0M2\<^bsub>(X)\<^esub>-of s holds it be non-emptyFUNCT-1V4"
sorry
qed "sorry"

reserve i, j for "NatNAT-1M1"
syntax VALUED_0V13 :: " Set \<Rightarrow> Ty" ("constantVALUED-0V13\<^bsub>'( _ ')\<^esub>" [0]70)
translations "constantVALUED-0V13\<^bsub>(X)\<^esub>" \<rightharpoonup> "constantFUNCT-1V5"

mtheorem valued_0_def_18:
  mlet "X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "s be sequenceNAT-1M2-of X"
"redefine attr constantVALUED-0V13\<^bsub>(X)\<^esub> for sequenceNAT-1M2-of X means
  (\<lambda>s.  ex x be ElementSUBSET-1M1-of X st  for n be NatNAT-1M1 holds s .NAT-1K8\<^bsub>(X)\<^esub> n =XBOOLE-0R4 x)"
proof
(*compatibility*)
  show " for s be sequenceNAT-1M2-of X holds s be constantVALUED-0V13\<^bsub>(X)\<^esub> iff ( ex x be ElementSUBSET-1M1-of X st  for n be NatNAT-1M1 holds s .NAT-1K8\<^bsub>(X)\<^esub> n =XBOOLE-0R4 x)"
sorry
qed "sorry"

mtheorem valued_0_th_23:
" for i be NatNAT-1M1 holds  for j be NatNAT-1M1 holds  for X be setHIDDENM2 holds  for s be constantFUNCT-1V5\<bar>sequenceNAT-1M2-of X holds s .NAT-1K8\<^bsub>(X)\<^esub> i =XBOOLE-0R4 s .NAT-1K8\<^bsub>(X)\<^esub> j"
sorry

mtheorem valued_0_th_24:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for s be sequenceNAT-1M2-of X holds ( for i be NatNAT-1M1 holds  for j be NatNAT-1M1 holds s .NAT-1K8\<^bsub>(X)\<^esub> i =XBOOLE-0R4 s .NAT-1K8\<^bsub>(X)\<^esub> j) implies s be constantFUNCT-1V5"
   sorry

mtheorem valued_0_th_25:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for s be sequenceNAT-1M2-of X holds ( for i be NatNAT-1M1 holds s .NAT-1K8\<^bsub>(X)\<^esub> i =XBOOLE-0R4 s .NAT-1K8\<^bsub>(X)\<^esub> (i +NAT-1K1 \<one>\<^sub>M)) implies s be constantFUNCT-1V5"
sorry

mtheorem valued_0_th_26:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for s be sequenceNAT-1M2-of X holds  for s1 be sequenceNAT-1M2-of X holds s be constantFUNCT-1V5 & s1 be subsequenceVALUED-0M2\<^bsub>(X)\<^esub>-of s implies s =FUNCT-2R2\<^bsub>(omegaORDINAL1K4,X)\<^esub> s1"
sorry

reserve n for "NatNAT-1M1"
mtheorem valued_0_th_27:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for Y be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for s be sequenceNAT-1M2-of X holds  for h be PartFuncPARTFUN1M1-of(X,Y) holds  for n be NatNAT-1M1 holds rngRELSET-1K2\<^bsub>(X)\<^esub> s c=TARSKIR1 domRELSET-1K1\<^bsub>(X)\<^esub> h implies h /*FUNCT-2K8\<^bsub>(omegaORDINAL1K4,Y,X)\<^esub> s ^\\VALUED-0K1\<^bsub>(Y)\<^esub> n =FUNCT-2R2\<^bsub>(omegaORDINAL1K4,Y)\<^esub> h /*FUNCT-2K8\<^bsub>(omegaORDINAL1K4,Y,X)\<^esub> (s ^\\VALUED-0K1\<^bsub>(X)\<^esub> n)"
sorry

mtheorem valued_0_th_28:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for s be sequenceNAT-1M2-of X holds  for n be NatNAT-1M1 holds s .NAT-1K8\<^bsub>(X)\<^esub> n inTARSKIR2 rngRELSET-1K2\<^bsub>(X)\<^esub> s"
sorry

mtheorem valued_0_th_29:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for Y be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for s be sequenceNAT-1M2-of X holds  for h be PartFuncPARTFUN1M1-of(X,Y) holds  for n be NatNAT-1M1 holds h be totalPARTFUN1V1\<^bsub>(X)\<^esub> implies h /*FUNCT-2K8\<^bsub>(omegaORDINAL1K4,Y,X)\<^esub> (s ^\\VALUED-0K1\<^bsub>(X)\<^esub> n) =FUNCT-2R2\<^bsub>(omegaORDINAL1K4,Y)\<^esub> h /*FUNCT-2K8\<^bsub>(omegaORDINAL1K4,Y,X)\<^esub> s ^\\VALUED-0K1\<^bsub>(Y)\<^esub> n"
sorry

mtheorem valued_0_th_30:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for Y be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for s be sequenceNAT-1M2-of X holds  for h be PartFuncPARTFUN1M1-of(X,Y) holds rngRELSET-1K2\<^bsub>(X)\<^esub> s c=TARSKIR1 domRELSET-1K1\<^bsub>(X)\<^esub> h implies h .:RELSET-1K7\<^bsub>(X,Y)\<^esub> rngRELSET-1K2\<^bsub>(X)\<^esub> s =XBOOLE-0R4 rngRELSET-1K2\<^bsub>(Y)\<^esub> (h /*FUNCT-2K8\<^bsub>(omegaORDINAL1K4,Y,X)\<^esub> s)"
sorry

mtheorem valued_0_th_31:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for Y be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for Z be setHIDDENM2 holds  for s be sequenceNAT-1M2-of X holds  for h1 be PartFuncPARTFUN1M1-of(X,Y) holds  for h2 be PartFuncPARTFUN1M1-of(Y,Z) holds rngRELSET-1K2\<^bsub>(X)\<^esub> s c=TARSKIR1 domRELSET-1K1\<^bsub>(X)\<^esub> (h2 *PARTFUN1K1\<^bsub>(X,Y,Y,Z)\<^esub> h1) implies h2 /*FUNCT-2K8\<^bsub>(omegaORDINAL1K4,Z,Y)\<^esub> (h1 /*FUNCT-2K8\<^bsub>(omegaORDINAL1K4,Y,X)\<^esub> s) =FUNCT-2R2\<^bsub>(omegaORDINAL1K4,Z)\<^esub> (h2 *PARTFUN1K1\<^bsub>(X,Y,Y,Z)\<^esub> h1)/*FUNCT-2K8\<^bsub>(omegaORDINAL1K4,Z,X)\<^esub> s"
sorry

mdef valued_0_def_19 ("zeroedVALUED-0V14" 70 ) where
"attr zeroedVALUED-0V14 for ext-real-valuedVALUED-0V6\<bar>FunctionFUNCT-1M1 means
  (\<lambda>f. f .FUNCT-1K1 {}XBOOLE-0K1 =XBOOLE-0R4 0NUMBERSK6)"..

mtheorem valued_0_cl_132:
"cluster COMPLEXNUMBERSK3 -valuedRELAT-1V5 also-is complex-valuedVALUED-0V1 for RelationRELAT-1M1"
proof
(*coherence*)
  show " for it be RelationRELAT-1M1 holds it be COMPLEXNUMBERSK3 -valuedRELAT-1V5 implies it be complex-valuedVALUED-0V1"
     sorry
qed "sorry"

mtheorem valued_0_cl_133:
"cluster ExtREALXXREAL-0K3 -valuedRELAT-1V5 also-is ext-real-valuedVALUED-0V2 for RelationRELAT-1M1"
proof
(*coherence*)
  show " for it be RelationRELAT-1M1 holds it be ExtREALXXREAL-0K3 -valuedRELAT-1V5 implies it be ext-real-valuedVALUED-0V2"
     sorry
qed "sorry"

mtheorem valued_0_cl_134:
"cluster REALNUMBERSK2 -valuedRELAT-1V5 also-is real-valuedVALUED-0V3 for RelationRELAT-1M1"
proof
(*coherence*)
  show " for it be RelationRELAT-1M1 holds it be REALNUMBERSK2 -valuedRELAT-1V5 implies it be real-valuedVALUED-0V3"
     sorry
qed "sorry"

mtheorem valued_0_cl_135:
"cluster NATNUMBERSK1 -valuedRELAT-1V5 also-is natural-valuedVALUED-0V4 for RelationRELAT-1M1"
proof
(*coherence*)
  show " for it be RelationRELAT-1M1 holds it be NATNUMBERSK1 -valuedRELAT-1V5 implies it be natural-valuedVALUED-0V4"
     sorry
qed "sorry"

abbreviation(input) VALUED_0V15("constantVALUED-0V15" 70) where
  "constantVALUED-0V15 \<equiv> constantFUNCT-1V5"

mtheorem valued_0_def_20:
  mlet "s be ManySortedSetPBOOLEM1-of NATNUMBERSK1"
"redefine attr constantVALUED-0V15 for ManySortedSetPBOOLEM1-of NATNUMBERSK1 means
  (\<lambda>s.  ex x be setHIDDENM2 st  for n be NatNAT-1M1 holds s .FUNCT-1K1 n =XBOOLE-0R4 x)"
proof
(*compatibility*)
  show " for s be ManySortedSetPBOOLEM1-of NATNUMBERSK1 holds s be constantVALUED-0V15 iff ( ex x be setHIDDENM2 st  for n be NatNAT-1M1 holds s .FUNCT-1K1 n =XBOOLE-0R4 x)"
sorry
qed "sorry"

mtheorem valued_0_th_32:
" for x be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for M be ManySortedSetPBOOLEM1-of NATNUMBERSK1 holds  for s be subsequenceVALUED-0M1-of M holds rngFUNCT-1K2 s c=TARSKIR1 rngFUNCT-1K2 M"
  using valued_0_lm_1 sorry

mtheorem valued_0_cl_136:
  mlet "X be setHIDDENM2"
"cluster natural-valuedVALUED-0V8 for ManySortedSetPBOOLEM1-of X"
proof
(*existence*)
  show " ex it be ManySortedSetPBOOLEM1-of X st it be natural-valuedVALUED-0V8"
sorry
qed "sorry"

end
