theory supinf_1
  imports domain_1 xxreal_2
begin
(*begin*)
syntax SUPINF_1M1 :: "Ty" ("R-ealSUPINF-1M1" 70)
translations "R-ealSUPINF-1M1" \<rightharpoonup> "ElementSUBSET-1M1-of ExtREALXXREAL-0K3"

abbreviation(input) SUPINF_1K1("+inftySUPINF-1K1" 300) where
  "+inftySUPINF-1K1 \<equiv> +inftyXXREAL-0K1"

mtheorem supinf_1_add_1:
"cluster +inftyXXREAL-0K1 as-term-is R-ealSUPINF-1M1"
proof
(*coherence*)
  show "+inftyXXREAL-0K1 be R-ealSUPINF-1M1"
    using xxreal_0_def_1 sorry
qed "sorry"

abbreviation(input) SUPINF_1K2("-inftySUPINF-1K2" 300) where
  "-inftySUPINF-1K2 \<equiv> -inftyXXREAL-0K2"

mtheorem supinf_1_add_2:
"cluster -inftyXXREAL-0K2 as-term-is R-ealSUPINF-1M1"
proof
(*coherence*)
  show "-inftyXXREAL-0K2 be R-ealSUPINF-1M1"
    using xxreal_0_def_1 sorry
qed "sorry"

mdef supinf_1_def_1 ("SetMajorantSUPINF-1K3  _ " [164]164 ) where
  mlet "X be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2"
"func SetMajorantSUPINF-1K3 X \<rightarrow> ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 means
  \<lambda>it.  for x be ExtRealXXREAL-0M1 holds x inHIDDENR3 it iff x be UpperBoundXXREAL-2M1-of X"
proof-
  (*existence*)
    show " ex it be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 st  for x be ExtRealXXREAL-0M1 holds x inHIDDENR3 it iff x be UpperBoundXXREAL-2M1-of X"
sorry
  (*uniqueness*)
    show " for it1 be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for it2 be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds ( for x be ExtRealXXREAL-0M1 holds x inHIDDENR3 it1 iff x be UpperBoundXXREAL-2M1-of X) & ( for x be ExtRealXXREAL-0M1 holds x inHIDDENR3 it2 iff x be UpperBoundXXREAL-2M1-of X) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mtheorem supinf_1_cl_1:
  mlet "X be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2"
"cluster SetMajorantSUPINF-1K3 X as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "SetMajorantSUPINF-1K3 X be  non emptyXBOOLE-0V1"
sorry
qed "sorry"

mtheorem supinf_1_th_1:
" for X be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for Y be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds X c=MEMBEREDR2 Y implies ( for x be ExtRealXXREAL-0M1 holds x inHIDDENR3 SetMajorantSUPINF-1K3 Y implies x inHIDDENR3 SetMajorantSUPINF-1K3 X)"
sorry

mdef supinf_1_def_2 ("SetMinorantSUPINF-1K4  _ " [164]164 ) where
  mlet "X be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2"
"func SetMinorantSUPINF-1K4 X \<rightarrow> ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 means
  \<lambda>it.  for x be ExtRealXXREAL-0M1 holds x inHIDDENR3 it iff x be LowerBoundXXREAL-2M2-of X"
proof-
  (*existence*)
    show " ex it be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 st  for x be ExtRealXXREAL-0M1 holds x inHIDDENR3 it iff x be LowerBoundXXREAL-2M2-of X"
sorry
  (*uniqueness*)
    show " for it1 be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for it2 be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds ( for x be ExtRealXXREAL-0M1 holds x inHIDDENR3 it1 iff x be LowerBoundXXREAL-2M2-of X) & ( for x be ExtRealXXREAL-0M1 holds x inHIDDENR3 it2 iff x be LowerBoundXXREAL-2M2-of X) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mtheorem supinf_1_cl_2:
  mlet "X be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2"
"cluster SetMinorantSUPINF-1K4 X as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "SetMinorantSUPINF-1K4 X be  non emptyXBOOLE-0V1"
sorry
qed "sorry"

mtheorem supinf_1_th_2:
" for X be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for Y be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds X c=MEMBEREDR2 Y implies ( for x be ExtRealXXREAL-0M1 holds x inHIDDENR3 SetMinorantSUPINF-1K4 Y implies x inHIDDENR3 SetMinorantSUPINF-1K4 X)"
sorry

mtheorem supinf_1_th_3:
" for X be  non emptyXBOOLE-0V1\<bar>ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds supXXREAL-2K1 X =HIDDENR1 infXXREAL-2K2 (SetMajorantSUPINF-1K3 X) & infXXREAL-2K2 X =HIDDENR1 supXXREAL-2K1 (SetMinorantSUPINF-1K4 X)"
sorry

mtheorem supinf_1_cl_3:
  mlet "X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster  non emptyXBOOLE-0V1\<bar>with-non-empty-elementsSETFAM-1V1 for Subset-FamilySETFAM-1M1-of X"
proof
(*existence*)
  show " ex it be Subset-FamilySETFAM-1M1-of X st it be  non emptyXBOOLE-0V1\<bar>with-non-empty-elementsSETFAM-1V1"
sorry
qed "sorry"

syntax SUPINF_1M2 :: " Set \<Rightarrow> Ty" ("bool-DOMAINSUPINF-1M2-of  _ " [70]70)
translations "bool-DOMAINSUPINF-1M2-of X" \<rightharpoonup> " non emptyXBOOLE-0V1\<bar>with-non-empty-elementsSETFAM-1V1\<bar>Subset-FamilySETFAM-1M1-of X"

mdef supinf_1_def_3 ("SUPSUPINF-1K5  _ " [164]164 ) where
  mlet "F be bool-DOMAINSUPINF-1M2-of ExtREALXXREAL-0K3"
"func SUPSUPINF-1K5 F \<rightarrow> ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 means
  \<lambda>it.  for a be ExtRealXXREAL-0M1 holds a inHIDDENR3 it iff ( ex A be  non emptyXBOOLE-0V1\<bar>ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 st A inHIDDENR3 F & a =HIDDENR1 supXXREAL-2K1 A)"
proof-
  (*existence*)
    show " ex it be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 st  for a be ExtRealXXREAL-0M1 holds a inHIDDENR3 it iff ( ex A be  non emptyXBOOLE-0V1\<bar>ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 st A inHIDDENR3 F & a =HIDDENR1 supXXREAL-2K1 A)"
sorry
  (*uniqueness*)
    show " for it1 be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for it2 be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds ( for a be ExtRealXXREAL-0M1 holds a inHIDDENR3 it1 iff ( ex A be  non emptyXBOOLE-0V1\<bar>ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 st A inHIDDENR3 F & a =HIDDENR1 supXXREAL-2K1 A)) & ( for a be ExtRealXXREAL-0M1 holds a inHIDDENR3 it2 iff ( ex A be  non emptyXBOOLE-0V1\<bar>ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 st A inHIDDENR3 F & a =HIDDENR1 supXXREAL-2K1 A)) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mtheorem supinf_1_cl_4:
  mlet "F be bool-DOMAINSUPINF-1M2-of ExtREALXXREAL-0K3"
"cluster SUPSUPINF-1K5 F as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "SUPSUPINF-1K5 F be  non emptyXBOOLE-0V1"
sorry
qed "sorry"

mtheorem supinf_1_th_4:
" for F be bool-DOMAINSUPINF-1M2-of ExtREALXXREAL-0K3 holds  for S be  non emptyXBOOLE-0V1\<bar>ext-real-memberedMEMBEREDV2\<bar>numberORDINAL1M2 holds S =MEMBEREDR8 unionSETFAM-1K5\<^bsub>(ExtREALXXREAL-0K3)\<^esub> F implies supXXREAL-2K1 S be UpperBoundXXREAL-2M1-of SUPSUPINF-1K5 F"
sorry

mtheorem supinf_1_th_5:
" for F be bool-DOMAINSUPINF-1M2-of ExtREALXXREAL-0K3 holds  for S be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds S =MEMBEREDR8 unionSETFAM-1K5\<^bsub>(ExtREALXXREAL-0K3)\<^esub> F implies supXXREAL-2K1 (SUPSUPINF-1K5 F) be UpperBoundXXREAL-2M1-of S"
sorry

mtheorem supinf_1_th_6:
" for F be bool-DOMAINSUPINF-1M2-of ExtREALXXREAL-0K3 holds  for S be  non emptyXBOOLE-0V1\<bar>ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds S =MEMBEREDR8 unionSETFAM-1K5\<^bsub>(ExtREALXXREAL-0K3)\<^esub> F implies supXXREAL-2K1 S =HIDDENR1 supXXREAL-2K1 (SUPSUPINF-1K5 F)"
sorry

mdef supinf_1_def_4 ("INFSUPINF-1K6  _ " [164]164 ) where
  mlet "F be bool-DOMAINSUPINF-1M2-of ExtREALXXREAL-0K3"
"func INFSUPINF-1K6 F \<rightarrow> ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 means
  \<lambda>it.  for a be ExtRealXXREAL-0M1 holds a inHIDDENR3 it iff ( ex A be  non emptyXBOOLE-0V1\<bar>ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 st A inHIDDENR3 F & a =HIDDENR1 infXXREAL-2K2 A)"
proof-
  (*existence*)
    show " ex it be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 st  for a be ExtRealXXREAL-0M1 holds a inHIDDENR3 it iff ( ex A be  non emptyXBOOLE-0V1\<bar>ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 st A inHIDDENR3 F & a =HIDDENR1 infXXREAL-2K2 A)"
sorry
  (*uniqueness*)
    show " for it1 be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds  for it2 be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds ( for a be ExtRealXXREAL-0M1 holds a inHIDDENR3 it1 iff ( ex A be  non emptyXBOOLE-0V1\<bar>ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 st A inHIDDENR3 F & a =HIDDENR1 infXXREAL-2K2 A)) & ( for a be ExtRealXXREAL-0M1 holds a inHIDDENR3 it2 iff ( ex A be  non emptyXBOOLE-0V1\<bar>ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 st A inHIDDENR3 F & a =HIDDENR1 infXXREAL-2K2 A)) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mtheorem supinf_1_cl_5:
  mlet "F be bool-DOMAINSUPINF-1M2-of ExtREALXXREAL-0K3"
"cluster INFSUPINF-1K6 F as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "INFSUPINF-1K6 F be  non emptyXBOOLE-0V1"
sorry
qed "sorry"

mtheorem supinf_1_th_7:
" for F be bool-DOMAINSUPINF-1M2-of ExtREALXXREAL-0K3 holds  for S be  non emptyXBOOLE-0V1\<bar>ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds S =MEMBEREDR8 unionSETFAM-1K5\<^bsub>(ExtREALXXREAL-0K3)\<^esub> F implies infXXREAL-2K2 S be LowerBoundXXREAL-2M2-of INFSUPINF-1K6 F"
sorry

mtheorem supinf_1_th_8:
" for F be bool-DOMAINSUPINF-1M2-of ExtREALXXREAL-0K3 holds  for S be ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds S =MEMBEREDR8 unionSETFAM-1K5\<^bsub>(ExtREALXXREAL-0K3)\<^esub> F implies infXXREAL-2K2 (INFSUPINF-1K6 F) be LowerBoundXXREAL-2M2-of S"
sorry

mtheorem supinf_1_th_9:
" for F be bool-DOMAINSUPINF-1M2-of ExtREALXXREAL-0K3 holds  for S be  non emptyXBOOLE-0V1\<bar>ext-real-memberedMEMBEREDV2\<bar>setHIDDENM2 holds S =MEMBEREDR8 unionSETFAM-1K5\<^bsub>(ExtREALXXREAL-0K3)\<^esub> F implies infXXREAL-2K2 S =HIDDENR1 infXXREAL-2K2 (INFSUPINF-1K6 F)"
sorry

end
