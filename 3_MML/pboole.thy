theory pboole
  imports funct_4 classes1
begin
(*begin*)
reserve i, j, e, u for "objectHIDDENM1"
mtheorem pboole_th_1:
" for f be FunctionFUNCT-1M1 holds f be non-emptyFUNCT-1V4 implies rngFUNCT-1K2 f be with-non-empty-elementsSETFAM-1V1"
   sorry

mtheorem pboole_th_2:
" for f be FunctionFUNCT-1M1 holds f be empty-yieldingFUNCT-1V3 iff f =FUNCT-1R1 {}XBOOLE-0K1 or rngFUNCT-1K2 f =XBOOLE-0R4 {TARSKIK1 {}XBOOLE-0K1 }"
sorry

reserve I for "setHIDDENM2"
mtheorem pboole_cl_1:
  mlet "I be setHIDDENM2"
"cluster totalPARTFUN1V1\<^bsub>(I)\<^esub> for I -definedRELAT-1V4\<bar>FunctionFUNCT-1M1"
proof
(*existence*)
  show " ex it be I -definedRELAT-1V4\<bar>FunctionFUNCT-1M1 st it be totalPARTFUN1V1\<^bsub>(I)\<^esub>"
sorry
qed "sorry"

syntax PBOOLEM1 :: " Set \<Rightarrow> Ty" ("ManySortedSetPBOOLEM1-of  _ " [70]70)
translations "ManySortedSetPBOOLEM1-of I" \<rightharpoonup> "totalPARTFUN1V1\<^bsub>(I)\<^esub>\<bar>I -definedRELAT-1V4\<bar>FunctionFUNCT-1M1"

reserve x, X, Y, Z, V for "ManySortedSetPBOOLEM1-of I"
theorem pboole_sch_1:
  fixes Af0 Ff1 
  assumes
[ty]: "Af0 be setHIDDENM2" and
  [ty_func]: "\<And> x1. x1 be objectHIDDENM1 \<Longrightarrow> Ff1(x1) be setHIDDENM2" and
   A1: " for e be objectHIDDENM1 holds e inHIDDENR3 Af0 implies Ff1(e) <>HIDDENR2 {}XBOOLE-0K1"
  shows " ex f be ManySortedSetPBOOLEM1-of Af0 st  for e be objectHIDDENM1 holds e inHIDDENR3 Af0 implies f .FUNCT-1K1 e inTARSKIR2 Ff1(e)"
sorry

mdef pboole_def_1 (" _ inPBOOLER1\<^bsub>'( _ ')\<^esub>  _ " [50,0,50]50 ) where
  mlet "I be setHIDDENM2", "X be ManySortedSetPBOOLEM1-of I", "Y be ManySortedSetPBOOLEM1-of I"
"pred X inPBOOLER1\<^bsub>(I)\<^esub> Y means
   for i be objectHIDDENM1 holds i inHIDDENR3 I implies X .FUNCT-1K1 i inTARSKIR2 Y .FUNCT-1K1 i"..

mdef pboole_def_2 (" _ c=PBOOLER2\<^bsub>'( _ ')\<^esub>  _ " [50,0,50]50 ) where
  mlet "I be setHIDDENM2", "X be ManySortedSetPBOOLEM1-of I", "Y be ManySortedSetPBOOLEM1-of I"
"pred X c=PBOOLER2\<^bsub>(I)\<^esub> Y means
   for i be objectHIDDENM1 holds i inHIDDENR3 I implies X .FUNCT-1K1 i c=TARSKIR1 Y .FUNCT-1K1 i"..

mtheorem PBOOLER2_reflexivity:
  mlet "I be setHIDDENM2"
" for Y be ManySortedSetPBOOLEM1-of I holds Y c=PBOOLER2\<^bsub>(I)\<^esub> Y"
sorry

abbreviation(input) PBOOLER3(" _ inPBOOLER3\<^bsub>'( _ ')\<^esub>  _ " [50,0,50]50) where
  "X inPBOOLER3\<^bsub>(I)\<^esub> Y \<equiv> X inPBOOLER1\<^bsub>(I)\<^esub> Y"

mtheorem PBOOLER3_asymmetry:
  mlet "I be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
" for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds X inPBOOLER3\<^bsub>(I)\<^esub> Y implies  not Y inPBOOLER3\<^bsub>(I)\<^esub> X"
sorry

theorem pboole_sch_2:
  fixes If0 Af0 Pp2 
  assumes
[ty]: "If0 be setHIDDENM2" and
  [ty]: "Af0 be ManySortedSetPBOOLEM1-of If0"
  shows " ex X be ManySortedSetPBOOLEM1-of If0 st  for i be objectHIDDENM1 holds i inHIDDENR3 If0 implies ( for e be objectHIDDENM1 holds e inHIDDENR3 X .FUNCT-1K1 i iff e inHIDDENR3 Af0 .FUNCT-1K1 i & Pp2(i,e))"
sorry

mtheorem pboole_th_3:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds ( for i be objectHIDDENM1 holds i inHIDDENR3 I implies X .FUNCT-1K1 i =XBOOLE-0R4 Y .FUNCT-1K1 i) implies X =FUNCT-1R1 Y"
sorry

mdef pboole_def_3 ("EmptyMSPBOOLEK1  _ " [350]350 ) where
  mlet "I be setHIDDENM2"
"func EmptyMSPBOOLEK1 I \<rightarrow> ManySortedSetPBOOLEM1-of I equals
  I -->FUNCOP-1K7 {}XBOOLE-0K1"
proof-
  (*coherence*)
    show "I -->FUNCOP-1K7 {}XBOOLE-0K1 be ManySortedSetPBOOLEM1-of I"
       sorry
qed "sorry"

mdef pboole_def_4 (" _ '('\\'/')PBOOLEK2\<^bsub>'( _ ')\<^esub>  _ " [132,0,132]132 ) where
  mlet "I be setHIDDENM2", "X be ManySortedSetPBOOLEM1-of I", "Y be ManySortedSetPBOOLEM1-of I"
"func X (\\/)PBOOLEK2\<^bsub>(I)\<^esub> Y \<rightarrow> ManySortedSetPBOOLEM1-of I means
  \<lambda>it.  for i be objectHIDDENM1 holds i inHIDDENR3 I implies it .FUNCT-1K1 i =XBOOLE-0R4 X .FUNCT-1K1 i \\/XBOOLE-0K2 Y .FUNCT-1K1 i"
proof-
  (*existence*)
    show " ex it be ManySortedSetPBOOLEM1-of I st  for i be objectHIDDENM1 holds i inHIDDENR3 I implies it .FUNCT-1K1 i =XBOOLE-0R4 X .FUNCT-1K1 i \\/XBOOLE-0K2 Y .FUNCT-1K1 i"
sorry
  (*uniqueness*)
    show " for it1 be ManySortedSetPBOOLEM1-of I holds  for it2 be ManySortedSetPBOOLEM1-of I holds ( for i be objectHIDDENM1 holds i inHIDDENR3 I implies it1 .FUNCT-1K1 i =XBOOLE-0R4 X .FUNCT-1K1 i \\/XBOOLE-0K2 Y .FUNCT-1K1 i) & ( for i be objectHIDDENM1 holds i inHIDDENR3 I implies it2 .FUNCT-1K1 i =XBOOLE-0R4 X .FUNCT-1K1 i \\/XBOOLE-0K2 Y .FUNCT-1K1 i) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mtheorem PBOOLEK2_commutativity:
  mlet "I be setHIDDENM2"
" for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds X (\\/)PBOOLEK2\<^bsub>(I)\<^esub> Y =HIDDENR1 Y (\\/)PBOOLEK2\<^bsub>(I)\<^esub> X"
sorry

mtheorem PBOOLEK2_idempotence:
  mlet "I be setHIDDENM2"
" for Y be ManySortedSetPBOOLEM1-of I holds Y =HIDDENR1 Y (\\/)PBOOLEK2\<^bsub>(I)\<^esub> Y"
sorry

mdef pboole_def_5 (" _ '('/'\\')PBOOLEK3\<^bsub>'( _ ')\<^esub>  _ " [164,0,164]164 ) where
  mlet "I be setHIDDENM2", "X be ManySortedSetPBOOLEM1-of I", "Y be ManySortedSetPBOOLEM1-of I"
"func X (/\\)PBOOLEK3\<^bsub>(I)\<^esub> Y \<rightarrow> ManySortedSetPBOOLEM1-of I means
  \<lambda>it.  for i be objectHIDDENM1 holds i inHIDDENR3 I implies it .FUNCT-1K1 i =XBOOLE-0R4 X .FUNCT-1K1 i /\\XBOOLE-0K3 Y .FUNCT-1K1 i"
proof-
  (*existence*)
    show " ex it be ManySortedSetPBOOLEM1-of I st  for i be objectHIDDENM1 holds i inHIDDENR3 I implies it .FUNCT-1K1 i =XBOOLE-0R4 X .FUNCT-1K1 i /\\XBOOLE-0K3 Y .FUNCT-1K1 i"
sorry
  (*uniqueness*)
    show " for it1 be ManySortedSetPBOOLEM1-of I holds  for it2 be ManySortedSetPBOOLEM1-of I holds ( for i be objectHIDDENM1 holds i inHIDDENR3 I implies it1 .FUNCT-1K1 i =XBOOLE-0R4 X .FUNCT-1K1 i /\\XBOOLE-0K3 Y .FUNCT-1K1 i) & ( for i be objectHIDDENM1 holds i inHIDDENR3 I implies it2 .FUNCT-1K1 i =XBOOLE-0R4 X .FUNCT-1K1 i /\\XBOOLE-0K3 Y .FUNCT-1K1 i) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mtheorem PBOOLEK3_commutativity:
  mlet "I be setHIDDENM2"
" for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds X (/\\)PBOOLEK3\<^bsub>(I)\<^esub> Y =HIDDENR1 Y (/\\)PBOOLEK3\<^bsub>(I)\<^esub> X"
sorry

mtheorem PBOOLEK3_idempotence:
  mlet "I be setHIDDENM2"
" for Y be ManySortedSetPBOOLEM1-of I holds Y =HIDDENR1 Y (/\\)PBOOLEK3\<^bsub>(I)\<^esub> Y"
sorry

mdef pboole_def_6 (" _ '('\\')PBOOLEK4\<^bsub>'( _ ')\<^esub>  _ " [132,0,132]132 ) where
  mlet "I be setHIDDENM2", "X be ManySortedSetPBOOLEM1-of I", "Y be ManySortedSetPBOOLEM1-of I"
"func X (\\)PBOOLEK4\<^bsub>(I)\<^esub> Y \<rightarrow> ManySortedSetPBOOLEM1-of I means
  \<lambda>it.  for i be objectHIDDENM1 holds i inHIDDENR3 I implies it .FUNCT-1K1 i =XBOOLE-0R4 X .FUNCT-1K1 i \\SUBSET-1K6 Y .FUNCT-1K1 i"
proof-
  (*existence*)
    show " ex it be ManySortedSetPBOOLEM1-of I st  for i be objectHIDDENM1 holds i inHIDDENR3 I implies it .FUNCT-1K1 i =XBOOLE-0R4 X .FUNCT-1K1 i \\SUBSET-1K6 Y .FUNCT-1K1 i"
sorry
  (*uniqueness*)
    show " for it1 be ManySortedSetPBOOLEM1-of I holds  for it2 be ManySortedSetPBOOLEM1-of I holds ( for i be objectHIDDENM1 holds i inHIDDENR3 I implies it1 .FUNCT-1K1 i =XBOOLE-0R4 X .FUNCT-1K1 i \\SUBSET-1K6 Y .FUNCT-1K1 i) & ( for i be objectHIDDENM1 holds i inHIDDENR3 I implies it2 .FUNCT-1K1 i =XBOOLE-0R4 X .FUNCT-1K1 i \\SUBSET-1K6 Y .FUNCT-1K1 i) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mdef pboole_def_7 (" _ overlapsPBOOLER4\<^bsub>'( _ ')\<^esub>  _ " [50,0,50]50 ) where
  mlet "I be setHIDDENM2", "X be ManySortedSetPBOOLEM1-of I", "Y be ManySortedSetPBOOLEM1-of I"
"pred X overlapsPBOOLER4\<^bsub>(I)\<^esub> Y means
   for i be objectHIDDENM1 holds i inHIDDENR3 I implies X .FUNCT-1K1 i meetsXBOOLE-0R5 Y .FUNCT-1K1 i"..

mtheorem PBOOLER4_symmetry:
  mlet "I be setHIDDENM2"
" for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds X overlapsPBOOLER4\<^bsub>(I)\<^esub> Y implies Y overlapsPBOOLER4\<^bsub>(I)\<^esub> X"
sorry

mdef pboole_def_8 (" _ missesPBOOLER5\<^bsub>'( _ ')\<^esub>  _ " [50,0,50]50 ) where
  mlet "I be setHIDDENM2", "X be ManySortedSetPBOOLEM1-of I", "Y be ManySortedSetPBOOLEM1-of I"
"pred X missesPBOOLER5\<^bsub>(I)\<^esub> Y means
   for i be objectHIDDENM1 holds i inHIDDENR3 I implies X .FUNCT-1K1 i missesXBOOLE-0R1 Y .FUNCT-1K1 i"..

mtheorem PBOOLER5_symmetry:
  mlet "I be setHIDDENM2"
" for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds X missesPBOOLER5\<^bsub>(I)\<^esub> Y implies Y missesPBOOLER5\<^bsub>(I)\<^esub> X"
sorry

syntax PBOOLER6 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> o" (" _ meetsPBOOLER6\<^bsub>'( _ ')\<^esub>  _ " [50,0,50]50)
translations "X meetsPBOOLER6\<^bsub>(I)\<^esub> Y" \<rightharpoonup> " not X missesPBOOLER5\<^bsub>(I)\<^esub> Y"

mdef pboole_def_9 (" _ '('\\+'\\')PBOOLEK5\<^bsub>'( _ ')\<^esub>  _ " [130,0,130]130 ) where
  mlet "I be setHIDDENM2", "X be ManySortedSetPBOOLEM1-of I", "Y be ManySortedSetPBOOLEM1-of I"
"func X (\\+\\)PBOOLEK5\<^bsub>(I)\<^esub> Y \<rightarrow> ManySortedSetPBOOLEM1-of I equals
  (X (\\)PBOOLEK4\<^bsub>(I)\<^esub> Y)(\\/)PBOOLEK2\<^bsub>(I)\<^esub> (Y (\\)PBOOLEK4\<^bsub>(I)\<^esub> X)"
proof-
  (*coherence*)
    show "(X (\\)PBOOLEK4\<^bsub>(I)\<^esub> Y)(\\/)PBOOLEK2\<^bsub>(I)\<^esub> (Y (\\)PBOOLEK4\<^bsub>(I)\<^esub> X) be ManySortedSetPBOOLEM1-of I"
       sorry
qed "sorry"

mtheorem PBOOLEK5_commutativity:
  mlet "I be setHIDDENM2"
" for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds X (\\+\\)PBOOLEK5\<^bsub>(I)\<^esub> Y =HIDDENR1 Y (\\+\\)PBOOLEK5\<^bsub>(I)\<^esub> X"
sorry

mtheorem pboole_th_4:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds  for i be objectHIDDENM1 holds i inHIDDENR3 I implies (X (\\+\\)PBOOLEK5\<^bsub>(I)\<^esub> Y).FUNCT-1K1 i =XBOOLE-0R4 X .FUNCT-1K1 i \\+\\XBOOLE-0K5 Y .FUNCT-1K1 i"
sorry

mtheorem pboole_th_5:
" for I be setHIDDENM2 holds  for i be objectHIDDENM1 holds EmptyMSPBOOLEK1 I .FUNCT-1K1 i =XBOOLE-0R4 {}XBOOLE-0K1"
sorry

mtheorem pboole_th_6:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds ( for i be objectHIDDENM1 holds i inHIDDENR3 I implies X .FUNCT-1K1 i =XBOOLE-0R4 {}XBOOLE-0K1) implies X =FUNCT-1R1 EmptyMSPBOOLEK1 I"
sorry

mtheorem pboole_th_7:
" for I be setHIDDENM2 holds  for x be ManySortedSetPBOOLEM1-of I holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds x inPBOOLER1\<^bsub>(I)\<^esub> X or x inPBOOLER1\<^bsub>(I)\<^esub> Y implies x inPBOOLER1\<^bsub>(I)\<^esub> X (\\/)PBOOLEK2\<^bsub>(I)\<^esub> Y"
sorry

mtheorem pboole_th_8:
" for I be setHIDDENM2 holds  for x be ManySortedSetPBOOLEM1-of I holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds x inPBOOLER1\<^bsub>(I)\<^esub> X (/\\)PBOOLEK3\<^bsub>(I)\<^esub> Y iff x inPBOOLER1\<^bsub>(I)\<^esub> X & x inPBOOLER1\<^bsub>(I)\<^esub> Y"
sorry

mtheorem pboole_th_9:
" for I be setHIDDENM2 holds  for x be ManySortedSetPBOOLEM1-of I holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds x inPBOOLER1\<^bsub>(I)\<^esub> X & X c=PBOOLER2\<^bsub>(I)\<^esub> Y implies x inPBOOLER1\<^bsub>(I)\<^esub> Y"
sorry

mtheorem pboole_th_10:
" for I be setHIDDENM2 holds  for x be ManySortedSetPBOOLEM1-of I holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds x inPBOOLER1\<^bsub>(I)\<^esub> X & x inPBOOLER1\<^bsub>(I)\<^esub> Y implies X overlapsPBOOLER4\<^bsub>(I)\<^esub> Y"
sorry

mtheorem pboole_th_11:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds X overlapsPBOOLER4\<^bsub>(I)\<^esub> Y implies ( ex x be ManySortedSetPBOOLEM1-of I st x inPBOOLER1\<^bsub>(I)\<^esub> X & x inPBOOLER1\<^bsub>(I)\<^esub> Y)"
sorry

mtheorem pboole_th_12:
" for I be setHIDDENM2 holds  for x be ManySortedSetPBOOLEM1-of I holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds x inPBOOLER1\<^bsub>(I)\<^esub> X (\\)PBOOLEK4\<^bsub>(I)\<^esub> Y implies x inPBOOLER1\<^bsub>(I)\<^esub> X"
sorry

(*begin*)
mlemma pboole_lm_1:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds X c=PBOOLER2\<^bsub>(I)\<^esub> Y & Y c=PBOOLER2\<^bsub>(I)\<^esub> X implies X =FUNCT-1R1 Y"
sorry

syntax PBOOLER7 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> o" (" _ =PBOOLER7\<^bsub>'( _ ')\<^esub>  _ " [50,0,50]50)
translations "X =PBOOLER7\<^bsub>(I)\<^esub> Y" \<rightharpoonup> "X =HIDDENR1 Y"

mtheorem pboole_def_10:
  mlet "I be setHIDDENM2", "X be ManySortedSetPBOOLEM1-of I", "Y be ManySortedSetPBOOLEM1-of I"
"redefine pred X =PBOOLER7\<^bsub>(I)\<^esub> Y means
   for i be objectHIDDENM1 holds i inHIDDENR3 I implies X .FUNCT-1K1 i =XBOOLE-0R4 Y .FUNCT-1K1 i"
proof
(*compatibility*)
  show "X =PBOOLER7\<^bsub>(I)\<^esub> Y iff ( for i be objectHIDDENM1 holds i inHIDDENR3 I implies X .FUNCT-1K1 i =XBOOLE-0R4 Y .FUNCT-1K1 i)"
    using pboole_th_3 sorry
qed "sorry"

mtheorem pboole_th_13:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds  for Z be ManySortedSetPBOOLEM1-of I holds X c=PBOOLER2\<^bsub>(I)\<^esub> Y & Y c=PBOOLER2\<^bsub>(I)\<^esub> Z implies X c=PBOOLER2\<^bsub>(I)\<^esub> Z"
sorry

mtheorem pboole_th_14:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds X c=PBOOLER2\<^bsub>(I)\<^esub> X (\\/)PBOOLEK2\<^bsub>(I)\<^esub> Y"
sorry

mtheorem pboole_th_15:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds X (/\\)PBOOLEK3\<^bsub>(I)\<^esub> Y c=PBOOLER2\<^bsub>(I)\<^esub> X"
sorry

mtheorem pboole_th_16:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds  for Z be ManySortedSetPBOOLEM1-of I holds X c=PBOOLER2\<^bsub>(I)\<^esub> Z & Y c=PBOOLER2\<^bsub>(I)\<^esub> Z implies X (\\/)PBOOLEK2\<^bsub>(I)\<^esub> Y c=PBOOLER2\<^bsub>(I)\<^esub> Z"
sorry

mtheorem pboole_th_17:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds  for Z be ManySortedSetPBOOLEM1-of I holds Z c=PBOOLER2\<^bsub>(I)\<^esub> X & Z c=PBOOLER2\<^bsub>(I)\<^esub> Y implies Z c=PBOOLER2\<^bsub>(I)\<^esub> X (/\\)PBOOLEK3\<^bsub>(I)\<^esub> Y"
sorry

mtheorem pboole_th_18:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds  for Z be ManySortedSetPBOOLEM1-of I holds X c=PBOOLER2\<^bsub>(I)\<^esub> Y implies X (\\/)PBOOLEK2\<^bsub>(I)\<^esub> Z c=PBOOLER2\<^bsub>(I)\<^esub> Y (\\/)PBOOLEK2\<^bsub>(I)\<^esub> Z"
sorry

mtheorem pboole_th_19:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds  for Z be ManySortedSetPBOOLEM1-of I holds X c=PBOOLER2\<^bsub>(I)\<^esub> Y implies X (/\\)PBOOLEK3\<^bsub>(I)\<^esub> Z c=PBOOLER2\<^bsub>(I)\<^esub> Y (/\\)PBOOLEK3\<^bsub>(I)\<^esub> Z"
sorry

mtheorem pboole_th_20:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds  for Z be ManySortedSetPBOOLEM1-of I holds  for V be ManySortedSetPBOOLEM1-of I holds X c=PBOOLER2\<^bsub>(I)\<^esub> Y & Z c=PBOOLER2\<^bsub>(I)\<^esub> V implies X (\\/)PBOOLEK2\<^bsub>(I)\<^esub> Z c=PBOOLER2\<^bsub>(I)\<^esub> Y (\\/)PBOOLEK2\<^bsub>(I)\<^esub> V"
sorry

mtheorem pboole_th_21:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds  for Z be ManySortedSetPBOOLEM1-of I holds  for V be ManySortedSetPBOOLEM1-of I holds X c=PBOOLER2\<^bsub>(I)\<^esub> Y & Z c=PBOOLER2\<^bsub>(I)\<^esub> V implies X (/\\)PBOOLEK3\<^bsub>(I)\<^esub> Z c=PBOOLER2\<^bsub>(I)\<^esub> Y (/\\)PBOOLEK3\<^bsub>(I)\<^esub> V"
sorry

mtheorem pboole_th_22:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds X c=PBOOLER2\<^bsub>(I)\<^esub> Y implies X (\\/)PBOOLEK2\<^bsub>(I)\<^esub> Y =PBOOLER7\<^bsub>(I)\<^esub> Y"
sorry

mtheorem pboole_th_23:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds X c=PBOOLER2\<^bsub>(I)\<^esub> Y implies X (/\\)PBOOLEK3\<^bsub>(I)\<^esub> Y =PBOOLER7\<^bsub>(I)\<^esub> X"
sorry

mtheorem pboole_th_24:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds  for Z be ManySortedSetPBOOLEM1-of I holds X (/\\)PBOOLEK3\<^bsub>(I)\<^esub> Y c=PBOOLER2\<^bsub>(I)\<^esub> X (\\/)PBOOLEK2\<^bsub>(I)\<^esub> Z"
sorry

mtheorem pboole_th_25:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds  for Z be ManySortedSetPBOOLEM1-of I holds X c=PBOOLER2\<^bsub>(I)\<^esub> Z implies X (\\/)PBOOLEK2\<^bsub>(I)\<^esub> Y (/\\)PBOOLEK3\<^bsub>(I)\<^esub> Z =PBOOLER7\<^bsub>(I)\<^esub> (X (\\/)PBOOLEK2\<^bsub>(I)\<^esub> Y)(/\\)PBOOLEK3\<^bsub>(I)\<^esub> Z"
sorry

mtheorem pboole_th_26:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds  for Z be ManySortedSetPBOOLEM1-of I holds X =PBOOLER7\<^bsub>(I)\<^esub> Y (\\/)PBOOLEK2\<^bsub>(I)\<^esub> Z iff (Y c=PBOOLER2\<^bsub>(I)\<^esub> X & Z c=PBOOLER2\<^bsub>(I)\<^esub> X) & ( for V be ManySortedSetPBOOLEM1-of I holds Y c=PBOOLER2\<^bsub>(I)\<^esub> V & Z c=PBOOLER2\<^bsub>(I)\<^esub> V implies X c=PBOOLER2\<^bsub>(I)\<^esub> V)"
sorry

mtheorem pboole_th_27:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds  for Z be ManySortedSetPBOOLEM1-of I holds X =PBOOLER7\<^bsub>(I)\<^esub> Y (/\\)PBOOLEK3\<^bsub>(I)\<^esub> Z iff (X c=PBOOLER2\<^bsub>(I)\<^esub> Y & X c=PBOOLER2\<^bsub>(I)\<^esub> Z) & ( for V be ManySortedSetPBOOLEM1-of I holds V c=PBOOLER2\<^bsub>(I)\<^esub> Y & V c=PBOOLER2\<^bsub>(I)\<^esub> Z implies V c=PBOOLER2\<^bsub>(I)\<^esub> X)"
sorry

mtheorem pboole_th_28:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds  for Z be ManySortedSetPBOOLEM1-of I holds (X (\\/)PBOOLEK2\<^bsub>(I)\<^esub> Y)(\\/)PBOOLEK2\<^bsub>(I)\<^esub> Z =PBOOLER7\<^bsub>(I)\<^esub> X (\\/)PBOOLEK2\<^bsub>(I)\<^esub> (Y (\\/)PBOOLEK2\<^bsub>(I)\<^esub> Z)"
sorry

mtheorem pboole_th_29:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds  for Z be ManySortedSetPBOOLEM1-of I holds (X (/\\)PBOOLEK3\<^bsub>(I)\<^esub> Y)(/\\)PBOOLEK3\<^bsub>(I)\<^esub> Z =PBOOLER7\<^bsub>(I)\<^esub> X (/\\)PBOOLEK3\<^bsub>(I)\<^esub> (Y (/\\)PBOOLEK3\<^bsub>(I)\<^esub> Z)"
sorry

mtheorem pboole_th_30:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds X (/\\)PBOOLEK3\<^bsub>(I)\<^esub> (X (\\/)PBOOLEK2\<^bsub>(I)\<^esub> Y) =PBOOLER7\<^bsub>(I)\<^esub> X"
sorry

mtheorem pboole_th_31:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds X (\\/)PBOOLEK2\<^bsub>(I)\<^esub> X (/\\)PBOOLEK3\<^bsub>(I)\<^esub> Y =PBOOLER7\<^bsub>(I)\<^esub> X"
sorry

mtheorem pboole_th_32:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds  for Z be ManySortedSetPBOOLEM1-of I holds X (/\\)PBOOLEK3\<^bsub>(I)\<^esub> (Y (\\/)PBOOLEK2\<^bsub>(I)\<^esub> Z) =PBOOLER7\<^bsub>(I)\<^esub> X (/\\)PBOOLEK3\<^bsub>(I)\<^esub> Y (\\/)PBOOLEK2\<^bsub>(I)\<^esub> X (/\\)PBOOLEK3\<^bsub>(I)\<^esub> Z"
sorry

mtheorem pboole_th_33:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds  for Z be ManySortedSetPBOOLEM1-of I holds X (\\/)PBOOLEK2\<^bsub>(I)\<^esub> Y (/\\)PBOOLEK3\<^bsub>(I)\<^esub> Z =PBOOLER7\<^bsub>(I)\<^esub> (X (\\/)PBOOLEK2\<^bsub>(I)\<^esub> Y)(/\\)PBOOLEK3\<^bsub>(I)\<^esub> (X (\\/)PBOOLEK2\<^bsub>(I)\<^esub> Z)"
sorry

mtheorem pboole_th_34:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds  for Z be ManySortedSetPBOOLEM1-of I holds X (/\\)PBOOLEK3\<^bsub>(I)\<^esub> Y (\\/)PBOOLEK2\<^bsub>(I)\<^esub> X (/\\)PBOOLEK3\<^bsub>(I)\<^esub> Z =PBOOLER7\<^bsub>(I)\<^esub> X implies X c=PBOOLER2\<^bsub>(I)\<^esub> Y (\\/)PBOOLEK2\<^bsub>(I)\<^esub> Z"
sorry

mtheorem pboole_th_35:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds  for Z be ManySortedSetPBOOLEM1-of I holds (X (\\/)PBOOLEK2\<^bsub>(I)\<^esub> Y)(/\\)PBOOLEK3\<^bsub>(I)\<^esub> (X (\\/)PBOOLEK2\<^bsub>(I)\<^esub> Z) =PBOOLER7\<^bsub>(I)\<^esub> X implies Y (/\\)PBOOLEK3\<^bsub>(I)\<^esub> Z c=PBOOLER2\<^bsub>(I)\<^esub> X"
sorry

mtheorem pboole_th_36:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds  for Z be ManySortedSetPBOOLEM1-of I holds (X (/\\)PBOOLEK3\<^bsub>(I)\<^esub> Y (\\/)PBOOLEK2\<^bsub>(I)\<^esub> Y (/\\)PBOOLEK3\<^bsub>(I)\<^esub> Z)(\\/)PBOOLEK2\<^bsub>(I)\<^esub> Z (/\\)PBOOLEK3\<^bsub>(I)\<^esub> X =PBOOLER7\<^bsub>(I)\<^esub> ((X (\\/)PBOOLEK2\<^bsub>(I)\<^esub> Y)(/\\)PBOOLEK3\<^bsub>(I)\<^esub> (Y (\\/)PBOOLEK2\<^bsub>(I)\<^esub> Z))(/\\)PBOOLEK3\<^bsub>(I)\<^esub> (Z (\\/)PBOOLEK2\<^bsub>(I)\<^esub> X)"
sorry

mtheorem pboole_th_37:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds  for Z be ManySortedSetPBOOLEM1-of I holds X (\\/)PBOOLEK2\<^bsub>(I)\<^esub> Y c=PBOOLER2\<^bsub>(I)\<^esub> Z implies X c=PBOOLER2\<^bsub>(I)\<^esub> Z"
sorry

mtheorem pboole_th_38:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds  for Z be ManySortedSetPBOOLEM1-of I holds X c=PBOOLER2\<^bsub>(I)\<^esub> Y (/\\)PBOOLEK3\<^bsub>(I)\<^esub> Z implies X c=PBOOLER2\<^bsub>(I)\<^esub> Y"
sorry

mtheorem pboole_th_39:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds  for Z be ManySortedSetPBOOLEM1-of I holds (X (\\/)PBOOLEK2\<^bsub>(I)\<^esub> Y)(\\/)PBOOLEK2\<^bsub>(I)\<^esub> Z =PBOOLER7\<^bsub>(I)\<^esub> (X (\\/)PBOOLEK2\<^bsub>(I)\<^esub> Z)(\\/)PBOOLEK2\<^bsub>(I)\<^esub> (Y (\\/)PBOOLEK2\<^bsub>(I)\<^esub> Z)"
sorry

mtheorem pboole_th_40:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds  for Z be ManySortedSetPBOOLEM1-of I holds (X (/\\)PBOOLEK3\<^bsub>(I)\<^esub> Y)(/\\)PBOOLEK3\<^bsub>(I)\<^esub> Z =PBOOLER7\<^bsub>(I)\<^esub> (X (/\\)PBOOLEK3\<^bsub>(I)\<^esub> Z)(/\\)PBOOLEK3\<^bsub>(I)\<^esub> (Y (/\\)PBOOLEK3\<^bsub>(I)\<^esub> Z)"
sorry

mtheorem pboole_th_41:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds X (\\/)PBOOLEK2\<^bsub>(I)\<^esub> (X (\\/)PBOOLEK2\<^bsub>(I)\<^esub> Y) =PBOOLER7\<^bsub>(I)\<^esub> X (\\/)PBOOLEK2\<^bsub>(I)\<^esub> Y"
sorry

mtheorem pboole_th_42:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds X (/\\)PBOOLEK3\<^bsub>(I)\<^esub> (X (/\\)PBOOLEK3\<^bsub>(I)\<^esub> Y) =PBOOLER7\<^bsub>(I)\<^esub> X (/\\)PBOOLEK3\<^bsub>(I)\<^esub> Y"
sorry

(*begin*)
mtheorem pboole_th_43:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds EmptyMSPBOOLEK1 I c=PBOOLER2\<^bsub>(I)\<^esub> X"
sorry

mtheorem pboole_th_44:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds X c=PBOOLER2\<^bsub>(I)\<^esub> EmptyMSPBOOLEK1 I implies X =PBOOLER7\<^bsub>(I)\<^esub> EmptyMSPBOOLEK1 I"
sorry

mtheorem pboole_th_45:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds  for Z be ManySortedSetPBOOLEM1-of I holds (X c=PBOOLER2\<^bsub>(I)\<^esub> Y & X c=PBOOLER2\<^bsub>(I)\<^esub> Z) & Y (/\\)PBOOLEK3\<^bsub>(I)\<^esub> Z =PBOOLER7\<^bsub>(I)\<^esub> EmptyMSPBOOLEK1 I implies X =PBOOLER7\<^bsub>(I)\<^esub> EmptyMSPBOOLEK1 I"
  using pboole_th_17 pboole_th_44 sorry

mtheorem pboole_th_46:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds  for Z be ManySortedSetPBOOLEM1-of I holds X c=PBOOLER2\<^bsub>(I)\<^esub> Y & Y (/\\)PBOOLEK3\<^bsub>(I)\<^esub> Z =PBOOLER7\<^bsub>(I)\<^esub> EmptyMSPBOOLEK1 I implies X (/\\)PBOOLEK3\<^bsub>(I)\<^esub> Z =PBOOLER7\<^bsub>(I)\<^esub> EmptyMSPBOOLEK1 I"
  using pboole_th_44 pboole_th_19 sorry

mtheorem pboole_th_47:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds X (\\/)PBOOLEK2\<^bsub>(I)\<^esub> EmptyMSPBOOLEK1 I =PBOOLER7\<^bsub>(I)\<^esub> X & EmptyMSPBOOLEK1 I (\\/)PBOOLEK2\<^bsub>(I)\<^esub> X =PBOOLER7\<^bsub>(I)\<^esub> X"
  using pboole_th_22 pboole_th_43 sorry

mtheorem pboole_th_48:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds X (\\/)PBOOLEK2\<^bsub>(I)\<^esub> Y =PBOOLER7\<^bsub>(I)\<^esub> EmptyMSPBOOLEK1 I implies X =PBOOLER7\<^bsub>(I)\<^esub> EmptyMSPBOOLEK1 I"
  using pboole_th_44 pboole_th_14 sorry

mtheorem pboole_th_49:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds X (/\\)PBOOLEK3\<^bsub>(I)\<^esub> EmptyMSPBOOLEK1 I =PBOOLER7\<^bsub>(I)\<^esub> EmptyMSPBOOLEK1 I"
  using pboole_th_23 pboole_th_43 sorry

mtheorem pboole_th_50:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds  for Z be ManySortedSetPBOOLEM1-of I holds X c=PBOOLER2\<^bsub>(I)\<^esub> Y (\\/)PBOOLEK2\<^bsub>(I)\<^esub> Z & X (/\\)PBOOLEK3\<^bsub>(I)\<^esub> Z =PBOOLER7\<^bsub>(I)\<^esub> EmptyMSPBOOLEK1 I implies X c=PBOOLER2\<^bsub>(I)\<^esub> Y"
sorry

mtheorem pboole_th_51:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds Y c=PBOOLER2\<^bsub>(I)\<^esub> X & X (/\\)PBOOLEK3\<^bsub>(I)\<^esub> Y =PBOOLER7\<^bsub>(I)\<^esub> EmptyMSPBOOLEK1 I implies Y =PBOOLER7\<^bsub>(I)\<^esub> EmptyMSPBOOLEK1 I"
  using pboole_th_23 sorry

(*begin*)
mtheorem pboole_th_52:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds X (\\)PBOOLEK4\<^bsub>(I)\<^esub> Y =PBOOLER7\<^bsub>(I)\<^esub> EmptyMSPBOOLEK1 I iff X c=PBOOLER2\<^bsub>(I)\<^esub> Y"
sorry

mtheorem pboole_th_53:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds  for Z be ManySortedSetPBOOLEM1-of I holds X c=PBOOLER2\<^bsub>(I)\<^esub> Y implies X (\\)PBOOLEK4\<^bsub>(I)\<^esub> Z c=PBOOLER2\<^bsub>(I)\<^esub> Y (\\)PBOOLEK4\<^bsub>(I)\<^esub> Z"
sorry

mtheorem pboole_th_54:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds  for Z be ManySortedSetPBOOLEM1-of I holds X c=PBOOLER2\<^bsub>(I)\<^esub> Y implies Z (\\)PBOOLEK4\<^bsub>(I)\<^esub> Y c=PBOOLER2\<^bsub>(I)\<^esub> Z (\\)PBOOLEK4\<^bsub>(I)\<^esub> X"
sorry

mtheorem pboole_th_55:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds  for Z be ManySortedSetPBOOLEM1-of I holds  for V be ManySortedSetPBOOLEM1-of I holds X c=PBOOLER2\<^bsub>(I)\<^esub> Y & Z c=PBOOLER2\<^bsub>(I)\<^esub> V implies X (\\)PBOOLEK4\<^bsub>(I)\<^esub> V c=PBOOLER2\<^bsub>(I)\<^esub> Y (\\)PBOOLEK4\<^bsub>(I)\<^esub> Z"
sorry

mtheorem pboole_th_56:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds X (\\)PBOOLEK4\<^bsub>(I)\<^esub> Y c=PBOOLER2\<^bsub>(I)\<^esub> X"
sorry

mtheorem pboole_th_57:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds X c=PBOOLER2\<^bsub>(I)\<^esub> Y (\\)PBOOLEK4\<^bsub>(I)\<^esub> X implies X =PBOOLER7\<^bsub>(I)\<^esub> EmptyMSPBOOLEK1 I"
sorry

mtheorem pboole_th_58:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds X (\\)PBOOLEK4\<^bsub>(I)\<^esub> X =PBOOLER7\<^bsub>(I)\<^esub> EmptyMSPBOOLEK1 I"
  using pboole_th_52 sorry

mtheorem pboole_th_59:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds X (\\)PBOOLEK4\<^bsub>(I)\<^esub> EmptyMSPBOOLEK1 I =PBOOLER7\<^bsub>(I)\<^esub> X"
sorry

mtheorem pboole_th_60:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds EmptyMSPBOOLEK1 I (\\)PBOOLEK4\<^bsub>(I)\<^esub> X =PBOOLER7\<^bsub>(I)\<^esub> EmptyMSPBOOLEK1 I"
  using pboole_th_43 pboole_th_52 sorry

mtheorem pboole_th_61:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds X (\\)PBOOLEK4\<^bsub>(I)\<^esub> (X (\\/)PBOOLEK2\<^bsub>(I)\<^esub> Y) =PBOOLER7\<^bsub>(I)\<^esub> EmptyMSPBOOLEK1 I"
  using pboole_th_14 pboole_th_52 sorry

mtheorem pboole_th_62:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds  for Z be ManySortedSetPBOOLEM1-of I holds X (/\\)PBOOLEK3\<^bsub>(I)\<^esub> (Y (\\)PBOOLEK4\<^bsub>(I)\<^esub> Z) =PBOOLER7\<^bsub>(I)\<^esub> X (/\\)PBOOLEK3\<^bsub>(I)\<^esub> Y (\\)PBOOLEK4\<^bsub>(I)\<^esub> Z"
sorry

mtheorem pboole_th_63:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds (X (\\)PBOOLEK4\<^bsub>(I)\<^esub> Y)(/\\)PBOOLEK3\<^bsub>(I)\<^esub> Y =PBOOLER7\<^bsub>(I)\<^esub> EmptyMSPBOOLEK1 I"
sorry

mtheorem pboole_th_64:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds  for Z be ManySortedSetPBOOLEM1-of I holds X (\\)PBOOLEK4\<^bsub>(I)\<^esub> (Y (\\)PBOOLEK4\<^bsub>(I)\<^esub> Z) =PBOOLER7\<^bsub>(I)\<^esub> (X (\\)PBOOLEK4\<^bsub>(I)\<^esub> Y)(\\/)PBOOLEK2\<^bsub>(I)\<^esub> X (/\\)PBOOLEK3\<^bsub>(I)\<^esub> Z"
sorry

mtheorem pboole_th_65:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds (X (\\)PBOOLEK4\<^bsub>(I)\<^esub> Y)(\\/)PBOOLEK2\<^bsub>(I)\<^esub> X (/\\)PBOOLEK3\<^bsub>(I)\<^esub> Y =PBOOLER7\<^bsub>(I)\<^esub> X"
sorry

mtheorem pboole_th_66:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds X c=PBOOLER2\<^bsub>(I)\<^esub> Y implies Y =PBOOLER7\<^bsub>(I)\<^esub> X (\\/)PBOOLEK2\<^bsub>(I)\<^esub> (Y (\\)PBOOLEK4\<^bsub>(I)\<^esub> X)"
sorry

mtheorem pboole_th_67:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds X (\\/)PBOOLEK2\<^bsub>(I)\<^esub> (Y (\\)PBOOLEK4\<^bsub>(I)\<^esub> X) =PBOOLER7\<^bsub>(I)\<^esub> X (\\/)PBOOLEK2\<^bsub>(I)\<^esub> Y"
sorry

mtheorem pboole_th_68:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds X (\\)PBOOLEK4\<^bsub>(I)\<^esub> (X (\\)PBOOLEK4\<^bsub>(I)\<^esub> Y) =PBOOLER7\<^bsub>(I)\<^esub> X (/\\)PBOOLEK3\<^bsub>(I)\<^esub> Y"
sorry

mtheorem pboole_th_69:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds  for Z be ManySortedSetPBOOLEM1-of I holds X (\\)PBOOLEK4\<^bsub>(I)\<^esub> Y (/\\)PBOOLEK3\<^bsub>(I)\<^esub> Z =PBOOLER7\<^bsub>(I)\<^esub> (X (\\)PBOOLEK4\<^bsub>(I)\<^esub> Y)(\\/)PBOOLEK2\<^bsub>(I)\<^esub> (X (\\)PBOOLEK4\<^bsub>(I)\<^esub> Z)"
sorry

mtheorem pboole_th_70:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds X (\\)PBOOLEK4\<^bsub>(I)\<^esub> X (/\\)PBOOLEK3\<^bsub>(I)\<^esub> Y =PBOOLER7\<^bsub>(I)\<^esub> X (\\)PBOOLEK4\<^bsub>(I)\<^esub> Y"
sorry

mtheorem pboole_th_71:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds X (/\\)PBOOLEK3\<^bsub>(I)\<^esub> Y =PBOOLER7\<^bsub>(I)\<^esub> EmptyMSPBOOLEK1 I iff X (\\)PBOOLEK4\<^bsub>(I)\<^esub> Y =PBOOLER7\<^bsub>(I)\<^esub> X"
sorry

mtheorem pboole_th_72:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds  for Z be ManySortedSetPBOOLEM1-of I holds (X (\\/)PBOOLEK2\<^bsub>(I)\<^esub> Y)(\\)PBOOLEK4\<^bsub>(I)\<^esub> Z =PBOOLER7\<^bsub>(I)\<^esub> (X (\\)PBOOLEK4\<^bsub>(I)\<^esub> Z)(\\/)PBOOLEK2\<^bsub>(I)\<^esub> (Y (\\)PBOOLEK4\<^bsub>(I)\<^esub> Z)"
sorry

mtheorem pboole_th_73:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds  for Z be ManySortedSetPBOOLEM1-of I holds (X (\\)PBOOLEK4\<^bsub>(I)\<^esub> Y)(\\)PBOOLEK4\<^bsub>(I)\<^esub> Z =PBOOLER7\<^bsub>(I)\<^esub> X (\\)PBOOLEK4\<^bsub>(I)\<^esub> (Y (\\/)PBOOLEK2\<^bsub>(I)\<^esub> Z)"
sorry

mtheorem pboole_th_74:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds  for Z be ManySortedSetPBOOLEM1-of I holds X (/\\)PBOOLEK3\<^bsub>(I)\<^esub> Y (\\)PBOOLEK4\<^bsub>(I)\<^esub> Z =PBOOLER7\<^bsub>(I)\<^esub> (X (\\)PBOOLEK4\<^bsub>(I)\<^esub> Z)(/\\)PBOOLEK3\<^bsub>(I)\<^esub> (Y (\\)PBOOLEK4\<^bsub>(I)\<^esub> Z)"
sorry

mtheorem pboole_th_75:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds (X (\\/)PBOOLEK2\<^bsub>(I)\<^esub> Y)(\\)PBOOLEK4\<^bsub>(I)\<^esub> Y =PBOOLER7\<^bsub>(I)\<^esub> X (\\)PBOOLEK4\<^bsub>(I)\<^esub> Y"
sorry

mtheorem pboole_th_76:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds  for Z be ManySortedSetPBOOLEM1-of I holds X c=PBOOLER2\<^bsub>(I)\<^esub> Y (\\/)PBOOLEK2\<^bsub>(I)\<^esub> Z implies X (\\)PBOOLEK4\<^bsub>(I)\<^esub> Y c=PBOOLER2\<^bsub>(I)\<^esub> Z & X (\\)PBOOLEK4\<^bsub>(I)\<^esub> Z c=PBOOLER2\<^bsub>(I)\<^esub> Y"
sorry

mtheorem pboole_th_77:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds (X (\\/)PBOOLEK2\<^bsub>(I)\<^esub> Y)(\\)PBOOLEK4\<^bsub>(I)\<^esub> X (/\\)PBOOLEK3\<^bsub>(I)\<^esub> Y =PBOOLER7\<^bsub>(I)\<^esub> (X (\\)PBOOLEK4\<^bsub>(I)\<^esub> Y)(\\/)PBOOLEK2\<^bsub>(I)\<^esub> (Y (\\)PBOOLEK4\<^bsub>(I)\<^esub> X)"
sorry

mtheorem pboole_th_78:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds (X (\\)PBOOLEK4\<^bsub>(I)\<^esub> Y)(\\)PBOOLEK4\<^bsub>(I)\<^esub> Y =PBOOLER7\<^bsub>(I)\<^esub> X (\\)PBOOLEK4\<^bsub>(I)\<^esub> Y"
sorry

mtheorem pboole_th_79:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds  for Z be ManySortedSetPBOOLEM1-of I holds X (\\)PBOOLEK4\<^bsub>(I)\<^esub> (Y (\\/)PBOOLEK2\<^bsub>(I)\<^esub> Z) =PBOOLER7\<^bsub>(I)\<^esub> (X (\\)PBOOLEK4\<^bsub>(I)\<^esub> Y)(/\\)PBOOLEK3\<^bsub>(I)\<^esub> (X (\\)PBOOLEK4\<^bsub>(I)\<^esub> Z)"
sorry

mtheorem pboole_th_80:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds X (\\)PBOOLEK4\<^bsub>(I)\<^esub> Y =PBOOLER7\<^bsub>(I)\<^esub> Y (\\)PBOOLEK4\<^bsub>(I)\<^esub> X implies X =PBOOLER7\<^bsub>(I)\<^esub> Y"
sorry

mtheorem pboole_th_81:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds  for Z be ManySortedSetPBOOLEM1-of I holds X (/\\)PBOOLEK3\<^bsub>(I)\<^esub> (Y (\\)PBOOLEK4\<^bsub>(I)\<^esub> Z) =PBOOLER7\<^bsub>(I)\<^esub> X (/\\)PBOOLEK3\<^bsub>(I)\<^esub> Y (\\)PBOOLEK4\<^bsub>(I)\<^esub> X (/\\)PBOOLEK3\<^bsub>(I)\<^esub> Z"
sorry

mtheorem pboole_th_82:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds  for Z be ManySortedSetPBOOLEM1-of I holds X (\\)PBOOLEK4\<^bsub>(I)\<^esub> Y c=PBOOLER2\<^bsub>(I)\<^esub> Z implies X c=PBOOLER2\<^bsub>(I)\<^esub> Y (\\/)PBOOLEK2\<^bsub>(I)\<^esub> Z"
sorry

mtheorem pboole_th_83:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds X (\\)PBOOLEK4\<^bsub>(I)\<^esub> Y c=PBOOLER2\<^bsub>(I)\<^esub> X (\\+\\)PBOOLEK5\<^bsub>(I)\<^esub> Y"
  using pboole_th_14 sorry

mtheorem pboole_th_84:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds X (\\+\\)PBOOLEK5\<^bsub>(I)\<^esub> EmptyMSPBOOLEK1 I =PBOOLER7\<^bsub>(I)\<^esub> X"
sorry

mtheorem pboole_th_85:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds X (\\+\\)PBOOLEK5\<^bsub>(I)\<^esub> X =PBOOLER7\<^bsub>(I)\<^esub> EmptyMSPBOOLEK1 I"
  using pboole_th_52 sorry

mtheorem pboole_th_86:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds X (\\/)PBOOLEK2\<^bsub>(I)\<^esub> Y =PBOOLER7\<^bsub>(I)\<^esub> (X (\\+\\)PBOOLEK5\<^bsub>(I)\<^esub> Y)(\\/)PBOOLEK2\<^bsub>(I)\<^esub> X (/\\)PBOOLEK3\<^bsub>(I)\<^esub> Y"
sorry

mtheorem pboole_th_87:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds X (\\+\\)PBOOLEK5\<^bsub>(I)\<^esub> Y =PBOOLER7\<^bsub>(I)\<^esub> (X (\\/)PBOOLEK2\<^bsub>(I)\<^esub> Y)(\\)PBOOLEK4\<^bsub>(I)\<^esub> X (/\\)PBOOLEK3\<^bsub>(I)\<^esub> Y"
sorry

mtheorem pboole_th_88:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds  for Z be ManySortedSetPBOOLEM1-of I holds (X (\\+\\)PBOOLEK5\<^bsub>(I)\<^esub> Y)(\\)PBOOLEK4\<^bsub>(I)\<^esub> Z =PBOOLER7\<^bsub>(I)\<^esub> (X (\\)PBOOLEK4\<^bsub>(I)\<^esub> (Y (\\/)PBOOLEK2\<^bsub>(I)\<^esub> Z))(\\/)PBOOLEK2\<^bsub>(I)\<^esub> (Y (\\)PBOOLEK4\<^bsub>(I)\<^esub> (X (\\/)PBOOLEK2\<^bsub>(I)\<^esub> Z))"
sorry

mtheorem pboole_th_89:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds  for Z be ManySortedSetPBOOLEM1-of I holds X (\\)PBOOLEK4\<^bsub>(I)\<^esub> (Y (\\+\\)PBOOLEK5\<^bsub>(I)\<^esub> Z) =PBOOLER7\<^bsub>(I)\<^esub> (X (\\)PBOOLEK4\<^bsub>(I)\<^esub> (Y (\\/)PBOOLEK2\<^bsub>(I)\<^esub> Z))(\\/)PBOOLEK2\<^bsub>(I)\<^esub> (X (/\\)PBOOLEK3\<^bsub>(I)\<^esub> Y)(/\\)PBOOLEK3\<^bsub>(I)\<^esub> Z"
sorry

mtheorem pboole_th_90:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds  for Z be ManySortedSetPBOOLEM1-of I holds (X (\\+\\)PBOOLEK5\<^bsub>(I)\<^esub> Y)(\\+\\)PBOOLEK5\<^bsub>(I)\<^esub> Z =PBOOLER7\<^bsub>(I)\<^esub> X (\\+\\)PBOOLEK5\<^bsub>(I)\<^esub> (Y (\\+\\)PBOOLEK5\<^bsub>(I)\<^esub> Z)"
sorry

mtheorem pboole_th_91:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds  for Z be ManySortedSetPBOOLEM1-of I holds X (\\)PBOOLEK4\<^bsub>(I)\<^esub> Y c=PBOOLER2\<^bsub>(I)\<^esub> Z & Y (\\)PBOOLEK4\<^bsub>(I)\<^esub> X c=PBOOLER2\<^bsub>(I)\<^esub> Z implies X (\\+\\)PBOOLEK5\<^bsub>(I)\<^esub> Y c=PBOOLER2\<^bsub>(I)\<^esub> Z"
  using pboole_th_16 sorry

mtheorem pboole_th_92:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds X (\\/)PBOOLEK2\<^bsub>(I)\<^esub> Y =PBOOLER7\<^bsub>(I)\<^esub> X (\\+\\)PBOOLEK5\<^bsub>(I)\<^esub> Y (\\)PBOOLEK4\<^bsub>(I)\<^esub> X"
sorry

mtheorem pboole_th_93:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds X (/\\)PBOOLEK3\<^bsub>(I)\<^esub> Y =PBOOLER7\<^bsub>(I)\<^esub> X (\\+\\)PBOOLEK5\<^bsub>(I)\<^esub> X (\\)PBOOLEK4\<^bsub>(I)\<^esub> Y"
sorry

mtheorem pboole_th_94:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds X (\\)PBOOLEK4\<^bsub>(I)\<^esub> Y =PBOOLER7\<^bsub>(I)\<^esub> X (\\+\\)PBOOLEK5\<^bsub>(I)\<^esub> X (/\\)PBOOLEK3\<^bsub>(I)\<^esub> Y"
sorry

mtheorem pboole_th_95:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds Y (\\)PBOOLEK4\<^bsub>(I)\<^esub> X =PBOOLER7\<^bsub>(I)\<^esub> X (\\+\\)PBOOLEK5\<^bsub>(I)\<^esub> X (\\/)PBOOLEK2\<^bsub>(I)\<^esub> Y"
sorry

mtheorem pboole_th_96:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds X (\\/)PBOOLEK2\<^bsub>(I)\<^esub> Y =PBOOLER7\<^bsub>(I)\<^esub> (X (\\+\\)PBOOLEK5\<^bsub>(I)\<^esub> Y)(\\+\\)PBOOLEK5\<^bsub>(I)\<^esub> X (/\\)PBOOLEK3\<^bsub>(I)\<^esub> Y"
sorry

mtheorem pboole_th_97:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds X (/\\)PBOOLEK3\<^bsub>(I)\<^esub> Y =PBOOLER7\<^bsub>(I)\<^esub> (X (\\+\\)PBOOLEK5\<^bsub>(I)\<^esub> Y)(\\+\\)PBOOLEK5\<^bsub>(I)\<^esub> X (\\/)PBOOLEK2\<^bsub>(I)\<^esub> Y"
sorry

(*begin*)
mtheorem pboole_th_98:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds  for Z be ManySortedSetPBOOLEM1-of I holds X overlapsPBOOLER4\<^bsub>(I)\<^esub> Y or X overlapsPBOOLER4\<^bsub>(I)\<^esub> Z implies X overlapsPBOOLER4\<^bsub>(I)\<^esub> Y (\\/)PBOOLEK2\<^bsub>(I)\<^esub> Z"
sorry

mtheorem pboole_th_99:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds  for Z be ManySortedSetPBOOLEM1-of I holds X overlapsPBOOLER4\<^bsub>(I)\<^esub> Y & Y c=PBOOLER2\<^bsub>(I)\<^esub> Z implies X overlapsPBOOLER4\<^bsub>(I)\<^esub> Z"
sorry

mtheorem pboole_th_100:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds  for Z be ManySortedSetPBOOLEM1-of I holds X overlapsPBOOLER4\<^bsub>(I)\<^esub> Y & X c=PBOOLER2\<^bsub>(I)\<^esub> Z implies Z overlapsPBOOLER4\<^bsub>(I)\<^esub> Y"
sorry

mtheorem pboole_th_101:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds  for Z be ManySortedSetPBOOLEM1-of I holds  for V be ManySortedSetPBOOLEM1-of I holds (X c=PBOOLER2\<^bsub>(I)\<^esub> Y & Z c=PBOOLER2\<^bsub>(I)\<^esub> V) & X overlapsPBOOLER4\<^bsub>(I)\<^esub> Z implies Y overlapsPBOOLER4\<^bsub>(I)\<^esub> V"
sorry

mtheorem pboole_th_102:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds  for Z be ManySortedSetPBOOLEM1-of I holds X overlapsPBOOLER4\<^bsub>(I)\<^esub> Y (/\\)PBOOLEK3\<^bsub>(I)\<^esub> Z implies X overlapsPBOOLER4\<^bsub>(I)\<^esub> Y & X overlapsPBOOLER4\<^bsub>(I)\<^esub> Z"
sorry

mtheorem pboole_th_103:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Z be ManySortedSetPBOOLEM1-of I holds  for V be ManySortedSetPBOOLEM1-of I holds X overlapsPBOOLER4\<^bsub>(I)\<^esub> Z & X c=PBOOLER2\<^bsub>(I)\<^esub> V implies X overlapsPBOOLER4\<^bsub>(I)\<^esub> Z (/\\)PBOOLEK3\<^bsub>(I)\<^esub> V"
sorry

mtheorem pboole_th_104:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds  for Z be ManySortedSetPBOOLEM1-of I holds X overlapsPBOOLER4\<^bsub>(I)\<^esub> Y (\\)PBOOLEK4\<^bsub>(I)\<^esub> Z implies X overlapsPBOOLER4\<^bsub>(I)\<^esub> Y"
  using pboole_th_56 pboole_th_99 sorry

mtheorem pboole_th_105:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds  for Z be ManySortedSetPBOOLEM1-of I holds  not Y overlapsPBOOLER4\<^bsub>(I)\<^esub> Z implies  not X (/\\)PBOOLEK3\<^bsub>(I)\<^esub> Y overlapsPBOOLER4\<^bsub>(I)\<^esub> X (/\\)PBOOLEK3\<^bsub>(I)\<^esub> Z"
sorry

mtheorem pboole_th_106:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds  for Z be ManySortedSetPBOOLEM1-of I holds X overlapsPBOOLER4\<^bsub>(I)\<^esub> Y (\\)PBOOLEK4\<^bsub>(I)\<^esub> Z implies Y overlapsPBOOLER4\<^bsub>(I)\<^esub> X (\\)PBOOLEK4\<^bsub>(I)\<^esub> Z"
sorry

mtheorem pboole_th_107:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds  for Z be ManySortedSetPBOOLEM1-of I holds X meetsPBOOLER6\<^bsub>(I)\<^esub> Y & Y c=PBOOLER2\<^bsub>(I)\<^esub> Z implies X meetsPBOOLER6\<^bsub>(I)\<^esub> Z"
sorry

mtheorem pboole_th_108:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds Y missesPBOOLER5\<^bsub>(I)\<^esub> X (\\)PBOOLEK4\<^bsub>(I)\<^esub> Y"
sorry

mtheorem pboole_th_109:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds X (/\\)PBOOLEK3\<^bsub>(I)\<^esub> Y missesPBOOLER5\<^bsub>(I)\<^esub> X (\\)PBOOLEK4\<^bsub>(I)\<^esub> Y"
sorry

mtheorem pboole_th_110:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds X (/\\)PBOOLEK3\<^bsub>(I)\<^esub> Y missesPBOOLER5\<^bsub>(I)\<^esub> X (\\+\\)PBOOLEK5\<^bsub>(I)\<^esub> Y"
sorry

mtheorem pboole_th_111:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds X missesPBOOLER5\<^bsub>(I)\<^esub> Y implies X (/\\)PBOOLEK3\<^bsub>(I)\<^esub> Y =PBOOLER7\<^bsub>(I)\<^esub> EmptyMSPBOOLEK1 I"
sorry

mtheorem pboole_th_112:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds X <>HIDDENR2 EmptyMSPBOOLEK1 I implies X meetsPBOOLER6\<^bsub>(I)\<^esub> X"
sorry

mtheorem pboole_th_113:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds  for Z be ManySortedSetPBOOLEM1-of I holds (X c=PBOOLER2\<^bsub>(I)\<^esub> Y & X c=PBOOLER2\<^bsub>(I)\<^esub> Z) & Y missesPBOOLER5\<^bsub>(I)\<^esub> Z implies X =PBOOLER7\<^bsub>(I)\<^esub> EmptyMSPBOOLEK1 I"
sorry

mtheorem pboole_th_114:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds  for Z be ManySortedSetPBOOLEM1-of I holds  for V be ManySortedSetPBOOLEM1-of I holds (Z (\\/)PBOOLEK2\<^bsub>(I)\<^esub> V =PBOOLER7\<^bsub>(I)\<^esub> X (\\/)PBOOLEK2\<^bsub>(I)\<^esub> Y & X missesPBOOLER5\<^bsub>(I)\<^esub> Z) & Y missesPBOOLER5\<^bsub>(I)\<^esub> V implies X =PBOOLER7\<^bsub>(I)\<^esub> V & Y =PBOOLER7\<^bsub>(I)\<^esub> Z"
sorry

mtheorem pboole_th_115:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds X missesPBOOLER5\<^bsub>(I)\<^esub> Y implies X (\\)PBOOLEK4\<^bsub>(I)\<^esub> Y =PBOOLER7\<^bsub>(I)\<^esub> X"
sorry

mtheorem pboole_th_116:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds X missesPBOOLER5\<^bsub>(I)\<^esub> Y implies (X (\\/)PBOOLEK2\<^bsub>(I)\<^esub> Y)(\\)PBOOLEK4\<^bsub>(I)\<^esub> Y =PBOOLER7\<^bsub>(I)\<^esub> X"
sorry

mtheorem pboole_th_117:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds X (\\)PBOOLEK4\<^bsub>(I)\<^esub> Y =PBOOLER7\<^bsub>(I)\<^esub> X implies X missesPBOOLER5\<^bsub>(I)\<^esub> Y"
sorry

mtheorem pboole_th_118:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds X (\\)PBOOLEK4\<^bsub>(I)\<^esub> Y missesPBOOLER5\<^bsub>(I)\<^esub> Y (\\)PBOOLEK4\<^bsub>(I)\<^esub> X"
sorry

(*begin*)
mdef pboole_def_11 (" _ [=PBOOLER8\<^bsub>'( _ ')\<^esub>  _ " [50,0,50]50 ) where
  mlet "I be setHIDDENM2", "X be ManySortedSetPBOOLEM1-of I", "Y be ManySortedSetPBOOLEM1-of I"
"pred X [=PBOOLER8\<^bsub>(I)\<^esub> Y means
   for x be ManySortedSetPBOOLEM1-of I holds x inPBOOLER1\<^bsub>(I)\<^esub> X implies x inPBOOLER1\<^bsub>(I)\<^esub> Y"..

mtheorem PBOOLER8_reflexivity:
  mlet "I be setHIDDENM2"
" for Y be ManySortedSetPBOOLEM1-of I holds Y [=PBOOLER8\<^bsub>(I)\<^esub> Y"
sorry

mtheorem pboole_th_119:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds X c=PBOOLER2\<^bsub>(I)\<^esub> Y implies X [=PBOOLER8\<^bsub>(I)\<^esub> Y"
sorry

mtheorem pboole_th_120:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds  for Z be ManySortedSetPBOOLEM1-of I holds X [=PBOOLER8\<^bsub>(I)\<^esub> Y & Y [=PBOOLER8\<^bsub>(I)\<^esub> Z implies X [=PBOOLER8\<^bsub>(I)\<^esub> Z"
   sorry

(*begin*)
mtheorem pboole_th_121:
"EmptyMSPBOOLEK1 ({}XBOOLE-0K1) inPBOOLER1\<^bsub>({}XBOOLE-0K1)\<^esub> EmptyMSPBOOLEK1 ({}XBOOLE-0K1)"
   sorry

mtheorem pboole_th_122:
" for X be ManySortedSetPBOOLEM1-of {}XBOOLE-0K1 holds X =FUNCT-1R1 {}XBOOLE-0K1"
   sorry

reserve I for " non emptyXBOOLE-0V1\<bar>setHIDDENM2"
reserve x, X, Y for "ManySortedSetPBOOLEM1-of I"
mtheorem pboole_th_123:
" for I be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds X overlapsPBOOLER4\<^bsub>(I)\<^esub> Y implies X meetsPBOOLER6\<^bsub>(I)\<^esub> Y"
sorry

mtheorem pboole_th_124:
" for I be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  not ( ex x be ManySortedSetPBOOLEM1-of I st x inPBOOLER3\<^bsub>(I)\<^esub> EmptyMSPBOOLEK1 I)"
sorry

mtheorem pboole_th_125:
" for I be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for x be ManySortedSetPBOOLEM1-of I holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds x inPBOOLER3\<^bsub>(I)\<^esub> X & x inPBOOLER3\<^bsub>(I)\<^esub> Y implies X (/\\)PBOOLEK3\<^bsub>(I)\<^esub> Y <>HIDDENR2 EmptyMSPBOOLEK1 I"
  using pboole_th_8 pboole_th_124 sorry

mtheorem pboole_th_126:
" for I be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  not X overlapsPBOOLER4\<^bsub>(I)\<^esub> EmptyMSPBOOLEK1 I"
sorry

mtheorem pboole_th_127:
" for I be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds X (/\\)PBOOLEK3\<^bsub>(I)\<^esub> Y =PBOOLER7\<^bsub>(I)\<^esub> EmptyMSPBOOLEK1 I implies  not X overlapsPBOOLER4\<^bsub>(I)\<^esub> Y"
sorry

mtheorem pboole_th_128:
" for I be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds X overlapsPBOOLER4\<^bsub>(I)\<^esub> X implies X <>HIDDENR2 EmptyMSPBOOLEK1 I"
sorry

(*begin*)
reserve I for "setHIDDENM2"
reserve x, X, Y, Z for "ManySortedSetPBOOLEM1-of I"
syntax PBOOLEV1 :: " Set \<Rightarrow> Ty" ("empty-yieldingPBOOLEV1\<^bsub>'( _ ')\<^esub>" [0]70)
translations "empty-yieldingPBOOLEV1\<^bsub>(I)\<^esub>" \<rightharpoonup> "empty-yieldingRELAT-1V3"

mtheorem pboole_def_12:
  mlet "I be setHIDDENM2", "X be ManySortedSetPBOOLEM1-of I"
"redefine attr empty-yieldingPBOOLEV1\<^bsub>(I)\<^esub> for ManySortedSetPBOOLEM1-of I means
  (\<lambda>X.  for i be objectHIDDENM1 holds i inHIDDENR3 I implies X .FUNCT-1K1 i be emptyXBOOLE-0V1)"
proof
(*compatibility*)
  show " for X be ManySortedSetPBOOLEM1-of I holds X be empty-yieldingPBOOLEV1\<^bsub>(I)\<^esub> iff ( for i be objectHIDDENM1 holds i inHIDDENR3 I implies X .FUNCT-1K1 i be emptyXBOOLE-0V1)"
sorry
qed "sorry"

syntax PBOOLEV2 :: " Set \<Rightarrow> Ty" ("non-emptyPBOOLEV2\<^bsub>'( _ ')\<^esub>" [0]70)
translations "non-emptyPBOOLEV2\<^bsub>(I)\<^esub>" \<rightharpoonup> "non-emptyRELAT-1V2"

mtheorem pboole_def_13:
  mlet "I be setHIDDENM2", "X be ManySortedSetPBOOLEM1-of I"
"redefine attr non-emptyPBOOLEV2\<^bsub>(I)\<^esub> for ManySortedSetPBOOLEM1-of I means
  (\<lambda>X.  for i be objectHIDDENM1 holds i inHIDDENR3 I implies X .FUNCT-1K1 i be  non emptyXBOOLE-0V1)"
proof
(*compatibility*)
  show " for X be ManySortedSetPBOOLEM1-of I holds X be non-emptyPBOOLEV2\<^bsub>(I)\<^esub> iff ( for i be objectHIDDENM1 holds i inHIDDENR3 I implies X .FUNCT-1K1 i be  non emptyXBOOLE-0V1)"
sorry
qed "sorry"

mtheorem pboole_cl_2:
  mlet "I be setHIDDENM2"
"cluster empty-yieldingRELAT-1V3 for ManySortedSetPBOOLEM1-of I"
proof
(*existence*)
  show " ex it be ManySortedSetPBOOLEM1-of I st it be empty-yieldingRELAT-1V3"
sorry
qed "sorry"

mtheorem pboole_cl_3:
  mlet "I be setHIDDENM2"
"cluster non-emptyRELAT-1V2 for ManySortedSetPBOOLEM1-of I"
proof
(*existence*)
  show " ex it be ManySortedSetPBOOLEM1-of I st it be non-emptyRELAT-1V2"
sorry
qed "sorry"

mtheorem pboole_cl_4:
  mlet "I be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster non-emptyRELAT-1V2 also-is  non empty-yieldingRELAT-1V3 for ManySortedSetPBOOLEM1-of I"
proof
(*coherence*)
  show " for it be ManySortedSetPBOOLEM1-of I holds it be non-emptyRELAT-1V2 implies it be  non empty-yieldingRELAT-1V3"
sorry
qed "sorry"

mtheorem pboole_cl_5:
  mlet "I be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster empty-yieldingRELAT-1V3 also-is  non non-emptyRELAT-1V2 for ManySortedSetPBOOLEM1-of I"
proof
(*coherence*)
  show " for it be ManySortedSetPBOOLEM1-of I holds it be empty-yieldingRELAT-1V3 implies it be  non non-emptyRELAT-1V2"
     sorry
qed "sorry"

mtheorem pboole_th_129:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds X be empty-yieldingRELAT-1V3 iff X =PBOOLER7\<^bsub>(I)\<^esub> EmptyMSPBOOLEK1 I"
sorry

mtheorem pboole_th_130:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds Y be empty-yieldingRELAT-1V3 & X c=PBOOLER2\<^bsub>(I)\<^esub> Y implies X be empty-yieldingRELAT-1V3"
sorry

mtheorem pboole_th_131:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds X be non-emptyRELAT-1V2 & X c=PBOOLER2\<^bsub>(I)\<^esub> Y implies Y be non-emptyRELAT-1V2"
sorry

mtheorem pboole_th_132:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds X be non-emptyRELAT-1V2 & X [=PBOOLER8\<^bsub>(I)\<^esub> Y implies X c=PBOOLER2\<^bsub>(I)\<^esub> Y"
sorry

mtheorem pboole_th_133:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds X be non-emptyRELAT-1V2 & X [=PBOOLER8\<^bsub>(I)\<^esub> Y implies Y be non-emptyRELAT-1V2"
sorry

reserve X for "non-emptyRELAT-1V2\<bar>ManySortedSetPBOOLEM1-of I"
mtheorem pboole_th_134:
" for I be setHIDDENM2 holds  for X be non-emptyRELAT-1V2\<bar>ManySortedSetPBOOLEM1-of I holds  ex x be ManySortedSetPBOOLEM1-of I st x inPBOOLER1\<^bsub>(I)\<^esub> X"
sorry

mtheorem pboole_th_135:
" for I be setHIDDENM2 holds  for Y be ManySortedSetPBOOLEM1-of I holds  for X be non-emptyRELAT-1V2\<bar>ManySortedSetPBOOLEM1-of I holds ( for x be ManySortedSetPBOOLEM1-of I holds x inPBOOLER1\<^bsub>(I)\<^esub> X iff x inPBOOLER1\<^bsub>(I)\<^esub> Y) implies X =PBOOLER7\<^bsub>(I)\<^esub> Y"
sorry

mtheorem pboole_th_136:
" for I be setHIDDENM2 holds  for Y be ManySortedSetPBOOLEM1-of I holds  for Z be ManySortedSetPBOOLEM1-of I holds  for X be non-emptyRELAT-1V2\<bar>ManySortedSetPBOOLEM1-of I holds ( for x be ManySortedSetPBOOLEM1-of I holds x inPBOOLER1\<^bsub>(I)\<^esub> X iff x inPBOOLER1\<^bsub>(I)\<^esub> Y & x inPBOOLER1\<^bsub>(I)\<^esub> Z) implies X =PBOOLER7\<^bsub>(I)\<^esub> Y (/\\)PBOOLEK3\<^bsub>(I)\<^esub> Z"
sorry

(*begin*)
theorem pboole_sch_3:
  fixes If0 Pp2 
  assumes
[ty]: "If0 be setHIDDENM2" and
   A1: " for i be objectHIDDENM1 holds i inHIDDENR3 If0 implies ( ex j be objectHIDDENM1 st Pp2(i,j))"
  shows " ex f be ManySortedSetPBOOLEM1-of If0 st  for i be objectHIDDENM1 holds i inHIDDENR3 If0 implies Pp2(i,f .FUNCT-1K1 i)"
sorry

theorem pboole_sch_4:
  fixes If0 Ff1 
  assumes
[ty]: "If0 be setHIDDENM2" and
  [ty_func]: "\<And> x1. x1 be objectHIDDENM1 \<Longrightarrow> Ff1(x1) be objectHIDDENM1"
  shows " ex f be ManySortedSetPBOOLEM1-of If0 st  for i be objectHIDDENM1 holds i inHIDDENR3 If0 implies f .FUNCT-1K1 i =HIDDENR1 Ff1(i)"
sorry

mtheorem pboole_cl_6:
  mlet "I be setHIDDENM2"
"cluster Function-yieldingFUNCOP-1V1 for ManySortedSetPBOOLEM1-of I"
proof
(*existence*)
  show " ex it be ManySortedSetPBOOLEM1-of I st it be Function-yieldingFUNCOP-1V1"
sorry
qed "sorry"

syntax PBOOLEM2 :: " Set \<Rightarrow> Ty" ("ManySortedFunctionPBOOLEM2-of  _ " [70]70)
translations "ManySortedFunctionPBOOLEM2-of I" \<rightharpoonup> "Function-yieldingFUNCOP-1V1\<bar>ManySortedSetPBOOLEM1-of I"

mtheorem pboole_th_137:
" for I be setHIDDENM2 holds  not ( ex M be non-emptyRELAT-1V2\<bar>ManySortedSetPBOOLEM1-of I st {}XBOOLE-0K1 inTARSKIR2 rngFUNCT-1K2 M)"
sorry

abbreviation(input) PBOOLEM3("ComponentPBOOLEM3-of  _ " [70]70) where
  "ComponentPBOOLEM3-of M \<equiv> ElementSUBSET-1M1-of rngFUNCT-1K2 M"

mtheorem pboole_th_138:
" for I be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for M be ManySortedSetPBOOLEM1-of I holds  for A be ComponentPBOOLEM3-of M holds  ex i be objectHIDDENM1 st i inHIDDENR3 I & A =XBOOLE-0R4 M .FUNCT-1K1 i"
sorry

mtheorem pboole_th_139:
" for I be setHIDDENM2 holds  for M be ManySortedSetPBOOLEM1-of I holds  for i be objectHIDDENM1 holds i inHIDDENR3 I implies M .FUNCT-1K1 i be ComponentPBOOLEM3-of M"
sorry

mdef pboole_def_14 ("ElementPBOOLEM4\<^bsub>'( _ ')\<^esub>-of  _ " [0,70]70 ) where
  mlet "I be setHIDDENM2", "B be ManySortedSetPBOOLEM1-of I"
"mode ElementPBOOLEM4\<^bsub>(I)\<^esub>-of B \<rightarrow> ManySortedSetPBOOLEM1-of I means
  (\<lambda>it.  for i be objectHIDDENM1 holds i inHIDDENR3 I implies it .FUNCT-1K1 i be ElementSUBSET-1M1-of B .FUNCT-1K1 i)"
proof-
  (*existence*)
    show " ex it be ManySortedSetPBOOLEM1-of I st  for i be objectHIDDENM1 holds i inHIDDENR3 I implies it .FUNCT-1K1 i be ElementSUBSET-1M1-of B .FUNCT-1K1 i"
sorry
qed "sorry"

(*begin*)
mdef pboole_def_15 ("ManySortedFunctionPBOOLEM5\<^bsub>'( _ ')\<^esub>-of'( _ , _ ')" [0,0,0]70 ) where
  mlet "I be setHIDDENM2", "A be ManySortedSetPBOOLEM1-of I", "B be ManySortedSetPBOOLEM1-of I"
"mode ManySortedFunctionPBOOLEM5\<^bsub>(I)\<^esub>-of(A,B) \<rightarrow> ManySortedSetPBOOLEM1-of I means
  (\<lambda>it.  for i be objectHIDDENM1 holds i inHIDDENR3 I implies it .FUNCT-1K1 i be FunctionFUNCT-2M1-of(A .FUNCT-1K1 i,B .FUNCT-1K1 i))"
proof-
  (*existence*)
    show " ex it be ManySortedSetPBOOLEM1-of I st  for i be objectHIDDENM1 holds i inHIDDENR3 I implies it .FUNCT-1K1 i be FunctionFUNCT-2M1-of(A .FUNCT-1K1 i,B .FUNCT-1K1 i)"
sorry
qed "sorry"

mtheorem pboole_cl_7:
  mlet "I be setHIDDENM2", "A be ManySortedSetPBOOLEM1-of I", "B be ManySortedSetPBOOLEM1-of I"
"cluster note-that Function-yieldingFUNCOP-1V1 for ManySortedFunctionPBOOLEM5\<^bsub>(I)\<^esub>-of(A,B)"
proof
(*coherence*)
  show " for it be ManySortedFunctionPBOOLEM5\<^bsub>(I)\<^esub>-of(A,B) holds it be Function-yieldingFUNCOP-1V1"
sorry
qed "sorry"

mtheorem pboole_cl_8:
  mlet "I be setHIDDENM2", "J be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "O be FunctionFUNCT-2M1-of(I,J)", "F be ManySortedSetPBOOLEM1-of J"
"cluster F *FUNCT-1K3 O as-term-is totalPARTFUN1V1\<^bsub>(I)\<^esub> for I -definedRELAT-1V4\<bar>FunctionFUNCT-1M1"
proof
(*coherence*)
  show " for it be I -definedRELAT-1V4\<bar>FunctionFUNCT-1M1 holds it =HIDDENR1 F *FUNCT-1K3 O implies it be totalPARTFUN1V1\<^bsub>(I)\<^esub>"
sorry
qed "sorry"

theorem pboole_sch_5:
  fixes Df0 Ff1 
  assumes
[ty]: "Df0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
  [ty_func]: "\<And> x1. x1 be objectHIDDENM1 \<Longrightarrow> Ff1(x1) be objectHIDDENM1"
  shows " ex X be ManySortedSetPBOOLEM1-of Df0 st  for d be ElementSUBSET-1M1-of Df0 holds X .FUNCT-1K1 d =HIDDENR1 Ff1(d)"
sorry

mtheorem pboole_cl_9:
  mlet "J be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "B be non-emptyRELAT-1V2\<bar>ManySortedSetPBOOLEM1-of J", "j be ElementSUBSET-1M1-of J"
"cluster B .FUNCT-1K1 j as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "B .FUNCT-1K1 j be  non emptyXBOOLE-0V1"
    using pboole_def_13 sorry
qed "sorry"

reserve X, Y for "ManySortedSetPBOOLEM1-of I"
mdef pboole_def_16 ("[|PBOOLEK6\<^bsub>'( _ ')\<^esub> _ , _ |]" [0,0,0]164 ) where
  mlet "I be setHIDDENM2", "X be ManySortedSetPBOOLEM1-of I", "Y be ManySortedSetPBOOLEM1-of I"
"func [|PBOOLEK6\<^bsub>(I)\<^esub> X,Y |] \<rightarrow> ManySortedSetPBOOLEM1-of I means
  \<lambda>it.  for i be objectHIDDENM1 holds i inHIDDENR3 I implies it .FUNCT-1K1 i =XBOOLE-0R4 [:ZFMISC-1K2 X .FUNCT-1K1 i,Y .FUNCT-1K1 i :]"
proof-
  (*existence*)
    show " ex it be ManySortedSetPBOOLEM1-of I st  for i be objectHIDDENM1 holds i inHIDDENR3 I implies it .FUNCT-1K1 i =XBOOLE-0R4 [:ZFMISC-1K2 X .FUNCT-1K1 i,Y .FUNCT-1K1 i :]"
sorry
  (*uniqueness*)
    show " for it1 be ManySortedSetPBOOLEM1-of I holds  for it2 be ManySortedSetPBOOLEM1-of I holds ( for i be objectHIDDENM1 holds i inHIDDENR3 I implies it1 .FUNCT-1K1 i =XBOOLE-0R4 [:ZFMISC-1K2 X .FUNCT-1K1 i,Y .FUNCT-1K1 i :]) & ( for i be objectHIDDENM1 holds i inHIDDENR3 I implies it2 .FUNCT-1K1 i =XBOOLE-0R4 [:ZFMISC-1K2 X .FUNCT-1K1 i,Y .FUNCT-1K1 i :]) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mdef pboole_def_17 ("'(Funcs')PBOOLEK7\<^bsub>'( _ ')\<^esub>'( _ , _ ')" [0,0,0]164 ) where
  mlet "I be setHIDDENM2", "X be ManySortedSetPBOOLEM1-of I", "Y be ManySortedSetPBOOLEM1-of I"
"func (Funcs)PBOOLEK7\<^bsub>(I)\<^esub>(X,Y) \<rightarrow> ManySortedSetPBOOLEM1-of I means
  \<lambda>it.  for i be objectHIDDENM1 holds i inHIDDENR3 I implies it .FUNCT-1K1 i =XBOOLE-0R4 FuncsFUNCT-2K1(X .FUNCT-1K1 i,Y .FUNCT-1K1 i)"
proof-
  (*existence*)
    show " ex it be ManySortedSetPBOOLEM1-of I st  for i be objectHIDDENM1 holds i inHIDDENR3 I implies it .FUNCT-1K1 i =XBOOLE-0R4 FuncsFUNCT-2K1(X .FUNCT-1K1 i,Y .FUNCT-1K1 i)"
sorry
  (*uniqueness*)
    show " for it1 be ManySortedSetPBOOLEM1-of I holds  for it2 be ManySortedSetPBOOLEM1-of I holds ( for i be objectHIDDENM1 holds i inHIDDENR3 I implies it1 .FUNCT-1K1 i =XBOOLE-0R4 FuncsFUNCT-2K1(X .FUNCT-1K1 i,Y .FUNCT-1K1 i)) & ( for i be objectHIDDENM1 holds i inHIDDENR3 I implies it2 .FUNCT-1K1 i =XBOOLE-0R4 FuncsFUNCT-2K1(X .FUNCT-1K1 i,Y .FUNCT-1K1 i)) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mdef pboole_def_18 ("ManySortedSubsetPBOOLEM6\<^bsub>'( _ ')\<^esub>-of  _ " [0,70]70 ) where
  mlet "I be setHIDDENM2", "M be ManySortedSetPBOOLEM1-of I"
"mode ManySortedSubsetPBOOLEM6\<^bsub>(I)\<^esub>-of M \<rightarrow> ManySortedSetPBOOLEM1-of I means
  (\<lambda>it. it c=PBOOLER2\<^bsub>(I)\<^esub> M)"
proof-
  (*existence*)
    show " ex it be ManySortedSetPBOOLEM1-of I st it c=PBOOLER2\<^bsub>(I)\<^esub> M"
       sorry
qed "sorry"

mtheorem pboole_cl_10:
  mlet "I be setHIDDENM2", "M be non-emptyRELAT-1V2\<bar>ManySortedSetPBOOLEM1-of I"
"cluster non-emptyRELAT-1V2 for ManySortedSubsetPBOOLEM6\<^bsub>(I)\<^esub>-of M"
proof
(*existence*)
  show " ex it be ManySortedSubsetPBOOLEM6\<^bsub>(I)\<^esub>-of M st it be non-emptyRELAT-1V2"
sorry
qed "sorry"

mdef pboole_def_19 (" _ **PBOOLEK8  _ " [164,164]164 ) where
  mlet "F be Function-yieldingFUNCOP-1V1\<bar>FunctionFUNCT-1M1", "G be Function-yieldingFUNCOP-1V1\<bar>FunctionFUNCT-1M1"
"func G **PBOOLEK8 F \<rightarrow> FunctionFUNCT-1M1 means
  \<lambda>it. domRELAT-1K1 it =XBOOLE-0R4 domRELAT-1K1 F /\\XBOOLE-0K3 domRELAT-1K1 G & ( for i be objectHIDDENM1 holds i inHIDDENR3 domRELAT-1K1 it implies it .FUNCT-1K1 i =XBOOLE-0R4 G .FUNCT-1K1 i *FUNCT-1K3 F .FUNCT-1K1 i)"
proof-
  (*existence*)
    show " ex it be FunctionFUNCT-1M1 st domRELAT-1K1 it =XBOOLE-0R4 domRELAT-1K1 F /\\XBOOLE-0K3 domRELAT-1K1 G & ( for i be objectHIDDENM1 holds i inHIDDENR3 domRELAT-1K1 it implies it .FUNCT-1K1 i =XBOOLE-0R4 G .FUNCT-1K1 i *FUNCT-1K3 F .FUNCT-1K1 i)"
sorry
  (*uniqueness*)
    show " for it1 be FunctionFUNCT-1M1 holds  for it2 be FunctionFUNCT-1M1 holds (domRELAT-1K1 it1 =XBOOLE-0R4 domRELAT-1K1 F /\\XBOOLE-0K3 domRELAT-1K1 G & ( for i be objectHIDDENM1 holds i inHIDDENR3 domRELAT-1K1 it1 implies it1 .FUNCT-1K1 i =XBOOLE-0R4 G .FUNCT-1K1 i *FUNCT-1K3 F .FUNCT-1K1 i)) & (domRELAT-1K1 it2 =XBOOLE-0R4 domRELAT-1K1 F /\\XBOOLE-0K3 domRELAT-1K1 G & ( for i be objectHIDDENM1 holds i inHIDDENR3 domRELAT-1K1 it2 implies it2 .FUNCT-1K1 i =XBOOLE-0R4 G .FUNCT-1K1 i *FUNCT-1K3 F .FUNCT-1K1 i)) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mtheorem pboole_cl_11:
  mlet "F be Function-yieldingFUNCOP-1V1\<bar>FunctionFUNCT-1M1", "G be Function-yieldingFUNCOP-1V1\<bar>FunctionFUNCT-1M1"
"cluster G **PBOOLEK8 F as-term-is Function-yieldingFUNCOP-1V1"
proof
(*coherence*)
  show "G **PBOOLEK8 F be Function-yieldingFUNCOP-1V1"
sorry
qed "sorry"

mdef pboole_def_20 (" _ .:.:PBOOLEK9\<^bsub>'( _ ')\<^esub>  _ " [164,0,164]164 ) where
  mlet "I be setHIDDENM2", "A be ManySortedSetPBOOLEM1-of I", "F be ManySortedFunctionPBOOLEM2-of I"
"func F .:.:PBOOLEK9\<^bsub>(I)\<^esub> A \<rightarrow> ManySortedSetPBOOLEM1-of I means
  \<lambda>it.  for i be setHIDDENM2 holds i inTARSKIR2 I implies it .FUNCT-1K1 i =XBOOLE-0R4 (F .FUNCT-1K1 i).:FUNCT-1K5 (A .FUNCT-1K1 i)"
proof-
  (*existence*)
    show " ex it be ManySortedSetPBOOLEM1-of I st  for i be setHIDDENM2 holds i inTARSKIR2 I implies it .FUNCT-1K1 i =XBOOLE-0R4 (F .FUNCT-1K1 i).:FUNCT-1K5 (A .FUNCT-1K1 i)"
sorry
  (*uniqueness*)
    show " for it1 be ManySortedSetPBOOLEM1-of I holds  for it2 be ManySortedSetPBOOLEM1-of I holds ( for i be setHIDDENM2 holds i inTARSKIR2 I implies it1 .FUNCT-1K1 i =XBOOLE-0R4 (F .FUNCT-1K1 i).:FUNCT-1K5 (A .FUNCT-1K1 i)) & ( for i be setHIDDENM2 holds i inTARSKIR2 I implies it2 .FUNCT-1K1 i =XBOOLE-0R4 (F .FUNCT-1K1 i).:FUNCT-1K5 (A .FUNCT-1K1 i)) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mtheorem pboole_cl_12:
  mlet "I be setHIDDENM2"
"cluster EmptyMSPBOOLEK1 I as-term-is empty-yieldingRELAT-1V3"
proof
(*coherence*)
  show "EmptyMSPBOOLEK1 I be empty-yieldingRELAT-1V3"
    using funcop_1_th_13 sorry
qed "sorry"

theorem pboole_sch_6:
  fixes If0 Pp2 
  assumes
[ty]: "If0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
   A1: " for i be ElementSUBSET-1M1-of If0 holds  ex j be objectHIDDENM1 st Pp2(i,j)"
  shows " ex f be ManySortedSetPBOOLEM1-of If0 st  for i be ElementSUBSET-1M1-of If0 holds Pp2(i,f .FUNCT-1K1 i)"
sorry

mtheorem pboole_cl_13:
  mlet "A be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster non-emptyRELAT-1V2 also-is  non empty-yieldingRELAT-1V3 for ManySortedSetPBOOLEM1-of A"
proof
(*coherence*)
  show " for it be ManySortedSetPBOOLEM1-of A holds it be non-emptyRELAT-1V2 implies it be  non empty-yieldingRELAT-1V3"
     sorry
qed "sorry"

mtheorem pboole_cl_14:
  mlet "X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster note-that  non emptyXBOOLE-0V1 for ManySortedSetPBOOLEM1-of X"
proof
(*coherence*)
  show " for it be ManySortedSetPBOOLEM1-of X holds it be  non emptyXBOOLE-0V1"
     sorry
qed "sorry"

mtheorem pboole_th_140:
" for F be Function-yieldingFUNCOP-1V1\<bar>FunctionFUNCT-1M1 holds  for G be Function-yieldingFUNCOP-1V1\<bar>FunctionFUNCT-1M1 holds  for H be Function-yieldingFUNCOP-1V1\<bar>FunctionFUNCT-1M1 holds (H **PBOOLEK8 G)**PBOOLEK8 F =FUNCT-1R1 H **PBOOLEK8 (G **PBOOLEK8 F)"
sorry

mtheorem pboole_cl_15:
  mlet "I be setHIDDENM2", "f be non-emptyRELAT-1V2\<bar>ManySortedSetPBOOLEM1-of I"
"cluster totalPARTFUN1V1\<^bsub>(I)\<^esub> for I -definedRELAT-1V4\<bar>f -compatibleFUNCT-1V7\<bar>FunctionFUNCT-1M1"
proof
(*existence*)
  show " ex it be I -definedRELAT-1V4\<bar>f -compatibleFUNCT-1V7\<bar>FunctionFUNCT-1M1 st it be totalPARTFUN1V1\<^bsub>(I)\<^esub>"
sorry
qed "sorry"

mtheorem pboole_th_141:
" for I be setHIDDENM2 holds  for f be non-emptyRELAT-1V2\<bar>ManySortedSetPBOOLEM1-of I holds  for p be f -compatibleFUNCT-1V7\<bar>I -definedRELAT-1V4\<bar>FunctionFUNCT-1M1 holds  ex s be f -compatibleFUNCT-1V7\<bar>ManySortedSetPBOOLEM1-of I st p c=RELAT-1R2 s"
sorry

mtheorem pboole_th_142:
" for I be setHIDDENM2 holds  for A be setHIDDENM2 holds  for s be ManySortedSetPBOOLEM1-of I holds  for ss be ManySortedSetPBOOLEM1-of I holds (ss +*FUNCT-4K1 s |RELAT-1K8 A)|RELAT-1K8 A =FUNCT-1R1 s |RELAT-1K8 A"
sorry

mtheorem pboole_cl_16:
  mlet "X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "Y be setHIDDENM2"
"cluster X -valuedRELAT-1V5 for ManySortedSetPBOOLEM1-of Y"
proof
(*existence*)
  show " ex it be ManySortedSetPBOOLEM1-of Y st it be X -valuedRELAT-1V5"
sorry
qed "sorry"

mtheorem pboole_th_143:
" for I be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for Y be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for M be Y -valuedRELAT-1V5\<bar>ManySortedSetPBOOLEM1-of I holds  for x be ElementSUBSET-1M1-of I holds M .FUNCT-1K1 x =XBOOLE-0R4 M /.PARTFUN1K7\<^bsub>(Y)\<^esub> x"
sorry

mtheorem pboole_th_144:
" for I be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds  for M be ManySortedSetPBOOLEM1-of I holds (f +*FUNCT-4K1 M)|RELAT-1K8 I =FUNCT-1R1 M"
sorry

mtheorem pboole_th_145:
" for I be setHIDDENM2 holds  for Y be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for p be Y -valuedRELAT-1V5\<bar>I -definedRELAT-1V4\<bar>FunctionFUNCT-1M1 holds  ex s be Y -valuedRELAT-1V5\<bar>ManySortedSetPBOOLEM1-of I st p c=RELAT-1R2 s"
sorry

mtheorem pboole_th_146:
" for I be setHIDDENM2 holds  for X be ManySortedSetPBOOLEM1-of I holds  for Y be ManySortedSetPBOOLEM1-of I holds X c=PBOOLER2\<^bsub>(I)\<^esub> Y & Y c=PBOOLER2\<^bsub>(I)\<^esub> X implies X =PBOOLER7\<^bsub>(I)\<^esub> Y"
  using pboole_lm_1 sorry

syntax PBOOLER9 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> o" (" _ =PBOOLER9\<^bsub>'( _ ')\<^esub>  _ " [50,0,50]50)
translations "A =PBOOLER9\<^bsub>(I)\<^esub> B" \<rightharpoonup> "A =HIDDENR1 B"

mtheorem pboole_def_21:
  mlet "I be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "A be ManySortedSetPBOOLEM1-of I", "B be ManySortedSetPBOOLEM1-of I"
"redefine pred A =PBOOLER9\<^bsub>(I)\<^esub> B means
   for i be ElementSUBSET-1M1-of I holds A .FUNCT-1K1 i =XBOOLE-0R4 B .FUNCT-1K1 i"
proof
(*compatibility*)
  show "A =PBOOLER9\<^bsub>(I)\<^esub> B iff ( for i be ElementSUBSET-1M1-of I holds A .FUNCT-1K1 i =XBOOLE-0R4 B .FUNCT-1K1 i)"
     sorry
qed "sorry"

mtheorem pboole_cl_17:
  mlet "X be with-non-empty-elementsSETFAM-1V1\<bar>setHIDDENM2"
"cluster idPARTFUN1K6 X as-term-is non-emptyFUNCT-1V4"
proof
(*coherence*)
  show "idPARTFUN1K6 X be non-emptyFUNCT-1V4"
    using setfam_1_def_8 sorry
qed "sorry"

theorem pboole_sch_7:
  fixes If0 Ff1 
  assumes
[ty]: "If0 be setHIDDENM2" and
  [ty_func]: "\<And> x1. x1 be objectHIDDENM1 \<Longrightarrow> Ff1(x1) be objectHIDDENM1"
  shows " ex f be ManySortedSetPBOOLEM1-of If0 st  for i be setHIDDENM2 holds i inTARSKIR2 If0 implies f .FUNCT-1K1 i =HIDDENR1 Ff1(i)"
sorry

end
