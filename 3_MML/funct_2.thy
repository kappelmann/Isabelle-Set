theory funct_2
  imports setfam_1 mcart_1 partfun1
begin
(*begin*)
reserve P, Q, X, Y, Z for "setHIDDENM2"
reserve p, x, x9, x1, x2, y, z for "objectHIDDENM1"
mdef funct_2_def_1 ("quasi-totalFUNCT-2V1\<^bsub>'( _ , _ ')\<^esub>" [0,0]70 ) where
  mlet "X be setHIDDENM2", "Y be setHIDDENM2"
"attr quasi-totalFUNCT-2V1\<^bsub>(X,Y)\<^esub> for RelationRELSET-1M1-of(X,Y) means
  \<lambda>R. X =XBOOLE-0R4 domRELSET-1K1\<^bsub>(X)\<^esub> R if \<lambda>R. Y <>HIDDENR2 {}XBOOLE-0K1 otherwise \<lambda>R. R =RELAT-1R1 {}XBOOLE-0K1"
proof-
  (*consistency*)
    show " for R be RelationRELSET-1M1-of(X,Y) holds  True "
sorry
qed "sorry"

mtheorem funct_2_cl_1:
  mlet "X be setHIDDENM2", "Y be setHIDDENM2"
"cluster quasi-totalFUNCT-2V1\<^bsub>(X,Y)\<^esub> for PartFuncPARTFUN1M1-of(X,Y)"
proof
(*existence*)
  show " ex it be PartFuncPARTFUN1M1-of(X,Y) st it be quasi-totalFUNCT-2V1\<^bsub>(X,Y)\<^esub>"
sorry
qed "sorry"

mtheorem funct_2_cl_2:
  mlet "X be setHIDDENM2", "Y be setHIDDENM2"
"cluster totalPARTFUN1V1\<^bsub>(X)\<^esub> also-is quasi-totalFUNCT-2V1\<^bsub>(X,Y)\<^esub> for RelationRELSET-1M1-of(X,Y)"
proof
(*coherence*)
  show " for it be RelationRELSET-1M1-of(X,Y) holds it be totalPARTFUN1V1\<^bsub>(X)\<^esub> implies it be quasi-totalFUNCT-2V1\<^bsub>(X,Y)\<^esub>"
sorry
qed "sorry"

abbreviation(input) FUNCT_2M1("FunctionFUNCT-2M1-of'( _ , _ ')" [0,0]70) where
  "FunctionFUNCT-2M1-of(X,Y) \<equiv> quasi-totalFUNCT-2V1\<^bsub>(X,Y)\<^esub>\<bar>PartFuncPARTFUN1M1-of(X,Y)"

mtheorem funct_2_cl_3:
  mlet "X be emptyXBOOLE-0V1\<bar>setHIDDENM2", "Y be setHIDDENM2"
"cluster quasi-totalFUNCT-2V1\<^bsub>(X,Y)\<^esub> also-is totalPARTFUN1V1\<^bsub>(X)\<^esub> for RelationRELSET-1M1-of(X,Y)"
proof
(*coherence*)
  show " for it be RelationRELSET-1M1-of(X,Y) holds it be quasi-totalFUNCT-2V1\<^bsub>(X,Y)\<^esub> implies it be totalPARTFUN1V1\<^bsub>(X)\<^esub>"
     sorry
qed "sorry"

mtheorem funct_2_cl_4:
  mlet "X be setHIDDENM2", "Y be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster quasi-totalFUNCT-2V1\<^bsub>(X,Y)\<^esub> also-is totalPARTFUN1V1\<^bsub>(X)\<^esub> for RelationRELSET-1M1-of(X,Y)"
proof
(*coherence*)
  show " for it be RelationRELSET-1M1-of(X,Y) holds it be quasi-totalFUNCT-2V1\<^bsub>(X,Y)\<^esub> implies it be totalPARTFUN1V1\<^bsub>(X)\<^esub>"
    using funct_2_def_1 sorry
qed "sorry"

mtheorem funct_2_cl_5:
  mlet "X be setHIDDENM2"
"cluster quasi-totalFUNCT-2V1\<^bsub>(X,X)\<^esub> also-is totalPARTFUN1V1\<^bsub>(X)\<^esub> for RelationRELSET-1M1-of(X,X)"
proof
(*coherence*)
  show " for it be RelationRELSET-1M1-of(X,X) holds it be quasi-totalFUNCT-2V1\<^bsub>(X,X)\<^esub> implies it be totalPARTFUN1V1\<^bsub>(X)\<^esub>"
sorry
qed "sorry"

mtheorem funct_2_cl_6:
  mlet "X be setHIDDENM2"
"cluster quasi-totalFUNCT-2V1\<^bsub>([:ZFMISC-1K2 X,X :],X)\<^esub> also-is totalPARTFUN1V1\<^bsub>([:ZFMISC-1K2 X,X :])\<^esub> for RelationRELSET-1M1-of([:ZFMISC-1K2 X,X :],X)"
proof
(*coherence*)
  show " for it be RelationRELSET-1M1-of([:ZFMISC-1K2 X,X :],X) holds it be quasi-totalFUNCT-2V1\<^bsub>([:ZFMISC-1K2 X,X :],X)\<^esub> implies it be totalPARTFUN1V1\<^bsub>([:ZFMISC-1K2 X,X :])\<^esub>"
sorry
qed "sorry"

mtheorem funct_2_th_1:
" for f be FunctionFUNCT-1M1 holds f be FunctionFUNCT-2M1-of(domRELAT-1K1 f,rngFUNCT-1K2 f)"
sorry

mtheorem funct_2_th_2:
" for Y be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds rngFUNCT-1K2 f c=TARSKIR1 Y implies f be FunctionFUNCT-2M1-of(domRELAT-1K1 f,Y)"
sorry

mtheorem funct_2_th_3:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds domRELAT-1K1 f =XBOOLE-0R4 X & ( for x be objectHIDDENM1 holds x inHIDDENR3 X implies f .FUNCT-1K1 x inTARSKIR2 Y) implies f be FunctionFUNCT-2M1-of(X,Y)"
sorry

mtheorem funct_2_th_4:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for x be objectHIDDENM1 holds  for f be FunctionFUNCT-2M1-of(X,Y) holds Y <>HIDDENR2 {}XBOOLE-0K1 & x inHIDDENR3 X implies f .FUNCT-1K1 x inTARSKIR2 rngRELSET-1K2\<^bsub>(Y)\<^esub> f"
sorry

mtheorem funct_2_th_5:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for x be objectHIDDENM1 holds  for f be FunctionFUNCT-2M1-of(X,Y) holds Y <>HIDDENR2 {}XBOOLE-0K1 & x inHIDDENR3 X implies f .FUNCT-1K1 x inTARSKIR2 Y"
sorry

mtheorem funct_2_th_6:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(X,Y) holds (Y =XBOOLE-0R4 {}XBOOLE-0K1 implies X =XBOOLE-0R4 {}XBOOLE-0K1) & rngRELSET-1K2\<^bsub>(Y)\<^esub> f c=TARSKIR1 Z implies f be FunctionFUNCT-2M1-of(X,Z)"
sorry

mtheorem funct_2_th_7:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(X,Y) holds (Y =XBOOLE-0R4 {}XBOOLE-0K1 implies X =XBOOLE-0R4 {}XBOOLE-0K1) & Y c=TARSKIR1 Z implies f be FunctionFUNCT-2M1-of(X,Z)"
  using relset_1_th_7 sorry

theorem funct_2_sch_1:
  fixes Xf0 Yf0 Pp2 
  assumes
[ty]: "Xf0 be setHIDDENM2" and
  [ty]: "Yf0 be setHIDDENM2" and
   A1: " for x be objectHIDDENM1 holds x inHIDDENR3 Xf0 implies ( ex y be objectHIDDENM1 st y inHIDDENR3 Yf0 & Pp2(x,y))"
  shows " ex f be FunctionFUNCT-2M1-of(Xf0,Yf0) st  for x be objectHIDDENM1 holds x inHIDDENR3 Xf0 implies Pp2(x,f .FUNCT-1K1 x)"
sorry

theorem funct_2_sch_2:
  fixes Xf0 Yf0 Ff1 
  assumes
[ty]: "Xf0 be setHIDDENM2" and
  [ty]: "Yf0 be setHIDDENM2" and
  [ty_func]: "\<And> x1. x1 be objectHIDDENM1 \<Longrightarrow> Ff1(x1) be objectHIDDENM1" and
   A1: " for x be objectHIDDENM1 holds x inHIDDENR3 Xf0 implies Ff1(x) inHIDDENR3 Yf0"
  shows " ex f be FunctionFUNCT-2M1-of(Xf0,Yf0) st  for x be objectHIDDENM1 holds x inHIDDENR3 Xf0 implies f .FUNCT-1K1 x =HIDDENR1 Ff1(x)"
sorry

mdef funct_2_def_2 ("FuncsFUNCT-2K1'( _ , _ ')" [0,0]228 ) where
  mlet "X be setHIDDENM2", "Y be setHIDDENM2"
"func FuncsFUNCT-2K1(X,Y) \<rightarrow> setHIDDENM2 means
  \<lambda>it.  for x be objectHIDDENM1 holds x inHIDDENR3 it iff ( ex f be FunctionFUNCT-1M1 st (x =HIDDENR1 f & domRELAT-1K1 f =XBOOLE-0R4 X) & rngFUNCT-1K2 f c=TARSKIR1 Y)"
proof-
  (*existence*)
    show " ex it be setHIDDENM2 st  for x be objectHIDDENM1 holds x inHIDDENR3 it iff ( ex f be FunctionFUNCT-1M1 st (x =HIDDENR1 f & domRELAT-1K1 f =XBOOLE-0R4 X) & rngFUNCT-1K2 f c=TARSKIR1 Y)"
sorry
  (*uniqueness*)
    show " for it1 be setHIDDENM2 holds  for it2 be setHIDDENM2 holds ( for x be objectHIDDENM1 holds x inHIDDENR3 it1 iff ( ex f be FunctionFUNCT-1M1 st (x =HIDDENR1 f & domRELAT-1K1 f =XBOOLE-0R4 X) & rngFUNCT-1K2 f c=TARSKIR1 Y)) & ( for x be objectHIDDENM1 holds x inHIDDENR3 it2 iff ( ex f be FunctionFUNCT-1M1 st (x =HIDDENR1 f & domRELAT-1K1 f =XBOOLE-0R4 X) & rngFUNCT-1K2 f c=TARSKIR1 Y)) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mtheorem funct_2_th_8:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(X,Y) holds (Y =XBOOLE-0R4 {}XBOOLE-0K1 implies X =XBOOLE-0R4 {}XBOOLE-0K1) implies f inTARSKIR2 FuncsFUNCT-2K1(X,Y)"
sorry

mtheorem funct_2_th_9:
" for X be setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(X,X) holds f inTARSKIR2 FuncsFUNCT-2K1(X,X)"
  using funct_2_th_8 sorry

mtheorem funct_2_cl_7:
  mlet "X be setHIDDENM2", "Y be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster FuncsFUNCT-2K1(X,Y) as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "FuncsFUNCT-2K1(X,Y) be  non emptyXBOOLE-0V1"
    using funct_2_th_8 sorry
qed "sorry"

mtheorem funct_2_cl_8:
  mlet "X be setHIDDENM2"
"cluster FuncsFUNCT-2K1(X,X) as-term-is  non emptyXBOOLE-0V1"
proof
(*coherence*)
  show "FuncsFUNCT-2K1(X,X) be  non emptyXBOOLE-0V1"
    using funct_2_th_8 sorry
qed "sorry"

mtheorem funct_2_cl_9:
  mlet "X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "Y be emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster FuncsFUNCT-2K1(X,Y) as-term-is emptyXBOOLE-0V1"
proof
(*coherence*)
  show "FuncsFUNCT-2K1(X,Y) be emptyXBOOLE-0V1"
sorry
qed "sorry"

mtheorem funct_2_th_10:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(X,Y) holds ( for y be objectHIDDENM1 holds y inHIDDENR3 Y implies ( ex x be objectHIDDENM1 st x inHIDDENR3 X & y =HIDDENR1 f .FUNCT-1K1 x)) implies rngRELSET-1K2\<^bsub>(Y)\<^esub> f =XBOOLE-0R4 Y"
sorry

mtheorem funct_2_th_11:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for y be objectHIDDENM1 holds  for f be FunctionFUNCT-2M1-of(X,Y) holds y inHIDDENR3 rngRELSET-1K2\<^bsub>(Y)\<^esub> f implies ( ex x be objectHIDDENM1 st x inHIDDENR3 X & f .FUNCT-1K1 x =HIDDENR1 y)"
sorry

mtheorem funct_2_th_12:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f1 be FunctionFUNCT-2M1-of(X,Y) holds  for f2 be FunctionFUNCT-2M1-of(X,Y) holds ( for x be objectHIDDENM1 holds x inHIDDENR3 X implies f1 .FUNCT-1K1 x =XBOOLE-0R4 f2 .FUNCT-1K1 x) implies f1 =RELSET-1R2\<^bsub>(X,Y)\<^esub> f2"
sorry

mtheorem funct_2_th_13:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds  for f be quasi-totalFUNCT-2V1\<^bsub>(X,Y)\<^esub>\<bar>RelationRELSET-1M1-of(X,Y) holds  for g be quasi-totalFUNCT-2V1\<^bsub>(Y,Z)\<^esub>\<bar>RelationRELSET-1M1-of(Y,Z) holds (Y =XBOOLE-0R4 {}XBOOLE-0K1 implies Z =XBOOLE-0R4 {}XBOOLE-0K1 or X =XBOOLE-0R4 {}XBOOLE-0K1) implies f *RELSET-1K4\<^bsub>(X,Y,Y,Z)\<^esub> g be quasi-totalFUNCT-2V1\<^bsub>(X,Z)\<^esub>"
sorry

mtheorem funct_2_th_14:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(X,Y) holds  for g be FunctionFUNCT-2M1-of(Y,Z) holds (Z <>HIDDENR2 {}XBOOLE-0K1 & rngRELSET-1K2\<^bsub>(Y)\<^esub> f =XBOOLE-0R4 Y) & rngRELSET-1K2\<^bsub>(Z)\<^esub> g =XBOOLE-0R4 Z implies rngRELSET-1K2\<^bsub>(Z)\<^esub> (g *PARTFUN1K1\<^bsub>(X,Y,Y,Z)\<^esub> f) =XBOOLE-0R4 Z"
sorry

mtheorem funct_2_th_15:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for x be objectHIDDENM1 holds  for f be FunctionFUNCT-2M1-of(X,Y) holds  for g be FunctionFUNCT-1M1 holds Y <>HIDDENR2 {}XBOOLE-0K1 & x inHIDDENR3 X implies (g *FUNCT-1K3 f).FUNCT-1K1 x =XBOOLE-0R4 g .FUNCT-1K1 (f .FUNCT-1K1 x)"
sorry

mtheorem funct_2_th_16:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(X,Y) holds Y <>HIDDENR2 {}XBOOLE-0K1 implies (rngRELSET-1K2\<^bsub>(Y)\<^esub> f =XBOOLE-0R4 Y iff ( for Z be setHIDDENM2 holds Z <>HIDDENR2 {}XBOOLE-0K1 implies ( for g be FunctionFUNCT-2M1-of(Y,Z) holds  for h be FunctionFUNCT-2M1-of(Y,Z) holds g *PARTFUN1K1\<^bsub>(X,Y,Y,Z)\<^esub> f =RELSET-1R2\<^bsub>(X,Z)\<^esub> h *PARTFUN1K1\<^bsub>(X,Y,Y,Z)\<^esub> f implies g =RELSET-1R2\<^bsub>(Y,Z)\<^esub> h)))"
sorry

mtheorem funct_2_th_17:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be RelationRELSET-1M1-of(X,Y) holds idPARTFUN1K6 X *RELSET-1K4\<^bsub>(X,X,X,Y)\<^esub> f =RELSET-1R2\<^bsub>(X,Y)\<^esub> f & f *RELSET-1K4\<^bsub>(X,Y,Y,Y)\<^esub> idPARTFUN1K6 Y =RELSET-1R2\<^bsub>(X,Y)\<^esub> f"
sorry

mtheorem funct_2_th_18:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(X,Y) holds  for g be FunctionFUNCT-2M1-of(Y,X) holds f *PARTFUN1K1\<^bsub>(Y,X,X,Y)\<^esub> g =RELSET-1R2\<^bsub>(Y,Y)\<^esub> idPARTFUN1K6 Y implies rngRELSET-1K2\<^bsub>(Y)\<^esub> f =XBOOLE-0R4 Y"
sorry

mtheorem funct_2_th_19:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(X,Y) holds (Y =XBOOLE-0R4 {}XBOOLE-0K1 implies X =XBOOLE-0R4 {}XBOOLE-0K1) implies (f be one-to-oneFUNCT-1V2 iff ( for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds (x1 inHIDDENR3 X & x2 inHIDDENR3 X) & f .FUNCT-1K1 x1 =XBOOLE-0R4 f .FUNCT-1K1 x2 implies x1 =HIDDENR1 x2))"
sorry

mtheorem funct_2_th_20:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(X,Y) holds  for g be FunctionFUNCT-2M1-of(Y,Z) holds (Z =XBOOLE-0R4 {}XBOOLE-0K1 implies Y =XBOOLE-0R4 {}XBOOLE-0K1) & g *PARTFUN1K1\<^bsub>(X,Y,Y,Z)\<^esub> f be one-to-oneFUNCT-1V2 implies f be one-to-oneFUNCT-1V2"
sorry

mtheorem funct_2_th_21:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(X,Y) holds X <>HIDDENR2 {}XBOOLE-0K1 & Y <>HIDDENR2 {}XBOOLE-0K1 implies (f be one-to-oneFUNCT-1V2 iff ( for Z be setHIDDENM2 holds  for g be FunctionFUNCT-2M1-of(Z,X) holds  for h be FunctionFUNCT-2M1-of(Z,X) holds f *PARTFUN1K1\<^bsub>(Z,X,X,Y)\<^esub> g =RELSET-1R2\<^bsub>(Z,Y)\<^esub> f *PARTFUN1K1\<^bsub>(Z,X,X,Y)\<^esub> h implies g =RELSET-1R2\<^bsub>(Z,X)\<^esub> h))"
sorry

mtheorem funct_2_th_22:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(X,Y) holds  for g be FunctionFUNCT-2M1-of(Y,Z) holds (Z <>HIDDENR2 {}XBOOLE-0K1 & rngRELSET-1K2\<^bsub>(Z)\<^esub> (g *PARTFUN1K1\<^bsub>(X,Y,Y,Z)\<^esub> f) =XBOOLE-0R4 Z) & g be one-to-oneFUNCT-1V2 implies rngRELSET-1K2\<^bsub>(Y)\<^esub> f =XBOOLE-0R4 Y"
sorry

mdef funct_2_def_3 ("ontoFUNCT-2V2\<^bsub>'( _ ')\<^esub>" [0]70 ) where
  mlet "Y be setHIDDENM2"
"attr ontoFUNCT-2V2\<^bsub>(Y)\<^esub> for Y -valuedRELAT-1V5\<bar>RelationRELAT-1M1 means
  (\<lambda>f. rngRELSET-1K2\<^bsub>(Y)\<^esub> f =XBOOLE-0R4 Y)"..

mtheorem funct_2_th_23:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(X,Y) holds  for g be FunctionFUNCT-2M1-of(Y,X) holds g *PARTFUN1K1\<^bsub>(X,Y,Y,X)\<^esub> f =RELSET-1R2\<^bsub>(X,X)\<^esub> idPARTFUN1K6 X implies f be one-to-oneFUNCT-1V2 & g be ontoFUNCT-2V2\<^bsub>(X)\<^esub>"
sorry

mtheorem funct_2_th_24:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(X,Y) holds  for g be FunctionFUNCT-2M1-of(Y,Z) holds ((Z =XBOOLE-0R4 {}XBOOLE-0K1 implies Y =XBOOLE-0R4 {}XBOOLE-0K1) & g *PARTFUN1K1\<^bsub>(X,Y,Y,Z)\<^esub> f be one-to-oneFUNCT-1V2) & rngRELSET-1K2\<^bsub>(Y)\<^esub> f =XBOOLE-0R4 Y implies f be one-to-oneFUNCT-1V2 & g be one-to-oneFUNCT-1V2"
sorry

mtheorem funct_2_th_25:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(X,Y) holds f be one-to-oneFUNCT-1V2 & rngRELSET-1K2\<^bsub>(Y)\<^esub> f =XBOOLE-0R4 Y implies f \<inverse>FUNCT-1K4 be FunctionFUNCT-2M1-of(Y,X)"
sorry

mtheorem funct_2_th_26:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for x be objectHIDDENM1 holds  for f be FunctionFUNCT-2M1-of(X,Y) holds (Y <>HIDDENR2 {}XBOOLE-0K1 & f be one-to-oneFUNCT-1V2) & x inHIDDENR3 X implies f \<inverse>FUNCT-1K4 .FUNCT-1K1 (f .FUNCT-1K1 x) =HIDDENR1 x"
sorry

mtheorem funct_2_th_27:
" for X be setHIDDENM2 holds  for Y be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for Z be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(X,Y) holds  for g be FunctionFUNCT-2M1-of(Y,Z) holds f be ontoFUNCT-2V2\<^bsub>(Y)\<^esub> & g be ontoFUNCT-2V2\<^bsub>(Z)\<^esub> implies g *PARTFUN1K1\<^bsub>(X,Y,Y,Z)\<^esub> f be ontoFUNCT-2V2\<^bsub>(Z)\<^esub>"
sorry

mtheorem funct_2_th_28:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(X,Y) holds  for g be FunctionFUNCT-2M1-of(Y,X) holds (((X <>HIDDENR2 {}XBOOLE-0K1 & Y <>HIDDENR2 {}XBOOLE-0K1) & rngRELSET-1K2\<^bsub>(Y)\<^esub> f =XBOOLE-0R4 Y) & f be one-to-oneFUNCT-1V2) & ( for y be objectHIDDENM1 holds  for x be objectHIDDENM1 holds y inHIDDENR3 Y & g .FUNCT-1K1 y =HIDDENR1 x iff x inHIDDENR3 X & f .FUNCT-1K1 x =HIDDENR1 y) implies g =FUNCT-1R1 f \<inverse>FUNCT-1K4"
sorry

mtheorem funct_2_th_29:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(X,Y) holds (Y <>HIDDENR2 {}XBOOLE-0K1 & rngRELSET-1K2\<^bsub>(Y)\<^esub> f =XBOOLE-0R4 Y) & f be one-to-oneFUNCT-1V2 implies f \<inverse>FUNCT-1K4 *FUNCT-1K3 f =FUNCT-1R1 idPARTFUN1K6 X & f *FUNCT-1K3 f \<inverse>FUNCT-1K4 =FUNCT-1R1 idPARTFUN1K6 Y"
sorry

mtheorem funct_2_th_30:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(X,Y) holds  for g be FunctionFUNCT-2M1-of(Y,X) holds (((X <>HIDDENR2 {}XBOOLE-0K1 & Y <>HIDDENR2 {}XBOOLE-0K1) & rngRELSET-1K2\<^bsub>(Y)\<^esub> f =XBOOLE-0R4 Y) & g *PARTFUN1K1\<^bsub>(X,Y,Y,X)\<^esub> f =RELSET-1R2\<^bsub>(X,X)\<^esub> idPARTFUN1K6 X) & f be one-to-oneFUNCT-1V2 implies g =FUNCT-1R1 f \<inverse>FUNCT-1K4"
sorry

mtheorem funct_2_th_31:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(X,Y) holds Y <>HIDDENR2 {}XBOOLE-0K1 & ( ex g be FunctionFUNCT-2M1-of(Y,X) st g *PARTFUN1K1\<^bsub>(X,Y,Y,X)\<^esub> f =RELSET-1R2\<^bsub>(X,X)\<^esub> idPARTFUN1K6 X) implies f be one-to-oneFUNCT-1V2"
sorry

mtheorem funct_2_th_32:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(X,Y) holds (Y =XBOOLE-0R4 {}XBOOLE-0K1 implies X =XBOOLE-0R4 {}XBOOLE-0K1) & Z c=TARSKIR1 X implies f |PARTFUN1K2\<^bsub>(X,Y)\<^esub> Z be FunctionFUNCT-2M1-of(Z,Y)"
sorry

mtheorem funct_2_th_33:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(X,Y) holds X c=TARSKIR1 Z implies f |PARTFUN1K2\<^bsub>(X,Y)\<^esub> Z =RELSET-1R2\<^bsub>(X,Y)\<^esub> f"
  using relset_1_th_19 sorry

mtheorem funct_2_th_34:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds  for x be objectHIDDENM1 holds  for f be FunctionFUNCT-2M1-of(X,Y) holds (Y <>HIDDENR2 {}XBOOLE-0K1 & x inHIDDENR3 X) & f .FUNCT-1K1 x inTARSKIR2 Z implies (Z |`RELSET-1K6\<^bsub>(X,Y)\<^esub> f).FUNCT-1K1 x =XBOOLE-0R4 f .FUNCT-1K1 x"
sorry

mtheorem funct_2_th_35:
" for P be setHIDDENM2 holds  for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(X,Y) holds Y <>HIDDENR2 {}XBOOLE-0K1 implies ( for y be objectHIDDENM1 holds ( ex x be objectHIDDENM1 st (x inHIDDENR3 X & x inHIDDENR3 P) & y =HIDDENR1 f .FUNCT-1K1 x) implies y inHIDDENR3 f .:RELSET-1K7\<^bsub>(X,Y)\<^esub> P)"
sorry

mtheorem funct_2_th_36:
" for P be setHIDDENM2 holds  for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(X,Y) holds f .:RELSET-1K7\<^bsub>(X,Y)\<^esub> P c=TARSKIR1 Y"
   sorry

(*\$CT*)
mtheorem funct_2_th_38:
" for Q be setHIDDENM2 holds  for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(X,Y) holds Y <>HIDDENR2 {}XBOOLE-0K1 implies ( for x be objectHIDDENM1 holds x inHIDDENR3 f \<inverse>RELSET-1K8\<^bsub>(X,Y)\<^esub> Q iff x inHIDDENR3 X & f .FUNCT-1K1 x inTARSKIR2 Q)"
sorry

mtheorem funct_2_th_39:
" for Q be setHIDDENM2 holds  for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be PartFuncPARTFUN1M1-of(X,Y) holds f \<inverse>RELSET-1K8\<^bsub>(X,Y)\<^esub> Q c=TARSKIR1 X"
   sorry

mtheorem funct_2_th_40:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(X,Y) holds (Y =XBOOLE-0R4 {}XBOOLE-0K1 implies X =XBOOLE-0R4 {}XBOOLE-0K1) implies f \<inverse>RELSET-1K8\<^bsub>(X,Y)\<^esub> Y =XBOOLE-0R4 X"
sorry

mtheorem funct_2_th_41:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(X,Y) holds ( for y be objectHIDDENM1 holds y inHIDDENR3 Y implies f \<inverse>RELSET-1K8\<^bsub>(X,Y)\<^esub> {TARSKIK1 y} <>HIDDENR2 {}XBOOLE-0K1) iff rngRELSET-1K2\<^bsub>(Y)\<^esub> f =XBOOLE-0R4 Y"
  using funct_1_th_73 funct_1_th_72 sorry

mtheorem funct_2_th_42:
" for P be setHIDDENM2 holds  for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(X,Y) holds (Y =XBOOLE-0R4 {}XBOOLE-0K1 implies X =XBOOLE-0R4 {}XBOOLE-0K1) & P c=TARSKIR1 X implies P c=TARSKIR1 f \<inverse>RELSET-1K8\<^bsub>(X,Y)\<^esub> (f .:RELSET-1K7\<^bsub>(X,Y)\<^esub> P)"
sorry

mtheorem funct_2_th_43:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(X,Y) holds (Y =XBOOLE-0R4 {}XBOOLE-0K1 implies X =XBOOLE-0R4 {}XBOOLE-0K1) implies f \<inverse>RELSET-1K8\<^bsub>(X,Y)\<^esub> (f .:RELSET-1K7\<^bsub>(X,Y)\<^esub> X) =XBOOLE-0R4 X"
sorry

mtheorem funct_2_th_44:
" for Q be setHIDDENM2 holds  for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(X,Y) holds  for g be FunctionFUNCT-2M1-of(Y,Z) holds (Z =XBOOLE-0R4 {}XBOOLE-0K1 implies Y =XBOOLE-0R4 {}XBOOLE-0K1) implies f \<inverse>RELSET-1K8\<^bsub>(X,Y)\<^esub> Q c=TARSKIR1 (g *PARTFUN1K1\<^bsub>(X,Y,Y,Z)\<^esub> f)\<inverse>RELSET-1K8\<^bsub>(X,Z)\<^esub> (g .:RELSET-1K7\<^bsub>(Y,Z)\<^esub> Q)"
sorry

mtheorem funct_2_th_45:
" for P be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of({}XBOOLE-0K1,Y) holds f .:RELSET-1K7\<^bsub>({}XBOOLE-0K1,Y)\<^esub> P =FUNCT-1R1 {}XBOOLE-0K1"
   sorry

mtheorem funct_2_th_46:
" for Q be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of({}XBOOLE-0K1,Y) holds f \<inverse>RELSET-1K8\<^bsub>({}XBOOLE-0K1,Y)\<^esub> Q =FUNCT-1R1 {}XBOOLE-0K1"
   sorry

mtheorem funct_2_th_47:
" for Y be setHIDDENM2 holds  for x be objectHIDDENM1 holds  for f be FunctionFUNCT-2M1-of({TARSKIK1 x},Y) holds Y <>HIDDENR2 {}XBOOLE-0K1 implies f .FUNCT-1K1 x inTARSKIR2 Y"
sorry

mtheorem funct_2_th_48:
" for Y be setHIDDENM2 holds  for x be objectHIDDENM1 holds  for f be FunctionFUNCT-2M1-of({TARSKIK1 x},Y) holds Y <>HIDDENR2 {}XBOOLE-0K1 implies rngRELSET-1K2\<^bsub>(Y)\<^esub> f =XBOOLE-0R4 {TARSKIK1 f .FUNCT-1K1 x }"
sorry

mtheorem funct_2_th_49:
" for P be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for x be objectHIDDENM1 holds  for f be FunctionFUNCT-2M1-of({TARSKIK1 x},Y) holds Y <>HIDDENR2 {}XBOOLE-0K1 implies f .:RELSET-1K7\<^bsub>({TARSKIK1 x},Y)\<^esub> P c=TARSKIR1 {TARSKIK1 f .FUNCT-1K1 x }"
sorry

mtheorem funct_2_th_50:
" for X be setHIDDENM2 holds  for x be objectHIDDENM1 holds  for y be objectHIDDENM1 holds  for f be FunctionFUNCT-2M1-of(X,{TARSKIK1 y}) holds x inHIDDENR3 X implies f .FUNCT-1K1 x =HIDDENR1 y"
sorry

mtheorem funct_2_th_51:
" for X be setHIDDENM2 holds  for y be objectHIDDENM1 holds  for f1 be FunctionFUNCT-2M1-of(X,{TARSKIK1 y}) holds  for f2 be FunctionFUNCT-2M1-of(X,{TARSKIK1 y}) holds f1 =RELSET-1R2\<^bsub>(X,{TARSKIK1 y})\<^esub> f2"
sorry

mtheorem funct_2_th_52:
" for X be setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(X,X) holds domRELSET-1K1\<^bsub>(X)\<^esub> f =XBOOLE-0R4 X"
sorry

mtheorem funct_2_cl_10:
  mlet "X be setHIDDENM2", "Y be setHIDDENM2", "f be quasi-totalFUNCT-2V1\<^bsub>(X,Y)\<^esub>\<bar>PartFuncPARTFUN1M1-of(X,Y)", "g be quasi-totalFUNCT-2V1\<^bsub>(X,X)\<^esub>\<bar>PartFuncPARTFUN1M1-of(X,X)"
"cluster f *PARTFUN1K1\<^bsub>(X,X,X,Y)\<^esub> g as-term-is quasi-totalFUNCT-2V1\<^bsub>(X,Y)\<^esub> for PartFuncPARTFUN1M1-of(X,Y)"
proof
(*coherence*)
  show " for it be PartFuncPARTFUN1M1-of(X,Y) holds it =HIDDENR1 f *PARTFUN1K1\<^bsub>(X,X,X,Y)\<^esub> g implies it be quasi-totalFUNCT-2V1\<^bsub>(X,Y)\<^esub>"
sorry
qed "sorry"

mtheorem funct_2_cl_11:
  mlet "X be setHIDDENM2", "Y be setHIDDENM2", "f be quasi-totalFUNCT-2V1\<^bsub>(Y,Y)\<^esub>\<bar>PartFuncPARTFUN1M1-of(Y,Y)", "g be quasi-totalFUNCT-2V1\<^bsub>(X,Y)\<^esub>\<bar>PartFuncPARTFUN1M1-of(X,Y)"
"cluster f *PARTFUN1K1\<^bsub>(X,Y,Y,Y)\<^esub> g as-term-is quasi-totalFUNCT-2V1\<^bsub>(X,Y)\<^esub> for PartFuncPARTFUN1M1-of(X,Y)"
proof
(*coherence*)
  show " for it be PartFuncPARTFUN1M1-of(X,Y) holds it =HIDDENR1 f *PARTFUN1K1\<^bsub>(X,Y,Y,Y)\<^esub> g implies it be quasi-totalFUNCT-2V1\<^bsub>(X,Y)\<^esub>"
sorry
qed "sorry"

mtheorem funct_2_th_53:
" for X be setHIDDENM2 holds  for f be RelationRELSET-1M1-of(X,X) holds  for g be RelationRELSET-1M1-of(X,X) holds rngRELSET-1K2\<^bsub>(X)\<^esub> f =XBOOLE-0R4 X & rngRELSET-1K2\<^bsub>(X)\<^esub> g =XBOOLE-0R4 X implies rngRELSET-1K2\<^bsub>(X)\<^esub> (g *RELSET-1K4\<^bsub>(X,X,X,X)\<^esub> f) =XBOOLE-0R4 X"
sorry

mtheorem funct_2_th_54:
" for X be setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(X,X) holds  for g be FunctionFUNCT-2M1-of(X,X) holds g *PARTFUN1K1\<^bsub>(X,X,X,X)\<^esub> f =RELSET-1R2\<^bsub>(X,X)\<^esub> f & rngRELSET-1K2\<^bsub>(X)\<^esub> f =XBOOLE-0R4 X implies g =RELSET-1R2\<^bsub>(X,X)\<^esub> idPARTFUN1K6 X"
sorry

mtheorem funct_2_th_55:
" for X be setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(X,X) holds  for g be FunctionFUNCT-2M1-of(X,X) holds f *PARTFUN1K1\<^bsub>(X,X,X,X)\<^esub> g =RELSET-1R2\<^bsub>(X,X)\<^esub> f & f be one-to-oneFUNCT-1V2 implies g =RELSET-1R2\<^bsub>(X,X)\<^esub> idPARTFUN1K6 X"
sorry

mtheorem funct_2_th_56:
" for X be setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(X,X) holds f be one-to-oneFUNCT-1V2 iff ( for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds (x1 inHIDDENR3 X & x2 inHIDDENR3 X) & f .FUNCT-1K1 x1 =XBOOLE-0R4 f .FUNCT-1K1 x2 implies x1 =HIDDENR1 x2)"
sorry

mdef funct_2_def_4 ("bijectiveFUNCT-2V3\<^bsub>'( _ , _ ')\<^esub>" [0,0]70 ) where
  mlet "X be setHIDDENM2", "Y be setHIDDENM2"
"attr bijectiveFUNCT-2V3\<^bsub>(X,Y)\<^esub> for X -definedRELAT-1V4\<bar>Y -valuedRELAT-1V5\<bar>FunctionFUNCT-1M1 means
  (\<lambda>f. f be one-to-oneFUNCT-1V2\<bar>ontoFUNCT-2V2\<^bsub>(Y)\<^esub>)"..

mtheorem funct_2_cl_12:
  mlet "X be setHIDDENM2", "Y be setHIDDENM2"
"cluster bijectiveFUNCT-2V3\<^bsub>(X,Y)\<^esub> also-is one-to-oneFUNCT-1V2\<bar>ontoFUNCT-2V2\<^bsub>(Y)\<^esub> for PartFuncPARTFUN1M1-of(X,Y)"
proof
(*coherence*)
  show " for it be PartFuncPARTFUN1M1-of(X,Y) holds it be bijectiveFUNCT-2V3\<^bsub>(X,Y)\<^esub> implies it be one-to-oneFUNCT-1V2\<bar>ontoFUNCT-2V2\<^bsub>(Y)\<^esub>"
     sorry
qed "sorry"

mtheorem funct_2_cl_13:
  mlet "X be setHIDDENM2", "Y be setHIDDENM2"
"cluster one-to-oneFUNCT-1V2\<bar>ontoFUNCT-2V2\<^bsub>(Y)\<^esub> also-is bijectiveFUNCT-2V3\<^bsub>(X,Y)\<^esub> for PartFuncPARTFUN1M1-of(X,Y)"
proof
(*coherence*)
  show " for it be PartFuncPARTFUN1M1-of(X,Y) holds it be one-to-oneFUNCT-1V2\<bar>ontoFUNCT-2V2\<^bsub>(Y)\<^esub> implies it be bijectiveFUNCT-2V3\<^bsub>(X,Y)\<^esub>"
     sorry
qed "sorry"

mtheorem funct_2_cl_14:
  mlet "X be setHIDDENM2"
"cluster bijectiveFUNCT-2V3\<^bsub>(X,X)\<^esub> for FunctionFUNCT-2M1-of(X,X)"
proof
(*existence*)
  show " ex it be FunctionFUNCT-2M1-of(X,X) st it be bijectiveFUNCT-2V3\<^bsub>(X,X)\<^esub>"
sorry
qed "sorry"

syntax FUNCT_2M2 :: " Set \<Rightarrow> Ty" ("PermutationFUNCT-2M2-of  _ " [70]70)
translations "PermutationFUNCT-2M2-of X" \<rightharpoonup> "bijectiveFUNCT-2V3\<^bsub>(X,X)\<^esub>\<bar>FunctionFUNCT-2M1-of(X,X)"

mtheorem funct_2_th_57:
" for X be setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(X,X) holds f be one-to-oneFUNCT-1V2 & rngRELSET-1K2\<^bsub>(X)\<^esub> f =XBOOLE-0R4 X implies f be PermutationFUNCT-2M2-of X"
sorry

mtheorem funct_2_th_58:
" for X be setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(X,X) holds f be one-to-oneFUNCT-1V2 implies ( for x1 be objectHIDDENM1 holds  for x2 be objectHIDDENM1 holds (x1 inHIDDENR3 X & x2 inHIDDENR3 X) & f .FUNCT-1K1 x1 =XBOOLE-0R4 f .FUNCT-1K1 x2 implies x1 =HIDDENR1 x2)"
  using funct_2_th_56 sorry

mtheorem funct_2_cl_15:
  mlet "X be setHIDDENM2", "f be ontoFUNCT-2V2\<^bsub>(X)\<^esub>\<bar>PartFuncPARTFUN1M1-of(X,X)", "g be ontoFUNCT-2V2\<^bsub>(X)\<^esub>\<bar>PartFuncPARTFUN1M1-of(X,X)"
"cluster f *PARTFUN1K1\<^bsub>(X,X,X,X)\<^esub> g as-term-is ontoFUNCT-2V2\<^bsub>(X)\<^esub> for PartFuncPARTFUN1M1-of(X,X)"
proof
(*coherence*)
  show " for it be PartFuncPARTFUN1M1-of(X,X) holds it =HIDDENR1 f *PARTFUN1K1\<^bsub>(X,X,X,X)\<^esub> g implies it be ontoFUNCT-2V2\<^bsub>(X)\<^esub>"
sorry
qed "sorry"

mtheorem funct_2_cl_16:
  mlet "X be setHIDDENM2", "f be bijectiveFUNCT-2V3\<^bsub>(X,X)\<^esub>\<bar>FunctionFUNCT-2M1-of(X,X)", "g be bijectiveFUNCT-2V3\<^bsub>(X,X)\<^esub>\<bar>FunctionFUNCT-2M1-of(X,X)"
"cluster g *PARTFUN1K1\<^bsub>(X,X,X,X)\<^esub> f as-term-is bijectiveFUNCT-2V3\<^bsub>(X,X)\<^esub> for FunctionFUNCT-2M1-of(X,X)"
proof
(*coherence*)
  show " for it be FunctionFUNCT-2M1-of(X,X) holds it =HIDDENR1 g *PARTFUN1K1\<^bsub>(X,X,X,X)\<^esub> f implies it be bijectiveFUNCT-2V3\<^bsub>(X,X)\<^esub>"
     sorry
qed "sorry"

mtheorem funct_2_cl_17:
  mlet "X be setHIDDENM2"
"cluster reflexiveRELAT-2V1\<bar>totalPARTFUN1V1\<^bsub>(X)\<^esub> also-is bijectiveFUNCT-2V3\<^bsub>(X,X)\<^esub> for FunctionFUNCT-2M1-of(X,X)"
proof
(*coherence*)
  show " for it be FunctionFUNCT-2M1-of(X,X) holds it be reflexiveRELAT-2V1\<bar>totalPARTFUN1V1\<^bsub>(X)\<^esub> implies it be bijectiveFUNCT-2V3\<^bsub>(X,X)\<^esub>"
sorry
qed "sorry"

syntax FUNCT_2K2 :: " Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ \<inverse>FUNCT-2K2\<^bsub>'( _ ')\<^esub>" [228,0]228)
translations "f \<inverse>FUNCT-2K2\<^bsub>(X)\<^esub>" \<rightharpoonup> "f \<inverse>FUNCT-1K4"

mtheorem funct_2_add_1:
  mlet "X be setHIDDENM2", "f be PermutationFUNCT-2M2-of X"
"cluster f \<inverse>FUNCT-1K4 as-term-is PermutationFUNCT-2M2-of X"
proof
(*coherence*)
  show "f \<inverse>FUNCT-1K4 be PermutationFUNCT-2M2-of X"
sorry
qed "sorry"

mtheorem funct_2_th_59:
" for X be setHIDDENM2 holds  for f be PermutationFUNCT-2M2-of X holds  for g be PermutationFUNCT-2M2-of X holds g *PARTFUN1K1\<^bsub>(X,X,X,X)\<^esub> f =RELSET-1R2\<^bsub>(X,X)\<^esub> g implies f =RELSET-1R2\<^bsub>(X,X)\<^esub> idPARTFUN1K6 X"
sorry

mtheorem funct_2_th_60:
" for X be setHIDDENM2 holds  for f be PermutationFUNCT-2M2-of X holds  for g be PermutationFUNCT-2M2-of X holds g *PARTFUN1K1\<^bsub>(X,X,X,X)\<^esub> f =RELSET-1R2\<^bsub>(X,X)\<^esub> idPARTFUN1K6 X implies g =RELSET-1R2\<^bsub>(X,X)\<^esub> f \<inverse>FUNCT-2K2\<^bsub>(X)\<^esub>"
sorry

mtheorem funct_2_th_61:
" for X be setHIDDENM2 holds  for f be PermutationFUNCT-2M2-of X holds f \<inverse>FUNCT-2K2\<^bsub>(X)\<^esub> *PARTFUN1K1\<^bsub>(X,X,X,X)\<^esub> f =RELSET-1R2\<^bsub>(X,X)\<^esub> idPARTFUN1K6 X & f *PARTFUN1K1\<^bsub>(X,X,X,X)\<^esub> f \<inverse>FUNCT-2K2\<^bsub>(X)\<^esub> =RELSET-1R2\<^bsub>(X,X)\<^esub> idPARTFUN1K6 X"
sorry

mtheorem funct_2_th_62:
" for P be setHIDDENM2 holds  for X be setHIDDENM2 holds  for f be PermutationFUNCT-2M2-of X holds P c=TARSKIR1 X implies f .:RELSET-1K7\<^bsub>(X,X)\<^esub> f \<inverse>RELSET-1K8\<^bsub>(X,X)\<^esub> P =XBOOLE-0R4 P & f \<inverse>RELSET-1K8\<^bsub>(X,X)\<^esub> (f .:RELSET-1K7\<^bsub>(X,X)\<^esub> P) =XBOOLE-0R4 P"
sorry

reserve D for " non emptyXBOOLE-0V1\<bar>setHIDDENM2"
mtheorem funct_2_cl_18:
  mlet "X be setHIDDENM2", "D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "Z be setHIDDENM2", "f be FunctionFUNCT-2M1-of(X,D)", "g be FunctionFUNCT-2M1-of(D,Z)"
"cluster g *PARTFUN1K1\<^bsub>(X,D,D,Z)\<^esub> f as-term-is quasi-totalFUNCT-2V1\<^bsub>(X,Z)\<^esub> for PartFuncPARTFUN1M1-of(X,Z)"
proof
(*coherence*)
  show " for it be PartFuncPARTFUN1M1-of(X,Z) holds it =HIDDENR1 g *PARTFUN1K1\<^bsub>(X,D,D,Z)\<^esub> f implies it be quasi-totalFUNCT-2V1\<^bsub>(X,Z)\<^esub>"
    using funct_2_th_13 sorry
qed "sorry"

syntax FUNCT_2K3 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ .FUNCT-2K3\<^bsub>'( _ , _ ')\<^esub>  _ " [200,0,0,200]200)
translations "f .FUNCT-2K3\<^bsub>(C,D)\<^esub> c" \<rightharpoonup> "f .FUNCT-1K1 c"

mtheorem funct_2_add_2:
  mlet "C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "D be setHIDDENM2", "f be FunctionFUNCT-2M1-of(C,D)", "c be ElementSUBSET-1M1-of C"
"cluster f .FUNCT-1K1 c as-term-is ElementSUBSET-1M1-of D"
proof
(*coherence*)
  show "f .FUNCT-1K1 c be ElementSUBSET-1M1-of D"
sorry
qed "sorry"

theorem funct_2_sch_3:
  fixes Cf0 Df0 Pp2 
  assumes
[ty]: "Cf0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
  [ty]: "Df0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
   A1: " for x be ElementSUBSET-1M1-of Cf0 holds  ex y be ElementSUBSET-1M1-of Df0 st Pp2(x,y)"
  shows " ex f be FunctionFUNCT-2M1-of(Cf0,Df0) st  for x be ElementSUBSET-1M1-of Cf0 holds Pp2(x,f .FUNCT-2K3\<^bsub>(Cf0,Df0)\<^esub> x)"
sorry

theorem funct_2_sch_4:
  fixes Cf0 Df0 Ff1 
  assumes
[ty]: "Cf0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
  [ty]: "Df0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
  [ty_func]: "\<And> x1. x1 be ElementSUBSET-1M1-of Cf0 \<Longrightarrow> Ff1(x1) be ElementSUBSET-1M1-of Df0"
  shows " ex f be FunctionFUNCT-2M1-of(Cf0,Df0) st  for x be ElementSUBSET-1M1-of Cf0 holds f .FUNCT-2K3\<^bsub>(Cf0,Df0)\<^esub> x =XBOOLE-0R4 Ff1(x)"
sorry

mtheorem funct_2_th_63:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f1 be FunctionFUNCT-2M1-of(X,Y) holds  for f2 be FunctionFUNCT-2M1-of(X,Y) holds ( for x be ElementSUBSET-1M1-of X holds f1 .FUNCT-1K1 x =XBOOLE-0R4 f2 .FUNCT-1K1 x) implies f1 =RELSET-1R2\<^bsub>(X,Y)\<^esub> f2"
sorry

mtheorem funct_2_th_64:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for P be setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(X,Y) holds  for y be objectHIDDENM1 holds y inHIDDENR3 f .:RELSET-1K7\<^bsub>(X,Y)\<^esub> P implies ( ex x be objectHIDDENM1 st (x inHIDDENR3 X & x inHIDDENR3 P) & y =HIDDENR1 f .FUNCT-1K1 x)"
sorry

mtheorem funct_2_th_65:
" for P be setHIDDENM2 holds  for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(X,Y) holds  for y be objectHIDDENM1 holds y inHIDDENR3 f .:RELSET-1K7\<^bsub>(X,Y)\<^esub> P implies ( ex c be ElementSUBSET-1M1-of X st c inTARSKIR2 P & y =HIDDENR1 f .FUNCT-1K1 c)"
sorry

(*begin*)
mtheorem funct_2_th_66:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be setHIDDENM2 holds f inTARSKIR2 FuncsFUNCT-2K1(X,Y) implies f be FunctionFUNCT-2M1-of(X,Y)"
sorry

theorem funct_2_sch_5:
  fixes Af0 Bf0 Ff1 Gf1 Cp1 
  assumes
[ty]: "Af0 be setHIDDENM2" and
  [ty]: "Bf0 be setHIDDENM2" and
  [ty_func]: "\<And> x1. x1 be objectHIDDENM1 \<Longrightarrow> Ff1(x1) be objectHIDDENM1" and
  [ty_func]: "\<And> x1. x1 be objectHIDDENM1 \<Longrightarrow> Gf1(x1) be objectHIDDENM1" and
   A1: " for x be objectHIDDENM1 holds x inHIDDENR3 Af0 implies (Cp1(x) implies Ff1(x) inHIDDENR3 Bf0) & ( not Cp1(x) implies Gf1(x) inHIDDENR3 Bf0)"
  shows " ex f be FunctionFUNCT-2M1-of(Af0,Bf0) st  for x be objectHIDDENM1 holds x inHIDDENR3 Af0 implies (Cp1(x) implies f .FUNCT-1K1 x =HIDDENR1 Ff1(x)) & ( not Cp1(x) implies f .FUNCT-1K1 x =HIDDENR1 Gf1(x))"
sorry

mtheorem funct_2_th_67:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be PartFuncPARTFUN1M1-of(X,Y) holds domRELSET-1K1\<^bsub>(X)\<^esub> f =XBOOLE-0R4 X implies f be FunctionFUNCT-2M1-of(X,Y)"
sorry

mtheorem funct_2_th_68:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be PartFuncPARTFUN1M1-of(X,Y) holds f be totalPARTFUN1V1\<^bsub>(X)\<^esub> implies f be FunctionFUNCT-2M1-of(X,Y)"
   sorry

mtheorem funct_2_th_69:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be PartFuncPARTFUN1M1-of(X,Y) holds (Y =XBOOLE-0R4 {}XBOOLE-0K1 implies X =XBOOLE-0R4 {}XBOOLE-0K1) & f be FunctionFUNCT-2M1-of(X,Y) implies f be totalPARTFUN1V1\<^bsub>(X)\<^esub>"
   sorry

mtheorem funct_2_th_70:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(X,Y) holds (Y =XBOOLE-0R4 {}XBOOLE-0K1 implies X =XBOOLE-0R4 {}XBOOLE-0K1) implies <:PARTFUN1K3 f,X,Y :> be totalPARTFUN1V1\<^bsub>(X)\<^esub>"
   sorry

mtheorem funct_2_cl_19:
  mlet "X be setHIDDENM2", "f be FunctionFUNCT-2M1-of(X,X)"
"cluster <:PARTFUN1K3 f,X,X :> as-term-is totalPARTFUN1V1\<^bsub>(X)\<^esub>"
proof
(*coherence*)
  show "<:PARTFUN1K3 f,X,X :> be totalPARTFUN1V1\<^bsub>(X)\<^esub>"
     sorry
qed "sorry"

mtheorem funct_2_th_71:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be PartFuncPARTFUN1M1-of(X,Y) holds (Y =XBOOLE-0R4 {}XBOOLE-0K1 implies X =XBOOLE-0R4 {}XBOOLE-0K1) implies ( ex g be FunctionFUNCT-2M1-of(X,Y) st  for x be objectHIDDENM1 holds x inHIDDENR3 domRELSET-1K1\<^bsub>(X)\<^esub> f implies g .FUNCT-1K1 x =XBOOLE-0R4 f .FUNCT-1K1 x)"
sorry

mtheorem funct_2_th_72:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds FuncsFUNCT-2K1(X,Y) c=TARSKIR1 PFuncsPARTFUN1K4(X,Y)"
sorry

mtheorem funct_2_th_73:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(X,Y) holds  for g be FunctionFUNCT-2M1-of(X,Y) holds (Y =XBOOLE-0R4 {}XBOOLE-0K1 implies X =XBOOLE-0R4 {}XBOOLE-0K1) & f toleratesPARTFUN1R1 g implies f =RELSET-1R2\<^bsub>(X,Y)\<^esub> g"
  using partfun1_th_66 sorry

mtheorem funct_2_th_74:
" for X be setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(X,X) holds  for g be FunctionFUNCT-2M1-of(X,X) holds f toleratesPARTFUN1R1 g implies f =RELSET-1R2\<^bsub>(X,X)\<^esub> g"
  using partfun1_th_66 sorry

mtheorem funct_2_th_75:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be PartFuncPARTFUN1M1-of(X,Y) holds  for g be FunctionFUNCT-2M1-of(X,Y) holds (Y =XBOOLE-0R4 {}XBOOLE-0K1 implies X =XBOOLE-0R4 {}XBOOLE-0K1) implies (f toleratesPARTFUN1R1 g iff ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELSET-1K1\<^bsub>(X)\<^esub> f implies f .FUNCT-1K1 x =XBOOLE-0R4 g .FUNCT-1K1 x))"
sorry

mtheorem funct_2_th_76:
" for X be setHIDDENM2 holds  for f be PartFuncPARTFUN1M1-of(X,X) holds  for g be FunctionFUNCT-2M1-of(X,X) holds f toleratesPARTFUN1R1 g iff ( for x be objectHIDDENM1 holds x inHIDDENR3 domRELSET-1K1\<^bsub>(X)\<^esub> f implies f .FUNCT-1K1 x =XBOOLE-0R4 g .FUNCT-1K1 x)"
sorry

mtheorem funct_2_th_77:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be PartFuncPARTFUN1M1-of(X,Y) holds (Y =XBOOLE-0R4 {}XBOOLE-0K1 implies X =XBOOLE-0R4 {}XBOOLE-0K1) implies ( ex g be FunctionFUNCT-2M1-of(X,Y) st f toleratesPARTFUN1R1 g)"
sorry

mtheorem funct_2_th_78:
" for X be setHIDDENM2 holds  for f be PartFuncPARTFUN1M1-of(X,X) holds  for g be PartFuncPARTFUN1M1-of(X,X) holds  for h be FunctionFUNCT-2M1-of(X,X) holds f toleratesPARTFUN1R1 h & g toleratesPARTFUN1R1 h implies f toleratesPARTFUN1R1 g"
  using partfun1_th_67 sorry

mtheorem funct_2_th_79:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be PartFuncPARTFUN1M1-of(X,Y) holds  for g be PartFuncPARTFUN1M1-of(X,Y) holds (Y =XBOOLE-0R4 {}XBOOLE-0K1 implies X =XBOOLE-0R4 {}XBOOLE-0K1) & f toleratesPARTFUN1R1 g implies ( ex h be FunctionFUNCT-2M1-of(X,Y) st f toleratesPARTFUN1R1 h & g toleratesPARTFUN1R1 h)"
sorry

mtheorem funct_2_th_80:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be PartFuncPARTFUN1M1-of(X,Y) holds  for g be FunctionFUNCT-2M1-of(X,Y) holds (Y =XBOOLE-0R4 {}XBOOLE-0K1 implies X =XBOOLE-0R4 {}XBOOLE-0K1) & f toleratesPARTFUN1R1 g implies g inTARSKIR2 TotFuncsPARTFUN1K5\<^bsub>(X,Y)\<^esub> f"
  using partfun1_def_5 sorry

mtheorem funct_2_th_81:
" for X be setHIDDENM2 holds  for f be PartFuncPARTFUN1M1-of(X,X) holds  for g be FunctionFUNCT-2M1-of(X,X) holds f toleratesPARTFUN1R1 g implies g inTARSKIR2 TotFuncsPARTFUN1K5\<^bsub>(X,X)\<^esub> f"
  using partfun1_def_5 sorry

mtheorem funct_2_th_82:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be PartFuncPARTFUN1M1-of(X,Y) holds  for g be setHIDDENM2 holds g inTARSKIR2 TotFuncsPARTFUN1K5\<^bsub>(X,Y)\<^esub> f implies g be FunctionFUNCT-2M1-of(X,Y)"
sorry

mtheorem funct_2_th_83:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be PartFuncPARTFUN1M1-of(X,Y) holds TotFuncsPARTFUN1K5\<^bsub>(X,Y)\<^esub> f c=TARSKIR1 FuncsFUNCT-2K1(X,Y)"
sorry

mtheorem funct_2_th_84:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds TotFuncsPARTFUN1K5\<^bsub>(X,Y)\<^esub> (<:PARTFUN1K3 {}XBOOLE-0K1,X,Y :>) =XBOOLE-0R4 FuncsFUNCT-2K1(X,Y)"
sorry

mtheorem funct_2_th_85:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(X,Y) holds (Y =XBOOLE-0R4 {}XBOOLE-0K1 implies X =XBOOLE-0R4 {}XBOOLE-0K1) implies TotFuncsPARTFUN1K5\<^bsub>(X,Y)\<^esub> (<:PARTFUN1K3 f,X,Y :>) =XBOOLE-0R4 {TARSKIK1 f}"
  using partfun1_th_72 sorry

mtheorem funct_2_th_86:
" for X be setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(X,X) holds TotFuncsPARTFUN1K5\<^bsub>(X,X)\<^esub> (<:PARTFUN1K3 f,X,X :>) =XBOOLE-0R4 {TARSKIK1 f}"
  using partfun1_th_72 sorry

mtheorem funct_2_th_87:
" for X be setHIDDENM2 holds  for y be objectHIDDENM1 holds  for f be PartFuncPARTFUN1M1-of(X,{TARSKIK1 y}) holds  for g be FunctionFUNCT-2M1-of(X,{TARSKIK1 y}) holds TotFuncsPARTFUN1K5\<^bsub>(X,{TARSKIK1 y})\<^esub> f =XBOOLE-0R4 {TARSKIK1 g}"
sorry

mtheorem funct_2_th_88:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be PartFuncPARTFUN1M1-of(X,Y) holds  for g be PartFuncPARTFUN1M1-of(X,Y) holds g c=RELSET-1R1\<^bsub>(X,Y)\<^esub> f implies TotFuncsPARTFUN1K5\<^bsub>(X,Y)\<^esub> f c=TARSKIR1 TotFuncsPARTFUN1K5\<^bsub>(X,Y)\<^esub> g"
sorry

mtheorem funct_2_th_89:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be PartFuncPARTFUN1M1-of(X,Y) holds  for g be PartFuncPARTFUN1M1-of(X,Y) holds domRELSET-1K1\<^bsub>(X)\<^esub> g c=TARSKIR1 domRELSET-1K1\<^bsub>(X)\<^esub> f & TotFuncsPARTFUN1K5\<^bsub>(X,Y)\<^esub> f c=TARSKIR1 TotFuncsPARTFUN1K5\<^bsub>(X,Y)\<^esub> g implies g c=RELSET-1R1\<^bsub>(X,Y)\<^esub> f"
sorry

mtheorem funct_2_th_90:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be PartFuncPARTFUN1M1-of(X,Y) holds  for g be PartFuncPARTFUN1M1-of(X,Y) holds TotFuncsPARTFUN1K5\<^bsub>(X,Y)\<^esub> f c=TARSKIR1 TotFuncsPARTFUN1K5\<^bsub>(X,Y)\<^esub> g & ( for y be objectHIDDENM1 holds Y <>HIDDENR2 {TARSKIK1 y}) implies g c=RELSET-1R1\<^bsub>(X,Y)\<^esub> f"
sorry

mtheorem funct_2_th_91:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for f be PartFuncPARTFUN1M1-of(X,Y) holds  for g be PartFuncPARTFUN1M1-of(X,Y) holds ( for y be objectHIDDENM1 holds Y <>HIDDENR2 {TARSKIK1 y}) & TotFuncsPARTFUN1K5\<^bsub>(X,Y)\<^esub> f =XBOOLE-0R4 TotFuncsPARTFUN1K5\<^bsub>(X,Y)\<^esub> g implies f =RELSET-1R2\<^bsub>(X,Y)\<^esub> g"
  using funct_2_th_90 sorry

mtheorem funct_2_cl_20:
  mlet "A be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "B be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster note-that  non emptyXBOOLE-0V1 for FunctionFUNCT-2M1-of(A,B)"
proof
(*coherence*)
  show " for it be FunctionFUNCT-2M1-of(A,B) holds it be  non emptyXBOOLE-0V1"
    using funct_2_def_1 relat_1_th_38 sorry
qed "sorry"

(*begin*)
theorem funct_2_sch_6:
  fixes Df0 Rf0 Af0 Bf0 Ff1 
  assumes
[ty]: "Df0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
  [ty]: "Rf0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
  [ty]: "Af0 be ElementSUBSET-1M1-of Df0" and
  [ty]: "Bf0 be ElementSUBSET-1M1-of Rf0" and
  [ty_func]: "\<And> x1. x1 be objectHIDDENM1 \<Longrightarrow> Ff1(x1) be ElementSUBSET-1M1-of Rf0"
  shows " ex f be FunctionFUNCT-2M1-of(Df0,Rf0) st f .FUNCT-2K3\<^bsub>(Df0,Rf0)\<^esub> Af0 =XBOOLE-0R4 Bf0 & ( for x be ElementSUBSET-1M1-of Df0 holds x <>HIDDENR2 Af0 implies f .FUNCT-2K3\<^bsub>(Df0,Rf0)\<^esub> x =XBOOLE-0R4 Ff1(x))"
sorry

theorem funct_2_sch_7:
  fixes Df0 Rf0 A1f0 A2f0 B1f0 B2f0 Ff1 
  assumes
[ty]: "Df0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
  [ty]: "Rf0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
  [ty]: "A1f0 be ElementSUBSET-1M1-of Df0" and
  [ty]: "A2f0 be ElementSUBSET-1M1-of Df0" and
  [ty]: "B1f0 be ElementSUBSET-1M1-of Rf0" and
  [ty]: "B2f0 be ElementSUBSET-1M1-of Rf0" and
  [ty_func]: "\<And> x1. x1 be objectHIDDENM1 \<Longrightarrow> Ff1(x1) be ElementSUBSET-1M1-of Rf0" and
   A1: "A1f0 <>HIDDENR2 A2f0"
  shows " ex f be FunctionFUNCT-2M1-of(Df0,Rf0) st (f .FUNCT-2K3\<^bsub>(Df0,Rf0)\<^esub> A1f0 =XBOOLE-0R4 B1f0 & f .FUNCT-2K3\<^bsub>(Df0,Rf0)\<^esub> A2f0 =XBOOLE-0R4 B2f0) & ( for x be ElementSUBSET-1M1-of Df0 holds x <>HIDDENR2 A1f0 & x <>HIDDENR2 A2f0 implies f .FUNCT-2K3\<^bsub>(Df0,Rf0)\<^esub> x =XBOOLE-0R4 Ff1(x))"
sorry

mtheorem funct_2_th_92:
" for A be setHIDDENM2 holds  for B be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds f inTARSKIR2 FuncsFUNCT-2K1(A,B) implies domRELAT-1K1 f =XBOOLE-0R4 A & rngFUNCT-1K2 f c=TARSKIR1 B"
sorry

theorem funct_2_sch_8:
  fixes Xf0 Yf0 Ff1 
  assumes
[ty]: "Xf0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
  [ty]: "Yf0 be setHIDDENM2" and
  [ty_func]: "\<And> x1. x1 be objectHIDDENM1 \<Longrightarrow> Ff1(x1) be objectHIDDENM1" and
   A1: " for x be ElementSUBSET-1M1-of Xf0 holds Ff1(x) inHIDDENR3 Yf0"
  shows " ex f be FunctionFUNCT-2M1-of(Xf0,Yf0) st  for x be ElementSUBSET-1M1-of Xf0 holds f .FUNCT-2K3\<^bsub>(Xf0,Yf0)\<^esub> x =HIDDENR1 Ff1(x)"
sorry

theorem funct_2_sch_9:
  fixes Xf0 Yf0 Ff1 
  assumes
[ty]: "Xf0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
  [ty]: "Yf0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
  [ty_func]: "\<And> x1. x1 be objectHIDDENM1 \<Longrightarrow> Ff1(x1) be objectHIDDENM1" and
   A1: " for x be ElementSUBSET-1M1-of Xf0 holds Ff1(x) be ElementSUBSET-1M1-of Yf0"
  shows " ex f be FunctionFUNCT-2M1-of(Xf0,Yf0) st  for x be ElementSUBSET-1M1-of Xf0 holds f .FUNCT-2K3\<^bsub>(Xf0,Yf0)\<^esub> x =HIDDENR1 Ff1(x)"
sorry

syntax FUNCT_2K4 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" ("pr1FUNCT-2K4\<^bsub>'( _ , _ , _ ')\<^esub>  _ " [0,0,0,228]228)
translations "pr1FUNCT-2K4\<^bsub>(A,B,C)\<^esub> f" \<rightharpoonup> "pr1MCART-1K11 f"

mtheorem funct_2_def_5:
  mlet "A be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "B be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "f be FunctionFUNCT-2M1-of(A,[:ZFMISC-1K2 B,C :])"
"redefine func pr1FUNCT-2K4\<^bsub>(A,B,C)\<^esub> f \<rightarrow> FunctionFUNCT-2M1-of(A,B) means
  \<lambda>it.  for x be ElementSUBSET-1M1-of A holds it .FUNCT-2K3\<^bsub>(A,B)\<^esub> x =HIDDENR1 (f .FUNCT-2K3\<^bsub>(A,[:ZFMISC-1K2 B,C :])\<^esub> x)`1XTUPLE-0K1"
proof
(*compatibility*)
  show " for it be FunctionFUNCT-2M1-of(A,B) holds it =HIDDENR1 pr1FUNCT-2K4\<^bsub>(A,B,C)\<^esub> f iff ( for x be ElementSUBSET-1M1-of A holds it .FUNCT-2K3\<^bsub>(A,B)\<^esub> x =HIDDENR1 (f .FUNCT-2K3\<^bsub>(A,[:ZFMISC-1K2 B,C :])\<^esub> x)`1XTUPLE-0K1)"
sorry
qed "sorry"

mtheorem funct_2_add_3:
  mlet "A be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "B be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "f be FunctionFUNCT-2M1-of(A,[:ZFMISC-1K2 B,C :])"
"cluster pr1MCART-1K11 f as-term-is FunctionFUNCT-2M1-of(A,B)"
proof
(*coherence*)
  show "pr1MCART-1K11 f be FunctionFUNCT-2M1-of(A,B)"
sorry
qed "sorry"

syntax FUNCT_2K5 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" ("pr2FUNCT-2K5\<^bsub>'( _ , _ , _ ')\<^esub>  _ " [0,0,0,228]228)
translations "pr2FUNCT-2K5\<^bsub>(A,B,C)\<^esub> f" \<rightharpoonup> "pr2MCART-1K12 f"

mtheorem funct_2_def_6:
  mlet "A be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "B be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "f be FunctionFUNCT-2M1-of(A,[:ZFMISC-1K2 B,C :])"
"redefine func pr2FUNCT-2K5\<^bsub>(A,B,C)\<^esub> f \<rightarrow> FunctionFUNCT-2M1-of(A,C) means
  \<lambda>it.  for x be ElementSUBSET-1M1-of A holds it .FUNCT-2K3\<^bsub>(A,C)\<^esub> x =HIDDENR1 (f .FUNCT-2K3\<^bsub>(A,[:ZFMISC-1K2 B,C :])\<^esub> x)`2XTUPLE-0K2"
proof
(*compatibility*)
  show " for it be FunctionFUNCT-2M1-of(A,C) holds it =HIDDENR1 pr2FUNCT-2K5\<^bsub>(A,B,C)\<^esub> f iff ( for x be ElementSUBSET-1M1-of A holds it .FUNCT-2K3\<^bsub>(A,C)\<^esub> x =HIDDENR1 (f .FUNCT-2K3\<^bsub>(A,[:ZFMISC-1K2 B,C :])\<^esub> x)`2XTUPLE-0K2)"
sorry
qed "sorry"

mtheorem funct_2_add_4:
  mlet "A be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "B be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "f be FunctionFUNCT-2M1-of(A,[:ZFMISC-1K2 B,C :])"
"cluster pr2MCART-1K12 f as-term-is FunctionFUNCT-2M1-of(A,C)"
proof
(*coherence*)
  show "pr2MCART-1K12 f be FunctionFUNCT-2M1-of(A,C)"
sorry
qed "sorry"

syntax FUNCT_2R1 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> o" (" _ =FUNCT-2R1\<^bsub>'( _ , _ , _ , _ ')\<^esub>  _ " [50,0,0,0,0,50]50)
translations "f1 =FUNCT-2R1\<^bsub>(A1,B1,A2,B2)\<^esub> f2" \<rightharpoonup> "f1 =HIDDENR1 f2"

mtheorem funct_2_def_7:
  mlet "A1 be setHIDDENM2", "B1 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "A2 be setHIDDENM2", "B2 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "f1 be FunctionFUNCT-2M1-of(A1,B1)", "f2 be FunctionFUNCT-2M1-of(A2,B2)"
"redefine pred f1 =FUNCT-2R1\<^bsub>(A1,B1,A2,B2)\<^esub> f2 means
  A1 =XBOOLE-0R4 A2 & ( for a be ElementSUBSET-1M1-of A1 holds f1 .FUNCT-1K1 a =XBOOLE-0R4 f2 .FUNCT-1K1 a)"
proof
(*compatibility*)
  show "f1 =FUNCT-2R1\<^bsub>(A1,B1,A2,B2)\<^esub> f2 iff A1 =XBOOLE-0R4 A2 & ( for a be ElementSUBSET-1M1-of A1 holds f1 .FUNCT-1K1 a =XBOOLE-0R4 f2 .FUNCT-1K1 a)"
sorry
qed "sorry"

syntax FUNCT_2R2 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> o" (" _ =FUNCT-2R2\<^bsub>'( _ , _ ')\<^esub>  _ " [50,0,0,50]50)
translations "f1 =FUNCT-2R2\<^bsub>(A,B)\<^esub> f2" \<rightharpoonup> "f1 =HIDDENR1 f2"

mtheorem funct_2_def_8:
  mlet "A be setHIDDENM2", "B be setHIDDENM2", "f1 be FunctionFUNCT-2M1-of(A,B)", "f2 be FunctionFUNCT-2M1-of(A,B)"
"redefine pred f1 =FUNCT-2R2\<^bsub>(A,B)\<^esub> f2 means
   for a be ElementSUBSET-1M1-of A holds f1 .FUNCT-1K1 a =XBOOLE-0R4 f2 .FUNCT-1K1 a"
proof
(*compatibility*)
  show "f1 =FUNCT-2R2\<^bsub>(A,B)\<^esub> f2 iff ( for a be ElementSUBSET-1M1-of A holds f1 .FUNCT-1K1 a =XBOOLE-0R4 f2 .FUNCT-1K1 a)"
    using funct_2_th_63 sorry
qed "sorry"

mtheorem funct_2_th_93:
" for N be setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(N,boolSETFAM-1K9 N) holds  ex R be RelationRELSET-1M2-of N st  for i be setHIDDENM2 holds i inTARSKIR2 N implies ImRELAT-1K12(R,i) =XBOOLE-0R4 f .FUNCT-1K1 i"
sorry

mtheorem funct_2_th_94:
" for X be setHIDDENM2 holds  for A be SubsetSUBSET-1M2-of X holds (idPARTFUN1K6 X)\<inverse>RELSET-1K8\<^bsub>(X,X)\<^esub> A =XBOOLE-0R4 A"
sorry

reserve A, B for " non emptyXBOOLE-0V1\<bar>setHIDDENM2"
mtheorem funct_2_th_95:
" for A be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for B be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(A,B) holds  for A0 be SubsetSUBSET-1M2-of A holds  for B0 be SubsetSUBSET-1M2-of B holds f .:RELSET-1K7\<^bsub>(A,B)\<^esub> A0 c=TARSKIR1 B0 iff A0 c=TARSKIR1 f \<inverse>RELSET-1K8\<^bsub>(A,B)\<^esub> B0"
sorry

mtheorem funct_2_th_96:
" for A be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for B be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(A,B) holds  for A0 be  non emptyXBOOLE-0V1\<bar>SubsetSUBSET-1M2-of A holds  for f0 be FunctionFUNCT-2M1-of(A0,B) holds ( for c be ElementSUBSET-1M1-of A holds c inTARSKIR2 A0 implies f .FUNCT-2K3\<^bsub>(A,B)\<^esub> c =XBOOLE-0R4 f0 .FUNCT-1K1 c) implies f |PARTFUN1K2\<^bsub>(A,B)\<^esub> A0 =FUNCT-1R1 f0"
sorry

mtheorem funct_2_th_97:
" for f be FunctionFUNCT-1M1 holds  for A0 be setHIDDENM2 holds  for C be setHIDDENM2 holds C c=TARSKIR1 A0 implies f .:FUNCT-1K5 C =XBOOLE-0R4 (f |RELAT-1K8 A0).:FUNCT-1K5 C"
sorry

mtheorem funct_2_th_98:
" for f be FunctionFUNCT-1M1 holds  for A0 be setHIDDENM2 holds  for D be setHIDDENM2 holds f \<inverse>FUNCT-1K6 D c=TARSKIR1 A0 implies f \<inverse>FUNCT-1K6 D =XBOOLE-0R4 (f |RELAT-1K8 A0)\<inverse>FUNCT-1K6 D"
sorry

theorem funct_2_sch_10:
  fixes Af0 Bf0 Ff1 
  assumes
[ty]: "Af0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
  [ty]: "Bf0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
  [ty_func]: "\<And> x1. x1 be objectHIDDENM1 \<Longrightarrow> Ff1(x1) be setHIDDENM2" and
   A1: " for a be ElementSUBSET-1M1-of Af0 holds Bf0 meetsXBOOLE-0R5 Ff1(a)"
  shows " ex t be FunctionFUNCT-2M1-of(Af0,Bf0) st  for a be ElementSUBSET-1M1-of Af0 holds t .FUNCT-2K3\<^bsub>(Af0,Bf0)\<^esub> a inTARSKIR2 Ff1(a)"
sorry

mtheorem funct_2_th_99:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for p be FunctionFUNCT-2M1-of(X,D) holds  for i be ElementSUBSET-1M1-of X holds p /.PARTFUN1K7\<^bsub>(D)\<^esub> i =XBOOLE-0R4 p .FUNCT-2K3\<^bsub>(X,D)\<^esub> i"
sorry

mtheorem funct_2_ident_1:
  mlet "X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "p be FunctionFUNCT-2M1-of(X,D)", "i be ElementSUBSET-1M1-of X"
"identify p /.PARTFUN1K7\<^bsub>(D)\<^esub> i with p .FUNCT-2K3\<^bsub>(X,D)\<^esub> i"
proof
(*compatibility*)
  show "p /.PARTFUN1K7\<^bsub>(D)\<^esub> i =HIDDENR1 p .FUNCT-2K3\<^bsub>(X,D)\<^esub> i"
    using funct_2_th_99 sorry
qed "sorry"

mtheorem funct_2_th_100:
" for S be setHIDDENM2 holds  for X be setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(S,X) holds  for A be SubsetSUBSET-1M2-of X holds (X =XBOOLE-0R4 {}XBOOLE-0K1 implies S =XBOOLE-0R4 {}XBOOLE-0K1) implies (f \<inverse>RELSET-1K8\<^bsub>(S,X)\<^esub> A)`SUBSET-1K3\<^bsub>(S)\<^esub> =XBOOLE-0R4 f \<inverse>RELSET-1K8\<^bsub>(S,X)\<^esub> A `SUBSET-1K3\<^bsub>(X)\<^esub>"
sorry

mtheorem funct_2_th_101:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for Z be setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(X,D) holds Y c=TARSKIR1 X & f .:RELSET-1K7\<^bsub>(X,D)\<^esub> Y c=TARSKIR1 Z implies f |PARTFUN1K2\<^bsub>(X,D)\<^esub> Y be FunctionFUNCT-2M1-of(Y,Z)"
sorry

mdef funct_2_def_9 (" _ \<inverse>FUNCT-2K6\<^bsub>'( _ , _ ')\<^esub>  _ " [228,0,0,228]228 ) where
  mlet "T be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "S be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "f be FunctionFUNCT-2M1-of(T,S)", "G be Subset-FamilySETFAM-1M1-of S"
"func f \<inverse>FUNCT-2K6\<^bsub>(T,S)\<^esub> G \<rightarrow> Subset-FamilySETFAM-1M1-of T means
  \<lambda>it.  for A be SubsetSUBSET-1M2-of T holds A inTARSKIR2 it iff ( ex B be SubsetSUBSET-1M2-of S st B inTARSKIR2 G & A =XBOOLE-0R4 f \<inverse>RELSET-1K8\<^bsub>(T,S)\<^esub> B)"
proof-
  (*existence*)
    show " ex it be Subset-FamilySETFAM-1M1-of T st  for A be SubsetSUBSET-1M2-of T holds A inTARSKIR2 it iff ( ex B be SubsetSUBSET-1M2-of S st B inTARSKIR2 G & A =XBOOLE-0R4 f \<inverse>RELSET-1K8\<^bsub>(T,S)\<^esub> B)"
sorry
  (*uniqueness*)
    show " for it1 be Subset-FamilySETFAM-1M1-of T holds  for it2 be Subset-FamilySETFAM-1M1-of T holds ( for A be SubsetSUBSET-1M2-of T holds A inTARSKIR2 it1 iff ( ex B be SubsetSUBSET-1M2-of S st B inTARSKIR2 G & A =XBOOLE-0R4 f \<inverse>RELSET-1K8\<^bsub>(T,S)\<^esub> B)) & ( for A be SubsetSUBSET-1M2-of T holds A inTARSKIR2 it2 iff ( ex B be SubsetSUBSET-1M2-of S st B inTARSKIR2 G & A =XBOOLE-0R4 f \<inverse>RELSET-1K8\<^bsub>(T,S)\<^esub> B)) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mtheorem funct_2_th_102:
" for T be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for S be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(T,S) holds  for A be Subset-FamilySETFAM-1M1-of S holds  for B be Subset-FamilySETFAM-1M1-of S holds A c=TARSKIR1 B implies f \<inverse>FUNCT-2K6\<^bsub>(T,S)\<^esub> A c=TARSKIR1 f \<inverse>FUNCT-2K6\<^bsub>(T,S)\<^esub> B"
sorry

mdef funct_2_def_10 (" _ .:FUNCT-2K7\<^bsub>'( _ , _ ')\<^esub>  _ " [200,0,0,200]200 ) where
  mlet "T be setHIDDENM2", "S be setHIDDENM2", "f be FunctionFUNCT-2M1-of(T,S)", "G be Subset-FamilySETFAM-1M1-of T"
"func f .:FUNCT-2K7\<^bsub>(T,S)\<^esub> G \<rightarrow> Subset-FamilySETFAM-1M1-of S means
  \<lambda>it.  for A be SubsetSUBSET-1M2-of S holds A inTARSKIR2 it iff ( ex B be SubsetSUBSET-1M2-of T st B inTARSKIR2 G & A =XBOOLE-0R4 f .:RELSET-1K7\<^bsub>(T,S)\<^esub> B)"
proof-
  (*existence*)
    show " ex it be Subset-FamilySETFAM-1M1-of S st  for A be SubsetSUBSET-1M2-of S holds A inTARSKIR2 it iff ( ex B be SubsetSUBSET-1M2-of T st B inTARSKIR2 G & A =XBOOLE-0R4 f .:RELSET-1K7\<^bsub>(T,S)\<^esub> B)"
sorry
  (*uniqueness*)
    show " for it1 be Subset-FamilySETFAM-1M1-of S holds  for it2 be Subset-FamilySETFAM-1M1-of S holds ( for A be SubsetSUBSET-1M2-of S holds A inTARSKIR2 it1 iff ( ex B be SubsetSUBSET-1M2-of T st B inTARSKIR2 G & A =XBOOLE-0R4 f .:RELSET-1K7\<^bsub>(T,S)\<^esub> B)) & ( for A be SubsetSUBSET-1M2-of S holds A inTARSKIR2 it2 iff ( ex B be SubsetSUBSET-1M2-of T st B inTARSKIR2 G & A =XBOOLE-0R4 f .:RELSET-1K7\<^bsub>(T,S)\<^esub> B)) implies it1 =HIDDENR1 it2"
sorry
qed "sorry"

mtheorem funct_2_th_103:
" for T be setHIDDENM2 holds  for S be setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(T,S) holds  for A be Subset-FamilySETFAM-1M1-of T holds  for B be Subset-FamilySETFAM-1M1-of T holds A c=TARSKIR1 B implies f .:FUNCT-2K7\<^bsub>(T,S)\<^esub> A c=TARSKIR1 f .:FUNCT-2K7\<^bsub>(T,S)\<^esub> B"
sorry

mtheorem funct_2_th_104:
" for T be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for S be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(T,S) holds  for B be Subset-FamilySETFAM-1M1-of S holds  for P be SubsetSUBSET-1M2-of S holds f .:FUNCT-2K7\<^bsub>(T,S)\<^esub> f \<inverse>FUNCT-2K6\<^bsub>(T,S)\<^esub> B be CoverSETFAM-1M2-of P implies B be CoverSETFAM-1M2-of P"
sorry

mtheorem funct_2_th_105:
" for T be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for S be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(T,S) holds  for B be Subset-FamilySETFAM-1M1-of T holds  for P be SubsetSUBSET-1M2-of T holds B be CoverSETFAM-1M2-of P implies f \<inverse>FUNCT-2K6\<^bsub>(T,S)\<^esub> (f .:FUNCT-2K7\<^bsub>(T,S)\<^esub> B) be CoverSETFAM-1M2-of P"
sorry

mtheorem funct_2_th_106:
" for T be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for S be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(T,S) holds  for Q be Subset-FamilySETFAM-1M1-of S holds unionSETFAM-1K5\<^bsub>(S)\<^esub> (f .:FUNCT-2K7\<^bsub>(T,S)\<^esub> f \<inverse>FUNCT-2K6\<^bsub>(T,S)\<^esub> Q) c=TARSKIR1 unionSETFAM-1K5\<^bsub>(S)\<^esub> Q"
sorry

mtheorem funct_2_th_107:
" for T be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for S be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(T,S) holds  for P be Subset-FamilySETFAM-1M1-of T holds unionSETFAM-1K5\<^bsub>(T)\<^esub> P c=TARSKIR1 unionSETFAM-1K5\<^bsub>(T)\<^esub> (f \<inverse>FUNCT-2K6\<^bsub>(T,S)\<^esub> (f .:FUNCT-2K7\<^bsub>(T,S)\<^esub> P))"
sorry

mdef funct_2_def_11 (" _ '/*FUNCT-2K8\<^bsub>'( _ , _ , _ ')\<^esub>  _ " [228,0,0,0,228]228 ) where
  mlet "X be setHIDDENM2", "Z be setHIDDENM2", "Y be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "f be FunctionFUNCT-2M1-of(X,Y)", "p be Z -valuedRELAT-1V5\<bar>FunctionFUNCT-1M1"
"assume rngRELSET-1K2\<^bsub>(Y)\<^esub> f c=TARSKIR1 domRELAT-1K1 p func p /*FUNCT-2K8\<^bsub>(X,Z,Y)\<^esub> f \<rightarrow> FunctionFUNCT-2M1-of(X,Z) equals
  p *FUNCT-1K3 f"
proof-
  (*coherence*)
    show "rngRELSET-1K2\<^bsub>(Y)\<^esub> f c=TARSKIR1 domRELAT-1K1 p implies p *FUNCT-1K3 f be FunctionFUNCT-2M1-of(X,Z)"
sorry
qed "sorry"

reserve Y for " non emptyXBOOLE-0V1\<bar>setHIDDENM2"
reserve f for "FunctionFUNCT-2M1-of(X,Y)"
reserve p for "PartFuncPARTFUN1M1-of(Y,Z)"
reserve x for "ElementSUBSET-1M1-of X"
mtheorem funct_2_th_108:
" for X be setHIDDENM2 holds  for Z be setHIDDENM2 holds  for Y be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(X,Y) holds  for p be PartFuncPARTFUN1M1-of(Y,Z) holds  for x be ElementSUBSET-1M1-of X holds X <>HIDDENR2 {}XBOOLE-0K1 & rngRELSET-1K2\<^bsub>(Y)\<^esub> f c=TARSKIR1 domRELSET-1K1\<^bsub>(Y)\<^esub> p implies p /*FUNCT-2K8\<^bsub>(X,Z,Y)\<^esub> f .FUNCT-1K1 x =XBOOLE-0R4 p .FUNCT-1K1 (f .FUNCT-1K1 x)"
sorry

mtheorem funct_2_th_109:
" for X be setHIDDENM2 holds  for Z be setHIDDENM2 holds  for Y be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(X,Y) holds  for p be PartFuncPARTFUN1M1-of(Y,Z) holds  for x be ElementSUBSET-1M1-of X holds X <>HIDDENR2 {}XBOOLE-0K1 & rngRELSET-1K2\<^bsub>(Y)\<^esub> f c=TARSKIR1 domRELSET-1K1\<^bsub>(Y)\<^esub> p implies p /*FUNCT-2K8\<^bsub>(X,Z,Y)\<^esub> f .FUNCT-1K1 x =XBOOLE-0R4 p /.PARTFUN1K7\<^bsub>(Z)\<^esub> (f .FUNCT-1K1 x)"
sorry

reserve g for "FunctionFUNCT-2M1-of(X,X)"
mtheorem funct_2_th_110:
" for X be setHIDDENM2 holds  for Z be setHIDDENM2 holds  for Y be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(X,Y) holds  for p be PartFuncPARTFUN1M1-of(Y,Z) holds  for g be FunctionFUNCT-2M1-of(X,X) holds rngRELSET-1K2\<^bsub>(Y)\<^esub> f c=TARSKIR1 domRELSET-1K1\<^bsub>(Y)\<^esub> p implies p /*FUNCT-2K8\<^bsub>(X,Z,Y)\<^esub> f *PARTFUN1K1\<^bsub>(X,X,X,Z)\<^esub> g =FUNCT-2R2\<^bsub>(X,Z)\<^esub> p /*FUNCT-2K8\<^bsub>(X,Z,Y)\<^esub> (f *PARTFUN1K1\<^bsub>(X,X,X,Y)\<^esub> g)"
sorry

mtheorem funct_2_th_111:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for Y be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(X,Y) holds f be constantFUNCT-1V5 iff ( ex y be ElementSUBSET-1M1-of Y st rngRELSET-1K2\<^bsub>(Y)\<^esub> f =XBOOLE-0R4 {TARSKIK1 y})"
sorry

mtheorem funct_2_th_112:
" for A be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for B be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for x be ElementSUBSET-1M1-of A holds  for f be FunctionFUNCT-2M1-of(A,B) holds f .FUNCT-2K3\<^bsub>(A,B)\<^esub> x inTARSKIR2 rngRELSET-1K2\<^bsub>(B)\<^esub> f"
sorry

mtheorem funct_2_th_113:
" for y be objectHIDDENM1 holds  for A be setHIDDENM2 holds  for B be setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(A,B) holds y inHIDDENR3 rngRELSET-1K2\<^bsub>(B)\<^esub> f implies ( ex x be ElementSUBSET-1M1-of A st y =HIDDENR1 f .FUNCT-1K1 x)"
sorry

mtheorem funct_2_th_114:
" for Z be setHIDDENM2 holds  for A be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for B be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(A,B) holds ( for x be ElementSUBSET-1M1-of A holds f .FUNCT-2K3\<^bsub>(A,B)\<^esub> x inTARSKIR2 Z) implies rngRELSET-1K2\<^bsub>(B)\<^esub> f c=TARSKIR1 Z"
sorry

reserve X, Y for " non emptyXBOOLE-0V1\<bar>setHIDDENM2"
reserve Z, S, T for "setHIDDENM2"
reserve f for "FunctionFUNCT-2M1-of(X,Y)"
reserve g for "PartFuncPARTFUN1M1-of(Y,Z)"
reserve x for "ElementSUBSET-1M1-of X"
mtheorem funct_2_th_115:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for Y be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for Z be setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(X,Y) holds  for g be PartFuncPARTFUN1M1-of(Y,Z) holds  for x be ElementSUBSET-1M1-of X holds g be totalPARTFUN1V1\<^bsub>(Y)\<^esub> implies g /*FUNCT-2K8\<^bsub>(X,Z,Y)\<^esub> f .FUNCT-2K3\<^bsub>(X,Z)\<^esub> x =XBOOLE-0R4 g .FUNCT-1K1 (f .FUNCT-2K3\<^bsub>(X,Y)\<^esub> x)"
sorry

mtheorem funct_2_th_116:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for Y be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for Z be setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(X,Y) holds  for g be PartFuncPARTFUN1M1-of(Y,Z) holds  for x be ElementSUBSET-1M1-of X holds g be totalPARTFUN1V1\<^bsub>(Y)\<^esub> implies g /*FUNCT-2K8\<^bsub>(X,Z,Y)\<^esub> f .FUNCT-2K3\<^bsub>(X,Z)\<^esub> x =XBOOLE-0R4 g /.PARTFUN1K7\<^bsub>(Z)\<^esub> (f .FUNCT-2K3\<^bsub>(X,Y)\<^esub> x)"
sorry

mtheorem funct_2_th_117:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for Y be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for Z be setHIDDENM2 holds  for S be setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(X,Y) holds  for g be PartFuncPARTFUN1M1-of(Y,Z) holds rngRELSET-1K2\<^bsub>(Y)\<^esub> f c=TARSKIR1 domRELSET-1K1\<^bsub>(Y)\<^esub> (g |PARTFUN1K2\<^bsub>(Y,Z)\<^esub> S) implies (g |PARTFUN1K2\<^bsub>(Y,Z)\<^esub> S)/*FUNCT-2K8\<^bsub>(X,Z,Y)\<^esub> f =FUNCT-2R2\<^bsub>(X,Z)\<^esub> g /*FUNCT-2K8\<^bsub>(X,Z,Y)\<^esub> f"
sorry

mtheorem funct_2_th_118:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for Y be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for Z be setHIDDENM2 holds  for S be setHIDDENM2 holds  for T be setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(X,Y) holds  for g be PartFuncPARTFUN1M1-of(Y,Z) holds rngRELSET-1K2\<^bsub>(Y)\<^esub> f c=TARSKIR1 domRELSET-1K1\<^bsub>(Y)\<^esub> (g |PARTFUN1K2\<^bsub>(Y,Z)\<^esub> S) & S c=TARSKIR1 T implies (g |PARTFUN1K2\<^bsub>(Y,Z)\<^esub> S)/*FUNCT-2K8\<^bsub>(X,Z,Y)\<^esub> f =FUNCT-2R2\<^bsub>(X,Z)\<^esub> (g |PARTFUN1K2\<^bsub>(Y,Z)\<^esub> T)/*FUNCT-2K8\<^bsub>(X,Z,Y)\<^esub> f"
sorry

mtheorem funct_2_th_119:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for A be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for B be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for H be FunctionFUNCT-2M1-of(D,[:ZFMISC-1K2 A,B :]) holds  for d be ElementSUBSET-1M1-of D holds H .FUNCT-2K3\<^bsub>(D,[:ZFMISC-1K2 A,B :])\<^esub> d =HIDDENR1 [TARSKIK4 pr1FUNCT-2K4\<^bsub>(D,A,B)\<^esub> H .FUNCT-2K3\<^bsub>(D,A)\<^esub> d,pr2FUNCT-2K5\<^bsub>(D,A,B)\<^esub> H .FUNCT-2K3\<^bsub>(D,B)\<^esub> d ]"
sorry

mtheorem funct_2_th_120:
" for A1 be setHIDDENM2 holds  for A2 be setHIDDENM2 holds  for B1 be setHIDDENM2 holds  for B2 be setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(A1,A2) holds  for g be FunctionFUNCT-2M1-of(B1,B2) holds f toleratesPARTFUN1R1 g implies f /\\SUBSET-1K9\<^bsub>([:ZFMISC-1K2 B1,B2 :])\<^esub> g be FunctionFUNCT-2M1-of(A1 /\\XBOOLE-0K3 B1,A2 /\\XBOOLE-0K3 B2)"
sorry

mtheorem funct_2_cl_21:
  mlet "A be setHIDDENM2", "B be setHIDDENM2"
"cluster FuncsFUNCT-2K1(A,B) as-term-is functionalFUNCT-1V6"
proof
(*coherence*)
  show "FuncsFUNCT-2K1(A,B) be functionalFUNCT-1V6"
sorry
qed "sorry"

mdef funct_2_def_12 ("FUNCTION-DOMAINFUNCT-2M3-of'( _ , _ ')" [0,0]70 ) where
  mlet "A be setHIDDENM2", "B be setHIDDENM2"
"mode FUNCTION-DOMAINFUNCT-2M3-of(A,B) \<rightarrow>  non emptyXBOOLE-0V1\<bar>setHIDDENM2 means
  (\<lambda>it.  for x be ElementSUBSET-1M1-of it holds x be FunctionFUNCT-2M1-of(A,B))"
proof-
  (*existence*)
    show " ex it be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 st  for x be ElementSUBSET-1M1-of it holds x be FunctionFUNCT-2M1-of(A,B)"
sorry
qed "sorry"

mtheorem funct_2_cl_22:
  mlet "A be setHIDDENM2", "B be setHIDDENM2"
"cluster note-that functionalFUNCT-1V6 for FUNCTION-DOMAINFUNCT-2M3-of(A,B)"
proof
(*coherence*)
  show " for it be FUNCTION-DOMAINFUNCT-2M3-of(A,B) holds it be functionalFUNCT-1V6"
    using funct_2_def_12 sorry
qed "sorry"

mtheorem funct_2_th_121:
" for P be setHIDDENM2 holds  for Q be setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(P,Q) holds {TARSKIK1 f} be FUNCTION-DOMAINFUNCT-2M3-of(P,Q)"
sorry

mtheorem funct_2_th_122:
" for P be setHIDDENM2 holds  for B be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds FuncsFUNCT-2K1(P,B) be FUNCTION-DOMAINFUNCT-2M3-of(P,B)"
sorry

abbreviation(input) FUNCT_2K9("FuncsFUNCT-2K9'( _ , _ ')" [0,0]228) where
  "FuncsFUNCT-2K9(A,B) \<equiv> FuncsFUNCT-2K1(A,B)"

mtheorem funct_2_add_5:
  mlet "A be setHIDDENM2", "B be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
"cluster FuncsFUNCT-2K1(A,B) as-term-is FUNCTION-DOMAINFUNCT-2M3-of(A,B)"
proof
(*coherence*)
  show "FuncsFUNCT-2K1(A,B) be FUNCTION-DOMAINFUNCT-2M3-of(A,B)"
    using funct_2_th_122 sorry
qed "sorry"

syntax FUNCT_2M4 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Ty" ("ElementFUNCT-2M4\<^bsub>'( _ , _ ')\<^esub>-of  _ " [0,0,70]70)
translations "ElementFUNCT-2M4\<^bsub>(A,B)\<^esub>-of F" \<rightharpoonup> "ElementSUBSET-1M1-of F"

mtheorem funct_2_add_6:
  mlet "A be setHIDDENM2", "B be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "F be FUNCTION-DOMAINFUNCT-2M3-of(A,B)"
"cluster note-that FunctionFUNCT-2M1-of(A,B) for ElementSUBSET-1M1-of F"
proof
(*coherence*)
  show " for it be ElementSUBSET-1M1-of F holds it be FunctionFUNCT-2M1-of(A,B)"
    using funct_2_def_12 sorry
qed "sorry"

mtheorem funct_2_cl_23:
  mlet "I be setHIDDENM2"
"cluster idPARTFUN1K6 I as-term-is totalPARTFUN1V1\<^bsub>(I)\<^esub> for I -definedRELAT-1V4\<bar>FunctionFUNCT-1M1"
proof
(*coherence*)
  show " for it be I -definedRELAT-1V4\<bar>FunctionFUNCT-1M1 holds it =HIDDENR1 idPARTFUN1K6 I implies it be totalPARTFUN1V1\<^bsub>(I)\<^esub>"
     sorry
qed "sorry"

syntax FUNCT_2K10 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ '/.FUNCT-2K10\<^bsub>'( _ , _ ')\<^esub>  _ " [200,0,0,200]200)
translations "F /.FUNCT-2K10\<^bsub>(X,A)\<^esub> x" \<rightharpoonup> "F /.PARTFUN1K7\<^bsub>(A)\<^esub> x"

mtheorem funct_2_def_13:
  mlet "X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "A be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "F be FunctionFUNCT-2M1-of(X,A)", "x be setHIDDENM2"
"assume x inTARSKIR2 X redefine func F /.FUNCT-2K10\<^bsub>(X,A)\<^esub> x \<rightarrow> ElementSUBSET-1M1-of A equals
  F .FUNCT-1K1 x"
proof
(*compatibility*)
  show "x inTARSKIR2 X implies ( for it be ElementSUBSET-1M1-of A holds it =HIDDENR1 F /.FUNCT-2K10\<^bsub>(X,A)\<^esub> x iff it =HIDDENR1 F .FUNCT-1K1 x)"
sorry
qed "sorry"

mtheorem funct_2_th_123:
" for X be setHIDDENM2 holds  for Y be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(X,Y) holds  for g be X -valuedRELAT-1V5\<bar>FunctionFUNCT-1M1 holds domRELAT-1K1 (f *FUNCT-1K3 g) =XBOOLE-0R4 domRELAT-1K1 g"
sorry

mtheorem funct_2_th_124:
" for X be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(X,X) holds ( for x be ElementSUBSET-1M1-of X holds f .FUNCT-2K3\<^bsub>(X,X)\<^esub> x =XBOOLE-0R4 x) implies f =FUNCT-2R2\<^bsub>(X,X)\<^esub> idPARTFUN1K6 X"
   sorry

abbreviation(input) FUNCT_2M5("ActionFUNCT-2M5-of'( _ , _ ')" [0,0]70) where
  "ActionFUNCT-2M5-of(O,E) \<equiv> FunctionFUNCT-2M1-of(O,FuncsFUNCT-2K1(E,E))"

mtheorem funct_2_th_125:
" for x be setHIDDENM2 holds  for A be setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of({TARSKIK1 x},A) holds  for g be FunctionFUNCT-2M1-of({TARSKIK1 x},A) holds f .FUNCT-1K1 x =XBOOLE-0R4 g .FUNCT-1K1 x implies f =FUNCT-2R2\<^bsub>({TARSKIK1 x},A)\<^esub> g"
sorry

mtheorem funct_2_th_126:
" for A be setHIDDENM2 holds idPARTFUN1K6 A inTARSKIR2 FuncsFUNCT-2K1(A,A)"
sorry

mtheorem funct_2_th_127:
"FuncsFUNCT-2K1({}XBOOLE-0K1,{}XBOOLE-0K1) =XBOOLE-0R4 {TARSKIK1 idPARTFUN1K6 ({}XBOOLE-0K1) }"
sorry

mtheorem funct_2_th_128:
" for A be setHIDDENM2 holds  for B be setHIDDENM2 holds  for C be setHIDDENM2 holds  for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds f inTARSKIR2 FuncsFUNCT-2K1(A,B) & g inTARSKIR2 FuncsFUNCT-2K1(B,C) implies g *FUNCT-1K3 f inTARSKIR2 FuncsFUNCT-2K1(A,C)"
sorry

mtheorem funct_2_th_129:
" for A be setHIDDENM2 holds  for B be setHIDDENM2 holds  for C be setHIDDENM2 holds FuncsFUNCT-2K1(A,B) <>HIDDENR2 {}XBOOLE-0K1 & FuncsFUNCT-2K1(B,C) <>HIDDENR2 {}XBOOLE-0K1 implies FuncsFUNCT-2K1(A,C) <>HIDDENR2 {}XBOOLE-0K1"
sorry

mtheorem funct_2_th_130:
" for A be setHIDDENM2 holds {}XBOOLE-0K1 be FunctionFUNCT-2M1-of(A,{}XBOOLE-0K1)"
  using funct_2_def_1 relset_1_th_12 sorry

theorem funct_2_sch_11:
  fixes Xf0 Yf0 Ff1 
  assumes
[ty]: "Xf0 be setHIDDENM2" and
  [ty]: "Yf0 be setHIDDENM2" and
  [ty_func]: "\<And> x1. x1 be objectHIDDENM1 \<Longrightarrow> Ff1(x1) be objectHIDDENM1" and
   A1: " for x be setHIDDENM2 holds x inTARSKIR2 Xf0 implies Ff1(x) inHIDDENR3 Yf0"
  shows " ex f be FunctionFUNCT-2M1-of(Xf0,Yf0) st  for x be setHIDDENM2 holds x inTARSKIR2 Xf0 implies f .FUNCT-1K1 x =HIDDENR1 Ff1(x)"
sorry

end
