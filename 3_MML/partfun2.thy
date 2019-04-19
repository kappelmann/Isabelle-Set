theory partfun2
  imports funcop_1
begin
(*begin*)
reserve x, y, X, Y for "setHIDDENM2"
reserve C, D, E for " non emptyXBOOLE-0V1\<bar>setHIDDENM2"
reserve SC for "SubsetSUBSET-1M2-of C"
reserve SD for "SubsetSUBSET-1M2-of D"
reserve SE for "SubsetSUBSET-1M2-of E"
reserve c, c1, c2 for "ElementSUBSET-1M1-of C"
reserve d, d1, d2 for "ElementSUBSET-1M1-of D"
reserve e for "ElementSUBSET-1M1-of E"
reserve f, f1, g for "PartFuncPARTFUN1M1-of(C,D)"
reserve t for "PartFuncPARTFUN1M1-of(D,C)"
reserve s for "PartFuncPARTFUN1M1-of(D,E)"
reserve h for "PartFuncPARTFUN1M1-of(C,E)"
reserve F for "PartFuncPARTFUN1M1-of(D,D)"
mtheorem partfun2_th_1:
" for C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for f be PartFuncPARTFUN1M1-of(C,D) holds  for g be PartFuncPARTFUN1M1-of(C,D) holds domRELSET-1K1\<^bsub>(C)\<^esub> f =XBOOLE-0R4 domRELSET-1K1\<^bsub>(C)\<^esub> g & ( for c be ElementSUBSET-1M1-of C holds c inTARSKIR2 domRELSET-1K1\<^bsub>(C)\<^esub> f implies f /.PARTFUN1K7\<^bsub>(D)\<^esub> c =XBOOLE-0R4 g /.PARTFUN1K7\<^bsub>(D)\<^esub> c) implies f =RELSET-1R2\<^bsub>(C,D)\<^esub> g"
sorry

mtheorem partfun2_th_2:
" for y be setHIDDENM2 holds  for C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for f be PartFuncPARTFUN1M1-of(C,D) holds y inTARSKIR2 rngRELSET-1K2\<^bsub>(D)\<^esub> f iff ( ex c be ElementSUBSET-1M1-of C st c inTARSKIR2 domRELSET-1K1\<^bsub>(C)\<^esub> f & y =XBOOLE-0R4 f /.PARTFUN1K7\<^bsub>(D)\<^esub> c)"
sorry

mtheorem partfun2_th_3:
" for C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for E be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for f be PartFuncPARTFUN1M1-of(C,D) holds  for s be PartFuncPARTFUN1M1-of(D,E) holds  for h be PartFuncPARTFUN1M1-of(C,E) holds h =RELSET-1R2\<^bsub>(C,E)\<^esub> s *PARTFUN1K1\<^bsub>(C,D,D,E)\<^esub> f iff ( for c be ElementSUBSET-1M1-of C holds c inTARSKIR2 domRELSET-1K1\<^bsub>(C)\<^esub> h iff c inTARSKIR2 domRELSET-1K1\<^bsub>(C)\<^esub> f & f /.PARTFUN1K7\<^bsub>(D)\<^esub> c inTARSKIR2 domRELSET-1K1\<^bsub>(D)\<^esub> s) & ( for c be ElementSUBSET-1M1-of C holds c inTARSKIR2 domRELSET-1K1\<^bsub>(C)\<^esub> h implies h /.PARTFUN1K7\<^bsub>(E)\<^esub> c =XBOOLE-0R4 s /.PARTFUN1K7\<^bsub>(E)\<^esub> (f /.PARTFUN1K7\<^bsub>(D)\<^esub> c))"
sorry

mtheorem partfun2_th_4:
" for C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for E be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for c be ElementSUBSET-1M1-of C holds  for f be PartFuncPARTFUN1M1-of(C,D) holds  for s be PartFuncPARTFUN1M1-of(D,E) holds c inTARSKIR2 domRELSET-1K1\<^bsub>(C)\<^esub> f & f /.PARTFUN1K7\<^bsub>(D)\<^esub> c inTARSKIR2 domRELSET-1K1\<^bsub>(D)\<^esub> s implies (s *PARTFUN1K1\<^bsub>(C,D,D,E)\<^esub> f)/.PARTFUN1K7\<^bsub>(E)\<^esub> c =XBOOLE-0R4 s /.PARTFUN1K7\<^bsub>(E)\<^esub> (f /.PARTFUN1K7\<^bsub>(D)\<^esub> c)"
sorry

mtheorem partfun2_th_5:
" for C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for E be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for c be ElementSUBSET-1M1-of C holds  for f be PartFuncPARTFUN1M1-of(C,D) holds  for s be PartFuncPARTFUN1M1-of(D,E) holds rngRELSET-1K2\<^bsub>(D)\<^esub> f c=TARSKIR1 domRELSET-1K1\<^bsub>(D)\<^esub> s & c inTARSKIR2 domRELSET-1K1\<^bsub>(C)\<^esub> f implies (s *PARTFUN1K1\<^bsub>(C,D,D,E)\<^esub> f)/.PARTFUN1K7\<^bsub>(E)\<^esub> c =XBOOLE-0R4 s /.PARTFUN1K7\<^bsub>(E)\<^esub> (f /.PARTFUN1K7\<^bsub>(D)\<^esub> c)"
sorry

syntax PARTFUN2K1 :: " Set \<Rightarrow>  Set \<Rightarrow> Set" ("idPARTFUN2K1\<^bsub>'( _ ')\<^esub>  _ " [0,228]228)
translations "idPARTFUN2K1\<^bsub>(D)\<^esub> SD" \<rightharpoonup> "idRELAT-1K7 SD"

mtheorem partfun2_add_1:
  mlet "D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "SD be SubsetSUBSET-1M2-of D"
"cluster idRELAT-1K7 SD as-term-is PartFuncPARTFUN1M1-of(D,D)"
proof
(*coherence*)
  show "idRELAT-1K7 SD be PartFuncPARTFUN1M1-of(D,D)"
sorry
qed "sorry"

mtheorem partfun2_th_6:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for SD be SubsetSUBSET-1M2-of D holds  for F be PartFuncPARTFUN1M1-of(D,D) holds F =RELSET-1R2\<^bsub>(D,D)\<^esub> idPARTFUN2K1\<^bsub>(D)\<^esub> SD iff domRELSET-1K1\<^bsub>(D)\<^esub> F =XBOOLE-0R4 SD & ( for d be ElementSUBSET-1M1-of D holds d inTARSKIR2 SD implies F /.PARTFUN1K7\<^bsub>(D)\<^esub> d =XBOOLE-0R4 d)"
sorry

mtheorem partfun2_th_7:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for SD be SubsetSUBSET-1M2-of D holds  for d be ElementSUBSET-1M1-of D holds  for F be PartFuncPARTFUN1M1-of(D,D) holds d inTARSKIR2 domRELSET-1K1\<^bsub>(D)\<^esub> F /\\SUBSET-1K9\<^bsub>(D)\<^esub> SD implies F /.PARTFUN1K7\<^bsub>(D)\<^esub> d =XBOOLE-0R4 (F *PARTFUN1K1\<^bsub>(D,D,D,D)\<^esub> idPARTFUN2K1\<^bsub>(D)\<^esub> SD)/.PARTFUN1K7\<^bsub>(D)\<^esub> d"
sorry

mtheorem partfun2_th_8:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for SD be SubsetSUBSET-1M2-of D holds  for d be ElementSUBSET-1M1-of D holds  for F be PartFuncPARTFUN1M1-of(D,D) holds d inTARSKIR2 domRELSET-1K1\<^bsub>(D)\<^esub> (idPARTFUN2K1\<^bsub>(D)\<^esub> SD *PARTFUN1K1\<^bsub>(D,D,D,D)\<^esub> F) iff d inTARSKIR2 domRELSET-1K1\<^bsub>(D)\<^esub> F & F /.PARTFUN1K7\<^bsub>(D)\<^esub> d inTARSKIR2 SD"
sorry

mtheorem partfun2_th_9:
" for C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for f be PartFuncPARTFUN1M1-of(C,D) holds ( for c1 be ElementSUBSET-1M1-of C holds  for c2 be ElementSUBSET-1M1-of C holds (c1 inTARSKIR2 domRELSET-1K1\<^bsub>(C)\<^esub> f & c2 inTARSKIR2 domRELSET-1K1\<^bsub>(C)\<^esub> f) & f /.PARTFUN1K7\<^bsub>(D)\<^esub> c1 =XBOOLE-0R4 f /.PARTFUN1K7\<^bsub>(D)\<^esub> c2 implies c1 =XBOOLE-0R4 c2) implies f be one-to-oneFUNCT-1V2"
sorry

mtheorem partfun2_th_10:
" for x be setHIDDENM2 holds  for y be setHIDDENM2 holds  for C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for f be PartFuncPARTFUN1M1-of(C,D) holds ((f be one-to-oneFUNCT-1V2 & x inTARSKIR2 domRELSET-1K1\<^bsub>(C)\<^esub> f) & y inTARSKIR2 domRELSET-1K1\<^bsub>(C)\<^esub> f) & f /.PARTFUN1K7\<^bsub>(D)\<^esub> x =XBOOLE-0R4 f /.PARTFUN1K7\<^bsub>(D)\<^esub> y implies x =XBOOLE-0R4 y"
sorry

syntax PARTFUN2K2 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ \<inverse>PARTFUN2K2\<^bsub>'( _ , _ ')\<^esub>" [228,0,0]228)
translations "f \<inverse>PARTFUN2K2\<^bsub>(X,Y)\<^esub>" \<rightharpoonup> "f \<inverse>FUNCT-1K4"

mtheorem partfun2_add_2:
  mlet "X be setHIDDENM2", "Y be setHIDDENM2", "f be one-to-oneFUNCT-1V2\<bar>PartFuncPARTFUN1M1-of(X,Y)"
"cluster f \<inverse>FUNCT-1K4 as-term-is PartFuncPARTFUN1M1-of(Y,X)"
proof
(*coherence*)
  show "f \<inverse>FUNCT-1K4 be PartFuncPARTFUN1M1-of(Y,X)"
    using partfun1_th_9 sorry
qed "sorry"

mtheorem partfun2_th_11:
" for C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for f be one-to-oneFUNCT-1V2\<bar>PartFuncPARTFUN1M1-of(C,D) holds  for g be PartFuncPARTFUN1M1-of(D,C) holds g =RELSET-1R2\<^bsub>(D,C)\<^esub> f \<inverse>PARTFUN2K2\<^bsub>(C,D)\<^esub> iff domRELSET-1K1\<^bsub>(D)\<^esub> g =XBOOLE-0R4 rngRELSET-1K2\<^bsub>(D)\<^esub> f & ( for d be ElementSUBSET-1M1-of D holds  for c be ElementSUBSET-1M1-of C holds d inTARSKIR2 rngRELSET-1K2\<^bsub>(D)\<^esub> f & c =XBOOLE-0R4 g /.PARTFUN1K7\<^bsub>(C)\<^esub> d iff c inTARSKIR2 domRELSET-1K1\<^bsub>(C)\<^esub> f & d =XBOOLE-0R4 f /.PARTFUN1K7\<^bsub>(D)\<^esub> c)"
sorry

mtheorem partfun2_th_12:
" for C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for c be ElementSUBSET-1M1-of C holds  for f be one-to-oneFUNCT-1V2\<bar>PartFuncPARTFUN1M1-of(C,D) holds c inTARSKIR2 domRELSET-1K1\<^bsub>(C)\<^esub> f implies c =XBOOLE-0R4 f \<inverse>PARTFUN2K2\<^bsub>(C,D)\<^esub> /.PARTFUN1K7\<^bsub>(C)\<^esub> (f /.PARTFUN1K7\<^bsub>(D)\<^esub> c) & c =XBOOLE-0R4 (f \<inverse>PARTFUN2K2\<^bsub>(C,D)\<^esub> *PARTFUN1K1\<^bsub>(C,D,D,C)\<^esub> f)/.PARTFUN1K7\<^bsub>(C)\<^esub> c"
sorry

mtheorem partfun2_th_13:
" for C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d be ElementSUBSET-1M1-of D holds  for f be one-to-oneFUNCT-1V2\<bar>PartFuncPARTFUN1M1-of(C,D) holds d inTARSKIR2 rngRELSET-1K2\<^bsub>(D)\<^esub> f implies d =XBOOLE-0R4 f /.PARTFUN1K7\<^bsub>(D)\<^esub> (f \<inverse>PARTFUN2K2\<^bsub>(C,D)\<^esub> /.PARTFUN1K7\<^bsub>(C)\<^esub> d) & d =XBOOLE-0R4 (f *PARTFUN1K1\<^bsub>(D,C,C,D)\<^esub> f \<inverse>PARTFUN2K2\<^bsub>(C,D)\<^esub>)/.PARTFUN1K7\<^bsub>(D)\<^esub> d"
sorry

mtheorem partfun2_th_14:
" for C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for f be PartFuncPARTFUN1M1-of(C,D) holds  for t be PartFuncPARTFUN1M1-of(D,C) holds ((f be one-to-oneFUNCT-1V2 & domRELSET-1K1\<^bsub>(C)\<^esub> f =XBOOLE-0R4 rngRELSET-1K2\<^bsub>(C)\<^esub> t) & rngRELSET-1K2\<^bsub>(D)\<^esub> f =XBOOLE-0R4 domRELSET-1K1\<^bsub>(D)\<^esub> t) & ( for c be ElementSUBSET-1M1-of C holds  for d be ElementSUBSET-1M1-of D holds c inTARSKIR2 domRELSET-1K1\<^bsub>(C)\<^esub> f & d inTARSKIR2 domRELSET-1K1\<^bsub>(D)\<^esub> t implies (f /.PARTFUN1K7\<^bsub>(D)\<^esub> c =XBOOLE-0R4 d iff t /.PARTFUN1K7\<^bsub>(C)\<^esub> d =XBOOLE-0R4 c)) implies t =FUNCT-1R1 f \<inverse>FUNCT-1K4"
sorry

mtheorem partfun2_th_15:
" for X be setHIDDENM2 holds  for C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for f be PartFuncPARTFUN1M1-of(C,D) holds  for g be PartFuncPARTFUN1M1-of(C,D) holds g =RELSET-1R2\<^bsub>(C,D)\<^esub> f |PARTFUN1K2\<^bsub>(C,D)\<^esub> X iff domRELSET-1K1\<^bsub>(C)\<^esub> g =XBOOLE-0R4 domRELSET-1K1\<^bsub>(C)\<^esub> f /\\SUBSET-1K8\<^bsub>(C)\<^esub> X & ( for c be ElementSUBSET-1M1-of C holds c inTARSKIR2 domRELSET-1K1\<^bsub>(C)\<^esub> g implies g /.PARTFUN1K7\<^bsub>(D)\<^esub> c =XBOOLE-0R4 f /.PARTFUN1K7\<^bsub>(D)\<^esub> c)"
sorry

mtheorem partfun2_th_16:
" for X be setHIDDENM2 holds  for C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for c be ElementSUBSET-1M1-of C holds  for f be PartFuncPARTFUN1M1-of(C,D) holds c inTARSKIR2 domRELSET-1K1\<^bsub>(C)\<^esub> f /\\SUBSET-1K8\<^bsub>(C)\<^esub> X implies (f |PARTFUN1K2\<^bsub>(C,D)\<^esub> X)/.PARTFUN1K7\<^bsub>(D)\<^esub> c =XBOOLE-0R4 f /.PARTFUN1K7\<^bsub>(D)\<^esub> c"
sorry

mtheorem partfun2_th_17:
" for X be setHIDDENM2 holds  for C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for c be ElementSUBSET-1M1-of C holds  for f be PartFuncPARTFUN1M1-of(C,D) holds c inTARSKIR2 domRELSET-1K1\<^bsub>(C)\<^esub> f & c inTARSKIR2 X implies (f |PARTFUN1K2\<^bsub>(C,D)\<^esub> X)/.PARTFUN1K7\<^bsub>(D)\<^esub> c =XBOOLE-0R4 f /.PARTFUN1K7\<^bsub>(D)\<^esub> c"
sorry

mtheorem partfun2_th_18:
" for X be setHIDDENM2 holds  for C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for c be ElementSUBSET-1M1-of C holds  for f be PartFuncPARTFUN1M1-of(C,D) holds c inTARSKIR2 domRELSET-1K1\<^bsub>(C)\<^esub> f & c inTARSKIR2 X implies f /.PARTFUN1K7\<^bsub>(D)\<^esub> c inTARSKIR2 rngRELSET-1K2\<^bsub>(D)\<^esub> (f |PARTFUN1K2\<^bsub>(C,D)\<^esub> X)"
sorry

syntax PARTFUN2K3 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ |`PARTFUN2K3\<^bsub>'( _ , _ ')\<^esub>  _ " [200,0,0,200]200)
translations "X |`PARTFUN2K3\<^bsub>(C,D)\<^esub> f" \<rightharpoonup> "X |`RELAT-1K9 f"

mtheorem partfun2_add_3:
  mlet "C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "X be setHIDDENM2", "f be PartFuncPARTFUN1M1-of(C,D)"
"cluster X |`RELAT-1K9 f as-term-is PartFuncPARTFUN1M1-of(C,D)"
proof
(*coherence*)
  show "X |`RELAT-1K9 f be PartFuncPARTFUN1M1-of(C,D)"
    using partfun1_th_13 sorry
qed "sorry"

mtheorem partfun2_th_19:
" for X be setHIDDENM2 holds  for C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for f be PartFuncPARTFUN1M1-of(C,D) holds  for g be PartFuncPARTFUN1M1-of(C,D) holds g =RELSET-1R2\<^bsub>(C,D)\<^esub> X |`PARTFUN2K3\<^bsub>(C,D)\<^esub> f iff ( for c be ElementSUBSET-1M1-of C holds c inTARSKIR2 domRELSET-1K1\<^bsub>(C)\<^esub> g iff c inTARSKIR2 domRELSET-1K1\<^bsub>(C)\<^esub> f & f /.PARTFUN1K7\<^bsub>(D)\<^esub> c inTARSKIR2 X) & ( for c be ElementSUBSET-1M1-of C holds c inTARSKIR2 domRELSET-1K1\<^bsub>(C)\<^esub> g implies g /.PARTFUN1K7\<^bsub>(D)\<^esub> c =XBOOLE-0R4 f /.PARTFUN1K7\<^bsub>(D)\<^esub> c)"
sorry

mtheorem partfun2_th_20:
" for X be setHIDDENM2 holds  for C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for c be ElementSUBSET-1M1-of C holds  for f be PartFuncPARTFUN1M1-of(C,D) holds c inTARSKIR2 domRELSET-1K1\<^bsub>(C)\<^esub> (X |`PARTFUN2K3\<^bsub>(C,D)\<^esub> f) iff c inTARSKIR2 domRELSET-1K1\<^bsub>(C)\<^esub> f & f /.PARTFUN1K7\<^bsub>(D)\<^esub> c inTARSKIR2 X"
  using partfun2_th_19 sorry

mtheorem partfun2_th_21:
" for X be setHIDDENM2 holds  for C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for c be ElementSUBSET-1M1-of C holds  for f be PartFuncPARTFUN1M1-of(C,D) holds c inTARSKIR2 domRELSET-1K1\<^bsub>(C)\<^esub> (X |`PARTFUN2K3\<^bsub>(C,D)\<^esub> f) implies (X |`PARTFUN2K3\<^bsub>(C,D)\<^esub> f)/.PARTFUN1K7\<^bsub>(D)\<^esub> c =XBOOLE-0R4 f /.PARTFUN1K7\<^bsub>(D)\<^esub> c"
  using partfun2_th_19 sorry

mtheorem partfun2_th_22:
" for X be setHIDDENM2 holds  for C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for SD be SubsetSUBSET-1M2-of D holds  for f be PartFuncPARTFUN1M1-of(C,D) holds SD =XBOOLE-0R4 f .:RELSET-1K7\<^bsub>(C,D)\<^esub> X iff ( for d be ElementSUBSET-1M1-of D holds d inTARSKIR2 SD iff ( ex c be ElementSUBSET-1M1-of C st (c inTARSKIR2 domRELSET-1K1\<^bsub>(C)\<^esub> f & c inTARSKIR2 X) & d =XBOOLE-0R4 f /.PARTFUN1K7\<^bsub>(D)\<^esub> c))"
sorry

mtheorem partfun2_th_23:
" for X be setHIDDENM2 holds  for C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d be ElementSUBSET-1M1-of D holds  for f be PartFuncPARTFUN1M1-of(C,D) holds d inTARSKIR2 f .:RELSET-1K7\<^bsub>(C,D)\<^esub> X iff ( ex c be ElementSUBSET-1M1-of C st (c inTARSKIR2 domRELSET-1K1\<^bsub>(C)\<^esub> f & c inTARSKIR2 X) & d =XBOOLE-0R4 f /.PARTFUN1K7\<^bsub>(D)\<^esub> c)"
  using partfun2_th_22 sorry

mtheorem partfun2_th_24:
" for C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for c be ElementSUBSET-1M1-of C holds  for f be PartFuncPARTFUN1M1-of(C,D) holds c inTARSKIR2 domRELSET-1K1\<^bsub>(C)\<^esub> f implies ImRELAT-1K12(f,c) =XBOOLE-0R4 {TARSKIK1 f /.PARTFUN1K7\<^bsub>(D)\<^esub> c }"
sorry

mtheorem partfun2_th_25:
" for C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for c1 be ElementSUBSET-1M1-of C holds  for c2 be ElementSUBSET-1M1-of C holds  for f be PartFuncPARTFUN1M1-of(C,D) holds c1 inTARSKIR2 domRELSET-1K1\<^bsub>(C)\<^esub> f & c2 inTARSKIR2 domRELSET-1K1\<^bsub>(C)\<^esub> f implies f .:RELSET-1K7\<^bsub>(C,D)\<^esub> {TARSKIK2 c1,c2 } =XBOOLE-0R4 {TARSKIK2 f /.PARTFUN1K7\<^bsub>(D)\<^esub> c1,f /.PARTFUN1K7\<^bsub>(D)\<^esub> c2 }"
sorry

mtheorem partfun2_th_26:
" for X be setHIDDENM2 holds  for C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for SC be SubsetSUBSET-1M2-of C holds  for f be PartFuncPARTFUN1M1-of(C,D) holds SC =XBOOLE-0R4 f \<inverse>RELSET-1K8\<^bsub>(C,D)\<^esub> X iff ( for c be ElementSUBSET-1M1-of C holds c inTARSKIR2 SC iff c inTARSKIR2 domRELSET-1K1\<^bsub>(C)\<^esub> f & f /.PARTFUN1K7\<^bsub>(D)\<^esub> c inTARSKIR2 X)"
sorry

mtheorem partfun2_th_27:
" for C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for f be PartFuncPARTFUN1M1-of(C,D) holds  ex g be FunctionFUNCT-2M1-of(C,D) st  for c be ElementSUBSET-1M1-of C holds c inTARSKIR2 domRELSET-1K1\<^bsub>(C)\<^esub> f implies g .FUNCT-2K3\<^bsub>(C,D)\<^esub> c =XBOOLE-0R4 f /.PARTFUN1K7\<^bsub>(D)\<^esub> c"
sorry

mtheorem partfun2_th_28:
" for C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for f be PartFuncPARTFUN1M1-of(C,D) holds  for g be PartFuncPARTFUN1M1-of(C,D) holds f toleratesPARTFUN1R1 g iff ( for c be ElementSUBSET-1M1-of C holds c inTARSKIR2 domRELSET-1K1\<^bsub>(C)\<^esub> f /\\SUBSET-1K9\<^bsub>(C)\<^esub> domRELSET-1K1\<^bsub>(C)\<^esub> g implies f /.PARTFUN1K7\<^bsub>(D)\<^esub> c =XBOOLE-0R4 g /.PARTFUN1K7\<^bsub>(D)\<^esub> c)"
sorry

theorem partfun2_sch_1:
  fixes Df0 Cf0 Pp2 
  assumes
[ty]: "Df0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
  [ty]: "Cf0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
  shows " ex f be PartFuncPARTFUN1M1-of(Df0,Cf0) st ( for d be ElementSUBSET-1M1-of Df0 holds d inTARSKIR2 domRELSET-1K1\<^bsub>(Df0)\<^esub> f iff ( ex c be ElementSUBSET-1M1-of Cf0 st Pp2(d,c))) & ( for d be ElementSUBSET-1M1-of Df0 holds d inTARSKIR2 domRELSET-1K1\<^bsub>(Df0)\<^esub> f implies Pp2(d,f /.PARTFUN1K7\<^bsub>(Cf0)\<^esub> d))"
sorry

theorem partfun2_sch_2:
  fixes Df0 Cf0 Ff1 Pp1 
  assumes
[ty]: "Df0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
  [ty]: "Cf0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
  [ty_func]: "\<And> x1. x1 be setHIDDENM2 \<Longrightarrow> Ff1(x1) be ElementSUBSET-1M1-of Cf0"
  shows " ex f be PartFuncPARTFUN1M1-of(Df0,Cf0) st ( for d be ElementSUBSET-1M1-of Df0 holds d inTARSKIR2 domRELSET-1K1\<^bsub>(Df0)\<^esub> f iff Pp1(d)) & ( for d be ElementSUBSET-1M1-of Df0 holds d inTARSKIR2 domRELSET-1K1\<^bsub>(Df0)\<^esub> f implies f /.PARTFUN1K7\<^bsub>(Cf0)\<^esub> d =XBOOLE-0R4 Ff1(d))"
sorry

theorem partfun2_sch_3:
  fixes Cf0 Df0 Xf0 Ff1 
  assumes
[ty]: "Cf0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
  [ty]: "Df0 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2" and
  [ty]: "Xf0 be setHIDDENM2" and
  [ty_func]: "\<And> x1. x1 be setHIDDENM2 \<Longrightarrow> Ff1(x1) be ElementSUBSET-1M1-of Df0"
  shows " for f be PartFuncPARTFUN1M1-of(Cf0,Df0) holds  for g be PartFuncPARTFUN1M1-of(Cf0,Df0) holds (domRELSET-1K1\<^bsub>(Cf0)\<^esub> f =XBOOLE-0R4 Xf0 & ( for c be ElementSUBSET-1M1-of Cf0 holds c inTARSKIR2 domRELSET-1K1\<^bsub>(Cf0)\<^esub> f implies f /.PARTFUN1K7\<^bsub>(Df0)\<^esub> c =XBOOLE-0R4 Ff1(c))) & (domRELSET-1K1\<^bsub>(Cf0)\<^esub> g =XBOOLE-0R4 Xf0 & ( for c be ElementSUBSET-1M1-of Cf0 holds c inTARSKIR2 domRELSET-1K1\<^bsub>(Cf0)\<^esub> g implies g /.PARTFUN1K7\<^bsub>(Df0)\<^esub> c =XBOOLE-0R4 Ff1(c))) implies f =RELSET-1R2\<^bsub>(Cf0,Df0)\<^esub> g"
sorry

syntax PARTFUN2K4 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ -->PARTFUN2K4\<^bsub>'( _ , _ ')\<^esub>  _ " [116,0,0,116]116)
translations "SC -->PARTFUN2K4\<^bsub>(C,D)\<^esub> d" \<rightharpoonup> "SC -->FUNCOP-1K2 d"

mtheorem partfun2_add_4:
  mlet "C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "SC be SubsetSUBSET-1M2-of C", "d be ElementSUBSET-1M1-of D"
"cluster SC -->FUNCOP-1K2 d as-term-is PartFuncPARTFUN1M1-of(C,D)"
proof
(*coherence*)
  show "SC -->FUNCOP-1K2 d be PartFuncPARTFUN1M1-of(C,D)"
sorry
qed "sorry"

mtheorem partfun2_th_29:
" for C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for SC be SubsetSUBSET-1M2-of C holds  for c be ElementSUBSET-1M1-of C holds  for d be ElementSUBSET-1M1-of D holds c inTARSKIR2 SC implies (SC -->PARTFUN2K4\<^bsub>(C,D)\<^esub> d)/.PARTFUN1K7\<^bsub>(D)\<^esub> c =XBOOLE-0R4 d"
sorry

mtheorem partfun2_th_30:
" for C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d be ElementSUBSET-1M1-of D holds  for f be PartFuncPARTFUN1M1-of(C,D) holds ( for c be ElementSUBSET-1M1-of C holds c inTARSKIR2 domRELSET-1K1\<^bsub>(C)\<^esub> f implies f /.PARTFUN1K7\<^bsub>(D)\<^esub> c =XBOOLE-0R4 d) implies f =RELSET-1R2\<^bsub>(C,D)\<^esub> domRELSET-1K1\<^bsub>(C)\<^esub> f -->PARTFUN2K4\<^bsub>(C,D)\<^esub> d"
sorry

mtheorem partfun2_th_31:
" for C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for E be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for SE be SubsetSUBSET-1M2-of E holds  for c be ElementSUBSET-1M1-of C holds  for f be PartFuncPARTFUN1M1-of(C,D) holds c inTARSKIR2 domRELSET-1K1\<^bsub>(C)\<^esub> f implies f *PARTFUN1K1\<^bsub>(E,C,C,D)\<^esub> (SE -->PARTFUN2K4\<^bsub>(E,C)\<^esub> c) =RELSET-1R2\<^bsub>(E,D)\<^esub> SE -->PARTFUN2K4\<^bsub>(E,D)\<^esub> f /.PARTFUN1K7\<^bsub>(D)\<^esub> c"
sorry

mtheorem partfun2_th_32:
" for C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for SC be SubsetSUBSET-1M2-of C holds idPARTFUN2K1\<^bsub>(C)\<^esub> SC be totalPARTFUN1V1\<^bsub>(C)\<^esub> iff SC =XBOOLE-0R4 C"
sorry

mtheorem partfun2_th_33:
" for C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for SC be SubsetSUBSET-1M2-of C holds  for d be ElementSUBSET-1M1-of D holds SC -->PARTFUN2K4\<^bsub>(C,D)\<^esub> d be totalPARTFUN1V1\<^bsub>(C)\<^esub> implies SC <>HIDDENR2 {}XBOOLE-0K1"
sorry

mtheorem partfun2_th_34:
" for C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for SC be SubsetSUBSET-1M2-of C holds  for d be ElementSUBSET-1M1-of D holds SC -->PARTFUN2K4\<^bsub>(C,D)\<^esub> d be totalPARTFUN1V1\<^bsub>(C)\<^esub> iff SC =XBOOLE-0R4 C"
sorry

syntax PARTFUN2V1 :: " Set \<Rightarrow>  Set \<Rightarrow> Ty" ("constantPARTFUN2V1\<^bsub>'( _ , _ ')\<^esub>" [0,0]70)
translations "constantPARTFUN2V1\<^bsub>(C,D)\<^esub>" \<rightharpoonup> "constantFUNCT-1V5"

mtheorem partfun2_def_1:
  mlet "C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "f be PartFuncPARTFUN1M1-of(C,D)"
"redefine attr constantPARTFUN2V1\<^bsub>(C,D)\<^esub> for PartFuncPARTFUN1M1-of(C,D) means
  (\<lambda>f.  ex d be ElementSUBSET-1M1-of D st  for c be ElementSUBSET-1M1-of C holds c inTARSKIR2 domRELSET-1K1\<^bsub>(C)\<^esub> f implies f .FUNCT-1K1 c =XBOOLE-0R4 d)"
proof
(*compatibility*)
  show " for f be PartFuncPARTFUN1M1-of(C,D) holds f be constantPARTFUN2V1\<^bsub>(C,D)\<^esub> iff ( ex d be ElementSUBSET-1M1-of D st  for c be ElementSUBSET-1M1-of C holds c inTARSKIR2 domRELSET-1K1\<^bsub>(C)\<^esub> f implies f .FUNCT-1K1 c =XBOOLE-0R4 d)"
sorry
qed "sorry"

mtheorem partfun2_th_35:
" for X be setHIDDENM2 holds  for C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for f be PartFuncPARTFUN1M1-of(C,D) holds f |PARTFUN1K2\<^bsub>(C,D)\<^esub> X be constantFUNCT-1V5 iff ( ex d be ElementSUBSET-1M1-of D st  for c be ElementSUBSET-1M1-of C holds c inTARSKIR2 X /\\SUBSET-1K9\<^bsub>(C)\<^esub> domRELSET-1K1\<^bsub>(C)\<^esub> f implies f /.PARTFUN1K7\<^bsub>(D)\<^esub> c =XBOOLE-0R4 d)"
sorry

mtheorem partfun2_th_36:
" for X be setHIDDENM2 holds  for C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for f be PartFuncPARTFUN1M1-of(C,D) holds f |PARTFUN1K2\<^bsub>(C,D)\<^esub> X be constantFUNCT-1V5 iff ( for c1 be ElementSUBSET-1M1-of C holds  for c2 be ElementSUBSET-1M1-of C holds c1 inTARSKIR2 X /\\SUBSET-1K9\<^bsub>(C)\<^esub> domRELSET-1K1\<^bsub>(C)\<^esub> f & c2 inTARSKIR2 X /\\SUBSET-1K9\<^bsub>(C)\<^esub> domRELSET-1K1\<^bsub>(C)\<^esub> f implies f /.PARTFUN1K7\<^bsub>(D)\<^esub> c1 =XBOOLE-0R4 f /.PARTFUN1K7\<^bsub>(D)\<^esub> c2)"
sorry

mtheorem partfun2_th_37:
" for X be setHIDDENM2 holds  for C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for f be PartFuncPARTFUN1M1-of(C,D) holds X meetsXBOOLE-0R5 domRELSET-1K1\<^bsub>(C)\<^esub> f implies (f |PARTFUN1K2\<^bsub>(C,D)\<^esub> X be constantFUNCT-1V5 iff ( ex d be ElementSUBSET-1M1-of D st rngRELSET-1K2\<^bsub>(D)\<^esub> (f |PARTFUN1K2\<^bsub>(C,D)\<^esub> X) =XBOOLE-0R4 {TARSKIK1 d}))"
sorry

mtheorem partfun2_th_38:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for f be PartFuncPARTFUN1M1-of(C,D) holds f |PARTFUN1K2\<^bsub>(C,D)\<^esub> X be constantFUNCT-1V5 & Y c=TARSKIR1 X implies f |PARTFUN1K2\<^bsub>(C,D)\<^esub> Y be constantFUNCT-1V5"
sorry

mtheorem partfun2_th_39:
" for X be setHIDDENM2 holds  for C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for f be PartFuncPARTFUN1M1-of(C,D) holds X missesXBOOLE-0R1 domRELSET-1K1\<^bsub>(C)\<^esub> f implies f |PARTFUN1K2\<^bsub>(C,D)\<^esub> X be constantFUNCT-1V5"
sorry

mtheorem partfun2_th_40:
" for C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for SC be SubsetSUBSET-1M2-of C holds  for d be ElementSUBSET-1M1-of D holds  for f be PartFuncPARTFUN1M1-of(C,D) holds f |PARTFUN1K2\<^bsub>(C,D)\<^esub> SC =RELSET-1R2\<^bsub>(C,D)\<^esub> domRELSET-1K1\<^bsub>(C)\<^esub> (f |PARTFUN1K2\<^bsub>(C,D)\<^esub> SC) -->PARTFUN2K4\<^bsub>(C,D)\<^esub> d implies f |PARTFUN1K2\<^bsub>(C,D)\<^esub> SC be constantFUNCT-1V5"
sorry

mtheorem partfun2_th_41:
" for x be setHIDDENM2 holds  for C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for f be PartFuncPARTFUN1M1-of(C,D) holds f |PARTFUN1K2\<^bsub>(C,D)\<^esub> {TARSKIK1 x} be constantFUNCT-1V5"
sorry

mtheorem partfun2_th_42:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for f be PartFuncPARTFUN1M1-of(C,D) holds (f |PARTFUN1K2\<^bsub>(C,D)\<^esub> X be constantFUNCT-1V5 & f |PARTFUN1K2\<^bsub>(C,D)\<^esub> Y be constantFUNCT-1V5) & X /\\XBOOLE-0K3 Y meetsXBOOLE-0R5 domRELSET-1K1\<^bsub>(C)\<^esub> f implies f |PARTFUN1K2\<^bsub>(C,D)\<^esub> (X \\/XBOOLE-0K2 Y) be constantFUNCT-1V5"
sorry

mtheorem partfun2_th_43:
" for X be setHIDDENM2 holds  for Y be setHIDDENM2 holds  for C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for f be PartFuncPARTFUN1M1-of(C,D) holds f |PARTFUN1K2\<^bsub>(C,D)\<^esub> Y be constantFUNCT-1V5 implies (f |PARTFUN1K2\<^bsub>(C,D)\<^esub> X)|PARTFUN1K2\<^bsub>(C,D)\<^esub> Y be constantFUNCT-1V5"
sorry

mtheorem partfun2_th_44:
" for C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for SC be SubsetSUBSET-1M2-of C holds  for d be ElementSUBSET-1M1-of D holds (SC -->PARTFUN2K4\<^bsub>(C,D)\<^esub> d)|PARTFUN1K2\<^bsub>(C,D)\<^esub> SC be constantFUNCT-1V5"
sorry

mtheorem partfun2_th_45:
" for C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for f be PartFuncPARTFUN1M1-of(C,D) holds  for g be PartFuncPARTFUN1M1-of(C,D) holds domRELSET-1K1\<^bsub>(C)\<^esub> f c=TARSKIR1 domRELSET-1K1\<^bsub>(C)\<^esub> g & ( for c be ElementSUBSET-1M1-of C holds c inTARSKIR2 domRELSET-1K1\<^bsub>(C)\<^esub> f implies f /.PARTFUN1K7\<^bsub>(D)\<^esub> c =XBOOLE-0R4 g /.PARTFUN1K7\<^bsub>(D)\<^esub> c) implies f c=RELSET-1R1\<^bsub>(C,D)\<^esub> g"
sorry

mtheorem partfun2_th_46:
" for C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for c be ElementSUBSET-1M1-of C holds  for d be ElementSUBSET-1M1-of D holds  for f be PartFuncPARTFUN1M1-of(C,D) holds c inTARSKIR2 domRELSET-1K1\<^bsub>(C)\<^esub> f & d =XBOOLE-0R4 f /.PARTFUN1K7\<^bsub>(D)\<^esub> c iff [TARSKIK4 c,d ] inHIDDENR3 f"
sorry

mtheorem partfun2_th_47:
" for C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for E be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for c be ElementSUBSET-1M1-of C holds  for e be ElementSUBSET-1M1-of E holds  for f be PartFuncPARTFUN1M1-of(C,D) holds  for s be PartFuncPARTFUN1M1-of(D,E) holds [TARSKIK4 c,e ] inHIDDENR3 s *PARTFUN1K1\<^bsub>(C,D,D,E)\<^esub> f implies [TARSKIK4 c,f /.PARTFUN1K7\<^bsub>(D)\<^esub> c ] inHIDDENR3 f & [TARSKIK4 f /.PARTFUN1K7\<^bsub>(D)\<^esub> c,e ] inHIDDENR3 s"
sorry

mtheorem partfun2_th_48:
" for C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for c be ElementSUBSET-1M1-of C holds  for d be ElementSUBSET-1M1-of D holds  for f be PartFuncPARTFUN1M1-of(C,D) holds f =XBOOLE-0R4 {TARSKIK1 [TARSKIK4 c,d ] } implies f /.PARTFUN1K7\<^bsub>(D)\<^esub> c =XBOOLE-0R4 d"
sorry

mtheorem partfun2_th_49:
" for C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for c be ElementSUBSET-1M1-of C holds  for f be PartFuncPARTFUN1M1-of(C,D) holds domRELSET-1K1\<^bsub>(C)\<^esub> f =XBOOLE-0R4 {TARSKIK1 c} implies f =XBOOLE-0R4 {TARSKIK1 [TARSKIK4 c,f /.PARTFUN1K7\<^bsub>(D)\<^esub> c ] }"
sorry

mtheorem partfun2_th_50:
" for C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for c be ElementSUBSET-1M1-of C holds  for f be PartFuncPARTFUN1M1-of(C,D) holds  for f1 be PartFuncPARTFUN1M1-of(C,D) holds  for g be PartFuncPARTFUN1M1-of(C,D) holds f1 =RELSET-1R2\<^bsub>(C,D)\<^esub> f /\\SUBSET-1K9\<^bsub>([:ZFMISC-1K2 C,D :])\<^esub> g & c inTARSKIR2 domRELSET-1K1\<^bsub>(C)\<^esub> f1 implies f1 /.PARTFUN1K7\<^bsub>(D)\<^esub> c =XBOOLE-0R4 f /.PARTFUN1K7\<^bsub>(D)\<^esub> c & f1 /.PARTFUN1K7\<^bsub>(D)\<^esub> c =XBOOLE-0R4 g /.PARTFUN1K7\<^bsub>(D)\<^esub> c"
sorry

mtheorem partfun2_th_51:
" for C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for c be ElementSUBSET-1M1-of C holds  for f be PartFuncPARTFUN1M1-of(C,D) holds  for f1 be PartFuncPARTFUN1M1-of(C,D) holds  for g be PartFuncPARTFUN1M1-of(C,D) holds c inTARSKIR2 domRELSET-1K1\<^bsub>(C)\<^esub> f & f1 =RELSET-1R2\<^bsub>(C,D)\<^esub> f \\/SUBSET-1K4\<^bsub>([:ZFMISC-1K2 C,D :])\<^esub> g implies f1 /.PARTFUN1K7\<^bsub>(D)\<^esub> c =XBOOLE-0R4 f /.PARTFUN1K7\<^bsub>(D)\<^esub> c"
sorry

mtheorem partfun2_th_52:
" for C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for c be ElementSUBSET-1M1-of C holds  for f be PartFuncPARTFUN1M1-of(C,D) holds  for f1 be PartFuncPARTFUN1M1-of(C,D) holds  for g be PartFuncPARTFUN1M1-of(C,D) holds c inTARSKIR2 domRELSET-1K1\<^bsub>(C)\<^esub> g & f1 =RELSET-1R2\<^bsub>(C,D)\<^esub> f \\/SUBSET-1K4\<^bsub>([:ZFMISC-1K2 C,D :])\<^esub> g implies f1 /.PARTFUN1K7\<^bsub>(D)\<^esub> c =XBOOLE-0R4 g /.PARTFUN1K7\<^bsub>(D)\<^esub> c"
sorry

mtheorem partfun2_th_53:
" for C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for c be ElementSUBSET-1M1-of C holds  for f be PartFuncPARTFUN1M1-of(C,D) holds  for f1 be PartFuncPARTFUN1M1-of(C,D) holds  for g be PartFuncPARTFUN1M1-of(C,D) holds c inTARSKIR2 domRELSET-1K1\<^bsub>(C)\<^esub> f1 & f1 =RELSET-1R2\<^bsub>(C,D)\<^esub> f \\/SUBSET-1K4\<^bsub>([:ZFMISC-1K2 C,D :])\<^esub> g implies f1 /.PARTFUN1K7\<^bsub>(D)\<^esub> c =XBOOLE-0R4 f /.PARTFUN1K7\<^bsub>(D)\<^esub> c or f1 /.PARTFUN1K7\<^bsub>(D)\<^esub> c =XBOOLE-0R4 g /.PARTFUN1K7\<^bsub>(D)\<^esub> c"
sorry

mtheorem partfun2_th_54:
" for C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for SC be SubsetSUBSET-1M2-of C holds  for c be ElementSUBSET-1M1-of C holds  for f be PartFuncPARTFUN1M1-of(C,D) holds c inTARSKIR2 domRELSET-1K1\<^bsub>(C)\<^esub> f & c inTARSKIR2 SC iff [TARSKIK4 c,f /.PARTFUN1K7\<^bsub>(D)\<^esub> c ] inHIDDENR3 f |PARTFUN1K2\<^bsub>(C,D)\<^esub> SC"
sorry

mtheorem partfun2_th_55:
" for C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for SD be SubsetSUBSET-1M2-of D holds  for c be ElementSUBSET-1M1-of C holds  for f be PartFuncPARTFUN1M1-of(C,D) holds c inTARSKIR2 domRELSET-1K1\<^bsub>(C)\<^esub> f & f /.PARTFUN1K7\<^bsub>(D)\<^esub> c inTARSKIR2 SD iff [TARSKIK4 c,f /.PARTFUN1K7\<^bsub>(D)\<^esub> c ] inHIDDENR3 SD |`PARTFUN2K3\<^bsub>(C,D)\<^esub> f"
sorry

mtheorem partfun2_th_56:
" for C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for SD be SubsetSUBSET-1M2-of D holds  for c be ElementSUBSET-1M1-of C holds  for f be PartFuncPARTFUN1M1-of(C,D) holds c inTARSKIR2 f \<inverse>RELSET-1K8\<^bsub>(C,D)\<^esub> SD iff [TARSKIK4 c,f /.PARTFUN1K7\<^bsub>(D)\<^esub> c ] inHIDDENR3 f & f /.PARTFUN1K7\<^bsub>(D)\<^esub> c inTARSKIR2 SD"
sorry

mtheorem partfun2_th_57:
" for X be setHIDDENM2 holds  for C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for f be PartFuncPARTFUN1M1-of(C,D) holds f |PARTFUN1K2\<^bsub>(C,D)\<^esub> X be constantFUNCT-1V5 iff ( ex d be ElementSUBSET-1M1-of D st  for c be ElementSUBSET-1M1-of C holds c inTARSKIR2 X /\\SUBSET-1K9\<^bsub>(C)\<^esub> domRELSET-1K1\<^bsub>(C)\<^esub> f implies f .FUNCT-1K1 c =XBOOLE-0R4 d)"
sorry

mtheorem partfun2_th_58:
" for X be setHIDDENM2 holds  for C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for f be PartFuncPARTFUN1M1-of(C,D) holds f |PARTFUN1K2\<^bsub>(C,D)\<^esub> X be constantFUNCT-1V5 iff ( for c1 be ElementSUBSET-1M1-of C holds  for c2 be ElementSUBSET-1M1-of C holds c1 inTARSKIR2 X /\\SUBSET-1K9\<^bsub>(C)\<^esub> domRELSET-1K1\<^bsub>(C)\<^esub> f & c2 inTARSKIR2 X /\\SUBSET-1K9\<^bsub>(C)\<^esub> domRELSET-1K1\<^bsub>(C)\<^esub> f implies f .FUNCT-1K1 c1 =XBOOLE-0R4 f .FUNCT-1K1 c2)"
sorry

mtheorem partfun2_th_59:
" for X be setHIDDENM2 holds  for C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d be ElementSUBSET-1M1-of D holds  for f be PartFuncPARTFUN1M1-of(C,D) holds d inTARSKIR2 f .:RELSET-1K7\<^bsub>(C,D)\<^esub> X implies ( ex c be ElementSUBSET-1M1-of C st (c inTARSKIR2 domRELSET-1K1\<^bsub>(C)\<^esub> f & c inTARSKIR2 X) & d =XBOOLE-0R4 f .FUNCT-1K1 c)"
sorry

mtheorem partfun2_th_60:
" for C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for c be ElementSUBSET-1M1-of C holds  for d be ElementSUBSET-1M1-of D holds  for f be PartFuncPARTFUN1M1-of(C,D) holds f be one-to-oneFUNCT-1V2 implies (d inTARSKIR2 rngRELSET-1K2\<^bsub>(D)\<^esub> f & c =XBOOLE-0R4 f \<inverse>FUNCT-1K4 .FUNCT-1K1 d iff c inTARSKIR2 domRELSET-1K1\<^bsub>(C)\<^esub> f & d =XBOOLE-0R4 f .FUNCT-1K1 c)"
sorry

mtheorem partfun2_th_61:
" for Y be setHIDDENM2 holds  for f be Y -valuedRELAT-1V5\<bar>FunctionFUNCT-1M1 holds  for g be Y -valuedRELAT-1V5\<bar>FunctionFUNCT-1M1 holds f c=RELAT-1R2 g implies ( for x be setHIDDENM2 holds x inTARSKIR2 domRELAT-1K1 f implies f /.PARTFUN1K7\<^bsub>(Y)\<^esub> x =XBOOLE-0R4 g /.PARTFUN1K7\<^bsub>(Y)\<^esub> x)"
sorry

end
