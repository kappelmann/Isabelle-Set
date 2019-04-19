theory finseqop
  imports eqrel_1 finseq_2
   "../mizar_extension/E_number"
begin
(*begin*)
reserve x, y for "setHIDDENM2"
reserve C, C9, D, D9, E for " non emptyXBOOLE-0V1\<bar>setHIDDENM2"
reserve c for "ElementSUBSET-1M1-of C"
reserve c9 for "ElementSUBSET-1M1-of C9"
reserve d, d1, d2, d3, d4, e for "ElementSUBSET-1M1-of D"
reserve d9 for "ElementSUBSET-1M1-of D9"
mtheorem finseqop_th_1:
" for f be FunctionFUNCT-1M1 holds <:FUNCT-3K14 {}XBOOLE-0K1,f :> =FUNCT-1R1 {}XBOOLE-0K1 & <:FUNCT-3K14 f,{}XBOOLE-0K1 :> =FUNCT-1R1 {}XBOOLE-0K1"
sorry

mtheorem finseqop_th_2:
" for f be FunctionFUNCT-1M1 holds [:FUNCT-3K16 {}XBOOLE-0K1,f :] =FUNCT-1R1 {}XBOOLE-0K1 & [:FUNCT-3K16 f,{}XBOOLE-0K1 :] =FUNCT-1R1 {}XBOOLE-0K1"
sorry

mtheorem finseqop_th_3:
" for F be FunctionFUNCT-1M1 holds  for f be FunctionFUNCT-1M1 holds F .:FUNCOP-1K3({}XBOOLE-0K1,f) =FUNCT-1R1 {}XBOOLE-0K1 & F .:FUNCOP-1K3(f,{}XBOOLE-0K1) =FUNCT-1R1 {}XBOOLE-0K1"
sorry

mtheorem finseqop_th_4:
" for x be setHIDDENM2 holds  for F be FunctionFUNCT-1M1 holds F [:]FUNCOP-1K4({}XBOOLE-0K1,x) =FUNCT-1R1 {}XBOOLE-0K1"
sorry

mtheorem finseqop_th_5:
" for x be setHIDDENM2 holds  for F be FunctionFUNCT-1M1 holds F [;]FUNCOP-1K5(x,{}XBOOLE-0K1) =FUNCT-1R1 {}XBOOLE-0K1"
sorry

mtheorem finseqop_th_6:
" for X be setHIDDENM2 holds  for x1 be setHIDDENM2 holds  for x2 be setHIDDENM2 holds <:FUNCT-3K15\<^bsub>(X,{TARSKIK1 x1},{TARSKIK1 x2})\<^esub> X -->FUNCOP-1K7 x1,X -->FUNCOP-1K7 x2 :> =FUNCT-2R1\<^bsub>(X,[:ZFMISC-1K2 {TARSKIK1 x1},{TARSKIK1 x2} :],X,{TARSKIK1 [TARSKIK4 x1,x2 ] })\<^esub> X -->FUNCOP-1K7 [TARSKIK4 x1,x2 ]"
sorry

mtheorem finseqop_th_7:
" for F be FunctionFUNCT-1M1 holds  for X be setHIDDENM2 holds  for x1 be setHIDDENM2 holds  for x2 be setHIDDENM2 holds [TARSKIK4 x1,x2 ] inHIDDENR3 domRELAT-1K1 F implies F .:FUNCOP-1K3(X -->FUNCOP-1K7 x1,X -->FUNCOP-1K7 x2) =FUNCT-1R1 X -->FUNCOP-1K7 F .BINOP-1K1(x1,x2)"
sorry

reserve i, j for "naturalORDINAL1V7\<bar>NumberORDINAL1M1"
reserve F for "FunctionFUNCT-2M1-of([:ZFMISC-1K2 D,D9 :],E)"
reserve p, q for "FinSequenceFINSEQ-1M3-of D"
reserve p9, q9 for "FinSequenceFINSEQ-1M3-of D9"
syntax FINSEQOPK1 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ .:FINSEQOPK1\<^bsub>'( _ , _ , _ ')\<^esub>'( _ , _ ')" [200,0,0,0,0,0]200)
translations "F .:FINSEQOPK1\<^bsub>(D,D9,E)\<^esub>(p,p9)" \<rightharpoonup> "F .:FUNCOP-1K3(p,p9)"

mtheorem finseqop_add_1:
  mlet "D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "D9 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "E be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "F be FunctionFUNCT-2M1-of([:ZFMISC-1K2 D,D9 :],E)", "p be FinSequenceFINSEQ-1M3-of D", "p9 be FinSequenceFINSEQ-1M3-of D9"
"cluster F .:FUNCOP-1K3(p,p9) as-term-is FinSequenceFINSEQ-1M3-of E"
proof
(*coherence*)
  show "F .:FUNCOP-1K3(p,p9) be FinSequenceFINSEQ-1M3-of E"
    using finseq_2_th_70 sorry
qed "sorry"

syntax FINSEQOPK2 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ [:]FINSEQOPK2\<^bsub>'( _ , _ , _ ')\<^esub>'( _ , _ ')" [180,0,0,0,0,0]180)
translations "F [:]FINSEQOPK2\<^bsub>(D,D9,E)\<^esub>(p,d9)" \<rightharpoonup> "F [:]FUNCOP-1K4(p,d9)"

mtheorem finseqop_add_2:
  mlet "D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "D9 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "E be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "F be FunctionFUNCT-2M1-of([:ZFMISC-1K2 D,D9 :],E)", "p be FinSequenceFINSEQ-1M3-of D", "d9 be ElementSUBSET-1M1-of D9"
"cluster F [:]FUNCOP-1K4(p,d9) as-term-is FinSequenceFINSEQ-1M3-of E"
proof
(*coherence*)
  show "F [:]FUNCOP-1K4(p,d9) be FinSequenceFINSEQ-1M3-of E"
    using finseq_2_th_83 sorry
qed "sorry"

syntax FINSEQOPK3 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ [;]FINSEQOPK3\<^bsub>'( _ , _ , _ ')\<^esub>'( _ , _ ')" [180,0,0,0,0,0]180)
translations "F [;]FINSEQOPK3\<^bsub>(D,D9,E)\<^esub>(d,p9)" \<rightharpoonup> "F [;]FUNCOP-1K5(d,p9)"

mtheorem finseqop_add_3:
  mlet "D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "D9 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "E be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "F be FunctionFUNCT-2M1-of([:ZFMISC-1K2 D,D9 :],E)", "d be ElementSUBSET-1M1-of D", "p9 be FinSequenceFINSEQ-1M3-of D9"
"cluster F [;]FUNCOP-1K5(d,p9) as-term-is FinSequenceFINSEQ-1M3-of E"
proof
(*coherence*)
  show "F [;]FUNCOP-1K5(d,p9) be FinSequenceFINSEQ-1M3-of E"
    using finseq_2_th_77 sorry
qed "sorry"

reserve f, f9 for "FunctionFUNCT-2M1-of(C,D)"
reserve h for "FunctionFUNCT-2M1-of(D,E)"
syntax FINSEQOPK4 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ *FINSEQOPK4\<^bsub>'( _ , _ ')\<^esub>  _ " [164,0,0,164]164)
translations "h *FINSEQOPK4\<^bsub>(D,E)\<^esub> p" \<rightharpoonup> "p *RELAT-1K6 h"

mtheorem finseqop_add_4:
  mlet "D be setHIDDENM2", "E be setHIDDENM2", "p be FinSequenceFINSEQ-1M3-of D", "h be FunctionFUNCT-2M1-of(D,E)"
"cluster p *RELAT-1K6 h as-term-is FinSequenceFINSEQ-1M3-of E"
proof
(*coherence*)
  show "p *RELAT-1K6 h be FinSequenceFINSEQ-1M3-of E"
    using finseq_2_th_32 sorry
qed "sorry"

mtheorem finseqop_th_8:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for E be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d be ElementSUBSET-1M1-of D holds  for p be FinSequenceFINSEQ-1M3-of D holds  for h be FunctionFUNCT-2M1-of(D,E) holds h *FINSEQOPK4\<^bsub>(D,E)\<^esub> (p ^FINSEQ-1K9\<^bsub>(D)\<^esub> (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>)) =RELSET-1R2\<^bsub>(omegaORDINAL1K4,E)\<^esub> (h *FINSEQOPK4\<^bsub>(D,E)\<^esub> p)^FINSEQ-1K9\<^bsub>(E)\<^esub> (<*FINSEQ-1K13\<^bsub>(E)\<^esub> h .FUNCT-2K3\<^bsub>(D,E)\<^esub> d*>)"
sorry

mtheorem finseqop_th_9:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for E be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for p be FinSequenceFINSEQ-1M3-of D holds  for q be FinSequenceFINSEQ-1M3-of D holds  for h be FunctionFUNCT-2M1-of(D,E) holds h *FINSEQOPK4\<^bsub>(D,E)\<^esub> (p ^FINSEQ-1K9\<^bsub>(D)\<^esub> q) =RELSET-1R2\<^bsub>(omegaORDINAL1K4,E)\<^esub> (h *FINSEQOPK4\<^bsub>(D,E)\<^esub> p)^FINSEQ-1K9\<^bsub>(E)\<^esub> (h *FINSEQOPK4\<^bsub>(D,E)\<^esub> q)"
sorry

reserve T, T1, T2, T3 for "TupleFINSEQ-2M3-of(i,D)"
reserve T9 for "TupleFINSEQ-2M3-of(i,D9)"
reserve S for "TupleFINSEQ-2M3-of(j,D)"
reserve S9 for "TupleFINSEQ-2M3-of(j,D9)"
mlemma finseqop_lm_1:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D9 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for E be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for F be FunctionFUNCT-2M1-of([:ZFMISC-1K2 D,D9 :],E) holds  for T9 be TupleFINSEQ-2M3-of(i,D9) holds  for T be TupleFINSEQ-2M3-of(0NUMBERSK6,D) holds F .:FINSEQOPK1\<^bsub>(D,D9,E)\<^esub>(T,T9) =RELSET-1R2\<^bsub>(omegaORDINAL1K4,E)\<^esub> <*>FINSEQ-1K7 E"
sorry

mlemma finseqop_lm_2:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D9 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for E be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d be ElementSUBSET-1M1-of D holds  for F be FunctionFUNCT-2M1-of([:ZFMISC-1K2 D,D9 :],E) holds  for T9 be TupleFINSEQ-2M3-of(0NUMBERSK6,D9) holds F [;]FINSEQOPK3\<^bsub>(D,D9,E)\<^esub>(d,T9) =RELSET-1R2\<^bsub>(omegaORDINAL1K4,E)\<^esub> <*>FINSEQ-1K7 E"
sorry

mlemma finseqop_lm_3:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D9 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for E be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d9 be ElementSUBSET-1M1-of D9 holds  for F be FunctionFUNCT-2M1-of([:ZFMISC-1K2 D,D9 :],E) holds  for T be TupleFINSEQ-2M3-of(0NUMBERSK6,D) holds F [:]FINSEQOPK2\<^bsub>(D,D9,E)\<^esub>(T,d9) =RELSET-1R2\<^bsub>(omegaORDINAL1K4,E)\<^esub> <*>FINSEQ-1K7 E"
sorry

mtheorem finseqop_th_10:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D9 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for E be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d be ElementSUBSET-1M1-of D holds  for d9 be ElementSUBSET-1M1-of D9 holds  for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for F be FunctionFUNCT-2M1-of([:ZFMISC-1K2 D,D9 :],E) holds  for T be TupleFINSEQ-2M3-of(i,D) holds  for T9 be TupleFINSEQ-2M3-of(i,D9) holds F .:FINSEQOPK1\<^bsub>(D,D9,E)\<^esub>(T ^FINSEQ-1K9\<^bsub>(D)\<^esub> (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>),T9 ^FINSEQ-1K9\<^bsub>(D9)\<^esub> (<*FINSEQ-1K13\<^bsub>(D9)\<^esub> d9*>)) =RELSET-1R2\<^bsub>(omegaORDINAL1K4,E)\<^esub> F .:FINSEQOPK1\<^bsub>(D,D9,E)\<^esub>(T,T9) ^FINSEQ-1K9\<^bsub>(E)\<^esub> (<*FINSEQ-1K13\<^bsub>(E)\<^esub> F .BINOP-1K2\<^bsub>(D,D9,E)\<^esub>(d,d9)*>)"
sorry

mtheorem finseqop_th_11:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D9 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for E be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for j be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for F be FunctionFUNCT-2M1-of([:ZFMISC-1K2 D,D9 :],E) holds  for T be TupleFINSEQ-2M3-of(i,D) holds  for T9 be TupleFINSEQ-2M3-of(i,D9) holds  for S be TupleFINSEQ-2M3-of(j,D) holds  for S9 be TupleFINSEQ-2M3-of(j,D9) holds F .:FINSEQOPK1\<^bsub>(D,D9,E)\<^esub>(T ^FINSEQ-1K9\<^bsub>(D)\<^esub> S,T9 ^FINSEQ-1K9\<^bsub>(D9)\<^esub> S9) =RELSET-1R2\<^bsub>(omegaORDINAL1K4,E)\<^esub> F .:FINSEQOPK1\<^bsub>(D,D9,E)\<^esub>(T,T9) ^FINSEQ-1K9\<^bsub>(E)\<^esub> F .:FINSEQOPK1\<^bsub>(D,D9,E)\<^esub>(S,S9)"
sorry

mtheorem finseqop_th_12:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D9 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for E be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d be ElementSUBSET-1M1-of D holds  for d9 be ElementSUBSET-1M1-of D9 holds  for F be FunctionFUNCT-2M1-of([:ZFMISC-1K2 D,D9 :],E) holds  for p9 be FinSequenceFINSEQ-1M3-of D9 holds F [;]FINSEQOPK3\<^bsub>(D,D9,E)\<^esub>(d,p9 ^FINSEQ-1K9\<^bsub>(D9)\<^esub> (<*FINSEQ-1K13\<^bsub>(D9)\<^esub> d9*>)) =RELSET-1R2\<^bsub>(omegaORDINAL1K4,E)\<^esub> F [;]FINSEQOPK3\<^bsub>(D,D9,E)\<^esub>(d,p9) ^FINSEQ-1K9\<^bsub>(E)\<^esub> (<*FINSEQ-1K13\<^bsub>(E)\<^esub> F .BINOP-1K2\<^bsub>(D,D9,E)\<^esub>(d,d9)*>)"
sorry

mtheorem finseqop_th_13:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D9 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for E be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d be ElementSUBSET-1M1-of D holds  for F be FunctionFUNCT-2M1-of([:ZFMISC-1K2 D,D9 :],E) holds  for p9 be FinSequenceFINSEQ-1M3-of D9 holds  for q9 be FinSequenceFINSEQ-1M3-of D9 holds F [;]FINSEQOPK3\<^bsub>(D,D9,E)\<^esub>(d,p9 ^FINSEQ-1K9\<^bsub>(D9)\<^esub> q9) =RELSET-1R2\<^bsub>(omegaORDINAL1K4,E)\<^esub> F [;]FINSEQOPK3\<^bsub>(D,D9,E)\<^esub>(d,p9) ^FINSEQ-1K9\<^bsub>(E)\<^esub> F [;]FINSEQOPK3\<^bsub>(D,D9,E)\<^esub>(d,q9)"
sorry

mtheorem finseqop_th_14:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D9 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for E be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d be ElementSUBSET-1M1-of D holds  for d9 be ElementSUBSET-1M1-of D9 holds  for F be FunctionFUNCT-2M1-of([:ZFMISC-1K2 D,D9 :],E) holds  for p be FinSequenceFINSEQ-1M3-of D holds F [:]FINSEQOPK2\<^bsub>(D,D9,E)\<^esub>(p ^FINSEQ-1K9\<^bsub>(D)\<^esub> (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>),d9) =RELSET-1R2\<^bsub>(omegaORDINAL1K4,E)\<^esub> F [:]FINSEQOPK2\<^bsub>(D,D9,E)\<^esub>(p,d9) ^FINSEQ-1K9\<^bsub>(E)\<^esub> (<*FINSEQ-1K13\<^bsub>(E)\<^esub> F .BINOP-1K2\<^bsub>(D,D9,E)\<^esub>(d,d9)*>)"
sorry

mtheorem finseqop_th_15:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D9 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for E be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d9 be ElementSUBSET-1M1-of D9 holds  for F be FunctionFUNCT-2M1-of([:ZFMISC-1K2 D,D9 :],E) holds  for p be FinSequenceFINSEQ-1M3-of D holds  for q be FinSequenceFINSEQ-1M3-of D holds F [:]FINSEQOPK2\<^bsub>(D,D9,E)\<^esub>(p ^FINSEQ-1K9\<^bsub>(D)\<^esub> q,d9) =RELSET-1R2\<^bsub>(omegaORDINAL1K4,E)\<^esub> F [:]FINSEQOPK2\<^bsub>(D,D9,E)\<^esub>(p,d9) ^FINSEQ-1K9\<^bsub>(E)\<^esub> F [:]FINSEQOPK2\<^bsub>(D,D9,E)\<^esub>(q,d9)"
sorry

mtheorem finseqop_th_16:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for E be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d be ElementSUBSET-1M1-of D holds  for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for h be FunctionFUNCT-2M1-of(D,E) holds h *FINSEQOPK4\<^bsub>(D,E)\<^esub> (i |->FINSEQ-2K5\<^bsub>(D)\<^esub> d) =RELSET-1R2\<^bsub>(omegaORDINAL1K4,E)\<^esub> i |->FINSEQ-2K5\<^bsub>(E)\<^esub> h .FUNCT-2K3\<^bsub>(D,E)\<^esub> d"
sorry

mtheorem finseqop_th_17:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D9 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for E be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d be ElementSUBSET-1M1-of D holds  for d9 be ElementSUBSET-1M1-of D9 holds  for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for F be FunctionFUNCT-2M1-of([:ZFMISC-1K2 D,D9 :],E) holds F .:FINSEQOPK1\<^bsub>(D,D9,E)\<^esub>(i |->FINSEQ-2K5\<^bsub>(D)\<^esub> d,i |->FINSEQ-2K5\<^bsub>(D9)\<^esub> d9) =RELSET-1R2\<^bsub>(omegaORDINAL1K4,E)\<^esub> i |->FINSEQ-2K5\<^bsub>(E)\<^esub> F .BINOP-1K2\<^bsub>(D,D9,E)\<^esub>(d,d9)"
sorry

mtheorem finseqop_th_18:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D9 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for E be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d be ElementSUBSET-1M1-of D holds  for d9 be ElementSUBSET-1M1-of D9 holds  for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for F be FunctionFUNCT-2M1-of([:ZFMISC-1K2 D,D9 :],E) holds F [;]FINSEQOPK3\<^bsub>(D,D9,E)\<^esub>(d,i |->FINSEQ-2K5\<^bsub>(D9)\<^esub> d9) =RELSET-1R2\<^bsub>(omegaORDINAL1K4,E)\<^esub> i |->FINSEQ-2K5\<^bsub>(E)\<^esub> F .BINOP-1K2\<^bsub>(D,D9,E)\<^esub>(d,d9)"
sorry

mtheorem finseqop_th_19:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D9 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for E be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d be ElementSUBSET-1M1-of D holds  for d9 be ElementSUBSET-1M1-of D9 holds  for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for F be FunctionFUNCT-2M1-of([:ZFMISC-1K2 D,D9 :],E) holds F [:]FINSEQOPK2\<^bsub>(D,D9,E)\<^esub>(i |->FINSEQ-2K5\<^bsub>(D)\<^esub> d,d9) =RELSET-1R2\<^bsub>(omegaORDINAL1K4,E)\<^esub> i |->FINSEQ-2K5\<^bsub>(E)\<^esub> F .BINOP-1K2\<^bsub>(D,D9,E)\<^esub>(d,d9)"
sorry

mtheorem finseqop_th_20:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D9 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for E be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d be ElementSUBSET-1M1-of D holds  for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for F be FunctionFUNCT-2M1-of([:ZFMISC-1K2 D,D9 :],E) holds  for T9 be TupleFINSEQ-2M3-of(i,D9) holds F .:FINSEQOPK1\<^bsub>(D,D9,E)\<^esub>(i |->FINSEQ-2K5\<^bsub>(D)\<^esub> d,T9) =RELSET-1R2\<^bsub>(omegaORDINAL1K4,E)\<^esub> F [;]FINSEQOPK3\<^bsub>(D,D9,E)\<^esub>(d,T9)"
sorry

mtheorem finseqop_th_21:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D9 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for E be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d be ElementSUBSET-1M1-of D holds  for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for F be FunctionFUNCT-2M1-of([:ZFMISC-1K2 D,D9 :],E) holds  for T be TupleFINSEQ-2M3-of(i,D) holds F .:FUNCOP-1K3(T,i |->FINSEQ-2K5\<^bsub>(D)\<^esub> d) =FUNCT-1R1 F [:]FUNCOP-1K4(T,d)"
sorry

mtheorem finseqop_th_22:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D9 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for E be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d be ElementSUBSET-1M1-of D holds  for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for F be FunctionFUNCT-2M1-of([:ZFMISC-1K2 D,D9 :],E) holds  for T9 be TupleFINSEQ-2M3-of(i,D9) holds F [;]FINSEQOPK3\<^bsub>(D,D9,E)\<^esub>(d,T9) =FUNCT-1R1 F [;]FUNCOP-1K5(d,idPARTFUN1K6 D9) *FUNCT-1K3 T9"
sorry

mtheorem finseqop_th_23:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D9 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for E be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d be ElementSUBSET-1M1-of D holds  for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for F be FunctionFUNCT-2M1-of([:ZFMISC-1K2 D,D9 :],E) holds  for T be TupleFINSEQ-2M3-of(i,D) holds F [:]FUNCOP-1K4(T,d) =FUNCT-1R1 F [:]FUNCOP-1K4(idPARTFUN1K6 D,d) *FUNCT-1K3 T"
sorry

reserve F, G for "BinOpBINOP-1M2-of D"
reserve u for "UnOpBINOP-1M1-of D"
reserve H for "BinOpBINOP-1M2-of E"
mlemma finseqop_lm_4:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for T be TupleFINSEQ-2M3-of(i,D) holds T be FunctionFUNCT-2M1-of(SegFINSEQ-1K1 i,D)"
sorry

mtheorem finseqop_th_24:
" for C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d be ElementSUBSET-1M1-of D holds  for f be FunctionFUNCT-2M1-of(C,D) holds  for f9 be FunctionFUNCT-2M1-of(C,D) holds  for F be BinOpBINOP-1M2-of D holds F be associativeBINOP-1V2\<^bsub>(D)\<^esub> implies F [;]FUNCOP-1K10\<^bsub>(D,D)\<^esub>(d,idPARTFUN1K6 D) *PARTFUN1K1\<^bsub>(C,D,D,D)\<^esub> F .:FUNCOP-1K6\<^bsub>(D,C)\<^esub>(f,f9) =FUNCT-2R2\<^bsub>(C,D)\<^esub> F .:FUNCOP-1K6\<^bsub>(D,C)\<^esub>(F [;]FUNCOP-1K10\<^bsub>(D,D)\<^esub>(d,idPARTFUN1K6 D) *PARTFUN1K1\<^bsub>(C,D,D,D)\<^esub> f,f9)"
sorry

mtheorem finseqop_th_25:
" for C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d be ElementSUBSET-1M1-of D holds  for f be FunctionFUNCT-2M1-of(C,D) holds  for f9 be FunctionFUNCT-2M1-of(C,D) holds  for F be BinOpBINOP-1M2-of D holds F be associativeBINOP-1V2\<^bsub>(D)\<^esub> implies F [:]FUNCOP-1K9\<^bsub>(D,D)\<^esub>(idPARTFUN1K6 D,d) *PARTFUN1K1\<^bsub>(C,D,D,D)\<^esub> F .:FUNCOP-1K6\<^bsub>(D,C)\<^esub>(f,f9) =FUNCT-2R2\<^bsub>(C,D)\<^esub> F .:FUNCOP-1K6\<^bsub>(D,C)\<^esub>(f,F [:]FUNCOP-1K9\<^bsub>(D,D)\<^esub>(idPARTFUN1K6 D,d) *PARTFUN1K1\<^bsub>(C,D,D,D)\<^esub> f9)"
sorry

mtheorem finseqop_th_26:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d be ElementSUBSET-1M1-of D holds  for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for T1 be TupleFINSEQ-2M3-of(i,D) holds  for T2 be TupleFINSEQ-2M3-of(i,D) holds  for F be BinOpBINOP-1M2-of D holds F be associativeBINOP-1V2\<^bsub>(D)\<^esub> implies F [;]FUNCOP-1K10\<^bsub>(D,D)\<^esub>(d,idPARTFUN1K6 D) *FINSEQOPK4\<^bsub>(D,D)\<^esub> F .:FINSEQOPK1\<^bsub>(D,D,D)\<^esub>(T1,T2) =RELSET-1R2\<^bsub>(omegaORDINAL1K4,D)\<^esub> F .:FINSEQOPK1\<^bsub>(D,D,D)\<^esub>(F [;]FUNCOP-1K10\<^bsub>(D,D)\<^esub>(d,idPARTFUN1K6 D) *FINSEQOPK4\<^bsub>(D,D)\<^esub> T1,T2)"
sorry

mtheorem finseqop_th_27:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d be ElementSUBSET-1M1-of D holds  for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for T1 be TupleFINSEQ-2M3-of(i,D) holds  for T2 be TupleFINSEQ-2M3-of(i,D) holds  for F be BinOpBINOP-1M2-of D holds F be associativeBINOP-1V2\<^bsub>(D)\<^esub> implies F [:]FUNCOP-1K9\<^bsub>(D,D)\<^esub>(idPARTFUN1K6 D,d) *FINSEQOPK4\<^bsub>(D,D)\<^esub> F .:FINSEQOPK1\<^bsub>(D,D,D)\<^esub>(T1,T2) =RELSET-1R2\<^bsub>(omegaORDINAL1K4,D)\<^esub> F .:FINSEQOPK1\<^bsub>(D,D,D)\<^esub>(T1,F [:]FUNCOP-1K9\<^bsub>(D,D)\<^esub>(idPARTFUN1K6 D,d) *FINSEQOPK4\<^bsub>(D,D)\<^esub> T2)"
sorry

mtheorem finseqop_th_28:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for T1 be TupleFINSEQ-2M3-of(i,D) holds  for T2 be TupleFINSEQ-2M3-of(i,D) holds  for T3 be TupleFINSEQ-2M3-of(i,D) holds  for F be BinOpBINOP-1M2-of D holds F be associativeBINOP-1V2\<^bsub>(D)\<^esub> implies F .:FINSEQOPK1\<^bsub>(D,D,D)\<^esub>(F .:FINSEQOPK1\<^bsub>(D,D,D)\<^esub>(T1,T2),T3) =RELSET-1R2\<^bsub>(omegaORDINAL1K4,D)\<^esub> F .:FINSEQOPK1\<^bsub>(D,D,D)\<^esub>(T1,F .:FINSEQOPK1\<^bsub>(D,D,D)\<^esub>(T2,T3))"
sorry

mtheorem finseqop_th_29:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d1 be ElementSUBSET-1M1-of D holds  for d2 be ElementSUBSET-1M1-of D holds  for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for T be TupleFINSEQ-2M3-of(i,D) holds  for F be BinOpBINOP-1M2-of D holds F be associativeBINOP-1V2\<^bsub>(D)\<^esub> implies F [:]FINSEQOPK2\<^bsub>(D,D,D)\<^esub>(F [;]FINSEQOPK3\<^bsub>(D,D,D)\<^esub>(d1,T),d2) =RELSET-1R2\<^bsub>(omegaORDINAL1K4,D)\<^esub> F [;]FINSEQOPK3\<^bsub>(D,D,D)\<^esub>(d1,F [:]FINSEQOPK2\<^bsub>(D,D,D)\<^esub>(T,d2))"
sorry

mtheorem finseqop_th_30:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d be ElementSUBSET-1M1-of D holds  for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for T1 be TupleFINSEQ-2M3-of(i,D) holds  for T2 be TupleFINSEQ-2M3-of(i,D) holds  for F be BinOpBINOP-1M2-of D holds F be associativeBINOP-1V2\<^bsub>(D)\<^esub> implies F .:FINSEQOPK1\<^bsub>(D,D,D)\<^esub>(F [:]FINSEQOPK2\<^bsub>(D,D,D)\<^esub>(T1,d),T2) =RELSET-1R2\<^bsub>(omegaORDINAL1K4,D)\<^esub> F .:FINSEQOPK1\<^bsub>(D,D,D)\<^esub>(T1,F [;]FINSEQOPK3\<^bsub>(D,D,D)\<^esub>(d,T2))"
sorry

mtheorem finseqop_th_31:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d1 be ElementSUBSET-1M1-of D holds  for d2 be ElementSUBSET-1M1-of D holds  for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for T be TupleFINSEQ-2M3-of(i,D) holds  for F be BinOpBINOP-1M2-of D holds F be associativeBINOP-1V2\<^bsub>(D)\<^esub> implies F [;]FINSEQOPK3\<^bsub>(D,D,D)\<^esub>(F .BINOP-1K4\<^bsub>(D)\<^esub>(d1,d2),T) =RELSET-1R2\<^bsub>(omegaORDINAL1K4,D)\<^esub> F [;]FINSEQOPK3\<^bsub>(D,D,D)\<^esub>(d1,F [;]FINSEQOPK3\<^bsub>(D,D,D)\<^esub>(d2,T))"
sorry

mtheorem finseqop_th_32:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d1 be ElementSUBSET-1M1-of D holds  for d2 be ElementSUBSET-1M1-of D holds  for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for T be TupleFINSEQ-2M3-of(i,D) holds  for F be BinOpBINOP-1M2-of D holds F be associativeBINOP-1V2\<^bsub>(D)\<^esub> implies F [:]FINSEQOPK2\<^bsub>(D,D,D)\<^esub>(T,F .BINOP-1K4\<^bsub>(D)\<^esub>(d1,d2)) =RELSET-1R2\<^bsub>(omegaORDINAL1K4,D)\<^esub> F [:]FINSEQOPK2\<^bsub>(D,D,D)\<^esub>(F [:]FINSEQOPK2\<^bsub>(D,D,D)\<^esub>(T,d1),d2)"
sorry

mtheorem finseqop_th_33:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for T1 be TupleFINSEQ-2M3-of(i,D) holds  for T2 be TupleFINSEQ-2M3-of(i,D) holds  for F be BinOpBINOP-1M2-of D holds F be commutativeBINOP-1V1\<^bsub>(D)\<^esub> implies F .:FINSEQOPK1\<^bsub>(D,D,D)\<^esub>(T1,T2) =RELSET-1R2\<^bsub>(omegaORDINAL1K4,D)\<^esub> F .:FINSEQOPK1\<^bsub>(D,D,D)\<^esub>(T2,T1)"
sorry

mtheorem finseqop_th_34:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d be ElementSUBSET-1M1-of D holds  for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for T be TupleFINSEQ-2M3-of(i,D) holds  for F be BinOpBINOP-1M2-of D holds F be commutativeBINOP-1V1\<^bsub>(D)\<^esub> implies F [;]FINSEQOPK3\<^bsub>(D,D,D)\<^esub>(d,T) =RELSET-1R2\<^bsub>(omegaORDINAL1K4,D)\<^esub> F [:]FINSEQOPK2\<^bsub>(D,D,D)\<^esub>(T,d)"
sorry

mtheorem finseqop_th_35:
" for C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d1 be ElementSUBSET-1M1-of D holds  for d2 be ElementSUBSET-1M1-of D holds  for f be FunctionFUNCT-2M1-of(C,D) holds  for F be BinOpBINOP-1M2-of D holds  for G be BinOpBINOP-1M2-of D holds F is-distributive-wrtBINOP-1R6\<^bsub>(D)\<^esub> G implies F [;]FUNCOP-1K10\<^bsub>(D,C)\<^esub>(G .BINOP-1K4\<^bsub>(D)\<^esub>(d1,d2),f) =FUNCT-2R2\<^bsub>(C,D)\<^esub> G .:FUNCOP-1K6\<^bsub>(D,C)\<^esub>(F [;]FUNCOP-1K10\<^bsub>(D,C)\<^esub>(d1,f),F [;]FUNCOP-1K10\<^bsub>(D,C)\<^esub>(d2,f))"
sorry

mtheorem finseqop_th_36:
" for C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d1 be ElementSUBSET-1M1-of D holds  for d2 be ElementSUBSET-1M1-of D holds  for f be FunctionFUNCT-2M1-of(C,D) holds  for F be BinOpBINOP-1M2-of D holds  for G be BinOpBINOP-1M2-of D holds F is-distributive-wrtBINOP-1R6\<^bsub>(D)\<^esub> G implies F [:]FUNCOP-1K9\<^bsub>(D,C)\<^esub>(f,G .BINOP-1K4\<^bsub>(D)\<^esub>(d1,d2)) =FUNCT-2R2\<^bsub>(C,D)\<^esub> G .:FUNCOP-1K6\<^bsub>(D,C)\<^esub>(F [:]FUNCOP-1K9\<^bsub>(D,C)\<^esub>(f,d1),F [:]FUNCOP-1K9\<^bsub>(D,C)\<^esub>(f,d2))"
sorry

mtheorem finseqop_th_37:
" for C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for E be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(C,D) holds  for f9 be FunctionFUNCT-2M1-of(C,D) holds  for h be FunctionFUNCT-2M1-of(D,E) holds  for F be BinOpBINOP-1M2-of D holds  for H be BinOpBINOP-1M2-of E holds ( for d1 be ElementSUBSET-1M1-of D holds  for d2 be ElementSUBSET-1M1-of D holds h .FUNCT-2K3\<^bsub>(D,E)\<^esub> (F .BINOP-1K4\<^bsub>(D)\<^esub>(d1,d2)) =XBOOLE-0R4 H .BINOP-1K4\<^bsub>(E)\<^esub>(h .FUNCT-2K3\<^bsub>(D,E)\<^esub> d1,h .FUNCT-2K3\<^bsub>(D,E)\<^esub> d2)) implies h *PARTFUN1K1\<^bsub>(C,D,D,E)\<^esub> F .:FUNCOP-1K6\<^bsub>(D,C)\<^esub>(f,f9) =FUNCT-2R2\<^bsub>(C,E)\<^esub> H .:FUNCOP-1K6\<^bsub>(E,C)\<^esub>(h *PARTFUN1K1\<^bsub>(C,D,D,E)\<^esub> f,h *PARTFUN1K1\<^bsub>(C,D,D,E)\<^esub> f9)"
sorry

mtheorem finseqop_th_38:
" for C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for E be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d be ElementSUBSET-1M1-of D holds  for f be FunctionFUNCT-2M1-of(C,D) holds  for h be FunctionFUNCT-2M1-of(D,E) holds  for F be BinOpBINOP-1M2-of D holds  for H be BinOpBINOP-1M2-of E holds ( for d1 be ElementSUBSET-1M1-of D holds  for d2 be ElementSUBSET-1M1-of D holds h .FUNCT-2K3\<^bsub>(D,E)\<^esub> (F .BINOP-1K4\<^bsub>(D)\<^esub>(d1,d2)) =XBOOLE-0R4 H .BINOP-1K4\<^bsub>(E)\<^esub>(h .FUNCT-2K3\<^bsub>(D,E)\<^esub> d1,h .FUNCT-2K3\<^bsub>(D,E)\<^esub> d2)) implies h *PARTFUN1K1\<^bsub>(C,D,D,E)\<^esub> F [;]FUNCOP-1K10\<^bsub>(D,C)\<^esub>(d,f) =FUNCT-2R2\<^bsub>(C,E)\<^esub> H [;]FUNCOP-1K10\<^bsub>(E,C)\<^esub>(h .FUNCT-2K3\<^bsub>(D,E)\<^esub> d,h *PARTFUN1K1\<^bsub>(C,D,D,E)\<^esub> f)"
sorry

mtheorem finseqop_th_39:
" for C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for E be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d be ElementSUBSET-1M1-of D holds  for f be FunctionFUNCT-2M1-of(C,D) holds  for h be FunctionFUNCT-2M1-of(D,E) holds  for F be BinOpBINOP-1M2-of D holds  for H be BinOpBINOP-1M2-of E holds ( for d1 be ElementSUBSET-1M1-of D holds  for d2 be ElementSUBSET-1M1-of D holds h .FUNCT-2K3\<^bsub>(D,E)\<^esub> (F .BINOP-1K4\<^bsub>(D)\<^esub>(d1,d2)) =XBOOLE-0R4 H .BINOP-1K4\<^bsub>(E)\<^esub>(h .FUNCT-2K3\<^bsub>(D,E)\<^esub> d1,h .FUNCT-2K3\<^bsub>(D,E)\<^esub> d2)) implies h *PARTFUN1K1\<^bsub>(C,D,D,E)\<^esub> F [:]FUNCOP-1K9\<^bsub>(D,C)\<^esub>(f,d) =FUNCT-2R2\<^bsub>(C,E)\<^esub> H [:]FUNCOP-1K9\<^bsub>(E,C)\<^esub>(h *PARTFUN1K1\<^bsub>(C,D,D,E)\<^esub> f,h .FUNCT-2K3\<^bsub>(D,E)\<^esub> d)"
sorry

mtheorem finseqop_th_40:
" for C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(C,D) holds  for f9 be FunctionFUNCT-2M1-of(C,D) holds  for F be BinOpBINOP-1M2-of D holds  for u be UnOpBINOP-1M1-of D holds u is-distributive-wrtBINOP-1R12\<^bsub>(D)\<^esub> F implies u *PARTFUN1K1\<^bsub>(C,D,D,D)\<^esub> F .:FUNCOP-1K6\<^bsub>(D,C)\<^esub>(f,f9) =FUNCT-2R2\<^bsub>(C,D)\<^esub> F .:FUNCOP-1K6\<^bsub>(D,C)\<^esub>(u *PARTFUN1K1\<^bsub>(C,D,D,D)\<^esub> f,u *PARTFUN1K1\<^bsub>(C,D,D,D)\<^esub> f9)"
  using finseqop_th_37 sorry

mtheorem finseqop_th_41:
" for C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d be ElementSUBSET-1M1-of D holds  for f be FunctionFUNCT-2M1-of(C,D) holds  for F be BinOpBINOP-1M2-of D holds  for u be UnOpBINOP-1M1-of D holds u is-distributive-wrtBINOP-1R12\<^bsub>(D)\<^esub> F implies u *PARTFUN1K1\<^bsub>(C,D,D,D)\<^esub> F [;]FUNCOP-1K10\<^bsub>(D,C)\<^esub>(d,f) =FUNCT-2R2\<^bsub>(C,D)\<^esub> F [;]FUNCOP-1K10\<^bsub>(D,C)\<^esub>(u .FUNCT-2K3\<^bsub>(D,D)\<^esub> d,u *PARTFUN1K1\<^bsub>(C,D,D,D)\<^esub> f)"
  using finseqop_th_38 sorry

mtheorem finseqop_th_42:
" for C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d be ElementSUBSET-1M1-of D holds  for f be FunctionFUNCT-2M1-of(C,D) holds  for F be BinOpBINOP-1M2-of D holds  for u be UnOpBINOP-1M1-of D holds u is-distributive-wrtBINOP-1R12\<^bsub>(D)\<^esub> F implies u *PARTFUN1K1\<^bsub>(C,D,D,D)\<^esub> F [:]FUNCOP-1K9\<^bsub>(D,C)\<^esub>(f,d) =FUNCT-2R2\<^bsub>(C,D)\<^esub> F [:]FUNCOP-1K9\<^bsub>(D,C)\<^esub>(u *PARTFUN1K1\<^bsub>(C,D,D,D)\<^esub> f,u .FUNCT-2K3\<^bsub>(D,D)\<^esub> d)"
  using finseqop_th_39 sorry

mtheorem finseqop_th_43:
" for C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(C,D) holds  for F be BinOpBINOP-1M2-of D holds F be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> implies F .:FUNCOP-1K6\<^bsub>(D,C)\<^esub>(C -->FUNCOP-1K8\<^bsub>(D)\<^esub> the-unity-wrtBINOP-1K3\<^bsub>(D)\<^esub> F,f) =FUNCT-2R2\<^bsub>(C,D)\<^esub> f & F .:FUNCOP-1K6\<^bsub>(D,C)\<^esub>(f,C -->FUNCOP-1K8\<^bsub>(D)\<^esub> the-unity-wrtBINOP-1K3\<^bsub>(D)\<^esub> F) =FUNCT-2R2\<^bsub>(C,D)\<^esub> f"
sorry

mtheorem finseqop_th_44:
" for C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(C,D) holds  for F be BinOpBINOP-1M2-of D holds F be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> implies F [;]FUNCOP-1K10\<^bsub>(D,C)\<^esub>(the-unity-wrtBINOP-1K3\<^bsub>(D)\<^esub> F,f) =FUNCT-2R2\<^bsub>(C,D)\<^esub> f"
sorry

mtheorem finseqop_th_45:
" for C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(C,D) holds  for F be BinOpBINOP-1M2-of D holds F be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> implies F [:]FUNCOP-1K9\<^bsub>(D,C)\<^esub>(f,the-unity-wrtBINOP-1K3\<^bsub>(D)\<^esub> F) =FUNCT-2R2\<^bsub>(C,D)\<^esub> f"
sorry

mtheorem finseqop_th_46:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d1 be ElementSUBSET-1M1-of D holds  for d2 be ElementSUBSET-1M1-of D holds  for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for T be TupleFINSEQ-2M3-of(i,D) holds  for F be BinOpBINOP-1M2-of D holds  for G be BinOpBINOP-1M2-of D holds F is-distributive-wrtBINOP-1R6\<^bsub>(D)\<^esub> G implies F [;]FINSEQOPK3\<^bsub>(D,D,D)\<^esub>(G .BINOP-1K4\<^bsub>(D)\<^esub>(d1,d2),T) =RELSET-1R2\<^bsub>(omegaORDINAL1K4,D)\<^esub> G .:FINSEQOPK1\<^bsub>(D,D,D)\<^esub>(F [;]FINSEQOPK3\<^bsub>(D,D,D)\<^esub>(d1,T),F [;]FINSEQOPK3\<^bsub>(D,D,D)\<^esub>(d2,T))"
sorry

mtheorem finseqop_th_47:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d1 be ElementSUBSET-1M1-of D holds  for d2 be ElementSUBSET-1M1-of D holds  for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for T be TupleFINSEQ-2M3-of(i,D) holds  for F be BinOpBINOP-1M2-of D holds  for G be BinOpBINOP-1M2-of D holds F is-distributive-wrtBINOP-1R6\<^bsub>(D)\<^esub> G implies F [:]FINSEQOPK2\<^bsub>(D,D,D)\<^esub>(T,G .BINOP-1K4\<^bsub>(D)\<^esub>(d1,d2)) =RELSET-1R2\<^bsub>(omegaORDINAL1K4,D)\<^esub> G .:FINSEQOPK1\<^bsub>(D,D,D)\<^esub>(F [:]FINSEQOPK2\<^bsub>(D,D,D)\<^esub>(T,d1),F [:]FINSEQOPK2\<^bsub>(D,D,D)\<^esub>(T,d2))"
sorry

mtheorem finseqop_th_48:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for E be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for h be FunctionFUNCT-2M1-of(D,E) holds  for T1 be TupleFINSEQ-2M3-of(i,D) holds  for T2 be TupleFINSEQ-2M3-of(i,D) holds  for F be BinOpBINOP-1M2-of D holds  for H be BinOpBINOP-1M2-of E holds ( for d1 be ElementSUBSET-1M1-of D holds  for d2 be ElementSUBSET-1M1-of D holds h .FUNCT-2K3\<^bsub>(D,E)\<^esub> (F .BINOP-1K4\<^bsub>(D)\<^esub>(d1,d2)) =XBOOLE-0R4 H .BINOP-1K4\<^bsub>(E)\<^esub>(h .FUNCT-2K3\<^bsub>(D,E)\<^esub> d1,h .FUNCT-2K3\<^bsub>(D,E)\<^esub> d2)) implies h *FINSEQOPK4\<^bsub>(D,E)\<^esub> F .:FINSEQOPK1\<^bsub>(D,D,D)\<^esub>(T1,T2) =RELSET-1R2\<^bsub>(omegaORDINAL1K4,E)\<^esub> H .:FINSEQOPK1\<^bsub>(E,E,E)\<^esub>(h *FINSEQOPK4\<^bsub>(D,E)\<^esub> T1,h *FINSEQOPK4\<^bsub>(D,E)\<^esub> T2)"
sorry

mtheorem finseqop_th_49:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for E be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d be ElementSUBSET-1M1-of D holds  for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for h be FunctionFUNCT-2M1-of(D,E) holds  for T be TupleFINSEQ-2M3-of(i,D) holds  for F be BinOpBINOP-1M2-of D holds  for H be BinOpBINOP-1M2-of E holds ( for d1 be ElementSUBSET-1M1-of D holds  for d2 be ElementSUBSET-1M1-of D holds h .FUNCT-2K3\<^bsub>(D,E)\<^esub> (F .BINOP-1K4\<^bsub>(D)\<^esub>(d1,d2)) =XBOOLE-0R4 H .BINOP-1K4\<^bsub>(E)\<^esub>(h .FUNCT-2K3\<^bsub>(D,E)\<^esub> d1,h .FUNCT-2K3\<^bsub>(D,E)\<^esub> d2)) implies h *FINSEQOPK4\<^bsub>(D,E)\<^esub> F [;]FINSEQOPK3\<^bsub>(D,D,D)\<^esub>(d,T) =RELSET-1R2\<^bsub>(omegaORDINAL1K4,E)\<^esub> H [;]FINSEQOPK3\<^bsub>(E,E,E)\<^esub>(h .FUNCT-2K3\<^bsub>(D,E)\<^esub> d,h *FINSEQOPK4\<^bsub>(D,E)\<^esub> T)"
sorry

mtheorem finseqop_th_50:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for E be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d be ElementSUBSET-1M1-of D holds  for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for h be FunctionFUNCT-2M1-of(D,E) holds  for T be TupleFINSEQ-2M3-of(i,D) holds  for F be BinOpBINOP-1M2-of D holds  for H be BinOpBINOP-1M2-of E holds ( for d1 be ElementSUBSET-1M1-of D holds  for d2 be ElementSUBSET-1M1-of D holds h .FUNCT-2K3\<^bsub>(D,E)\<^esub> (F .BINOP-1K4\<^bsub>(D)\<^esub>(d1,d2)) =XBOOLE-0R4 H .BINOP-1K4\<^bsub>(E)\<^esub>(h .FUNCT-2K3\<^bsub>(D,E)\<^esub> d1,h .FUNCT-2K3\<^bsub>(D,E)\<^esub> d2)) implies h *FINSEQOPK4\<^bsub>(D,E)\<^esub> F [:]FINSEQOPK2\<^bsub>(D,D,D)\<^esub>(T,d) =RELSET-1R2\<^bsub>(omegaORDINAL1K4,E)\<^esub> H [:]FINSEQOPK2\<^bsub>(E,E,E)\<^esub>(h *FINSEQOPK4\<^bsub>(D,E)\<^esub> T,h .FUNCT-2K3\<^bsub>(D,E)\<^esub> d)"
sorry

mtheorem finseqop_th_51:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for T1 be TupleFINSEQ-2M3-of(i,D) holds  for T2 be TupleFINSEQ-2M3-of(i,D) holds  for F be BinOpBINOP-1M2-of D holds  for u be UnOpBINOP-1M1-of D holds u is-distributive-wrtBINOP-1R12\<^bsub>(D)\<^esub> F implies u *FINSEQOPK4\<^bsub>(D,D)\<^esub> F .:FINSEQOPK1\<^bsub>(D,D,D)\<^esub>(T1,T2) =RELSET-1R2\<^bsub>(omegaORDINAL1K4,D)\<^esub> F .:FINSEQOPK1\<^bsub>(D,D,D)\<^esub>(u *FINSEQOPK4\<^bsub>(D,D)\<^esub> T1,u *FINSEQOPK4\<^bsub>(D,D)\<^esub> T2)"
  using finseqop_th_48 sorry

mtheorem finseqop_th_52:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d be ElementSUBSET-1M1-of D holds  for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for T be TupleFINSEQ-2M3-of(i,D) holds  for F be BinOpBINOP-1M2-of D holds  for u be UnOpBINOP-1M1-of D holds u is-distributive-wrtBINOP-1R12\<^bsub>(D)\<^esub> F implies u *FINSEQOPK4\<^bsub>(D,D)\<^esub> F [;]FINSEQOPK3\<^bsub>(D,D,D)\<^esub>(d,T) =RELSET-1R2\<^bsub>(omegaORDINAL1K4,D)\<^esub> F [;]FINSEQOPK3\<^bsub>(D,D,D)\<^esub>(u .FUNCT-2K3\<^bsub>(D,D)\<^esub> d,u *FINSEQOPK4\<^bsub>(D,D)\<^esub> T)"
  using finseqop_th_49 sorry

mtheorem finseqop_th_53:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d be ElementSUBSET-1M1-of D holds  for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for T be TupleFINSEQ-2M3-of(i,D) holds  for F be BinOpBINOP-1M2-of D holds  for u be UnOpBINOP-1M1-of D holds u is-distributive-wrtBINOP-1R12\<^bsub>(D)\<^esub> F implies u *FINSEQOPK4\<^bsub>(D,D)\<^esub> F [:]FINSEQOPK2\<^bsub>(D,D,D)\<^esub>(T,d) =RELSET-1R2\<^bsub>(omegaORDINAL1K4,D)\<^esub> F [:]FINSEQOPK2\<^bsub>(D,D,D)\<^esub>(u *FINSEQOPK4\<^bsub>(D,D)\<^esub> T,u .FUNCT-2K3\<^bsub>(D,D)\<^esub> d)"
  using finseqop_th_50 sorry

mtheorem finseqop_th_54:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d be ElementSUBSET-1M1-of D holds  for F be BinOpBINOP-1M2-of D holds  for G be BinOpBINOP-1M2-of D holds  for u be UnOpBINOP-1M1-of D holds G is-distributive-wrtBINOP-1R6\<^bsub>(D)\<^esub> F & u =FUNCT-2R2\<^bsub>(D,D)\<^esub> G [;]FUNCOP-1K10\<^bsub>(D,D)\<^esub>(d,idPARTFUN1K6 D) implies u is-distributive-wrtBINOP-1R12\<^bsub>(D)\<^esub> F"
sorry

mtheorem finseqop_th_55:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d be ElementSUBSET-1M1-of D holds  for F be BinOpBINOP-1M2-of D holds  for G be BinOpBINOP-1M2-of D holds  for u be UnOpBINOP-1M1-of D holds G is-distributive-wrtBINOP-1R6\<^bsub>(D)\<^esub> F & u =FUNCT-2R2\<^bsub>(D,D)\<^esub> G [:]FUNCOP-1K9\<^bsub>(D,D)\<^esub>(idPARTFUN1K6 D,d) implies u is-distributive-wrtBINOP-1R12\<^bsub>(D)\<^esub> F"
sorry

mtheorem finseqop_th_56:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for T be TupleFINSEQ-2M3-of(i,D) holds  for F be BinOpBINOP-1M2-of D holds F be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> implies F .:FINSEQOPK1\<^bsub>(D,D,D)\<^esub>(i |->FINSEQ-2K5\<^bsub>(D)\<^esub> the-unity-wrtBINOP-1K3\<^bsub>(D)\<^esub> F,T) =RELSET-1R2\<^bsub>(omegaORDINAL1K4,D)\<^esub> T & F .:FINSEQOPK1\<^bsub>(D,D,D)\<^esub>(T,i |->FINSEQ-2K5\<^bsub>(D)\<^esub> the-unity-wrtBINOP-1K3\<^bsub>(D)\<^esub> F) =RELSET-1R2\<^bsub>(omegaORDINAL1K4,D)\<^esub> T"
sorry

mtheorem finseqop_th_57:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for T be TupleFINSEQ-2M3-of(i,D) holds  for F be BinOpBINOP-1M2-of D holds F be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> implies F [;]FINSEQOPK3\<^bsub>(D,D,D)\<^esub>(the-unity-wrtBINOP-1K3\<^bsub>(D)\<^esub> F,T) =RELSET-1R2\<^bsub>(omegaORDINAL1K4,D)\<^esub> T"
sorry

mtheorem finseqop_th_58:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for T be TupleFINSEQ-2M3-of(i,D) holds  for F be BinOpBINOP-1M2-of D holds F be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> implies F [:]FINSEQOPK2\<^bsub>(D,D,D)\<^esub>(T,the-unity-wrtBINOP-1K3\<^bsub>(D)\<^esub> F) =RELSET-1R2\<^bsub>(omegaORDINAL1K4,D)\<^esub> T"
sorry

mdef finseqop_def_1 (" _ is-an-inverseOp-wrtFINSEQOPR1\<^bsub>'( _ ')\<^esub>  _ " [50,0,50]50 ) where
  mlet "D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "u be UnOpBINOP-1M1-of D", "F be BinOpBINOP-1M2-of D"
"pred u is-an-inverseOp-wrtFINSEQOPR1\<^bsub>(D)\<^esub> F means
   for d be ElementSUBSET-1M1-of D holds F .BINOP-1K4\<^bsub>(D)\<^esub>(d,u .FUNCT-2K3\<^bsub>(D,D)\<^esub> d) =XBOOLE-0R4 the-unity-wrtBINOP-1K3\<^bsub>(D)\<^esub> F & F .BINOP-1K4\<^bsub>(D)\<^esub>(u .FUNCT-2K3\<^bsub>(D,D)\<^esub> d,d) =XBOOLE-0R4 the-unity-wrtBINOP-1K3\<^bsub>(D)\<^esub> F"..

mdef finseqop_def_2 ("having-an-inverseOpFINSEQOPV1\<^bsub>'( _ ')\<^esub>" [0]70 ) where
  mlet "D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
"attr having-an-inverseOpFINSEQOPV1\<^bsub>(D)\<^esub> for BinOpBINOP-1M2-of D means
  (\<lambda>F.  ex u be UnOpBINOP-1M1-of D st u is-an-inverseOp-wrtFINSEQOPR1\<^bsub>(D)\<^esub> F)"..

mdef finseqop_def_3 ("the-inverseOp-wrtFINSEQOPK5\<^bsub>'( _ ')\<^esub>  _ " [0,164]164 ) where
  mlet "D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "F be BinOpBINOP-1M2-of D"
"assume F be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> & (F be associativeBINOP-1V2\<^bsub>(D)\<^esub> & F be having-an-inverseOpFINSEQOPV1\<^bsub>(D)\<^esub>) func the-inverseOp-wrtFINSEQOPK5\<^bsub>(D)\<^esub> F \<rightarrow> UnOpBINOP-1M1-of D means
  \<lambda>it. it is-an-inverseOp-wrtFINSEQOPR1\<^bsub>(D)\<^esub> F"
proof-
  (*existence*)
    show "F be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> & (F be associativeBINOP-1V2\<^bsub>(D)\<^esub> & F be having-an-inverseOpFINSEQOPV1\<^bsub>(D)\<^esub>) implies ( ex it be UnOpBINOP-1M1-of D st it is-an-inverseOp-wrtFINSEQOPR1\<^bsub>(D)\<^esub> F)"
sorry
  (*uniqueness*)
    show "F be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> & (F be associativeBINOP-1V2\<^bsub>(D)\<^esub> & F be having-an-inverseOpFINSEQOPV1\<^bsub>(D)\<^esub>) implies ( for it1 be UnOpBINOP-1M1-of D holds  for it2 be UnOpBINOP-1M1-of D holds it1 is-an-inverseOp-wrtFINSEQOPR1\<^bsub>(D)\<^esub> F & it2 is-an-inverseOp-wrtFINSEQOPR1\<^bsub>(D)\<^esub> F implies it1 =HIDDENR1 it2)"
sorry
qed "sorry"

mtheorem finseqop_th_59:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d be ElementSUBSET-1M1-of D holds  for F be BinOpBINOP-1M2-of D holds (F be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> & F be associativeBINOP-1V2\<^bsub>(D)\<^esub>) & F be having-an-inverseOpFINSEQOPV1\<^bsub>(D)\<^esub> implies F .BINOP-1K4\<^bsub>(D)\<^esub>((the-inverseOp-wrtFINSEQOPK5\<^bsub>(D)\<^esub> F).FUNCT-2K3\<^bsub>(D,D)\<^esub> d,d) =XBOOLE-0R4 the-unity-wrtBINOP-1K3\<^bsub>(D)\<^esub> F & F .BINOP-1K4\<^bsub>(D)\<^esub>(d,(the-inverseOp-wrtFINSEQOPK5\<^bsub>(D)\<^esub> F).FUNCT-2K3\<^bsub>(D,D)\<^esub> d) =XBOOLE-0R4 the-unity-wrtBINOP-1K3\<^bsub>(D)\<^esub> F"
sorry

mtheorem finseqop_th_60:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d1 be ElementSUBSET-1M1-of D holds  for d2 be ElementSUBSET-1M1-of D holds  for F be BinOpBINOP-1M2-of D holds ((F be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> & F be associativeBINOP-1V2\<^bsub>(D)\<^esub>) & F be having-an-inverseOpFINSEQOPV1\<^bsub>(D)\<^esub>) & F .BINOP-1K4\<^bsub>(D)\<^esub>(d1,d2) =XBOOLE-0R4 the-unity-wrtBINOP-1K3\<^bsub>(D)\<^esub> F implies d1 =XBOOLE-0R4 (the-inverseOp-wrtFINSEQOPK5\<^bsub>(D)\<^esub> F).FUNCT-2K3\<^bsub>(D,D)\<^esub> d2 & (the-inverseOp-wrtFINSEQOPK5\<^bsub>(D)\<^esub> F).FUNCT-2K3\<^bsub>(D,D)\<^esub> d1 =XBOOLE-0R4 d2"
sorry

mtheorem finseqop_th_61:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for F be BinOpBINOP-1M2-of D holds (F be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> & F be associativeBINOP-1V2\<^bsub>(D)\<^esub>) & F be having-an-inverseOpFINSEQOPV1\<^bsub>(D)\<^esub> implies (the-inverseOp-wrtFINSEQOPK5\<^bsub>(D)\<^esub> F).FUNCT-2K3\<^bsub>(D,D)\<^esub> the-unity-wrtBINOP-1K3\<^bsub>(D)\<^esub> F =XBOOLE-0R4 the-unity-wrtBINOP-1K3\<^bsub>(D)\<^esub> F"
sorry

mtheorem finseqop_th_62:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d be ElementSUBSET-1M1-of D holds  for F be BinOpBINOP-1M2-of D holds (F be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> & F be associativeBINOP-1V2\<^bsub>(D)\<^esub>) & F be having-an-inverseOpFINSEQOPV1\<^bsub>(D)\<^esub> implies (the-inverseOp-wrtFINSEQOPK5\<^bsub>(D)\<^esub> F).FUNCT-2K3\<^bsub>(D,D)\<^esub> ((the-inverseOp-wrtFINSEQOPK5\<^bsub>(D)\<^esub> F).FUNCT-2K3\<^bsub>(D,D)\<^esub> d) =XBOOLE-0R4 d"
sorry

mtheorem finseqop_th_63:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for F be BinOpBINOP-1M2-of D holds ((F be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> & F be associativeBINOP-1V2\<^bsub>(D)\<^esub>) & F be commutativeBINOP-1V1\<^bsub>(D)\<^esub>) & F be having-an-inverseOpFINSEQOPV1\<^bsub>(D)\<^esub> implies the-inverseOp-wrtFINSEQOPK5\<^bsub>(D)\<^esub> F is-distributive-wrtBINOP-1R12\<^bsub>(D)\<^esub> F"
sorry

mtheorem finseqop_th_64:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d be ElementSUBSET-1M1-of D holds  for d1 be ElementSUBSET-1M1-of D holds  for d2 be ElementSUBSET-1M1-of D holds  for F be BinOpBINOP-1M2-of D holds ((F be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> & F be associativeBINOP-1V2\<^bsub>(D)\<^esub>) & F be having-an-inverseOpFINSEQOPV1\<^bsub>(D)\<^esub>) & (F .BINOP-1K4\<^bsub>(D)\<^esub>(d,d1) =XBOOLE-0R4 F .BINOP-1K4\<^bsub>(D)\<^esub>(d,d2) or F .BINOP-1K4\<^bsub>(D)\<^esub>(d1,d) =XBOOLE-0R4 F .BINOP-1K4\<^bsub>(D)\<^esub>(d2,d)) implies d1 =XBOOLE-0R4 d2"
sorry

mtheorem finseqop_th_65:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d1 be ElementSUBSET-1M1-of D holds  for d2 be ElementSUBSET-1M1-of D holds  for F be BinOpBINOP-1M2-of D holds ((F be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> & F be associativeBINOP-1V2\<^bsub>(D)\<^esub>) & F be having-an-inverseOpFINSEQOPV1\<^bsub>(D)\<^esub>) & (F .BINOP-1K4\<^bsub>(D)\<^esub>(d1,d2) =XBOOLE-0R4 d2 or F .BINOP-1K4\<^bsub>(D)\<^esub>(d2,d1) =XBOOLE-0R4 d2) implies d1 =XBOOLE-0R4 the-unity-wrtBINOP-1K3\<^bsub>(D)\<^esub> F"
sorry

mtheorem finseqop_th_66:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for e be ElementSUBSET-1M1-of D holds  for F be BinOpBINOP-1M2-of D holds  for G be BinOpBINOP-1M2-of D holds (((F be associativeBINOP-1V2\<^bsub>(D)\<^esub> & F be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub>) & F be having-an-inverseOpFINSEQOPV1\<^bsub>(D)\<^esub>) & G is-distributive-wrtBINOP-1R6\<^bsub>(D)\<^esub> F) & e =XBOOLE-0R4 the-unity-wrtBINOP-1K3\<^bsub>(D)\<^esub> F implies ( for d be ElementSUBSET-1M1-of D holds G .BINOP-1K4\<^bsub>(D)\<^esub>(e,d) =XBOOLE-0R4 e & G .BINOP-1K4\<^bsub>(D)\<^esub>(d,e) =XBOOLE-0R4 e)"
sorry

mtheorem finseqop_th_67:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d1 be ElementSUBSET-1M1-of D holds  for d2 be ElementSUBSET-1M1-of D holds  for F be BinOpBINOP-1M2-of D holds  for G be BinOpBINOP-1M2-of D holds  for u be UnOpBINOP-1M1-of D holds (((F be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> & F be associativeBINOP-1V2\<^bsub>(D)\<^esub>) & F be having-an-inverseOpFINSEQOPV1\<^bsub>(D)\<^esub>) & u =FUNCT-2R2\<^bsub>(D,D)\<^esub> the-inverseOp-wrtFINSEQOPK5\<^bsub>(D)\<^esub> F) & G is-distributive-wrtBINOP-1R6\<^bsub>(D)\<^esub> F implies u .FUNCT-2K3\<^bsub>(D,D)\<^esub> (G .BINOP-1K4\<^bsub>(D)\<^esub>(d1,d2)) =XBOOLE-0R4 G .BINOP-1K4\<^bsub>(D)\<^esub>(u .FUNCT-2K3\<^bsub>(D,D)\<^esub> d1,d2) & u .FUNCT-2K3\<^bsub>(D,D)\<^esub> (G .BINOP-1K4\<^bsub>(D)\<^esub>(d1,d2)) =XBOOLE-0R4 G .BINOP-1K4\<^bsub>(D)\<^esub>(d1,u .FUNCT-2K3\<^bsub>(D,D)\<^esub> d2)"
sorry

mtheorem finseqop_th_68:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for F be BinOpBINOP-1M2-of D holds  for G be BinOpBINOP-1M2-of D holds  for u be UnOpBINOP-1M1-of D holds ((((F be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> & F be associativeBINOP-1V2\<^bsub>(D)\<^esub>) & F be having-an-inverseOpFINSEQOPV1\<^bsub>(D)\<^esub>) & u =FUNCT-2R2\<^bsub>(D,D)\<^esub> the-inverseOp-wrtFINSEQOPK5\<^bsub>(D)\<^esub> F) & G is-distributive-wrtBINOP-1R6\<^bsub>(D)\<^esub> F) & G be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> implies G [;]FUNCOP-1K10\<^bsub>(D,D)\<^esub>(u .FUNCT-2K3\<^bsub>(D,D)\<^esub> the-unity-wrtBINOP-1K3\<^bsub>(D)\<^esub> G,idPARTFUN1K6 D) =FUNCT-2R2\<^bsub>(D,D)\<^esub> u"
sorry

mtheorem finseqop_th_69:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d be ElementSUBSET-1M1-of D holds  for F be BinOpBINOP-1M2-of D holds  for G be BinOpBINOP-1M2-of D holds ((F be associativeBINOP-1V2\<^bsub>(D)\<^esub> & F be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub>) & F be having-an-inverseOpFINSEQOPV1\<^bsub>(D)\<^esub>) & G is-distributive-wrtBINOP-1R6\<^bsub>(D)\<^esub> F implies (G [;]FUNCOP-1K10\<^bsub>(D,D)\<^esub>(d,idPARTFUN1K6 D)).FUNCT-2K3\<^bsub>(D,D)\<^esub> the-unity-wrtBINOP-1K3\<^bsub>(D)\<^esub> F =XBOOLE-0R4 the-unity-wrtBINOP-1K3\<^bsub>(D)\<^esub> F"
sorry

mtheorem finseqop_th_70:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d be ElementSUBSET-1M1-of D holds  for F be BinOpBINOP-1M2-of D holds  for G be BinOpBINOP-1M2-of D holds ((F be associativeBINOP-1V2\<^bsub>(D)\<^esub> & F be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub>) & F be having-an-inverseOpFINSEQOPV1\<^bsub>(D)\<^esub>) & G is-distributive-wrtBINOP-1R6\<^bsub>(D)\<^esub> F implies (G [:]FUNCOP-1K9\<^bsub>(D,D)\<^esub>(idPARTFUN1K6 D,d)).FUNCT-2K3\<^bsub>(D,D)\<^esub> the-unity-wrtBINOP-1K3\<^bsub>(D)\<^esub> F =XBOOLE-0R4 the-unity-wrtBINOP-1K3\<^bsub>(D)\<^esub> F"
sorry

mtheorem finseqop_th_71:
" for C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(C,D) holds  for F be BinOpBINOP-1M2-of D holds (F be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> & F be associativeBINOP-1V2\<^bsub>(D)\<^esub>) & F be having-an-inverseOpFINSEQOPV1\<^bsub>(D)\<^esub> implies F .:FUNCOP-1K6\<^bsub>(D,C)\<^esub>(f,(the-inverseOp-wrtFINSEQOPK5\<^bsub>(D)\<^esub> F)*PARTFUN1K1\<^bsub>(C,D,D,D)\<^esub> f) =FUNCT-2R2\<^bsub>(C,D)\<^esub> C -->FUNCOP-1K8\<^bsub>(D)\<^esub> the-unity-wrtBINOP-1K3\<^bsub>(D)\<^esub> F & F .:FUNCOP-1K6\<^bsub>(D,C)\<^esub>((the-inverseOp-wrtFINSEQOPK5\<^bsub>(D)\<^esub> F)*PARTFUN1K1\<^bsub>(C,D,D,D)\<^esub> f,f) =FUNCT-2R2\<^bsub>(C,D)\<^esub> C -->FUNCOP-1K8\<^bsub>(D)\<^esub> the-unity-wrtBINOP-1K3\<^bsub>(D)\<^esub> F"
sorry

mtheorem finseqop_th_72:
" for C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(C,D) holds  for f9 be FunctionFUNCT-2M1-of(C,D) holds  for F be BinOpBINOP-1M2-of D holds ((F be associativeBINOP-1V2\<^bsub>(D)\<^esub> & F be having-an-inverseOpFINSEQOPV1\<^bsub>(D)\<^esub>) & F be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub>) & F .:FUNCOP-1K6\<^bsub>(D,C)\<^esub>(f,f9) =FUNCT-2R2\<^bsub>(C,D)\<^esub> C -->FUNCOP-1K8\<^bsub>(D)\<^esub> the-unity-wrtBINOP-1K3\<^bsub>(D)\<^esub> F implies f =FUNCT-2R2\<^bsub>(C,D)\<^esub> (the-inverseOp-wrtFINSEQOPK5\<^bsub>(D)\<^esub> F)*PARTFUN1K1\<^bsub>(C,D,D,D)\<^esub> f9 & (the-inverseOp-wrtFINSEQOPK5\<^bsub>(D)\<^esub> F)*PARTFUN1K1\<^bsub>(C,D,D,D)\<^esub> f =FUNCT-2R2\<^bsub>(C,D)\<^esub> f9"
sorry

mtheorem finseqop_th_73:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for T be TupleFINSEQ-2M3-of(i,D) holds  for F be BinOpBINOP-1M2-of D holds (F be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> & F be associativeBINOP-1V2\<^bsub>(D)\<^esub>) & F be having-an-inverseOpFINSEQOPV1\<^bsub>(D)\<^esub> implies F .:FINSEQOPK1\<^bsub>(D,D,D)\<^esub>(T,(the-inverseOp-wrtFINSEQOPK5\<^bsub>(D)\<^esub> F)*FINSEQOPK4\<^bsub>(D,D)\<^esub> T) =RELSET-1R2\<^bsub>(omegaORDINAL1K4,D)\<^esub> i |->FINSEQ-2K5\<^bsub>(D)\<^esub> the-unity-wrtBINOP-1K3\<^bsub>(D)\<^esub> F & F .:FINSEQOPK1\<^bsub>(D,D,D)\<^esub>((the-inverseOp-wrtFINSEQOPK5\<^bsub>(D)\<^esub> F)*FINSEQOPK4\<^bsub>(D,D)\<^esub> T,T) =RELSET-1R2\<^bsub>(omegaORDINAL1K4,D)\<^esub> i |->FINSEQ-2K5\<^bsub>(D)\<^esub> the-unity-wrtBINOP-1K3\<^bsub>(D)\<^esub> F"
sorry

mtheorem finseqop_th_74:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for T1 be TupleFINSEQ-2M3-of(i,D) holds  for T2 be TupleFINSEQ-2M3-of(i,D) holds  for F be BinOpBINOP-1M2-of D holds ((F be associativeBINOP-1V2\<^bsub>(D)\<^esub> & F be having-an-inverseOpFINSEQOPV1\<^bsub>(D)\<^esub>) & F be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub>) & F .:FINSEQOPK1\<^bsub>(D,D,D)\<^esub>(T1,T2) =RELSET-1R2\<^bsub>(omegaORDINAL1K4,D)\<^esub> i |->FINSEQ-2K5\<^bsub>(D)\<^esub> the-unity-wrtBINOP-1K3\<^bsub>(D)\<^esub> F implies T1 =RELSET-1R2\<^bsub>(omegaORDINAL1K4,D)\<^esub> (the-inverseOp-wrtFINSEQOPK5\<^bsub>(D)\<^esub> F)*FINSEQOPK4\<^bsub>(D,D)\<^esub> T2 & (the-inverseOp-wrtFINSEQOPK5\<^bsub>(D)\<^esub> F)*FINSEQOPK4\<^bsub>(D,D)\<^esub> T1 =RELSET-1R2\<^bsub>(omegaORDINAL1K4,D)\<^esub> T2"
sorry

mtheorem finseqop_th_75:
" for C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for e be ElementSUBSET-1M1-of D holds  for f be FunctionFUNCT-2M1-of(C,D) holds  for F be BinOpBINOP-1M2-of D holds  for G be BinOpBINOP-1M2-of D holds (((F be associativeBINOP-1V2\<^bsub>(D)\<^esub> & F be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub>) & e =XBOOLE-0R4 the-unity-wrtBINOP-1K3\<^bsub>(D)\<^esub> F) & F be having-an-inverseOpFINSEQOPV1\<^bsub>(D)\<^esub>) & G is-distributive-wrtBINOP-1R6\<^bsub>(D)\<^esub> F implies G [;]FUNCOP-1K10\<^bsub>(D,C)\<^esub>(e,f) =FUNCT-2R2\<^bsub>(C,D)\<^esub> C -->FUNCOP-1K8\<^bsub>(D)\<^esub> e"
sorry

mtheorem finseqop_th_76:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for e be ElementSUBSET-1M1-of D holds  for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for T be TupleFINSEQ-2M3-of(i,D) holds  for F be BinOpBINOP-1M2-of D holds  for G be BinOpBINOP-1M2-of D holds (((F be associativeBINOP-1V2\<^bsub>(D)\<^esub> & F be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub>) & e =XBOOLE-0R4 the-unity-wrtBINOP-1K3\<^bsub>(D)\<^esub> F) & F be having-an-inverseOpFINSEQOPV1\<^bsub>(D)\<^esub>) & G is-distributive-wrtBINOP-1R6\<^bsub>(D)\<^esub> F implies G [;]FINSEQOPK3\<^bsub>(D,D,D)\<^esub>(e,T) =RELSET-1R2\<^bsub>(omegaORDINAL1K4,D)\<^esub> i |->FINSEQ-2K5\<^bsub>(D)\<^esub> e"
sorry

mdef finseqop_def_4 (" _ *FINSEQOPK6'( _ , _ ')" [164,0,0]164 ) where
  mlet "F be FunctionFUNCT-1M1", "f be FunctionFUNCT-1M1", "g be FunctionFUNCT-1M1"
"func F *FINSEQOPK6(f,g) \<rightarrow> FunctionFUNCT-1M1 equals
  F *FUNCT-1K3 ([:FUNCT-3K16 f,g :])"
proof-
  (*coherence*)
    show "F *FUNCT-1K3 ([:FUNCT-3K16 f,g :]) be FunctionFUNCT-1M1"
       sorry
qed "sorry"

mtheorem finseqop_th_77:
" for x be setHIDDENM2 holds  for y be setHIDDENM2 holds  for F be FunctionFUNCT-1M1 holds  for f be FunctionFUNCT-1M1 holds  for g be FunctionFUNCT-1M1 holds [TARSKIK4 x,y ] inHIDDENR3 domRELAT-1K1 (F *FINSEQOPK6(f,g)) implies (F *FINSEQOPK6(f,g)).BINOP-1K1(x,y) =XBOOLE-0R4 F .BINOP-1K1(f .FUNCT-1K1 x,g .FUNCT-1K1 y)"
sorry

(*\$CT*)
mtheorem finseqop_th_79:
" for C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for C9 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D9 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for E be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for F be FunctionFUNCT-2M1-of([:ZFMISC-1K2 D,D9 :],E) holds  for f be FunctionFUNCT-2M1-of(C,D) holds  for g be FunctionFUNCT-2M1-of(C9,D9) holds F *FINSEQOPK6(f,g) be FunctionFUNCT-2M1-of([:ZFMISC-1K2 C,C9 :],E)"
sorry

mtheorem finseqop_th_80:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for F be BinOpBINOP-1M2-of D holds  for u be FunctionFUNCT-2M1-of(D,D) holds  for u9 be FunctionFUNCT-2M1-of(D,D) holds F *FINSEQOPK6(u,u9) be BinOpBINOP-1M2-of D"
  using finseqop_th_79 sorry

syntax FINSEQOPK7 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ *FINSEQOPK7\<^bsub>'( _ ')\<^esub>'( _ , _ ')" [164,0,0,0]164)
translations "F *FINSEQOPK7\<^bsub>(D)\<^esub>(f,f9)" \<rightharpoonup> "F *FINSEQOPK6(f,f9)"

mtheorem finseqop_add_5:
  mlet "D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "F be BinOpBINOP-1M2-of D", "f be FunctionFUNCT-2M1-of(D,D)", "f9 be FunctionFUNCT-2M1-of(D,D)"
"cluster F *FINSEQOPK6(f,f9) as-term-is BinOpBINOP-1M2-of D"
proof
(*coherence*)
  show "F *FINSEQOPK6(f,f9) be BinOpBINOP-1M2-of D"
    using finseqop_th_79 sorry
qed "sorry"

mtheorem finseqop_th_81:
" for C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for C9 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D9 be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for E be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for c be ElementSUBSET-1M1-of C holds  for c9 be ElementSUBSET-1M1-of C9 holds  for F be FunctionFUNCT-2M1-of([:ZFMISC-1K2 D,D9 :],E) holds  for f be FunctionFUNCT-2M1-of(C,D) holds  for g be FunctionFUNCT-2M1-of(C9,D9) holds (F *FINSEQOPK6(f,g)).BINOP-1K1(c,c9) =XBOOLE-0R4 F .BINOP-1K2\<^bsub>(D,D9,E)\<^esub>(f .FUNCT-2K3\<^bsub>(C,D)\<^esub> c,g .FUNCT-2K3\<^bsub>(C9,D9)\<^esub> c9)"
sorry

mtheorem finseqop_th_82:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d1 be ElementSUBSET-1M1-of D holds  for d2 be ElementSUBSET-1M1-of D holds  for F be BinOpBINOP-1M2-of D holds  for u be FunctionFUNCT-2M1-of(D,D) holds (F *FINSEQOPK7\<^bsub>(D)\<^esub>(idPARTFUN1K6 D,u)).BINOP-1K4\<^bsub>(D)\<^esub>(d1,d2) =XBOOLE-0R4 F .BINOP-1K4\<^bsub>(D)\<^esub>(d1,u .FUNCT-2K3\<^bsub>(D,D)\<^esub> d2) & (F *FINSEQOPK7\<^bsub>(D)\<^esub>(u,idPARTFUN1K6 D)).BINOP-1K4\<^bsub>(D)\<^esub>(d1,d2) =XBOOLE-0R4 F .BINOP-1K4\<^bsub>(D)\<^esub>(u .FUNCT-2K3\<^bsub>(D,D)\<^esub> d1,d2)"
sorry

mtheorem finseqop_th_83:
" for C be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for f be FunctionFUNCT-2M1-of(C,D) holds  for f9 be FunctionFUNCT-2M1-of(C,D) holds  for F be BinOpBINOP-1M2-of D holds  for u be UnOpBINOP-1M1-of D holds (F *FINSEQOPK7\<^bsub>(D)\<^esub>(idPARTFUN1K6 D,u)).:FUNCOP-1K6\<^bsub>(D,C)\<^esub>(f,f9) =FUNCT-2R2\<^bsub>(C,D)\<^esub> F .:FUNCOP-1K6\<^bsub>(D,C)\<^esub>(f,u *PARTFUN1K1\<^bsub>(C,D,D,D)\<^esub> f9)"
sorry

mtheorem finseqop_th_84:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for i be naturalORDINAL1V7\<bar>NumberORDINAL1M1 holds  for T1 be TupleFINSEQ-2M3-of(i,D) holds  for T2 be TupleFINSEQ-2M3-of(i,D) holds  for F be BinOpBINOP-1M2-of D holds  for u be UnOpBINOP-1M1-of D holds (F *FINSEQOPK7\<^bsub>(D)\<^esub>(idPARTFUN1K6 D,u)).:FINSEQOPK1\<^bsub>(D,D,D)\<^esub>(T1,T2) =RELSET-1R2\<^bsub>(omegaORDINAL1K4,D)\<^esub> F .:FINSEQOPK1\<^bsub>(D,D,D)\<^esub>(T1,u *FINSEQOPK4\<^bsub>(D,D)\<^esub> T2)"
sorry

mtheorem finseqop_th_85:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d1 be ElementSUBSET-1M1-of D holds  for d2 be ElementSUBSET-1M1-of D holds  for F be BinOpBINOP-1M2-of D holds  for u be UnOpBINOP-1M1-of D holds (((F be associativeBINOP-1V2\<^bsub>(D)\<^esub> & F be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub>) & F be commutativeBINOP-1V1\<^bsub>(D)\<^esub>) & F be having-an-inverseOpFINSEQOPV1\<^bsub>(D)\<^esub>) & u =FUNCT-2R2\<^bsub>(D,D)\<^esub> the-inverseOp-wrtFINSEQOPK5\<^bsub>(D)\<^esub> F implies u .FUNCT-2K3\<^bsub>(D,D)\<^esub> ((F *FINSEQOPK7\<^bsub>(D)\<^esub>(idPARTFUN1K6 D,u)).BINOP-1K4\<^bsub>(D)\<^esub>(d1,d2)) =XBOOLE-0R4 (F *FINSEQOPK7\<^bsub>(D)\<^esub>(u,idPARTFUN1K6 D)).BINOP-1K4\<^bsub>(D)\<^esub>(d1,d2) & (F *FINSEQOPK7\<^bsub>(D)\<^esub>(idPARTFUN1K6 D,u)).BINOP-1K4\<^bsub>(D)\<^esub>(d1,d2) =XBOOLE-0R4 u .FUNCT-2K3\<^bsub>(D,D)\<^esub> ((F *FINSEQOPK7\<^bsub>(D)\<^esub>(u,idPARTFUN1K6 D)).BINOP-1K4\<^bsub>(D)\<^esub>(d1,d2))"
sorry

mtheorem finseqop_th_86:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d be ElementSUBSET-1M1-of D holds  for F be BinOpBINOP-1M2-of D holds (F be associativeBINOP-1V2\<^bsub>(D)\<^esub> & F be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub>) & F be having-an-inverseOpFINSEQOPV1\<^bsub>(D)\<^esub> implies (F *FINSEQOPK7\<^bsub>(D)\<^esub>(idPARTFUN1K6 D,the-inverseOp-wrtFINSEQOPK5\<^bsub>(D)\<^esub> F)).BINOP-1K4\<^bsub>(D)\<^esub>(d,d) =XBOOLE-0R4 the-unity-wrtBINOP-1K3\<^bsub>(D)\<^esub> F"
sorry

mtheorem finseqop_th_87:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d be ElementSUBSET-1M1-of D holds  for F be BinOpBINOP-1M2-of D holds (F be associativeBINOP-1V2\<^bsub>(D)\<^esub> & F be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub>) & F be having-an-inverseOpFINSEQOPV1\<^bsub>(D)\<^esub> implies (F *FINSEQOPK7\<^bsub>(D)\<^esub>(idPARTFUN1K6 D,the-inverseOp-wrtFINSEQOPK5\<^bsub>(D)\<^esub> F)).BINOP-1K4\<^bsub>(D)\<^esub>(d,the-unity-wrtBINOP-1K3\<^bsub>(D)\<^esub> F) =XBOOLE-0R4 d"
sorry

mtheorem finseqop_th_88:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d be ElementSUBSET-1M1-of D holds  for F be BinOpBINOP-1M2-of D holds  for u be UnOpBINOP-1M1-of D holds F be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> implies (F *FINSEQOPK7\<^bsub>(D)\<^esub>(idPARTFUN1K6 D,u)).BINOP-1K4\<^bsub>(D)\<^esub>(the-unity-wrtBINOP-1K3\<^bsub>(D)\<^esub> F,d) =XBOOLE-0R4 u .FUNCT-2K3\<^bsub>(D,D)\<^esub> d"
sorry

mtheorem finseqop_th_89:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for F be BinOpBINOP-1M2-of D holds  for G be BinOpBINOP-1M2-of D holds (((F be commutativeBINOP-1V1\<^bsub>(D)\<^esub> & F be associativeBINOP-1V2\<^bsub>(D)\<^esub>) & F be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub>) & F be having-an-inverseOpFINSEQOPV1\<^bsub>(D)\<^esub>) & G =BINOP-1R13\<^bsub>(D,D,D)\<^esub> F *FINSEQOPK7\<^bsub>(D)\<^esub>(idPARTFUN1K6 D,the-inverseOp-wrtFINSEQOPK5\<^bsub>(D)\<^esub> F) implies ( for d1 be ElementSUBSET-1M1-of D holds  for d2 be ElementSUBSET-1M1-of D holds  for d3 be ElementSUBSET-1M1-of D holds  for d4 be ElementSUBSET-1M1-of D holds F .BINOP-1K4\<^bsub>(D)\<^esub>(G .BINOP-1K4\<^bsub>(D)\<^esub>(d1,d2),G .BINOP-1K4\<^bsub>(D)\<^esub>(d3,d4)) =XBOOLE-0R4 G .BINOP-1K4\<^bsub>(D)\<^esub>(F .BINOP-1K4\<^bsub>(D)\<^esub>(d1,d3),F .BINOP-1K4\<^bsub>(D)\<^esub>(d2,d4)))"
sorry

end
