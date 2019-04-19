theory finsop_1
  imports finseq_4 setwiseo
   "../mizar_extension/E_number"
begin
(*begin*)
reserve D for " non emptyXBOOLE-0V1\<bar>setHIDDENM2"
reserve d, d1, d2, d3 for "ElementSUBSET-1M1-of D"
reserve F, G, H, H1, H2 for "FinSequenceFINSEQ-1M3-of D"
reserve f, f1, f2 for "sequenceNAT-1M2-of D"
reserve g for "BinOpBINOP-1M2-of D"
reserve k, n, i, l for "NatNAT-1M1"
reserve P for "PermutationFUNCT-2M2-of domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> F"
mdef finsop_1_def_1 (" _ \<inverse>**\<inverse>FINSOP-1K1\<^bsub>'( _ ')\<^esub>  _ " [148,0,148]148 ) where
  mlet "D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "F be FinSequenceFINSEQ-1M3-of D", "g be BinOpBINOP-1M2-of D"
"assume g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> or lenFINSEQ-1K4 F >=XXREAL-0R2 \<one>\<^sub>M func g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F \<rightarrow> ElementSUBSET-1M1-of D means

  \<lambda>it. it =XBOOLE-0R4 the-unity-wrtBINOP-1K3\<^bsub>(D)\<^esub> g if g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> & lenFINSEQ-1K4 F =XBOOLE-0R4 0NUMBERSK6 
          otherwise \<lambda>it.  ex f be sequenceNAT-1M2-of D st (f .NAT-1K8\<^bsub>(D)\<^esub> \<one>\<^sub>M =XBOOLE-0R4 F .FUNCT-1K1 \<one>\<^sub>M & ( for n be NatNAT-1M1 holds 0NUMBERSK6 <>HIDDENR2 n & n <XXREAL-0R3 lenFINSEQ-1K4 F implies f .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 g .BINOP-1K1(f .NAT-1K8\<^bsub>(D)\<^esub> n,F .FUNCT-1K1 (n +NAT-1K1 \<one>\<^sub>M)))) & it =XBOOLE-0R4 f .NAT-1K8\<^bsub>(D)\<^esub> lenFINSEQ-1K4 F"
proof-
  (*existence*)
    show "g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> or lenFINSEQ-1K4 F >=XXREAL-0R2 \<one>\<^sub>M implies (g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> & lenFINSEQ-1K4 F =XBOOLE-0R4 0NUMBERSK6 implies ( ex it be ElementSUBSET-1M1-of D st it =XBOOLE-0R4 the-unity-wrtBINOP-1K3\<^bsub>(D)\<^esub> g)) & ( not (g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> & lenFINSEQ-1K4 F =XBOOLE-0R4 0NUMBERSK6) implies ( ex it be ElementSUBSET-1M1-of D st  ex f be sequenceNAT-1M2-of D st (f .NAT-1K8\<^bsub>(D)\<^esub> \<one>\<^sub>M =XBOOLE-0R4 F .FUNCT-1K1 \<one>\<^sub>M & ( for n be NatNAT-1M1 holds 0NUMBERSK6 <>HIDDENR2 n & n <XXREAL-0R3 lenFINSEQ-1K4 F implies f .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 g .BINOP-1K1(f .NAT-1K8\<^bsub>(D)\<^esub> n,F .FUNCT-1K1 (n +NAT-1K1 \<one>\<^sub>M)))) & it =XBOOLE-0R4 f .NAT-1K8\<^bsub>(D)\<^esub> lenFINSEQ-1K4 F))"
    proof(rule impI)
      assume Assume: "g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> or lenFINSEQ-1K4 F >=XXREAL-0R2 \<one>\<^sub>M"
      have A1: "g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> or lenFINSEQ-1K4 F >=XXREAL-0R2 \<one>\<^sub>M"
        using Assume sorry
      show "(g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> & lenFINSEQ-1K4 F =XBOOLE-0R4 0NUMBERSK6 implies ( ex it be ElementSUBSET-1M1-of D st it =XBOOLE-0R4 the-unity-wrtBINOP-1K3\<^bsub>(D)\<^esub> g)) & ( not (g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> & lenFINSEQ-1K4 F =XBOOLE-0R4 0NUMBERSK6) implies ( ex it be ElementSUBSET-1M1-of D st  ex f be sequenceNAT-1M2-of D st (f .NAT-1K8\<^bsub>(D)\<^esub> \<one>\<^sub>M =XBOOLE-0R4 F .FUNCT-1K1 \<one>\<^sub>M & ( for n be NatNAT-1M1 holds 0NUMBERSK6 <>HIDDENR2 n & n <XXREAL-0R3 lenFINSEQ-1K4 F implies f .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 g .BINOP-1K1(f .NAT-1K8\<^bsub>(D)\<^esub> n,F .FUNCT-1K1 (n +NAT-1K1 \<one>\<^sub>M)))) & it =XBOOLE-0R4 f .NAT-1K8\<^bsub>(D)\<^esub> lenFINSEQ-1K4 F))"
      proof-
        have " not ((g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> & lenFINSEQ-1K4 F =XBOOLE-0R4 0NUMBERSK6) & ( for VarFor1 be ElementSUBSET-1M1-of D holds  not VarFor1 =XBOOLE-0R4 the-unity-wrtBINOP-1K3\<^bsub>(D)\<^esub> g)) &  not ( not (g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> & lenFINSEQ-1K4 F =XBOOLE-0R4 0NUMBERSK6) & ( for VarFor1 be ElementSUBSET-1M1-of D holds  for f be sequenceNAT-1M2-of D holds  not ((f .NAT-1K8\<^bsub>(D)\<^esub> \<one>\<^sub>M =XBOOLE-0R4 F .FUNCT-1K1 \<one>\<^sub>M & ( for n be NatNAT-1M1 holds  not (( not 0NUMBERSK6 <>HIDDENR2 n &  not n <XXREAL-0R3 lenFINSEQ-1K4 F) &  not f .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 g .BINOP-1K1(f .NAT-1K8\<^bsub>(D)\<^esub> n,F .FUNCT-1K1 (n +NAT-1K1 \<one>\<^sub>M))))) & VarFor1 =XBOOLE-0R4 f .NAT-1K8\<^bsub>(D)\<^esub> lenFINSEQ-1K4 F)))"
        proof-
          have " not ((g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> & lenFINSEQ-1K4 F =XBOOLE-0R4 0NUMBERSK6) & ( for VarFor1 be ElementSUBSET-1M1-of D holds  not VarFor1 =XBOOLE-0R4 the-unity-wrtBINOP-1K3\<^bsub>(D)\<^esub> g)) &  not ( not (g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> & lenFINSEQ-1K4 F =XBOOLE-0R4 0NUMBERSK6) & ( for VarFor1 be ElementSUBSET-1M1-of D holds  for f be sequenceNAT-1M2-of D holds  not ((f .NAT-1K8\<^bsub>(D)\<^esub> \<one>\<^sub>M =XBOOLE-0R4 F .FUNCT-1K1 \<one>\<^sub>M & ( for n be NatNAT-1M1 holds  not (( not 0NUMBERSK6 <>HIDDENR2 n &  not n <XXREAL-0R3 lenFINSEQ-1K4 F) &  not f .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 g .BINOP-1K1(f .NAT-1K8\<^bsub>(D)\<^esub> n,F .FUNCT-1K1 (n +NAT-1K1 \<one>\<^sub>M))))) & VarFor1 =XBOOLE-0R4 f .NAT-1K8\<^bsub>(D)\<^esub> lenFINSEQ-1K4 F)))"
          proof-
            show " not ((g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> & lenFINSEQ-1K4 F =XBOOLE-0R4 0NUMBERSK6) & ( for VarFor1 be ElementSUBSET-1M1-of D holds  not VarFor1 =XBOOLE-0R4 the-unity-wrtBINOP-1K3\<^bsub>(D)\<^esub> g)) &  not ( not (g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> & lenFINSEQ-1K4 F =XBOOLE-0R4 0NUMBERSK6) & ( for VarFor1 be ElementSUBSET-1M1-of D holds  for f be sequenceNAT-1M2-of D holds  not ((f .NAT-1K8\<^bsub>(D)\<^esub> \<one>\<^sub>M =XBOOLE-0R4 F .FUNCT-1K1 \<one>\<^sub>M & ( for n be NatNAT-1M1 holds  not (( not 0NUMBERSK6 <>HIDDENR2 n &  not n <XXREAL-0R3 lenFINSEQ-1K4 F) &  not f .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 g .BINOP-1K1(f .NAT-1K8\<^bsub>(D)\<^esub> n,F .FUNCT-1K1 (n +NAT-1K1 \<one>\<^sub>M))))) & VarFor1 =XBOOLE-0R4 f .NAT-1K8\<^bsub>(D)\<^esub> lenFINSEQ-1K4 F)))"
            proof-
              have cases: "lenFINSEQ-1K4 F =XBOOLE-0R4 0NUMBERSK6 or lenFINSEQ-1K4 F <>HIDDENR2 0NUMBERSK6"
                 sorry
              have case1: "lenFINSEQ-1K4 F =XBOOLE-0R4 0NUMBERSK6 implies  not ((g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> & lenFINSEQ-1K4 F =XBOOLE-0R4 0NUMBERSK6) & ( for VarFor1 be ElementSUBSET-1M1-of D holds  not VarFor1 =XBOOLE-0R4 the-unity-wrtBINOP-1K3\<^bsub>(D)\<^esub> g)) &  not ( not (g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> & lenFINSEQ-1K4 F =XBOOLE-0R4 0NUMBERSK6) & ( for VarFor1 be ElementSUBSET-1M1-of D holds  for f be sequenceNAT-1M2-of D holds  not ((f .NAT-1K8\<^bsub>(D)\<^esub> \<one>\<^sub>M =XBOOLE-0R4 F .FUNCT-1K1 \<one>\<^sub>M & ( for n be NatNAT-1M1 holds  not (( not 0NUMBERSK6 <>HIDDENR2 n &  not n <XXREAL-0R3 lenFINSEQ-1K4 F) &  not f .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 g .BINOP-1K1(f .NAT-1K8\<^bsub>(D)\<^esub> n,F .FUNCT-1K1 (n +NAT-1K1 \<one>\<^sub>M))))) & VarFor1 =XBOOLE-0R4 f .NAT-1K8\<^bsub>(D)\<^esub> lenFINSEQ-1K4 F)))"
              proof(rule impI)
                assume "lenFINSEQ-1K4 F =XBOOLE-0R4 0NUMBERSK6"
                thus " not ((g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> & lenFINSEQ-1K4 F =XBOOLE-0R4 0NUMBERSK6) & ( for VarFor1 be ElementSUBSET-1M1-of D holds  not VarFor1 =XBOOLE-0R4 the-unity-wrtBINOP-1K3\<^bsub>(D)\<^esub> g)) &  not ( not (g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> & lenFINSEQ-1K4 F =XBOOLE-0R4 0NUMBERSK6) & ( for VarFor1 be ElementSUBSET-1M1-of D holds  for f be sequenceNAT-1M2-of D holds  not ((f .NAT-1K8\<^bsub>(D)\<^esub> \<one>\<^sub>M =XBOOLE-0R4 F .FUNCT-1K1 \<one>\<^sub>M & ( for n be NatNAT-1M1 holds  not (( not 0NUMBERSK6 <>HIDDENR2 n &  not n <XXREAL-0R3 lenFINSEQ-1K4 F) &  not f .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 g .BINOP-1K1(f .NAT-1K8\<^bsub>(D)\<^esub> n,F .FUNCT-1K1 (n +NAT-1K1 \<one>\<^sub>M))))) & VarFor1 =XBOOLE-0R4 f .NAT-1K8\<^bsub>(D)\<^esub> lenFINSEQ-1K4 F)))"
                  using A1 sorry
              qed
              have case2: "lenFINSEQ-1K4 F <>HIDDENR2 0NUMBERSK6 implies  not ((g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> & lenFINSEQ-1K4 F =XBOOLE-0R4 0NUMBERSK6) & ( for VarFor1 be ElementSUBSET-1M1-of D holds  not VarFor1 =XBOOLE-0R4 the-unity-wrtBINOP-1K3\<^bsub>(D)\<^esub> g)) &  not ( not (g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> & lenFINSEQ-1K4 F =XBOOLE-0R4 0NUMBERSK6) & ( for VarFor1 be ElementSUBSET-1M1-of D holds  for f be sequenceNAT-1M2-of D holds  not ((f .NAT-1K8\<^bsub>(D)\<^esub> \<one>\<^sub>M =XBOOLE-0R4 F .FUNCT-1K1 \<one>\<^sub>M & ( for n be NatNAT-1M1 holds  not (( not 0NUMBERSK6 <>HIDDENR2 n &  not n <XXREAL-0R3 lenFINSEQ-1K4 F) &  not f .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 g .BINOP-1K1(f .NAT-1K8\<^bsub>(D)\<^esub> n,F .FUNCT-1K1 (n +NAT-1K1 \<one>\<^sub>M))))) & VarFor1 =XBOOLE-0R4 f .NAT-1K8\<^bsub>(D)\<^esub> lenFINSEQ-1K4 F)))"
              proof(rule impI)
                assume A2: "lenFINSEQ-1K4 F <>HIDDENR2 0NUMBERSK6"
                let ?P = "\<lambda>Lamb1.  for F be FinSequenceFINSEQ-1M3-of D holds lenFINSEQ-1K4 F =XBOOLE-0R4 Lamb1 & lenFINSEQ-1K4 F <>HIDDENR2 0NUMBERSK6 implies ( ex d be ElementSUBSET-1M1-of D st  ex f be sequenceNAT-1M2-of D st (f .NAT-1K8\<^bsub>(D)\<^esub> \<one>\<^sub>M =XBOOLE-0R4 F .FUNCT-1K1 \<one>\<^sub>M & ( for n be NatNAT-1M1 holds 0NUMBERSK6 <>HIDDENR2 n & n <XXREAL-0R3 lenFINSEQ-1K4 F implies f .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 g .BINOP-1K1(f .NAT-1K8\<^bsub>(D)\<^esub> n,F .FUNCT-1K1 (n +NAT-1K1 \<one>\<^sub>M)))) & d =XBOOLE-0R4 f .NAT-1K8\<^bsub>(D)\<^esub> lenFINSEQ-1K4 F)"
                have A3: " for k be NatNAT-1M1 holds ?P(k) implies ?P(k +NAT-1K1 \<one>\<^sub>M)"
                proof-
                  have " for k be NatNAT-1M1 holds ( for F be FinSequenceFINSEQ-1M3-of D holds lenFINSEQ-1K4 F =XBOOLE-0R4 k & lenFINSEQ-1K4 F <>HIDDENR2 0NUMBERSK6 implies ( ex d be ElementSUBSET-1M1-of D st  ex f be sequenceNAT-1M2-of D st (f .NAT-1K8\<^bsub>(D)\<^esub> \<one>\<^sub>M =XBOOLE-0R4 F .FUNCT-1K1 \<one>\<^sub>M & ( for n be NatNAT-1M1 holds 0NUMBERSK6 <>HIDDENR2 n & n <XXREAL-0R3 lenFINSEQ-1K4 F implies f .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 g .BINOP-1K1(f .NAT-1K8\<^bsub>(D)\<^esub> n,F .FUNCT-1K1 (n +NAT-1K1 \<one>\<^sub>M)))) & d =XBOOLE-0R4 f .NAT-1K8\<^bsub>(D)\<^esub> lenFINSEQ-1K4 F)) implies ( for F be FinSequenceFINSEQ-1M3-of D holds lenFINSEQ-1K4 F =XBOOLE-0R4 k +NAT-1K1 \<one>\<^sub>M & lenFINSEQ-1K4 F <>HIDDENR2 0NUMBERSK6 implies  not ( for d be ElementSUBSET-1M1-of D holds  for f be sequenceNAT-1M2-of D holds  not ((f .NAT-1K8\<^bsub>(D)\<^esub> \<one>\<^sub>M =XBOOLE-0R4 F .FUNCT-1K1 \<one>\<^sub>M & ( for n be NatNAT-1M1 holds  not (( not 0NUMBERSK6 <>HIDDENR2 n &  not n <XXREAL-0R3 lenFINSEQ-1K4 F) &  not f .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 g .BINOP-1K1(f .NAT-1K8\<^bsub>(D)\<^esub> n,F .FUNCT-1K1 (n +NAT-1K1 \<one>\<^sub>M))))) & d =XBOOLE-0R4 f .NAT-1K8\<^bsub>(D)\<^esub> lenFINSEQ-1K4 F)))"
                  proof(rule ballI,rule impI,rule ballI,rule impMI ,rule impI)
                    fix k assume [ty]: "k be NatNAT-1M1"
                    assume A4: "?P(k)"
                    fix F assume [ty]: "F be FinSequenceFINSEQ-1M3-of D"
                    assume A5: "lenFINSEQ-1K4 F =XBOOLE-0R4 k +NAT-1K1 \<one>\<^sub>M"
                      and "lenFINSEQ-1K4 F <>HIDDENR2 0NUMBERSK6"
                    obtain G where 
                      [ty]:"G be FinSequenceFINSEQ-1M3-of D" and GDef:"G = F |RELSET-1K5\<^bsub>(NATNUMBERSK1,D)\<^esub> SegFINSEQ-1K2 k"
                      using finseq_1_th_18 sorry
                    have A6: "lenFINSEQ-1K4 G =XBOOLE-0R4 k"
                      using A5 finseq_3_th_53 sorry
                    have " ex d be ElementSUBSET-1M1-of D st  ex f be sequenceNAT-1M2-of D st f .NAT-1K8\<^bsub>(D)\<^esub> \<one>\<^sub>M =XBOOLE-0R4 F .FUNCT-1K1 \<one>\<^sub>M & (( for n be NatNAT-1M1 holds 0NUMBERSK6 <>HIDDENR2 n & n <XXREAL-0R3 lenFINSEQ-1K4 F implies f .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 g .BINOP-1K1(f .NAT-1K8\<^bsub>(D)\<^esub> n,F .FUNCT-1K1 (n +NAT-1K1 \<one>\<^sub>M))) & d =XBOOLE-0R4 f .NAT-1K8\<^bsub>(D)\<^esub> lenFINSEQ-1K4 F)"
                    proof-
                      show " ex d be ElementSUBSET-1M1-of D st  ex f be sequenceNAT-1M2-of D st f .NAT-1K8\<^bsub>(D)\<^esub> \<one>\<^sub>M =XBOOLE-0R4 F .FUNCT-1K1 \<one>\<^sub>M & (( for n be NatNAT-1M1 holds 0NUMBERSK6 <>HIDDENR2 n & n <XXREAL-0R3 lenFINSEQ-1K4 F implies f .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 g .BINOP-1K1(f .NAT-1K8\<^bsub>(D)\<^esub> n,F .FUNCT-1K1 (n +NAT-1K1 \<one>\<^sub>M))) & d =XBOOLE-0R4 f .NAT-1K8\<^bsub>(D)\<^esub> lenFINSEQ-1K4 F)"
                      proof-
                        have cases: "lenFINSEQ-1K4 G =XBOOLE-0R4 0NUMBERSK6 or lenFINSEQ-1K4 G <>HIDDENR2 0NUMBERSK6"
                           sorry
                        have case1: "lenFINSEQ-1K4 G =XBOOLE-0R4 0NUMBERSK6 implies ( ex d be ElementSUBSET-1M1-of D st  ex f be sequenceNAT-1M2-of D st f .NAT-1K8\<^bsub>(D)\<^esub> \<one>\<^sub>M =XBOOLE-0R4 F .FUNCT-1K1 \<one>\<^sub>M & (( for n be NatNAT-1M1 holds 0NUMBERSK6 <>HIDDENR2 n & n <XXREAL-0R3 lenFINSEQ-1K4 F implies f .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 g .BINOP-1K1(f .NAT-1K8\<^bsub>(D)\<^esub> n,F .FUNCT-1K1 (n +NAT-1K1 \<one>\<^sub>M))) & d =XBOOLE-0R4 f .NAT-1K8\<^bsub>(D)\<^esub> lenFINSEQ-1K4 F))"
                        proof(rule impI)
                          assume A7: "lenFINSEQ-1K4 G =XBOOLE-0R4 0NUMBERSK6"
                          let ?f = "NATNUMBERSK1 -->FUNCOP-1K7 F .FUNCT-1K1 \<one>\<^sub>M"
                          have A8: "rngFUNCT-1K2 ?f c=TARSKIR1 D"
                          proof-
                            have "rngFUNCT-1K2 (NATNUMBERSK1 -->FUNCOP-1K7 F .FUNCT-1K1 \<one>\<^sub>M) c=TARSKIR1 D"
                            proof-
                              have " for x be objectHIDDENM1 holds x inHIDDENR3 rngFUNCT-1K2 (NATNUMBERSK1 -->FUNCOP-1K7 F .FUNCT-1K1 \<one>\<^sub>M) implies x inHIDDENR3 D"
                              proof(rule ballI,rule impI)
                                fix x assume [ty]: "x be objectHIDDENM1"
                                assume "x inHIDDENR3 rngFUNCT-1K2 ?f"
                                then have " ex y be objectHIDDENM1 st y inHIDDENR3 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> ?f & ?f .FUNCT-1K1 y =HIDDENR1 x"
                                  using funct_1_def_3 sorry
                                then have A9: "x =HIDDENR1 F .FUNCT-1K1 \<one>\<^sub>M"
                                  using funcop_1_th_7 sorry
                                have "\<one>\<^sub>M inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> F"
                                  using A5 A6 A7 finseq_3_th_25 sorry
                                then have A10: "x inHIDDENR3 rngFUNCT-1K2 F"
                                  using A9 funct_1_def_3 sorry
                                have "rngFUNCT-1K2 F c=TARSKIR1 D"
                                  using finseq_1_def_4 sorry
                                thus "x inHIDDENR3 D"
                                  using A10 sorry
                              qed "sorry"
                              thus "rngFUNCT-1K2 (NATNUMBERSK1 -->FUNCOP-1K7 F .FUNCT-1K1 \<one>\<^sub>M) c=TARSKIR1 D"
                                using tarski_def_3 sorry
                            qed
                            thus " ?thesis "
                               sorry
                          qed
                          have "domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> ?f =XBOOLE-0R4 NATNUMBERSK1"
                            using funcop_1_th_13 sorry
                          then obtain f where 
                            [ty]:"f be sequenceNAT-1M2-of D" and fDef:"f = ?f"
                            using A8 relset_1_th_4 sorry
                          obtain d where 
                            [ty]:"d be ElementSUBSET-1M1-of D" and dDef:"d = f .NAT-1K8\<^bsub>(D)\<^esub> \<one>\<^sub>M"
                             sorry
                          show " ex d be ElementSUBSET-1M1-of D st  ex f be sequenceNAT-1M2-of D st f .NAT-1K8\<^bsub>(D)\<^esub> \<one>\<^sub>M =XBOOLE-0R4 F .FUNCT-1K1 \<one>\<^sub>M & (( for n be NatNAT-1M1 holds 0NUMBERSK6 <>HIDDENR2 n & n <XXREAL-0R3 lenFINSEQ-1K4 F implies f .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 g .BINOP-1K1(f .NAT-1K8\<^bsub>(D)\<^esub> n,F .FUNCT-1K1 (n +NAT-1K1 \<one>\<^sub>M))) & d =XBOOLE-0R4 f .NAT-1K8\<^bsub>(D)\<^esub> lenFINSEQ-1K4 F)"
                          proof(rule bexI[of _ "d"])
                            show " ex f be sequenceNAT-1M2-of D st f .NAT-1K8\<^bsub>(D)\<^esub> \<one>\<^sub>M =XBOOLE-0R4 F .FUNCT-1K1 \<one>\<^sub>M & (( for n be NatNAT-1M1 holds 0NUMBERSK6 <>HIDDENR2 n & n <XXREAL-0R3 lenFINSEQ-1K4 F implies f .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 g .BINOP-1K1(f .NAT-1K8\<^bsub>(D)\<^esub> n,F .FUNCT-1K1 (n +NAT-1K1 \<one>\<^sub>M))) & d =XBOOLE-0R4 f .NAT-1K8\<^bsub>(D)\<^esub> lenFINSEQ-1K4 F)"
                            proof(rule bexI[of _ "f"],rule conjMI,rule conjMI)
                              show "f .NAT-1K8\<^bsub>(D)\<^esub> \<one>\<^sub>M =XBOOLE-0R4 F .FUNCT-1K1 \<one>\<^sub>M"
                                using funcop_1_th_7 sorry
                              show " for n be NatNAT-1M1 holds 0NUMBERSK6 <>HIDDENR2 n & n <XXREAL-0R3 lenFINSEQ-1K4 F implies f .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 g .BINOP-1K1(f .NAT-1K8\<^bsub>(D)\<^esub> n,F .FUNCT-1K1 (n +NAT-1K1 \<one>\<^sub>M))"
                                using A5 A6 A7 nat_1_th_14 sorry
                              show "d =XBOOLE-0R4 f .NAT-1K8\<^bsub>(D)\<^esub> lenFINSEQ-1K4 F"
                                using A5 A6 A7 sorry
                            qed "sorry"
                          qed "sorry"
                        qed
                        have case2: "lenFINSEQ-1K4 G <>HIDDENR2 0NUMBERSK6 implies ( ex a be ElementSUBSET-1M1-of D st  ex h be sequenceNAT-1M2-of D st h .NAT-1K8\<^bsub>(D)\<^esub> \<one>\<^sub>M =HIDDENR1 F .FUNCT-1K1 \<one>\<^sub>M & (( for n be NatNAT-1M1 holds 0NUMBERSK6 <>HIDDENR2 n & n <XXREAL-0R3 lenFINSEQ-1K4 F implies h .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 g .BINOP-1K1(h .NAT-1K8\<^bsub>(D)\<^esub> n,F .FUNCT-1K1 (n +NAT-1K1 \<one>\<^sub>M))) & a =XBOOLE-0R4 h .NAT-1K8\<^bsub>(D)\<^esub> lenFINSEQ-1K4 F))"
                        proof(rule impI)
                          assume A11: "lenFINSEQ-1K4 G <>HIDDENR2 0NUMBERSK6"
                          obtain j where 
                            [ty]:"j be ElementSUBSET-1M1-of NATNUMBERSK1" and jDef:"j = lenFINSEQ-1K4 F"
                             sorry
                          have "\<one>\<^sub>M <=XXREAL-0R1 lenFINSEQ-1K4 F"
                            using A5 nat_1_th_12 sorry
                          then have "lenFINSEQ-1K4 F inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> F"
                            using finseq_3_th_25 sorry
                          then have A12: "F .FUNCT-1K1 lenFINSEQ-1K4 F inTARSKIR2 rngFUNCT-1K2 F"
                            using funct_1_def_3 sorry
                          have "rngFUNCT-1K2 F c=TARSKIR1 D"
                            using finseq_1_def_4 sorry
                          then obtain t where 
                            [ty]:"t be ElementSUBSET-1M1-of D" and tDef:"t = F .FUNCT-1K1 lenFINSEQ-1K4 F"
                            using A12 sorry
                          have "lenFINSEQ-1K4 G >=XXREAL-0R2 \<one>\<^sub>M"
                            using A11 nat_1_th_14 sorry
                          then have A13: "\<one>\<^sub>M inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> G"
                            using finseq_3_th_25 sorry
                          obtain d f where
                            [ty]:"d be ElementSUBSET-1M1-of D" "f be sequenceNAT-1M2-of D" and 
                            A14: "f .NAT-1K8\<^bsub>(D)\<^esub> \<one>\<^sub>M =XBOOLE-0R4 G .FUNCT-1K1 \<one>\<^sub>M"and A15: " for n be NatNAT-1M1 holds 0NUMBERSK6 <>HIDDENR2 n & n <XXREAL-0R3 lenFINSEQ-1K4 G implies f .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 g .BINOP-1K1(f .NAT-1K8\<^bsub>(D)\<^esub> n,G .FUNCT-1K1 (n +NAT-1K1 \<one>\<^sub>M))"and A16: "d =XBOOLE-0R4 f .NAT-1K8\<^bsub>(D)\<^esub> lenFINSEQ-1K4 G"
                            using A4 A5 A11 finseq_3_th_53 sorry
                          let ?F = "\<lambda>Lamb1. f .NAT-1K8\<^bsub>(D)\<^esub> Lamb1"
                          obtain h where
                            [ty]:"h be sequenceNAT-1M2-of D" and 
                            A17: "h .NAT-1K8\<^bsub>(D)\<^esub> j =XBOOLE-0R4 g .BINOP-1K4\<^bsub>(D)\<^esub>(d,t)"and A18: " for n be ElementSUBSET-1M1-of NATNUMBERSK1 holds n <>HIDDENR2 j implies h .NAT-1K8\<^bsub>(D)\<^esub> n =XBOOLE-0R4 ?F(n)"
                            using funct_2_sch_6 sorry
                          obtain a where 
                            [ty]:"a be ElementSUBSET-1M1-of D" and aDef:"a = h .NAT-1K8\<^bsub>(D)\<^esub> j"
                             sorry
                          show " ex a be ElementSUBSET-1M1-of D st  ex h be sequenceNAT-1M2-of D st h .NAT-1K8\<^bsub>(D)\<^esub> \<one>\<^sub>M =HIDDENR1 F .FUNCT-1K1 \<one>\<^sub>M & (( for n be NatNAT-1M1 holds 0NUMBERSK6 <>HIDDENR2 n & n <XXREAL-0R3 lenFINSEQ-1K4 F implies h .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 g .BINOP-1K1(h .NAT-1K8\<^bsub>(D)\<^esub> n,F .FUNCT-1K1 (n +NAT-1K1 \<one>\<^sub>M))) & a =XBOOLE-0R4 h .NAT-1K8\<^bsub>(D)\<^esub> lenFINSEQ-1K4 F)"
                          proof(rule bexI[of _ "a"])
                            show " ex h be sequenceNAT-1M2-of D st h .NAT-1K8\<^bsub>(D)\<^esub> \<one>\<^sub>M =HIDDENR1 F .FUNCT-1K1 \<one>\<^sub>M & (( for n be NatNAT-1M1 holds 0NUMBERSK6 <>HIDDENR2 n & n <XXREAL-0R3 lenFINSEQ-1K4 F implies h .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 g .BINOP-1K1(h .NAT-1K8\<^bsub>(D)\<^esub> n,F .FUNCT-1K1 (n +NAT-1K1 \<one>\<^sub>M))) & a =XBOOLE-0R4 h .NAT-1K8\<^bsub>(D)\<^esub> lenFINSEQ-1K4 F)"
                            proof(rule bexI[of _ "h"],rule conjMI,rule conjMI)
                              have "\<one>\<^sub>M <>HIDDENR2 j"
                                using A5 A11 finseq_3_th_53 sorry
                              then have "h .NAT-1K8\<^bsub>(D)\<^esub> \<one>\<^sub>M =HIDDENR1 G .FUNCT-1K1 \<one>\<^sub>M"
                                using A14 A18 sorry
                              also have "... = F .FUNCT-1K1 \<one>\<^sub>M"
                                using A13 funct_1_th_47 sorry
                              finally show "h .NAT-1K8\<^bsub>(D)\<^esub> \<one>\<^sub>M =HIDDENR1 F .FUNCT-1K1 \<one>\<^sub>M"
                                 sorry
                              show " for n be NatNAT-1M1 holds 0NUMBERSK6 <>HIDDENR2 n & n <XXREAL-0R3 lenFINSEQ-1K4 F implies h .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 g .BINOP-1K1(h .NAT-1K8\<^bsub>(D)\<^esub> n,F .FUNCT-1K1 (n +NAT-1K1 \<one>\<^sub>M))"
                              proof-
                                have " for n be NatNAT-1M1 holds n <>HIDDENR2 0NUMBERSK6 & n <XXREAL-0R3 lenFINSEQ-1K4 F implies h .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 g .BINOP-1K1(h .NAT-1K8\<^bsub>(D)\<^esub> n,F .FUNCT-1K1 (n +NAT-1K1 \<one>\<^sub>M))"
                                proof(rule ballI,rule impMI ,rule impI)
                                  fix n assume [ty]: "n be NatNAT-1M1"
                                  assume A19: "n <>HIDDENR2 0NUMBERSK6"
                                    and A20: "n <XXREAL-0R3 lenFINSEQ-1K4 F"
                                  have "h .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 g .BINOP-1K1(h .NAT-1K8\<^bsub>(D)\<^esub> n,F .FUNCT-1K1 (n +NAT-1K1 \<one>\<^sub>M))"
                                  proof-
                                    show "h .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 g .BINOP-1K1(h .NAT-1K8\<^bsub>(D)\<^esub> n,F .FUNCT-1K1 (n +NAT-1K1 \<one>\<^sub>M))"
                                    proof-
                                      have cases: "n +NAT-1K1 \<one>\<^sub>M =XBOOLE-0R4 lenFINSEQ-1K4 F or n +NAT-1K1 \<one>\<^sub>M <>HIDDENR2 lenFINSEQ-1K4 F"
                                         sorry
                                      have case1: "n +NAT-1K1 \<one>\<^sub>M =XBOOLE-0R4 lenFINSEQ-1K4 F implies h .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 g .BINOP-1K1(h .NAT-1K8\<^bsub>(D)\<^esub> n,F .FUNCT-1K1 (n +NAT-1K1 \<one>\<^sub>M))"
                                      proof(rule impI)
                                        assume A21: "n +NAT-1K1 \<one>\<^sub>M =XBOOLE-0R4 lenFINSEQ-1K4 F"
                                        have "lenFINSEQ-1K4 G <>HIDDENR2 lenFINSEQ-1K4 F"
                                          using A5 A6 sorry
                                        thus "h .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 g .BINOP-1K1(h .NAT-1K8\<^bsub>(D)\<^esub> n,F .FUNCT-1K1 (n +NAT-1K1 \<one>\<^sub>M))"
                                          using A5 A6 A16 A17 A18 A21 sorry
                                      qed
                                      have case2: "n +NAT-1K1 \<one>\<^sub>M <>HIDDENR2 lenFINSEQ-1K4 F implies h .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 g .BINOP-1K1(h .NAT-1K8\<^bsub>(D)\<^esub> n,F .FUNCT-1K1 (n +NAT-1K1 \<one>\<^sub>M))"
                                      proof(rule impI)
                                        assume A22: "n +NAT-1K1 \<one>\<^sub>M <>HIDDENR2 lenFINSEQ-1K4 F"
                                        have "n +NAT-1K1 \<one>\<^sub>M <=XXREAL-0R1 lenFINSEQ-1K4 F"
                                          using A20 nat_1_th_13 sorry
                                        then have A23: "n +NAT-1K1 \<one>\<^sub>M <XXREAL-0R3 lenFINSEQ-1K4 F"
                                          using A22 xxreal_0_th_1 sorry
                                        then have A24: "n <XXREAL-0R3 lenFINSEQ-1K4 G"
                                          using A5 A6 xreal_1_th_6 sorry
                                        have "\<one>\<^sub>M <=XXREAL-0R1 n +NAT-1K1 \<one>\<^sub>M & n +NAT-1K1 \<one>\<^sub>M <=XXREAL-0R1 lenFINSEQ-1K4 G"
                                          using A5 A6 A23 nat_1_th_12 nat_1_th_13 sorry
                                        then have A25: "n +NAT-1K1 \<one>\<^sub>M inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> G"
                                          using finseq_3_th_25 sorry
                                        have "h .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M) =HIDDENR1 f .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M)"
                                          using A18 A22 sorry
                                        also have "... = g .BINOP-1K1(f .NAT-1K8\<^bsub>(D)\<^esub> n,G .FUNCT-1K1 (n +NAT-1K1 \<one>\<^sub>M))"
                                          using A15 A19 A24 sorry
                                        also have "... = g .BINOP-1K1(f .NAT-1K8\<^bsub>(D)\<^esub> n,F .FUNCT-1K1 (n +NAT-1K1 \<one>\<^sub>M))"
                                          using A25 funct_1_th_47 sorry
                                        also have "... = g .BINOP-1K1(h .NAT-1K8\<^bsub>(D)\<^esub> (InSUBSET-1K10(n,NATNUMBERSK1)),F .FUNCT-1K1 (n +NAT-1K1 \<one>\<^sub>M))"
                                          using A18 A20 sorry
                                        finally have "h .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M) =HIDDENR1 g .BINOP-1K1(h .NAT-1K8\<^bsub>(D)\<^esub> (InSUBSET-1K10(n,NATNUMBERSK1)),F .FUNCT-1K1 (n +NAT-1K1 \<one>\<^sub>M))"
                                           sorry
                                        thus "h .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 g .BINOP-1K1(h .NAT-1K8\<^bsub>(D)\<^esub> n,F .FUNCT-1K1 (n +NAT-1K1 \<one>\<^sub>M))"
                                           sorry
                                      qed
                                      show " ?thesis "
                                        using cases case1 case2 sorry
                                    qed
                                  qed
                                  thus "h .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 g .BINOP-1K1(h .NAT-1K8\<^bsub>(D)\<^esub> n,F .FUNCT-1K1 (n +NAT-1K1 \<one>\<^sub>M))"
                                     sorry
                                qed "sorry"
                                thus " ?thesis "
                                   sorry
                              qed
                              show "a =XBOOLE-0R4 h .NAT-1K8\<^bsub>(D)\<^esub> lenFINSEQ-1K4 F"
                                 sorry
                            qed "sorry"
                          qed "sorry"
                        qed
                        show " ?thesis "
                          using cases case1 case2 sorry
                      qed
                    qed
                    thus " not ( for d be ElementSUBSET-1M1-of D holds  for f be sequenceNAT-1M2-of D holds  not ((f .NAT-1K8\<^bsub>(D)\<^esub> \<one>\<^sub>M =XBOOLE-0R4 F .FUNCT-1K1 \<one>\<^sub>M & ( for n be NatNAT-1M1 holds  not (( not 0NUMBERSK6 <>HIDDENR2 n &  not n <XXREAL-0R3 lenFINSEQ-1K4 F) &  not f .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 g .BINOP-1K1(f .NAT-1K8\<^bsub>(D)\<^esub> n,F .FUNCT-1K1 (n +NAT-1K1 \<one>\<^sub>M))))) & d =XBOOLE-0R4 f .NAT-1K8\<^bsub>(D)\<^esub> lenFINSEQ-1K4 F))"
                       sorry
                  qed "sorry"
                  thus " ?thesis "
                     sorry
                qed
                have A26: "?P(0NUMBERSK6)"
                   sorry
                have " for k be NatNAT-1M1 holds ?P(k)"
                  using nat_1_sch_2 A26 A3 sorry
                thus " not ((g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> & lenFINSEQ-1K4 F =XBOOLE-0R4 0NUMBERSK6) & ( for VarFor1 be ElementSUBSET-1M1-of D holds  not VarFor1 =XBOOLE-0R4 the-unity-wrtBINOP-1K3\<^bsub>(D)\<^esub> g)) &  not ( not (g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> & lenFINSEQ-1K4 F =XBOOLE-0R4 0NUMBERSK6) & ( for VarFor1 be ElementSUBSET-1M1-of D holds  for f be sequenceNAT-1M2-of D holds  not ((f .NAT-1K8\<^bsub>(D)\<^esub> \<one>\<^sub>M =XBOOLE-0R4 F .FUNCT-1K1 \<one>\<^sub>M & ( for n be NatNAT-1M1 holds  not (( not 0NUMBERSK6 <>HIDDENR2 n &  not n <XXREAL-0R3 lenFINSEQ-1K4 F) &  not f .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 g .BINOP-1K1(f .NAT-1K8\<^bsub>(D)\<^esub> n,F .FUNCT-1K1 (n +NAT-1K1 \<one>\<^sub>M))))) & VarFor1 =XBOOLE-0R4 f .NAT-1K8\<^bsub>(D)\<^esub> lenFINSEQ-1K4 F)))"
                  using A2 sorry
              qed
              show " ?thesis "
                using cases case1 case2 sorry
            qed
          qed
          thus " not ((g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> & lenFINSEQ-1K4 F =XBOOLE-0R4 0NUMBERSK6) & ( for VarFor1 be ElementSUBSET-1M1-of D holds  not VarFor1 =XBOOLE-0R4 the-unity-wrtBINOP-1K3\<^bsub>(D)\<^esub> g)) &  not ( not (g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> & lenFINSEQ-1K4 F =XBOOLE-0R4 0NUMBERSK6) & ( for VarFor1 be ElementSUBSET-1M1-of D holds  for f be sequenceNAT-1M2-of D holds  not ((f .NAT-1K8\<^bsub>(D)\<^esub> \<one>\<^sub>M =XBOOLE-0R4 F .FUNCT-1K1 \<one>\<^sub>M & ( for n be NatNAT-1M1 holds  not (( not 0NUMBERSK6 <>HIDDENR2 n &  not n <XXREAL-0R3 lenFINSEQ-1K4 F) &  not f .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 g .BINOP-1K1(f .NAT-1K8\<^bsub>(D)\<^esub> n,F .FUNCT-1K1 (n +NAT-1K1 \<one>\<^sub>M))))) & VarFor1 =XBOOLE-0R4 f .NAT-1K8\<^bsub>(D)\<^esub> lenFINSEQ-1K4 F)))"
             sorry
        qed
        thus " ?thesis "
           sorry
      qed
    qed
  (*uniqueness*)
    show "g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> or lenFINSEQ-1K4 F >=XXREAL-0R2 \<one>\<^sub>M implies ( for it1 be ElementSUBSET-1M1-of D holds  for it2 be ElementSUBSET-1M1-of D holds (g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> & lenFINSEQ-1K4 F =XBOOLE-0R4 0NUMBERSK6 implies (it1 =XBOOLE-0R4 the-unity-wrtBINOP-1K3\<^bsub>(D)\<^esub> g & it2 =XBOOLE-0R4 the-unity-wrtBINOP-1K3\<^bsub>(D)\<^esub> g implies it1 =HIDDENR1 it2)) & ( not (g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> & lenFINSEQ-1K4 F =XBOOLE-0R4 0NUMBERSK6) implies (( ex f be sequenceNAT-1M2-of D st (f .NAT-1K8\<^bsub>(D)\<^esub> \<one>\<^sub>M =XBOOLE-0R4 F .FUNCT-1K1 \<one>\<^sub>M & ( for n be NatNAT-1M1 holds 0NUMBERSK6 <>HIDDENR2 n & n <XXREAL-0R3 lenFINSEQ-1K4 F implies f .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 g .BINOP-1K1(f .NAT-1K8\<^bsub>(D)\<^esub> n,F .FUNCT-1K1 (n +NAT-1K1 \<one>\<^sub>M)))) & it1 =XBOOLE-0R4 f .NAT-1K8\<^bsub>(D)\<^esub> lenFINSEQ-1K4 F) & ( ex f be sequenceNAT-1M2-of D st (f .NAT-1K8\<^bsub>(D)\<^esub> \<one>\<^sub>M =XBOOLE-0R4 F .FUNCT-1K1 \<one>\<^sub>M & ( for n be NatNAT-1M1 holds 0NUMBERSK6 <>HIDDENR2 n & n <XXREAL-0R3 lenFINSEQ-1K4 F implies f .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 g .BINOP-1K1(f .NAT-1K8\<^bsub>(D)\<^esub> n,F .FUNCT-1K1 (n +NAT-1K1 \<one>\<^sub>M)))) & it2 =XBOOLE-0R4 f .NAT-1K8\<^bsub>(D)\<^esub> lenFINSEQ-1K4 F) implies it1 =HIDDENR1 it2)))"
    proof(rule impI)
      assume Assume: "g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> or lenFINSEQ-1K4 F >=XXREAL-0R2 \<one>\<^sub>M"
      have A1: "g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> or lenFINSEQ-1K4 F >=XXREAL-0R2 \<one>\<^sub>M"
        using Assume sorry
      show " for it1 be ElementSUBSET-1M1-of D holds  for it2 be ElementSUBSET-1M1-of D holds (g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> & lenFINSEQ-1K4 F =XBOOLE-0R4 0NUMBERSK6 implies (it1 =XBOOLE-0R4 the-unity-wrtBINOP-1K3\<^bsub>(D)\<^esub> g & it2 =XBOOLE-0R4 the-unity-wrtBINOP-1K3\<^bsub>(D)\<^esub> g implies it1 =HIDDENR1 it2)) & ( not (g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> & lenFINSEQ-1K4 F =XBOOLE-0R4 0NUMBERSK6) implies (( ex f be sequenceNAT-1M2-of D st (f .NAT-1K8\<^bsub>(D)\<^esub> \<one>\<^sub>M =XBOOLE-0R4 F .FUNCT-1K1 \<one>\<^sub>M & ( for n be NatNAT-1M1 holds 0NUMBERSK6 <>HIDDENR2 n & n <XXREAL-0R3 lenFINSEQ-1K4 F implies f .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 g .BINOP-1K1(f .NAT-1K8\<^bsub>(D)\<^esub> n,F .FUNCT-1K1 (n +NAT-1K1 \<one>\<^sub>M)))) & it1 =XBOOLE-0R4 f .NAT-1K8\<^bsub>(D)\<^esub> lenFINSEQ-1K4 F) & ( ex f be sequenceNAT-1M2-of D st (f .NAT-1K8\<^bsub>(D)\<^esub> \<one>\<^sub>M =XBOOLE-0R4 F .FUNCT-1K1 \<one>\<^sub>M & ( for n be NatNAT-1M1 holds 0NUMBERSK6 <>HIDDENR2 n & n <XXREAL-0R3 lenFINSEQ-1K4 F implies f .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 g .BINOP-1K1(f .NAT-1K8\<^bsub>(D)\<^esub> n,F .FUNCT-1K1 (n +NAT-1K1 \<one>\<^sub>M)))) & it2 =XBOOLE-0R4 f .NAT-1K8\<^bsub>(D)\<^esub> lenFINSEQ-1K4 F) implies it1 =HIDDENR1 it2))"
      proof-
        have " for d1 be ElementSUBSET-1M1-of D holds  for d2 be ElementSUBSET-1M1-of D holds (((g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> & lenFINSEQ-1K4 F =XBOOLE-0R4 0NUMBERSK6) & d1 =XBOOLE-0R4 the-unity-wrtBINOP-1K3\<^bsub>(D)\<^esub> g) & d2 =XBOOLE-0R4 the-unity-wrtBINOP-1K3\<^bsub>(D)\<^esub> g implies d1 =XBOOLE-0R4 d2) & ( not g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> or lenFINSEQ-1K4 F <>HIDDENR2 0NUMBERSK6 implies (( ex f1 be sequenceNAT-1M2-of D st (f1 .NAT-1K8\<^bsub>(D)\<^esub> \<one>\<^sub>M =XBOOLE-0R4 F .FUNCT-1K1 \<one>\<^sub>M & ( for n be NatNAT-1M1 holds 0NUMBERSK6 <>HIDDENR2 n & n <XXREAL-0R3 lenFINSEQ-1K4 F implies f1 .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 g .BINOP-1K1(f1 .NAT-1K8\<^bsub>(D)\<^esub> n,F .FUNCT-1K1 (n +NAT-1K1 \<one>\<^sub>M)))) & d1 =XBOOLE-0R4 f1 .NAT-1K8\<^bsub>(D)\<^esub> lenFINSEQ-1K4 F) implies (( ex f2 be sequenceNAT-1M2-of D st (f2 .NAT-1K8\<^bsub>(D)\<^esub> \<one>\<^sub>M =XBOOLE-0R4 F .FUNCT-1K1 \<one>\<^sub>M & ( for n be NatNAT-1M1 holds 0NUMBERSK6 <>HIDDENR2 n & n <XXREAL-0R3 lenFINSEQ-1K4 F implies f2 .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 g .BINOP-1K1(f2 .NAT-1K8\<^bsub>(D)\<^esub> n,F .FUNCT-1K1 (n +NAT-1K1 \<one>\<^sub>M)))) & d2 =XBOOLE-0R4 f2 .NAT-1K8\<^bsub>(D)\<^esub> lenFINSEQ-1K4 F) implies d1 =HIDDENR1 d2)))"
        proof(rule ballI,rule ballI,rule conjMI,rule impI,rule impI,rule impI)
          fix d1 assume [ty]: "d1 be ElementSUBSET-1M1-of D"
          fix d2 assume [ty]: "d2 be ElementSUBSET-1M1-of D"
          show "((g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> & lenFINSEQ-1K4 F =XBOOLE-0R4 0NUMBERSK6) & d1 =XBOOLE-0R4 the-unity-wrtBINOP-1K3\<^bsub>(D)\<^esub> g) & d2 =XBOOLE-0R4 the-unity-wrtBINOP-1K3\<^bsub>(D)\<^esub> g implies d1 =XBOOLE-0R4 d2"
             sorry
          assume A27: " not g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> or lenFINSEQ-1K4 F <>HIDDENR2 0NUMBERSK6"
          assume Given: " ex f1 be sequenceNAT-1M2-of D st (f1 .NAT-1K8\<^bsub>(D)\<^esub> \<one>\<^sub>M =XBOOLE-0R4 F .FUNCT-1K1 \<one>\<^sub>M & ( for n be NatNAT-1M1 holds 0NUMBERSK6 <>HIDDENR2 n & n <XXREAL-0R3 lenFINSEQ-1K4 F implies f1 .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 g .BINOP-1K1(f1 .NAT-1K8\<^bsub>(D)\<^esub> n,F .FUNCT-1K1 (n +NAT-1K1 \<one>\<^sub>M)))) & d1 =XBOOLE-0R4 f1 .NAT-1K8\<^bsub>(D)\<^esub> lenFINSEQ-1K4 F"
          then obtain f1 where
            [ty]:"f1 be sequenceNAT-1M2-of D" and 
            A28: "f1 .NAT-1K8\<^bsub>(D)\<^esub> \<one>\<^sub>M =XBOOLE-0R4 F .FUNCT-1K1 \<one>\<^sub>M"and A29: " for n be NatNAT-1M1 holds 0NUMBERSK6 <>HIDDENR2 n & n <XXREAL-0R3 lenFINSEQ-1K4 F implies f1 .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 g .BINOP-1K1(f1 .NAT-1K8\<^bsub>(D)\<^esub> n,F .FUNCT-1K1 (n +NAT-1K1 \<one>\<^sub>M))"and A30: "d1 =XBOOLE-0R4 f1 .NAT-1K8\<^bsub>(D)\<^esub> lenFINSEQ-1K4 F"
             sorry
          assume Given: " ex f2 be sequenceNAT-1M2-of D st (f2 .NAT-1K8\<^bsub>(D)\<^esub> \<one>\<^sub>M =XBOOLE-0R4 F .FUNCT-1K1 \<one>\<^sub>M & ( for n be NatNAT-1M1 holds 0NUMBERSK6 <>HIDDENR2 n & n <XXREAL-0R3 lenFINSEQ-1K4 F implies f2 .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 g .BINOP-1K1(f2 .NAT-1K8\<^bsub>(D)\<^esub> n,F .FUNCT-1K1 (n +NAT-1K1 \<one>\<^sub>M)))) & d2 =XBOOLE-0R4 f2 .NAT-1K8\<^bsub>(D)\<^esub> lenFINSEQ-1K4 F"
          then obtain f2 where
            [ty]:"f2 be sequenceNAT-1M2-of D" and 
            A31: "f2 .NAT-1K8\<^bsub>(D)\<^esub> \<one>\<^sub>M =XBOOLE-0R4 F .FUNCT-1K1 \<one>\<^sub>M"and A32: " for n be NatNAT-1M1 holds 0NUMBERSK6 <>HIDDENR2 n & n <XXREAL-0R3 lenFINSEQ-1K4 F implies f2 .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 g .BINOP-1K1(f2 .NAT-1K8\<^bsub>(D)\<^esub> n,F .FUNCT-1K1 (n +NAT-1K1 \<one>\<^sub>M))"and A33: "d2 =XBOOLE-0R4 f2 .NAT-1K8\<^bsub>(D)\<^esub> lenFINSEQ-1K4 F"
             sorry
          let ?P = "\<lambda>Lamb1. Lamb1 <>HIDDENR2 0NUMBERSK6 & Lamb1 <=XXREAL-0R1 lenFINSEQ-1K4 F implies f1 .NAT-1K8\<^bsub>(D)\<^esub> Lamb1 =XBOOLE-0R4 f2 .NAT-1K8\<^bsub>(D)\<^esub> Lamb1"
          have A34: " for n be NatNAT-1M1 holds ?P(n) implies ?P(n +NAT-1K1 \<one>\<^sub>M)"
          proof-
            have " for n be NatNAT-1M1 holds (n <>HIDDENR2 0NUMBERSK6 & n <=XXREAL-0R1 lenFINSEQ-1K4 F implies f1 .NAT-1K8\<^bsub>(D)\<^esub> n =XBOOLE-0R4 f2 .NAT-1K8\<^bsub>(D)\<^esub> n) implies (n +NAT-1K1 \<one>\<^sub>M <>HIDDENR2 0NUMBERSK6 & n +NAT-1K1 \<one>\<^sub>M <=XXREAL-0R1 lenFINSEQ-1K4 F implies f1 .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 f2 .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M))"
            proof(rule ballI,rule impI,rule impMI ,rule impI)
              fix n assume [ty]: "n be NatNAT-1M1"
              assume A35: "n <>HIDDENR2 0NUMBERSK6 & n <=XXREAL-0R1 lenFINSEQ-1K4 F implies f1 .NAT-1K8\<^bsub>(D)\<^esub> n =XBOOLE-0R4 f2 .NAT-1K8\<^bsub>(D)\<^esub> n"
              assume "n +NAT-1K1 \<one>\<^sub>M <>HIDDENR2 0NUMBERSK6"
                and A36: "n +NAT-1K1 \<one>\<^sub>M <=XXREAL-0R1 lenFINSEQ-1K4 F"
              have "f1 .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 f2 .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M)"
              proof-
                show "f1 .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 f2 .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M)"
                proof-
                  have cases: "n =XBOOLE-0R4 0NUMBERSK6 or n <>HIDDENR2 0NUMBERSK6"
                     sorry
                  have case1: "n =XBOOLE-0R4 0NUMBERSK6 implies f1 .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 f2 .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M)"
                  proof(rule impI)
                    assume "n =XBOOLE-0R4 0NUMBERSK6"
                    thus "f1 .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 f2 .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M)"
                      using A28 A31 sorry
                  qed
                  have case2: "n <>HIDDENR2 0NUMBERSK6 implies f1 .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 f2 .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M)"
                  proof(rule impI)
                    assume A37: "n <>HIDDENR2 0NUMBERSK6"
                    have A38: "n <XXREAL-0R3 lenFINSEQ-1K4 F"
                      using A36 nat_1_th_13 sorry
                    then have "f1 .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 g .BINOP-1K1(f1 .NAT-1K8\<^bsub>(D)\<^esub> n,F .FUNCT-1K1 (n +NAT-1K1 \<one>\<^sub>M))"
                      using A29 A37 sorry
                    thus "f1 .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 f2 .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M)"
                      using A32 A35 A37 A38 sorry
                  qed
                  show " ?thesis "
                    using cases case1 case2 sorry
                qed
              qed
              thus "f1 .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 f2 .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M)"
                 sorry
            qed "sorry"
            thus " ?thesis "
               sorry
          qed
          have A39: "?P(0NUMBERSK6)"
             sorry
          have " for n be NatNAT-1M1 holds ?P(n)"
            using nat_1_sch_2 A39 A34 sorry
          thus "d1 =HIDDENR1 d2"
            using A1 A27 A30 A33 sorry
        qed "sorry"
        thus " ?thesis "
           sorry
      qed
    qed
  (*consistency*)
    show "g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> or lenFINSEQ-1K4 F >=XXREAL-0R2 \<one>\<^sub>M implies ( for it be ElementSUBSET-1M1-of D holds  True )"
    proof(rule impI)
      assume Assume: "g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> or lenFINSEQ-1K4 F >=XXREAL-0R2 \<one>\<^sub>M"
      have A1: "g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> or lenFINSEQ-1K4 F >=XXREAL-0R2 \<one>\<^sub>M"
        using Assume sorry
      show " for it be ElementSUBSET-1M1-of D holds  True "
         sorry
    qed
qed "sorry"

mtheorem finsop_1_th_1:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for F be FinSequenceFINSEQ-1M3-of D holds  for g be BinOpBINOP-1M2-of D holds lenFINSEQ-1K4 F >=XXREAL-0R2 \<one>\<^sub>M implies ( ex f be sequenceNAT-1M2-of D st (f .NAT-1K8\<^bsub>(D)\<^esub> \<one>\<^sub>M =XBOOLE-0R4 F .FUNCT-1K1 \<one>\<^sub>M & ( for n be NatNAT-1M1 holds 0NUMBERSK6 <>HIDDENR2 n & n <XXREAL-0R3 lenFINSEQ-1K4 F implies f .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 g .BINOP-1K1(f .NAT-1K8\<^bsub>(D)\<^esub> n,F .FUNCT-1K1 (n +NAT-1K1 \<one>\<^sub>M)))) & g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F =XBOOLE-0R4 f .NAT-1K8\<^bsub>(D)\<^esub> lenFINSEQ-1K4 F)"
  using finsop_1_def_1 sorry

mtheorem finsop_1_th_2:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d be ElementSUBSET-1M1-of D holds  for F be FinSequenceFINSEQ-1M3-of D holds  for g be BinOpBINOP-1M2-of D holds lenFINSEQ-1K4 F >=XXREAL-0R2 \<one>\<^sub>M & ( ex f be sequenceNAT-1M2-of D st (f .NAT-1K8\<^bsub>(D)\<^esub> \<one>\<^sub>M =XBOOLE-0R4 F .FUNCT-1K1 \<one>\<^sub>M & ( for n be NatNAT-1M1 holds 0NUMBERSK6 <>HIDDENR2 n & n <XXREAL-0R3 lenFINSEQ-1K4 F implies f .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 g .BINOP-1K1(f .NAT-1K8\<^bsub>(D)\<^esub> n,F .FUNCT-1K1 (n +NAT-1K1 \<one>\<^sub>M)))) & d =XBOOLE-0R4 f .NAT-1K8\<^bsub>(D)\<^esub> lenFINSEQ-1K4 F) implies d =XBOOLE-0R4 g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F"
  using finsop_1_def_1 sorry

syntax FINSOP_1K2 :: " Set \<Rightarrow>  Set \<Rightarrow>  Set \<Rightarrow> Set" (" _ +*FINSOP-1K2\<^bsub>'( _ ')\<^esub>  _ " [164,0,164]164)
translations "F +*FINSOP-1K2\<^bsub>(A)\<^esub> p" \<rightharpoonup> "F +*FUNCT-4K1 p"

mtheorem finsop_1_add_1:
  mlet "A be  non emptyXBOOLE-0V1\<bar>setHIDDENM2", "F be sequenceNAT-1M2-of A", "p be FinSequenceFINSEQ-1M3-of A"
"cluster F +*FUNCT-4K1 p as-term-is sequenceNAT-1M2-of A"
proof
(*coherence*)
  show "F +*FUNCT-4K1 p be sequenceNAT-1M2-of A"
  proof-
    have A1: "domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> F =XBOOLE-0R4 NATNUMBERSK1"
      using funct_2_def_1 sorry
    have "domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> (F +*FUNCT-4K9\<^bsub>(NATNUMBERSK1,A)\<^esub> p) =HIDDENR1 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> F \\/SUBSET-1K4\<^bsub>(NATNUMBERSK1)\<^esub> domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> p"
      using funct_4_def_1 sorry
    also have "... = NATNUMBERSK1"
      using A1 xboole_1_th_12 sorry
    finally have "domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> (F +*FUNCT-4K9\<^bsub>(NATNUMBERSK1,A)\<^esub> p) =HIDDENR1 NATNUMBERSK1"
       sorry
    thus "F +*FUNCT-4K1 p be sequenceNAT-1M2-of A"
      using funct_2_def_1 sorry
  qed
qed "sorry"

abbreviation(input) FINSOP_1K3("findomFINSOP-1K3  _ " [164]164) where
  "findomFINSOP-1K3 f \<equiv> domRELAT-1K1 f"

abbreviation(input) FINSOP_1K4("findomFINSOP-1K4  _ " [164]164) where
  "findomFINSOP-1K4 f \<equiv> domRELAT-1K1 f"

mtheorem finsop_1_add_2:
  mlet "f be FinSequenceFINSEQ-1M1"
"cluster domRELAT-1K1 f as-term-is ElementSUBSET-1M1-of FinFINSUB-1K5 NATNUMBERSK1"
proof
(*coherence*)
  show "domRELAT-1K1 f be ElementSUBSET-1M1-of FinFINSUB-1K5 NATNUMBERSK1"
  proof-
    have "domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> f =XBOOLE-0R4 SegFINSEQ-1K2 (lenFINSEQ-1K4 f)"
      using finseq_1_def_3 sorry
    thus "domRELAT-1K1 f be ElementSUBSET-1M1-of FinFINSUB-1K5 NATNUMBERSK1"
      using finsub_1_def_5 sorry
  qed
qed "sorry"

mlemma finsop_1_lm_1:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for F be FinSequenceFINSEQ-1M3-of D holds  for g be BinOpBINOP-1M2-of D holds (lenFINSEQ-1K4 F >=XXREAL-0R2 \<one>\<^sub>M & g be associativeBINOP-1V2\<^bsub>(D)\<^esub>) & g be commutativeBINOP-1V1\<^bsub>(D)\<^esub> implies g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F =XBOOLE-0R4 g $$SETWISEOK10\<^bsub>(NATNUMBERSK1,D)\<^esub>(findomFINSOP-1K4 F,(NATNUMBERSK1 -->FUNCOP-1K8\<^bsub>(D)\<^esub> the-unity-wrtBINOP-1K3\<^bsub>(D)\<^esub> g)+*FINSOP-1K2\<^bsub>(D)\<^esub> F)"
proof-
  have " for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for F be FinSequenceFINSEQ-1M3-of D holds  for g be BinOpBINOP-1M2-of D holds lenFINSEQ-1K4 F >=XXREAL-0R2 \<one>\<^sub>M & (g be associativeBINOP-1V2\<^bsub>(D)\<^esub> & g be commutativeBINOP-1V1\<^bsub>(D)\<^esub>) implies g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F =XBOOLE-0R4 g $$SETWISEOK10\<^bsub>(NATNUMBERSK1,D)\<^esub>(findomFINSOP-1K4 F,(NATNUMBERSK1 -->FUNCOP-1K8\<^bsub>(D)\<^esub> the-unity-wrtBINOP-1K3\<^bsub>(D)\<^esub> g)+*FINSOP-1K2\<^bsub>(D)\<^esub> F)"
  proof(rule ballI,rule ballI,rule ballI,rule impMI ,rule impI)
    fix D assume [ty]: "D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
    fix F assume [ty]: "F be FinSequenceFINSEQ-1M3-of D"
    fix g assume [ty]: "g be BinOpBINOP-1M2-of D"
    assume A1: "lenFINSEQ-1K4 F >=XXREAL-0R2 \<one>\<^sub>M"
      and A2: "g be associativeBINOP-1V2\<^bsub>(D)\<^esub> & g be commutativeBINOP-1V1\<^bsub>(D)\<^esub>"
    let ?A = "findomFINSOP-1K4 F"
    let ?h = "(NATNUMBERSK1 -->FUNCOP-1K8\<^bsub>(D)\<^esub> the-unity-wrtBINOP-1K3\<^bsub>(D)\<^esub> g)+*FINSOP-1K2\<^bsub>(D)\<^esub> F"
    have A3: "domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> F =XBOOLE-0R4 SegFINSEQ-1K2 (lenFINSEQ-1K4 F)"
      using finseq_1_def_3 sorry
    then obtain G where
      [ty]:"G be FunctionFUNCT-2M1-of(FinFINSUB-1K5 NATNUMBERSK1,D)" and 
      A4: "g $$SETWISEOK10\<^bsub>(NATNUMBERSK1,D)\<^esub>(?A,?h) =XBOOLE-0R4 G .FUNCT-1K1 ?A"and " for d be ElementSUBSET-1M1-of D holds d is-a-unity-wrtBINOP-1R3\<^bsub>(D)\<^esub> g implies G .FUNCT-1K1 {}XBOOLE-0K1 =XBOOLE-0R4 d"and A5: " for n be ElementSUBSET-1M1-of NATNUMBERSK1 holds G .FUNCT-1K1 {TARSKIK1 n} =XBOOLE-0R4 ?h .NAT-1K8\<^bsub>(D)\<^esub> n"and A6: " for B be ElementSUBSET-1M1-of FinFINSUB-1K5 NATNUMBERSK1 holds B c=TARSKIR1 ?A & B <>HIDDENR2 {}XBOOLE-0K1 implies ( for n be ElementSUBSET-1M1-of NATNUMBERSK1 holds n inTARSKIR2 ?A \\SETWISEOK9\<^bsub>(NATNUMBERSK1)\<^esub> B implies G .FUNCT-1K1 (B \\/XBOOLE-0K2 {TARSKIK1 n}) =XBOOLE-0R4 g .BINOP-1K1(G .FUNCT-1K1 B,?h .NAT-1K8\<^bsub>(D)\<^esub> n))"
      using A1 A2 setwiseo_def_3 sorry
    obtain f where
      [ty]:"f be sequenceNAT-1M2-of D" and 
      A7: "f .NAT-1K8\<^bsub>(D)\<^esub> \<one>\<^sub>M =XBOOLE-0R4 F .FUNCT-1K1 \<one>\<^sub>M"and A8: " for n be NatNAT-1M1 holds 0NUMBERSK6 <>HIDDENR2 n & n <XXREAL-0R3 lenFINSEQ-1K4 F implies f .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 g .BINOP-1K1(f .NAT-1K8\<^bsub>(D)\<^esub> n,F .FUNCT-1K1 (n +NAT-1K1 \<one>\<^sub>M))"and A9: "g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F =XBOOLE-0R4 f .NAT-1K8\<^bsub>(D)\<^esub> lenFINSEQ-1K4 F"
      using A1 finsop_1_def_1 sorry
    let ?P = "\<lambda>Lamb1. Lamb1 <>HIDDENR2 0NUMBERSK6 & Lamb1 <=XXREAL-0R1 lenFINSEQ-1K4 F implies f .NAT-1K8\<^bsub>(D)\<^esub> Lamb1 =XBOOLE-0R4 G .FUNCT-1K1 SegFINSEQ-1K2 Lamb1"
    have A10: " for n be NatNAT-1M1 holds ?P(n) implies ?P(n +NAT-1K1 \<one>\<^sub>M)"
    proof-
      have " for n be NatNAT-1M1 holds (n <>HIDDENR2 0NUMBERSK6 & n <=XXREAL-0R1 lenFINSEQ-1K4 F implies f .NAT-1K8\<^bsub>(D)\<^esub> n =XBOOLE-0R4 G .FUNCT-1K1 SegFINSEQ-1K2 n) implies (n +NAT-1K1 \<one>\<^sub>M <>HIDDENR2 0NUMBERSK6 & n +NAT-1K1 \<one>\<^sub>M <=XXREAL-0R1 lenFINSEQ-1K4 F implies f .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 G .FUNCT-1K1 SegFINSEQ-1K2 (n +NAT-1K1 \<one>\<^sub>M))"
      proof(rule ballI,rule impI,rule impMI ,rule impI)
        fix n assume [ty]: "n be NatNAT-1M1"
        assume A11: "n <>HIDDENR2 0NUMBERSK6 & n <=XXREAL-0R1 lenFINSEQ-1K4 F implies f .NAT-1K8\<^bsub>(D)\<^esub> n =XBOOLE-0R4 G .FUNCT-1K1 SegFINSEQ-1K2 n"
        assume "n +NAT-1K1 \<one>\<^sub>M <>HIDDENR2 0NUMBERSK6"
          and A12: "n +NAT-1K1 \<one>\<^sub>M <=XXREAL-0R1 lenFINSEQ-1K4 F"
        have "f .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 G .FUNCT-1K1 SegFINSEQ-1K2 (n +NAT-1K1 \<one>\<^sub>M)"
        proof-
          show "f .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 G .FUNCT-1K1 SegFINSEQ-1K2 (n +NAT-1K1 \<one>\<^sub>M)"
          proof-
            have cases: "n =XBOOLE-0R4 0NUMBERSK6 or n <>HIDDENR2 0NUMBERSK6"
               sorry
            have case1: "n =XBOOLE-0R4 0NUMBERSK6 implies f .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 G .FUNCT-1K1 SegFINSEQ-1K2 (n +NAT-1K1 \<one>\<^sub>M)"
            proof(rule impI)
              assume A13: "n =XBOOLE-0R4 0NUMBERSK6"
              have "\<one>\<^sub>M inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> F"
                using A1 A3 finseq_1_th_1 sorry
              then have "?h .NAT-1K8\<^bsub>(D)\<^esub> \<one>\<^sub>M =XBOOLE-0R4 F .FUNCT-1K1 \<one>\<^sub>M"
                using funct_4_th_13 sorry
              thus "f .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 G .FUNCT-1K1 SegFINSEQ-1K2 (n +NAT-1K1 \<one>\<^sub>M)"
                using A7 A5 A13 finseq_1_th_2 sorry
            qed
            have case2: "n <>HIDDENR2 0NUMBERSK6 implies f .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 G .FUNCT-1K1 SegFINSEQ-1K2 (n +NAT-1K1 \<one>\<^sub>M)"
            proof(rule impI)
              assume A14: "n <>HIDDENR2 0NUMBERSK6"
              obtain B where 
                [ty]:"B be ElementSUBSET-1M1-of FinFINSUB-1K5 NATNUMBERSK1" and BDef:"B = SegFINSEQ-1K2 n"
                using finsub_1_def_5 sorry
              have "n +NAT-1K1 \<one>\<^sub>M >=XXREAL-0R2 \<one>\<^sub>M"
                using nat_1_th_12 sorry
              then have A15: "n +NAT-1K1 \<one>\<^sub>M inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> F"
                using A12 finseq_3_th_25 sorry
              have A16: "n <XXREAL-0R3 lenFINSEQ-1K4 F"
                using A12 nat_1_th_13 sorry
              then have A17: "f .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 g .BINOP-1K1(f .NAT-1K8\<^bsub>(D)\<^esub> n,F .FUNCT-1K1 (n +NAT-1K1 \<one>\<^sub>M))"
                using A8 A14 sorry
              have " not n +NAT-1K1 \<one>\<^sub>M inTARSKIR2 SegFINSEQ-1K2 n"
                using finseq_3_th_10 sorry
              then have A18: "n +NAT-1K1 \<one>\<^sub>M inTARSKIR2 ?A \\SUBSET-1K6 SegFINSEQ-1K2 n"
                using A15 xboole_0_def_5 sorry
              have A19: "SegFINSEQ-1K2 n c=TARSKIR1 ?A"
                using A3 A16 finseq_1_th_5 sorry
              have "G .FUNCT-1K1 SegFINSEQ-1K2 (n +NAT-1K1 \<one>\<^sub>M) =HIDDENR1 G .FUNCT-1K1 (SegFINSEQ-1K2 n \\/XBOOLE-0K2 {TARSKIK1 n +NAT-1K1 \<one>\<^sub>M })"
                using finseq_1_th_9 sorry
              also have "... = g .BINOP-1K1(G .FUNCT-1K1 B,?h .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M))"
                using A6 A14 A19 A18 sorry
              finally have "G .FUNCT-1K1 SegFINSEQ-1K2 (n +NAT-1K1 \<one>\<^sub>M) =HIDDENR1 g .BINOP-1K1(G .FUNCT-1K1 B,?h .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M))"
                 sorry
              thus "f .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 G .FUNCT-1K1 SegFINSEQ-1K2 (n +NAT-1K1 \<one>\<^sub>M)"
                using A11 A12 A14 A17 A15 funct_4_th_13 nat_1_th_13 sorry
            qed
            show " ?thesis "
              using cases case1 case2 sorry
          qed
        qed
        thus "f .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 G .FUNCT-1K1 SegFINSEQ-1K2 (n +NAT-1K1 \<one>\<^sub>M)"
           sorry
      qed "sorry"
      thus " ?thesis "
         sorry
    qed
    have A20: "?P(0NUMBERSK6)"
       sorry
    have " for n be NatNAT-1M1 holds ?P(n)"
      using nat_1_sch_2 A20 A10 sorry
    thus "g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F =XBOOLE-0R4 g $$SETWISEOK10\<^bsub>(NATNUMBERSK1,D)\<^esub>(findomFINSOP-1K4 F,(NATNUMBERSK1 -->FUNCOP-1K8\<^bsub>(D)\<^esub> the-unity-wrtBINOP-1K3\<^bsub>(D)\<^esub> g)+*FINSOP-1K2\<^bsub>(D)\<^esub> F)"
      using A1 A9 A3 A4 sorry
  qed "sorry"
  thus " ?thesis "
     sorry
qed

mlemma finsop_1_lm_2:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for F be FinSequenceFINSEQ-1M3-of D holds  for g be BinOpBINOP-1M2-of D holds ((lenFINSEQ-1K4 F =XBOOLE-0R4 0NUMBERSK6 & g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub>) & g be associativeBINOP-1V2\<^bsub>(D)\<^esub>) & g be commutativeBINOP-1V1\<^bsub>(D)\<^esub> implies g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F =XBOOLE-0R4 g $$SETWISEOK10\<^bsub>(NATNUMBERSK1,D)\<^esub>(findomFINSOP-1K4 F,(NATNUMBERSK1 -->FUNCOP-1K8\<^bsub>(D)\<^esub> the-unity-wrtBINOP-1K3\<^bsub>(D)\<^esub> g)+*FINSOP-1K2\<^bsub>(D)\<^esub> F)"
proof-
  have " for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for F be FinSequenceFINSEQ-1M3-of D holds  for g be BinOpBINOP-1M2-of D holds lenFINSEQ-1K4 F =XBOOLE-0R4 0NUMBERSK6 & (g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> & (g be associativeBINOP-1V2\<^bsub>(D)\<^esub> & g be commutativeBINOP-1V1\<^bsub>(D)\<^esub>)) implies g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F =HIDDENR1 g $$SETWISEOK10\<^bsub>(NATNUMBERSK1,D)\<^esub>(findomFINSOP-1K4 F,(NATNUMBERSK1 -->FUNCOP-1K8\<^bsub>(D)\<^esub> the-unity-wrtBINOP-1K3\<^bsub>(D)\<^esub> g)+*FINSOP-1K2\<^bsub>(D)\<^esub> F)"
  proof(rule ballI,rule ballI,rule ballI,rule impMI ,rule impMI ,rule impI)
    fix D assume [ty]: "D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
    fix F assume [ty]: "F be FinSequenceFINSEQ-1M3-of D"
    fix g assume [ty]: "g be BinOpBINOP-1M2-of D"
    assume A1: "lenFINSEQ-1K4 F =XBOOLE-0R4 0NUMBERSK6"
      and A2: "g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub>"
      and A3: "g be associativeBINOP-1V2\<^bsub>(D)\<^esub> & g be commutativeBINOP-1V1\<^bsub>(D)\<^esub>"
    have "F =XBOOLE-0R4 {}XBOOLE-0K1"
      using A1 sorry
    then have A4: "domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> F =XBOOLE-0R4 {}.SETWISEOK1 NATNUMBERSK1"
       sorry
    have "g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F =HIDDENR1 the-unity-wrtBINOP-1K3\<^bsub>(D)\<^esub> g"
      using A1 A2 finsop_1_def_1 sorry
    also have "... = g $$SETWISEOK10\<^bsub>(NATNUMBERSK1,D)\<^esub>(findomFINSOP-1K4 F,(NATNUMBERSK1 -->FUNCOP-1K8\<^bsub>(D)\<^esub> the-unity-wrtBINOP-1K3\<^bsub>(D)\<^esub> g)+*FINSOP-1K2\<^bsub>(D)\<^esub> F)"
      using A2 A3 A4 setwiseo_th_31 sorry
    finally show "g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F =HIDDENR1 g $$SETWISEOK10\<^bsub>(NATNUMBERSK1,D)\<^esub>(findomFINSOP-1K4 F,(NATNUMBERSK1 -->FUNCOP-1K8\<^bsub>(D)\<^esub> the-unity-wrtBINOP-1K3\<^bsub>(D)\<^esub> g)+*FINSOP-1K2\<^bsub>(D)\<^esub> F)"
       sorry
  qed "sorry"
  thus " ?thesis "
     sorry
qed

mtheorem finsop_1_th_3:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for F be FinSequenceFINSEQ-1M3-of D holds  for g be BinOpBINOP-1M2-of D holds ((g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> or lenFINSEQ-1K4 F >=XXREAL-0R2 \<one>\<^sub>M) & g be associativeBINOP-1V2\<^bsub>(D)\<^esub>) & g be commutativeBINOP-1V1\<^bsub>(D)\<^esub> implies g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F =XBOOLE-0R4 g $$SETWISEOK10\<^bsub>(NATNUMBERSK1,D)\<^esub>(findomFINSOP-1K4 F,(NATNUMBERSK1 -->FUNCOP-1K8\<^bsub>(D)\<^esub> the-unity-wrtBINOP-1K3\<^bsub>(D)\<^esub> g)+*FINSOP-1K2\<^bsub>(D)\<^esub> F)"
proof-
  have " for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for F be FinSequenceFINSEQ-1M3-of D holds  for g be BinOpBINOP-1M2-of D holds  not ((( not ( not g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> &  not lenFINSEQ-1K4 F >=XXREAL-0R2 \<one>\<^sub>M) & g be associativeBINOP-1V2\<^bsub>(D)\<^esub>) & g be commutativeBINOP-1V1\<^bsub>(D)\<^esub>) &  not g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F =XBOOLE-0R4 g $$SETWISEOK10\<^bsub>(NATNUMBERSK1,D)\<^esub>(findomFINSOP-1K4 F,(NATNUMBERSK1 -->FUNCOP-1K8\<^bsub>(D)\<^esub> the-unity-wrtBINOP-1K3\<^bsub>(D)\<^esub> g)+*FINSOP-1K2\<^bsub>(D)\<^esub> F))"
  proof(rule ballI,rule ballI,rule ballI)
    fix D assume [ty]: "D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
    fix F assume [ty]: "F be FinSequenceFINSEQ-1M3-of D"
    fix g assume [ty]: "g be BinOpBINOP-1M2-of D"
    have "lenFINSEQ-1K4 F =XBOOLE-0R4 0NUMBERSK6 or lenFINSEQ-1K4 F >=XXREAL-0R2 \<one>\<^sub>M"
      using nat_1_th_14 sorry
    thus " not ((( not ( not g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> &  not lenFINSEQ-1K4 F >=XXREAL-0R2 \<one>\<^sub>M) & g be associativeBINOP-1V2\<^bsub>(D)\<^esub>) & g be commutativeBINOP-1V1\<^bsub>(D)\<^esub>) &  not g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F =XBOOLE-0R4 g $$SETWISEOK10\<^bsub>(NATNUMBERSK1,D)\<^esub>(findomFINSOP-1K4 F,(NATNUMBERSK1 -->FUNCOP-1K8\<^bsub>(D)\<^esub> the-unity-wrtBINOP-1K3\<^bsub>(D)\<^esub> g)+*FINSOP-1K2\<^bsub>(D)\<^esub> F))"
      using finsop_1_lm_1 finsop_1_lm_2 sorry
  qed "sorry"
  thus " ?thesis "
     sorry
qed

mlemma finsop_1_lm_3:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for g be BinOpBINOP-1M2-of D holds g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> implies g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> <*>FINSEQ-1K7 D =XBOOLE-0R4 the-unity-wrtBINOP-1K3\<^bsub>(D)\<^esub> g"
proof-
  have " for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for g be BinOpBINOP-1M2-of D holds g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> implies g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> <*>FINSEQ-1K7 D =XBOOLE-0R4 the-unity-wrtBINOP-1K3\<^bsub>(D)\<^esub> g"
  proof(rule ballI,rule ballI,rule impI)
    fix D assume [ty]: "D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
    fix g assume [ty]: "g be BinOpBINOP-1M2-of D"
    have A1: "lenFINSEQ-1K4 <*>FINSEQ-1K7 D =XBOOLE-0R4 0NUMBERSK6"
       sorry
    assume "g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub>"
    thus "g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> <*>FINSEQ-1K7 D =XBOOLE-0R4 the-unity-wrtBINOP-1K3\<^bsub>(D)\<^esub> g"
      using A1 finsop_1_def_1 sorry
  qed "sorry"
  thus " ?thesis "
     sorry
qed

mlemma finsop_1_lm_4:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d be ElementSUBSET-1M1-of D holds  for g be BinOpBINOP-1M2-of D holds g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> <*FINSEQ-1K13\<^bsub>(D)\<^esub> d*> =XBOOLE-0R4 d"
proof-
  have " for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d be ElementSUBSET-1M1-of D holds  for g be BinOpBINOP-1M2-of D holds g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> <*FINSEQ-1K13\<^bsub>(D)\<^esub> d*> =XBOOLE-0R4 d"
  proof(rule ballI,rule ballI,rule ballI)
    fix D assume [ty]: "D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
    fix d assume [ty]: "d be ElementSUBSET-1M1-of D"
    fix g assume [ty]: "g be BinOpBINOP-1M2-of D"
    have A1: "lenFINSEQ-1K4 (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>) =XBOOLE-0R4 \<one>\<^sub>M"
      using finseq_1_th_39 sorry
    then have " ex f be sequenceNAT-1M2-of D st (f .NAT-1K8\<^bsub>(D)\<^esub> \<one>\<^sub>M =XBOOLE-0R4 (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>).FUNCT-1K1 \<one>\<^sub>M & ( for n be NatNAT-1M1 holds 0NUMBERSK6 <>HIDDENR2 n & n <XXREAL-0R3 lenFINSEQ-1K4 (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>) implies f .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 g .BINOP-1K1(f .NAT-1K8\<^bsub>(D)\<^esub> n,(<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>).FUNCT-1K1 (n +NAT-1K1 \<one>\<^sub>M)))) & g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> <*FINSEQ-1K13\<^bsub>(D)\<^esub> d*> =XBOOLE-0R4 f .NAT-1K8\<^bsub>(D)\<^esub> lenFINSEQ-1K4 (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>)"
      using finsop_1_def_1 sorry
    thus "g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> <*FINSEQ-1K13\<^bsub>(D)\<^esub> d*> =XBOOLE-0R4 d"
      using A1 finseq_1_def_8 sorry
  qed "sorry"
  thus " ?thesis "
     sorry
qed

mlemma finsop_1_lm_5:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d be ElementSUBSET-1M1-of D holds  for F be FinSequenceFINSEQ-1M3-of D holds  for g be BinOpBINOP-1M2-of D holds lenFINSEQ-1K4 F >=XXREAL-0R2 \<one>\<^sub>M implies g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F ^FINSEQ-1K9\<^bsub>(D)\<^esub> (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>) =XBOOLE-0R4 g .BINOP-1K4\<^bsub>(D)\<^esub>(g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F,d)"
proof-
  have " for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d be ElementSUBSET-1M1-of D holds  for F be FinSequenceFINSEQ-1M3-of D holds  for g be BinOpBINOP-1M2-of D holds lenFINSEQ-1K4 F >=XXREAL-0R2 \<one>\<^sub>M implies g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F ^FINSEQ-1K9\<^bsub>(D)\<^esub> (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>) =XBOOLE-0R4 g .BINOP-1K4\<^bsub>(D)\<^esub>(g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F,d)"
  proof(rule ballI,rule ballI,rule ballI,rule ballI,rule impI)
    fix D assume [ty]: "D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
    fix d assume [ty]: "d be ElementSUBSET-1M1-of D"
    fix F assume [ty]: "F be FinSequenceFINSEQ-1M3-of D"
    fix g assume [ty]: "g be BinOpBINOP-1M2-of D"
    let ?G = "F ^FINSEQ-1K9\<^bsub>(D)\<^esub> (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>)"
    have A1: "?G .FUNCT-1K1 (lenFINSEQ-1K4 F +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 d"
      using finseq_1_th_42 sorry
    have A2: "lenFINSEQ-1K4 ?G =HIDDENR1 lenFINSEQ-1K4 F +NAT-1K1 lenFINSEQ-1K4 (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>)"
      using finseq_1_th_22 sorry
    also have "... = lenFINSEQ-1K4 F +NAT-1K1 \<one>\<^sub>M"
      using finseq_1_th_39 sorry
    finally have "lenFINSEQ-1K4 ?G =HIDDENR1 lenFINSEQ-1K4 F +NAT-1K1 \<one>\<^sub>M"
       sorry
    then have "\<one>\<^sub>M <=XXREAL-0R1 lenFINSEQ-1K4 ?G"
      using nat_1_th_12 sorry
    then obtain f1 where
      [ty]:"f1 be sequenceNAT-1M2-of D" and 
      A3: "f1 .NAT-1K8\<^bsub>(D)\<^esub> \<one>\<^sub>M =XBOOLE-0R4 ?G .FUNCT-1K1 \<one>\<^sub>M"and A4: " for n be NatNAT-1M1 holds 0NUMBERSK6 <>HIDDENR2 n & n <XXREAL-0R3 lenFINSEQ-1K4 ?G implies f1 .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 g .BINOP-1K1(f1 .NAT-1K8\<^bsub>(D)\<^esub> n,?G .FUNCT-1K1 (n +NAT-1K1 \<one>\<^sub>M))"and A5: "g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> ?G =XBOOLE-0R4 f1 .NAT-1K8\<^bsub>(D)\<^esub> lenFINSEQ-1K4 ?G"
      using finsop_1_def_1 sorry
    assume A6: "lenFINSEQ-1K4 F >=XXREAL-0R2 \<one>\<^sub>M"
    then obtain f where
      [ty]:"f be sequenceNAT-1M2-of D" and 
      A7: "f .NAT-1K8\<^bsub>(D)\<^esub> \<one>\<^sub>M =XBOOLE-0R4 F .FUNCT-1K1 \<one>\<^sub>M"and A8: " for n be NatNAT-1M1 holds 0NUMBERSK6 <>HIDDENR2 n & n <XXREAL-0R3 lenFINSEQ-1K4 F implies f .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 g .BINOP-1K1(f .NAT-1K8\<^bsub>(D)\<^esub> n,F .FUNCT-1K1 (n +NAT-1K1 \<one>\<^sub>M))"and A9: "g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F =XBOOLE-0R4 f .NAT-1K8\<^bsub>(D)\<^esub> lenFINSEQ-1K4 F"
      using finsop_1_def_1 sorry
    let ?P = "\<lambda>Lamb1. 0NUMBERSK6 <>HIDDENR2 Lamb1 & Lamb1 <XXREAL-0R3 lenFINSEQ-1K4 ?G implies f .NAT-1K8\<^bsub>(D)\<^esub> Lamb1 =XBOOLE-0R4 f1 .NAT-1K8\<^bsub>(D)\<^esub> Lamb1"
    have A10: " for n be NatNAT-1M1 holds ?P(n) implies ?P(n +NAT-1K1 \<one>\<^sub>M)"
    proof-
      have " for n be NatNAT-1M1 holds (0NUMBERSK6 <>HIDDENR2 n & n <XXREAL-0R3 lenFINSEQ-1K4 (F ^FINSEQ-1K9\<^bsub>(D)\<^esub> (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>)) implies f .NAT-1K8\<^bsub>(D)\<^esub> n =XBOOLE-0R4 f1 .NAT-1K8\<^bsub>(D)\<^esub> n) implies (0NUMBERSK6 <>HIDDENR2 n +NAT-1K1 \<one>\<^sub>M & n +NAT-1K1 \<one>\<^sub>M <XXREAL-0R3 lenFINSEQ-1K4 (F ^FINSEQ-1K9\<^bsub>(D)\<^esub> (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>)) implies f .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 f1 .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M))"
      proof(rule ballI,rule impI,rule impMI ,rule impI)
        fix n assume [ty]: "n be NatNAT-1M1"
        assume A11: "?P(n)"
        assume "0NUMBERSK6 <>HIDDENR2 n +NAT-1K1 \<one>\<^sub>M"
          and A12: "n +NAT-1K1 \<one>\<^sub>M <XXREAL-0R3 lenFINSEQ-1K4 ?G"
        have A13: "n +NAT-1K1 \<one>\<^sub>M >=XXREAL-0R2 \<one>\<^sub>M"
          using nat_1_th_14 sorry
        have "f .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 f1 .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M)"
        proof-
          show "f .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 f1 .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M)"
          proof-
            have cases: "n +NAT-1K1 \<one>\<^sub>M =XBOOLE-0R4 \<one>\<^sub>M or n +NAT-1K1 \<one>\<^sub>M >XXREAL-0R4 \<one>\<^sub>M"
              using A13 xxreal_0_th_1 sorry
            have case1: "n +NAT-1K1 \<one>\<^sub>M =XBOOLE-0R4 \<one>\<^sub>M implies f .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 f1 .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M)"
            proof(rule impI)
              assume A14: "n +NAT-1K1 \<one>\<^sub>M =XBOOLE-0R4 \<one>\<^sub>M"
              have "\<one>\<^sub>M inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> F"
                using A6 finseq_3_th_25 sorry
              thus "f .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 f1 .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M)"
                using A7 A3 A14 finseq_1_def_7 sorry
            qed
            have case2: "n +NAT-1K1 \<one>\<^sub>M >XXREAL-0R4 \<one>\<^sub>M implies f .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 f1 .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M)"
            proof(rule impI)
              assume A15: "n +NAT-1K1 \<one>\<^sub>M >XXREAL-0R4 \<one>\<^sub>M"
              then have "n <>HIDDENR2 0NUMBERSK6"
                 sorry
              then have A16: "f1 .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 g .BINOP-1K1(f1 .NAT-1K8\<^bsub>(D)\<^esub> n,?G .FUNCT-1K1 (n +NAT-1K1 \<one>\<^sub>M))"
                using A4 A12 nat_1_th_12 sorry
              have A17: "n +NAT-1K1 \<one>\<^sub>M <=XXREAL-0R1 lenFINSEQ-1K4 F"
                using A2 A12 nat_1_th_13 sorry
              then have A18: "n <XXREAL-0R3 lenFINSEQ-1K4 F"
                using nat_1_th_13 sorry
              have "\<one>\<^sub>M <=XXREAL-0R1 n +NAT-1K1 \<one>\<^sub>M"
                using nat_1_th_12 sorry
              then have A19: "n +NAT-1K1 \<one>\<^sub>M inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> F"
                using A17 finseq_3_th_25 sorry
              have "n +NAT-1K1 \<one>\<^sub>M >XXREAL-0R4 0NUMBERSK6 +NAT-1K1 \<one>\<^sub>M"
                using A15 sorry
              then have "f .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 g .BINOP-1K1(f .NAT-1K8\<^bsub>(D)\<^esub> n,F .FUNCT-1K1 (n +NAT-1K1 \<one>\<^sub>M))"
                using A8 A18 sorry
              thus "f .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 f1 .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M)"
                using A11 A12 A15 A16 A19 finseq_1_def_7 nat_1_th_12 sorry
            qed
            show " ?thesis "
              using cases case1 case2 sorry
          qed
        qed
        thus "f .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 f1 .NAT-1K8\<^bsub>(D)\<^esub> (n +NAT-1K1 \<one>\<^sub>M)"
           sorry
      qed "sorry"
      thus " ?thesis "
         sorry
    qed
    have A20: "?P(0NUMBERSK6)"
       sorry
    have A21: " for n be NatNAT-1M1 holds ?P(n)"
      using nat_1_sch_2 A20 A10 sorry
    have "g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> ?G =XBOOLE-0R4 g .BINOP-1K1(f1 .NAT-1K8\<^bsub>(D)\<^esub> lenFINSEQ-1K4 F,?G .FUNCT-1K1 (lenFINSEQ-1K4 F +NAT-1K1 \<one>\<^sub>M))"
      using A6 A2 A4 A5 xreal_1_th_29 sorry
    thus "g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F ^FINSEQ-1K9\<^bsub>(D)\<^esub> (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>) =XBOOLE-0R4 g .BINOP-1K4\<^bsub>(D)\<^esub>(g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F,d)"
      using A6 A9 A2 A1 A21 xreal_1_th_29 sorry
  qed "sorry"
  thus " ?thesis "
     sorry
qed

mlemma finsop_1_lm_6:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d be ElementSUBSET-1M1-of D holds  for F be FinSequenceFINSEQ-1M3-of D holds  for g be BinOpBINOP-1M2-of D holds g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> & lenFINSEQ-1K4 F =XBOOLE-0R4 0NUMBERSK6 implies g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F ^FINSEQ-1K9\<^bsub>(D)\<^esub> (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>) =XBOOLE-0R4 g .BINOP-1K4\<^bsub>(D)\<^esub>(g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F,d)"
proof-
  have " for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d be ElementSUBSET-1M1-of D holds  for F be FinSequenceFINSEQ-1M3-of D holds  for g be BinOpBINOP-1M2-of D holds g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> & lenFINSEQ-1K4 F =XBOOLE-0R4 0NUMBERSK6 implies g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F ^FINSEQ-1K9\<^bsub>(D)\<^esub> (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>) =HIDDENR1 g .BINOP-1K4\<^bsub>(D)\<^esub>(g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F,d)"
  proof(rule ballI,rule ballI,rule ballI,rule ballI,rule impMI ,rule impI)
    fix D assume [ty]: "D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
    fix d assume [ty]: "d be ElementSUBSET-1M1-of D"
    fix F assume [ty]: "F be FinSequenceFINSEQ-1M3-of D"
    fix g assume [ty]: "g be BinOpBINOP-1M2-of D"
    assume A1: "g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub>"
      and A2: "lenFINSEQ-1K4 F =XBOOLE-0R4 0NUMBERSK6"
    have "F =FUNCT-1R1 <*>FINSEQ-1K7 D"
      using A2 sorry
    then have "g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F ^FINSEQ-1K9\<^bsub>(D)\<^esub> (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>) =HIDDENR1 g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> <*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>"
      using finseq_1_th_34 sorry
    also have "... = d"
      using finsop_1_lm_4 sorry
    also have "... = g .BINOP-1K4\<^bsub>(D)\<^esub>(the-unity-wrtBINOP-1K3\<^bsub>(D)\<^esub> g,d)"
      using A1 setwiseo_th_15 sorry
    also have "... = g .BINOP-1K4\<^bsub>(D)\<^esub>(g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F,d)"
      using A1 A2 finsop_1_def_1 sorry
    finally show "g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F ^FINSEQ-1K9\<^bsub>(D)\<^esub> (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>) =HIDDENR1 g .BINOP-1K4\<^bsub>(D)\<^esub>(g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F,d)"
       sorry
  qed "sorry"
  thus " ?thesis "
     sorry
qed

mtheorem finsop_1_th_4:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d be ElementSUBSET-1M1-of D holds  for F be FinSequenceFINSEQ-1M3-of D holds  for g be BinOpBINOP-1M2-of D holds g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> or lenFINSEQ-1K4 F >=XXREAL-0R2 \<one>\<^sub>M implies g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F ^FINSEQ-1K9\<^bsub>(D)\<^esub> (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>) =XBOOLE-0R4 g .BINOP-1K4\<^bsub>(D)\<^esub>(g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F,d)"
proof-
  have " for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d be ElementSUBSET-1M1-of D holds  for F be FinSequenceFINSEQ-1M3-of D holds  for g be BinOpBINOP-1M2-of D holds  not ( not ( not g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> &  not lenFINSEQ-1K4 F >=XXREAL-0R2 \<one>\<^sub>M) &  not g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F ^FINSEQ-1K9\<^bsub>(D)\<^esub> (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>) =XBOOLE-0R4 g .BINOP-1K4\<^bsub>(D)\<^esub>(g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F,d))"
  proof(rule ballI,rule ballI,rule ballI,rule ballI)
    fix D assume [ty]: "D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
    fix d assume [ty]: "d be ElementSUBSET-1M1-of D"
    fix F assume [ty]: "F be FinSequenceFINSEQ-1M3-of D"
    fix g assume [ty]: "g be BinOpBINOP-1M2-of D"
    have "lenFINSEQ-1K4 F >=XXREAL-0R2 \<one>\<^sub>M or lenFINSEQ-1K4 F =XBOOLE-0R4 0NUMBERSK6"
      using nat_1_th_14 sorry
    thus " not ( not ( not g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> &  not lenFINSEQ-1K4 F >=XXREAL-0R2 \<one>\<^sub>M) &  not g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F ^FINSEQ-1K9\<^bsub>(D)\<^esub> (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>) =XBOOLE-0R4 g .BINOP-1K4\<^bsub>(D)\<^esub>(g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F,d))"
      using finsop_1_lm_5 finsop_1_lm_6 sorry
  qed "sorry"
  thus " ?thesis "
     sorry
qed

mtheorem finsop_1_th_5:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for F be FinSequenceFINSEQ-1M3-of D holds  for G be FinSequenceFINSEQ-1M3-of D holds  for g be BinOpBINOP-1M2-of D holds g be associativeBINOP-1V2\<^bsub>(D)\<^esub> & (g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> or lenFINSEQ-1K4 F >=XXREAL-0R2 \<one>\<^sub>M & lenFINSEQ-1K4 G >=XXREAL-0R2 \<one>\<^sub>M) implies g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F ^FINSEQ-1K9\<^bsub>(D)\<^esub> G =XBOOLE-0R4 g .BINOP-1K4\<^bsub>(D)\<^esub>(g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F,g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> G)"
proof-
  have " for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for F be FinSequenceFINSEQ-1M3-of D holds  for G be FinSequenceFINSEQ-1M3-of D holds  for g be BinOpBINOP-1M2-of D holds  not ((g be associativeBINOP-1V2\<^bsub>(D)\<^esub> &  not ( not g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> &  not (lenFINSEQ-1K4 F >=XXREAL-0R2 \<one>\<^sub>M & lenFINSEQ-1K4 G >=XXREAL-0R2 \<one>\<^sub>M))) &  not g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F ^FINSEQ-1K9\<^bsub>(D)\<^esub> G =XBOOLE-0R4 g .BINOP-1K4\<^bsub>(D)\<^esub>(g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F,g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> G))"
  proof(rule ballI,rule ballI,rule ballI,rule ballI)
    fix D assume [ty]: "D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
    fix F assume [ty]: "F be FinSequenceFINSEQ-1M3-of D"
    fix G assume [ty]: "G be FinSequenceFINSEQ-1M3-of D"
    fix g assume [ty]: "g be BinOpBINOP-1M2-of D"
    let ?P = "\<lambda>Lamb1.  for F be FinSequenceFINSEQ-1M3-of D holds  for g be BinOpBINOP-1M2-of D holds g be associativeBINOP-1V2\<^bsub>(D)\<^esub> & (g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> or lenFINSEQ-1K4 F >=XXREAL-0R2 \<one>\<^sub>M & lenFINSEQ-1K4 Lamb1 >=XXREAL-0R2 \<one>\<^sub>M) implies g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F ^FINSEQ-1K9\<^bsub>(D)\<^esub> Lamb1 =XBOOLE-0R4 g .BINOP-1K4\<^bsub>(D)\<^esub>(g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F,g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> Lamb1)"
    have A1: " for G be FinSequenceFINSEQ-1M3-of D holds  for d be ElementSUBSET-1M1-of D holds ?P(G) implies ?P(G ^FINSEQ-1K9\<^bsub>(D)\<^esub> (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>))"
    proof-
      have " for G be FinSequenceFINSEQ-1M3-of D holds  for d be ElementSUBSET-1M1-of D holds ( for F be FinSequenceFINSEQ-1M3-of D holds  for g be BinOpBINOP-1M2-of D holds g be associativeBINOP-1V2\<^bsub>(D)\<^esub> & (g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> or lenFINSEQ-1K4 F >=XXREAL-0R2 \<one>\<^sub>M & lenFINSEQ-1K4 G >=XXREAL-0R2 \<one>\<^sub>M) implies g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F ^FINSEQ-1K9\<^bsub>(D)\<^esub> G =XBOOLE-0R4 g .BINOP-1K4\<^bsub>(D)\<^esub>(g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F,g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> G)) implies ( for F be FinSequenceFINSEQ-1M3-of D holds  for g be BinOpBINOP-1M2-of D holds g be associativeBINOP-1V2\<^bsub>(D)\<^esub> & (g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> or lenFINSEQ-1K4 F >=XXREAL-0R2 \<one>\<^sub>M & lenFINSEQ-1K4 (G ^FINSEQ-1K9\<^bsub>(D)\<^esub> (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>)) >=XXREAL-0R2 \<one>\<^sub>M) implies g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F ^FINSEQ-1K9\<^bsub>(D)\<^esub> (G ^FINSEQ-1K9\<^bsub>(D)\<^esub> (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>)) =XBOOLE-0R4 g .BINOP-1K4\<^bsub>(D)\<^esub>(g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F,g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> G ^FINSEQ-1K9\<^bsub>(D)\<^esub> (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>)))"
      proof(rule ballI,rule ballI,rule impI,rule ballI,rule ballI,rule impMI ,rule impI)
        fix G assume [ty]: "G be FinSequenceFINSEQ-1M3-of D"
        fix d assume [ty]: "d be ElementSUBSET-1M1-of D"
        assume A2: "?P(G)"
        fix F assume [ty]: "F be FinSequenceFINSEQ-1M3-of D"
        fix g assume [ty]: "g be BinOpBINOP-1M2-of D"
        assume A3: "g be associativeBINOP-1V2\<^bsub>(D)\<^esub>"
          and A4: "g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> or lenFINSEQ-1K4 F >=XXREAL-0R2 \<one>\<^sub>M & lenFINSEQ-1K4 (G ^FINSEQ-1K9\<^bsub>(D)\<^esub> (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>)) >=XXREAL-0R2 \<one>\<^sub>M"
        have A5: " not g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> implies lenFINSEQ-1K4 (F ^FINSEQ-1K9\<^bsub>(D)\<^esub> G) >=XXREAL-0R2 \<one>\<^sub>M"
        proof(rule impI)
          have A6: "lenFINSEQ-1K4 (F ^FINSEQ-1K9\<^bsub>(D)\<^esub> G) =XBOOLE-0R4 lenFINSEQ-1K4 F +NAT-1K1 lenFINSEQ-1K4 G"
            using finseq_1_th_22 sorry
          assume " not g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub>"
          thus "lenFINSEQ-1K4 (F ^FINSEQ-1K9\<^bsub>(D)\<^esub> G) >=XXREAL-0R2 \<one>\<^sub>M"
            using A4 A6 nat_1_th_12 sorry
        qed
        have A7: "g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F ^FINSEQ-1K9\<^bsub>(D)\<^esub> (G ^FINSEQ-1K9\<^bsub>(D)\<^esub> (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>)) =HIDDENR1 g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> (F ^FINSEQ-1K9\<^bsub>(D)\<^esub> G)^FINSEQ-1K9\<^bsub>(D)\<^esub> (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>)"
          using finseq_1_th_32 sorry
        also have "... = g .BINOP-1K4\<^bsub>(D)\<^esub>(g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F ^FINSEQ-1K9\<^bsub>(D)\<^esub> G,d)"
          using A5 finsop_1_th_4 sorry
        finally have "g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F ^FINSEQ-1K9\<^bsub>(D)\<^esub> (G ^FINSEQ-1K9\<^bsub>(D)\<^esub> (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>)) =HIDDENR1 g .BINOP-1K4\<^bsub>(D)\<^esub>(g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F ^FINSEQ-1K9\<^bsub>(D)\<^esub> G,d)"
           sorry
        have "g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F ^FINSEQ-1K9\<^bsub>(D)\<^esub> (G ^FINSEQ-1K9\<^bsub>(D)\<^esub> (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>)) =HIDDENR1 g .BINOP-1K4\<^bsub>(D)\<^esub>(g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F,g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> G ^FINSEQ-1K9\<^bsub>(D)\<^esub> (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>))"
        proof-
          show "g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F ^FINSEQ-1K9\<^bsub>(D)\<^esub> (G ^FINSEQ-1K9\<^bsub>(D)\<^esub> (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>)) =HIDDENR1 g .BINOP-1K4\<^bsub>(D)\<^esub>(g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F,g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> G ^FINSEQ-1K9\<^bsub>(D)\<^esub> (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>))"
          proof-
            have cases: "lenFINSEQ-1K4 G <>HIDDENR2 0NUMBERSK6 or lenFINSEQ-1K4 G =XBOOLE-0R4 0NUMBERSK6"
               sorry
            have case1: "lenFINSEQ-1K4 G <>HIDDENR2 0NUMBERSK6 implies g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F ^FINSEQ-1K9\<^bsub>(D)\<^esub> (G ^FINSEQ-1K9\<^bsub>(D)\<^esub> (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>)) =HIDDENR1 g .BINOP-1K4\<^bsub>(D)\<^esub>(g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F,g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> G ^FINSEQ-1K9\<^bsub>(D)\<^esub> (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>))"
            proof(rule impI)
              assume A8: "lenFINSEQ-1K4 G <>HIDDENR2 0NUMBERSK6"
              then have "lenFINSEQ-1K4 G >=XXREAL-0R2 \<one>\<^sub>M"
                using nat_1_th_14 sorry
              then have "g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F ^FINSEQ-1K9\<^bsub>(D)\<^esub> (G ^FINSEQ-1K9\<^bsub>(D)\<^esub> (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>)) =HIDDENR1 g .BINOP-1K4\<^bsub>(D)\<^esub>(g .BINOP-1K4\<^bsub>(D)\<^esub>(g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F,g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> G),d)"
                using A2 A3 A4 A7 sorry
              also have "... = g .BINOP-1K4\<^bsub>(D)\<^esub>(g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F,g .BINOP-1K4\<^bsub>(D)\<^esub>(g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> G,d))"
                using A3 binop_1_def_3 sorry
              also have "... = g .BINOP-1K4\<^bsub>(D)\<^esub>(g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F,g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> G ^FINSEQ-1K9\<^bsub>(D)\<^esub> (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>))"
                using A8 finsop_1_th_4 nat_1_th_14 sorry
              finally show "g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F ^FINSEQ-1K9\<^bsub>(D)\<^esub> (G ^FINSEQ-1K9\<^bsub>(D)\<^esub> (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>)) =HIDDENR1 g .BINOP-1K4\<^bsub>(D)\<^esub>(g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F,g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> G ^FINSEQ-1K9\<^bsub>(D)\<^esub> (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>))"
                 sorry
            qed
            have case2: "lenFINSEQ-1K4 G =XBOOLE-0R4 0NUMBERSK6 implies g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F ^FINSEQ-1K9\<^bsub>(D)\<^esub> (G ^FINSEQ-1K9\<^bsub>(D)\<^esub> (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>)) =HIDDENR1 g .BINOP-1K4\<^bsub>(D)\<^esub>(g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F,g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> G ^FINSEQ-1K9\<^bsub>(D)\<^esub> (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>))"
            proof(rule impI)
              assume "lenFINSEQ-1K4 G =XBOOLE-0R4 0NUMBERSK6"
              then have A9: "G =XBOOLE-0R4 {}XBOOLE-0K1"
                 sorry
              then have "g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F ^FINSEQ-1K9\<^bsub>(D)\<^esub> (G ^FINSEQ-1K9\<^bsub>(D)\<^esub> (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>)) =HIDDENR1 g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F ^FINSEQ-1K9\<^bsub>(D)\<^esub> (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>)"
                using finseq_1_th_34 sorry
              also have "... = g .BINOP-1K4\<^bsub>(D)\<^esub>(g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F,d)"
                using A4 finsop_1_th_4 sorry
              also have "... = g .BINOP-1K4\<^bsub>(D)\<^esub>(g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F,g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> <*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>)"
                using finsop_1_lm_4 sorry
              also have "... = g .BINOP-1K4\<^bsub>(D)\<^esub>(g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F,g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> G ^FINSEQ-1K9\<^bsub>(D)\<^esub> (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>))"
                using A9 finseq_1_th_34 sorry
              finally show "g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F ^FINSEQ-1K9\<^bsub>(D)\<^esub> (G ^FINSEQ-1K9\<^bsub>(D)\<^esub> (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>)) =HIDDENR1 g .BINOP-1K4\<^bsub>(D)\<^esub>(g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F,g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> G ^FINSEQ-1K9\<^bsub>(D)\<^esub> (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>))"
                 sorry
            qed
            show " ?thesis "
              using cases case1 case2 sorry
          qed
        qed
        thus "g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F ^FINSEQ-1K9\<^bsub>(D)\<^esub> (G ^FINSEQ-1K9\<^bsub>(D)\<^esub> (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>)) =XBOOLE-0R4 g .BINOP-1K4\<^bsub>(D)\<^esub>(g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F,g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> G ^FINSEQ-1K9\<^bsub>(D)\<^esub> (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>))"
           sorry
      qed "sorry"
      thus " ?thesis "
         sorry
    qed
    have A10: "?P(<*>FINSEQ-1K7 D)"
    proof-
      have " for F be FinSequenceFINSEQ-1M3-of D holds  for g be BinOpBINOP-1M2-of D holds g be associativeBINOP-1V2\<^bsub>(D)\<^esub> & (g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> or lenFINSEQ-1K4 F >=XXREAL-0R2 \<one>\<^sub>M & lenFINSEQ-1K4 <*>FINSEQ-1K7 D >=XXREAL-0R2 \<one>\<^sub>M) implies g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F ^FINSEQ-1K9\<^bsub>(D)\<^esub> <*>FINSEQ-1K7 D =HIDDENR1 g .BINOP-1K4\<^bsub>(D)\<^esub>(g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F,g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> <*>FINSEQ-1K7 D)"
      proof(rule ballI,rule ballI,rule impMI ,rule impI)
        fix F assume [ty]: "F be FinSequenceFINSEQ-1M3-of D"
        fix g assume [ty]: "g be BinOpBINOP-1M2-of D"
        assume "g be associativeBINOP-1V2\<^bsub>(D)\<^esub>"
          and A11: "g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> or lenFINSEQ-1K4 F >=XXREAL-0R2 \<one>\<^sub>M & lenFINSEQ-1K4 <*>FINSEQ-1K7 D >=XXREAL-0R2 \<one>\<^sub>M"
        have "g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F ^FINSEQ-1K9\<^bsub>(D)\<^esub> <*>FINSEQ-1K7 D =HIDDENR1 g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F"
          using finseq_1_th_34 sorry
        also have "... = g .BINOP-1K4\<^bsub>(D)\<^esub>(g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F,the-unity-wrtBINOP-1K3\<^bsub>(D)\<^esub> g)"
          using A11 setwiseo_th_15 sorry
        also have "... = g .BINOP-1K4\<^bsub>(D)\<^esub>(g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F,g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> <*>FINSEQ-1K7 D)"
          using A11 finsop_1_lm_3 sorry
        finally show "g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F ^FINSEQ-1K9\<^bsub>(D)\<^esub> <*>FINSEQ-1K7 D =HIDDENR1 g .BINOP-1K4\<^bsub>(D)\<^esub>(g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F,g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> <*>FINSEQ-1K7 D)"
           sorry
      qed "sorry"
      thus " ?thesis "
         sorry
    qed
    have " for G be FinSequenceFINSEQ-1M3-of D holds ?P(G)"
      using finseq_2_sch_2 A10 A1 sorry
    thus " not ((g be associativeBINOP-1V2\<^bsub>(D)\<^esub> &  not ( not g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> &  not (lenFINSEQ-1K4 F >=XXREAL-0R2 \<one>\<^sub>M & lenFINSEQ-1K4 G >=XXREAL-0R2 \<one>\<^sub>M))) &  not g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F ^FINSEQ-1K9\<^bsub>(D)\<^esub> G =XBOOLE-0R4 g .BINOP-1K4\<^bsub>(D)\<^esub>(g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F,g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> G))"
       sorry
  qed "sorry"
  thus " ?thesis "
     sorry
qed

mtheorem finsop_1_th_6:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d be ElementSUBSET-1M1-of D holds  for F be FinSequenceFINSEQ-1M3-of D holds  for g be BinOpBINOP-1M2-of D holds g be associativeBINOP-1V2\<^bsub>(D)\<^esub> & (g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> or lenFINSEQ-1K4 F >=XXREAL-0R2 \<one>\<^sub>M) implies g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>)^FINSEQ-1K9\<^bsub>(D)\<^esub> F =XBOOLE-0R4 g .BINOP-1K4\<^bsub>(D)\<^esub>(d,g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F)"
proof-
  have " for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d be ElementSUBSET-1M1-of D holds  for F be FinSequenceFINSEQ-1M3-of D holds  for g be BinOpBINOP-1M2-of D holds g be associativeBINOP-1V2\<^bsub>(D)\<^esub> & (g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> or lenFINSEQ-1K4 F >=XXREAL-0R2 \<one>\<^sub>M) implies g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>)^FINSEQ-1K9\<^bsub>(D)\<^esub> F =HIDDENR1 g .BINOP-1K4\<^bsub>(D)\<^esub>(d,g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F)"
  proof(rule ballI,rule ballI,rule ballI,rule ballI,rule impI)
    fix D assume [ty]: "D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
    fix d assume [ty]: "d be ElementSUBSET-1M1-of D"
    fix F assume [ty]: "F be FinSequenceFINSEQ-1M3-of D"
    fix g assume [ty]: "g be BinOpBINOP-1M2-of D"
    have A1: "lenFINSEQ-1K4 (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>) =XBOOLE-0R4 \<one>\<^sub>M"
      using finseq_1_th_39 sorry
    assume "g be associativeBINOP-1V2\<^bsub>(D)\<^esub> & (g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> or lenFINSEQ-1K4 F >=XXREAL-0R2 \<one>\<^sub>M)"
    then have "g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>)^FINSEQ-1K9\<^bsub>(D)\<^esub> F =HIDDENR1 g .BINOP-1K4\<^bsub>(D)\<^esub>(g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> <*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>,g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F)"
      using A1 finsop_1_th_5 sorry
    also have "... = g .BINOP-1K4\<^bsub>(D)\<^esub>(d,g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F)"
      using finsop_1_lm_4 sorry
    finally show "g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>)^FINSEQ-1K9\<^bsub>(D)\<^esub> F =HIDDENR1 g .BINOP-1K4\<^bsub>(D)\<^esub>(d,g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F)"
       sorry
  qed "sorry"
  thus " ?thesis "
     sorry
qed

mlemma finsop_1_lm_7:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for F be FinSequenceFINSEQ-1M3-of D holds  for G be FinSequenceFINSEQ-1M3-of D holds  for g be BinOpBINOP-1M2-of D holds g be associativeBINOP-1V2\<^bsub>(D)\<^esub> & g be commutativeBINOP-1V1\<^bsub>(D)\<^esub> implies ( for f be PermutationFUNCT-2M2-of domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> F holds (lenFINSEQ-1K4 F >=XXREAL-0R2 \<one>\<^sub>M & lenFINSEQ-1K4 F =XBOOLE-0R4 lenFINSEQ-1K4 G) & ( for i be NatNAT-1M1 holds i inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> G implies G .FUNCT-1K1 i =XBOOLE-0R4 F .FUNCT-1K1 (f .FUNCT-1K1 i)) implies g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F =XBOOLE-0R4 g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> G)"
proof-
  have " for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for F be FinSequenceFINSEQ-1M3-of D holds  for G be FinSequenceFINSEQ-1M3-of D holds  for g be BinOpBINOP-1M2-of D holds g be associativeBINOP-1V2\<^bsub>(D)\<^esub> & g be commutativeBINOP-1V1\<^bsub>(D)\<^esub> implies ( for f be PermutationFUNCT-2M2-of domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> F holds  not (((lenFINSEQ-1K4 F >=XXREAL-0R2 \<one>\<^sub>M & lenFINSEQ-1K4 F =XBOOLE-0R4 lenFINSEQ-1K4 G) & ( for i be NatNAT-1M1 holds  not (i inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> G &  not G .FUNCT-1K1 i =XBOOLE-0R4 F .FUNCT-1K1 (f .FUNCT-1K1 i)))) &  not g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F =XBOOLE-0R4 g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> G))"
  proof(rule ballI,rule ballI,rule ballI,rule ballI,rule impMI ,rule impI,rule ballI)
    fix D assume [ty]: "D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
    fix F assume [ty]: "F be FinSequenceFINSEQ-1M3-of D"
    fix G assume [ty]: "G be FinSequenceFINSEQ-1M3-of D"
    fix g assume [ty]: "g be BinOpBINOP-1M2-of D"
    assume A1: "g be associativeBINOP-1V2\<^bsub>(D)\<^esub>"
      and A2: "g be commutativeBINOP-1V1\<^bsub>(D)\<^esub>"
    let ?P = "\<lambda>Lamb1.  for H1 be FinSequenceFINSEQ-1M3-of D holds  for H2 be FinSequenceFINSEQ-1M3-of D holds (lenFINSEQ-1K4 H1 >=XXREAL-0R2 \<one>\<^sub>M & lenFINSEQ-1K4 H1 =XBOOLE-0R4 Lamb1) & lenFINSEQ-1K4 H1 =XBOOLE-0R4 lenFINSEQ-1K4 H2 implies ( for f be PermutationFUNCT-2M2-of domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> H1 holds ( for i be NatNAT-1M1 holds i inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> H2 implies H2 .FUNCT-1K1 i =XBOOLE-0R4 H1 .FUNCT-1K1 (f .FUNCT-1K1 i)) implies g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> H1 =XBOOLE-0R4 g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> H2)"
    have A3: " for k be NatNAT-1M1 holds ( for H1 be FinSequenceFINSEQ-1M3-of D holds  for H2 be FinSequenceFINSEQ-1M3-of D holds (lenFINSEQ-1K4 H1 >=XXREAL-0R2 \<one>\<^sub>M & lenFINSEQ-1K4 H1 =XBOOLE-0R4 k) & lenFINSEQ-1K4 H1 =XBOOLE-0R4 lenFINSEQ-1K4 H2 implies ( for f be PermutationFUNCT-2M2-of domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> H1 holds ( for i be NatNAT-1M1 holds i inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> H2 implies H2 .FUNCT-1K1 i =XBOOLE-0R4 H1 .FUNCT-1K1 (f .FUNCT-1K1 i)) implies g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> H1 =XBOOLE-0R4 g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> H2)) implies ( for H1 be FinSequenceFINSEQ-1M3-of D holds  for H2 be FinSequenceFINSEQ-1M3-of D holds (lenFINSEQ-1K4 H1 >=XXREAL-0R2 \<one>\<^sub>M & lenFINSEQ-1K4 H1 =XBOOLE-0R4 k +NAT-1K1 \<one>\<^sub>M) & lenFINSEQ-1K4 H1 =XBOOLE-0R4 lenFINSEQ-1K4 H2 implies ( for f be PermutationFUNCT-2M2-of domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> H1 holds ( for i be NatNAT-1M1 holds i inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> H2 implies H2 .FUNCT-1K1 i =XBOOLE-0R4 H1 .FUNCT-1K1 (f .FUNCT-1K1 i)) implies g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> H1 =XBOOLE-0R4 g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> H2))"
    proof(rule ballI,rule impI)
      fix k assume [ty]: "k be NatNAT-1M1"
      assume A4: "?P(k)"
      show " for H1 be FinSequenceFINSEQ-1M3-of D holds  for H2 be FinSequenceFINSEQ-1M3-of D holds (lenFINSEQ-1K4 H1 >=XXREAL-0R2 \<one>\<^sub>M & lenFINSEQ-1K4 H1 =XBOOLE-0R4 k +NAT-1K1 \<one>\<^sub>M) & lenFINSEQ-1K4 H1 =XBOOLE-0R4 lenFINSEQ-1K4 H2 implies ( for f be PermutationFUNCT-2M2-of domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> H1 holds ( for i be NatNAT-1M1 holds i inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> H2 implies H2 .FUNCT-1K1 i =XBOOLE-0R4 H1 .FUNCT-1K1 (f .FUNCT-1K1 i)) implies g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> H1 =XBOOLE-0R4 g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> H2)"
      proof-
        have " for H1 be FinSequenceFINSEQ-1M3-of D holds  for H2 be FinSequenceFINSEQ-1M3-of D holds lenFINSEQ-1K4 H1 >=XXREAL-0R2 \<one>\<^sub>M & (lenFINSEQ-1K4 H1 =XBOOLE-0R4 k +NAT-1K1 \<one>\<^sub>M & lenFINSEQ-1K4 H1 =XBOOLE-0R4 lenFINSEQ-1K4 H2) implies ( for f be PermutationFUNCT-2M2-of domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> H1 holds ( for i be NatNAT-1M1 holds i inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> H2 implies H2 .FUNCT-1K1 i =XBOOLE-0R4 H1 .FUNCT-1K1 (f .FUNCT-1K1 i)) implies g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> H1 =XBOOLE-0R4 g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> H2)"
        proof(rule ballI,rule ballI,rule impMI ,rule impMI ,rule impI,rule ballI,rule impI)
          fix H1 assume [ty]: "H1 be FinSequenceFINSEQ-1M3-of D"
          fix H2 assume [ty]: "H2 be FinSequenceFINSEQ-1M3-of D"
          assume "lenFINSEQ-1K4 H1 >=XXREAL-0R2 \<one>\<^sub>M"
            and A5: "lenFINSEQ-1K4 H1 =XBOOLE-0R4 k +NAT-1K1 \<one>\<^sub>M"
            and A6: "lenFINSEQ-1K4 H1 =XBOOLE-0R4 lenFINSEQ-1K4 H2"
          obtain p where 
            [ty]:"p be FinSequenceFINSEQ-1M3-of D" and pDef:"p = H2 |RELSET-1K5\<^bsub>(NATNUMBERSK1,D)\<^esub> SegFINSEQ-1K2 k"
            using finseq_1_th_18 sorry
          fix f assume [ty]: "f be PermutationFUNCT-2M2-of domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> H1"
          have A7: "domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> H1 =XBOOLE-0R4 SegFINSEQ-1K2 (k +NAT-1K1 \<one>\<^sub>M)"
            using A5 finseq_1_def_3 sorry
          then have A8: "rngFUNCT-1K2 f =XBOOLE-0R4 SegFINSEQ-1K2 (k +NAT-1K1 \<one>\<^sub>M)"
            using funct_2_def_3 sorry
          have A9: " for n be NatNAT-1M1 holds n inTARSKIR2 domRELSET-1K1\<^bsub>(domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> H1)\<^esub> f implies f .FUNCT-1K1 n be ElementSUBSET-1M1-of NATNUMBERSK1"
          proof(rule ballI,rule impI)
            fix n assume [ty]: "n be NatNAT-1M1"
            assume "n inTARSKIR2 domRELSET-1K1\<^bsub>(domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> H1)\<^esub> f"
            then have "f .FUNCT-1K1 n inTARSKIR2 SegFINSEQ-1K2 (k +NAT-1K1 \<one>\<^sub>M)"
              using A8 funct_1_def_3 sorry
            thus "f .FUNCT-1K1 n be ElementSUBSET-1M1-of NATNUMBERSK1"
               sorry
          qed "sorry"
          have A10: "rngFUNCT-1K2 H2 c=TARSKIR1 D"
            using finseq_1_def_4 sorry
          have A11: "domRELSET-1K1\<^bsub>(domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> H1)\<^esub> f =XBOOLE-0R4 SegFINSEQ-1K2 (k +NAT-1K1 \<one>\<^sub>M)"
            using A7 funct_2_def_1 sorry
          have A12: "k +NAT-1K1 \<one>\<^sub>M inTARSKIR2 SegFINSEQ-1K2 (k +NAT-1K1 \<one>\<^sub>M)"
            using finseq_1_th_4 sorry
          then have A13: "f .FUNCT-1K1 (k +NAT-1K1 \<one>\<^sub>M) inTARSKIR2 SegFINSEQ-1K2 (k +NAT-1K1 \<one>\<^sub>M)"
            using A11 A8 funct_1_def_3 sorry
          then obtain n where 
            [ty]:"n be ElementSUBSET-1M1-of NATNUMBERSK1" and nDef:"n = f .FUNCT-1K1 (k +NAT-1K1 \<one>\<^sub>M)"
             sorry
          have A14: "domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> H2 =XBOOLE-0R4 SegFINSEQ-1K2 (k +NAT-1K1 \<one>\<^sub>M)"
            using A5 A6 finseq_1_def_3 sorry
          then have "H2 .FUNCT-1K1 (k +NAT-1K1 \<one>\<^sub>M) inTARSKIR2 rngFUNCT-1K2 H2"
            using A12 funct_1_def_3 sorry
          then obtain d where 
            [ty]:"d be ElementSUBSET-1M1-of D" and dDef:"d = H2 .FUNCT-1K1 (k +NAT-1K1 \<one>\<^sub>M)"
            using A10 sorry
          have A15: "n <=XXREAL-0R1 k +NAT-1K1 \<one>\<^sub>M"
            using A13 finseq_1_th_1 sorry
          then obtain m2 where
            [ty]:"m2 be NatNAT-1M1" and 
            A16: "n +XCMPLX-0K2 m2 =XBOOLE-0R4 k +NAT-1K1 \<one>\<^sub>M"
            using nat_1_th_10 sorry
          let ?P = "\<lambda>Lamb1. \<lambda>Lamb2. Lamb2 =HIDDENR1 H1 .FUNCT-1K1 (n +XCMPLX-0K2 Lamb1)"
          have "\<one>\<^sub>M <=XXREAL-0R1 n"
            using A13 finseq_1_th_1 sorry
          then obtain m1 where
            [ty]:"m1 be NatNAT-1M1" and 
            A17: "\<one>\<^sub>M +XCMPLX-0K2 m1 =XBOOLE-0R4 n"
            using nat_1_th_10 sorry
          have 
            [ty]:"m1 be ElementSUBSET-1M1-of NATNUMBERSK1" and
            [ty]:"m2 be ElementSUBSET-1M1-of NATNUMBERSK1"
            using ordinal1_def_12 sorry
          have A18: " for j be NatNAT-1M1 holds j inTARSKIR2 SegFINSEQ-1K2 m2 implies ( ex x be objectHIDDENM1 st ?P(j,x))"
             sorry
          obtain q2 where
            [ty]:"q2 be FinSequenceFINSEQ-1M1" and 
            A19: "domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> q2 =XBOOLE-0R4 SegFINSEQ-1K2 m2"and A20: " for k be NatNAT-1M1 holds k inTARSKIR2 SegFINSEQ-1K2 m2 implies ?P(k,q2 .FUNCT-1K1 k)"
            using finseq_1_sch_1 A18 sorry
          have "rngFUNCT-1K2 q2 c=TARSKIR1 D"
          proof-
            have " for x be objectHIDDENM1 holds x inHIDDENR3 rngFUNCT-1K2 q2 implies x inHIDDENR3 D"
            proof(rule ballI,rule impI)
              fix x assume [ty]: "x be objectHIDDENM1"
              assume "x inHIDDENR3 rngFUNCT-1K2 q2"
              then obtain y where
                [ty]:"y be objectHIDDENM1" and 
                A21: "y inHIDDENR3 findomFINSOP-1K4 q2"and A22: "x =HIDDENR1 q2 .FUNCT-1K1 y"
                using funct_1_def_3 sorry
              have 
                [ty]:"y be ElementSUBSET-1M1-of NATNUMBERSK1"
                using A21 setwiseo_th_9 sorry
              have "\<one>\<^sub>M <=XXREAL-0R1 y"
                using A19 A21 finseq_1_th_1 sorry
              then have A23: "\<one>\<^sub>M <=XXREAL-0R1 n +NAT-1K1 y"
                using nat_1_th_12 sorry
              have "y <=XXREAL-0R1 m2"
                using A19 A21 finseq_1_th_1 sorry
              then have "n +NAT-1K1 y <=XXREAL-0R1 lenFINSEQ-1K4 H1"
                using A5 A16 xreal_1_th_7 sorry
              then have "n +NAT-1K1 y inTARSKIR2 SegFINSEQ-1K2 (lenFINSEQ-1K4 H1)"
                using A23 finseq_1_th_1 sorry
              then have "n +NAT-1K1 y inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> H1"
                using finseq_1_def_3 sorry
              then have A24: "H1 .FUNCT-1K1 (n +NAT-1K1 y) inTARSKIR2 rngFUNCT-1K2 H1"
                using funct_1_def_3 sorry
              have "rngFUNCT-1K2 H1 c=TARSKIR1 D"
                using finseq_1_def_4 sorry
              then obtain xx where 
                [ty]:"xx be ElementSUBSET-1M1-of D" and xxDef:"xx = H1 .FUNCT-1K1 (n +NAT-1K1 y)"
                using A24 sorry
              have "xx inTARSKIR2 D"
                 sorry
              thus "x inHIDDENR3 D"
                using A19 A20 A21 A22 sorry
            qed "sorry"
            thus "rngFUNCT-1K2 q2 c=TARSKIR1 D"
              using tarski_def_3 sorry
          qed
          then have 
            [ty]:"q2 be FinSequenceFINSEQ-1M3-of D"
            using finseq_1_def_4 sorry
          obtain q1 where 
            [ty]:"q1 be FinSequenceFINSEQ-1M3-of D" and q1Def:"q1 = H1 |RELSET-1K5\<^bsub>(NATNUMBERSK1,D)\<^esub> SegFINSEQ-1K2 m1"
            using finseq_1_th_18 sorry
          let ?P = "\<lambda>Lamb1. \<lambda>Lamb2. (f .FUNCT-1K1 Lamb1 inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> q1 implies Lamb2 =HIDDENR1 f .FUNCT-1K1 Lamb1) & ( not f .FUNCT-1K1 Lamb1 inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> q1 implies ( for l be NatNAT-1M1 holds l =XBOOLE-0R4 f .FUNCT-1K1 Lamb1 implies Lamb2 =HIDDENR1 l -XCMPLX-0K6 \<one>\<^sub>M))"
          have A25: "k <=XXREAL-0R1 k +NAT-1K1 \<one>\<^sub>M"
            using nat_1_th_12 sorry
          then have A26: "SegFINSEQ-1K2 k c=TARSKIR1 SegFINSEQ-1K2 (k +NAT-1K1 \<one>\<^sub>M)"
            using finseq_1_th_5 sorry
          have A27: " for i be NatNAT-1M1 holds i inTARSKIR2 SegFINSEQ-1K2 k implies ( ex y be objectHIDDENM1 st ?P(i,y))"
          proof-
            have " for i be NatNAT-1M1 holds i inTARSKIR2 SegFINSEQ-1K2 k implies  not ( for y be objectHIDDENM1 holds  not ((f .FUNCT-1K1 i inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> q1 implies y =HIDDENR1 f .FUNCT-1K1 i) & ( not f .FUNCT-1K1 i inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> q1 implies ( for l be NatNAT-1M1 holds l =XBOOLE-0R4 f .FUNCT-1K1 i implies y =HIDDENR1 l -XCMPLX-0K6 \<one>\<^sub>M))))"
            proof(rule ballI,rule impI)
              fix i assume [ty]: "i be NatNAT-1M1"
              assume A28: "i inTARSKIR2 SegFINSEQ-1K2 k"
              have " not f .FUNCT-1K1 i inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> q1 implies ( ex y be setHIDDENM2 st (f .FUNCT-1K1 i inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> q1 implies y =XBOOLE-0R4 f .FUNCT-1K1 i) & ( not f .FUNCT-1K1 i inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> q1 implies ( for t be NatNAT-1M1 holds t =XBOOLE-0R4 f .FUNCT-1K1 i implies y =XBOOLE-0R4 t -XCMPLX-0K6 \<one>\<^sub>M)))"
              proof(rule impI)
                have "f .FUNCT-1K1 i inTARSKIR2 SegFINSEQ-1K2 (k +NAT-1K1 \<one>\<^sub>M)"
                  using A11 A8 A26 A28 funct_1_def_3 sorry
                then obtain j where 
                  [ty]:"j be ElementSUBSET-1M1-of NATNUMBERSK1" and jDef:"j = f .FUNCT-1K1 i"
                   sorry
                assume A29: " not f .FUNCT-1K1 i inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> q1"
                obtain y where 
                  [ty]:"y be setHIDDENM2" and yDef:"y = j -XCMPLX-0K6 \<one>\<^sub>M"
                   sorry
                show " ex y be setHIDDENM2 st (f .FUNCT-1K1 i inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> q1 implies y =XBOOLE-0R4 f .FUNCT-1K1 i) & ( not f .FUNCT-1K1 i inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> q1 implies ( for t be NatNAT-1M1 holds t =XBOOLE-0R4 f .FUNCT-1K1 i implies y =XBOOLE-0R4 t -XCMPLX-0K6 \<one>\<^sub>M))"
                proof(rule bexI[of _ "y"],rule conjMI,rule impI,rule ballI,rule impI)
                  show "f .FUNCT-1K1 i inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> q1 implies y =XBOOLE-0R4 f .FUNCT-1K1 i"
                    using A29 sorry
                  assume " not f .FUNCT-1K1 i inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> q1"
                  fix t assume [ty]: "t be NatNAT-1M1"
                  assume "t =XBOOLE-0R4 f .FUNCT-1K1 i"
                  thus "y =XBOOLE-0R4 t -XCMPLX-0K6 \<one>\<^sub>M"
                     sorry
                qed "sorry"
              qed
              thus " not ( for y be objectHIDDENM1 holds  not ((f .FUNCT-1K1 i inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> q1 implies y =HIDDENR1 f .FUNCT-1K1 i) & ( not f .FUNCT-1K1 i inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> q1 implies ( for l be NatNAT-1M1 holds l =XBOOLE-0R4 f .FUNCT-1K1 i implies y =HIDDENR1 l -XCMPLX-0K6 \<one>\<^sub>M))))"
                 sorry
            qed "sorry"
            thus " ?thesis "
               sorry
          qed
          obtain gg where
            [ty]:"gg be FinSequenceFINSEQ-1M1" and 
            A30: "domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> gg =XBOOLE-0R4 SegFINSEQ-1K2 k"and A31: " for i be NatNAT-1M1 holds i inTARSKIR2 SegFINSEQ-1K2 k implies ?P(i,gg .FUNCT-1K1 i)"
            using finseq_1_sch_1 A27 sorry
          have A32: "domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> p =XBOOLE-0R4 SegFINSEQ-1K2 k"
            using A5 A6 A25 finseq_1_th_17 sorry
          have "m1 <=XXREAL-0R1 n"
            using A17 nat_1_th_11 sorry
          then have A33: "m1 <=XXREAL-0R1 k +NAT-1K1 \<one>\<^sub>M"
            using A15 xxreal_0_th_2 sorry
          then have A34: "domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> q1 =XBOOLE-0R4 SegFINSEQ-1K2 m1"
            using A5 finseq_1_th_17 sorry
          have A35: " for i be NatNAT-1M1 holds  for l be NatNAT-1M1 holds l =XBOOLE-0R4 f .FUNCT-1K1 i & ( not f .FUNCT-1K1 i inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> q1 & i inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> gg) implies m1 +NAT-1K1 \<two>\<^sub>M <=XXREAL-0R1 l"
          proof(rule ballI,rule ballI,rule impMI ,rule impMI ,rule impI)
            fix i assume [ty]: "i be NatNAT-1M1"
            fix l assume [ty]: "l be NatNAT-1M1"
            assume A36: "l =XBOOLE-0R4 f .FUNCT-1K1 i"
              and A37: " not f .FUNCT-1K1 i inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> q1"
              and A38: "i inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> gg"
            have A39: "l <XXREAL-0R3 \<one>\<^sub>M or m1 <XXREAL-0R3 l"
              using A34 A36 A37 finseq_1_th_1 sorry
            have A40: "m1 +NAT-1K1 \<one>\<^sub>M =XBOOLE-0R4 l implies  False "
            proof(rule impI)
              assume "m1 +NAT-1K1 \<one>\<^sub>M =XBOOLE-0R4 l"
              then have "k +NAT-1K1 \<one>\<^sub>M =XBOOLE-0R4 i"
                using A12 A11 A17 A26 A30 A36 A38 funct_1_def_4 sorry
              then have "k +NAT-1K1 \<one>\<^sub>M <=XXREAL-0R1 k +NAT-1K1 0NUMBERSK6"
                using A30 A38 finseq_1_th_1 sorry
              thus " False "
                using xreal_1_th_6 sorry
            qed
            have "f .FUNCT-1K1 i inTARSKIR2 rngFUNCT-1K2 f"
              using A11 A26 A30 A38 funct_1_def_3 sorry
            then have "m1 +NAT-1K1 \<one>\<^sub>M <=XXREAL-0R1 l"
              using A8 A36 A39 finseq_1_th_1 nat_1_th_13 sorry
            then have "m1 +NAT-1K1 \<one>\<^sub>M <XXREAL-0R3 l"
              using A40 xxreal_0_th_1 sorry
            then have "(m1 +NAT-1K1 \<one>\<^sub>M)+NAT-1K1 \<one>\<^sub>M <=XXREAL-0R1 l"
              using nat_1_th_13 sorry
            thus "m1 +NAT-1K1 \<two>\<^sub>M <=XXREAL-0R1 l"
               sorry
          qed "sorry"
          have "\<one>\<^sub>M +XCMPLX-0K2 k =XBOOLE-0R4 \<one>\<^sub>M +NAT-1K1 (m1 +NAT-1K1 m2)"
            using A17 A16 sorry
          then have A41: "m1 <=XXREAL-0R1 k"
            using nat_1_th_11 sorry
          have A42: "rngFUNCT-1K2 gg c=TARSKIR1 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> p"
          proof-
            have " for y be objectHIDDENM1 holds y inHIDDENR3 rngFUNCT-1K2 gg implies y inHIDDENR3 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> p"
            proof(rule ballI,rule impI)
              fix y assume [ty]: "y be objectHIDDENM1"
              assume "y inHIDDENR3 rngFUNCT-1K2 gg"
              then obtain x where
                [ty]:"x be objectHIDDENM1" and 
                A43: "x inHIDDENR3 findomFINSOP-1K4 gg"and A44: "gg .FUNCT-1K1 x =HIDDENR1 y"
                using funct_1_def_3 sorry
              have 
                [ty]:"x be ElementSUBSET-1M1-of NATNUMBERSK1"
                using A43 setwiseo_th_9 sorry
              have "y inHIDDENR3 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> p"
              proof-
                show "y inHIDDENR3 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> p"
                proof-
                  have cases: "f .FUNCT-1K1 x inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> q1 or  not f .FUNCT-1K1 x inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> q1"
                     sorry
                  have case1: "f .FUNCT-1K1 x inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> q1 implies y inHIDDENR3 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> p"
                  proof(rule impI)
                    assume A45: "f .FUNCT-1K1 x inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> q1"
                    have A46: "domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> q1 c=TARSKIR1 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> p"
                      using A41 A34 A32 finseq_1_th_5 sorry
                    have "f .FUNCT-1K1 x =XBOOLE-0R4 gg .FUNCT-1K1 x"
                      using A30 A31 A43 A45 sorry
                    thus "y inHIDDENR3 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> p"
                      using A44 A45 A46 sorry
                  qed
                  have case2: " not f .FUNCT-1K1 x inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> q1 implies y inHIDDENR3 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> p"
                  proof(rule impI)
                    assume A47: " not f .FUNCT-1K1 x inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> q1"
                    obtain j where 
                      [ty]:"j be ElementSUBSET-1M1-of NATNUMBERSK1" and jDef:"j = f .FUNCT-1K1 x"
                      using A11 A26 A9 A30 A43 sorry
                    have A48: "f .FUNCT-1K1 x inTARSKIR2 SegFINSEQ-1K2 (k +NAT-1K1 \<one>\<^sub>M)"
                      using A11 A8 A26 A30 A43 funct_1_def_3 sorry
                    have "j <XXREAL-0R3 \<one>\<^sub>M or m1 <XXREAL-0R3 j"
                      using A34 A47 finseq_1_th_1 sorry
                    then obtain l where 
                      [ty]:"l be ElementSUBSET-1M1-of NATNUMBERSK1" and lDef:"l = j -XCMPLX-0K6 \<one>\<^sub>M"
                      using A48 finseq_1_th_1 nat_1_th_20 sorry
                    have "j <=XXREAL-0R1 k +NAT-1K1 \<one>\<^sub>M"
                      using A48 finseq_1_th_1 sorry
                    then have A49: "l <=XXREAL-0R1 (k +NAT-1K1 \<one>\<^sub>M)-XCMPLX-0K6 \<one>\<^sub>M"
                      using xreal_1_th_9 sorry
                    have "m1 +NAT-1K1 \<two>\<^sub>M <=XXREAL-0R1 j"
                      using A35 A43 A47 sorry
                    then have A50: "(m1 +NAT-1K1 \<two>\<^sub>M)-XCMPLX-0K6 \<one>\<^sub>M <=XXREAL-0R1 l"
                      using xreal_1_th_9 sorry
                    have "\<one>\<^sub>M <=XXREAL-0R1 m1 +NAT-1K1 \<one>\<^sub>M"
                      using nat_1_th_12 sorry
                    then have A51: "\<one>\<^sub>M <=XXREAL-0R1 l"
                      using A50 xxreal_0_th_2 sorry
                    have "gg .FUNCT-1K1 x =XBOOLE-0R4 j -XCMPLX-0K6 \<one>\<^sub>M"
                      using A30 A31 A43 A47 sorry
                    thus "y inHIDDENR3 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> p"
                      using A32 A44 A51 A49 finseq_1_th_1 sorry
                  qed
                  show " ?thesis "
                    using cases case1 case2 sorry
                qed
              qed
              thus "y inHIDDENR3 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> p"
                 sorry
            qed "sorry"
            thus "rngFUNCT-1K2 gg c=TARSKIR1 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> p"
              using tarski_def_3 sorry
          qed
          have A52: "lenFINSEQ-1K4 q1 =XBOOLE-0R4 m1"
            using A5 A33 finseq_1_th_17 sorry
          have A53: " for j be NatNAT-1M1 holds j inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> q2 implies H1 .FUNCT-1K1 (lenFINSEQ-1K4 (q1 ^FINSEQ-1K9\<^bsub>(D)\<^esub> (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>)) +XCMPLX-0K2 j) =XBOOLE-0R4 q2 .FUNCT-1K1 j"
          proof(rule ballI,rule impI)
            fix j assume [ty]: "j be NatNAT-1M1"
            assume A54: "j inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> q2"
            have "lenFINSEQ-1K4 (q1 ^FINSEQ-1K9\<^bsub>(D)\<^esub> (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>)) =HIDDENR1 m1 +NAT-1K1 lenFINSEQ-1K4 (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>)"
              using A52 finseq_1_th_22 sorry
            also have "... = n"
              using A17 finseq_1_th_39 sorry
            finally have "lenFINSEQ-1K4 (q1 ^FINSEQ-1K9\<^bsub>(D)\<^esub> (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>)) =HIDDENR1 n"
               sorry
            thus "H1 .FUNCT-1K1 (lenFINSEQ-1K4 (q1 ^FINSEQ-1K9\<^bsub>(D)\<^esub> (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>)) +XCMPLX-0K2 j) =XBOOLE-0R4 q2 .FUNCT-1K1 j"
              using A19 A20 A54 sorry
          qed "sorry"
          let ?q = "q1 ^FINSEQ-1K9\<^bsub>(D)\<^esub> q2"
          have A55: "lenFINSEQ-1K4 q2 =XBOOLE-0R4 m2"
            using A19 finseq_1_def_3 sorry
          then have A56: "lenFINSEQ-1K4 ?q =XBOOLE-0R4 m1 +NAT-1K1 m2"
            using A52 finseq_1_th_22 sorry
          then have A57: "domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> ?q =XBOOLE-0R4 SegFINSEQ-1K2 k"
            using A17 A16 finseq_1_def_3 sorry
          then have 
            [ty]:"gg be FunctionFUNCT-2M1-of(domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> ?q,domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> ?q)"
            using A32 A30 A42 funct_2_th_2 sorry
          have A58: "lenFINSEQ-1K4 p =XBOOLE-0R4 k"
            using A5 A6 A25 finseq_1_th_17 sorry
          have A59: "rngFUNCT-1K2 gg =XBOOLE-0R4 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> ?q"
          proof-
            have "rngFUNCT-1K2 gg =XBOOLE-0R4 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> (q1 ^FINSEQ-1K9\<^bsub>(D)\<^esub> q2)"
            proof-
              have "rngFUNCT-1K2 gg c=TARSKIR1 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> (q1 ^FINSEQ-1K9\<^bsub>(D)\<^esub> q2) & domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> (q1 ^FINSEQ-1K9\<^bsub>(D)\<^esub> q2) c=TARSKIR1 rngFUNCT-1K2 gg"
              proof(rule conjMI)
                show "rngFUNCT-1K2 gg c=TARSKIR1 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> (q1 ^FINSEQ-1K9\<^bsub>(D)\<^esub> q2)"
                  using A17 A16 A56 A32 A42 finseq_1_def_3 sorry
                have " for y be objectHIDDENM1 holds y inHIDDENR3 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> (q1 ^FINSEQ-1K9\<^bsub>(D)\<^esub> q2) implies y inHIDDENR3 rngFUNCT-1K2 gg"
                proof(rule ballI,rule impI)
                  fix y assume [ty]: "y be objectHIDDENM1"
                  assume A60: "y inHIDDENR3 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> ?q"
                  then obtain j where 
                    [ty]:"j be ElementSUBSET-1M1-of NATNUMBERSK1" and jDef:"j = y"
                     sorry
                  obtain x where
                    [ty]:"x be objectHIDDENM1" and 
                    A61: "x inHIDDENR3 domRELSET-1K1\<^bsub>(domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> H1)\<^esub> f"and A62: "f .FUNCT-1K1 x =HIDDENR1 y"
                    using A8 A26 A57 A60 funct_1_def_3 sorry
                  have 
                    [ty]:"x be ElementSUBSET-1M1-of NATNUMBERSK1"
                    using A11 A61 sorry
                  have "y inHIDDENR3 rngFUNCT-1K2 gg"
                  proof-
                    show "y inHIDDENR3 rngFUNCT-1K2 gg"
                    proof-
                      have cases: "x inTARSKIR2 domRELSET-1K1\<^bsub>(domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> (q1 ^FINSEQ-1K9\<^bsub>(D)\<^esub> q2))\<^esub> gg or  not x inTARSKIR2 domRELSET-1K1\<^bsub>(domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> (q1 ^FINSEQ-1K9\<^bsub>(D)\<^esub> q2))\<^esub> gg"
                         sorry
                      have case1: "x inTARSKIR2 domRELSET-1K1\<^bsub>(domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> (q1 ^FINSEQ-1K9\<^bsub>(D)\<^esub> q2))\<^esub> gg implies y inHIDDENR3 rngFUNCT-1K2 gg"
                      proof(rule impI)
                        assume A63: "x inTARSKIR2 domRELSET-1K1\<^bsub>(domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> (q1 ^FINSEQ-1K9\<^bsub>(D)\<^esub> q2))\<^esub> gg"
                        have "y inHIDDENR3 rngFUNCT-1K2 gg"
                        proof-
                          show "y inHIDDENR3 rngFUNCT-1K2 gg"
                          proof-
                            have cases: "f .FUNCT-1K1 x inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> q1 or  not f .FUNCT-1K1 x inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> q1"
                               sorry
                            have case1: "f .FUNCT-1K1 x inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> q1 implies y inHIDDENR3 rngFUNCT-1K2 gg"
                            proof(rule impI)
                              assume "f .FUNCT-1K1 x inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> q1"
                              then have "gg .FUNCT-1K1 x =XBOOLE-0R4 f .FUNCT-1K1 x"
                                using A30 A31 A63 sorry
                              thus "y inHIDDENR3 rngFUNCT-1K2 gg"
                                using A62 A63 funct_1_def_3 sorry
                            qed
                            have case2: " not f .FUNCT-1K1 x inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> q1 implies y inHIDDENR3 rngFUNCT-1K2 gg"
                            proof(rule impI)
                              assume A64: " not f .FUNCT-1K1 x inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> q1"
                              have "j <=XXREAL-0R1 k"
                                using A57 A60 finseq_1_th_1 sorry
                              then have "\<one>\<^sub>M <=XXREAL-0R1 j +NAT-1K1 \<one>\<^sub>M & j +NAT-1K1 \<one>\<^sub>M <=XXREAL-0R1 k +NAT-1K1 \<one>\<^sub>M"
                                using nat_1_th_12 xreal_1_th_7 sorry
                              then have "j +NAT-1K1 \<one>\<^sub>M inTARSKIR2 rngFUNCT-1K2 f"
                                using A8 finseq_1_th_1 sorry
                              then obtain x1 where
                                [ty]:"x1 be objectHIDDENM1" and 
                                A65: "x1 inHIDDENR3 domRELSET-1K1\<^bsub>(domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> H1)\<^esub> f"and A66: "f .FUNCT-1K1 x1 =XBOOLE-0R4 j +NAT-1K1 \<one>\<^sub>M"
                                using funct_1_def_3 sorry
                              have A67: " not x1 inHIDDENR3 domRELSET-1K1\<^bsub>(domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> (q1 ^FINSEQ-1K9\<^bsub>(D)\<^esub> q2))\<^esub> gg implies  False "
                              proof(rule impI)
                                assume " not x1 inHIDDENR3 domRELSET-1K1\<^bsub>(domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> (q1 ^FINSEQ-1K9\<^bsub>(D)\<^esub> q2))\<^esub> gg"
                                then have "x1 inHIDDENR3 SegFINSEQ-1K2 (k +NAT-1K1 \<one>\<^sub>M) \\SUBSET-1K7\<^bsub>(NATNUMBERSK1)\<^esub> SegFINSEQ-1K2 k"
                                  using A7 A30 A65 xboole_0_def_5 sorry
                                then have "x1 inHIDDENR3 {TARSKIK1 k +NAT-1K1 \<one>\<^sub>M }"
                                  using finseq_3_th_15 sorry
                                then have A68: "j +NAT-1K1 \<one>\<^sub>M =XBOOLE-0R4 m1 +NAT-1K1 \<one>\<^sub>M"
                                  using A17 A66 tarski_def_1 sorry
                                have "\<one>\<^sub>M <=XXREAL-0R1 j"
                                  using A57 A60 finseq_1_th_1 sorry
                                thus " False "
                                  using A34 A62 A64 A68 finseq_1_th_1 sorry
                              qed
                              have "j <XXREAL-0R3 \<one>\<^sub>M or m1 <XXREAL-0R3 j"
                                using A34 A62 A64 finseq_1_th_1 sorry
                              then have " not j +NAT-1K1 \<one>\<^sub>M <=XXREAL-0R1 m1"
                                using A57 A60 finseq_1_th_1 nat_1_th_13 sorry
                              then have " not f .FUNCT-1K1 x1 inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> q1"
                                using A34 A66 finseq_1_th_1 sorry
                              then have "gg .FUNCT-1K1 x1 =HIDDENR1 (j +NAT-1K1 \<one>\<^sub>M)-XCMPLX-0K6 \<one>\<^sub>M"
                                using A30 A31 A66 A67 sorry
                              also have "... = y"
                                 sorry
                              finally have "gg .FUNCT-1K1 x1 =HIDDENR1 y"
                                 sorry
                              thus "y inHIDDENR3 rngFUNCT-1K2 gg"
                                using A67 funct_1_def_3 sorry
                            qed
                            show " ?thesis "
                              using cases case1 case2 sorry
                          qed
                        qed
                        thus "y inHIDDENR3 rngFUNCT-1K2 gg"
                           sorry
                      qed
                      have case2: " not x inTARSKIR2 domRELSET-1K1\<^bsub>(domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> (q1 ^FINSEQ-1K9\<^bsub>(D)\<^esub> q2))\<^esub> gg implies y inHIDDENR3 rngFUNCT-1K2 gg"
                      proof(rule impI)
                        assume A69: " not x inTARSKIR2 domRELSET-1K1\<^bsub>(domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> (q1 ^FINSEQ-1K9\<^bsub>(D)\<^esub> q2))\<^esub> gg"
                        have "j <=XXREAL-0R1 k"
                          using A57 A60 finseq_1_th_1 sorry
                        then have "\<one>\<^sub>M <=XXREAL-0R1 j +NAT-1K1 \<one>\<^sub>M & j +NAT-1K1 \<one>\<^sub>M <=XXREAL-0R1 k +NAT-1K1 \<one>\<^sub>M"
                          using nat_1_th_12 xreal_1_th_7 sorry
                        then have "j +NAT-1K1 \<one>\<^sub>M inTARSKIR2 rngFUNCT-1K2 f"
                          using A8 finseq_1_th_1 sorry
                        then obtain x1 where
                          [ty]:"x1 be objectHIDDENM1" and 
                          A70: "x1 inHIDDENR3 domRELSET-1K1\<^bsub>(domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> H1)\<^esub> f"and A71: "f .FUNCT-1K1 x1 =XBOOLE-0R4 j +NAT-1K1 \<one>\<^sub>M"
                          using funct_1_def_3 sorry
                        have "x inTARSKIR2 SegFINSEQ-1K2 (k +NAT-1K1 \<one>\<^sub>M) \\SUBSET-1K7\<^bsub>(NATNUMBERSK1)\<^esub> SegFINSEQ-1K2 k"
                          using A7 A30 A61 A69 xboole_0_def_5 sorry
                        then have "x inTARSKIR2 {TARSKIK1 k +NAT-1K1 \<one>\<^sub>M }"
                          using finseq_3_th_15 sorry
                        then have A72: "x =XBOOLE-0R4 k +NAT-1K1 \<one>\<^sub>M"
                          using tarski_def_1 sorry
                        have A73: " not x1 inHIDDENR3 domRELSET-1K1\<^bsub>(domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> (q1 ^FINSEQ-1K9\<^bsub>(D)\<^esub> q2))\<^esub> gg implies  False "
                        proof(rule impI)
                          assume " not x1 inHIDDENR3 domRELSET-1K1\<^bsub>(domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> (q1 ^FINSEQ-1K9\<^bsub>(D)\<^esub> q2))\<^esub> gg"
                          then have "x1 inHIDDENR3 SegFINSEQ-1K2 (k +NAT-1K1 \<one>\<^sub>M) \\SUBSET-1K7\<^bsub>(NATNUMBERSK1)\<^esub> SegFINSEQ-1K2 k"
                            using A7 A30 A70 xboole_0_def_5 sorry
                          then have "x1 inHIDDENR3 {TARSKIK1 k +NAT-1K1 \<one>\<^sub>M }"
                            using finseq_3_th_15 sorry
                          then have "j +NAT-1K1 \<one>\<^sub>M =XBOOLE-0R4 j +NAT-1K1 0NUMBERSK6"
                            using A62 A72 A71 tarski_def_1 sorry
                          thus " False "
                             sorry
                        qed
                        have "m1 <=XXREAL-0R1 j"
                          using A17 A62 A72 xreal_1_th_29 sorry
                        then have " not j +NAT-1K1 \<one>\<^sub>M <=XXREAL-0R1 m1"
                          using nat_1_th_13 sorry
                        then have " not f .FUNCT-1K1 x1 inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> q1"
                          using A34 A71 finseq_1_th_1 sorry
                        then have "gg .FUNCT-1K1 x1 =HIDDENR1 (j +NAT-1K1 \<one>\<^sub>M)-XCMPLX-0K6 \<one>\<^sub>M"
                          using A30 A31 A71 A73 sorry
                        also have "... = y"
                           sorry
                        finally have "gg .FUNCT-1K1 x1 =HIDDENR1 y"
                           sorry
                        thus "y inHIDDENR3 rngFUNCT-1K2 gg"
                          using A73 funct_1_def_3 sorry
                      qed
                      show " ?thesis "
                        using cases case1 case2 sorry
                    qed
                  qed
                  thus "y inHIDDENR3 rngFUNCT-1K2 gg"
                     sorry
                qed "sorry"
                thus "domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> (q1 ^FINSEQ-1K9\<^bsub>(D)\<^esub> q2) c=TARSKIR1 rngFUNCT-1K2 gg"
                  using tarski_def_3 sorry
              qed
              thus "rngFUNCT-1K2 gg =XBOOLE-0R4 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> (q1 ^FINSEQ-1K9\<^bsub>(D)\<^esub> q2)"
                using xboole_0_def_10 sorry
            qed
            thus " ?thesis "
               sorry
          qed
          assume A74: " for i be NatNAT-1M1 holds i inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> H2 implies H2 .FUNCT-1K1 i =XBOOLE-0R4 H1 .FUNCT-1K1 (f .FUNCT-1K1 i)"
          then have A75: "H2 .FUNCT-1K1 (k +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 H1 .FUNCT-1K1 (f .FUNCT-1K1 (k +NAT-1K1 \<one>\<^sub>M))"
            using A14 finseq_1_th_4 sorry
          have A76: " for j be NatNAT-1M1 holds j inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> (q1 ^FINSEQ-1K9\<^bsub>(D)\<^esub> (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>)) implies H1 .FUNCT-1K1 j =XBOOLE-0R4 (q1 ^FINSEQ-1K9\<^bsub>(D)\<^esub> (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>)).FUNCT-1K1 j"
          proof(rule ballI,rule impI)
            fix j assume [ty]: "j be NatNAT-1M1"
            assume A77: "j inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> (q1 ^FINSEQ-1K9\<^bsub>(D)\<^esub> (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>))"
            have A78: "j inTARSKIR2 SegFINSEQ-1K2 m1 implies H1 .FUNCT-1K1 j =XBOOLE-0R4 (q1 ^FINSEQ-1K9\<^bsub>(D)\<^esub> (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>)).FUNCT-1K1 j"
            proof(rule impI)
              assume "j inTARSKIR2 SegFINSEQ-1K2 m1"
              then have A79: "j inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> q1"
                using A5 A33 finseq_1_th_17 sorry
              then have "q1 .FUNCT-1K1 j =XBOOLE-0R4 H1 .FUNCT-1K1 j"
                using funct_1_th_47 sorry
              thus "H1 .FUNCT-1K1 j =XBOOLE-0R4 (q1 ^FINSEQ-1K9\<^bsub>(D)\<^esub> (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>)).FUNCT-1K1 j"
                using A79 finseq_1_def_7 sorry
            qed
            have A80: "j inTARSKIR2 {TARSKIK1 n} implies (q1 ^FINSEQ-1K9\<^bsub>(D)\<^esub> (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>)).FUNCT-1K1 j =XBOOLE-0R4 H1 .FUNCT-1K1 j"
            proof(rule impI)
              have "\<one>\<^sub>M inTARSKIR2 SegFINSEQ-1K2 \<one>\<^sub>M & lenFINSEQ-1K4 (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>) =XBOOLE-0R4 \<one>\<^sub>M"
                using finseq_1_th_1 finseq_1_th_39 sorry
              then have "\<one>\<^sub>M inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>)"
                using finseq_1_def_3 sorry
              then have A81: "(q1 ^FINSEQ-1K9\<^bsub>(D)\<^esub> (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>)).FUNCT-1K1 (lenFINSEQ-1K4 q1 +NAT-1K1 \<one>\<^sub>M) =XBOOLE-0R4 (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>).FUNCT-1K1 \<one>\<^sub>M"
                using finseq_1_def_7 sorry
              assume "j inTARSKIR2 {TARSKIK1 n}"
              then have "j =XBOOLE-0R4 n"
                using tarski_def_1 sorry
              thus "(q1 ^FINSEQ-1K9\<^bsub>(D)\<^esub> (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>)).FUNCT-1K1 j =XBOOLE-0R4 H1 .FUNCT-1K1 j"
                using A75 A17 A52 A81 finseq_1_th_40 sorry
            qed
            have "lenFINSEQ-1K4 (q1 ^FINSEQ-1K9\<^bsub>(D)\<^esub> (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>)) =HIDDENR1 m1 +NAT-1K1 lenFINSEQ-1K4 (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>)"
              using A52 finseq_1_th_22 sorry
            also have "... = m1 +NAT-1K1 \<one>\<^sub>M"
              using finseq_1_th_40 sorry
            finally have "lenFINSEQ-1K4 (q1 ^FINSEQ-1K9\<^bsub>(D)\<^esub> (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>)) =HIDDENR1 m1 +NAT-1K1 \<one>\<^sub>M"
               sorry
            then have "j inTARSKIR2 SegFINSEQ-1K2 (m1 +NAT-1K1 \<one>\<^sub>M)"
              using A77 finseq_1_def_3 sorry
            then have "j inTARSKIR2 SegFINSEQ-1K2 m1 \\/XBOOLE-0K2 {TARSKIK1 n}"
              using A17 finseq_1_th_9 sorry
            thus "H1 .FUNCT-1K1 j =XBOOLE-0R4 (q1 ^FINSEQ-1K9\<^bsub>(D)\<^esub> (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>)).FUNCT-1K1 j"
              using A78 A80 xboole_0_def_3 sorry
          qed "sorry"
          have "gg be one-to-oneFUNCT-1V2"
          proof-
            have " for y1 be objectHIDDENM1 holds  for y2 be objectHIDDENM1 holds y1 inHIDDENR3 domRELSET-1K1\<^bsub>(domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> (q1 ^FINSEQ-1K9\<^bsub>(D)\<^esub> q2))\<^esub> gg & (y2 inHIDDENR3 domRELSET-1K1\<^bsub>(domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> (q1 ^FINSEQ-1K9\<^bsub>(D)\<^esub> q2))\<^esub> gg & gg .FUNCT-1K1 y1 =XBOOLE-0R4 gg .FUNCT-1K1 y2) implies y1 =HIDDENR1 y2"
            proof(rule ballI,rule ballI,rule impMI ,rule impMI ,rule impI)
              fix y1 assume [ty]: "y1 be objectHIDDENM1"
              fix y2 assume [ty]: "y2 be objectHIDDENM1"
              assume A82: "y1 inHIDDENR3 domRELSET-1K1\<^bsub>(domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> (q1 ^FINSEQ-1K9\<^bsub>(D)\<^esub> q2))\<^esub> gg"
                and A83: "y2 inHIDDENR3 domRELSET-1K1\<^bsub>(domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> (q1 ^FINSEQ-1K9\<^bsub>(D)\<^esub> q2))\<^esub> gg"
                and A84: "gg .FUNCT-1K1 y1 =XBOOLE-0R4 gg .FUNCT-1K1 y2"
              obtain j1 j2 where 
                [ty]:"j1 be ElementSUBSET-1M1-of NATNUMBERSK1" and j1Def:"j1 = y1" and
                [ty]:"j2 be ElementSUBSET-1M1-of NATNUMBERSK1" and j2Def:"j2 = y2"
                using A30 A82 A83 sorry
              have A85: "f .FUNCT-1K1 y2 inTARSKIR2 SegFINSEQ-1K2 (k +NAT-1K1 \<one>\<^sub>M)"
                using A11 A8 A26 A30 A83 funct_1_def_3 sorry
              have A86: "f .FUNCT-1K1 y1 inTARSKIR2 SegFINSEQ-1K2 (k +NAT-1K1 \<one>\<^sub>M)"
                using A11 A8 A26 A30 A82 funct_1_def_3 sorry
              then obtain a b where 
                [ty]:"a be ElementSUBSET-1M1-of NATNUMBERSK1" and aDef:"a = f .FUNCT-1K1 y1" and
                [ty]:"b be ElementSUBSET-1M1-of NATNUMBERSK1" and bDef:"b = f .FUNCT-1K1 y2"
                using A85 sorry
              have "y1 =HIDDENR1 y2"
              proof-
                show "y1 =HIDDENR1 y2"
                proof-
                  have cases: "((f .FUNCT-1K1 y1 inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> q1 & f .FUNCT-1K1 y2 inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> q1 or f .FUNCT-1K1 y1 inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> q1 &  not f .FUNCT-1K1 y2 inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> q1) or  not f .FUNCT-1K1 y1 inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> q1 & f .FUNCT-1K1 y2 inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> q1) or  not f .FUNCT-1K1 y1 inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> q1 &  not f .FUNCT-1K1 y2 inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> q1"
                     sorry
                  have case1: "f .FUNCT-1K1 y1 inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> q1 & f .FUNCT-1K1 y2 inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> q1 implies y1 =HIDDENR1 y2"
                  proof(rule impI)
                    assume "f .FUNCT-1K1 y1 inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> q1 & f .FUNCT-1K1 y2 inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> q1"
                    then have "gg .FUNCT-1K1 j1 =XBOOLE-0R4 f .FUNCT-1K1 y1 & gg .FUNCT-1K1 j2 =XBOOLE-0R4 f .FUNCT-1K1 y2"
                      using A30 A31 A82 A83 sorry
                    thus "y1 =HIDDENR1 y2"
                      using A11 A26 A30 A82 A83 A84 funct_1_def_4 sorry
                  qed
                  have case2: "f .FUNCT-1K1 y1 inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> q1 &  not f .FUNCT-1K1 y2 inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> q1 implies y1 =HIDDENR1 y2"
                  proof(rule impI)
                    assume A87: "f .FUNCT-1K1 y1 inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> q1 &  not f .FUNCT-1K1 y2 inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> q1"
                    then have A88: "a <=XXREAL-0R1 m1"
                      using A34 finseq_1_th_1 sorry
                    have "gg .FUNCT-1K1 j1 =XBOOLE-0R4 a & gg .FUNCT-1K1 j2 =XBOOLE-0R4 b -XCMPLX-0K6 \<one>\<^sub>M"
                      using A30 A31 A82 A83 A87 sorry
                    then have A89: "(b -XCMPLX-0K6 \<one>\<^sub>M)+XCMPLX-0K2 \<one>\<^sub>M <=XXREAL-0R1 m1 +NAT-1K1 \<one>\<^sub>M"
                      using A84 A88 xreal_1_th_6 sorry
                    have "\<one>\<^sub>M <=XXREAL-0R1 b"
                      using A85 finseq_1_th_1 sorry
                    then have A90: "b inTARSKIR2 SegFINSEQ-1K2 (m1 +NAT-1K1 \<one>\<^sub>M)"
                      using A89 finseq_1_th_1 sorry
                    have " not b inTARSKIR2 SegFINSEQ-1K2 m1"
                      using A5 A33 A87 finseq_1_th_17 sorry
                    then have "b inTARSKIR2 SegFINSEQ-1K2 (m1 +NAT-1K1 \<one>\<^sub>M) \\SUBSET-1K7\<^bsub>(NATNUMBERSK1)\<^esub> SegFINSEQ-1K2 m1"
                      using A90 xboole_0_def_5 sorry
                    then have "b inTARSKIR2 {TARSKIK1 m1 +NAT-1K1 \<one>\<^sub>M }"
                      using finseq_3_th_15 sorry
                    then have "b =XBOOLE-0R4 m1 +NAT-1K1 \<one>\<^sub>M"
                      using tarski_def_1 sorry
                    then have "y2 =HIDDENR1 k +NAT-1K1 \<one>\<^sub>M"
                      using A12 A11 A17 A26 A30 A83 funct_1_def_4 sorry
                    thus "y1 =HIDDENR1 y2"
                      using A30 A83 finseq_3_th_8 sorry
                  qed
                  have case3: " not f .FUNCT-1K1 y1 inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> q1 & f .FUNCT-1K1 y2 inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> q1 implies y1 =HIDDENR1 y2"
                  proof(rule impI)
                    assume A91: " not f .FUNCT-1K1 y1 inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> q1 & f .FUNCT-1K1 y2 inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> q1"
                    then have A92: "b <=XXREAL-0R1 m1"
                      using A34 finseq_1_th_1 sorry
                    have "gg .FUNCT-1K1 j1 =XBOOLE-0R4 a -XCMPLX-0K6 \<one>\<^sub>M & gg .FUNCT-1K1 j2 =XBOOLE-0R4 b"
                      using A30 A31 A82 A83 A91 sorry
                    then have A93: "(a -XCMPLX-0K6 \<one>\<^sub>M)+XCMPLX-0K2 \<one>\<^sub>M <=XXREAL-0R1 m1 +NAT-1K1 \<one>\<^sub>M"
                      using A84 A92 xreal_1_th_6 sorry
                    have "\<one>\<^sub>M <=XXREAL-0R1 a"
                      using A86 finseq_1_th_1 sorry
                    then have A94: "a inTARSKIR2 SegFINSEQ-1K2 (m1 +NAT-1K1 \<one>\<^sub>M)"
                      using A93 finseq_1_th_1 sorry
                    have " not a inTARSKIR2 SegFINSEQ-1K2 m1"
                      using A5 A33 A91 finseq_1_th_17 sorry
                    then have "a inTARSKIR2 SegFINSEQ-1K2 (m1 +NAT-1K1 \<one>\<^sub>M) \\SUBSET-1K7\<^bsub>(NATNUMBERSK1)\<^esub> SegFINSEQ-1K2 m1"
                      using A94 xboole_0_def_5 sorry
                    then have "a inTARSKIR2 {TARSKIK1 m1 +NAT-1K1 \<one>\<^sub>M }"
                      using finseq_3_th_15 sorry
                    then have "a =XBOOLE-0R4 m1 +NAT-1K1 \<one>\<^sub>M"
                      using tarski_def_1 sorry
                    then have "y1 =HIDDENR1 k +NAT-1K1 \<one>\<^sub>M"
                      using A12 A11 A17 A26 A30 A82 funct_1_def_4 sorry
                    thus "y1 =HIDDENR1 y2"
                      using A30 A82 finseq_3_th_8 sorry
                  qed
                  have case4: " not f .FUNCT-1K1 y1 inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> q1 &  not f .FUNCT-1K1 y2 inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> q1 implies y1 =HIDDENR1 y2"
                  proof(rule impI)
                    assume A95: " not f .FUNCT-1K1 y1 inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> q1 &  not f .FUNCT-1K1 y2 inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> q1"
                    then have "gg .FUNCT-1K1 j2 =XBOOLE-0R4 b -XCMPLX-0K6 \<one>\<^sub>M"
                      using A30 A31 A83 sorry
                    then have A96: "gg .FUNCT-1K1 y2 =XBOOLE-0R4 b +XCMPLX-0K2 (-XCMPLX-0K4 \<one>\<^sub>M)"
                       sorry
                    have "gg .FUNCT-1K1 j1 =XBOOLE-0R4 a -XCMPLX-0K6 \<one>\<^sub>M"
                      using A30 A31 A82 A95 sorry
                    then have "gg .FUNCT-1K1 j1 =XBOOLE-0R4 a +XCMPLX-0K2 (-XCMPLX-0K4 \<one>\<^sub>M)"
                       sorry
                    then have "a =XBOOLE-0R4 b"
                      using A84 A96 xcmplx_1_th_2 sorry
                    thus "y1 =HIDDENR1 y2"
                      using A11 A26 A30 A82 A83 funct_1_def_4 sorry
                  qed
                  show " ?thesis "
                    using cases case1 case2 case3 case4 sorry
                qed
              qed
              thus "y1 =HIDDENR1 y2"
                 sorry
            qed "sorry"
            thus "gg be one-to-oneFUNCT-1V2"
              using funct_1_def_4 sorry
          qed
          then have 
            [ty]:"gg be PermutationFUNCT-2M2-of domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> ?q"
            using A59 funct_2_th_57 sorry
          have "lenFINSEQ-1K4 (q1 ^FINSEQ-1K9\<^bsub>(D)\<^esub> (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>)) +NAT-1K1 lenFINSEQ-1K4 q2 =HIDDENR1 (lenFINSEQ-1K4 q1 +NAT-1K1 lenFINSEQ-1K4 (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>))+NAT-1K1 m2"
            using A55 finseq_1_th_22 sorry
          also have "... = k +NAT-1K1 \<one>\<^sub>M"
            using A17 A16 A52 finseq_1_th_40 sorry
          finally have "lenFINSEQ-1K4 (q1 ^FINSEQ-1K9\<^bsub>(D)\<^esub> (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>)) +NAT-1K1 lenFINSEQ-1K4 q2 =HIDDENR1 k +NAT-1K1 \<one>\<^sub>M"
             sorry
          then have "domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> H1 =XBOOLE-0R4 SegFINSEQ-1K2 (lenFINSEQ-1K4 (q1 ^FINSEQ-1K9\<^bsub>(D)\<^esub> (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>)) +NAT-1K1 lenFINSEQ-1K4 q2)"
            using A5 finseq_1_def_3 sorry
          then have A97: "H1 =FUNCT-1R1 (q1 ^FINSEQ-1K9\<^bsub>(D)\<^esub> (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>))^FINSEQ-1K9\<^bsub>(D)\<^esub> q2"
            using A76 A53 finseq_1_def_7 sorry
          have A98: " for i be NatNAT-1M1 holds i inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> p implies p .FUNCT-1K1 i =XBOOLE-0R4 (q1 ^FINSEQ-1K9\<^bsub>(D)\<^esub> q2).FUNCT-1K1 (gg .FUNCT-1K1 i)"
          proof(rule ballI,rule impI)
            fix i assume [ty]: "i be NatNAT-1M1"
            assume A99: "i inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> p"
            then have "f .FUNCT-1K1 i inTARSKIR2 rngFUNCT-1K2 f"
              using A11 A26 A32 funct_1_def_3 sorry
            then obtain j where 
              [ty]:"j be ElementSUBSET-1M1-of NATNUMBERSK1" and jDef:"j = f .FUNCT-1K1 i"
              using A8 sorry
            have "p .FUNCT-1K1 i =XBOOLE-0R4 (q1 ^FINSEQ-1K9\<^bsub>(D)\<^esub> q2).FUNCT-1K1 (gg .FUNCT-1K1 i)"
            proof-
              show "p .FUNCT-1K1 i =XBOOLE-0R4 (q1 ^FINSEQ-1K9\<^bsub>(D)\<^esub> q2).FUNCT-1K1 (gg .FUNCT-1K1 i)"
              proof-
                have cases: "f .FUNCT-1K1 i inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> q1 or  not f .FUNCT-1K1 i inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> q1"
                   sorry
                have case1: "f .FUNCT-1K1 i inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> q1 implies p .FUNCT-1K1 i =XBOOLE-0R4 (q1 ^FINSEQ-1K9\<^bsub>(D)\<^esub> q2).FUNCT-1K1 (gg .FUNCT-1K1 i)"
                proof(rule impI)
                  assume A100: "f .FUNCT-1K1 i inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> q1"
                  then have A101: "f .FUNCT-1K1 i =XBOOLE-0R4 gg .FUNCT-1K1 i & H1 .FUNCT-1K1 j =XBOOLE-0R4 q1 .FUNCT-1K1 j"
                    using A32 A31 A99 funct_1_th_47 sorry
                  have "H2 .FUNCT-1K1 i =XBOOLE-0R4 p .FUNCT-1K1 i & H2 .FUNCT-1K1 i =XBOOLE-0R4 H1 .FUNCT-1K1 (f .FUNCT-1K1 i)"
                    using A74 A14 A26 A32 A99 funct_1_th_47 sorry
                  thus "p .FUNCT-1K1 i =XBOOLE-0R4 (q1 ^FINSEQ-1K9\<^bsub>(D)\<^esub> q2).FUNCT-1K1 (gg .FUNCT-1K1 i)"
                    using A100 A101 finseq_1_def_7 sorry
                qed
                have case2: " not f .FUNCT-1K1 i inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> q1 implies p .FUNCT-1K1 i =XBOOLE-0R4 (q1 ^FINSEQ-1K9\<^bsub>(D)\<^esub> q2).FUNCT-1K1 (gg .FUNCT-1K1 i)"
                proof(rule impI)
                  assume A102: " not f .FUNCT-1K1 i inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> q1"
                  then have "m1 +NAT-1K1 \<two>\<^sub>M <=XXREAL-0R1 j"
                    using A32 A30 A35 A99 sorry
                  then have A103: "(m1 +NAT-1K1 \<two>\<^sub>M)-XCMPLX-0K6 \<one>\<^sub>M <=XXREAL-0R1 j -XCMPLX-0K6 \<one>\<^sub>M"
                    using xreal_1_th_9 sorry
                  have "m1 <XXREAL-0R3 m1 +NAT-1K1 \<one>\<^sub>M"
                    using xreal_1_th_29 sorry
                  then have A104: "m1 <XXREAL-0R3 j -XCMPLX-0K6 \<one>\<^sub>M"
                    using A103 xxreal_0_th_2 sorry
                  then have "m1 <XXREAL-0R3 j"
                    using xreal_1_th_146 xxreal_0_th_2 sorry
                  then obtain j1 where 
                    [ty]:"j1 be ElementSUBSET-1M1-of NATNUMBERSK1" and j1Def:"j1 = j -XCMPLX-0K6 \<one>\<^sub>M"
                    using nat_1_th_20 sorry
                  have A105: " not j1 inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> q1"
                    using A34 A104 finseq_1_th_1 sorry
                  have A106: "gg .FUNCT-1K1 i =XBOOLE-0R4 j -XCMPLX-0K6 \<one>\<^sub>M"
                    using A32 A31 A99 A102 sorry
                  then have "j -XCMPLX-0K6 \<one>\<^sub>M inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> ?q"
                    using A32 A30 A59 A99 funct_1_def_3 sorry
                  then obtain a where
                    [ty]:"a be NatNAT-1M1" and 
                    A107: "a inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> q2"and A108: "j1 =XBOOLE-0R4 lenFINSEQ-1K4 q1 +XCMPLX-0K2 a"
                    using A105 finseq_1_th_25 sorry
                  have A109: "lenFINSEQ-1K4 (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>) =XBOOLE-0R4 \<one>\<^sub>M"
                    using finseq_1_th_39 sorry
                  have A110: "H2 .FUNCT-1K1 i =XBOOLE-0R4 p .FUNCT-1K1 i & H2 .FUNCT-1K1 i =XBOOLE-0R4 H1 .FUNCT-1K1 (f .FUNCT-1K1 i)"
                    using A74 A14 A26 A32 A99 funct_1_th_47 sorry
                  have A111: "H1 =FUNCT-1R1 q1 ^FINSEQ-1K9\<^bsub>(D)\<^esub> ((<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>)^FINSEQ-1K9\<^bsub>(D)\<^esub> q2)"
                    using A97 finseq_1_th_32 sorry
                  have "j inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> H1"
                    using A7 A11 A8 A26 A32 A99 funct_1_def_3 sorry
                  then obtain b where
                    [ty]:"b be NatNAT-1M1" and 
                    A112: "b inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> ((<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>)^FINSEQ-1K9\<^bsub>(D)\<^esub> q2)"and A113: "j =XBOOLE-0R4 lenFINSEQ-1K4 q1 +XCMPLX-0K2 b"
                    using A102 A111 finseq_1_th_25 sorry
                  have A114: "H1 .FUNCT-1K1 j =XBOOLE-0R4 ((<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>)^FINSEQ-1K9\<^bsub>(D)\<^esub> q2).FUNCT-1K1 b"
                    using A111 A112 A113 finseq_1_def_7 sorry
                  have A115: "b =XBOOLE-0R4 \<one>\<^sub>M +XCMPLX-0K2 a"
                    using A108 A113 sorry
                  have "?q .FUNCT-1K1 (j -XCMPLX-0K6 \<one>\<^sub>M) =XBOOLE-0R4 q2 .FUNCT-1K1 a"
                    using A107 A108 finseq_1_def_7 sorry
                  thus "p .FUNCT-1K1 i =XBOOLE-0R4 (q1 ^FINSEQ-1K9\<^bsub>(D)\<^esub> q2).FUNCT-1K1 (gg .FUNCT-1K1 i)"
                    using A106 A110 A107 A114 A115 A109 finseq_1_def_7 sorry
                qed
                show " ?thesis "
                  using cases case1 case2 sorry
              qed
            qed
            thus "p .FUNCT-1K1 i =XBOOLE-0R4 (q1 ^FINSEQ-1K9\<^bsub>(D)\<^esub> q2).FUNCT-1K1 (gg .FUNCT-1K1 i)"
               sorry
          qed "sorry"
          have "g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> H1 =XBOOLE-0R4 g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> H2"
          proof-
            show "g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> H1 =XBOOLE-0R4 g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> H2"
            proof-
              have cases: "lenFINSEQ-1K4 p <>HIDDENR2 0NUMBERSK6 or lenFINSEQ-1K4 p =XBOOLE-0R4 0NUMBERSK6"
                 sorry
              have case1: "lenFINSEQ-1K4 p <>HIDDENR2 0NUMBERSK6 implies g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> H1 =XBOOLE-0R4 g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> H2"
              proof(rule impI)
                assume A116: "lenFINSEQ-1K4 p <>HIDDENR2 0NUMBERSK6"
                have A117: "H2 =FUNCT-1R1 p ^FINSEQ-1K9\<^bsub>(D)\<^esub> (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>)"
                  using A5 A6 finseq_3_th_55 sorry
                have "g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> p =XBOOLE-0R4 g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> ?q"
                  using A4 A17 A16 A58 A56 A98 A116 nat_1_th_14 sorry
                then have A118: "g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> H2 =XBOOLE-0R4 g .BINOP-1K4\<^bsub>(D)\<^esub>(g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> ?q,d)"
                  using A116 A117 finsop_1_th_4 nat_1_th_14 sorry
                have "g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> H1 =XBOOLE-0R4 g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> H2"
                proof-
                  show "g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> H1 =XBOOLE-0R4 g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> H2"
                  proof-
                    have cases: "((lenFINSEQ-1K4 q1 <>HIDDENR2 0NUMBERSK6 & lenFINSEQ-1K4 q2 <>HIDDENR2 0NUMBERSK6 or lenFINSEQ-1K4 q1 =XBOOLE-0R4 0NUMBERSK6 & lenFINSEQ-1K4 q2 <>HIDDENR2 0NUMBERSK6) or lenFINSEQ-1K4 q1 <>HIDDENR2 0NUMBERSK6 & lenFINSEQ-1K4 q2 =XBOOLE-0R4 0NUMBERSK6) or lenFINSEQ-1K4 q1 =XBOOLE-0R4 0NUMBERSK6 & lenFINSEQ-1K4 q2 =XBOOLE-0R4 0NUMBERSK6"
                       sorry
                    have case1: "lenFINSEQ-1K4 q1 <>HIDDENR2 0NUMBERSK6 & lenFINSEQ-1K4 q2 <>HIDDENR2 0NUMBERSK6 implies g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> H1 =XBOOLE-0R4 g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> H2"
                    proof(rule impI)
                      assume A119: "lenFINSEQ-1K4 q1 <>HIDDENR2 0NUMBERSK6 & lenFINSEQ-1K4 q2 <>HIDDENR2 0NUMBERSK6"
                      have "lenFINSEQ-1K4 ((<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>)^FINSEQ-1K9\<^bsub>(D)\<^esub> q2) =XBOOLE-0R4 lenFINSEQ-1K4 (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>) +NAT-1K1 lenFINSEQ-1K4 q2 & lenFINSEQ-1K4 (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>) =XBOOLE-0R4 \<one>\<^sub>M"
                        using finseq_1_th_22 finseq_1_th_40 sorry
                      then have A120: "lenFINSEQ-1K4 ((<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>)^FINSEQ-1K9\<^bsub>(D)\<^esub> q2) >=XXREAL-0R2 \<one>\<^sub>M"
                        using nat_1_th_12 sorry
                      have A121: "lenFINSEQ-1K4 q1 >=XXREAL-0R2 \<one>\<^sub>M"
                        using A119 nat_1_th_14 sorry
                      have "lenFINSEQ-1K4 q2 >=XXREAL-0R2 \<one>\<^sub>M"
                        using A119 nat_1_th_14 sorry
                      then have "g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> H2 =HIDDENR1 g .BINOP-1K4\<^bsub>(D)\<^esub>(g .BINOP-1K4\<^bsub>(D)\<^esub>(g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> q1,g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> q2),d)"
                        using A1 A118 A121 finsop_1_th_5 sorry
                      also have "... = g .BINOP-1K4\<^bsub>(D)\<^esub>(g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> q1,g .BINOP-1K4\<^bsub>(D)\<^esub>(g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> q2,d))"
                        using A1 binop_1_def_3 sorry
                      also have "... = g .BINOP-1K4\<^bsub>(D)\<^esub>(g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> q1,g .BINOP-1K4\<^bsub>(D)\<^esub>(d,g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> q2))"
                        using A2 binop_1_def_2 sorry
                      also have "... = g .BINOP-1K4\<^bsub>(D)\<^esub>(g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> q1,g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>)^FINSEQ-1K9\<^bsub>(D)\<^esub> q2)"
                        using A1 A119 finsop_1_th_6 nat_1_th_14 sorry
                      also have "... = g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> q1 ^FINSEQ-1K9\<^bsub>(D)\<^esub> ((<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>)^FINSEQ-1K9\<^bsub>(D)\<^esub> q2)"
                        using A1 A121 A120 finsop_1_th_5 sorry
                      also have "... = g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> H1"
                        using A97 finseq_1_th_32 sorry
                      finally have "g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> H2 =HIDDENR1 g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> H1"
                         sorry
                      thus "g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> H1 =XBOOLE-0R4 g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> H2"
                         sorry
                    qed
                    have case2: "lenFINSEQ-1K4 q1 =XBOOLE-0R4 0NUMBERSK6 & lenFINSEQ-1K4 q2 <>HIDDENR2 0NUMBERSK6 implies g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> H1 =XBOOLE-0R4 g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> H2"
                    proof(rule impI)
                      assume "lenFINSEQ-1K4 q1 =XBOOLE-0R4 0NUMBERSK6 & lenFINSEQ-1K4 q2 <>HIDDENR2 0NUMBERSK6"
                      then have A122: "q1 =XBOOLE-0R4 {}XBOOLE-0K1"
                         sorry
                      then have A123: "H1 =HIDDENR1 (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>)^FINSEQ-1K9\<^bsub>(D)\<^esub> q2"
                        using A97 finseq_1_th_34 sorry
                      also have "... = (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>)^FINSEQ-1K9\<^bsub>(D)\<^esub> ?q"
                        using A122 finseq_1_th_34 sorry
                      finally have "H1 =HIDDENR1 (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>)^FINSEQ-1K9\<^bsub>(D)\<^esub> ?q"
                         sorry
                      have "g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> H2 =HIDDENR1 g .BINOP-1K4\<^bsub>(D)\<^esub>(d,g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> ?q)"
                        using A2 A118 binop_1_def_2 sorry
                      also have "... = g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>)^FINSEQ-1K9\<^bsub>(D)\<^esub> ?q"
                        using A1 A17 A16 A58 A56 A116 finsop_1_th_6 nat_1_th_14 sorry
                      finally have "g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> H2 =HIDDENR1 g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>)^FINSEQ-1K9\<^bsub>(D)\<^esub> ?q"
                         sorry
                      thus "g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> H1 =XBOOLE-0R4 g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> H2"
                        using A123 sorry
                    qed
                    have case3: "lenFINSEQ-1K4 q1 <>HIDDENR2 0NUMBERSK6 & lenFINSEQ-1K4 q2 =XBOOLE-0R4 0NUMBERSK6 implies g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> H1 =XBOOLE-0R4 g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> H2"
                    proof(rule impI)
                      assume "lenFINSEQ-1K4 q1 <>HIDDENR2 0NUMBERSK6 & lenFINSEQ-1K4 q2 =XBOOLE-0R4 0NUMBERSK6"
                      then have A124: "q2 =XBOOLE-0R4 {}XBOOLE-0K1"
                         sorry
                      then have "H1 =HIDDENR1 q1 ^FINSEQ-1K9\<^bsub>(D)\<^esub> (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>)"
                        using A97 finseq_1_th_34 sorry
                      also have "... = ?q ^FINSEQ-1K9\<^bsub>(D)\<^esub> (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>)"
                        using A124 finseq_1_th_34 sorry
                      finally have "H1 =HIDDENR1 ?q ^FINSEQ-1K9\<^bsub>(D)\<^esub> (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>)"
                         sorry
                      thus "g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> H1 =XBOOLE-0R4 g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> H2"
                        using A17 A16 A58 A56 A116 A118 finsop_1_th_4 nat_1_th_14 sorry
                    qed
                    have case4: "lenFINSEQ-1K4 q1 =XBOOLE-0R4 0NUMBERSK6 & lenFINSEQ-1K4 q2 =XBOOLE-0R4 0NUMBERSK6 implies g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> H1 =XBOOLE-0R4 g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> H2"
                    proof(rule impI)
                      assume "lenFINSEQ-1K4 q1 =XBOOLE-0R4 0NUMBERSK6 & lenFINSEQ-1K4 q2 =XBOOLE-0R4 0NUMBERSK6"
                      then have "lenFINSEQ-1K4 ?q =XBOOLE-0R4 0NUMBERSK6 +NAT-1K1 0NUMBERSK6"
                        using finseq_1_th_22 sorry
                      thus "g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> H1 =XBOOLE-0R4 g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> H2"
                        using A6 A17 A16 A56 A116 finseq_1_th_17 sorry
                    qed
                    show " ?thesis "
                      using cases case1 case2 case3 case4 sorry
                  qed
                qed
                thus "g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> H1 =XBOOLE-0R4 g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> H2"
                   sorry
              qed
              have case2: "lenFINSEQ-1K4 p =XBOOLE-0R4 0NUMBERSK6 implies g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> H1 =XBOOLE-0R4 g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> H2"
              proof(rule impI)
                assume A125: "lenFINSEQ-1K4 p =XBOOLE-0R4 0NUMBERSK6"
                then have "domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> H1 =XBOOLE-0R4 {TARSKIK1 \<one>\<^sub>M}"
                  using A5 A58 finseq_1_th_2 finseq_1_def_3 sorry
                then have A126: "domRELSET-1K1\<^bsub>(domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> H1)\<^esub> f =XBOOLE-0R4 {TARSKIK1 \<one>\<^sub>M} & rngFUNCT-1K2 f =XBOOLE-0R4 {TARSKIK1 \<one>\<^sub>M}"
                  using funct_2_def_1 funct_2_def_3 sorry
                have "\<one>\<^sub>M inTARSKIR2 {TARSKIK1 \<one>\<^sub>M}"
                  using tarski_def_1 sorry
                then have "f .FUNCT-1K1 \<one>\<^sub>M inTARSKIR2 {TARSKIK1 \<one>\<^sub>M}"
                  using A126 funct_1_def_3 sorry
                then have "H1 .FUNCT-1K1 \<one>\<^sub>M =XBOOLE-0R4 H2 .FUNCT-1K1 \<one>\<^sub>M"
                  using A75 A58 A125 tarski_def_1 sorry
                then have "H1 =FUNCT-1R1 <*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>"
                  using A5 A58 A125 finseq_1_th_40 sorry
                thus "g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> H1 =XBOOLE-0R4 g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> H2"
                  using A5 A6 A58 A125 finseq_1_th_40 sorry
              qed
              show " ?thesis "
                using cases case1 case2 sorry
            qed
          qed
          thus "g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> H1 =XBOOLE-0R4 g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> H2"
             sorry
        qed "sorry"
        thus " ?thesis "
           sorry
      qed
    qed "sorry"
    fix f assume [ty]: "f be PermutationFUNCT-2M2-of domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> F"
    have A127: "?P(0NUMBERSK6)"
       sorry
    have " for k be NatNAT-1M1 holds ?P(k)"
      using nat_1_sch_2 A127 A3 sorry
    thus " not (((lenFINSEQ-1K4 F >=XXREAL-0R2 \<one>\<^sub>M & lenFINSEQ-1K4 F =XBOOLE-0R4 lenFINSEQ-1K4 G) & ( for i be NatNAT-1M1 holds  not (i inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> G &  not G .FUNCT-1K1 i =XBOOLE-0R4 F .FUNCT-1K1 (f .FUNCT-1K1 i)))) &  not g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F =XBOOLE-0R4 g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> G)"
       sorry
  qed "sorry"
  thus " ?thesis "
     sorry
qed

mlemma finsop_1_lm_8:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for F be FinSequenceFINSEQ-1M3-of D holds  for G be FinSequenceFINSEQ-1M3-of D holds  for g be BinOpBINOP-1M2-of D holds  for P be PermutationFUNCT-2M2-of domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> F holds (g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> & lenFINSEQ-1K4 F =XBOOLE-0R4 0NUMBERSK6) & G =FUNCT-1R1 F *FUNCT-1K3 P implies g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F =XBOOLE-0R4 g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> G"
proof-
  have " for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for F be FinSequenceFINSEQ-1M3-of D holds  for G be FinSequenceFINSEQ-1M3-of D holds  for g be BinOpBINOP-1M2-of D holds  for P be PermutationFUNCT-2M2-of domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> F holds g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> & lenFINSEQ-1K4 F =XBOOLE-0R4 0NUMBERSK6 implies (G =FUNCT-1R1 F *FUNCT-1K3 P implies g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F =HIDDENR1 g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> G)"
  proof(rule ballI,rule ballI,rule ballI,rule ballI,rule ballI,rule impMI ,rule impI,rule impI)
    fix D assume [ty]: "D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
    fix F assume [ty]: "F be FinSequenceFINSEQ-1M3-of D"
    fix G assume [ty]: "G be FinSequenceFINSEQ-1M3-of D"
    fix g assume [ty]: "g be BinOpBINOP-1M2-of D"
    fix P assume [ty]: "P be PermutationFUNCT-2M2-of domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> F"
    assume A1: "g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub>"
      and A2: "lenFINSEQ-1K4 F =XBOOLE-0R4 0NUMBERSK6"
    assume A3: "G =FUNCT-1R1 F *FUNCT-1K3 P"
    have "F =XBOOLE-0R4 {}XBOOLE-0K1"
      using A2 sorry
    then have "G =XBOOLE-0R4 {}XBOOLE-0K1"
      using A3 relat_1_th_39 sorry
    then have A4: "lenFINSEQ-1K4 G =XBOOLE-0R4 0NUMBERSK6"
       sorry
    have "g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F =HIDDENR1 the-unity-wrtBINOP-1K3\<^bsub>(D)\<^esub> g"
      using A1 A2 finsop_1_def_1 sorry
    also have "... = g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> G"
      using A1 A4 finsop_1_def_1 sorry
    finally show "g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F =HIDDENR1 g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> G"
       sorry
  qed "sorry"
  thus " ?thesis "
     sorry
qed

mtheorem finsop_1_th_7:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for F be FinSequenceFINSEQ-1M3-of D holds  for G be FinSequenceFINSEQ-1M3-of D holds  for g be BinOpBINOP-1M2-of D holds  for P be PermutationFUNCT-2M2-of domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> F holds (g be commutativeBINOP-1V1\<^bsub>(D)\<^esub>\<bar>associativeBINOP-1V2\<^bsub>(D)\<^esub> & (g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> or lenFINSEQ-1K4 F >=XXREAL-0R2 \<one>\<^sub>M)) & G =FUNCT-1R1 F *FUNCT-1K3 P implies g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F =XBOOLE-0R4 g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> G"
proof-
  have " for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for F be FinSequenceFINSEQ-1M3-of D holds  for G be FinSequenceFINSEQ-1M3-of D holds  for g be BinOpBINOP-1M2-of D holds  for P be PermutationFUNCT-2M2-of domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> F holds g be commutativeBINOP-1V1\<^bsub>(D)\<^esub>\<bar>associativeBINOP-1V2\<^bsub>(D)\<^esub> & (g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> or lenFINSEQ-1K4 F >=XXREAL-0R2 \<one>\<^sub>M) implies (G =FUNCT-1R1 F *FUNCT-1K3 P implies g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F =XBOOLE-0R4 g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> G)"
  proof(rule ballI,rule ballI,rule ballI,rule ballI,rule ballI,rule impMI ,rule impI,rule impI)
    fix D assume [ty]: "D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
    fix F assume [ty]: "F be FinSequenceFINSEQ-1M3-of D"
    fix G assume [ty]: "G be FinSequenceFINSEQ-1M3-of D"
    fix g assume [ty]: "g be BinOpBINOP-1M2-of D"
    fix P assume [ty]: "P be PermutationFUNCT-2M2-of domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> F"
    assume A1: "g be commutativeBINOP-1V1\<^bsub>(D)\<^esub>\<bar>associativeBINOP-1V2\<^bsub>(D)\<^esub>"
      and A2: "g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> or lenFINSEQ-1K4 F >=XXREAL-0R2 \<one>\<^sub>M"
    assume A3: "G =FUNCT-1R1 F *FUNCT-1K3 P"
    have "g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F =XBOOLE-0R4 g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> G"
    proof-
      show "g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F =XBOOLE-0R4 g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> G"
      proof-
        have cases: "lenFINSEQ-1K4 F =XBOOLE-0R4 0NUMBERSK6 or lenFINSEQ-1K4 F <>HIDDENR2 0NUMBERSK6"
           sorry
        have case1: "lenFINSEQ-1K4 F =XBOOLE-0R4 0NUMBERSK6 implies g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F =XBOOLE-0R4 g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> G"
        proof(rule impI)
          assume "lenFINSEQ-1K4 F =XBOOLE-0R4 0NUMBERSK6"
          thus "g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F =XBOOLE-0R4 g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> G"
            using A2 A3 finsop_1_lm_8 sorry
        qed
        have case2: "lenFINSEQ-1K4 F <>HIDDENR2 0NUMBERSK6 implies g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F =XBOOLE-0R4 g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> G"
        proof(rule impI)
          assume A4: "lenFINSEQ-1K4 F <>HIDDENR2 0NUMBERSK6"
          have "lenFINSEQ-1K4 F =XBOOLE-0R4 lenFINSEQ-1K4 G & ( for i be NatNAT-1M1 holds i inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> G implies G .FUNCT-1K1 i =XBOOLE-0R4 F .FUNCT-1K1 (P .FUNCT-1K1 i))"
            using A3 finseq_2_th_44 funct_1_th_12 sorry
          thus "g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F =XBOOLE-0R4 g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> G"
            using A1 A4 finsop_1_lm_7 nat_1_th_14 sorry
        qed
        show " ?thesis "
          using cases case1 case2 sorry
      qed
    qed
    thus "g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F =XBOOLE-0R4 g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> G"
       sorry
  qed "sorry"
  thus " ?thesis "
     sorry
qed

mlemma finsop_1_lm_9:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for F be FinSequenceFINSEQ-1M3-of D holds  for G be FinSequenceFINSEQ-1M3-of D holds  for g be BinOpBINOP-1M2-of D holds (((g be associativeBINOP-1V2\<^bsub>(D)\<^esub>\<bar>commutativeBINOP-1V1\<^bsub>(D)\<^esub> & F be one-to-oneFUNCT-1V2) & G be one-to-oneFUNCT-1V2) & rngFUNCT-1K2 F =XBOOLE-0R4 rngFUNCT-1K2 G) & lenFINSEQ-1K4 F >=XXREAL-0R2 \<one>\<^sub>M implies g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F =XBOOLE-0R4 g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> G"
proof-
  have " for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for F be FinSequenceFINSEQ-1M3-of D holds  for G be FinSequenceFINSEQ-1M3-of D holds  for g be BinOpBINOP-1M2-of D holds g be associativeBINOP-1V2\<^bsub>(D)\<^esub>\<bar>commutativeBINOP-1V1\<^bsub>(D)\<^esub> & (F be one-to-oneFUNCT-1V2 & (G be one-to-oneFUNCT-1V2 & (rngFUNCT-1K2 F =XBOOLE-0R4 rngFUNCT-1K2 G & lenFINSEQ-1K4 F >=XXREAL-0R2 \<one>\<^sub>M))) implies g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F =XBOOLE-0R4 g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> G"
  proof(rule ballI,rule ballI,rule ballI,rule ballI,rule impMI ,rule impMI ,rule impMI ,rule impMI ,rule impI)
    fix D assume [ty]: "D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
    fix F assume [ty]: "F be FinSequenceFINSEQ-1M3-of D"
    fix G assume [ty]: "G be FinSequenceFINSEQ-1M3-of D"
    fix g assume [ty]: "g be BinOpBINOP-1M2-of D"
    assume A1: "g be associativeBINOP-1V2\<^bsub>(D)\<^esub>\<bar>commutativeBINOP-1V1\<^bsub>(D)\<^esub>"
      and A2: "F be one-to-oneFUNCT-1V2"
      and A3: "G be one-to-oneFUNCT-1V2"
      and A4: "rngFUNCT-1K2 F =XBOOLE-0R4 rngFUNCT-1K2 G"
      and A5: "lenFINSEQ-1K4 F >=XXREAL-0R2 \<one>\<^sub>M"
    have A6: "lenFINSEQ-1K4 F =XBOOLE-0R4 lenFINSEQ-1K4 G"
      using A2 A3 A4 finseq_1_th_48 sorry
    let ?P = "F \<inverse>FUNCT-1K4 *FUNCT-1K3 G"
    have A7: "domRELAT-1K1 (F \<inverse>FUNCT-1K4) =XBOOLE-0R4 rngFUNCT-1K2 F"
      using A2 funct_1_th_33 sorry
    then have A8: "domRELAT-1K1 ?P =HIDDENR1 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> G"
      using A4 relat_1_th_27 sorry
    also have "... = SegFINSEQ-1K2 (lenFINSEQ-1K4 F)"
      using A6 finseq_1_def_3 sorry
    also have "... = domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> F"
      using finseq_1_def_3 sorry
    finally have "domRELAT-1K1 ?P =HIDDENR1 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> F"
       sorry
    have "rngFUNCT-1K2 (F \<inverse>FUNCT-1K4) =XBOOLE-0R4 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> F"
      using A2 funct_1_th_33 sorry
    then have A9: "rngFUNCT-1K2 ?P c=TARSKIR1 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> F"
      using relat_1_th_26 sorry
    have "domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> F =XBOOLE-0R4 SegFINSEQ-1K2 (lenFINSEQ-1K4 F)"
      using finseq_1_def_3 sorry
    then obtain P where 
      [ty]:"P be FunctionFUNCT-2M1-of(domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> F,domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> F)" and PDef:"P = ?P"
      using A5 A8 A9 funct_2_def_1 relset_1_th_4 sorry
    have "rngFUNCT-1K2 P =HIDDENR1 rngFUNCT-1K2 (F \<inverse>FUNCT-1K4)"
      using A4 A7 relat_1_th_28 sorry
    also have "... = domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> F"
      using A2 funct_1_th_33 sorry
    finally have "rngFUNCT-1K2 P =HIDDENR1 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> F"
       sorry
    then have 
      [ty]:"P be PermutationFUNCT-2M2-of domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> F"
      using A2 A3 funct_2_th_57 sorry
    have "F *FUNCT-1K3 P =HIDDENR1 (F *FUNCT-1K3 F \<inverse>FUNCT-1K4)*FUNCT-1K3 G"
      using relat_1_th_36 sorry
    also have "... = idRELAT-1K7 (rngFUNCT-1K2 G) *FUNCT-1K3 G"
      using A2 A4 funct_1_th_39 sorry
    also have "... = G"
      using relat_1_th_54 sorry
    finally have "F *FUNCT-1K3 P =HIDDENR1 G"
       sorry
    thus "g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F =XBOOLE-0R4 g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> G"
      using A1 A5 finsop_1_th_7 sorry
  qed "sorry"
  thus " ?thesis "
     sorry
qed

mlemma finsop_1_lm_10:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for F be FinSequenceFINSEQ-1M3-of D holds  for G be FinSequenceFINSEQ-1M3-of D holds  for g be BinOpBINOP-1M2-of D holds (((lenFINSEQ-1K4 F =XBOOLE-0R4 0NUMBERSK6 & g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub>) & F be one-to-oneFUNCT-1V2) & G be one-to-oneFUNCT-1V2) & rngFUNCT-1K2 F =XBOOLE-0R4 rngFUNCT-1K2 G implies g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F =XBOOLE-0R4 g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> G"
proof-
  have " for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for F be FinSequenceFINSEQ-1M3-of D holds  for G be FinSequenceFINSEQ-1M3-of D holds  for g be BinOpBINOP-1M2-of D holds (lenFINSEQ-1K4 F =XBOOLE-0R4 0NUMBERSK6 & g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub>) & ((F be one-to-oneFUNCT-1V2 & G be one-to-oneFUNCT-1V2) & rngFUNCT-1K2 F =XBOOLE-0R4 rngFUNCT-1K2 G) implies g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F =XBOOLE-0R4 g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> G"
  proof(rule ballI,rule ballI,rule ballI,rule ballI,rule impMI ,rule impI)
    fix D assume [ty]: "D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
    fix F assume [ty]: "F be FinSequenceFINSEQ-1M3-of D"
    fix G assume [ty]: "G be FinSequenceFINSEQ-1M3-of D"
    fix g assume [ty]: "g be BinOpBINOP-1M2-of D"
    assume A1: "lenFINSEQ-1K4 F =XBOOLE-0R4 0NUMBERSK6 & g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub>"
      and A2: "(F be one-to-oneFUNCT-1V2 & G be one-to-oneFUNCT-1V2) & rngFUNCT-1K2 F =XBOOLE-0R4 rngFUNCT-1K2 G"
    have "lenFINSEQ-1K4 G =XBOOLE-0R4 lenFINSEQ-1K4 F & g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F =XBOOLE-0R4 the-unity-wrtBINOP-1K3\<^bsub>(D)\<^esub> g"
      using A1 A2 finsop_1_def_1 finseq_1_th_48 sorry
    thus "g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F =XBOOLE-0R4 g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> G"
      using A1 finsop_1_def_1 sorry
  qed "sorry"
  thus " ?thesis "
     sorry
qed

mtheorem finsop_1_th_8:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for F be FinSequenceFINSEQ-1M3-of D holds  for G be FinSequenceFINSEQ-1M3-of D holds  for g be BinOpBINOP-1M2-of D holds ((((g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> or lenFINSEQ-1K4 F >=XXREAL-0R2 \<one>\<^sub>M) & g be associativeBINOP-1V2\<^bsub>(D)\<^esub>\<bar>commutativeBINOP-1V1\<^bsub>(D)\<^esub>) & F be one-to-oneFUNCT-1V2) & G be one-to-oneFUNCT-1V2) & rngFUNCT-1K2 F =XBOOLE-0R4 rngFUNCT-1K2 G implies g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F =XBOOLE-0R4 g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> G"
proof-
  have " for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for F be FinSequenceFINSEQ-1M3-of D holds  for G be FinSequenceFINSEQ-1M3-of D holds  for g be BinOpBINOP-1M2-of D holds  not (((((( not ( not g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> &  not lenFINSEQ-1K4 F >=XXREAL-0R2 \<one>\<^sub>M) & g be associativeBINOP-1V2\<^bsub>(D)\<^esub>) & g be commutativeBINOP-1V1\<^bsub>(D)\<^esub>) & F be one-to-oneFUNCT-1V2) & G be one-to-oneFUNCT-1V2) & rngFUNCT-1K2 F =XBOOLE-0R4 rngFUNCT-1K2 G) &  not g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F =XBOOLE-0R4 g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> G)"
  proof(rule ballI,rule ballI,rule ballI,rule ballI)
    fix D assume [ty]: "D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
    fix F assume [ty]: "F be FinSequenceFINSEQ-1M3-of D"
    fix G assume [ty]: "G be FinSequenceFINSEQ-1M3-of D"
    fix g assume [ty]: "g be BinOpBINOP-1M2-of D"
    have "lenFINSEQ-1K4 F >=XXREAL-0R2 \<one>\<^sub>M or lenFINSEQ-1K4 F =XBOOLE-0R4 0NUMBERSK6"
      using nat_1_th_14 sorry
    thus " not (((((( not ( not g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> &  not lenFINSEQ-1K4 F >=XXREAL-0R2 \<one>\<^sub>M) & g be associativeBINOP-1V2\<^bsub>(D)\<^esub>) & g be commutativeBINOP-1V1\<^bsub>(D)\<^esub>) & F be one-to-oneFUNCT-1V2) & G be one-to-oneFUNCT-1V2) & rngFUNCT-1K2 F =XBOOLE-0R4 rngFUNCT-1K2 G) &  not g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F =XBOOLE-0R4 g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> G)"
      using finsop_1_lm_9 finsop_1_lm_10 sorry
  qed "sorry"
  thus " ?thesis "
     sorry
qed

mlemma finsop_1_lm_11:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for F be FinSequenceFINSEQ-1M3-of D holds  for g be BinOpBINOP-1M2-of D holds lenFINSEQ-1K4 F =XBOOLE-0R4 \<one>\<^sub>M implies g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F =XBOOLE-0R4 F .FUNCT-1K1 \<one>\<^sub>M"
proof-
  have " for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for F be FinSequenceFINSEQ-1M3-of D holds  for g be BinOpBINOP-1M2-of D holds lenFINSEQ-1K4 F =XBOOLE-0R4 \<one>\<^sub>M implies g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F =HIDDENR1 F .FUNCT-1K1 \<one>\<^sub>M"
  proof(rule ballI,rule ballI,rule ballI,rule impI)
    fix D assume [ty]: "D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
    fix F assume [ty]: "F be FinSequenceFINSEQ-1M3-of D"
    fix g assume [ty]: "g be BinOpBINOP-1M2-of D"
    assume A1: "lenFINSEQ-1K4 F =XBOOLE-0R4 \<one>\<^sub>M"
    then have "F =HIDDENR1 <*FINSEQ-1K10 F .FUNCT-1K1 \<one>\<^sub>M*>"
      using finseq_1_th_40 sorry
    also have "... = <*FINSEQ-1K13\<^bsub>(D)\<^esub> F /.PARTFUN1K7\<^bsub>(D)\<^esub> \<one>\<^sub>M*>"
      using A1 finseq_4_th_15 sorry
    finally have "F =HIDDENR1 <*FINSEQ-1K13\<^bsub>(D)\<^esub> F /.PARTFUN1K7\<^bsub>(D)\<^esub> \<one>\<^sub>M*>"
       sorry
    then have "g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F =HIDDENR1 F /.PARTFUN1K7\<^bsub>(D)\<^esub> \<one>\<^sub>M"
      using finsop_1_lm_4 sorry
    also have "... = F .FUNCT-1K1 \<one>\<^sub>M"
      using A1 finseq_4_th_15 sorry
    finally show "g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F =HIDDENR1 F .FUNCT-1K1 \<one>\<^sub>M"
       sorry
  qed "sorry"
  thus " ?thesis "
     sorry
qed

mlemma finsop_1_lm_12:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for F be FinSequenceFINSEQ-1M3-of D holds  for G be FinSequenceFINSEQ-1M3-of D holds  for H be FinSequenceFINSEQ-1M3-of D holds  for g be BinOpBINOP-1M2-of D holds ((((g be associativeBINOP-1V2\<^bsub>(D)\<^esub> & g be commutativeBINOP-1V1\<^bsub>(D)\<^esub>) & lenFINSEQ-1K4 F >=XXREAL-0R2 \<one>\<^sub>M) & lenFINSEQ-1K4 F =XBOOLE-0R4 lenFINSEQ-1K4 G) & lenFINSEQ-1K4 F =XBOOLE-0R4 lenFINSEQ-1K4 H) & ( for k be NatNAT-1M1 holds k inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> F implies H .FUNCT-1K1 k =XBOOLE-0R4 g .BINOP-1K1(F .FUNCT-1K1 k,G .FUNCT-1K1 k)) implies g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> H =XBOOLE-0R4 g .BINOP-1K4\<^bsub>(D)\<^esub>(g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F,g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> G)"
proof-
  have " for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for F be FinSequenceFINSEQ-1M3-of D holds  for G be FinSequenceFINSEQ-1M3-of D holds  for H be FinSequenceFINSEQ-1M3-of D holds  for g be BinOpBINOP-1M2-of D holds g be associativeBINOP-1V2\<^bsub>(D)\<^esub> & g be commutativeBINOP-1V1\<^bsub>(D)\<^esub> implies ((lenFINSEQ-1K4 F >=XXREAL-0R2 \<one>\<^sub>M & lenFINSEQ-1K4 F =XBOOLE-0R4 lenFINSEQ-1K4 G) & lenFINSEQ-1K4 F =XBOOLE-0R4 lenFINSEQ-1K4 H implies  not (( for k be NatNAT-1M1 holds  not (k inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> F &  not H .FUNCT-1K1 k =XBOOLE-0R4 g .BINOP-1K1(F .FUNCT-1K1 k,G .FUNCT-1K1 k))) &  not g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> H =XBOOLE-0R4 g .BINOP-1K4\<^bsub>(D)\<^esub>(g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F,g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> G)))"
  proof(rule ballI,rule ballI,rule ballI,rule ballI,rule ballI,rule impMI ,rule impI,rule impI)
    fix D assume [ty]: "D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
    fix F assume [ty]: "F be FinSequenceFINSEQ-1M3-of D"
    fix G assume [ty]: "G be FinSequenceFINSEQ-1M3-of D"
    fix H assume [ty]: "H be FinSequenceFINSEQ-1M3-of D"
    fix g assume [ty]: "g be BinOpBINOP-1M2-of D"
    assume A1: "g be associativeBINOP-1V2\<^bsub>(D)\<^esub>"
      and A2: "g be commutativeBINOP-1V1\<^bsub>(D)\<^esub>"
    let ?P = "\<lambda>Lamb1.  for F be FinSequenceFINSEQ-1M3-of D holds  for G be FinSequenceFINSEQ-1M3-of D holds  for H be FinSequenceFINSEQ-1M3-of D holds (((lenFINSEQ-1K4 F >=XXREAL-0R2 \<one>\<^sub>M & lenFINSEQ-1K4 F =XBOOLE-0R4 Lamb1) & lenFINSEQ-1K4 F =XBOOLE-0R4 lenFINSEQ-1K4 G) & lenFINSEQ-1K4 F =XBOOLE-0R4 lenFINSEQ-1K4 H) & ( for n be NatNAT-1M1 holds n inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> F implies H .FUNCT-1K1 n =XBOOLE-0R4 g .BINOP-1K1(F .FUNCT-1K1 n,G .FUNCT-1K1 n)) implies g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> H =XBOOLE-0R4 g .BINOP-1K4\<^bsub>(D)\<^esub>(g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F,g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> G)"
    have A3: " for k be NatNAT-1M1 holds ( for F be FinSequenceFINSEQ-1M3-of D holds  for G be FinSequenceFINSEQ-1M3-of D holds  for H be FinSequenceFINSEQ-1M3-of D holds (((lenFINSEQ-1K4 F >=XXREAL-0R2 \<one>\<^sub>M & lenFINSEQ-1K4 F =XBOOLE-0R4 k) & lenFINSEQ-1K4 F =XBOOLE-0R4 lenFINSEQ-1K4 G) & lenFINSEQ-1K4 F =XBOOLE-0R4 lenFINSEQ-1K4 H) & ( for n be NatNAT-1M1 holds n inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> F implies H .FUNCT-1K1 n =XBOOLE-0R4 g .BINOP-1K1(F .FUNCT-1K1 n,G .FUNCT-1K1 n)) implies g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> H =XBOOLE-0R4 g .BINOP-1K4\<^bsub>(D)\<^esub>(g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F,g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> G)) implies ( for F be FinSequenceFINSEQ-1M3-of D holds  for G be FinSequenceFINSEQ-1M3-of D holds  for H be FinSequenceFINSEQ-1M3-of D holds (((lenFINSEQ-1K4 F >=XXREAL-0R2 \<one>\<^sub>M & lenFINSEQ-1K4 F =XBOOLE-0R4 k +NAT-1K1 \<one>\<^sub>M) & lenFINSEQ-1K4 F =XBOOLE-0R4 lenFINSEQ-1K4 G) & lenFINSEQ-1K4 F =XBOOLE-0R4 lenFINSEQ-1K4 H) & ( for n be NatNAT-1M1 holds n inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> F implies H .FUNCT-1K1 n =XBOOLE-0R4 g .BINOP-1K1(F .FUNCT-1K1 n,G .FUNCT-1K1 n)) implies g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> H =XBOOLE-0R4 g .BINOP-1K4\<^bsub>(D)\<^esub>(g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F,g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> G))"
    proof(rule ballI,rule impI)
      fix k assume [ty]: "k be NatNAT-1M1"
      assume A4: "?P(k)"
      show " for F be FinSequenceFINSEQ-1M3-of D holds  for G be FinSequenceFINSEQ-1M3-of D holds  for H be FinSequenceFINSEQ-1M3-of D holds (((lenFINSEQ-1K4 F >=XXREAL-0R2 \<one>\<^sub>M & lenFINSEQ-1K4 F =XBOOLE-0R4 k +NAT-1K1 \<one>\<^sub>M) & lenFINSEQ-1K4 F =XBOOLE-0R4 lenFINSEQ-1K4 G) & lenFINSEQ-1K4 F =XBOOLE-0R4 lenFINSEQ-1K4 H) & ( for n be NatNAT-1M1 holds n inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> F implies H .FUNCT-1K1 n =XBOOLE-0R4 g .BINOP-1K1(F .FUNCT-1K1 n,G .FUNCT-1K1 n)) implies g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> H =XBOOLE-0R4 g .BINOP-1K4\<^bsub>(D)\<^esub>(g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F,g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> G)"
      proof-
        have " for F be FinSequenceFINSEQ-1M3-of D holds  for G be FinSequenceFINSEQ-1M3-of D holds  for H be FinSequenceFINSEQ-1M3-of D holds lenFINSEQ-1K4 F >=XXREAL-0R2 \<one>\<^sub>M & (lenFINSEQ-1K4 F =XBOOLE-0R4 k +NAT-1K1 \<one>\<^sub>M & (lenFINSEQ-1K4 F =XBOOLE-0R4 lenFINSEQ-1K4 G & (lenFINSEQ-1K4 F =XBOOLE-0R4 lenFINSEQ-1K4 H & ( for k be NatNAT-1M1 holds k inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> F implies H .FUNCT-1K1 k =XBOOLE-0R4 g .BINOP-1K1(F .FUNCT-1K1 k,G .FUNCT-1K1 k))))) implies g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> H =XBOOLE-0R4 g .BINOP-1K4\<^bsub>(D)\<^esub>(g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F,g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> G)"
        proof(rule ballI,rule ballI,rule ballI,rule impMI ,rule impMI ,rule impMI ,rule impMI ,rule impI)
          fix F assume [ty]: "F be FinSequenceFINSEQ-1M3-of D"
          fix G assume [ty]: "G be FinSequenceFINSEQ-1M3-of D"
          fix H assume [ty]: "H be FinSequenceFINSEQ-1M3-of D"
          assume "lenFINSEQ-1K4 F >=XXREAL-0R2 \<one>\<^sub>M"
            and A5: "lenFINSEQ-1K4 F =XBOOLE-0R4 k +NAT-1K1 \<one>\<^sub>M"
            and A6: "lenFINSEQ-1K4 F =XBOOLE-0R4 lenFINSEQ-1K4 G"
            and A7: "lenFINSEQ-1K4 F =XBOOLE-0R4 lenFINSEQ-1K4 H"
            and A8: " for k be NatNAT-1M1 holds k inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> F implies H .FUNCT-1K1 k =XBOOLE-0R4 g .BINOP-1K1(F .FUNCT-1K1 k,G .FUNCT-1K1 k)"
          obtain f gg h where 
            [ty]:"f be FinSequenceFINSEQ-1M3-of D" and fDef:"f = F |RELSET-1K5\<^bsub>(NATNUMBERSK1,D)\<^esub> SegFINSEQ-1K2 k" and
            [ty]:"gg be FinSequenceFINSEQ-1M3-of D" and ggDef:"gg = G |RELSET-1K5\<^bsub>(NATNUMBERSK1,D)\<^esub> SegFINSEQ-1K2 k" and
            [ty]:"h be FinSequenceFINSEQ-1M3-of D" and hDef:"h = H |RELSET-1K5\<^bsub>(NATNUMBERSK1,D)\<^esub> SegFINSEQ-1K2 k"
            using finseq_1_th_18 sorry
          have A9: "lenFINSEQ-1K4 h =XBOOLE-0R4 k"
            using A5 A7 finseq_3_th_53 sorry
          have A10: "lenFINSEQ-1K4 f =XBOOLE-0R4 k"
            using A5 finseq_3_th_53 sorry
          have A11: "lenFINSEQ-1K4 gg =XBOOLE-0R4 k"
            using A5 A6 finseq_3_th_53 sorry
          have A12: " for i be NatNAT-1M1 holds i inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> f implies h .FUNCT-1K1 i =XBOOLE-0R4 g .BINOP-1K1(f .FUNCT-1K1 i,gg .FUNCT-1K1 i)"
          proof(rule ballI,rule impI)
            have "k <=XXREAL-0R1 k +NAT-1K1 \<one>\<^sub>M"
              using nat_1_th_12 sorry
            then have "SegFINSEQ-1K2 (lenFINSEQ-1K4 f) c=TARSKIR1 SegFINSEQ-1K2 (lenFINSEQ-1K4 F)"
              using A5 A10 finseq_1_th_5 sorry
            then have "SegFINSEQ-1K2 (lenFINSEQ-1K4 f) c=TARSKIR1 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> F"
              using finseq_1_def_3 sorry
            then have A13: "domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> f c=TARSKIR1 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> F"
              using finseq_1_def_3 sorry
            fix i assume [ty]: "i be NatNAT-1M1"
            assume A14: "i inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> f"
            then have "i inTARSKIR2 SegFINSEQ-1K2 (lenFINSEQ-1K4 gg)"
              using A10 A11 finseq_1_def_3 sorry
            then have "i inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> gg"
              using finseq_1_def_3 sorry
            then have A15: "G .FUNCT-1K1 i =XBOOLE-0R4 gg .FUNCT-1K1 i"
              using funct_1_th_47 sorry
            have "i inTARSKIR2 SegFINSEQ-1K2 (lenFINSEQ-1K4 h)"
              using A10 A9 A14 finseq_1_def_3 sorry
            then have "i inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> h"
              using finseq_1_def_3 sorry
            then have A16: "H .FUNCT-1K1 i =XBOOLE-0R4 h .FUNCT-1K1 i"
              using funct_1_th_47 sorry
            have "F .FUNCT-1K1 i =XBOOLE-0R4 f .FUNCT-1K1 i"
              using A14 funct_1_th_47 sorry
            thus "h .FUNCT-1K1 i =XBOOLE-0R4 g .BINOP-1K1(f .FUNCT-1K1 i,gg .FUNCT-1K1 i)"
              using A8 A14 A15 A16 A13 sorry
          qed "sorry"
          have "g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> H =HIDDENR1 g .BINOP-1K4\<^bsub>(D)\<^esub>(g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F,g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> G)"
          proof-
            show "g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> H =HIDDENR1 g .BINOP-1K4\<^bsub>(D)\<^esub>(g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F,g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> G)"
            proof-
              have cases: "lenFINSEQ-1K4 f >=XXREAL-0R2 \<one>\<^sub>M or lenFINSEQ-1K4 f =XBOOLE-0R4 0NUMBERSK6"
                using nat_1_th_14 sorry
              have case1: "lenFINSEQ-1K4 f >=XXREAL-0R2 \<one>\<^sub>M implies g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> H =HIDDENR1 g .BINOP-1K4\<^bsub>(D)\<^esub>(g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F,g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> G)"
              proof(rule impI)
                assume A17: "lenFINSEQ-1K4 f >=XXREAL-0R2 \<one>\<^sub>M"
                have A18: "rngFUNCT-1K2 H c=TARSKIR1 D"
                  using finseq_1_def_4 sorry
                have A19: "rngFUNCT-1K2 F c=TARSKIR1 D & rngFUNCT-1K2 G c=TARSKIR1 D"
                  using finseq_1_def_4 sorry
                have A20: "k +NAT-1K1 \<one>\<^sub>M inTARSKIR2 SegFINSEQ-1K2 (k +NAT-1K1 \<one>\<^sub>M)"
                  using finseq_1_th_4 sorry
                then have "k +NAT-1K1 \<one>\<^sub>M inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> G"
                  using A5 A6 finseq_1_def_3 sorry
                then have A21: "G .FUNCT-1K1 (k +NAT-1K1 \<one>\<^sub>M) inTARSKIR2 rngFUNCT-1K2 G"
                  using funct_1_def_3 sorry
                have "k +NAT-1K1 \<one>\<^sub>M inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> H"
                  using A5 A7 A20 finseq_1_def_3 sorry
                then have A22: "H .FUNCT-1K1 (k +NAT-1K1 \<one>\<^sub>M) inTARSKIR2 rngFUNCT-1K2 H"
                  using funct_1_def_3 sorry
                have A23: "k +NAT-1K1 \<one>\<^sub>M inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> F"
                  using A5 A20 finseq_1_def_3 sorry
                then have "F .FUNCT-1K1 (k +NAT-1K1 \<one>\<^sub>M) inTARSKIR2 rngFUNCT-1K2 F"
                  using funct_1_def_3 sorry
                then obtain d d1 d2 where 
                  [ty]:"d be ElementSUBSET-1M1-of D" and dDef:"d = F .FUNCT-1K1 (k +NAT-1K1 \<one>\<^sub>M)" and
                  [ty]:"d1 be ElementSUBSET-1M1-of D" and d1Def:"d1 = G .FUNCT-1K1 (k +NAT-1K1 \<one>\<^sub>M)" and
                  [ty]:"d2 be ElementSUBSET-1M1-of D" and d2Def:"d2 = H .FUNCT-1K1 (k +NAT-1K1 \<one>\<^sub>M)"
                  using A21 A22 A19 A18 sorry
                have A24: "d2 =XBOOLE-0R4 g .BINOP-1K1(F .FUNCT-1K1 (k +NAT-1K1 \<one>\<^sub>M),G .FUNCT-1K1 (k +NAT-1K1 \<one>\<^sub>M))"
                  using A8 A23 sorry
                have "F =FUNCT-1R1 f ^FINSEQ-1K9\<^bsub>(D)\<^esub> (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>)"
                  using A5 finseq_3_th_55 sorry
                then have A25: "g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F =XBOOLE-0R4 g .BINOP-1K4\<^bsub>(D)\<^esub>(g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> f,d)"
                  using A17 finsop_1_th_4 sorry
                have "G =FUNCT-1R1 gg ^FINSEQ-1K9\<^bsub>(D)\<^esub> (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d1*>)"
                  using A5 A6 finseq_3_th_55 sorry
                then have A26: "g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> G =XBOOLE-0R4 g .BINOP-1K4\<^bsub>(D)\<^esub>(g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> gg,d1)"
                  using A10 A11 A17 finsop_1_th_4 sorry
                have A27: "H =FUNCT-1R1 h ^FINSEQ-1K9\<^bsub>(D)\<^esub> (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d2*>)"
                  using A5 A7 finseq_3_th_55 sorry
                have "g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> h =XBOOLE-0R4 g .BINOP-1K4\<^bsub>(D)\<^esub>(g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> f,g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> gg)"
                  using A4 A10 A11 A9 A12 A17 sorry
                then have "g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> H =HIDDENR1 g .BINOP-1K4\<^bsub>(D)\<^esub>(g .BINOP-1K4\<^bsub>(D)\<^esub>(g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> f,g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> gg),g .BINOP-1K4\<^bsub>(D)\<^esub>(d,d1))"
                  using A10 A9 A17 A27 A24 finsop_1_th_4 sorry
                also have "... = g .BINOP-1K4\<^bsub>(D)\<^esub>(g .BINOP-1K4\<^bsub>(D)\<^esub>(g .BINOP-1K4\<^bsub>(D)\<^esub>(g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> f,g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> gg),d),d1)"
                  using A1 binop_1_def_3 sorry
                also have "... = g .BINOP-1K4\<^bsub>(D)\<^esub>(g .BINOP-1K4\<^bsub>(D)\<^esub>(g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> f,g .BINOP-1K4\<^bsub>(D)\<^esub>(g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> gg,d)),d1)"
                  using A1 binop_1_def_3 sorry
                also have "... = g .BINOP-1K4\<^bsub>(D)\<^esub>(g .BINOP-1K4\<^bsub>(D)\<^esub>(g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> f,g .BINOP-1K4\<^bsub>(D)\<^esub>(d,g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> gg)),d1)"
                  using A2 binop_1_def_2 sorry
                also have "... = g .BINOP-1K4\<^bsub>(D)\<^esub>(g .BINOP-1K4\<^bsub>(D)\<^esub>(g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F,g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> gg),d1)"
                  using A1 A25 binop_1_def_3 sorry
                also have "... = g .BINOP-1K4\<^bsub>(D)\<^esub>(g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F,g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> G)"
                  using A1 A26 binop_1_def_3 sorry
                finally show "g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> H =HIDDENR1 g .BINOP-1K4\<^bsub>(D)\<^esub>(g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F,g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> G)"
                   sorry
              qed
              have case2: "lenFINSEQ-1K4 f =XBOOLE-0R4 0NUMBERSK6 implies g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> H =XBOOLE-0R4 g .BINOP-1K4\<^bsub>(D)\<^esub>(g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F,g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> G)"
              proof(rule impI)
                assume A28: "lenFINSEQ-1K4 f =XBOOLE-0R4 0NUMBERSK6"
                then have A29: "g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> G =XBOOLE-0R4 G .FUNCT-1K1 \<one>\<^sub>M & \<one>\<^sub>M inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> F"
                  using A5 A6 A10 finsop_1_lm_11 finseq_3_th_25 sorry
                have "g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> H =XBOOLE-0R4 H .FUNCT-1K1 \<one>\<^sub>M & g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F =XBOOLE-0R4 F .FUNCT-1K1 \<one>\<^sub>M"
                  using A5 A7 A10 A28 finsop_1_lm_11 sorry
                thus "g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> H =XBOOLE-0R4 g .BINOP-1K4\<^bsub>(D)\<^esub>(g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F,g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> G)"
                  using A8 A29 sorry
              qed
              show " ?thesis "
                using cases case1 case2 sorry
            qed
          qed
          thus "g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> H =XBOOLE-0R4 g .BINOP-1K4\<^bsub>(D)\<^esub>(g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F,g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> G)"
             sorry
        qed "sorry"
        thus " ?thesis "
           sorry
      qed
    qed "sorry"
    assume A30: "(lenFINSEQ-1K4 F >=XXREAL-0R2 \<one>\<^sub>M & lenFINSEQ-1K4 F =XBOOLE-0R4 lenFINSEQ-1K4 G) & lenFINSEQ-1K4 F =XBOOLE-0R4 lenFINSEQ-1K4 H"
    have A31: "?P(0NUMBERSK6)"
       sorry
    have " for k be NatNAT-1M1 holds ?P(k)"
      using nat_1_sch_2 A31 A3 sorry
    thus " not (( for k be NatNAT-1M1 holds  not (k inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> F &  not H .FUNCT-1K1 k =XBOOLE-0R4 g .BINOP-1K1(F .FUNCT-1K1 k,G .FUNCT-1K1 k))) &  not g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> H =XBOOLE-0R4 g .BINOP-1K4\<^bsub>(D)\<^esub>(g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F,g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> G))"
      using A30 sorry
  qed "sorry"
  thus " ?thesis "
     sorry
qed

mlemma finsop_1_lm_13:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for F be FinSequenceFINSEQ-1M3-of D holds  for G be FinSequenceFINSEQ-1M3-of D holds  for H be FinSequenceFINSEQ-1M3-of D holds  for g be BinOpBINOP-1M2-of D holds ((g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> & lenFINSEQ-1K4 F =XBOOLE-0R4 0NUMBERSK6) & lenFINSEQ-1K4 F =XBOOLE-0R4 lenFINSEQ-1K4 G) & lenFINSEQ-1K4 F =XBOOLE-0R4 lenFINSEQ-1K4 H implies g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F =XBOOLE-0R4 g .BINOP-1K4\<^bsub>(D)\<^esub>(g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> G,g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> H)"
proof-
  have " for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for F be FinSequenceFINSEQ-1M3-of D holds  for G be FinSequenceFINSEQ-1M3-of D holds  for H be FinSequenceFINSEQ-1M3-of D holds  for g be BinOpBINOP-1M2-of D holds g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> & (lenFINSEQ-1K4 F =XBOOLE-0R4 0NUMBERSK6 & (lenFINSEQ-1K4 F =XBOOLE-0R4 lenFINSEQ-1K4 G & lenFINSEQ-1K4 F =XBOOLE-0R4 lenFINSEQ-1K4 H)) implies g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F =HIDDENR1 g .BINOP-1K4\<^bsub>(D)\<^esub>(g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> G,g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> H)"
  proof(rule ballI,rule ballI,rule ballI,rule ballI,rule ballI,rule impMI ,rule impMI ,rule impMI ,rule impI)
    fix D assume [ty]: "D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
    fix F assume [ty]: "F be FinSequenceFINSEQ-1M3-of D"
    fix G assume [ty]: "G be FinSequenceFINSEQ-1M3-of D"
    fix H assume [ty]: "H be FinSequenceFINSEQ-1M3-of D"
    fix g assume [ty]: "g be BinOpBINOP-1M2-of D"
    assume A1: "g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub>"
      and A2: "lenFINSEQ-1K4 F =XBOOLE-0R4 0NUMBERSK6"
      and A3: "lenFINSEQ-1K4 F =XBOOLE-0R4 lenFINSEQ-1K4 G"
      and A4: "lenFINSEQ-1K4 F =XBOOLE-0R4 lenFINSEQ-1K4 H"
    have "g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F =HIDDENR1 the-unity-wrtBINOP-1K3\<^bsub>(D)\<^esub> g"
      using A1 A2 finsop_1_def_1 sorry
    also have "... = g .BINOP-1K4\<^bsub>(D)\<^esub>(the-unity-wrtBINOP-1K3\<^bsub>(D)\<^esub> g,the-unity-wrtBINOP-1K3\<^bsub>(D)\<^esub> g)"
      using A1 setwiseo_th_15 sorry
    also have "... = g .BINOP-1K4\<^bsub>(D)\<^esub>(g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> G,the-unity-wrtBINOP-1K3\<^bsub>(D)\<^esub> g)"
      using A1 A2 A3 finsop_1_def_1 sorry
    also have "... = g .BINOP-1K4\<^bsub>(D)\<^esub>(g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> G,g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> H)"
      using A1 A2 A4 finsop_1_def_1 sorry
    finally show "g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F =HIDDENR1 g .BINOP-1K4\<^bsub>(D)\<^esub>(g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> G,g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> H)"
       sorry
  qed "sorry"
  thus " ?thesis "
     sorry
qed

mtheorem finsop_1_th_9:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for F be FinSequenceFINSEQ-1M3-of D holds  for G be FinSequenceFINSEQ-1M3-of D holds  for H be FinSequenceFINSEQ-1M3-of D holds  for g be BinOpBINOP-1M2-of D holds (((g be associativeBINOP-1V2\<^bsub>(D)\<^esub>\<bar>commutativeBINOP-1V1\<^bsub>(D)\<^esub> & (g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> or lenFINSEQ-1K4 F >=XXREAL-0R2 \<one>\<^sub>M)) & lenFINSEQ-1K4 F =XBOOLE-0R4 lenFINSEQ-1K4 G) & lenFINSEQ-1K4 F =XBOOLE-0R4 lenFINSEQ-1K4 H) & ( for k be NatNAT-1M1 holds k inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> F implies F .FUNCT-1K1 k =XBOOLE-0R4 g .BINOP-1K1(G .FUNCT-1K1 k,H .FUNCT-1K1 k)) implies g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F =XBOOLE-0R4 g .BINOP-1K4\<^bsub>(D)\<^esub>(g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> G,g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> H)"
proof-
  have " for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for F be FinSequenceFINSEQ-1M3-of D holds  for G be FinSequenceFINSEQ-1M3-of D holds  for H be FinSequenceFINSEQ-1M3-of D holds  for g be BinOpBINOP-1M2-of D holds g be associativeBINOP-1V2\<^bsub>(D)\<^esub>\<bar>commutativeBINOP-1V1\<^bsub>(D)\<^esub> & (g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> or lenFINSEQ-1K4 F >=XXREAL-0R2 \<one>\<^sub>M) implies  not (((lenFINSEQ-1K4 F =XBOOLE-0R4 lenFINSEQ-1K4 G & lenFINSEQ-1K4 F =XBOOLE-0R4 lenFINSEQ-1K4 H) & ( for k be NatNAT-1M1 holds  not (k inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> F &  not F .FUNCT-1K1 k =XBOOLE-0R4 g .BINOP-1K1(G .FUNCT-1K1 k,H .FUNCT-1K1 k)))) &  not g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F =XBOOLE-0R4 g .BINOP-1K4\<^bsub>(D)\<^esub>(g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> G,g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> H))"
  proof(rule ballI,rule ballI,rule ballI,rule ballI,rule ballI,rule impI)
    fix D assume [ty]: "D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
    fix F assume [ty]: "F be FinSequenceFINSEQ-1M3-of D"
    fix G assume [ty]: "G be FinSequenceFINSEQ-1M3-of D"
    fix H assume [ty]: "H be FinSequenceFINSEQ-1M3-of D"
    fix g assume [ty]: "g be BinOpBINOP-1M2-of D"
    have A1: "domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> F =XBOOLE-0R4 SegFINSEQ-1K2 (lenFINSEQ-1K4 F) & domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> G =XBOOLE-0R4 SegFINSEQ-1K2 (lenFINSEQ-1K4 G)"
      using finseq_1_def_3 sorry
    have A2: "lenFINSEQ-1K4 F =XBOOLE-0R4 0NUMBERSK6 or lenFINSEQ-1K4 F >=XXREAL-0R2 \<one>\<^sub>M"
      using nat_1_th_14 sorry
    assume "g be associativeBINOP-1V2\<^bsub>(D)\<^esub>\<bar>commutativeBINOP-1V1\<^bsub>(D)\<^esub> & (g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> or lenFINSEQ-1K4 F >=XXREAL-0R2 \<one>\<^sub>M)"
    thus " not (((lenFINSEQ-1K4 F =XBOOLE-0R4 lenFINSEQ-1K4 G & lenFINSEQ-1K4 F =XBOOLE-0R4 lenFINSEQ-1K4 H) & ( for k be NatNAT-1M1 holds  not (k inTARSKIR2 domRELSET-1K1\<^bsub>(NATNUMBERSK1)\<^esub> F &  not F .FUNCT-1K1 k =XBOOLE-0R4 g .BINOP-1K1(G .FUNCT-1K1 k,H .FUNCT-1K1 k)))) &  not g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F =XBOOLE-0R4 g .BINOP-1K4\<^bsub>(D)\<^esub>(g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> G,g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> H))"
      using A1 A2 finsop_1_lm_12 finsop_1_lm_13 sorry
  qed "sorry"
  thus " ?thesis "
     sorry
qed

mtheorem finsop_1_th_10:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for g be BinOpBINOP-1M2-of D holds g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> implies g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> <*>FINSEQ-1K7 D =XBOOLE-0R4 the-unity-wrtBINOP-1K3\<^bsub>(D)\<^esub> g"
  using finsop_1_lm_3 sorry

mtheorem finsop_1_th_11:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d be ElementSUBSET-1M1-of D holds  for g be BinOpBINOP-1M2-of D holds g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> <*FINSEQ-1K13\<^bsub>(D)\<^esub> d*> =XBOOLE-0R4 d"
  using finsop_1_lm_4 sorry

mtheorem finsop_1_th_12:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d1 be ElementSUBSET-1M1-of D holds  for d2 be ElementSUBSET-1M1-of D holds  for g be BinOpBINOP-1M2-of D holds g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> <*FINSEQ-4K2\<^bsub>(D)\<^esub> d1,d2 *> =XBOOLE-0R4 g .BINOP-1K4\<^bsub>(D)\<^esub>(d1,d2)"
proof-
  have " for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d1 be ElementSUBSET-1M1-of D holds  for d2 be ElementSUBSET-1M1-of D holds  for g be BinOpBINOP-1M2-of D holds g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> <*FINSEQ-4K2\<^bsub>(D)\<^esub> d1,d2 *> =HIDDENR1 g .BINOP-1K4\<^bsub>(D)\<^esub>(d1,d2)"
  proof(rule ballI,rule ballI,rule ballI,rule ballI)
    fix D assume [ty]: "D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
    fix d1 assume [ty]: "d1 be ElementSUBSET-1M1-of D"
    fix d2 assume [ty]: "d2 be ElementSUBSET-1M1-of D"
    fix g assume [ty]: "g be BinOpBINOP-1M2-of D"
    have A1: "lenFINSEQ-1K4 (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d1*>) =XBOOLE-0R4 \<one>\<^sub>M"
      using finseq_1_th_39 sorry
    have "g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> <*FINSEQ-4K2\<^bsub>(D)\<^esub> d1,d2 *> =HIDDENR1 g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d1*>)^FINSEQ-1K9\<^bsub>(D)\<^esub> (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d2*>)"
      using finseq_1_def_9 sorry
    also have "... = g .BINOP-1K4\<^bsub>(D)\<^esub>(g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> <*FINSEQ-1K13\<^bsub>(D)\<^esub> d1*>,d2)"
      using A1 finsop_1_th_4 sorry
    also have "... = g .BINOP-1K4\<^bsub>(D)\<^esub>(d1,d2)"
      using finsop_1_lm_4 sorry
    finally show "g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> <*FINSEQ-4K2\<^bsub>(D)\<^esub> d1,d2 *> =HIDDENR1 g .BINOP-1K4\<^bsub>(D)\<^esub>(d1,d2)"
       sorry
  qed "sorry"
  thus " ?thesis "
     sorry
qed

mtheorem finsop_1_th_13:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d1 be ElementSUBSET-1M1-of D holds  for d2 be ElementSUBSET-1M1-of D holds  for g be BinOpBINOP-1M2-of D holds g be commutativeBINOP-1V1\<^bsub>(D)\<^esub> implies g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> <*FINSEQ-4K2\<^bsub>(D)\<^esub> d1,d2 *> =XBOOLE-0R4 g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> <*FINSEQ-4K2\<^bsub>(D)\<^esub> d2,d1 *>"
proof-
  have " for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d1 be ElementSUBSET-1M1-of D holds  for d2 be ElementSUBSET-1M1-of D holds  for g be BinOpBINOP-1M2-of D holds g be commutativeBINOP-1V1\<^bsub>(D)\<^esub> implies g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> <*FINSEQ-4K2\<^bsub>(D)\<^esub> d1,d2 *> =HIDDENR1 g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> <*FINSEQ-4K2\<^bsub>(D)\<^esub> d2,d1 *>"
  proof(rule ballI,rule ballI,rule ballI,rule ballI,rule impI)
    fix D assume [ty]: "D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
    fix d1 assume [ty]: "d1 be ElementSUBSET-1M1-of D"
    fix d2 assume [ty]: "d2 be ElementSUBSET-1M1-of D"
    fix g assume [ty]: "g be BinOpBINOP-1M2-of D"
    assume A1: "g be commutativeBINOP-1V1\<^bsub>(D)\<^esub>"
    have "g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> <*FINSEQ-4K2\<^bsub>(D)\<^esub> d1,d2 *> =HIDDENR1 g .BINOP-1K4\<^bsub>(D)\<^esub>(d1,d2)"
      using finsop_1_th_12 sorry
    also have "... = g .BINOP-1K4\<^bsub>(D)\<^esub>(d2,d1)"
      using A1 binop_1_def_2 sorry
    also have "... = g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> <*FINSEQ-4K2\<^bsub>(D)\<^esub> d2,d1 *>"
      using finsop_1_th_12 sorry
    finally show "g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> <*FINSEQ-4K2\<^bsub>(D)\<^esub> d1,d2 *> =HIDDENR1 g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> <*FINSEQ-4K2\<^bsub>(D)\<^esub> d2,d1 *>"
       sorry
  qed "sorry"
  thus " ?thesis "
     sorry
qed

mtheorem finsop_1_th_14:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d1 be ElementSUBSET-1M1-of D holds  for d2 be ElementSUBSET-1M1-of D holds  for d3 be ElementSUBSET-1M1-of D holds  for g be BinOpBINOP-1M2-of D holds g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> <*FINSEQ-4K3\<^bsub>(D)\<^esub> d1,d2,d3 *> =XBOOLE-0R4 g .BINOP-1K4\<^bsub>(D)\<^esub>(g .BINOP-1K4\<^bsub>(D)\<^esub>(d1,d2),d3)"
proof-
  have " for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d1 be ElementSUBSET-1M1-of D holds  for d2 be ElementSUBSET-1M1-of D holds  for d3 be ElementSUBSET-1M1-of D holds  for g be BinOpBINOP-1M2-of D holds g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> <*FINSEQ-4K3\<^bsub>(D)\<^esub> d1,d2,d3 *> =HIDDENR1 g .BINOP-1K4\<^bsub>(D)\<^esub>(g .BINOP-1K4\<^bsub>(D)\<^esub>(d1,d2),d3)"
  proof(rule ballI,rule ballI,rule ballI,rule ballI,rule ballI)
    fix D assume [ty]: "D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
    fix d1 assume [ty]: "d1 be ElementSUBSET-1M1-of D"
    fix d2 assume [ty]: "d2 be ElementSUBSET-1M1-of D"
    fix d3 assume [ty]: "d3 be ElementSUBSET-1M1-of D"
    fix g assume [ty]: "g be BinOpBINOP-1M2-of D"
    have A1: "lenFINSEQ-1K4 (<*FINSEQ-4K2\<^bsub>(D)\<^esub> d1,d2 *>) =XBOOLE-0R4 \<two>\<^sub>M"
      using finseq_1_th_44 sorry
    have "g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> <*FINSEQ-4K3\<^bsub>(D)\<^esub> d1,d2,d3 *> =HIDDENR1 g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> (<*FINSEQ-4K2\<^bsub>(D)\<^esub> d1,d2 *>)^FINSEQ-1K9\<^bsub>(D)\<^esub> (<*FINSEQ-1K13\<^bsub>(D)\<^esub> d3*>)"
      using finseq_1_th_43 sorry
    also have "... = g .BINOP-1K4\<^bsub>(D)\<^esub>(g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> <*FINSEQ-4K2\<^bsub>(D)\<^esub> d1,d2 *>,d3)"
      using A1 finsop_1_th_4 sorry
    also have "... = g .BINOP-1K4\<^bsub>(D)\<^esub>(g .BINOP-1K4\<^bsub>(D)\<^esub>(d1,d2),d3)"
      using finsop_1_th_12 sorry
    finally show "g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> <*FINSEQ-4K3\<^bsub>(D)\<^esub> d1,d2,d3 *> =HIDDENR1 g .BINOP-1K4\<^bsub>(D)\<^esub>(g .BINOP-1K4\<^bsub>(D)\<^esub>(d1,d2),d3)"
       sorry
  qed "sorry"
  thus " ?thesis "
     sorry
qed

mtheorem finsop_1_th_15:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d1 be ElementSUBSET-1M1-of D holds  for d2 be ElementSUBSET-1M1-of D holds  for d3 be ElementSUBSET-1M1-of D holds  for g be BinOpBINOP-1M2-of D holds g be commutativeBINOP-1V1\<^bsub>(D)\<^esub> implies g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> <*FINSEQ-4K3\<^bsub>(D)\<^esub> d1,d2,d3 *> =XBOOLE-0R4 g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> <*FINSEQ-4K3\<^bsub>(D)\<^esub> d2,d1,d3 *>"
proof-
  have " for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d1 be ElementSUBSET-1M1-of D holds  for d2 be ElementSUBSET-1M1-of D holds  for d3 be ElementSUBSET-1M1-of D holds  for g be BinOpBINOP-1M2-of D holds g be commutativeBINOP-1V1\<^bsub>(D)\<^esub> implies g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> <*FINSEQ-4K3\<^bsub>(D)\<^esub> d1,d2,d3 *> =HIDDENR1 g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> <*FINSEQ-4K3\<^bsub>(D)\<^esub> d2,d1,d3 *>"
  proof(rule ballI,rule ballI,rule ballI,rule ballI,rule ballI,rule impI)
    fix D assume [ty]: "D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
    fix d1 assume [ty]: "d1 be ElementSUBSET-1M1-of D"
    fix d2 assume [ty]: "d2 be ElementSUBSET-1M1-of D"
    fix d3 assume [ty]: "d3 be ElementSUBSET-1M1-of D"
    fix g assume [ty]: "g be BinOpBINOP-1M2-of D"
    assume A1: "g be commutativeBINOP-1V1\<^bsub>(D)\<^esub>"
    have "g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> <*FINSEQ-4K3\<^bsub>(D)\<^esub> d1,d2,d3 *> =HIDDENR1 g .BINOP-1K4\<^bsub>(D)\<^esub>(g .BINOP-1K4\<^bsub>(D)\<^esub>(d1,d2),d3)"
      using finsop_1_th_14 sorry
    also have "... = g .BINOP-1K4\<^bsub>(D)\<^esub>(g .BINOP-1K4\<^bsub>(D)\<^esub>(d2,d1),d3)"
      using A1 binop_1_def_2 sorry
    also have "... = g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> <*FINSEQ-4K3\<^bsub>(D)\<^esub> d2,d1,d3 *>"
      using finsop_1_th_14 sorry
    finally show "g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> <*FINSEQ-4K3\<^bsub>(D)\<^esub> d1,d2,d3 *> =HIDDENR1 g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> <*FINSEQ-4K3\<^bsub>(D)\<^esub> d2,d1,d3 *>"
       sorry
  qed "sorry"
  thus " ?thesis "
     sorry
qed

mtheorem finsop_1_th_16:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d be ElementSUBSET-1M1-of D holds  for g be BinOpBINOP-1M2-of D holds g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> \<one>\<^sub>M |->FINSEQ-2K5\<^bsub>(D)\<^esub> d =XBOOLE-0R4 d"
proof-
  have " for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d be ElementSUBSET-1M1-of D holds  for g be BinOpBINOP-1M2-of D holds g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> \<one>\<^sub>M |->FINSEQ-2K5\<^bsub>(D)\<^esub> d =HIDDENR1 d"
  proof(rule ballI,rule ballI,rule ballI)
    fix D assume [ty]: "D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
    fix d assume [ty]: "d be ElementSUBSET-1M1-of D"
    fix g assume [ty]: "g be BinOpBINOP-1M2-of D"
    have "g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> \<one>\<^sub>M |->FINSEQ-2K5\<^bsub>(D)\<^esub> d =HIDDENR1 g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> <*FINSEQ-1K13\<^bsub>(D)\<^esub> d*>"
      using finseq_2_th_59 sorry
    also have "... = d"
      using finsop_1_lm_4 sorry
    finally show "g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> \<one>\<^sub>M |->FINSEQ-2K5\<^bsub>(D)\<^esub> d =HIDDENR1 d"
       sorry
  qed "sorry"
  thus " ?thesis "
     sorry
qed

mtheorem finsop_1_th_17:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d be ElementSUBSET-1M1-of D holds  for g be BinOpBINOP-1M2-of D holds g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> \<two>\<^sub>M |->FINSEQ-2K5\<^bsub>(D)\<^esub> d =XBOOLE-0R4 g .BINOP-1K4\<^bsub>(D)\<^esub>(d,d)"
proof-
  have " for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d be ElementSUBSET-1M1-of D holds  for g be BinOpBINOP-1M2-of D holds g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> \<two>\<^sub>M |->FINSEQ-2K5\<^bsub>(D)\<^esub> d =HIDDENR1 g .BINOP-1K4\<^bsub>(D)\<^esub>(d,d)"
  proof(rule ballI,rule ballI,rule ballI)
    fix D assume [ty]: "D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
    fix d assume [ty]: "d be ElementSUBSET-1M1-of D"
    fix g assume [ty]: "g be BinOpBINOP-1M2-of D"
    have "g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> \<two>\<^sub>M |->FINSEQ-2K5\<^bsub>(D)\<^esub> d =HIDDENR1 g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> <*FINSEQ-4K2\<^bsub>(D)\<^esub> d,d *>"
      using finseq_2_th_61 sorry
    also have "... = g .BINOP-1K4\<^bsub>(D)\<^esub>(d,d)"
      using finsop_1_th_12 sorry
    finally show "g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> \<two>\<^sub>M |->FINSEQ-2K5\<^bsub>(D)\<^esub> d =HIDDENR1 g .BINOP-1K4\<^bsub>(D)\<^esub>(d,d)"
       sorry
  qed "sorry"
  thus " ?thesis "
     sorry
qed

mtheorem finsop_1_th_18:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d be ElementSUBSET-1M1-of D holds  for g be BinOpBINOP-1M2-of D holds  for k be NatNAT-1M1 holds  for l be NatNAT-1M1 holds g be associativeBINOP-1V2\<^bsub>(D)\<^esub> & (g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> or k <>HIDDENR2 0NUMBERSK6 & l <>HIDDENR2 0NUMBERSK6) implies g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> (k +XCMPLX-0K2 l)|->FINSEQ-2K5\<^bsub>(D)\<^esub> d =XBOOLE-0R4 g .BINOP-1K4\<^bsub>(D)\<^esub>(g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> k |->FINSEQ-2K5\<^bsub>(D)\<^esub> d,g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> l |->FINSEQ-2K5\<^bsub>(D)\<^esub> d)"
proof-
  have " for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d be ElementSUBSET-1M1-of D holds  for g be BinOpBINOP-1M2-of D holds  for k be NatNAT-1M1 holds  for l be NatNAT-1M1 holds  not ((g be associativeBINOP-1V2\<^bsub>(D)\<^esub> &  not ( not g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> &  not ( not k <>HIDDENR2 0NUMBERSK6 &  not l <>HIDDENR2 0NUMBERSK6))) &  not g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> (k +XCMPLX-0K2 l)|->FINSEQ-2K5\<^bsub>(D)\<^esub> d =XBOOLE-0R4 g .BINOP-1K4\<^bsub>(D)\<^esub>(g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> k |->FINSEQ-2K5\<^bsub>(D)\<^esub> d,g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> l |->FINSEQ-2K5\<^bsub>(D)\<^esub> d))"
  proof(rule ballI,rule ballI,rule ballI,rule ballI,rule ballI)
    fix D assume [ty]: "D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
    fix d assume [ty]: "d be ElementSUBSET-1M1-of D"
    fix g assume [ty]: "g be BinOpBINOP-1M2-of D"
    fix k assume [ty]: "k be NatNAT-1M1"
    fix l assume [ty]: "l be NatNAT-1M1"
    have A1: "k <>HIDDENR2 0NUMBERSK6 & l <>HIDDENR2 0NUMBERSK6 implies lenFINSEQ-1K4 (k |->FINSEQ-2K5\<^bsub>(D)\<^esub> d) >=XXREAL-0R2 \<one>\<^sub>M & lenFINSEQ-1K4 (l |->FINSEQ-2K5\<^bsub>(D)\<^esub> d) >=XXREAL-0R2 \<one>\<^sub>M"
      using nat_1_th_14 sorry
    have "(k +XCMPLX-0K2 l)|->FINSEQ-2K5\<^bsub>(D)\<^esub> d =FUNCT-1R1 (k |->FINSEQ-2K5\<^bsub>(D)\<^esub> d)^FINSEQ-1K9\<^bsub>(D)\<^esub> (l |->FINSEQ-2K5\<^bsub>(D)\<^esub> d)"
      using finseq_2_th_123 sorry
    thus " not ((g be associativeBINOP-1V2\<^bsub>(D)\<^esub> &  not ( not g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> &  not ( not k <>HIDDENR2 0NUMBERSK6 &  not l <>HIDDENR2 0NUMBERSK6))) &  not g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> (k +XCMPLX-0K2 l)|->FINSEQ-2K5\<^bsub>(D)\<^esub> d =XBOOLE-0R4 g .BINOP-1K4\<^bsub>(D)\<^esub>(g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> k |->FINSEQ-2K5\<^bsub>(D)\<^esub> d,g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> l |->FINSEQ-2K5\<^bsub>(D)\<^esub> d))"
      using A1 finsop_1_th_5 sorry
  qed "sorry"
  thus " ?thesis "
     sorry
qed

mtheorem finsop_1_th_19:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d be ElementSUBSET-1M1-of D holds  for g be BinOpBINOP-1M2-of D holds  for k be NatNAT-1M1 holds  for l be NatNAT-1M1 holds g be associativeBINOP-1V2\<^bsub>(D)\<^esub> & (g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> or k <>HIDDENR2 0NUMBERSK6 & l <>HIDDENR2 0NUMBERSK6) implies g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> (k *XCMPLX-0K3 l)|->FINSEQ-2K5\<^bsub>(D)\<^esub> d =XBOOLE-0R4 g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> l |->FINSEQ-2K5\<^bsub>(D)\<^esub> (g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> k |->FINSEQ-2K5\<^bsub>(D)\<^esub> d)"
proof-
  have " for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for d be ElementSUBSET-1M1-of D holds  for g be BinOpBINOP-1M2-of D holds  for k be NatNAT-1M1 holds  for l be NatNAT-1M1 holds  not ((g be associativeBINOP-1V2\<^bsub>(D)\<^esub> &  not ( not g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> &  not ( not k <>HIDDENR2 0NUMBERSK6 &  not l <>HIDDENR2 0NUMBERSK6))) &  not g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> (k *XCMPLX-0K3 l)|->FINSEQ-2K5\<^bsub>(D)\<^esub> d =XBOOLE-0R4 g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> l |->FINSEQ-2K5\<^bsub>(D)\<^esub> (g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> k |->FINSEQ-2K5\<^bsub>(D)\<^esub> d))"
  proof(rule ballI,rule ballI,rule ballI,rule ballI,rule ballI)
    fix D assume [ty]: "D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
    fix d assume [ty]: "d be ElementSUBSET-1M1-of D"
    fix g assume [ty]: "g be BinOpBINOP-1M2-of D"
    fix k assume [ty]: "k be NatNAT-1M1"
    fix l assume [ty]: "l be NatNAT-1M1"
    let ?P = "\<lambda>Lamb1.  for g be BinOpBINOP-1M2-of D holds  for k be NatNAT-1M1 holds  for d be ElementSUBSET-1M1-of D holds g be associativeBINOP-1V2\<^bsub>(D)\<^esub> & (g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> or k <>HIDDENR2 0NUMBERSK6 & Lamb1 <>HIDDENR2 0NUMBERSK6) implies g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> (k *XCMPLX-0K3 Lamb1)|->FINSEQ-2K5\<^bsub>(D)\<^esub> d =XBOOLE-0R4 g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> Lamb1 |->FINSEQ-2K5\<^bsub>(D)\<^esub> (g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> k |->FINSEQ-2K5\<^bsub>(D)\<^esub> d)"
    have A1: " for l be NatNAT-1M1 holds ?P(l) implies ?P(l +NAT-1K1 \<one>\<^sub>M)"
    proof-
      have " for l be NatNAT-1M1 holds ( for g be BinOpBINOP-1M2-of D holds  for k be NatNAT-1M1 holds  for d be ElementSUBSET-1M1-of D holds g be associativeBINOP-1V2\<^bsub>(D)\<^esub> & (g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> or k <>HIDDENR2 0NUMBERSK6 & l <>HIDDENR2 0NUMBERSK6) implies g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> (k *XCMPLX-0K3 l)|->FINSEQ-2K5\<^bsub>(D)\<^esub> d =XBOOLE-0R4 g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> l |->FINSEQ-2K5\<^bsub>(D)\<^esub> (g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> k |->FINSEQ-2K5\<^bsub>(D)\<^esub> d)) implies ( for g be BinOpBINOP-1M2-of D holds  for k be NatNAT-1M1 holds  for d be ElementSUBSET-1M1-of D holds g be associativeBINOP-1V2\<^bsub>(D)\<^esub> & (g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> or k <>HIDDENR2 0NUMBERSK6 & l +NAT-1K1 \<one>\<^sub>M <>HIDDENR2 0NUMBERSK6) implies g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> (k *XCMPLX-0K3 (l +NAT-1K1 \<one>\<^sub>M))|->FINSEQ-2K5\<^bsub>(D)\<^esub> d =XBOOLE-0R4 g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> (l +NAT-1K1 \<one>\<^sub>M)|->FINSEQ-2K5\<^bsub>(D)\<^esub> (g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> k |->FINSEQ-2K5\<^bsub>(D)\<^esub> d))"
      proof(rule ballI,rule impI,rule ballI,rule ballI,rule ballI,rule impMI ,rule impI)
        fix l assume [ty]: "l be NatNAT-1M1"
        assume A2: "?P(l)"
        fix g assume [ty]: "g be BinOpBINOP-1M2-of D"
        fix k assume [ty]: "k be NatNAT-1M1"
        fix d assume [ty]: "d be ElementSUBSET-1M1-of D"
        assume A3: "g be associativeBINOP-1V2\<^bsub>(D)\<^esub>"
          and A4: "g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> or k <>HIDDENR2 0NUMBERSK6 & l +NAT-1K1 \<one>\<^sub>M <>HIDDENR2 0NUMBERSK6"
        have "g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> (k *XCMPLX-0K3 (l +NAT-1K1 \<one>\<^sub>M))|->FINSEQ-2K5\<^bsub>(D)\<^esub> d =XBOOLE-0R4 g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> (l +NAT-1K1 \<one>\<^sub>M)|->FINSEQ-2K5\<^bsub>(D)\<^esub> (g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> k |->FINSEQ-2K5\<^bsub>(D)\<^esub> d)"
        proof-
          show "g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> (k *XCMPLX-0K3 (l +NAT-1K1 \<one>\<^sub>M))|->FINSEQ-2K5\<^bsub>(D)\<^esub> d =XBOOLE-0R4 g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> (l +NAT-1K1 \<one>\<^sub>M)|->FINSEQ-2K5\<^bsub>(D)\<^esub> (g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> k |->FINSEQ-2K5\<^bsub>(D)\<^esub> d)"
          proof-
            have cases: "l =XBOOLE-0R4 0NUMBERSK6 or l <>HIDDENR2 0NUMBERSK6"
               sorry
            have case1: "l =XBOOLE-0R4 0NUMBERSK6 implies g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> (k *XCMPLX-0K3 (l +NAT-1K1 \<one>\<^sub>M))|->FINSEQ-2K5\<^bsub>(D)\<^esub> d =XBOOLE-0R4 g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> (l +NAT-1K1 \<one>\<^sub>M)|->FINSEQ-2K5\<^bsub>(D)\<^esub> (g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> k |->FINSEQ-2K5\<^bsub>(D)\<^esub> d)"
            proof(rule impI)
              assume "l =XBOOLE-0R4 0NUMBERSK6"
              thus "g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> (k *XCMPLX-0K3 (l +NAT-1K1 \<one>\<^sub>M))|->FINSEQ-2K5\<^bsub>(D)\<^esub> d =XBOOLE-0R4 g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> (l +NAT-1K1 \<one>\<^sub>M)|->FINSEQ-2K5\<^bsub>(D)\<^esub> (g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> k |->FINSEQ-2K5\<^bsub>(D)\<^esub> d)"
                using finsop_1_th_16 sorry
            qed
            have case2: "l <>HIDDENR2 0NUMBERSK6 implies g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> (k *XCMPLX-0K3 (l +NAT-1K1 \<one>\<^sub>M))|->FINSEQ-2K5\<^bsub>(D)\<^esub> d =XBOOLE-0R4 g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> (l +NAT-1K1 \<one>\<^sub>M)|->FINSEQ-2K5\<^bsub>(D)\<^esub> (g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> k |->FINSEQ-2K5\<^bsub>(D)\<^esub> d)"
            proof(rule impI)
              assume A5: "l <>HIDDENR2 0NUMBERSK6"
              then have A6: "k <>HIDDENR2 0NUMBERSK6 implies k *XCMPLX-0K3 l <>HIDDENR2 0NUMBERSK6"
                using xcmplx_1_th_6 sorry
              have "g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> (k *XCMPLX-0K3 (l +NAT-1K1 \<one>\<^sub>M))|->FINSEQ-2K5\<^bsub>(D)\<^esub> d =HIDDENR1 g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> (k *XCMPLX-0K3 l +XCMPLX-0K2 k *XCMPLX-0K3 \<one>\<^sub>M)|->FINSEQ-2K5\<^bsub>(D)\<^esub> d"
                 sorry
              also have "... = g .BINOP-1K4\<^bsub>(D)\<^esub>(g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> (k *XCMPLX-0K3 l)|->FINSEQ-2K5\<^bsub>(D)\<^esub> d,g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> k |->FINSEQ-2K5\<^bsub>(D)\<^esub> d)"
                using A3 A4 A6 finsop_1_th_18 sorry
              also have "... = g .BINOP-1K4\<^bsub>(D)\<^esub>(g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> l |->FINSEQ-2K5\<^bsub>(D)\<^esub> (g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> k |->FINSEQ-2K5\<^bsub>(D)\<^esub> d),g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> k |->FINSEQ-2K5\<^bsub>(D)\<^esub> d)"
                using A2 A3 A4 A5 sorry
              also have "... = g .BINOP-1K4\<^bsub>(D)\<^esub>(g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> l |->FINSEQ-2K5\<^bsub>(D)\<^esub> (g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> k |->FINSEQ-2K5\<^bsub>(D)\<^esub> d),g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> \<one>\<^sub>M |->FINSEQ-2K5\<^bsub>(D)\<^esub> (g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> k |->FINSEQ-2K5\<^bsub>(D)\<^esub> d))"
                using finsop_1_th_16 sorry
              finally have "g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> (k *XCMPLX-0K3 (l +NAT-1K1 \<one>\<^sub>M))|->FINSEQ-2K5\<^bsub>(D)\<^esub> d =HIDDENR1 g .BINOP-1K4\<^bsub>(D)\<^esub>(g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> l |->FINSEQ-2K5\<^bsub>(D)\<^esub> (g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> k |->FINSEQ-2K5\<^bsub>(D)\<^esub> d),g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> \<one>\<^sub>M |->FINSEQ-2K5\<^bsub>(D)\<^esub> (g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> k |->FINSEQ-2K5\<^bsub>(D)\<^esub> d))"
                 sorry
              thus "g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> (k *XCMPLX-0K3 (l +NAT-1K1 \<one>\<^sub>M))|->FINSEQ-2K5\<^bsub>(D)\<^esub> d =XBOOLE-0R4 g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> (l +NAT-1K1 \<one>\<^sub>M)|->FINSEQ-2K5\<^bsub>(D)\<^esub> (g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> k |->FINSEQ-2K5\<^bsub>(D)\<^esub> d)"
                using A3 A5 finsop_1_th_18 sorry
            qed
            show " ?thesis "
              using cases case1 case2 sorry
          qed
        qed
        thus "g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> (k *XCMPLX-0K3 (l +NAT-1K1 \<one>\<^sub>M))|->FINSEQ-2K5\<^bsub>(D)\<^esub> d =XBOOLE-0R4 g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> (l +NAT-1K1 \<one>\<^sub>M)|->FINSEQ-2K5\<^bsub>(D)\<^esub> (g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> k |->FINSEQ-2K5\<^bsub>(D)\<^esub> d)"
           sorry
      qed "sorry"
      thus " ?thesis "
         sorry
    qed
    have A7: "?P(0NUMBERSK6)"
       sorry
    have " for l be NatNAT-1M1 holds ?P(l)"
      using nat_1_sch_2 A7 A1 sorry
    thus " not ((g be associativeBINOP-1V2\<^bsub>(D)\<^esub> &  not ( not g be having-a-unitySETWISEOV1\<^bsub>(D)\<^esub> &  not ( not k <>HIDDENR2 0NUMBERSK6 &  not l <>HIDDENR2 0NUMBERSK6))) &  not g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> (k *XCMPLX-0K3 l)|->FINSEQ-2K5\<^bsub>(D)\<^esub> d =XBOOLE-0R4 g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> l |->FINSEQ-2K5\<^bsub>(D)\<^esub> (g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> k |->FINSEQ-2K5\<^bsub>(D)\<^esub> d))"
       sorry
  qed "sorry"
  thus " ?thesis "
     sorry
qed

mtheorem finsop_1_th_20:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for F be FinSequenceFINSEQ-1M3-of D holds  for g be BinOpBINOP-1M2-of D holds lenFINSEQ-1K4 F =XBOOLE-0R4 \<one>\<^sub>M implies g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F =XBOOLE-0R4 F .FUNCT-1K1 \<one>\<^sub>M"
  using finsop_1_lm_11 sorry

mtheorem finsop_1_th_21:
" for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for F be FinSequenceFINSEQ-1M3-of D holds  for g be BinOpBINOP-1M2-of D holds lenFINSEQ-1K4 F =XBOOLE-0R4 \<two>\<^sub>M implies g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F =XBOOLE-0R4 g .BINOP-1K1(F .FUNCT-1K1 \<one>\<^sub>M,F .FUNCT-1K1 \<two>\<^sub>M)"
proof-
  have " for D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2 holds  for F be FinSequenceFINSEQ-1M3-of D holds  for g be BinOpBINOP-1M2-of D holds lenFINSEQ-1K4 F =XBOOLE-0R4 \<two>\<^sub>M implies g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F =HIDDENR1 g .BINOP-1K1(F .FUNCT-1K1 \<one>\<^sub>M,F .FUNCT-1K1 \<two>\<^sub>M)"
  proof(rule ballI,rule ballI,rule ballI,rule impI)
    fix D assume [ty]: "D be  non emptyXBOOLE-0V1\<bar>setHIDDENM2"
    fix F assume [ty]: "F be FinSequenceFINSEQ-1M3-of D"
    fix g assume [ty]: "g be BinOpBINOP-1M2-of D"
    assume A1: "lenFINSEQ-1K4 F =XBOOLE-0R4 \<two>\<^sub>M"
    then have "F =HIDDENR1 <*FINSEQ-1K11 F .FUNCT-1K1 \<one>\<^sub>M,F .FUNCT-1K1 \<two>\<^sub>M *>"
      using finseq_1_th_44 sorry
    also have "... = <*FINSEQ-1K11 F /.PARTFUN1K7\<^bsub>(D)\<^esub> \<one>\<^sub>M,F .FUNCT-1K1 \<two>\<^sub>M *>"
      using A1 finseq_4_th_15 sorry
    also have "... = <*FINSEQ-4K2\<^bsub>(D)\<^esub> F /.PARTFUN1K7\<^bsub>(D)\<^esub> \<one>\<^sub>M,F /.PARTFUN1K7\<^bsub>(D)\<^esub> \<two>\<^sub>M *>"
      using A1 finseq_4_th_15 sorry
    finally have "F =HIDDENR1 <*FINSEQ-4K2\<^bsub>(D)\<^esub> F /.PARTFUN1K7\<^bsub>(D)\<^esub> \<one>\<^sub>M,F /.PARTFUN1K7\<^bsub>(D)\<^esub> \<two>\<^sub>M *>"
       sorry
    then have "g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F =HIDDENR1 g .BINOP-1K4\<^bsub>(D)\<^esub>(F /.PARTFUN1K7\<^bsub>(D)\<^esub> \<one>\<^sub>M,F /.PARTFUN1K7\<^bsub>(D)\<^esub> \<two>\<^sub>M)"
      using finsop_1_th_12 sorry
    also have "... = g .BINOP-1K1(F .FUNCT-1K1 \<one>\<^sub>M,F /.PARTFUN1K7\<^bsub>(D)\<^esub> \<two>\<^sub>M)"
      using A1 finseq_4_th_15 sorry
    also have "... = g .BINOP-1K1(F .FUNCT-1K1 \<one>\<^sub>M,F .FUNCT-1K1 \<two>\<^sub>M)"
      using A1 finseq_4_th_15 sorry
    finally show "g \<inverse>**\<inverse>FINSOP-1K1\<^bsub>(D)\<^esub> F =HIDDENR1 g .BINOP-1K1(F .FUNCT-1K1 \<one>\<^sub>M,F .FUNCT-1K1 \<two>\<^sub>M)"
       sorry
  qed "sorry"
  thus " ?thesis "
     sorry
qed

end
