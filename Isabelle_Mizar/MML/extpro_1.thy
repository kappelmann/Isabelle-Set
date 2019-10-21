theory extpro_1
  imports compos_1 memstr_0 funcop_1
begin


mdef AMI_Struct_over ("AMI-Struct-over _") where
  mlet "N be set"
  "struct [ COM-Struct \<bar>Mem-Struct-over N]AMI-Struct-over N(# carrier \<rightarrow> (\<lambda>S. set);
   ZeroF \<rightarrow> (\<lambda>S. Element-of the carrier of S);
   InstructionsF \<rightarrow> (\<lambda>_. Instructions);
   Object-Kind \<rightarrow> (\<lambda>S. Function-of the carrier of S, N);
   ValuesF \<rightarrow>  (\<lambda>S. ManySortedSet-of N);
    Execution \<rightarrow> (\<lambda>S. Action-of the InstructionsF of S,product ((the ValuesF of S)*`the Object-Kind of S)
 )#) defined on {carrier} \<union>{ZeroF}\<union>{InstructionsF}\<union>{Object-Kind}\<union>{ValuesF}\<union>{Execution}"
proof (standard,auto simp add: COM_Struct MemStruct_over,
 auto intro!: Fields_add_3_arg_Mode First_0_arg_Mode dest!:field_E simp add:string)
  fix X1
    assume [ty]:"the carrier of X1 is set"
          "the Object-Kind of X1 is Function_like"
          "the Object-Kind of X1 is Relation-of the carrier of X1,N"
          "the ValuesF of X1 is Function_like"
          "the InstructionsF of X1 is set"
          "the ValuesF of X1 is Relation_like"
          "the ValuesF of X1 is set"
    have [ty]:"the Object-Kind of X1 is Function" using relset_1_cl_1[of "the carrier of X1" N] by mauto   (* !?! CK !?!*)              
        
     show "inhabited(Action-of (the InstructionsF of X1) , product (the Object-Kind of X1) * (the ValuesF of X1))"
      by mauto
qed  


mtheorem
 mlet "N be set"," S be AMI-Struct-over N"
 "cluster (the Execution of S) \<rightarrow> Action-of the InstructionsF of S,product ((the ValuesF of S)*`the Object-Kind of S)"
using field AMI_Struct_overE by mauto
  
mtheorem AMI_Struct_over_ag:
mlet "N be set",
      "C be set","Z be Element-of C"," I be Instructions",
      "O be (Function-of C, N)"," V be ManySortedSet-of N","
 E be Action-of I,product (V*`O)"
 "cluster [#carrier\<mapsto>C;ZeroF\<mapsto>Z;InstructionsF\<mapsto>I; Object-Kind\<mapsto>O;
   ValuesF\<mapsto>V;Execution\<mapsto>E#] \<rightarrow>  strict(AMI-Struct-over N)"
unfolding AMI_Struct_over_def
    by (auto,rule struct_aggr_ancesors_rule, 
        auto intro!: aggrI struct_aggr3  struct_aggr0 Fields_add_3_arg_Mode First_0_arg_Mode dest!:field_E simp add:string)

mtheorem extpro_1_lm_1:
  mlet "N be with_zero\<bar> set"
  "[#carrier\<mapsto>{{}};ZeroF\<mapsto>{};InstructionsF\<mapsto>{[{},{},{}]}; Object-Kind\<mapsto>{{}} \<midarrow>> {};
   ValuesF\<mapsto>N \<midarrow>> NAT;Execution\<mapsto> ({[{},{},{}]} \<midarrow>> id (product( (N \<midarrow>> NAT) *` ({{}} \<midarrow>> {}))))#]
is strict(AMI-Struct-over N)"
proof-
  let ?h = "[{},{},{}]"
  let ?IT = "[#carrier\<mapsto>{{}};ZeroF\<mapsto>{};InstructionsF\<mapsto>{?h}; Object-Kind\<mapsto>{{}} \<midarrow>> {};
   ValuesF\<mapsto>N \<midarrow>> NAT;Execution\<mapsto> ({?h} \<midarrow>> id (product( (N \<midarrow>> NAT) *` ({{}} \<midarrow>> {}))))#]"
  have [ty]:"{{}} is set" by mauto
  have [ty]:"{} is Element-of {{}}" using tarski_def_1 by mauto
  have [ty]:"{?h} is Instructions" using Instructions_ex by auto

  have B1:"{} in N" using ordinal1_def_16E by auto
  hence [ty]: "({{}} \<midarrow>> {}) is Function-of {{}}, N" using funcop_cl by mty auto

  have "dom (N \<midarrow>> NAT) = N" "(N \<midarrow>> NAT) be Function" using funcop_1_th_13 all_set funcop_1_cl_1 by auto
  hence [ty]:"(N \<midarrow>> NAT) be ManySortedSet-of N" using pboole_def_1_th_1 by auto
  let ?E = "product( (N \<midarrow>> NAT) *` ({{}}\<midarrow>> {}))"
  have [ty]:"({?h} \<midarrow>> id (?E)) be (Action-of {?h}, ?E)"
   proof-
     have E:"id (?E) be Function" using funct_1_cl_4 relat_1_def_8 by mty auto
     have E1: "dom id (?E) = ?E"
          "rng id (?E) = ?E" using relat_1_id_dom relat_1_id_rng by mauto
     hence "rng id (?E) \<subseteq> ?E" using xboole_0_def_10 by mty auto
     hence "ex x be Function st id(?E) = x \<and> dom x= ?E \<and> rng x\<subseteq>?E" using E bexI[of _ "id (?E)"] E1
           by mauto
     hence I: "id(?E) in Funcs(?E,?E)"
       using funct_2_def_2[THEN iffD2] by mty auto
     thm funcop_cl
     show ?thesis using funcop_cl[OF _ _ _ I, of "{?h}"] all_set by auto
   qed
   show "?IT is strict(AMI-Struct-over N)" using AMI_Struct_over_ag by mauto
qed

mdef extpro_1_def_1 ("Trivial-AMI _") where
  mlet "N be with_zero\<bar> set"
  "func Trivial-AMI N \<rightarrow> strict(AMI-Struct-over N)
     means (\<lambda>it.
      the carrier of it = {{}} \<and>
        the ZeroF of it = {} \<and>
the InstructionsF of it = {[{},{},{}]} \<and>
  the Object-Kind of it = {{}} \<midarrow>> {}  \<and>
      the ValuesF of it = N \<midarrow>> NAT \<and>
    the Execution of it = {[{},{},{}]} \<midarrow>> id (product( N \<midarrow>> NAT \<circ> {{}} \<midarrow>> {})))"
proof-
  let ?h = "[{},{},{}]"
  let ?IT = "[#carrier\<mapsto>{{}};ZeroF\<mapsto>{};InstructionsF\<mapsto>{?h}; Object-Kind\<mapsto>{{}} \<midarrow>> {};
   ValuesF\<mapsto>N \<midarrow>> NAT;Execution\<mapsto> ({?h} \<midarrow>> id (product( (N \<midarrow>> NAT) *` ({{}} \<midarrow>> {}))))#]"
  let ?T = "\<lambda>it .the carrier of it = {{}} \<and> (the ZeroF of it) = {} \<and>
     (the InstructionsF of it) = {?h} \<and>
     (the Object-Kind of it) = ({{}}\<midarrow>> {})  \<and>
     (the ValuesF of it) = (N \<midarrow>> NAT) \<and>
     (the Execution of it) = ({?h} \<midarrow>> id (product( (N \<midarrow>> NAT) *` ({{}}\<midarrow>> {}))))"
  have A1[ty]:"?IT is strict(AMI-Struct-over N)" using extpro_1_lm_1 by mauto
  have [ty]:"?IT is AMI-Struct-over N" using strict by mauto
  have A2: "?T(?IT)"
    using aggr by (auto intro: the_selector_of_1)
  have I:"inhabited(strict(AMI-Struct-over N))" by mauto
  show "ex it be strict (AMI-Struct-over N) st ?T(it)"
    using bexI[OF _  A1 I] A2 by auto
next
      let ?h = "[{},{},{}]"
  let ?T = "\<lambda>it .the carrier of it = {{}} \<and> (the ZeroF of it) = {} \<and>
     (the InstructionsF of it) = {?h} \<and>
     (the Object-Kind of it) = ({{}}\<midarrow>> {})  \<and>
     (the ValuesF of it) = (N \<midarrow>> NAT) \<and>
     (the Execution of it) = ({?h} \<midarrow>> id (product( (N \<midarrow>> NAT) *` ({{}}\<midarrow>> {}))))"
  fix it1 it2 assume
    [ty]: "it1 be strict (AMI-Struct-over N)"
    "it2 be strict (AMI-Struct-over N)"
    and A1: "?T(it1)" "?T(it2)"
  show "it1=it2"
     proof(rule Equal_strict[of _ _ "AMI-Struct-over N"])
    show "it1 be Struct"  "it2 be Struct" using strict[THEN conjunct2] AMI_Struct_over by auto
    show "it1 is strict (AMI-Struct-over N)" "it2 is strict (AMI-Struct-over N)" by auto
    fix selector
    assume "selector in domain_of AMI-Struct-over N"
    hence "selector in {carrier}\<union>{ZeroF}\<union>{InstructionsF}\<union>
           {Object-Kind}\<union>{ValuesF}\<union>
             {Execution}" using AMI_Struct_over_dom by auto
   hence "selector in {carrier} \<or> selector in {ZeroF} \<or> selector in {InstructionsF} \<or>
           selector in {Object-Kind} \<or> selector in {ValuesF} \<or> selector in { Execution}"
    using xboole_0_def_3 all_set by auto
    hence A2: "selector = carrier \<or> selector = ZeroF \<or> selector =InstructionsF \<or>
           selector =Object-Kind \<or> selector =ValuesF \<or> selector = Execution" using tarski_def_1 xboole_0_def_3 all_set by auto
    thus "the selector of it1 = the selector of it2" using A1 by auto
   qed
 qed mauto

mtheorem extpro_1_cl_1:
  mlet "N be with_zero\<bar>set"
   "cluster Trivial-AMI N \<rightarrow> N:with_non-empty_values"
proof(standard,standard,simp)
  let ?T = "Trivial-AMI N"
  let ?VT =  "the_Values_of ?T"
  show T1[ty]: "?T be Mem-Struct-over N" using extpro_1_def_1 by mauto
  have A0: "the ValuesF of ?T = N \<midarrow>> NAT"
       "(the Object-Kind of ?T) = ({{}}\<midarrow>> {})" using extpro_1_def_1 by auto
  have V[ty]: "the ValuesF of ?T be ManySortedSet-of N" by mauto
  have V1: "the ValuesF of ?T be Function" by mauto
  have O[ty]: "the Object-Kind of ?T be Function-of the carrier of ?T, N" by mauto
  hence O1[ty]: "the Object-Kind of ?T be Function" using  relset_1_cl_1 by mauto
  have [ty]: "?VT be ManySortedSet-of the carrier of ?T" by mty auto
  have T2: "?VT = (the ValuesF of ?T)*`(the Object-Kind of ?T)" using T1 memstr_0_def_2[of N ?T] by mauto
  have "not {} in rng ?VT"
    proof
    have VT: "?VT be Function" using T2 by mauto
    assume A: "{} in rng ?VT"
    obtain n where
       A3: "n be object" "n in dom ?VT" "{} = ((the ValuesF of ?T)*`(the Object-Kind of ?T)).n"
      using funct_1_def_3[of ?VT] A T2 by mauto
    hence S:"n in dom the' Object-Kind(?T)" "the' Object-Kind(?T) . n in dom the' ValuesF(?T)"
      using funct_1_th_11[THEN iffD1, of "(the ValuesF of ?T)" "(the Object-Kind of ?T)" n,simplified]
       T2 by mty auto
    have "dom (the ValuesF of ?T) = N" using A0(1) funcop_1_th_13 by auto
    thm funct_1_th_12
    hence A4: "(the Object-Kind of ?T).n in N" using S by mauto
    have "?VT.n =  (the ValuesF of ?T). ((the Object-Kind of ?T).n)" using
         funct_1_th_12[] T2 A3(2) by mauto
    hence "?VT.n = NAT" using A0 A4 funcop_1_th_7 by mty auto
    hence "NAT={}" using A3 T2 by auto
    thus "False" using xb ordinal1_def_11 by auto
  qed
  thus "?VT is non-empty" using funct_1_def_9I T2 by mauto
qed mauto

text_raw {*\DefineSnippet{extpro_1_def_2}{*}
mdef extpro_1_def_2( "Exec \<^sub>_'(_ ,  _')" 190) where
 mlet "N be with_zero\<bar>set",
           "S be N:with_non-empty_values \<bar> AMI-Struct-over N",
           "I be Instruction-of S",
           "s be State-of S"
  "func Exec \<^sub>S(I,s) \<rightarrow> State-of S equals
    ((the Execution of S).I).s "
text_raw {*}%EndSnippet*}
proof-
  let ?E = "the Execution of S"
  let ?EI = "?E.I"
  let ?EIs = "?EI.s"
  let ?VS = "(the ValuesF of S)*`the Object-Kind of S " 
  have T0:"S be Mem-Struct-over N" "S be COM-Struct" by auto
  hence T1: "(the ValuesF of S)*`the Object-Kind of S = the_Values_of S" and
        [ty]:"the_Values_of S be non-empty\<bar>ManySortedSet-of the carrier of S"
    using memstr_0_def_2[of N S] memstr_0_def_3E[of N S] memstr_0_def_2_ty by mauto
  have I1[ty]: "the InstructionsF of S be Instructions" using T0 field COM_Struct by auto
  
  have [ty]: "product the_Values_of S is set" by mauto
      have [ty]: "Funcs( product the_Values_of S  , product the_Values_of S  ) is set" by mauto
  have "?E is Action-of the InstructionsF of S,product ((the ValuesF of S)*`the Object-Kind of S)" by mty auto
  hence E1: "?E be Action-of the InstructionsF of S,product (the_Values_of S)" using T1(1)
    by auto
  hence E2[ty]: "?E be Relation_like" using  
    relset_1_cl_1[of "the InstructionsF of S" "Funcs(product (the_Values_of S),product (the_Values_of S))"] by mauto
       (* !?! CK !?!*)    
  have [ty]:"?VS is Function" using T1 by mauto
  have [ty]:"product(?VS) is set" by mauto
  hence [ty]:"Funcs(product(?VS),product(?VS)) is set" by mauto  
  have "?E is Relation-of the InstructionsF of S, Funcs(product(?VS),product(?VS))" by mauto
  hence [ty]: "?E be set" using subset_1_def_1_ty_parent by mauto
  (* !?! CK !?!*)
  have P1:"product (the_Values_of S) is non empty" using T1 card_3_cl by auto
  hence "product (the_Values_of S)\<noteq>{}" using xboole_0_cl_2 by auto
  have "Funcs(product (the_Values_of S),product (the_Values_of S)) is non empty"
    using funct_2_cl_Funcs all_set by auto
  hence "Funcs(product (the_Values_of S),product (the_Values_of S)) \<noteq>{}"
     using xboole_0_cl_2 by auto
  hence DE: "dom ?E = the InstructionsF of S"
    using funct_2_def_1E[of "the InstructionsF of S" "Funcs(product (the_Values_of S),product (the_Values_of S))"] E1
      by mauto
  have "I in the InstructionsF of S" using Instructions_non_empty[OF I1] Element_of1 by auto
  hence Y: "?EI in rng ?E" using funct_1_def_3 E2 DE by mauto

  have "rng ?E c= Funcs(product (the' Object-Kind(S) * the' ValuesF(S)),product (the' Object-Kind(S) * the' ValuesF(S)))"
  using relat_1_def_19E by mauto
    hence r: "?EI in Funcs(product (the_Values_of S),product (the_Values_of S))"
         using Y T1 tarski_def_3E all_set by auto
  obtain EI where
     [ty]: "EI be Function" and
          ei:"?EI = EI \<and> dom EI = product (the_Values_of S) \<and> rng EI c= product (the_Values_of S)"
    using funct_2_def_2[THEN iffD1, OF _ _ r] all_set by auto
  have DD: "dom (the_Values_of S) = the carrier of S"
          " dom s =the carrier of S" using T1 partfun_1_def_2E[of "the carrier of S" s]
            partfun_1_def_2E[of "the carrier of S" "the_Values_of S"] by mty auto
  have "for y being object st y in dom s holds s. y in (the_Values_of S). y"
    using funct_1_def_14E[of "the_Values_of S" s] T1
    by auto
  hence "s in product (the_Values_of S)" using card_3_def_5[of "the_Values_of S"] DD T1 by auto
  hence "EI. s in rng EI" using ei funct_1_def_3 all_set by auto
  hence u: "EI. s in product (the_Values_of S)" using ei tarski_def_3E all_set by mty auto
  have T3: "the_Values_of S be Function" using T1 by auto
  obtain EIs where
     [ty]: "EIs be Function" and eis: "EI. s = EIs \<and> dom EIs = dom (the_Values_of S) \<and>
         (for y being object st y in dom (the_Values_of S) holds EIs. y in (the_Values_of S). y)"
     using card_3_def_5[THEN iffD1, OF _ u] by auto
   have W1:"?EIs be ManySortedSet-of the carrier of S" using DD eis ei pboole_def_1_th_1 by auto
  have E: "?EIs = EIs" using eis ei by auto
  have "EIs is (the_Values_of S)-compatible"
    proof(standard,auto)
       fix y assume "y in dom EIs"
      thus "EIs. y in (the_Values_of S). y" using eis ei by auto
    qed mauto
  thus "?EIs be State-of S" using W1 eis ei by auto
qed

text_raw {*\DefineSnippet{extpro_1_def_3}{*}
mdef extpro_1_def_3("halting _, _")where
  mlet "N be with_zero\<bar>set","
           S be N:with_non-empty_values \<bar> AMI-Struct-over N"
"attr halting S,N for Instruction-of S means (\<lambda>I.
       for s be State-of S holds Exec \<^sub>S(I,s) = s)"..
text_raw {*}%EndSnippet*}

thm extpro_1_def_3 
  
  
text_raw {*\DefineSnippet{extpro_1_def_4}{*}
mdef extpro_1_def_4 ("halting'_on _")where
  mlet "N be with_zero\<bar>set ""
    attr halting_on N for N:with_non-empty_values \<bar> AMI-Struct-over N means (\<lambda>S.
      halt \<^sub>S is halting S,N)"..
text_raw {*}%EndSnippet*}

  
  
text_raw {*\DefineSnippet{extpro_1_cl}{*}
mtheorem extpro_1_cl:
  "for N be with_zero\<bar>set,
       I be Instruction-of Trivial-AMI N,
       s be State-of Trivial-AMI N holds
    Exec \<^sub>Trivial-AMI N(I,s) = s"
text_raw {*}%EndSnippet*}
proof(intro ballI)
  fix N I s
  let ?T = "Trivial-AMI N"
  assume A1[ty]:"N be with_zero\<bar>set"
  thus "inhabited(Element-of the' InstructionsF(Trivial-AMI N))" by mauto
  thus "inhabited(State-of ?T)" using memstr_0_cl_ex by mauto
  assume A[ty]: "I be Instruction-of ?T"
          "s be State-of ?T"


  have A2: "?T be N:with_non-empty_values \<bar> AMI-Struct-over N" using extpro_1_cl_1 extpro_1_def_1 A1(1) by mauto
  have E: "Exec \<^sub>?T(I,s) = ((the Execution of ?T).I).s" using extpro_1_def_2[OF A1(1) A2] by auto
  hence R: "the Execution of ?T = op2 \<midarrow>> id (product( (N \<midarrow>> NAT) *` ({{}}\<midarrow>> {})))"
    using extpro_1_def_1 by auto
  have "I be Element-of {[{},{},{}]}" using extpro_1_def_1[OF A1] A1 A by auto
  hence A5: "I in {[{},{},{}]}" using Element_of by mty auto
  hence A3: "(the Execution of ?T).I = id (product( (N \<midarrow>> NAT) *` ({{}}\<midarrow>> {})))"
    using funcop_1_th_7 R by mauto
   have U[ty]: "the_Values_of ?T be ManySortedSet-of the carrier of ?T" by mty auto
  have "the ValuesF of ?T = (N\<midarrow>> NAT)"
       "(the Object-Kind of ?T) = ({{}}\<midarrow>> {})" using extpro_1_def_1[OF A1(1)] A1 by auto
  hence A4: "(N \<midarrow>> NAT) *` ({{}}\<midarrow>> {}) = the_Values_of ?T"
        "the_Values_of ?T be non-empty"
    using memstr_0_def_2[of N ?T] memstr_0_def_3E[of N ?T] A1 A2 by mauto
  have D: "dom s = the carrier of ?T \<and> dom the_Values_of ?T=the carrier of ?T"
       using A4 A1 partfun_1_def_2 U by mauto
   have "(\<forall>y : object. y in proj1 s \<longrightarrow> s . y in (the_Values_of ?T)  . y)"
       using funct_1_def_14[of "the_Values_of ?T" s,THEN iffD1] by mty auto
   hence "s in product(the_Values_of ?T)" using
   card_3_def_5[THEN iffD2,of "the_Values_of ?T" s]
     A1 A4(2)  D by mauto
  thus "Exec \<^sub>?T(I,s) = s" using A5 A4 A3 E funct_1_th_18 by mauto
qed mauto

(* NON CLOSED!:
  text_raw {*\DefineSnippet{extpro_1_cl_2}{*}
*)
mtheorem extpro_1_cl_2:
  mlet "N be with_zero\<bar>set"
   "cluster Trivial-AMI N \<rightarrow> halting_on N"
proof(standard,standard,mauto)
  let ?T = "Trivial-AMI N"
  show "halt \<^sub>Trivial-AMI N is halting Trivial-AMI N,N"
  proof(standard,auto)
    show I: "inhabited(State-of ?T)" using memstr_0_cl_ex by mauto
    fix s assume [ty]:"s is the' carrier(Trivial-AMI N) : total""
         s is the' carrier(Trivial-AMI N)-defined""
         s is the_Values_of Trivial-AMI N -compatible""
         s is Function_like""s is Relation_like""s is set"
      hence "?T be COM-Struct" by mauto
     hence W1:"halt \<^sub>?T be Instruction-of ?T" using compos_1_def_10[of ?T] by mty auto
     show " Exec \<^sub>Trivial-AMI N(halt \<^sub>Trivial-AMI N ,  s) = s" using extpro_1_cl[of N "halt \<^sub>Trivial-AMI N " s] I by mauto
  qed mauto
qed

notation
  compos_1_def_10 ("halt\<^bsub>_\<^esub>")

text_raw {*\DefineSnippet{extpro_1}{*}
theorem extpro_1:
  assumes [ty]: "N be with_zero \<bar> set"
  shows "halt\<^bsub>Trivial-AMI N\<^esub> is halting Trivial-AMI N, N"
text_raw {*}%EndSnippet*}
proof(standard,mauto)
  let ?T = "Trivial-AMI N"
 show I: "inhabited(State-of ?T)" using memstr_0_cl_ex by mauto
  fix s assume [ty]:"s is the' carrier(Trivial-AMI N) : total""
         s is the' carrier(Trivial-AMI N)-defined""
         s is the_Values_of Trivial-AMI N -compatible""
         s is Function_like""s is Relation_like""s is set"
     hence "?T be COM-Struct" by mauto
     hence W1:"halt \<^sub>?T be Instruction-of ?T" using compos_1_def_10[of ?T] by mty auto
     show " Exec \<^sub>Trivial-AMI N(halt \<^sub>Trivial-AMI N ,  s) = s" using extpro_1_cl[of N "halt \<^sub>Trivial-AMI N " s] I by auto
qed

end
