theory memstr_0
imports struct_0 ordinal1
begin


abbreviation MemStruct_fields_prefix ("Mem-Struct'_fields _")
  where "Mem-Struct_fields N \<equiv> (#
   carrier \<rightarrow> (\<lambda>S. set);
   ZeroF \<rightarrow> (\<lambda>S. Element-of the carrier of S) ;
   Object-Kind \<rightarrow> (\<lambda>S. Function-of the carrier of S, N) ;
   ValuesF \<rightarrow>  (\<lambda>S. ManySortedSet-of N) #)"

text_raw {*\DefineSnippet{MemStruct}{*}
mdef MemStruct_over ("Mem-Struct-over _" [120] 120) where
  mlet "N be set"
"struct [ZeroStr] Mem-Struct-over N (#
   carrier \<rightarrow> (\<lambda>S. set);
   ZeroF \<rightarrow> (\<lambda>S. Element-of the carrier of S);
   Object-Kind \<rightarrow> (\<lambda>S. Function-of the carrier of S, N);
   ValuesF \<rightarrow> (\<lambda>S. ManySortedSet-of N)
#) defined on {carrier}\<union>{ZeroF}\<union>{Object-Kind}\<union>{ValuesF}"
text_raw {*}%EndSnippet*}
 by (auto simp add: ZeroStr,
     auto intro!: Fields_add_3_arg_Mode First_0_arg_Mode dest!:field_E simp add:string)


mtheorem 
  mlet "N be set","S be Mem-Struct-over N"
  "cluster the Object-Kind of S \<rightarrow> Function-of the carrier of S, N"
using field MemStruct_overE by mauto

mtheorem
 mlet "N be set","S be Mem-Struct-over N"
  "cluster the ValuesF of S \<rightarrow> ManySortedSet-of N"
using field MemStruct_overE by mauto

abbreviation(input) Instruction_Counter_prefix ("IC \<^sub>_" [190] 190)
  where "IC \<^sub>S \<equiv> 0\<^sub>S"

abbreviation (input) Data_Locations_prefix ("Data-Locations \<^sub>_")
  where " Data-Locations \<^sub>S \<equiv>NonZero \<^sub>S"

mdef memstr_0_def_2 ( "the'_Values'_of _ " [190] 190) where
mlet "N be with_zero\<bar>set","S be Mem-Struct-over N"
  "func the_Values_of S \<rightarrow> ManySortedSet-of the carrier of S equals
     the ValuesF of S \<circ> the Object-Kind of S"
proof-
  have "{} in N" using ordinal1_def_16E by auto
  hence N: "N \<noteq> {}" using xb by auto
  let ?V = "the ValuesF of S"
  let ?O = "the Object-Kind of S"
  have A2: "dom ?O = the carrier of S" using funct_2_def_1E N by mauto
  have [ty]:"?O is Function-of the carrier of S, N" by mauto
   thm ty
  hence [ty]:"?O is Function" using relset_1_cl_1[of S N ?O] by mauto   (* !?! CK !?!*)  
(* bez tej linii powyżej nie zaskoczy*)
    
  have "?O is N-valued" using relset_1_cl_2 by mty auto
  hence A1: "rng ?O c= N" using relat_1_def_19E[of N ?O]  by mty auto
  have "dom ?V=N" using partfun_1_def_2E by mauto
  hence "dom (?O*?V) = the carrier of S" using A2 funct_2_lm_1[of ?O ?V] A1 by auto
  thus "(?V *` ?O ) is the' carrier(S) : total \<bar> the' carrier(S)-defined \<bar> (Function_like \<bar> (Relation_like \<bar> set))" using
     pboole_def_1_th_1[of "the carrier of S" ] by mauto
qed

text_raw {*\DefineSnippet{memstr_0_mode_1}{*}
abbreviation memstr_0_mode_1 ("PartState-of _" [190] 190) where
  "PartState-of M \<equiv> the carrier of M-defined \<bar> the_Values_of M-compatible \<bar> Function"
text_raw {*}%EndSnippet*}

mtheorem memstr_0_cl:
  mlet "M be with_zero\<bar>set","S be Mem-Struct-over M"
  "cluster the carrier of S-defined \<bar> the_Values_of S-compatible for Function"
proof(standard,standard)
  have "dom {} is empty" by mauto
  hence D: "dom {}={}" using xboole_0_lm_1 by mauto
  hence "dom {} \<subseteq> the carrier of S" using tarski_def_3 xb by mauto
  hence [ty]:"{} is the carrier of S-defined" using relat_1_def_18 by mauto
  have [ty]:"{} is the_Values_of S-compatible"
  proof(standard,mauto)
    fix x assume "x in dom {}"
    thus "{} . x in (the_Values_of S). x" using D xb by auto
  qed
  show "{} is the carrier of S-defined \<bar> the_Values_of S-compatible \<bar> Function" by mauto
qed


mdef memstr_0_def_3 ("_ :with'_non-empty'_values" [120] 120) where
 mlet "N be set ""
   attr N :with_non-empty_values for Mem-Struct-over N means (\<lambda>S. (the_Values_of S) is non-empty)"..


theorem I: "inhabited(A\<bar>B\<bar>C) \<Longrightarrow> inhabited(A\<bar>(B\<bar>C))" unfolding inhabited_def by simp
theorem I1: "inhabited(D\<bar>(A\<bar>(B\<bar>C))) \<Longrightarrow> inhabited(D\<bar>((A\<bar>B)\<bar>C))" unfolding inhabited_def by simp
theorem I2: "inhabited(A\<bar>B) \<Longrightarrow> inhabited(A)" unfolding inhabited_def
proof-
  assume "\<exists>\<^sub>Lx. x is A \<bar> B"
  then obtain x where "x is A\<bar>B" by auto
  hence "x is A" by auto
  thus "\<exists>\<^sub>Lx. x is A" by auto
qed
theorem I3: "inhabited(A\<bar>B) \<Longrightarrow> inhabited(B)" unfolding inhabited_def
proof-
  assume "\<exists>\<^sub>Lx. x is A \<bar> B"
  then obtain x where "x is A\<bar>B" by auto
  hence "x is B" by auto
  thus "\<exists>\<^sub>Lx. x is B" by auto
qed



mtheorem memstr_0_cl_1:
  mlet "N be with_zero\<bar>set","S be N:with_non-empty_values \<bar> Mem-Struct-over N"
   "cluster (the carrier of S):total for PartState-of S"
proof(standard)
  have [ty]: "the_Values_of S be non-empty\<bar> Function " using memstr_0_def_3E by mauto
 have "inhabited(
  (the' carrier(S) : total \<bar> the' carrier(S)-defined) \<bar> the_Values_of S -compatible \<bar> Function)"
   using funct_2_cl_comp[of "the carrier of S" "the_Values_of S"] by mty auto
 hence "inhabited(
  (the' carrier(S) : total \<bar> the' carrier(S)-defined) \<bar> (the_Values_of S -compatible \<bar> Function))"
    using I by auto
  hence "inhabited(
      the' carrier(S) : total \<bar> (the' carrier(S)-defined \<bar> (the_Values_of S -compatible \<bar> Function)))"
      using I by auto
  thus "inhabited(
      the' carrier(S) : total \<bar> (the' carrier(S)-defined \<bar> the_Values_of S -compatible \<bar> Function))"
      using I1 by auto
  qed



mtheorem memstr_0_cl_ex:
  mlet "N be with_zero\<bar>set","S be N:with_non-empty_values\<bar> Mem-Struct-over N"
  "cluster (the carrier of S):total \<bar> (the carrier of S)-defined \<bar> the_Values_of S-compatible for Function"
proof(standard)
  have "the_Values_of S is non-empty" using memstr_0_def_3E by mauto
  thus "inhabited((the carrier of S):total \<bar> (the carrier of S)-defined \<bar> the_Values_of S-compatible\<bar> Function)"
   using funct_2_cl_comp by mauto
qed


text_raw {*\DefineSnippet{memstr_0_mode_2}{*}
abbreviation memstr_0_mode_2 ("State-of _" 190)
  where "State-of M \<equiv>
         (the carrier of M):total \<bar> (the carrier of M)-defined \<bar> the_Values_of M-compatible \<bar> Function"
text_raw {*}%EndSnippet*}

abbreviation memstr_0_mode_3 ("Object-of _" 190)
where "Object-of S \<equiv> Element-of-struct S"

mdef memstr_0_def_4( "ObjectKind'( _ , _ ') _ " 190) where
  mlet "N be with_zero\<bar>set ", " S be non empty-struct \<bar> Mem-Struct-over N"," o be Object-of S"
  "func ObjectKind(N,S) o \<rightarrow> Element-of N equals
    (the Object-Kind of S).o "
proof-
  have "{} in N" using ordinal1_def_16E by auto
  hence N: "N \<noteq> {}" using xb by auto
  let ?O = "the Object-Kind of S"
  have A2: "dom ?O = the carrier of S" using funct_2_def_1E N by mauto
  have "?O is Function-of the carrier of S, N" by mauto
  hence [ty]:"?O is Function" using relset_1_cl_1[of S N ?O] by mauto
  have "?O is N-valued" using relset_1_cl_2 by mauto
  hence A1: "rng ?O c= N" using relat_1_def_19E[of N ?O] by auto
  have "the carrier of S is non empty" using struct_0_def_1 by mauto
  hence "the carrier of S \<noteq>{}" using xboole_0_def_1 by mauto
  hence "o in dom ?O" using A2 Element_of_rule2 by mauto
 thus "(?O .o) be Element-of N" using A1 funct_1_def_3[of ?O] Element_of_rule by mauto
qed

mdef memstr_0_def_5 :: "Set \<Rightarrow> Set \<Rightarrow> Set \<Rightarrow> Set" ( "Values'( _ , _ ') _ " 190) where
  "func Values(N,S) o \<rightarrow> set equals
    (the_Values_of S).o"
proof-
  show "((the_Values_of S).o) be set" using all_set by auto
qed

ML {* Term.add_frees @{term "cluster Values(N,S) o \<rightarrow> non empty"} []*}
mtheorem memstr_0_cl_2:
  mlet "N be with_zero\<bar>set",
       "S be non empty-struct \<bar> N:with_non-empty_values \<bar> Mem-Struct-over N",
       "o be Object-of S"
   "cluster Values(N,S) o \<rightarrow> non empty"
 proof
   let ?VS = "the_Values_of S"
   have Vo: "Values(N,S) o =  ?VS .o" using memstr_0_def_5 by mauto
   have VS: "?VS be ManySortedSet-of the carrier of S" by mty auto
   hence A2: "dom ?VS = the carrier of S" using partfun_1_def_2E by mauto
   have VS1:"?VS be Function" using VS by auto
   have "the carrier of S is non empty" by mauto
   hence "o in dom ?VS" using A2 Element_of1 by auto
   hence H: "?VS. o in rng ?VS" using funct_1_def_3 by mauto
   have "?VS is non-empty" using memstr_0_def_3 by mauto
   hence "?VS. o \<noteq> {}" using H funct_1_def_9 by mauto
   thus "Values(N,S) o is non empty" using Vo xboole_0_lm_1 all_set by auto
 qed


mdef memstr_0_def_8 ("DataPart \<^sub>_ _" [190, 190] 190) where
  mlet "N be with_zero\<bar>set","S be Mem-Struct-over N","p be PartState-of S"
  "func DataPart \<^sub>S p \<rightarrow> PartState-of S equals
    p | Data-Locations \<^sub>S"
proof
  have [ty]: "NonZero \<^sub>S is set" using struct_0_def_17_ty[of S] subset_1_def_1_ty_parent by mauto (* !?! CK !?!*)
  show "p | (NonZero \<^sub>S) is Function" by mauto
  let ?D="Data-Locations \<^sub>S"
  let ?pD ="p | ?D"
  let ?V = "the_Values_of S"
 (* have W1: "?pD be Function_like" by auto *)
   have W: "dom p c= the carrier of S" using relat_1_def_18E by simp
  have S: "dom ?pD = proj1 p \<inter> NonZero \<^sub>S" using relat_1_th_55[of ?D p] by mauto
  have "dom ?pD c= the carrier of S"
  proof(standard,auto)
    fix x assume "x in dom ?pD"
    hence "x in proj1 p" using S xboole_0_def_4 by mauto
    thus "x in the carrier of S" using W tarski_def_3E by mauto
  qed mauto
  hence W2: "?pD is the carrier of S -defined" using relat_1_def_18I[of "the carrier of S" ?pD] by mty auto
  have W3: "?pD is ?V -compatible"
  proof(standard,mauto)
   fix x assume A1: "x in dom ?pD"
    hence A2: "?pD. x = p .x" using funct_1_th_47 by mauto
    have "x in dom p" using A1 relat_1_th_51 by mauto
    hence "p. x in ?V.x" using funct_1_def_14E by auto
    thus "?pD. x in ?V. x" using A2 by auto
  qed
  thus "p | (NonZero \<^sub>S) is the' carrier(S)-defined \<bar> the_Values_of S -compatible" using W2 by mauto
qed mauto

mdef memstr_0_def_9 ("_ :data-only" [150] 150) where
 mlet "N be with_zero\<bar>set"," S be Mem-Struct-over N"
"attr S :data-only for PartState-of S means (\<lambda>p. dom p misses {IC \<^sub>S})"..

mtheorem memstr_0_th_3[rule_format]:
  "for N be with_zero\<bar>set holds
      for S be Mem-Struct-over N holds
         for p be PartState-of S holds
           \<not> IC \<^sub>S in dom DataPart \<^sub>S p"
proof(intro ballI)
  fix N S p
  assume T0[ty]: "N be with_zero\<bar>set"
         "S be Mem-Struct-over N"
  have [ty]: "NonZero \<^sub>S is set" using struct_0_def_17_ty[of S] subset_1_def_1_ty_parent by mauto (* !?! CK !?!*)

  show "inhabited(the carrier of S-defined \<bar> the_Values_of S -compatible \<bar> Function)" using
     memstr_0_cl by mauto
assume [ty]:"p be PartState-of S"
    show "not IC \<^sub>S in dom DataPart \<^sub>S p"
  proof
    have "S be ZeroStr" by auto
    hence A1: "NonZero \<^sub>S = ([#]S) \\ {0\<^sub>S}" using struct_0_def_17 by simp
    have "([#] S ) is Subset-of the' carrier(S)" by mauto
    hence [ty]: "([#]S) is set" by mauto (* !?! CK !?!*)

    assume "IC \<^sub>S in dom DataPart \<^sub>S p"
    hence "IC \<^sub>S in dom (p | Data-Locations \<^sub>S)" using memstr_0_def_8 by mauto
    hence "0\<^sub>S in NonZero \<^sub>S" using relat_1_th_51 by mauto
    thus "False" using tarski_def_1 xboole_0_def_5 A1 by mauto
  qed
qed mauto

theorem memstr_0_th_4[rule_format]:
  "for N be with_zero\<bar>set holds
      for S be Mem-Struct-over N holds
         for p be PartState-of S holds
            {IC \<^sub>S}  misses dom DataPart \<^sub>S p"
proof(intro ballI)
  fix N S p
  assume T0[ty]: "N be with_zero\<bar>set"
         "S be Mem-Struct-over N"
  show "inhabited(the carrier of S-defined \<bar> the_Values_of S -compatible \<bar> Function)" using
     memstr_0_cl by mauto
  assume [ty]:"p be PartState-of S"
  have "{IC \<^sub>S}  meets dom DataPart \<^sub>S p \<longrightarrow> False"
  proof
    assume "{IC \<^sub>S}  meets dom DataPart \<^sub>S p"
    then obtain x where
      A1: "x be object" "x in {IC \<^sub>S}  \<and> x in dom DataPart \<^sub>S p" using xboole_0_th_3 all_set by auto
    hence "x = IC \<^sub>S" using tarski_def_1 by auto
    thus "False" using A1 memstr_0_th_3 T0 memstr_0_cl by mauto
  qed
  thus "{IC \<^sub>S}  misses dom DataPart \<^sub>S p" using xboole_0_antonym_meets all_set by auto
qed mauto

text_raw {*\DefineSnippet{memstr_0_th_6}{*}
theorem memstr_0_th_6:
  "for N be with_zero\<bar>set holds
      for S be Mem-Struct-over N holds
         for p be PartState-of S holds
    p is S:data-only \<longleftrightarrow> dom p c= Data-Locations \<^sub>S"
text_raw {*}%EndSnippet*}
proof(intro ballI,rule iffI3)
  fix N S p
  assume T0[ty]: "N be with_zero\<bar>set"
         "S be Mem-Struct-over N"
  show "inhabited(the carrier of S-defined \<bar> the_Values_of S -compatible \<bar> Function)" using
     memstr_0_cl by mauto
  assume [ty]:"p be PartState-of S"
  have A2: "Data-Locations \<^sub>S = ([#]S) \\ {IC \<^sub>S}" using struct_0_def_17 by simp
   have "([#] S ) is Subset-of the' carrier(S)" by mauto
  hence [ty]: "([#]S) is set" by mauto (* !?! CK !?!*)
  have [ty]: "NonZero \<^sub>S is set" using struct_0_def_17_ty[of S] subset_1_def_1_ty_parent by mauto (* !?! CK !?!*)

  show "p is S:data-only \<longrightarrow> dom p c= Data-Locations \<^sub>S"
  proof(rule impI,standard,auto)
    fix x
    assume A1: "p is S:data-only" "x in dom p"
    hence "dom p misses {IC \<^sub>S}" using memstr_0_def_9 by mauto
    hence "(dom p \<inter> {IC \<^sub>S}) is empty " using xboole_0_def_7 xboole_0_def_2 by mauto
    hence A3: "not x in {IC \<^sub>S}" using A1(2) xboole_0_def_1 xboole_0_def_4 by mauto
    have "dom p \<subseteq> the carrier of S" using relat_1_def_18 by mauto
    hence "x in [#]S" using T0 A1(2) struct_0_def_3 tarski_def_3 by mauto
    thus "x in Data-Locations \<^sub>S" using A2 A3 xboole_0_def_5 by mauto
  qed mauto
  assume A3: "dom p c= Data-Locations \<^sub>S"
   have "dom p meets {IC \<^sub>S}  \<longrightarrow> False"
  proof
    assume "dom p meets {IC \<^sub>S}"
    then obtain x where
      A1: "x be object" "x in dom p \<and> x in {IC \<^sub>S}" using xboole_0_th_3 all_set by auto
    hence "x in Data-Locations \<^sub>S" using A3 tarski_def_3E by mauto
    thus "False" using A1 A2 xboole_0_def_5 by mauto
  qed
  hence "dom p misses {IC \<^sub>S}" using xboole_0_antonym_meets all_set by auto
  thus "p is S:data-only" using memstr_0_def_9 T0 by mauto
qed mauto

end
