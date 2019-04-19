theory struct_0
  imports "../2_Mizar/mizar_struct" 
          "../2_Mizar/mizar_string"
          "../2_Mizar/mizar_fraenkel_2"
  binop_1
begin  
  
mdef one_sorted :: "Ty"  ("1-sorted") where
  "struct 1-sorted (# carrier \<rightarrow>  set' #) defined on {carrier}"
  by (auto intro!: Fields_add_3_arg_Mode First_0_arg_Mode dest!:field_E simp add:string)
 
mtheorem
  mlet "S be 1-sorted" 
  "cluster the carrier of S \<rightarrow> set" 
using field_E one_sortedE by mauto   
   
mtheorem
  mlet "X be set"  
  "cluster [#carrier\<mapsto>X#] \<rightarrow> strict(1-sorted)"
  unfolding one_sorted_def
    by (auto,rule struct_aggr_no_ancesors_rule,
         auto intro!: aggrI struct_aggr3  struct_aggr0 Fields_add_3_arg_Mode First_0_arg_Mode dest!:field_E simp add:string) ty_auto

    
mdef struct_0_def_1 ("empty-struct")where
   "attr empty-struct for 1-sorted means (\<lambda> IT. (the carrier of IT) is empty)".

mtheorem struct_0_cl_1:
  "cluster empty-struct\<bar> strict (1-sorted) for 1-sorted"
proof(standard,standard,simp,intro conjI)
    let ?X = "[#carrier \<mapsto>{} #]"
    show F2[ty]: "?X be strict(1-sorted)" "?X be 1-sorted" by mauto
    have "the carrier of ?X ={}" using the_selector_of_1[of _ carrier op0] aggr by ty_auto
    thus "?X is empty-struct" using struct_0_def_1 F2 by ty_simp
qed

mtheorem struct_0_cl_2:
  "cluster non empty-struct \<bar> strict(1-sorted) for 1-sorted"
proof(standard,standard)
    let ?X = "[# carrier \<mapsto> {{}}#]"
    have F2[ty]: "?X be strict(1-sorted)"  by mauto
    have "the carrier of ?X ={{}}" using the_selector_of_1[of _ carrier "{op0}"] aggr by ty_auto
    hence "(the carrier of ?X) is non empty" by mauto
    thus "?X is non empty-struct \<bar> strict(1-sorted) \<bar> 1-sorted" using F2 struct_0_def_1E by mauto
qed

mtheorem struct_0_cl_3:
 mlet "S be empty-struct \<bar> 1-sorted"
   "cluster the carrier of S \<rightarrow> empty" 
using struct_0_def_1[of S] by ty_auto
  
mtheorem struct_0_cl_4:
  mlet "S be non empty-struct \<bar> 1-sorted"
   "cluster (the carrier of S) \<rightarrow> non empty" 
using struct_0_def_1[of S] by ty_auto

abbreviation struct_of_mode_1_prefix ("Element-of-struct _" [150] 150)
  where "Element-of-struct X \<equiv> Element-of (the carrier of X)"
abbreviation struct_of_mode_2_prefix ("Subset-of-struct _" [150] 150)
  where "Subset-of-struct X \<equiv> Subset-of (the carrier of X)"
abbreviation struct_of_mode_3_prefix ("Subset-Family-of-struct _" [150] 150)
  where "Subset-Family-of-struct X \<equiv> Subset-Family-of (the carrier of X)"


abbreviation struct_of_mode_4_prefix ("Function-of-1struct _ , _ " [150] 150)
  where "Function-of-1struct X,Y \<equiv> Function-of (the carrier of X), Y"
abbreviation struct_of_mode_5_prefix ("Function-of-2struct _ , _ " [150] 150)
  where "Function-of-2struct X,Y \<equiv> Function-of X, (the carrier of Y)"

abbreviation struct_of_mode_6_prefix ("Function-of-struct _ , _ " [150] 150)
  where "Function-of-struct X,Y \<equiv> Function-of (the carrier of X), (the carrier of Y)"

text_raw {*\DefineSnippet{struct0def2prefix}{*}

mdef struct_0_def_2 ( "{}s _ " 90) where
  mlet "T be 1-sorted"
  "func ({}s T) \<rightarrow> Subset-of-struct T equals {}"
text_raw {*}%EndSnippet*}
proof-
  show "op0 be (Subset-of-struct T)" using Subset_of_rule xb tarski_def_3
     one_sorted field by ty_auto
qed

text_raw {*\DefineSnippet{struct0def3}{*}

mdef struct_0_def_3 ( "[#] _ " 90) where
  mlet "T be 1-sorted"
  "func ([#] T) \<rightarrow> Subset-of-struct T equals
    the carrier of T"
text_raw {*}%EndSnippet*}
proof-
  show "(the carrier of T) be (Subset-of-struct T)" using Subset_of_rule xb tarski_def_3
     one_sorted field by ty_auto
qed


mtheorem struct_0_cl_5:
  mlet "T be 1-sorted"
   "cluster {}s T \<rightarrow> empty" 
using struct_0_def_2 by mauto
  
mtheorem struct_0_cl_6:
  mlet "T be empty-struct \<bar>1-sorted"
  "cluster [#]T \<rightarrow> empty" 
using struct_0_def_3 struct_0_def_1 by mauto
  
mtheorem struct_0_cl_7:
  mlet "T be non empty-struct \<bar>1-sorted"
  "cluster [#]T \<rightarrow> non empty" 
using struct_0_def_3 struct_0_def_1 by mauto
    
mtheorem struct_0_cl_8:
  mlet "S be non empty-struct \<bar>1-sorted"
   "cluster non empty for (Subset-of-struct S)"
proof(standard,standard)
  show "([#]S) is (non empty) \<bar>  (Subset-of-struct S)" using struct_0_cl_7 by mauto
qed

mdef struct_0_def_4( "id-struct _" [90] 90) where
  mlet "S be 1-sorted"
  "func id-struct S \<rightarrow> Function-of-struct S,S equals
     id the carrier of S"
proof-
  show "id (the carrier of S) be Function-of-struct S,S" by mauto
qed

abbreviation struct_of_mode_8_prefix ("PartFunc-of-1struct _ , _ " 150)
  where "PartFunc-of-1struct X,Y \<equiv> PartFunc-of (the carrier of X), Y"
abbreviation struct_of_mode_9_prefix ("PartFunc-of-2struct _ , _ " 150)
  where "PartFunc-of-2struct X,Y \<equiv> PartFunc-of X,(the carrier of Y)"
abbreviation struct_of_mode_10_prefix ("PartFunc-of-struct _ , _ " 150)
  where "PartFunc-of-struct X,Y \<equiv> PartFunc-of (the carrier of X), (the carrier of Y)"

abbreviation(input) in_struct_prefix ("_ in'_struct _" 10) where
  "x in_struct y \<equiv> x in (the carrier of y)"

mdef ZeroStr ("ZeroStr") where
  "struct [1-sorted] ZeroStr (#
      carrier \<rightarrow> set' ;
      ZeroF \<rightarrow> Element-of' the' carrier#) defined on ({carrier}\<union>{ZeroF})"
  by (auto simp add:one_sorted, auto intro!: Fields_add_3_arg_Mode First_0_arg_Mode dest!:field_E simp add:string)
mtheorem
  mlet "X be ZeroStr" 
  "cluster the ZeroF of X \<rightarrow> Element-of-struct X" 
using field ZeroStrE by ty_auto

mtheorem
  mlet "X be set", "Z be Element-of X"
  "cluster [#carrier\<mapsto>X; ZeroF\<mapsto> Z#] \<rightarrow> strict(ZeroStr)"
unfolding ZeroStr_def
    by (auto,rule struct_aggr_ancesors_rule,
         auto intro!: aggrI struct_aggr3  struct_aggr0 Fields_add_3_arg_Mode First_0_arg_Mode dest!:field_E simp add:string) ty_auto

mtheorem struct_0_cl_9:
  "cluster strict (ZeroStr) \<bar> non empty-struct for ZeroStr"
proof(standard,standard,simp,intro conjI)
    let ?x = "the set"
    let ?X ="[#carrier \<mapsto> {?x} ; ZeroF\<mapsto> ?x#]"
        have [ty]: "?x be Element-of {?x}" using Element_of_rule3 tarski_def_1 tarski_def_1_ty by auto
        thus [ty]:"?X be strict(ZeroStr)" "?X be ZeroStr" by mauto
        have C1: "the carrier of ?X = {?x}" using the_selector_of_1[of _ "carrier" "{the set}"] aggr by mauto
        hence "the carrier of ?X is non empty" using C1 tarski_def_1 xboole_0_def_1 by mauto
        thus "\<not> ?X is empty-struct" using C1 struct_0_def_1 by mauto
      qed

mdef OneStr("OneStr") where
  "struct [1-sorted] OneStr (#
      carrier \<rightarrow> set' ;
      OneF \<rightarrow> Element-of' the' carrier#) defined on {carrier}\<union>{OneF}"
  by (auto simp add:one_sorted,
      auto intro!: Fields_add_3_arg_Mode First_0_arg_Mode dest!:field_E simp add:string)  
    
mtheorem
  mlet "X be OneStr" 
 "cluster the OneF of X \<rightarrow> Element-of-struct X" 
using field OneStrE by ty_auto
  
mtheorem
  mlet "X be set", "O be Element-of X"
  "cluster [#carrier\<mapsto>X; OneF\<mapsto> O#] \<rightarrow> strict(OneStr)"
 unfolding OneStr_def
    by (auto,rule struct_aggr_ancesors_rule,
         auto intro!: aggrI struct_aggr3  struct_aggr0 Fields_add_3_arg_Mode First_0_arg_Mode dest!:field_E simp add:string) ty_auto
    
mdef ZeroOneStr ("ZeroOneStr") where
  "struct [ZeroStr\<bar>OneStr] ZeroOneStr 
     (# carrier \<rightarrow> set' ; ZeroF \<rightarrow> Element-of' the' carrier; OneF \<rightarrow> Element-of' the' carrier#)
     defined on {carrier}\<union>{ZeroF}\<union>{OneF}"
  by (auto simp add:ZeroStr OneStr,
    auto intro!: Fields_add_3_arg_Mode First_0_arg_Mode dest!:field_E simp add:string)
  
mtheorem
  mlet "X be set", "Z be Element-of X","O be Element-of X"
  "cluster [#carrier\<mapsto>X;ZeroF \<mapsto> Z; OneF\<mapsto> O#] \<rightarrow> strict(ZeroOneStr)"
unfolding ZeroOneStr_def
    by (auto,rule struct_aggr_ancesors_rule,
         auto intro!: aggrI struct_aggr3  struct_aggr0 Fields_add_3_arg_Mode First_0_arg_Mode dest!:field_E simp add:string) ty_auto
  
text_raw {*\DefineSnippet{struct0def6}{*}

mdef struct_0_def_6 ( "0\<^sub>_" [1000] 99) where
mlet "S be ZeroStr"
  "func 0\<^sub>S \<rightarrow> Element-of-struct S equals
     the ZeroF of S"
text_raw {*}%EndSnippet*}
proof-
  show "(the ZeroF of S) be Element-of (the carrier of S)"
       by ty_simp
qed


text_raw {*\DefineSnippet{struct0def7}{*}

mdef struct_0_def_7 ("1\<^sub>_" [1000] 99) where
  mlet "S be OneStr"
  "func 1\<^sub>S \<rightarrow> Element-of-struct S equals
     the OneF of S"
text_raw {*}%EndSnippet*}
proof-
  show "(the OneF of S) be Element-of (the carrier of S)" by ty_auto
qed



mdef struct_0_def_8 ("degenerated")where
   "attr degenerated for ZeroOneStr means (\<lambda> S. 0\<^sub>S = 1\<^sub>S)".

(*lemma struct_0_def_8c: "X is ZeroOneStr \<Longrightarrow> 0\<^sub>X \<noteq> 1\<^sub>X \<Longrightarrow> \<not> X is degenerated" using struct_0_def_8 by auto*)

mdef struct_0_def_9 ("trivial-struct")where
   "attr trivial-struct for 1-sorted means (\<lambda> S. the carrier of S is trivial)".

mtheorem struct_0_def_10:
   "redefine attr trivial-struct for 1-sorted means
        \<lambda>S. for x, y be Element-of-struct S holds x=y"
proof(standard,rule ballI,rule iffI3)
  fix S assume [ty]:"S is 1-sorted" 
  show "S is trivial-struct \<longrightarrow> (for x, y be Element-of-struct S holds x=y)"
  proof(intro impI ballI)
    fix x y assume A2[ty]: "S is trivial-struct" "x be Element-of-struct S" "y be Element-of-struct S"
    have A3: "the carrier of S is trivial" using struct_0_def_9E A2 by ty_auto
    show "x=y"
    proof (cases "the carrier of S={}")
      case True
        hence "x={}" "y={}" using A2(2,3) Element(5)  by auto
        thus ?thesis by simp
    next
      case False
        hence "x in_struct S" "y in_struct S" using Element_of_rule2 by mauto
        thus ?thesis using zfmisc_1_def_10 A3 by mauto
      qed
  qed mauto
  assume A4: "for x, y be Element-of-struct S holds x=y"
  show "S is trivial-struct"
  proof(intro struct_0_def_9I)
    show "(the carrier of S) is trivial"
      proof(standard,auto)
        fix x y assume "x in_struct S" "y in_struct S"
        hence "x be Element-of-struct S" "y be Element-of-struct S" using Element_of_rule3 by mauto
        thus "x=y" using A4 by auto
     qed mauto
  qed mauto
qed mauto

mdef struct_0_def_12 ("Zero \<^sub>_" [190] 190)where
mlet   "S be ZeroStr"
"attr Zero \<^sub>S for Element-of-struct S means (\<lambda> IT.  IT = 0\<^sub>S )".

mtheorem struct_0_cl_10:
  mlet "S be ZeroStr"
  "cluster 0\<^sub>S \<rightarrow> Zero \<^sub>S" using struct_0_def_12I[of S "0\<^sub>S"] by mauto

mtheorem struct_0_cl_11:
  "cluster strict (ZeroOneStr) \<bar> non degenerated for ZeroOneStr"
proof(standard,standard)
  let ?c = "carrier \<rightarrow> set'"
  let ?z = "ZeroF \<rightarrow> Element-of' the' carrier"
  let ?o = "OneF \<rightarrow> Element-of' the' carrier"
  let ?x = "the set"
  let ?X ="[#carrier \<mapsto> ({?x}\<union>{{?x}}) ; ZeroF \<mapsto> ?x ;OneF\<mapsto> {?x} #]"
  
  have T2[ty]: "?x be Element-of ({?x}\<union>{{?x}})" "{?x} be Element-of ({?x}\<union>{{?x}})"
    using Element(6) tarski_def_1 xboole_0_def_3 by mauto
  have S3[ty]: "?X is strict(ZeroOneStr)" by mauto
         have "the ZeroF of ?X = ?x " "the OneF of ?X = {?x} "
          using the_selector_of_1[of _ ZeroF ?x] the_selector_of_1[of _ OneF "{?x}"] aggr by mauto
        hence "0\<^sub>?X = ?x" "1\<^sub>?X={?x}" using struct_0_def_7 struct_0_def_6 S3 by ty_auto
        hence "0\<^sub>?X in 1\<^sub>?X" using tarski_def_1 by auto
        hence "0\<^sub>?X \<noteq> 1\<^sub>?X" using prefix_in_irreflexive all_set by auto
        thus "?X is strict (ZeroOneStr)\<bar> non degenerated\<bar>ZeroOneStr" using struct_0_def_8 S3 by ty_auto
qed


text_raw {*\DefineSnippet{struct_0_cl_12}{*}
mtheorem struct_0_cl_12:
  mlet "S be non degenerated \<bar> ZeroOneStr"
  "cluster 1\<^sub>S \<rightarrow> non Zero \<^sub>S"
text_raw {*}%EndSnippet*}
proof
  have "1\<^sub>S \<noteq> 0\<^sub>S" using struct_0_def_8[of S] by ty_auto
  thus "1\<^sub>S is non Zero \<^sub>S" using struct_0_def_12 by mauto
qed

abbreviation struct_of_mode_11_prefix ("BinOp-of-struct _ " 60)
  where "BinOp-of-struct X \<equiv> BinOp-of (the carrier of X)"


abbreviation struct_of_mode_12_prefix ("UnOp-of-struct _ " 60)
  where "UnOp-of-struct X \<equiv> BinOp-of (the carrier of X)"

(* :: "(Set\<Rightarrow>Set)\<Rightarrow>Set\<Rightarrow>Mode"*)
text_raw {*\DefineSnippet{BinOfP}{*}
abbreviation(input) BinOp_of ("BinOp-of'' _") where
  "BinOp-of' X \<equiv> \<lambda>it. BinOp-of X(it)"
text_raw {*}%EndSnippet*}

abbreviation(input) Subset_Falmily_of :: "(Set \<Rightarrow> Set) \<Rightarrow> (Set \<Rightarrow> Ty)" ("Subset-Family-of'' _") where
  "Subset-Family-of' X \<equiv> \<lambda>it. Subset-Family-of X(it)"

abbreviation(input) Function_of :: "(Set \<Rightarrow> Set) \<Rightarrow> (Set \<Rightarrow> Set) \<Rightarrow> (Set \<Rightarrow> Ty)" ("Function-of'' _ , _") where
  "Function-of' X, Y\<equiv> \<lambda>it. Function-of X(it), Y(it)"

abbreviation(input) cartesian_product1 :: "Set \<Rightarrow> (Set \<Rightarrow> Set) \<Rightarrow> (Set \<Rightarrow> Set)" ("[: _ , _ '':]") where
  "[: X, Y ':] \<equiv> \<lambda>it. [: X, Y(it):]"

abbreviation(input) cartesian_product2 :: "(Set \<Rightarrow> Set) \<Rightarrow> Set \<Rightarrow> (Set \<Rightarrow> Set)" ("[:'' _ , _ :]") where
  "[:' X, Y :] \<equiv> \<lambda>it. [: X(it), Y:]"

mdef struct_0_def_19_a ("1-element-struct")where
  "attr 1-element-struct for 1-sorted means (\<lambda> IT. ex x be object st {x} = the carrier of IT)".

mtheorem struct_0_redef_1:
  mlet "S be non empty-struct\<bar>1-sorted",
       "x be Element-of-struct S"
   "redefine func {x} \<rightarrow> Subset-of-struct S"
proof (standard)
  have [ty]:"S is 1-sorted" by ty_auto
  have "the carrier of S is non empty" using struct_0_def_1 by ty_auto
  hence "x in the carrier of S" using Element(7) by ty_auto
  hence "{x} c= the carrier of S" using tarski_def_3 tarski_def_1 by mauto
  thus "{x} be Subset-of-struct S" using Subset_of_rule by auto
qed


text_raw {*\DefineSnippet{struct_0_redef_2}{*}
mtheorem struct_0_redef_2:
  mlet "S be non empty-struct\<bar>1-sorted",
       "x be Element-of-struct S","y be Element-of-struct S"
   "redefine func {x,y} \<rightarrow> Subset-of-struct S"
text_raw {*}%EndSnippet*}
proof 
  have "the carrier of S is non empty" using struct_0_def_1 by ty_auto
  hence "x in the carrier of S" " y in the carrier of S" using Element(7)[of "the carrier of S"]  by ty_auto
  hence "{x,y} c= the carrier of S" using tarski_def_2 by (intro tarski_def_3I) mauto
  thus "{x,y} be Subset-of-struct S" using Subset_of_rule by auto
qed

  
mtheorem struct_0_cl_triv:
  "cluster non trivial-struct \<rightarrow> non empty-struct for 1-sorted"
proof(standard,standard,standard,standard,simp)
  fix X assume [ty]:"X is 1-sorted" "X is non trivial-struct"
  have "the carrier of X is non trivial" using struct_0_def_9 by mauto
  then obtain x y where
       "x be object" "y be object"
       "x in the carrier of X \<and> x in the carrier of X \<and> x\<noteq>y" using zfmisc_1_def_10 by mauto
  thus "\<not> the carrier of X is empty" using xboole_0_def_1E by mauto
qed mauto
  
mtheorem struct_0_cl_empty:
  "cluster 1-element-struct \<rightarrow> non empty-struct for 1-sorted"
proof(standard,standard,standard,standard,simp)
  fix it assume [ty]:"it is 1-sorted" "it is 1-element-struct" 
  obtain x where "x be object" and 
     A1: " {x} = the carrier of it" using struct_0_def_19_a by mauto
  have "{x} is non empty" by mauto
  thus "\<not> the carrier of it is empty" using A1 by auto   
qed mauto 
  

mdef struct_0_def_17 ("NonZero \<^sub>_" [1000] 99) where
  mlet "S be ZeroStr"
  "func NonZero \<^sub>S \<rightarrow> Subset-of-struct S equals ([#]S) \\ {0\<^sub>S}"
proof-
  have A1:"([#]S) be Subset-of-struct S" using struct_0_def_3[of S] Subset_of_rule xboole_0_def_10 by mauto
  have "(([#]S) \\ {0\<^sub>S}) be Subset-of ([#]S)" using Subset_of_rule xboole_0_def_5[of "[#]S" "{0\<^sub>S}"]
         tarski_def_3[of "([#]S) \\ {0\<^sub>S}" "[#]S"] by mauto
  thus "(([#]S) \\ {0\<^sub>S}) be Subset-of-struct S" using A1 Subset_trans[OF _ A1] by auto
qed


mdef two_sorted ("2-sorted") where
  "struct [1-sorted] 2-sorted (#
      carrier \<rightarrow> set' ;
      carrier` \<rightarrow> set'#) defined on {carrier}\<union>{carrier`}"
  by (auto simp add:one_sorted,auto intro!: Fields_add_3_arg_Mode First_0_arg_Mode dest!:field_E simp add:string)    

mtheorem
  mlet "X be set", "X1 be set"
  "cluster [#carrier\<mapsto>X;carrier` \<mapsto> X1#] \<rightarrow> strict(2-sorted)"
unfolding two_sorted_def
    by (auto, rule struct_aggr_ancesors_rule,
         auto intro!: aggrI struct_aggr3  struct_aggr0 Fields_add_3_arg_Mode First_0_arg_Mode dest!:field_E simp add:string) ty_auto

mtheorem
  mlet "X be 2-sorted"
  "cluster (the carrier` of X) \<rightarrow> set" 
  using field two_sortedE by ty_auto

  
mdef struct_0_def_13 ("void-struct")where
   "attr void-struct for 2-sorted means (\<lambda> IT. (the carrier` of IT) is empty)".

mtheorem struct_0_cl_x:
  mlet "S be (non void-struct \<bar> 2-sorted)"
  "cluster (the carrier` of S) \<rightarrow> non empty" 
using struct_0_def_13[of S] by ty_auto
   
text_raw {*\DefineSnippet{struct_contrE}{*}
mdef I_one_sorted :: "Ty"  ("Inhabited'_1-sorted") where
  "struct Inhabited_1-sorted (# carrier \<rightarrow>  (\<lambda>S. non empty\<bar>set) #) defined on {carrier}"
text_raw {*}%EndSnippet*}
  by (auto intro!: Fields_add_3_arg_Mode First_0_arg_Mode dest!:field_E simp add:string)

mtheorem
  mlet "S be Inhabited_1-sorted"
   "cluster the carrier of S \<rightarrow> non empty\<bar> set" 
using field I_one_sortedE by mauto

text_raw {*\DefineSnippet{struct_contr1a}{*}
theorem
  "X be Inhabited_1-sorted \<Longrightarrow> X be 1-sorted"
  "X be non empty-struct\<bar>1-sorted \<Longrightarrow> X be Inhabited_1-sorted"
text_raw {*}%EndSnippet*}
proof-
  assume [ty]: "X be Inhabited_1-sorted"
  hence "X is (carrier \<rightarrow>  (\<lambda>S. non empty\<bar>set))" using I_one_sorted[of X] by auto+
  hence "(the carrier of X) is non empty\<bar>set" "carrier in dom X" using field by simp+
  thus "X is 1-sorted" using one_sorted field by ty_auto
next
  assume [ty]:"X be non empty-struct\<bar>1-sorted"
  hence [ty]: "the carrier of X is non empty" by mauto
  have "X is (carrier \<rightarrow>  (\<lambda>S. set))" using one_sorted[of X] by ty_auto
  hence "(the carrier of X) is set" "carrier in dom X" using field by simp+
  hence "X is (carrier \<rightarrow>  (\<lambda>S. non empty\<bar>set))" using field by ty_auto
  thus "X is Inhabited_1-sorted" using I_one_sorted field by ty_auto
qed


text_raw {*\DefineSnippet{struct_contr1b}{*}
mdefinition Test where
  "struct Test (# testA \<rightarrow> (\<lambda>T. Element-of the testB of T);
                     testB \<rightarrow> (\<lambda>T. Element-of the testA of T) #)":
   struct_scheme[of _ _ "{testA}\<union>{testB}"]
text_raw {*}%EndSnippet*}
proof-
  let ?A = "testA \<rightarrow> (\<lambda>T . Element-of the testB of T)"
  let ?B = "testB \<rightarrow> (\<lambda>T . Element-of the testA of T)"
  let ?AB = "{testA}\<union>{testB}"
  show "\<exists>\<^sub>L X . X be (#?A;?B #)\<bar>Struct \<and> dom X = ?AB"
  proof (intro exI)
    let ?ab = "[# testA\<mapsto>{};testB \<mapsto>{} #]"
     have [ty]:"?ab is Struct" using Struct_2[of testA testB "{}" "{}"] string by auto
     have A1: "[testA,{}] in ?ab" "[testB,{}] in ?ab" using aggr by auto
     hence A2: "the testA of ?ab = {}" "the testB of ?ab = {}" using the_selector_of_1 by mauto
     have A4: "{} is Element-of {}" using Element_of_rule1 by simp
     have A3:"dom ?ab = ?AB" using Dom_2 by auto
     hence "testA in dom ?ab" "testB in dom ?ab" using string by auto
     hence "?ab be ?A" "?ab be ?B" using A4 field A2 by auto
     thus "?ab be (#?A;?B #)\<bar>Struct\<and>dom ?ab = ?AB" using A3 by ty_auto
    qed
    show "\<forall>\<^sub>L X1. X1 be (#?A;?B#)\<bar>Struct \<longrightarrow> ?AB \<subseteq> dom X1"
      proof(standard,standard)
         fix X1
         assume [ty]:"X1 be (#?A;?B#)\<bar>Struct"
         hence A1: "testA in dom X1" "testB in dom X1" using field by auto
         have [ty]: "X1 be Function" using Struct_def by mauto
         show "?AB \<subseteq> dom X1"
         proof(standard,auto)
           fix x assume "x in {testA} \<union> {testB}"
           hence "x=testA \<or> x=testB" using tarski_def_1 xboole_0_def_3 by mauto
           thus "x in dom X1" using A1 by mauto
         qed mauto
      qed
  show "\<forall>\<^sub>L X1. X1 be (#?A;?B#)\<bar>Struct \<longrightarrow> X1|?AB is (#?A;?B#)"
      proof(standard,standard)
        fix X1
        assume A1[ty]: "X1 be (#?A;?B#)\<bar>Struct"
        have G1: "testA in ?AB" "testB in ?AB" using tarski_def_1 xboole_0_def_3 all_set by auto
        have "testA in dom X1" "testB in dom X1" using A1 field[of X1 testA "\<lambda>T . Element-of the testB of T"]
                                        field[of X1 testB "\<lambda>T . Element-of the testA of T"] by auto
        hence "(the' testA)(X1) = (the' testA)(X1|?AB)"
              "(the' testB)(X1) = (the' testB)(X1|?AB)" using the_selector_of_restriction[of X1 _ ?AB] G1 by mauto
        thus "(X1 | ?AB) is (#?A;?B#)" using A1 G1 fields_restriction by simp
     qed
qed

lemmas [ex] = Test(2,3)


text_raw {*\DefineSnippet{struct_contr3}{*}
theorem "\<forall>T:Test. the testA of T = {} \<and> the testB of T = {}"
text_raw {*}%EndSnippet*}
proof(standard,standard)
  fix T
  assume A1:"T be Test"
  hence A2: "the testA of T is Element-of the testB of T"
            "the testB of T is Element-of the testA of T" using field Test by auto
  show "the testA of T ={}"
    proof (rule ccontr)
      assume A3: "the testA of T \<noteq> {}"
      hence A4: "the testB of T in the testA of T" using Element_of_rule2 A2 all_set by auto
      have "the testB of T \<noteq> {}" using Element_of_rule[of "the testA of T"] A2(1) A3 by auto
      hence "the testA of T in the testB of T" using Element_of_rule2 A2 all_set by auto
      thus "False" using prefix_in_asymmetry all_set A4 by mauto
    qed
  show "the testB of T ={}"
    proof (rule ccontr)
      assume A3: "the testB of T \<noteq> {}"
      hence A4: "the testA of T in the testB of T" using Element_of_rule2 A2 all_set by auto
      have "the testA of T \<noteq> {}" using Element_of_rule[of "the testB of T"] A2(2) A3 by auto
      hence "the testB of T in the testA of T" using Element_of_rule2 A2 all_set by auto
      thus "False" using prefix_in_asymmetry all_set A4 by auto
    qed
  qed mauto

mdef struct_0_def_21 ("trivial`-struct")where
   "attr trivial`-struct for 2-sorted means (\<lambda> S. the carrier` of S is trivial)".


mtheorem struct_0_def_21R:
  "redefine attr trivial`-struct for 2-sorted means
       \<lambda>S. for x, y be Element-of the carrier` of S holds x=y"
proof(standard,rule ballI ,rule iffI3)
  fix S assume [ty]:"S be 2-sorted"
  show "S is trivial`-struct \<longrightarrow> (for x, y be Element-of the carrier` of S holds x=y)"
  proof(intro impI ballI)
    fix x y assume A2[ty]: "S is trivial`-struct" "x be Element-of the carrier` of S" "y be Element-of the carrier` of S"
    have A3: "the carrier` of S is trivial" using struct_0_def_21E A2 by ty_auto
    show "x=y"
    proof (cases "the carrier` of S={}")
      case True
        hence "x={}" "y={}" using A2(2,3) Element(5)  by auto
        thus ?thesis by simp
    next
      case False
        hence "x in the carrier` of S" "y in the carrier` of S" using Element_of_rule2 by mauto
        thus ?thesis using zfmisc_1_def_10 A3 by mauto
      qed
  qed mauto
  assume A4: "for x, y be Element-of the carrier` of S holds x=y"
  show "S is trivial`-struct"
  proof(intro struct_0_def_21I)
    show "(the carrier` of S) is trivial"
      proof(standard,auto)
        fix x y assume "x in the carrier` of S" "y in the carrier` of S"
        hence "x be Element-of the carrier` of S" "y be Element-of the carrier` of S" using Element_of_rule3 by mauto
        thus "x=y" using A4 by auto
     qed mauto
  qed mauto
qed mauto

end
