theory Transfer_Test_T
imports
  Isabelle_Set.Integers
  Trans.Trans
  HOL.Sledgehammer
begin

(* resolve name clashes *)
no_syntax "_Bex" :: "pttrn \<Rightarrow> 'a set \<Rightarrow> bool \<Rightarrow> bool" ("(3\<exists>(_/\<in>_)./ _)" [0, 0, 10] 10)
no_notation Set.member ("(_/ : _)" [51, 51] 50)
no_notation Set.member  ("'(\<in>')")
no_notation Set.member ("(_/ \<in> _)" [51, 51] 50)
no_notation Set.empty ("{}")
no_syntax "_Finset" :: "args \<Rightarrow> 'a set" ("{(_)}")
no_syntax "_UNION" :: "pttrn => 'a set => 'b set => 'b set"  ("(3\<Union>_\<in>_./ _)" [0, 0, 10] 10)
no_notation BNF_Def.convol ("\<langle>(_,/ _)\<rangle>")
no_notation Product_Type.Times (infixr "\<times>" 80)
no_notation Nat.Nats ("\<nat>")
no_notation Int.ring_1_class.Ints ("\<int>")
no_notation Groups.plus_class.plus (infixl "+" 65)
no_notation Groups.zero_class.zero ("0")
hide_fact sumE
hide_const fst snd
hide_const Nat nat
notation rel_fun  (infixr "===>" 55)

lemma Int_Rep_mul_inj_1:
  assumes assms: "i \<in> int_rep" "i' \<in> int_rep" "j \<in> int_rep \<setminus> Int_Rep_nonneg 0"
    "Int_Rep_mul i j = Int_Rep_mul i' j"
  shows "i = i'"
  sorry

lemma Int_Rep_mul_inj_2:
  assumes assms: "i \<in> int_rep" "i' \<in> int_rep" "j \<in> int_rep \<setminus> Int_Rep_nonneg 0"
    "Int_Rep_mul j i = Int_Rep_mul j i'"
  shows "i = i'"
  sorry

definition "Int_Rep_div i j \<equiv> (THE k. k \<in> int_rep \<and> Int_Rep_mul j k = i)"

lemma
  assumes i: "i \<in> int_rep"
    and j: "j \<in> (int_rep \<setminus> Int_Rep_nonneg 0)"
    and exists_k: "\<exists>k\<in>int_rep. i = Int_Rep_mul j k"
  shows "Int_Rep_div i j \<in> int_rep"
proof -
  let ?k = "(THE k. k \<in> int_rep \<and> Int_Rep_mul j k = i)"
  obtain k where k: "k \<in> int_rep \<and> Int_Rep_mul j k = i"
    using exists_k by blast
  have k_in_int_rep: "?k \<in> int_rep"
    using k Int_Rep_mul_inj_2[of k _ j] theI[of _ k]
    by (smt (verit, ccfv_threshold) j)
  show ?thesis
    unfolding Int_Rep_div_def
    using k_in_int_rep .
qed

definition "int_div i j \<equiv> Int.Abs (Int_Rep_div (Int.Rep i) (Int.Rep j))"

definition "divides_rep i j \<equiv> (\<exists>k. Int_Rep_mul k j = i)"

definition "divides i j \<equiv> divides_rep (Int.Rep i) (Int.Rep j)"

lemma Int_Rep_div_type [type]:
  "Int_Rep_div : (i : Int_Rep) \<Rightarrow> (Int_Rep & type (divides_rep i)) \<Rightarrow> Int_Rep"
  apply unfold_types
  unfolding Int_Rep_div_def
  sorry

lemma int_div_type [type]:
  "int_div : (i : Integers.Int) \<Rightarrow> (Int_Rep & type (divides_rep i)) \<Rightarrow> Integers.Int"
  apply unfold_types
  unfolding int_div_def
  using Int_Rep_div_type
  sorry

definition "int_rep_pow n i \<equiv> nat_rec n (Int_Rep_nonneg 0) (Int_Rep_mul i)"
definition "int_pow n i \<equiv> Int.Abs (int_rep_pow n (Int.Rep i))"

(* transfer relation *)
definition "Int_Rel i_rep i \<equiv> i \<in> Int.abs_image \<and> Int.Rep i = i_rep"

(* transfer rules *)
lemma bi_unique_Int_Rel [trans_rule]: "bi_unique Int_Rel"
  unfolding Int_Rel_def bi_unique_def
  using Int.Abs_Rep_inv by fastforce

lemma Int_Rel_0 [trans_rule]: "Int_Rel (Int_Rep_nonneg 0) 0"
  unfolding Int.Rep_def Int_Rel_def Int.abs_image_def
  by (simp add: int_rep_def)

lemma Int_Rel_eq [trans_rule]: "(Int_Rel → Int_Rel → (=)) (=) (=)"
  unfolding rel_fun_def Int_Rel_def Int.Rep_def Int.abs_image_def
  by auto

lemma
  shows int_add_type [type]: "int_add : Integers.Int \<Rightarrow> Integers.Int \<Rightarrow> Integers.Int"
  and int_sub_type [type]: "int_sub : Integers.Int \<Rightarrow> Integers.Int \<Rightarrow> Integers.Int"
  and int_mul_type [type]: "int_mul : Integers.Int \<Rightarrow> Integers.Int \<Rightarrow> Integers.Int"
  sorry

lemma Int_Rel_add [trans_rule]: "(Int_Rel → Int_Rel → Int_Rel) Int_Rep_add int_add"
  unfolding rel_fun_def Int_Rel_def
  using int_add_def Int.Rep_Abs_inv int_add_type
  by (metis (no_types, lifting) ElementD ElementI Dep_fun_typeE)

lemma Int_Rel_sub [trans_rule]: "(Int_Rel → Int_Rel → Int_Rel) Int_Rep_sub int_sub"
  unfolding  rel_fun_def Int_Rel_def
  using int_sub_def Int.Rep_Abs_inv int_sub_type
  by (metis (no_types, lifting) ElementD ElementI Dep_fun_typeE)

lemma Int_Rel_mul [trans_rule]: "(Int_Rel → Int_Rel → Int_Rel) Int_Rep_mul int_mul"
  unfolding  rel_fun_def Int_Rel_def
  using int_mul_def Int.Rep_Abs_inv int_mul_type
  by (metis (no_types, lifting) ElementD ElementI Dep_fun_typeE)

lemma Int_Rel_div [trans_rule]: "(Int_Rel → Int_Rel → Int_Rel) Int_Rep_div int_div"
  unfolding  rel_fun_def Int_Rel_def
  using int_div_def Int.Rep_Abs_inv
  oops

lemma divides_mul_rep: "divides_rep (Int_Rep_mul i j) j"
  unfolding divides_rep_def by blast

lemma Int_Rel_mul': "Int_Rel i i' \<Longrightarrow> Int_Rel j j' \<Longrightarrow> Int_Rel (Int_Rep_mul i j) (int_mul i' j')"
  unfolding  rel_fun_def Int_Rel_def
  using int_mul_def Int.Rep_Abs_inv int_mul_type
  sorry

lemma Int_Rel_div [trans_rule]: "Int_Rel i i' \<Longrightarrow> Int_Rel j j' \<Longrightarrow> divides_rep i j \<Longrightarrow> Int_Rel (Int_Rep_div i j) (int_div i' j')"
  unfolding  rel_fun_def Int_Rel_def divides_rep_def
  using int_div_def Int.Rep_Abs_inv Int_Rep_div_type int_div_type
  sorry

lemma Int_Rel_All [trans_rule]:
  "((Int_Rel → (=)) → (=)) (ball int_rep) (ball \<int>)"
  unfolding rel_fun_def Int_Rel_def
  by (smt (verit, ccfv_threshold) ElementD ElementI Int.Rep_Abs_inv Int.Abs_type
    Int.Rep_type Dep_fun_typeE ball_def)


(* proving theorems by transfer *)
lemma
  assumes "int_rep_add (inl 0) (inl 0) = (inl 0)"
  shows "0 + 0 = 0"
  by trans

lemma
  assumes "\<And>i j. i \<in> int_rep \<Longrightarrow> j \<in> int_rep \<Longrightarrow> int_rep_div (Int_Rep_mul i j) j = i"
  shows "ball \<int> (\<lambda>i. ball \<int> (\<lambda>j. int_div (int_mul i j) j = i))"
  apply trans_start
  apply trans_step
  apply trans_step
  apply trans_step
  apply trans_step
  apply trans_step
  apply trans_step
  apply trans_step
  apply trans_step
  apply (rule divides_mul_rep)
  apply trans_step
  using assms by blast

(* Can't hide notation for bounded universal quantifier from HOL.Set *)
lemma
  assumes "ball int_rep (\<lambda>i. ball int_rep (\<lambda>j. ball int_rep (\<lambda>k .
    Int_Rep_mul i (int_rep_sub j k) = int_rep_sub (Int_Rep_mul k i) (Int_Rep_mul j i))))"
  shows "ball \<int> (\<lambda>i. ball \<int> (\<lambda>j. ball \<int> (\<lambda>k. i \<cdot> (j - k) = (k \<cdot> i) - (j \<cdot> i))))"
  by trans

end