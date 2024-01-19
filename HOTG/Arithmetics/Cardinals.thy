theory Cardinals
  imports 
    SAddition
    Coproduct
    Ordinals
    Transport.Functions_Bijection
    Transport.Equivalence_Relations
begin
term "bijection_on (mem_of X) (mem_of Y) f g"

definition "equipollent X Y \<equiv> \<exists>f g. bijection_on (mem_of X) (mem_of Y) (f :: set \<Rightarrow> set) g"

notation equipollent (infixl "\<approx>" 50)

lemma equipollentI [intro]: 
  assumes "bijection_on (mem_of X) (mem_of Y) (f :: set \<Rightarrow> set) g"
  shows "X \<approx> Y"
  using assms by (auto simp: equipollent_def)

lemma equipollentE [elim]: 
  assumes "X \<approx> Y" 
  obtains f g where "bijection_on (mem_of X) (mem_of Y) (f :: set \<Rightarrow> set) g"
  using assms by (auto simp: equipollent_def)

find_theorems "bijection_on ?X ?X"

lemma reflexive_equipollent: "reflexive equipollent"
  using bijection_on_self_id by auto

lemma equivalence_rel_equipollent: "equivalence_rel equipollent"
  sorry

lemma eqpoll_sym: 
  assumes "A \<approx> B " shows "B \<approx> A"
  using bijection_on_right_left_if_bijection_on_left_right[of "mem_of A" "mem_of B"]
   equipollentE[of A B]  equipollentI[of B A] sorry

lemma eqpoll_trans [trans]: "\<lbrakk>A \<approx> B; B \<approx> C\<rbrakk> \<Longrightarrow> A \<approx> C"
  unfolding equipollent_def
(*about inverse_on P (kf) (gl)*)
  sorry

(*transitive, symmetric, preorder, equivalence relation*)

definition "cardinality (X :: set) \<equiv> (LEAST Y. ordinal Y \<and> X \<approx> Y)"

lemma Least_eq_Least_if_iff:
  assumes "\<And>Z. P Z \<longleftrightarrow> Q Z"
  shows "(LEAST Z. P Z) = (LEAST Z. Q Z)"
  using assms by simp

lemma gcardinal_cong:
  assumes "X \<approx> Y" shows "cardinality X = cardinality Y"
proof -
  have "Y \<approx> X" using assms by (simp add: eqpoll_sym)
  then have left:"\<And>Z. (X \<approx> Z) \<longrightarrow> (Y \<approx> Z)" by (auto simp: eqpoll_trans)
  also have right:"\<And>Z. (Y \<approx> Z) \<longrightarrow> (X \<approx> Z)" using assms by (auto simp: eqpoll_trans)
  with left have "\<And>Z. (X \<approx> Z) \<longleftrightarrow> (Y \<approx> Z)" by auto
  then have "(LEAST Z. ordinal Z \<and> X \<approx> Z) = (LEAST Z. ordinal Z \<and> Y \<approx> Z)"
      using Least_eq_Least_if_iff by auto
  then show ?thesis by (auto simp: cardinality_def)
qed

lemma cardinal_eqpoll: "(cardinality X) \<approx> X"
  unfolding cardinality_def
(*new type needed*)
  sorry

definition "cardinal_add \<kappa> \<mu> \<equiv> cardinality (\<kappa> \<Coprod> \<mu>)"

lemma inl_nonzero [simp]:"inl x \<noteq> {}"
  by (auto simp:inl_def)

lemma inr_nonzero [simp]:"inr x \<noteq> {}"
  by (auto simp:inr_def)

definition is_sum :: "set \<Rightarrow> bool"
  where "is_sum z = (\<exists>X. z = inl X \<or> z = inr X)"

definition sum_case  :: "(set \<Rightarrow> 'a) \<Rightarrow> (set \<Rightarrow> 'a) \<Rightarrow> set \<Rightarrow> 'a"
  where
  "sum_case f g a \<equiv>
    THE z. (\<forall>x. a = inl x \<longrightarrow> z = f x) \<and> (\<forall>y. a = inr y \<longrightarrow> z = g y) \<and> (\<not> is_sum a \<longrightarrow> z = undefined)"
(*why intersection*)

lemma card_lift: "cardinality (lift X Y) = cardinality Y"
proof (rule gcardinal_cong)
  have "bijection_on (mem_of (lift X Y)) (mem_of Y) (f :: set \<Rightarrow> set) g" sorry
  then show "((lift X Y)) \<approx>  Y" 
    by (simp add: equipollentI)
qed

lemma cardinal_disjoint_sup:
  assumes "X \<inter> Y = 0" shows "cardinality (X \<union> Y) = cardinal_add (cardinality X) (cardinality Y)"
proof-
  have "(X \<union> Y)  \<approx> (cardinal_add X Y)" 
    unfolding equipollent_def
  proof(rule exI)
    let ?f = "\<lambda>z. if z \<in> X then inl z else inr z"
    let ?g = "sum_case id id"
    show " \<exists>g. bijection_on (\<lambda>x. x \<in> X \<union> Y) (\<lambda>x. x \<in> cardinal_add X Y) ?f g" sorry
  qed 
  then show ?thesis sorry 
qed

lemma vcard_add: "cardinality (X + Y) = cardinal_add (cardinality X) (cardinality Y)"
  using card_lift [of X Y] bin_inter_lift_self_eq_empty [of X]
  by (simp add: add_eq_bin_union_lift cardinal_disjoint_sup)


(*
  have "bijection_on ((mem_of ({ X + y | y \<in> Y })) (mem_of (lift X Y))) f g"
    unfolding bij_betw_def
    by (simp add: inj_on_def lift_def)
  then show "elts (lift x y) \<approx> elts y"
    using eqpoll_def eqpoll_sym by blast
*)

end