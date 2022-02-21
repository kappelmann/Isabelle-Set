theory Poly_Rat
  imports Rational
begin

hide_type set
unbundle
  no_notation_rat_div

lemma h1: "(\<And>x. x : s \<Longrightarrow> x : t) \<Longrightarrow> (\<And>x. x : t \<Longrightarrow> x : s) \<Longrightarrow> s = t"
  using meaning_of_type
  sorry

lemma function'_type: "Element (functions a b) = (Element a) \<rightarrow>c (Element b)"
  by (rule h1) (auto dest: ElementD intro: ElementI)

definition "poly_rat_rep = functions \<nat> \<rat>"

definition rat_in_poly_rat :: \<open>set \<Rightarrow> set\<close>
  where "rat_in_poly_rat x = (\<lambda>n\<in>\<nat>. if n = 0 then x else 0)"


lemma [type]: "rat_in_poly_rat: Element \<rat> \<Rightarrow> Element poly_rat_rep"
  unfolding poly_rat_rep_def rat_in_poly_rat_def
  apply unfold_types
  by (auto 0 3 iff: mem_dep_functions_iff_CDep_Function)

interpretation Poly_Rat: set_extension \<rat> poly_rat_rep rat_in_poly_rat
proof
  show "rat_in_poly_rat : Rat \<Rightarrow> Element poly_rat_rep"
    by simp
  { fix x y
    assume assms: "x \<in> \<rat>" "y \<in> \<rat>"
      "(\<lambda>n \<in> \<nat>. if n = 0 then x else 0) = (\<lambda>n \<in> \<nat>. if n = 0 then y else 0)"
    have "x = y" sorry
  }
  note 1 = this
  show " \<forall>x \<in> \<rat>.
      \<forall>y \<in> \<rat>. rat_in_poly_rat x = rat_in_poly_rat y \<longrightarrow> x = y"
    unfolding rat_in_poly_rat_def
    using 1 by blast
qed

abbreviation "poly_rat \<equiv> Poly_Rat.abs_image"
abbreviation "Poly_Rat \<equiv> Element poly_rat"

term "type_definition Poly_Rat.Rep Poly_Rat.Abs poly_rat_rep"

lemmas rat_subset_poly_rat [simp] = Poly_Rat.subset_abs_image

corollary [derive]: "x : Rat \<Longrightarrow> x : Poly_Rat"
  apply unfold_types
  apply (rule mem_if_mem_if_subset)
  using rat_subset_poly_rat by blast

definition "poly_rat_rep_add p q = (\<lambda>n\<in>\<nat>. p`n + q`n)"

definition "poly_rat_rep_neg p = (\<lambda>n\<in>\<nat>. 0 - (p`n))"

definition "poly_rat_rep_coeffs p = rng p"

definition "poly_rat_rep_zero = (\<lambda>n\<in>\<nat>. 0)"

lemma poly_rat_rep_zero_type: "poly_rat_rep_zero \<in> poly_rat_rep"
  unfolding poly_rat_rep_zero_def poly_rat_rep_def
  by (auto iff: mem_dep_functions_iff_CDep_Function)

lemma poly_rat_rep_add_type: "p \<in> poly_rat_rep \<Longrightarrow> q \<in> poly_rat_rep \<Longrightarrow> poly_rat_rep_add p q \<in> poly_rat_rep"
  sorry

lemma "p \<in> poly_rat_rep \<Longrightarrow> q \<in> poly_rat_rep \<Longrightarrow> poly_rat_rep_add p q \<in> poly_rat_rep"
  unfolding poly_rat_rep_def poly_rat_rep_add_def
  using rat_add_type eval_type function'_type
  (* by (auto iff: mem_dep_functions_iff_CDep_Function intro!: Dep_fun_typeI) *)
  sorry

lemma poly_rat_zero_add_rep: "p \<in> poly_rat_rep \<Longrightarrow> poly_rat_rep_add poly_rat_rep_zero p = p"
  unfolding poly_rat_rep_zero_def poly_rat_rep_add_def poly_rat_rep_def
  sorry

lemma poly_rat_rep_add_comm: "p \<in> poly_rat_rep \<Longrightarrow> q \<in> poly_rat_rep \<Longrightarrow> poly_rat_rep_add p q = poly_rat_rep_add q p"
  unfolding poly_rat_rep_add_def poly_rat_rep_def
  using rat_add_comm
  sorry

lemma poly_rat_rep_add_neg: "p \<in> poly_rat_rep \<Longrightarrow> poly_rat_rep_add p (poly_rat_rep_neg p) = poly_rat_rep_zero"
  sorry

definition "poly_rat_add p q = Poly_Rat.Abs (poly_rat_rep_add (Poly_Rat.Rep p) (Poly_Rat.Rep q))"

definition "poly_rat_neg p = Poly_Rat.Abs (poly_rat_rep_neg (Poly_Rat.Rep p))"

definition "poly_rat_coeffs p = poly_rat_rep_coeffs (Poly_Rat.Rep p)"

lemma poly_rat_add_type [type]: "poly_rat_add: Poly_Rat \<Rightarrow> Poly_Rat \<Rightarrow> Poly_Rat"
  sorry

lemma poly_rat_neg_type [type]: "poly_rat_neg: Poly_Rat \<Rightarrow> Poly_Rat"
  sorry

bundle notation_poly_rat_add begin notation poly_rat_add (infixl "+" 65) end
bundle no_notation_poly_rat_add begin no_notation poly_rat_add (infixl "+" 65) end

unbundle
  no_notation_rat_add
  notation_poly_rat_add

definition "Poly_Rat_Rel p_rep p \<equiv> p \<in> Poly_Rat.abs_image \<and> Poly_Rat.Rep p = p_rep"

lemma zero_in_rat: "0 \<in> \<rat>"
  using Rat_Rel_0 Rat_Rel_def by blast

lemma Poly_Rat_Rel_0 [transfer_rule]: "Poly_Rat_Rel poly_rat_rep_zero 0"
proof -
  have "Poly_Rat.Rep 0 = poly_rat_rep_zero"
    unfolding Poly_Rat.Rep_def poly_rat_rep_zero_def rat_in_poly_rat_def
    by (simp add: zero_in_rat)
  moreover have "0 \<in> poly_rat"
    unfolding Poly_Rat.abs_image_def
    by (simp add: zero_in_rat)
  ultimately show ?thesis
    unfolding Poly_Rat_Rel_def
    by blast
qed

lemma Poly_Rel_eq [transfer_rule]: "(Poly_Rat_Rel ===> Poly_Rat_Rel ===> (=)) (=) (=)"
  unfolding rel_fun_def Poly_Rat_Rel_def Poly_Rat.Rep_def Poly_Rat.abs_image_def
  by (metis Poly_Rat.Rep_def Poly_Rat.Abs_Rep_inv Poly_Rat.abs_image_def)

lemma Poly_Rel_add [transfer_rule]: "(Poly_Rat_Rel ===> Poly_Rat_Rel ===> Poly_Rat_Rel) poly_rat_rep_add poly_rat_add"
  unfolding  rel_fun_def Poly_Rat_Rel_def
  using poly_rat_add_def Poly_Rat.Rep_Abs_inv poly_rat_add_type
  sorry

lemma Poly_Rel_neg [transfer_rule]: "(Poly_Rat_Rel ===> Poly_Rat_Rel) poly_rat_rep_neg poly_rat_neg"
  unfolding  rel_fun_def Poly_Rat_Rel_def
  using poly_rat_neg_def Poly_Rat.Rep_Abs_inv poly_rat_neg_type mem_iff_Element Dep_fun_typeE
  by metis

lemma Poly_Rel_All [transfer_rule]:
  "((Poly_Rat_Rel ===> (=)) ===> (=)) (ball poly_rat_rep) (ball poly_rat)"
  unfolding rel_fun_def Poly_Rat_Rel_def
  sorry

lemma "\<forall>p\<in>poly_rat. 0 + p = p"
  apply transfer
  by (simp add: poly_rat_zero_add_rep)

lemma poly_rat_add_comm: "\<forall>p\<in>poly_rat. \<forall>q\<in>poly_rat. poly_rat_add p q = poly_rat_add q p"
  apply transfer
  by (simp add: poly_rat_rep_add_comm)

lemma poly_rat_add_neg: "\<forall>p\<in>poly_rat. poly_rat_add p (poly_rat_neg p) = 0"
  apply transfer
  by (simp add: poly_rat_rep_add_neg)

lemma "\<forall>p\<in>poly_rat. p + 0 = p"
  apply transfer
  using poly_rat_zero_add_rep poly_rat_rep_add_comm poly_rat_rep_zero_type
  by simp

lemma "\<forall>p\<in>poly_rat. p + (p + (poly_rat_neg p)) = p"
  apply transfer
  using poly_rat_rep_add_neg poly_rat_zero_add_rep poly_rat_rep_add_comm poly_rat_rep_add_type poly_rat_rep_zero_type
  by simp

lemma "\<forall>p\<in>poly_rat. \<forall>q\<in>poly_rat. p = q \<longrightarrow> poly_rat_add p (poly_rat_neg q) = 0"
  apply transfer
  using poly_rat_rep_add_neg by force

definition "Poly_Int = (\<lambda>p. poly_rat_coeffs p \<subseteq> \<int>) \<sqdot> Poly_Rat"

lemma rng_lambdaI: "(\<And>x. x \<in> A \<Longrightarrow> f x \<in> B) \<Longrightarrow> rng (lambda A f) \<subseteq> B"
  by blast

lemma Int_is_Poly_Int:
  assumes "i : Integers.Int"
  shows "i : Poly_Int"
proof -
  let ?poly_int = "{p \<in> poly_rat | poly_rat_coeffs p \<subseteq> \<int>}"
  let ?p = "\<lambda>n \<in> \<nat>. if n = 0 then i else 0"
  have zero_in_int: "0 \<in> \<int>" by simp
  have i_in_int: "i \<in> \<int>" by simp
  have i_in_poly_rat: "i \<in> poly_rat"
    using i_in_int rat_subset_poly_rat int_subset_rat by blast
  have "i \<in> \<rat>" by simp
  hence "Poly_Rat.Rep i = rat_in_poly_rat i"
    using Poly_Rat.Rep_def by simp
  moreover have "rat_in_poly_rat i = ?p"
    using rat_in_poly_rat_def by simp
  ultimately have "poly_rat_coeffs i \<subseteq> \<int>"
    using zero_in_int i_in_int poly_rat_coeffs_def poly_rat_rep_coeffs_def rng_lambdaI by simp
  with i_in_poly_rat have "i \<in> ?poly_int" by simp
  thus ?thesis
    using Poly_Int_def mem_iff_Element meaning_of_adj mem_collect_iff by metis
qed

lemma "(\<And>p. p : Poly_Int \<Longrightarrow> P p) \<Longrightarrow> i : Integers.Int \<Longrightarrow> P i"
  using Int_is_Poly_Int by blast



lemma "(Poly_Rat_Rel ===> Poly_Rat_Rel ===> Poly_Rat_Rel) poly_rat_rep_add poly_rat_add"
  unfolding  rel_fun_def Poly_Rat_Rel_def
  apply atomize_rev'
  apply (rule conjI)
    (* drop non-relevant part of premises *)
   apply (drule conjE)+
  unfolding poly_rat_add_def
    (* make goal more readable *)
   apply(rule Dep_fun_typeE[OF _ Poly_Rat.Abs_type])
   apply (rule l1[OF _ Rep_surj[OF Poly_Rat.set_extension_axioms]], assumption)
   apply (rule l1[OF _ Rep_surj[OF Poly_Rat.set_extension_axioms]], assumption)
    (* clean up premises *)
   apply (erule HOL.cnf.weakening_thm)
   apply (erule HOL.cnf.weakening_thm)
   defer
    (* prove second goal *)
  unfolding Poly_Rat.Rep_Abs_inv
   apply (erule conjE')+
   apply (erule subst')+
   apply (rule refl)
  sorry

end