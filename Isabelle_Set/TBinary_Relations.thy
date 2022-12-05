\<^marker>\<open>creator "Josh Chen"\<close>
\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Binary Relations\<close>
theory TBinary_Relations
  imports
    HOTG.SBinary_Relations
    TPairs
begin

subsection \<open>Dependent Binary Relations\<close>

definition [typedef]: "Dep_Bin_Rel A B \<equiv> Collection (\<Sum>x : A. (B x))"

abbreviation "Bin_Rel A B \<equiv> Dep_Bin_Rel A (\<lambda>_. B)"

lemma subset_dep_pairs_iff_Dep_Bin_Rel:
  "R \<subseteq> (\<Sum>x \<in> A. (B x)) \<longleftrightarrow> R : Dep_Bin_Rel (Element A) (\<lambda>x. Element (B x))"
  by unfold_types auto

soft_type_translation
  "R \<subseteq> (\<Sum>x \<in> A. (B x))" \<rightleftharpoons> "R : Dep_Bin_Rel (Element A) (\<lambda>x. Element (B x))"
  using subset_dep_pairs_iff_Dep_Bin_Rel by auto

lemma Dep_Bin_RelI:
  "(\<And>p. p \<in> R \<Longrightarrow> p : \<Sum>x : A. (B x)) \<Longrightarrow> R : Dep_Bin_Rel A B"
  unfolding Dep_Bin_Rel_def by (rule CollectionI)

lemma Dep_Bin_Rel_memE [elim]:
  assumes "R : Dep_Bin_Rel A B"
  and "p \<in> R"
  obtains x y where "x : A" "y : B x" "p = \<langle>x, y\<rangle>"
  using assms unfolding Dep_Bin_Rel_def
  by (auto dest: Collection_memD)

lemma Dep_Bin_Rel_covariant_dom:
  "R : Dep_Bin_Rel A B \<Longrightarrow> (\<And>x. x : A \<Longrightarrow> x : A') \<Longrightarrow> R : Dep_Bin_Rel A' B"
  unfolding Dep_Bin_Rel_def
  by (elim Collection_covariant) (blast intro: Dep_Pair_covariant_fst)

lemma Dep_Bin_Rel_covariant_rng:
  assumes "R : Dep_Bin_Rel A B"
  and "\<And>x y. x : A \<Longrightarrow> y : B x \<Longrightarrow> \<langle>x, y\<rangle> \<in> R \<Longrightarrow> y : B' x"
  shows "R : Dep_Bin_Rel A B'"
  using assms unfolding Dep_Bin_Rel_def
  by (elim Collection_covariant) (auto intro: Dep_Pair_covariant_snd)


subsection \<open>Predicates on Binary Relations\<close>

overloading
  set_injective_on_type \<equiv> "set_injective_on :: set type \<Rightarrow> set \<Rightarrow> bool"
begin
  definition "set_injective_on_type (T :: set type) R \<equiv>
    set_injective_on (type_pred T) R"
end

lemma set_injective_on_type_iff_set_injective_on [iff]:
  "set_injective_on (T :: set type) R \<longleftrightarrow> set_injective_on (type_pred T) R"
  unfolding set_injective_on_type_def by simp

overloading
  set_right_unique_on_type \<equiv> "set_right_unique_on :: set type \<Rightarrow> set \<Rightarrow> bool"
begin
  definition "set_right_unique_on_type (T :: set type) R \<equiv>
    set_right_unique_on (type_pred T) R"
end

lemma set_right_unique_on_type_iff_set_right_unique_on [iff]:
  "set_right_unique_on (T :: set type) R \<longleftrightarrow> set_right_unique_on (type_pred T) R"
  unfolding set_right_unique_on_type_def by simp

overloading
  set_left_total_on_type \<equiv> "set_left_total_on :: set type \<Rightarrow> set \<Rightarrow> bool"
begin
  definition "set_left_total_on_type (T :: set type) R \<equiv>
    set_left_total_on (type_pred T) R"
end

lemma set_left_total_on_type_iff_set_left_total_on [iff]:
  "set_left_total_on (T :: set type) R \<longleftrightarrow> set_left_total_on (type_pred T) R"
  unfolding set_left_total_on_type_def by simp

overloading
  set_surjective_at_type \<equiv> "set_surjective_at :: set type \<Rightarrow> set \<Rightarrow> bool"
begin
  definition "set_surjective_at_type (T :: set type) R \<equiv>
    set_surjective_at (type_pred T) R"
end

lemma set_surjective_at_type_iff_set_surjective_at [iff]:
  "set_surjective_at (T :: set type) R \<longleftrightarrow> set_surjective_at (type_pred T) R"
  unfolding set_surjective_at_type_def by simp


subsection \<open>Functions on Binary Relations\<close>

lemma extend_type [type]:
  "extend : (x : A) \<Rightarrow> B x \<Rightarrow> Dep_Bin_Rel A B \<Rightarrow> Dep_Bin_Rel A B"
  by unfold_types auto

lemma glue_type [type]: "glue : Collection (Dep_Bin_Rel A B) \<Rightarrow> Dep_Bin_Rel A B"
  by unfold_types auto

overloading
  set_restrict_left_type \<equiv> "set_restrict_left :: set \<Rightarrow> set type \<Rightarrow> set"
begin
  definition "set_restrict_left_type R (T :: set type) \<equiv>
    set_restrict_left R (type_pred T)"
end

lemma set_restrict_left_type_eq_set_restrict_left [simp]:
  "set_restrict_left R (T :: set type) = set_restrict_left R (type_pred T)"
  unfolding set_restrict_left_type_def by simp

lemma set_restrict_left_set_eq_set_restrict_left_type [simp]:
  "set_restrict_left R S = set_restrict_left R (Element S)"
  by (auto iff: mem_iff_Element)

lemma set_restrict_left_type [type]:
  "set_restrict_left : Dep_Bin_Rel A B \<Rightarrow> (P : Set \<Rightarrow> Bool) \<Rightarrow>
    Dep_Bin_Rel (A & type P) B"
  by unfold_types force

lemma set_restrict_left_set_type [type]:
  "set_restrict_left : Dep_Bin_Rel A B \<Rightarrow> (A' : Set) \<Rightarrow>
    Dep_Bin_Rel (A & Element A') B"
  (*TODO: should be proved with lemma above*)
  by unfold_types force

lemma set_restrict_left_type_type [type]:
  "set_restrict_left : Dep_Bin_Rel A B \<Rightarrow> (T : Any) \<Rightarrow> Dep_Bin_Rel (A & T) B"
  (*TODO: should be proved with lemma above*)
  by unfold_types force

lemma agree_type_iff_agree [iff]:
  "agree (T :: set type) \<R> \<longleftrightarrow> agree (type_pred T) \<R>"
  unfolding agree_def by simp

lemma dom_type [type]: "dom : Dep_Bin_Rel A B \<Rightarrow> Collection A"
  by (auto intro: CollectionI)

lemma rng_type: "rng : Dep_Bin_Rel A B \<Rightarrow> Collection (type (\<lambda>y. \<exists>x : A. y : B x))"
  by (auto intro!: CollectionI elim!: Dep_Bin_Rel_memE simp: meaning_of_type)

lemma rng_type' [type]: "rng : Bin_Rel A B \<Rightarrow> Collection B"
  by (auto intro: CollectionI)

lemma set_rel_inv_type:
  "set_rel_inv : Dep_Bin_Rel A B \<Rightarrow> Bin_Rel (type (\<lambda>y. \<exists>x : A. y : B x)) A"
  by unfold_types force

lemma set_rel_inv_type' [type]: "set_rel_inv : Bin_Rel A B \<Rightarrow> Bin_Rel B A"
  by unfold_types auto

lemma Dep_Bin_Rel_mem_set_rel_invE [elim]:
  assumes "R : Dep_Bin_Rel A B"
  and "p \<in> set_rel_inv R"
  obtains x y where "x : A" "y : B x" "\<langle>x, y\<rangle> \<in> R" "p = \<langle>y, x\<rangle>"
  using assms by auto

lemma Dep_Bin_Rel_pair_mem_set_rel_inv_iff [iff]:
  "R : Dep_Bin_Rel A B \<Longrightarrow> \<langle>a, b\<rangle> \<in> set_rel_inv R \<longleftrightarrow> \<langle>b, a\<rangle> \<in> R"
  by auto

lemma Dep_Bin_Rel_set_rel_inv_set_rel_inv_eq_self [simp]:
  "R : Dep_Bin_Rel A B \<Longrightarrow> set_rel_inv (set_rel_inv R) = R"
  by (rule eqI) (auto simp: set_rel_inv_inv_eq)

lemma diag_type [type]: "diag : (A : Set) \<Rightarrow> Bin_Rel (Element A) (Element A)"
  by (auto intro: Dep_Bin_RelI)

lemma set_comp_type [type]:
  "set_comp : (S : Bin_Rel B C) \<Rightarrow> (R : Bin_Rel A B) \<Rightarrow> Bin_Rel A C"
  by unfold_types auto


end
