section \<open>Binary Relations\<close>
theory TBinary_Relations
  imports
    HOTG.Binary_Relations
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
  injective_type \<equiv> "injective :: set type \<Rightarrow> set \<Rightarrow> bool"
begin
  definition "injective_type (T :: set type) R \<equiv> injective (\<lambda>y. y : T) R"
end

lemma injective_type_iff_injective [iff]:
  "injective (T :: set type) R \<longleftrightarrow> injective (\<lambda>y. y : T) R"
  unfolding injective_type_def by simp

overloading
  right_unique_type \<equiv> "right_unique :: set type \<Rightarrow> set \<Rightarrow> bool"
begin
  definition "right_unique_type (T :: set type) R \<equiv> right_unique (\<lambda>x. x : T) R"
end

lemma right_unique_type_iff_right_unique [iff]:
  "right_unique (T :: set type) R \<longleftrightarrow> right_unique (\<lambda>x. x : T) R"
  unfolding right_unique_type_def by simp

overloading
  left_total_type \<equiv> "left_total :: set type \<Rightarrow> set \<Rightarrow> bool"
begin
  definition "left_total_type (T :: set type) R \<equiv> left_total (\<lambda>x. x : T) R"
end

lemma left_total_type_iff_left_total [iff]:
  "left_total (T :: set type) R \<longleftrightarrow> left_total (\<lambda>x. x : T) R"
  unfolding left_total_type_def by simp

overloading
  surjective_type \<equiv> "surjective :: set type \<Rightarrow> set \<Rightarrow> bool"
begin
  definition "surjective_type (T :: set type) R \<equiv> surjective (\<lambda>y. y : T) R"
end

lemma surjective_type_iff_surjective [iff]:
  "surjective (T :: set type) R \<longleftrightarrow> surjective (\<lambda>y. y : T) R"
  unfolding surjective_type_def by simp




subsection \<open>Functions on Binary Relations\<close>

lemma extend_type [type]:
  "extend : (x : A) \<Rightarrow> B x \<Rightarrow> Dep_Bin_Rel A B \<Rightarrow> Dep_Bin_Rel A B"
  by unfold_types auto

lemma glue_type [type]: "glue : Collection (Dep_Bin_Rel A B) \<Rightarrow> Dep_Bin_Rel A B"
  by unfold_types auto

overloading
  restrict_type \<equiv> "restrict :: set \<Rightarrow> set type \<Rightarrow> set"
begin
  definition "restrict_type R (T :: set type) \<equiv> restrict R (\<lambda>x. x : T)"
end

lemma restrict_type_eq_restrict [simp]:
  "restrict R (T :: set type) = restrict R (\<lambda>x. x : T)"
  unfolding restrict_type_def by simp

lemma restrict_set_eq_restrict_type [simp]:
  "restrict R S = restrict R (Element S)"
  by (auto iff: mem_iff_Element)

lemma restrict_type [type]:
  "restrict : Dep_Bin_Rel A B \<Rightarrow> (P : Set \<Rightarrow> Bool) \<Rightarrow> Dep_Bin_Rel (A & type P) B"
  by unfold_types force

lemma restrict_set_type [type]:
  "restrict : Dep_Bin_Rel A B \<Rightarrow> (A' : Set) \<Rightarrow> Dep_Bin_Rel (A & Element A') B"
  (*TODO: should be proved with lemma above*)
  by unfold_types force

lemma restrict_type_type [type]:
  "restrict : Dep_Bin_Rel A B \<Rightarrow> (T : Any) \<Rightarrow> Dep_Bin_Rel (A & T) B"
  (*TODO: should be proved with lemma above*)
  by unfold_types force

lemma agree_type_iff_agree [iff]:
  "agree (T :: set type) \<R> \<longleftrightarrow> agree (\<lambda>x. x : T) \<R>"
  unfolding agree_def by simp

lemma dom_type [type]: "dom : Dep_Bin_Rel A B \<Rightarrow> Collection A"
  by (auto intro: CollectionI)

lemma rng_type: "rng : Dep_Bin_Rel A B \<Rightarrow> Collection (type (\<lambda>y. \<exists>x : A. y : B x))"
  by (auto intro!: CollectionI elim!: Dep_Bin_Rel_memE simp: meaning_of_type)

lemma rng_type' [type]: "rng : Bin_Rel A B \<Rightarrow> Collection B"
  by (auto intro: CollectionI)

lemma converse_type:
  "converse : Dep_Bin_Rel A B \<Rightarrow> Bin_Rel (type (\<lambda>y. \<exists>x : A. y : B x)) A"
  by unfold_types force

lemma converse_type' [type]: "converse : Bin_Rel A B \<Rightarrow> Bin_Rel B A"
  by unfold_types auto

lemma Dep_Bin_Rel_mem_converseE [elim]:
  assumes "R : Dep_Bin_Rel A B"
  and "p \<in> converse R"
  obtains x y where "x : A" "y : B x" "\<langle>x, y\<rangle> \<in> R" "p = \<langle>y, x\<rangle>"
  using assms by auto

lemma Dep_Bin_Rel_pair_mem_converse_iff [iff]:
  "R : Dep_Bin_Rel A B \<Longrightarrow> \<langle>a, b\<rangle> \<in> converse R \<longleftrightarrow> \<langle>b, a\<rangle> \<in> R"
  by auto

lemma Dep_Bin_Rel_converse_converse_eq_self [simp]:
  "R : Dep_Bin_Rel A B \<Longrightarrow> converse (converse R) = R"
  by (rule eqI) (auto simp: converse_converse_eq)

lemma diag_type [type]: "diag : (A : Set) \<Rightarrow> Bin_Rel (Element A) (Element A)"
  by (auto intro: Dep_Bin_RelI)

lemma comp_type [type]:
  "comp : (S : Bin_Rel B C) \<Rightarrow> (R : Bin_Rel A B) \<Rightarrow> Bin_Rel A C"
  by unfold_types auto


end
