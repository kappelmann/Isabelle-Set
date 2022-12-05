\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Injective\<close>
theory SBinary_Relations_Injective
  imports
    HOL_Basics.Functions_Monotone
    SBinary_Relation_Functions
begin

consts set_injective_on :: "'a \<Rightarrow> set \<Rightarrow> bool"

overloading
  set_injective_on_pred \<equiv> "set_injective_on :: (set \<Rightarrow> bool) \<Rightarrow> set \<Rightarrow> bool"
  set_injective_on_set \<equiv> "set_injective_on :: set \<Rightarrow> set \<Rightarrow> bool"
begin
  definition "set_injective_on_pred P R \<equiv>
    \<forall>x x' y. P x \<and> P x' \<and> \<langle>x, y\<rangle> \<in> R \<and> \<langle>x', y\<rangle> \<in> R \<longrightarrow> x = x'"
  definition "set_injective_on_set B R \<equiv> set_injective_on (mem_of B) R"
end

lemma set_injective_on_set_iff_set_injective_on [iff]:
  "set_injective_on B R \<longleftrightarrow> set_injective_on (mem_of B) R"
  unfolding set_injective_on_set_def by simp

lemma set_injective_onI [intro]:
  assumes "\<And>x x' y. P x \<Longrightarrow> P x' \<Longrightarrow> \<langle>x, y\<rangle> \<in> R \<Longrightarrow> \<langle>x', y\<rangle> \<in> R \<Longrightarrow> x = x'"
  shows "set_injective_on P R"
  using assms unfolding set_injective_on_pred_def by blast

lemma set_injective_onD:
  assumes "set_injective_on P R"
  and "P x" "P x'"
  and "\<langle>x, y\<rangle> \<in> R" "\<langle>x', y\<rangle> \<in> R"
  shows "x = x'"
  using assms unfolding set_injective_on_pred_def by blast

lemma antimono'_set_injective_on_pred:
  "antimono' (\<lambda>P. set_injective_on (P :: set \<Rightarrow> bool) R)"
  by (intro antimono'I) (auto dest: set_injective_onD)

lemma antimono'_set_injective_on_set:
  "antimono' (\<lambda>R. set_injective_on (P :: set \<Rightarrow> bool) R)"
  by (intro antimono'I) (auto dest: set_injective_onD)

lemma set_injective_on_compI:
  fixes P :: "set \<Rightarrow> bool"
  assumes "set_injective_on (dom R) R"
  and "set_injective_on (rng R \<inter> dom S) S"
  shows "set_injective_on P (S \<circ> R)"
  using assms by (auto dest: set_injective_onD)


end