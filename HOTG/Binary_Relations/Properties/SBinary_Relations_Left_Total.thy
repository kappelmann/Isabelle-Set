\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Left Total\<close>
theory SBinary_Relations_Left_Total
  imports
    SBinary_Relation_Functions
begin

consts set_left_total_on :: "'a \<Rightarrow> set \<Rightarrow> bool"

overloading
  set_left_total_on_pred \<equiv> "set_left_total_on :: (set \<Rightarrow> bool) \<Rightarrow> set \<Rightarrow> bool"
  set_left_total_on_set \<equiv> "set_left_total_on :: set \<Rightarrow> set \<Rightarrow> bool"
begin
  definition "set_left_total_on_pred P R \<equiv> \<forall>x. P x \<longrightarrow> x \<in> dom R"
  definition "set_left_total_on_set A R \<equiv> set_left_total_on (mem_of A) R"
end

lemma set_left_total_on_set_iff_set_left_total_on [iff]:
  "set_left_total_on A R \<longleftrightarrow> set_left_total_on (mem_of A) R"
  unfolding set_left_total_on_set_def by simp

lemma set_left_total_onI [intro]:
  assumes "\<And>x. P x \<Longrightarrow> x \<in> dom R"
  shows "set_left_total_on P R"
  unfolding set_left_total_on_pred_def using assms by blast

lemma set_left_total_onE [elim]:
  assumes "set_left_total_on P R"
  and "P x"
  obtains "x \<in> dom R"
  using assms unfolding set_left_total_on_pred_def by blast

lemma antimono'_set_left_total_on_pred:
  "antimono' (\<lambda>P. set_left_total_on (P :: set \<Rightarrow> bool) R)"
  by (intro antimono'I) fastforce

lemma mono'_set_left_total_on_set:
  "mono' (\<lambda>R. set_left_total_on (P :: set \<Rightarrow> bool) R)"
  by (intro mono'I) fastforce

lemma set_left_total_on_set_iff_subset_dom [iff]:
  "set_left_total_on A R \<longleftrightarrow> A \<subseteq> dom R"
  by auto

lemma set_left_total_on_inf_restrict_leftI:
  fixes P P' :: "set \<Rightarrow> bool"
  assumes "set_left_total_on P R"
  shows "set_left_total_on (P \<sqinter> P') R\<restriction>\<^bsub>P'\<^esub>"
  using assms by (intro set_left_total_onI) auto

lemma set_left_total_on_compI:
  fixes P :: "set \<Rightarrow> bool"
  assumes "set_left_total_on P R"
  and "set_left_total_on (rng (R\<restriction>\<^bsub>P\<^esub>)) S"
  shows "set_left_total_on P (S \<circ> R)"
  using assms by (intro set_left_total_onI) auto


end