\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Surjective\<close>
theory SBinary_Relations_Surjective
  imports
    SBinary_Relation_Functions
begin

consts set_surjective_at :: "'a \<Rightarrow> set \<Rightarrow> bool"

overloading
  set_surjective_at_pred \<equiv> "set_surjective_at :: (set \<Rightarrow> bool) \<Rightarrow> set \<Rightarrow> bool"
  set_surjective_at_set \<equiv> "set_surjective_at :: set \<Rightarrow> set \<Rightarrow> bool"
begin
  definition "set_surjective_at_pred P R \<equiv> \<forall>y. P y \<longrightarrow> y \<in> rng R"
  definition "set_surjective_at_set B R \<equiv> set_surjective_at (mem_of B) R"
end

lemma set_surjective_at_set_iff_set_surjective_at [iff]:
  "set_surjective_at B R \<longleftrightarrow> set_surjective_at (mem_of B) R"
  unfolding set_surjective_at_set_def by simp

lemma set_surjective_atI [intro]:
  assumes "\<And>y. P y \<Longrightarrow> y \<in> rng R"
  shows "set_surjective_at P R"
  unfolding set_surjective_at_pred_def using assms by blast

lemma set_surjective_atE [elim]:
  assumes "set_surjective_at P R"
  and "P y"
  obtains x where "\<langle>x, y\<rangle> \<in> R"
  using assms unfolding set_surjective_at_pred_def by blast

lemma antimono_set_surjective_at_pred:
  "antimono (\<lambda>P. set_surjective_at (P :: set \<Rightarrow> bool) R)"
  by (intro antimonoI) fastforce

lemma mono_set_surjective_at_set:
  "mono (\<lambda>R. set_surjective_at (P :: set \<Rightarrow> bool) R)"
  by (intro monoI) fastforce

lemma subset_rng_if_set_surjective_at [simp]:
  "set_surjective_at B R \<Longrightarrow> B \<subseteq> rng R"
  by auto

lemma set_surjective_at_compI:
  fixes P :: "set \<Rightarrow> bool"
  assumes surj_R: "set_surjective_at (dom S) R"
  and surj_S: "set_surjective_at P S"
  shows "set_surjective_at P (S \<circ> R)"
proof
  fix y assume "P y"
  then obtain x where "\<langle>x, y\<rangle> \<in> S" using surj_S by auto
  moreover then have "x \<in> dom S" by auto
  moreover then obtain z where "\<langle>z, x\<rangle> \<in> R" using surj_R by auto
  ultimately show "y \<in> rng (S \<circ> R)" by blast
qed


end