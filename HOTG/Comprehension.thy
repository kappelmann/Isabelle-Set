section \<open>Restricted Comprehension\<close>

theory Comprehension
imports Finite_Sets
begin

definition collect :: \<open>set \<Rightarrow> (set \<Rightarrow> bool) \<Rightarrow> set\<close>
  where "collect A P \<equiv> \<Union>{if P x then {x} else {} | x \<in> A}"

(*TODO: localise*)
syntax
  "_collect." :: \<open>pttrn \<Rightarrow> set \<Rightarrow> (set \<Rightarrow> bool) \<Rightarrow> set\<close> ("(1{_ \<in> _ ./ _})")
  "_collect|" :: \<open>pttrn \<Rightarrow> set \<Rightarrow> (set \<Rightarrow> bool) \<Rightarrow> set\<close> ("(1{_ \<in> _ |/ _})")
translations
  "{x \<in> A . P}" \<rightharpoonup> "CONST collect A (\<lambda>x. P)"
  "{x \<in> A | P}" \<rightleftharpoons> "CONST collect A (\<lambda>x. P)"

(*TOOD: simp_proc to apply one point rules (see Provers/quantifier1.ML)*)

lemma mem_collect_iff [iff]: "x \<in> {y \<in> A. P y} \<longleftrightarrow> x \<in> A \<and> P x"
  by (auto simp: collect_def)

lemma mem_collectI [intro]: "\<lbrakk>x \<in> A; P x\<rbrakk> \<Longrightarrow> x \<in> {y \<in> A | P y}"
  by auto

lemma mem_collectD: "x \<in> {y \<in> A | P y} \<Longrightarrow> x \<in> A" by auto

lemma mem_collectD': "x \<in> {y \<in> A | P y} \<Longrightarrow> P x" by auto

lemma collect_subset: "{x \<in> A | P x} \<subseteq> A" by blast

lemma collect_cong [cong]:
  "A = B \<Longrightarrow> (\<And>x. x \<in> B \<Longrightarrow> P x = Q x) \<Longrightarrow> {x \<in> A | P x} = {x \<in> B | Q x}"
  unfolding collect_def by simp

lemma collect_collect_eq [simp]: "collect (collect A P) Q = {x \<in> A | P x \<and> Q x}"
  by auto

lemma collect_cons_eq:
  "{x \<in> cons a B. P x} = (if P a then cons a {x \<in> B | P x} else {x \<in> B | P x})"
  by auto

lemma collect_subset_if_subset: "A \<subseteq> B \<Longrightarrow> {x \<in> A | P x} \<subseteq> {x \<in> B | P x}"
  by auto

end
