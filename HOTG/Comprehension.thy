\<^marker>\<open>creator "Alexander Krauss"\<close>
\<^marker>\<open>creator "Kevin Kappelmann"\<close>
\<^marker>\<open>creator "Larry Paulson"\<close>
section \<open>Restricted Comprehension\<close>
theory Comprehension
  imports
    Finite_Sets
begin

unbundle no_HOL_ascii_syntax

definition collect :: \<open>set \<Rightarrow> (set \<Rightarrow> bool) \<Rightarrow> set\<close>
  where "collect A P \<equiv> \<Union>{if P x then {x} else {} | x \<in> A}"

bundle hotg_collect_syntax
begin
syntax "_collect" :: \<open>idt \<Rightarrow> set \<Rightarrow> (set \<Rightarrow> bool) \<Rightarrow> set\<close> ("(1{_ \<in> _ |/ _})")
end
bundle no_hotg_collect_syntax
begin
no_syntax "_collect" :: \<open>idt \<Rightarrow> set \<Rightarrow> (set \<Rightarrow> bool) \<Rightarrow> set\<close> ("(1{_ \<in> _ |/ _})")
end
unbundle hotg_collect_syntax

translations
  "{x \<in> A | P}" \<rightleftharpoons> "CONST collect A (\<lambda>x. P)"

(*TOOD: simp_proc to apply one point rules (see Provers/quantifier1.ML)*)

lemma mem_collect_iff [iff]: "x \<in> {y \<in> A | P y} \<longleftrightarrow> x \<in> A \<and> P x"
  by (auto simp: collect_def)

lemma mem_collectI [intro]: "\<lbrakk>x \<in> A; P x\<rbrakk> \<Longrightarrow> x \<in> {y \<in> A | P y}" by auto

lemma mem_collectD: "x \<in> {y \<in> A | P y} \<Longrightarrow> x \<in> A" by auto

lemma mem_collectD': "x \<in> {y \<in> A | P y} \<Longrightarrow> P x" by auto

lemma collect_subset: "{x \<in> A | P x} \<subseteq> A" by blast

lemma collect_cong [cong]:
  "A = B \<Longrightarrow> (\<And>x. x \<in> B \<Longrightarrow> P x = Q x) \<Longrightarrow> {x \<in> A | P x} = {x \<in> B | Q x}"
  unfolding collect_def by simp

lemma collect_collect_eq [simp]: "collect (collect A P) Q = {x \<in> A | P x \<and> Q x}"
  by auto

lemma collect_insert_eq:
  "{x \<in> insert a B | P x} = (if P a then insert a {x \<in> B | P x} else {x \<in> B | P x})"
  by auto

lemma mono_subset_le_collect_set: "((\<subseteq>) \<Rrightarrow>\<^sub>m (\<le>) \<Rrightarrow> (\<subseteq>)) collect"
  by (intro dep_mono_wrt_relI) auto

end