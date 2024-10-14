\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Subset\<close>
theory HOTG_Subset
  imports
    HOTG_Basics
    Transport.Partial_Orders
begin

abbreviation (input) "supset A B \<equiv> B \<subseteq> A"
open_bundle hotg_supset_syntax begin notation supset (infix "\<supseteq>" 50) end

lemma subsetI [intro]: "(\<And>x. x \<in> A \<Longrightarrow> x \<in> B) \<Longrightarrow> A \<subseteq> B"
  unfolding subset_def by simp

lemma subsetD [dest]: "\<lbrakk>A \<subseteq> B; a \<in> A\<rbrakk> \<Longrightarrow> a \<in> B"
  unfolding subset_def by blast

lemma subset_eq_rel_map_mem_of_le [set_to_HOL_simp]: "subset = rel_map mem_of (\<le>)"
  by (intro ext) auto

corollary mono_subset_le_mem_of: "((\<subseteq>) \<Rightarrow> (\<le>)) mem_of" by auto

lemma mem_if_subset_if_mem [trans]: "\<lbrakk>a \<in> A; A \<subseteq> B\<rbrakk> \<Longrightarrow> a \<in> B" by blast

lemma subset_self [iff]: "A \<subseteq> A" by blast

corollary reflexive_subset: "reflexive (\<subseteq>)" by auto

lemma empty_subset [iff]: "{} \<subseteq> A" by blast

lemma subset_empty_iff [iff]: "A \<subseteq> {} \<longleftrightarrow> A = {}" by blast

lemma not_mem_if_subset_if_not_mem [trans]: "\<lbrakk>a \<notin> B; A \<subseteq> B\<rbrakk> \<Longrightarrow> a \<notin> A"
  by blast

lemma subset_if_subset_if_subset [trans]: "\<lbrakk>A \<subseteq> B; B \<subseteq> C\<rbrakk> \<Longrightarrow> A \<subseteq> C"
  by blast

lemma subsetCE [elim]:
  assumes "A \<subseteq> B"
  obtains "a \<notin> A" | "a \<in> B"
  using assms by auto

lemma transitive_subset: "transitive (\<subseteq>)" by blast

corollary preorder_subset: "preorder (\<subseteq>)"
  using reflexive_subset transitive_subset by blast

lemma antisymmetric_subset: "antisymmetric (\<subseteq>)" by blast

corollary partial_order_subset: "partial_order (\<subseteq>)"
  using preorder_subset antisymmetric_subset by blast

subsection \<open>Strict Subsets\<close>

definition "ssubset A B \<equiv> A \<subseteq> B \<and> A \<noteq> B"

open_bundle hotg_ssubset_syntax begin notation ssubset (infixl "\<subset>" 50) end

lemma ssubsetI [intro]:
  assumes "A \<subseteq> B"
  and "A \<noteq> B"
  shows "A \<subset> B"
  unfolding ssubset_def using assms by blast

lemma ssubsetE [elim]:
  assumes "A \<subset> B"
  obtains "A \<subseteq> B" "A \<noteq> B"
  using assms unfolding ssubset_def by blast

lemma ssubset_iff_subset_and_ne: "X \<subset> Y \<longleftrightarrow> X \<subseteq> Y \<and> X \<noteq> Y" by auto

lemma subset_if_eq: "X = Y \<Longrightarrow> X \<subseteq> Y" by simp

lemma not_ssubset_iff_not_subset_or_eq: "\<not>(X \<subset> Y) \<longleftrightarrow> \<not>(X \<subseteq> Y) \<or> X = Y" by blast

local_setup \<open>
  HOL_Order_Tac.declare_order {
    ops = {eq = @{term \<open>(=) :: set \<Rightarrow> set \<Rightarrow> bool\<close>}, le = @{term \<open>(\<subseteq>)\<close>}, lt = @{term \<open>(\<subset>)\<close>}},
    thms = {trans = @{thm subset_if_subset_if_subset}, refl = @{thm subset_self},
      eqD1 = @{thm subset_if_eq},
      eqD2 = @{thm subset_if_eq[OF sym]}, antisym = @{thm antisymmetricD[OF antisymmetric_subset]},
      contr = @{thm notE}},
    conv_thms = {less_le = @{thm eq_reflection[OF ssubset_iff_subset_and_ne]},
      nless_le = @{thm eq_reflection[OF not_ssubset_iff_not_subset_or_eq]}}
  }
\<close>

end

