\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Set Equality\<close>
theory HOTG_Equality
  imports HOTG_Subset
begin

lemma eqI [intro]: "(\<And>x. x \<in> A \<Longrightarrow> x \<in> B) \<Longrightarrow> (\<And>x. x \<in> B \<Longrightarrow> x \<in> A) \<Longrightarrow> A = B"
  by auto

lemma eq_if_mem_of_eq_mem_of:
  assumes "mem_of R = mem_of S"
  shows "R = S"
  using assms by (auto simp only: set_to_HOL_simp)

corollary eq_iff_mem_of_eq_mem_of [set_to_HOL_simp]: "R = S \<longleftrightarrow> mem_of R = mem_of S"
  using eq_if_mem_of_eq_mem_of by blast

lemma eqI': "(\<And>x. x \<in> A \<longleftrightarrow> x \<in> B) \<Longrightarrow> A = B" by auto

lemma eqE: "\<lbrakk>A = B; \<lbrakk>A \<subseteq> B ; B \<subseteq> A\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P" by blast

lemma eqD [dest]: "A = B \<Longrightarrow> (\<And>x. x \<in> A \<longleftrightarrow> x \<in> B)" by auto

lemma ne_if_ex_mem_not_mem: "\<exists>x. x \<in> A \<and> x \<notin> B \<Longrightarrow> A \<noteq> B" by auto

lemma neD: "A \<noteq> B \<Longrightarrow> \<exists>x. (x \<in> A \<and> x \<notin> B) \<or> (x \<notin> A \<and> x \<in> B)" by auto

lemma neE:
  assumes "A \<noteq> B"
  obtains x where "x \<in> A" "x \<notin> B" | x where "x \<notin> A" "x \<in> B"
  using assms by blast

lemma eq_empty_iff_all_not_mem: "A = {} \<longleftrightarrow> (\<forall>x. x \<notin> A)" by blast

end
