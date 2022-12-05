\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Set Equality\<close>
theory Equality
  imports Subset
begin

lemma eqI [intro]: "(\<And>x. x \<in> A \<Longrightarrow> x \<in> B) \<Longrightarrow> (\<And>x. x \<in> B \<Longrightarrow> x \<in> A) \<Longrightarrow> A = B"
  by auto

lemma eqI': "(\<And>x. x \<in> A \<longleftrightarrow> x \<in> B) \<Longrightarrow> A = B" by auto

lemma eqE: "\<lbrakk>A = B; \<lbrakk>A \<subseteq> B ; B \<subseteq> A\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P" by blast

lemma eqD [dest]: "A = B \<Longrightarrow> (\<And>x. x \<in> A \<longleftrightarrow> x \<in> B)" by auto

lemma ne_if_ex_mem_not_mem: "\<exists>x. x \<in> A \<and> x \<notin> B \<Longrightarrow> A \<noteq> B" by auto

lemma neD: "A \<noteq> B \<Longrightarrow> \<exists>x. (x \<in> A \<and> x \<notin> B) \<or> (x \<notin> A \<and> x \<in> B)" by auto

end
