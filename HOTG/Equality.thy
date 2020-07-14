section \<open>Set Equality\<close>

theory Equality
imports Subset
begin

lemma equalityI: "(\<And>x. x \<in> A \<Longrightarrow> x \<in> B) \<Longrightarrow> (\<And>x. x \<in> B \<Longrightarrow> x \<in> A) \<Longrightarrow> A = B"
  by (rule extensionality) auto

lemma equalityI': "(\<And>x. x \<in> A \<longleftrightarrow> x \<in> B) \<Longrightarrow> A = B"
  by (rule extensionality) auto

lemma equalityE: "\<lbrakk>A = B; \<lbrakk>A \<subseteq> B ; B \<subseteq> A\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by blast

lemma equalityCE: "\<lbrakk>A = B; \<lbrakk>a \<in> A; a \<in> B\<rbrakk> \<Longrightarrow> P; \<lbrakk>a \<notin> A; a \<notin> B\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (erule equalityE, blast)

lemma equalityD: "A = B \<Longrightarrow> (\<And>x. x \<in> A \<longleftrightarrow> x \<in> B)"
  by auto


end
