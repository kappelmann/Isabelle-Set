section \<open>Subset\<close>

theory Subset
imports Basic
begin

lemma subsetI [intro!]: "(\<And>x. x \<in> A \<Longrightarrow> x \<in> B) \<Longrightarrow> A \<subseteq> B"
  by (simp add: subset_def)

lemma subsetE [elim, trans]: "\<lbrakk>A \<subseteq> B; a \<in> A\<rbrakk> \<Longrightarrow> a \<in> B"
  by (unfold subset_def) auto

lemma subsetD: "A \<subseteq> B \<Longrightarrow> a \<in> A \<longrightarrow> a \<in> B"
  by auto

lemma subsetCE [elim]: "\<lbrakk>A \<subseteq> B; a \<notin> A \<Longrightarrow> P; a \<in> B \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (simp add: subset_def, blast)

lemma rev_subsetE [trans]: "\<lbrakk>a \<in> A; A \<subseteq> B\<rbrakk> \<Longrightarrow> a \<in> B"
  by auto

lemma contra_subsetE: "\<lbrakk>A \<subseteq> B; a \<notin> B\<rbrakk> \<Longrightarrow> a \<notin> A"
  by blast

lemma rev_contra_subsetE: "\<lbrakk>a \<notin> B; A \<subseteq> B\<rbrakk> \<Longrightarrow> a \<notin> A"
  by auto

lemma subset_refl [simp, intro]: "A \<subseteq> A"
  by blast

lemma subset_trans [trans]: "\<lbrakk>A \<subseteq> B; B \<subseteq> C\<rbrakk> \<Longrightarrow> A \<subseteq> C"
  by blast

(*LP: Useful for proving A \<subseteq> B by rewriting in some cases*)
lemma subset_iff: "A \<subseteq> B \<longleftrightarrow> (\<forall>x. x \<in> A \<longrightarrow> x \<in> B)"
  unfolding subset_def ..


end
