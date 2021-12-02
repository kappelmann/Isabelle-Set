section \<open>Well-Foundedness of Sets\<close>

theory Foundation
imports
  Union_Intersection
  Mem_Trans
begin

lemma foundation_if_not_empty: "X \<noteq> {} \<Longrightarrow> \<exists>Y \<in> X. Y \<inter> X = {}"
  using Axioms.mem_induction[where ?P="\<lambda>x. x \<notin> X"] by blast

lemma foundation_if_not_empty': "X \<noteq> {} \<Longrightarrow> \<exists>Y \<in> X. \<not>(\<exists>y \<in> Y. y \<in> X)"
proof -
  assume "X \<noteq> {}"
  with foundation_if_not_empty obtain Y where "Y \<in> X" and "Y \<inter> X = {}" by auto
  thus "\<exists>Y \<in> X. \<not>(\<exists>y \<in> Y. y \<in> X)" by auto
qed

lemma empty_or_foundation: "X = {} \<or> (\<exists>Y \<in> X. \<forall>y \<in> Y. y \<notin> X)"
  using foundation_if_not_empty by auto

lemma empty_mem_if_mem_trans:
  assumes "mem_trans X"
  and "X \<noteq> {}"
  shows "{} \<in> X"
proof (rule ccontr)
  from foundation_if_not_empty[OF \<open>X \<noteq> {}\<close>]
    obtain A where "A \<in> X" and X_foundation: "\<forall>a \<in> A. a \<notin> X"
    by auto
  assume "{} \<notin> X"
  with \<open>A \<in> X\<close> have "A \<noteq> {}" by auto
  then obtain a where "a \<in> A" by auto
  with mem_transE[OF \<open>mem_trans X\<close> \<open>A \<in> X\<close>] have "a \<in> X" by auto
  with X_foundation \<open>a \<in> A\<close> show False by auto
qed

lemma mem_asym:
  assumes "a \<in> b"
  shows "b \<notin> a"
proof (rule ccontr)
  presume "b \<in> a"
  consider (empty) "{a, b} = {}" | (not_empty) "\<exists>c \<in> {a, b}. \<forall>d \<in> c. d \<notin> {a, b}"
    using empty_or_foundation[of "{a, b}"] by simp
  with \<open>b \<in> a\<close> assms show "False" by cases auto
qed auto

lemma mem_irrefl [simp, intro!]: "a \<notin> a"
  using mem_asym by blast

lemma bin_union_singleton_self_ne_self [simp, intro!]: "A \<union> {A} \<noteq> A" by auto

lemma bin_inter_singleton_self_eq_empty [simp, intro!]: "A \<inter> {A} = {}" by auto

lemma ne_if_mem: "a \<in> A \<Longrightarrow> a \<noteq> A"
  using mem_irrefl by blast

lemma not_mem_if_eq: "a = A \<Longrightarrow> a \<notin> A"
  by simp

lemma not_mem_if_mem_if_mem:
  assumes "a \<in> b" "b \<in> c"
  shows "c \<notin> a"
proof
  assume "c \<in> a"
  let ?X = "{a, b, c}"
  have "?X \<noteq> {}" by simp
  from foundation_if_not_empty[OF this] obtain Y where "Y \<in> ?X" "Y \<inter> ?X = {}"
    by blast
  from \<open>Y \<in> ?X\<close> have "Y = a \<or> Y = b \<or> Y = c" by simp
  with assms \<open>c \<in> a\<close> have "a \<in> Y \<or> b \<in> Y \<or> c \<in> Y" by blast
  with \<open>Y \<inter> ?X = {}\<close> show False by blast
qed

lemma mem_double_induct:
  assumes "\<And>X Y. \<lbrakk>\<And>x. x \<in> X \<Longrightarrow> P x Y; \<And>y. y \<in> Y \<Longrightarrow> P X y\<rbrakk> \<Longrightarrow> P X Y"
  shows "P X Y"
proof (induction X arbitrary: Y rule: mem_induction)
  fix X Y assume IH1: "\<And>x Y. x \<in> X \<Longrightarrow> P x Y"
  show "P X Y"
  proof (induction Y rule: mem_induction)
    fix Y assume "\<And>y. y \<in> Y \<Longrightarrow> P X y"
    with IH1 show "P X Y" by (rule assms)
  qed
qed

lemma cons_ne_self [simp, intro!]: "cons x A \<noteq> x"
  by (rule ne_if_mem[symmetric]) simp

lemma self_ne_cons [simp, intro!]: "x \<noteq> cons x A"
  by (fact cons_ne_self[symmetric])


end
