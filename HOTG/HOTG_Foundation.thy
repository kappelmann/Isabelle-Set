\<^marker>\<open>creator "Alexander Krauss"\<close>
\<^marker>\<open>creator "Kevin Kappelmann"\<close>
\<^marker>\<open>creator "Larry Paulson"\<close>
section \<open>Well-Foundedness of Sets\<close>
theory HOTG_Foundation
  imports
    HOTG_Mem_Transitive_Closed_Base
    HOTG_Union_Intersection
    Transport.Binary_Relations_Asymmetric
begin

lemma bex_disjoint_if_ne_empty: "X \<noteq> {} \<Longrightarrow> \<exists>Y : X. disjoint Y X"
  using HOTG_Axioms.mem_induction[where ?P="\<lambda>x. x \<notin> X"] by blast

lemma bex_disjoint_if_ne_empty': "X \<noteq> {} \<Longrightarrow> \<exists>Y : X. \<forall>y : Y. y \<notin> X"
proof -
  assume "X \<noteq> {}"
  with bex_disjoint_if_ne_empty obtain Y where "Y \<in> X" "disjoint Y X" by auto
  then show ?thesis by blast
qed

lemma empty_or_bex_disjoint: "X = {} \<or> (\<exists>Y : X. disjoint Y X)"
  using bex_disjoint_if_ne_empty by auto

lemma empty_mem_if_mem_trans_closedI:
  assumes "mem_trans_closed X"
  and "X \<noteq> {}"
  shows "{} \<in> X"
proof (rule ccontr)
  from bex_disjoint_if_ne_empty \<open>X \<noteq> {}\<close> obtain A where "A \<in> X" and X_foundation: "\<forall>a : A. a \<notin> X"
    by auto
  assume "{} \<notin> X"
  with \<open>A \<in> X\<close> have "A \<noteq> {}" by auto
  then obtain a where "a \<in> A" by auto
  with mem_trans_closedD[OF \<open>mem_trans_closed X\<close> \<open>A \<in> X\<close>] have "a \<in> X" by auto
  with X_foundation \<open>a \<in> A\<close> show False by auto
qed

lemma not_mem_if_mem:
  assumes "a \<in> b"
  shows "b \<notin> a"
proof (rule ccontr)
  presume "b \<in> a"
  consider (empty) "{a, b} = {}" | (ne_empty) "\<exists>c : {a, b}. \<forall>d : c. d \<notin> {a, b}"
    using empty_or_bex_disjoint[of "{a, b}"] by simp
  then show "False" by cases (use \<open>b \<in> a\<close> assms in auto)
qed auto

corollary asymmetric_mem: "asymmetric (\<in>)"
  using not_mem_if_mem by blast

lemma not_mem_self [iff]: "a \<notin> a" using not_mem_if_mem by blast

lemma bin_union_singleton_self_ne_self [iff]: "A \<union> {A} \<noteq> A" by auto

lemma bin_inter_singleton_self_eq_empty [simp]: "A \<inter> {A} = {}" by auto

lemma ne_if_mem: "a \<in> A \<Longrightarrow> a \<noteq> A"
  using not_mem_self by blast

lemma not_mem_if_eq: "a = A \<Longrightarrow> a \<notin> A"
  by simp

lemma not_mem_if_mem_if_mem:
  assumes "a \<in> b" "b \<in> c"
  shows "c \<notin> a"
proof
  assume "c \<in> a"
  let ?X = "{a, b, c}"
  have "?X \<noteq> {}" by simp
  with bex_disjoint_if_ne_empty obtain Y where "Y \<in> ?X" "Y \<inter> ?X = {}" by (urule bexE) auto
  from \<open>Y \<in> ?X\<close> have "Y = a \<or> Y = b \<or> Y = c" by auto
  with assms \<open>c \<in> a\<close> have "a \<in> Y \<or> b \<in> Y \<or> c \<in> Y" by blast
  with \<open>Y \<inter> ?X = {}\<close> show False by blast
qed

lemma mem_double_induct:
  assumes "\<And>X Y. \<lbrakk>\<And>x. x \<in> X \<Longrightarrow> P x Y; \<And>y. y \<in> Y \<Longrightarrow> P X y\<rbrakk> \<Longrightarrow> P X Y"
  shows "P X Y"
proof (induction X arbitrary: Y rule: mem_induction)
  case (mem X)
  then show ?case by (induction Y rule: mem_induction) (auto intro: assms)
qed

lemma insert_ne_self [iff]: "insert x A \<noteq> x"
  by (rule ne_if_mem[symmetric]) auto


end