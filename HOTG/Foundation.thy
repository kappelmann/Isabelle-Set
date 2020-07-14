section \<open>Well-Foundedness of Sets\<close>

theory Foundation
imports
  Union_Intersection
  Mem_Transitive
begin

lemma foundation: "X \<noteq> {} \<Longrightarrow> \<exists>Y \<in> X. Y \<inter> X = {}"
  using Axioms.mem_induction[where ?P="\<lambda>x. x \<notin> X"] by auto

lemma foundation2: "X = {} \<or> (\<exists>Y \<in> X. \<forall>y \<in> Y. y \<notin> X)"
  using foundation by blast

lemma foundation3: "X \<noteq> {} \<Longrightarrow> \<exists>Y \<in> X. \<not>(\<exists>y \<in> Y. y \<in> X)"
proof -
  assume "X \<noteq> {}"
  with foundation obtain Y where "Y \<in> X" and "Y \<inter> X = {}" by blast
  thus "\<exists>Y \<in> X. \<not>(\<exists>y \<in> Y. y \<in> X)" by auto
qed

lemma empty_in_transitive_set:
  assumes "mem_transitive X"
  and "X \<noteq> {}"
  shows "{} \<in> X"
proof (rule ccontr)
  from foundation2 \<open>X \<noteq> {}\<close> obtain A where
    1: "A \<in> X" and
    2: "\<forall>a \<in> A. a \<notin> X"
    by force
  assume "{} \<notin> X" with 1 have "A \<noteq> {}" by auto
  then obtain a where
    3: "a \<in> A"
    by auto
  with \<open>mem_transitive X\<close> 1 have "a \<in> X" by (auto dest: mem_transitiveE)
  then show False using 2 3 by auto
qed

lemma mem_asymE:
  assumes "a \<in> b" and b_in_a_of_not_P: "\<not>P \<Longrightarrow> b \<in> a"
  shows "P"
proof (rule ccontr)                                               
  assume not_P: "\<not>P"
  then have "b \<in> a" by (fact b_in_a_of_not_P)
  consider (empty) "{a, b} = {}" | (not_empty) "\<exists> c \<in> {a, b}. \<forall>d \<in> c. d \<notin> {a, b}"
    using foundation2[of "{a, b}"] by simp
  then show "False" using not_P assms by cases blast+
qed

lemma mem_asym: "a \<in> b \<Longrightarrow> b \<notin> a"
  by (auto intro: mem_asymE)

lemma mem_irreflE: "a \<in> a \<Longrightarrow> P"
  by (blast intro: mem_asymE)

(*LP: @{thm mem_irreflE} should NOT be added to default databases: it would be
  tried on most goals, making proofs slower!*)
(* Note Kevin: I suppose Larry means not added as an elim-rule (or similar) *)

lemma mem_irrefl [simp]: "a \<notin> a"
  by (rule notI) (erule mem_irreflE)

(*LP: Good for proving inequalities by rewriting*)
lemma mem_imp_ne: "a \<in> A \<Longrightarrow> a \<noteq> A"
  by (blast elim: mem_irreflE)

lemma eq_imp_not_elem: "a = A \<Longrightarrow> a \<notin> A"
  by (blast elim: mem_irreflE)

lemma union_singletonE [elim]: "A = A \<union> {A} \<Longrightarrow> P"
  by (blast elim: equalityE mem_irreflE)

lemma mem_3_cycle:
  assumes "a \<in> b" "b \<in> c" "c \<in> a"
  shows "False"
proof -
  let ?C = "{a, b, c}"
  have "?C \<noteq> {}" by simp
  from foundation[OF this]
  obtain Y where "Y \<in> ?C" "Y \<inter> ?C = {}" by auto
  from \<open>Y \<in> ?C\<close> have "Y = a \<or> Y = b \<or> Y = c" by simp
  thus ?thesis
  proof (elim disjE)
    assume "Y = a"
    with assms have "c \<in> Y \<inter> ?C" by auto
    with \<open>Y \<inter> ?C = {}\<close> show False by auto
  next
    assume "Y = b"
    with assms have "a \<in> Y \<inter> ?C" by auto
    with \<open>Y \<inter> ?C = {}\<close> show False by auto
  next
    assume "Y = c"
    with assms have "b \<in> Y \<inter> ?C" by auto
    with \<open>Y \<inter> ?C = {}\<close> show False by auto
  qed
qed

lemma mem_double_induct:
  assumes "\<And>X Y. \<lbrakk>\<And>x. x \<in> X \<Longrightarrow> P x Y; \<And>y. y \<in> Y \<Longrightarrow> P X y\<rbrakk> \<Longrightarrow> P X Y"
  shows "P X Y"
proof (induction X arbitrary: Y rule: mem_induction)
  fix X Y assume *: "\<And>x Y. x \<in> X \<Longrightarrow> P x Y"
  show "P X Y"
  proof (induction Y rule: mem_induction)
    fix Y assume "\<And>y. y \<in> Y \<Longrightarrow> P X y"
    with * show "P X Y" by (rule assms)
  qed
qed                                                                                      

lemma cons_ne_self [simp]: "cons x A \<noteq> x"
  by (auto intro: mem_irreflE)

lemma self_ne_cons [simp]: "x \<noteq> cons x A"
  by (fact cons_ne_self[symmetric])


end
