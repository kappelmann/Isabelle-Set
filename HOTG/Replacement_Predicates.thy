section \<open>Replacement on Function-Like Predicates\<close>

theory Replacement_Predicates
imports Comprehension
begin

text \<open>Replacement based on function-like predicates, as formulated in first-order theories.\<close>

definition replace :: \<open>set \<Rightarrow> (set \<Rightarrow> set \<Rightarrow> bool) \<Rightarrow> set\<close>
  where "replace A P = {THE y. P x y | x \<in> {x \<in> A | \<exists>!y. P x y}}"

syntax
  "_replace." :: \<open>[pttrn, pttrn, set, bool] => set\<close> ("(1{_ ./ _ \<in> _, _})")
  "_replace|" :: \<open>[pttrn, pttrn, set, bool] => set\<close> ("(1{_ |/ _ \<in> _, _})")
translations
  "{y . x \<in> A, Q}" \<rightharpoonup> "CONST replace A (\<lambda>x y. Q)"
  "{y | x \<in> A, Q}" \<rightleftharpoons> "CONST replace A (\<lambda>x y. Q)"

lemma replace_iff:
  "b \<in> {y | x \<in> A, P x y} \<longleftrightarrow> (\<exists>x \<in> A. P x b \<and> (\<forall>y. P x y \<longrightarrow> y = b))"
proof -
  have "b \<in> {y | x \<in> A, P x y} \<longleftrightarrow> (\<exists>x \<in> A. (\<exists>!y. P x y) \<and> b = (THE y. P x y))"
    using replace_def by auto
  also have "... \<longleftrightarrow> (\<exists>x \<in> A. P x b \<and> (\<forall>y. P x y \<longrightarrow> y = b))"
  proof (rule bex_cong[OF refl])
    fix x assume "x \<in> A"
    show
      "(\<exists>!y. P x y) \<and> b = (THE y. P x y) \<longleftrightarrow> P x b \<and> (\<forall>y. P x y \<longrightarrow> y = b)"
      (is "?lhs \<longleftrightarrow> ?rhs")
    proof
      assume "?lhs"
      then have ex1: "\<exists>!y. P x y" and b: "b = (THE y. P x y)" by auto
      show ?rhs
      proof
        from ex1 show "P x b" unfolding b by (rule theI')
        with ex1 show "\<forall>y. P x y \<longrightarrow> y = b" unfolding Ex1_def by blast
      qed
    next
      assume ?rhs
      then have P: "P x b" and uniq: "\<And>y. P x y \<Longrightarrow> y = b" by auto
      show ?lhs
      proof
        from P uniq
        show "\<exists>!y. P x y" by (rule ex1I)
        from this P
        show "b = (THE y. P x y)" by (rule the1_equality[symmetric])
      qed
    qed
  qed
  ultimately show ?thesis by auto
qed

(*Introduction; there must be a unique y such that P x y, namely y = b.*)
lemma replaceI [intro]:
  "\<lbrakk> P x b;  x \<in> A;  \<And>y. P x y \<Longrightarrow> y = b \<rbrakk> \<Longrightarrow> b \<in> {y | x \<in> A, P x y}"
  by (rule replace_iff [THEN iffD2], blast)

(*Elimination; may assume there is a unique y such that P x y, namely y = b.*)
lemma replaceE:
  "\<lbrakk> b \<in> {y | x \<in> A, P x y};  \<And>x. \<lbrakk>x \<in> A; P x b; \<forall>y. P x y \<longrightarrow> y = b\<rbrakk> \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
  by (rule replace_iff [THEN iffD1, THEN bexE], simp+)

(*As above but without the (generally useless) third assumption*)
lemma replaceE2 [elim!]:
  "\<lbrakk>b \<in> {y. x \<in> A, P x y}; \<And>x. \<lbrakk>x \<in> A; P x b\<rbrakk> \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
  by (erule replaceE, blast)

lemma replace_cong [cong]:
  "\<lbrakk>A = B; \<And>x y. x \<in> B \<Longrightarrow> P x y \<longleftrightarrow> Q x y\<rbrakk> \<Longrightarrow> replace A P = replace B Q"
  by (rule equalityI') (simp add: replace_iff)


end
