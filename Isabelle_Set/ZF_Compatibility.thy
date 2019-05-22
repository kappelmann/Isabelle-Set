theory ZF_Compatibility
imports Isabelle_Set

begin

subsection \<open>Disjoint union as a sigma type\<close>

abbreviation (input) "Sigma \<equiv> DUnion"


subsection \<open>Generalized replacement\<close>

text \<open>Replacement in predicate form, as it is done in ZF.\<close>

definition Replace :: "set \<Rightarrow> (set \<Rightarrow> set \<Rightarrow> bool) \<Rightarrow> set"
  where "Replace A P = {THE y. P x y | x \<in> {x \<in> A | \<exists>!y. P x y}}"

syntax
  "_GenRepl"  :: "[pttrn, pttrn, set, bool] => set"  ("(1{_ |/ _ \<in> _, _})")
  "_GenRepl'"  :: "[pttrn, pttrn, set, bool] => set"  ("(1{_ ./ _ \<in> _, _})")
translations
  "{y | x \<in> A, Q}" \<rightleftharpoons> "CONST Replace A (\<lambda>x y. Q)"
  "{y . x \<in> A, Q}" \<rightharpoonup> "CONST Replace A (\<lambda>x y. Q)"


lemma Replace_iff:
  "b \<in> {y | x \<in> A, P x y} \<longleftrightarrow> (\<exists>x \<in> A. P x b \<and> (\<forall>y. P x y \<longrightarrow> y = b))"
proof -
  have "b \<in> {y | x \<in> A, P x y} \<longleftrightarrow> (\<exists>x \<in> A. (\<exists>!y. P x y) \<and> b = (THE y. P x y))"
    using Replace_def by auto
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

(* Introduction; there must be a unique y such that P(x,y), namely y = b. *)
lemma ReplaceI [intro]: "\<lbrakk>P x b; x \<in> A; \<And>y. P x y \<Longrightarrow> y = b\<rbrakk> \<Longrightarrow> b \<in> {y | x \<in> A, P x y}"
  by (rule Replace_iff [THEN iffD2], blast)

(* Elimination; may assume there is a unique y such that P(x,y), namely y = b. *)
lemma ReplaceE:
  "\<lbrakk>b \<in> {y | x \<in> A, P x y}; \<And>x. \<lbrakk>x \<in> A; P x b; \<forall>y. P x y \<longrightarrow> y = b\<rbrakk> \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
  by (rule Replace_iff [THEN iffD1, THEN bexE], simp+)

(* As above but without the (generally useless) 3rd assumption *)
lemma ReplaceE2 [elim!]:
    "\<lbrakk>b \<in> {y. x \<in> A, P x y};
        \<And>x. \<lbrakk>x \<in> A; P x b\<rbrakk> \<Longrightarrow> R
    \<rbrakk> \<Longrightarrow> R"
by (erule ReplaceE, blast)

lemma Replace_cong [cong]:
    "\<lbrakk>A=B; \<And>x y. x \<in>B \<Longrightarrow> P x y \<longleftrightarrow> Q x y\<rbrakk> \<Longrightarrow>
     Replace A P = Replace B Q"
by (rule equality_iffI) (simp add: Replace_iff)



end