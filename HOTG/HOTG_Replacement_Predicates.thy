\<^marker>\<open>creator "Alexander Krauss"\<close>
\<^marker>\<open>creator "Kevin Kappelmann"\<close>
\<^marker>\<open>creator "Larry Paulson"\<close>
section \<open>Replacement on Function-Like Predicates\<close>
theory HOTG_Replacement_Predicates
  imports HOTG_Comprehension
begin

text \<open>Replacement based on function-like predicates, as formulated in first-order theories.\<close>

definition replace :: \<open>set \<Rightarrow> (set \<Rightarrow> set \<Rightarrow> bool) \<Rightarrow> set\<close>
  where "replace A P = {THE y. P x y | x \<in> {x \<in> A | \<exists>!y. P x y}}"

open_bundle hotg_replacement_syntax
begin
syntax
  "_replace" :: \<open>[pttrn, pttrn, set, set \<Rightarrow> set \<Rightarrow> bool] => set\<close> ("{_ |/ _ \<in> _, _}")
end
syntax_consts "_replace" \<rightleftharpoons> replace
translations
  "{y | x \<in> A, Q}" \<rightleftharpoons> "CONST replace A (\<lambda>x y. Q)"

lemma mem_replace_iff:
  "b \<in> {y | x \<in> A, P x y} \<longleftrightarrow> (\<exists>x : A. P x b \<and> (\<forall>y. P x y \<longrightarrow> y = b))"
proof -
  have "b \<in> {y | x \<in> A, P x y} \<longleftrightarrow> (\<exists>x : A. (\<exists>!y. P x y) \<and> b = (THE y. P x y))"
    using replace_def by auto
  also have "... \<longleftrightarrow> (\<exists>x : A. P x b \<and> (\<forall>y. P x y \<longrightarrow> y = b))"
  proof (urule bex_cong[OF refl])
    fix x presume "x \<in> A"
    show
      "(\<exists>!y. P x y) \<and> b = (THE y. P x y) \<longleftrightarrow> P x b \<and> (\<forall>y. P x y \<longrightarrow> y = b)"
      (is "?lhs \<longleftrightarrow> ?rhs")
    proof
      assume "?lhs"
      then have ex1: "\<exists>!y. P x y" and b_eq: "b = (THE y. P x y)" by auto
      show ?rhs
      proof
        from ex1 show "P x b" unfolding b_eq by (rule theI')
        with ex1 show "\<forall>y. P x y \<longrightarrow> y = b" unfolding Ex1_def by blast
      qed
    next
      assume ?rhs
      then have P: "P x b" and uniq: "\<And>y. P x y \<Longrightarrow> y = b" by auto
      show ?lhs
      proof
        from P uniq show "\<exists>!y. P x y" by (rule ex1I)
        then show "b = (THE y. P x y)" using P by (rule the1_equality[symmetric])
      qed
    qed
  qed simp
  finally show ?thesis .
qed

(*Introduction; there must be a unique y such that P x y, namely y = b.*)
lemma replaceI [intro!]:
  "\<lbrakk>P x b;  x \<in> A;  \<And>y. P x y \<Longrightarrow> y = b\<rbrakk> \<Longrightarrow> b \<in> {y | x \<in> A, P x y}"
  by (rule mem_replace_iff[THEN iffD2]) blast

(*Elimination; may assume there is a unique y such that P x y, namely y = b.*)
lemma replaceE:
  assumes "b \<in> {y | x \<in> A, P x y}"
  obtains x where "x \<in> A" and "P x b" and "\<And>y. P x y \<Longrightarrow> y = b"
  using assms by (blast dest: mem_replace_iff[THEN iffD1])

(*As above but without the (generally useless) third assumption*)
lemma replaceE' [elim!]:
  assumes "b \<in> {y | x \<in> A, P x y}"
  obtains x where "x \<in> A" "P x b"
  using assms by (elim replaceE) blast

lemma replace_cong [cong]:
  "\<lbrakk>A = B; \<And>x y. x \<in> B \<Longrightarrow> P x y \<longleftrightarrow> Q x y\<rbrakk> \<Longrightarrow> {y | x \<in> A, P x y} = {y | x \<in> B, Q x y}"
  by (rule eqI') (auto simp add: mem_replace_iff)

lemma mono_subset_replace_set: "((\<subseteq>) \<Rightarrow> (\<subseteq>)) (\<lambda>A. {y | x \<in> A, P x y})"
  by (intro mono_wrt_relI) (auto elim!: replaceE)

end

