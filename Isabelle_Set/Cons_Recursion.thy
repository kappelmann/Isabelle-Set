section \<open>Recursion on hereditary \<open>cons\<close> sets\<close>

theory Cons_Recursion
imports Function

begin

text \<open>
  We develop a theory of recursive functions on finite sets constructed using \<^term>\<open>cons\<close>.
  The main results essentially specialize the well-founded recursion theorem to the implicit
  ordering on finite hereditary \<^term>\<open>cons\<close> terms.

  The initial motivation for this was to define object instances, but this is not needed
  if we move the finitely many definitions to the HOL level.
\<close>

lemma cons_recursion_base:
  assumes "G \<in> Univ U \<rightarrow> Univ U"
  shows "\<exists>!F \<in> {x} \<rightarrow> Univ U. F `x = G `{}"
proof
  let ?F = "{\<langle>x, G `{}\<rangle>}"
  show "?F `x = G `{}" by simp
  moreover
  show "?F \<in> {x} \<rightarrow> Univ U"
    by (rule singleton_functionI) (auto intro: FunctionE assms)
  ultimately
  show "\<And>f. \<lbrakk>f \<in> {x} \<rightarrow> Univ U; f `x = G `{}\<rbrakk> \<Longrightarrow> f = ?F"
    by (auto intro: funext)
qed

(* cons_recursion_base is in fact a special case of the following theorem. *)

lemma cons_recursion_lemma:
  assumes
    G: "G \<in> Univ U \<rightarrow> Univ U" and
    H: "H \<in> A \<rightarrow> Univ U" and
    A: "A \<in> Univ U" and
    B: "B = cons x A" and
    x: "x \<notin> A"
  shows
    "\<exists>!F \<in> B \<rightarrow> Univ U. (\<forall>a \<in> A. F `a = H `a) \<and> F `x = G `{F `a | a \<in> A}"
proof (rule, rule)
  let ?Fx = "G `{H `a | a \<in> A}"
  let ?F = "{\<langle>x, ?Fx\<rangle>} \<union> H"

  show 1: "?F \<in> B \<rightarrow> Univ U"
  proof -
    note
      bin_union_functionI[of H A "Univ U" x ?Fx, OF H x]
      bin_union_eq_cons'[of A x]
    moreover
    have "Univ U \<union> {?Fx} = Univ U"
      by (auto intro!: Univ_bin_union_simp FunctionE assms)
    ultimately
    show ?thesis
      using assms by auto
  qed

  show 2: "(\<forall>a \<in> A. ?F `a = H `a)"
    by (auto intro: apply_function function_mems bin_unionI2 H 1)

  show 3: "?F `x = G `{?F `a . a \<in> A}"
    sorry
oops


end
