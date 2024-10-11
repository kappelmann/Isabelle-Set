theory Hilbert_Eps
  imports HOTG_Basics
begin
(*from HOL Hilbert_Choice*)
subsection \<open>Hilbert's epsilon\<close>

axiomatization Eps :: "('a \<Rightarrow> bool) \<Rightarrow> 'a"
  where someI: "P x \<Longrightarrow> P (Eps P)"

syntax (epsilon)
  "_Eps" :: "pttrn \<Rightarrow> bool \<Rightarrow> 'a"  ("(3\<some>_./ _)" [0, 10] 10)
syntax (input)
  "_Eps" :: "pttrn \<Rightarrow> bool \<Rightarrow> 'a"  ("(3@ _./ _)" [0, 10] 10)
syntax
  "_Eps" :: "pttrn \<Rightarrow> bool \<Rightarrow> 'a"  ("(3SOME _./ _)" [0, 10] 10)

syntax_consts "_Eps" \<rightleftharpoons> Eps

translations
  "SOME x. P" \<rightleftharpoons> "CONST Eps (\<lambda>x. P)"

print_translation \<open>
  [(\<^const_syntax>\<open>Eps\<close>, fn _ => fn [Abs abs] =>
      let val (x, t) = Syntax_Trans.atomic_abs_tr' abs
      in Syntax.const \<^syntax_const>\<open>_Eps\<close> $ x $ t end)]
\<close> \<comment> \<open>to avoid eta-contraction of body\<close>

subsection \<open>Hilbert's Epsilon-operator\<close>

lemma Eps_cong:
  assumes "\<And>x. P x = Q x"
  shows "Eps P = Eps Q"
  using ext[of P Q, OF assms] by simp

text \<open>
  Easier to use than \<open>someI\<close> if the witness comes from an
  existential formula.
\<close>
lemma someI_ex [elim?]: "\<exists>x. P x \<Longrightarrow> P (SOME x. P x)"
  by (elim exE someI)

lemma some_eq_imp:
  assumes "Eps P = a" "P b" shows "P a"
  using assms someI_ex by force

text \<open>
  Easier to use than \<open>someI\<close> because the conclusion has only one
  occurrence of \<^term>\<open>P\<close>.
\<close>
lemma someI2: "P a \<Longrightarrow> (\<And>x. P x \<Longrightarrow> Q x) \<Longrightarrow> Q (SOME x. P x)"
  by (blast intro: someI)

text \<open>
  Easier to use than \<open>someI2\<close> if the witness comes from an
  existential formula.
\<close>
lemma someI2_ex: "\<exists>a. P a \<Longrightarrow> (\<And>x. P x \<Longrightarrow> Q x) \<Longrightarrow> Q (SOME x. P x)"
  by (blast intro: someI2)

lemma some_equality [intro]: "P a \<Longrightarrow> (\<And>x. P x \<Longrightarrow> x = a) \<Longrightarrow> (SOME x. P x) = a"
  by (blast intro: someI2)

lemma some1_equality: "\<exists>!x. P x \<Longrightarrow> P a \<Longrightarrow> (SOME x. P x) = a"
  by blast

lemma some_eq_ex: "P (SOME x. P x) \<longleftrightarrow> (\<exists>x. P x)"
  by (blast intro: someI)


lemma some_eq_trivial [simp]: "(SOME y. y = x) = x"
  by (rule some_equality) (rule refl)

lemma some_sym_eq_trivial [simp]: "(SOME y. x = y) = x"
  by (iprover intro: some_equality)



end