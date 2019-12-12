theory Object2
imports Function String

begin

definition object_selector :: \<open>set \<Rightarrow> set \<Rightarrow> set\<close> ("_@_" [1000, 1000])
  where "G@s \<equiv> G `s"

lemmas object_selector_simps =
  apply_cons_head[folded object_selector_def, simp]
  apply_cons_tail[folded object_selector_def, simp]

lemma not_in_cons_dom: "\<lbrakk>x \<noteq> a; x \<notin> A\<rbrakk> \<Longrightarrow> x \<notin> cons a A" by auto

ML \<open>
(*
  Solver for the condition "x \<notin> dom A" arising from applications of
  apply_cons_head to object selector simplifications.
*)

fun selector_tac ctxt =
  REPEAT o (EqSubst.eqsubst_tac ctxt [0] @{thms cons_dom})
  THEN' CHANGED_PROP o REPEAT_ALL_NEW (match_tac ctxt @{thms not_in_cons_dom})
  THEN' REPEAT o SOLVED' (string_neq_tac ctxt)
  THEN' (EqSubst.eqsubst_tac ctxt [0] @{thms dom_empty})
  THEN' resolve_tac ctxt @{thms emptyset}

val selector_subgoaler = map_theory_simpset (Simplifier.set_subgoaler
  (fn ctxt => selector_tac ctxt ORELSE' asm_simp_tac ctxt))
\<close>

setup \<open>selector_subgoaler\<close>


(* Eventually want to have syntax like

    object Monoid
    fixes A
    contains op id
    where
      "op \<in> A \<rightarrow> A \<rightarrow> A"
      "e \<in> A"
      "x \<in> A \<Longrightarrow> op `x `e = x"
      "x \<in> A \<Longrightarrow> op `e `x = x"

  which should generate

    Monoid A \<equiv> type (\<lambda>obj::set.
      (* "contains" part *)
      {@op, @id} \<subseteq> dom obj \<and>
      (* "where" part *)
      obj@@op \<in> A \<rightarrow> A \<rightarrow> A \<and>
      obj@@e \<in> A \<and>
      \<forall>x. x \<in> A \<longrightarrow> op `x `e = x \<and>
      \<forall>x. x \<in> A \<longrightarrow> op `e `x = x)
*)


end
