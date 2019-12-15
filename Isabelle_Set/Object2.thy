section \<open>Structure objects\<close>

theory Object2
imports Function String

begin

text \<open>
We'd eventually want to have syntax like
  \<open> object Monoid
    fixes A
    contains op id
    where
      "op \<in> A \<rightarrow> A \<rightarrow> A"
      "e \<in> A"
      "x \<in> A \<Longrightarrow> op `x `e = x"
      "x \<in> A \<Longrightarrow> op `e `x = x"
  \<close>
to define structure object types, which should generate
  \<open> Monoid A \<equiv> type (\<lambda>obj::set.
      (* "contains" part *)
      {@op, @id} \<subseteq> dom obj \<and>
      (* "where" part *)
      obj@@op \<in> A \<rightarrow> A \<rightarrow> A \<and>
      obj@@e \<in> A \<and>
      \<forall>x. x \<in> A \<longrightarrow> op `x `e = x \<and>
      \<forall>x. x \<in> A \<longrightarrow> op `e `x = x)
  \<close>.
\<close>


subsection \<open>Object instance constructors\<close>

definition "object graph = graph"


subsection \<open>Object fields\<close>

definition "object_fields O = dom (THE graph. O = object graph)"

lemma object_fields_simp [simp]:
  "object_fields (object (cons \<langle>x, y\<rangle> A)) = cons x (dom A)"
  unfolding object_fields_def object_def by auto

definition object_selector :: \<open>set \<Rightarrow> set \<Rightarrow> set\<close> ("_@_" [999, 1000])
  where "O@s \<equiv> (THE graph. O = object graph) `s"

lemma object_selector_simps [simp]:
  "x \<notin> dom A \<Longrightarrow> (object (cons \<langle>x, y\<rangle> A)) @ x = y"
  "x \<noteq> y \<Longrightarrow> (object (cons \<langle>y, z\<rangle> A)) @ x = A `x"
  unfolding object_def object_selector_def
  using apply_cons_head apply_cons_tail by auto

lemma not_in_cons_dom: "\<lbrakk>x \<noteq> a; x \<notin> A\<rbrakk> \<Longrightarrow> x \<notin> cons a A" by auto

ML \<open>
(*Solver for the condition "x \<notin> dom A" arising object selector simplifications*)

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


subsection \<open>Object composition\<close>

text \<open>
  For now object composition is just the set-theoretic union of the graphs,
  which means that it's only well-defined for object instances with disjoint
  fields.
\<close>

definition object_composition :: \<open>set \<Rightarrow> set \<Rightarrow> set\<close> (infixl "[+]" 69)
  where "O1 [+] O2 = O1 \<union> O2"

lemma object_composition_selector [simp]:
  assumes
    "object_fields O1 \<inter> object_fields O2 = {}"
  shows
    "(O1 [+] O2) @ x = (if x \<in> object_fields O1 then O1 @ x else O2 @ x)"
  using assms
  unfolding object_composition_def object_fields_def object_selector_def object_def
  by (auto intro: apply_bin_union1 apply_bin_union2)


end
