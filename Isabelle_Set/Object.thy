section \<open>Structure objects\<close>

theory Object
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
  "x \<notin> dom A \<Longrightarrow> (object (cons \<langle>x, y\<rangle> A))@x = y"
  "x \<noteq> y \<Longrightarrow> (object (cons \<langle>y, z\<rangle> A))@x = A`x"
  unfolding object_def object_selector_def by auto

lemma not_in_cons_dom: "\<lbrakk>x \<noteq> a; x \<notin> A\<rbrakk> \<Longrightarrow> x \<notin> cons a A" by auto

ML \<open>
(*Solver for the condition "x \<notin> dom A" arising object selector simplifications*)

fun selector_tac ctxt =
  REPEAT o (EqSubst.eqsubst_tac ctxt [0] @{thms cons_dom})
  THEN' CHANGED_PROP o REPEAT_ALL_NEW (match_tac ctxt @{thms not_in_cons_dom})
  THEN' REPEAT o SOLVED' (string_ne_tac ctxt)
  THEN' (EqSubst.eqsubst_tac ctxt [0] @{thms dom_empty})
  THEN' resolve_tac ctxt @{thms emptyset}

val selector_subgoaler = map_theory_simpset (Simplifier.set_subgoaler
  (fn ctxt => selector_tac ctxt ORELSE' asm_simp_tac ctxt))
\<close>

setup \<open>selector_subgoaler\<close>


end
