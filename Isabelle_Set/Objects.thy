\<^marker>\<open>creator "Alexander Krauss"\<close>
\<^marker>\<open>creator "Josh Chen"\<close>
\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Structure Objects\<close>
theory Objects
  imports
    TFunctions
    Strings
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

lemma object_insert_pair_eq_extend [simp]:
  "object (insert \<langle>x, y\<rangle> O) = object (extend x y O)"
  unfolding object_def using insert_pair_eq_extend by simp

lemma object_fields_empty_eq [simp]:
  "object_fields (object {}) = {}"
  unfolding object_fields_def object_def by auto

lemma object_fields_extend_eq [simp]:
  "object_fields (object (extend x y A)) = insert x (object_fields (object A))"
  unfolding object_fields_def object_def by auto

definition "object_selector O s \<equiv> (THE graph. O = object graph)`s"

bundle isa_set_object_selector_syntax
  begin notation object_selector ("_@_" [999, 1000]) end
bundle no_isa_set_object_selector_syntax
  begin no_notation object_selector ("_@_" [999, 1000]) end

unbundle isa_set_object_selector_syntax

lemma
  shows object_selector_extend_eq [simp]:
    "x \<notin> object_fields (object A) \<Longrightarrow> (object (extend x y A))@x = y"
  and object_selector_extend_eq' [simp]:
    "x \<noteq> y \<Longrightarrow> (object (extend y z A))@x = (object A)@x"
  unfolding object_def object_selector_def object_fields_def by auto

(*TODO: solver has some bugs*)
(* ML \<open>
(*Solver for the condition "x \<notin> dom A" arising object selector simplifications*)

fun selector_tac ctxt =
  REPEAT o (EqSubst.eqsubst_tac ctxt [0] @{thms dom_extend_eq})
  THEN' CHANGED_PROP o REPEAT_ALL_NEW (match_tac ctxt @{thms not_mem_insert_if_not_mem_if_ne})
  THEN' REPEAT o SOLVED' (string_ne_tac ctxt)
  THEN' (EqSubst.eqsubst_tac ctxt [0] @{thms dom_empty_eq})
  THEN' resolve_tac ctxt @{thms emptyset}

val selector_subgoaler = map_theory_simpset (Simplifier.set_subgoaler
  (fn ctxt => selector_tac ctxt ORELSE' asm_simp_tac ctxt))
\<close>
setup \<open>selector_subgoaler\<close> *)


end