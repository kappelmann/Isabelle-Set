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

definition Function :: "set type"
  where [typedef]: "Function \<equiv> type (\<lambda>f. \<exists> A B. f \<in> A \<rightarrow> B)"

lemma FunctionI [derive]: "f : element (\<Prod>a \<in> A. (B a)) \<Longrightarrow> f : Function"
  by unfold_types (auto dest: function_forget)

lemma FunctionE: assumes "f : Function"
  obtains A B where "f \<in> A \<rightarrow> B"
  unfolding Function_def using assms by unfold_types auto

definition [typedef]: "Object \<equiv> Function"

\<comment> \<open>Note Kevin: We need to think about how the lifting of lemmas
from functions to objects should work.\<close>
definition "object graph = graph"

lemma object_type [type]: "object : Function \<Rightarrow> Object"
  unfolding Object_def object_def by discharge_types

definition "extend Base Ext \<equiv> object (glue {
  THE graph. Base = object graph,
  THE graph. Ext = object graph
})"


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

lemma object_selector_extend: assumes "Base : Object" "Ext : Object"
  and "a \<in> object_fields Base"
  and "a \<in> object_fields Ext \<Longrightarrow> object_selector Base a = object_selector Ext a"
  shows "object_selector (extend Base Ext) a = object_selector Base a"
proof -
  from assms(1) obtain A B where 1: "Base \<in> A \<rightarrow> B"
    unfolding Object_def using FunctionE by auto
  from assms(2) obtain A' B' where 2: "Ext \<in> A' \<rightarrow> B'"
    unfolding Object_def using FunctionE by auto
  let ?C = "B \<union> B'"
  from 1 2 have 3: "Base \<in> A \<rightarrow> ?C" "Ext \<in> A' \<rightarrow> ?C"
    by (auto intro: function_enlarge_range')
  from 1 2 have 4: "a \<in> dom Base \<Longrightarrow> a \<in> A" "a \<in> A' \<Longrightarrow> a \<in> dom Ext"
    by simp_all
  show ?thesis using assms(3-4)
    unfolding object_selector_def object_def object_fields_def extend_def
    by (simp only: the_sym_eq_trivial)
      (blast intro: apply_glue_bin[OF 3] dest: 4)
qed

lemma object_selector_extend': assumes "Base : Object" "Ext : Object"
  and "a \<in> object_fields Ext"
  and "a \<in> object_fields Base \<Longrightarrow> object_selector Base a = object_selector Ext a"
  shows "object_selector (extend Base Ext) a = object_selector Ext a"
proof -
  from assms(1) obtain A B where 1: "Base \<in> A \<rightarrow> B"
    unfolding Object_def using FunctionE by auto
  from assms(2) obtain A' B' where 2: "Ext \<in> A' \<rightarrow> B'"
    unfolding Object_def using FunctionE by auto
  let ?C = "B \<union> B'"
  from 1 2 have 3: "Base \<in> A \<rightarrow> ?C" "Ext \<in> A' \<rightarrow> ?C"
    by (auto intro: function_enlarge_range')
  from 1 2 have 4: "a \<in> dom Ext \<Longrightarrow> a \<in> A'" "a \<in> A \<Longrightarrow> a \<in> dom Base"
    by simp_all
  show ?thesis using assms(3-4)
    unfolding object_selector_def object_def object_fields_def extend_def
    by (simp only: the_sym_eq_trivial)
      (blast intro: apply_glue_bin'[OF 3] dest: 4)
qed

lemma object_extend_preserve: assumes "Base : Object" "Ext : Object"
  and "s \<in> object_fields Base"
  and "s \<in> object_fields Ext \<Longrightarrow> object_selector Base s = object_selector Ext s"
  and "P (object_selector Base s)"
  shows "P (object_selector (extend Base Ext) s)"
  using assms(5) by (subst object_selector_extend[OF assms(1-4)])

lemma extend_typeI: assumes "Base : Object" "Ext : Object"
  and "\<And>a. \<lbrakk>a \<in> object_fields Base \<inter> object_fields Ext\<rbrakk>
    \<Longrightarrow> object_selector Base a = object_selector Ext a"
  shows "extend Base Ext : Object"
proof -
  from assms(1) obtain A B where 1: "Base \<in> A \<rightarrow> B"
    unfolding Object_def using FunctionE by auto
  from assms(2) obtain A' B' where 2: "Ext \<in> A' \<rightarrow> B'"
    unfolding Object_def using FunctionE by auto
  let ?C = "B \<union> B'"
  from 1 2 have 3: "Base \<in> A \<rightarrow> ?C" "Ext \<in> A' \<rightarrow> ?C"
    by (auto intro: function_enlarge_range')
  from assms(3) have 4: "\<And>a. a \<in> A' \<and> a \<in> A \<Longrightarrow> Base `a = Ext `a"
    unfolding object_selector_def object_fields_def object_def by simp
  show ?thesis unfolding extend_def object_def
    by (unfold_types, rule exI[where ?x="A \<union> A'"], rule exI[where ?x="B \<union> B'"],
      rule glue_pairI) (auto intro: 4)
qed

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


end
