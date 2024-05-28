section \<open>Isar Integration Tests\<close>
theory Isar_Integration_Tests
imports Soft_Types.Soft_Types_HOL
begin

text \<open>Not all of the examples below work as expected yet.
First, assume a little bit of context:\<close>

declare [[trace_soft_types]]

typedecl set

experiment
  fixes Set :: "set type"
  and Element :: "set \<Rightarrow> set type"
  and list :: "set \<Rightarrow> set"
  and nil :: "set \<Rightarrow> set"
  and cons :: "set \<Rightarrow> set \<Rightarrow> set \<Rightarrow> set"
  assumes nil_type[type]: "nil \<Ztypecolon> (A : Set) \<Rightarrow> Element (list A)"
  and list_cons_type[type]: "cons \<Ztypecolon> (A : Set) \<Rightarrow> Element A \<Rightarrow> Element (list A) \<Rightarrow> Element (list A)"
begin

declare[[auto_elaborate]]

subsection \<open>Top-Level Lemma Statements\<close>

lemma foo: "nil A = B"
proof -
  txt \<open>Assumptions about the type of \<open>A\<close> and \<open>B\<close> are available in the context:\<close>
  print_types
  show ?thesis sorry
qed

text \<open>The assumptions lead to additional premises in the result:\<close>
thm foo


subsection \<open>Local Goals\<close>

text \<open>Currently, the augment operation is not included in "have" statements,
but we would expect it to be:\<close>

notepad
begin
  subsubsection \<open>Example 1\<close>
  fix A B
  have 1: "nil A = B" sorry

  text \<open>Here, \<open>A\<close> and \<open>B\<close> are part of the surrounding context, so the
  assumptions about their type should also live in that context.\<close>
  print_types \<comment> \<open>Types of \<open>A\<close> and \<open>B\<close> are known at this point.\<close>
  thm 1
next
  subsubsection \<open>Example 2\<close>
  have 1: "nil A = B" for A B sorry
  text \<open>Here, \<open>A\<close> and \<open>B\<close> are part of the statement's eigencontext, so the
  assumptions should end up in as premises of the proved fact, similar to a
  top-level lemma statement.\<close>
  thm 1 \<comment> \<open>We get additional assumptions for the proved fact..\<close>
next
  subsubsection \<open>Example 3\<close>
  fix B
  have 1: "nil ? = B" sorry
  text \<open>Similar to Example 1, but one variable is implicit and introduced by elaboration.

  Here, \<open>B\<close> lives in the surrounding context, and \<open>A\<close> is implicitly introduced in the statement
  for the first time. Since the type of \<open>B\<close> depends on \<open>A\<close>, we cannot generalize \<open>A\<close> which must
  be introduced into the resulting context.

  This situation should probably emit a warning. The introduced variable can also not be referred
  to in the text.\<close>
  print_types
  thm 1
next
  subsubsection \<open>Example 4\<close>
  have 1: "nil ? = B" for B sorry
  text \<open>Similar to Example 2, but with one implicit argument.
  Here, the implicit \<open>A\<close> can be fully generalized. It also cannot be referenced
  in the text.\<close>
  print_types \<comment> \<open>FIXME: implicit variable should not appear here.\<close>
  thm 1 \<comment> \<open>FIXME: Should be fully generalized.\<close>
end


subsection \<open>Definitions\<close>

text \<open>Definitions work (for now) by just purging the type information, which is
not needed for the primitive definition.

Ideally, we should infer and save type information for the defined constant, but
we postpone this as future work for now. Users can always derive type information
afterwards.\<close>

definition f where "f A x = cons A x (nil A)"

end


end