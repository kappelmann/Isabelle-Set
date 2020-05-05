section \<open>Illustrations of the Isar integration\<close>

theory Implicit_Assumptions
  imports "../Ordered_Pairs"
begin


text \<open>
  Not all of the examples below work as expected yet.


  First, assume a little bit of context:
\<close>

declare [[auto_elaborate, trace_soft_types, quick_and_dirty]]

axiomatization
  List :: "set \<Rightarrow> set"
    and Nil :: "set \<Rightarrow> set"
    and Cons :: "set \<Rightarrow> set \<Rightarrow> set \<Rightarrow> set"
    where Nil_type[type]: "Nil: (A: set) \<Rightarrow> element (List A)"
    and List_Cons_type[type]: "Cons: (A: set) \<Rightarrow> element A \<Rightarrow> element (List A) \<Rightarrow> element (List A)" 


subsection \<open>Top-level lemma statements\<close>

lemma foo: "Nil A = B"
proof -

  txt \<open>Assumptions about the type of \<open>A\<close> and \<open>B\<close> are available in the context:\<close>

  print_types

  show ?thesis sorry
qed

text \<open>The assumptions lead to additional premises in the result:\<close>

thm foo



subsection \<open>Local goals\<close>

text \<open>
  Currently, the augment operation is not included in "have" statements,
  but we would expect it to be:
\<close>

notepad
begin

  subsubsection \<open>Example 1\<close>

  fix A B
  have 1: "Nil A = B"
    sorry

  text \<open>
    Here, \<open>A\<close> and \<open>B\<close> are part of the surrounding context, so the assumptions about
    their type should also live in that context.
  \<close>
  print_types \<comment> \<open>Types of \<open>A\<close> and \<open>B\<close> are known at this point.\<close>

  thm 1

next

  subsubsection \<open>Example 2\<close>

  have 1: "Nil A = B" for A B
    sorry

  text \<open>
    Here, \<open>A\<close> and \<open>B\<close> are part of the statement's eigencontext, so the assumptions should end
    up in as premises of the proved fact, similar to a top-level lemma statement.
  \<close>

  thm 1 \<comment> \<open>We get additional assumptions for the proved fact..\<close>

next

  subsubsection \<open>Example 3\<close>

  fix B
  have 1: "Nil ? = B"
    sorry

  text \<open>
    Similar to Example 1, but one variable is implicit and introduced by elaboration.
  
    Here, \<open>B\<close> lives in the surrounding context, and \<open>A\<close> is implicitly introduced in the statement
    for the first time. Since the type of \<open>B\<close> depends on \<open>A\<close>, we cannot generalize \<open>A\<close> which must
    be introduced into the resulting context.

    This situation should probably emit a warning. The introduced variable can also not be referred
    to in the text.
  \<close>

  print_types
  thm 1

next

  subsubsection \<open>Example 4\<close>

  have 1: "Nil ? = B" for B
    sorry

  text \<open>
    Similar to Example 2, but with one implicit.

    Here, the implicit \<open>A\<close> can be fully generalized. It also cannot be referenced in the text.
  \<close>

  print_types \<comment> \<open>FIXME: implicit variable should not appear here.\<close>
  thm 1 \<comment> \<open>FIXME: Should be fully generalized.\<close>

end
  


subsection \<open>Definitions\<close>


text \<open>
  Definitions work (for now) by just purging the type information, which is
  not needed for the primitive definition.

  Ideally, we should infer and save type information for the defined constant, but
  we postpone this as future work for now. Users can always derive type information
  afterwards.
\<close>


definition f where "f A x = Cons A x (Nil A)"







end
