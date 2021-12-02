section \<open>Implicit Arguments Tests\<close>
theory Implicit_Arguments_Tests
imports "Soft_Types.Soft_Types_HOL"
begin

declare [[trace_soft_types]]

subsection \<open>Example: Implicit arguments for list operations\<close>

text \<open>This example is similar to the one in \<^file>\<open>./Elaboration_Tests.thy\<close>,
but this time the set arguments are hidden from the syntax.\<close>

typedecl set
(*TODO: does not work in experiment environment*)
axiomatization Set :: "set type"
  and Element :: "set \<Rightarrow> set type"
  and list :: "set \<Rightarrow> set"
  and nil :: "set \<Rightarrow> set"
  and cons :: "set \<Rightarrow> set \<Rightarrow> set \<Rightarrow> set"
  and append :: "set \<Rightarrow> set \<Rightarrow> set \<Rightarrow> set"
  where nil_type [type implicit: 1]: "nil : (A : Set) \<Rightarrow> Element (list A)"
  and cons_type [type implicit: 1]: "cons : (A : Set) \<Rightarrow> Element A \<Rightarrow>
    Element (list A) \<Rightarrow> Element (list A)"
  and append_type [type implicit: 1]: "append : (A : Set) \<Rightarrow> Element (list A) \<Rightarrow>
    Element (list A) \<Rightarrow> Element (list A)"

declare [[auto_elaborate]]

lemma "cons x nil = ys" oops

ML \<open>Elaboration.elaborate_terms \<^context> [
  \<^term>\<open>nil = B\<close>
]\<close>

ML \<open>Elaboration.elaborate_terms \<^context> [
  \<^term>\<open>cons x xs\<close>
]\<close>

lemma
  "append (cons x xs) ys = cons x (append xs ys)"
  "append nil ys = ys"
  oops

