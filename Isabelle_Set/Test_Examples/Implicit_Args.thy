theory Implicit_Args
  imports "../Pair"
begin


subsection \<open>Example: Implicit arguments for list operations\<close>

text \<open>
  This example is similar to the one in \<^file>\<open>./Typing_Examples.thy\<close>, but this time the set arguments
  are hidden from the syntax.
\<close>

axiomatization
  List :: "set \<Rightarrow> set"
  and Nil :: "set \<Rightarrow> set"
  and Cons :: "set \<Rightarrow> set \<Rightarrow> set \<Rightarrow> set"
  and append :: "set \<Rightarrow> set \<Rightarrow> set \<Rightarrow> set"
  where
    Nil_type[type implicit: 1]: "Nil : (A: set) \<Rightarrow> element (List A)"
    and Cons_type[type implicit: 1]: "Cons : (A: set) \<Rightarrow> element A \<Rightarrow> element (List A) \<Rightarrow> element (List A)" 
    and append_type[type implicit: 1]: "append : (A: set) \<Rightarrow> element (List A) \<Rightarrow> element (List A) \<Rightarrow> element (List A)"

declare [[auto_elaborate]]

lemma "Cons x Nil = ys"
  oops




ML \<open>Elaboration.elaborate_terms @{context} [
  @{term "Nil = B"}
]\<close>

ML \<open>Elaboration.elaborate_terms @{context} [
  @{term "Cons x xs"}
]\<close>


lemma 
  "append (Cons x xs) ys = Cons x (append xs ys)"
  "append Nil ys = ys"
  oops



end