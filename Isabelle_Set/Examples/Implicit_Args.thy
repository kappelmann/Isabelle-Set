theory Implicit_Args
  imports "../Pair"
begin


axiomatization
  List :: "set \<Rightarrow> set"
  and Nil :: "set \<Rightarrow> set"
  and Cons :: "set \<Rightarrow> set \<Rightarrow> set \<Rightarrow> set"
  and append :: "set \<Rightarrow> set \<Rightarrow> set \<Rightarrow> set"
  where
    Nil_type[type implicit: 1]: "Nil : (A: set) \<Rightarrow> element (List A)"
    and Cons_type[type implicit: 1]: "Cons : (A: set) \<Rightarrow> element A \<Rightarrow> element (List A) \<Rightarrow> element (List A)" 
    and append_type[type implicit: 1]: "append : (A: set) \<Rightarrow> element (List A) \<Rightarrow> element (List A) \<Rightarrow> element (List A)"





ML \<open> Context.>> (
  Syntax_Phases.term_check 5 "elaboration" Soft_Type_Inference.elaborate
) \<close>


lemma "Cons x Nil = ys"
  oops


ML \<open>
\<^term>\<open>Cons x Nil\<close>
\<close>




ML \<open>Soft_Type_Inference.print_inferred_types @{context} [
  @{term "Nil = B"}
]\<close>

ML \<open>Soft_Type_Inference.print_inferred_types @{context} [
  @{term "Cons x xs"}
]\<close>


lemma 
  "append (Cons x xs) ys = Cons x (append xs ys)"
  "append Nil ys = ys"
  oops



end