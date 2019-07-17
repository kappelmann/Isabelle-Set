theory Implicit_Assumptions
  imports "../Pair"
begin


axiomatization
  List :: "set \<Rightarrow> set"
    and Nil :: "set \<Rightarrow> set"
    and Cons :: "set \<Rightarrow> set \<Rightarrow> set \<Rightarrow> set"
    and append :: "set \<Rightarrow> set \<Rightarrow> set \<Rightarrow> set"
    where
      Nil_type[type]: "Nil : (A: set) \<Rightarrow> element (List A)"
    and List_Cons_type[type]: "Cons : (A: set) \<Rightarrow> element A \<Rightarrow> element (List A) \<Rightarrow> element (List A)" 
    and append[type]: "append : (A: set) \<Rightarrow> element (List A) \<Rightarrow> element (List A) \<Rightarrow> element (List A)"


setup \<open>Soft_Type_Operations.register_operations Isar_Integration.operations\<close>
declare [[auto_elaborate, trace_soft_types]]

declare [[quick_and_dirty]] (* some sorries below *)

lemma foo: "Nil A = B"
proof -

  txt \<open>Assumptions about the type of \<open>A\<close> and \<open>B\<close> are available in the context:\<close>

  print_types

  show ?thesis sorry
qed

text \<open>The assumptions lead to additional premises in the result:\<close>

thm foo


text \<open>
  Currently, the augment/purge operations are not called in "have" statements,
  but we would expect them to be:
\<close>

notepad
begin
  fix A B
  have a: "Nil A = B" sorry

  thm a (* No premises here, but there should be... *)

end

text \<open>
  Definitions work (for now) by just purging the type information, which is
  not needed for the primitive definition.

  Ideally, we should infer and save type information for the defined constant.
\<close>


definition f where "f A x = Cons A x (Nil A)"

















end
