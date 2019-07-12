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
declare [[auto_elaborate]]

lemma foo: "Nil A = B"
proof -

  txt \<open>Assumptions about the type of \<open>A\<close> and \<open>B\<close> are available in the context:\<close>
  ML_prf \<open>fst (Soft_Type_Context.Current_Type.get (Context.Proof \<^context>))\<close>

  show ?thesis using [[quick_and_dirty]] sorry
qed

text \<open>The assumptions lead to additional premises in the result:\<close>

thm foo



end
