\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Inverse\<close>
theory SFunctions_Inverse
  imports
    SFunctions_Base
    Transport.Functions_Inverse
begin

overloading
  inverse_on_set \<equiv> "inverse_on :: set \<Rightarrow> (set \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> set) \<Rightarrow> bool"
  set_inverse_on_pred \<equiv> "inverse_on :: (set \<Rightarrow> bool) \<Rightarrow> set \<Rightarrow> set \<Rightarrow> bool"
  set_inverse_on_set \<equiv> "inverse_on :: set \<Rightarrow> set \<Rightarrow> set \<Rightarrow> bool"
begin
  definition "inverse_on_set (A :: set) :: (set \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> set) \<Rightarrow> bool \<equiv> inverse_on (mem_of A)"
  definition "set_inverse_on_pred (P :: set \<Rightarrow> bool) (f :: set) (g :: set) \<equiv>
    inverse_on P (eval f) (eval g)"
  definition "set_inverse_on_set (A :: set) :: set \<Rightarrow> set \<Rightarrow> bool \<equiv> inverse_on (mem_of A)"
end

lemma inverse_on_set_eq_inverse_on_pred [simp]:
  "(inverse_on (A :: set) :: (set \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> set) \<Rightarrow> bool) = inverse_on (mem_of A)"
  unfolding inverse_on_set_def by simp

lemma inverse_on_set_iff_inverse_on_pred [iff]:
  "inverse_on (A :: set) (f :: set \<Rightarrow> 'a) (g :: 'a \<Rightarrow> set) \<longleftrightarrow> inverse_on (mem_of A) f g"
  by simp

lemma set_inverse_on_pred_iff_inverse_on_pred [iff]:
  "inverse_on (P :: set \<Rightarrow> bool) (f :: set) (g :: set) \<longleftrightarrow> inverse_on P (eval f) (eval g)"
  unfolding set_inverse_on_pred_def by simp

lemma set_inverse_on_set_eq_set_inverse_on_pred [simp]:
  "(inverse_on (A :: set) :: set \<Rightarrow> set \<Rightarrow> bool) = inverse_on (mem_of A)"
  unfolding set_inverse_on_set_def by simp

lemma set_inverse_on_set_iff_set_inverse_on_pred [iff]:
  "inverse_on (A :: set) (f :: set) (g :: set) \<longleftrightarrow> inverse_on (mem_of A) f g"
  by simp

end