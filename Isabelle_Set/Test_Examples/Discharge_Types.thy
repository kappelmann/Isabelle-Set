section \<open>Examples for the automatic type derivation procedure.\<close>

theory Discharge_Types
  imports "../Isabelle_Set"
begin

text \<open>Proving that something is in some universe.\<close>

lemma "inl {}: element (univ A)"
  by discharge_types

text \<open>Eta-normalization.\<close>

lemma "C A: T \<Longrightarrow> C (\<lambda>x. A x): T"
  by (subst eta_contract_eq) discharge_types

lemma "C (\<lambda>x y z. D x y z): T \<Longrightarrow> C D: T"
  by discharge_types

text \<open>Function application.\<close>

lemma "\<lbrakk>f: A \<Rightarrow> B; a: A\<rbrakk> \<Longrightarrow> f a: B"
  by discharge_types


end
