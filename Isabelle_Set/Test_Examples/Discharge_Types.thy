section \<open>Examples for the automatic type derivation procedure.\<close>

theory Discharge_Types
  imports "../Isabelle_Set"
begin

text \<open>
  Proving that something is in some universe.
\<close>

lemma "Inl {} : element (Univ A)"
  by discharge_types



end
