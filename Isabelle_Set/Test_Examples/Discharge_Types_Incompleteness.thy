theory Discharge_Types_Incompleteness
  imports "../Isabelle_Set"
begin

text \<open>
  Exposes a problem in @{method discharge_types}.
\<close>

lemma "Inl {} : element (Univ A)"
  apply discharge_types (* fails although both rules below are marked as derivation rules *)
  apply (rule Inl_Univ)
  apply (rule Univ_type_empty)
  done


end
