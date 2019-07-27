theory Discharge_Types_Incompleteness
  imports "../Isabelle_Set"
begin

text \<open>
  Exposes a problem in @{method discharge_types}.
\<close>

lemma "Inl {} : element (Univ A)"
  by discharge_types


end
