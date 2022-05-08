theory Set_Type
  imports Set_T Isabelle_Set.Sets
begin

lemma in_dom_eqD: "in_dom (Eq_Rel A) x \<Longrightarrow> x : Element A"
  unfolding Eq_Rel_def in_dom_Iso_Rel_if_mem
  using ElementI .

end