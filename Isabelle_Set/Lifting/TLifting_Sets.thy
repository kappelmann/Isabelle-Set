theory TLifting_Sets
  imports
    Lifting_Sets
    Isabelle_Set.Sets
begin

lemma in_dom_eqD: "in_dom (Eq_Rel A) x \<Longrightarrow> x : Element A"
  unfolding Eq_Rel_def in_dom_Iso_Rel_iff_mem
  using ElementI .


end