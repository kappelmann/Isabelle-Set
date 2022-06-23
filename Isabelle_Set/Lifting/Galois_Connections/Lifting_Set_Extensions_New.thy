theory Lifting_Set_Extensions_New
  imports
    Lifting_Relations_New
    Isabelle_Set.Set_Extension
begin

context set_extension
begin

(* lemma galois_property: "galois_property (Eq_Rel B) (Eq_Rel abs_image) Abs Rep"
  unfolding Eq_Rel_def Iso_Rel_def by (rule galois_propertyI)

lemma bijection: "bijection B abs_image abs rep"
  apply (rule bijectionI)
  apply (rule ElementD)
  apply (rule Dep_fun_typeE[OF Abs_type])
  apply (fact ElementI)
  apply (rule ElementD)
  apply (rule Dep_fun_typeE[OF Rep_type])
    apply (fact ElementI)
  apply (rule inverse_onI)
    apply (rule Rep_Abs_inv)
  apply (rule inverse_onI)
    apply (fact Abs_Rep_inv)
  done

lemma injective: "LBinary_Relations.injective rel"
  using bijection
  by (intro injective_Iso_Rel_if_injective_on injective_on_if_bijection)

lemma "Eq_rep rel = Eq_Rel B"
  using Eq_rep_Iso_Rel_eq_if_bijection bijection .

lemma lifting_triple: "lifting_triple rel abs rep"
  using lifting_triple_Iso_Rel_if_bijection bijection . *)

end


end