theory Lifting_Set_Extensions
  imports
    Lifting_Sets
    Isabelle_Set.Set_Extension
begin

locale set_extension_lifting =
  ext: set_extension A Rep inj
  for A Rep inj
begin

abbreviation "abs \<equiv> ext.Abs"
abbreviation "rep \<equiv> ext.Rep"
abbreviation "Abs \<equiv> ext.abs_image"

abbreviation "rel \<equiv> Iso_Rel Rep abs"

lemma z_property: "z_property rel"
  using z_property_Iso_Rel .

lemma bijection: "bijection Rep Abs abs rep"
  apply (rule bijectionI)
  apply (rule ElementD)
  apply (rule Dep_fun_typeE[OF ext.Abs_type])
  apply (fact ElementI)
  apply (rule ElementD)
  apply (rule Dep_fun_typeE[OF ext.Rep_type])
    apply (fact ElementI)
  apply (rule ext.Rep_Abs_inv)
  apply (fact ext.Abs_Rep_inv)
  done

lemma left_unique: "left_unique rel"
  using left_unique_Iso_Rel_if_bijection bijection .

lemma lifting_triple: "lifting_triple rel abs rep"
  using lifting_triple_Iso_Rel_if_bijection bijection .

end

end