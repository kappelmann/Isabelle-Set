theory Set_Extension_T
  imports Set_T Isabelle_Set.Set_Extension
begin

locale set_extension_lifting =
  ext: set_extension A Rep inj
  for A Rep inj
begin

abbreviation "abs \<equiv> ext.Abs"
abbreviation "rep \<equiv> ext.Rep"
abbreviation "Abs \<equiv> ext.abs_image"

abbreviation "T \<equiv> Iso_Rel Rep abs"

lemma z_property_T: "z_property T"
  using z_property_Iso_Rel .

lemma bijection_ext: "bijection Rep Abs abs rep"
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

lemma left_unique_T: "left_unique T"
  using left_unique_Iso_Rel bijection_ext .

lemma ext_tranfer_triple: "transfer_triple T abs rep"
  using bijection_transfer_triple bijection_ext .

end

end