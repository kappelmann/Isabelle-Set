theory pre_topc
imports struct_0
begin

abbreviation "TopStruct_fields \<equiv> (#carrier \<rightarrow> set';topology \<rightarrow> Subset-Family-of' the' carrier #)"




mdef TopStruct ("TopStruct") where  "struct [1-sorted] TopStruct 
 (#carrier \<rightarrow> set';topology \<rightarrow> Subset-Family-of' the' carrier #)
   defined on {carrier}\<union>{topology}"
  by (auto simp add: one_sorted,
     auto intro!: Fields_add_3_arg_Mode First_0_arg_Mode dest!:field_E simp add:string)

mtheorem
  mlet "X be set",   "T be  Subset-Family-of X"
   "cluster [#carrier\<mapsto>X; topology\<mapsto> T#] \<rightarrow> strict(TopStruct)"
unfolding TopStruct_def
    by (auto,rule struct_aggr_ancesors_rule, 
        auto intro!: aggrI struct_aggr3  struct_aggr0 Fields_add_3_arg_Mode First_0_arg_Mode dest!:field_E simp add:string)
  
mtheorem
  mlet "X be TopStruct"
  "cluster  (the topology of X) \<rightarrow> Subset-Family-of (the carrier of X)" 
     using field TopStructE by auto

end
