theory group_1a
imports algstr_0 pre_topc
begin

mdef group_1a_topaddgrstr ("TopaddGrStr") where
  "struct [addMagma\<bar>TopStruct] TopaddGrStr 
(#carrier \<rightarrow> set'; addF\<rightarrow> BinOp-of' the' carrier;topology \<rightarrow> Subset-Family-of' the' carrier #) 
   defined on {carrier}\<union>{addF}\<union>{topology}"
  by (auto simp add: addMagma TopStruct,
     auto intro!: Fields_add_3_arg_Mode First_0_arg_Mode dest!:field_E simp add:string)

end
