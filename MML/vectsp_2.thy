theory vectsp_2
imports vectsp_1
begin

abbreviation RightModStr_fields_prefix ("RightModStr'_fields _" [110] 110) where
 "RightModStr_fields F \<equiv> (#carrier \<rightarrow> set'; addF\<rightarrow> BinOp-of' the' carrier;ZeroF \<rightarrow> Element-of' the' carrier;
               rmult \<rightarrow>  Function-of' [:' the' carrier,the carrier of F:], the' carrier #)"

mdef RightModStr_over ("RightModStr-over _") where
  mlet "F be 1-sorted"
  "struct [addLoopStr] RightModStr-over F (#carrier \<rightarrow> set'; addF\<rightarrow> BinOp-of' the' carrier;ZeroF \<rightarrow> Element-of' the' carrier;
               rmult \<rightarrow>  Function-of' [:' the' carrier,the carrier of F:], the' carrier #) defined on 
  {carrier}\<union>{addF}\<union>{ZeroF}\<union>{rmult}"
    by (auto simp add: addLoopStr,
     auto intro!: Fields_add_3_arg_Mode First_0_arg_Mode dest!:field_E simp add:string)

mtheorem
  mlet "F be 1-sorted", "X be set",   "A be BinOp-of X", "z be Element-of X",
   "R be Function-of [:X, the carrier of F:],X" 
   "cluster [#carrier\<mapsto>X; addF\<mapsto>A; ZeroF\<mapsto>z; rmult\<mapsto>R #] \<rightarrow> strict(RightModStr-over F)"
 unfolding RightModStr_over_def
    by (auto,rule struct_aggr_ancesors_rule, 
        auto intro!: aggrI struct_aggr3  struct_aggr0 Fields_add_3_arg_Mode First_0_arg_Mode dest!:field_E simp add:string)

mdef BiModStr_over ("BiModStr-over _") where
  mlet "F be 1-sorted"
  "struct [ModuleStr-over F\<bar>RightModStr-over F] BiModStr-over F (#carrier \<rightarrow> set'; addF\<rightarrow> BinOp-of' the' carrier; ZeroF \<rightarrow> Element-of' the' carrier;
               lmult \<rightarrow>  Function-of' [: the carrier of F,the' carrier ':], the' carrier;
               rmult \<rightarrow>  Function-of' [:' the' carrier,the carrier of F:], the' carrier #) defined on
   {carrier}\<union>{addF}\<union>{ZeroF}\<union>{lmult}\<union>{rmult}"
    by (auto simp add: ModuleStr_over RightModStr_over,
     auto intro!: Fields_add_3_arg_Mode First_0_arg_Mode dest!:field_E simp add:string)

mtheorem
  mlet "F be 1-sorted", "X be set",   "A be BinOp-of X", "z be Element-of X",
   "L be Function-of [: the carrier of F,X:],X", 
   "R be Function-of [:X, the carrier of F:],X" 
   "cluster [#carrier\<mapsto>X; addF\<mapsto>A; ZeroF\<mapsto>z; lmult \<mapsto> L; rmult\<mapsto>R #] \<rightarrow> strict(BiModStr-over F)"
unfolding BiModStr_over_def
    by (auto,rule struct_aggr_ancesors_rule, 
        auto intro!: aggrI struct_aggr3  struct_aggr0 Fields_add_3_arg_Mode First_0_arg_Mode dest!:field_E simp add:string)

end
