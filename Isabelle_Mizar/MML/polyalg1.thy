theory polyalg1
imports vectsp_2
begin

abbreviation AlgebraStr_fields_prefix ("AlgebraStr'_fields _" [110] 110) where 
 "AlgebraStr_fields F \<equiv> (#
   carrier \<rightarrow> (\<lambda>S. set);
   addF \<rightarrow> (\<lambda>S. BinOp-of the carrier of S);
   ZeroF \<rightarrow> (\<lambda>S. Element-of the carrier of S);
   multF \<rightarrow> (\<lambda>S. BinOp-of the carrier of S);
   OneF \<rightarrow> (\<lambda>S. Element-of the carrier of S);
   lmult \<rightarrow>  Function-of' [: the carrier of F,the' carrier ':], the' carrier#)"

mdef AlgebraStr_over ("AlgebraStr-over _") where
  mlet "F be 1-sorted"
  "struct [ doubleLoopStr\<bar> ModuleStr-over F] AlgebraStr-over F AlgebraStr_fields F
defined on {carrier}\<union>{addF}\<union>{ZeroF}\<union>{multF}\<union>{OneF}\<union>{lmult}"
    by (auto simp add: doubleLoopStr ModuleStr_over,
     auto intro!: Fields_add_3_arg_Mode First_0_arg_Mode dest!:field_E simp add:string)

mtheorem
 mlet "F be 1-sorted",
     "X be set",   "A be BinOp-of X","z be Element-of X",
       "M be BinOp-of X","E be Element-of X", "L be Function-of [:the carrier of F,X:],X"
   "cluster [#carrier\<mapsto>X; addF\<mapsto>A; ZeroF\<mapsto>z; multF\<mapsto>M; OneF\<mapsto>E;lmult \<mapsto> L #] \<rightarrow> strict( AlgebraStr-over F)"
 unfolding AlgebraStr_over_def
    by (auto,rule struct_aggr_ancesors_rule, 
        auto intro!: aggrI struct_aggr3  struct_aggr0 Fields_add_3_arg_Mode First_0_arg_Mode dest!:field_E simp add:string)
end
