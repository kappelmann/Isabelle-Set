theory graph_1
imports struct_0
begin
  mdef MultiGraphStruct :: "Ty" ("MultiGraphStruct") where
  "struct [2-sorted]MultiGraphStruct
      (#carrier \<rightarrow> set';
        carrier` \<rightarrow> set';
        Source \<rightarrow> Function-of' the' carrier`, the' carrier;
        Target \<rightarrow> Function-of' the' carrier`, the' carrier #)
    defined on {carrier}\<union>{carrier`}\<union>{Source}\<union>{Target}"
    by (auto simp add: two_sorted,
     auto intro!: Fields_add_3_arg_Mode First_0_arg_Mode dest!:field_E simp add:string)

mtheorem 
 mlet "X be MultiGraphStruct"
 "cluster  (the Source of X) \<rightarrow> Function-of the carrier` of X, the carrier of X"
using field MultiGraphStructE by auto

mtheorem 
  mlet "X be MultiGraphStruct"
  "cluster (the Target of X) \<rightarrow> Function-of the carrier` of X, the carrier of X"
using field MultiGraphStructE by auto 

mtheorem
  mlet "X be set", "Y be set", "S be Function-of Y,X", "T be Function-of Y,X"
  "cluster [#carrier\<mapsto> X ; carrier`\<mapsto>Y; Source\<mapsto>S; Target\<mapsto>T #] \<rightarrow> strict(MultiGraphStruct)"
unfolding MultiGraphStruct_def
  by (auto,rule struct_aggr_ancesors_rule,
    auto intro!: aggrI struct_aggr3  struct_aggr0 Fields_add_3_arg_Mode First_0_arg_Mode dest!:field_E simp add:
          string)

abbreviation graph_1_mode_1_prefix ("Vertex-of _" [150] 150)
  where "Vertex-of X \<equiv> Element-of (the carrier of X)"

abbreviation graph_1_mode_2_prefix ("Edge-of _" [150] 150)
  where "Edge-of X \<equiv> Element-of (the carrier` of X)"


mdef graph_1_def_1 ("dom \<^bsub>_\<^esub> _" [999,105] 105) where
 mlet "C be MultiGraphStruct", "f be Edge-of C"
 "func dom\<^bsub>C\<^esub> f \<rightarrow> Vertex-of C equals
     (the Source of C) . f if (C is non void-struct \<bar>non empty-struct)
        otherwise the Vertex-of C"
proof(intro conjI impI)
  assume [ty]: "C is non void-struct \<bar> non empty-struct"
  show "the' Source(C) . f is Vertex-of C" 
    using funct_2_def_5[of "the carrier` of C" "the carrier of C" "the Source of C"] by mauto
  next
    assume  "\<not>C is non void-struct \<bar> non empty-struct" 
    thus "(the Vertex-of C) is Vertex-of C" by auto
qed mauto

mdef graph_1_def_2 ("cod \<^bsub>_\<^esub> _" [999,105] 105) where
 mlet "C be MultiGraphStruct", "f be Edge-of C"
 "func cod\<^bsub>C\<^esub>f \<rightarrow> Vertex-of C equals
      (the Target of C) . f if (C is non void-struct \<bar>non empty-struct)
        otherwise the Vertex-of C"
proof(intro conjI impI)
   assume [ty]: "C is non void-struct \<bar> non empty-struct"
  show "((the Target of C) . f) is Vertex-of C" 
    using funct_2_def_5[of "the carrier` of C" "the carrier of C" "the Target of C"] by mauto
  next
    assume  "\<not>C is non void-struct \<bar> non empty-struct" 
    thus "(the Vertex-of C) is Vertex-of C" by auto
qed mauto

text_raw {*\DefineSnippet{redefine_func_equals}{*}
abbreviation (input) redefine_func_equals ("let _ redefine func _ \<rightarrow> _ equals _" [10,10,10,10] 10)
  where "let lt redefine func F \<rightarrow> M equals term \<equiv>
   ( lt \<longrightarrow> ( F be M \<and> F = term))"
text_raw {*}%EndSnippet*}

theorem graph_1_def_3[simplified,rule_format]:
  "let C be non void-struct \<bar> non empty-struct \<bar> MultiGraphStruct \<and> f be Edge-of C
   redefine func dom\<^bsub>C\<^esub>f \<rightarrow> Vertex-of C equals
      (the Source of C) . f"
proof
  assume [ty]: "C be non void-struct \<bar> non empty-struct \<bar> MultiGraphStruct \<and> f be Edge-of C"
  have A: "dom\<^bsub>C\<^esub> f is Vertex-of C" by mauto
  thus "dom\<^bsub>C\<^esub> f is Vertex-of C \<and> dom\<^bsub>C\<^esub> f = (the Source of C) . f" using graph_1_def_1 by auto
qed

theorem graph_1_def_4[simplified,rule_format]:
  "let C be non void-struct \<bar> non empty-struct \<bar> MultiGraphStruct \<and> f be Edge-of C
   redefine func cod\<^bsub>C\<^esub>f \<rightarrow> Vertex-of C equals
      (the Target of C) . f"
proof
  assume [ty]: "C be non void-struct \<bar> non empty-struct \<bar> MultiGraphStruct \<and> f be Edge-of C"
  have A: "cod\<^bsub>C\<^esub> f is Vertex-of C" by mauto
  thus "cod\<^bsub>C\<^esub> f is Vertex-of C \<and> cod\<^bsub>C\<^esub> f = (the Target of C) . f" using graph_1_def_2 by auto
qed

end
