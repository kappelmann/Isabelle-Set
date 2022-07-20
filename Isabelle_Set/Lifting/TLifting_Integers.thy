theory TLifting_Integers
  imports
    Isabelle_Set.Integers
    Lifting_Set_Extensions
    TLifting_Functions
    TLifting_Sets
begin

declare[[eta_contract]]

interpretation int_lifting: set_extension_lifting \<nat> int_rep Int_Rep_nonneg
  using set_extension_lifting.intro Int.set_extension_axioms .

lemma int_rep_translation: "Element int_rep = Int_Rep"
  (* should be proven elsewhere *)
  sorry

lemmas transfer_start = Lifting_Basic.lifting_triple_rel_abs_if_in_dom

lemma in_dom_int_lifting_iff_Int_Rep:
  "in_dom int_lifting.rel x \<longleftrightarrow> (x : Int_Rep)"
  unfolding in_dom_Iso_Rel_iff_mem mem_int_rep_iff_Int_Rep ..

lemma in_dom_int_lifting_if_Int_Rep:
  "x : Int_Rep \<Longrightarrow> in_dom int_lifting.rel x"
  using in_dom_int_lifting_iff_Int_Rep by blast

lemma Int_Rep_if_in_dom_int_lifting: "in_dom int_lifting.rel x \<Longrightarrow> x : Int_Rep"
  using in_dom_int_lifting_iff_Int_Rep by blast

schematic_goal "?T Int_Rep_zero ?Int_Abs_zero"
  (* initial step *)
  apply (rule transfer_start[where ?T=int_lifting.rel and ?x=Int_Rep_zero])
  (* search matching transfer-triple *)
  apply (fact int_lifting.lifting_triple)
  (* search for in-dom-rule to translate goal to user friendly form *)
  apply (rule in_dom_int_lifting_if_Int_Rep)
  (* discharge typing subgoal *)
  apply discharge_types
  done

definition "Int_zero \<equiv> int_lifting.abs Int_Rep_zero"

lemma Int_zero_type [type]: "Int_zero : Int"
  unfolding Int_zero_def
  apply (rule fun_typeE[of "int_lifting.abs"])
  apply (fact Int.Abs_type)
  apply (subst int_rep_translation)
  apply (fact Int_Rep_zero_type)
  done

schematic_goal "?T Int_Rep_add ?Int_Abs_add"
  (* initial step. instantiation required to prevent flex-flex-pairs of higher-order unifier *)
  apply (rule transfer_start[where
    ?T="int_lifting.rel \<Rrightarrow> int_lifting.rel \<Rrightarrow> int_lifting.rel" and ?x=Int_Rep_add])
  (* search matching transfer-triple *)
  apply (rule lifting_triple_rel_funI)
    apply (fact int_lifting.lifting_triple)
  apply (rule lifting_triple_rel_funI)
    apply (fact int_lifting.lifting_triple)
    apply (fact int_lifting.lifting_triple)
  (* search for in-dom-rule to translate goal to user friendly form *)
  apply (rule in_dom_rel_fun_if_Eq_rep_if_lifting_triples')
    apply (fact int_lifting.lifting_triple)
    apply (rule lifting_triple_rel_funI)
      apply (fact int_lifting.lifting_triple)
      apply (fact int_lifting.lifting_triple)
    apply (fact int_lifting.left_unique)
  apply (rule in_dom_rel_fun_if_Eq_rep_if_lifting_triples')
    apply (rule int_lifting.lifting_triple)
    apply (rule int_lifting.lifting_triple)
    apply (rule int_lifting.left_unique)
  apply (rule in_dom_int_lifting_if_Int_Rep)
    apply (drule Int_Rep_if_in_dom_int_lifting)
    apply (drule Int_Rep_if_in_dom_int_lifting)
    (* discharge remaining goal *)
    apply discharge_types
  done

definition "Int_add \<equiv>
  fun_map int_lifting.rep (fun_map int_lifting.rep int_lifting.abs) Int_Rep_add"

lemma Int_add_type [type]: "Int_add : Int \<Rightarrow> Int \<Rightarrow> Int"
  unfolding Int_add_def
  apply (rule fun_typeE[of "fun_map int_lifting.rep (fun_map int_lifting.rep int_lifting.abs)"])
  apply (rule fun_typeE[of "fun_map int_lifting.rep"])
  apply (rule fun_typeE[of "fun_map"])
  apply (fact fun_map_type)
  apply (fact Int.Rep_type)
  apply (rule fun_typeE[of "fun_map int_lifting.rep"])
  apply (rule fun_typeE[of "fun_map"])
  apply (fact fun_map_type)
  apply (fact Int.Rep_type)
  apply (fact Int.Abs_type)
  apply (subst int_rep_translation)+
  apply (fact Int_Rep_add_type)
  done

definition "Int_Rep_pow n i \<equiv> nat_rec n Int_Rep_one (Int_Rep_mul i)"

lemma Int_Rep_pow_zero_eq: "Int_Rep_pow 0 i = Int_Rep_one"
  unfolding Int_Rep_pow_def
  by simp

lemma Int_Rep_pow_succ_eq:
  "n : Nat \<Longrightarrow> Int_Rep_pow (succ n) i = Int_Rep_mul i (Int_Rep_pow n i)"
  unfolding Int_Rep_pow_def
  by simp

lemma Int_Rep_pow_type [type]: "Int_Rep_pow : Nat \<Rightarrow> Int_Rep \<Rightarrow> Int_Rep"
  unfolding Int_Rep_pow_def
proof (rule Dep_fun_typeI)+
  fix n i
  assume n_type: "n : Nat" and i_type: "i : Int_Rep"
  show "nat_rec n Int_Rep_one (Int_Rep_mul i) : Int_Rep"
  apply (rule fun_typeE[of "nat_rec n Int_Rep_one"])
  apply (rule fun_typeE[of "nat_rec n"])
  apply (rule fun_typeE[OF nat_rec_type])
  apply (fact n_type)
  apply (fact Int_Rep_one_type)
  apply (rule fun_typeE[OF Int_Rep_mul_type])
  apply (fact i_type)
  done
qed

schematic_goal "?T Int_Rep_pow ?Int_Abs_pow"
  apply (rule transfer_start[of
    "Eq_Rel nat \<Rrightarrow> int_lifting.rel \<Rrightarrow> int_lifting.rel" _ _ Int_Rep_pow])
  apply (rule lifting_triple_rel_funI)
  apply (fact lifting_triple_Eq_Rel_id)
  apply (rule lifting_triple_rel_funI)
  apply (fact int_lifting.lifting_triple)
  apply (fact int_lifting.lifting_triple)
  (* search for in-dom-rule to translate goal to user friendly form *)
  apply (rule in_dom_rel_fun_if_Eq_rep_if_lifting_triples')
    apply (fact lifting_triple_Eq_Rel_id)
    apply (rule lifting_triple_rel_funI)
      apply (fact int_lifting.lifting_triple)+
    apply (fact left_unique_Eq_Rel)
  apply (rule in_dom_rel_fun_if_Eq_rep_if_lifting_triples')
    apply (rule int_lifting.lifting_triple)
    apply (rule int_lifting.lifting_triple)
    apply (rule int_lifting.left_unique)
  apply (drule Int_Rep_if_in_dom_int_lifting in_dom_eqD)
  apply (drule Int_Rep_if_in_dom_int_lifting in_dom_eqD)
  apply (rule in_dom_int_lifting_if_Int_Rep)
  (* discharge remaining goal *)
  apply discharge_types
  done

definition "Int_pow \<equiv> map_funfun_mapp_funfun_mapfting.rep int_lifting.abs) Int_Rep_pow"

lemma Int_pow_type [type]: "Int_pow : Nat \<Rightarrow> Int \<Rightarrow> Int"
  unfolding Int_pow_def
  apply (rule fun_typeE[of "fun_map id (fun_map int_lifting.rep int_lifting.abs)"])
  apply (rule fun_typeE[of "fun_map id"])
  apply (rule fun_typeE[of "fun_map"])
  apply (fact fun_map_type)
  apply (fact id_type)
  apply (rule fun_typeE[of "fun_map int_lifting.rep"])
  apply (rule fun_typeE[of "fun_map"])
  apply (fact fun_map_type)
  apply (fact Int.Rep_type)
  apply (fact Int.Abs_type)
  apply (subst int_rep_translation)+
  apply (fact Int_Rep_pow_type)
  done

schematic_goal "?T Int_Rep_inv ?Int_Abs_inv"
  apply (rule transfer_start[of
    "int_lifting.rel \<Rrightarrow> int_lifting.rel" _ _ Int_Rep_inv])
  apply (rule lifting_triple_rel_funI)
  apply (fact int_lifting.lifting_triple)
  apply (fact int_lifting.lifting_triple)
  (* search for in-dom-rule to translate goal to user friendly form *)
  apply (rule in_dom_rel_fun_if_Eq_rep_if_lifting_triples')
  apply (fact int_lifting.lifting_triple)
  apply (fact int_lifting.lifting_triple)
  apply (rule int_lifting.left_unique)
  apply (rule in_dom_int_lifting_if_Int_Rep)
  apply (drule Int_Rep_if_in_dom_int_lifting)
  (* discharge remaining goal *)
  apply discharge_types
  done

lemma in_dom_eq: "in_dom (=) x"
  apply (rule in_domI)
  apply (rule refl)
  done

definition "Int_Rep_divisable i j \<equiv> (\<exists>k. Int_Rep_mul j k = i)"

lemma Int_Rep_divisable_type [type]: "Int_Rep_divisable : Int_Rep \<Rightarrow> Int_Rep \<Rightarrow> Bool"
  by discharge_types

schematic_goal "?T Int_Rep_divisable ?Int_Abs_divisable"
  apply (rule transfer_start[of
    "int_lifting.rel \<Rrightarrow> int_lifting.rel \<Rrightarrow> (=)" _ _ Int_Rep_divisable])
  apply (rule lifting_triple_rel_funI)
  apply (fact int_lifting.lifting_triple)
  apply (rule lifting_triple_rel_funI)
    apply (fact int_lifting.lifting_triple)
  apply (rule lifting_triple_eq_id)
  (* search for in-dom-rule to translate goal to user friendly form *)
  apply (rule in_dom_rel_fun_if_Eq_rep_if_lifting_triples')
    apply (fact int_lifting.lifting_triple)
  apply (rule lifting_triple_rel_funI)
    apply (fact int_lifting.lifting_triple)
    apply (fact lifting_triple_eq_id)
    apply (fact int_lifting.left_unique)
  apply (rule in_dom_rel_fun_if_Eq_rep_if_lifting_triples')
    apply (rule int_lifting.lifting_triple)
    apply (rule lifting_triple_eq_id)
    apply (rule int_lifting.left_unique)
  apply (drule Int_Rep_if_in_dom_int_lifting)+
  apply (rule in_dom_eq)
  done

definition "Int_Abs_divisable \<equiv>
  fun_map int_lifting.rep (fun_map int_lifting.rep id) Int_Rep_divisable"

definition "Int_Rep_div i j \<equiv> (THE k. Int_Rep_mul j k = i)"

lemma Int_Rep_div_type [type]:
  "Int_Rep_div : (i : Int_Rep) \<Rightarrow> (Int_Rep & type (Int_Rep_divisable i)) \<Rightarrow> Int_Rep"
  sorry

abbreviation "Int_Rel \<equiv> int_lifting.rel"
abbreviation "Int_rep \<equiv> int_lifting.rep"
abbreviation "Int_abs \<equiv> int_lifting.abs"

lemma Int_Abs_divisable_parametric:
  "(Eq_abs Int_Rel \<Rrightarrow> Eq_abs Int_Rel \<Rrightarrow> (=)) Int_Abs_divisable Int_Abs_divisable"
  apply (rule rel_funI)
  apply (rule rel_funI)
  apply (rule arg_cong2[where ?f=Int_Abs_divisable])
  sorry

schematic_goal "?T Int_Rep_div ?Int_Abs_div"
  apply (rule transfer_start[of
    "[_ i' \<Colon> Int_Rel] \<Rrightarrow> [Int_Rel | (\<lambda>_ j'. Int_Abs_divisable i' j')] \<Rrightarrow> Int_Rel"
    "fun_map Int_rep (fun_map Int_rep Int_abs)"
    "fun_map Int_abs (fun_map Int_abs Int_rep)"
    Int_Rep_div])
  apply (rule lifting_triple_dep_rel_funI')
    apply (fact int_lifting.lifting_triple)
  apply (rule lifting_triple_rel_funI)
    apply (rule lifting_triple_rel_restI)
    apply (rule int_lifting.lifting_triple)
    apply (rule rel_funI)
    apply (rule Int_Abs_divisable_parametric)
    defer
  apply (rule int_lifting.lifting_triple)
  defer
  defer
  sorry

end