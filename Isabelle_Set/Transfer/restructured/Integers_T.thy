theory Integers_T
  imports Isabelle_Set.Integers Set_Extension_T Function_Type Set_Type
begin

interpretation int_lifting: set_extension_lifting \<nat> int_rep Int_Rep_nonneg
  using set_extension_lifting.intro Int.set_extension_axioms .

lemma int_rep_translation: "Element int_rep = Int_Rep"
  (* should be proved elsewhere *)
  sorry

lemmas transfer_start = Basic_T.rel_abs

lemma in_dom_int: "in_dom int_lifting.T x = (x : Int_Rep)"
  unfolding in_dom_Iso_Rel_if_mem mem_int_rep_iff_Int_Rep ..

lemma in_dom_intI: "x : Int_Rep \<Longrightarrow> in_dom int_lifting.T x"
  using in_dom_int by blast

lemma in_dom_intD: "in_dom int_lifting.T x \<Longrightarrow> x : Int_Rep"
  using in_dom_int by blast

schematic_goal "?T Int_Rep_zero ?Int_Abs_zero"
  (* initial step. instantiation required to prevent flex-flex-pairs of higher-order unifier *)
  apply (rule transfer_start[of int_lifting.T int_lifting.abs int_lifting.rep Int_Rep_zero])
  (* search matching transfer-triple *) 
   apply (fact int_lifting.ext_tranfer_triple)
  (* search for in-dom-rule to translate goal to user friendly form *)
  apply (rule in_dom_intI)
  (* discharge remaining goal *)
  apply discharge_types
  done

definition "Int_zero = int_lifting.abs Int_Rep_zero"

lemma "Int_zero : Int"
  unfolding Int_zero_def
  apply (rule fun_typeE[of "int_lifting.abs"])
  apply (fact Int.Abs_type)
  apply (subst int_rep_translation)
  apply (fact Int_Rep_zero_type)
  done

definition "const a _ \<equiv> a"

lemma in_dom_no_dep_fun'':
  assumes "transfer_triple T1 abs1 rep1" "transfer_triple T2 abs2 rep2"
    "left_unique T1"
    "\<And>x. in_dom T1 x \<Longrightarrow> in_dom T2 (f x)"
  shows "in_dom (T1 \<Rrightarrow> T2) f"
  apply (rule in_dom_no_dep_fun')
    apply (fact assms)+
proof -
  fix x1 x2
  assume prem: "Eq_rep T1 x1 x2"
  obtain y where 1: "T1 x1 y"
    using Eq_repE' prem .
  have 2: "in_dom T1 x1"
    using in_domI 1 .
  have 3: "in_dom T2 (f x1)"
    using assms(4) 2 .
  have 4: "x1 = x2"
    using assms(3) prem left_unique_def by fast
  show "Eq_rep T2 (f x1) (f x2)"
    apply (subst 4[symmetric])
    using Eq_rep_self[OF 3] .
qed

schematic_goal "?T Int_Rep_add ?Int_Abs_add"
  (* initial step. instantiation required to prevent flex-flex-pairs of higher-order unifier *)
  apply (rule transfer_start[of
        "no_dep_rel_fun int_lifting.T (no_dep_rel_fun int_lifting.T int_lifting.T)"
        "map_fun int_lifting.rep (map_fun int_lifting.rep int_lifting.abs)"
        "map_fun int_lifting.abs (map_fun int_lifting.abs int_lifting.rep)"
        Int_Rep_add])
  (* search matching transfer-triple *)
  apply (rule no_dep_fun_transfer_triple)
   apply (fact int_lifting.ext_tranfer_triple)
  apply (rule no_dep_fun_transfer_triple)
   apply (fact int_lifting.ext_tranfer_triple)
   apply (fact int_lifting.ext_tranfer_triple)
  (* search for in-dom-rule to translate goal to user friendly form *)
  apply (rule in_dom_no_dep_fun'')
   apply (fact int_lifting.ext_tranfer_triple)
  apply (rule no_dep_fun_transfer_triple)
   apply (fact int_lifting.ext_tranfer_triple)
    apply (fact int_lifting.ext_tranfer_triple)
  apply (fact int_lifting.left_unique_T)
  apply (rule in_dom_no_dep_fun'')
   apply (rule int_lifting.ext_tranfer_triple)+
  apply (rule int_lifting.left_unique_T)
  apply (rule in_dom_intI)
  apply (drule in_dom_intD)+
  (* discharge remaining goal *)
   apply discharge_types (* how were the schematic variables instantiated? *)
  done

definition "Int_add = map_fun int_lifting.rep (map_fun int_lifting.rep int_lifting.abs) Int_Rep_add"

lemma "Int_add : Int \<Rightarrow> Int \<Rightarrow> Int"
  unfolding Int_add_def
  apply (rule fun_typeE[of "map_fun int_lifting.rep (map_fun int_lifting.rep int_lifting.abs)"])
  apply (rule fun_typeE[of "map_fun int_lifting.rep"])
  apply (rule fun_typeE[of "map_fun"])
  apply (fact map_fun_type)
  apply (fact Int.Rep_type)
  apply (rule fun_typeE[of "map_fun int_lifting.rep"])
  apply (rule fun_typeE[of "map_fun"])
  apply (fact map_fun_type)
  apply (fact Int.Rep_type)
  apply (fact Int.Abs_type)
  apply (subst int_rep_translation)+
  apply (fact Int_Rep_add_type)
  done

definition "Int_Rep_pow n i = nat_rec n Int_Rep_one (Int_Rep_mul i)"

lemma Int_Rep_pow_0: "Int_Rep_pow 0 i = Int_Rep_one"
  unfolding Int_Rep_pow_def
  by simp

lemma Int_Rep_pow_succ: "n : Nat \<Longrightarrow> Int_Rep_pow (succ n) i = Int_Rep_mul i (Int_Rep_pow n i)"
  unfolding Int_Rep_pow_def
  by simp

lemma Int_Rep_pow_type[type]: "Int_Rep_pow : Nat \<Rightarrow> Int_Rep \<Rightarrow> Int_Rep"
  unfolding Int_Rep_pow_def
proof (rule Dep_fun_typeI)+
  fix n i
  assume n_type: "n : Nat"
     and i_type: "i : Int_Rep"
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
        "no_dep_rel_fun (Eq_Rel nat) (no_dep_rel_fun int_lifting.T int_lifting.T)"
        "map_fun id (map_fun int_lifting.rep int_lifting.abs)"
        "map_fun id (map_fun int_lifting.abs int_lifting.rep)"
        Int_Rep_pow])
  apply (rule no_dep_fun_transfer_triple)
  apply (fact id_transfer_triple)
  apply (rule no_dep_fun_transfer_triple)
  apply (fact int_lifting.ext_tranfer_triple)
  apply (fact int_lifting.ext_tranfer_triple)
  (* search for in-dom-rule to translate goal to user friendly form *)
  apply (rule in_dom_no_dep_fun'')
  apply (fact id_transfer_triple)
  apply (rule no_dep_fun_transfer_triple)
     apply (fact int_lifting.ext_tranfer_triple)+
  apply (fact left_unique_Eq_Rel)
  apply (rule in_dom_no_dep_fun'')
     apply (rule int_lifting.ext_tranfer_triple)+
  apply (rule int_lifting.left_unique_T)
  apply (drule in_dom_intD in_dom_eqD)+
  apply (rule in_dom_intI)
  (* discharge remaining goal *)
  apply discharge_types (* how were the schematic variables instantiated? *)
  done

definition "Int_pow \<equiv> map_fun id (map_fun int_lifting.rep int_lifting.abs) Int_Rep_pow"

lemma "Int_pow : Nat \<Rightarrow> Int \<Rightarrow> Int"
  unfolding Int_pow_def
  apply (rule fun_typeE[of "map_fun id (map_fun int_lifting.rep int_lifting.abs)"])
  apply (rule fun_typeE[of "map_fun id"])
  apply (rule fun_typeE[of "map_fun"])
  apply (fact map_fun_type)
  apply (fact id_type)
  apply (rule fun_typeE[of "map_fun int_lifting.rep"])
  apply (rule fun_typeE[of "map_fun"])
  apply (fact map_fun_type)
  apply (fact Int.Rep_type)
  apply (fact Int.Abs_type)
  apply (subst int_rep_translation)+
  apply (fact Int_Rep_pow_type)
  done

lemma Int_Rep_add_inv_eq_zero: "i : Int_Rep \<Longrightarrow> Int_Rep_add i (Int_Rep_inv i) = Int_Rep_zero"
  sorry

lemma "Int_Rep_inv : (i : Int_Rep) \<Rightarrow> (\<lambda>j. (Int_Rep_add i j) = Int_Rep_zero) \<sqdot> Int_Rep"
proof (rule Dep_fun_typeI)+
  fix i
  assume i_type: "i : Int_Rep"
  show "Int_Rep_inv i : (\<lambda>j. Int_Rep_add i j = Int_Rep_zero) \<sqdot> Int_Rep"
    apply (rule Dep_fun_typeE[of Int_Rep_inv])
    apply (rule Dep_fun_typeI)
    apply (rule has_adjI)
    apply (rule Int_Rep_add_inv_eq_zero)
    apply assumption
    apply (rule fun_typeE[of Int_Rep_inv])
    apply (rule Int_Rep_inv_type)
    apply assumption
    apply (fact i_type)
    done
qed

schematic_goal "?T Int_Rep_inv ?Int_Abs_inv"
  apply (rule transfer_start[of
        "no_dep_rel_fun int_lifting.T int_lifting.T"
        "map_fun int_lifting.rep int_lifting.abs"
        "map_fun int_lifting.abs int_lifting.rep"
        Int_Rep_inv])
  apply (rule no_dep_fun_transfer_triple)
  apply (fact int_lifting.ext_tranfer_triple)
  apply (fact int_lifting.ext_tranfer_triple)
  (* search for in-dom-rule to translate goal to user friendly form *)
  apply (rule in_dom_no_dep_fun'')
  apply (fact int_lifting.ext_tranfer_triple)+
  apply (rule int_lifting.left_unique_T)
  apply (rule in_dom_intI)
  apply (drule in_dom_intD)+
  (* discharge remaining goal *)
  apply discharge_types
  done

schematic_goal "([_ i' \<Colon> int_lifting.T] \<Rrightarrow> [int_lifting.T | (\<lambda>_ j'. i' + j' = 0)]) Int_Rep_inv ?Int_Abs_inv"
  apply (rule transfer_start[of
      "dep_rel_fun int_lifting.T (\<lambda>_ i'. rel_rest int_lifting.T (\<lambda>_ j'. i' + j' = 0))"
      "map_fun int_lifting.rep int_lifting.abs"
      "map_fun int_lifting.abs int_lifting.rep"
      Int_Rep_inv])
  apply (rule fun_transfer_triple')
  apply (fact int_lifting.ext_tranfer_triple)
  sorry

lemma in_dom_id'I: "in_dom (=) x"
  apply (rule in_domI) by simp

definition "Int_Rep_divisable i j \<equiv> (\<exists>k. Int_Rep_mul j k = i)"

lemma Int_Rep_divisable_type[type]: "Int_Rep_divisable : Int_Rep \<Rightarrow> Int_Rep \<Rightarrow> Bool"
  sorry

schematic_goal "?T Int_Rep_divisable ?Int_Abs_divisable"
  apply (rule transfer_start[of
      "int_lifting.T \<Rrightarrow> int_lifting.T \<Rrightarrow> (=)"
      "map_fun int_lifting.rep (map_fun int_lifting.rep id)"
      "map_fun int_lifting.abs (map_fun int_lifting.abs id)"
      Int_Rep_divisable])
  apply (rule no_dep_fun_transfer_triple)
  apply (fact int_lifting.ext_tranfer_triple)
  apply (rule no_dep_fun_transfer_triple)
    apply (fact int_lifting.ext_tranfer_triple)
  apply (rule id_transfer_triple')
  apply (rule in_dom_no_dep_fun'')
    apply (fact int_lifting.ext_tranfer_triple)
  apply (rule no_dep_fun_transfer_triple)
    apply (fact int_lifting.ext_tranfer_triple)
  apply (fact id_transfer_triple')
    apply (fact int_lifting.left_unique_T)
  apply (rule in_dom_no_dep_fun'')
    apply (rule int_lifting.ext_tranfer_triple)
  apply (rule id_transfer_triple')
    apply (rule int_lifting.left_unique_T)
  apply (drule in_dom_intD)+
  apply (rule in_dom_id'I)
  done

definition "Int_Abs_divisable \<equiv> map_fun int_lifting.rep (map_fun int_lifting.rep id) Int_Rep_divisable"

definition "Int_Rep_div i j \<equiv> (THE k. Int_Rep_mul j k = i)"

lemma Int_Rep_div_type[type]: "Int_Rep_div : (i : Int_Rep) \<Rightarrow> (\<lambda>j. Int_Rep_divisable i j ) \<sqdot> Int_Rep \<Rightarrow> Int_Rep"
  sorry

abbreviation "Int_Rel \<equiv> int_lifting.T"
abbreviation "Int_rep \<equiv> int_lifting.rep"
abbreviation "Int_abs \<equiv> int_lifting.abs"

schematic_goal "([_ i \<Colon> Int_Rel] \<Rrightarrow> [Int_Rel | (\<lambda>_ j. Int_Abs_divisable i j)] \<Rrightarrow> Int_Rel) Int_Rep_div ?Int_Abs_div"
  apply (rule transfer_start[of
      "[_ i \<Colon> Int_Rel] \<Rrightarrow> [Int_Rel | (\<lambda>_ j. Int_Abs_divisable i j)] \<Rrightarrow> Int_Rel"
      "map_fun Int_rep (map_fun Int_rep Int_abs)"
      "map_fun Int_abs (map_fun Int_abs Int_rep)"
      Int_Rep_div])
  apply (rule fun_transfer_triple')
  apply (fact int_lifting.ext_tranfer_triple)
  apply (rule no_dep_fun_transfer_triple)
  defer
  apply (rule int_lifting.ext_tranfer_triple)
  sorry

end