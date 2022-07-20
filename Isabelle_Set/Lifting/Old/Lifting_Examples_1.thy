theory Lifting_Examples_1
  imports
    Lifting_Set
    Rational
    Isabelle_Set.Rewrite
    Lifting_Group
begin

lemma Int_Rel_def': "Int_Rel = Ext_Rel \<int> Int.Rep"
  unfolding Int_Rel_def Ext_Rel_def by simp

lemma Rat_Rel_def': "Rat_Rel = Ext_Rel \<rat> Rat.Rep"
  unfolding Rat_Rel_def Ext_Rel_def by simp

definition "Nat_Rel m n \<equiv> n \<in> nat \<and> m = n"

lemma Nat_Rel_def': "Nat_Rel = Ext_Rel \<nat> id"
  unfolding Nat_Rel_def Ext_Rel_def by auto

thm set_extension_lifting(1)[OF  Rat.set_extension_axioms] Rat_Rel_def'
lemmas Rat_Rel_lifting = set_extension_lifting(1)[OF Rat.set_extension_axioms, folded Rat_Rel_def']
   and is_equality_eq_rat_rep = set_extension_lifting(2)[OF Rat.set_extension_axioms]
   and is_equality_eq_rat_abs = set_extension_lifting(3)[OF Rat.set_extension_axioms]

definition "eq_Rat \<equiv> eq Rat.abs_image"

definition "rat_rep_app f x \<equiv> f x"
definition "rat_app f x \<equiv> Rat.Abs (rat_rep_app (\<lambda>x. Rat.Rep (f (Rat.Abs x))) (Rat.Rep x))"

lemmas is_symmetric_rat_rep = equality_sym[OF is_equality_eq_rat_rep]
   and is_symmetric_rat_abs = equality_sym[OF is_equality_eq_rat_abs]

lemma Rat_Rel_app: "((Rat_Rel ===> Rat_Rel) ===> Rat_Rel ===> Rat_Rel) rat_rep_app rat_app"
proof (
    rewrite in "\<hole>" rel_fun_def,
    rewrite in "\<forall>_ _. _ \<longrightarrow> \<hole>" rel_fun_def,
    atomize_rev')
  fix f f' x x'
  assume rels: "(Rat_Rel ===> Rat_Rel) f f'" "Rat_Rel x x'"
  note rep_x = lifting_rel(1)[OF Rat_Rel_lifting rels(2)]
  (* unlifing f' *)
  define f'' where "f'' \<equiv> (\<lambda>x. Rat.Rep (f' (Rat.Abs x)))"
  (* can this be abstracted? *)
  have rep_f: "(eq rat_rep ===> eq rat_rep) f'' f"
  proof (rewrite in "\<hole>" rel_fun_def, atomize_rev')
    fix x1 x2
    assume assms: "eq rat_rep x1 x2"
    show "eq rat_rep (f'' x1) (f x2)"
      apply (subst f''_def)
      apply (rule lifting_rel(1)[OF Rat_Rel_lifting])
      apply (rule rel_funE'[OF rels(1)])
      apply (rule lifting_Eq_rep(1)[OF Rat_Rel_lifting])
      apply (fact symE[OF eq_symmetric assms(1)])
      done
  qed
  note is_symmetric1 = rel_fun_sym[OF is_symmetric_rat_rep is_symmetric_rat_rep]
  note is_symmetric2 = rel_fun_sym[OF is_symmetric_rat_abs is_symmetric_rat_abs]
  note reps = rep_x rep_f[unfolded f''_def] symE[OF is_symmetric1, OF rep_f[unfolded f''_def]] symE[OF is_symmetric_rat_rep rep_x]
  have u1eq: "\<And>f g x. (\<And>x. x : Element rat_rep \<Longrightarrow> f x = g x) \<Longrightarrow> x : Element rat_rep \<Longrightarrow> rat_rep_app f x = rat_rep_app g x"
    (* left to the user *)
    sorry
  have u1elem: "\<And>f x. (\<And>x. x : Element rat_rep \<Longrightarrow> f x : Element rat_rep) \<Longrightarrow> x : Element rat_rep \<Longrightarrow> rat_rep_app f x : Element rat_rep"
    (* left to the user *)
    sorry
  note u2eq = u1eq[unfolded type_in_rep_iff]
  note u2elem = u1elem[unfolded type_in_rep_iff]
  { fix f g x y
    assume rels: "(eq rat_rep ===> eq rat_rep) f g" "eq rat_rep x y"
    have 1: "in_rep (eq rat_rep) x"
      apply (rule equalityE(2)[OF is_equality_eq_rat_rep])
      apply (fact rels(2))
      done
    have 2: "\<And>x. in_rep (eq rat_rep) x \<Longrightarrow> f x = g x"
      apply (rule equalityE[OF is_equality_eq_rat_rep])
      apply (rule rel_funE'[OF  rels(1)])
      apply (rule equalityI[OF is_equality_eq_rat_rep])
      apply assumption
      done
    have 3: "\<And>x. in_rep (eq rat_rep) x \<Longrightarrow> in_rep (eq rat_rep) (f x)"
      apply (rule equalityE(2)[OF is_equality_eq_rat_rep])
      apply (rule rel_funE'[OF rels(1)])
      apply (rule equalityI[OF is_equality_eq_rat_rep])
      apply assumption
      done
    have 6: "x = y"
      apply (rule equalityE[OF is_equality_eq_rat_rep])
      apply (fact rels(2))
      done
    have "eq rat_rep (rat_rep_app f x) (rat_rep_app g y)"
      apply (rule equalityI'[OF is_equality_eq_rat_rep])
      apply (rule u2elem)
      apply (fact 3)
      apply (fact 1)
      apply (subst 6[symmetric])
      apply (rule u2eq)
      apply (fact 2)
      apply (fact 1)
      done
  }
  note u4 = this
  show "Rat_Rel (rat_rep_app f x) (rat_app f' x')"
    apply (subst rat_app_def)
    apply (rule lifting_Eq_rep[OF Rat_Rel_lifting])
    apply (rule u4)
    apply (fact reps(3))
    apply (fact reps(4))
    done
qed

lemma "((Rat_Rel ===> Rat_Rel) ===> Rat_Rel ===> Rat_Rel) rat_rep_app rat_app"
proof (
    rewrite in "\<hole>" rel_fun_def,
    rewrite in "\<forall>_ _. _ \<longrightarrow> \<hole>" rel_fun_def,
    atomize_rev')
  fix f f' x x'
  assume rels: "(Rat_Rel ===> Rat_Rel) f f'" "Rat_Rel x x'"
  note is_symmetric1 = rel_fun_sym[OF is_symmetric_rat_rep is_symmetric_rat_rep]
  note is_symmetric2 = rel_fun_sym[OF is_symmetric_rat_abs is_symmetric_rat_abs]
  have u1eq: "\<And>f g x. (\<And>x. x : Element rat_rep \<Longrightarrow> f x = g x) \<Longrightarrow> x : Element rat_rep \<Longrightarrow> rat_rep_app f x = rat_rep_app g x"
    (* equality in assumption should be replaced by `eq rat_rep` or combined with `f x : Element rat_rep` *)
    (* left to the user *)
    sorry
  have u1elem: "\<And>f x. (\<And>x. x : Element rat_rep \<Longrightarrow> f x : Element rat_rep) \<Longrightarrow> x : Element rat_rep \<Longrightarrow> rat_rep_app f x : Element rat_rep"
    (* left to the user *)
    sorry
  note u2eq = u1eq[unfolded type_in_rep_iff]
  note u2elem = u1elem[unfolded type_in_rep_iff]
  { fix f g x y
    assume rels: "(eq rat_rep ===> eq rat_rep) f g" "eq rat_rep x y"
    have 1: "in_rep (eq rat_rep) x"
      apply (rule equalityE(2)[OF is_equality_eq_rat_rep])
      apply (fact rels(2))
      done
    have 2: "\<And>x. in_rep (eq rat_rep) x \<Longrightarrow> f x = g x"
      apply (rule equalityE[OF is_equality_eq_rat_rep])
      apply (rule rel_funE'[OF  rels(1)])
      apply (rule equalityI[OF is_equality_eq_rat_rep])
      apply assumption
      done
    have 3: "\<And>x. in_rep (eq rat_rep) x \<Longrightarrow> in_rep (eq rat_rep) (f x)"
      apply (rule equalityE(2)[OF is_equality_eq_rat_rep])
      apply (rule rel_funE'[OF rels(1)])
      apply (rule equalityI[OF is_equality_eq_rat_rep])
      apply assumption
      done
    have 6: "x = y"
      apply (rule equalityE[OF is_equality_eq_rat_rep])
      apply (fact rels(2))
      done
    have "eq rat_rep (rat_rep_app f x) (rat_rep_app g y)"
      apply (rule equalityI'[OF is_equality_eq_rat_rep])
      apply (rule u2elem)
      apply (fact 3)
      apply (fact 1)
      apply (subst 6[symmetric])
      apply (rule u2eq)
      apply (fact 2)
      apply (fact 1)
      done
  }
  note u4 = this
  show "Rat_Rel (rat_rep_app f x) (rat_app f' x')"
    apply (subst rat_app_def)
    apply (rule lifting_Eq_rep[OF Rat_Rel_lifting])
    apply (rule u4)
    apply (rule symE[OF is_symmetric1, OF lifting_rel(1)[OF fun_lifting[OF Rat_Rel_lifting Rat_Rel_lifting]]])
     apply (fact rels(1))
    apply (rule symE[OF is_symmetric_rat_rep lifting_rel(1)[OF Rat_Rel_lifting]])
    apply (fact rels(2))
    done
qed

lemma Fun_typeI: "(\<And>x. x : A \<Longrightarrow> f x : B) \<Longrightarrow> f : A \<Rightarrow> B"
  by discharge_types

lemma abs_type: "lifting Eq_A Eq_B T Abs Rep \<Longrightarrow> x : type (in_rep Eq_A) \<Longrightarrow> Abs x : type (in_abs Eq_B)"
  apply unfold_types
  unfolding lifting_unfold in_rep_def in_abs_def
  by blast

lemma Element_rep: "Element A \<equiv> type (in_rep (eq A))"
  unfolding Element_def in_rep_def eq_def by simp

lemma Element_abs: "Element A \<equiv> type (in_abs (eq A))"
  unfolding Element_def in_abs_def eq_def by simp

lemma rat_app_type: "rat_app : (Rat \<Rightarrow> Rat) \<Rightarrow> Rat \<Rightarrow> Rat"
proof -
  have u1elem: "\<And>f x. (\<And>x. x : Element rat_rep \<Longrightarrow> f x : Element rat_rep) \<Longrightarrow> x : Element rat_rep \<Longrightarrow> rat_rep_app f x : Element rat_rep"
    (* left to the user *)
    sorry
  show "rat_app : (Rat \<Rightarrow> Rat) \<Rightarrow> Rat \<Rightarrow> Rat"
    apply (rule Fun_typeI)+
    apply (subst rat_app_def)
    apply (subst Element_abs)
    apply (rule abs_type[OF Rat_Rel_lifting])
    apply (rule u1elem[unfolded Element_rep])
    apply (insert Rat.Rep_type)
    unfolding Element_rep[symmetric]
    apply unfold_types
    done
qed

hide_const  abs


definition "const = K"

lemma lifting_start: "lifting Eq_rep Eq_abs T abs rep \<Longrightarrow> Eq_rep x x \<Longrightarrow> const True (T x (abs x)) \<Longrightarrow> T x (abs x)"
  using lifting_Eq_rep(1)
  by metis

lemma eq_resp_simp: "is_equality_set in_dom R \<Longrightarrow> (\<And>z. in_dom z \<Longrightarrow> P z z) \<Longrightarrow> (\<And>x y. R x y \<Longrightarrow> P x y)"
  by (metis Lifting_Set.equalityE(1) Lifting_Set.equalityE(2))

lemma h1: "is_equality_set (elem A) (eq A)"
  unfolding is_equality_set_def elem_def eq_def
  by blast

lemma h2: "elem A x \<Longrightarrow> eq A x x"
  unfolding elem_def eq_def by blast

lemma rat_rep_add_resp: "elem rat_rep z \<Longrightarrow> elem rat_rep za \<Longrightarrow> elem rat_rep (rat_rep_add za z)"
  sorry

lemma "\<exists>t. (Rat_Rel ===> Rat_Rel ===> Rat_Rel) rat_rep_add t"
  apply (rule exI)
  apply (rule lifting_start[where T="Rat_Rel ===> Rat_Rel ===> Rat_Rel" and x=rat_rep_add])
    apply (rule fun_lifting')
  apply (rule Rat_Rel_lifting)
   apply (rule fun_lifting')
     apply (rule Rat_Rel_lifting)
    apply (rule Rat_Rel_lifting)
   apply (rewrite in "\<hole>" rel_fun_def, rewrite in "\<forall>_ _. _ \<longrightarrow> \<hole>" rel_fun_def, atomize_rev')
proof -
  fix x y x' y'
  show "eq rat_rep x y \<Longrightarrow> eq rat_rep x' y' \<Longrightarrow> eq rat_rep (rat_rep_add x x') (rat_rep_add y y')"
    apply (rule eq_resp_simp[OF h1, of rat_rep "\<lambda>x' y'. eq rat_rep (rat_rep_add x x') (rat_rep_add y y')"])
    defer apply assumption
  proof -
    fix z
    show "eq rat_rep x y \<Longrightarrow> eq rat_rep x' y' \<Longrightarrow> elem rat_rep z \<Longrightarrow> eq rat_rep (rat_rep_add x z) (rat_rep_add y z)"
      apply (rule eq_resp_simp[OF h1, of rat_rep "\<lambda>x y. eq rat_rep (rat_rep_add x z) (rat_rep_add y z)"])
      defer apply assumption
      apply (rule h2)
      apply (rule rat_rep_add_resp, assumption, assumption)
      done
  qed
next
  show "const True
     ((Rat_Rel ===> Rat_Rel ===> Rat_Rel) rat_rep_add (fun_map Rat.Rep (fun_map Rat.Rep Rat.Abs) rat_rep_add))"
  apply (subst const_def) ..
qed


lemma "\<exists>T t. T rat_rep_add t"
  apply (rule exI, rule exI)
  apply (rule lifting_start[where x=rat_rep_add])
    apply (rule fun_lifting')
  apply (rule Rat_Rel_lifting)
   apply (rule fun_lifting')
     apply (rule Rat_Rel_lifting)
    apply (rule Rat_Rel_lifting)
  apply (subst refl)
   apply (rewrite in "\<hole>" rel_fun_def, rewrite in "\<forall>_ _. _ \<longrightarrow> \<hole>" rel_fun_def, atomize_rev')
proof -
  fix x y x' y'
  show "eq rat_rep x y \<Longrightarrow> eq rat_rep x' y' \<Longrightarrow> eq rat_rep (rat_rep_add x x') (rat_rep_add y y')"
    apply (rule eq_resp_simp[OF h1, of rat_rep "\<lambda>x' y'. eq rat_rep (rat_rep_add x x') (rat_rep_add y y')"])
    defer apply assumption
  proof -
    fix z
    show "eq rat_rep x y \<Longrightarrow> eq rat_rep x' y' \<Longrightarrow> elem rat_rep z \<Longrightarrow> eq rat_rep (rat_rep_add x z) (rat_rep_add y z)"
      apply (rule eq_resp_simp[OF h1, of rat_rep "\<lambda>x y. eq rat_rep (rat_rep_add x z) (rat_rep_add y z)"])
      defer apply assumption
      apply (rule h2)
      apply (rule rat_rep_add_resp, assumption, assumption)
      done
  qed
next
  show "const True
     ((Rat_Rel ===> Rat_Rel ===> Rat_Rel) rat_rep_add (fun_map Rat.Rep (fun_map Rat.Rep Rat.Abs) rat_rep_add))"
  apply (subst const_def) ..
qed


lemma Rat_Rel_add'': "(Rat_Rel ===> Rat_Rel ===> Rat_Rel) rat_rep_add rat_add"
proof (
    rewrite in "\<hole>" rel_fun_def,
    rewrite in "\<forall>_ _. _ \<longrightarrow> \<hole>" rel_fun_def,
    atomize_rev')
  fix i j i' j'
  assume rels: "Rat_Rel i i'" "Rat_Rel j j'"
  have u1elem: "\<And>i j. i : Element rat_rep \<Longrightarrow> j : Element rat_rep \<Longrightarrow> rat_rep_add i j : Element rat_rep"
    (* left to the user *)
    sorry
  note u2elem = u1elem[unfolded type_in_rep_iff]
  { fix i1 j1 i2 j2
    assume rels: "eq rat_rep i1 i2" "eq rat_rep j1 j2"
    note rels = rels symE[OF eq_symmetric rels(1)] symE[OF eq_symmetric rels(2)]
    have 1: "in_rep (eq rat_rep) i1"
      apply (rule equalityE(2)[OF is_equality_eq_rat_rep])
      apply (fact rels(1))
      done
    have 2: "in_rep (eq rat_rep) j1"
      apply (rule equalityE(2)[OF is_equality_eq_rat_rep])
      apply (fact rels(2))
      done
    have 3: "i2 = i1"
      apply (rule equalityE[OF is_equality_eq_rat_rep])
      apply (fact rels(3))
      done
    have 4: "j2 = j1"
      apply (rule equalityE[OF is_equality_eq_rat_rep])
      apply (fact rels(4))
      done
    have "eq rat_rep (rat_rep_add i1 j1) (rat_rep_add i2 j2)"
      apply (rule equalityI'[OF is_equality_eq_rat_rep])
       apply (rule u2elem)
      apply (fact 1)
       apply (fact 2)
      apply (subst 3)
      apply (subst 4)
      apply (rule refl)
      done
  }
  note eq_rat_rep_add = this
  show "Rat_Rel (rat_rep_add i j) (i' + j')"
    apply (subst rat_add_def)
    apply (rule lifting_Eq_rep(1)[OF Rat_Rel_lifting])
    apply (rule eq_rat_rep_add)
    apply (rule symE[OF is_symmetric_rat_rep lifting_rel(1)[OF Rat_Rel_lifting]])
    apply (fact rels(1))
    apply (rule symE[OF is_symmetric_rat_rep lifting_rel(1)[OF Rat_Rel_lifting]])
    apply (fact rels(2))
    done
qed


lemma rat_add_type': "rat_add : Rat \<Rightarrow> Rat \<Rightarrow> Rat"
proof -
  have u1elem: "\<And>i j. i : Element rat_rep \<Longrightarrow> j : Element rat_rep \<Longrightarrow> rat_rep_add i j : Element rat_rep"
    (* left to the user *)
    sorry
  show "rat_add : Rat \<Rightarrow> Rat \<Rightarrow> Rat"
    apply (rule Fun_typeI)+
    apply (subst rat_add_def)
    apply (subst Element_abs)
    apply (rule abs_type[OF Rat_Rel_lifting])
    apply (rule u1elem[unfolded Element_rep])
    apply (insert Rat.Rep_type)
    unfolding Element_rep[symmetric]
    apply unfold_types
    done
qed

lemma Nat_Rel_def''': "Nat_Rel \<equiv> Eq_Rel nat"
  apply (rule eq_reflection)
  unfolding Nat_Rel_def Eq_Rel_def Ext_Rel_def by auto

lemmas Nat_Rel_lifting = equality_lifting(1)[OF Nat_Rel_def''']
   and is_equality_eq_nat_rep = equality_lifting(2)[OF Nat_Rel_def''']
   and is_equality_eq_nat_abs = equality_lifting(3)[OF Nat_Rel_def''']

lemmas is_symmetric_nat_rep = equality_sym[OF is_equality_eq_nat_rep]
   and is_symmetric_nat_abs = equality_sym[OF is_equality_eq_nat_abs]

lemmas Int_Rel_lifting = set_extension_lifting(1)[OF Int.set_extension_axioms, folded Int_Rel_def']
   and is_equality_eq_int_rep = set_extension_lifting(2)[OF Int.set_extension_axioms]
   and is_equality_eq_int_abs = set_extension_lifting(3)[OF Int.set_extension_axioms]

lemmas is_symmetric_int_rep = equality_sym[OF is_equality_eq_int_rep]
   and is_symmetric_int_abs = equality_sym[OF is_equality_eq_int_abs]

lemma Int_Rel_pow'': "(Nat_Rel ===> Int_Rel ===> Int_Rel) int_rep_pow int_pow"
proof ((subst rel_fun_def)+, atomize_rev')
  fix n i n' i'
  assume rels: "Nat_Rel n n'" "Int_Rel i i'"
  have u1elem: "\<And>n i. n : Nat \<Longrightarrow> i : Element int_rep \<Longrightarrow> int_rep_pow n i : Element int_rep"
    (* left to the user *)
    sorry
  note u2elem = u1elem[unfolded type_in_rep_iff]
  { fix i1 n1 i2 n2
    assume rels: "eq \<nat> n1 n2" "eq int_rep i1 i2"
    note rels = rels symE[OF eq_symmetric rels(1)] symE[OF eq_symmetric rels(2)]
    have 1: "in_rep (eq \<nat>) n1"
      apply (rule equalityE(2)[OF is_equality_eq_nat_rep])
      apply (fact rels(1))
      done
    have 2: "in_rep (eq int_rep) i1"
      apply (rule equalityE(2)[OF is_equality_eq_int_rep])
      apply (fact rels(2))
      done
    have 3: "n2 = n1"
      apply (rule equalityE[OF is_equality_eq_nat_rep])
      apply (fact rels(3))
      done
    have 4: "i2 = i1"
      apply (rule equalityE[OF is_equality_eq_int_rep])
      apply (fact rels(4))
      done
    have "eq int_rep (int_rep_pow n1 i1) (int_rep_pow n2 i2)"
      apply (rule equalityI'[OF is_equality_eq_int_rep])
       apply (rule u2elem)
      apply (fact 1)
       apply (fact 2)
      apply (subst 3)
      apply (subst 4)
      apply (rule refl)
      done
  }
  note eq_rat_rep_add = this
  show "Int_Rel (int_rep_pow n i) (int_pow n' i')"
    apply (subst int_pow_def)
    apply (rule lifting_Eq_rep[OF Int_Rel_lifting])
    apply (rule eq_rat_rep_add)
    apply (rule symE[OF is_symmetric_nat_rep lifting_rel(1)[OF Nat_Rel_lifting]])
     apply (fact rels(1))
    apply (rule symE[OF is_symmetric_int_rep lifting_rel(1)[OF Int_Rel_lifting]])
    apply (fact rels(2))
    done
qed

lemma rat_pow_type': "int_pow : Nat \<Rightarrow> Integers.Int \<Rightarrow> Integers.Int"
proof -
  have u1elem: "\<And>n i. n : Nat \<Longrightarrow> i : Element int_rep \<Longrightarrow> int_rep_pow n i : Element int_rep"
    (* left to the user *)
  sorry
  show "int_pow : Nat \<Rightarrow> Integers.Int \<Rightarrow> Integers.Int"
    apply (rule Fun_typeI)+
    apply (subst int_pow_def)
    apply (subst Element_abs)
    apply (rule abs_type[OF Int_Rel_lifting])
    apply (rule u1elem[unfolded Element_rep])
    apply (insert Int.Rep_type)
    unfolding Element_rep[symmetric]
    apply unfold_types
    done
qed



lemma Int_Rel_divides'': "(Int_Rel ===> Int_Rel ===> (=)) divides_rep divides"
proof (
    rewrite in "\<hole>" rel_fun_def,
    rewrite in "\<forall>_ _. _ \<longrightarrow> \<hole>" rel_fun_def,
    atomize_rev')
  fix i j i' j'
  assume rels: "Int_Rel i i'" "Int_Rel j j'"
  { fix i1 j1 i2 j2
    assume rels: "eq int_rep i1 i2" "eq int_rep j1 j2"
    note rels = rels symE[OF eq_symmetric rels(1)] symE[OF eq_symmetric rels(2)]
    have 3: "i2 = i1"
      apply (rule equalityE[OF is_equality_eq_int_rep])
      apply (fact rels(3))
      done
    have 4: "j2 = j1"
      apply (rule equalityE[OF is_equality_eq_int_rep])
      apply (fact rels(4))
      done
    have "(divides_rep i1 j1) = (divides_rep i2 j2)"
      apply (subst 3)
      apply (subst 4)
      apply (rule refl)
      done
  }
  note eq_divides_rep = this
  show "divides_rep i j = divides i' j'"
    apply (subst divides_def)
    apply (rule eq_divides_rep)
    apply (rule symE[OF is_symmetric_int_rep lifting_rel(1)[OF Int_Rel_lifting]])
    apply (fact rels(1))
    apply (rule symE[OF is_symmetric_int_rep lifting_rel(1)[OF Int_Rel_lifting]])
    apply (fact rels(2))
    done
qed

lemma divides_type': "divides : Integers.Int \<Rightarrow> Integers.Int \<Rightarrow> Bool"
  apply (rule type_from_rel_fun)
  apply (rule Int_Rel_divides'')
   apply unfold_types[1]
  apply (erule isomorphism_exists_left[OF isomorphism_Int_Rel])

  apply (rule type_from_rel_fun)
  apply assumption
  apply unfold_types[1]
  apply (erule isomorphism_exists_left[OF isomorphism_Int_Rel])

  apply (rule Any_typeI)
  done

lemmas bi_unique_Int_Rel = isomorphism_bi_unique[OF isomorphism_Int_Rel]

lemma Rat_Rel_eq'': "(Int_Rel ===> Int_Rel ===> (=)) (=) (=)"
proof ((subst rel_fun_def)+, atomize_rev')
  fix i j i' j'
  assume rels: "Int_Rel i i'" "Int_Rel j j'"
  note 1 = isomorphism_rel[OF isomorphism_Int_Rel rels(1)]
  note 2 = isomorphism_rel[OF isomorphism_Int_Rel rels(2)]
  note reps = 1(1) 2(1)
  note abss = 1(2) 2(2)
  note in_defs = 1(3) 2(3)
  note in_reps = 1(4) 2(4)
  show "(i = j) = (i' = j')"
    apply (rule bi_uniqueE[OF bi_unique_Int_Rel in_reps in_defs rels])
    done
qed

definition "int_0_rep \<equiv> Int_Rep_nonneg 0"
definition "int_0 \<equiv> Int.Abs int_0_rep"

lemma Int_Rel_0': "Int_Rel int_0_rep int_0"
proof (subst Int_Rel_def, rule conjI)
  show "int_0 \<in> \<int>"
    apply (subst int_0_def)
    apply(rule Fun_typeE'[OF _ Int.Abs_type])
    (* left to the user *)
    sorry
next
  show "Int.Rep int_0 = int_0_rep"
    apply (subst int_0_def)
    apply (subst Int.Rep_Abs_inv)
    apply (rule refl)
    done
qed

lemma "int_0_type": "int_0 : Integers.Int"
  apply (rule type_from_isomorphism_rel_elem[OF isomorphism_Int_Rel])
  apply (rule Int_Rel_0')
  done

lemma Nat_Rel_def''': "Nat_Rel = Eq_Rel nat"
  unfolding Nat_Rel_def Eq_Rel_def Ext_Rel_def by auto

lemmas isomorphism_Nat_Rel = eq_isomorphism[OF Nat_Rel_def''']

lemma Int_Rel_pow'': "(Nat_Rel ===> Int_Rel ===> Int_Rel) int_rep_pow int_pow"
proof ((subst rel_fun_def)+, atomize_rev')
  fix n i n' i'
  assume rels: "Nat_Rel n n'" "Int_Rel i i'"
  note 1 = isomorphism_rel[OF isomorphism_Nat_Rel rels(1)]
  note 2 = isomorphism_rel[OF isomorphism_Int_Rel rels(2)]
  note reps = 1(1) 2(1)
  note abss = 1(2) 2(2)
  note in_defs = 1(3) 2(3)
  note in_reps = 1(4) 2(4)
  show "Int_Rel (int_rep_pow n i) (int_pow n' i')"
  proof (subst Int_Rel_def, rule conjI)
    show "int_pow n' i' \<in> \<int>"
      apply (subst int_pow_def)
      apply (rule Fun_typeE'[OF _ Int.Abs_type])
      apply (subst reps)+
      apply (insert in_reps)
      (* left to the user *)
      sorry
  next
    show "Int.Rep (int_pow n' i') = int_rep_pow n i"
      apply (subst int_pow_def')
      apply (subst Int.Rep_Abs_inv)
      apply (subst reps)+
      apply (rule refl)
      done
  qed
qed

lemma rat_pow_type': "int_pow : Nat \<Rightarrow> Integers.Int \<Rightarrow> Integers.Int"
  apply (rule type_from_rel_fun)
  apply (rule Int_Rel_pow'')
   apply unfold_types[1]
  apply (erule isomorphism_exists_left[OF isomorphism_Nat_Rel])

  apply (rule type_from_rel_fun)
  apply assumption
  apply unfold_types[1]
  apply (erule isomorphism_exists_left[OF isomorphism_Int_Rel])

  apply (rule type_from_rel_elem)
  apply (rule Int_Rel_def')
  apply assumption
  done

lemma rat_pow_type'':
  assumes types: "n : Nat" "i : Integers.Int"
  shows "int_pow n i : Integers.Int"
  apply (rule type_from_isomorphism_rel_elem[OF isomorphism_Int_Rel])
  apply (rule rel_funE'[OF rel_funE'[OF Int_Rel_pow'']])
  apply (fact isomorphism_rel2(1)[OF isomorphism_Nat_Rel ElementD[OF types(1)]])
  apply (fact isomorphism_rel2(1)[OF isomorphism_Int_Rel ElementD[OF types(2)]])
  done

(* Int_Rel i i' ===> (divides i \<sqdot> Int_Rel) ===> Int_Rel *)
(* Int_Rel i i' ===> Int_Rel j j' | divides i j ===> Int_Rel *)
lemma Int_Rel_div': "Int_Rel i i' \<Longrightarrow> Int_Rel j j' \<Longrightarrow> divides i' j' \<Longrightarrow> Int_Rel (int_rep_div i j) (int_div i' j')"
proof -
  assume rels: "Int_Rel i i'" "Int_Rel j j'"
     and prems: "divides i' j'"
  note 1 = isomorphism_rel[OF isomorphism_Int_Rel rels(1)]
  note 2 = isomorphism_rel[OF isomorphism_Int_Rel rels(2)]
  note reps = 1(1) 2(1)
  note abss = 1(2) 2(2)
  note in_defs = 1(3) 2(3)
  note in_reps = 1(4) 2(4)
  (* only works for simple expressions, should be done by transfer *)
  note prems' = prems[unfolded divides_def reps]
  show "Int_Rel (int_rep_div i j) (int_div i' j')"
  proof (subst Int_Rel_def, rule conjI)
    show "int_div i' j' \<in> \<int>"
      apply (subst int_div_def)
      apply(rule Fun_typeE'[OF _ Int.Abs_type])
      apply (subst reps)+
      apply (insert in_reps)
      apply (insert prems')
      (* left to the user *)
      sorry
  next
    show "Int.Rep (int_div i' j') = int_rep_div i j"
      apply (subst int_div_def)
      apply (subst Int.Rep_Abs_inv)
      apply (subst reps)+
      apply (rule refl)
      done
    qed
  qed

end