theory Lifting_Examples_2
  imports Lifting_Examples_1
begin

lemma rel_adj_subst: "rel_adj R p x y \<longrightarrow> P \<equiv> R x y \<longrightarrow> p x y \<longrightarrow> P"
  unfolding rel_adj_def
  apply (rule eq_reflection)
  apply (rule iffI)
  by blast+

lemma Int_Rel_div''': "([i i' \<Colon> Int_Rel] \<Rrightarrow> [j j' \<Colon> Int_Rel | divides i' j'] \<Rrightarrow> Int_Rel) Int_Rep_div int_div"
proof (
    rewrite in "\<hole>" dep_rel_fun_def,
    rewrite in "\<forall>_ _. _ \<longrightarrow> \<hole>" dep_rel_fun_def,
    subst rel_adj_subst, atomize_rev')
  fix i j i' j'
  assume rels_raw: "Int_Rel i i'" "Int_Rel j j'" "divides i' j'"
  note rels = rels_raw(1) rels_raw(2)
  note prems = rels_raw(3)
  have prems': "divides_rep i j"
    (* inverse transfer *)
    sorry
  have u1elem: "\<And>i j. i : Element int_rep \<Longrightarrow> j : Element int_rep \<Longrightarrow> divides_rep i j \<Longrightarrow> Int_Rep_div i j : Element int_rep"
    sorry
  note u2elem = u1elem[unfolded type_in_rep_iff]
  { fix i1 i2 j1 j2
    assume assms: "eq int_rep i1 i2" "eq int_rep j1 j2" "divides_rep i1 j1"
    note rels = assms(1, 2) symE[OF eq_symmetric assms(1)] symE[OF eq_symmetric assms(2)]
    have 1: "in_rep (eq int_rep) i1"
      apply (rule equalityE(2)[OF is_equality_eq_int_rep])
      apply (fact rels(1))
      done
    have 2: "in_rep (eq int_rep) j1"
      apply (rule equalityE(2)[OF is_equality_eq_int_rep])
      apply (fact rels(2))
      done
    have 3: "i2 = i1"
      apply (rule equalityE[OF is_equality_eq_int_rep])
      apply (fact rels(3))
      done
    have 4: "j2 = j1"
      apply (rule equalityE[OF is_equality_eq_int_rep])
      apply (fact rels(4))
      done
    have "eq int_rep (Int_Rep_div i1 j1) (Int_Rep_div i2 j2)"
      apply (rule equalityI'[OF is_equality_eq_int_rep])
       apply (rule u2elem)
      apply (fact 1)
      apply (fact 2)
       apply (fact assms(3))
      apply (subst 3)
      apply (subst 4)
      apply (rule refl)
      done
  }
  note eq_Int_Rep_add = this
  show "Int_Rel (Int_Rep_div i j) (int_div i' j')"
    apply (subst int_div_def)
    apply (rule lifting_Eq_rep[OF Int_Rel_lifting])
    apply (rule eq_Int_Rep_add)
      apply (rule symE[OF is_symmetric_int_rep lifting_rel(1)[OF Int_Rel_lifting]])
    apply (fact rels(1))
      apply (rule symE[OF is_symmetric_int_rep lifting_rel(1)[OF Int_Rel_lifting]])
    apply (fact rels(2))
    apply (fact prems')
    done
qed

term "Int_Rel i i' \<Longrightarrow> Int_Rel j j' \<Longrightarrow> divides i' j' \<Longrightarrow> Int_Rel (Int_Rep_div i j) (int_div i' j')"


term "([i i' \<Colon> Int_Rel] \<Rrightarrow> [j j' \<Colon> Int_Rel | divides i' j'] \<Rrightarrow> Int_Rel) Int_Rep_div int_div"
term "int_div (n * j) (n * i) = int_div j i"
term "(=) ?c (int_div (n * j) (n * i) = int_div j i)"

term "?R ?a (int_div (n * j) (n * i))"

term "Int_Rel ?d (n * j)"

term "?S ?b (int_div j i)"

lemma int_div_type': "int_div: (i : Integers.Int) \<Rightarrow> (divides i \<sqdot> Integers.Int) \<Rightarrow> Integers.Int"
  apply (rule type_from_rel_fun_dep')
  apply (rule Int_Rel_div''')
  apply (rule isomorphism_exists_left[OF isomorphism_Int_Rel ElementD])
  apply assumption

  apply (rule type_from_rel_fun_adj)
  apply assumption
  apply (erule conjE)
  apply (rule conj_exD2)
  apply (rule conjI)
  apply assumption
  apply (erule isomorphism_exists_left[OF isomorphism_Int_Rel ElementD])

  apply (rule type_from_isomorphism_rel_elem[OF isomorphism_Int_Rel])
  apply assumption
  sorry

definition "ite_rep b x y \<equiv> (if b = True_set then x else y)"

lemma "ite_rep : Element Bool_set \<Rightarrow> \<alpha> \<Rightarrow> \<alpha> \<Rightarrow> \<alpha>"
  apply unfold_types
  unfolding ite_rep_def
  by simp

lemma ite_type: "ite_rep : (b : Element Bool_set) \<Rightarrow> type (\<lambda>x. b = True_set \<longrightarrow> x : \<alpha>) \<Rightarrow> type (\<lambda>x. b \<noteq> True_set \<longrightarrow> x : \<alpha>) \<Rightarrow> \<alpha>"
  apply unfold_types
  unfolding ite_rep_def
  by simp

definition "ite b x y \<equiv> Int.Abs (ite_rep b (Int.Rep x) (Int.Rep y))"

lemma aux1: "f : (x : A) \<Rightarrow> (y : (P x \<sqdot> B)) \<Rightarrow> C \<Longrightarrow>
       f : (x : A) \<Rightarrow> (y : B) \<Rightarrow> type (\<lambda>z. P x y \<longrightarrow> z : C)"
  by (unfold_types, blast)

lemma aux2: "x : A \<Longrightarrow> x : type (\<lambda>x. P x \<longrightarrow> x : A)"
  by (unfold_types, blast)

lemma
  assumes "i : Integers.Int" "j : Integers.Int"
  shows "ite (divides i j) (int_div i j) (i) : Integers.Int"
  apply (rule Fun_typeE[where f="ite (divides i j) (int_div i j)" and x=i and B=Integers.Int])
  prefer 2
  apply (rule Fun_typeE[where f="ite (divides i j)" and x="int_div i j"])
  prefer 2
  apply (rule dep_fun_typeE[where f=ite and x="divides i j"])
  prefer 2
  apply (rule ite_type[where \<alpha>=Integers.Int])
  apply (rule Fun_typeE[where f="divides i"])
  prefer 2
  apply (rule Fun_typeE[where f=divides])
  prefer 2
  apply (rule divides_type')
  apply (rule assms)+
  apply (rule dep_fun_typeE[where f="int_div i" and x=j])
  apply (rule assms)
  apply (rule dep_fun_typeE[where f="int_div" and x=i])
  apply (rule assms)
  apply (rule int_div_type aux1[OF int_div_type])
  apply (rule aux2, rule assms)
  done

definition "Bool_Rel \<equiv> Eq_Rel Bool_set"

lemmas Bool_Rel_lifting = equality_lifting(1)[OF Bool_Rel_def]
   and is_equality_eq_bool_rep = equality_lifting(2)[OF Bool_Rel_def]
   and is_equality_eq_bool_abs = equality_lifting(3)[OF Bool_Rel_def]

lemmas is_symmetric_bool_rep = equality_sym[OF is_equality_eq_bool_rep]
   and is_symmetric_bool_abs = equality_sym[OF is_equality_eq_bool_abs]

lemma Rel_ite': "([b b' \<Colon> Bool_Rel] \<Rrightarrow> [to_HOL b \<longrightarrow> Int_Rel] \<Rrightarrow> [to_HOL (not_set b) \<longrightarrow> Int_Rel] \<Rrightarrow> Int_Rel) ite_rep ite"
proof (rewrite in "\<hole>" dep_rel_fun_def,
    rewrite in "\<forall>_ _. _ \<longrightarrow> \<hole>" no_dep_rel_weak_fun_unfold,
    rewrite in "\<forall>_ _. _ \<longrightarrow> (\<forall>_ _. _ \<longrightarrow> \<hole>)" no_dep_rel_weak_fun_unfold,
    atomize_rev')
  fix b i j b' i' j'
  assume rels: "Bool_Rel b b'" "to_HOL b \<Longrightarrow> Int_Rel i i'" "to_HOL (not_set b) \<Longrightarrow> Int_Rel j j'"
  have u1elem: "\<And>b i j. b : Element Bool_set \<Longrightarrow> (to_HOL b \<Longrightarrow> i : Element int_rep) \<Longrightarrow> (to_HOL (not_set b) \<Longrightarrow> j : Element int_rep) \<Longrightarrow> ite_rep b i j : Element int_rep"
    sorry
  have u1eq: "\<And>b i1 j1 i2 j2. b : Element Bool_set \<Longrightarrow> (to_HOL b \<Longrightarrow> eq int_rep i1 i2) \<Longrightarrow> (to_HOL (not_set b) \<Longrightarrow> eq int_rep j1 j2) \<Longrightarrow> ite_rep b i1 j1 = ite_rep b i2 j2"
    sorry
  note u2elem = u1elem[unfolded type_in_rep_iff]
  note u2eq = u1eq[unfolded type_in_rep_iff]
  { fix b1 b2 i1 i2 j1 j2
    assume assms: "eq Bool_set b1 b2" "to_HOL b1 \<Longrightarrow> eq int_rep i1 i2" "to_HOL (not_set b1) \<Longrightarrow> eq int_rep j1 j2"
    have 1: "in_rep (eq Bool_set) b1"
      apply (rule equalityE(2)[OF is_equality_eq_bool_rep])
      apply (fact assms(1))
      done
    have 2: "to_HOL b1 \<Longrightarrow> in_rep (eq int_rep) i1"
      apply (rule equalityE(2)[OF is_equality_eq_int_rep])
      apply (fact assms(2))
      done
    have 3: "to_HOL (not_set b1) \<Longrightarrow> in_rep (eq int_rep) j1"
      apply (rule equalityE(2)[OF is_equality_eq_int_rep])
      apply (fact assms(3))
      done
    have 4: "b2 = b1"
      apply (rule equalityE[OF is_equality_eq_bool_rep])
      apply (fact symE[OF eq_symmetric assms(1)])
      done
    have 5: "to_HOL b1 \<Longrightarrow> i2 = i1"
      apply (rule equalityE[OF is_equality_eq_int_rep])
      apply (fact symE[OF eq_symmetric assms(2)])
      done
    have 6: "to_HOL (not_set b1) \<Longrightarrow> j2 = j1"
      apply (rule equalityE[OF is_equality_eq_int_rep])
      apply (fact symE[OF eq_symmetric assms(3)])
      done
    have "eq int_rep (ite_rep b1 i1 j1) (ite_rep b2 i2 j2)"
      apply (rule equalityI'[OF is_equality_eq_int_rep])
       apply (rule u2elem)
      apply (fact 1)
        apply (fact 2)
       apply (fact 3)
      apply (subst 4)
      apply (rule u2eq)
      apply (fact 1)
      apply (fact assms(2))
      apply (fact assms(3))
      done
  }
  note ite_eq_rep = this
  show "Int_Rel (ite_rep b i j) (ite b' i' j')"
    apply (subst ite_def)
    apply (rule lifting_Eq_rep[OF Int_Rel_lifting])
    apply (rule ite_eq_rep)
    apply (rule symE[OF is_symmetric_bool_rep lifting_rel(1)[OF Bool_Rel_lifting]])
    apply (fact rels(1))
    apply (rule symE[OF is_symmetric_int_rep lifting_rel(1)[OF Int_Rel_lifting]])
    apply (fact rels(2))
    apply (rule symE[OF is_symmetric_int_rep lifting_rel(1)[OF Int_Rel_lifting]])
    apply (fact rels(3))
    done
qed

definition "two_rep \<equiv> Int_Rep_nonneg (succ 1)"
definition "two \<equiv> Int.Abs two_rep"

hide_const even
definition "even_rep i \<equiv> (if (\<exists>j. Int_Rep_mul two_rep j = i) then True_set else False_set)"
definition "even i \<equiv> even_rep (Int.Rep i)"

lemma Int_Rel_even: "(Int_Rel ===> Bool_Rel) even_rep even"
proof (
    rewrite in "\<hole>" rel_fun_def,
    atomize_rev')
  fix i i'
  assume rels: "Int_Rel i i'"
  note 1 = lifting_rel[OF Int_Rel_lifting rels(1)]
  note reps = 1(1) symE[OF is_symmetric_int_rep 1(1)]
  have u1elem: "\<And>i. i : Element int_rep \<Longrightarrow> even_rep i : Element Bool_set"
    sorry
  note u2elem = u1elem[unfolded type_in_rep_iff]
  { fix i1 i2
    assume rels: "eq int_rep i1 i2"
    note rels = rels symE[OF eq_symmetric rels(1)]
    have 1: "in_rep (eq int_rep) i1"
      apply (rule equalityE(2)[OF is_equality_eq_int_rep])
      apply (fact rels(1))
      done
    have 2: "i2 = i1"
      apply (rule equalityE[OF is_equality_eq_int_rep])
      apply (fact rels(2))
      done
    have "eq Bool_set (even_rep i1) (even_rep i2)"
      apply (rule equalityI'[OF is_equality_eq_bool_rep])
       apply (rule u2elem)
       apply (fact 1)
      apply (subst 2)
      apply (rule refl)
      done
  }
  note eq_even_rep = this
  show "Bool_Rel (even_rep i) (even i')"
    apply (subst even_def)
    apply (rule lifting_Eq_rep[OF Bool_Rel_lifting])
    apply (rule eq_even_rep)
    apply (fact reps(2))
    done
qed

lemma even_type: "even : Integers.Int \<Rightarrow> Element Bool_set"
proof -
  have u1elem: "\<And>i. i : Element int_rep \<Longrightarrow> even_rep i : Element Bool_set"
    sorry
  show "even : Integers.Int \<Rightarrow> Element Bool_set"
    apply (rule Fun_typeI)+
    apply (subst even_def)
    apply (subst Element_abs)
    apply (rule abs_type[OF Bool_Rel_lifting])
    apply (rule u1elem[unfolded Element_rep])
    apply (insert Int.Rep_type)
    unfolding Element_rep[symmetric]
    apply unfold_types
    done
qed

definition "even_cases_rep f g i \<equiv> ite (even_rep i) (f i) (g i)"
definition "even_cases f g i \<equiv> Int.Abs (even_cases_rep (\<lambda>i. Int.Rep (f (Int.Abs i))) (\<lambda>i. Int.Rep (g (Int.Abs i))) (Int.Rep i))"

lemma even_cases_rep_ext:
  assumes f: "f : Element int_rep \<Rightarrow> Element int_rep"
    and f': "f' : Element int_rep \<Rightarrow> Element int_rep"
    and g: "g : Element int_rep \<Rightarrow> Element int_rep"
    and g': "g' : Element int_rep \<Rightarrow> Element int_rep"
    and i: "i : Element int_rep"
    and f_eq: "\<And>i. i : Element int_rep \<Longrightarrow> f i = f' i"
    and g_eq: "\<And>i. i : Element int_rep \<Longrightarrow> g i = g' i"
  shows "even_cases_rep f g i = even_cases_rep f' g' i"
  apply (subst even_cases_rep_def)+
  apply (subst f_eq, fact i)
  apply (subst g_eq, fact i)
  apply (rule refl)
  done

lemma Int_Rel_even_cases: "((Int_Rel ===> Int_Rel) ===> (Int_Rel ===> Int_Rel) ===> Int_Rel ===> Int_Rel) even_cases_rep even_cases"
proof (
    rewrite in "\<hole>" rel_fun_def,
    rewrite in "\<forall>_ _. _ \<longrightarrow> \<hole>" rel_fun_def,
    rewrite in "\<forall>_ _. _ \<longrightarrow> (\<forall>_ _. _ \<longrightarrow> \<hole>)" rel_fun_def[of "Int_Rel" "Int_Rel"],
    atomize_rev')
  fix f g i f' g' i'
  assume rels: "(Int_Rel ===> Int_Rel) f f'" "(Int_Rel ===> Int_Rel) g g'" "Int_Rel i i'"
  note is_symmetric1 = rel_fun_sym[OF is_symmetric_int_rep is_symmetric_int_rep]
  note is_symmetric2 = rel_fun_sym[OF is_symmetric_int_abs is_symmetric_int_abs]
  have u1eq: "\<And>f1 f2 g1 g2 x. (\<And>x. x : Element int_rep \<Longrightarrow> f1 x = f2 x) \<Longrightarrow> (\<And>x. x : Element int_rep \<Longrightarrow> g1 x = g2 x) \<Longrightarrow> x : Element int_rep \<Longrightarrow> even_cases_rep f1 g1 x = even_cases_rep f2 g2 x"
    (* left to the user *)
    sorry
  have u1elem: "\<And>f g x. (\<And>x. x : Element int_rep \<Longrightarrow> f x : Element int_rep) \<Longrightarrow> (\<And>x. x : Element int_rep \<Longrightarrow> g x : Element int_rep) \<Longrightarrow> x : Element int_rep \<Longrightarrow> even_cases_rep f g x : Element int_rep"
    (* left to the user *)
    sorry
  note u2eq = u1eq[unfolded type_in_rep_iff]
  note u2elem = u1elem[unfolded type_in_rep_iff]
  { fix f1 g1 i1 f2 g2 i2
    assume rels: "(eq int_rep ===> eq int_rep) f1 f2" "(eq int_rep ===> eq int_rep) g1 g2" "eq int_rep i1 i2"
    have 1: "\<And>x. in_rep (eq int_rep) x \<Longrightarrow> f1 x = f2 x"
      apply (rule equalityE[OF is_equality_eq_int_rep])
      apply (rule rel_funE'[OF  rels(1)])
      apply (rule equalityI[OF is_equality_eq_int_rep])
      apply assumption
      done
    have 2: "\<And>x. in_rep (eq int_rep) x \<Longrightarrow> in_rep (eq int_rep) (f1 x)"
      apply (rule equalityE(2)[OF is_equality_eq_int_rep])
      apply (rule rel_funE'[OF rels(1)])
      apply (rule equalityI[OF is_equality_eq_int_rep])
      apply assumption
      done
    have 3: "\<And>x. in_rep (eq int_rep) x \<Longrightarrow> g1 x = g2 x"
      apply (rule equalityE[OF is_equality_eq_int_rep])
      apply (rule rel_funE'[OF  rels(2)])
      apply (rule equalityI[OF is_equality_eq_int_rep])
      apply assumption
      done
    have 4: "\<And>x. in_rep (eq int_rep) x \<Longrightarrow> in_rep (eq int_rep) (g1 x)"
      apply (rule equalityE(2)[OF is_equality_eq_int_rep])
      apply (rule rel_funE'[OF rels(2)])
      apply (rule equalityI[OF is_equality_eq_int_rep])
      apply assumption
      done
    have 5: "in_rep (eq int_rep) i1"
      apply (rule equalityE(2)[OF is_equality_eq_int_rep])
      apply (fact rels(3))
      done
    have 6: "i1 = i2"
      apply (rule equalityE[OF is_equality_eq_int_rep])
      apply (fact rels(3))
      done
    have "eq int_rep (even_cases_rep f1 g1 i1) (even_cases_rep f2 g2 i2)"
      apply (rule equalityI'[OF is_equality_eq_int_rep])
      apply (rule u2elem)
      apply (fact 2)
      apply (fact 4)
      apply (fact 5)
      apply (subst 6[symmetric])
      apply (rule u2eq)
      apply (fact 1)
      apply (fact 3)
      apply (fact 5)
      done
  }
  note eq_even_cases_rep = this
  show "Int_Rel (even_cases_rep f g i) (even_cases f' g' i')"
    apply (subst even_cases_def)
    apply (rule lifting_Eq_rep[OF Int_Rel_lifting])
    apply (rule eq_even_cases_rep)
      apply (rule symE[OF is_symmetric1, OF lifting_rel(1)[OF fun_lifting[OF Int_Rel_lifting Int_Rel_lifting]]])
    apply (fact rels(1))
      apply (rule symE[OF is_symmetric1, OF lifting_rel(1)[OF fun_lifting[OF Int_Rel_lifting Int_Rel_lifting]]])
     apply (fact rels(2))
    apply (rule symE[OF is_symmetric_int_rep lifting_rel(1)[OF Int_Rel_lifting]])
    apply (fact rels(3))
    done
qed

lemma even_cases_type': "even_cases : (Integers.Int \<Rightarrow> Integers.Int) \<Rightarrow> (Integers.Int \<Rightarrow> Integers.Int) \<Rightarrow> Integers.Int \<Rightarrow> Integers.Int"
proof -
  have u1elem: "\<And>f g x. (\<And>x. x : Element int_rep \<Longrightarrow> f x : Element int_rep) \<Longrightarrow> (\<And>x. x : Element int_rep \<Longrightarrow> g x : Element int_rep) \<Longrightarrow> x : Element int_rep \<Longrightarrow> even_cases_rep f g x : Element int_rep"
    (* left to the user *)
    sorry
  show "even_cases : (Integers.Int \<Rightarrow> Integers.Int) \<Rightarrow> (Integers.Int \<Rightarrow> Integers.Int) \<Rightarrow> Integers.Int \<Rightarrow> Integers.Int"
    apply (rule Fun_typeI)+
    apply (subst even_cases_def)
    apply (subst Element_abs)
    apply (rule abs_type[OF Int_Rel_lifting])
    apply (rule u1elem[unfolded Element_rep])
    apply (insert Int.Rep_type)
    unfolding Element_rep[symmetric]
    apply unfold_types
    done
qed

(* 1 \<equiv> Element {\<emptyset>} *)
(* 2 \<equiv> Element {\<emptyset>, {\<emptyset>}} *)
(* app f x = f x *)
(* app : (\<alpha> \<rightarrow> \<beta>) \<rightarrow> \<alpha> \<rightarrow> \<beta> *)
(* app : ((1 \<rightarrow> 1) \<rightarrow> 2) \<rightarrow> (1 \<rightarrow> 1) \<rightarrow> 2 *)
(* (((Eq1 \<Rightarrow> Eq1) \<Rightarrow> Eq2) \<Rightarrow> (Eq1 \<Rightarrow> Eq1) \<Rightarrow> Eq 2) app app *)
(* f g \<equiv> if g {\<emptyset>} = \<emptyset> then \<emptyset> else {\<emptyset>}) *)
(* f : (1 \<rightarrow> 1) \<rightarrow> 2 *)
(* ((Eq1 \<Rightarrow> Eq1) \<Rightarrow> Eq2) f f \<Longrightarrow> False *)
(* (Eq1 \<Rightarrow> Eq1) id (const \<emptyset>) *)
(* app f id        = {\<emptyset>} *)
(* app f (const \<emptyset>) = \<emptyset> *)
(* (Eq 2) (app f id) (app f (const \<emptyset>)) \<Longrightarrow> False *)
(* ((Eq1 \<Rightarrow> Eq1) \<Rightarrow> Eq 2) (app f) (app f) \<Longrightarrow> False *)

definition "Int_Rep_app2 f g x \<equiv> f g x"
definition "int_app2 f g x \<equiv> Int.Abs (Int_Rep_app2 (\<lambda>g x. Int.Rep (f (\<lambda>x. Int.Abs (g (Int.Rep x))) (Int.Abs x))) (\<lambda>x. Int.Rep (g (Int.Abs x))) (Int.Rep x))"

term "Int_Rep_app2 :: (('a \<Rightarrow> 'b) \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'c \<Rightarrow> 'd"

lemma fun_typeIff: "(f : A \<Rightarrow> B) \<equiv> (\<forall>x. x : A \<longrightarrow> f x : B)"
  by unfold_types

lemma modus_ponens: "(P \<Longrightarrow> Q) \<Longrightarrow> P \<Longrightarrow> Q"
  by blast

lemma Int_Rel_app2: "(((Int_Rel ===> Int_Rel) ===> Int_Rel ===> Int_Rel) ===> (Int_Rel ===> Int_Rel) ===> Int_Rel ===> Int_Rel) Int_Rep_app2 int_app2"
proof (
    rewrite in "\<hole>" rel_fun_def,
    rewrite in "\<forall>_ _. _ \<longrightarrow> \<hole>" rel_fun_def,
    rewrite in "\<forall>_ _. _ \<longrightarrow> (\<forall>_ _. _ \<longrightarrow> \<hole>)" rel_fun_def,
    atomize_rev')
  fix f f' g g' i i'
  assume rels: "((Int_Rel ===> Int_Rel) ===> Int_Rel ===> Int_Rel) f f'" "(Int_Rel ===> Int_Rel) g g'" "Int_Rel i i'"
  note lifting1 = fun_lifting[OF Int_Rel_lifting Int_Rel_lifting]
  note lifting2 = fun_lifting[OF lifting1 lifting1]
  note is_symmetric1 = rel_fun_sym[OF is_symmetric_int_rep is_symmetric_int_rep]
  note is_symmetric2 = rel_fun_sym[OF is_symmetric1 is_symmetric1]
  have u1eq:
    "\<And>f1 f2 g1 g2 x.
      (\<And>g1 g2 x.
        g1 : Element rat_rep \<Rightarrow> Element rat_rep \<Longrightarrow>
        g2 : Element rat_rep \<Rightarrow> Element rat_rep \<Longrightarrow>
        (\<And>x. x : Element rat_rep \<Longrightarrow> g1 x = g2 x) \<Longrightarrow>
        x : Element rat_rep \<Longrightarrow>
        eq rat_rep (f1 g1 x) (f2 g2 x)) \<Longrightarrow>
      g1 : Element rat_rep \<Rightarrow> Element rat_rep \<Longrightarrow>
      g2 : Element rat_rep \<Rightarrow> Element rat_rep \<Longrightarrow>
      (\<And>x. x : Element rat_rep \<Longrightarrow> g1 x = g2 x) \<Longrightarrow>
      x : Element rat_rep \<Longrightarrow>
      Int_Rep_app2 f1 g1 x = Int_Rep_app2 f2 g2 x"
    (* left to the user *)
    sorry
  have u1type:
    "\<And>f g x.
      f : (Element int_rep \<Rightarrow> Element int_rep) \<Rightarrow> Element int_rep \<Rightarrow> Element int_rep \<Longrightarrow>
      g : Element int_rep \<Rightarrow> Element int_rep \<Longrightarrow>
      Int_Rep_app2 f g x : Element int_rep"
    (* left to the user *)
    sorry
  note u2eq = u1eq[unfolded
      type_in_rep_iff
      type_in_rep_fun_iff[OF type_in_rep_iff type_in_rep_iff]]
  note u2type = u1type[unfolded type_in_rep_iff fun_typeIff atomize_imp[symmetric] atomize_all[symmetric]]
  { fix f1 f2 g1 g2 i1 i2
    assume assms:
      "((eq int_rep ===> eq int_rep) ===> eq int_rep ===> eq int_rep) f1 f2"
      "(eq int_rep ===> eq int_rep) g1 g2"
      "eq int_rep i1 i2"
    have 1: "\<And>g1 g2 x.
      in_rep (eq int_rep ===> eq int_rep) g1 \<Longrightarrow>
      in_rep (eq int_rep ===> eq int_rep) g2 \<Longrightarrow>
      (\<And>x. in_rep (eq int_rep) x \<Longrightarrow> g1 x = g2 x) \<Longrightarrow>
      in_rep (eq int_rep) x \<Longrightarrow> eq int_rep (f1 g1 x) (f2 g2 x)"
      (* would be easier with isar proof *)
      apply (rule rel_funE'[OF rel_funE'[OF assms(1)]])
       apply (rule rel_funI)
       apply (rule equalityI'[OF is_equality_eq_int_rep])
      apply (erule in_rep_funE)
        apply (rule in_repI'[OF equality_is_partial_equivalence[OF is_equality_eq_int_rep]])
        apply assumption
       apply (frule equalityE(1)[OF is_equality_eq_int_rep])
       apply (erule subst)
       apply (meson Lifting_Set.equalityE(2) is_equality_eq_int_rep)
      apply (rule equalityI'[OF is_equality_eq_int_rep])
       apply assumption
      apply (rule refl)
      done
    have "eq int_rep (Int_Rep_app2 f1 g1 i1) (Int_Rep_app2 f2 g2 i2)"
      sorry
  }
  note Int_Rep_app2_eq = this
  show "Int_Rel (Int_Rep_app2 f g i) (int_app2 f' g' i')"
    apply (subst int_app2_def)
    apply (rule lifting_Eq_rep[OF Int_Rel_lifting])
    apply (rule Int_Rep_app2_eq)
    apply (rule symE[OF is_symmetric2, OF lifting_rel(1)[OF
      fun_lifting[OF
        fun_lifting[OF Int_Rel_lifting Int_Rel_lifting]
          fun_lifting[OF Int_Rel_lifting Int_Rel_lifting]]]])
      apply (fact rels(1))
    apply (rule symE[OF is_symmetric1, OF lifting_rel(1)[OF
      fun_lifting[OF Int_Rel_lifting Int_Rel_lifting]]])
      apply (fact rels(2))
    apply (rule symE[OF is_symmetric_int_rep lifting_rel(1)[OF Int_Rel_lifting]])
      apply (fact rels(3))
    done
qed

lemma fun_per: "partial_equivalence R \<Longrightarrow> partial_equivalence S \<Longrightarrow> partial_equivalence (R ===> S)"
  unfolding partial_equivalence_unfold rel_fun_def
  by metis

lemma eq_int_is_per: "partial_equivalence (eq \<int>)"
  using eq_is_per is_equality_eq_int_abs by blast

lemma "int_app2 : ((Integers.Int \<Rightarrow> Integers.Int) \<Rightarrow> Integers.Int \<Rightarrow> Integers.Int) \<Rightarrow> (Integers.Int \<Rightarrow> Integers.Int) \<Rightarrow> Integers.Int \<Rightarrow> Integers.Int"
proof (
      rule type_from_rel_fun2'[OF
        fun_lifting[OF
          fun_lifting[OF Int_Rel_lifting Int_Rel_lifting]
          fun_lifting[OF Int_Rel_lifting Int_Rel_lifting]]
        fun_lifting[OF
          fun_lifting[OF Int_Rel_lifting Int_Rel_lifting]
          fun_lifting[OF Int_Rel_lifting Int_Rel_lifting]]
        Int_Rel_app2])
  fix f
  assume f_type: "f : (Integers.Int \<Rightarrow> Integers.Int) \<Rightarrow> Integers.Int \<Rightarrow> Integers.Int"
  note 1 = Fun_typeE[OF _ f_type]
  { fix x y
    assume eq_x_y: "(eq \<int> ===> eq \<int>) x y"
    have x_type: "x : Integers.Int \<Rightarrow> Integers.Int"
      apply (rule type_from_in_abs_fun[OF Int_Rel_lifting Int_Rel_lifting])
        apply (fact in_absI1[OF fun_per[OF eq_int_is_per eq_int_is_per], OF eq_x_y])
      unfolding type_in_abs_iff
       apply assumption+
      done
    have y_type: "y : Integers.Int \<Rightarrow> Integers.Int"
      apply (rule type_from_in_abs_fun[OF Int_Rel_lifting Int_Rel_lifting])
        apply (fact in_absI2[OF fun_per[OF eq_int_is_per eq_int_is_per], OF eq_x_y])
      unfolding type_in_abs_iff
       apply assumption+
      done
    have "(eq \<int> ===> eq \<int>) (f x) (f y)"
      using Fun_typeE[OF x_type f_type] Fun_typeE[OF y_type f_type]
      (* not provable because `f x` may depend on arbitrary properties of `x` *)
      sorry
  }
  note 2 = this
  show "in_abs ((eq \<int> ===> eq \<int>) ===> eq \<int> ===> eq \<int>) f"
    apply (rewrite in_abs_def)
    apply (rewrite rel_fun_def)
    apply atomize_rev'
    apply (erule 2)
    done
next
  fix x
  assume "in_abs ((eq \<int> ===> eq \<int>) ===> eq \<int> ===> eq \<int>) (int_app2 x)"
  show "int_app2 x : (Integers.Int \<Rightarrow> Integers.Int) \<Rightarrow> Integers.Int \<Rightarrow> Integers.Int"
    sorry
qed

end