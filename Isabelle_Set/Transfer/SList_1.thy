theory SList_1
  imports
    SOption
    Lifting_Expe
    Lifting_Set
    Lifting_Group
begin

definition Nil_rep where "Nil_rep = inl {}"
definition Cons_rep where "Cons_rep x xs = inr \<langle>x, xs\<rangle>"

lemma nil_neq_cons: "Nil_rep \<noteq> Cons_rep x xs"
  unfolding Nil_rep_def Cons_rep_def
  by simp

lemma cons_inject [iff]: "Cons_rep x xs = Cons_rep y ys \<longleftrightarrow> x = y \<and> xs = ys"
  unfolding Cons_rep_def
  by simp

hide_const lfp

definition List_rep where
  "List_rep A = lfp (univ A) (\<lambda>L. {Nil_rep} \<union> {Cons_rep x xs | \<langle>x, xs\<rangle> \<in> A \<times> L})"

lemma List_rep_distinct[simp]: "Nil_rep \<noteq> Cons_rep x xs"
  unfolding Nil_rep_def Cons_rep_def by simp

definition "list_rep_case n c \<equiv> coprod_rec (\<lambda>_. n) (\<lambda>p. c (fst p) (snd p))"

lemma list_rep_case_type: "list_rep_case : A \<Rightarrow> (Element B \<Rightarrow> Element (List_rep B) \<Rightarrow> A) \<Rightarrow> Element (List_rep B) \<Rightarrow> A"
proof (intro Dep_fun_typeI)
  fix n c l
  assume assms: "n : A" "c : Element B \<Rightarrow> Element (List_rep B) \<Rightarrow> A" "l : Element (List_rep B)"
  show "list_rep_case n c l : A"
    apply (subst list_rep_case_def)
    apply (rule Fun_typeE[OF _ Fun_typeE[OF _ Fun_typeE[OF _ coprod_rec_type]]])
    using assms(3)
    sorry
qed

hide_fact def_lfp_unfold
hide_fact monotoneI

lemma Nil_rep_in_univ: "Nil_rep \<in> univ A"
  by (simp add: Nil_rep_def univ_closed_inl)

lemma Cons_rep_in_univ: "x \<in> A \<Longrightarrow> xs \<in> univ A \<Longrightarrow> Cons_rep x xs \<in> univ A"
  using Cons_rep_def univ_closed_inr mem_univ_trans' by auto

lemma List_rep_mono: "(\<lambda>L. {Nil_rep} \<union> {Cons_rep x xs | \<langle>x, xs\<rangle> \<in> A \<times> L}) : Monop (univ A)"
  apply unfold_types
  apply (rule conjI, rule monotoneI)
  by (blast, auto simp add: Nil_rep_in_univ Cons_rep_in_univ)

lemmas List_rep_unfold =
  fixpoint_lfp[OF List_rep_mono, folded List_rep_def, unfolded fixpoint_def, symmetric]

lemma Nil_rep_type [type]: "Nil_rep: Element (List_rep A)"
  by (subst List_rep_unfold) (unfold_types, auto)

lemma Cons_rep_type [type]: "Cons_rep: Element A \<Rightarrow> Element (List_rep A) \<Rightarrow> Element (List_rep A)"
  by (subst (2) List_rep_unfold) (unfold_types, auto)

lemma Cons_rep_type': "x \<in> A \<Longrightarrow> xs \<in> List_rep A \<Longrightarrow> Cons_rep x xs \<in> List_rep A"
  by simp

lemma opairD2: "\<langle>a, b\<rangle> \<in> A \<times> B \<Longrightarrow> b \<in> B"
  by simp

hide_fact def_lfp_induct
hide_const collect

lemma List_rep_induct:
  assumes xs_type: "xs: Element (List_rep A)"
  assumes Nil: "P Nil_rep"
  assumes Cons: "\<And>x xs. x: Element A \<Longrightarrow> xs: Element (List_rep A) \<Longrightarrow> P xs \<Longrightarrow> P (Cons_rep x xs)"
  shows "P xs"
proof (rule Least_Fixpoint.lfp_induct[OF List_rep_mono, folded List_rep_def,
  where ?P=P and ?a=xs and ?A1=A])
  from xs_type show "xs \<in> List_rep A" by unfold_types
next
  fix x assume assm: "x \<in> {Nil_rep} \<union> {Cons_rep x xs | \<langle>x, xs\<rangle> \<in> A \<times> collect (List_rep A) P}"
  show "P x"
  proof (cases "x=Nil_rep")
    case True
    then show ?thesis
      using Nil mem_iff_Element by simp
  next
    case False
    obtain y ys where x: "x = Cons_rep y ys"
      using False assm by auto
    have y_type: "y : Element A" using x assm sorry
    have ys_type: "ys : Element (List_rep A)" sorry
    have "x \<in> {Cons_rep x xs | \<langle>x, xs\<rangle> \<in> A \<times> collect (List_rep A) P}"
      using assm False List_rep_distinct by blast
    then have "ys \<in> collect (List_rep A) P"
      using x by auto
    hence "P ys" using x assm by auto
    thus ?thesis
      using x Cons[OF y_type ys_type] by simp
  qed
qed

definition "singleton_rep x = Cons_rep x Nil_rep"

lemma singleton_rep_type: "singleton_rep : Element A \<Rightarrow> Element (List_rep A)"
  apply unfold_types
  unfolding singleton_rep_def
  using Cons_rep_type Nil_rep_type
  by simp

lemma singleton_rep_inject [iff]: "singleton_rep x = singleton_rep y \<longleftrightarrow> x = y"
  unfolding singleton_rep_def by simp

definition "option_in_list = option_case singleton_rep Nil_rep"

lemma option_in_list_type: "option_in_list : Option A \<Rightarrow> Element (List_rep A)"
  apply unfold_types
  unfolding option_in_list_def
  using option_case_type[OF singleton_rep_type Nil_rep_type] by simp

hide_type Set.set

axiomatization list_rep_rec :: "(set \<Rightarrow> set) \<Rightarrow> (set \<Rightarrow> set \<Rightarrow> set \<Rightarrow> set \<Rightarrow> set) \<Rightarrow> (set \<Rightarrow> set \<Rightarrow> set \<Rightarrow> set) \<Rightarrow> set \<Rightarrow> set \<Rightarrow> set"
  where list_rep_rec_nil: "list_rep_rec n c f a Nil_rep = n a"
    and list_rep_rec_cons: "x : Element A \<Longrightarrow> xs : Element (List_rep A) \<Longrightarrow>
    list_rep_rec n c f a (Cons_rep x xs) = coprod_rec (\<lambda>b. c x xs a b) (\<lambda>b. c x xs a (list_rep_rec n c f b xs)) (f x xs a)"

lemma list_rep_rec_type [type]:
  "list_rep_rec : (Element X \<Rightarrow> Element Y) \<Rightarrow> (Element A \<Rightarrow> Element (List_rep A) \<Rightarrow> Element X \<Rightarrow> Element Y \<Rightarrow> Element Y) \<Rightarrow> (Element A \<Rightarrow> Element (List_rep A) \<Rightarrow> Element X \<Rightarrow> Element (coprod Y X)) \<Rightarrow> Element X \<Rightarrow> Element (List_rep A) \<Rightarrow> Element Y"
proof (intro Dep_fun_typeI)
  fix n c f a xs
  assume assms[type]:
    "n : Element X \<Rightarrow> Element Y"
    "c : Element A \<Rightarrow> Element (List_rep A) \<Rightarrow> Element X \<Rightarrow> Element Y \<Rightarrow> Element Y"
    "f : Element A \<Rightarrow> Element (List_rep A) \<Rightarrow> Element X \<Rightarrow> Element (coprod Y X)"
    "a : Element X"
    "xs : Element (List_rep A)"
  have "a : Element X \<Longrightarrow> list_rep_rec n c f a xs : Element Y"
  proof (induction xs arbitrary: a rule: List_rep_induct)
    case 1
    show "xs : Element (List_rep A)" by simp
  next
    case 2
    fix a
    assume assm2: "a : Element X"
    show "list_rep_rec n c f a Nil_rep : Element Y"
      apply (subst list_rep_rec_nil)
      apply (rule Fun_typeE[OF _ assms(1)])
      apply (fact assm2)
      done
    next
    case 3
    fix a x xs
    assume assms3:
      "x : Element A"
      "xs : Element (List_rep A)"
      "\<And>a. a : Element X \<Longrightarrow> list_rep_rec n c f a xs : Element Y"
      "a : Element X"
    show "list_rep_rec n c f a (Cons_rep x xs) : Element Y"
    thm Fun_typeE[OF _ Fun_typeE[OF _ Fun_typeE[OF _ assms(3)]]]
      apply (subst list_rep_rec_cons[OF assms3(1, 2)])
      apply (rule Fun_typeE[OF _ Fun_typeE[OF _ Fun_typeE[OF _ coprod_rec_type]]])
      apply (subst mem_coprod_iff_Coprod[symmetric])
      apply (rule ElementD)
      apply (rule Fun_typeE[OF _ Fun_typeE[OF _ Fun_typeE[OF _ assms(3)]]])
      apply (fact assms3)+
      apply (rule Fun_typeE'')
      apply (rule Fun_typeE[OF _ Fun_typeE[OF _ Fun_typeE[OF _ Fun_typeE[OF _ assms(2)]]]])
      apply (fact assms3 | rule assms3)+
      apply (rule Fun_typeE[OF _ Fun_typeE[OF _ Fun_typeE[OF _ assms(2)]]])
      apply (fact assms3)+
      done
  qed
  thus "list_rep_rec n c f a xs : Element Y"
    using assms(4) by simp
qed

definition "map_rep f xs \<equiv>
  list_rep_rec (\<lambda>_. Nil_rep) (\<lambda>h _ _ l. Cons_rep (f h) l) (\<lambda>_ _ _. inr \<emptyset>) \<emptyset> xs"

lemma singleton_type: "a : Element {a}"
  by (unfold_types, simp)

lemma "map_rep : (Element A \<Rightarrow> Element B) \<Rightarrow> Element (List_rep A) \<Rightarrow> Element (List_rep B)"
proof (intro Dep_fun_typeI)
  fix f xs
  assume assms:
    "f : Element A \<Rightarrow> Element B"
    "xs : Element (List_rep A)"
  show "map_rep f xs : Element (List_rep B)"
    apply (subst map_rep_def)
    apply (rule Fun_typeE[OF _ Fun_typeE[OF _ Fun_typeE[OF _ Fun_typeE[OF _ Fun_typeE[OF _ list_rep_rec_type]]]]])
        apply (fact assms(2))
    apply (fact singleton_type)
      apply (rule Fun_typeE'')+
      apply (rule ElementI)
      apply (subst mem_coprod_iff_Coprod)
      apply (rule Fun_typeE[OF _ inr_type])
    apply (rule singleton_type)
      apply (rule Fun_typeE'')+
     apply (rule Fun_typeE[OF _ Fun_typeE[OF _ Cons_rep_type]])
    apply assumption
       apply (rule Fun_typeE[OF _ assms(1)])
    apply assumption
    apply (rule Fun_typeE'')+
    apply (rule Nil_rep_type)
    done
qed

definition "list_all2 R xs ys \<equiv>
  list_rep_rec
    (list_rep_case True_set (\<lambda>_ _. False_set))
    (\<lambda>h t a b. and_set b (list_rep_case False_set (\<lambda>h' _. R h' h) a))
    (\<lambda>h t l. list_rep_case (inl False_set) (\<lambda>_ t. inr t) l)
    xs ys"

lemma "list_all2 : (Element A \<Rightarrow> Element B \<Rightarrow> Element Bool_set) \<Rightarrow> Element (List_rep A) \<Rightarrow> Element (List_rep B) \<Rightarrow> Element Bool_set"
proof (intro Dep_fun_typeI)
  fix R xs ys
  assume assms:
    "R : Element A \<Rightarrow> Element B \<Rightarrow> Element Bool_set"
    "xs : Element (List_rep A)"
    "ys : Element (List_rep B)"
  show "list_all2 R xs ys : Element Bool_set"
    apply (subst list_all2_def)
    apply (rule Fun_typeE[OF _ Fun_typeE[OF _ Fun_typeE[OF _ Fun_typeE[OF _ Fun_typeE[OF _ list_rep_rec_type]]]]])
        apply (fact assms(3))
       apply (fact assms(2))
      apply (rule Fun_typeE'')+
      apply (rule Fun_typeE[OF _ Fun_typeE[OF _ Fun_typeE[OF _ list_rep_case_type]]])
    apply assumption
      apply (rule Fun_typeE'')+
      apply (rule ElementI)
      apply (subst mem_coprod_iff_Coprod)
      apply (rule Fun_typeE[OF _ inr_type])
    apply assumption
      apply (rule ElementI)
      apply (subst mem_coprod_iff_Coprod)
      apply (rule Fun_typeE[OF _ inl_type])
    apply (rule False_type)
       apply (rule Fun_typeE'')+
       apply (rule Fun_typeE[OF _ Fun_typeE[OF _ and_set_type]])
      apply (rule Fun_typeE[OF _ Fun_typeE[OF _ Fun_typeE[OF _ list_rep_case_type]]])
    apply assumption
       apply (rule Fun_typeE'')+
       apply (rule Fun_typeE[OF _ Fun_typeE[OF _ assms(1)]])
    apply assumption
    apply assumption
      apply (rule False_type)
    apply assumption
       apply (rule Fun_typeE[OF _ Fun_typeE[OF _ list_rep_case_type]])
        apply (rule Fun_typeE'')+
      apply (rule False_type)
     apply (rule True_type)
    done
qed


interpretation List: set_extension "option A" "List_rep A" option_in_list
proof
  show "option_in_list : Option A \<Rightarrow> Element (List_rep A)"
    using option_in_list_type .
  show "\<forall>x \<in> option A. \<forall>y \<in> option A. option_in_list x = option_in_list y \<longrightarrow> x = y"
    unfolding option_in_list_def
    using cons_inject singleton_rep_inject
    case_some singleton_rep_def
    by (smt (z3) Bounded_Quantifiers.ballI Bounded_Quantifiers.bexE nil_neq_cons option_case_def option_iff)
qed

abbreviation "list \<equiv> List.abs_image"
abbreviation "List A \<equiv> Element (list A)"

lemmas option_subset_list [simp] = List.subset_abs_image

corollary [derive]: "x : Option A \<Longrightarrow> x : List A"
  apply unfold_types
  apply (rule mem_if_mem_if_subset)
  using option_subset_list by auto

definition "Nil A = List.Abs A Nil_rep"

definition "Cons A x xs = List.Abs A (Cons_rep x (List.Rep A xs))"

lemma Nil_type [type]: "Nil A : List A"
  apply unfold_types
  unfolding Nil_def by simp

lemma Cons_type [type]: "Cons A : (Element A \<Rightarrow> List A \<Rightarrow> List A)"
proof (unfold_types)
  fix x xs
  assume assms: "x \<in> A" "xs \<in> list A"
  have "List.Rep A xs \<in> List_rep A" by simp
  thus "Cons A x xs \<in> list A"
    unfolding Cons_def
    using  Cons_rep_type' by simp
qed

definition "list_all2' R xs ys \<equiv> list_all2 (\<lambda>x y. if R x y = True then True_set else False_set) xs ys = True_set"

term List.Rep
thm List.Rep_def set_extension.Rep_def
thm set_extension_lifting[OF List.set_extension_axioms]

hide_const abs

definition "rep_List rep \<equiv> map_rep rep"
definition "abs_List abs \<equiv> map_rep abs"
definition "Rel_List R \<equiv> list_all2' R"
definition "Eq_rep_List Eq \<equiv> list_all2' Eq"
definition "Eq_abs_List Eq \<equiv> list_all2' Eq"


definition "relator_resp_functor R F \<equiv>
  \<forall>r f g. (\<forall>x y. r x y \<longrightarrow> r x (f x) \<and> r (g y) y) \<longrightarrow>
    (\<forall>x y. R r x y \<longrightarrow> R r x (F f x) \<and> R r (F g y) y)"

lemma relator_resp_functor:
  assumes "relator_resp_functor R F"
      and "lifting Eq_rep Eq_abs T abs rep"
      and "R T x y"
    shows "R T x (F abs x)" "R T (F rep y) y"
proof -
  have "\<forall>x y. T x y \<longrightarrow> T x (abs x) \<and> T (rep y) y"
    using assms(2)[unfolded lifting_unfold]
    by blast
  thus "R T x (F abs x)"
    using assms(1, 3)[unfolded relator_resp_functor_def]
    by blast
next
  have "\<forall>x y. T x y \<longrightarrow> T x (abs x) \<and> T (rep y) y"
    using assms(2)[unfolded lifting_unfold]
    by blast
  thus "R T (F rep y) y "
    using assms(1, 3)[unfolded relator_resp_functor_def]
    by blast
qed

definition "relator R \<equiv>
  (\<forall>S T. rel_comp' (R S) (R T) = R (rel_comp' S T)) \<and>
  (\<forall>S. rel_inv (R S) = R (rel_inv S))"

lemma relator_per:
  assumes R: "relator R"
      and E: "partial_equivalence E"
    shows "partial_equivalence (R E)"
proof -
  { fix x y z
    assume prems: "R E x y" "R E y z"
    have "rel_comp' (R E) (R E) x z"
      using prems rel_comp'_def by metis
    hence "R (rel_comp' E E) x z"
      using R relator_def by metis
    hence "R E x z"
      using E per_idemp by metis
  }
  note trans = this
  { fix x y
    assume "R E x y"
    hence "R (rel_inv E) x y"
      using E per_inv by metis
    hence "rel_inv (R E) x y"
      using R relator_def by metis
    hence "R E y x"
      using rel_inv_def by metis
  }
  note sym = this
  show ?thesis
    using trans sym partial_equivalence_unfold by blast
qed

lemma list_all2'_is_relator: "relator list_all2'"
  sorry

lemma relator_inv: "relator R \<Longrightarrow> rel_inv (R S) = R (rel_inv S)"
  using relator_def
  by blast

lemma relator_comp: "relator R \<Longrightarrow> rel_comp' (R S) (R T) = R (rel_comp' S T)"
  using relator_def
  by blast

definition "functor F \<equiv> (\<forall>f g. F (comp f g) = comp (F f) (F g)) \<and> F id = id"

definition "rel_functor R \<equiv>
  (\<forall>Eq_rep1 Eq_abs1 T1 abs1 rep1 Eq_rep2 Eq_abs2 T2 abs2 rep2.
    lifting Eq_rep1 Eq_abs1 T1 abs1 rep1 \<longrightarrow>
    lifting Eq_rep2 Eq_abs2 T2 abs2 rep2 \<longrightarrow>
    R (rel_comp' T1 T2) = rel_comp' (R T1) (R T2))"

term relator

lemma rel_functor_comp:
  assumes "rel_functor R"
      and "lifting Eq_rep1 Eq_abs1 T1 abs1 rep1"
      and "lifting Eq_rep2 Eq_abs2 T2 abs2 rep2"
    shows "R (rel_comp' T1 T2) = rel_comp' (R T1) (R T2)"
  using assms
  unfolding rel_functor_def rel_comp'_def
  by blast

lemma lifing_abs_idemp:
  assumes assm: "lifting Eq_rep Eq_abs T abs rep"
  shows "rel_comp' Eq_abs T = T"
proof ((rule ext)+, rule iffI)
  fix x y
  assume "rel_comp' Eq_abs T x y"
  then obtain z where "T x z" "Eq_abs z y"
    using rel_comp'_def by metis
  thus "T x y"
    using assms[unfolded lifting_unfold]
    by metis
next
  fix x y
  assume "T x y"
  hence "T x (abs x)" "Eq_abs (abs x) y"
    using assms[unfolded lifting_unfold]
    by metis+
  thus "rel_comp' Eq_abs T x y"
    using rel_comp'_def by metis
qed

lemma lifing_rep_idemp:
  assumes assm: "lifting Eq_rep Eq_abs T abs rep"
  shows "rel_comp' T Eq_rep = T"
proof ((rule ext)+, rule iffI)
  fix x y
  assume "rel_comp' T Eq_rep x y"
  then obtain z where "Eq_rep x z" "T z y"
    using rel_comp'_def by metis
  thus "T x y"
    using assms[unfolded lifting_unfold]
    by metis
next
  fix x y
  assume "T x y"
  hence "T (rep y) y" "Eq_rep x (rep y)"
    using assms[unfolded lifting_unfold]
    by metis+
  thus "rel_comp' T Eq_rep x y"
    using rel_comp'_def by metis
qed

lemma map_rep_is_functor: "functor map_rep"
  sorry

lemma list_all2'_is_rel_functor: "rel_functor list_all2'"
  sorry

lemma list_relator_resp_functor: "relator_resp_functor list_all2' map_rep"
  sorry

lemma list_relator:
  assumes assm: "lifting Eq_rep Eq_abs T abs rep"
  shows "lifting (list_all2' Eq_rep) (list_all2' Eq_abs) (list_all2' T) (map_rep abs) (map_rep rep)"
proof (rule liftingI)
  note pers = lifting_eq_per[OF assm]
  fix x y
  assume prems: "list_all2' Eq_rep x y"
  show "list_all2' Eq_rep y x"
    by (fact per_sym[OF relator_per[OF list_all2'_is_relator pers(1)] prems])
next
  note pers1 = lifting_eq_per[OF assm]
  note pers2 = relator_per[OF list_all2'_is_relator pers1(1)] relator_per[OF list_all2'_is_relator pers1(2)]
  fix x y z
  assume prems:
    "list_all2' Eq_rep x y"
    "list_all2' Eq_rep y z"
  show "list_all2' Eq_rep x z"
    by (fact per_trans[OF pers2(1) prems])
next
  note pers1 = lifting_eq_per[OF assm]
  note pers2 = relator_per[OF list_all2'_is_relator pers1(1)] relator_per[OF list_all2'_is_relator pers1(2)]
  fix x y
  assume prems: "list_all2' Eq_abs x y"
  show "list_all2' Eq_abs y x"
    by (fact per_sym[OF pers2(2) prems])
next
  note pers1 = lifting_eq_per[OF assm]
  note pers2 = relator_per[OF list_all2'_is_relator pers1(1)] relator_per[OF list_all2'_is_relator pers1(2)]
  fix x y z
  assume prems:
    "list_all2' Eq_abs x y"
    "list_all2' Eq_abs y z"
  show "list_all2' Eq_abs x z"
    by (fact per_trans[OF pers2(2) prems])
next
  fix x y z
  assume prems:
    "list_all2' T x z"
    "list_all2' T y z"
  note 1 = rel_invI[of "list_all2' T", OF prems(2)]
  show "list_all2' Eq_rep x y"
    apply (subst lifting_rel_comp(2)[OF assm, symmetric])
    apply (subst rel_functor_comp[OF list_all2'_is_rel_functor inv_lifting[OF assms] assms])
    (* apply (subst relator_inv[OF list_all2'_is_relator, symmetric]) *)
    using prems(1) 1 rel_comp'_def by metis
next
  fix x y z
  assume prems:
    "list_all2' T x y"
    "list_all2' T x z"
  note 1 = rel_invI[of "list_all2' T", OF prems(1)]
  show "list_all2' Eq_abs y z"
    apply (subst lifting_rel_comp(1)[OF assm, symmetric])
    apply (subst rel_functor_comp[OF list_all2'_is_rel_functor assms inv_lifting[OF assms]])
    (* apply (subst relator_inv[OF list_all2'_is_relator, symmetric]) *)
    using prems(2) 1 rel_comp'_def by metis
next
  fix x y z
  assume prems:
    "list_all2' Eq_rep x y"
    "list_all2' T x z"
  note pers1 = lifting_eq_per[OF assm]
  note rel_comp'I[of "rel_inv (list_all2' Eq_rep)" _ _ "list_all2' T", OF
      rel_invI[of "list_all2' Eq_rep", OF prems(1)]
      prems(2)]
  hence "list_all2' (rel_comp' T Eq_rep) y z"
    using relator_inv relator_comp list_all2'_is_relator per_inv[OF pers1(1)]
    by metis
  thus "list_all2' T y z"
    using lifing_rep_idemp[OF assm]
    by simp
next
  fix x y z
  assume prems:
    "list_all2' Eq_abs y z"
    "list_all2' T x y"
  note pers1 = lifting_eq_per[OF assm]
  note rel_comp'I[of "list_all2' T" _ _ "list_all2' Eq_abs",OF prems(2) prems(1)]
  hence "list_all2' (rel_comp' Eq_abs T) x z"
    using relator_inv relator_comp list_all2'_is_relator per_inv[OF pers1(2)]
    by metis
  thus "list_all2' T x z"
    using lifing_abs_idemp[OF assm]
    by simp
next
  fix x
  assume prem: "list_all2' Eq_rep x x"
  have 1: "list_all2' (rel_comp' (rel_inv T) T) x x"
    apply (subst lifting_rel_comp[OF assms])
    apply (fact prem)
    done
  obtain y where y: "list_all2' T x y"
    using 1[folded relator_comp[OF list_all2'_is_relator]] rel_comp'_def
    by metis
  show "list_all2' T x (map_rep abs x)"
    apply (rule relator_resp_functor[OF list_relator_resp_functor])
    apply (fact assms)
    apply (fact y)
    done
next
  fix y
  assume prem: "list_all2' Eq_abs y y"
  have 1: "list_all2' (rel_comp' T (rel_inv T)) y y"
    apply (subst lifting_rel_comp[OF assms])
    apply (fact prem)
    done
  obtain x where x: "list_all2' T x y"
    using 1[folded relator_comp[OF list_all2'_is_relator]] rel_comp'_def
    by metis
  show "list_all2' T (map_rep rep y) y"
    apply (rule relator_resp_functor[OF list_relator_resp_functor])
    apply (fact assms)
    apply (fact x)
    done
qed

definition "List_Rel A R \<equiv> Param_Ext_Rel List.abs_image List.Rep list_all2' A R"

lemma "List_Rel A R Nil_rep (Nil A)"
proof -
  show "List_Rel A R Nil_rep (Nil A)"
    apply (subst Nil_def)
    unfolding List_Rel_def[unfolded Param_Ext_Rel_def]
    using lifting_Eq_rep(1)[OF list_relator] List_Rel_def[unfolded Param_Ext_Rel_def]
    sorry
qed



lemma list_rep_rec_ext:
  assumes c: "c : Element A \<Rightarrow> Element (List_rep A) \<Rightarrow> B \<Rightarrow> B"
    and c': "c' : Element A \<Rightarrow> Element (List_rep A) \<Rightarrow> B \<Rightarrow> B"
    and eq: "\<And>x xs a. x : Element A \<Longrightarrow> xs : Element (List_rep A) \<Longrightarrow> a : B \<Longrightarrow> c x xs a = c' x xs a"
    and n: "n : B"
    and xs: "xs : Element (List_rep A)"
  shows "list_rep_rec n c xs = list_rep_rec n c' xs"
proof -
  have "n : B \<Longrightarrow> list_rep_rec n c xs = list_rep_rec n c' xs"
  proof (induction arbitrary: n rule: List_rep_induct[OF xs])
    case 1
    show ?case by ((subst list_rep_rec_nil)+, rule refl)
  next
    case (2 x xs)
    then show ?case
      apply (subst list_rep_rec_cons[OF 2(1, 2)])+
      apply (subst 2(3))
      apply assumption
      apply (rule eq)
      apply assumption+
      apply (rule Fun_typeE[OF 2(2), of "list_rep_rec n c'" B])
      apply (rule Fun_typeE[OF c', of "list_rep_rec n" "Element (List_rep A) \<Rightarrow> B"])
      apply (rule Fun_typeE[OF 2(4), of "list_rep_rec" "(Element A \<Rightarrow> Element (List_rep A) \<Rightarrow> B \<Rightarrow> B) \<Rightarrow> Element (List_rep A) \<Rightarrow> B"])
      apply (rule list_rec_type)
      done
  qed
  note 1 = this
  show "list_rep_rec n c xs = list_rep_rec n c' xs"
    by (fact 1[OF n])
qed

definition "list_rep_all2 R xs ys \<equiv> list_rep_rec "

definition "List_Rel A xs xs' \<equiv> xs' \<in> List.abs_image A \<and> List.Rep A xs' = xs"

lemma List_Rel_def': "List_Rel A = Rel (List.abs_image A) (List.Rep A)"
  unfolding List_Rel_def Rel_def
  by blast

definition "Eq A x y \<equiv> x \<in> A \<and> x = y"

lemma Eq_refl [transfer_rule]: "x \<in> A \<Longrightarrow> Eq A x x"
  unfolding Eq_def by simp

lemma List_Rel_Nil [transfer_rule]: "List_Rel A Nil_rep (Nil A)"
  unfolding List_Rel_def Nil_def by simp

lemma List_Rel_Cons [transfer_rule]: "((Eq A) ===> List_Rel A ===> List_Rel A) Cons_rep (Cons A)"
  unfolding rel_fun_def List_Rel_def Cons_def
proof auto
  fix x x' xs
  assume assms: "Eq A x' x" "xs \<in> list A"
  have "x : Element A"
    using assms(1) Eq_def by auto
  moreover have "List.Rep A xs : Element (List_rep A)"
    using assms(1) by simp
  ultimately have "Cons_rep x (List.Rep A xs) : Element (List_rep A)"
    using Cons_rep_type by simp
  thus "List.Abs A (Cons_rep x (List.Rep A xs)) \<in> list A"
    using List.Abs_type mem_iff_Element by simp
  show "x = x'" using assms(1) Eq_def by simp
qed

lemma List_Rel_eq [transfer_rule]: "(List_Rel A ===> List_Rel A ===> (=)) (=) (=)"
  unfolding rel_fun_def List_Rel_def
  using List.Rep_inverse by fastforce

lemma List_ball [transfer_rule]: "((Eq A ===> (=)) ===> (=)) (ball A) (ball A)"
  unfolding rel_fun_def List_Rel_def Eq_def
  by blast

lemma List_ball' [transfer_rule]: "((List_Rel A ===> (=)) ===> (=)) (ball (List_rep A)) (ball (list A))"
  unfolding rel_fun_def List_Rel_def List_Rel_def
  sorry

lemma Nil_neq_Cons: "ball A (\<lambda>x. ball (list A) (\<lambda>xs. Nil A \<noteq> Cons A x xs))"
  apply (transfer fixing: A)
  by simp

definition "list_rec A n c xs \<equiv> list_rep_rec n (\<lambda>x xs a. c x (List.Abs A xs) a) (List.Rep A xs)"

lemma Eq_def'': "Eq A = Rel' A"
  unfolding Eq_def Rel'_def by (rule refl)

lemma Eq_def': "Eq A = Rel A id"
  unfolding Eq_def Rel_def id_def by blast

lemma ext: "(\<And>x. f x = g x) \<Longrightarrow> f = g" by (erule HOL.ext)

lemma List_rec: "(Eq B ===> (Eq A ===> List_Rel A ===> Eq B ===> Eq B) ===> List_Rel A ===> Eq B) list_rep_rec (list_rec A)"
proof (
    rewrite in "\<hole>" rel_fun_def,
    rewrite in "\<forall>_ _. _ \<longrightarrow> \<hole>" rel_fun_def,
    rewrite in "\<forall>_ _. _ \<longrightarrow> (\<forall>_ _. _ \<longrightarrow> \<hole>)" rel_fun_def,
    atomize_rev', rule triv)
  fix n f xs n' f' xs'
  assume rels: "Eq B n n'" "(Eq A ===> List_Rel A ===> Eq B ===> Eq B) f f'" "List_Rel A xs xs'"
  note 1 = Rel'[OF Eq_def' rels(1)]
  note 3 = Rel[OF List.set_extension_axioms rels(3)[unfolded List_Rel_def']]
  note reps = 1(1) 3(1)
  note abss = 1(2) 3(2)
  note in_defs = 1(3) 3(3)
  note in_reps = 1(4) 3(4)

  { fix x xs a
    assume assms: "x \<in> A" "xs \<in> List_rep A" "a \<in> B"
    have "f' x (List.Abs A xs) a = f x xs a"
    by (fact
      conjE2[OF rel_funE'[OF
        rel_funE'[OF
          rel_funE'[OF rels(2) Eq_refl[OF assms(1)]]
          Rel''(2)[OF List.set_extension_axioms assms(2), unfolded List_Rel_def'[symmetric]]]
        Eq_refl[OF assms(3)], unfolded Eq_def], symmetric])
  }
  note f_rep = this

  { fix x xs a
    assume assms: "x : Element A" "xs : Element (List_rep A)" "a : Element B"
    have "f x xs a = f' x (List.Abs A xs) a"
      by (fact f_rep[OF ElementD[OF assms(1)] ElementD[OF assms(2)] ElementD[OF assms(3)], symmetric])
  }
  note f_rep' = this

  have f'_type: "f' : Element A \<Rightarrow> List A \<Rightarrow> Element B \<Rightarrow> Element B"
    apply (rule type_from_rel_fun)
    apply (rule rels(2))
    apply unfold_types[1]
    apply (erule h2'[OF Eq_def'])

    apply (rule type_from_rel_fun)
    apply assumption
     apply unfold_types[1]
    apply (erule h2[OF List.set_extension_axioms List_Rel_def'])

    apply (rule type_from_rel_fun)
    apply assumption
    apply unfold_types[1]
    apply (erule h2'[OF Eq_def'])

    apply (rule type_from_rel_eq2)
    apply (rule Eq_def'')
    apply assumption
    done

  have f_type: "f : Element A \<Rightarrow> Element (List_rep A) \<Rightarrow> Element B \<Rightarrow> Element B"
    apply (rule type_from_rel_fun1)
    apply (rule rels(2))
    apply unfold_types[1]
    apply (erule h2'1[OF Eq_def'])

    apply (rule type_from_rel_fun1)
    apply assumption
     apply unfold_types[1]
    apply (erule h21[OF List.set_extension_axioms List_Rel_def'])

    apply (rule type_from_rel_fun1)
    apply assumption
    apply unfold_types[1]
    apply (erule h2'1[OF Eq_def'])

    apply (rule type_from_rel_eq1)
    apply (rule Eq_def'')
    apply assumption
    done

  note types = ElementI[OF in_defs(1)] ElementI[OF in_defs(2)] ElementI[OF in_reps(1)] ElementI[OF in_reps(2)] f_type f'_type
  show "Eq B (list_rep_rec n f xs) (list_rec A n' f' xs')"
  proof (subst Eq_def, rule conjI)
    show "list_rep_rec n f xs \<in> B"
    (* doesn't need to be automated *)
    proof (induction rule: List_rep_induct[OF types(4)])
      case 1
      show ?case
      apply (subst list_rep_rec_nil)
      apply (rule in_reps)
      done
    next
      case (2 x xs)
      show ?case
        apply (subst list_rep_rec_cons[OF 2(1, 2)])
        apply (rule ElementD)
        apply (fact
          Fun_typeE[of "list_rep_rec n f xs", OF ElementI[OF 2(3)]
            Fun_typeE[of xs _ "f x", OF 2(2)
              Fun_typeE[OF 2(1) types(5)]]])
        done
    qed
  next
    show "list_rep_rec n f xs = list_rec A n' f' xs'"
      apply (subst list_rec_def)
      apply (subst reps)+
      apply (rule list_rep_rec_ext[OF f_type _ f_rep'])
      defer
      apply assumption+
        apply (fact types)+
      apply (rule Fun_typeE'')+
      apply unfold_types
      done
  qed
qed

end