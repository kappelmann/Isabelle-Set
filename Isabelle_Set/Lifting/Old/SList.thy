theory SList
  imports
    Isabelle_Set.Rewrite
    Lifting_Expe
    SOption
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

lemma Nil_rep_type [type]: "Nil_rep : Element (List_rep A)"
  by (subst List_rep_unfold) (unfold_types, auto)

lemma Cons_rep_type [type]:
  "Cons_rep : Element A \<Rightarrow> Element (List_rep A) \<Rightarrow> Element (List_rep A)"
  by (subst (2) List_rep_unfold) (unfold_types, auto)

lemma Cons_rep_type': "x \<in> A \<Longrightarrow> xs \<in> List_rep A \<Longrightarrow> Cons_rep x xs \<in> List_rep A"
  by simp

lemma opairD2: "\<langle>a, b\<rangle> \<in> A \<times> B \<Longrightarrow> b \<in> B"
  by simp

hide_fact def_lfp_induct
hide_const collect
thm Least_Fixpoint.lfp_induct
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
    then have "ys \<in> collect (List_rep A) P" using x by auto
    hence "P ys" using x assm by blast
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
  using List.Abs_Rep_inv by fastforce

lemma List_ball [transfer_rule]: "((Eq A ===> (=)) ===> (=)) (ball A) (ball A)"
  unfolding rel_fun_def List_Rel_def Eq_def
  by blast

lemma List_ball' [transfer_rule]: "((List_Rel A ===> (=)) ===> (=)) (ball (List_rep A)) (ball (list A))"
  unfolding rel_fun_def List_Rel_def List_Rel_def
  sorry

lemma Nil_neq_Cons: "ball A (\<lambda>x. ball (list A) (\<lambda>xs. Nil A \<noteq> Cons A x xs))"
  apply (transfer fixing: A)
  by simp

hide_type Set.set

axiomatization list_rep_rec :: "set \<Rightarrow> (set \<Rightarrow> set \<Rightarrow> set \<Rightarrow> set) \<Rightarrow> set \<Rightarrow> set"
  where list_rep_rec_nil: "list_rep_rec n c Nil_rep = n"
  and list_rep_rec_cons: "x : Element A \<Longrightarrow> xs : Element (List_rep A) \<Longrightarrow>
    list_rep_rec n c (Cons_rep x xs) = c x xs (list_rep_rec n c xs)"

lemma list_rec_type [type]:
  "list_rep_rec : X \<Rightarrow> (Element A \<Rightarrow> Element (List_rep A) \<Rightarrow> X \<Rightarrow> X) \<Rightarrow> Element (List_rep A) \<Rightarrow> X"
proof (intro Dep_fun_typeI)
  fix N C xs
  assume [type]: "N : X"
    "C : Element A \<Rightarrow> Element (List_rep A) \<Rightarrow> X \<Rightarrow> X" "xs : Element (List_rep A)"
  show "list_rep_rec N C xs : X"
    by (induction xs rule: List_rep_induct)
    (auto simp only: list_rep_rec_nil list_rep_rec_cons)
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