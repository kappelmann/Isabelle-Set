theory Lifting_Expe
  imports
    Rational
    Dep_Rel
begin

method_setup unfold =
  \<open>Attrib.thms >> (fn thms => fn ctxt =>
    SIMPLE_METHOD (FIRSTGOAL (rewrite_goal_tac ctxt thms)))\<close>

method prove_lifting_triple_rel_rep_if_in_codom uses rel_def rep_def =
  (unfold rel_def rep_def, rule conjI, assumption, rule refl)

method prove_rel_inj uses rel_def =
  (unfold rel_def, unfold_types)

method prove_lifting_triple_rel_abs_if_Eq_rep_self uses rel_def rep_inv =
  (unfold rel_def, erule conjE, erule HOL.subst, erule rep_inv)

lemma Rat_lifting_triple_rel_rep_if_in_codom: "a \<in> Rat.abs_image \<Longrightarrow> Rat_Rel (Rat.Rep a) a"
  by (prove_lifting_triple_rel_rep_if_in_codom rel_def: Rat_Rel_def rep_def: Rat.Rep_def)

lemma Rat_Rel_inj: "Rat_Rel a b \<Longrightarrow> Rat_Rel a' b \<Longrightarrow> a = a'"
  by (prove_rel_inj rel_def: Rat_Rel_def)

lemma Rat_lifting_triple_rel_abs_if_Eq_rep_self: "Rat_Rel a b \<Longrightarrow> Rat.Abs a = b"
  by (prove_lifting_triple_rel_abs_if_Eq_rep_self rel_def: Rat_Rel_def rep_inv: Rat.Abs_Rep_inv)


lemma Fun_typeE': "x \<in> A \<Longrightarrow> f : Element A \<Rightarrow> Element B \<Longrightarrow> f x \<in> B"
  by unfold_types

lemma Fun_typeE: "x : A \<Longrightarrow> f : A \<Rightarrow> B \<Longrightarrow> f x : B"
  by unfold_types

lemma rel_funE': "(A ===> B) f g \<Longrightarrow> (\<And>x y. A x y \<Longrightarrow> B (f x) (g y))"
  using rel_fun_def by metis

lemma conjE1: "(A \<and> B \<Longrightarrow> A)"
  by (rule HOL.conjE, assumption+)

lemma conjE1': "A \<and> B \<Longrightarrow> (B \<Longrightarrow> P) \<Longrightarrow> P"
  by (rule HOL.conjE, assumption+)

lemma conjE2: "A \<and> B \<Longrightarrow> B"
  by (erule conjE, assumption)

lemma conjE': "(P \<Longrightarrow> Q \<Longrightarrow> R) \<Longrightarrow> (P \<and> Q \<Longrightarrow> R)"
  by (erule conjE, assumption)

lemma ex_conj_True: "\<exists>x. P x \<Longrightarrow> \<exists>x. P x \<and> True" by simp

definition "surj' A B f \<equiv> ({f x | x \<in> A} = B)"

lemma Rep_surj:
  assumes set_ext: "set_extension A B f"
  shows "surj' (set_extension.abs_image A B f) B (set_extension.Rep A f)"
proof -
  define def where "def = set_extension.abs_image A B f"
  define Rep where "Rep = set_extension.Rep A f"
  define Abs where "Abs = set_extension.Abs A f"
  note 1 = this
  have 2: "{Rep y | y \<in> def} \<subseteq> B"
  proof
    fix y
    assume y: "y \<in> {Rep x | x \<in> def}"
    obtain x where x: "x \<in> def \<and> y = Rep x" using y by blast
    show "y \<in> B" using set_extension.Rep_type[OF set_ext] x Rep_def def_def
      by unfold_types
  qed
  have 3: "B \<subseteq> {Rep x | x \<in> def}"
  proof
    fix y
    assume y: "y \<in> B"
    have "Abs y \<in> def"
      using set_extension.Abs_type[OF set_ext] def_def Abs_def
      by unfold_types
    then obtain x where x: "x \<in> def \<and> y = Rep x"
      using set_extension.Rep_Abs_inv[OF set_ext] Abs_def Rep_def
      by fastforce
    show "y \<in> {Rep x | x \<in> def}" using x
      by blast
  qed
  show ?thesis
    using 2 3 unfolding def_def Rep_def surj'_def
    by auto
  qed

lemma Rep_eq:
  assumes set_ext: "set_extension A B f" "x \<in> set_extension.abs_image A B f"
    "y \<in> set_extension.abs_image A B f"
  shows "(set_extension.Rep A f x = set_extension.Rep A f y) = (x = y)"
proof (rule HOL.iffI)
  assume "set_extension.Rep A f x = set_extension.Rep A f y"
  thus "x = y" using assms set_extension.Abs_Rep_inv by metis
next
  assume "x = y"
  thus "set_extension.Rep A f x = set_extension.Rep A f y"
    using assms by simp
qed

lemma l1: "x \<in> A \<Longrightarrow> surj' A B f \<Longrightarrow> (\<And>y. y \<in> B \<Longrightarrow> P y) \<Longrightarrow> P (f x)"
  using surj'_def by auto

lemma subst': "x = y \<Longrightarrow> P x \<Longrightarrow> P y" by (erule subst, assumption)

lemma triv: "P x \<Longrightarrow> P x"
  by simp

lemma l4: "x \<in> \<int> \<Longrightarrow> Int.Rep x = y \<Longrightarrow> y \<in> int_rep"
  using Int.Rep_type Fun_typeE' by blast

lemma l5: "x \<in> A \<Longrightarrow> x = y \<Longrightarrow> y \<in> A" by simp

lemma doub: "(P \<Longrightarrow> Q) \<Longrightarrow> P \<Longrightarrow> Q" by simp

definition "Rel def Rep x y \<equiv> y \<in> def \<and> Rep y = x"

lemma Rel:
  fixes A B f
  defines "Rep \<equiv> set_extension.Rep A f"
    and "Abs \<equiv> set_extension.Abs A f"
    and "def \<equiv> set_extension.abs_image A B f"
  assumes axioms: "set_extension A B f"
    and rel: "Rel def Rep x y"
  shows "Rep y = x" "Abs x = y" "y \<in> def" "x \<in> B"
proof -
  show "Rep y = x"
    using rel by (meson Rel_def)
next
  show "Abs x = y"
    using set_extension.Abs_Rep_inv axioms rel by (metis Rel_def Rep_def def_def Abs_def)
next
  show "y \<in> def"
    using rel by (meson Rel_def)
next
  show "x \<in> B"
    using axioms rel set_extension.Rep_type by (metis Rel_def Rep_def def_def Fun_typeE')
qed

lemma Rel'':
  fixes A B f
  defines "Rep \<equiv> set_extension.Rep A f"
    and "Abs \<equiv> set_extension.Abs A f"
    and "def \<equiv> set_extension.abs_image A B f"
  assumes axioms: "set_extension A B f"
  shows "x \<in> def \<Longrightarrow> Rel def Rep (Rep x) x" "y \<in> B \<Longrightarrow> Rel def Rep y (Abs y)"
proof -
  show "x \<in> def \<Longrightarrow> Rel def Rep (Rep x) x"
    by (simp add: Lifting_Expe.Rel_def)
next
  show "y \<in> B \<Longrightarrow> Rel def Rep y (Abs y)"
    unfolding Rel_def
    using set_extension.Abs_type[OF axioms] set_extension.Rep_Abs_inv[OF axioms]
    by (simp add: Abs_def Fun_typeE' def_def Rep_def)
qed

lemma h2:
  fixes A B f
  defines "Rep \<equiv> set_extension.Rep A f"
    and "def \<equiv> set_extension.abs_image A B f"
  assumes axioms: "set_extension A B f"
    and rel: "R = Rel def Rep"
    and y: "y \<in> def"
  shows "\<exists>x. R x y"
  unfolding rel Rel_def by simp

lemma h2':
  assumes rel: "R = Rel A id"
    and y: "y \<in> A"
  shows "\<exists>x. R x y"
  unfolding rel Rel_def by simp

lemma Rel':
  assumes R_def: "R = Rel A id"
    and rel: "R x y"
  shows "y = x" "x = y" "y \<in> A" "x \<in> A"
  using R_def rel unfolding Rel_def by simp+

definition "Nat_Rel m n \<equiv> n \<in> nat \<and> m = n"

definition "Rel' A x y \<equiv> x \<in> A \<and> x = y"

lemma Nat_Rel_def'': "Nat_Rel = Rel' nat"
  unfolding Nat_Rel_def Rel'_def
  by fast

lemma Rel'I: "x \<in> A \<Longrightarrow> Rel' A x x"
  unfolding Rel'_def by simp

lemma Int_Rel_def': "Int_Rel = Rel \<int> Int.Rep"
  unfolding Int_Rel_def Rel_def by simp

lemma Rat_Rel_def': "Rat_Rel = Rel \<rat> Rat.Rep"
  unfolding Rat_Rel_def Rel_def by simp

lemma Nat_Rel_def': "Nat_Rel = Rel \<nat> id"
  unfolding Nat_Rel_def Rel_def by auto

lemma type_from_rel_type: "R x y \<Longrightarrow> (\<And>x y. R x y \<Longrightarrow> P y) \<Longrightarrow> y : type P"
  by unfold_types

lemma type_from_rel_elem: "R = Rel A f \<Longrightarrow> R x y \<Longrightarrow> y : Element A"
  apply unfold_types
  unfolding Rel_def
  by blast

lemma rel_from_type_elem: "y : Element A \<Longrightarrow> R = Rel A f \<Longrightarrow> \<exists>x. R x y"
  apply unfold_types
  unfolding Rel_def
  by blast

lemma rel_from_type_elem': "y : Element A \<Longrightarrow> R = Rel A f \<Longrightarrow> (\<And>x. R x y \<Longrightarrow> Q) \<Longrightarrow> Q"
  apply unfold_types
  unfolding Rel_def
  by blast

lemma type_from_rel_fun: "(R ===> S) f g \<Longrightarrow> (\<And>y. y : A \<Longrightarrow> \<exists>x. R x y) \<Longrightarrow> (\<And>x y. S (f x) (g y) \<Longrightarrow> g y : B) \<Longrightarrow> g : A \<Rightarrow> B"
  apply unfold_types
  unfolding rel_fun_def
  by blast

lemma type_from_rel_fun_adj: "([x x' \<Colon> R | P x x'] \<Rrightarrow> S) f g \<Longrightarrow> (\<And>x'. x' : A \<and> Q x' \<Longrightarrow> \<exists>x. R x x' \<and> P x x') \<Longrightarrow> (\<And>x x'. S (f x) (g x') \<Longrightarrow> g x' : B) \<Longrightarrow> g : (Q \<sqdot> A) \<Rightarrow> B"
  apply unfold_types
  unfolding dep_rel_fun_def rel_adj_def
  by blast

lemma type_from_rel_fun_dep:
  "(\<And>x y. R x y \<Longrightarrow> S x y (f x) (g y)) \<Longrightarrow> (\<And>y. y : A \<Longrightarrow> \<exists>x. R x y) \<Longrightarrow> (\<And>x y. S x y (f x) (g y) \<Longrightarrow>
    g y : B y) \<Longrightarrow> g : (x: A) \<Rightarrow> (B x)"
  apply unfold_types
  unfolding rel_fun_def
  by blast

lemma type_from_rel_fun_dep':
  "([x x' \<Colon> R] \<Rrightarrow> S x x') f g \<Longrightarrow> (\<And>x'. x' : A \<Longrightarrow> \<exists>x. R x x') \<Longrightarrow> (\<And>x x'. S x x' (f x) (g x') \<Longrightarrow>
    g x' : B x') \<Longrightarrow> g : (x : A) \<Rightarrow> (B x)"
  apply unfold_types
  unfolding dep_rel_fun_def rel_adj_def
  by blast

lemma Rat_Rel_add'': "(Rat_Rel ===> Rat_Rel ===> Rat_Rel) rat_rep_add rat_add"
proof ((subst rel_fun_def)+, atomize_rev', rule triv)
  fix i j i' j'
  assume rels: "Rat_Rel i i'" "Rat_Rel j j'"
  note 1 = Rel[OF Rat.set_extension_axioms rels(1)[unfolded Rat_Rel_def']]
  note 2 = Rel[OF Rat.set_extension_axioms rels(2)[unfolded Rat_Rel_def']]
  note reps = 1(1) 2(1)
  note abss = 1(2) 2(2)
  note in_defs = 1(3) 2(3)
  note in_reps = 1(4) 2(4)
  show "Rat_Rel (rat_rep_add i j) (i' + j')"
  proof (subst Rat_Rel_def, rule conjI)
    show "i' + j' \<in> \<rat>"
      apply (subst rat_add_def)
      apply (rule Fun_typeE'[OF _ Rat.Abs_type])
      apply (subst reps)+
      apply (insert in_reps)
      (* left to the user *)
      sorry
  next
    show "Rat.Rep (i' + j') = rat_rep_add i j"
      apply (subst rat_add_def)
      apply (subst Rat.Rep_Abs_inv)
      apply (subst reps)+
      apply (rule refl)
      done
  qed
qed

lemma rat_add_type': "rat_add : Rat \<Rightarrow> Rat \<Rightarrow> Rat"
  apply (rule type_from_rel_fun)
  apply (rule Rat_Rel_add)
   apply unfold_types[1]
  apply (erule h2[OF Rat.set_extension_axioms Rat_Rel_def'])

  apply (rule type_from_rel_fun)
  apply assumption
  apply unfold_types[1]
  apply (erule h2[OF Rat.set_extension_axioms Rat_Rel_def'])

  apply (rule type_from_rel_elem)
  apply (rule Rat_Rel_def')
  apply assumption
  done

lemma Int_Rel_divides'': "(Int_Rel ===> Int_Rel ===> (=)) divides_rep divides"
proof ((subst rel_fun_def)+, atomize_rev', rule triv)
  fix i j i' j'
  assume rels: "Int_Rel i i'" "Int_Rel j j'"
  note 1 = Rel[OF Int.set_extension_axioms rels(1)[unfolded Int_Rel_def']]
  note 2 = Rel[OF Int.set_extension_axioms rels(2)[unfolded Int_Rel_def']]
  note reps = 1(1) 2(1)
  note abss = 1(2) 2(2)
  note in_defs = 1(3) 2(3)
  note in_reps = 1(4) 2(4)
  show "divides_rep i j = divides i' j'"
    apply (subst divides_def)
    apply (subst reps)+
    apply (rule refl)
    done
qed

lemma divides_type': "divides : Integers.Int \<Rightarrow> Integers.Int \<Rightarrow> Bool"
  apply (rule type_from_rel_fun)
  apply (rule Int_Rel_divides'')
  apply unfold_types[1]
  apply (erule h2[OF Int.set_extension_axioms Int_Rel_def'])

  apply (rule type_from_rel_fun)
  apply assumption
  apply unfold_types[1]
  apply (erule h2[OF Int.set_extension_axioms Int_Rel_def'])

  apply (rule Any_typeI)
  done

lemma Rat_Rel_eq'': "(Int_Rel ===> Int_Rel ===> (=)) (=) (=)"
proof ((subst rel_fun_def)+, atomize_rev')
  fix i j i' j'
  assume rels: "Int_Rel i i'" "Int_Rel j j'"
  note 1 = Rel[OF Int.set_extension_axioms rels(1)[unfolded Int_Rel_def']]
  note 2 = Rel[OF Int.set_extension_axioms rels(2)[unfolded Int_Rel_def']]
  note reps = 1(1) 2(1)
  note abss = 1(2) 2(2)
  note in_defs = 1(3) 2(3)
  note in_reps = 1(4) 2(4)
  show "(i = j) = (i' = j')"
    apply (subst sym[OF Rep_eq[OF Int.set_extension_axioms in_defs]])
    apply (subst reps)+
    apply (rule refl)
    done
qed

definition "int_0_rep \<equiv> inl 0"
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
  apply (rule type_from_rel_elem, rule refl)
  apply (rule Int_Rel_0'[unfolded Int_Rel_def'])
  done

lemma Int_Rel_pow'': "(Nat_Rel ===> Int_Rel ===> Int_Rel) int_rep_pow int_pow"
proof ((subst rel_fun_def)+, atomize_rev')
  fix n i n' i'
  assume rels: "Nat_Rel n n'" "Int_Rel i i'"
  note 1 = Rel'[OF Nat_Rel_def' rels(1)]
  note 2 = Rel[OF Int.set_extension_axioms rels(2)[unfolded Int_Rel_def']]
  note reps = 1(1) 2(1)
  note abss = 1(2) 2(2)
  note in_defs = 1(3) 2(3)
  note in_reps = 1(4) 2(4)
  show "Int_Rel (int_rep_pow n i) (int_pow n' i')"
  proof (subst Int_Rel_def, rule conjI)
    show "int_pow n' i' \<in> \<int>"
      apply (subst int_pow_def)
      apply(rule Fun_typeE'[OF _ Int.Abs_type])
      apply (subst reps)+
      apply (insert in_reps)
      (* left to the user *)
      sorry
  next
    show "Int.Rep (int_pow n' i') = int_rep_pow n i"
      apply (subst int_pow_def)
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
  apply (erule h2'[OF Nat_Rel_def'])

  apply (rule type_from_rel_fun)
  apply assumption
  apply unfold_types[1]
  apply (erule h2[OF Int.set_extension_axioms Int_Rel_def'])

  apply (rule type_from_rel_elem)
  apply (rule Int_Rel_def')
  apply assumption
  done

lemma rat_pow_type'':
  assumes types: "n : Nat" "i : Integers.Int"
  shows "int_pow n i : Integers.Int"
  apply (rule type_from_rel_elem)
  apply (rule Int_Rel_def')
  apply (rule rel_funE'[OF rel_funE'[OF Int_Rel_pow'']])
  apply (subst Nat_Rel_def'')
  apply (fact Rel'I[OF ElementD[OF types(1)]])
  apply (subst Int_Rel_def')
  apply (fact Rel''(1)[OF Int.set_extension_axioms ElementD[OF types(2)]])
  done

(* Int_Rel i i' ===> (divides i \<sqdot> Int_Rel) ===> Int_Rel *)
(* Int_Rel i i' ===> Int_Rel j j' | divides i j ===> Int_Rel *)
lemma Int_Rel_div': "Int_Rel i i' \<Longrightarrow> Int_Rel j j' \<Longrightarrow> divides i' j' \<Longrightarrow> Int_Rel (Int_Rep_div i j) (int_div i' j')"
proof (unfold rel_fun_def)
  assume rels: "Int_Rel i i'" "Int_Rel j j'"
     and prems: "divides i' j'"
  note 1 = Rel[OF Int.set_extension_axioms rels(1)[unfolded Int_Rel_def']]
  note 2 = Rel[OF Int.set_extension_axioms rels(2)[unfolded Int_Rel_def']]
  note reps = 1(1) 2(1)
  note abss = 1(2) 2(2)
  note in_defs = 1(3) 2(3)
  note in_reps = 1(4) 2(4)
  (* only works for simple expressions, should be done by transfer *)
  note prems' = prems[unfolded divides_def reps]
  show "Int_Rel (Int_Rep_div i j) (int_div i' j')"
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
    show "Int.Rep (int_div i' j') = Int_Rep_div i j"
      apply (subst int_div_def)
      apply (subst Int.Rep_Abs_inv)
      apply (subst reps)+
      apply (rule refl)
      done
    qed
  qed

lemma Int_Rel_div''': "([i i' \<Colon> Int_Rel] \<Rrightarrow> [j j' \<Colon> Int_Rel | divides i' j'] \<Rrightarrow> Int_Rel) Int_Rep_div int_div"
proof ((subst dep_rel_fun_def rel_adj_def)+, atomize_rev', rule triv)
  fix i j i' j'
  assume rels_raw: "Int_Rel i i'" "Int_Rel j j' \<and> divides i' j'"
  note rels = rels_raw(1) conjE1[OF rels_raw(2)]
  note prems = conjE2[OF rels_raw(2)]
  note 1 = Rel[OF Int.set_extension_axioms rels(1)[unfolded Int_Rel_def']]
  note 2 = Rel[OF Int.set_extension_axioms rels(2)[unfolded Int_Rel_def']]
  note reps = 1(1) 2(1)
  note abss = 1(2) 2(2)
  note in_defs = 1(3) 2(3)
  note in_reps = 1(4) 2(4)
  note prems' = prems[unfolded divides_def reps]
  show "Int_Rel (Int_Rep_div i j) (int_div i' j')"
  proof (subst Int_Rel_def, rule conjI)
    show "int_div i' j' \<in> \<int>"
      apply (subst int_div_def)
      apply (rule Fun_typeE'[OF _ Int.Abs_type])
      apply (subst reps)+
      apply (insert in_reps prems')
      (* left to the user *)
      sorry
  next
    show "Int.Rep (int_div i' j') = Int_Rep_div i j"
      apply (subst int_div_def)
      apply (subst Int.Rep_Abs_inv)
      apply (subst reps)+
      apply (rule refl)
      done
  qed
qed

lemma int_div_type': "int_div: (i : Integers.Int) \<Rightarrow> (divides i \<sqdot> Integers.Int) \<Rightarrow> Integers.Int"
  apply (rule type_from_rel_fun_dep)
  prefer 2
  apply unfold_types[1]
  apply (rule h2[OF Int.set_extension_axioms Int_Rel_def'], assumption)
  oops

lemma int_div_type': "int_div: (i : Integers.Int) \<Rightarrow> (divides i \<sqdot> Integers.Int) \<Rightarrow> Integers.Int"
  apply (rule type_from_rel_fun_dep')
  apply (rule Int_Rel_div''')
  apply unfold_types[1]
  apply (erule h2[OF Int.set_extension_axioms Int_Rel_def'])

  apply (rule type_from_rel_fun_adj)
  apply assumption
  apply unfold_types[1]
  apply (erule conjE)
  apply (rule ex_conj_True)
  apply (erule h2[OF Int.set_extension_axioms Int_Rel_def'])

  apply (rule type_from_rel_elem)
  apply (rule Int_Rel_def')
  apply assumption
  done

lemma int_div_type'':
  assumes types: "i : Integers.Int" "j : Integers.Int"
    and refinements: "divides i j"
  shows "int_div i j : Integers.Int"
  apply (rule type_from_rel_elem)
  apply (rule Int_Rel_def')
  apply (rule Int_Rel_div')
  apply (subst Int_Rel_def')
  apply (fact Rel''(1)[OF Int.set_extension_axioms ElementD[OF types(1)]])
  apply (subst Int_Rel_def')
  apply (fact Rel''(1)[OF Int.set_extension_axioms ElementD[OF types(2)]])
  apply (fact refinements)
  done

lemma Rat_Rel_add': "(Rat_Rel ===> Rat_Rel ===> Rat_Rel) rat_rep_add rat_add"
  unfolding  rel_fun_def Rat_Rel_def
  apply atomize_rev'
  apply (rule conjI)
    (* drop non-relevant part of premises *)
   apply (drule conjE1)+
  unfolding rat_add_def
    (* make goal more readable *)
   apply(rule Fun_typeE'[OF _ Rat.Abs_type])
   apply (rule l1[OF _ Rep_surj[OF Rat.set_extension_axioms]], assumption)
   apply (rule l1[OF _ Rep_surj[OF Rat.set_extension_axioms]], assumption)
    (* clean up premises *)
   apply (erule HOL.cnf.weakening_thm)
   apply (erule HOL.cnf.weakening_thm)
   defer
    (* prove second goal *)
  unfolding Rat.Rep_Abs_inv
   apply (erule conjE1')+
   apply (erule subst)+
   apply (rule refl)
  sorry

lemma Rat_Rel_divides': "(Int_Rel ===> Int_Rel ===> (=)) divides_rep divides"
  unfolding  rel_fun_def Int_Rel_def
  apply atomize_rev'
  apply (rule triv)
  apply (erule conjE)+
  unfolding divides_def
  apply (drule l4, assumption)+
  apply (erule ssubst)+
  apply (rule refl)
  done

lemma Rat_Rel_eq': "(Int_Rel ===> Int_Rel ===> (=)) (=) (=)"
  unfolding  rel_fun_def Int_Rel_def
  apply atomize_rev'
  apply (rule triv)
  apply (erule conjE)+
  apply (erule subst)+
  apply (rule Rep_eq[OF Int.set_extension_axioms], assumption+)
  done

lemma Rat_Rel_pow': "(Nat_Rel ===> Int_Rel ===> Int_Rel) int_rep_pow int_pow"
  unfolding  rel_fun_def Int_Rel_def Nat_Rel_def
  apply atomize_rev'
  apply (rule conjI)
   apply (drule conjE1)+
  apply (subst int_pow_def)
   apply(rule Fun_typeE'[OF _ Int.Abs_type])
   apply (rule l1[OF _ Rep_surj[OF Int.set_extension_axioms]], assumption)
   apply (erule HOL.cnf.weakening_thm) back
   defer
  apply (subst int_pow_def)
  apply (subst Int.Rep_Abs_inv)
   apply (erule conjE1')+
   apply (erule subst)+
  apply (rule refl)
  sorry

lemma Int_Rel_div'': "Int_Rel i i' \<Longrightarrow> Int_Rel j j' \<Longrightarrow> divides i' j' \<Longrightarrow> Int_Rel (Int_Rep_div i j) (int_div i' j')"
  unfolding  rel_fun_def Int_Rel_def
  apply (rule conjI)
  apply (rule conjE')
  prefer 2 apply assumption
  apply (erule HOL.cnf.weakening_thm)
  apply (rule conjE')
  prefer 2 apply assumption
  apply (erule HOL.cnf.weakening_thm)
  apply (subst int_div_def)
   apply(rule Fun_typeE'[OF _ Int.Abs_type])
   apply (rule doub[where ?P="Int.Rep i' = i"])
    prefer 2 apply assumption
   apply (rule doub[where ?P="Int.Rep j' = j"])
    prefer 2 apply assumption
   apply (erule forw_subst)
   apply (erule forw_subst)
   apply (unfold divides_def)
   apply (erule ssubst)
  oops


end