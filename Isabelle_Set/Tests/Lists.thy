section \<open>Lists\<close>
theory Lists
imports
  Isabelle_Set.Least_Fixpoint
  Isabelle_Set.TSFunctions
begin
text \<open>This theory aims to replicate the example from "Programming and Proving in
Isabelle/HOL". Compared to HOL, many conveniences are missing, but the reasoning
is basically the same.\<close>

text \<open>Of course, the following tedium can be fully automated.\<close>

definition nil where "nil = inl {}"
definition cons where "cons x xs = inr \<langle>x, xs\<rangle>"

definition "list_op A L \<equiv> {nil} \<union> {cons x xs | \<langle>x, xs\<rangle> \<in> A \<times> L}"

definition "list A \<equiv> lfp (univ A) (list_op A)"

lemma nil_ne_cons [iff]: "nil \<noteq> cons x xs"
  unfolding nil_def cons_def by simp

lemma cons_inj [iff]: "cons x xs = cons y ys \<longleftrightarrow> (x = y \<and> xs = ys)"
  unfolding cons_def by simp

(*needed for list_op_Monop*)
lemma [type]: "A : Subset (univ A)" by unfold_types auto
lemma [type]: "nil : Element (univ A)"
  unfolding nil_def by unfold_types auto
lemma [type]:
  "cons : Element (univ A) \<Rightarrow> Element (univ A) \<Rightarrow> Element (univ A)"
  unfolding cons_def by unfold_types auto
lemma "A \<Longrightarrow> (A \<Longrightarrow> B) \<Longrightarrow> B"
  by (rule Pure.meta_impE)

lemma list_op_Monop [type]: "list_op : (A : Set) \<Rightarrow> Monop (univ A)"
  apply (intro Dep_fun_typeI)
  apply (unfold list_op_def)
  apply (rule bin_union_MonopI)
    apply discharge_types[1]
  apply (rule replacement_MonopI)
    apply (rule pairs_MonopI)
      apply discharge_types[1]
      apply discharge_types[1]
  apply (intro Dep_fun_typeI)
  apply unfold_types
  apply (drule subset_if_mem_powerset)
  apply (drule monoD[OF mono_pairs_rng, simplified le_set_eq_subset])
  apply (drule subsetD)
    apply assumption
  apply (tactic \<open>rotate_tac 2 1\<close>)
  apply (drule subsetD[OF monoD[OF mono_pairs_dom,
    simplified le_set_eq_subset, OF subset_univ]])
  apply discharge_types
  done

lemmas list_fold =
  fixpoint_lfp[OF Dep_fun_typeE[OF list_op_Monop Any_typeI],
    folded list_def, unfolded fixpoint_def]

lemma nil_type [type]: "nil : Element (list A)"
  by (subst list_fold[symmetric]) (unfold_types, unfold list_op_def, simp)

lemma cons_type [type]: "cons : Element A \<Rightarrow> Element (list A) \<Rightarrow> Element (list A)"
  by (subst (2) list_fold[symmetric]) (unfold_types, unfold list_op_def, auto)

lemma list_type [type]: "list : (A : Set) \<Rightarrow> Subset (univ A)"
  unfolding list_def by discharge_types

lemma list_induct:
  assumes xs_type: "xs : Element (list A)"
  assumes nil: "P nil"
  assumes cons:
    "\<And>x xs. x : Element A \<Longrightarrow> xs : Element (list A) \<Longrightarrow> P xs \<Longrightarrow> P (cons x xs)"
  shows "P xs"
proof (rule lfp_induct[OF Dep_fun_typeE[OF list_op_Monop Any_typeI], of xs A P,
  folded list_def, unfolded list_op_def])
  from xs_type show "xs \<in> list A" by unfold_types
next
  fix x assume "x \<in> {nil} \<union> {cons x xs | \<langle>x, xs\<rangle> \<in> A \<times> {xs \<in> list A | P xs}}"
  with nil cons show "P x" by auto
qed

(*experiment to derive a recursor*)
(* definition "list_rec_op A n c L \<equiv>
  {\<langle>nil, n\<rangle>} \<union> {\<langle>cons x xs, c x xs v\<rangle> | \<langle>x, \<langle>xs, v\<rangle>\<rangle> \<in> A \<times> L}"

definition "list_rec A n c \<equiv> lfp (univ A) (list_rec_op A n c)"

lemma list_rec_op_Monop [type]:
  shows "list_rec_op :
    (A : Set) \<Rightarrow> Element (M nil) \<Rightarrow> ((x : Element A) \<Rightarrow> (xs : Element (list A)) \<Rightarrow>
      Element (M xs) \<Rightarrow> Element (M (cons x xs))) \<Rightarrow> Monop (univ (\<Sum>xs \<in> list A. (M xs)))"
  apply (intro Dep_fun_typeI)
  apply (unfold list_rec_op_def)
  apply (rule bin_union_MonopI)
    apply (rule K_MonopI)
    apply unfold_types[1]
    apply (rule mem_powerset_if_subset)
    apply (subst singleton_subset_iff_mem)
    apply (rule univ_closed_pair)
      apply discharge_types[1]
      defer
      (* apply assumption *)
  apply (rule replacement_MonopI)
    apply (rule pairs_MonopI)
      apply (rule K_MonopI)
      defer
      apply discharge_types[1]
  apply (intro Dep_fun_typeI)
  apply unfold_types
  sorry

definition "list_rec' A n c xs \<equiv> (list_rec A n c)`xs"

lemma "list_rec' A n c nil = n" *)

axiomatization list_rec :: "set \<Rightarrow> (set \<Rightarrow> set \<Rightarrow> set \<Rightarrow> set) \<Rightarrow> set \<Rightarrow> set"
  where list_rec_nil: "list_rec n c nil = n"
  and list_rec_cons: "x : Element A \<Longrightarrow> xs : Element (list A) \<Longrightarrow>
    list_rec n c (cons x xs) = c x xs (list_rec n c xs)"

lemma list_rec_type [type]:
  "list_rec : X \<Rightarrow> (Element A \<Rightarrow> Element (list A) \<Rightarrow> X \<Rightarrow> X) \<Rightarrow> Element (list A) \<Rightarrow> X"
proof (intro Dep_fun_typeI)
  fix N C xs
  assume [type]: "N : X"
    "C : Element A \<Rightarrow> Element (list A) \<Rightarrow> X \<Rightarrow> X" "xs : Element (list A)"
  show "list_rec N C xs : X"
    by (induction xs rule: list_induct)
    (auto simp only: list_rec_nil list_rec_cons)
qed


subsection \<open>Append\<close>

definition "append xs ys \<equiv> list_rec ys (\<lambda>x _. cons x) xs"

lemma append_type [type]:
  "append : Element (list A) \<Rightarrow> Element (list A) \<Rightarrow> Element (list A)"
proof -
  have "(\<lambda>x _. cons x) : Element A \<Rightarrow> Element (list A) \<Rightarrow> Element (list A)
    \<Rightarrow> Element (list A)"
    by discharge_types
  then show ?thesis unfolding append_def by discharge_types
qed

declare [[auto_elaborate]]

lemma nil_append_eq [simp]: "append nil ys = ys"
  by (simp add: list_rec_nil append_def)

thm nil_append_eq

lemma cons_append_eq [simp]:
  "append (cons x xs) ys = cons x (append xs ys)"
  by (simp add: append_def list_rec_cons)

thm cons_append_eq

lemma append_assoc [simp]:
  "append (append xs ys) zs = append xs (append ys zs)"
  by (induction xs rule: list_induct) (simp_all, auto)

thm append_assoc

lemma append_nil_eq [simp]:
  "append xs nil = xs"
  by (induction xs rule: list_induct) (simp_all, auto)


subsection \<open>Rev\<close>

declare [[auto_elaborate = false]]

definition "rev \<equiv> list_rec nil (\<lambda>x _ acc. append acc (cons x nil))"

lemma rev_type [type]: "rev : Element (list A) \<Rightarrow> Element (list A)"
proof -
  have "(\<lambda>x _ acc. append acc (cons x nil)) :
    Element A \<Rightarrow> Element (list A) \<Rightarrow> Element (list A) \<Rightarrow> Element (list A)"
    by discharge_types
  then show ?thesis unfolding rev_def by discharge_types
qed

declare [[auto_elaborate]]

lemma rev_nil_eq [simp]: "rev nil = nil"
  by (simp add: rev_def list_rec_nil)

lemma rev_cons_eq [simp]: "rev (cons x xs) = append (rev xs) (cons x nil)"
  by (simp add: rev_def list_rec_cons)

lemma rev_app_eq [simp]: "rev (append xs ys) = append (rev ys) (rev xs)"
  by (induction xs rule: list_induct) (simp_all, auto)

lemma rev_rev_eq [simp]: "rev (rev xs) = xs"
  by (induction xs rule: list_induct) (simp_all, auto)


end
