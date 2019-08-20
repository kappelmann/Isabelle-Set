section \<open>Example theory: Lists\<close>

text \<open>
  This theory aims to replicate the example from "Programming and Proving in Isabelle/HOL".

  Compared to HOL, many conveniences are missing, but the reasoning is basically the same.
\<close>


theory MyList
  imports "../Isabelle_Set"
begin

subsection \<open>Datatype definition\<close>

text \<open>Of course, the following tedium can be fully automated.\<close>

definition Nil where "Nil = Inl {}"
definition Cons where "Cons x xs = Inr \<langle>x, xs\<rangle>"

definition List where
  "List A = lfp (Univ A) (\<lambda>L. {Nil} \<union> {Cons x xs | \<langle>x, xs\<rangle> \<in> A \<times> L})"

lemma
  Nil_Univ[derive]: "Nil : element (Univ A)" and
  Cons_Univ[derive]: "x : element (Univ A) \<Longrightarrow> xs : element (Univ A) \<Longrightarrow> Cons x xs : element (Univ A)"
  unfolding Nil_def Cons_def
  by discharge_types

lemma List_distinct[simp]: "Nil \<noteq> Cons x xs"
  unfolding Nil_def Cons_def by simp

lemma Cons_inject[simp]: "Cons x xs = Cons y ys \<longleftrightarrow> (x = y \<and> xs = ys)"
  unfolding Cons_def by simp


lemma List_mono: "(\<lambda>L. {Nil} \<union> {Cons x xs | \<langle>x, xs\<rangle> \<in> A \<times> L}) : monop (Univ A)"
  apply (unfold split_def)
  apply (rule monop_UnI)
   apply discharge_types[1]
  apply (rule monop_ReplI)
   apply (rule monop_timesI)
  apply discharge_types
  apply (rule Cons_Univ)
   apply (drule fst_prod_type)
   apply (drule Univ_base_type, asSigmaption)
  apply (drule snd_prod_type)
  apply (rule Univ_baseent_closed_type'') (* Should be done by discharge_types, but too general unifier *)
   apply asSigmaption
  apply asSigmaption
  done

lemmas List_unfold = def_lfp_unfold[OF any_typeI List_mono List_def]

lemma Nil_type [type]: "Nil : element (List A)"
  by (subst List_unfold) (squash_types, auto)

lemma Cons_type [type]: "Cons : element A \<Rightarrow> element (List A) \<Rightarrow> element (List A)"
  by (subst (2) List_unfold) (squash_types, auto)

lemma List_type [type]: "List : set \<Rightarrow> set"
  by discharge_types

lemma List_induct:
  assumes xs_type: "xs : element (List A)"
  assumes Nil: "P Nil"
  assumes Cons: "\<And>x xs. x : element A \<Longrightarrow> xs : element (List A) \<Longrightarrow> P xs \<Longrightarrow> P (Cons x xs)"
  shows "P xs"
proof (rule def_lfp_induct[OF any_typeI List_mono List_def, of xs A P])
  from xs_type show "xs \<in> List A" by squash_types
next
  fix x assume "x \<in> {Nil} \<union> {MyList.Cons x xs | \<langle>x, xs\<rangle> \<in> A \<times> Collect (List A) P}"
  with Nil Cons
  show "P x" by squash_types auto
qed

axiomatization
  List_rec :: "set \<Rightarrow> (set \<Rightarrow> set \<Rightarrow> set \<Rightarrow> set) \<Rightarrow> set \<Rightarrow> set"
  where
  List_rec_Nil: "List_rec N C Nil = N" and
  List_rec_Cons: "x : element A \<Longrightarrow> xs : element (List A) \<Longrightarrow> 
    List_rec N C (Cons x xs) = C x xs (List_rec N C xs)"

setup \<open>soft_type_simp_solver\<close>

lemma List_rec_type[type]:
  "List_rec : R \<Rightarrow> (element A \<Rightarrow> element (List A) \<Rightarrow> R \<Rightarrow> R) \<Rightarrow> element (List A) \<Rightarrow> R"
proof (intro Pi_typeI)
  fix N C xs
  assume [type]: "N : R" "C : element A \<Rightarrow> element (List A) \<Rightarrow> R \<Rightarrow> R" "xs : element (List A)"

  show "List_rec N C xs : R"
    by (induct xs rule: List_induct, auto simp: List_rec_Nil List_rec_Cons) discharge_types
qed

subsection \<open>Append\<close>


definition append where
  "append xs ys = List_rec ys (\<lambda>x xs xsys. Cons x xsys) xs"

lemma append_type[type]: "append : element (List A) \<Rightarrow> element (List A) \<Rightarrow> element (List A)"
  unfolding append_def by discharge_types

declare [[auto_elaborate, trace_soft_types]]

lemma append_Nil[simp]: "append Nil ys = ys"
  by (simp add: List_rec_Nil append_def)

thm append_Nil

lemma append_Cons[simp]:
  "append (Cons x xs) ys = Cons x (append xs ys)"
  by (simp add: append_def List_rec_Cons)

thm append_Cons

lemma append_assoc[simp]:
  "append (append xs ys) zs = append xs (append ys zs)"
  by (induct xs rule: List_induct) auto

thm append_assoc

lemma append_to_Nil[simp]:
  "append xs Nil = xs"
  by (induct xs rule: List_induct) auto


subsection \<open>Rev\<close>

declare [[auto_elaborate = false]]

definition
  "rev = List_rec Nil (\<lambda>x xs rxs. append rxs (Cons x Nil))"

lemma rev_type[type]: "rev : element (List A) \<Rightarrow> element (List A)"
  unfolding rev_def by discharge_types

declare [[auto_elaborate]]

lemma rev_Nil[simp]: "rev Nil = Nil"
  by (simp add: rev_def List_rec_Nil)

lemma rev_Cons[simp]: "rev (Cons x xs) = append (rev xs) (Cons x Nil)"
  by (simp add: rev_def List_rec_Cons)

lemma rev_app[simp]: "rev (append xs ys) = append (rev ys) (rev xs)"
  by (induct xs rule: List_induct) auto

lemma rev_rev[simp]: "rev (rev xs) = xs"
  by (induct xs rule: List_induct) auto



end
