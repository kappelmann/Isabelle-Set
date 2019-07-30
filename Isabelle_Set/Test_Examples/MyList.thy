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
  unfolding Nil_def Cons_def by discharge_types

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
   apply (drule Univ_elem_type, assumption)
  apply (drule snd_prod_type)
  apply squash_types
  apply auto
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





declare [[auto_elaborate, trace_soft_types]]

end
