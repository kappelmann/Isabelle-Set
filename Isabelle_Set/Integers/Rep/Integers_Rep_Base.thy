subsection \<open>Representation of Integers\<close>
theory Integers_Rep_Base
imports
  HOTG.Coproduct
  Nat
  Set_Extension
begin

text \<open>We construct the integers as a pair of a non-negative and a negative part.
By using the set extension principle, we ensure that \<open>\<nat> \<subseteq> \<int>\<close>.\<close>

(*TOOD: define as a quotient of \<nat> pairs instead?*)
definition "int_rep = \<nat> \<Coprod> (\<nat> \<setminus> {0})"

\<comment> \<open>Some type derivation rule setup\<close>
lemma [type]: "succ : Element \<nat> \<Rightarrow> Element (\<nat> \<setminus> {0})"
  unfolding int_rep_def by unfold_types auto


text \<open>Constructors, Recursor and Eliminator\<close>

definition "int_rep_nonneg \<equiv> inl"

definition "int_rep_neg \<equiv> inr"

lemma int_rep_nonneg_type [type]: "int_rep_nonneg : Nat \<Rightarrow> Element int_rep"
  unfolding int_rep_nonneg_def int_rep_def by discharge_types

lemma int_rep_neg_type [type]:
  "int_rep_neg : Element (\<nat> \<setminus> {0}) \<Rightarrow> Element int_rep"
  unfolding int_rep_neg_def int_rep_def by discharge_types

lemma
  int_rep_nonneg_eq_iff [iff]: "int_rep_nonneg x = int_rep_nonneg y \<longleftrightarrow> x = y" and
  int_rep_neg_eq_iff [iff]: "int_rep_neg x = int_rep_neg y \<longleftrightarrow> x = y" and
  int_rep_nonneg_ne_neg [simp, intro!]: "int_rep_nonneg x \<noteq> int_rep_neg y" and
  int_rep_neg_ne_nonneg [simp, intro!]: "int_rep_neg x \<noteq> int_rep_nonneg y"
  unfolding int_rep_nonneg_def int_rep_neg_def by auto

definition "int_rep_rec \<equiv> coprod_rec"

lemma
  shows int_rep_rec_nonneg_eq [simp]:
    "int_rep_rec f_nneg f_neg (int_rep_nonneg n) = f_nneg n"
  and int_rep_rec_neg_eq [simp]: "int_rep_rec f_nneg f_neg (int_rep_neg n) = f_neg n"
  unfolding int_rep_rec_def int_rep_nonneg_def int_rep_neg_def by simp_all

lemma int_rep_rec_type [type]:
  "int_rep_rec : (Element \<nat> \<Rightarrow> X) \<Rightarrow> (Element (\<nat> \<setminus> {0}) \<Rightarrow> X) \<Rightarrow> Element int_rep \<Rightarrow> X"
  unfolding int_rep_rec_def int_rep_def by discharge_types

lemma mem_int_repE [elim]:
  assumes "x \<in> int_rep"
  obtains (nonneg) n where "n \<in> \<nat>" "x = int_rep_nonneg n"
    | (neg) n where "n \<in> \<nat> \<setminus> {0}" "x = int_rep_neg n"
  using assms unfolding int_rep_def int_rep_nonneg_def int_rep_neg_def by blast

definition "int_rep_zero \<equiv> int_rep_nonneg 0"

lemma int_rep_zero_type [type]: "int_rep_zero : Element int_rep"
  unfolding int_rep_zero_def by discharge_types

definition "int_rep_one \<equiv> int_rep_nonneg 1"

lemma int_rep_one_type [type]: "int_rep_one : Element int_rep"
  unfolding int_rep_one_def by discharge_types


end
