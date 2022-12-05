\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Representation of Integers\<close>
theory Integers_Rep_Base
imports
  HOTG.Set_Difference
  Nat
  TCoproduct
begin

unbundle no_HOL_groups_syntax

text \<open>We construct the integers as a pair of a non-negative and a negative part.
By using the set extension principle, we will ensure that \<open>\<nat> \<subseteq> \<int>\<close>.\<close>

(*TOOD: define as a quotient of \<nat> pairs instead?*)
definition "int_rep \<equiv> \<nat> \<Coprod> (\<nat> \<setminus> {0})"

definition [typedef]: "Int_Rep = Nat \<Coprod> Element (\<nat> \<setminus> {0})"

\<comment> \<open>Some type derivation setup\<close>
lemma mem_int_rep_iff_Int_Rep: "x \<in> int_rep \<longleftrightarrow> x : Int_Rep"
  unfolding int_rep_def Int_Rep_def by (fact mem_coprod_iff_Coprod)

soft_type_translation
  "x \<in> int_rep" \<rightleftharpoons> "x : Int_Rep"
  by (auto iff: mem_int_rep_iff_Int_Rep)

lemma [type]: "succ : Element \<nat> \<Rightarrow> Element (\<nat> \<setminus> {0})"
  by unfold_types auto


text \<open>Constructors, Recursor and Eliminator\<close>

definition "Int_Rep_nonneg \<equiv> inl"

definition "Int_Rep_neg \<equiv> inr"

lemma Int_Rep_nonneg_type [type]: "Int_Rep_nonneg : Nat \<Rightarrow> Int_Rep"
  unfolding Int_Rep_nonneg_def Int_Rep_def by discharge_types

lemma Int_Rep_neg_type [type]:
  "Int_Rep_neg : Element (\<nat> \<setminus> {0}) \<Rightarrow> Int_Rep"
  unfolding Int_Rep_neg_def Int_Rep_def by discharge_types

lemma
  Int_Rep_nonneg_eq_iff [iff]: "Int_Rep_nonneg x = Int_Rep_nonneg y \<longleftrightarrow> x = y" and
  Int_Rep_neg_eq_iff [iff]: "Int_Rep_neg x = Int_Rep_neg y \<longleftrightarrow> x = y" and
  Int_Rep_nonneg_ne_neg [iff]: "Int_Rep_nonneg x \<noteq> Int_Rep_neg y" and
  Int_Rep_neg_ne_nonneg [iff]: "Int_Rep_neg x \<noteq> Int_Rep_nonneg y"
  unfolding Int_Rep_nonneg_def Int_Rep_neg_def by auto

definition "Int_Rep_rec \<equiv> coprod_rec"

lemma
  shows Int_Rep_rec_nonneg_eq [simp]:
    "Int_Rep_rec f_nneg f_neg (Int_Rep_nonneg n) = f_nneg n"
  and Int_Rep_rec_neg_eq [simp]: "Int_Rep_rec f_nneg f_neg (Int_Rep_neg n) = f_neg n"
  unfolding Int_Rep_rec_def Int_Rep_nonneg_def Int_Rep_neg_def by simp_all

lemma Int_Rep_rec_type [type]:
  "Int_Rep_rec : (Element \<nat> \<Rightarrow> X) \<Rightarrow> (Element (\<nat> \<setminus> {0}) \<Rightarrow> X) \<Rightarrow> Int_Rep \<Rightarrow> X"
  unfolding Int_Rep_rec_def Int_Rep_def by discharge_types

lemma Int_RepE [elim]:
  assumes "x : Int_Rep"
  obtains (nonneg) n where "n \<in> \<nat>" "x = Int_Rep_nonneg n"
    | (neg) n where "n \<in> \<nat> \<setminus> {0}" "x = Int_Rep_neg n"
  using assms unfolding Int_Rep_def Int_Rep_nonneg_def Int_Rep_neg_def
  by (auto iff: mem_iff_Element)

definition "Int_Rep_zero \<equiv> Int_Rep_nonneg 0"

lemma Int_Rep_zero_type [type]: "Int_Rep_zero : Int_Rep"
  unfolding Int_Rep_zero_def by discharge_types

definition "Int_Rep_one \<equiv> Int_Rep_nonneg 1"

lemma Int_Rep_one_type [type]: "Int_Rep_one : Int_Rep"
  unfolding Int_Rep_one_def by discharge_types


end
