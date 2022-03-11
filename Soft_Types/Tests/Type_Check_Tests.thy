section \<open>Type Check Tests\<close>
theory Type_Check_Tests
  imports "Soft_Types.Soft_Types_HOL"
begin

declare [[trace_type_derivation, type_derivation_depth=5]]

text \<open>Eta-normalization.\<close>

lemma "C A : T \<Longrightarrow> C (\<lambda>x. A x) : T"
  by (subst eta_contract_eq) discharge_types
  (*TODO: this should also work*)
  (* by discharge_types *)

lemma "C (\<lambda>x y z. D x y z) : T \<Longrightarrow> C D : T"
  by discharge_types

text \<open>Binders\<close>

typedecl ('a, 'b) pair

consts pair_rec :: "('a, 'b) pair \<Rightarrow> ('a \<Rightarrow> 'c) \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> 'c"
consts Pair :: "'a type \<Rightarrow> 'b type \<Rightarrow> ('a, 'b) pair type"

lemma [type]: "pair_rec : Pair A B \<Rightarrow> (A \<Rightarrow> C) \<Rightarrow> (B \<Rightarrow> C) \<Rightarrow> C"
  sorry

(*should be backward derive but currently isn't allowed*)
lemma [derive]:
  assumes "p : Pair A B"
  and "fl : A \<Rightarrow> C"
  and "fr : B \<Rightarrow> C"
  shows "pair_rec p fl fr : C"
  by discharge_types

lemma
  assumes "p : Pair A B"
  and "c : A \<Rightarrow> Bool \<Rightarrow> C"
  and "d : B \<Rightarrow> Bool \<Rightarrow> C"
  shows "pair_rec p (\<lambda>x. c x True) (\<lambda>x. d x False) : C"
  (*works with backward derive rule above*)
  (* by discharge_types *)
  oops

(*should be backward derive with low priority but not allowed currently*)
lemma app_type [derive]:
  assumes "t : A \<Rightarrow> C"
  and "u : A"
  shows "t u : C"
  by discharge_types

lemma lambda_type [backward_derive]:
  assumes "\<And>x. x : A \<Longrightarrow> t x : C"
  shows "(\<lambda>x. t x) : A \<Rightarrow> C"
  using assms by unfold_types

lemma
  assumes [type]: "f : (A \<Rightarrow> C) \<Rightarrow> C"
  and [type]: "c : A \<Rightarrow> Bool \<Rightarrow> C"
  shows "f (\<lambda> a. c a True) : C"
  (* by discharge_types *)
  oops


end
