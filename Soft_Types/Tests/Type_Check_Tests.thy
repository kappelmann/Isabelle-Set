section \<open>Type Check Tests\<close>
theory Type_Check_Tests
  imports "Soft_Types.Soft_Types_HOL"
begin

declare [[trace_type_derivation, type_derivation_depth=5]]

text \<open>Eta-normalization.\<close>

lemma "C A \<Ztypecolon> T \<Longrightarrow> C (\<lambda>x. A x) \<Ztypecolon> T"
  by (subst eta_contract_eq) discharge_types
  (*TODO: this should also work*)
  (* by discharge_types *)

lemma "C (\<lambda>x y z. D x y z) \<Ztypecolon> T \<Longrightarrow> C D \<Ztypecolon> T"
  by discharge_types

text \<open>Binders\<close>

typedecl ('a, 'b) pair

consts pair_rec :: "('a, 'b) pair \<Rightarrow> ('a \<Rightarrow> 'c) \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> 'c"
consts Pair :: "'a type \<Rightarrow> 'b type \<Rightarrow> ('a, 'b) pair type"

lemma [type]: "pair_rec \<Ztypecolon> Pair A B \<Rightarrow> (A \<Rightarrow> C) \<Rightarrow> (B \<Rightarrow> C) \<Rightarrow> C"
  sorry

(*should be backward derive but currently isn't allowed*)
lemma [derive]:
  assumes "p \<Ztypecolon> Pair A B"
  and "fl \<Ztypecolon> A \<Rightarrow> C"
  and "fr \<Ztypecolon> B \<Rightarrow> C"
  shows "pair_rec p fl fr \<Ztypecolon> C"
  by discharge_types

lemma
  assumes "p \<Ztypecolon> Pair A B"
  and "c \<Ztypecolon> A \<Rightarrow> Bool \<Rightarrow> C"
  and "d \<Ztypecolon> B \<Rightarrow> Bool \<Rightarrow> C"
  shows "pair_rec p (\<lambda>x. c x True) (\<lambda>x. d x False) \<Ztypecolon> C"
  (*works with backward derive rule above*)
  (* by discharge_types *)
  oops

(*should be backward derive with low priority but not allowed currently*)
lemma app_type [derive]:
  assumes "t \<Ztypecolon> A \<Rightarrow> C"
  and "u \<Ztypecolon> A"
  shows "t u \<Ztypecolon> C"
  by discharge_types

lemma lambda_type [backward_derive]:
  assumes "\<And>x. x \<Ztypecolon> A \<Longrightarrow> t x \<Ztypecolon> C"
  shows "(\<lambda>x. t x) \<Ztypecolon> A \<Rightarrow> C"
  using assms by unfold_types

lemma
  assumes [type]: "f \<Ztypecolon> (A \<Rightarrow> C) \<Rightarrow> C"
  and [type]: "c \<Ztypecolon> A \<Rightarrow> Bool \<Rightarrow> C"
  shows "f (\<lambda> a. c a True) \<Ztypecolon> C"
  (* by discharge_types *)
  oops


end
