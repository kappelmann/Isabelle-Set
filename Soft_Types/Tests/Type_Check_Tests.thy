section \<open>Type Check Tests\<close>
theory Type_Check_Tests
imports "Soft_Types.Soft_Types_HOL"
begin

declare [[trace_type_derivation]]

text \<open>Eta-normalization.\<close>

lemma "C A : T \<Longrightarrow> C (\<lambda>x. A x) : T"
  by (subst eta_contract_eq) discharge_types
  (*TODO: this should also work*)
  (* by discharge_types *)

lemma "C (\<lambda>x y z. D x y z) : T \<Longrightarrow> C D : T"
  by discharge_types

\<comment> \<open>Note Kevin: The following works if we use the following:
lemma [derive]: "c: C \<Longrightarrow> (\<lambda>a. c): A \<Rightarrow> C" sorry

However, I do not think it solves the task in the right way. Once we start with
typeclasses, we should think about making the type derivator more syntax
directed if the situation allows and only saturate (or use unification hints)
if needed.\<close>
lemma
  assumes [type]: "f: (A \<Rightarrow> C) \<Rightarrow> (B \<Rightarrow> C) \<Rightarrow> D \<Rightarrow> C"
  and [type]: "c : C" "d : D"
  shows "f (\<lambda> a. c) (\<lambda> a. c) d : C"
  by discharge_types

typedecl set
axiomatization Set :: "set type" and empty finite infinite :: "set \<Rightarrow> bool"
  where
  *: "empty x \<Longrightarrow> finite x" and
  **: "finite x \<Longrightarrow> \<not>(infinite x)"

lemma
  assumes [type]: "a : empty \<sqdot> Set"
  shows "blabla"
  ML_prf \<open>
    Soft_Type_Context.get_types @{context} [@{term a}];
    Soft_Type_Context.get_adjs @{context} [@{term a}];
  \<close>
oops


end
