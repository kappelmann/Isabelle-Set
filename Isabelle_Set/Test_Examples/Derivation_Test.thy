theory Derivation_Test
imports "../Isabelle_Set"

begin

declare [[trace_type_derivation]]

\<comment> \<open>Note Kevin: The following works if we use the following:
lemma [derive]: "c: C \<Longrightarrow> (\<lambda>a. c): A \<Rightarrow> C" sorry

However, I do not think it solves the task in the right way. Once we start with
typeclasses, we should think about making the type derivator more syntax
directed if the situation allows and only saturate (or use unification hints)
if needed.\<close>
lemma assumes [type]: "f: (A \<Rightarrow> C) \<Rightarrow> (B \<Rightarrow> C) \<Rightarrow> D \<Rightarrow> C"
  and [type]: "c: C" "d: D"
  shows "f (\<lambda> a. c) (\<lambda> a. c) d: C"
  apply discharge_types
  oops

typedecl set
axiomatization set :: "set type" and empty finite infinite :: "set \<Rightarrow> bool" 
  where
  * [derive]: "empty x \<Longrightarrow> finite x" and
  ** [derive]: "finite x \<Longrightarrow> non-infinite x"

lemma
  assumes [type]: "a: empty \<sqdot> set"
  shows "blabla"

  ML_prf \<open>
    Soft_Type_Context.get_types @{context} [@{term a}];
    Soft_Type_Context.get_adjs @{context} [@{term a}];
    Derivation.derive_jdgmts @{context} [@{term a}];
  \<close>
oops

axiomatization pair subset_of where
  pair [derive]: "s: set \<Longrightarrow> t: set \<Longrightarrow> pair s t: non-empty \<sqdot> set" and
  subset [derive]: "x: set \<Longrightarrow> y: subset_of x \<Longrightarrow> y: set"

lemma
  assumes [type]: "s: set" "t: subset_of s"
  shows "non-empty (pair s t)"

  thm derivation_rules

  ML_prf \<open>
    Derivation.derive_jdgmts @{context} [@{term "pair s t"}, @{term s}, @{term t}]
  \<close>
oops

axiomatization
  Prod :: \<open>set \<Rightarrow> set \<Rightarrow> set\<close> and
  Function_like Relation_like :: \<open>set \<Rightarrow> bool\<close> and
  quasi_total :: \<open>set \<Rightarrow> set \<Rightarrow> set \<Rightarrow> bool\<close>
where
  *** [derive]: "X: set \<Longrightarrow> Y: set \<Longrightarrow> R: subset_of (Prod X Y) \<Longrightarrow> Relation_like R"

abbreviation "Relation_of X Y \<equiv> subset_of (Prod X Y)"
abbreviation "PartFunc_of X Y \<equiv> Function_like \<sqdot> (Relation_of X Y)"
abbreviation "Function_of X Y \<equiv> (quasi_total X Y) \<sqdot> (PartFunc_of X Y)"

lemma
  assumes [type]: "X: set" "Y: set" "F: Function_of X Y"
  shows "Relation_like F"

  ML_prf \<open>
    Derivation.derive_jdgmts @{context} [@{term F}];
    Derivation.derive_jdgmts @{context} [@{term F}, @{term X}, @{term Y}];
  \<close>
oops


end
