theory Derivation_Test
imports "../Soft_Types/Soft_Types_HOL"

begin

declare [[derive_debug]]

typedecl set
axiomatization set :: "set type" and empty finite infinite :: "set \<Rightarrow> bool" 
  where
  * [derive]: "empty x \<Longrightarrow> finite x" and
  ** [derive]: "finite x \<Longrightarrow> non-infinite x"

lemma
  assumes [type]: "a : empty \<sqdot> set"
  shows "blabla"

  ML_prf \<open>
    Soft_Type_Context.get_types @{context} [@{term a}];
    Soft_Type_Context.get_adjs @{context} [@{term a}];
    Derivation.derive_jdgmts @{context} [@{term a}];
  \<close>
oops

axiomatization pair subset_of where
  pair [derive]: "s : set \<Longrightarrow> t : set \<Longrightarrow> pair s t : non-empty \<sqdot> set" and
  subset [derive]: "x : set \<Longrightarrow> y : subset_of x \<Longrightarrow> y : set"

lemma
  assumes [type]: "s : set" "t : subset_of s"
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
  *** [derive]: "X : set \<Longrightarrow> Y : set \<Longrightarrow> R : subset_of (Prod X Y) \<Longrightarrow> Relation_like R"

abbreviation "Relation_of X Y \<equiv> subset_of (Prod X Y)"
abbreviation "PartFunc_of X Y \<equiv> Function_like \<sqdot> (Relation_of X Y)"
abbreviation "Function_of X Y \<equiv> (quasi_total X Y) \<sqdot> (PartFunc_of X Y)"

lemma
  assumes [type]: "X : set" "Y : set" "F : Function_of X Y"
  shows "Relation_like F"

  ML_prf \<open>
    Derivation.derive_jdgmts @{context} [@{term F}];
    Derivation.derive_jdgmts @{context} [@{term F}, @{term X}, @{term Y}];
  \<close>
oops


end
