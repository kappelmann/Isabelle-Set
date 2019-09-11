section \<open>Various structures\<close>

theory Structures
imports Object

begin

subsection \<open>Plus structures\<close>

object Plus "A :: set"
  is "\<lparr> (plus @plus). plus : element (A \<rightarrow> A \<rightarrow> A) \<rparr>"

lemma Plus_typeI: "str[@plus] : element (A \<rightarrow> A \<rightarrow> A) \<Longrightarrow> str : Plus A"
  unfolding Plus_typedef by squash_types

lemma Plus_PLUS_type [derive]: "str: Plus A \<Longrightarrow> str[@plus] : element (A \<rightarrow> A \<rightarrow> A)"
  unfolding Plus_typedef by squash_types


definition plus :: "set \<Rightarrow> set \<Rightarrow> set \<Rightarrow> set"
  where "plus p = (\<lambda>x y. p[@plus] ` x ` y)"

lemma plus_type [type]: "plus : (P : Plus A) \<Rightarrow> element A \<Rightarrow> element A \<Rightarrow> element A"
  unfolding plus_def by discharge_types

abbreviation plus_implicit :: "set \<Rightarrow> set \<Rightarrow> set" (infixl "+" 65)
  where "x + y \<equiv> plus \<implicit>M x y"


subsection \<open>Zero structures\<close>

object Zero "A :: set"
  is "\<lparr> (z @zero). z : element A \<rparr>"

lemma Zero_typeI: "str[@zero] : element A \<Longrightarrow> str : Zero A"
  unfolding Zero_typedef by auto

lemma Zero_ZERO_type [derive]: "str: Zero A \<Longrightarrow> str[@zero] : element A"
  unfolding Zero_typedef by squash_types

definition zero :: "set \<Rightarrow> set"
  where "zero Z = Z[@zero]"

lemma zero_type [type]: "zero : (Z : Zero A) \<Rightarrow> element A"
  unfolding zero_def by discharge_types

abbreviation zero_implicit :: "set" ("0")
  where "0 \<equiv> zero \<implicit>Z"


end
