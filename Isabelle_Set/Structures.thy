section \<open>Various structures\<close>

text \<open>Notation for various structure operations.\<close>

theory Structures
imports Object

begin

subsection \<open>Structures with binary operation\<close>

object binop_equipped "name::set" "A::set"
  is "\<lparr> (name op). op : element (A \<rightarrow> A \<rightarrow> A) \<rparr>"

(* Josh: Got to come back to this after I implement object unions *)


subsection \<open>Plus (additive binop) structures\<close>

object Plus "A::set" is "\<lparr> (@plus plus). plus : element (A \<rightarrow> A \<rightarrow> A) \<rparr>"

lemma Plus_typeI:
  "struct[@plus] : element (A \<rightarrow> A \<rightarrow> A) \<Longrightarrow> struct : Plus A"
  unfolding Plus_typedef by squash_types

lemma Plus_plus_type [derive]:
  "struct: Plus A \<Longrightarrow> struct[@plus] : element (A \<rightarrow> A \<rightarrow> A)"
  unfolding Plus_typedef by squash_types

definition plus :: "set \<Rightarrow> set \<Rightarrow> set \<Rightarrow> set"
  where "plus p = (\<lambda>x y. p[@plus]`x`y)"

lemma plus_type [type]: "plus : (P : Plus A) \<Rightarrow> element A \<Rightarrow> element A \<Rightarrow> element A"
  unfolding plus_def by discharge_types

abbreviation plus_implicit :: "set \<Rightarrow> set \<Rightarrow> set" (infixl "+" 65)
  where "x + y \<equiv> plus \<implicit>M x y"

definition additive :: \<open>set \<Rightarrow> set \<Rightarrow> bool\<close>
  where "additive A struct \<equiv> struct : Plus A"


subsection \<open>Times (multiplicative binop) structures\<close>

object Times "A::set" is "\<lparr> (@times times). times : element (A \<rightarrow> A \<rightarrow> A) \<rparr>"

lemma Times_typeI:
  "struct[@times] : element (A \<rightarrow> A \<rightarrow> A) \<Longrightarrow> struct : Times A"
  unfolding Times_typedef by squash_types

lemma Times_times_type [derive]:
  "struct: Times A \<Longrightarrow> struct[@times] : element (A \<rightarrow> A \<rightarrow> A)"
  unfolding Times_typedef by squash_types

definition times :: "set \<Rightarrow> set \<Rightarrow> set \<Rightarrow> set"
  where "times p = (\<lambda>x y. p[@times]`x`y)"

lemma times_type [type]: "times : (P : Times A) \<Rightarrow> element A \<Rightarrow> element A \<Rightarrow> element A"
  unfolding times_def by discharge_types

abbreviation times_implicit :: "set \<Rightarrow> set \<Rightarrow> set" (infixl "\<cdot>" 65)
  where "x \<cdot> y \<equiv> times \<implicit>M x y"

definition multiplicative :: \<open>set \<Rightarrow> set \<Rightarrow> bool\<close>
  where "multiplicative A struct \<equiv> struct : Times A"


subsection \<open>Zero structures\<close>

object Zero "A :: set"
  is "\<lparr> (@zero z). z : element A \<rparr>"

lemma Zero_typeI: "struct[@zero] : element A \<Longrightarrow> struct : Zero A"
  unfolding Zero_typedef by auto

lemma Zero_zero_type [derive]: "struct: Zero A \<Longrightarrow> struct[@zero] : element A"
  unfolding Zero_typedef by squash_types

definition zero :: "set \<Rightarrow> set"
  where "zero Z = Z[@zero]"

lemma zero_type [type]: "zero : (Z : Zero A) \<Rightarrow> element A"
  unfolding zero_def by discharge_types

abbreviation zero_implicit :: "set" ("0")
  where "0 \<equiv> zero \<implicit>Z"


end
