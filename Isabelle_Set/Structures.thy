section \<open>Various structures\<close>

text \<open>Collection of various structure definitions.\<close>

theory Structures
imports Object

begin

subsection \<open>Various basic structure templates\<close>

text \<open>Structures with a distinguished element.\<close>

object Pointed "name::set" "A::set"
  is "\<lparr> (base name). base : element A \<rparr>"

text \<open>Structures with binary operation.\<close>

object Binop_Equipped "name::set" "A::set"
  is "\<lparr> (op name). op : element (A \<rightarrow> A \<rightarrow> A) \<rparr>"


subsection \<open>Plus (additive binop) structures\<close>

definition Plus :: "set \<Rightarrow> set type"
  where [typedef]: "Plus A \<equiv> Binop_Equipped @plus A"

lemma Plus_typeI:
  "struct[@plus] : element (A \<rightarrow> A \<rightarrow> A) \<Longrightarrow> struct : Plus A"
  unfolding Plus_def Binop_Equipped_def by unfold_types (simp add: object_simps)

lemma Plus_plus_type [derive]:
  "struct: Plus A \<Longrightarrow> struct[@plus] : element (A \<rightarrow> A \<rightarrow> A)"
  unfolding Plus_def Binop_Equipped_def by unfold_types (simp add: object_simps)

definition plus :: "set \<Rightarrow> set \<Rightarrow> set \<Rightarrow> set"
  where "plus p = (\<lambda>x y. p[@plus] `x `y)"

lemma plus_type [type]: "plus : (P : Plus A) \<Rightarrow> element A \<Rightarrow> element A \<Rightarrow> element A"
  unfolding plus_def oops

abbreviation plus_implicit :: "set \<Rightarrow> set \<Rightarrow> set" (infixl "+" 65)
  where "x + y \<equiv> plus \<implicit>M x y"


subsection \<open>Times (multiplicative binop) structures\<close>

definition Times :: "set \<Rightarrow> set type"
  where Times_def: "Times A \<equiv> Binop_Equipped @times A"

lemma Times_typeI:
  "struct[@times] : element (A \<rightarrow> A \<rightarrow> A) \<Longrightarrow> struct : Times A"
  unfolding Times_def Binop_Equipped_def by unfold_types (simp add: object_simps)

lemma Times_times_type [derive]:
  "struct: Times A \<Longrightarrow> struct[@times] : element (A \<rightarrow> A \<rightarrow> A)"
  unfolding Times_def Binop_Equipped_def by unfold_types (simp add: object_simps)

definition times :: "set \<Rightarrow> set \<Rightarrow> set \<Rightarrow> set"
  where "times p = (\<lambda>x y. p[@times] `x `y)"

lemma times_type [type]: "times : (P : Times A) \<Rightarrow> element A \<Rightarrow> element A \<Rightarrow> element A"
  unfolding times_def oops

abbreviation times_implicit :: "set \<Rightarrow> set \<Rightarrow> set" (infixl "\<cdot>" 65)
  where "x \<cdot> y \<equiv> times \<implicit>M x y"


subsection \<open>"Zero" and "one" structures\<close>

text \<open>Just structures with distinguished elements of their carriers.\<close>

definition Zero :: \<open>set \<Rightarrow> set type\<close>
  where "Zero A = Pointed @zero A"

lemma Zero_typeI: "struct[@zero] : element A \<Longrightarrow> struct : Zero A"
  unfolding Zero_def Pointed_def by unfold_types (simp add: object_simps)

lemma Zero_zero_type [derive]: "struct: Zero A \<Longrightarrow> struct[@zero] : element A"
  unfolding Zero_def Pointed_def by unfold_types (simp add: object_simps)

definition zero :: "set \<Rightarrow> set"
  where "zero struct = struct[@zero]"

lemma zero_type [type]: "zero : (struct : Zero A) \<Rightarrow> element A"
  unfolding zero_def by discharge_types

abbreviation zero_implicit :: "set" ("0")
  where "0 \<equiv> zero \<implicit>struct"


definition One :: \<open>set \<Rightarrow> set type\<close>
  where One_def: "One A = Pointed @one A"

lemma One_typeI: "struct[@one] : element A \<Longrightarrow> struct : One A"
  unfolding One_def Pointed_def by unfold_types (simp add: object_simps)

lemma One_one_type [derive]: "struct: One A \<Longrightarrow> struct[@one] : element A"
  unfolding One_def Pointed_def by unfold_types (simp add: object_simps)

definition one :: "set \<Rightarrow> set"
  where "one struct = struct[@one]"

lemma one_type [type]: "one : (struct : One A) \<Rightarrow> element A"
  unfolding one_def by discharge_types

abbreviation one_implicit :: "set" ("1")
  where "1 \<equiv> one \<implicit>struct"


end
