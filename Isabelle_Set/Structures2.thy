section \<open>Structures\<close>

theory Structures2
imports Object2

begin

text \<open>Various basic structure definitions.\<close>


subsection \<open>Plus (additive binop) structures\<close>

definition [typeclass]:
  "Plus A \<equiv> type (\<lambda>P. P @@ plus \<in> A \<rightarrow> A \<rightarrow> A)"

ML \<open>Type_Classes.get_type_classes @{context}\<close>

lemma Plus_typeI:
  "P @@ plus : element (A \<rightarrow> A \<rightarrow> A) \<Longrightarrow> P : Plus A"
  unfolding Plus_def by unfold_types

lemma Plus_plus_type [derive]:
  "P: Plus A \<Longrightarrow> P @@ plus : element (A \<rightarrow> A \<rightarrow> A)"
  unfolding Plus_def by unfold_types

definition plus :: "set \<Rightarrow> set \<Rightarrow> set \<Rightarrow> set"
  where "plus P = (\<lambda>x y. P @@ plus `x `y)"

lemma plus_type [type]:
  "plus : Plus A \<Rightarrow> element A \<Rightarrow> element A \<Rightarrow> element A"
  unfolding plus_def by unfold_types

abbreviation plus_implicit :: "set \<Rightarrow> set \<Rightarrow> set" (infixl "+" 65)
  where "x + y \<equiv> plus \<implicit>P x y"


subsection \<open>Times (multiplicative binop) structures\<close>

definition [typeclass]:
  "Times A \<equiv> type (\<lambda>T. T @@ times \<in> A \<rightarrow> A \<rightarrow> A)"

lemma Times_typeI:
  "T @@ times : element (A \<rightarrow> A \<rightarrow> A) \<Longrightarrow> T : Times A"
  unfolding Times_def by unfold_types

lemma Times_plus_type [derive]:
  "T: Times A \<Longrightarrow> T @@ times : element (A \<rightarrow> A \<rightarrow> A)"
  unfolding Times_def by unfold_types

definition times :: "set \<Rightarrow> set \<Rightarrow> set \<Rightarrow> set"
  where "times T = (\<lambda>x y. T @@ times `x `y)"

lemma times_type [type]:
  "times : Times A \<Rightarrow> element A \<Rightarrow> element A \<Rightarrow> element A"
  unfolding times_def by unfold_types

abbreviation times_implicit :: "set \<Rightarrow> set \<Rightarrow> set" (infixl "\<cdot>" 65)
  where "x \<cdot> y \<equiv> times \<implicit>T x y"


subsection \<open>"Zero" and "One" structures\<close>

text \<open>Structures with distinguished elements.\<close>

definition [typeclass]:
  "Zero A = type (\<lambda>Z. Z @@ zero \<in> A)"

lemma Zero_typeI:
  "Z @@ zero : element A \<Longrightarrow> Z : Zero A"
  unfolding Zero_def by unfold_types

lemma Zero_zero_type [derive]:
  "Z: Zero A \<Longrightarrow> Z @@ zero : element A"
  unfolding Zero_def by unfold_types

definition zero :: "set \<Rightarrow> set"
  where "zero Z = Z @@ zero"

lemma zero_type [type]:
  "zero : Zero A \<Rightarrow> element A"
  unfolding zero_def by auto

abbreviation zero_implicit :: "set" ("0")
  where "0 \<equiv> zero \<implicit>Z"

definition [typeclass]:
  "One A = type (\<lambda>O. O @@ one \<in> A)"

lemma One_typeI:
  "O @@ one : element A \<Longrightarrow> O : One A"
  unfolding One_def by unfold_types

lemma One_one_type [derive]:
  "O: One A \<Longrightarrow> O @@ one : element A"
  unfolding One_def by unfold_types

definition one :: "set \<Rightarrow> set"
  where "one O = O @@ one"

lemma one_type [type]:
  "one : One A \<Rightarrow> element A"
  unfolding one_def by auto

abbreviation one_implicit :: "set" ("1")
  where "1 \<equiv> one \<implicit>O"


end
