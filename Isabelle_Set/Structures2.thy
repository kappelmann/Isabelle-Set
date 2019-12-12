section \<open>Structures\<close>

theory Structures2
imports Object2

begin

text \<open>Various basic structure definitions.\<close>


subsection \<open>Plus (additive binop) structures\<close>

definition [typedef]:
  "Plus A \<equiv> type (\<lambda>struct. struct @@ plus \<in> A \<rightarrow> A \<rightarrow> A)"

lemma Plus_typeI [intro]:
  "struct @@ plus : element (A \<rightarrow> A \<rightarrow> A) \<Longrightarrow> struct : Plus A"
  unfolding Plus_def by unfold_types

lemma Plus_plus_type [derive]:
  "struct: Plus A \<Longrightarrow> struct @@ plus : element (A \<rightarrow> A \<rightarrow> A)"
  unfolding Plus_def by unfold_types

definition plus :: "set \<Rightarrow> set \<Rightarrow> set \<Rightarrow> set"
  where "plus struct = (\<lambda>x y. struct @@ plus `x `y)"

lemma plus_type [type]:
  "plus : Plus A \<Rightarrow> element A \<Rightarrow> element A \<Rightarrow> element A"
  unfolding plus_def by unfold_types (auto intro: FunctionE)

abbreviation plus_implicit :: "set \<Rightarrow> set \<Rightarrow> set" (infixl "+" 65)
  where "x + y \<equiv> plus \<implicit>struct x y"


subsection \<open>Times (multiplicative binop) structures\<close>

definition [typedef]:
  "Times A \<equiv> type (\<lambda>struct. struct @@ times \<in> A \<rightarrow> A \<rightarrow> A)"

lemma Times_typeI [intro]:
  "struct @@ times : element (A \<rightarrow> A \<rightarrow> A) \<Longrightarrow> struct : Times A"
  unfolding Times_def by unfold_types

lemma Times_plus_type [derive]:
  "struct: Times A \<Longrightarrow> struct @@ times : element (A \<rightarrow> A \<rightarrow> A)"
  unfolding Times_def by unfold_types

definition times :: "set \<Rightarrow> set \<Rightarrow> set \<Rightarrow> set"
  where "times struct = (\<lambda>x y. struct @@ times `x `y)"

lemma times_type [type]:
  "times : Times A \<Rightarrow> element A \<Rightarrow> element A \<Rightarrow> element A"
  unfolding times_def by unfold_types (auto intro: FunctionE)

abbreviation times_implicit :: "set \<Rightarrow> set \<Rightarrow> set" (infixl "\<cdot>" 65)
  where "x \<cdot> y \<equiv> times \<implicit>struct x y"


subsection \<open>"Zero" and "One" structures\<close>

text \<open>Structures with distinguished elements.\<close>

definition [typedef]:
  "Zero A = type (\<lambda>struct. struct @@ zero \<in> A)"

lemma Zero_typeI [intro]:
  "struct @@ zero : element A \<Longrightarrow> struct : Zero A"
  unfolding Zero_def by unfold_types

lemma Zero_zero_type [derive]:
  "struct: Zero A \<Longrightarrow> struct @@ zero : element A"
  unfolding Zero_def by unfold_types

definition zero :: "set \<Rightarrow> set"
  where "zero struct = struct @@ zero"

lemma zero_type [type]:
  "zero : Zero A \<Rightarrow> element A"
  unfolding zero_def by auto

abbreviation zero_implicit :: "set" ("0")
  where "0 \<equiv> zero \<implicit>struct"

definition [typedef]:
  "One A = type (\<lambda>struct. struct @@ one \<in> A)"

lemma One_typeI [intro]:
  "struct @@ one : element A \<Longrightarrow> struct : One A"
  unfolding One_def by unfold_types

lemma One_one_type [derive]:
  "struct: One A \<Longrightarrow> struct @@ one : element A"
  unfolding One_def by unfold_types

definition one :: "set \<Rightarrow> set"
  where "one struct = struct @@ one"

lemma one_type [type]:
  "one : One A \<Rightarrow> element A"
  unfolding one_def by auto

abbreviation one_implicit :: "set" ("1")
  where "1 \<equiv> one \<implicit>struct"


end
