section \<open>Structures\<close>

theory Structures
imports Object

begin

text \<open>Various basic structure definitions.\<close>


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

lemma assumes "Z : Zero A" "Ext : Object A' B"
  and "@zero \<in> object_fields Ext \<Longrightarrow> Z @@ zero = Ext @@ zero"
  shows "extend Z Ext : Zero A"
  by (rule Zero_typeI,
    rule object_extend_preserve[where s="@zero", OF _ assms(2)])
  (auto simp: assms(3))
\<comment> \<open>Note Kevin: Problem: what are the universes A and B when also requiring that
  "Zero A : Object A B"?\<close>

definition zero :: "set \<Rightarrow> set"
  where "zero Z = Z @@ zero"

lemma zero_type [type]:
  "zero : Zero A \<Rightarrow> element A"
  unfolding zero_def by auto

abbreviation zero_implicit :: "set"
  where "zero_implicit \<equiv> zero \<implicit>Z"

bundle notation_zero_implicit begin notation zero_implicit ("0") end
bundle no_notation_zero_implicit begin no_notation zero_implicit ("0") end

unbundle notation_zero_implicit

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

bundle notation_one_implicit begin notation one_implicit ("1") end
bundle no_notation_one_implicit begin no_notation one_implicit ("1") end

unbundle notation_one_implicit


subsection \<open>Additive (binop) structures\<close>

definition [typeclass]:
  "Add A \<equiv> type (\<lambda>P. P @@ add \<in> A \<rightarrow> A \<rightarrow> A)"

ML \<open>Type_Classes.get_type_classes @{context}\<close>

lemma Add_typeI:
  "P @@ add : element (A \<rightarrow> A \<rightarrow> A) \<Longrightarrow> P : Add A"
  unfolding Add_def by unfold_types

lemma Add_add_type [derive]:
  "P: Add A \<Longrightarrow> P @@ add : element (A \<rightarrow> A \<rightarrow> A)"
  unfolding Add_def by unfold_types

definition add :: "set \<Rightarrow> set \<Rightarrow> set \<Rightarrow> set"
  where "add P = (\<lambda>x y. P @@ add `x `y)"

lemma add_type [type]:
  "add : Add A \<Rightarrow> element A \<Rightarrow> element A \<Rightarrow> element A"
  unfolding add_def by unfold_types

abbreviation add_implicit :: "set \<Rightarrow> set \<Rightarrow> set"
  where "add_implicit x y \<equiv> add \<implicit>P x y"

bundle notation_add_implicit
  begin notation add_implicit  (infixl "+" 65) end

bundle no_notation_add_implicit
  begin no_notation add_implicit  (infixl "+" 65) end

unbundle notation_add_implicit


subsection \<open>Multiplicative (binop) structures\<close>

definition [typeclass]:
  "Mul A \<equiv> type (\<lambda>T. T @@ mul \<in> A \<rightarrow> A \<rightarrow> A)"

lemma Mul_typeI:
  "T @@ mul : element (A \<rightarrow> A \<rightarrow> A) \<Longrightarrow> T : Mul A"
  unfolding Mul_def by unfold_types

lemma Mul_mul_type [derive]:
  "T: Mul A \<Longrightarrow> T @@ mul : element (A \<rightarrow> A \<rightarrow> A)"
  unfolding Mul_def by unfold_types

definition mul :: "set \<Rightarrow> set \<Rightarrow> set \<Rightarrow> set"
  where "mul T = (\<lambda>x y. T @@ mul `x `y)"

lemma mul_type [type]:
  "mul : Mul A \<Rightarrow> element A \<Rightarrow> element A \<Rightarrow> element A"
  unfolding mul_def by unfold_types

abbreviation mul_implicit :: "set \<Rightarrow> set \<Rightarrow> set" (infixl "\<cdot>" 65)
  where "x \<cdot> y \<equiv> mul \<implicit>T x y"

bundle notation_mul_implicit
  begin notation mul_implicit  (infixl "\<cdot>" 65) end

bundle no_notation_mul_implicit
  begin no_notation mul_implicit  (infixl "\<cdot>" 65) end


end
