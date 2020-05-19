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
  "Z @@ zero: Element A \<Longrightarrow> Z: Zero A"
  unfolding Zero_def by unfold_types

lemma Zero_zero_type [derive]:
  "Z: Zero A \<Longrightarrow> Z @@ zero: Element A"
  unfolding Zero_def by unfold_types

definition zero :: "set \<Rightarrow> set"
  where "zero Z = Z @@ zero"

lemma zero_type [type]:
  "zero: Zero A \<Rightarrow> Element A"
  unfolding zero_def by auto

abbreviation zero_implicit :: "set"
  where "zero_implicit \<equiv> zero \<implicit>Z"

bundle notation_zero_implicit begin notation zero_implicit ("0") end
bundle no_notation_zero_implicit begin no_notation zero_implicit ("0") end

unbundle notation_zero_implicit

definition [typeclass]:
  "One A = type (\<lambda>O. O @@ one \<in> A)"

lemma One_typeI:
  "O @@ one: Element A \<Longrightarrow> O: One A"
  unfolding One_def by unfold_types

lemma One_one_type [derive]:
  "O: One A \<Longrightarrow> O @@ one: Element A"
  unfolding One_def by unfold_types

definition one :: "set \<Rightarrow> set"
  where "one O = O @@ one"

lemma one_type [type]:
  "one: One A \<Rightarrow> Element A"
  unfolding one_def by auto

abbreviation one_implicit :: "set" ("1")
  where "1 \<equiv> one \<implicit>O"

bundle notation_one_implicit begin notation one_implicit ("1") end
bundle no_notation_one_implicit begin no_notation one_implicit ("1") end

unbundle notation_one_implicit


subsection \<open>Additive structures\<close>

definition [typeclass]:
  "Add A \<equiv> type (\<lambda>P. P @@ add: A \<rightarrow> A \<rightarrow> A)"

\<comment> \<open>Show declared type classes\<close>
ML \<open>Type_Classes.get_type_classes @{context}\<close>

lemma Add_typeI:
  "P @@ add: A \<rightarrow> A \<rightarrow> A \<Longrightarrow> P: Add A"
  unfolding Add_def by unfold_types

lemma Add_add_type [derive]:
  "P: Add A \<Longrightarrow> P @@ add: A \<rightarrow> A \<rightarrow> A"
  unfolding Add_def by unfold_types

definition add :: "set \<Rightarrow> set \<Rightarrow> set \<Rightarrow> set"
  where "add P = (\<lambda>x y. P @@ add `x `y)"

lemma add_type [type]:
  "add: Add A \<Rightarrow> Element A \<Rightarrow> Element A \<Rightarrow> Element A"
  unfolding add_def by discharge_types

abbreviation add_implicit :: "set \<Rightarrow> set \<Rightarrow> set"
  where "add_implicit x y \<equiv> add \<implicit>P x y"

bundle notation_add_implicit
  begin notation add_implicit  (infixl "+" 65) end

bundle no_notation_add_implicit
  begin no_notation add_implicit  (infixl "+" 65) end

unbundle notation_add_implicit


subsection \<open>Multiplicative structures\<close>

definition [typeclass]:
  "Mul A \<equiv> type (\<lambda>T. T @@ mul: A \<rightarrow> A \<rightarrow> A)"

lemma Mul_typeI:
  "T @@ mul: A \<rightarrow> A \<rightarrow> A \<Longrightarrow> T: Mul A"
  unfolding Mul_def by unfold_types

lemma Mul_mul_type [derive]:
  "T: Mul A \<Longrightarrow> T @@ mul: A \<rightarrow> A \<rightarrow> A"
  unfolding Mul_def by unfold_types

definition mul :: "set \<Rightarrow> set \<Rightarrow> set \<Rightarrow> set"
  where "mul T = (\<lambda>x y. T @@ mul `x `y)"

lemma mul_type [type]:
  "mul: Mul A \<Rightarrow> Element A \<Rightarrow> Element A \<Rightarrow> Element A"
  unfolding mul_def by discharge_types

abbreviation mul_implicit :: "set \<Rightarrow> set \<Rightarrow> set"
  where "mul_implicit x y \<equiv> mul \<implicit>T x y"

bundle notation_mul_implicit
  begin notation mul_implicit  (infixl "\<cdot>" 65) end

bundle no_notation_mul_implicit
  begin no_notation mul_implicit  (infixl "\<cdot>" 65) end


subsection \<open>Structures with additive inverses\<close>

definition [typeclass]:
  "Inv A \<equiv> type (\<lambda>I. I @@ inv: A \<rightarrow> A)"

lemma Inv_typeI:
  "I @@ inv: A \<rightarrow> A \<Longrightarrow> I: Inv A"
  unfolding Inv_def by unfold_types

lemma Inv_inv_type [derive]:
  "I: Inv A \<Longrightarrow> I @@ inv: A \<rightarrow> A"
  unfolding Inv_def by unfold_types

definition "inv I x = I @@ inv `x"

lemma inv_type [type]:
  "inv: Inv A \<Rightarrow> Element A \<Rightarrow> Element A"
  unfolding inv_def by discharge_types

abbreviation inv_implicit where "inv_implicit x \<equiv> inv \<implicit>I x"

bundle notation_inv_implicit
  begin notation inv_implicit  ("-_" [1000]) end

bundle no_notation_inv_implicit
  begin no_notation inv_implicit  ("-_" [1000]) end


end
