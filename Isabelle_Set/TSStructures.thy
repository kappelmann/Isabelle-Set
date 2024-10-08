\<^marker>\<open>creator "Alexander Krauss"\<close>
\<^marker>\<open>creator "Josh Chen"\<close>
\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Typed Set-Structures\<close>
theory TSStructures
  imports
    SObjects
    TSFunctions_Base
begin

text \<open>Various basic structure definitions.\<close>

subsection \<open>"Zero" and "One" structures\<close>

text \<open>Structures with distinguished elements.\<close>

definition [typeclass]: "Zero A \<equiv> type (\<lambda>Z. Z@$zero \<Ztypecolon> A)"

lemma ZeroI: "Z@$zero \<Ztypecolon> A \<Longrightarrow> Z \<Ztypecolon> Zero A"
  unfolding Zero_def by unfold_types

lemma Zero_zero_type [derive]: "Z \<Ztypecolon> Zero A \<Longrightarrow> Z@$zero \<Ztypecolon> A"
  unfolding Zero_def by unfold_types

definition "zero Z \<equiv> Z@$zero"

lemma zero_type [type]: "zero \<Ztypecolon> Zero A \<Rightarrow> A"
  unfolding zero_def by auto

abbreviation zero_implicit :: "set"
  where "zero_implicit \<equiv> zero \<implicit>Z"

bundle isa_set_zero_implicit_syntax begin notation zero_implicit ("0") end

definition [typeclass]: "One A \<equiv> type (\<lambda>O. O@$one \<Ztypecolon> A)"

lemma OneI: "O@$one \<Ztypecolon> A \<Longrightarrow> O \<Ztypecolon> One A"
  unfolding One_def by unfold_types

lemma One_one_type [derive]: "O \<Ztypecolon> One A \<Longrightarrow> O@$one \<Ztypecolon> A"
  unfolding One_def by unfold_types

definition "one O \<equiv> O@$one"

lemma one_type [type]: "one \<Ztypecolon> One A \<Rightarrow> A"
  unfolding one_def by auto

abbreviation one_implicit :: "set"
  where "one_implicit \<equiv> one \<implicit>O"

bundle isa_set_one_implicit_syntax begin notation one_implicit ("1") end


subsection \<open>Additive structures\<close>

definition [typeclass]: "Add A \<equiv> type (\<lambda>P. P@$add \<Ztypecolon> A \<rightarrow> A \<rightarrow> A)"

\<comment>\<open>Show declared type classes\<close>
ML \<open>Type_Classes.get_type_classes @{context}\<close>

lemma AddI: "P@$add \<Ztypecolon> A \<rightarrow> A \<rightarrow> A \<Longrightarrow> P \<Ztypecolon> Add A"
  unfolding Add_def by unfold_types

lemma Add_add_type [derive]: "P \<Ztypecolon> Add A \<Longrightarrow> P@$add \<Ztypecolon> A \<rightarrow> A \<rightarrow> A"
  unfolding Add_def by unfold_types

definition add where "add P x y \<equiv> (P@$add)`x`y"

lemma add_type [type]: "add \<Ztypecolon> Add A \<Rightarrow> A \<Rightarrow> A \<Rightarrow> A"
  (*TODO: should not need an increase of the limit*)
  using [[type_derivation_depth=5]]
  unfolding add_def by discharge_types

abbreviation add_implicit :: "set \<Rightarrow> set \<Rightarrow> set"
  where "add_implicit x y \<equiv> add \<implicit>P x y"

bundle isa_set_add_implicit_syntax begin notation add_implicit  (infixl "+" 65) end


subsection \<open>Multiplicative structures\<close>

definition [typeclass]:
  "Mul A \<equiv> type (\<lambda>M. M@$mul \<Ztypecolon> A \<rightarrow> A \<rightarrow> A)"

lemma MulI: "M@$mul \<Ztypecolon> A \<rightarrow> A \<rightarrow> A \<Longrightarrow> M \<Ztypecolon> Mul A"
  unfolding Mul_def by unfold_types

lemma Mul_mul_type [derive]: "M \<Ztypecolon> Mul A \<Longrightarrow> M@$mul \<Ztypecolon> A \<rightarrow> A \<rightarrow> A"
  unfolding Mul_def by unfold_types

definition "mul M x y \<equiv> (M@$mul)`x`y"

lemma mul_type [type]: "mul \<Ztypecolon> Mul A \<Rightarrow> A \<Rightarrow> A \<Rightarrow> A"
  (*TODO: should not need an increase of the limit*)
  using [[type_derivation_depth=5]]
  unfolding mul_def by discharge_types

abbreviation mul_implicit :: "set \<Rightarrow> set \<Rightarrow> set"
  where "mul_implicit x y \<equiv> mul \<implicit>T x y"

bundle isa_set_mul_implicit_syntax begin notation mul_implicit  (infixl "*" 65) end


subsection \<open>Structures with additive inverses\<close>

definition [typeclass]: "Inv A \<equiv> type (\<lambda>I. I@$inv \<Ztypecolon> A \<rightarrow> A)"

lemma InvI: "I@$inv \<Ztypecolon> A \<rightarrow> A \<Longrightarrow> I \<Ztypecolon> Inv A"
  unfolding Inv_def by unfold_types

lemma Inv_inv_type [derive]: "I \<Ztypecolon> Inv A \<Longrightarrow> I@$inv \<Ztypecolon> A \<rightarrow> A"
  unfolding Inv_def by unfold_types

definition "inv I x = (I@$inv)`x"

lemma inv_type [type]: "inv \<Ztypecolon> Inv A \<Rightarrow> A \<Rightarrow> A"
  supply [[type_derivation_depth=5]] unfolding inv_def by discharge_types

abbreviation inv_implicit where "inv_implicit x \<equiv> inv \<implicit>I x"

bundle isa_set_inv_implicit_syntax begin notation inv_implicit  ("_\<inverse>" [1000]) end


end
