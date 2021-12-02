section \<open>Structures\<close>
theory Structures
imports Objects
begin
text \<open>Various basic structure definitions.\<close>


subsection \<open>"Zero" and "One" structures\<close>

text \<open>Structures with distinguished elements.\<close>

definition [typeclass]: "Zero A \<equiv> type (\<lambda>Z. Z @@ zero \<in> A)"

lemma ZeroI: "Z @@ zero : Element A \<Longrightarrow> Z : Zero A"
  unfolding Zero_def by unfold_types

lemma Zero_zero_type [derive]: "Z : Zero A \<Longrightarrow> Z @@ zero : Element A"
  unfolding Zero_def by unfold_types

definition "zero Z \<equiv> Z @@ zero"

lemma zero_type [type]: "zero : Zero A \<Rightarrow> Element A"
  unfolding zero_def by auto

abbreviation zero_implicit :: "set"
  where "zero_implicit \<equiv> zero \<implicit>Z"

bundle isa_set_zero_implicit_syntax begin notation zero_implicit ("0") end
bundle no_isa_set_zero_implicit_syntax begin no_notation zero_implicit ("0") end

unbundle isa_set_zero_implicit_syntax

definition [typeclass]: "One A \<equiv> type (\<lambda>O. O @@ one \<in> A)"

lemma OneI: "O @@ one : Element A \<Longrightarrow> O : One A"
  unfolding One_def by unfold_types

lemma One_one_type [derive]: "O : One A \<Longrightarrow> O @@ one : Element A"
  unfolding One_def by unfold_types

definition "one O \<equiv> O @@ one"

lemma one_type [type]: "one : One A \<Rightarrow> Element A"
  unfolding one_def by auto

abbreviation one_implicit :: "set"
  where "one_implicit \<equiv> one \<implicit>O"

bundle isa_set_one_implicit_syntax begin notation one_implicit ("1") end
bundle no_isa_set_one_implicit_syntax begin no_notation one_implicit ("1") end

unbundle isa_set_one_implicit_syntax


subsection \<open>Additive structures\<close>

definition [typeclass]: "Add A \<equiv> type (\<lambda>P. P @@ add : A \<rightarrow> A \<rightarrow> A)"

\<comment>\<open>Show declared type classes\<close>
ML \<open>Type_Classes.get_type_classes @{context}\<close>

lemma AddI: "P @@ add : A \<rightarrow> A \<rightarrow> A \<Longrightarrow> P : Add A"
  unfolding Add_def by unfold_types

lemma Add_add_type [derive]: "P : Add A \<Longrightarrow> P @@ add : A \<rightarrow> A \<rightarrow> A"
  unfolding Add_def by unfold_types

definition "add P x y \<equiv> (P @@ add)`x`y"

lemma add_type [type]: "add : Add A \<Rightarrow> Element A \<Rightarrow> Element A \<Rightarrow> Element A"
  (*TODO: should not need an increase of the limit*)
  using [[type_derivation_depth=4]]
  unfolding add_def by discharge_types

abbreviation add_implicit :: "set \<Rightarrow> set \<Rightarrow> set"
  where "add_implicit x y \<equiv> add \<implicit>P x y"

bundle isa_set_add_implicit_syntax
begin notation add_implicit  (infixl "+" 65) end

bundle no_isa_set_add_implicit_syntax
begin no_notation add_implicit  (infixl "+" 65) end

unbundle isa_set_add_implicit_syntax


subsection \<open>Multiplicative structures\<close>

definition [typeclass]:
  "Mul A \<equiv> type (\<lambda>M. M @@ mul : A \<rightarrow> A \<rightarrow> A)"

lemma MulI: "M @@ mul : A \<rightarrow> A \<rightarrow> A \<Longrightarrow> M : Mul A"
  unfolding Mul_def by unfold_types

lemma Mul_mul_type [derive]: "M : Mul A \<Longrightarrow> M @@ mul : A \<rightarrow> A \<rightarrow> A"
  unfolding Mul_def by unfold_types

definition "mul M x y \<equiv> (M @@ mul)`x`y"

lemma mul_type [type]: "mul : Mul A \<Rightarrow> Element A \<Rightarrow> Element A \<Rightarrow> Element A"
  (*TODO: should not need an increase of the limit*)
  using [[type_derivation_depth=4]]
  unfolding mul_def by discharge_types

abbreviation mul_implicit :: "set \<Rightarrow> set \<Rightarrow> set"
  where "mul_implicit x y \<equiv> mul \<implicit>T x y"

bundle isa_set_mul_implicit_syntax
begin notation mul_implicit  (infixl "*" 65) end

bundle no_isa_set_mul_implicit_syntax
begin no_notation mul_implicit  (infixl "*" 65) end

unbundle isa_set_mul_implicit_syntax

subsection \<open>Structures with additive inverses\<close>

definition [typeclass]: "Inv A \<equiv> type (\<lambda>I. I @@ inv : A \<rightarrow> A)"

lemma InvI: "I @@ inv : A \<rightarrow> A \<Longrightarrow> I : Inv A"
  unfolding Inv_def by unfold_types

lemma Inv_inv_type [derive]: "I : Inv A \<Longrightarrow> I @@ inv : A \<rightarrow> A"
  unfolding Inv_def by unfold_types

definition "inv I x = (I @@ inv)`x"

lemma inv_type [type]: "inv : Inv A \<Rightarrow> Element A \<Rightarrow> Element A"
  unfolding inv_def by discharge_types

abbreviation inv_implicit where "inv_implicit x \<equiv> inv \<implicit>I x"

bundle isa_set_inv_implicit_syntax
  begin notation inv_implicit  ("_\<inverse>" [1000]) end

bundle no_isa_set_inv_implicit_syntax
  begin no_notation inv_implicit  ("_\<inverse>" [1000]) end


end
