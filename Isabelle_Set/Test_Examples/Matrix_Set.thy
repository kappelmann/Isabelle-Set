section \<open>Matrices\<close>

theory Matrix_Set
imports "../Isabelle_Set"

begin

definition upto ("{0..< _}") where "{0..< n} = {i \<in> \<nat> | i < n}"

definition "matrix A m n \<equiv> {0..<m} \<rightarrow> {0..<n} \<rightarrow> A"


subsection \<open>Zero\<close>

definition "matrix_zero Z m n \<equiv>
  \<lambda>i \<in> {0..<m}. \<lambda>j \<in> {0..<n}. zero Z"

lemma matrix_zero_type [type]:
  "matrix_zero : Zero A \<Rightarrow> (m : Nat) \<Rightarrow> (n : Nat) \<Rightarrow> element (matrix A m n)"
  unfolding matrix_def matrix_zero_def by discharge_types

definition "matrix_Zero Z m n \<equiv> object {
  \<langle>@zero, matrix_zero Z m n\<rangle>
}"

lemma matrix_Zero_type: assumes "Z : Zero A" "m : Nat" "n : Nat"
  shows "matrix_Zero Z m n : Zero (matrix A m n)"
  unfolding matrix_Zero_def by (rule Zero_typeI) auto


subsection \<open>Addition\<close>

definition "matrix_add A m n M N \<equiv>
  \<lambda>i \<in> {0..<m}. \<lambda>j \<in> {0..<n}. add A (M `i `j) (N `i `j)"

lemma matrix_add_type [type]: "matrix_add : Add A \<Rightarrow> (m : Nat) \<Rightarrow> (n : Nat) \<Rightarrow>
  element (matrix A m n) \<Rightarrow> element (matrix A m n) \<Rightarrow> element (matrix A m n)"
  unfolding matrix_def matrix_add_def by discharge_types

\<comment> \<open>Note Kevin: or one could do the following:\<close>
\<comment> \<open>declare [[coercion_enabled]] [[coercion "apply"]]

definition "matrix_add a m n (M :: set) (N :: set) \<equiv>
  \<lambda>i \<in> {0..<m}. \<lambda>j \<in> {0..<n}. add a (M i j) (N i j)"

declare [[coercion "element"]]

lemma matrix_add_type [type]: "matrix_add : Add A \<Rightarrow> (m : Nat) \<Rightarrow> (n : Nat) \<Rightarrow>
  matrix A m n \<Rightarrow> matrix A m n \<Rightarrow> matrix A m n"
  unfolding matrix_def matrix_add_def by discharge_types
\<close>

definition "matrix_Add C A m n \<equiv> object {
  \<langle>@add, \<lambda>M N \<in> matrix C m n. matrix_add A m n M N\<rangle>
}"

lemma matrix_Add_type : assumes "A : Add C" "m : Nat" "n : Nat"
  shows "matrix_Add C A m n : Add (matrix C m n)"
  unfolding matrix_Add_def by (rule Add_typeI) auto


subsection \<open>Monoid\<close>

lemma assumes "M : Monoid A" "N : element (matrix A m n)"
  shows matrix_add_zero: "matrix_add M m n N (matrix_zero M m n) = N"
  and matrix_zero_add: "matrix_add M m n (matrix_zero M m n) N = N"
  unfolding matrix_add_def matrix_zero_def
  using assms by (auto intro!: lambda_ext simp: matrix_def)

lemma matrix_add_assoc: assumes "M : Monoid A" "N : element (matrix A m n)"
  "O : element (matrix A m n)" "P : element (matrix A m n)"
  shows "matrix_add M m n (matrix_add M m n N O) P =
    matrix_add M m n N (matrix_add M m n O P)"
  unfolding matrix_add_def
  using assms add_assoc by (auto intro!: lambda_ext simp: matrix_def)

lemma assumes "A : Add C" "m : Nat" "n : Nat"
  shows "matrix_Add C A m n : Add (matrix C m n)"
  unfolding matrix_Add_def by (rule Add_typeI) auto

definition "matrix_Monoid A M m n \<equiv> object {
  \<langle>@zero, matrix_zero M m n\<rangle>,
  \<langle>@add, \<lambda>N O \<in> matrix A m n. matrix_add M m n N O\<rangle>
}"

\<comment> \<open>TODO Kevin: Create object extension method so that one can re-use the proofs
from matrix_Add_type and matrix_Zero_type instead of unfolding and
proving everything again.\<close>
lemma assumes "M : Monoid A" "m : Nat" "n : Nat"
  shows "matrix_Monoid A M m n : Monoid (matrix A m n)"
  unfolding matrix_Monoid_def by (rule MonoidI)
  (auto simp: matrix_add_zero matrix_zero_add matrix_add_assoc add_def zero_def
    intro!: Zero_typeI Add_typeI)


end