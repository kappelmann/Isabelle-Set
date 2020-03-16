section \<open>Matrices\<close>

theory Matrix_Set
imports "../Isabelle_Set"

begin

definition upto ("{0..< _}") where "{0..< n} = {i \<in> \<nat> | i < n}"

definition "matrix A m n \<equiv> {0..<m} \<rightarrow> {0..<n} \<rightarrow> A"


subsection \<open>Addition\<close>

definition "matrix_add a m n M N \<equiv>
  \<lambda>i \<in> {0..<m}. \<lambda>j \<in> {0..<n}. add a (M `i `j) (N `i `j)"

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

definition "matrix_Add A a m n \<equiv> object {
  \<langle>@add, \<lambda>M N \<in> matrix A m n. matrix_add a m n M N\<rangle>
}"

lemma assumes "a : Add A" "m : Nat" "n : Nat"
  shows "matrix_Add A a m n : Add (matrix A m n)"
  unfolding matrix_Add_def by (rule Add_typeI) auto
                                      

end