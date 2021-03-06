section \<open>Matrices\<close>
theory Matrices_Typed
  imports Nat
begin

\<comment> \<open>I want the following -- is this safe?\<close>
\<comment> \<open>declare [[coercion_enabled]] [[coercion Element]] [[coercion "apply"]]\<close>

definition upto ("{0..< _}") where "{0..< n} = {i \<in> \<nat> | i < n}"

\<comment> \<open>Note Kevin: Having both, HOL and set functions is pain.\<close>
definition [typedef]:
  "Matrix A m n \<equiv> Element {0..<m} \<Rightarrow> Element {0..<n} \<Rightarrow> Element A"

definition "matrix A m n \<equiv> {0..<m} \<rightarrow> {0..<n} \<rightarrow> A"

definition "Matrix_to_matrix m n M \<equiv> \<lambda>i \<in> {0..<m}. \<lambda>j \<in> {0..<n}. M i j"

lemma Matrix_to_matrix_type [type]:
  "Matrix_to_matrix : (m : Nat) \<Rightarrow> (n : Nat) \<Rightarrow> Matrix A m n \<Rightarrow>
    Element (matrix A m n)"
  unfolding matrix_def Matrix_def Matrix_to_matrix_def
  by discharge_types

definition "matrix_to_Matrix M \<equiv> \<lambda>i j. M `i `j"

lemma matrix_to_Matrix_type [type]:
  "matrix_to_Matrix : Element (matrix A m n) \<Rightarrow> Matrix A m n"
  unfolding matrix_to_Matrix_def Matrix_def matrix_def by discharge_types


subsection \<open>Addition\<close>

definition "Matrix_add A M N i j = add A (M i j) (N i j)"

lemma Matrix_add_type [type]: "Matrix_add: Add A \<Rightarrow> Matrix A m n \<Rightarrow>
  Matrix A m n \<Rightarrow> Matrix A m n"
  unfolding Matrix_def Matrix_add_def by discharge_types

definition "matrix_Add C A m n \<equiv> object {
  \<langle>@add, \<lambda>M N \<in> matrix C m n. Matrix_to_matrix m n
    (Matrix_add A (matrix_to_Matrix M) (matrix_to_Matrix N))\<rangle>
}"

lemma assumes "A: Add C" "m: Nat" "n: Nat"
  shows "matrix_Add C A m n: Add (matrix C m n)"
  unfolding matrix_Add_def by (rule Add_typeI) auto

\<comment> \<open>Note Kevin: Now, given "M N \<in> matrix A m n", I could write "M + N" but given
"M N: Matrix A m n", I could not write "M + N" but need to write
"matrix_to_Matrix (Matrix_to_matrix m n M + Matrix_to_matrix m n N).\<close>

lemma Matrix_add_assoc: assumes "M : Monoid A" "N : Matrix A m n"
  "O : Matrix A m n" "P : Matrix A m n"
  "i : Element {0..<m}" "j : Element {0..<n}"
  shows "Matrix_add M (Matrix_add M N O) P i j =
    Matrix_add M N (Matrix_add M O P) i j"
  unfolding Matrix_add_def
  using assms add_assoc by (auto simp: Matrix_def)

definition "matrix_add A m n M N \<equiv> Matrix_to_matrix m n
  (Matrix_add A (matrix_to_Matrix M) (matrix_to_Matrix N))"

lemma matrix_add_assoc: assumes "M : Monoid A" "N : Element (matrix A m n)"
  "O : Element (matrix A m n)" "P : Element (matrix A m n)"
  shows "matrix_add M m n (matrix_add M m n N O) P =
    matrix_add M m n N (matrix_add M m n O P)"
  oops


end