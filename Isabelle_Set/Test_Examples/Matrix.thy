section "Matrices"

theory Matrix
  imports "../Isabelle_Set"
begin

definition upto ("{0..<_}") where
  "{0..<n} = {i \<in> \<nat> | i < n}"

lemma upto_type[type]: "upto : nat \<Rightarrow> subset \<nat>"
  unfolding upto_def by discharge_types

definition 
  "Matrix A n m = {0..<n} \<rightarrow> {0..<m} \<rightarrow> A"

lemma Matrix_type[type]: "Matrix : set \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> set"
  by discharge_types

definition
  "matrix_idx M i j = M`i`j"

lemma matrix_idx_type[type]: 
  "matrix_idx : element (Matrix A n m) \<Rightarrow> element {0..<n} \<Rightarrow> element {0..<m} \<Rightarrow> element A"
  unfolding Matrix_def matrix_idx_def
  by discharge_types


text \<open>Given the dimensions and a function mapping indices to values, construct a matrix:\<close>

definition  
  "matrix_comp n m f = (\<lambda>i\<in>{0..<n}. \<lambda>j\<in>{0..<m}. f i j)"

lemma matrix_comp_type[type]:
  "matrix_comp : (n : nat) \<Rightarrow> (m : nat) \<Rightarrow> (element {0..<n} \<Rightarrow> element {0..<m} \<Rightarrow> element A) 
  \<Rightarrow> element (Matrix A n m)"
  unfolding matrix_comp_def Matrix_def
  apply discharge_types (* takes way too long and does not solve the goal *)
  by (drule Pi_typeE | assumption)+


subsection \<open>Addition\<close>


text \<open>Class instance:\<close>

definition
  "Plus_Matrix A n m p = \<lparr> @plus = (\<lambda>M\<in>Matrix A n m. \<lambda>N\<in>Matrix A n m.
     matrix_comp n m (% i j. plus p (matrix_idx M i j) (matrix_idx N i j))) \<rparr>"

lemma Plus_Matrix_type[type]: "Plus_Matrix : (A : set) \<Rightarrow> (n : nat) \<Rightarrow> (m : nat) \<Rightarrow> Plus A \<Rightarrow> Plus (Matrix A n m)"
  apply (intro Pi_typeI Plus_typeI)
  apply (simp add: Plus_Matrix_def)
  apply (rule derivation_rules) (* From here on, discharge_types should do it. *)
   apply discharge_types[1]
  apply (rule Pi_typeI)
  apply (rule derivation_rules)
   apply discharge_types[1]
  apply (rule Pi_typeI)
  apply (rule derivation_rules, assumption, assumption)
  apply discharge_types
  done

lemma Plus_Matrix_instance[type_instance]:
  "n : nat \<Longrightarrow> m : nat \<Longrightarrow> p : Plus A \<Longrightarrow> Plus_Matrix A n m p : Plus (Matrix A n m)"
  by discharge_types


(*

declare [[auto_elaborate]]

lemma "matrix_idx (M + N) i j = matrix_idx M i j + matrix_idx N i j"

*)

end