section \<open>Matrices\<close>

theory Matrix
imports "../Isabelle_Set"

begin

definition upto ("{0..< _}") where
  "{0..< n} = {i \<in> \<nat> | i < n}"

definition
  "Matrix A m n = {0..< m} \<rightarrow> {0..< n} \<rightarrow> A"

definition
  "matrix_idx (A::set) (m::set) (n::set) M i j = M`i`j"

lemma upto_type [type]: "upto : nat \<Rightarrow> subset \<nat>"
  unfolding upto_def by unfold_types auto

lemma Matrix_type [type]: "Matrix : set \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> set"
  by discharge_types

lemma matrix_idx_type [type]:
  "matrix_idx : (A : set) \<Rightarrow> (m : nat) \<Rightarrow> (n : nat) \<Rightarrow> element (Matrix A m n) \<Rightarrow> element {0..< m} \<Rightarrow> element {0..< n} \<Rightarrow> element A"
  unfolding Matrix_def matrix_idx_def
  by discharge_types


text \<open>Given the dimensions and a function mapping indices to values, construct a matrix:\<close>

definition  
  "matrix_comp (A::set) n m f = \<lambda>i \<in> {0..< n}. \<lambda>j \<in> {0..< m}. f i j"

lemma matrix_comp_type [type]:
  "matrix_comp : (A : set) \<Rightarrow> (m : nat) \<Rightarrow> (n : nat) \<Rightarrow> (element {0..< m} \<Rightarrow> element {0..< n} \<Rightarrow> element A) 
    \<Rightarrow> element (Matrix A m n)"
  unfolding matrix_comp_def Matrix_def
  by unfold_types auto


subsection \<open>Addition\<close>

text \<open>Class instance:\<close>

definition
  "Plus_Matrix A n m p = \<lparr> @plus = (\<lambda>M\<in>Matrix A n m. \<lambda>N\<in>Matrix A n m.
     matrix_comp A n m (\<lambda> i j. plus p (matrix_idx A n m M i j) (matrix_idx A n m N i j))) \<rparr>"

lemma Plus_Matrix_type [type]:
  "Plus_Matrix : (A : set) \<Rightarrow> (n : nat) \<Rightarrow> (m : nat) \<Rightarrow> Plus A \<Rightarrow> Plus (Matrix A n m)"
  apply (intro Pi_typeI Plus_typeI)
  apply (simp add: Plus_Matrix_def)
  by discharge_types

lemma Plus_Matrix_instance [type_instance]:
  "n : nat \<Longrightarrow> m : nat \<Longrightarrow> p : Plus A \<Longrightarrow> Plus_Matrix A n m p : Plus (Matrix A n m)"
  by discharge_types

declare [[auto_elaborate]]
thm matrix_idx_type


lemma "matrix_idx A n m (M + N) i j = matrix_idx A n m M i j + matrix_idx A n m N i j"
  print_types
  oops


end