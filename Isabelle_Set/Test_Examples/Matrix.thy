section \<open>Matrices\<close>

theory Matrix
imports "../Isabelle_Set"

begin

unbundle no_notation_zero_implicit
unbundle notation_nat_zero

definition range_excl_right ("{_..<_}") where
  "{l..<u} \<equiv> {i \<in> \<nat> | l \<le> i \<and> i < u}"

lemma range_excl_right_succ_eq_range [simp]: assumes "l : Nat" "u : Nat"
  shows "{l..<succ u} = {l..u}"
oops

lemma in_range_imp_succ_in_range [derive]:
  "n : element {l..u} \<Longrightarrow> succ n : element {succ l..succ u}"
oops

lemma in_range_imp_pred_in_range_ [derive]:
  "n : element {l..u} \<Longrightarrow> pred n : element {pred l..pred m}"
oops

lemma in_range_succ_imp_pred_in_range_excl_right [derive]:
  "n : element {succ l..u} \<Longrightarrow> pred n : element {0..<u}"
oops

definition "matrix C m n \<equiv> {0..<m} \<rightarrow> {0..<n} \<rightarrow> C"

subsection \<open>Zero\<close>

definition "matrix_zero Z m n \<equiv>
  \<lambda>i \<in> {0..<m}. \<lambda>j \<in> {0..<n}. zero Z"

lemma matrix_zero_type [type]:
  "matrix_zero : Zero C \<Rightarrow> (m : Nat) \<Rightarrow> (n : Nat) \<Rightarrow> element (matrix C m n)"
  unfolding matrix_def matrix_zero_def by discharge_types

definition "matrix_Zero Z m n \<equiv> object {
  \<langle>@zero, matrix_zero Z m n\<rangle>
}"

lemma matrix_Zero_type: assumes "Z : Zero C" "m : Nat" "n : Nat"
  shows "matrix_Zero Z m n : Zero (matrix C m n)"
  unfolding matrix_Zero_def by (rule Zero_typeI) auto


subsection \<open>Addition\<close>

definition "matrix_add A m n M N \<equiv>
  \<lambda>i \<in> {0..<m}. \<lambda>j \<in> {0..<n}. add A (M `i `j) (N `i `j)"

lemma matrix_add_type [type]: "matrix_add : Add C \<Rightarrow> (m : Nat) \<Rightarrow> (n : Nat) \<Rightarrow>
  element (matrix C m n) \<Rightarrow> element (matrix C m n) \<Rightarrow> element (matrix C m n)"
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


subsection \<open>Additive Monoid\<close>

lemma assumes "M : Monoid C" "N : element (matrix C m n)"
  shows matrix_add_zero: "matrix_add M m n N (matrix_zero M m n) = N"
  and matrix_zero_add: "matrix_add M m n (matrix_zero M m n) N = N"
  unfolding matrix_add_def matrix_zero_def
  using assms by (auto intro!: lambda_ext simp: matrix_def)

lemma matrix_add_assoc: assumes "M : Monoid C" "N : element (matrix C m n)"
  "O : element (matrix C m n)" "P : element (matrix C m n)"
  shows "matrix_add M m n (matrix_add M m n N O) P =
    matrix_add M m n N (matrix_add M m n O P)"
  unfolding matrix_add_def
  using assms add_assoc by (auto intro!: lambda_ext simp: matrix_def)

lemma assumes "A : Add C" "m : Nat" "n : Nat"
  shows "matrix_Add C A m n : Add (matrix C m n)"
  unfolding matrix_Add_def by (rule Add_typeI) auto

definition "matrix_Monoid C M m n \<equiv> object {
  \<langle>@zero, matrix_zero M m n\<rangle>,
  \<langle>@add, \<lambda>N O \<in> matrix C m n. matrix_add M m n N O\<rangle>
}"

\<comment> \<open>TODO Kevin: Create object extension method so that one can re-use the proofs
from matrix_Add_type and matrix_Zero_type instead of unfolding and
proving everything again.\<close>
lemma assumes "M : Monoid C" "m : Nat" "n : Nat"
  shows "matrix_Monoid C M m n : Monoid (matrix C m n)"
  unfolding matrix_Monoid_def by (rule MonoidI)
  (auto simp: matrix_add_zero matrix_zero_add matrix_add_assoc add_def zero_def
    intro!: Zero_typeI Add_typeI)

subsection \<open>Multiplication\<close>

text \<open>Recursion on Nat with index\<close>
definition "natrec' n x\<^sub>0 f \<equiv> snd (natrec
  \<langle>nat_zero, x\<^sub>0\<rangle>
  (\<lambda>p. \<langle>succ (fst p), f (succ (fst p)) (snd p)\<rangle>)
  n
)"

text \<open>Note Kevin: TODO: type derivator is not able to handle this automatically
yet\<close>
lemma natrec'_type:
  "natrec' : Nat \<Rightarrow> element A \<Rightarrow> (Nat \<Rightarrow> element A \<Rightarrow> element A) \<Rightarrow> element A"
proof (rule typeI)+
  fix x\<^sub>0 f n
  assume "x\<^sub>0 : element A" "f : Nat \<Rightarrow> element A \<Rightarrow> element A" "n : Nat"
  have "(\<lambda>p. \<langle>succ (fst p), f (succ (fst p)) (snd p)\<rangle>)
    : element (\<nat> \<times> A) \<Rightarrow> element (\<nat> \<times> A)" using [[type_derivation_depth=5]]
    by discharge_types
  then show "natrec' n x\<^sub>0 f : element A" unfolding natrec'_def
    by discharge_types
qed

unbundle no_notation_one_implicit
unbundle notation_nat_one
\<comment> \<open>
declare [[trace_type_derivation=true]]\<close>

lemma natrec'_dep_type [type]: "natrec' : (n : Nat) \<Rightarrow> element A \<Rightarrow>
  (element {1..n} \<Rightarrow> element A \<Rightarrow> element A) \<Rightarrow> element A"
sorry
(*proof (rule typeI)+
  fix n x\<^sub>0 f
  assume  "n : Nat" "x\<^sub>0 : element A"
    "f : element {1..n} \<Rightarrow> element A \<Rightarrow> element A"
  \<comment> \<open>then have "(\<lambda>p. \<langle>succ (fst p), f (succ (fst p)) (snd p)\<rangle>)
    : element ({0..<n} \<times> A) \<Rightarrow> element ({1..n} \<times> A)"
    using [[type_derivation_depth=4]] unfolding nat_one_def
    by discharge_types\<close>
  then show "natrec' n x\<^sub>0 f : element A"
  proof (induction n rule: Nat_induct)
    case base
    then show ?case unfolding natrec'_def by simp
  next
    case (induct n)
    show ?case unfolding natrec'_def by simp
  qed
qed*)


text \<open>Multiplying an l \<times> 0 with a 0 \<times> n matrix returns the l \<times> n zero matrix.\<close>
definition "matrix_mul A M l m n N O \<equiv> \<lambda>i \<in> {0..<l}. \<lambda>j \<in> {0..<n}. natrec'
  m
  (zero A)
  (\<lambda>k acc. add A acc (mul M (N `i `(pred k)) (O `(pred k) `j)))"

declare [[trace_type_derivation=true]]

lemma matrix_mul_type [type]: "matrix_mul : Monoid C \<Rightarrow> Mul C \<Rightarrow> (l : Nat) \<Rightarrow>
  (m : Nat) \<Rightarrow> (n : Nat) \<Rightarrow> element (matrix C l m) \<Rightarrow> element (matrix C m n) \<Rightarrow>
  element (matrix C l n)"
\<comment> \<open>Note Kevin: The following works once the oops at the beginning of this
theory are fixed\<close>
\<comment> \<open>unfolding matrix_def
proof (rule typeI)+
  fix AddM M l m n N O
  assume "AddM : Monoid C" "M : Mul C" "l : Nat" "m : Nat" "n : Nat"
    "N : element ({0..<l} \<rightarrow> {0..<m} \<rightarrow> C)"
    "O : element ({0..<m} \<rightarrow> {0..<n} \<rightarrow> C)"
  {
    fix i j
    assume "i : element {0..<l}" "j : element {0..<n}"
    then have "(\<lambda>k acc. add AddM acc (mul M (N `i `(pred k)) (O `(pred k) `j)))
      : element {1..m} \<Rightarrow> element C \<Rightarrow> element C"
      using [[type_derivation_depth=5]] unfolding nat_one_def
      by discharge_types
  }
  then show "matrix_mul AddM M l m n N O : element ({0..<l} \<rightarrow> {0..<n} \<rightarrow> C)"
    unfolding matrix_mul_def nat_one_def by discharge_types
qed\<close>
oops

end