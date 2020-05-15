theory Matrix
imports "../Isabelle_Set"

begin

unbundle no_notation_zero_implicit
unbundle notation_nat_zero


section\<open>Ranges with exluded upper bound\<close>
(*Note Kevin: I did not want to put them into Nat yet as I am not convinced
this is set up in a good way.*)

definition range_excl_right ("{_..<_}") where
  "{l..<u} \<equiv> {i \<in> \<nat> | l \<le> i \<and> i < u}"

lemma in_range_excl_rightI [intro]:
  assumes "n : Nat" "l \<le> n" "n < u"
  shows "n \<in> {l..<u}"
  unfolding range_excl_right_def by auto

lemma range_excl_right_succ_eq_range [simp]:
  assumes "l : Nat" "u : Nat"
  shows "{l..<succ u} = {l..u}"
  unfolding range_excl_right_def range_def
  by (rule equalityI) (auto intro: le_if_lt_succ lt_succ_if_le)

(* Note Kevin: Those feel really awkward as typing rules. The statement as a set
theoretic result seems more intuitive. Is this a job for automatic set to
type-theoretic result translation? *)

lemma in_range_imp_succ_in_range [derive]:
  assumes "l : Nat" "u : Nat" "n : Element {l..u}"
  shows "succ n : Element {succ l..succ u}"
  using assms unfolding range_def by unfold_types (auto intro: succ_le_monotone)

lemma in_range_excl_right_imp_succ_in_range [derive]:
  assumes "l : Nat" "u : Nat" "n : Element {l..<u}"
  shows "succ n : Element {succ l..u}"
  using assms unfolding range_excl_right_def range_def
  by unfold_types (auto intro: succ_le_monotone succ_le_if_lt)

(*Note Kevin: not needed for now but maybe a good test for set and type
conversion *)
(*lemma in_range_imp_pred_in_range [derive]:
  assumes "l : Nat" "u : Nat" "n : Element {l..u}"
  shows "pred n : Element {pred l..pred u}"
  using assms unfolding range_def
  oops*)

lemma in_range_succ_imp_pred_in_range_excl_right [derive]:
  assumes "l : Nat" "u : Nat" "n : Element {succ l..u}"
  shows "pred n : Element {l..<u}"
  using assms unfolding range_def range_excl_right_def
  by unfold_types (auto intro: pred_lt_if_le_if_ne_zero)

lemma range_subseteq_succ_right:
  assumes "l : Nat" "u : Nat"
  shows "{l..u} \<subseteq> {l..succ u}"
  using lt_succ_if_le nat_lt_imp_le
  unfolding range_def by unfold_types auto


section \<open>Matrices\<close>

definition "matrix C m n \<equiv> {0..<m} \<rightarrow> {0..<n} \<rightarrow> C"


subsection \<open>Zero\<close>

definition "matrix_zero Z m n \<equiv>
  \<lambda>i \<in> {0..<m}. \<lambda>j \<in> {0..<n}. zero Z"

lemma matrix_zero_type [type]:
  "matrix_zero : Zero C \<Rightarrow> (m : Nat) \<Rightarrow> (n : Nat) \<Rightarrow> Element (matrix C m n)"
  unfolding matrix_def matrix_zero_def by discharge_types

definition "matrix_Zero Z m n \<equiv> object {
  \<langle>@zero, matrix_zero Z m n\<rangle>
}"

lemma matrix_Zero_type: assumes "Z : Zero C" "m : Nat" "n : Nat"
  shows "matrix_Zero Z m n : Zero (matrix C m n)"
  unfolding matrix_Zero_def by (rule Zero_typeI) auto


subsection \<open>One\<close>

(*Note Kevin: TODO: why is not just auto working?*)
lemma if_type [type]: "If : bool \<Rightarrow> A \<Rightarrow> A \<Rightarrow> A"
 by (rule typeI) auto

definition "matrix_one Z O m n \<equiv>
  \<lambda>i \<in> {0..<m}. \<lambda>j \<in> {0..<n}. if i = j then one O else zero Z"

lemma matrix_one_type [type]:
  "matrix_one : Zero C \<Rightarrow> One C \<Rightarrow> (m : Nat) \<Rightarrow> (n : Nat) \<Rightarrow>
    Element (matrix C m n)"
  using [[trace_type_derivation]]
  unfolding matrix_def matrix_one_def by discharge_types

definition "matrix_One Z O m n \<equiv> object {
  \<langle>@one, matrix_one Z O m n\<rangle>
}"

lemma matrix_One_type: assumes "Z : Zero C" "O : One C" "m : Nat" "n : Nat"
  shows "matrix_One Z O m n : One (matrix C m n)"
  unfolding matrix_One_def by (rule One_typeI) auto


subsection \<open>Addition\<close>

definition "matrix_add A m n M N \<equiv>
  \<lambda>i \<in> {0..<m}. \<lambda>j \<in> {0..<n}. add A (M `i `j) (N `i `j)"

lemma matrix_add_type [type]: "matrix_add : Add C \<Rightarrow> (m : Nat) \<Rightarrow> (n : Nat) \<Rightarrow>
  Element (matrix C m n) \<Rightarrow> Element (matrix C m n) \<Rightarrow> Element (matrix C m n)"
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

lemma assumes "M : Monoid C" "N : Element (matrix C m n)"
  shows matrix_add_zero: "matrix_add M m n N (matrix_zero M m n) = N"
  and matrix_zero_add: "matrix_add M m n (matrix_zero M m n) N = N"
  unfolding matrix_add_def matrix_zero_def
  using assms by (auto intro!: lambda_ext simp: matrix_def)

lemma matrix_add_assoc: assumes "M : Monoid C" "N : Element (matrix C m n)"
  "O : Element (matrix C m n)" "P : Element (matrix C m n)"
  shows "matrix_add M m n (matrix_add M m n N O) P =
    matrix_add M m n N (matrix_add M m n O P)"
  unfolding matrix_add_def
  using assms add_assoc by (auto intro!: lambda_ext simp: matrix_def)

definition "matrix_Monoid C M m n \<equiv> object {
  \<langle>@zero, matrix_zero M m n\<rangle>,
  \<langle>@add, \<lambda>N O \<in> matrix C m n. matrix_add M m n N O\<rangle>
}"

(*TODO Kevin: Create object extension method so that one can re-use the proofs
from matrix_Add_type and matrix_Zero_type instead of unfolding and
proving everything again (cf branch object_extend).*)
lemma assumes "M : Monoid C" "m : Nat" "n : Nat"
  shows "matrix_Monoid C M m n : Monoid (matrix C m n)"
  unfolding matrix_Monoid_def by (rule MonoidI)
  (auto simp: matrix_add_zero matrix_zero_add matrix_add_assoc add_def zero_def
    intro!: Zero_typeI Add_typeI)


subsection \<open>Multiplication\<close>

unbundle no_notation_one_implicit
unbundle notation_nat_one

text \<open>Multiplying an l \<times> 0 with a 0 \<times> n matrix returns the l \<times> n zero matrix.\<close>
definition "matrix_mul A M l m n N O \<equiv> \<lambda>i \<in> {0..<l}. \<lambda>j \<in> {0..<n}. natrec'
  m
  (zero A)
  (\<lambda>k acc. add A acc (mul M (N `i `(pred k)) (O `(pred k) `j)))"

(*Note Kevin: this can be put in Nat.thy once the lemmas it relies on are
considered to be clean.*)
lemma natrec'_dep_type [type]: "natrec' : (n : Nat) \<Rightarrow> Element A \<Rightarrow>
  (Element {1..n} \<Rightarrow> Element A \<Rightarrow> Element A) \<Rightarrow> Element A"
proof (rule typeI)+
  fix n x\<^sub>0 f
  assume  "n : Nat" "x\<^sub>0 : Element A"
    "f : Element {1..n} \<Rightarrow> Element A \<Rightarrow> Element A"
  then show "natrec' n x\<^sub>0 f : Element A"
  proof (induction n rule: Nat_induct)
    case (induct n)
    have "f : Element {1..n} \<Rightarrow> Element A \<Rightarrow> Element A"
      using func_type_restrict_set_domain[OF range_subseteq_succ_right]
      by discharge_types (*Note Kevin: How come this works by discharge_types?*)
    moreover have "succ n : Element {1..succ n}"
      unfolding nat_one_def by discharge_types
    ultimately show ?case using induct.prems unfolding nat_one_def by auto
  qed simp
qed

(*Note Kevin: TODO: type derivator is not able to handle this automatically
yet*)
lemma matrix_mul_type [type]: "matrix_mul : Monoid C \<Rightarrow> Mul C \<Rightarrow> (l : Nat) \<Rightarrow>
  (m : Nat) \<Rightarrow> (n : Nat) \<Rightarrow> Element (matrix C l m) \<Rightarrow> Element (matrix C m n) \<Rightarrow>
  Element (matrix C l n)"
unfolding matrix_def
proof (rule typeI)+
  fix AddM M l m n N O
  assume "AddM : Monoid C" "M : Mul C" "l : Nat" "m : Nat" "n : Nat"
    "N : Element ({0..<l} \<rightarrow> {0..<m} \<rightarrow> C)"
    "O : Element ({0..<m} \<rightarrow> {0..<n} \<rightarrow> C)"
  {
    fix i j
    assume "i : Element {0..<l}" "j : Element {0..<n}"
    moreover have "pred : Element {succ 0..m} \<Rightarrow> Element {0..<m}"
      by discharge_types
    then have "(\<lambda>k acc. add AddM acc (mul M (N `i `(pred k)) (O `(pred k) `j)))
      : Element {1..m} \<Rightarrow> Element C \<Rightarrow> Element C"
      using [[type_derivation_depth=5]] unfolding nat_one_def by discharge_types
  }
  then show "matrix_mul AddM M l m n N O : Element ({0..<l} \<rightarrow> {0..<n} \<rightarrow> C)"
    unfolding matrix_mul_def nat_one_def by discharge_types
qed

definition "matrix_Mul C A M l m n \<equiv> object {
  \<langle>@mul, \<lambda>N \<in> matrix C l m. (\<lambda>O \<in> matrix C m n. matrix_mul A M l m n N O)\<rangle>
}"

lemma matrix_Mul_type:
  assumes "A : Monoid C" "M : Mul C" "n : Nat"
  shows "matrix_Mul C A M n n n : Mul (matrix C n n)"
  using [[trace_type_derivation]] [[type_derivation_depth=8]]
  unfolding matrix_Mul_def by (rule Mul_typeI) auto


subsection \<open>Multiplicative Monoid\<close>

lemma
  assumes "A : Monoid C" "M : Mul_Monoid C" "N : Element (matrix C n n)"
  shows matrix_mul_one: "matrix_mul A M n n n N (matrix_one A M n n) = N"
  oops

end


