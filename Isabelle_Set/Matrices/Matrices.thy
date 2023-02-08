section \<open>Matrices\<close>
theory Matrices
  imports
    Nat
    (* TSFunctions *)
begin

unbundle no_HOL_groups_syntax
unbundle no_HOL_order_syntax

definition "matrices A m n \<equiv> ([0,\<dots>,m[ :: set) \<rightarrow>s ([0,\<dots>,n[ :: set) \<rightarrow>s A"

definition [typedef]: "Matrix A m n \<equiv> Element [0,\<dots>,m[ \<rightarrow>cs Element [0,\<dots>,n[ \<rightarrow>cs A"

lemma mem_matrices_iff_Matrix:
  "M \<in> matrices A m n \<longleftrightarrow> M : Matrix (Element A) m n"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof -
  have
    "?lhs \<longleftrightarrow> M : Element [0,\<dots>,m[ \<rightarrow>cs Element (([0,\<dots>,n[ :: set) \<rightarrow>s A)"
    unfolding matrices_def by auto
  also have "...  \<longleftrightarrow> ?rhs"
  proof -
    have "\<And>N. N : Element (([0,\<dots>,n[ :: set) \<rightarrow>s A) \<longleftrightarrow> N : (Element [0,\<dots>,n[ \<rightarrow>cs Element A)"
      by (subst mem_iff_Element[symmetric]) auto
    then show ?thesis
      unfolding Matrix_def by (auto elim: CDep_Function_covariant_codom)
  qed
  finally show ?thesis .
qed

soft_type_translation
  "M \<in> matrices A m n" \<rightleftharpoons> "M : Matrix (Element A) m n"
  using mem_matrices_iff_Matrix by auto

lemma Matrix_if_CDep_Function [derive]:
  assumes "M : Element [0,\<dots>,m[ \<rightarrow>cs Element [0,\<dots>,n[ \<rightarrow>cs A"
  shows "M : Matrix A m n"
  using assms Dep_Function_covariant_codom unfolding Matrix_def by auto

lemma eval_type [type]:
  "eval : Matrix A m n \<Rightarrow> (x : Element [0,\<dots>,m[) \<Rightarrow> Element [0,\<dots>,n[ \<rightarrow>cs A"
  unfolding Matrix_def by discharge_types

lemma Matrix_eval_typeI:
  assumes "M : Matrix A m n" "i : Nat" "j : Nat"
  and i_lt_m: "i < m"
  and j_lt_n: "j < n"
  shows "M`i`j : A"
proof -
  have "i \<in> [0,\<dots>,m[" "j \<in> [0,\<dots>,n[" by auto
  then show ?thesis
    using assms [[type_derivation_depth=4]] unfolding Matrix_def
    by discharge_types
qed

subsection \<open>Zero\<close>

definition "Matrix_zero Z m n \<equiv> \<lambda>i \<in> [0,\<dots>,m[. \<lambda>j \<in> [0,\<dots>,n[. zero Z"

lemma Matrix_zero_type [type]:
  "Matrix_zero : Zero A \<Rightarrow> (m : Nat) \<Rightarrow> (n : Nat) \<Rightarrow> Matrix A m n"
  unfolding Matrix_zero_def by discharge_types

lemma Matrix_zero_eq_zero [simp]:
  assumes "i : Nat" "j : Nat"
  and i_lt_m: "i < m"
  and j_lt_n: "j < n"
  shows "(Matrix_zero Z m n)`i`j = zero Z"
proof -
(*
Note Kevin: The simplifier tries to apply eval_lambda_eq. We need to discharge
i \<in> [0,\<dots>,m[.  This goal gets transformed to i : Element [0,\<dots>,m[.
Now, the type-derivator cannot solve this as there's no good rule for this type.
We might think about tagging {@thm in_range_excl_rightI} with "backward_derive".
But then the type derivator gets called with 0 \<le> i as a goal, which is no good.

Maybe there's a good way to incorporate auto/simp calls for non-type
premises in typing rules without making everything blow up.
*)
  have "i \<in> [0,\<dots>,m[" and "j \<in> [0,\<dots>,n[" by auto
  then show ?thesis unfolding Matrix_zero_def by auto
qed


definition "Matrix_Zero Z m n \<equiv> object {
    \<langle>@zero, Matrix_zero Z m n\<rangle>
  }"

lemma Matrix_Zero_type: assumes "Z : Zero A" "m : Nat" "n : Nat"
  shows "Matrix_Zero Z m n : Zero (Matrix A m n)"
  unfolding Matrix_Zero_def by (rule ZeroI) auto


subsection \<open>One\<close>

definition "Matrix_one Z O m n \<equiv>
  \<lambda>i \<in> [0,\<dots>,m[. \<lambda>j \<in> [0,\<dots>,n[. if i = j then one O else zero Z"

lemma Matrix_one_type [type]:
  "Matrix_one : Zero A \<Rightarrow> One A \<Rightarrow> (m : Nat) \<Rightarrow> (n : Nat) \<Rightarrow> Matrix A m n"
  unfolding Matrix_one_def by discharge_types

lemma Matrix_one_eq_one [simp]:
  assumes "i : Nat"
  and i_lt_m: "i < m"
  and i_lt_n: "i < n"
  shows "(Matrix_one Z O m n)`i`i = one O"
proof -
  have "i \<in> [0,\<dots>,m[" and "i \<in> [0,\<dots>,n[" by auto
  then show ?thesis unfolding Matrix_one_def by auto
qed

lemma Matrix_one_eq_zero [simp]:
  assumes "i : Nat" "j : Nat"
  and i_lt_m: "i < m"
  and j_lt_n: "j < n"
  and i_ne_j: "i \<noteq> j"
  shows "(Matrix_one Z O m n)`i`j = zero Z"
proof -
  have "i \<in> [0,\<dots>,m[" and "j \<in> [0,\<dots>,n[" by auto
  with i_ne_j show ?thesis unfolding Matrix_one_def by auto
qed

definition "Matrix_One Z O m n \<equiv> object {
    \<langle>@one, Matrix_one Z O m n\<rangle>
  }"

lemma Matrix_One_type:
  assumes "Z : Zero A" "O : One A" "m : Nat" "n : Nat"
  shows "Matrix_One Z O m n : One (Matrix A m n)"
  unfolding Matrix_One_def by (rule OneI) simp


subsection \<open>Addition\<close>

definition "Matrix_add A m n M N \<equiv>
  \<lambda>i \<in> [0,\<dots>,m[. \<lambda>j \<in> [0,\<dots>,n[. add A (M`i`j) (N`i`j)"

lemma Matrix_add_type [type]:
  "Matrix_add : Add C \<Rightarrow> (m : Nat) \<Rightarrow> (n : Nat) \<Rightarrow> Matrix C m n \<Rightarrow> Matrix C m n
    \<Rightarrow> Matrix C m n"
  unfolding Matrix_add_def using [[type_derivation_depth=4]]
  by discharge_types

lemma Matrix_add_eq_add [simp]:
  assumes "i : Nat" "j : Nat"
  and i_lt_m: "i < m"
  and j_lt_n: "j < n"
  shows "(Matrix_add A m n M N)`i`j = add A (M`i`j) (N`i`j)"
proof -
  have "i \<in> [0,\<dots>,m[" and "j \<in> [0,\<dots>,n[" by auto
  then show ?thesis unfolding Matrix_add_def by auto
qed

(*Note Kevin: or one could do the following:*)
(* declare [[coercion_enabled]] [[coercion "eval"]]

definition "Matrix_add' a m n (M :: set) (N :: set) \<equiv>
  \<lambda>i \<in> [0,\<dots>,m[. \<lambda>j \<in> [0,\<dots>,n[. add a (M i j) (N i j)"

declare [[coercion "Element"]]

lemma Matrix_add'_type [type]: "Matrix_add' : Add A \<Rightarrow> (m : Nat) \<Rightarrow> (n : Nat) \<Rightarrow>
  Matrix A m n \<Rightarrow> Matrix A m n \<Rightarrow> Matrix A m n"
  using [[type_derivation_depth=5]]
  unfolding Matrix_def Matrix_add'_def by discharge_types *)

definition "Matrix_Add C A m n \<equiv> object {
    \<langle>@add, \<lambda>M N \<in> matrices C m n. Matrix_add A m n M N\<rangle>
  }"

lemma Matrix_Add_type : assumes "A : Add (Element C)" "m : Nat" "n : Nat"
  shows "Matrix_Add C A m n : Add (Matrix (Element C) m n)"
proof -
  have [derive]: "\<And>M. M : Element (matrices C m n) \<Longrightarrow> M : Matrix (Element C) m n"
    by (drule ElementD) discharge_types
  have 2 [derive]: "\<And>M. M : Matrix (Element C) m n \<Longrightarrow> M : Element (matrices C m n)"
    by (rule ElementI) discharge_types
  then have "\<lambda>M N \<in> matrices C m n. Matrix_add A m n M N :
    Element (matrices C m n) \<rightarrow>cs Element (matrices C m n) \<rightarrow>cs
      Matrix (Element C) m n"
    by discharge_types
  then have "\<lambda>M N \<in> matrices C m n. Matrix_add A m n M N :
    Element (matrices C m n) \<rightarrow>s Element (matrices C m n) \<rightarrow>cs Matrix (Element C) m n"
    by (elim Dep_Function_if_CDep_Function)
  then have "\<lambda>M N \<in> matrices C m n. Matrix_add A m n M N :
    Element (matrices C m n) \<rightarrow>s Element (matrices C m n) \<rightarrow>s Matrix (Element C) m n"
    by (rule Dep_Function_covariant_codom, intro Dep_Function_if_CDep_Function)
  then have "\<lambda>M N \<in> matrices C m n. Matrix_add A m n M N :
    Matrix (Element C) m n \<rightarrow>s Element (matrices C m n) \<rightarrow>s Matrix (Element C) m n"
    by (elim Dep_Function_contravariant_dom) discharge_types
  then have "\<lambda>M N \<in> matrices C m n. Matrix_add A m n M N :
    Matrix (Element C) m n \<rightarrow>s Matrix (Element C) m n \<rightarrow>s Matrix (Element C) m n"
    by (elim Dep_Function_covariant_codom[OF Dep_Function_contravariant_dom])
      simp_all
  (* TODO Kevin: why is this selector not simplified automatically? *)
  have sel_simp:
    "(Matrix_Add C A m n)@@add = \<lambda>M N \<in> matrices C m n. Matrix_add A m n M N"
    unfolding Matrix_Add_def by simp
  show ?thesis by (intro AddI, subst sel_simp) fact
qed


subsection \<open>Additive Monoid\<close>

lemma Matrix_add_zero:
  assumes "M : Monoid (Element C)" "N : Matrix (Element C) m n"
  shows "Matrix_add M m n N (Matrix_zero M m n) = N"
  using assms using [[type_derivation_depth=4]]
  unfolding Matrix_add_def Matrix_zero_def
  apply (intro lambda_ext)
  apply (subst mem_dep_functions_iff_CDep_Function)
  apply (subst CDep_Function_covariant_codom)
  apply (simp only: Matrix_def)
  apply (rule ElementI)
  apply (subst mem_dep_functions_iff_CDep_Function)
  apply (auto simp only: eval_lambda_eq Monoid_add_zero_eq)
  done

lemma Matrix_zero_add:
  assumes "M : Monoid (Element C)" "N : Matrix (Element C) m n"
  shows "Matrix_add M m n (Matrix_zero M m n) N = N"
  using assms using [[type_derivation_depth=4]]
  unfolding Matrix_add_def Matrix_zero_def
  apply (intro lambda_ext)
  apply (subst mem_dep_functions_iff_CDep_Function)
  apply (subst CDep_Function_covariant_codom)
  apply (simp only: Matrix_def)
  apply (rule ElementI)
  apply (subst mem_dep_functions_iff_CDep_Function)
  apply (auto simp only: eval_lambda_eq Monoid_zero_add_eq)
  done

(*FIXME*)
lemma Matrix_add_assoc:
  assumes "M : Monoid (Element C)" "N : Matrix (Element C) m n"
    "O : Matrix (Element C) m n" "P : Matrix (Element C) m n"
  shows "Matrix_add M m n (Matrix_add M m n N O) P =
    Matrix_add M m n N (Matrix_add M m n O P)"
  using [[quick_and_dirty]]
  sorry
  (* using [[type_derivation_depth=4]] assms
  unfolding Matrix_add_def Matrix_def
  by (auto 0 0 intro!: lambda_ext simp: Nat_add_assoc) *)

definition "Matrix_Monoid C M m n \<equiv> object {
  \<langle>@zero, Matrix_zero M m n\<rangle>,
  \<langle>@add, \<lambda>N O \<in> matrices C m n. Matrix_add M m n N O\<rangle>
}"

(*TODO Kevin: Create object extension method so that one can re-use the proofs
from Matrix_Add_type and Matrix_Zero_type instead of unfolding and
proving everything again (cf branch object_extend).*)
lemma assumes "M : Monoid (Element C)" "m : Nat" "n : Nat"
  shows "Matrix_Monoid C M m n : Monoid (Matrix (Element C) m n)"
  using [[quick_and_dirty]]
  sorry
(* proof -
  have
    sel_add: "(Matrix_Monoid C M m n)@@add = \<lambda>N O \<in> matrices C m n. Matrix_add M m n N O"
    unfolding Matrix_Monoid_def by simp
  show ?thesis
    (* by (intro MonoidI ZeroI AddI; (subst sel_add)?)
    (auto simp: Matrix_Monoid_def Matrix_add_zero Matrix_zero_add
    Matrix_add_assoc add_def zero_def mem_dep_functions_iff_CDep_Function
    intro!: Dep_fun_typeI) *)
  (* proof (rule MonoidI)
    have "(Matrix_Monoid C M m n)@@add = (Matrix_Add C M m n)@@add"
      unfolding Matrix_Monoid_def Matrix_Add_def by simp
  qed *)
qed *)

subsection \<open>Multiplication\<close>

text \<open>Multiplying an l \<times> 0 with a 0 \<times> n Matrix returns the l \<times> n zero Matrix.\<close>
definition "Matrix_mul A M l m n N O \<equiv> \<lambda>i \<in> [0,\<dots>,l[. \<lambda>j \<in> [0,\<dots>,n[. nat_rec'
  m (zero A) (\<lambda>k acc. add A acc (mul M (N`i`(pred k)) (O `(pred k) `j)))"

(*Note Kevin: TODO: type derivator is not able to handle this automatically
yet*)
lemma Matrix_mul_type [type]: "Matrix_mul : Monoid C \<Rightarrow> Mul C \<Rightarrow> (l : Nat) \<Rightarrow>
  (m : Nat) \<Rightarrow> (n : Nat) \<Rightarrow> Matrix C l m \<Rightarrow> Matrix C m n \<Rightarrow> Matrix C l n"
proof (intro Dep_fun_typeI)
  fix AddM M l m n N O
  assume "AddM : Monoid C" "M : Mul C" "l : Nat" "m : Nat" "n : Nat"
    "N : Matrix C l m" "O : Matrix C m n"
  {
    fix i j assume "i : Element [0,\<dots>,l[" "j : Element [0,\<dots>,n["
    have "pred : Element [1,\<dots>,m] \<Rightarrow> Element [0,\<dots>,m["
    proof unfold_types
      fix n assume "n \<in> [1,\<dots>,m]"
      then have "n \<in> \<nat>" by (fact mem_nat_if_mem_range_incl_excl)
      have "pred n < m"
      proof -
        from \<open>n \<in> [1,\<dots>,m]\<close> have "0 \<noteq> n" "n \<le> m"
          unfolding nat_one_def by (auto elim: mem_rangeE)
        then show ?thesis by (auto intro: Nat_pred_lt_if_le_if_ne_zero)
      qed
      then show "pred n \<in> [0,\<dots>,m[" by auto
    qed
    have "(\<lambda>k acc. add AddM acc (mul M (N`i`(pred k)) (O`(pred k)`j)))
      : Element [1,\<dots>,m] \<Rightarrow> C \<Rightarrow> C"
      using [[type_derivation_depth=6]] by discharge_types
  }
  show "Matrix_mul AddM M l m n N O : Matrix C l n"
    using [[type_derivation_depth=4]]
    unfolding Matrix_mul_def by discharge_types
qed

definition "Matrix_Mul C A M l m n \<equiv> object {
    \<langle>@mul, \<lambda>N \<in> matrices C l m. (\<lambda>O \<in> matrices C m n. Matrix_mul A M l m n N O)\<rangle>
  }"

lemma Matrix_Mul_type:
  assumes "A : Monoid (Element C)" "M : Mul (Element C)" "n : Nat"
  shows "Matrix_Mul C A M n n n : Mul (Matrix (Element C) n n)"
proof -
  have [derive]: "\<And>M. M : Element (matrices C n n) \<Longrightarrow> M : Matrix (Element C) n n"
    by (drule ElementD) discharge_types
  have 2 [derive]: "\<And>M. M : Matrix (Element C) n n \<Longrightarrow> M : Element (matrices C n n)"
    by (rule ElementI) discharge_types
  let ?f = "\<lambda>N \<in> matrices C n n. (\<lambda>O \<in> matrices C n n. Matrix_mul A M n n n N O)"
  have "?f : Element (matrices C n n) \<rightarrow>cs Element (matrices C n n) \<rightarrow>cs
      Matrix (Element C) n n"
    by discharge_types
  then have "?f : Element (matrices C n n) \<rightarrow>s Element (matrices C n n) \<rightarrow>cs
    Matrix (Element C) n n"
    by (elim Dep_Function_if_CDep_Function)
  then have "?f : Element (matrices C n n) \<rightarrow>s Element (matrices C n n) \<rightarrow>s
    Matrix (Element C) n n"
    by (rule Dep_Function_covariant_codom, intro Dep_Function_if_CDep_Function)
  then have "?f : Matrix (Element C) n n \<rightarrow>s Element (matrices C n n) \<rightarrow>s
    Matrix (Element C) n n"
    by (elim Dep_Function_contravariant_dom) discharge_types
  then have "?f : Matrix (Element C) n n \<rightarrow>s Matrix (Element C) n n \<rightarrow>s
    Matrix (Element C) n n"
    by (elim Dep_Function_covariant_codom[OF Dep_Function_contravariant_dom])
      simp_all
  (* TODO Kevin: why is this selector not simplified automatically? *)
  have sel_simp: "(Matrix_Mul C A M n n n)@@mul =
    \<lambda>N \<in> matrices C n n. (\<lambda>O \<in> matrices C n n. Matrix_mul A M n n n N O)"
    unfolding Matrix_Mul_def by simp
  show ?thesis by (intro MulI, subst sel_simp) fact
qed

subsection \<open>Multiplicative Monoid\<close>

(*Note: This could be generalised to non-square matrices, but we do not need
that for now. *)
lemma
  assumes "A : Monoid C" "M : Mul_Monoid C" "n : Nat" "N : Matrix C n n"
  and mul_zero: "\<And>c. c : C \<Longrightarrow> mul M c (zero A) = zero A"
  and mul_one: "\<And>c. c : C \<Longrightarrow> mul M c (one M) = c"
  shows Matrix_mul_one: "Matrix_mul A M n n n N (Matrix_one A M n n) = N"
using mem_range_incl_exclE[elim]
(*FIXME*) [[quick_and_dirty]]
unfolding Matrix_mul_def
proof (intro lambda_ext)
  fix i j assume i_mem: "i \<in> [0,\<dots>,n[" and j_mem: "j \<in> [0,\<dots>,n["
  let ?f = "\<lambda>k acc. add A acc (mul M (N`i`(pred k)) (Matrix_one A M n n `(pred k) `j))"
  {
    fix m assume lassms: "m : Nat" "m < n"
    with i_mem have "N`i`m : C" by (intro Matrix_eval_typeI) auto
    with lassms have
      "nat_rec' (succ m) (zero A) ?f = (if m < j then zero A else N`i`j)"
    proof (induction m rule: Nat_induct)
      case zero
      then show ?case
      proof (cases "0 < j")
        case True
        with j_mem have "Matrix_one A M n n `0 `j = zero A"
          by (intro Matrix_one_eq_zero) auto
        with mul_zero show ?thesis using mul_zero True by auto
      next
        case False
        with j_mem have "j = 0" by (auto elim: leE)
        moreover with j_mem have "Matrix_one A M n n `0 `0 = one M"
          by (intro Matrix_one_eq_one) auto
        ultimately show ?thesis using mul_one by auto
      qed
    next
      case (succ m)
      then have "m < n" by (auto intro: Nat_lt_if_succ_lt)
      with i_mem have "N`i`m : C" by (intro Matrix_eval_typeI) auto
      with succ.IH have
        IH: "nat_rec' (succ m) (zero A) ?f = (if m < j then zero A else N`i`j)"
        by auto
      show ?case
      proof (cases "succ m < j")
        case True
        (* Note Kevin: this is BAD *)
        from j_mem have "j : Nat" by auto
        then have "m < j" using Nat_lt_if_succ_lt[OF _ \<open>succ m < j\<close>] by blast
        moreover with True j_mem have "Matrix_one A M n n `(succ m) `j = zero A"
          by (intro Matrix_one_eq_zero) auto
        ultimately show ?thesis using IH mul_zero True by auto
      next
        case False
        from j_mem have "j : Nat" "m : Nat" by auto
        then have f: "m < j \<and> j < succ m \<Longrightarrow> False" using
          Nat_succ_le_if_lt[of m j] Nat_not_lt_iff_le sorry
        have "j \<le> succ m" by (rule Nat_le_if_not_lt) simp
        then show ?thesis
        proof (cases rule: leE)
          case lt
          from i_mem j_mem have "N`i`j : C" by (intro Matrix_eval_typeI) auto
          from lt j_mem have "Matrix_one A M n n `(succ m) `j = zero A"
            by (intro Matrix_one_eq_zero) auto
          with f lt IH mul_zero show ?thesis using lt_asym by auto
        next
          case eq
          with IH mul_one show ?thesis by auto
        qed
      qed
    qed
  } note rec = this
  moreover from \<open>i \<in> [0,\<dots>,n[\<close> have "i < n" "i \<in> \<nat>" by auto
  (* case n=0 needed *)
  ultimately show "nat_rec' n (zero A) ?f = N`i`j"
  proof (cases "n = 0")
    case True
    with \<open>i < n\<close> show ?thesis by auto
  next
    case False
    then obtain m where n_eq_succ_m: "n = succ m" by (auto intro: mem_natE[of n])
    then have "m : Nat" "m < n" using \<open>n : Nat\<close> sorry
    then have
      lem: "nat_rec' (succ m) (zero A) ?f = (if m < j then zero A else N`i`j)"
      by (fact rec)
    have "j \<le> pred (succ m)"
      by (rule Nat_le_pred_if_lt) (insert j_mem n_eq_succ_m[symmetric], auto)
    then have "j \<le> m" by simp
    moreover from j_mem have "j : Nat" by auto
    ultimately have "\<not> m < j" using Nat_lt_if_lt_if_le[of j j m] by auto
    then show ?thesis using n_eq_succ_m lem by auto
  qed
  (*remaining type assumptions as in Matrix_Add_type and Matrix_Mul_Type*)
oops

end
