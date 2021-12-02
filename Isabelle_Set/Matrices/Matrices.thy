section \<open>Matrices\<close>
theory Matrices
imports Nat
begin

definition "matrix C m n \<equiv> \<Prod>_ \<in> [0,\<dots>,m[. \<Prod>_ \<in> [0,\<dots>,n[. C"

lemma matrix_eval_memI:
  assumes "M \<in> matrix C m n" "i : Nat" "j : Nat"
  and i_lt_m: "i < m"
  and j_lt_n: "j < n"
  shows "M `i `j \<in> C"
proof -
  have "i \<in> [0,\<dots>,m[" and "j \<in> [0,\<dots>,n[" by auto
  then show ?thesis using assms unfolding matrix_def
    (*TODO should not be needed*)
    using [[type_derivation_depth=4]]
    by (simp only: mem_dep_functions_iff_Dep_Function)
qed

subsection \<open>Zero\<close>

definition "matrix_zero Z m n \<equiv>
  \<lambda>i \<in> [0,\<dots>,m[. \<lambda>j \<in> [0,\<dots>,n[. zero Z"

lemma matrix_zero_type [type]:
  "matrix_zero : Zero Z \<Rightarrow> (m : Nat) \<Rightarrow> (n : Nat) \<Rightarrow> Element (matrix Z m n)"
  unfolding matrix_def matrix_zero_def by discharge_types

lemma matrix_zero_eq_zero [simp]:
  assumes "i : Nat" "j : Nat"
  and i_lt_m: "i < m"
  and j_lt_n: "j < n"
  shows "(matrix_zero Z m n) `i `j = zero Z"
proof -
(*
Note Kevin: The simplifier tries to apply beta. We need to discharge i \<in> [0,\<dots>,m[.
This goal gets transformed to i : Element [0,\<dots>,m[.
Now, the type-derivator cannot solve this as there's no good rule for this type.
We might think about tagging {@thm in_range_excl_rightI} with "backward_derive".
But then the type derivator gets called with 0 \<le> i as a goal, which is no good.

Maybe there's a good way to incorporate auto/simp calls for non-type
premises in typing rules without making everything blow up.
*)
  have "i \<in> [0,\<dots>,m[" and "j \<in> [0,\<dots>,n[" by auto
  then show ?thesis unfolding matrix_zero_def by auto
qed


definition "matrix_Zero Z m n \<equiv> object {
  \<langle>@zero, matrix_zero Z m n\<rangle>
}"

lemma matrix_Zero_type: assumes "Z : Zero C" "m : Nat" "n : Nat"
  shows "matrix_Zero Z m n : Zero (matrix C m n)"
  unfolding matrix_Zero_def by (rule ZeroI) auto


subsection \<open>One\<close>

definition "matrix_one Z O m n \<equiv>
  \<lambda>i \<in> [0,\<dots>,m[. \<lambda>j \<in> [0,\<dots>,n[. if i = j then one O else zero Z"

lemma matrix_one_type [type]:
  "matrix_one : Zero C \<Rightarrow> One C \<Rightarrow> (m : Nat) \<Rightarrow> (n : Nat) \<Rightarrow>
    Element (matrix C m n)"
  unfolding matrix_def matrix_one_def by discharge_types

lemma matrix_one_eq_one [simp]:
  assumes "i : Nat"
  and i_lt_m: "i < m"
  and i_lt_n: "i < n"
  shows "(matrix_one Z O m n) `i `i = one O"
proof -
  have "i \<in> [0,\<dots>,m[" and "i \<in> [0,\<dots>,n[" by auto
  then show ?thesis unfolding matrix_one_def by auto
qed

lemma matrix_one_eq_zero [simp]:
  assumes "i : Nat" "j : Nat"
  and i_lt_m: "i < m"
  and j_lt_n: "j < n"
  and i_ne_j: "i \<noteq> j"
  shows "(matrix_one Z O m n) `i `j = zero Z"
proof -
  have "i \<in> [0,\<dots>,m[" and "j \<in> [0,\<dots>,n[" by auto
  with i_ne_j show ?thesis unfolding matrix_one_def by auto
qed

definition "matrix_One Z O m n \<equiv> object {
  \<langle>@one, matrix_one Z O m n\<rangle>
}"

lemma matrix_One_type: assumes "Z : Zero C" "O : One C" "m : Nat" "n : Nat"
  shows "matrix_One Z O m n : One (matrix C m n)"
  unfolding matrix_One_def by (rule OneI) auto


subsection \<open>Addition\<close>

definition "matrix_add A m n M N \<equiv>
  \<lambda>i \<in> [0,\<dots>,m[. \<lambda>j \<in> [0,\<dots>,n[. add A (M `i `j) (N `i `j)"

lemma matrix_add_type [type]: "matrix_add : Add C \<Rightarrow> (m : Nat) \<Rightarrow> (n : Nat) \<Rightarrow>
  Element (matrix C m n) \<Rightarrow> Element (matrix C m n) \<Rightarrow> Element (matrix C m n)"
  using [[type_derivation_depth=5]]
  unfolding matrix_def matrix_add_def by discharge_types

lemma matrix_add_eq_add [simp]:
  assumes "i : Nat" "j : Nat"
  and i_lt_m: "i < m"
  and j_lt_n: "j < n"
  shows "(matrix_add A m n M N) `i `j = add A (M `i `j) (N `i `j)"
proof -
  have "i \<in> [0,\<dots>,m[" and "j \<in> [0,\<dots>,n[" by auto
  then show ?thesis unfolding matrix_add_def by auto
qed

(*Note Kevin: or one could do the following:*)
(* declare [[coercion_enabled]] [[coercion "eval"]]

definition "matrix_add' a m n (M :: set) (N :: set) \<equiv>
  \<lambda>i \<in> [0,\<dots>,m[. \<lambda>j \<in> [0,\<dots>,n[. add a (M i j) (N i j)"

declare [[coercion "Element"]]

lemma matrix_add'_type [type]: "matrix_add' : Add A \<Rightarrow> (m : Nat) \<Rightarrow> (n : Nat) \<Rightarrow>
  matrix A m n \<Rightarrow> matrix A m n \<Rightarrow> matrix A m n"
  using [[type_derivation_depth=5]]
  unfolding matrix_def matrix_add'_def by discharge_types *)

definition "matrix_Add C A m n \<equiv> object {
  \<langle>@add, \<lambda>M N \<in> matrix C m n. matrix_add A m n M N\<rangle>
}"

lemma matrix_Add_type : assumes "A : Add C" "m : Nat" "n : Nat"
  shows "matrix_Add C A m n : Add (matrix C m n)"
proof -
  (* TODO Kevin: why is this selector not simplified automatically? *)
  have sel_simp:
    "(matrix_Add C A m n)@@add = \<lambda>M N \<in> matrix C m n. matrix_add A m n M N"
    unfolding matrix_Add_def by simp
  show ?thesis by (intro AddI, subst sel_simp) discharge_types
qed


subsection \<open>Additive Monoid\<close>

(* TODO: slow proof *)
lemma
  assumes "M : Monoid C" "N : Element (matrix C m n)"
  shows matrix_add_zero: "matrix_add M m n N (matrix_zero M m n) = N"
    and matrix_zero_add: "matrix_add M m n (matrix_zero M m n) N = N"
  using [[type_derivation_depth=4]] assms
  unfolding matrix_add_def matrix_zero_def matrix_def
  by (auto intro!: lambda_ext)

(*FIXME*)
lemma matrix_add_assoc:
  assumes "M : Monoid C" "N : Element (matrix C m n)"
    "O : Element (matrix C m n)" "P : Element (matrix C m n)"
  shows "matrix_add M m n (matrix_add M m n N O) P =
    matrix_add M m n N (matrix_add M m n O P)"
using [[quick_and_dirty]]
sorry
  (* using [[type_derivation_depth=4]] assms
  unfolding matrix_add_def matrix_def
  by (auto 0 0 intro!: lambda_ext simp: Nat_add_assoc) *)

definition "matrix_Monoid C M m n \<equiv> object {
  \<langle>@zero, matrix_zero M m n\<rangle>,
  \<langle>@add, \<lambda>N O \<in> matrix C m n. matrix_add M m n N O\<rangle>
}"

(*TODO Kevin: Create object extension method so that one can re-use the proofs
from matrix_Add_type and matrix_Zero_type instead of unfolding and
proving everything again (cf branch object_extend).*)
lemma assumes "M : Monoid C" "m : Nat" "n : Nat"
  shows "matrix_Monoid C M m n : Monoid (matrix C m n)"
proof -
  have
    sel_add: "(matrix_Monoid C M m n)@@add = \<lambda>N O \<in> matrix C m n. matrix_add M m n N O"
    unfolding matrix_Monoid_def by simp
  show ?thesis
    by (intro MonoidI ZeroI AddI; (subst sel_add)?)
    (auto simp: matrix_Monoid_def matrix_add_zero matrix_zero_add
    matrix_add_assoc add_def zero_def Element_dep_functions_iff_Dep_Function
    intro!: Dep_fun_typeI)
qed


subsection \<open>Multiplication\<close>

unbundle no_isa_set_one_implicit_syntax
unbundle isa_set_nat_zero_syntax

text \<open>Multiplying an l \<times> 0 with a 0 \<times> n matrix returns the l \<times> n zero matrix.\<close>
definition "matrix_mul A M l m n N O \<equiv> \<lambda>i \<in> [0,\<dots>,l[. \<lambda>j \<in> [0,\<dots>,n[. nat_rec'
  m (zero A) (\<lambda>k acc. add A acc (mul M (N `i `(pred k)) (O `(pred k) `j)))"

(*Note Kevin: TODO: type derivator is not able to handle this automatically
yet*)
lemma matrix_mul_type [type]: "matrix_mul : Monoid C \<Rightarrow> Mul C \<Rightarrow> (l : Nat) \<Rightarrow>
  (m : Nat) \<Rightarrow> (n : Nat) \<Rightarrow> Element (matrix C l m) \<Rightarrow> Element (matrix C m n) \<Rightarrow>
  Element (matrix C l n)"
unfolding matrix_def
proof (intro Dep_fun_typeI, simp only: Element_dep_functions_iff_Dep_Function)
  fix AddM M l m n N O
  assume "AddM : Monoid C" "M : Mul C" "l : Nat" "m : Nat" "n : Nat"
    "N : [0,\<dots>,l[ \<rightarrow> [0,\<dots>,m[ \<rightarrow> C" "O : [0,\<dots>,m[ \<rightarrow> [0,\<dots>,n[ \<rightarrow> C"
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
    have "(\<lambda>k acc. add AddM acc (mul M (N `i `(pred k)) (O `(pred k) `j)))
      : Element [1,\<dots>,m] \<Rightarrow> Element C \<Rightarrow> Element C"
      using [[type_derivation_depth=6]] by discharge_types
  }
  then show "matrix_mul AddM M l m n N O : [0,\<dots>,l[ \<rightarrow> [0,\<dots>,n[ \<rightarrow> C"
    using [[type_derivation_depth=3]]
    unfolding matrix_mul_def by discharge_types
qed

definition "matrix_Mul C A M l m n \<equiv> object {
  \<langle>@mul, \<lambda>N \<in> matrix C l m. (\<lambda>O \<in> matrix C m n. matrix_mul A M l m n N O)\<rangle>
}"

lemma matrix_Mul_type:
  assumes "A : Monoid C" "M : Mul C" "n : Nat"
  shows "matrix_Mul C A M n n n : Mul (matrix C n n)"
proof -
  (* TODO Kevin: why is this selector not simplified automatically? *)
  have sel_simp: "(matrix_Mul C A M n n n)@@mul =
    \<lambda>N \<in> matrix C n n. (\<lambda>O \<in> matrix C n n. matrix_mul A M n n n N O)"
    unfolding matrix_Mul_def by simp
  show ?thesis by (intro MulI, subst sel_simp) discharge_types
qed


subsection \<open>Multiplicative Monoid\<close>

(*Note: This could be generalised to non-square matrices, but we do not need
that for now. *)
lemma
  assumes "A : Monoid C" "M : Mul_Monoid C" "n : Nat" "N : Element (matrix C n n)"
  and mul_zero: "\<And>c. c \<in> C \<Longrightarrow> mul M c (zero A) = zero A"
  and mul_one: "\<And>c. c \<in> C \<Longrightarrow> mul M c (one M) = c"
  shows matrix_mul_one: "matrix_mul A M n n n N (matrix_one A M n n) = N"
using mem_range_incl_exclE[elim]
(*FIXME*) [[quick_and_dirty]]
unfolding matrix_mul_def
proof (intro lambda_ext)
  fix i j assume i_mem: "i \<in> [0,\<dots>,n[" and j_mem: "j \<in> [0,\<dots>,n["
  let ?f = "\<lambda>k acc. add A acc (mul M (N `i `(pred k)) (matrix_one A M n n `(pred k) `j))"
  {
    fix m assume lassms: "m : Nat" "m < n"
    with i_mem have "N `i `m \<in> C" by (intro matrix_eval_memI) auto
    with lassms have
      "nat_rec' (succ m) (zero A) ?f = (if m < j then zero A else N `i `j)"
    proof (induction m rule: Nat_induct)
      case zero
      then show ?case
      proof (cases "0 < j")
        case True
        with j_mem have "matrix_one A M n n `0 `j = zero A"
          by (intro matrix_one_eq_zero) auto
        with mul_zero show ?thesis using mul_zero True by auto
      next
        case False
        with j_mem have "j = 0" by (auto elim: leE)
        moreover with j_mem have "matrix_one A M n n `0 `0 = one M"
          by (intro matrix_one_eq_one) auto
        ultimately show ?thesis using mul_one by auto
      qed
    next
      case (succ m)
      then have "m < n" by (auto intro: Nat_lt_if_succ_lt)
      with i_mem have "N `i `m \<in> C" by (intro matrix_eval_memI) auto
      with succ.IH have
        IH: "nat_rec' (succ m) (zero A) ?f = (if m < j then zero A else N `i `j)"
        by auto
      show ?case
      proof (cases "succ m < j")
        case True
        (* Note Kevin: this is BAD *)
        from j_mem have "j : Nat" by auto
        then have "m < j" using Nat_lt_if_succ_lt[OF _ \<open>succ m < j\<close>] by blast
        moreover with True j_mem have "matrix_one A M n n `(succ m) `j = zero A"
          by (intro matrix_one_eq_zero) auto
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
          from i_mem j_mem have "N `i `j \<in> C" by (intro matrix_eval_memI) auto
          from lt j_mem have "matrix_one A M n n `(succ m) `j = zero A"
            by (intro matrix_one_eq_zero) auto
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
  ultimately show "nat_rec' n (zero A) ?f = N `i `j"
  proof (cases "n = 0")
    case True
    with \<open>i < n\<close> show ?thesis by auto
  next
    case False
    then obtain m where n_eq_succ_m: "n = succ m" by (auto intro: mem_natE[of n])
    then have "m : Nat" "m < n" using \<open>n : Nat\<close> sorry
    then have
      lem: "nat_rec' (succ m) (zero A) ?f = (if m < j then zero A else N `i `j)"
      by (fact rec)
    have "j \<le> pred (succ m)"
      by (rule Nat_le_pred_if_lt) (insert j_mem n_eq_succ_m[symmetric], auto)
    then have "j \<le> m" by simp
    moreover from j_mem have "j : Nat" by auto
    ultimately have "\<not> m < j" using Nat_lt_if_lt_if_le[of j j m] by auto
    then show ?thesis using n_eq_succ_m lem by auto
  qed
qed (insert assms, auto simp: matrix_def Element_dep_functions_iff_Dep_Function)

end
