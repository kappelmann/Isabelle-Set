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

lemma
  assumes "n \<in> {l..<u}"
  shows nat_if_in_range_excl_right: "n \<in> \<nat>"
    and lt_if_in_range_excl_right: "n < u"
    and ge_if_in_range_excl_right: "l \<le> n"
  using assms unfolding range_excl_right_def by auto

(*Note Kevin: should this be intro? should this be backward_derive? what should
it be? If it's intro, it will not be picked when we, for example, want to beta
reduce M `i `j with "M" a matrix. *)
lemma in_range_excl_rightI [intro]:
  assumes "n : Nat" "l \<le> n" "n < u"
  shows "n \<in> {l..<u}"
  unfolding range_excl_right_def by auto

lemma range_excl_right_succ_eq_range [simp]:
  assumes "u : Nat"
  shows "{l..<succ u} = {l..u}"
  unfolding range_excl_right_def range_def
  by (rule equalityI) (auto intro: le_if_lt_succ lt_succ_if_le)

(* Note Kevin: Those feel really awkward as typing rules. The statement as a set
theoretic result seems more intuitive. Is this a job for automatic set to
type-theoretic result translation? *)
lemma in_range_imp_succ_in_range [derive]:
  assumes "u : Nat" "n : Element {l..u}"
  shows "succ n : Element {succ l..succ u}"
  (* for some reason, unfold_types loops *)
  using assms unfolding range_def Element_def meaning_of_type by auto

lemma in_range_excl_right_imp_succ_in_range [derive]:
  assumes "u : Nat" "n : Element {l..<u}"
  shows "succ n : Element {succ l..u}"
  using assms unfolding range_excl_right_def range_def Element_def meaning_of_type
  by (auto intro: succ_le_if_lt)

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
  using assms unfolding range_def range_excl_right_def Element_def meaning_of_type
  by (auto intro: pred_lt_if_le_if_ne_zero)

lemma range_subseteq_succ_right:
  assumes "u : Nat"
  shows "{l..u} \<subseteq> {l..succ u}"
  using lt_succ_if_le le_if_lt
  unfolding range_def by auto


section \<open>Matrices\<close>

definition "matrix C m n \<equiv> \<Prod>_ \<in> {0..<m}. \<Prod>_ \<in> {0..<n}. C"

(* Note Kevin: should this be tagged? *)
lemma matrix_apply [intro]:
  assumes "M \<in> matrix C m n" "i : Nat" "j : Nat"
  and i_lt_m: "i < m"
  and j_lt_n: "j < n"
  shows "M `i `j \<in> C"
proof -
  have "i \<in> {0..<m}" and "j \<in> {0..<n}" by auto
  then show ?thesis using assms unfolding matrix_def by auto
qed

subsection \<open>Zero\<close>
                                                       
definition "matrix_zero Z m n \<equiv>
  \<lambda>i \<in> {0..<m}. \<lambda>j \<in> {0..<n}. zero Z"

lemma matrix_zero_type [type]:
  "matrix_zero : Zero C \<Rightarrow> (m : Nat) \<Rightarrow> (n : Nat) \<Rightarrow> Element (matrix C m n)"
  unfolding matrix_def matrix_zero_def by (intro type_intro)+ (auto simp: Element_iff)

lemma matrix_zero_eq_zero [simp]:
  assumes "i : Nat" "j : Nat"
  and i_lt_m: "i < m"
  and j_lt_n: "j < n"
  shows "(matrix_zero Z m n) `i `j = zero Z"
proof -
(*
Note Kevin: The simplifier tries to apply beta. We need to discharge i \<in> {0..<m}.
This goal gets transformed to i : Element {0..<m}.
Now, the type-derivator cannot solve this as there's no good rule for this type.
We might think about tagging {@thm in_range_excl_rightI} with "backward_derive".
But then the type derivator gets called with 0 \<le> i as a goal, which is no good.

Maybe there's a good way to incorporate auto/simp calls for non-type
premises in typing rules without making everything blow up.
*)
  have "i \<in> {0..<m}" and "j \<in> {0..<n}" by auto
  then show ?thesis unfolding matrix_zero_def by auto
qed


definition "matrix_Zero Z m n \<equiv> object {
  \<langle>@zero, matrix_zero Z m n\<rangle>
}"

lemma matrix_Zero_type: assumes "Z : Zero C" "m : Nat" "n : Nat"
  shows "matrix_Zero Z m n : Zero (matrix C m n)"
  unfolding matrix_Zero_def by (rule Zero_typeI) auto


subsection \<open>One\<close>

(*Note Kevin: TODO: why is not just auto working? This also should be moved.*)
lemma if_type [type]: "If : bool \<Rightarrow> A \<Rightarrow> A \<Rightarrow> A"
 by (rule type_intro) auto

definition "matrix_one Z O m n \<equiv>
  \<lambda>i \<in> {0..<m}. \<lambda>j \<in> {0..<n}. if i = j then one O else zero Z"

lemma matrix_one_eq_one [simp]:
  assumes "i : Nat"
  and i_lt_m: "i < m"
  and i_lt_n: "i < n"
  shows "(matrix_one Z O m n) `i `i = one O"
proof -
  have "i \<in> {0..<m}" and "i \<in> {0..<n}" by auto
  then show ?thesis unfolding matrix_one_def by auto
qed

lemma matrix_one_eq_zero [simp]:
  assumes "i : Nat" "j : Nat"
  and i_lt_m: "i < m"
  and j_lt_n: "j < n"
  and i_neq_j: "i \<noteq> j"
  shows "(matrix_one Z O m n) `i `j = zero Z"
proof -
  have "i \<in> {0..<m}" and "j \<in> {0..<n}" by auto
  with i_neq_j show ?thesis unfolding matrix_one_def by auto
qed


lemma matrix_one_type [type]:
  "matrix_one : Zero C \<Rightarrow> One C \<Rightarrow> (m : Nat) \<Rightarrow> (n : Nat) \<Rightarrow>
    Element (matrix C m n)"
  unfolding matrix_def matrix_one_def by (intro type_intro)+ (auto simp: Element_iff)

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
  unfolding matrix_def matrix_add_def by (intro type_intro)+ (auto simp: Element_iff)

lemma matrix_add_eq_add [simp]:
  assumes "i : Nat" "j : Nat"
  and i_lt_m: "i < m"
  and j_lt_n: "j < n"
  shows "(matrix_add A m n M N) `i `j = add A (M `i `j) (N `i `j)"
proof -
  have "i \<in> {0..<m}" and "j \<in> {0..<n}" by auto
  then show ?thesis unfolding matrix_add_def by auto
qed

(*Note Kevin: or one could do the following:*)
(*declare [[coercion_enabled]] [[coercion "apply"]]

definition "matrix_add a m n (M :: set) (N :: set) \<equiv>
  \<lambda>i \<in> {0..<m}. \<lambda>j \<in> {0..<n}. add a (M i j) (N i j)"

declare [[coercion "element"]]

lemma matrix_add_type [type]: "matrix_add : Add A \<Rightarrow> (m : Nat) \<Rightarrow> (n : Nat) \<Rightarrow>
  matrix A m n \<Rightarrow> matrix A m n \<Rightarrow> matrix A m n"
  unfolding matrix_def matrix_add_def by discharge_types
*)

definition "matrix_Add C A m n \<equiv> object {
  \<langle>@add, \<lambda>M N \<in> matrix C m n. matrix_add A m n M N\<rangle>
}"

lemma matrix_Add_type : assumes "A : Add C" "m : Nat" "n : Nat"
  shows "matrix_Add C A m n : Add (matrix C m n)"
  (* TODO Kevin: why is this selector not simplified? *)
  unfolding matrix_Add_def by (intro Add_typeI) (auto simp: mem_piset_iff_DepFunction)


subsection \<open>Additive Monoid\<close>

lemma
  assumes "M : Monoid C" "N : Element (matrix C m n)"
  shows matrix_add_zero: "matrix_add M m n N (matrix_zero M m n) = N"
    and matrix_zero_add: "matrix_add M m n (matrix_zero M m n) N = N"
  unfolding matrix_add_def matrix_zero_def
  using assms by (auto intro!: lambda_ext simp: matrix_def)

lemma matrix_add_assoc:
  assumes "M : Monoid C" "N : Element (matrix C m n)"
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
proof (rule type_intro)+
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
proof (intro type_intro, simp only: Element_mem_piset_iff_DepFunction)+
  fix AddM M l m n N O
  assume "AddM : Monoid C" "M : Mul C" "l : Nat" "m : Nat" "n : Nat"
    "N : {0..<l} \<rightarrow> {0..<m} \<rightarrow> C"
    "O : {0..<m} \<rightarrow> {0..<n} \<rightarrow> C"
  {
    fix i j
    assume "i : Element {0..<l}" "j : Element {0..<n}"
    moreover have "pred : Element {succ 0..m} \<Rightarrow> Element {0..<m}"
      by discharge_types
    then have "(\<lambda>k acc. add AddM acc (mul M (N `i `(pred k)) (O `(pred k) `j)))
      : Element {1..m} \<Rightarrow> Element C \<Rightarrow> Element C"
      using [[type_derivation_depth=5]] unfolding nat_one_def by discharge_types
  }
  then show "matrix_mul AddM M l m n N O : {0..<l} \<rightarrow> {0..<n} \<rightarrow> C"
  using [[type_derivation_depth=3]]
  unfolding matrix_mul_def nat_one_def by
    (* TODO Kevin: why is this not working? "goal: no subgoals" *)
    (intro lambda_function_typeI, simp only: Element_mem_piset_iff_DepFunction)+
qed

definition "matrix_Mul C A M l m n \<equiv> object {
  \<langle>@mul, \<lambda>N \<in> matrix C l m. (\<lambda>O \<in> matrix C m n. matrix_mul A M l m n N O)\<rangle>
}"

lemma matrix_Mul_type:
  assumes "A : Monoid C" "M : Mul C" "n : Nat"
  shows "matrix_Mul C A M n n n : Mul (matrix C n n)"
  using [[trace_type_derivation=true]]
  unfolding matrix_Mul_def by (rule Mul_typeI) (auto simp: mem_piset_iff_DepFunction)


subsection \<open>Multiplicative Monoid\<close>

(*Note: This could be generalised to non-square matrices, but we do not need
that for now. *)
lemma
  assumes "A : Monoid C" "M : Mul_Monoid C" "n : Nat" "N : Element (matrix C n n)"
  and mul_zero: "\<And> c. c \<in> C \<Longrightarrow> mul M c (zero A) = zero A"
  and mul_one: "\<And> c. c \<in> C \<Longrightarrow> mul M c (one M) = c"
  shows matrix_mul_one: "matrix_mul A M n n n N (matrix_one A M n n) = N"
unfolding matrix_mul_def
proof (intro lambda_ext)
  fix i j
  assume i_dom: "i \<in> {0..<n}" and j_dom: "j \<in> {0..<n}"
  note nat_if_in_range_excl_right [dest] and lt_if_in_range_excl_right [dest] 
    and  ge_if_in_range_excl_right [dest]
  let ?f = "\<lambda>k acc. add A acc (mul M (N `i `(pred k)) (matrix_one A M n n `(pred k) `j))"
  {
    fix m assume lassms: "m : Nat" "m < n"
    with i_dom have "N `i `m \<in> C" by (intro matrix_apply) auto
    with lassms have "natrec' (succ m) (zero A) ?f = (if m < j then zero A else N `i `j)"
    proof (induction m rule: Nat_induct)
      case base
      then show ?case
      proof (cases "0 < j")
        case True
        with j_dom have "matrix_one A M n n `0 `j = zero A"
          by (intro matrix_one_eq_zero) auto
        with mul_zero show ?thesis using mul_zero True by auto
      next
        case False
        with j_dom have "j = 0" by (auto elim: leE)
        moreover with j_dom have "matrix_one A M n n `0 `0 = one M"
          by (intro matrix_one_eq_one) auto
        ultimately show ?thesis using mul_one by auto
      qed
    next
      case (induct m)
      then have "m < n" by (auto intro: lt_if_succ_lt)
      with i_dom have "N `i `m \<in> C" by (intro matrix_apply) auto
      with induct.IH have IH: "natrec' (succ m) (zero A) ?f = (if m < j then zero A else N `i `j)"
        by auto
      show ?case
      proof (cases "succ m < j")
        case True
        (* Note Kevin: BAD *)
        from j_dom have "j : Nat" by auto
        then have "m < j" using lt_if_succ_lt[OF _ \<open>succ m < j\<close>] by blast
        moreover with True j_dom have "matrix_one A M n n `(succ m) `j = zero A"
          by (intro matrix_one_eq_zero) auto
        ultimately show ?thesis using IH mul_zero True by auto
      next
        case False
        from j_dom have "j : Nat" "m : Nat" by auto
        then have f: "m < j \<and> j < succ m \<Longrightarrow> False" using
          succ_le_if_lt[of m j] not_le_if_lt[of j "succ m"] by auto
        have "j \<le> succ m" by (rule le_if_not_lt) simp
        then show ?thesis
        proof (cases rule: leE)
          case lt
          from i_dom j_dom have "N `i `j \<in> C" by (intro matrix_apply) auto
          from lt j_dom have "matrix_one A M n n `(succ m) `j = zero A"
            by (intro matrix_one_eq_zero) auto
          with f lt IH mul_zero show ?thesis using lt_asym by auto
        next
          case eq
          with IH mul_one show ?thesis by auto
        qed
      qed
    qed
  } note rec = this
  moreover from \<open>i \<in> {0..<n}\<close> have "i < n" "i \<in> \<nat>" by auto
  (* case n=0 needed *)
  ultimately show "natrec' n (zero A) ?f = N `i `j"
  proof (cases "n = 0")
    case True                                                     
    with \<open>i < n\<close> show ?thesis by auto
  next
    case False
    obtain m where n_eq_succ_m: "n = succ m" by (rule nat_succ_if_ne_zeroE[of n]) auto
    then have "m : Nat" "m < n" using \<open>n : Nat\<close> by auto
    then have lem: "natrec' (succ m) (zero A) ?f = (if m < j then zero A else N `i `j)" by
      (fact rec)
    have "j \<le> pred (succ m)" by (rule le_pred_if_lt) (insert j_dom n_eq_succ_m[symmetric], auto)
    then have "j \<le> m" by simp
    moreover from j_dom have "j : Nat" by auto
    ultimately have "\<not> m < j" using le_lt_lt[of j j m] by (auto intro: not_lt_if_le)
    then show ?thesis using n_eq_succ_m lem by auto
  qed
qed (insert assms, auto simp: matrix_def)

end
