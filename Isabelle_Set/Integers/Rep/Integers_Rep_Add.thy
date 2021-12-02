text \<open>Addition\<close>
theory Integers_Rep_Add
imports
  Integers_Rep_Succ_Pred_Inv
begin

definition "int_rep_add x y \<equiv> int_rep_rec
  (\<lambda>m. nat_rec m y int_rep_succ)
  (\<lambda>m. nat_rec m y int_rep_pred)
  x"

(*old definition; not very nice for inductive proofs*)
(* definition "int_rep_add x y \<equiv> coprod_rec
  (\<lambda>m. nat_rec m y 0
  (\<lambda>m. coprod_rec
    (\<lambda>n. if n < m then inr (m - n) else inl (n - m))
    (\<lambda>n. inr (m + n))
    y)
  x" *)

lemma int_rep_zero_add_eq [simp]:
  "int_rep_add int_rep_zero x = x"
  unfolding int_rep_add_def int_rep_zero_def by simp

(*useful for proofs*)
lemma int_rep_neg_zero_add_eq [simp]:
  "int_rep_add (int_rep_neg 0) x = x"
  unfolding int_rep_add_def by simp

lemma int_rep_nonneg_succ_add_eq:
  assumes "n : Nat"
  shows "int_rep_add (int_rep_nonneg (succ n)) y =
    int_rep_succ (int_rep_add (int_rep_nonneg n) y)"
  by (simp add: int_rep_add_def)

lemma int_rep_neg_succ_add_eq:
  assumes "n : Nat"
  shows "int_rep_add (int_rep_neg (succ n)) y =
    int_rep_pred (int_rep_add (int_rep_neg n) y)"
  by (simp add: int_rep_add_def)

lemma int_rep_add_type [type]: "int_rep_add :
  Element int_rep \<Rightarrow> Element int_rep \<Rightarrow> Element int_rep"
proof (intro Dep_fun_typeI)
(*TODO: this should be automatically provable by the type-checker*)
  fix x y assume [type]: "x : Element int_rep" "y : Element int_rep"
  then have [type]: "x : Element (\<nat> \<Coprod> (\<nat> \<setminus> {0}))" unfolding int_rep_def by simp
  have "(\<lambda>m. nat_rec m y int_rep_succ) : Nat \<Rightarrow> Element int_rep"
    by discharge_types
  moreover have "(\<lambda>m. nat_rec m y int_rep_pred) : Element (\<nat> \<setminus> {0}) \<Rightarrow> Element int_rep"
    by unfold_types auto
  ultimately show "int_rep_add x y : Element int_rep"
    unfolding int_rep_add_def int_rep_def by discharge_types
qed

lemma int_rep_succ_add_eq_succ_add:
  assumes "x \<in> int_rep" "y \<in> int_rep"
  shows "int_rep_add (int_rep_succ x) y = int_rep_succ (int_rep_add x y)"
using \<open>x \<in> int_rep\<close>
proof (cases x rule: mem_int_repE)
  case (nonneg n)
  then show ?thesis by (simp add: int_rep_nonneg_succ_add_eq)
next
  case (neg n)
  then have "n \<in> \<nat>" by simp
  from this neg show ?thesis
  proof (cases n rule: mem_natE)
    case (succ n)
    then show ?thesis
    proof (cases "n = 0")
      case False
      then have "n \<in> (\<nat> \<setminus> {0})" by auto
      from neg succ have "int_rep_add (int_rep_succ x) y =
        int_rep_add (int_rep_succ (int_rep_pred (int_rep_neg n))) y"
        by simp
      also have "... = int_rep_add (int_rep_neg n) y"
        by (simp only: int_rep_succ_pred_eq)
      also from neg succ have "... = int_rep_succ (int_rep_add x y)"
        by (simp add: int_rep_neg_succ_add_eq)
      finally show ?thesis .
    next
      case True
      with neg succ have "int_rep_add (int_rep_succ x) y = y"
        using nat_one_def by simp
      also from neg succ True have "... = int_rep_succ (int_rep_add x y)"
        by (simp add: int_rep_neg_succ_add_eq)
      finally show ?thesis by (simp add: int_rep_neg_succ_add_eq)
    qed
  qed auto
qed

lemma int_rep_inv_add_inv_inv_eq_add [simp]:
  assumes "x \<in> int_rep" "y \<in> int_rep"
  shows "int_rep_inv (int_rep_add (int_rep_inv x) (int_rep_inv y)) =
    int_rep_add x y" (is "?lhs = _")
using \<open>x \<in> int_rep\<close>
proof (cases x rule: mem_int_repE)
  (*we first prove a generalised version for the nonnegative case*)
  {
    fix n y assume "n \<in> \<nat>"
    let ?x = "int_rep_nonneg n"
    from \<open>n \<in> \<nat>\<close> have "y \<in> int_rep \<Longrightarrow>
      int_rep_inv (int_rep_add (int_rep_inv ?x) (int_rep_inv y)) = int_rep_add ?x y"
    proof (induction n rule: nat_induct)
      case zero
      then show ?case by (auto simp: int_rep_zero_def[symmetric])
    next
      case (succ n)
      then show ?case
      proof (cases n rule: mem_natE)
        case zero
        then show ?thesis unfolding int_rep_add_def by simp
      next
        case (succ _)
        have "int_rep_inv (
            int_rep_add (int_rep_inv (int_rep_nonneg (succ n))) (int_rep_inv y)
          ) = int_rep_inv (
            int_rep_add (int_rep_neg (succ n)) (int_rep_inv y)
          )" by simp
        also have "... = int_rep_inv (
            int_rep_pred (int_rep_add (int_rep_neg n) (int_rep_inv y))
          )"
          by (simp add: int_rep_neg_succ_add_eq)
        also have "... = int_rep_succ (
            int_rep_inv (int_rep_add (int_rep_neg n) (int_rep_inv y))
          )"
        proof -
          from \<open>n = succ _\<close> have
            "int_rep_add (int_rep_neg n) (int_rep_inv y) \<in> int_rep"
            (*TODO should be doable by type-checker*)
            using int_rep_add_type by unfold_types
          then show ?thesis by (simp only: int_rep_succ_inv_eq_inv_pred)
        qed
        also have "... = int_rep_succ (
            int_rep_inv (int_rep_add (int_rep_inv (int_rep_nonneg n)) (int_rep_inv y))
          )"
          using \<open>n = succ _ \<close> by (simp only: int_rep_inv_nonneg_eq[OF succ_ne_zero])
        also from succ.IH have
          "... = int_rep_succ (int_rep_add (int_rep_nonneg n) y)" by simp
        also have "... = int_rep_add (int_rep_nonneg (succ n)) y"
          by (simp only: int_rep_nonneg_succ_add_eq)
        finally show ?thesis .
      qed
    qed
  }
  note case_nonneg = this
  { case (nonneg _) then show ?thesis using case_nonneg by simp }
  case (neg n)
  then have "?lhs = int_rep_inv (int_rep_add (int_rep_nonneg n) (int_rep_inv y))"
    by simp
  also from case_nonneg[of "n" "int_rep_inv y"] have "... = int_rep_inv (
      int_rep_inv (int_rep_add (int_rep_inv (int_rep_nonneg n)) (int_rep_inv (int_rep_inv y)))
    )"
    using neg by simp
  also with neg have "... = int_rep_add x y" by simp
  finally show ?thesis .
qed

corollary int_rep_add_inv_inv_eq_inv_add:
  assumes "x \<in> int_rep" "y \<in> int_rep"
  shows "int_rep_add (int_rep_inv x) (int_rep_inv y) =
    int_rep_inv (int_rep_add x y)" (is "?lhs = _")
proof -
  have "?lhs = int_rep_inv (int_rep_inv (int_rep_add (int_rep_inv x) (int_rep_inv y)))"
    by (simp only: int_rep_inv_inv_eq)
  then show ?thesis using int_rep_inv_add_inv_inv_eq_add by simp
qed

lemma int_rep_pred_add_eq_pred_add:
  assumes "x \<in> int_rep" "y \<in> int_rep"
  shows "int_rep_add (int_rep_pred x) y = int_rep_pred (int_rep_add x y)"
    (is "int_rep_add ?x y = ?rhs")
proof -
  have "int_rep_add ?x y =
    int_rep_inv (int_rep_add (int_rep_inv ?x) (int_rep_inv y))"
    by simp
  also have "... = int_rep_inv (int_rep_add (int_rep_succ (int_rep_inv x))
    (int_rep_inv y))"
    by (simp only: int_rep_succ_inv_eq_inv_pred)
  also have "... = int_rep_pred (int_rep_inv (int_rep_add (int_rep_inv x)
    (int_rep_inv y)))"
    by (simp only: int_rep_succ_add_eq_succ_add int_rep_pred_inv_eq_inv_succ)
  also have "... = ?rhs" by simp
  finally show ?thesis .
qed

lemma int_rep_add_succ_eq_succ_add:
  assumes "x \<in> int_rep" "y \<in> int_rep"
  shows "int_rep_add x (int_rep_succ y) = int_rep_succ (int_rep_add x y)"
    (is "?lhs = _")
using assms
proof (cases x rule: mem_int_repE)
  {
    fix n y assume "n \<in> \<nat>" "y \<in> int_rep"
    then have 1: "int_rep_add (int_rep_nonneg n) (int_rep_succ y) =
      int_rep_succ (int_rep_add (int_rep_nonneg n) y)"
    by (induction n rule: nat_induct) (auto simp only:
      int_rep_zero_def[symmetric] int_rep_nonneg_succ_add_eq int_rep_zero_add_eq)
    from \<open>n \<in> \<nat>\<close> have "int_rep_add (int_rep_nonneg n) (int_rep_pred y) =
      int_rep_pred (int_rep_add (int_rep_nonneg n) y)"
    by (induction n rule: nat_induct) (auto simp:
      int_rep_zero_def[symmetric] int_rep_nonneg_succ_add_eq)
    note 1 this
  }
  note cases_nonneg = this
  { case (nonneg _) then show ?thesis using cases_nonneg by simp }
  case (neg n)
  then have "n \<in> \<nat>" by simp
  from neg have "?lhs = int_rep_inv (int_rep_add (int_rep_nonneg n)
    (int_rep_inv (int_rep_succ y)))"
    using int_rep_inv_add_inv_inv_eq_add[of x "int_rep_succ y"] by simp
  also have "... = int_rep_inv (int_rep_add (int_rep_nonneg n)
    (int_rep_pred (int_rep_inv y)))"
    by (simp only: int_rep_pred_inv_eq_inv_succ)
  also have "... = int_rep_inv (int_rep_pred (int_rep_add (int_rep_nonneg n)
    (int_rep_inv y)))"
    using cases_nonneg by simp
  also have "... = int_rep_succ (int_rep_inv (int_rep_add (int_rep_inv (int_rep_neg n))
    (int_rep_inv y)))"
    using int_rep_succ_inv_eq_inv_pred by simp
  also have "... = int_rep_succ (int_rep_add x y)"
    by (simp only: neg int_rep_inv_add_inv_inv_eq_add)
  finally show ?thesis .
qed

lemma int_rep_add_pred_eq_pred_add:
  assumes "x \<in> int_rep" "y \<in> int_rep"
  shows "int_rep_add x (int_rep_pred y) = int_rep_pred (int_rep_add x y)"
    (is "int_rep_add x ?y = ?rhs")
proof -
  have "int_rep_add x ?y =
    int_rep_inv (int_rep_add (int_rep_inv x) (int_rep_inv ?y))"
    by simp
  also have "... = int_rep_inv (int_rep_add (int_rep_inv x)
    (int_rep_succ (int_rep_inv y)))"
    by (simp only: int_rep_succ_inv_eq_inv_pred)
  also have "... = int_rep_pred (int_rep_inv (int_rep_add (int_rep_inv x)
    (int_rep_inv y)))"
    by (simp only: int_rep_add_succ_eq_succ_add int_rep_pred_inv_eq_inv_succ)
  also have "... = ?rhs" by simp
  finally show ?thesis .
qed

lemma int_rep_nonneg_add_nonneg_eq [simp]:
  assumes "n : Nat"
  shows "int_rep_add (int_rep_nonneg n) (int_rep_nonneg m) = int_rep_nonneg (n + m)"
  using assms by (induction n rule: Nat_induct)
  (auto simp: int_rep_zero_def[symmetric] int_rep_succ_add_eq_succ_add
    int_rep_nonneg_succ_add_eq)

lemma int_rep_neg_add_neg_eq [simp]:
  assumes "n : Nat"
  shows "int_rep_add (int_rep_neg n) (int_rep_neg m) = int_rep_neg (n + m)"
  using assms by (induction n rule: Nat_induct)
  (auto simp: int_rep_neg_succ_add_eq)

(*TODO: we could add more lemmas like the two above and simplify some proofs(?)*)
lemma int_rep_nonneg_add_neg_eq [simp]:
  assumes "n : Nat" "m : Nat"
  and "m \<noteq> 0"
  and "n < m"
  shows "int_rep_add (int_rep_nonneg n) (int_rep_neg m) = int_rep_neg (m - n)"
  (* using assms by (induction n rule: Nat_induct)
  (auto simp: int_rep_zero_def[symmetric] int_rep_nonneg_succ_add_eq) *)
oops

lemma int_rep_nonneg_add_neg_eq [simp]:
  assumes "n : Nat"
  and "m \<noteq> 0"
  and "m \<le> n"
  shows "int_rep_add (int_rep_nonneg n) (int_rep_neg m) = int_rep_nonneg (n - m)"
  (* using assms by (induction n rule: Nat_induct)
  (auto simp: int_rep_zero_def[symmetric] int_rep_nonneg_succ_add_eq) *)
oops

lemma int_rep_add_zero_eq [simp]:
  assumes "x \<in> int_rep"
  shows "int_rep_add x int_rep_zero = x"
using assms
proof (cases x rule: mem_int_repE)
  let ?z = int_rep_zero
  {
    fix n assume "n \<in> \<nat>"
    then have "int_rep_add (int_rep_nonneg n) ?z = int_rep_nonneg n"
    proof (induction n rule: nat_induct)
      case (succ n)
      have "int_rep_add (int_rep_nonneg (succ n)) ?z =
        int_rep_succ (int_rep_add (int_rep_nonneg n) ?z)"
        by (simp only: int_rep_nonneg_succ_add_eq)
      also from succ.IH have "... = int_rep_succ (int_rep_nonneg n)" by simp
      also have "... = int_rep_nonneg (succ n)" by simp
      finally show ?case .
    qed (simp add: int_rep_add_def int_rep_zero_def)
  }
  note case_nonneg = this
  { case (nonneg _) then show ?thesis using case_nonneg by simp }
  case (neg n)
  then have "int_rep_add x ?z = int_rep_inv (int_rep_add (int_rep_nonneg n) ?z)"
    using int_rep_inv_add_inv_inv_eq_add[of x ?z] by simp
  with neg case_nonneg show ?thesis by simp
qed

lemma int_rep_add_assoc:
  assumes "x \<in> int_rep" "y \<in> int_rep" "z \<in> int_rep"
  shows "int_rep_add (int_rep_add x y) z = int_rep_add x (int_rep_add y z)"
using \<open>x \<in> int_rep\<close>
proof (cases x rule: mem_int_repE)
  {
    fix n y z assume "n \<in> \<nat>" "y \<in> int_rep" "z \<in> int_rep"
    then have "int_rep_add (int_rep_add (int_rep_nonneg n) y) z =
      int_rep_add (int_rep_nonneg n) (int_rep_add y z)"
    proof (induction n arbitrary: y z rule: nat_induct)
      case zero
      then show ?case by (simp add: int_rep_zero_def[symmetric])
    next
      case (succ n)
      then have "int_rep_add (int_rep_add (int_rep_nonneg (succ n)) y) z =
        int_rep_add (int_rep_succ (int_rep_add (int_rep_nonneg n) y)) z"
        by (simp add: int_rep_nonneg_succ_add_eq)
      also have
        "... = int_rep_succ (int_rep_add (int_rep_add (int_rep_nonneg n) y) z)"
        by (simp only: int_rep_succ_add_eq_succ_add)
      also from succ.IH have
        "... = int_rep_succ (int_rep_add (int_rep_nonneg n) (int_rep_add y z))"
        by simp
      also from int_rep_nonneg_succ_add_eq have
        "... = int_rep_add (int_rep_nonneg (succ n)) (int_rep_add y z)"
        by simp
      finally show ?case .
    qed
  }
  note case_nonneg = this
  { case (nonneg _) then show ?thesis using case_nonneg by simp }
  case (neg n)
  have "int_rep_add (int_rep_add x y) z =
    int_rep_inv (int_rep_add (int_rep_inv (int_rep_add x y)) (int_rep_inv z))"
    by simp
  also have
    "... = int_rep_inv (
      int_rep_add (int_rep_inv (int_rep_add (int_rep_inv (int_rep_inv x))
      (int_rep_inv (int_rep_inv y)))) (int_rep_inv z))"
    by simp
  also have "... = int_rep_inv (
      int_rep_add (int_rep_add (int_rep_inv x) (int_rep_inv y)) (int_rep_inv z))"
    by (simp only: int_rep_inv_add_inv_inv_eq_add)
  also from neg case_nonneg have "... = int_rep_inv (
      int_rep_add (int_rep_nonneg n) (int_rep_add (int_rep_inv y) (int_rep_inv z))
    )"
    by simp
  also from neg have "... = int_rep_inv (
      int_rep_add (int_rep_inv x) (int_rep_inv (int_rep_add y z))
    )"
    by (simp add: int_rep_add_inv_inv_eq_inv_add)
  also have "... = int_rep_add x (int_rep_add y z)"
    by (simp add: int_rep_add_inv_inv_eq_inv_add)
  finally show ?thesis .
qed

lemma int_rep_add_comm:
  assumes "x \<in> int_rep" "y \<in> int_rep"
  shows "int_rep_add x y = int_rep_add y x"
using \<open>x \<in> int_rep\<close>
proof (cases x rule: mem_int_repE)
  {
    fix n y assume "n \<in> \<nat>" "y \<in> int_rep"
    then have "int_rep_add (int_rep_nonneg n) y = int_rep_add y (int_rep_nonneg n)"
    by (induction n rule: nat_induct)
    (auto simp add: int_rep_nonneg_succ_add_eq int_rep_zero_def[symmetric]
      int_rep_add_succ_eq_succ_add[symmetric])
  }
  note case_nonneg = this
  { case (nonneg _) then show ?thesis using case_nonneg by simp }
  case (neg n)
  then have "int_rep_add x y =
    int_rep_inv (int_rep_add (int_rep_nonneg n) (int_rep_inv y))"
    using int_rep_inv_add_inv_inv_eq_add[of x y] by simp
  also from neg case_nonneg have
    "... = int_rep_inv (int_rep_add (int_rep_inv y) (int_rep_inv (int_rep_neg n)))"
    by simp
  also from neg have "... = int_rep_add y x"
    by (simp only: int_rep_add_inv_inv_eq_inv_add int_rep_inv_inv_eq)
  finally show ?thesis .
qed

definition "int_rep_sub x y \<equiv> int_rep_add x (int_rep_inv y)"

lemma int_rep_sub_type [type]:
  "int_rep_sub : Element int_rep \<Rightarrow> Element int_rep \<Rightarrow> Element int_rep"
  unfolding int_rep_sub_def by discharge_types


end