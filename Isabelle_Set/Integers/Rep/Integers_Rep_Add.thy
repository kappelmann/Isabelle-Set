text \<open>Addition\<close>
theory Integers_Rep_Add
imports
  Integers_Rep_Succ_Pred_Inv
begin

definition "Int_Rep_add x y \<equiv> Int_Rep_rec
  (\<lambda>m. nat_rec m y Int_Rep_succ)
  (\<lambda>m. nat_rec m y Int_Rep_pred)
  x"

(*old definition; not very nice for inductive proofs*)
(* definition "Int_Rep_add x y \<equiv> coprod_rec
  (\<lambda>m. nat_rec m y 0
  (\<lambda>m. coprod_rec
    (\<lambda>n. if n < m then inr (m - n) else inl (n - m))
    (\<lambda>n. inr (m + n))
    y)
  x" *)

lemma Int_Rep_zero_add_eq [simp]:
  "Int_Rep_add Int_Rep_zero x = x"
  unfolding Int_Rep_add_def Int_Rep_zero_def by simp

(*useful for proofs*)
lemma Int_Rep_neg_zero_add_eq [simp]:
  "Int_Rep_add (Int_Rep_neg 0) x = x"
  unfolding Int_Rep_add_def by simp

lemma Int_Rep_nonneg_succ_add_eq:
  assumes "n : Nat"
  shows "Int_Rep_add (Int_Rep_nonneg (succ n)) y =
    Int_Rep_succ (Int_Rep_add (Int_Rep_nonneg n) y)"
  by (simp add: Int_Rep_add_def)

lemma Int_Rep_neg_succ_add_eq:
  assumes "n : Nat"
  shows "Int_Rep_add (Int_Rep_neg (succ n)) y =
    Int_Rep_pred (Int_Rep_add (Int_Rep_neg n) y)"
  by (simp add: Int_Rep_add_def)

lemma Int_Rep_add_type [type]: "Int_Rep_add : Int_Rep \<Rightarrow> Int_Rep \<Rightarrow> Int_Rep"
proof (intro Dep_fun_typeI)
(*TODO: this should be automatically provable by the type-checker*)
  fix x y assume [type]: "x : Int_Rep" "y : Int_Rep"
  have "(\<lambda>m. nat_rec m y Int_Rep_succ) : Nat \<Rightarrow> Int_Rep"
    by discharge_types
  moreover have "(\<lambda>m. nat_rec m y Int_Rep_pred) : Element (\<nat> \<setminus> {0}) \<Rightarrow> Int_Rep"
  proof -
    {
      fix m assume "m : Element (\<nat> \<setminus> {0})"
      then have "m : Nat" by (auto intro: ElementI dest: ElementD)
    }
    then show ?thesis by discharge_types
  qed
  ultimately show "Int_Rep_add x y : Int_Rep"
    unfolding Int_Rep_add_def Int_Rep_def by discharge_types
qed

lemma Int_Rep_succ_add_eq_succ_add:
  assumes "x : Int_Rep" "y : Int_Rep"
  shows "Int_Rep_add (Int_Rep_succ x) y = Int_Rep_succ (Int_Rep_add x y)"
using \<open>x : Int_Rep\<close>
proof (cases x rule: mem_Int_RepE)
  case (nonneg n)
  then show ?thesis by (simp add: Int_Rep_nonneg_succ_add_eq)
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
      from neg succ have "Int_Rep_add (Int_Rep_succ x) y =
        Int_Rep_add (Int_Rep_succ (Int_Rep_pred (Int_Rep_neg n))) y"
        by simp
      also have "... = Int_Rep_add (Int_Rep_neg n) y"
        by (simp only: Int_Rep_succ_pred_eq)
      also from neg succ have "... = Int_Rep_succ (Int_Rep_add x y)"
        by (simp add: Int_Rep_neg_succ_add_eq)
      finally show ?thesis .
    next
      case True
      with neg succ have "Int_Rep_add (Int_Rep_succ x) y = y"
        using nat_one_def by simp
      also from neg succ True have "... = Int_Rep_succ (Int_Rep_add x y)"
        by (simp add: Int_Rep_neg_succ_add_eq)
      finally show ?thesis by (simp add: Int_Rep_neg_succ_add_eq)
    qed
  qed auto
qed

lemma Int_Rep_inv_add_inv_inv_eq_add [simp]:
  assumes "x : Int_Rep" "y : Int_Rep"
  shows "Int_Rep_inv (Int_Rep_add (Int_Rep_inv x) (Int_Rep_inv y)) =
    Int_Rep_add x y" (is "?lhs = _")
using \<open>x : Int_Rep\<close>
proof (cases x rule: mem_Int_RepE)
  (*we first prove a generalised version for the nonnegative case*)
  {
    fix n y assume "n \<in> \<nat>"
    let ?x = "Int_Rep_nonneg n"
    from \<open>n \<in> \<nat>\<close> have "y : Int_Rep \<Longrightarrow>
      Int_Rep_inv (Int_Rep_add (Int_Rep_inv ?x) (Int_Rep_inv y)) = Int_Rep_add ?x y"
    proof (induction n rule: nat_induct)
      case zero
      then show ?case by (auto simp: Int_Rep_zero_def[symmetric])
    next
      case (succ n)
      then show ?case
      proof (cases n rule: mem_natE)
        case zero
        then show ?thesis unfolding Int_Rep_add_def by simp
      next
        case (succ _)
        have "Int_Rep_inv (
            Int_Rep_add (Int_Rep_inv (Int_Rep_nonneg (succ n))) (Int_Rep_inv y)
          ) = Int_Rep_inv (
            Int_Rep_add (Int_Rep_neg (succ n)) (Int_Rep_inv y)
          )" by simp
        also have "... = Int_Rep_inv (
            Int_Rep_pred (Int_Rep_add (Int_Rep_neg n) (Int_Rep_inv y))
          )"
          by (simp add: Int_Rep_neg_succ_add_eq)
        also have "... = Int_Rep_succ (
            Int_Rep_inv (Int_Rep_add (Int_Rep_neg n) (Int_Rep_inv y))
          )"
        proof -
          (*TODO should be doable by type-checker*)
          have "Int_Rep_add (Int_Rep_neg n) (Int_Rep_inv y) : Int_Rep"
          proof -
            from \<open>n = succ _\<close> have "n : Element (\<nat> \<setminus> {0})" by auto
            then show ?thesis by discharge_types
          qed
          then show ?thesis by (simp only: Int_Rep_succ_inv_eq_inv_pred)
        qed
        also have "... = Int_Rep_succ (
            Int_Rep_inv (Int_Rep_add (Int_Rep_inv (Int_Rep_nonneg n)) (Int_Rep_inv y))
          )"
          using \<open>n = succ _ \<close> by (simp only: Int_Rep_inv_nonneg_eq[OF succ_ne_zero])
        also from succ.IH have
          "... = Int_Rep_succ (Int_Rep_add (Int_Rep_nonneg n) y)" by simp
        also have "... = Int_Rep_add (Int_Rep_nonneg (succ n)) y"
          by (simp only: Int_Rep_nonneg_succ_add_eq)
        finally show ?thesis .
      qed
    qed
  }
  note case_nonneg = this
  { case (nonneg _) then show ?thesis using case_nonneg by simp }
  case (neg n)
  then have "?lhs = Int_Rep_inv (Int_Rep_add (Int_Rep_nonneg n) (Int_Rep_inv y))"
    by simp
  also from case_nonneg[of "n" "Int_Rep_inv y"] have "... = Int_Rep_inv (
      Int_Rep_inv (Int_Rep_add (Int_Rep_inv (Int_Rep_nonneg n)) (Int_Rep_inv (Int_Rep_inv y)))
    )"
    using neg by simp
  also with neg have "... = Int_Rep_add x y" by simp
  finally show ?thesis .
qed

corollary Int_Rep_add_inv_inv_eq_inv_add:
  assumes "x : Int_Rep" "y : Int_Rep"
  shows "Int_Rep_add (Int_Rep_inv x) (Int_Rep_inv y) =
    Int_Rep_inv (Int_Rep_add x y)" (is "?lhs = _")
proof -
  have "?lhs = Int_Rep_inv (Int_Rep_inv (Int_Rep_add (Int_Rep_inv x) (Int_Rep_inv y)))"
    by (simp only: Int_Rep_inv_inv_eq)
  then show ?thesis using Int_Rep_inv_add_inv_inv_eq_add by simp
qed

lemma Int_Rep_pred_add_eq_pred_add:
  assumes "x : Int_Rep" "y : Int_Rep"
  shows "Int_Rep_add (Int_Rep_pred x) y = Int_Rep_pred (Int_Rep_add x y)"
    (is "Int_Rep_add ?x y = ?rhs")
proof -
  have "Int_Rep_add ?x y =
    Int_Rep_inv (Int_Rep_add (Int_Rep_inv ?x) (Int_Rep_inv y))"
    by simp
  also have "... = Int_Rep_inv (Int_Rep_add (Int_Rep_succ (Int_Rep_inv x))
    (Int_Rep_inv y))"
    by (simp only: Int_Rep_succ_inv_eq_inv_pred)
  also have "... = Int_Rep_pred (Int_Rep_inv (Int_Rep_add (Int_Rep_inv x)
    (Int_Rep_inv y)))"
    by (simp only: Int_Rep_succ_add_eq_succ_add Int_Rep_pred_inv_eq_inv_succ)
  also have "... = ?rhs" by simp
  finally show ?thesis .
qed

lemma Int_Rep_add_succ_eq_succ_add:
  assumes "x : Int_Rep" "y : Int_Rep"
  shows "Int_Rep_add x (Int_Rep_succ y) = Int_Rep_succ (Int_Rep_add x y)"
    (is "?lhs = _")
using assms
proof (cases x rule: mem_Int_RepE)
  {
    fix n y assume "n \<in> \<nat>" "y : Int_Rep"
    then have 1: "Int_Rep_add (Int_Rep_nonneg n) (Int_Rep_succ y) =
      Int_Rep_succ (Int_Rep_add (Int_Rep_nonneg n) y)"
    by (induction n rule: nat_induct) (auto simp only:
      Int_Rep_zero_def[symmetric] Int_Rep_nonneg_succ_add_eq Int_Rep_zero_add_eq)
    from \<open>n \<in> \<nat>\<close> have "Int_Rep_add (Int_Rep_nonneg n) (Int_Rep_pred y) =
      Int_Rep_pred (Int_Rep_add (Int_Rep_nonneg n) y)"
    by (induction n rule: nat_induct) (auto simp:
      Int_Rep_zero_def[symmetric] Int_Rep_nonneg_succ_add_eq)
    note 1 this
  }
  note cases_nonneg = this
  { case (nonneg _) then show ?thesis using cases_nonneg by simp }
  case (neg n)
  then have "n \<in> \<nat>" by simp
  from neg have "?lhs = Int_Rep_inv (Int_Rep_add (Int_Rep_nonneg n)
    (Int_Rep_inv (Int_Rep_succ y)))"
    using Int_Rep_inv_add_inv_inv_eq_add[of x "Int_Rep_succ y"] by simp
  also have "... = Int_Rep_inv (Int_Rep_add (Int_Rep_nonneg n)
    (Int_Rep_pred (Int_Rep_inv y)))"
    by (simp only: Int_Rep_pred_inv_eq_inv_succ)
  also have "... = Int_Rep_inv (Int_Rep_pred (Int_Rep_add (Int_Rep_nonneg n)
    (Int_Rep_inv y)))"
    using cases_nonneg by simp
  also have "... = Int_Rep_succ (Int_Rep_inv (Int_Rep_add (Int_Rep_inv (Int_Rep_neg n))
    (Int_Rep_inv y)))"
    using Int_Rep_succ_inv_eq_inv_pred by simp
  also have "... = Int_Rep_succ (Int_Rep_add x y)"
    by (simp only: neg Int_Rep_inv_add_inv_inv_eq_add)
  finally show ?thesis .
qed

lemma Int_Rep_add_pred_eq_pred_add:
  assumes "x : Int_Rep" "y : Int_Rep"
  shows "Int_Rep_add x (Int_Rep_pred y) = Int_Rep_pred (Int_Rep_add x y)"
    (is "Int_Rep_add x ?y = ?rhs")
proof -
  have "Int_Rep_add x ?y =
    Int_Rep_inv (Int_Rep_add (Int_Rep_inv x) (Int_Rep_inv ?y))"
    by simp
  also have "... = Int_Rep_inv (Int_Rep_add (Int_Rep_inv x)
    (Int_Rep_succ (Int_Rep_inv y)))"
    by (simp only: Int_Rep_succ_inv_eq_inv_pred)
  also have "... = Int_Rep_pred (Int_Rep_inv (Int_Rep_add (Int_Rep_inv x)
    (Int_Rep_inv y)))"
    by (simp only: Int_Rep_add_succ_eq_succ_add Int_Rep_pred_inv_eq_inv_succ)
  also have "... = ?rhs" by simp
  finally show ?thesis .
qed

lemma Int_Rep_nonneg_add_nonneg_eq [simp]:
  assumes "n : Nat"
  shows "Int_Rep_add (Int_Rep_nonneg n) (Int_Rep_nonneg m) = Int_Rep_nonneg (n + m)"
  using assms by (induction n rule: Nat_induct)
  (auto simp: Int_Rep_zero_def[symmetric] Int_Rep_succ_add_eq_succ_add
    Int_Rep_nonneg_succ_add_eq)

lemma Int_Rep_neg_add_neg_eq [simp]:
  assumes "n : Nat"
  shows "Int_Rep_add (Int_Rep_neg n) (Int_Rep_neg m) = Int_Rep_neg (n + m)"
  using assms by (induction n rule: Nat_induct)
  (auto simp: Int_Rep_neg_succ_add_eq)

(*TODO: we could add more lemmas like the two above and simplify some proofs(?)*)
lemma Int_Rep_nonneg_add_neg_eq [simp]:
  assumes "n : Nat" "m : Nat"
  and "m \<noteq> 0"
  and "n < m"
  shows "Int_Rep_add (Int_Rep_nonneg n) (Int_Rep_neg m) = Int_Rep_neg (m - n)"
  (* using assms by (induction n rule: Nat_induct)
  (auto simp: Int_Rep_zero_def[symmetric] Int_Rep_nonneg_succ_add_eq) *)
oops

lemma Int_Rep_nonneg_add_neg_eq [simp]:
  assumes "n : Nat"
  and "m \<noteq> 0"
  and "m \<le> n"
  shows "Int_Rep_add (Int_Rep_nonneg n) (Int_Rep_neg m) = Int_Rep_nonneg (n - m)"
  (* using assms by (induction n rule: Nat_induct)
  (auto simp: Int_Rep_zero_def[symmetric] Int_Rep_nonneg_succ_add_eq) *)
oops

lemma Int_Rep_add_zero_eq [simp]:
  assumes "x : Int_Rep"
  shows "Int_Rep_add x Int_Rep_zero = x"
using assms
proof (cases x rule: mem_Int_RepE)
  let ?z = Int_Rep_zero
  {
    fix n assume "n \<in> \<nat>"
    then have "Int_Rep_add (Int_Rep_nonneg n) ?z = Int_Rep_nonneg n"
    proof (induction n rule: nat_induct)
      case (succ n)
      have "Int_Rep_add (Int_Rep_nonneg (succ n)) ?z =
        Int_Rep_succ (Int_Rep_add (Int_Rep_nonneg n) ?z)"
        by (simp only: Int_Rep_nonneg_succ_add_eq)
      also from succ.IH have "... = Int_Rep_succ (Int_Rep_nonneg n)" by simp
      also have "... = Int_Rep_nonneg (succ n)" by simp
      finally show ?case .
    qed (simp add: Int_Rep_add_def Int_Rep_zero_def)
  }
  note case_nonneg = this
  { case (nonneg _) then show ?thesis using case_nonneg by simp }
  case (neg n)
  then have "Int_Rep_add x ?z = Int_Rep_inv (Int_Rep_add (Int_Rep_nonneg n) ?z)"
    using Int_Rep_inv_add_inv_inv_eq_add[of x ?z] by simp
  with neg case_nonneg show ?thesis by simp
qed

lemma Int_Rep_add_assoc:
  assumes "x : Int_Rep" "y : Int_Rep" "z : Int_Rep"
  shows "Int_Rep_add (Int_Rep_add x y) z = Int_Rep_add x (Int_Rep_add y z)"
using \<open>x : Int_Rep\<close>
proof (cases x rule: mem_Int_RepE)
  {
    fix n y z assume "n \<in> \<nat>" "y : Int_Rep" "z : Int_Rep"
    then have "Int_Rep_add (Int_Rep_add (Int_Rep_nonneg n) y) z =
      Int_Rep_add (Int_Rep_nonneg n) (Int_Rep_add y z)"
    proof (induction n arbitrary: y z rule: nat_induct)
      case zero
      then show ?case by (simp add: Int_Rep_zero_def[symmetric])
    next
      case (succ n)
      then have "Int_Rep_add (Int_Rep_add (Int_Rep_nonneg (succ n)) y) z =
        Int_Rep_add (Int_Rep_succ (Int_Rep_add (Int_Rep_nonneg n) y)) z"
        by (simp add: Int_Rep_nonneg_succ_add_eq)
      also have
        "... = Int_Rep_succ (Int_Rep_add (Int_Rep_add (Int_Rep_nonneg n) y) z)"
        by (simp only: Int_Rep_succ_add_eq_succ_add)
      also from succ.IH have
        "... = Int_Rep_succ (Int_Rep_add (Int_Rep_nonneg n) (Int_Rep_add y z))"
        by simp
      also from Int_Rep_nonneg_succ_add_eq have
        "... = Int_Rep_add (Int_Rep_nonneg (succ n)) (Int_Rep_add y z)"
        by simp
      finally show ?case .
    qed
  }
  note case_nonneg = this
  { case (nonneg _) then show ?thesis using case_nonneg by simp }
  case (neg n)
  have "Int_Rep_add (Int_Rep_add x y) z =
    Int_Rep_inv (Int_Rep_add (Int_Rep_inv (Int_Rep_add x y)) (Int_Rep_inv z))"
    by simp
  also have
    "... = Int_Rep_inv (
      Int_Rep_add (Int_Rep_inv (Int_Rep_add (Int_Rep_inv (Int_Rep_inv x))
      (Int_Rep_inv (Int_Rep_inv y)))) (Int_Rep_inv z))"
    by simp
  also have "... = Int_Rep_inv (
      Int_Rep_add (Int_Rep_add (Int_Rep_inv x) (Int_Rep_inv y)) (Int_Rep_inv z))"
    by (simp only: Int_Rep_inv_add_inv_inv_eq_add)
  also from neg case_nonneg have "... = Int_Rep_inv (
      Int_Rep_add (Int_Rep_nonneg n) (Int_Rep_add (Int_Rep_inv y) (Int_Rep_inv z))
    )"
    by simp
  also from neg have "... = Int_Rep_inv (
      Int_Rep_add (Int_Rep_inv x) (Int_Rep_inv (Int_Rep_add y z))
    )"
    by (simp add: Int_Rep_add_inv_inv_eq_inv_add)
  also have "... = Int_Rep_add x (Int_Rep_add y z)"
    by (simp add: Int_Rep_add_inv_inv_eq_inv_add)
  finally show ?thesis .
qed

lemma Int_Rep_add_comm:
  assumes "x : Int_Rep" "y : Int_Rep"
  shows "Int_Rep_add x y = Int_Rep_add y x"
using \<open>x : Int_Rep\<close>
proof (cases x rule: mem_Int_RepE)
  {
    fix n y assume "n \<in> \<nat>" "y : Int_Rep"
    then have "Int_Rep_add (Int_Rep_nonneg n) y = Int_Rep_add y (Int_Rep_nonneg n)"
    by (induction n rule: nat_induct)
      (auto simp add: Int_Rep_nonneg_succ_add_eq Int_Rep_zero_def[symmetric]
        Int_Rep_add_succ_eq_succ_add[symmetric])
  }
  note case_nonneg = this
  { case (nonneg _) then show ?thesis using case_nonneg by simp }
  case (neg n)
  then have "Int_Rep_add x y =
    Int_Rep_inv (Int_Rep_add (Int_Rep_nonneg n) (Int_Rep_inv y))"
    using Int_Rep_inv_add_inv_inv_eq_add[of x y] by simp
  also from neg case_nonneg have
    "... = Int_Rep_inv (Int_Rep_add (Int_Rep_inv y) (Int_Rep_inv (Int_Rep_neg n)))"
    by simp
  also from neg have "... = Int_Rep_add y x"
    by (simp only: Int_Rep_add_inv_inv_eq_inv_add Int_Rep_inv_inv_eq)
  finally show ?thesis .
qed

definition "Int_Rep_sub x y \<equiv> Int_Rep_add x (Int_Rep_inv y)"

lemma Int_Rep_sub_type [type]:
  "Int_Rep_sub : Int_Rep \<Rightarrow> Int_Rep \<Rightarrow> Int_Rep"
  unfolding Int_Rep_sub_def by discharge_types


end