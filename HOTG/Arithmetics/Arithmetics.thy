theory Arithmetics
  imports
    Set_Add
    Replacement
    Less_Than
    Mem_transitive_Closure
begin

paragraph \<open>Summary\<close>
text \<open>Translation of generalised arithmetics from
\<^url>\<open>https://www.isa-afp.org/entries/ZFC_in_HOL.html\<close>.\<close>


paragraph \<open>Multiplication\<close>

definition "mul X \<equiv> transrec (\<lambda>mulX Y. \<Union>(image (\<lambda>y. lift (mulX y) X) Y))"

bundle hotg_mul_syntax begin notation mul (infixl "*" 70) end
bundle no_hotg_mul_syntax begin no_notation mul (infixl "*" 70) end
unbundle hotg_mul_syntax

lemma mul_eq_idx_union_lift_mul: "X * Y = (\<Union>y \<in> Y. lift (X * y) X)"
  by (auto simp: mul_def transrec_eq)

lemma mul_zero_eq_zero [simp]: "X * 0 = 0"
  by (subst mul_eq_idx_union_lift_mul) simp

lemma mul_one_eq_self [simp]: "X * 1 = X"
  by (auto simp: mul_eq_idx_union_lift_mul[of _ 1])

lemma mul_singleton_one_eq_lift_self: "X * {1} = lift X X"
  by (auto simp: mul_eq_idx_union_lift_mul[where ?Y="{1}"])

lemma mul_two_eq_add_self: "X * 2 = X + X"
proof -
  have "X * 2 = (\<Union>y \<in> 2. lift (X * y) X)" by (simp only: mul_eq_idx_union_lift_mul[where ?Y=2])
  also have "... = lift (X * 1) X \<union> lift (X * 0) X" by blast
  also have "... = X + X" by (auto simp: add_eq_bin_union_lift)
  finally show ?thesis .
qed

lemma mul_bin_union_eq_bin_union_mul: "X * (Y \<union> Z) = (X * Y) \<union> (X * Z)"
proof -
  have "X * (Y \<union> Z) = (\<Union>y \<in> (Y \<union> Z). lift (X * y) X)" by (subst mul_eq_idx_union_lift_mul) simp
  also have "... = (\<Union>y \<in> Y. lift (X * y) X) \<union> (\<Union>z \<in> Z. lift (X * z) X)" by blast
  also have "... = (X * Y) \<union> (X * Z)" by (simp flip: mul_eq_idx_union_lift_mul)
  finally show ?thesis .
qed

lemma mul_insert_eq_mul_bin_union_lift_mul: "X * (insert Z Y) = (X * Y) \<union> lift (X * Z) X"
proof -
  have "X * (insert Z Y) = X * (Y \<union> {Z})" by auto
  also have "... = (X * Y) \<union> (X * {Z})" by (simp only: mul_bin_union_eq_bin_union_mul)
  also have "... = (X * Y) \<union> lift (X * Z) X" by (auto simp: mul_eq_idx_union_lift_mul[of _ "{Z}"])
  finally show ?thesis .
qed

lemma mul_succ_eq_mul_add [simp]: "X * succ Y = X * Y + X"
proof -
  have "X * succ Y = X * (insert Y Y)"
    by (simp only: insert_self_eq_add_one[where ?X = Y] succ_eq_add_one)
  also have "... = (X * Y) \<union> lift (X * Y) X" by (simp only: mul_insert_eq_mul_bin_union_lift_mul)
  also have " ... = (X * Y) + X" by (simp add: add_eq_bin_union_lift)
  finally show ?thesis .
qed

lemma zero_mul_eq_zero [simp]: "0 * X = 0"
  by (induction X, subst mul_eq_idx_union_lift_mul) auto

lemma one_mul_eq_one [simp]: "1 * X = X"
proof (induction X)
  case (mem x)
  then show ?case by (auto simp: mul_eq_idx_union_lift_mul[where ?Y = x])
qed

lemma mul_union_eq_idx_union_mul: "X * \<Union>Y = (\<Union>y \<in> Y. X * y)"
proof -
  have "X * \<Union>Y = (\<Union>y \<in> Y. \<Union>z \<in> y. lift (X * z) X)" by (subst mul_eq_idx_union_lift_mul) simp
  also have "... = (\<Union>y \<in> Y. X * y)" by (simp flip: mul_eq_idx_union_lift_mul)
  finally show ?thesis .
qed

lemma mul_lift_eq_lift_mul_mul: "X * (lift Y Z) = lift (X * Y) (X * Z)"
proof (induction Z rule: mem_induction)
  case (mem Z)
  have "X * (lift Y Z) = (\<Union>z \<in> lift Y Z. lift (X * z) X)"
    by (subst mul_eq_idx_union_lift_mul) simp
  also have "... = (\<Union>z \<in> Z. lift (X * (Y + z)) X)" by (simp add: lift_eq_image_add)
  also from mem have "... = lift (X * Y) (\<Union>z \<in> Z. lift (X * z) X)"
    by (simp add: add_eq_bin_union_lift lift_union_eq_idx_union_lift lift_lift_eq_lift_add
      mul_bin_union_eq_bin_union_mul)
  also have "... = lift (X * Y) (X * Z)" by (simp flip: mul_eq_idx_union_lift_mul)
  finally show ?case .
qed

lemma mul_add_eq_mul_add_mul: "X * (Y + Z) = X * Y + X * Z"
  by (simp only: add_eq_bin_union_lift mul_bin_union_eq_bin_union_mul mul_lift_eq_lift_mul_mul)

lemma mul_assoc: "(X * Y) * Z = X * (Y * Z)"
proof (induction Z rule: mem_induction)
  case (mem Z)
  have "(X * Y) * Z = (\<Union>z \<in> Z. lift ((X * Y) * z) (X * Y))"
    by (subst mul_eq_idx_union_lift_mul) simp
  also have "... = (\<Union>z \<in> Z. X * lift(Y * z) Y)" by (simp add: mem mul_lift_eq_lift_mul_mul)
  also have "... = X * (\<Union>z \<in> Z. lift(Y * z) Y)" by (simp add: mul_union_eq_idx_union_mul)
  also have "... = X * (Y * Z)" by (simp flip: mul_eq_idx_union_lift_mul)
  finally show ?case .
qed

lemma le_self_add: "X \<le> X + Y"
proof (subst le_iff_mem_trans_closure_or_eq)
  show "X \<in> mem_trans_closure (X + Y) \<or> X = (X + Y)"
  proof (cases "Y = 0")
    case False
    then have "X \<in> mem_trans_closure (X + Y)"
    proof (induction Y)
      case (mem Y)
      then show ?case 
      proof (cases"0 \<in> Y")
        case True
        have "X \<in> X + Y"
          using True by (subst add_eq_bin_union_repl_add) auto
        then show ?thesis 
          by (auto simp: mem_mem_trans_closure_if_mem)
      next
        case False
        have "\<exists>y \<in> Y. y \<noteq> 0" using False \<open>Y \<noteq> 0\<close> sorry
        then obtain y where sub:"y \<in> Y" "y \<noteq> 0" "X \<in> mem_trans_closure (X + y)" using mem by blast
        have "X + y \<in> X + Y"
          using sub by (subst add_eq_bin_union_repl_add) auto
        then show ?thesis using sub by (auto simp: mem_mem_trans_closure_trans  mem_mem_trans_closure_if_mem)
      qed
    qed
    then show ?thesis by auto
  qed auto
qed

lemma le_mul_if_ne_zero:
  assumes "Y \<noteq> 0"
  shows "X \<le> X * Y"
proof (cases "X = 0")
  case False
  (*Note Fang: you have to pass the assumption about Y to the induction (otherwise, you won't
    be able to use it for the new Y in the mem case below*)
  from assms show ?thesis
  proof (induction Y rule: mem_induction)
    case (mem Y)
    then show ?case
    proof (cases "Y = 1")
      case False
      with mem obtain P where P: "P \<in> Y" "P \<noteq> 0" by (auto 5 0)
      from \<open>X \<noteq> 0\<close> obtain R where R: "R \<in> X" by auto
      from mem.IH have "X \<le> X * P" using P by auto
      also have "... \<le> X * P + R" by (auto simp: le_self_add)
      also have "... \<le> X * Y"
      proof -
        from R have "X * P + R \<in> lift (X * P) X" by (auto simp: lift_eq_image_add)
        moreover have "... \<subseteq> X * Y"
          using P by (auto simp: mul_eq_idx_union_lift_mul[of _ Y])
        ultimately show ?thesis
          by (auto simp: le_iff_mem_trans_closure_or_eq mem_mem_trans_closure_if_mem)
      qed
      finally show ?thesis .
    qed (auto simp: le_iff_mem_trans_closure_or_eq)
  qed
qed (auto simp: le_iff_mem_trans_closure_or_eq)

lemma sevenn: assumes "R < A" "S < A" "A * X + R \<subseteq> A * Y + S"
  shows "X \<subseteq> Y"
  sorry

lemma seven: assumes "R < A" "S < A" "A * X + R = A * Y + S"
  shows "X = Y" "R = S"
  sorry

lemma bin_inter_lift_mul_mem_trans_closure_lift_mul_mem_trans_closure_eq_zero:
  assumes "X \<noteq> Y"
  shows "lift (A * X) (mem_trans_closure A) \<inter> lift (A * Y) (mem_trans_closure A) = 0"
  (is "?s1 \<inter> ?s2 = 0")
proof (rule eqI)
  fix x assume asm: "x \<in> ?s1 \<inter> ?s2"
  then obtain r where R: "x = A * X + r" "r \<in> mem_trans_closure A"
    using lift_eq_repl_add by auto
  from asm obtain rr where RR: "x = A * Y + rr" "rr \<in> mem_trans_closure A"
    using lift_eq_repl_add by auto
  with R have "A * X + r = A * Y + rr" "r < A" "rr < A" by (auto simp: lt_iff_mem_trans_closure)
  then have "X = Y" "r = rr" using seven[of r _ rr X _] by auto
  then show "x \<in> 0" by (simp add: assms)
qed simp


end
