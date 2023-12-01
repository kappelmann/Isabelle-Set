theory Arithmetics
  imports
    Set_Add
    Replacement
    Less_Than
begin

paragraph \<open>Summary\<close>
text \<open>Translation of generalised arithmetics from
\<^url>\<open>https://www.isa-afp.org/entries/ZFC_in_HOL.html\<close>.\<close>


paragraph\<open>Multiplication\<close>

definition "mul X \<equiv> transrec (\<lambda>mulX Y. \<Union>(image (\<lambda>y. lift (mulX y) X) Y))"

bundle hotg_mul_syntax begin notation mul (infixl "*" 70) end
bundle no_hotg_mul_syntax begin no_notation mul (infixl "*" 70) end
unbundle hotg_mul_syntax

lemma mul_eq_union_repl_lift_mul: "X * Y = \<Union>{lift (X * y) X | y \<in> Y}"
  by (auto simp:mul_def transrec_eq)

lemma elts_multE:
  assumes "z \<in> (X * Y)"
  obtains u v where "u \<in> X" "v \<in> Y" "z = X * v + u"
 using mul_eq_union_repl_lift_mul[of X Y] assms lift_eq_image_add by auto

lemma mul_zero_eq_zero [simp]: "x * 0 = 0"
  unfolding mul_def by (auto simp: transrec_eq)

lemma mul_one_eq_self [simp]: "x * 1 = x"
  by (fastforce simp: mul_eq_union_repl_lift_mul[of _ 1])

lemma mul_singleton_one_eq_lift_self: "X * {1} = lift X X"
proof-
  have "X * {1} = \<Union>{lift (X * y) X | y \<in> {1}}"
    by (simp only: mul_eq_union_repl_lift_mul[where ?Y="{1}"])
  also have "... = \<Union>{lift (X * 1) X }" by auto
  also have "... = lift X X" by auto
  finally show ?thesis .
qed

lemma mul_two_eq_add: "X * 2 = X + X"
proof -
  have "X * 2 = \<Union>{lift (X * y) X | y \<in> 2}"
    by (simp only: mul_eq_union_repl_lift_mul[where ?Y=2])
  also have "... = (lift (X * 1) X) \<union> (lift (X * 0) X)" by blast
  also have "... = X + X" by (auto simp: add_eq_bin_union_lift)
  finally show ?thesis .
qed

lemma mul_bin_union_eq_bin_union_mul: "X * (Y \<union> Z) = (X * Y) \<union> (X * Z)"
proof-
  have "X * (Y \<union> Z) = \<Union>{lift (X * y) X | y \<in> (Y \<union> Z)}"
    by (subst mul_eq_union_repl_lift_mul) simp
  also have "... = \<Union>{lift (X * y) X | y \<in> Y} \<union> \<Union>{lift (X * y) X | y \<in> Z}" by blast
  also have "... = (X * Y) \<union> (X * Z)" by (simp flip: mul_eq_union_repl_lift_mul)
  finally show ?thesis .
qed

lemma mul_insert_eq_mul_bin_union_lift_mul:
  "X * (insert Z Y) = (X * Y) \<union> lift (X * Z) X"
proof -
  have mul_set:"X * {Z} = lift (X * Z) X"
    by (auto simp: mul_eq_union_repl_lift_mul[of _ "{Z}"])
  have "X * (insert Z Y) = X * (Y \<union> {Z})" by auto
  also have "... = (X * Y) \<union> (X * {Z})"
    by (simp only: mul_bin_union_eq_bin_union_mul[of _ _ "{Z}"])
  also have "... = (X * Y) \<union> lift (X * Z) X"
    by (auto simp: mul_set)
  finally show "X * (insert Z Y) = (X * Y) \<union> lift (X * Z) X" .
qed

lemma mul_add_one_eq_mul_add [simp]:
  "X * (Y + 1) = X * Y + X"
proof -
  have "X * (Y + 1) = X * (insert Y Y)" by (simp only: insert_self_eq_add_one[where ?X = Y])
  also have "... = (X * Y) \<union> lift (X * Y) X" by (simp only: mul_insert_eq_mul_bin_union_lift_mul)
  also have " ... = (X * Y) + X" by (simp add: add_eq_bin_union_lift)
  finally show ?thesis .
qed

lemma zero_mul_eq_zero [simp]: "0 * X = 0"
  by (induction X, subst mul_eq_union_repl_lift_mul) auto

lemma one_mul_eq_one [simp]: "1 * X = X"
proof (induction X)
  case (mem x)
  then show ?case by (auto simp: mul_eq_union_repl_lift_mul[where ?Y = x])
qed

lemma union_repl_distri: 
  shows "{f x | x \<in> \<Union>X} = \<Union>(repl X (\<lambda>Y. {f x | x \<in> Y})) "
  sorry

lemma mul_union_eq_union_mul: "X * \<Union>Y = \<Union>(repl Y ((*) X))"
proof-
  have 1:"(\<lambda>Y. \<Union>{lift (X * y) X | y \<in> Y})  = (\<lambda>Y. (*) X Y)"
    by (subst mul_eq_union_repl_lift_mul) auto
  then have 2: "repl Y (\<lambda>Y. \<Union>{lift (X * y) X | y \<in> Y})  = repl Y (\<lambda>Y. (*) X Y)"
    by (auto simp: arg_cong[of "(\<lambda>Y. \<Union>{lift (X * y) X | y \<in> Y})" "(*) X"])
  have "X * (\<Union>Y) = \<Union>{lift (X * y) X | y \<in> (\<Union>Y)}"
    by (subst mul_eq_union_repl_lift_mul) auto
  also have "... = \<Union>(repl Y (\<lambda>Y. \<Union>{lift (X * y) X | y \<in> Y}))"
    by (auto simp: union_repl_distri)
  also have "... = \<Union>(repl Y ((*) X))"
    by (auto simp: 2 arg_cong[of "(repl Y (\<lambda>Y. \<Union>{lift (X * y) X | y \<in> Y}))" "(repl Y ((*) X))"])
  finally show ?thesis .
qed

lemma mul_lift_eq_lift_mul_mul: "X * (lift Y Z) = lift (X * Y) (X * Z)"
proof(induction Z rule:mem_induction)
  case (mem Z)
  have sub:"\<Union>{lift (X * (Y + z)) X | z \<in> Z} = \<Union>{lift (X * Y + X * z) X| z \<in> Z }"
    by (auto simp: mem add_eq_bin_union_lift  mul_bin_union_eq_bin_union_mul)
  have "X * (lift Y Z) = \<Union>{lift (X * z) X | z \<in> (lift Y Z)}"
    by (subst mul_eq_union_repl_lift_mul) auto
  also have "... = \<Union>{lift (X * (Y + z)) X | z \<in> Z}"
    by (simp add: lift_eq_image_add)
  also have "... = lift (X * Y) (\<Union>{ lift  (X * z) X  | z \<in> Z})"
    by (auto simp: sub lift_union_eq_union_repl_lift lift_lift_eq_lift_add)
  also have "... = lift (X * Y) (X * Z)"
    by (subst mul_eq_union_repl_lift_mul) auto
  finally show ?case .
qed

lemma mul_lift_distrib: "X * (Y + Z) = X * Y + X * Z"
  by (auto simp: add_eq_bin_union_lift  mul_bin_union_eq_bin_union_mul mul_lift_eq_lift_mul_mul)

lemma mul_assoc: "(X * Y) * Z = X * (Y * Z)"
proof(induction Z rule:mem_induction)
  case (mem Z)
  have "(X * Y) * Z = \<Union>{lift ((X * Y) * z) (X * Y) | z \<in> Z}"
    by (subst mul_eq_union_repl_lift_mul) auto
  also have "... = \<Union>{X * lift(Y * z) Y | z \<in> Z}"
    by (auto simp: mem mul_lift_eq_lift_mul_mul)
  also have "... = X * \<Union>{lift(Y * z) Y | z \<in> Z}"
    by (auto simp: mul_union_eq_union_mul)
  also have "... = X * (Y * Z)"
    by (subst mul_eq_union_repl_lift_mul) auto
  finally show ?case .
qed

lemma le_add: "X \<le> X + Y"
proof-
  have "X \<in> mem_trans_closure (X + Y) \<or> X = (X + Y)" 
  proof(cases "Y = 0")
    case False
    then show ?thesis sorry
  qed auto
  then show ?thesis by (simp add: le_iff_mem_trans_closure_or_eq)
qed

lemma le_mul_if_not_zero: assumes "Y \<noteq> 0"  
  shows "X \<le> X * Y"
proof (cases "X = 0")
  case False
  then show ?thesis  
  proof (induction Y rule:mem_induction)
    case (mem Y)
    then show ?case
    proof (cases "Y = 1")
      case False
      obtain P where P: "P \<in> Y"  "P \<noteq> 0" 
        sorry
      have ineq_1:"X \<le> X * P" using P mem by auto
      obtain R where R: "R \<in> X" using \<open>X \<noteq> 0\<close> by auto
      then have "X * P + R \<in> lift (X * P) X"
        by (auto simp: lift_eq_image_add)
      moreover  have "lift (X * P) X \<subseteq> X * Y"
        using P(1) by (auto simp:mul_eq_union_repl_lift_mul[of _ Y])
      ultimately have ineq_3:"X * P + R \<le> X * Y"
        by (auto simp: le_iff_mem_trans_closure_or_eq mem_mem_trans_closure_if_mem)
      moreover have ineq_2:"X * P \<le> X * P + R"
        by (auto simp: le_add)
      then show ?thesis 
        using ineq_1 ineq_2 ineq_3 le_TC_trans by blast
    qed (auto simp:le_iff_mem_trans_closure_or_eq)
  qed
qed (auto simp:le_iff_mem_trans_closure_or_eq)

lemma sevenn: assumes "R < A" "S < A" "A * X + R \<subseteq> A * Y + S"
  shows "X \<subseteq> Y"
  sorry

lemma seven: assumes "R < A" "S < A" "A * X + R = A * Y + S"
  shows "X = Y" "R = S"
  sorry

lemma bin_inter_lift_mul_TC_lift_mul_TC_eq_zero:
  assumes "X \<noteq> Y"
  shows "lift (A * X) (mem_trans_closure A) \<inter> lift (A * Y) (mem_trans_closure A) = 0"
proof -
  have "lift (A * X) (mem_trans_closure A) \<inter> lift (A * Y) (mem_trans_closure A) \<subseteq> 0"
  proof(rule subsetI)
    have 1:"lift (A * X) (mem_trans_closure A) = {A * X + r | r \<in> mem_trans_closure A}"
           "lift (A * Y) (mem_trans_closure A) = {A * Y + r | r \<in> mem_trans_closure A}"
      by (auto simp: lift_eq_repl_add)
    fix x assume "x \<in> lift (A * X) (mem_trans_closure A) \<inter> lift (A * Y) (mem_trans_closure A)"
    then have 2:"x \<in> lift (A * X) (mem_trans_closure A)" "x \<in> lift (A * Y) (mem_trans_closure A)" by auto
    then obtain r where R:"x = A * X + r" "A * X + r \<in> lift (A * X) (mem_trans_closure A)" "r \<in> mem_trans_closure A"
      using 1 by auto
    then obtain rr where RR:"x = A * Y + rr" "A * Y + rr \<in> lift (A * Y) (mem_trans_closure A)" "rr \<in> mem_trans_closure A"
      using 1 2 by auto
    with R have "A * X + r = A * Y + rr" "r < A" "rr < A" 
      by (auto simp:lt_iff_mem_trans_closure  lift_eq_repl_add)
    then have "X = Y" "r = rr" using seven[of r _ rr X _]  by auto
    then show "x \<in> 0" by (simp add:assms)
  qed
  then show ?thesis by simp
qed


end
