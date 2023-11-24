theory Arithmetics
  imports
    Set_Add
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

lemma mul_insert_eq_mul_bin_union_lift_mul:
  "X * (insert Z Y) = (X * Y) \<union> lift (X * Z) X"
  sorry

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

lemma mul_bin_union_eq_bin_union_mul: "X * (Y \<union> Z) = (X * Y) \<union> (X * Z)"
proof-
  have "X * (Y \<union> Z) = \<Union>{lift (X * y) X | y \<in> (Y \<union> Z)}"
    by (subst mul_eq_union_repl_lift_mul) simp
  also have "... = \<Union>{lift (X * y) X | y \<in> Y} \<union> \<Union>{lift (X * y) X | y \<in> Z}" by blast
  also have "... = (X * Y) \<union> (X * Z)" by (simp flip: mul_eq_union_repl_lift_mul)
  finally show ?thesis .
qed

lemma mul_union_eq_union_mul: "X * \<Union>Y = \<Union>(X * Y)"
proof-
  have "X * (\<Union>Y) = \<Union>{lift (X * y) X | y \<in> (\<Union>Y)}"
    by (subst mul_eq_union_repl_lift_mul) auto
  also have "... = \<Union>\<Union>{lift (X * y) X | y \<in> Y}"
    sorry
  also have "... = \<Union>(X * Y)"
    by (subst mul_eq_union_repl_lift_mul) auto
  finally show ?thesis .
qed

lemma unfolding_mul_union_eq_union_mul:
  "\<Union>{X * lift(Y * z) Y | z \<in> Z} = X * \<Union>{lift(Y * z) Y | z \<in> Z}"
  sorry

lemma mul_lift_eq_lift_mul_mul: "X * (lift Y Z) = lift (X * Y) (X * Z)"
proof(induction Z rule:mem_induction)
  case (mem Z)
  have "X * (lift Y Z) = \<Union>{lift (X * z) X | z \<in> (lift Y Z)}"
    by (subst mul_eq_union_repl_lift_mul) auto
  also have "... = \<Union>{lift (X * (Y + z)) X | z \<in> Z}"
    sorry
  also have "... = \<Union>{lift (X * Y + X * z) X | z \<in> Z}"
    sorry
  also have "... = lift (X * Y) (\<Union>{ lift  (X * z) X  | z \<in> Z})"
    by (auto simp: lift_union_eq_union_repl_lift lift_lift_eq_lift_add)
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
    by (auto simp: unfolding_mul_union_eq_union_mul)
  also have "... = X * (Y * Z)"
    by (subst mul_eq_union_repl_lift_mul) auto
  finally show ?case .
qed

end
