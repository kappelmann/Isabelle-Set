\<^marker>\<open>creator "Linghan Fang"\<close>
\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Generalised Multiplication\<close>
theory SMultiplication
  imports
    SAddition
begin

paragraph \<open>Summary\<close>
text \<open>Translation of generalised set multiplication for sets from \<^cite>\<open>kirby_set_arithemtics\<close>
and \<^cite>\<open>ZFC_in_HOL_AFP\<close>. Note that general set multiplication is associative,
but it is not commutative (not proven here).\<close>

definition "mul X \<equiv> transrec (\<lambda>mulX Y. \<Union>(image (\<lambda>y. lift (mulX y) X) Y))"

bundle hotg_mul_syntax begin notation mul (infixl "*" 70) end
bundle no_hotg_mul_syntax begin no_notation mul (infixl "*" 70) end
unbundle hotg_mul_syntax

lemma mul_eq_idx_union_lift_mul: "X * Y = (\<Union>y \<in> Y. lift (X * y) X)"
  by (simp add: mul_def transrec_eq)

corollary mul_eq_idx_union_repl_mul_add: "X * Y = (\<Union>y \<in> Y. {X * y + x | x \<in> X})"
  using mul_eq_idx_union_lift_mul[of X Y] lift_eq_repl_add by simp

paragraph\<open>Lemma 4.2 from \<^cite>\<open>kirby_set_arithemtics\<close>\<close>

lemma mul_zero_eq_zero [simp]: "X * 0 = 0"
  by (subst mul_eq_idx_union_lift_mul) simp

text\<open>\<open>1\<close> is the right identity of set multiplication.\<close>

lemma mul_one_eq_self [simp]: "X * 1 = X"
  by (subst mul_eq_idx_union_lift_mul) (auto simp: succ_eq_insert_self)

lemma mul_singleton_one_eq_lift_self: "X * {1} = lift X X"
  by (auto simp: mul_eq_idx_union_lift_mul[where ?Y="{1}"])

lemma mul_two_eq_add_self: "X * 2 = X + X"
proof -
  have "X * 2 = (\<Union>y \<in> 2. lift (X * y) X)" by (simp only: mul_eq_idx_union_lift_mul[where ?Y=2])
  also have "... = lift (X * 1) X \<union> lift (X * 0) X"
    using idx_union_insert_dom_eq_bin_union_idx_union by (auto simp: succ_eq_insert_self)
  also have "... = X + X" by (auto simp: add_eq_bin_union_lift)
  finally show ?thesis .
qed

lemma mul_bin_union_eq_bin_union_mul: "X * (Y \<union> Z) = (X * Y) \<union> (X * Z)"
proof -
  have "X * (Y \<union> Z) = (\<Union>y \<in> (Y \<union> Z). lift (X * y) X)" by (simp flip: mul_eq_idx_union_lift_mul)
  also have "... = (\<Union>y \<in> Y. lift (X * y) X) \<union> (\<Union>z \<in> Z. lift (X * z) X)"
    using idx_union_bin_union_dom_eq_bin_union_idx_union by simp
  also have "... = (X * Y) \<union> (X * Z)" by (auto simp flip: mul_eq_idx_union_lift_mul)
  finally show ?thesis .
qed

lemma mul_insert_eq_mul_bin_union_lift_mul: "X * (insert Z Y) = (X * Y) \<union> lift (X * Z) X"
proof -
  have "X * (insert Z Y) = X * (Y \<union> {Z})" by auto
  also have "... = (X * Y) \<union> (X * {Z})" by (simp only: mul_bin_union_eq_bin_union_mul)
  also have "... = (X * Y) \<union> lift (X * Z) X" by (auto simp: mul_eq_idx_union_lift_mul[where ?Y="{Z}"])
  finally show ?thesis .
qed

lemma mul_succ_eq_mul_add [simp]: "X * succ Y = X * Y + X"
proof -
  have "X * succ Y = X * (insert Y Y)"
    by (simp only: insert_self_eq_add_one[where ?X = Y] succ_eq_insert_self)
  also have "... = (X * Y) \<union> lift (X * Y) X" by (simp only: mul_insert_eq_mul_bin_union_lift_mul)
  also have " ... = (X * Y) + X" by (simp add: add_eq_bin_union_lift)
  finally show ?thesis .
qed

lemma subset_self_mul_if_zero_mem:
  assumes "0 \<in> X"
  shows "Y \<subseteq> Y * X"
  using assms by (subst mul_eq_idx_union_lift_mul) fastforce


paragraph\<open>Proposition 4.3 from \<^cite>\<open>kirby_set_arithemtics\<close>\<close>

lemma zero_mul_eq_zero [simp]: "0 * X = 0"
  by (induction X, subst mul_eq_idx_union_lift_mul) auto

text\<open>\<open>1\<close> is also the left identity of set multiplication.\<close>

lemma one_mul_eq [simp]: "1 * X = X"
  by (induction X, subst mul_eq_idx_union_lift_mul) auto

lemma mul_union_eq_idx_union_mul: "X * \<Union>Y = (\<Union>y \<in> Y. X * y)"
proof -
  have "X * \<Union>Y = (\<Union>y \<in> Y. \<Union>z \<in> y. lift (X * z) X)" by (subst mul_eq_idx_union_lift_mul) simp
  also have "... = (\<Union>y \<in> Y. X * y)" by (simp flip: mul_eq_idx_union_lift_mul)
  finally show ?thesis .
qed

lemma mul_lift_eq_lift_mul_mul: "X * (lift Y Z) = lift (X * Y) (X * Z)"
proof (induction Z rule: mem_induction)
  case (mem Z)
  have "X * (lift Y Z) = (\<Union>z \<in> lift Y Z. lift (X * z) X)" by (simp flip: mul_eq_idx_union_lift_mul)
  also have "... = (\<Union>z \<in> Z. lift (X * (Y + z)) X)" by (simp add: lift_eq_image_add)
  also from mem have "... = lift (X * Y) (\<Union>z \<in> Z. lift (X * z) X)"
    by (simp add: add_eq_bin_union_lift lift_union_eq_idx_union_lift lift_lift_eq_lift_add
      mul_bin_union_eq_bin_union_mul)
  also have "... = lift (X * Y) (X * Z)" by (simp flip: mul_eq_idx_union_lift_mul)
  finally show ?case .
qed

lemma mul_add_eq_mul_add_mul: "X * (Y + Z) = X * Y + X * Z"
  by (simp only: add_eq_bin_union_lift mul_bin_union_eq_bin_union_mul mul_lift_eq_lift_mul_mul)

text \<open>Set multiplication is associative:\<close>

lemma mul_assoc: "(X * Y) * Z = X * (Y * Z)"
proof (induction Z rule: mem_induction)
  case (mem Z)
  have "(X * Y) * Z = (\<Union>z \<in> Z. lift ((X * Y) * z) (X * Y))"
    by (subst mul_eq_idx_union_lift_mul) simp
  also from mem have "... = (\<Union>z \<in> Z. X * lift(Y * z) Y)" by (simp add: mul_lift_eq_lift_mul_mul)
  also have "... = X * (\<Union>z \<in> Z. lift(Y * z) Y)" by (simp add: mul_union_eq_idx_union_mul)
  also have "... = X * (Y * Z)" by (simp flip: mul_eq_idx_union_lift_mul)
  finally show ?case .
qed

paragraph\<open>Lemma 4.5 from \<^cite>\<open>kirby_set_arithemtics\<close>\<close>

lemma le_mul_if_ne_zero:
  assumes "Y \<noteq> 0"
  shows "X \<le> X * Y"
proof (cases "X = 0")
  case False
  from assms show ?thesis
  proof (induction Y rule: mem_induction)
    case (mem Y)
    then show ?case
    proof (cases "Y = 1")
      case False
      with mem obtain P where P: "P \<in> Y" "P \<noteq> 0" by (auto 5 0 simp: succ_eq_insert_self)
      from \<open>X \<noteq> 0\<close> obtain R where R: "R \<in> X" by auto
      from mem.IH have "X \<le> X * P" using P by auto
      also have "... \<le> X * P + R" by simp
      also have "... \<le> X * Y"
      proof -
        from R have "X * P + R \<in> lift (X * P) X" by (auto simp: lift_eq_image_add)
        also have "... \<subseteq> X * Y" using P by (auto simp: mul_eq_idx_union_lift_mul[where ?Y=Y])
        finally have "X * P + R \<in> X * Y" .
        then show ?thesis by (intro le_if_lt lt_if_mem)
      qed
      finally show ?thesis .
    qed simp
  qed
qed simp

paragraph\<open>Lemma 4.6 from \<^cite>\<open>kirby_set_arithemtics\<close>\<close>

text\<open>The next lemma is rather complex and remains incomplete as of now. A complete proof
can be found in \<^cite>\<open>kirby_set_arithemtics\<close> and
\<^url>\<open>https://foss.heptapod.net/isa-afp/afp-devel/-/blob/06458dfa40c7b4aaaeb855a37ae77993cb4c8c18/thys/ZFC_in_HOL/Kirby.thy#L992\<close>.\<close>

lemma zero_if_multi_eq_multi_add: assumes "A * X = A * Y + B" "B < A"
  shows "B = 0"
proof (cases "A = 0 \<or> X = 0")
  case True
  with assms show ?thesis
  proof (cases "A = 0")
    case False
    then have "A * Y + B = 0" using  \<open>A = 0 \<or> X = 0\<close> assms by auto
    then show ?thesis
      by (auto simp: add_eq_zero_iff_and_eq_zero[of "A * Y" "B"])
  qed auto
next
  case False
  then have "A \<noteq> 0" "X \<noteq> 0" by auto
  then show ?thesis
  proof (cases"Y = 0")
    case True
    then show ?thesis sorry
  next
    case False
    then show ?thesis sorry
        qed
      qed

paragraph\<open>Lemma 4.7 from \<^cite>\<open>kirby_set_arithemtics\<close>\<close>

text\<open>For the next missing proofs, see
\<^url>\<open>https://foss.heptapod.net/isa-afp/afp-devel/-/blob/06458dfa40c7b4aaaeb855a37ae77993cb4c8c18/thys/ZFC_in_HOL/Kirby.thy#L1166\<close>.\<close>

lemma subset_if_mul_add_subset_mul_add: assumes "R < A" "S < A" "A * X + R \<subseteq> A * Y + S"
  shows "X \<subseteq> Y"
  sorry

lemma eq_if_mul_add_eq_mul_add: assumes "R < A" "S < A" "A * X + R = A * Y + S"
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
  then have "X = Y" "r = rr" using eq_if_mul_add_eq_mul_add[of r _ rr X _] by auto
  then show "x \<in> 0" by (simp add: assms)
qed simp


end
