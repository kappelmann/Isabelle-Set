\<^marker>\<open>creator "Linghan Fang"\<close>
\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Generalised Multiplication\<close>
theory HOTG_Multiplication
  imports
    HOTG_Addition HOTG_Additive_Order
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
  unfolding mul_def by (urule transrec_eq)

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

lemma zero_if_multi_eq_multi_add_aux:
  assumes "A * X = A * Y + B" "0 < B" "B < A"
  obtains u f where "A * Y = A * u + f" "0 < f" "f < A" "u < X"
proof -
  define \<phi> where "\<phi> x \<longleftrightarrow> (\<exists>r. 0 < r \<and> r < A \<and> A * x = A * Y + r)" for x
  have "\<phi> X" using \<phi>_def assms by auto
  then obtain X' where "\<phi> X'" "X' \<le> X" and X'_min: "\<And>x. x < X' \<Longrightarrow> \<not> \<phi> x" 
    using minimal_satisfier_le by auto
  from \<open>\<phi> X'\<close> obtain B' where "0 < B'" "B' < A" "A * X' = A * Y + B'" using \<phi>_def by auto
  then have "A * Y < A * X'" by auto
  then obtain p where "p \<in> A * X'" "A * Y \<le> p" by (auto elim: lt_mem_leE)
  from \<open>p \<in> A * X'\<close> obtain u c where "u \<in> X'" "c \<in> A" "p = A * u + c" 
    using mul_eq_idx_union_repl_mul_add[of A X'] by auto
  have "A * u \<noteq> A * Y"
  proof
    assume "A * u = A * Y"
    moreover have "lift (A * u) A \<subseteq> A * X'" using \<open>u \<in> X'\<close> mul_eq_idx_union_lift_mul by fast
    ultimately have "lift (A * Y) A \<subseteq> A * X'" by auto
    then have "lift (A * Y) A \<subseteq> A * Y \<union> lift (A * Y) B'" 
      using \<open>A * X' = A * Y + B'\<close> add_eq_bin_union_lift by blast
    then have "lift (A * Y) A \<subseteq> lift (A * Y) B'"
      using disjoint_lift_self_right disjoint_iff_all_not_mem by blast
    then have "A \<subseteq> B'" using subset_if_lift_subset_lift by blast
    then show "False" using \<open>B' < A\<close> not_subset_if_lt by blast
  qed
  from \<open>A * Y \<le> p\<close> have "p \<notin> A * Y" using lt_if_mem not_lt_if_le by auto
  then have "p \<in> lift (A * Y) B'" 
    using \<open>p \<in> A * X'\<close> \<open>A * X' = A * Y + B'\<close> add_eq_bin_union_lift by auto
  then obtain d where "d \<in> B'" "p = A * Y + d" using lift_eq_repl_add by auto
  then consider "A * Y \<unlhd> A * u" | "A * u \<unlhd> A * Y" 
    using \<open>p = A * u + c\<close> additively_divides_if_sums_equal by blast 
  then show ?thesis
  proof cases
    case 1
    then obtain e where "A * u = A * Y + e" by (auto elim!: additively_dividesE)
    then have "A * Y + d = A * Y + e + c" using \<open>p = A * Y + d\<close> \<open>p = A * u + c\<close> by auto
    then have "d = e + c" using add_assoc add_eq_add_if_eq_right by auto
    then have "e \<le> d" using le_self_add by auto
    also have "d < A" using \<open>d \<in> B'\<close> lt_if_mem \<open>B' < A\<close> lt_trans by blast
    finally have "e < A" using lt_if_le_if_lt by auto
    have "e \<noteq> 0" using \<open>A * u = A * Y + e\<close> add_zero_eq_self \<open>A * u \<noteq> A * Y\<close> by force
    then have "\<phi> u" using \<phi>_def \<open>e < A\<close> \<open>A * u = A * Y + e\<close> by blast
    then have "False" using X'_min \<open>u \<in> X'\<close> lt_if_mem by auto
    then show ?thesis by blast
  next
    case 2
    then obtain f where "A * Y = A * u + f" by (auto elim!: additively_dividesE) 
    then have "A * u + f + d = A * u + c" using \<open>p = A * Y + d\<close> \<open>p = A * u + c\<close> by auto
    then have "f + d = c" using add_assoc add_eq_add_if_eq_right by auto
    then have "f < A" using le_self_add \<open>c \<in> A\<close> lt_if_mem_if_le by auto
    have "f \<noteq> 0" using \<open>A * Y = A * u + f\<close> add_zero_eq_self \<open>A * u \<noteq> A * Y\<close> by force
    have "u < X" using \<open>u \<in> X'\<close> lt_if_mem \<open>X' \<le> X\<close> lt_if_le_if_lt by blast
    then show ?thesis using that \<open>A * Y = A * u + f\<close> \<open>f \<noteq> 0\<close> \<open>f < A\<close> \<open>u < X\<close> by auto
  qed
qed

lemma zero_if_multi_eq_multi_add:
  assumes "A * X = A * Y + B" "B < A"
  shows "B = 0"
  using assms 
proof (induction X arbitrary: Y B rule: lt_induct)
  case (step X)
  show ?case
  proof (rule ccontr)
    assume "B \<noteq> 0"
    then have "0 < B" by auto
    from zero_if_multi_eq_multi_add_aux[OF step(2) \<open>0 < B\<close> \<open>B < A\<close>] obtain u f where 
      "A * Y = A * u + f" "0 < f" "f < A" "u < X" by auto
    from zero_if_multi_eq_multi_add_aux[OF this(1, 2, 3)] obtain v g where
      "A * u = A * v + g" "0 < g" "g < A" "v < Y" by auto
    then have "g = 0" using step.IH \<open>u < X\<close> by auto
    then show "False" using \<open>0 < g\<close> by auto
  qed
qed

paragraph\<open>Lemma 4.7 from \<^cite>\<open>kirby_set_arithemtics\<close>\<close>

text\<open>For the next missing proofs, see
\<^url>\<open>https://foss.heptapod.net/isa-afp/afp-devel/-/blob/06458dfa40c7b4aaaeb855a37ae77993cb4c8c18/thys/ZFC_in_HOL/Kirby.thy#L1166\<close>.\<close>

(* lemma subset_if_mul_add_subset_mul_add_if_lt:
  assumes "R < A" "S < A"
  and "A * X + R \<subseteq> A * Y + S"
  shows "X \<subseteq> Y"
  sorry *)

lemma eq_if_mul_add_eq_mul_add_if_lt:
  assumes "R < A" "S < A"
  and "A * X + R = A * Y + S"
  shows "X = Y" "R = S"
proof (induction X rule: lt_induct)
  case (step X)
  have "X \<noteq> 0"
  proof
    assume "X = 0"
    then have "A * Y + S < A" sorry
    show "False" sorry
  qed
  {
    case 1
    then show ?case sorry
  next
    case 2
    then show ?case sorry
  }
qed

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
  then have "X = Y" "r = rr" using eq_if_mul_add_eq_mul_add_if_lt[of r _ rr X _] by auto
  then show "x \<in> 0" by (simp add: assms)
qed simp


end
