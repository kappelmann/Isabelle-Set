\<^marker>\<open>creator "Linghan Fang"\<close>
\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Generalised Multiplication\<close>
theory HOTG_Multiplication
  imports
    HOTG_Addition
    HOTG_Additively_Divides
    HOTG_Ranks
    HOTG_Ordinals_Max
begin

unbundle no_HOL_groups_syntax

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

lemma mul_eq_mul_add_ltE:
  assumes "A * X = A * Y + B" "0 < B" "B < A"
  obtains u f where "A * Y = A * u + f" "0 < f" "f < A" "u < X"
proof -
  define \<phi> where "\<phi> x \<longleftrightarrow> (\<exists>r. 0 < r \<and> r < A \<and> A * x = A * Y + r)" for x
  from assms have "\<phi> X" unfolding \<phi>_def by auto
  then obtain X' where "\<phi> X'" "X' \<le> X" and X'_min: "\<And>x. x < X' \<Longrightarrow> \<not> \<phi> x"
    using le_minimal_set_witnessE by auto
  from \<open>\<phi> X'\<close> obtain B' where "0 < B'" "B' < A" "A * X' = A * Y + B'" unfolding \<phi>_def by auto
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
    using \<open>p = A * u + c\<close> additively_divides_or_additively_divides_if_add_eq_add by blast
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
    then have "\<phi> u" using \<open>e < A\<close> \<open>A * u = A * Y + e\<close> unfolding \<phi>_def by blast
    then have "False" using X'_min \<open>u \<in> X'\<close> lt_if_mem by auto
    then show ?thesis by blast
  next
    case 2
    then obtain f where "A * Y = A * u + f" by fast
    then have "A * u + f + d = A * u + c" using \<open>p = A * Y + d\<close> \<open>p = A * u + c\<close> by auto
    then have "f + d = c" using add_assoc add_eq_add_if_eq_right by auto
    then have "f < A" using \<open>c \<in> A\<close> lt_if_mem_if_le by auto
    have "f \<noteq> 0" using \<open>A * Y = A * u + f\<close> add_zero_eq_self \<open>A * u \<noteq> A * Y\<close> by force
    have "u < X" using \<open>u \<in> X'\<close> lt_if_mem \<open>X' \<le> X\<close> lt_if_le_if_lt by blast
    then show ?thesis using that \<open>A * Y = A * u + f\<close> \<open>f \<noteq> 0\<close> \<open>f < A\<close> \<open>u < X\<close> by auto
  qed
qed

lemma eq_zero_if_lt_if_mul_eq_mul_add:
  assumes "A * X = A * Y + B" "B < A"
  shows "B = 0"
using assms
proof (induction X arbitrary: Y B rule: lt_induct)
  case (step X) show ?case
  proof (rule ccontr)
    assume "B \<noteq> 0"
    then have "0 < B" by auto
    with mul_eq_mul_add_ltE step obtain u f where "A * Y = A * u + f" "0 < f" "f < A" "u < X"
      by blast
    with mul_eq_mul_add_ltE obtain v g where "A * u = A * v + g" "0 < g" "g < A" "v < Y" by blast
    with step.IH have "g = 0" using \<open>u < X\<close> by auto
    then show "False" using \<open>0 < g\<close> by auto
  qed
qed

paragraph\<open>Lemma 4.7 from \<^cite>\<open>kirby_set_arithemtics\<close>\<close>

text\<open>For the next missing proofs, see
\<^url>\<open>https://foss.heptapod.net/isa-afp/afp-devel/-/blob/06458dfa40c7b4aaaeb855a37ae77993cb4c8c18/thys/ZFC_in_HOL/Kirby.thy#L1166\<close>.\<close>

lemma eq_if_mul_add_eq_mul_add_if_lt_aux:
  assumes "A * X + R = A * Y + S" "R < A" "S < A"
  assumes IH:
    "\<And>x y r s. x \<in> X \<Longrightarrow> y \<in> Y \<Longrightarrow> r < A \<Longrightarrow> s < A \<Longrightarrow> 
    A * x + r = A * y + s \<Longrightarrow> x = y \<and> r = s"
  shows "X \<subseteq> Y"
proof
  fix u assume "u \<in> X"
  have "A * u \<noteq> A * Y"
  proof
    assume "A * u = A * Y"
    moreover have "lift (A * u) A \<subseteq> A * X" using \<open>u \<in> X\<close> mul_eq_idx_union_lift_mul by fast
    ultimately have "lift (A * Y) A \<subseteq> A * X" by auto
    then have "lift (A * Y) A \<subseteq> A * Y \<union> lift (A * Y) S"
      using \<open>A * X + R = A * Y + S\<close> add_eq_bin_union_lift by blast
    then have "lift (A * Y) A \<subseteq> lift (A * Y) S"
      using disjoint_lift_self_right disjoint_iff_all_not_mem by blast
    then have "A \<subseteq> S" using subset_if_lift_subset_lift by blast
    then show "False" using \<open>S < A\<close> not_subset_if_lt by blast
  qed
  from \<open>R < A\<close> obtain R' where "R' \<in> A" "R \<le> R'" by (auto elim: lt_mem_leE)
  have "A * u + R' \<in> A * X" 
    using mul_eq_idx_union_repl_mul_add[of A X] \<open>R' \<in> A\<close> \<open>u \<in> X\<close> by auto
  moreover have "A * X \<subseteq> A * Y \<union> lift (A * Y) S"
    using \<open>A * X + R = A * Y + S\<close> add_eq_bin_union_lift by auto
  ultimately consider "A * u + R' \<in> lift (A * Y) S" | "A * u + R' \<in> A * Y" by auto
  then show "u \<in> Y"
  proof cases
    case 1
    then obtain t where "t \<in> S" "A * u + R' = A * Y + t" using lift_eq_repl_add by auto
    show ?thesis using additively_divides_if_add_eq_addE[OF \<open>A * u + R' = A * Y + t\<close>]
    proof cases
      case 1
      then obtain d where "A * u + d = A * Y" using additively_dividesE by auto
      then have "A * u + R' = A * u + d + t" using \<open>A * u + R' = A * Y + t\<close> by auto
      then have "R' = d + t" using add_assoc add_eq_add_if_eq_right by auto
      then have "d < A" using \<open>R' \<in> A\<close> lt_if_mem_if_le by auto
      moreover have "d \<noteq> 0" using \<open>A * u + d = A * Y\<close> add_zero_eq_self \<open>A * u \<noteq> A * Y\<close> by force
      ultimately have "False" using \<open>A * u + d = A * Y\<close>[symmetric] eq_zero_if_lt_if_mul_eq_mul_add by auto
      then show ?thesis by blast
    next
      case 2
      then obtain c where "A * Y + c = A * u" using additively_dividesE by auto
      then have "A * Y + c + R' = A * Y + t" using \<open>A * u + R' = A * Y + t\<close> by auto
      then have "c + R' = t" using add_eq_add_if_eq_right add_assoc by auto
      then have "c \<le> t" by auto
      also have "t < A" using \<open>t \<in> S\<close> lt_if_mem \<open>S < A\<close> lt_trans by blast
      finally have "c < A" using lt_if_le_if_lt by auto
      moreover have "c \<noteq> 0" using \<open>A * Y + c = A * u\<close> add_zero_eq_self \<open>A * u \<noteq> A * Y\<close> by force
      ultimately have "False" using \<open>A * Y + c = A * u\<close>[symmetric] eq_zero_if_lt_if_mul_eq_mul_add by auto
      then show ?thesis by blast
    qed
  next
    case 2
    then obtain v e where "v \<in> Y" "e \<in> A" "A * u + R' = A * v + e" 
      using mul_eq_idx_union_repl_mul_add[of A Y] by auto
    then have "u = v" using IH \<open>u \<in> X\<close> \<open>R' \<in> A\<close> lt_if_mem by blast
    then show ?thesis using \<open>v \<in> Y\<close> by blast
  qed
qed

lemma eq_if_mul_add_eq_mul_add_if_lt:
  assumes "R < A" "S < A"
  and "A * X + R = A * Y + S"
  shows "X = Y \<and> R = S"
proof -
  let ?\<alpha> = "max_ordinal (rank X) (rank Y)"
  have "X = Y \<and> R = S" if "ordinal \<alpha>" "rank X \<le> \<alpha>" "rank Y \<le> \<alpha>" for \<alpha> 
    using that assms
  proof (induction \<alpha> arbitrary: X Y R S rule: ordinal_mem_induct)
    case (step \<alpha>)
    have "\<exists>\<beta>. \<beta> \<in> \<alpha> \<and> rank x \<le> \<beta> \<and> rank y \<le> \<beta>" if "x \<in> X" "y \<in> Y" for x y
    proof
      define \<beta> :: set where "\<beta> = max_ordinal (rank x) (rank y)"
      have "rank x < \<alpha>" 
        using \<open>x \<in> X\<close> lt_if_mem rank_lt_rank_if_lt \<open>rank X \<le> \<alpha>\<close> lt_if_lt_if_le by fastforce
      moreover have "rank y < \<alpha>"
        using \<open>y \<in> Y\<close> lt_if_mem rank_lt_rank_if_lt \<open>rank Y \<le> \<alpha>\<close> lt_if_lt_if_le by fastforce
      ultimately have "\<beta> < \<alpha>" using \<beta>_def max_ordinal_lt_if_lt_if_lt by auto
      then have "\<beta> \<in> \<alpha>" using \<open>ordinal \<alpha>\<close> 
        using mem_if_lt_if_mem_trans_closed ordinal_mem_trans_closedE  by auto
      then show "\<beta> \<in> \<alpha> \<and> rank x \<le> \<beta> \<and> rank y \<le> \<beta>" using \<beta>_def ordinal_rank 
        le_max_ordinal_left_if_ordinal_if_ordinal le_max_ordinal_right_if_ordinal_if_ordinal by auto 
    qed
    then have IH': 
        "\<And>x y r s. x \<in> X \<Longrightarrow> y \<in> Y \<Longrightarrow> r < A \<Longrightarrow> s < A \<Longrightarrow> 
        A * x + r = A * y + s \<Longrightarrow> x = y \<and> r = s"
      using step.IH by blast
    then have "X \<subseteq> Y" 
      using eq_if_mul_add_eq_mul_add_if_lt_aux step.prems by auto
    moreover have "Y \<subseteq> X" 
      using eq_if_mul_add_eq_mul_add_if_lt_aux[OF \<open>A * X + R = A * Y + S\<close>[symmetric]]
      using \<open>S < A\<close> \<open>R < A\<close> IH' by force
    ultimately have "X = Y" by auto
    moreover from this have "R = S" using \<open>A * X + R = A * Y + S\<close> add_eq_add_if_eq_right by auto
    ultimately show ?case by auto
  qed
  moreover have "ordinal ?\<alpha> \<and> rank X \<le> ?\<alpha> \<and> rank Y \<le> ?\<alpha>"
    using ordinal_rank ordinal_max_ordinal_if_ordinal_if_ordinal
    using le_max_ordinal_left_if_ordinal_if_ordinal le_max_ordinal_right_if_ordinal_if_ordinal by auto
  ultimately show ?thesis by auto
qed

(*

lemma eq_if_mul_add_eq_mul_add_if_lt:
  assumes "R < A" "S < A"
  and "A * X + R = A * Y + S"
  shows "X = Y \<and> R = S"
  using assms
proof (induction X arbitrary: Y R S rule: mem_induction)
  case (mem X)
  then show ?case
  proof (cases "Y = 0")
    case True
    then have "A * X + R < A" using mem.prems by auto
    have "X = 0"
    proof (rule ccontr)
      assume "X \<noteq> 0"
      have "A \<le> A * X + R" 
        using le_mul_if_ne_zero[OF \<open>X \<noteq> 0\<close>] le_self_add le_trans by auto
      then show "False" using \<open>A * X + R < A\<close> by auto
    qed
    then have "R = S" using \<open>Y = 0\<close> \<open>A * X + R = A * Y + S\<close> by auto
    then show ?thesis using \<open>X = 0\<close> \<open>Y = 0\<close> by auto
  next
    case False
    have "X \<noteq> 0"
    proof
      assume "X = 0"
      then have "A * Y + S < A" using mem.prems by auto
      moreover have "A \<le> A * Y + S" 
        using le_mul_if_ne_zero[OF \<open>Y \<noteq> 0\<close>] le_self_add le_trans by auto
      ultimately show "False" by auto
    qed
    have "X \<subseteq> Y" using eq_if_mul_add_eq_mul_add_if_lt_aux mem by auto
    then show ?thesis sorry
  qed
qed

*)

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
