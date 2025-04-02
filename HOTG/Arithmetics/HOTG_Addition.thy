\<^marker>\<open>creator "Linghan Fang"\<close>
\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Generalised Addition\<close>
theory HOTG_Addition
  imports
    HOTG_Ordinals_Base
    HOTG_Epsilon_Recursion
begin

unbundle no HOL_groups_syntax
  and no HOL_order_syntax
  and no HOL_ascii_syntax

paragraph \<open>Summary\<close>
text \<open>Translation of generalised set addition from \<^cite>\<open>kirby_set_arithemtics\<close> and
\<^cite>\<open>ZFC_in_HOL_AFP\<close>. Note that general set addition is associative and
monotone and injective in the second argument, but it is not commutative.\<close>

definition "add X \<equiv> mem_rec (\<lambda>addX Y. X \<union> image addX Y)"

open_bundle hotg_add_syntax begin notation add (infixl "+" 65) end

lemma add_eq_bin_union_repl_add: "X + Y = X \<union> {X + y | y \<in> Y}"
  unfolding add_def supply mem_rec_eq[uhint] by (urule refl)

text \<open>The lift operation from \<^cite>\<open>kirby_set_arithemtics\<close>.\<close>

definition "lift X :: set \<Rightarrow> set \<equiv> image ((+) X)"

lemma lift_eq_image_add: "lift X = image ((+) X)"
  unfolding lift_def by simp

lemma lift_eq_repl_add: "lift X Y = {X + y | y \<in> Y}"
  using lift_eq_image_add by simp

lemma add_eq_bin_union_lift: "X + Y = X \<union> lift X Y"
  unfolding lift_eq_image_add by (urule add_eq_bin_union_repl_add)

corollary lift_subset_add: "lift X Y \<subseteq> X + Y"
  using add_eq_bin_union_lift by auto

paragraph \<open>Lemma 3.2 from \<^cite>\<open>kirby_set_arithemtics\<close>\<close>

lemma lift_bin_union_eq_lift_bin_union_lift: "lift X (A \<union> B) = lift X A \<union> lift X B"
  by (auto simp: lift_eq_image_add)

lemma lift_union_eq_idx_union_lift: "lift X (\<Union>Y) = (\<Union>y \<in> Y. lift X y)"
  by (auto simp: lift_eq_image_add)

lemma idx_union_add_eq_add_idx_union:
  "Y \<noteq> {} \<Longrightarrow> (\<Union>y \<in> Y. X + f y) = X + (\<Union>y \<in> Y. f y)"
  by (simp add: lift_union_eq_idx_union_lift add_eq_bin_union_lift)

lemma lift_zero_eq_zero [simp]: "lift X 0 = 0"
  by (auto simp: lift_eq_image_add)

text\<open>\<open>0\<close> is the right identity of set addition.\<close>

lemma add_zero_eq_self [simp]: "X + 0 = X"
  unfolding add_eq_bin_union_lift by simp

lemma lift_one_eq_singleton_self [simp]: "lift X 1 = {X}"
  unfolding lift_eq_image_add succ_eq_insert_self by simp

text \<open>The successor operation aligns with addition.\<close>

lemma succ_eq_add_one: "succ X = X + 1"
  by (subst add_eq_bin_union_repl_add) (auto simp: succ_eq_insert_self)

lemma insert_self_eq_add_one: "insert X X = X + 1"
  by (simp flip: succ_eq_insert_self[of X] succ_eq_add_one)

lemma lift_insert_eq_insert_add_lift: "lift X (insert Y Z) = insert (X + Y) (lift X Z)"
  unfolding lift_eq_image_add by (simp add: repl_insert_eq)

lemma add_insert_eq_insert_add: "X + insert Y Z = insert (X + Y) (X + Z)"
  by (auto simp: lift_insert_eq_insert_add_lift add_eq_bin_union_lift)


paragraph \<open>Proposition 3.3 from \<^cite>\<open>kirby_set_arithemtics\<close>\<close>

text\<open>\<open>0\<close> is the left identity of set addition.\<close>

lemma zero_add_eq_self [simp]: "0 + X = X"
proof (induction X)
  case (mem X)
  have "0 + X = lift 0 X" by (simp add: add_eq_bin_union_lift)
  also from mem have "... = X" by (simp add: lift_eq_image_add)
  finally show ?case .
qed

corollary lift_zero_eq_self [simp]: "lift 0 X = X"
  by (simp add: lift_eq_image_add)

corollary add_eq_zeroE:
  assumes "X + Y = 0"
  obtains "X = 0" "Y = 0"
  using assms by (auto simp: add_eq_bin_union_lift)

corollary add_eq_zero_iff_and_eq_zero [iff]: "X + Y = 0 \<longleftrightarrow> X = 0 \<and> Y = 0"
  using add_eq_zeroE by auto

text \<open>The next lemma demonstrates the associativity of set addition.\<close>

lemma add_assoc: "(X + Y) + Z = X + (Y + Z)"
proof (induction Z)
  case (mem Z)
  from add_eq_bin_union_lift have "(X + Y) + Z = (X + Y) \<union> (lift (X + Y) Z)" by simp
  also from lift_eq_repl_add have "... = (X + Y) \<union> {(X + Y) + z | z \<in> Z}" by simp
  also from add_eq_bin_union_lift have "... = X \<union> (lift X Y) \<union> {(X + Y) + z | z \<in> Z}" by simp
  also from mem have "... = X \<union> (lift X Y) \<union> {X + (Y + z) | z \<in> Z}" by simp
  also have "... = X \<union> lift X (Y + Z)"
  proof-
    from add_eq_bin_union_lift have "lift X (Y + Z) = lift X (Y \<union> lift Y Z)" by simp
    also from lift_bin_union_eq_lift_bin_union_lift have "... = (lift X Y) \<union> lift X (lift Y Z)" by simp
    also from lift_eq_repl_add have "... = (lift X Y) \<union> {X + (Y + z) | z \<in> Z}" by simp
    finally have "lift X (Y + Z) = (lift X Y) \<union> {X + (Y + z) | z \<in> Z}" .
    then show ?thesis by auto
  qed
  also from add_eq_bin_union_lift have "... = X + (Y + Z)" by simp
  finally show ?case .
qed

lemma lift_lift_eq_lift_add: "lift X (lift Y Z) = lift (X + Y) Z"
  by (simp add: lift_eq_image_add add_assoc)

lemma add_succ_eq_succ_add: "X + succ Y = succ (X + Y)"
  by (subst succ_eq_add_one, subst add_assoc[symmetric]) (simp flip: succ_eq_add_one)

lemma add_mem_lift_if_mem_right:
  assumes "X \<in> Y"
  shows "Z + X \<in> lift Z Y"
  using assms by (auto simp: lift_eq_repl_add)

corollary add_mem_add_if_mem_right:
  assumes "X \<in> Y"
  shows "Z + X \<in> Z + Y"
  using assms add_mem_lift_if_mem_right lift_subset_add by blast

lemma not_add_lt_left [iff]: "\<not>(X + Y < X)"
proof
  assume "X + Y < X"
  then show "False"
  proof (induction Y rule: mem_induction)
    case (mem Y)
    then show ?case
    proof (cases "Y = {}")
      case False
      then obtain y where "y \<in> Y" by blast
      with add_mem_add_if_mem_right have "X + y \<in> X + Y" by auto
      with mem.prems have "X + y < X" by (auto intro: lt_if_lt_if_mem)
      with \<open>y \<in> Y\<close> mem.IH show ?thesis by auto
    qed simp
  qed
qed

lemma not_add_mem_left [iff]: "X + Y \<notin> X"
  using subset_mem_trans_closure_self lt_iff_mem_trans_closure by auto

corollary add_subset_left_iff_right_eq_zero [iff]: "X + Y \<subseteq> X \<longleftrightarrow> Y = 0"
  by (subst add_eq_bin_union_repl_add) auto

corollary lift_subset_left_iff_right_eq_zero [iff]: "lift X Y \<subseteq> X \<longleftrightarrow> Y = 0"
  by (auto simp: lift_eq_repl_add)

lemma disjoint_mem_trans_closure_lift [iff]: "disjoint (mem_trans_closure X) (lift X Y)"
  by (auto simp: lift_eq_image_add simp flip: lt_iff_mem_trans_closure)

text \<open>The next lemma shows that \<open>X\<close> and @{term "lift X Y"} are disjoint,
implying that @{term "X + Y"} can be split into two disjoint parts.\<close>

lemma disjoint_lift_self_right [iff]: "disjoint X (lift X Y)"
  using disjoint_mem_trans_closure_lift subset_mem_trans_closure_self by blast

corollary disjoint_lift_self_left [iff]: "disjoint (lift X Y) X"
  using disjoint_lift_self_right by blast

lemma lift_eq_lift_if_bin_union_lift_eq_bin_union_lift:
  assumes "X \<union> lift X Y = X \<union> lift X Z"
  shows "lift X Y = lift X Z"
  using assms disjoint_lift_self_right by blast


paragraph \<open>Proposition 3.4 from \<^cite>\<open>kirby_set_arithemtics\<close>\<close>

lemma lift_injective_right: "injective (lift X)"
proof (rule injectiveI)
  fix Y Z assume "lift X Y = lift X Z"
  then show "Y = Z"
  proof (induction Y arbitrary: Z rule: mem_induction)
    case (mem Y)
    {
      fix U V u assume uvassms: "U \<in> {Y, Z}" "V \<in> {Y, Z}" "U \<noteq> V" "u \<in> U"
      with mem have "X + u \<in> lift X V" by (auto simp: lift_eq_repl_add mem_insert_iff)
      then obtain v where "v \<in> V" "X + u = X + v" using lift_eq_repl_add by auto
      then have "X \<union> lift X u  = X \<union> lift X v" by (simp add: add_eq_bin_union_lift)
      with disjoint_lift_self_right have "lift X u = lift X v" by blast
      with uvassms \<open>v \<in> V\<close> mem.IH have "u \<in> V" by (auto simp: mem_insert_iff)
    }
    then show ?case by blast
  qed
qed

corollary lift_eq_lift_if_eq_right: "lift X Y = lift X Z \<Longrightarrow> Y = Z"
  using lift_injective_right by (blast dest: injectiveD)

corollary lift_eq_lift_iff_eq_right [iff]: "lift X Y = lift X Z \<longleftrightarrow> Y = Z"
  using lift_eq_lift_if_eq_right by auto

lemma add_injective_right: "injective ((+) X)"
  using lift_injective_right lift_eq_image_add by auto

corollary add_eq_add_if_eq_right: "X + Y = X + Z \<Longrightarrow> Y = Z"
  using add_injective_right by (blast dest: injectiveD)

corollary add_eq_add_iff_eq_right [iff]: "X + Y = X + Z \<longleftrightarrow> Y = Z"
  using add_eq_add_if_eq_right by auto

lemma mem_if_add_mem_add_right:
  assumes "X + Y \<in> X + Z"
  shows "Y \<in> Z"
proof -
  have "X + Z = X \<union> lift X Z" by (simp only: add_eq_bin_union_lift)
  with assms have "X + Y \<in> lift X Z" by auto
  also have "... = {X + z| z \<in> Z}" by (simp add: lift_eq_image_add)
  finally have "X + Y \<in> {X + z| z \<in> Z}" .
  then show "Y \<in> Z" by blast
qed

corollary add_mem_add_iff_mem_right [iff]: "X + Y \<in> X + Z \<longleftrightarrow> Y \<in> Z"
  using mem_if_add_mem_add_right add_mem_add_if_mem_right by blast

text \<open>We next prove some monotonicity lemmas for @{term lift} and @{term "(+)"}.\<close>

lemma mono_lift: "((\<subseteq>) \<Rightarrow> (\<subseteq>)) (lift X)"
  by (intro mono_wrt_relI) (auto simp: lift_eq_repl_add)

lemma subset_if_lift_subset_lift: "lift X Y \<subseteq> lift X Z \<Longrightarrow> Y \<subseteq> Z"
  by (auto simp: lift_eq_repl_add)

corollary lift_subset_lift_iff_subset: "lift X Y \<subseteq> lift X Z \<longleftrightarrow> Y \<subseteq> Z"
  using subset_if_lift_subset_lift mono_lift[of X] by (auto del: subsetI)

lemma mono_add: "((\<subseteq>) \<Rightarrow> (\<subseteq>)) ((+) X)"
proof (rule mono_wrt_relI)
  fix Y Z assume "Y \<subseteq> Z"
  then have "lift X Y \<subseteq> lift X Z" by (simp only: lift_subset_lift_iff_subset)
  then show "X + Y \<subseteq> X + Z" by (auto simp: add_eq_bin_union_lift)
qed

lemma subset_if_add_subset_add:
  assumes "X + Y \<subseteq> X + Z"
  shows "Y \<subseteq> Z"
proof-
  have "X + Z = X \<union> lift X Z" by (simp only: add_eq_bin_union_lift)
  with assms have "lift X Y \<subseteq> X \<union> lift X Z" by (auto simp: add_eq_bin_union_lift)
  with disjoint_lift_self_left have "lift X Y \<subseteq> lift X Z" by blast
  with lift_subset_lift_iff_subset show ?thesis by simp
qed

corollary add_subset_add_iff_subset [iff]: "X + Y \<subseteq> X + Z \<longleftrightarrow> Y \<subseteq> Z"
  using subset_if_add_subset_add mono_add[of X] by (auto del: subsetI)

text \<open>The transitive closure of a sum can be split into two smaller closures of its arguments.\<close>

lemma mem_trans_closure_add_eq_mem_trans_closure_bin_union:
  "mem_trans_closure (X + Y) = mem_trans_closure X \<union> lift X (mem_trans_closure Y)"
proof (induction Y)
  case (mem Y)
  have "mem_trans_closure (X + Y) = (X + Y) \<union> (\<Union>z \<in> X + Y. mem_trans_closure z)"
    by (subst mem_trans_closure_eq_bin_union_idx_union) simp
  also have "... = mem_trans_closure X \<union> lift X Y \<union> (\<Union>y \<in> Y. mem_trans_closure (X + y))"
    (is "_ = ?unions \<union> _")
    by (auto simp: lift_eq_repl_add idx_union_bin_union_dom_eq_bin_union_idx_union
      add_eq_bin_union_lift[of X Y] mem_trans_closure_eq_bin_union_idx_union[of X])
  also have "... = ?unions \<union> (\<Union>y \<in> Y. mem_trans_closure X \<union> lift X (mem_trans_closure y))"
    using mem.IH by simp
  also have "... = ?unions \<union> (\<Union>y \<in> Y. lift X (mem_trans_closure y))" by auto
  also have "... = mem_trans_closure X \<union> lift X (Y \<union> (\<Union>y \<in> Y. mem_trans_closure y))"
    by (simp add: lift_bin_union_eq_lift_bin_union_lift
      lift_union_eq_idx_union_lift bin_union_assoc mem_trans_closure_eq_bin_union_idx_union[of X])
  also have "... = mem_trans_closure X \<union> lift X (mem_trans_closure Y)"
    by (simp flip: mem_trans_closure_eq_bin_union_idx_union)
  finally show ?case .
qed

corollary lt_add_if_lt_left:
  assumes "X < Y"
  shows "X < Y + Z"
  using assms mem_trans_closure_add_eq_mem_trans_closure_bin_union
  by (auto simp: lt_iff_mem_trans_closure)

corollary add_lt_add_if_lt_right:
  assumes "X < Y"
  shows "Z + X < Z + Y"
  using assms mem_trans_closure_add_eq_mem_trans_closure_bin_union
  by (auto simp: lt_iff_mem_trans_closure lift_eq_image_add)

corollary lt_add_if_eq_add_if_lt:
  assumes "x < X"
  and "Y = Z + x"
  shows "Y < Z + X"
  using assms add_lt_add_if_lt_right by simp

corollary lt_addE:
  assumes "X < Y + Z"
  obtains (lt_left) "X < Y" | (lt_eq) z where "z < Z" "X = Y + z"
  using assms mem_trans_closure_add_eq_mem_trans_closure_bin_union
  by (auto simp: lt_iff_mem_trans_closure lift_eq_image_add)

corollary lt_add_iff_lt_or_lt_eq: "X < Y + Z \<longleftrightarrow> X < Y \<or> (\<exists>z. z < Z \<and> X = Y + z)"
  by (blast intro: lt_add_if_lt_left add_lt_add_if_lt_right elim: lt_addE)

lemma not_lt_zero [iff]: "\<not>(X < 0)"
  unfolding lt_iff_mem_trans_closure by auto

lemma not_succ_le_zero [iff]: "\<not>(succ n \<le> 0)"
  by (auto elim: leE)

lemma zero_lt_if_ne_zero [iff]:
  assumes "X \<noteq> 0"
  shows "0 < X"
  using assms mem_trans_closed_mem_trans_closure
  by (intro lt_if_mem_trans_closure empty_mem_if_mem_trans_closedI) auto

lemma zero_le [iff]: "0 \<le> X" by (subst le_iff_lt_or_eq) auto

lemma le_zero_iff_eq_zero [simp]: "n \<le> 0 \<longleftrightarrow> n = 0"
  using le_iff_lt_or_eq by auto

lemma lt_self_add_if_ne_zero [simp]:
  assumes "Y \<noteq> 0"
  shows "X < X + Y"
  using assms by (intro lt_add_if_eq_add_if_lt) auto

corollary le_self_add [iff]: "X \<le> X + Y"
  using le_iff_lt_or_eq by (cases "Y = 0") auto

lemma lt_succ_self [iff]: "X < succ X"
  by (subst succ_eq_add_one) simp

lemma lt_succ_if_lt: "X < Y \<Longrightarrow> X < succ Y"
  by (subst succ_eq_add_one) (rule lt_add_if_lt_left)

lemma le_succ_if_le:
  assumes "X \<le> Y"
  shows "X \<le> succ Y"
  using assms by (rule le_trans) (auto intro: lt_succ_self simp: le_iff_lt_or_eq)

lemma lt_if_add_lt: "X + Y < Z \<Longrightarrow> X < Z"
  by (rule lt_if_lt_if_le) auto


end

