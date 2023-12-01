theory Set_Add
  imports
    Transport.HOL_Syntax_Bundles_Groups
    Less_Than
begin
(*
(*TODO Kevin: fix in library*)
lemma monoE [elim]:
  assumes "mono f"
  obtains "\<And>x y. x \<le> y \<Longrightarrow> f x \<le> f y"
  using assms by blast
*)
paragraph \<open>Summary\<close>
text \<open>Translation of addition for sets from \<^url>\<open>https://www.isa-afp.org/entries/ZFC_in_HOL.html\<close>.\<close>

unbundle no_HOL_ascii_syntax
unbundle no_HOL_groups_syntax
unbundle no_HOL_order_syntax

abbreviation "zero_set \<equiv> {}"
abbreviation "one_set \<equiv> {zero_set}"
abbreviation "two_set \<equiv> {zero_set, one_set}"

bundle hotg_set_zero_syntax begin notation zero_set ("0") end
bundle no_hotg_set_zero_syntax begin no_notation zero_set ("0") end

bundle hotg_set_one_syntax begin notation one_set ("1") end
bundle no_hotg_set_one_syntax begin no_notation one_set ("1") end

bundle hotg_set_two_syntax begin notation two_set ("2") end
bundle no_hotg_set_two_syntax begin no_notation two_set ("2") end

unbundle
  hotg_set_zero_syntax
  hotg_set_one_syntax
  hotg_set_two_syntax


definition "add X \<equiv> transrec (\<lambda>addX Y. X \<union> image addX Y)"

bundle hotg_add_syntax begin notation add (infixl "+" 65) end
bundle no_hotg_add_syntax begin no_notation add (infixl "+" 65) end
unbundle hotg_add_syntax

lemma add_eq_bin_union_image_add: "X + Y = X \<union> image ((+) X) Y"
  unfolding add_def by (simp add: transrec_eq)

lemma add_eq_bin_union_repl_add: "X + Y = X \<union> {X + y | y \<in> Y}"
  unfolding add_def by (simp add: transrec_eq)

definition "lift X \<equiv> image ((+) X)"

lemma lift_eq_image_add: "lift X = image ((+) X)"
  unfolding lift_def by simp

lemma lift_eq_repl_add: "lift X Y = {X + y | y \<in> Y}"
  using lift_eq_image_add by simp

lemma add_eq_bin_union_lift: "X + Y = X \<union> lift X Y"
  unfolding lift_eq_image_add by (subst add_eq_bin_union_image_add) simp

lemma lift_bin_union_eq_lift_bin_union_lift: "lift X (A \<union> B) = lift X A \<union> lift X B"
  by (auto simp: lift_eq_image_add)

lemma lift_union_eq_union_repl_lift: "lift X (\<Union>Y) = \<Union>{lift X y | y \<in> Y}"
  by (auto simp: lift_eq_image_add)

lemma idx_union_add_eq_add_idx_union:
  "Y \<noteq> {} \<Longrightarrow> (\<Union>y \<in> Y. X + f y) = X + (\<Union>y \<in> Y. f y)"
  by (simp add: lift_union_eq_union_repl_lift add_eq_bin_union_lift)

lemma lift_zero_eq_zero [simp]: "lift X 0 = 0"
  by (auto simp: lift_eq_image_add)

lemma add_zero_eq_self [simp]: "X + 0 = X"
  unfolding add_eq_bin_union_lift by simp

lemma lift_one_eq_singleton_self [simp]: "lift X 1 = {X}"
  unfolding lift_def by simp

definition "succ X \<equiv> X + 1"

lemma succ_eq_add_one: "succ X = X + 1"
  unfolding succ_def by simp

lemma insert_self_eq_add_one: "insert X X = X + 1"
  by (auto simp: add_eq_bin_union_lift succ_eq_add_one)

lemma lift_singleton_eq_singleton_add: "lift X {Z} = {X + Z}"
  unfolding lift_def by simp

lemma lift_singleton_eq_singleton_bin_union_lift: "lift X {Z} = {X \<union> lift X Z}"
  by (simp only: lift_singleton_eq_singleton_add add_eq_bin_union_lift)

lemma lift_bin_union_singleton_eq_lift_bin_union:
  "lift X (insert Y Z) = lift X Z \<union> {X \<union> lift X Y}"
  by (simp flip: lift_singleton_eq_singleton_bin_union_lift lift_bin_union_eq_lift_bin_union_lift)

lemma add_insert_eq_insert_add: "X + insert Y Z = insert (X + Y) (X + Z)"
  by (auto simp: lift_bin_union_singleton_eq_lift_bin_union add_eq_bin_union_lift)


paragraph\<open>Proposition 3.3\<close>

lemma zero_add_eq_self [simp]: "0 + X = X"
proof (induct X)
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

lemma add_assoc: "(X + Y) + Z = X + (Y + Z)"
proof(induct Z)
  case (mem Z)
  from add_eq_bin_union_lift have "(X + Y) + Z = (X + Y) \<union> (lift (X + Y) Z)" by simp
  also from lift_eq_repl_add have "... = (X + Y) \<union> {(X + Y) + z | z \<in> Z}" by simp
  also from add_eq_bin_union_lift have "... = X \<union> (lift X Y) \<union> {(X + Y) + z | z \<in> Z}" by simp
  also from mem have "... = X \<union> (lift X Y) \<union> {X + (Y + z) | z \<in> Z}" by simp
  also have "... = X \<union> lift X (Y + Z)"
  proof-
    from add_eq_bin_union_lift have "lift X (Y + Z) = lift X (Y \<union> lift Y Z)" by simp
    also from lift_bin_union_eq_lift_bin_union_lift have "... = (lift X Y) \<union> lift X (lift Y Z)"
      by simp
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
  by (auto simp: succ_eq_add_one add_assoc)

lemma add_mem_add_if_mem:
  assumes "Y \<in> Z"
  shows "X + Y \<in> X + Z"
proof-
  from assms have "X + Y \<in> {X + z| z \<in> Z}" by auto
  then show ?thesis by (auto simp: lift_eq_repl_add[of X Z] add_eq_bin_union_lift)
qed

lemma not_add_lt_left [iff]: "\<not>(X + Y < X)"
proof
  assume "X + Y < X"
  then show "False"
  proof (induction Y rule: mem_induction)
    case (mem Y)
    then show ?case
    proof (cases "Y = {}")
      case False
      then obtain y where sub: "y \<in> Y" by blast
      with add_mem_add_if_mem mem have sub_in: "X + y \<in> X + Y" by auto
      with mem have bla: "X + y < X" by (auto intro: lt_if_lt_if_mem)
      with sub mem.IH show ?thesis by auto
    qed simp
  qed
qed

lemma not_add_mem_left [iff]: "\<not>(X + Y \<in> X)"
  using subset_mem_trans_closure_self lt_iff_mem_trans_closure by auto

lemma mem_trans_closure_bin_inter_lift_eq_empty [simp]: "mem_trans_closure X \<inter> lift X Y = {}"
  by (auto simp: lift_eq_image_add simp flip: lt_iff_mem_trans_closure)

lemma bin_inter_lift_self_eq_empty [simp]: "X \<inter> lift X Y = {}"
  using mem_trans_closure_bin_inter_lift_eq_empty subset_mem_trans_closure_self by blast

lemma lift_bin_inter_self_eq_empty [simp]: "lift X Y \<inter> X = {}"
  using bin_inter_lift_self_eq_empty by blast

lemma lift_eq_lift_if_bin_union_lift_eq_bin_union_lift:
  assumes "X \<union> lift X Y = X \<union> lift X Z"
  shows "lift X Y = lift X Z"
  using assms bin_inter_lift_self_eq_empty by blast

paragraph\<open>Proposition 3.4\<close>

lemma lift_injective_right: "injective (lift X)"
proof (rule injectiveI)
  fix Y Z assume "lift X Y = lift X Z"
  then show "Y = Z"
  proof (induction Y arbitrary: Z rule: mem_induction)
    case (mem Y)
    {
      fix U V u assume uvassms: "U \<in> {Y, Z}" "V \<in> {Y, Z}" "U \<noteq> V" "u \<in> U"
      with mem have "X + u \<in> lift X V" by (auto simp: lift_eq_repl_add)
      then obtain v where "v \<in> V" "X + u = X + v" using lift_eq_repl_add by auto
      then have "X \<union> lift X u  = X \<union> lift X v" by (simp add: add_eq_bin_union_lift)
      with bin_inter_lift_self_eq_empty have "lift X u = lift X v" by blast
      with uvassms \<open>v \<in> V\<close> mem.IH have "u \<in> V" by auto
    }
    then show ?case by blast
  qed
qed

lemma add_injective_right: "injective (add X)"
  using lift_injective_right lift_eq_image_add  by auto

corollary add_eq_add_if_eq_right [dest, simp]: "X + Y = X + Z \<Longrightarrow> Y = Z"
  using add_injective_right by (blast dest: injectiveD)

lemma mem_if_add_mem_add:
  assumes "X + Y \<in> X + Z"
  shows "Y \<in> Z"
proof -
  have "X + Z = X \<union> lift X Z" by (simp only: add_eq_bin_union_lift)
  with assms have "X + Y \<in> lift X Z" by auto
  also have "... = {X + z| z \<in> Z}" by (simp add: lift_eq_image_add)
  finally have "X + Y \<in> {X + z| z \<in> Z}" .
  then show "Y \<in> Z" by blast
qed

corollary add_mem_add_iff_mem: "X + Y \<in> X + Z \<longleftrightarrow> Y \<in> Z"
  using mem_if_add_mem_add add_mem_add_if_mem by blast

lemma mono_lift: "mono (lift X)"
  by (auto simp: lift_eq_repl_add)

lemma subset_if_lift_subset_lift: "lift X Y \<subseteq> lift X Z \<Longrightarrow> Y \<subseteq> Z"
  by (auto simp: lift_eq_repl_add)

corollary lift_subset_lift_iff_subset: "lift X Y \<subseteq> lift X Z \<longleftrightarrow> Y \<subseteq> Z"
  using subset_if_lift_subset_lift mono_lift[of X] by (auto del: subsetI)

lemma mono_add: "mono ((+) X)"
proof (intro monoI[of "(+) X", simplified])
  fix Y Z assume "Y \<subseteq> Z"
  then have "lift X Y \<subseteq> lift X Z" by (simp only: lift_subset_lift_iff_subset)
  then show "X + Y \<subseteq> X + Z" by (auto simp: add_eq_bin_union_lift)
qed

lemma subset_if_add_subset_add:
  assumes "X + Y \<subseteq> X + Z"
  shows "Y \<subseteq> Z"
proof-
  have "X + Z = X \<union> lift X Z" by (simp only: add_eq_bin_union_lift)
  with assms have "X + Y \<subseteq> X \<union> lift X Z" by simp
  then have "lift X Y \<subseteq> X \<union> (lift X Z)" by (auto simp: add_eq_bin_union_lift)
  moreover have "lift X Y \<inter> X = {}" by simp
  ultimately have "lift X Y \<subseteq> lift X Z" by blast
  then show ?thesis by (simp only: lift_subset_lift_iff_subset)
qed

corollary add_subset_add_iff_subset: "X + Y \<subseteq> X + Z \<longleftrightarrow> Y \<subseteq> Z"
  using subset_if_add_subset_add mono_add[of X] by (auto del: subsetI)

corollary lift_subset_self [simp]: "lift x y \<subseteq> x \<longleftrightarrow> y = 0"
  by (auto simp: lift_eq_repl_add bin_inter_eq_left_iff_subset)

end
