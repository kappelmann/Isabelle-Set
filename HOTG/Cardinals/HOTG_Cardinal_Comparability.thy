theory HOTG_Cardinal_Comparability
  imports
    HOTG_Equipollence
    HOTG_Set_Difference
    HOTG_Ordinals_Omega
    HOTG_Functions_Monotone
    HOTG_Cardinals_Base
begin

unbundle no_HOL_groups_syntax
unbundle no_HOL_order_syntax

definition fun_pow :: "('a \<Rightarrow> 'a) \<Rightarrow> set \<Rightarrow> 'a \<Rightarrow> 'a" where
"fun_pow f = omega_rec id (\<lambda>g. f \<circ> g)"

bundle hotg_fun_pow_syntax begin notation fun_pow (infixl "#" 50) end
bundle no_hotg_fun_pow_syntax begin no_notation fun_pow (infixl "#" 50) end
unbundle hotg_fun_pow_syntax

lemma fun_pow_succ:
  assumes "n \<in> \<omega>"
  shows "(f # succ n) x = f ((f # n) x)"
  unfolding fun_pow_def omega_rec_succ[OF assms] by simp

lemma fun_pow_zero_eq_id [simp]: "f # 0 = id" 
  unfolding fun_pow_def omega_rec_zero by auto

lemma fun_pow_one_eq_self [simp]: "f # 1 = f" 
  unfolding fun_pow_succ[OF zero_mem_omega] by auto

definition "trans_image f X = (\<Union>n \<in> \<omega> \<setminus> {0}. image (f # n) X)"

lemma image_subset_trans_image: "image f X \<subseteq> trans_image f X" unfolding trans_image_def by force

lemma image_trans_image_subset_trans_image: "image f (trans_image f X) \<subseteq> trans_image f X"
proof
  fix y assume "y \<in> image f (trans_image f X)"
  then obtain x n where "x \<in> X" "n \<in> \<omega>" "y = f ((f # n) x)" unfolding trans_image_def by auto
  then have "y = (f # succ n) x" using fun_pow_succ[symmetric] by auto
  then show "y \<in> trans_image f X" 
    unfolding trans_image_def using \<open>x \<in> X\<close> \<open>n \<in> \<omega>\<close> succ_ne_zero by auto
qed

lemma trans_image_fixpoint: "trans_image f X = image f X \<union> image f (trans_image f X)"
proof -
  have "trans_image f X \<subseteq> image f X \<union> image f (trans_image f X)"
  proof
    fix y assume "y \<in> trans_image f X"
    then obtain x n where "x \<in> X" "n \<in> \<omega> \<setminus> {0}" "y = (f # n) x" unfolding trans_image_def by auto
    then consider "n = 1" | m where "m \<in> \<omega> \<setminus> {0}" "n = succ m" by (auto elim: mem_omegaE)
    then show "y \<in> image f X \<union> image f (trans_image f X)"
    proof cases
      case 1
      then show ?thesis using \<open>x \<in> X\<close> \<open>y = (f # n) x\<close> by auto
    next
      case 2
      then have "y = f ((f # m) x)" using \<open>y = (f # n) x\<close> fun_pow_succ by auto
      then show ?thesis using \<open>x \<in> X\<close> \<open>m \<in> \<omega> \<setminus> {0}\<close> unfolding trans_image_def by fastforce
    qed
  qed
  then show ?thesis using image_subset_trans_image image_trans_image_subset_trans_image by auto
qed

(* Source paper: https://web.williams.edu/Mathematics/lg5/200/CSB.pdf *)
(* Special case of Cantor-Bernstein *)
lemma equipollent_subset_if_injective_map_to_subset:
  fixes A B :: set and f :: "set \<Rightarrow> set"
  assumes "B \<subseteq> A" "(A \<Rightarrow> B) f" and inj: "injective_on A f"
  shows "A \<approx> B"
proof -
  have preliminary_consideration: "A \<approx> B" 
    if "B = C \<union> D" "C \<inter> D = \<emptyset>" "image f (A \<setminus> D) = C" for C D
  proof -
    define g where "g x = (if x \<in> D then x else f x)" for x
    have "injective_on A g"
    proof (urule injective_onI)
      fix x y presume asms: "x \<in> A" "y \<in> A" "g x = g y"
      show "x = y"
      proof (cases "x \<in> D")
        case True
        then have "y \<in> D" using \<open>y \<in> A\<close> \<open>image f (A \<setminus> D) = C\<close> \<open>g x = g y\<close> g_def \<open>C \<inter> D = \<emptyset>\<close> by auto
        then show ?thesis using \<open>x \<in> D\<close> \<open>g x = g y\<close> g_def by auto
      next
        case False
        moreover then have "y \<notin> D" 
          using g_def \<open>g x = g y\<close> \<open>x \<in> A\<close> \<open>image f (A \<setminus> D) = C\<close> \<open>C \<inter> D = \<emptyset>\<close> by auto
        ultimately have "f x = f y" using g_def \<open>g x = g y\<close> by auto
        then show ?thesis using inj \<open>x \<in> A\<close> \<open>y \<in> A\<close> by (auto dest: injective_onD)
      qed
    qed auto
    moreover have "image g A = B"
    proof
      fix y assume "y \<in> image g A"
      then show "y \<in> B" using g_def \<open>image f (A \<setminus> D) = C\<close> \<open>B = C \<union> D\<close> by auto
    next
      fix b assume "b \<in> B"
      show "b \<in> image g A" 
      proof (cases "b \<in> D")
        case True
        then show ?thesis using \<open>b \<in> B\<close> \<open>B \<subseteq> A\<close> g_def by auto
      next
        case False
        then have "b \<in> C" using \<open>b \<in> B\<close> \<open>B = C \<union> D\<close> by auto
        then obtain a where "a \<in> A" "a \<notin> D" "b = f a" using \<open>image f (A \<setminus> D) = C\<close> by auto
        then show ?thesis using g_def by auto
      qed
    qed
    ultimately show ?thesis 
      using bijection_on_image_the_inverse_on_if_injective_on by (auto intro!: equipollentI)
  qed

  define C where "C = trans_image f (A \<setminus> B)"
  have "C \<subseteq> B"
  proof -
    have "n \<noteq> 0 \<Longrightarrow> image (f # n) (A \<setminus> B) \<subseteq> B" if "n \<in> \<omega>" for n using that
    proof (induction rule: omega_induct)
      case (succ n)
      then have "(f # succ n) x \<in> B" if "n \<noteq> 0" "x \<in> (A \<setminus> B)" for x 
        using assms fun_pow_succ[of n f x] that by auto
      then show ?case using \<open>(A \<Rightarrow> B) f\<close> by (cases "n = 0") auto
    qed (auto simp: assms)
    then show ?thesis unfolding C_def trans_image_def by auto
  qed
  moreover define D where "D = B \<setminus> C"
  ultimately have B_disjoint_union: "B = C \<union> D" "C \<inter> D = \<emptyset>" by auto
  then have "image f (A \<setminus> D) = image f (A \<setminus> B) \<union> image f C" using\<open>B \<subseteq> A\<close> by auto
  then have "image f (A \<setminus> D) = C" using trans_image_fixpoint C_def by auto
  then show ?thesis using preliminary_consideration B_disjoint_union by blast
qed

lemma injective_on_comp_if_injective_on:
  fixes X Y :: set and f g :: "set \<Rightarrow> set"
  assumes "(X \<Rightarrow> Y) f"
  assumes "injective_on X f" "injective_on Y g"
  shows "injective_on X (g \<circ> f)"
proof (urule injective_onI)
  fix x\<^sub>1 x\<^sub>2 presume "x\<^sub>1 \<in> X" "x\<^sub>2 \<in> X" "g (f x\<^sub>1) = g (f x\<^sub>2)"
  then have "f x\<^sub>1 = f x\<^sub>2" using \<open>injective_on Y g\<close> \<open>(X \<Rightarrow> Y) f\<close> by (auto dest: injective_onD)
  then show "x\<^sub>1 = x\<^sub>2" using \<open>injective_on X f\<close> \<open>x\<^sub>1 \<in> X\<close> \<open>x\<^sub>2 \<in> X\<close> by (auto dest: injective_onD)
qed auto

theorem cantor_bernstein:
  fixes X Y :: set and f g :: "set \<Rightarrow> set"
  assumes "(X \<Rightarrow> Y) f" "(Y \<Rightarrow> X) g"
  assumes inj_f: "injective_on X f" and inj_g: "injective_on Y g"
  shows "X \<approx> Y"
proof -
  define X' where "X' = image f X"
  then have "X' \<subseteq> Y" using \<open>(X \<Rightarrow> Y) f\<close> by auto
  moreover have "injective_on Y (f \<circ> g)"
    using injective_on_comp_if_injective_on inj_f inj_g \<open>(Y \<Rightarrow> X) g\<close> by auto
  moreover have "(Y \<Rightarrow> X') (f \<circ> g)" using X'_def \<open>(Y \<Rightarrow> X) g\<close> by force
  ultimately have "Y \<approx> X'" using equipollent_subset_if_injective_map_to_subset by blast
  moreover from inj_f have "X \<approx> X'" 
    using bijection_on_image_the_inverse_on_if_injective_on X'_def by (auto intro!: equipollentI)
  ultimately show ?thesis 
    using symmetric_equipollent transitive_equipollent by (auto dest: symmetricD)
qed

corollary cardinality_le_if_injective_map:
  fixes f :: "set \<Rightarrow> set"
  assumes "(X \<Rightarrow> Y) f" "injective_on X f"
  shows "|X| \<le> |Y|"
proof (rule ccontr)
  assume "\<not> |X| \<le> |Y|"
  then have "|Y| < |X|" using ordinal_cardinality lt_if_not_le_if_ordinal by blast
  then have "|Y| \<subseteq> |X|" using ordinal_cardinality le_iff_subset_if_ordinal le_if_lt by blast
  obtain g\<^sub>X h\<^sub>X :: "set \<Rightarrow> set" where bijX: "bijection_on |X| X g\<^sub>X h\<^sub>X" 
    using cardinality_equipollent_self by blast
  obtain g\<^sub>Y h\<^sub>Y :: "set \<Rightarrow> set" where bijY: "bijection_on |Y| Y g\<^sub>Y h\<^sub>Y"
    using cardinality_equipollent_self by blast
  have "(|X| \<Rightarrow> X) g\<^sub>X" "injective_on |X| g\<^sub>X" 
    using mono_wrt_pred_if_bijection_on_left injective_on_if_bijection_on_left bijX by auto
  then have "injective_on |X| (f \<circ> g\<^sub>X)" 
    using injective_on_comp_if_injective_on \<open>injective_on X f\<close> by auto
  moreover have "(|X| \<Rightarrow> Y) (f \<circ> g\<^sub>X)" using \<open>(|X| \<Rightarrow> X) g\<^sub>X\<close> \<open>(X \<Rightarrow> Y) f\<close> by force
  moreover have "(Y \<Rightarrow> |Y|) h\<^sub>Y" "injective_on Y h\<^sub>Y"
    using mono_wrt_pred_if_bijection_on_right injective_on_if_bijection_on_right bijY by auto
  ultimately have "injective_on |X| (h\<^sub>Y \<circ> (f \<circ> g\<^sub>X))" using injective_on_comp_if_injective_on by auto
  moreover have "(|X| \<Rightarrow> |Y|) (h\<^sub>Y \<circ> (f \<circ> g\<^sub>X))" using \<open>(|X| \<Rightarrow> Y) (f \<circ> g\<^sub>X)\<close> \<open>(Y \<Rightarrow> |Y|) h\<^sub>Y\<close> by force
  ultimately have "|X| \<approx> |Y|" using \<open>|Y| \<subseteq> |X|\<close> equipollent_subset_if_injective_map_to_subset by blast
  then have "|X| = |Y|" using cardinality_eq_if_equipollent by force
  then show "False" using \<open>\<not> |X| \<le> |Y|\<close> by auto
qed

lemma injective_map_if_cardinality_leE:
  assumes "|X| \<le> |Y|"
  obtains f :: "set \<Rightarrow> set" where "(X \<Rightarrow> Y) f" "injective_on X f"
proof -
  obtain g\<^sub>X h\<^sub>X :: "set \<Rightarrow> set" where bijX: "bijection_on |X| X g\<^sub>X h\<^sub>X" 
    using cardinality_equipollent_self by blast
  obtain g\<^sub>Y h\<^sub>Y :: "set \<Rightarrow> set" where bijY: "bijection_on |Y| Y g\<^sub>Y h\<^sub>Y"
    using cardinality_equipollent_self by blast
  have "(X \<Rightarrow> |X|) h\<^sub>X" "injective_on X h\<^sub>X" 
    using mono_wrt_pred_if_bijection_on_right injective_on_if_bijection_on_right bijX by auto
  have "(|Y| \<Rightarrow> Y) g\<^sub>Y" "injective_on |Y| g\<^sub>Y"
    using mono_wrt_pred_if_bijection_on_left injective_on_if_bijection_on_left bijY by auto
  have "|X| \<subseteq> |Y|" using ordinal_cardinality le_iff_subset_if_ordinal assms by blast
  then have "(X \<Rightarrow> |Y|) h\<^sub>X" using \<open>(X \<Rightarrow> |X|) h\<^sub>X\<close> by auto 
  then have "injective_on X (g\<^sub>Y \<circ> h\<^sub>X)"
    using \<open>injective_on X h\<^sub>X\<close> \<open>injective_on |Y| g\<^sub>Y\<close> injective_on_comp_if_injective_on by auto
  moreover have "(X \<Rightarrow> Y) (g\<^sub>Y \<circ> h\<^sub>X)" using \<open>(X \<Rightarrow> |Y|) h\<^sub>X\<close> \<open>(|Y| \<Rightarrow> Y) g\<^sub>Y\<close> by force
  ultimately show ?thesis using that by auto
qed

corollary cardinality_le_iff_injective_map:
  shows "|X| \<le> |Y| \<longleftrightarrow> (\<exists>(f :: set \<Rightarrow> set) : X \<Rightarrow> Y. injective_on X f)"
  using cardinality_le_if_injective_map injective_map_if_cardinality_leE by force

end