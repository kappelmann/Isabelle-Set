\<^marker>\<open>creator "Niklas Krofta"\<close>
\<^marker>\<open>contributor "Kevin Kappelmann"\<close>
theory HOTG_Cantor_Schroeder_Bernstein
  imports
    HOTG_Cardinals_Base
    HOTG_Functions_Power
    Transport.Functions_Injective
begin

paragraph \<open>Summary\<close>
text \<open>A formalisation of the Cantor–Schröder–Bernstein theorem based on
\<^url>\<open>https://web.williams.edu/Mathematics/lg5/200/CSB.pdf\<close>.\<close>

definition "trans_image f X \<equiv> \<Union>n \<in> (\<omega> \<setminus> {0}). image f\<^bsup>n\<^esup> X"

lemma mem_trans_imageI [intro]:
  assumes "n \<in> (\<omega> \<setminus> {0})"
  and "x \<in> image f\<^bsup>n\<^esup> X"
  shows "x \<in> trans_image f X"
  using assms unfolding trans_image_def by blast

lemma mem_trans_imageE [elim]:
  assumes "x \<in> trans_image f X"
  obtains n where "n \<in> (\<omega> \<setminus> {0})" "x \<in> image f\<^bsup>n\<^esup> X"
  using assms unfolding trans_image_def by blast

lemma image_subset_trans_image: "image f X \<subseteq> trans_image f X"
  by force

lemma image_trans_image_subset_trans_image: "image f (trans_image f X) \<subseteq> trans_image f X"
proof (rule subsetI)
  fix y assume "y \<in> image f (trans_image f X)"
  then obtain x n where "x \<in> X" "n \<in> \<omega>" "y = f (f\<^bsup>n\<^esup> x)" by fastforce
  moreover then have "... = f\<^bsup>succ n\<^esup> x" by simp
  ultimately show "y \<in> trans_image f X" by fastforce
qed

lemma trans_image_eq_image_bin_union_image_trans_image:
  "trans_image f X = image f X \<union> image f (trans_image f X)"
proof -
  have "trans_image f X \<subseteq> image f X \<union> image f (trans_image f X)"
  proof (rule subsetI)
    fix y assume "y \<in> trans_image f X"
    then obtain x n where "x \<in> X" "n \<in> (\<omega> \<setminus> {0})" "y = f\<^bsup>n\<^esup> x" by fastforce
    then consider "n = 1" | m where "m \<in> (\<omega> \<setminus> {0})" "n = succ m" by (auto elim: mem_omegaE)
    then show "y \<in> image f X \<union> image f (trans_image f X)"
    proof cases
      case 1 then show ?thesis using \<open>x \<in> X\<close> \<open>y = f\<^bsup>n\<^esup> x\<close> by auto
    next
      case 2
      then have "y = f (f\<^bsup>m\<^esup> x)" using \<open>y = f\<^bsup>n\<^esup> x\<close> by auto
      then show ?thesis using \<open>x \<in> X\<close> \<open>m \<in> (\<omega> \<setminus> {0})\<close> by fastforce
    qed
  qed
  with image_subset_trans_image image_trans_image_subset_trans_image show ?thesis by auto
qed

lemma equipollent_if_subset_if_injective_on_if_mono_wrt:
  assumes "(A \<Rightarrow> B) (f :: set \<Rightarrow> set)"
  and inj: "injective_on A f"
  and "B \<subseteq> A"
  shows "A \<approx> B"
proof -
  have preliminary_consideration: "A \<approx> B" if "B = C \<union> D" "disjoint C D" "image f (A \<setminus> D) = C" for C D
  proof -
    define g where "g x \<equiv> if x \<in> D then x else f x" for x
    have "injective_on A g"
    proof (urule injective_onI)
      fix x y presume asms: "x \<in> A" "y \<in> A" "g x = g y"
      show "x = y"
      proof (cases "x \<in> D")
        case True
        then have "y \<in> D"
          using \<open>y \<in> A\<close> \<open>image f (A \<setminus> D) = C\<close> \<open>g x = g y\<close> g_def \<open>disjoint C D\<close> by fastforce
        then show ?thesis using \<open>x \<in> D\<close> \<open>g x = g y\<close> g_def by auto
      next
        case False
        moreover then have "y \<notin> D"
          using g_def \<open>g x = g y\<close> \<open>x \<in> A\<close> \<open>image f (A \<setminus> D) = C\<close> \<open>disjoint C D\<close> by fastforce
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
        case True then show ?thesis using \<open>b \<in> B\<close> \<open>B \<subseteq> A\<close> g_def by auto
      next
        case False
        then have "b \<in> C" using \<open>b \<in> B\<close> \<open>B = C \<union> D\<close> by auto
        then obtain a where "a \<in> A" "a \<notin> D" "b = f a" using \<open>image f (A \<setminus> D) = C\<close> by auto
        then show ?thesis using g_def by auto
      qed
    qed
    ultimately show ?thesis using bijection_on_image_the_inverse_on_if_injective_on by blast
  qed
  define C where "C = trans_image f (A \<setminus> B)"
  have "C \<subseteq> B"
  proof -
    have "n \<noteq> 0 \<Longrightarrow> image f\<^bsup>n\<^esup> (A \<setminus> B) \<subseteq> B" if "n \<in> \<omega>" for n using that
    proof (induction rule: omega_induct)
      case (succ n)
      then have "f\<^bsup>succ n\<^esup> x \<in> B" if "n \<noteq> 0" "x \<in> (A \<setminus> B)" for x using assms that by auto
      then show ?case using \<open>(A \<Rightarrow> B) f\<close> by (cases "n = 0") auto
    qed (use assms in auto)
    then show ?thesis unfolding C_def by fastforce
  qed
  moreover define D where "D = B \<setminus> C"
  ultimately have B_disjoint_union: "B = C \<union> D" "disjoint C D" by auto
  then have "image f (A \<setminus> D) = image f (A \<setminus> B) \<union> image f C" using \<open>B \<subseteq> A\<close> by auto
  then have "image f (A \<setminus> D) = C" using trans_image_eq_image_bin_union_image_trans_image C_def by auto
  then show ?thesis using preliminary_consideration B_disjoint_union by blast
qed

theorem equipollent_if_injective_on_if_injective_onI:
  fixes f g :: "set \<Rightarrow> set"
  assumes "(X \<Rightarrow> Y) f" "(Y \<Rightarrow> X) g"
  and inj_f: "injective_on X f"
  and inj_g: "injective_on Y g"
  shows "X \<approx> Y"
proof -
  let ?X' = "image f X"
  have "?X' \<subseteq> Y" using \<open>(X \<Rightarrow> Y) f\<close> by auto
  moreover from inj_f inj_g have "injective_on Y (f \<circ> g)"
    using injective_on_comp_if_injective_onI \<open>(Y \<Rightarrow> X) g\<close> by auto
  moreover have "(Y \<Rightarrow> ?X') (f \<circ> g)" using \<open>(Y \<Rightarrow> X) g\<close> by fastforce
  ultimately have "Y \<approx> ?X'" using equipollent_if_subset_if_injective_on_if_mono_wrt by blast
  moreover from inj_f have "X \<approx> ?X'" using bijection_on_image_the_inverse_on_if_injective_on by blast
  ultimately show "X \<approx> Y" using partial_equivalence_rel_equipollent by (blast dest: symmetricD)
qed

end