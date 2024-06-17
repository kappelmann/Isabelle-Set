\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Bijections\<close>
theory HOTG_Functions_Bijection
  imports
    HOTG_Functions_Evaluation
    HOTG_Functions_Injective
    Transport.Functions_Bijection
begin

definition "bijection_on_set (A :: set) (B :: set) :: (set \<Rightarrow> set) \<Rightarrow> (set \<Rightarrow> set) \<Rightarrow> bool \<equiv>
  bijection_on (mem_of A) (mem_of B)"
adhoc_overloading bijection_on bijection_on_set
definition "set_bijection_on_pred (P :: set \<Rightarrow> bool) (Q :: set \<Rightarrow> bool) (f :: set) (g :: set) :: bool
  \<equiv> bijection_on P Q (eval f) (eval g)"
adhoc_overloading bijection_on set_bijection_on_pred
definition "set_bijection_on_set (A :: set) (B :: set) :: set \<Rightarrow> set \<Rightarrow> bool \<equiv>
  bijection_on (mem_of A) (mem_of B)"
adhoc_overloading bijection_on set_bijection_on_set

lemma bijection_on_set_eq_bijection_on_pred [simp]:
  "(bijection_on (A :: set) (B :: set) :: (set \<Rightarrow> set) \<Rightarrow> (set \<Rightarrow> set) \<Rightarrow> bool) =
    bijection_on (mem_of A) (mem_of B)"
  unfolding bijection_on_set_def by simp

lemma bijection_on_set_eq_bijection_on_pred_uhint [uhint]:
  assumes "P \<equiv> mem_of A"
  and "Q \<equiv> mem_of B"
  shows "bijection_on A B :: (set \<Rightarrow> set) \<Rightarrow> (set \<Rightarrow> set) \<Rightarrow> bool \<equiv> bijection_on P Q"
  using assms by simp

lemma bijection_on_set_iff_bijection_on_pred [iff]:
  "bijection_on A B (f :: set \<Rightarrow> set) (g :: set \<Rightarrow> set) \<longleftrightarrow> bijection_on (mem_of A) (mem_of B) f g"
  by simp

lemma set_bijection_on_pred_iff_bijection_on_pred [iff]:
  "bijection_on (P :: set \<Rightarrow> bool) (Q :: set \<Rightarrow> bool) (f :: set) (g :: set) \<longleftrightarrow>
    bijection_on P Q (eval f) (eval g)"
  unfolding set_bijection_on_pred_def by simp

lemma set_bijection_on_pred_eq_bijection_on_pred_uhint [uhint]:
  assumes "f' \<equiv> eval f"
  and "g' \<equiv> eval g"
  and "P \<equiv> P'"
  and "Q \<equiv> Q'"
  shows "bijection_on (P :: set \<Rightarrow> bool) (Q :: set \<Rightarrow> bool) (f :: set) (g :: set) \<equiv>
    bijection_on P' Q' f' g'"
  using assms by simp

lemma set_bijection_on_set_eq_set_bijection_on_pred [simp]:
  "(bijection_on (A :: set) (B :: set) :: set \<Rightarrow> set \<Rightarrow> bool) = bijection_on (mem_of A) (mem_of B)"
  unfolding set_bijection_on_set_def by simp

lemma set_bijection_on_set_eq_set_bijection_on_pred_uhint [uhint]:
  assumes "P \<equiv> mem_of A"
  and "Q \<equiv> mem_of B"
  shows "bijection_on (A :: set) B :: set \<Rightarrow> set \<Rightarrow> bool \<equiv> bijection_on P Q"
  using assms by simp

lemma set_bijection_on_set_iff_set_bijection_on_pred [iff]:
  "bijection_on A B (f :: set) (g :: set) \<longleftrightarrow> bijection_on (mem_of A) (mem_of B) f g"
  by simp

lemma bijection_on_image_if_injective_on:
  assumes "injective_on X f"
  obtains g where "bijection_on X (image f X) f g"
proof
  define P where "P y x \<longleftrightarrow> x \<in> X \<and> f x = y" for y x
  let ?g = "\<lambda>y. THE x. P y x"
  have inv: "?g y \<in> X \<and> f (?g y) = y" if "y \<in> image f X" for y
  proof -
    from that obtain x where hx: "P y x" using P_def by auto
    moreover then have "x = x'" if "P y x'" for x' using P_def that assms
      by (auto dest: injective_onD)
    ultimately have "P y (?g y)" using theI[of "P y"] by blast
    then show ?thesis using P_def by auto
  qed
  moreover have "?g (f x) = x" if "x \<in> X" for x
  proof -
    have "?g (f x) \<in> X \<and> f (?g (f x)) = f x" using that inv by auto
    then show ?thesis using assms that by (auto dest: injective_onD)
  qed
  ultimately show "bijection_on X (image f X) f ?g"
    by (urule bijection_onI where chained = insert) auto
qed

end