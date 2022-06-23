section \<open>Lifting between Sets\<close>
theory Lifting_Sets
  imports
    HOTG.Bounded_Quantifiers
    Lifting_Triples
begin

subsection \<open>Basic Properties On Set Functions\<close>

definition "injective_on A f \<equiv> \<forall>x x' \<in> A. f x = f x' \<longrightarrow> x = x'"

lemma injective_onI:
  assumes "\<And>x x'. x \<in> A \<Longrightarrow> x' \<in> A \<Longrightarrow> f x = f x' \<Longrightarrow> x = x'"
  shows "injective_on A f"
  unfolding injective_on_def using assms by blast

lemma injective_onD:
  assumes "injective_on A f"
  and "x \<in> A" "x' \<in> A"
  and "f x = f x'"
  shows "x = x'"
  using assms unfolding injective_on_def by blast

definition "inverse_on A f g \<equiv> \<forall>x \<in> A. g (f x) = x"

lemma inverse_onI:
  assumes "\<And>x. x \<in> A \<Longrightarrow> g (f x) = x"
  shows "inverse_on A f g"
  unfolding inverse_on_def using assms by blast

lemma inverse_onD:
  assumes "inverse_on A f g"
  and "x \<in> A"
  shows "g (f x) = x"
  using assms unfolding inverse_on_def by blast

lemma injective_on_if_inverse_on:
  assumes inv: "inverse_on A f g"
  shows "injective_on A f"
proof (rule injective_onI)
  fix x x'
  assume x_in_A: "x \<in> A" and x'_in_A: "x' \<in> A" and f_x_eq_f_x': "f x = f x'"
  have "x = g (f x)" using inv x_in_A by (intro inverse_onD[symmetric])
  also have "... = g (f x')" by (simp only: f_x_eq_f_x')
  also have "... = x'" using inv x'_in_A by (intro inverse_onD)
  finally show "x = x'" .
qed

definition bijection :: "set \<Rightarrow> set \<Rightarrow> (set \<Rightarrow> set) \<Rightarrow> (set \<Rightarrow> set) \<Rightarrow> bool"
  where "bijection A B f g \<equiv>
    (\<forall>x \<in> A. f x \<in> B) \<and>
    (\<forall>y \<in> B. g y \<in> A) \<and>
    inverse_on A f g \<and>
    inverse_on B g f"

lemma bijectionI:
  assumes "\<And>x. x \<in> A \<Longrightarrow> f x \<in> B"
  and "\<And>y. y \<in> B \<Longrightarrow> g y \<in> A"
  and "inverse_on A f g"
  and "inverse_on B g f"
  shows "bijection A B f g"
  using assms unfolding bijection_def by blast

lemma app_mem_if_mem_if_bijection:
  assumes "bijection A B f g"
  and "x \<in> A"
  shows "f x \<in> B"
  using assms unfolding bijection_def by blast

lemma app_mem_if_mem_if_bijection':
  assumes "bijection A B f g"
  and "y \<in> B"
  shows "g y \<in> A"
  using assms unfolding bijection_def by blast

lemma inverse_on_if_bijection:
  assumes "bijection A B f g"
  shows "inverse_on A f g"
  using assms unfolding bijection_def by blast

lemma inverse_on_if_bijection':
  assumes "bijection A B f g"
  shows "inverse_on B g f"
  using assms unfolding bijection_def by blast

lemma app_app_eq_self_if_mem_if_bijection:
  assumes "bijection A B f g"
  and "x \<in> A"
  shows "g (f x) = x"
  using assms inverse_on_if_bijection by (intro inverse_onD)

lemma app_app_eq_self_if_mem_if_bijection':
  assumes "bijection A B f g"
  and "y \<in> B"
  shows "f (g y) = y"
  using assms inverse_on_if_bijection' by (intro inverse_onD)

lemma bijection_if_bijection:
  assumes "bijection A B f g"
  shows "bijection B A g f"
  using assms
  by (intro bijectionI) (blast dest: inverse_on_if_bijection inverse_on_if_bijection'
    app_mem_if_mem_if_bijection app_mem_if_mem_if_bijection')+

lemma injective_on_if_bijection:
  assumes "bijection A B f g"
  shows "injective_on A f"
  using assms by (intro injective_on_if_inverse_on inverse_on_if_bijection)

corollary injective_on_if_bijection':
  assumes "bijection A B f g"
  shows "injective_on B g"
  using bijection_if_bijection[OF assms] by (rule injective_on_if_bijection)

lemma bijection_id: "bijection A A id id"
  by (intro bijectionI inverse_onI) simp_all


subsection \<open>Relator For Bijective Sets\<close>

definition Iso_Rel :: "set \<Rightarrow> (set \<Rightarrow> set) \<Rightarrow> set \<Rightarrow> set \<Rightarrow> bool"
  where "Iso_Rel A f x y \<equiv> x \<in> A \<and> f x = y"

lemma Iso_RelI:
  assumes "x \<in> A"
  and "f x = y"
  shows "Iso_Rel A f x y"
  unfolding Iso_Rel_def using assms by blast

lemma Iso_RelE:
  assumes "Iso_Rel A f x y"
  obtains "x \<in> A" "f x = y"
  using assms unfolding Iso_Rel_def by blast

lemma right_unique_Iso_Rel: "right_unique (Iso_Rel A f)"
  by (rule right_uniqueI) (blast elim: Iso_RelE)

lemma z_property_Iso_Rel: "z_property (Iso_Rel A f)"
  using right_unique_Iso_Rel by (rule z_property_if_right_unique)

lemma lifting_relation_Iso_Rel: "lifting_relation (Iso_Rel A f)"
  using z_property_Iso_Rel by (rule lifting_relation_if_z_property)

lemma injective_Iso_Rel_if_injective_on:
  assumes "injective_on A f"
  shows "injective (Iso_Rel A f)"
proof (rule injectiveI)
  fix x x' y assume "Iso_Rel A f x y" "Iso_Rel A f x' y"
  then have "x \<in> A" "x' \<in> A" "f x = f x'" by (blast elim: Iso_RelE)+
  with assms show "x = x'" by (rule injective_onD)
qed

lemma mem_if_in_dom_Iso_Rel:
  assumes "in_dom (Iso_Rel A f) x"
  shows "x \<in> A"
  using assms by (blast elim: in_domE Iso_RelE)

lemma in_dom_Iso_Rel_if_mem:
  assumes "x \<in> A"
  shows "in_dom (Iso_Rel A f) x"
  using assms by (intro in_domI) (blast intro: Iso_RelI)

corollary in_dom_Iso_Rel_iff_mem: "in_dom (Iso_Rel A f) x \<longleftrightarrow> x \<in> A"
  using mem_if_in_dom_Iso_Rel in_dom_Iso_Rel_if_mem by blast

lemma in_codom_Iso_RelE:
  assumes "in_codom (Iso_Rel A f) y"
  obtains x where "x \<in> A" "f x = y"
  using assms by (blast elim: in_codomE Iso_RelE)

lemma in_codom_Iso_Rel_if_mem:
  assumes "x \<in> A"
  and "f x = y"
  shows "in_codom (Iso_Rel A f) y"
  using assms by (intro in_codomI) (blast intro: Iso_RelI)

lemma Iso_Rel_if_Iso_Rel_if_inverse_on:
  assumes f_type: "\<And>x. x \<in> A \<Longrightarrow> f x \<in> B"
  and inv: "inverse_on A f g"
  and Iso_Rel: "(Iso_Rel A f) x y"
  shows "(Iso_Rel B g) y x"
proof (rule Iso_RelI)
  from Iso_Rel have x_props: "x \<in> A" "f x = y" by (blast elim: Iso_RelE)+
  with inv show "g y = x" by (blast dest: inverse_onD)
  show "y \<in> B" using x_props by (blast intro: f_type)
qed

corollary Iso_Rel_if_Iso_Rel_if_bijection:
  assumes "bijection A B f g"
  and "(Iso_Rel A f) x y"
  shows "(Iso_Rel B g) y x"
  using assms by (intro Iso_Rel_if_Iso_Rel_if_inverse_on[of A f B g])
    (blast dest: app_mem_if_mem_if_bijection inverse_on_if_bijection)+

corollary Iso_Rel_if_Iso_Rel_if_bijection':
  assumes bij: "bijection A B f g"
  and "(Iso_Rel B g) y x"
  shows "(Iso_Rel A f) x y"
  using assms
  by (blast intro: Iso_Rel_if_Iso_Rel_if_bijection bijection_if_bijection)

corollary rel_inv_Iso_Rel_eq_Iso_Rel_if_bijection:
  assumes "bijection A B f g"
  shows "rel_inv (Iso_Rel A f) = Iso_Rel B g"
  using assms Iso_Rel_if_Iso_Rel_if_bijection Iso_Rel_if_Iso_Rel_if_bijection'
  by (blast intro: rel_invI dest: rel_invD)

(*TODO: could be generalised to more general relations and non-set functions*)
lemma lifting_triple_Iso_Rel_if_bijection:
  assumes bij: "bijection A B f g"
  shows "lifting_triple (Iso_Rel A f) f g"
proof (rule lifting_tripleI)
  {
    fix A f x assume "in_dom (Iso_Rel A f) x"
    then show "Iso_Rel A f x (f x)"
      by (blast intro: Iso_RelI dest: mem_if_in_dom_Iso_Rel)
  }
  note Iso_Rel_app_self = this
  fix y assume "in_codom (Iso_Rel A f) y"
  then have "in_dom (rel_inv (Iso_Rel A f)) y" by (subst in_dom_rel_inv_iff_in_codom)
  then have "in_dom (Iso_Rel B g) y"
    using bij by (simp only: rel_inv_Iso_Rel_eq_Iso_Rel_if_bijection)
  then have "(Iso_Rel B g) y (g y)" by (intro Iso_Rel_app_self)
  then have "rel_inv (Iso_Rel B g) (g y) y" by (rule rel_invI)
  then show "(Iso_Rel A f) (g y) y"
    using bijection_if_bijection[OF bij]
    by (simp only: rel_inv_Iso_Rel_eq_Iso_Rel_if_bijection)
qed (fact lifting_relation_Iso_Rel)

definition Eq_Rel :: "set \<Rightarrow> set \<Rightarrow> set \<Rightarrow> bool"
  where "Eq_Rel A \<equiv> Iso_Rel A id"

lemma Eq_Rel_eq_Iso_Rel: "Eq_Rel A = Iso_Rel A id"
  unfolding Eq_Rel_def ..

lemma Eq_RelI:
  assumes "x \<in> A"
  and "x = y"
  shows "Eq_Rel A x y"
  unfolding Eq_Rel_def using assms by (intro Iso_RelI) simp_all

lemma Eq_RelE:
  assumes "Eq_Rel A x y"
  obtains "x \<in> A" "x = y"
  using assms unfolding Eq_Rel_def by (elim Iso_RelE) simp

corollary Eq_Rel_iff_mem: "Eq_Rel A x x \<longleftrightarrow> x \<in> A"
  using Eq_RelI Eq_RelE by blast

lemma symmetric_Eq_Rel: "symmetric (Eq_Rel A)"
  by (rule symmetricI) (blast intro: Eq_RelI elim: Eq_RelE)

lemma transitive_Eq_Rel: "transitive (Eq_Rel A)"
  by (rule transitiveI) (blast intro: Eq_RelI elim: Eq_RelE)

lemma partial_equivalence_Eq_Rel: "partial_equivalence (Eq_Rel A)"
  using symmetric_Eq_Rel transitive_Eq_Rel
  by (rule partial_equivalenceI)

lemma injective_Eq_Rel: "injective (Eq_Rel A)"
  using bijection_id
  by (subst Eq_Rel_eq_Iso_Rel)
  (intro injective_Iso_Rel_if_injective_on injective_on_if_bijection)

lemma lifting_relation_Eq_Rel: "lifting_relation (Eq_Rel A)"
  by (subst Eq_Rel_eq_Iso_Rel) (rule lifting_relation_Iso_Rel)

lemma lifting_triple_Eq_Rel_id: "lifting_triple (Eq_Rel A) id id"
  using bijection_id
  by (subst Eq_Rel_eq_Iso_Rel) (intro lifting_triple_Iso_Rel_if_bijection)

lemma Eq_rep_Iso_Rel_eq_if_bijection:
  assumes biject: "bijection A B f g"
  shows "Eq_rep (Iso_Rel A f) = Eq_Rel A"
proof standard+
  fix x x' :: set
  {
    assume "x = x'"
    then have "Eq_rep (Iso_Rel A f) x x' \<longleftrightarrow> Eq_rep (Iso_Rel A f) x x" by simp
    also have "... \<longleftrightarrow> in_dom (Iso_Rel A f) x" by (rule Eq_rep_self_iff_in_dom)
    also have "... \<longleftrightarrow> x \<in> A" by (rule in_dom_Iso_Rel_iff_mem)
    also have "... \<longleftrightarrow> Eq_Rel A x x" by (rule Eq_Rel_iff_mem[symmetric])
    also have "... \<longleftrightarrow> Eq_Rel A x x'" by (simp only: \<open>x = x'\<close>)
    finally have 1: "Eq_rep (Iso_Rel A f) x x' \<longleftrightarrow> Eq_Rel A x x'" .
  }
  note 1 = this
  {
    have "injective (Iso_Rel A f)"
      using biject
      by (intro injective_Iso_Rel_if_injective_on injective_on_if_bijection)
    assume "Eq_rep (Iso_Rel A f) x x'"
    moreover then have "x = x'" using injectiveD[OF \<open>injective _\<close>] by (elim Eq_repE)
    ultimately show "Eq_Rel A x x'" using 1 by blast
  }
  assume "Eq_Rel A x x'"
  moreover then have "x = x'" using Eq_RelE by blast
  ultimately show "Eq_rep (Iso_Rel A f) x x'" using 1 by blast
qed


end