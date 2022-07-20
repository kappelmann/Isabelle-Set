subsection \<open>Monotonicity\<close>
theory Functions_Monotone
  imports
    Binary_Relations_Finer
    Function_Relators
begin

definition "dep_monotone R S f \<equiv> ([x y \<Colon> R] \<Rrightarrow> S x y) f f"

abbreviation "monotone R S \<equiv> dep_monotone R (\<lambda>_ _. S)"

lemma dep_monotone_if_Dep_Fun_Rel_self:
  assumes "([x y \<Colon> R] \<Rrightarrow> S x y) f f"
  shows "dep_monotone R S f"
  unfolding dep_monotone_def using assms .

lemma dep_monotoneI:
  assumes "\<And>x y. R x y \<Longrightarrow> S x y (f x) (f y)"
  shows "dep_monotone R S f"
  using assms by (intro dep_monotone_if_Dep_Fun_Rel_self Dep_Fun_RelI)

lemma Dep_Fun_Rel_self_if_dep_monotone:
  assumes "dep_monotone R S f"
  shows "([x y \<Colon> R] \<Rrightarrow> S x y) f f"
  using assms unfolding dep_monotone_def .

corollary Dep_Fun_Rel_self_iff_dep_monotone:
  "([x y \<Colon> R] \<Rrightarrow> S x y) f f \<longleftrightarrow> dep_monotone R S f"
  using dep_monotone_if_Dep_Fun_Rel_self Dep_Fun_Rel_self_if_dep_monotone by blast

lemma dep_monotoneD:
  assumes "dep_monotone R S f"
  and "R x y"
  shows "S x y (f x) (f y)"
  using assms by (blast dest: Dep_Fun_Rel_self_if_dep_monotone Dep_Fun_RelD)

lemma dep_monotoneE:
  assumes "dep_monotone R S f"
  and "R x y"
  obtains "S x y (f x) (f y)"
  using assms by (blast dest: Dep_Fun_Rel_self_if_dep_monotone Dep_Fun_RelD)

lemma monotone_rel_inv_if_monotone:
  assumes "monotone R S f"
  shows "monotone (rel_inv R) (rel_inv S) f"
  using assms by (intro dep_monotone_if_Dep_Fun_Rel_self Dep_Fun_Rel_inv_if_Dep_Fun_Rel)
    (blast dest: Dep_Fun_Rel_self_if_dep_monotone)

lemma dep_monotone_in_dom_if_rel:
  assumes "dep_monotone R S f"
  and "R x y"
  shows "in_dom (S x y) (f x)"
  using assms by (intro in_domI) (elim dep_monotoneE)

corollary monotone_in_dom_if_in_dom:
  assumes "monotone R S f"
  and "in_dom R x"
  shows "in_dom S (f x)"
  using assms by (elim in_domE) (rule dep_monotone_in_dom_if_rel)

lemma dep_monotone_in_codom_if_rel:
  assumes "dep_monotone R S f"
  and "R x y"
  shows "in_codom (S x y) (f y)"
  using assms by (intro in_codomI) (elim dep_monotoneE)

corollary monotone_in_codom_if_in_codom:
  assumes "monotone R S f"
  and "in_codom R y"
  shows "in_codom S (f y)"
  using assms by (elim in_codomE) (rule dep_monotone_in_codom_if_rel)

lemma monotone_compI:
  assumes mono1: "monotone R S f"
  and mono2: "monotone T U g"
  and S_f_finer: "\<And>x y. S (f x) (f y) \<Longrightarrow> T (f x) (f y)"
  shows "monotone R U (g \<circ> f)"
  using assms by (intro dep_monotone_if_Dep_Fun_Rel_self Dep_Fun_Rel_compI)
    (fastforce dest: Dep_Fun_Rel_self_if_dep_monotone)+

lemma monotone_comp_if_finer_if_monotone:
  assumes "monotone R S f"
  and "monotone T U g"
  and "S \<sqsubseteq> T"
  shows "monotone R U (g \<circ> f)"
  by (rule monotone_compI[OF assms(1-2) finerD[OF assms(3)]])

lemma monotone_comp_if_monotone:
  assumes "monotone R S f"
  and "monotone S T g"
  shows "monotone R T (g \<circ> f)"
  using assms by (intro monotone_compI)

lemma monotone_self_id: "monotone R R id"
  by (rule dep_monotoneI) simp

lemma finer_if_monotone_id:
  assumes "monotone R S id"
  shows "R \<sqsubseteq> S"
  using assms by (intro finerI) (fastforce dest: dep_monotoneD)

lemma monotone_id_if_finer:
  assumes "R \<sqsubseteq> S"
  shows "monotone R S id"
  using assms by (intro dep_monotoneI) (fastforce dest: finerD)

corollary monotone_id_iff_finer: "monotone R S id \<longleftrightarrow> R \<sqsubseteq> S"
  using monotone_id_if_finer finer_if_monotone_id by blast

lemma monotone_contravariant_left:
  assumes mono: "monotone S T f"
  and finer: "R \<sqsubseteq> S"
  shows "monotone R T f"
proof -
  from finer have "monotone R S id" by (rule monotone_id_if_finer)
  with mono have "monotone R T (f \<circ> id)" by (intro monotone_comp_if_monotone)
  then show ?thesis by simp
qed

lemma monotone_covariant_right:
  assumes mono: "monotone R S f"
  and finer: "S \<sqsubseteq> S'"
  shows "monotone R S' f"
proof -
  from finer have "monotone S S' id" by (rule monotone_id_if_finer)
  with mono have "monotone R S' (id \<circ> f)" by (rule monotone_comp_if_monotone)
  then show ?thesis by simp
qed


end