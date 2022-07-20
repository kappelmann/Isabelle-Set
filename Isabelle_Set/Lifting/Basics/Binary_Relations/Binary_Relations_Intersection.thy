subsection \<open>Intersection\<close>
theory Binary_Relations_Intersection
  imports
    Binary_Relations_Finer
begin

definition "rel_inter R S x y \<equiv> R x y \<and> S x y"

bundle notation_rel_inter begin notation rel_inter (infixl "\<sqinter>" 55) end
bundle no_notation_rel_inter begin no_notation rel_inter (infixl "\<sqinter>" 55) end
unbundle notation_rel_inter

lemma rel_interI:
  assumes "R x y"
  and "S x y"
  shows "(R \<sqinter> S) x y"
  using assms unfolding rel_inter_def by blast

lemma rel_interE:
  assumes "(R \<sqinter> S) x y"
  obtains "R x y" "S x y"
  using assms unfolding rel_inter_def by blast

lemma rel_inter_leftD:
  assumes "(R \<sqinter> S) x y"
  shows "R x y"
  using assms by (elim rel_interE)

lemma rel_inter_rightD:
  assumes "(R \<sqinter> S) x y"
  shows "S x y"
  using assms by (elim rel_interE)

lemma rel_inter_finer_left: "R \<sqinter> S \<sqsubseteq> R"
  by (rule finerI) (rule rel_inter_leftD)

lemma rel_inter_finer_right: "R \<sqinter> S \<sqsubseteq> S"
  by (rule finerI) (rule rel_inter_rightD)

lemma in_dom_rel_interI:
  assumes "R x y"
  and "S x y"
  shows "in_dom (R \<sqinter> S) x"
  using assms by (intro in_domI rel_interI)

lemma in_dom_rel_interE:
  assumes "in_dom (R \<sqinter> S) x"
  obtains y where "R x y" "S x y"
  using assms by (elim in_domE rel_interE)

lemma in_codom_rel_interI:
  assumes "R x y"
  and "S x y"
  shows "in_codom (R \<sqinter> S) y"
  using assms by (intro in_codomI rel_interI)

lemma in_codom_rel_interE:
  assumes "in_codom (R \<sqinter> S) y"
  obtains x where "R x y" "S x y"
  using assms by (elim in_codomE rel_interE)


end