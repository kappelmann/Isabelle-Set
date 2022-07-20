subsection \<open>Finer Relation\<close>
theory Binary_Relations_Finer
  imports
    Binary_Relations_Base
begin

definition "finer R S \<equiv> \<forall>x y. R x y \<longrightarrow> S x y"

bundle notation_finer begin notation finer (infix "\<sqsubseteq>" 50) end
bundle no_notation_finer begin no_notation finer (infix "\<sqsubseteq>" 50) end
unbundle notation_finer

lemma finerI:
  assumes "\<And>x y. R x y \<Longrightarrow> S x y"
  shows "R \<sqsubseteq> S"
  unfolding finer_def using assms by blast

lemma finerD:
  assumes "R \<sqsubseteq> S"
  and "R x y"
  shows "S x y"
  using assms unfolding finer_def by blast

lemma finerE:
  assumes "R \<sqsubseteq> S"
  and "R x y"
  obtains "S x y"
  using assms unfolding finer_def by blast

lemma finer_self: "R \<sqsubseteq> R" by (rule finerI)

lemma eq_if_finer_if_finer:
  assumes "R \<sqsubseteq> S"
  and "S \<sqsubseteq> R"
  shows "R = S"
  using assms by (intro ext) (blast dest: finerD)

lemma rel_inv_finer_rel_inv_if_finer:
  assumes "R \<sqsubseteq> S"
  shows "rel_inv R \<sqsubseteq> rel_inv S"
  using assms by (intro finerI) (blast intro: rel_invI dest: rel_invD finerD)

lemma rel_comp_finer_rel_inv_if_symmetric_if_rel_comp_finer:
  assumes finer: "(R1 \<circ>\<circ> R2) \<sqsubseteq> R3"
  and symms: "symmetric R1" "symmetric R2"
  shows "(R2 \<circ>\<circ> R1) \<sqsubseteq> rel_inv R3"
proof -
  from finer have "rel_inv (R1 \<circ>\<circ> R2) \<sqsubseteq> rel_inv R3"
    by (rule rel_inv_finer_rel_inv_if_finer)
  then have "rel_inv R2 \<circ>\<circ> rel_inv R1 \<sqsubseteq> rel_inv R3"
    by (simp only: rel_inv_comp_eq)
  with symms show ?thesis by (simp only: rel_inv_eq_self_if_symmetric)
qed

lemma rel_inv_finer_rel_comp_if_symmetric_if_finer_rel_comp:
  assumes finer: "R1 \<sqsubseteq> (R2 \<circ>\<circ> R3)"
  and symms: "symmetric R2" "symmetric R3"
  shows "rel_inv R1 \<sqsubseteq> (R3 \<circ>\<circ> R2)"
proof -
  from finer have "rel_inv R1 \<sqsubseteq> rel_inv (R2 \<circ>\<circ> R3)"
    by (rule rel_inv_finer_rel_inv_if_finer)
  then have "rel_inv R1 \<sqsubseteq> rel_inv R3 \<circ>\<circ> rel_inv R2"
    by (simp only: rel_inv_comp_eq)
  with symms show ?thesis by (simp only: rel_inv_eq_self_if_symmetric)
qed

corollary rel_comp_finer_rel_comp_if_symmetric_if_rel_comp_finer_rel_comp:
  assumes "(R1 \<circ>\<circ> R2) \<sqsubseteq> (R3 \<circ>\<circ> R4)"
  and "symmetric R1" "symmetric R2" "symmetric R3" "symmetric R4"
  shows "(R2 \<circ>\<circ> R1) \<sqsubseteq> (R4 \<circ>\<circ> R3)"
proof -
  from assms(1-3) have "(R2 \<circ>\<circ> R1) \<sqsubseteq> rel_inv (R3 \<circ>\<circ> R4)"
    by (rule rel_comp_finer_rel_inv_if_symmetric_if_rel_comp_finer)
  then have "(R2 \<circ>\<circ> R1) \<sqsubseteq> (rel_inv R4 \<circ>\<circ> rel_inv R3)"
    by (simp only: rel_inv_comp_eq)
  with assms(4-5) show ?thesis by (simp only: rel_inv_eq_self_if_symmetric)
qed

corollary rel_comp_finer_rel_comp_iff_if_symmetric:
  assumes "symmetric R1" "symmetric R2" "symmetric R3" "symmetric R4"
  shows "(R1 \<circ>\<circ> R2) \<sqsubseteq> (R3 \<circ>\<circ> R4) \<longleftrightarrow> (R2 \<circ>\<circ> R1) \<sqsubseteq> (R4 \<circ>\<circ> R3)"
  using assms
  by (blast intro: rel_comp_finer_rel_comp_if_symmetric_if_rel_comp_finer_rel_comp)

corollary eq_if_finer_if_symmetric:
  assumes "symmetric R" "symmetric S"
  and "(R \<circ>\<circ> S) \<sqsubseteq> (S \<circ>\<circ> R)"
  shows "(R \<circ>\<circ> S) = (S \<circ>\<circ> R)"
  using assms rel_comp_finer_rel_comp_iff_if_symmetric
    by (intro eq_if_finer_if_finer) blast+

lemma rel_comp_finer_rel_comp_if_rel_self_if_finer_if_trans:
  assumes trans: "transitive S"
  and finer: "R \<sqsubseteq> S"
  and rel_self_if_rel: "\<And>x y. S x y \<Longrightarrow> R y y"
  shows "R \<circ>\<circ> S \<sqsubseteq> S \<circ>\<circ> R"
proof (rule finerI)
  fix x1 x2
  assume"(R \<circ>\<circ> S) x1 x2"
  then obtain x3 where x3: "R x1 x3" "S x3 x2" by (elim rel_compE)
  then have "S x1 x3" using finer by (blast dest: finerD)
  then have "S x1 x2" using trans x3(2) by (blast dest: transitiveD)
  then have "R x2 x2" by (rule rel_self_if_rel)
  then show "(S \<circ>\<circ> R) x1 x2" using \<open>S x1 x2\<close> by (blast intro: rel_compI)
qed


end