subsection \<open>Basic Relators\<close>
theory Binary_Relations_Relators
  imports Binary_Relations_Base
begin

definition "Dep_Fun_Rel R S f g \<equiv> \<forall>x y. R x y \<longrightarrow> S x y (f x) (g y)"

abbreviation "Fun_Rel R S \<equiv> Dep_Fun_Rel R (\<lambda>_ _. S)"

syntax
  "_Fun_Rel" :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('c \<Rightarrow> 'd \<Rightarrow> bool) \<Rightarrow> (('a \<Rightarrow> 'c) \<Rightarrow>
    ('b \<Rightarrow> 'd) \<Rightarrow> bool)" ("(_) \<Rrightarrow> (_)" [101, 100] 100)
  "_Dep_Fun_Rel" :: "idt \<Rightarrow> idt \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('c \<Rightarrow> 'd \<Rightarrow> bool) \<Rightarrow>
    (('a \<Rightarrow> 'c) \<Rightarrow> ('b \<Rightarrow> 'd) \<Rightarrow> bool)" ("[_/ _/ \<Colon>/ _] \<Rrightarrow> (_)" [101, 101, 101, 100] 100)
translations
  "R \<Rrightarrow> S" \<rightleftharpoons> "CONST Fun_Rel R S"
  "[x y \<Colon> R] \<Rrightarrow> S" \<rightleftharpoons> "CONST Dep_Fun_Rel R (\<lambda>x y. S)"

lemma Dep_Fun_RelI:
  assumes "\<And>x y. R x y \<Longrightarrow> S x y (f x) (g y)"
  shows "([x y \<Colon> R] \<Rrightarrow> S x y) f g"
  unfolding Dep_Fun_Rel_def using assms by blast

lemma Dep_Fun_RelD:
  assumes "([x y \<Colon> R] \<Rrightarrow> S x y) f g"
  and "R x y"
  shows "S x y (f x) (g y)"
  using assms unfolding Dep_Fun_Rel_def by blast

lemma Dep_Fun_RelE:
  assumes "([x y \<Colon> R] \<Rrightarrow> S x y) f g"
  and "R x y"
  obtains "S x y (f x) (g y)"
  using assms unfolding Dep_Fun_Rel_def by blast

lemma Dep_Fun_Rel_inv_if_Dep_Fun_Rel:
  assumes "([x y \<Colon> R] \<Rrightarrow> S x y) f g"
  shows "([y x \<Colon> (rel_inv R)] \<Rrightarrow> (rel_inv (S x y))) g f"
  using assms
  by (intro Dep_Fun_RelI) (blast intro: rel_invI dest: rel_invD Dep_Fun_RelD)

lemma Dep_Fun_Rel_compI:
  assumes Dep_Fun_Rel1: "([x y \<Colon> R] \<Rrightarrow> S x y) f g"
  and Dep_Fun_Rel2: "\<And>x y. R x y \<Longrightarrow> ([x' y' \<Colon> T x y] \<Rrightarrow> U x y x' y') f' g'"
  and finer: "\<And>x y. S x y (f x) (g y) \<Longrightarrow> T x y (f x) (g y)"
  shows "([x y \<Colon> R] \<Rrightarrow> U x y (f x) (g y)) (f' \<circ> f) (g' \<circ> g)"
proof (rule Dep_Fun_RelI)
  fix x y assume "R x y"
  with Dep_Fun_Rel1 have "S x y (f x) (g y)" by (rule Dep_Fun_RelD)
  then have "T x y (f x) (g y)" by (rule finer)
  with Dep_Fun_Rel2 \<open>R x y\<close> show "U x y (f x) (g y) ((f' \<circ> f) x) ((g' \<circ> g) y)"
    by (fastforce dest: Dep_Fun_RelD)
qed

lemma Dep_Fun_Rel_compI':
  assumes "([x y \<Colon> R] \<Rrightarrow> S x y) f g"
  and "\<And>x y. R x y \<Longrightarrow> ([x' y' \<Colon> S x y] \<Rrightarrow> T x y x' y') f' g'"
  shows "([x y \<Colon> R] \<Rrightarrow> T x y (f x) (g y)) (f' \<circ> f) (g' \<circ> g)"
  using assms by (rule Dep_Fun_Rel_compI)

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

lemma monotone_compI:
  assumes mono1: "monotone R S f"
  and mono2: "monotone T U g"
  and S_f_finer: "\<And>x y. S (f x) (f y) \<Longrightarrow> T (f x) (f y)"
  shows "monotone R U (g \<circ> f)"
  using assms by (intro dep_monotone_if_Dep_Fun_Rel_self Dep_Fun_Rel_compI)
    (fastforce dest: Dep_Fun_Rel_self_if_dep_monotone)+

lemma monotone_comp_if_monotone:
  assumes "monotone R S f"
  and "monotone S T g"
  shows "monotone R T (g \<circ> f)"
  using assms by (intro monotone_compI)

lemma monotone_self_id: "monotone R R id"
  by (rule dep_monotoneI) simp

definition "finer R S \<equiv> monotone R S id"

bundle notation_finer begin notation finer (infix "\<sqsubseteq>" 50) end
bundle no_notation_finer begin no_notation finer (infix "\<sqsubseteq>" 50) end
unbundle notation_finer

lemma finer_if_monotone_id:
  assumes "monotone R S id"
  shows "R \<sqsubseteq> S"
  unfolding finer_def using assms .

lemma finerI:
  assumes "\<And>x y. R x y \<Longrightarrow> S x y"
  shows "R \<sqsubseteq> S"
  using assms by (intro finer_if_monotone_id dep_monotoneI) simp

lemma monotone_id_if_finer:
  assumes "R \<sqsubseteq> S"
  shows "monotone R S id"
  using assms unfolding finer_def .

corollary monotone_id_iff_finer: "monotone R S id \<longleftrightarrow> R \<sqsubseteq> S"
  using monotone_id_if_finer finer_if_monotone_id by blast

lemma finerD:
  assumes "R \<sqsubseteq> S"
  and "R x y"
  shows "S x y"
  using assms by (fastforce dest: monotone_id_if_finer dep_monotoneD)

lemma finerE:
  assumes "R \<sqsubseteq> S"
  and "R x y"
  obtains "S x y"
  using assms by (fastforce dest: monotone_id_if_finer elim: dep_monotoneE)

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

lemma monotone_if_monotone_if_finer:
  assumes finer: "R \<sqsubseteq> S"
  and mono: "monotone S T f"
  shows "monotone R T f"
proof -
  from finer have "monotone R S id" by (rule monotone_id_if_finer)
  with mono have "monotone R T (f \<circ> id)" by (intro monotone_comp_if_monotone)
  then show ?thesis by simp
qed

lemma monotone_if_finer_if_monotone:
  assumes mono: "monotone R S f"
  and finer: "S \<sqsubseteq> S'"
  shows "monotone R S' f"
proof -
  from finer have "monotone S S' id" by (rule monotone_id_if_finer)
  with mono have "monotone R S' (id \<circ> f)" by (rule monotone_comp_if_monotone)
  then show ?thesis by simp
qed

lemma monotone_comp_if_finer_if_monotone:
  assumes "monotone R S f"
  and "monotone T U g"
  and "S \<sqsubseteq> T"
  shows "monotone R U (g \<circ> f)"
  by (rule monotone_compI[OF assms(1-2) finerD[OF assms(3)]])


end