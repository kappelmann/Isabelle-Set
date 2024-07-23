\<^marker>\<open>creator "Linghan Fang"\<close>
\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Equipollence\<close>
theory HOTG_Equipollence_Base
  imports
    HOTG_Functions_Bijection
    Transport.Equivalence_Relations
begin

paragraph \<open>Summary\<close>
text \<open>Two sets \<open>X\<close> and \<open>Y\<close> are said to be equipollent if there exists a bijection between them.
We show that equipollence is an equivalence relation.\<close>

(*TODO: define using a more general constant and overloading*)
definition "equipollent (X :: set) (Y :: set) \<equiv>
  \<exists>(f :: set \<Rightarrow> set) (g :: set \<Rightarrow> set). bijection_on X Y f g"

bundle hotg_equipollent_syntax begin notation equipollent (infixl "\<approx>" 50) end
bundle no_hotg_equipollent_syntax begin no_notation equipollent (infixl "\<approx>" 50) end
unbundle hotg_equipollent_syntax

lemma equipollentI [intro]:
  assumes "bijection_on X Y (f :: set \<Rightarrow> set) (g :: set \<Rightarrow> set)"
  shows "X \<approx> Y"
  using assms unfolding equipollent_def by auto

lemma equipollentE [elim]:
  assumes "X \<approx> Y"
  obtains f g :: "set \<Rightarrow> set" where "bijection_on (X :: set) (Y :: set) f g"
  using assms unfolding equipollent_def by auto

lemma reflexive_equipollent: "reflexive (\<approx>)"
  using bijection_on_self_id by auto

lemma symmetric_equipollent: "symmetric (\<approx>)"
  by (intro symmetricI) (auto dest: bijection_on_right_left_if_bijection_on_left_right)

lemma transitive_equipollent: "transitive (\<approx>)"
  by (intro transitiveI) (blast intro: bijection_on_compI)

lemma equipollent_if_equipollent_if_equipollent [trans]:
  assumes "X \<approx> Y" "Y \<approx> Z"
  shows "X \<approx> Z"
  using assms transitive_equipollent by blast

lemma preorder_equipollent: "preorder (\<approx>)"
  by (intro preorderI transitive_equipollent reflexive_equipollent)

lemma partial_equivalence_rel_equipollent: "partial_equivalence_rel (\<approx>)"
  by (intro partial_equivalence_relI transitive_equipollent symmetric_equipollent)

lemma equivalence_rel_equipollent: "equivalence_rel (\<approx>)"
  by (intro equivalence_relI partial_equivalence_rel_equipollent reflexive_equipollent)


end
