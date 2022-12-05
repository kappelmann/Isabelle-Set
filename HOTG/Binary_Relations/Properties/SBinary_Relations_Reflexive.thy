\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Reflexive\<close>
theory SBinary_Relations_Reflexive
  imports
    Pairs
begin

definition "reflexive D R \<equiv> \<forall>x \<in> D. \<langle>x, x\<rangle> \<in> R"

lemma reflexiveI [intro]:
  assumes "\<And>x. x \<in> D \<Longrightarrow> \<langle>x, x\<rangle> \<in> R"
  shows "reflexive D R"
  using assms unfolding reflexive_def by blast

lemma reflexiveD:
  assumes "reflexive D R"
  and "x \<in> D"
  shows "\<langle>x, x\<rangle> \<in> R"
  using assms unfolding reflexive_def by blast


end