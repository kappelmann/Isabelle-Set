\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Irreflexive\<close>
theory SBinary_Relations_Irreflexive
  imports
    Pairs
begin

definition "irreflexive D R \<equiv> \<forall>x \<in> D. \<langle>x, x\<rangle> \<notin> R"

lemma irreflexiveI [intro]:
  assumes "\<And>x. x \<in> D \<Longrightarrow> \<langle>x, x\<rangle> \<notin> R"
  shows "irreflexive D R"
  using assms unfolding irreflexive_def by blast

lemma irreflexiveD:
  assumes "irreflexive D R"
  and "x \<in> D"
  shows "\<langle>x, x\<rangle> \<notin> R"
  using assms unfolding irreflexive_def by blast


end