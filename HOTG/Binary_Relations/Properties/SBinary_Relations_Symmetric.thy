\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Symmetric\<close>
theory SBinary_Relations_Symmetric
  imports
    Pairs
begin

definition "symmetric D R \<equiv> \<forall>x y \<in> D. \<langle>x, y\<rangle> \<in> R \<longrightarrow> \<langle>y, x\<rangle> \<in> R"

lemma symmetricI [intro]:
  assumes "\<And>x y. x \<in> D \<Longrightarrow> y \<in> D \<Longrightarrow> \<langle>x, y\<rangle> \<in> R \<Longrightarrow> \<langle>y, x\<rangle> \<in> R"
  shows "symmetric D R"
  using assms unfolding symmetric_def by blast

lemma symmetricD:
  assumes "symmetric D R"
  and "x \<in> D" "y \<in> D"
  and "\<langle>x, y\<rangle> \<in> R"
  shows "\<langle>y, x\<rangle> \<in> R"
  using assms unfolding symmetric_def by blast


end