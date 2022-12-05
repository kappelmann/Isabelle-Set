\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Antisymmetric\<close>
theory SBinary_Relations_Antisymmetric
  imports
    Pairs
begin

definition "antisymmetric D R \<equiv> \<forall>x y \<in> D. \<langle>x, y\<rangle> \<in> R \<and> \<langle>y, x\<rangle> \<in> R \<longrightarrow> x = y"

lemma antisymmetricI [intro]:
  assumes "\<And>x y. x \<in> D \<Longrightarrow> y \<in> D \<Longrightarrow> \<langle>x, y\<rangle> \<in> R \<Longrightarrow> \<langle>y, x\<rangle> \<in> R \<Longrightarrow> x = y"
  shows "antisymmetric D R"
  using assms unfolding antisymmetric_def by blast

lemma antisymmetricD:
  assumes "antisymmetric D R"
  and "x \<in> D" "y \<in> D"
  and "\<langle>x, y\<rangle> \<in> R" "\<langle>y, x\<rangle> \<in> R"
  shows "x = y"
  using assms unfolding antisymmetric_def by blast


end