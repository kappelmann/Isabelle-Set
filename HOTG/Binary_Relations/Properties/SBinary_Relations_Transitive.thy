\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Transitive\<close>
theory SBinary_Relations_Transitive
  imports
    Pairs
begin

definition "transitive D R \<equiv> \<forall>x y z \<in> D. \<langle>x, y\<rangle> \<in> R \<and> \<langle>y, z\<rangle> \<in> R \<longrightarrow> \<langle>x, z\<rangle> \<in> R"

lemma transitiveI [intro]:
  assumes
    "\<And>x y z. x \<in> D \<Longrightarrow> y \<in> D \<Longrightarrow> z \<in> D \<Longrightarrow> \<langle>x, y\<rangle> \<in> R \<Longrightarrow> \<langle>y, z\<rangle> \<in> R \<Longrightarrow> \<langle>x, z\<rangle> \<in> R"
  shows "transitive D R"
  using assms unfolding transitive_def by blast

lemma transitiveD:
  assumes "transitive D R"
  and "x \<in> D" "y \<in> D" "z \<in> D"
  and "\<langle>x, y\<rangle> \<in> R" "\<langle>y, z\<rangle> \<in> R"
  shows "\<langle>x, z\<rangle> \<in> R"
  using assms unfolding transitive_def by blast


end