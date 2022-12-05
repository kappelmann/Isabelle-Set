\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Connected\<close>
theory SBinary_Relations_Connected
  imports
    Pairs
begin

definition "connected D R \<equiv> \<forall>x y \<in> D. x \<noteq> y \<longrightarrow> \<langle>x, y\<rangle> \<in> R \<or> \<langle>y, x\<rangle> \<in> R"

lemma connectedI [intro]:
  assumes "\<And>x y. x \<in> D \<Longrightarrow> y \<in> D \<Longrightarrow> x \<noteq> y \<Longrightarrow> \<langle>x, y\<rangle> \<in> R \<or> \<langle>y, x\<rangle> \<in> R"
  shows "connected D R"
  using assms unfolding connected_def by blast

lemma connectedE:
  assumes "connected D R"
  and "x \<in> D" "y \<in> D"
  and "x \<noteq> y"
  obtains "\<langle>x, y\<rangle> \<in> R" | "\<langle>y, x\<rangle> \<in> R"
  using assms unfolding connected_def by auto


end