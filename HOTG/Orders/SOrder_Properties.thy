\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Order Properties\<close>
theory SOrder_Properties
  imports
    SBinary_Relations_Antisymmetric
    SBinary_Relations_Connected
    SBinary_Relations_Reflexive
    SBinary_Relations_Transitive
begin

definition "linear_order D R \<equiv> connected D R \<and> partial_order_on D R"

lemma linear_orderI [intro]:
  assumes "connected D R"
  and "partial_order_on D R"
  shows "linear_order D R"
  using assms unfolding linear_order_def by auto

lemma linear_orderE [elim]:
  assumes "linear_order D R"
  obtains "connected D R" "partial_order_on D R"
  using assms unfolding linear_order_def by auto

definition "well_founded D R \<equiv> \<forall>X. X \<subseteq> D \<and> X \<noteq> {} \<longrightarrow> (\<exists>a \<in> X. \<forall>x \<in> X. \<langle>x, a\<rangle> \<in> R \<longrightarrow> x = a)"

lemma well_foundedI [intro]:
  assumes "\<And>X. X \<subseteq> D \<Longrightarrow> X \<noteq> {} \<Longrightarrow> \<exists>a \<in> X. \<forall>x \<in> X. \<langle>x, a\<rangle> \<in> R \<longrightarrow> x = a"
  shows "well_founded D R"
  using assms unfolding well_founded_def by auto

lemma well_foundedE [elim]:
  assumes "well_founded D R"
  and "X \<subseteq> D"
  and "X \<noteq> {}"
  obtains a where "a \<in> X" "\<And>x. x \<in> X \<Longrightarrow> \<langle>x, a\<rangle> \<in> R \<Longrightarrow> x = a"
  using assms unfolding well_founded_def by (blast elim!: ballE)

definition "well_order D R \<equiv> linear_order D R \<and> well_founded D R"

lemma well_orderI [intro]:
  assumes "linear_order D R"
  and "well_founded D R"
  shows "well_order D R"
  using assms unfolding well_order_def by auto

lemma well_orderE [elim]:
  assumes "well_order D R"
  obtains "linear_order D R" "well_founded D R"
  using assms unfolding well_order_def by auto

end