\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Well-Founded Orders\<close>
theory HOTG_Well_Orders
  imports
    HOTG_Pairs
    Transport.Linear_Orders
begin

definition "well_founded_on D R \<equiv> \<forall>X. X \<subseteq> D \<and> X \<noteq> {} \<longrightarrow> (\<exists>a : X. \<forall>x : X. \<langle>x, a\<rangle> \<in> R \<longrightarrow> x = a)"

lemma well_founded_onI [intro]:
  assumes "\<And>X. X \<subseteq> D \<Longrightarrow> X \<noteq> {} \<Longrightarrow> \<exists>a : X. \<forall>x : X. \<langle>x, a\<rangle> \<in> R \<longrightarrow> x = a"
  shows "well_founded_on D R"
  using assms unfolding well_founded_on_def by auto

lemma well_founded_onE [elim]:
  assumes "well_founded_on D R"
  and "X \<subseteq> D"
  and "X \<noteq> {}"
  obtains a where "a \<in> X" "\<And>x. x \<in> X \<Longrightarrow> \<langle>x, a\<rangle> \<in> R \<Longrightarrow> x = a"
  using assms unfolding well_founded_on_def by (auto elim!: ballE)

definition "well_order_on \<equiv> linear_order_on \<sqinter> well_founded_on"

lemma well_order_onI [intro]:
  assumes "linear_order_on D R"
  and "well_founded_on D R"
  shows "well_order_on D R"
  using assms unfolding well_order_on_def by auto

lemma well_order_onE [elim]:
  assumes "well_order_on D R"
  obtains "linear_order_on D R" "well_founded_on D R"
  using assms unfolding well_order_on_def by auto

end