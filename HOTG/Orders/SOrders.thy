\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Set-Theoretic Orders\<close>
theory SOrders
  imports
    SBinary_Relations_Antisymmetric
    SBinary_Relations_Connected
    SBinary_Relations_Reflexive
    SBinary_Relations_Transitive
begin

definition "partial_order D R \<equiv>
  reflexive D R \<and> transitive D R \<and> antisymmetric D R"

definition "linear_order D R \<equiv> connected D R \<and> partial_order D R"

definition "well_founded D R \<equiv>
  \<forall>X. X \<subseteq> D \<and> X \<noteq> {} \<longrightarrow> (\<exists>a \<in> X. \<forall>x \<in> X. \<langle>x, a\<rangle> \<in> R \<longrightarrow> x = a)"

lemma well_foundedI:
  assumes "\<And>X. \<lbrakk>X \<subseteq> D; X \<noteq> {}\<rbrakk> \<Longrightarrow> \<exists>a \<in> X. \<forall>x \<in> X. \<langle>x, a\<rangle> \<in> R \<longrightarrow> x = a"
  shows "well_founded D R"
  using assms unfolding well_founded_def by auto

definition "well_order D R \<equiv> linear_order D R \<and> well_founded D R"


end