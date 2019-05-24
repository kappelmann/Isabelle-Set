theory tarski_0
imports "../Isabelle_Set/Set_Theory"

begin

section \<open>TARSKI_0\<close>

theorem tarski_0_1: "\<forall>x. x : set" using all_sets_set ..

theorem tarski_0_2: "(\<forall>x. x \<in> X \<longleftrightarrow> x \<in> Y) \<longrightarrow> X = Y" by extensionality

theorem tarski_0_3: "\<forall>x y. \<exists>z : set. \<forall>a. a \<in> z \<longleftrightarrow> a = x \<or> a = y"
proof rule+
  fix x y show "\<forall>a. a \<in> {x, y} \<longleftrightarrow> a = x \<or> a = y" by auto
qed (rule all_sets_set) (* This should be handled by the type-handler! *)

theorem tarski_0_4: "\<forall>X : set. \<exists>Z : set. \<forall>x. x \<in> Z \<longleftrightarrow> (\<exists>Y : set. x \<in> Y \<and> Y \<in> X)"
proof rule+
  fix X show "\<forall>x. (x \<in> \<Union>X) = (\<exists>Y : set. x \<in> Y \<and> Y \<in> X)"
    unfolding Soft_Bex_def
    using Union_axiom all_sets_set
    by auto
qed (rule all_sets_set)

theorem tarski_0_5: "x \<in> X \<longrightarrow> (\<exists>Y. Y \<in> X \<and> \<not>(\<exists>x. x \<in> X \<and> x \<in> Y))"
  using elem_induct_axiom[of "\<lambda>x. x \<notin> X"] by blast

theorem tarski_0_sch_1:
  assumes "A : set" and "\<forall>x y z. P x y \<and> P x z \<longrightarrow> y = z"
  shows "\<exists>Y. \<forall>y. y \<in> Y \<longleftrightarrow> (\<exists>x. x \<in> A \<and> P x y)"
proof
  let ?Y = "{y | x \<in> A, P x y}"
  show "\<forall>y. y \<in> ?Y \<longleftrightarrow> (\<exists>x. x \<in> A \<and> P x y)"
  proof (rule, rule)
    fix y assume "y \<in> ?Y"
    then obtain x where "x \<in> A" and "P x y" by auto
    thus "\<exists>x. x \<in> A \<and> P x y" by auto
  next
    fix y assume "\<exists>x. x \<in> A \<and> P x y"
    then obtain x where
      1: "x \<in> A" and
      2: "P x y"
      by auto
    show "y \<in> {y | x \<in> A, P x y}"
    proof
      fix u assume "P x u"
      with 2 assms(2) show "u = y" by auto
    qed (fact 1 2)+
  qed
qed


end
