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

lemma tarski_0_sch_1:
  "\<lbrakk>A : set; \<forall>x y z. P x y \<and> P x z \<longrightarrow> y = z\<rbrakk> \<Longrightarrow> \<exists>Y. \<forall>y. y \<in> Y \<longleftrightarrow> (\<exists>x. x \<in> A \<and> P x y)"
(* proof -
  assume asm: "\<forall>x y z. P x y \<and> P x z \<longrightarrow> y = z"
  let ?F = "\<lambda>x. (THE y. P x y)"
  have "\<forall>y. y \<in> {?F x | x \<in> A} \<longleftrightarrow> (\<exists>x. x \<in> A \<and> P x y)"
  proof (rule, rule)
    fix y assume "y \<in> {THE y. P x y | x \<in> A}"
    then obtain x where "x \<in> A" and "y = (THE y. P x y)"
      by (auto elim: ReplD)
    hence "P x y" apply simp apply (rule theI') *)

end
