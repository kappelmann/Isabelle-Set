section \<open>TARSKI\<close>

theory tarski
imports tarski_0

begin

(* reserve N,M,X,Y,Z for set *)

theorem tarski_th_1: "\<forall>x. x : set"
  using tarski_0_1 by auto

theorem tarski_th_2: "(\<forall>x. x \<in> X \<longleftrightarrow> x \<in> Y) \<longrightarrow> X = Y"
  using tarski_0_2 by auto

theorem tarksi_def_1_uniq: "(\<forall>x. x \<in> X \<longleftrightarrow> x = y) \<longrightarrow> X = {y}"
  by extensionality

theorem tarski_def_1_ty: "{y} : set"
  by (fact all_sets_set) (* Should be done by type-handler *)

theorem tarski_def_1_prop: "\<forall>x. x \<in> {y} \<longleftrightarrow> x = y"
  by auto

theorem tarski_def_2_uniq: "(\<forall>x. x \<in> X \<longleftrightarrow> x = y \<or> x = z) \<longrightarrow> X = {y, z}"
  by extensionality

theorem tarski_def_2_ty: "{y, z} : set"
  by (fact all_sets_set)

theorem tarski_def_2_prop: "x \<in> {y, z} \<longleftrightarrow> (x = y \<or> x = z)"
  by auto

theorem tarski_def_2_commutativity: "commutativity set (\<lambda>x y. {x, y})"
  by extensionality

theorem tarski_def_3_def: "X \<subseteq> Y \<longleftrightarrow> (\<forall>x. x \<in> X \<longrightarrow> x \<in> Y)"
  by (rule subset_iff)

theorem tarski_def_3_reflexivity: "reflexivity set (\<lambda>X Y. X \<subseteq> Y)"
  by auto

theorem tarski_def_4_uniq: "\<lbrakk>\<forall>x. x \<in> Z \<longleftrightarrow> (\<exists>Y. x \<in> Y \<and> Y \<in> X)\<rbrakk> \<Longrightarrow> Z = \<Union>X"
  by extensionality

theorem tarski_def_4_ty: "\<Union>X : set"
  by (fact all_sets_set)

theorem tarski_def_4_prop: "\<forall>x. x \<in> \<Union>X \<longleftrightarrow> (\<exists>Y. x \<in> Y \<and> Y \<in> X)"
  by auto

theorem tarski_th_3: "x \<in> X \<longrightarrow> (\<exists>Y. Y \<in> X \<and> \<not>(\<exists>x. x \<in> X \<and> x \<in> Y))"
  by (fact tarski_0_5)

theorem tarski_redef_1: "asymmetry set (\<lambda>x X. x \<in> X)"
proof rule+
  fix a b assume "a : set" "b : set"
  assume
  A1: "a \<in> b \<and> b \<in> a"
  hence
  A3: "a \<in> {a, b} \<and> b \<in> {a, b}" by auto
  from tarski_0_5 obtain y where
  A4: "y \<in> {a, b} \<and> (\<nexists>x. x \<in> {a, b} \<and> x \<in> y)" by blast
  hence "y = a \<or> y = b" by auto
  thus False using A1 A3 A4 by auto
qed

theorem tarski_sch_1:
  assumes "A : set" and "\<forall>x y z. P x y \<and> P x z \<longrightarrow> y = z"
  shows "\<exists>Y. \<forall>y. y \<in> Y \<longleftrightarrow> (\<exists>x. x \<in> A \<and> P x y)"
  using assms by (fact tarski_0_sch_1)

definition tarski_def_5 :: "[set, set] \<Rightarrow> set" ("([_, _])")
  where "[x, y] \<equiv> {{x, y}, {x}}"

axiomatization tarski_def_6 :: "[set, set] \<Rightarrow> bool" ("(_, _ are'_equipotent)")
  where tarski_def_6:
  "\<lbrakk>X : set; Y : set\<rbrakk> \<Longrightarrow>
    (X, Y are_equipotent) \<longleftrightarrow> (\<exists>Z.
      (\<forall>x. x \<in> X \<longrightarrow> (\<exists>y. y \<in> Y \<and> [x, y] \<in> Z)) \<and>
      (\<forall>y. y \<in> Y \<longrightarrow> (\<exists>x. x \<in> X \<and> [x, y] \<in> Z)) \<and>
      (\<forall>x y z u. ([x, y] \<in> Z \<and> [z, u] \<in> Z) \<longrightarrow> (x = z \<longleftrightarrow> y = u)))"


end



