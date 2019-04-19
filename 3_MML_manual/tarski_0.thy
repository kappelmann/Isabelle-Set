theory tarski_0
imports "../2_Mizar/mizar_reserve"

begin

section \<open> TARSKI_0 \<close>

reserve x, y, z, a for object
reserve X, Y, Z for set

\<comment>\<open>Set axiom\<close>
theorem tarski_0_1: "\<forall>x. x be set"
  using set_def by simp

theorem set_exists[ex]: "inhabited(set)"
  using tarski_0_1 inhabited_def by auto

\<comment>\<open>Extensionality axiom\<close>
axiomatization where tarski_0_2: "\<forall>X. \<forall>Y. (\<forall>x. x in X \<longleftrightarrow> x in Y) \<longrightarrow> X = Y"

lemmas tarski_0_2a = tarski_0_2[THEN bspec, THEN bspec, rule_format, OF _ _ _ _ ballI, simplified]

\<comment>\<open>Axiom of pair\<close>
axiomatization where tarski_0_3: "\<forall>x. \<forall>y. \<exists>Z. \<forall>a. a in Z \<longleftrightarrow> a = x \<or> a = y"

\<comment>\<open>Axiom of union\<close>
axiomatization where tarski_0_4: "\<forall>X. \<exists>Z. \<forall>x. x in Z \<longleftrightarrow> (\<exists>Y. x in Y \<and> Y in X)"

\<comment>\<open>Axiom of regularity\<close>
axiomatization where tarski_0_5: "\<forall>x. \<forall>X. x in X \<longrightarrow> (\<exists>Y. Y in X \<and> \<not>(\<exists>z. z in X \<and> z in Y))"

\<comment>\<open>Fraenkel's scheme\<close>
axiomatization where tarski_0_sch_1:
  "A be set \<Longrightarrow> \<forall>x, y, z. P(x,y) \<and> P(x,z) \<longrightarrow> y = z \<Longrightarrow> \<exists>X. \<forall>x. x in X \<longleftrightarrow> (\<exists>y. y in A \<and> P(y, x))"

end
