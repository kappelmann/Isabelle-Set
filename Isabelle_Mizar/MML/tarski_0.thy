theory tarski_0
imports "../Isabelle_Mizar/mizar_reserve"

begin

section \<open> TARSKI_0 \<close>

reserve x, y, z, a for object
reserve X, Y, Z for set

\<comment>\<open>Set axiom\<close>
axiomatization where tarski_0_1: "\<forall>x: object. x is set"

theorem set_exists[ex]: "inhabited(set)"
  using tarski_0_1 inhabited_def by auto

theorem set_object_eq[simp]: "x be set \<longleftrightarrow> x be object"
  using tarski_0_1 by auto

theorem all_set[clus]: "x be set" by auto \<comment>\<open>Basic cluster rule: everything is a set.\<close>

\<comment>\<open>Extensionality axiom\<close>
axiomatization where tarski_0_2:
  "(\<forall>x: object. x in X \<longleftrightarrow> x in Y) \<longrightarrow> X = Y"

\<comment>\<open>Axiom of pair\<close>
axiomatization where tarski_0_3:
  "for x,y being object holds ex z being set st
    for a being object holds
      a in z iff a = x or a = y"

\<comment>\<open>Axiom of union\<close>
axiomatization where tarski_0_4:
  "for X being set holds
    ex Z being set st
      for x being object holds
        x in Z iff (ex Y being set st x in Y \<and> Y in X)"

\<comment>\<open>Axiom of regularity\<close>
axiomatization where tarski_0_5:
  "x in X implies (ex Y st Y in X \<and> not (ex x st x in X \<and> x in Y))"

\<comment>\<open>Fraenkel's scheme\<close>
axiomatization where tarski_0_sch_1:
  "A be set \<Longrightarrow>
    for x,y,z being object st P(x,y) \<and> P(x,z) holds y = z \<Longrightarrow>
      ex X st for x holds x in X iff (ex y st y in A \<and> P(y,x))"

end
