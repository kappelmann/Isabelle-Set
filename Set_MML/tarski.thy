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

(*

mtheorem prefix_in_asymmetry:
  "asymmetry set prefix_in"
proof purify
  {
    fix a b assume "a be set" and "b be set"
    assume
    A1: "a in b \<and> b in a"
    let ?X = "{a, b}"
    have
    A3: "a in ?X \<and> b in ?X" using tarski_def_2 by auto
    obtain Y where "Y is set" and
    A4: "Y in ?X \<and> \<not>(\<exists>x: object. x in ?X \<and> x in Y)" using A3 tarski_0_5 by fastforce
    have "Y = a \<or> Y = b" using A4 tarski_def_2 by auto
    hence False using A1 A3 A4 by auto
  }
  thus "\<And>x1 x2. \<lbrakk>x1 be set; x2 be set; x1 in x2 \<and> x2 in x1\<rbrakk> \<Longrightarrow> False" by auto
qed auto

lemmas tarski_sch_1 = tarski_0_sch_1

mdef tarski_def_5 ("[_ , _]") where
  mlet "x be object", "y be object"
  "func [x,y] \<rightarrow> object equals
    {{x, y}, {x}}"
  by auto
  
mdef tarski_def_6 ("_,_ are'_equipotent" [100,100]) where
  mlet "X be set","Y be set"
  "pred X, Y are_equipotent means
    ex Z st
    (for x st x in X ex y st y in Y \<and> [x,y] in Z) \<and>
    (for y st y in Y ex x st x in X \<and> [x,y] in Z) \<and>
    (for x,y,z,u st [x,y] in Z \<and> [z,u] in Z holds x = z \<longleftrightarrow> y = u)" .
*)

end



