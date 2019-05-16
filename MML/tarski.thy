theory tarski
imports tarski_0 "../Isabelle_Mizar/mizar_methods"

begin

section \<open> TARSKI \<close>

reserve x,y,z,u for object
reserve N,M,X,Y,Z for set

theorem tarski_th_1: "for x being object holds x is set"
  using tarski_0_1 by auto

theorem tarski_th_2: "(for x being object holds x in X iff x in Y) implies X = Y"
  using tarski_0_2 by auto

mdef tarski_def_1 ("{_}") where
  mlet "y be object"
  "func { y } \<rightarrow> set means \<lambda>it.
    \<forall>x. x in it \<longleftrightarrow> x = y"
proof -
  \<comment>\<open>existence\<close>
  obtain X where "X be set" and
    "for x being object holds
      x in X iff x = y or x = y"
    using tarski_0_3 by fastforce
  thus "ex X st for x being object holds x in X iff x = y"
    by auto

  \<comment>\<open>uniqueness\<close>
  fix X1 X2 assume "X1 be set" "X2 be set" and
  A1: "for z being object holds z in X1 iff z = y" and
  A2: "for z being object holds z in X2 iff z = y"
  {
    fix z assume "z be object"
    have "z in X1 \<longleftrightarrow> z = y" using A1 by auto
    hence "z in X1 \<longleftrightarrow> z in X2" using A2 by auto
  }
  thus "X1 = X2" using tarski_0_2 by auto
qed auto

mdef tarski_def_2 ("{_ , _}") where
  mlet "y be object", "z be object"
  "func { y, z } \<rightarrow> set means \<lambda>it.
    \<forall>x. x in it \<longleftrightarrow> (x = y \<or> x = z)"
proof -
  \<comment>\<open>existence\<close>
  obtain X where "X be set" and
    "for x being object holds
      x in X iff x = y or x = z"
    using tarski_0_3 by fastforce
  thus "ex X st for x being object holds x in X iff x = y or x = z" by auto

  \<comment>\<open>uniqueness\<close>
  fix X1 X2 assume "X1 be set" "X2 be set" and
  A1: "for x being object holds x in X1 iff x = y or x = z" and
  A2: "for x being object holds x in X2 iff x = y or x = z"
  {
    fix x assume "x be object"
    hence "x in X1 iff x = y or x = z" using A1 by auto
    hence "x in X1 iff x in X2" using A2 by auto
  }
  thus "X1 = X2" using tarski_0_2 by auto
qed auto

mtheorem tarski_def_2_commutativity [simplified]:
  "commutativity object tarski_def_2"
    by (commutativity def: tarski_def_2)

mdef tarski_def_3 (infixl "c=" 50) where
  mlet "X be set", "Y be set"
    "pred X c= Y means (\<forall>x: object. x in X \<longrightarrow> x in Y)" .

theorem tarski_def_3_reflexivity:
  "reflexivity set tarski_def_3"
    by (reflexivity def: tarski_def_3)

lemmas tarski_def_3c = tarski_def_3_reflexivity[THEN bspec, simplified]

abbreviation tarski_def_3_notation (infixl "\<subseteq>" 50) where
  "X \<subseteq> Y \<equiv> X c= Y"

mdef tarski_def_4 ("union _" [90] 90) where
  mlet "X be set"
    "func union X \<rightarrow> set means \<lambda>it.
      \<forall>x. x in it \<longleftrightarrow> (\<exists>Y. x in Y \<and> Y in X)"
proof -
  \<comment>\<open>existence\<close>
  obtain Z where "Z is set" and
  "\<forall>x: object. x in Z \<longleftrightarrow> (\<exists>Y: set. x in Y \<and> Y in X)"
    using tarski_0_4 by fastforce
  thus "\<exists>Z: set. \<forall>x: object. x in Z \<longleftrightarrow> (\<exists>Y: set. x in Y \<and> Y in X)"
    by auto

  \<comment>\<open>uniqueness\<close>
  fix X1 X2 assume "X1 be set" and "X2 be set"
  assume
  A1: "\<forall>x: object. (x in X1 \<longleftrightarrow> (\<exists>Y: set. (x in Y \<and> Y in X)))" and
  A2: "\<forall>x: object. (x in X2 \<longleftrightarrow> (\<exists>Y:set. (x in Y \<and> Y in X)))"
  {
    fix x assume "x be object"
    have "x in X1 \<longleftrightarrow> (\<exists>Y: set. (x in Y \<and> Y in X))" using A1 by auto
    hence "x in X1 \<longleftrightarrow> x in X2" using A2 by auto
  }
  thus "X1 = X2" using tarski_0_2 by auto
qed auto

lemmas tarski_th_3 = tarski_0_5

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
   

end



