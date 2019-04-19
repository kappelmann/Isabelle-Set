theory tarski
imports "../2_Mizar/mizar_fraenkel"
begin

section "TARSKI"

reserve x,y,z,u for object
reserve N,M,X,Y,Z for set

theorem all_set: "x be set"
  using tarski_0_1 by auto

lemmas tarski_sch_1 = tarski_0_sch_1
lemmas tarski_th_2 = tarski_0_2a[intro?]

mdef tarski_def_1 ("{_}") where
  mlet "y be object"
  "func {y} \<rightarrow> set means \<lambda>it.
    \<forall>x. x in it \<longleftrightarrow> x = y"
proof -
  fix X1 X2
  assume
    [ty]: "X1 be set" "X2 be set" and
    A1: "\<forall>x: object. x in X1 \<longleftrightarrow> x = y" and
    A2: "\<forall>x: object. x in X2 \<longleftrightarrow> x = y"
    {
      fix x assume [ty]: "x be object"
      hence "x in X1 \<longleftrightarrow> x = y" using A1 by auto
      hence "x in X1 \<longleftrightarrow> x in X2" using A2 by auto
    }
    thus "X1 = X2" by (intro tarski_th_2) mauto
  next
  obtain X where
    [ty]: "X be set" and
    A1: "(\<forall>x: object. (x in X \<longleftrightarrow> (x = y \<or> x = y)))"
    using tarski_0_3[THEN bspec, THEN bspec] ex by mauto
    show "\<exists>Z: set. \<forall>x: object. x in Z \<longleftrightarrow> x = y"
    proof (rule bexI[of _ X])
      show "\<forall>x:object. x in X \<longleftrightarrow> x = y" using A1 by auto
    qed mauto
qed simp

mdef tarski_def_2 ("{_ , _}") where
  mlet "y be object", "z be object"
  "func {y, z} \<rightarrow> set means \<lambda>it.
    \<forall>x. x in it \<longleftrightarrow> (x = y \<or> x = z)"
proof -
  obtain X where "X be set" and "(\<forall>x:object. (x in X \<longleftrightarrow> (x = y \<or> x = z)))"
    using tarski_0_3[THEN bspec, THEN bspec] by mauto
  thus "\<exists>X: set. \<forall>x: object. x in X \<longleftrightarrow> (x = y \<or> x = z)" using ex by auto
next
  fix IT1 IT2
  assume
    [ty]: "IT1 be set" and
    A1: "\<forall>x: object. (x in IT1 \<longleftrightarrow> x = y \<or> x = z)" and
    [ty]: "IT2 be set" and
    A2: "\<forall>x: object. (x in IT2 \<longleftrightarrow> x = y \<or> x = z)"
  {
    fix x assume [ty]: "x be object"
    have "x in IT1 \<longleftrightarrow> x=y \<or> x = z" using A1 by auto
    hence "x in IT1 \<longleftrightarrow> x in IT2" using A2 by auto
  }
  thus "IT1 = IT2" by (intro tarski_th_2) mauto
qed simp

mtheorem tarski_def_2_commutativity[simplified]:
  "commutativity object tarski_def_2"
proof(intro ballI)
  fix x y assume "x be object" "y be object"
  have "{x,y} be set" by mauto
  {
    fix z
    assume T1[ty]: "z be object"
    have "z in {x,y} \<longleftrightarrow> z = x \<or> z = y" using tarski_def_2 by auto
    hence "z in {x,y} \<longleftrightarrow> z in {y,x}" using tarski_def_2 by auto
  }
  thus "{x,y}={y,x}" by (intro tarski_th_2) mauto
qed simp_all

mdef tarski_def_3 (infixl "c=" 50)where
  mlet "X be set", "Y be set"
    "pred X c= Y means (\<forall>x: object. x in X \<longrightarrow> x in Y)" .

theorem tarski_def_3_reflexive:
  "reflexive set tarski_def_3" using tarski_def_3 by auto

abbreviation tarski_def_3_notation (infixl "\<subseteq>" 50) where
  "X \<subseteq> Y \<equiv> X c= Y"

lemmas tarski_def_3c = tarski_def_3_reflexive[THEN bspec, simplified]

mdef tarski_def_4 ("union _" [90] 90) where
  mlet "X be set"
    "func union X \<rightarrow> set means \<lambda>it.
      \<forall>x. x in it \<longleftrightarrow> (\<exists>Y. x in Y \<and> Y in X)"
proof -
  show "\<exists>IT: set. \<forall>x: object. x in IT \<longleftrightarrow> (\<exists>Y: set. x in Y \<and> Y in X)"
    using tarski_0_4 by mauto
next
  fix IT1 IT2
  assume T0[ty]: "IT1 be set" "IT2 be set"
  assume A1: "\<forall>x:object. (x in IT1 \<longleftrightarrow> (\<exists>Y:set. (x in Y \<and> Y in X)))" and
         A2: " \<forall>x:object. (x in IT2 \<longleftrightarrow> (\<exists>Y:set. (x in Y \<and> Y in X)))"
    {
     fix x
     assume T1[ty]:"x be object"
     have "x in IT1 \<longleftrightarrow> (\<exists>Y:set. (x in Y \<and> Y in X))" using A1 by inst_nopass_auto
     hence "x in IT1 \<longleftrightarrow> x in IT2" using A2 by inst_nopass_auto
    }
  thus "IT1 = IT2" by (intro tarski_th_2) inst_nopass_auto
qed simp

lemmas tarski_th_3 = tarski_0_5[THEN bspec, THEN bspec]

mtheorem prefix_in_asymmetry:
  "asymmetry set prefix_in"
proof (intro ballI notI impI)
  fix a b
  assume T0[ty]:"a be set" "b be set" thm ty
  assume A1:"a in b \<and> b in a"
  let ?X = "{ a , b }"
  have "a in ?X" using tarski_def_2 by auto
  then obtain Y where
  T1[ty]: "Y be set" and A4:"Y in ?X \<and> \<not>(\<exists>z:object. z in ?X \<and> z in Y)"
    using tarski_0_5[THEN bspec,THEN bspec,of a ?X] by inst_nopass_auto
  have "Y=a \<or> Y=b" using A4 tarski_def_2 by auto
  then show False using A1 A4 tarski_def_2 by inst_pass_auto
qed simp_all

theorem prefix_in_irreflexive:
  "irreflexive object prefix_in"
proof (intro ballI notI impI)
  fix a b
  assume [ty]:"a be object"
  assume A1:"a in a"
  let ?X = "{ a }"
  have "a in ?X" using tarski_def_1 by auto
  then obtain Y where
  A4: "Y be set \<and> Y in ?X \<and> \<not>(\<exists>z:object. z in ?X \<and> z in Y)"
    using tarski_0_5[THEN bspec,THEN bspec] by inst_nopass_auto
  have "Y=a" using A4 tarski_def_1 by auto
  then show False using A1 A4 tarski_def_1 by auto
qed simp_all

text_raw {*\DefineSnippet{tarski-def5}{*}
mdef tarski_def_5    ("[_ , _]") where
  mlet "x be object", "y be object"
  "func [x,y] \<rightarrow> object equals
     {{x, y} , {x}}"
text_raw {*}%EndSnippet*}
proof-
  show "{{x, y}, {x}} be object" by auto
qed

mtheorem
  mlet "x be object",
       " y be object"
 "cluster  [x,y] \<rightarrow> set"  using tarski_def_5[of x y] by inst_nopass_auto
  
mdef tarski_def_6 ("_,_ areequipotent" [100,100]) where
  mlet "X be set","Y be set"
  "pred X, Y areequipotent means
    (ex Z st
     (for x st x in X ex y st y in Y \<and> [x,y] in Z) \<and>
     (for y st y in Y ex x st x in X \<and> [x,y] in Z) \<and>
     (for x,y,z,u st [x,y] in Z \<and> [z,u] in Z holds x = z \<longleftrightarrow> y = u))" .

section "TARSKI_A"

axiomatization where
tarski_a_th_1:
  "\<forall>N.  ex M st N in M \<and>
     (for X,Y holds X in M \<and> Y c= X \<longrightarrow> Y in M) \<and>
     (for X st X in M ex Z st Z in M \<and> (for Y st Y c= X holds Y in Z)) \<and>
     (\<forall>X.  X c= M \<longrightarrow> X,M areequipotent \<or> X in M)"


text_raw {*\DefineSnippet{redefine_func_mode_property}{*}
lemma redefine_func_mode_property:
assumes lt: "lt" and
  coherence: "\<forall>x : M.  x be M1" and
  mode_ex: "inhabited(M)" and
  compatibility: "\<And> it. it be set \<Longrightarrow> ((it be M) \<longleftrightarrow> newCondition(it))"
shows "x be M \<Longrightarrow> (x be M1 \<and> newCondition (x))"
text_raw {*}%EndSnippet*}
proof
  assume T0[ty]: "x be M"
  thus "x be M1" using coherence mode_ex by simp
  show "newCondition (x)" using compatibility[of x,OF all_set] by inst_nopass_auto
qed

(* :: "Ty \<Rightarrow> o" *)
  
   

end



