section \<open>Axioms of HOTG\<close>

theory Set_Theory_Axioms_T
imports More_HOL

begin

text \<open>
Axiomatic basis of higher-order Tarski-Grothendieck set theory embedded in HOL.

We axiomatize a rigid type \<open>set\<close>, with the standard set-theoretic operations and axioms.
\<close>

typedecl set

axiomatization
  elem :: "set \<Rightarrow> set \<Rightarrow> bool" (infixl "\<in>" 50) and
  pair :: "set \<Rightarrow> set \<Rightarrow> set " ( "{ _ , _ }" 90) and
  Union :: "set \<Rightarrow> set" ("\<Union>_" [90] 90) and
  ReplP :: "set \<Rightarrow> (set \<Rightarrow> set \<Rightarrow> bool) \<Rightarrow> set"
where
  extensionality_axiom_in: "\<forall>X Y .(\<forall>x. x \<in> X \<longleftrightarrow> x \<in> Y) \<longrightarrow> X = Y"
and
  pair_axiom: "z \<in> {x,y} \<longleftrightarrow> z = x \<or> z = y"
and
  union_axiom: "\<forall>X x. x \<in> \<Union>X \<longleftrightarrow> (\<exists>Y. Y \<in> X \<and> x \<in> Y)"
and
  regularity_axiom: "\<forall>x X. x \<in> X \<longrightarrow> (\<exists>Y. Y \<in> X \<and> \<not>(\<exists>z. z \<in> X \<and> z \<in> Y))"
and
  ReplacementP_axiom: "\<forall>X y. (\<forall> x y z. (Q x y \<and> Q x z) \<longrightarrow> y = z)  \<longrightarrow>   y \<in> ReplP X Q \<longleftrightarrow> (\<exists>x. x \<in> X \<and> Q x y)"

definition subset :: "set \<Rightarrow> set \<Rightarrow> bool" (infixl "\<subseteq>" 50) \<comment> \<open>subset relation\<close>
  where "A \<subseteq> B \<equiv> (\<forall>x. x \<in> A \<longrightarrow> x \<in> B)"

lemma extensionality_axiom:
 "\<forall>X Y. X \<subseteq> Y \<longrightarrow> Y \<subseteq> X \<longrightarrow> X = Y" using extensionality_axiom_in subset_def by blast 

definition Pair :: "set \<Rightarrow> set \<Rightarrow> set" 
  where " Pair a b  \<equiv> {{a, a}, {a, b}}"

definition equipotent :: "set \<Rightarrow> set \<Rightarrow> bool" 
  where "equipotent A B \<equiv>  \<exists> Z.(
       (\<forall> x. x \<in> A \<longrightarrow> (\<exists> y. y \<in> B \<and>  Pair x y \<in> Z)) \<and>
       (\<forall> y. y \<in> B \<longrightarrow> (\<exists> x. x \<in> A \<and> Pair x y \<in> Z)) \<and>
       (\<forall> x y z u. Pair x y \<in> Z \<and> Pair z u  \<in> Z \<longrightarrow> (x = z \<longleftrightarrow> y = u)))"

axiomatization
  Tarski :: "set \<Rightarrow> set"
where
  Tarski_elem: "X \<in> Tarski X"
and
  Tarski_subset_closed: "A \<in> Tarski X \<and> B \<subseteq> A \<longrightarrow> B \<in> Tarski X"
and
  Tarski_power_closed: "A \<in> Tarski X \<longrightarrow> (\<exists> P . P \<in> Tarski X \<and> (\<forall> B. B \<subseteq> A \<longrightarrow> B \<in> P))"
and
  Tarski_equipotent: "A \<in> Tarski X \<longrightarrow> equipotent A (Tarski X) \<or> A \<in> Tarski X"

definition Repl :: "set \<Rightarrow> (set \<Rightarrow> set) \<Rightarrow> set" 
   where "Repl X F \<equiv> ReplP X (\<lambda> x y. y = F x)" 
  
lemma Replacement_axiom: 
  "y \<in> Repl X F \<longleftrightarrow> (\<exists>x. x \<in> X \<and> y = F x)" using  ReplacementP_axiom Repl_def by auto

definition power:: "set \<Rightarrow> set" where
  "power X \<equiv> ReplP (Tarski X) (\<lambda>x y. x \<subseteq> X \<and> x = y)" 

lemma Pow_axiom: "\<forall>A x. x \<in> power A \<longleftrightarrow> x \<subseteq> A"
proof(standard,standard)
  fix A x
  let ?Q = "\<lambda>x y. x \<subseteq> A \<and> x = y"
  let ?T = "Tarski A"
  show "x \<in> power A \<longleftrightarrow> x \<subseteq> A" 
  proof
    assume "x \<in> power A"
    hence "\<exists>y. y \<in> ?T \<and> ?Q y x" using power_def ReplacementP_axiom by auto
    then show "x \<subseteq> A" by auto
  next
    assume xA: "x \<subseteq> A"
    hence "x \<in> ?T" using Tarski_subset_closed Tarski_elem by auto
    then show "x \<in> power A" using power_def ReplacementP_axiom xA by auto
  qed
qed

definition  empty :: set ("{}") where
  "{} \<equiv> ReplP (THE x. True) (\<lambda> x y. False)"

lemma empty_axiom: "\<not>(\<exists>x. x \<in> {})"
proof
  let ?Q = "\<lambda> x y. False"
  assume "\<exists>x. x \<in> {}"
  then obtain x where 
    "x \<in> {}" by auto
  then show "False" using ReplacementP_axiom[rule_format, of ?Q x "THE x. True"] empty_def by auto
qed



lemma in_asymmetry: "x \<in> y \<longrightarrow> \<not> y \<in> x"
proof(auto)
  assume A1: "x \<in> y" "y \<in> x"
  have "x \<in> {x,y}" using pair_axiom by auto
  then obtain Y where
  A2:  "Y \<in> {x,y} \<and> \<not>(\<exists>z. z \<in> {x,y} \<and> z \<in> Y)" using regularity_axiom[rule_format, of x "{x,y}"] by auto
  hence " Y=x \<or> Y=y" using  pair_axiom by auto  
  then show "False" using A1 pair_axiom A2 by auto
qed


end
