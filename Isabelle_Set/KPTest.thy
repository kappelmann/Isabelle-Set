
theory KPTest
imports Pair 

begin


(*Brown, C.E.: Reconsidering Pairs and Functions as Sets. J. Autom. Reasoning
55(3), 199 - 210 (Oct 2015) 

Theorem 1
*)

definition G :: "(set \<Rightarrow> (set \<Rightarrow> set) \<Rightarrow> set) \<Rightarrow> set \<Rightarrow> set \<Rightarrow> bool" where
   "G \<equiv> \<lambda> \<Phi> X Y. \<forall> R. (\<forall> X F. (\<forall> x. x \<in> X \<longrightarrow> R x (F x)) \<longrightarrow> R X (\<Phi> X F)) \<longrightarrow> R X Y"

definition C :: "(set \<Rightarrow> (set \<Rightarrow> set) \<Rightarrow> set) \<Rightarrow> bool"  where
   "C \<equiv> \<lambda> \<Phi>. \<forall>X F G. (\<forall>x . x \<in> X \<longrightarrow> F x = G x) \<longrightarrow> \<Phi> X F = \<Phi> X G "

definition R_CB :: "(set \<Rightarrow> (set \<Rightarrow> set) \<Rightarrow> set) \<Rightarrow> set \<Rightarrow> set" where
      "R_CB \<equiv> \<lambda> \<Phi> X .(THE Y. G \<Phi> X Y)"



lemma Lm1: 
  "(\<forall> x . x \<in> X \<longrightarrow> G \<Phi> x (F x)) \<longrightarrow> G \<Phi> X ( \<Phi> X F)"
proof
  let ?Y = "\<Phi> X F"
  assume A1: "\<forall>x. x \<in> X \<longrightarrow> G \<Phi> x (F x)"
  show "G \<Phi> X (\<Phi> X F)" unfolding G_def
  proof (auto)
    fix R
    assume A2: "\<forall>X F. (\<forall>x. x \<in> X \<longrightarrow> R x (F x)) \<longrightarrow> R X (\<Phi> X F)"
    hence A3: "(\<forall>x. x \<in> X \<longrightarrow> R x (F x)) \<longrightarrow> R X (\<Phi> X F)" by auto
    have "\<forall>x. x \<in> X \<longrightarrow> R x (F x)"
    proof(auto)
      fix x assume "x \<in> X"
      hence "G \<Phi> x (F x)" using A1 by auto   
      hence "\<forall> R. (\<forall> X F. (\<forall> x. x \<in> X \<longrightarrow> R x (F x)) \<longrightarrow> R X (\<Phi> X F)) \<longrightarrow> R x (F x)" unfolding G_def by auto 
      then show "R x (F x)" using A2 by auto
    qed
    then show "R X (\<Phi> X F)" using A3 by auto
  qed  
qed

lemma Lm2:
   "(\<forall>X F.(\<forall>x. x \<in> X \<longrightarrow> G \<Phi> x(F x) \<and> R x (F x)) \<longrightarrow> R X ( \<Phi> X F)) \<longrightarrow> (\<forall> X Y . G \<Phi> X Y \<longrightarrow> R X Y)"
proof
  let ?RR =" \<lambda>x y. G \<Phi> x y  \<and> R x y"
  assume  "\<forall>X F. (\<forall>x. x \<in> X \<longrightarrow> G \<Phi> x (F x) \<and> R x (F x)) \<longrightarrow> R X (\<Phi> X F)"
  hence A1: "\<forall> X F. (\<forall> x. x \<in> X \<longrightarrow> ?RR x (F x)) \<longrightarrow> ?RR X (\<Phi> X F)" using Lm1 by auto
  show "\<forall>x y. G \<Phi> x y \<longrightarrow> R x y"
  proof(auto)
    fix x y assume "G \<Phi> x y"
    hence A2: "\<forall> R. (\<forall> X F. (\<forall> x. x \<in> X \<longrightarrow> R x (F x)) \<longrightarrow> R X (\<Phi> X F)) \<longrightarrow> R x y" unfolding G_def by auto
    show "R x y" using A1 A2[rule_format, of ?RR] by auto    
  qed
qed

lemma Lm3: "G \<Phi> X Y  \<longrightarrow> (\<exists> F. (\<forall>x . x \<in> X \<longrightarrow> G \<Phi> x (F x)) \<and> Y =  \<Phi> X F)"
proof
  assume A1:"G \<Phi> X Y"
  let ?RR = "\<lambda> X Y . (\<exists> F.(\<forall>x . x \<in> X \<longrightarrow> G \<Phi> x (F x)) \<and> Y = \<Phi> X F)"
  have A2: "(\<forall>X F.(\<forall>x. x \<in> X \<longrightarrow> G \<Phi> x(F x) \<and> ?RR x (F x)) \<longrightarrow> ?RR X ( \<Phi> X F)) \<longrightarrow> (\<forall> X Y . G \<Phi> X Y \<longrightarrow> ?RR X Y)"
    using Lm2[of \<Phi> ?RR] by blast
  have "\<forall>X F.(\<forall>x. x \<in> X \<longrightarrow> G \<Phi> x(F x) \<and> ?RR x (F x)) \<longrightarrow> ?RR X ( \<Phi> X F)" by auto
  then show "(\<exists> F. (\<forall>x . x \<in> X \<longrightarrow> G \<Phi> x (F x)) \<and> Y =  \<Phi> X F)" using A1 A2  by blast
qed

lemma Lm4:
   "C \<Phi> \<longrightarrow> (\<forall> X Y Z . (G \<Phi> X Y \<longrightarrow> G \<Phi> X Z \<longrightarrow> Y = Z))"
proof(standard)
  assume CPhi: "C \<Phi>"
  let ?P ="\<lambda> X. (\<forall> Y Z . (G \<Phi> X Y \<longrightarrow> G \<Phi> X Z \<longrightarrow> Y = Z))"
  have "\<forall>X. (\<forall>x. x \<in> X \<longrightarrow> ?P x) \<longrightarrow> ?P X"
  proof(standard,standard,standard,standard,intro impI)
    fix X Y Z 
    assume B: "\<forall>x. x \<in> X \<longrightarrow> (\<forall>Y Z. G \<Phi> x Y \<longrightarrow> G \<Phi> x Z \<longrightarrow> Y = Z)"
    assume A: "G \<Phi> X Y" "G \<Phi> X Z"
    then obtain f where 
      F:"(\<forall>x . x \<in> X \<longrightarrow> G \<Phi> x (f x)) \<and> Y =  \<Phi> X f" using Lm3 by blast
    obtain g where 
      G:"(\<forall>x . x \<in> X \<longrightarrow> G \<Phi> x (g x)) \<and> Z =  \<Phi> X g" using A Lm3 by blast
    have "\<forall>x . x \<in> X \<longrightarrow> f x = g x"
    proof(auto)
      fix x assume x: "x \<in> X"
      hence "G \<Phi> x (f x)" " G \<Phi> x (g x)" using F G by auto  
      then show "f x = g x" using B x by auto
    qed
    hence "\<Phi> X f = \<Phi> X g" using CPhi unfolding C_def by auto
    then show "Y = Z" using F G by auto
  qed
  then show "\<forall> X. ?P X" using elem_induct_axiom[of ?P] by blast
qed

lemma Lm5:
   "C \<Phi> \<longrightarrow> (\<forall>X . G \<Phi> X (R_CB \<Phi> X))"
proof
  assume CP: "C \<Phi>"
  let ?P = "\<lambda> X. G \<Phi> X (R_CB \<Phi> X)"
  have "\<forall>X. (\<forall>x. x \<in> X \<longrightarrow> ?P x) \<longrightarrow> ?P X"
  proof (auto)
    fix X assume A1:"\<forall>x. x \<in> X \<longrightarrow> ?P x" 
    hence T1: "G \<Phi> X ( \<Phi> X (R_CB \<Phi>))" using Lm1 by auto
    hence "\<forall> Z . G \<Phi> X Z \<longrightarrow> \<Phi> X (R_CB \<Phi>) = Z" using CP Lm4 by auto
    hence "(THE Y. G \<Phi> X Y) = \<Phi> X (R_CB \<Phi>)" using T1 by blast
    hence "R_CB \<Phi> X = \<Phi> X (R_CB \<Phi>)" unfolding R_CB_def by blast
    then show "G \<Phi> X (R_CB \<Phi> X)" using T1 by auto
  qed
  then show "\<forall> X. ?P X" using elem_induct_axiom[of ?P] by blast
qed

lemma Lm6:
 "C \<Phi> \<longrightarrow> (\<forall> X . G \<Phi> X (\<Phi> X (R_CB \<Phi>)))" using Lm1 Lm5 by blast

theorem Th1:
  "C \<Phi> \<longrightarrow> (\<forall> X . R_CB \<Phi> X = \<Phi> X (R_CB \<Phi>))" using Lm4 Lm5 Lm6 by blast


end
