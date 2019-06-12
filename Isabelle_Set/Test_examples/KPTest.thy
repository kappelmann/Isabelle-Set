theory KPTest
<<<<<<< HEAD:Isabelle_Set/KPTest.thy
  imports Ordinal Function  

begin


(*Brown, C.E.: Reconsidering Pairs and Functions as Sets. J. Autom. Reasoning
55(3), 199 - 210 (Oct 2015) 
=======
imports "../Ordinal" "../Function"

begin

(*Brown, C.E.: Reconsidering Pairs and Functions as Sets.
J. Autom. Reasoning 55(3), 199 - 210 (Oct 2015) 
>>>>>>> b5feecea758d54b6686e13767d8345a5f8d88705:Isabelle_Set/Test_examples/KPTest.thy

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
proof
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

(*Chad E. Brown, Karol Pąk,	A Tale of Two Set Theories, 
   Intelligent Computer Mathematics - 12th Conference on Intelligent Computer Mathematics, CIIRC, Prague, Czech Republic, July 8-12, 2019.	*)

definition VV:: " set \<Rightarrow> set" where
  "VV = R_CB (\<lambda> X v . ( \<Union>x \<in> X. (Pow (v x))))"  

theorem VTh1:
  "\<forall> X. VV X = \<Union>x \<in> X. (Pow (VV x))"
proof
  fix X
  let ?\<Phi> = "\<lambda> X v . ( \<Union>x \<in> X. (Pow (v x)))"
  have "C ?\<Phi>" unfolding C_def by auto
  hence "R_CB ?\<Phi> X = ?\<Phi> X (R_CB ?\<Phi>)" using Th1 by auto
  then show "VV X = \<Union>x \<in> X. (Pow (VV x))" using VV_def by auto
qed

theorem VTh2_1:
  "x \<in> X \<and> y \<subseteq> VV x \<longrightarrow> y \<in> VV X"
proof
  assume "x \<in> X \<and> y \<subseteq> VV x" 
  hence " y \<in> \<Union>x \<in> X. (Pow (VV x))" by auto
  then show "y \<in> VV X" using VTh1[rule_format, of X] by auto
qed

theorem VTh2_2:
  "y \<in> VV X \<longrightarrow> (\<exists> x . x \<in> X \<and> y \<subseteq> VV x)"
proof
  assume "y \<in> VV X"
  hence "y \<in> \<Union>x \<in> X. (Pow (VV x))" using VTh1[rule_format, of X] by auto
  then show "\<exists> x . x \<in> X \<and> y \<subseteq> VV x" by auto
qed

theorem VTh2_3:
  "X \<subseteq> VV X"
proof-
  let ?P = "\<lambda> X . X \<subseteq> VV X"
  have "\<forall>X. (\<forall>x. x \<in> X \<longrightarrow> ?P x) \<longrightarrow> ?P X" using VTh2_1  by auto
  hence "\<forall>X. ?P X" using elem_induct_axiom[of ?P] by blast
  then show  "X \<subseteq> VV X" by auto
qed

theorem VTh2_4:
   "X \<subseteq> VV Y \<longrightarrow> VV X \<subseteq> VV Y"
proof-
  let ?PX = "\<lambda> X .\<forall> Y. X \<subseteq> VV Y \<longrightarrow> VV X \<subseteq> VV Y"
  have "\<forall>X. (\<forall>x. x \<in> X \<longrightarrow> ?PX x) \<longrightarrow> ?PX X"
  proof(rule allI, rule impI)
    fix X assume AX: "\<forall>x. x \<in> X \<longrightarrow> ?PX x"
    let ?PY = "\<lambda> Y. X \<subseteq> VV Y \<longrightarrow> VV X \<subseteq> VV Y"
    have "\<forall>Y. (\<forall>y. y \<in> Y \<longrightarrow> ?PY y) \<longrightarrow> ?PY Y"
    proof(standard,standard,standard,standard)
      fix Y x assume AY: "\<forall>y. y \<in> Y \<longrightarrow> ?PY y" 
      assume XY: "X \<subseteq> VV Y" "x \<in> VV X"
      then obtain a where
        a:  "a \<in> X \<and> x \<subseteq> VV a" using VTh2_2 by blast 
      obtain b where
         b:  "b \<in> Y \<and> a \<subseteq> VV b" using VTh2_2 XY a by blast
      have Pa: "\<forall> Y. a \<subseteq> VV Y \<longrightarrow> VV a \<subseteq> VV Y" using a b AX by auto
      hence " x \<subseteq> VV b" using a b by auto
      then show "x \<in> VV Y" using VTh2_1 b by auto
    qed
    then show "\<forall>Y. ?PY Y" using elem_induct_axiom[of ?PY] by blast
  qed
  hence "\<forall>X. ?PX X" using elem_induct_axiom[of ?PX] by blast
  then show ?thesis by auto
qed

theorem VTh2_5:
  "X \<in> VV Y \<longrightarrow> VV X \<in> VV Y"
proof
  assume "X \<in> VV Y"
  then obtain  x where
   x: "x \<in> Y \<and> X \<subseteq> VV x" using VTh2_2[of X Y] by blast
  hence "VV X \<subseteq> VV x" using VTh2_4 by auto 
  then show "VV X \<in> VV Y" using x VTh2_1[of x Y "VV X"] by auto
qed
theorem VTh2_6:
  "X \<in> VV Y \<or> VV Y \<subseteq> VV X"
proof-
  let ?PX = "\<lambda> X .\<forall> Y. X \<in> VV Y \<or> VV Y \<subseteq> VV X"
  have "\<forall>X. (\<forall>x. x \<in> X \<longrightarrow> ?PX x) \<longrightarrow> ?PX X"
  proof(rule allI,rule impI)
    fix X assume AX: "\<forall>x. x \<in> X \<longrightarrow> ?PX x"
    let ?PY = "\<lambda> Y. X \<in> VV Y \<or> VV Y \<subseteq> VV X"
    have "\<forall>Y. (\<forall>y. y \<in> Y \<longrightarrow> ?PY y) \<longrightarrow> ?PY Y"
    proof(auto)
      fix Y y assume Yy: "\<forall>y. y \<in> Y \<longrightarrow> ?PY y" "X \<notin> VV Y" "y \<in> VV Y"      
      then obtain a where
         a: "a \<in> Y \<and> y \<subseteq> VV a" using VTh2_2[of y Y] by auto
      then obtain b where
         b: "b \<in> X \<and> \<not> b \<in> VV a" using Yy(2) VTh2_1[of _ Y X] by auto 
      hence "VV a \<subseteq> VV b" using a AX by auto
      then show "y \<in> VV X" using a VTh2_1[of b X y] b by auto
    qed
      then show "\<forall>Y. ?PY Y" using elem_induct_axiom[of ?PY] by blast
  qed
  hence "\<forall>X. ?PX X" using elem_induct_axiom[of ?PX] by blast
  then show ?thesis by auto
qed

theorem VTh2_7:
  "VV X \<notin> VV Y \<longrightarrow> VV Y \<subseteq> VV X"
proof
  assume "VV X \<notin> VV Y"
  hence "X \<notin> VV Y" using VTh2_5 by auto
  then show "VV Y \<subseteq> VV X" using VTh2_6 by auto
qed

<<<<<<< HEAD:Isabelle_Set/KPTest.thy


theorem in_prop:
  " x  \<notin> x"
proof-
  let ?IN = "\<lambda> x. x  \<notin> x"
  have I:"\<forall>X. (\<forall>x. x \<in> X \<longrightarrow> ?IN x) \<longrightarrow> ?IN X" by auto
  have "\<forall>X. (?IN X)" using elem_induct_axiom[rule_format,of ?IN ] by blast
  then show " x \<notin> x" by auto
qed


lemma contraposR: "\<not>P \<longrightarrow> \<not>Q \<Longrightarrow> Q \<longrightarrow> P" by blast

theorem Regularity:
  "x \<in> X \<longrightarrow> (\<exists> y. y \<in> X \<and> y \<inter> X={})"
proof(rule contraposR,rule impI)
  assume E: "\<not> (\<exists> y. y \<in> X \<and> y \<inter> X={})"      
  let ?IN="\<lambda> x. x \<notin> X"
  have "\<forall>A. (\<forall>x. x \<in> A \<longrightarrow> ?IN x) \<longrightarrow> ?IN A" using E by auto
  then show "x \<notin> X" using elem_induct_axiom[of ?IN] by blast
qed

theorem CB_Th_3:
  assumes "epsilon_transitive U" "ZF_closed U" 
  shows "\<forall>X. X  \<in> U \<longrightarrow> VV X \<in> U"
proof-
  let ?H = "\<lambda> X. X  \<in> U \<longrightarrow> VV X \<in> U"
  have "\<forall>X. (\<forall>x. x \<in> X \<longrightarrow> ?H x) \<longrightarrow> ?H X"
  proof(intro allI impI)
    let ?PV = "\<lambda> x . Pow (VV x)"
    fix X assume IH: "\<forall>x. x \<in> X \<longrightarrow> ?H x" "X \<in> U"
    have "\<forall>x. x \<in> X \<longrightarrow> ?PV x \<in> U"
    proof(intro allI impI)
      have XU: "X \<subseteq> U" using assms(1) epsilon_transitive_def IH by auto 
      fix x assume "x \<in> X"
      hence "VV x \<in> U" using XU IH by auto
      thus  "?PV x \<in> U" using assms(2) ZF_closed_def by auto
    qed
    hence "{?PV  x| x \<in> X} \<in> U" using IH assms(2) ZF_closed_def[of U] by auto
    hence "\<Union>x \<in> X. (Pow (VV x)) \<in> U" using assms(2) ZF_closed_def[of U] by auto
    then show "VV X \<in> U" using VTh1[rule_format, of X] by auto
  qed
  then show "\<forall>X. ?H X" using elem_induct_axiom[of ?H] by blast
qed
=======
lemmas in_prop = elem_irrefl

theorem Regularity:
  "x \<in> X \<Longrightarrow> \<exists> y. y \<in> X \<and> y \<inter> X={}"
  using foundation by blast
>>>>>>> b5feecea758d54b6686e13767d8345a5f8d88705:Isabelle_Set/Test_examples/KPTest.thy


theorem Muzukashi:
  assumes "epsilon_transitive U" "ZF_closed U" 
          "X \<subseteq>  U" "X \<notin> U"
<<<<<<< HEAD:Isabelle_Set/KPTest.thy
  shows   "\<exists> b . (b : { x \<in> U | ordinal x} \<rightarrow> X) \<and> bijection b"
proof
  let ?Lamb ="{ x \<in> U | ordinal x}"
  let ?P = "\<lambda> a x f . x \<in> X\<and> (\<forall> b. b \<in> a \<longrightarrow> f b \<noteq> x)"
=======
  shows     "\<exists> b . (b \<in> { x \<in> U | x : Ord} \<rightarrow> X) \<and> bijection b"
proof
  let ?Lamb ="{ x \<in> U | x : Ord}"
  let ?D= "?Lamb"
  let ?P = "\<lambda> a x f . (x \<in> ?D \<and> (\<forall> b. b \<in> a \<longrightarrow> f b \<noteq> x))\<or> (x = ?D \<and> (\<forall> y. y \<in> ?D \<longrightarrow> (\<exists> b. b \<in> a \<and> f b = y)))"
>>>>>>> b5feecea758d54b6686e13767d8345a5f8d88705:Isabelle_Set/Test_examples/KPTest.thy
  obtain  Q where 
    QDef: "Q \<equiv> \<lambda> a f x . ?P a x f \<and>(\<forall>y. ?P a y f \<longrightarrow> VV x \<subseteq> VV y)" by simp
  obtain  F where
     FDef: "F\<equiv> \<lambda> a f . (THE  x. Q a f x)" by simp
  let ?f=  "R_CB F"
<<<<<<< HEAD:Isabelle_Set/KPTest.thy
  let ?g = "\<lambda> y .THE a . a \<in> ?Lamb \<and> ?f a = y"
  have C8: "\<And> a h k. (\<forall>b. b \<in> a \<longrightarrow> h b  = k b) \<Longrightarrow> (\<forall>x. ?P a x h \<longrightarrow> ?P a x k)"
   using in_prop by blast
=======
  let ?g = "\<lambda> y . THE a . a \<in> ?Lamb \<and> ?f a = y"
  have C0:"\<And> a h k. (\<forall>b. b \<in> a \<longrightarrow> h b  = k b) \<Longrightarrow>
          (\<forall> y. y \<in> ?D \<longrightarrow> (\<exists> b. b \<in> a \<and> h b = y))  \<longleftrightarrow> (\<forall> y. y \<in> ?D \<longrightarrow> (\<exists> b. b \<in> a \<and> k b = y))"
  proof-
    fix a ::set fix h k ::"set \<Rightarrow> set" 
    assume hk: "\<forall>b. b \<in> a \<longrightarrow> h b  = k b"
    show "(\<forall> y. y \<in> ?D \<longrightarrow> (\<exists> b. b \<in> a \<and> h b = y))  \<longleftrightarrow>
         (\<forall> y. y \<in> ?D \<longrightarrow> (\<exists> b. b \<in> a \<and> k b = y))"
    proof(intro iffI allI impI)
      fix z assume "(\<forall> y. y \<in> ?D \<longrightarrow> (\<exists> b. b \<in> a \<and> h b = y))" "z \<in> ?D"
      hence "\<exists> b. b \<in> a \<and> h b = z" by auto
      then show "\<exists> b. b \<in> a \<and> k b = z" using hk by auto 
    next 
      fix z assume "(\<forall> y. y \<in> ?D \<longrightarrow> (\<exists> b. b \<in> a \<and> k b = y))" "z \<in> ?D"
      hence "\<exists> b. b \<in> a \<and> k b = z" by auto
      then show "\<exists> b. b \<in> a \<and> h b = z" using hk by auto 
    qed
  qed
  have C8: "\<And> a h k. (\<forall>b. b \<in> a \<longrightarrow> h b  = k b) \<Longrightarrow> (\<forall>x. ?P a x h \<longrightarrow> ?P a x k)"
  proof(intro allI impI)
    fix a ::set fix h k ::"set \<Rightarrow> set" 
     assume hk: "\<forall>b. b \<in> a \<longrightarrow> h b  = k b"
    fix x
    assume x: "?P a x h"
    show "?P a x k" 
    proof  (cases "\<forall> y. y \<in> X \<longrightarrow> (\<exists> b. b \<in> a \<and> h b = y)")
      case True then show ?thesis using x hk C0 by blast
    next
      case False then show ?thesis using x hk in_prop C0 by blast
    qed
  qed
>>>>>>> b5feecea758d54b6686e13767d8345a5f8d88705:Isabelle_Set/Test_examples/KPTest.thy
  have C10: "\<And> a h k. (\<forall>b. b \<in> a \<longrightarrow>  h b = k b) \<Longrightarrow> (\<forall>x. Q a h x \<longrightarrow> Q a k x)"
  proof(intro allI impI)
    fix a ::set fix h k ::"set \<Rightarrow> set" 
    fix x assume A: "(\<forall>b. b \<in> a \<longrightarrow>  h b = k b)" "Q a h x"
    hence P: "?P a x k"  unfolding QDef using C8[OF A(1)] by auto
    have "\<forall>y. ?P a y k \<longrightarrow> VV x \<subseteq> VV y" 
    proof(intro allI impI)
      fix y assume "?P a y k"
      hence "?P a y h" using C8[of a k h] A by auto
      then show  "VV x \<subseteq> VV y" using A QDef by auto
    qed
    then show "Q a k x" using P QDef by auto
  qed
  have C11: "C F" unfolding C_def
  proof(intro allI impI)
    fix a ::set fix h k ::"set \<Rightarrow> set" 
    fix x assume hk: "(\<forall>b. b \<in> a \<longrightarrow>  h b = k b)"
    have "Q a h = Q a k" unfolding QDef using hk by auto
    then show "F a h = F a k" using FDef by auto
  qed
  hence C1: "(\<forall> X.?f X = F X ?f)" using Th1 by blast
  have C2:"\<And> a. a \<in> ?Lamb \<Longrightarrow> Q a ?f (?f a)"
  proof-
<<<<<<< HEAD:Isabelle_Set/KPTest.thy
    fix a assume A:"a \<in> ?Lamb"
    let ?I = "\<lambda> x. x \<in> ?Lamb \<longrightarrow> Q x ?f (?f x)"
    have " \<forall>a. (\<forall>x. x \<in> a \<longrightarrow> ?I x) \<longrightarrow> ?I a"
    proof(intro allI impI)
      fix a assume HI: "\<forall>x. x \<in> a \<longrightarrow> ?I x"
      assume a:"a \<in> ?Lamb"
      hence O: "a \<in> U \<and> ordinal a" by auto
      hence P: "Pow a \<subseteq> U" using assms ZF_closed_def epsilon_transitive_def[of U] by auto 
      have C13: "\<And> b. b \<in> a \<longrightarrow> Q b ?f (?f b)"
      proof(intro impI)
        fix b assume b: "b \<in> a"
        hence " b \<subseteq> a" using O unfolding ordinal_def using epsilon_transitive_def[of a] by auto
        hence "b \<in> U" "ordinal b" using P ord_th2 O b by auto
        then show "Q b ?f (?f b)" using b HI by auto
      qed
      have C14: "\<And> b. b \<in> a \<longrightarrow> ?f b \<in> X"
      proof
        fix b assume "b \<in> a"
        hence "Q b ?f (?f b)" using C13 by auto
        then show "?f b \<in> X"  unfolding QDef by auto
      qed      
      have C15: "{?f b|b \<in> a} \<subseteq> X" using C14 by auto
      have C14_1: "\<forall> b. b \<in> a \<longrightarrow> ?f b \<in> U" using C14 assms(3) by auto 
      have C16: "{?f b|b \<in> a} \<in> U" using assms(2) unfolding ZF_closed_def using C14_1 O by auto 
      have C17: "\<not> (\<forall> x. \<not>?P a x ?f)"
      proof
        assume "\<forall> x. \<not>?P a x ?f"
        hence "X \<subseteq> {?f b|b \<in> a}"  by auto
        hence "X = {?f b|b \<in> a}" using C15 extensionality_axiom by auto
        then show False using C16 assms by auto
      qed
      then obtain xx where
        xx: "?P a xx ?f" by auto
      let ?Pa = "{x \<in> X | \<forall>b. b \<in> a \<longrightarrow> ?f b \<noteq> x}"
      let ?Va = "{VV x | x \<in> ?Pa}"
      have "VV xx \<in> ?Va" using xx by auto
      then obtain v where
        v: "v \<in> ?Va \<and> v \<inter> ?Va={}" using Regularity[of "VV xx" "?Va"] by auto 
      then obtain x where
       x: "v = VV x \<and> ?P a x ?f" by auto
      have "\<forall>y. ?P a y ?f \<longrightarrow> VV x \<subseteq> VV y" using x v VTh2_7[of _ x] by auto 
      hence C18: "Q a ?f x" unfolding QDef using x by auto 
      have C19: "F a ?f =  (THE x. Q a ?f x)" using FDef by auto
      have "F a ?f = ?f a" using C1 FDef by auto
    (*  have "\<And> z t . Q a ?f z\<and>Q a ?f t \<longrightarrow> z =t"
      proof
        fix z t assume QQ: "Q a ?f z\<and>Q a ?f t"
        hence PP: "?P a z ?f" "?P a t ?f" unfolding QDef by auto
        hence "VV z \<subseteq> VV t" "VV t \<subseteq> VV z" using QQ unfolding QDef by auto
        hence "VV z = VV t" using extensionality_axiom by auto
        have "z \<in> a"using PP sorry
        show "z=t" sorry
      qed
      hence "(THE  z. (Q a ?f z)) =  x " using C18 by auto
      hence "x = F a ?f" "F a ?f = ?f a" using C1 FDef by auto*)
      then show "Q a ?f (?f a)" using C18 C19 sorry
=======
    fix a ::set fix h ::"set \<Rightarrow> set" 
    fix x y assume A: "Q a h x \<and> Q a h y"
    hence P:"?P a x h" "?P a y h" unfolding QDef by auto+
    show "x=y" 
    proof(cases "(\<forall>y. y \<in> ?D \<longrightarrow> (\<exists>b. b \<in> a \<and> h b = y))")
      case True
        hence "x=?D" "y=?D" using P by auto
        thus ?thesis by auto
      next case F: False
        hence "x : Ord" "y : Ord" using P by auto 
        hence C: "x \<in> y \<or> x = y \<or> y \<in> x" using Ord_trichotomy by auto
        have "VV x \<subseteq> VV y" "VV y \<subseteq> VV x" using A P unfolding QDef by blast+
        hence E: "VV x =VV y" using extensionality_axiom VTh2_3 by auto
        have C1: "\<not> x \<in> y"
        proof
          assume "x \<in> y"
          hence "x \<in> VV y" using VTh2_3 by auto
          hence "VV x \<in> VV y" using VTh2_5 by auto 
          thus "False" using E in_prop by auto
        qed
        have C2: "\<not> y \<in> x"
        proof
          assume "y \<in> x"
          hence "y \<in> VV x" using VTh2_3 by auto
          hence "VV y \<in> VV x" using VTh2_5 by auto 
          thus "False" using E in_prop by auto
        qed
        thus "x=y" using C C1 by simp
>>>>>>> b5feecea758d54b6686e13767d8345a5f8d88705:Isabelle_Set/Test_examples/KPTest.thy
    qed
    then show "Q a ?f (?f a)" using A  elem_induct_axiom[of ?I] by blast
  qed
  have C3: "\<And> a. a \<in> ?Lamb \<Longrightarrow> ?f a \<in> X"
  proof-
    fix a assume "a \<in> ?Lamb"
    hence "Q a ?f (?f a)" using C2 by auto
    then show  "?f a \<in> X" unfolding QDef by auto
  qed
<<<<<<< HEAD:Isabelle_Set/KPTest.thy
  have C4:"\<And> a b. a \<in> ?Lamb \<and> b \<in> ?Lamb \<and> ?f a = ?f b \<Longrightarrow> a = b"
  proof-
    fix a b assume AS: "a \<in> ?Lamb \<and> b \<in> ?Lamb \<and> ?f a = ?f b"
    hence Q:"Q a ?f (?f a)" "Q b ?f (?f b)" using C2[of a] C2[of b] by auto
    hence P: "?P a (?f a) ?f" "?P b (?f b) ?f" unfolding QDef by auto
    have "\<not> a \<in> b" "\<not>b\<in> a" using P AS by auto
    thus "a=b" using AS trichotomy by auto
  qed
  have "\<And> x . x \<in> ?Lamb \<Longrightarrow> x \<subseteq> ?Lamb"
  proof-
    fix x assume "x \<in> ?Lamb"
    hence "x \<subseteq> U\<and>ordinal x " using epsilon_transitive_def assms by auto
    then show "x \<subseteq> ?Lamb" using ord_th2 by auto
=======

  have C11: "C F" unfolding C_def
  proof(intro allI impI)
    fix a ::set fix h k ::"set \<Rightarrow> set" 
    fix x assume hk: "(\<forall>b. b \<in> a \<longrightarrow>  h b = k b)"
    obtain x where
       Q: "Q a h x" using H2 by auto
     hence "Q a k x" using  C10 hk by auto
     hence " F a h = x" " F a k = x" unfolding FDef using Q C_x by blast+
     thus "F a h = F a k" by auto
>>>>>>> b5feecea758d54b6686e13767d8345a5f8d88705:Isabelle_Set/Test_examples/KPTest.thy
  qed
  hence E: "epsilon_transitive ?Lamb" using epsilon_transitive_def by auto
  have "\<forall> x. x \<in> ?Lamb \<longrightarrow> epsilon_transitive x" unfolding ordinal_def by auto
  hence "ordinal ?Lamb" using E ordinal_def[of ?Lamb] by simp
  have C6: "?Lamb = {?g y|y \<in> ?Lamb}" sorry 
    (*let ?g = "\<lambda> y .THE a . a \<in> ?Lamb \<and> ?f a = y"*)

  have C7:"\<forall>x. x \<in> X \<longrightarrow> (\<exists>a. a \<in> ?Lamb \<and> ?f a = x)"
  proof(rule allI,rule contraposR,auto)
    fix x assume A: "\<forall> a. ordinal a \<longrightarrow> a \<in> U \<longrightarrow> ?f a \<noteq> x" "x \<in> X" 
    have C20: "\<And> a . a \<in> ?Lamb \<Longrightarrow> ?P a x ?f"
    proof(intro allI impI conjI)
      fix a assume A1: "a \<in> ?Lamb" show "x \<in> X" using A by auto
      fix b assume A2: "b \<in> a"
      hence A3:"ordinal b" using A1 ord_th2 by auto
      have "a \<subseteq> U" using A1 assms(1)  epsilon_transitive_def by auto
      then show "?f b \<noteq> x" using A A2 A3 by auto
    qed   
    have C21: "\<And> a . a \<in> ?Lamb \<Longrightarrow> VV (?f a) \<subseteq> VV x"
    proof-
      fix a assume "a \<in> ?Lamb" 
      hence "Q a ?f (?f a)" "?P a x ?f" using C2 C20 by auto
      then show "VV (?f a) \<subseteq> VV x" unfolding QDef by auto  
    qed
    have C22: "{?f a|a \<in> ?Lamb} \<in> U"
    proof-
      have "x \<in> U" using assms(3) A by auto
      hence "VV x \<in> U" using assms CB_Th_3 by auto
      hence "Pow (Pow (VV x)) \<in> U" using assms(2) ZF_closed_def by auto
      hence P: "Pow (Pow (VV x)) \<subseteq> U" using assms(1) epsilon_transitive_def by auto
      have "{?f a|a \<in> ?Lamb} \<subseteq> Pow (VV x)"
      proof
        fix fa assume "fa \<in> {?f a|a \<in> ?Lamb}"
        then obtain a where
           fa: "fa = ?f a \<and> a \<in>?Lamb" by auto
        hence "fa \<subseteq> VV fa" "VV (?f a) \<subseteq> VV x" using VTh2_3 C21 by auto
        then show "fa \<in> Pow (VV x)" using fa by auto
      qed
      then show "{?f a|a \<in> ?Lamb} \<in> U"  using P by auto
    qed
    
    thm "ZF_closed_def"
       


<<<<<<< HEAD:Isabelle_Set/KPTest.thy

    qed
  qed
qed
=======
  hence C1: "(\<forall> X.?f X = F X ?f)" using Th1 by blast
oops

end
>>>>>>> b5feecea758d54b6686e13767d8345a5f8d88705:Isabelle_Set/Test_examples/KPTest.thy
