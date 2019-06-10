
theory KPTest
  imports Ordinal Function
  

begin

lemma ballI : "\<lbrakk>\<And>x. P x\<rbrakk> \<Longrightarrow> \<forall>x. P x"
  by simp


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
  proof(rule ballI, rule impI)
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
  proof(rule ballI,rule impI)
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

theorem in_prop:
  "\<not> x \<in> x" sorry

theorem Regularity:
  "x \<in> X \<Longrightarrow> \<exists> y. y \<in> X \<and> y \<inter> X={}" sorry


theorem Muzukashi:
  assumes "epsilon_transitive U" "ZF_closed U" 
          "X \<subseteq>  U" "X \<notin> U"
  shows     "\<exists> b . (b : { x \<in> U | ordinal x} \<rightarrow> X) \<and> bijection b"
proof
  let ?Lamb ="{ x \<in> U | ordinal x}"
  let ?D= "?Lamb"
  let ?P = "\<lambda> a x f . (x \<in> ?D \<and> (\<forall> b. b \<in> a \<longrightarrow> f b \<noteq> x))\<or> (x = ?D \<and> (\<forall> y. y \<in> ?D \<longrightarrow> (\<exists> b. b \<in> a \<and> f b = y)))"
  obtain  Q where 
    QDef: "Q \<equiv> \<lambda> a f x . ?P a x f \<and> (\<forall>y. ?P a y f \<longrightarrow> VV x \<subseteq> VV y)" by simp
  obtain  F where
     FDef: "F\<equiv> \<lambda> a f . THE x. Q a f x" by simp
  let ?f=  "R_CB F"
  let ?g = "\<lambda> y . THE a . a \<in> ?Lamb \<and> ?f a = y"
  have C0:"\<And> a h k. (\<forall>b. b \<in> a \<longrightarrow> h b  = k b) \<Longrightarrow>
          (\<forall> y. y \<in> ?D \<longrightarrow> (\<exists> b. b \<in> a \<and> h b = y))  \<longleftrightarrow> (\<forall> y. y \<in> ?D \<longrightarrow> (\<exists> b. b \<in> a \<and> k b = y))"
  proof-
    fix a ::set fix h k ::"set \<Rightarrow> set" 
    assume hk: "\<forall>b. b \<in> a \<longrightarrow> h b  = k b"
    show "(\<forall> y. y \<in> ?D \<longrightarrow> (\<exists> b. b \<in> a \<and> h b = y))  \<longleftrightarrow>
         (\<forall> y. y \<in> ?D \<longrightarrow> (\<exists> b. b \<in> a \<and> k b = y))"
    proof(intro iffI ballI impI)
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
  proof(intro ballI impI)
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
  have C10: "\<And> a h k. (\<forall>b. b \<in> a \<longrightarrow>  h b = k b) \<Longrightarrow> (\<forall>x. Q a h x \<longrightarrow> Q a k x)"
  proof(intro ballI impI)
    fix a ::set fix h k ::"set \<Rightarrow> set" 
    fix x assume A: "(\<forall>b. b \<in> a \<longrightarrow>  h b = k b)" "Q a h x"
    hence "?P a x h" unfolding QDef by blast
    hence P: "?P a x k" using C8[OF A(1)] by auto
    have "\<forall>y. ?P a y k \<longrightarrow> VV x \<subseteq> VV y" 
    proof(intro ballI impI)
      fix y assume "?P a y k"
      hence "?P a y h" using C8[of a k h] A by auto
      then show  "VV x \<subseteq> VV y" using A(2) QDef by auto
    qed
    then show "Q a k x" using P QDef by auto
  qed
  have C_x: "\<And> a h x y .  Q a h x \<and> Q a h y \<Longrightarrow> x = y"
  proof-
    fix a ::set fix h ::"set \<Rightarrow> set" 
    fix x y assume A: "Q a h x \<and> Q a h y"
    hence P:"?P a x h" "?P a y h" unfolding QDef by auto+
    show "x=y" 
    proof(cases "(\<forall>y. y \<in> ?D \<longrightarrow> (\<exists>b. b \<in> a \<and> h b = y))")
      case True
        hence "x=?D" "y=?D" using P by auto
        thus ?thesis by auto
      next case F: False
        hence "ordinal x" "ordinal y" using P by auto 
        hence C: "x \<in> y \<or> x = y \<or> y \<in> x" using trichotomy by auto
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
    qed
  qed
  have H2: "\<forall> a f. \<exists> x. Q a f x"
  proof(standard,standard)
    fix a f
    show "\<exists> x. Q a f x" 
    proof (cases "\<forall> y. y \<in> ?D \<longrightarrow> (\<exists> b. b \<in> a \<and> f b = y)")
      case True
        hence "Q a f ?D" using QDef by auto
        then show ?thesis by auto
      next 
        case F: False
        then obtain y where
           y: "y \<in> ?D \<and> (\<forall> b. b \<in> a \<longrightarrow> f b \<noteq> y)" by auto
        let ?M = "{ VV x | x \<in> { xx \<in> ?D | (?P a xx f)}}"
        have "VV y \<in> ?M" using y by auto
        then obtain vv where
          vv:  " vv \<in> ?M \<and> vv \<inter> ?M={}" using  Regularity[of "VV y" ?M] by blast
        then obtain v where
          v: "vv = VV v \<and> v \<in> { xx \<in> ?D | (?P a xx f)}" by auto
        have "Q a f v" unfolding QDef
        proof
          show "?P a v f" using v by auto
          show "\<forall>y. ?P a y f \<longrightarrow> VV v \<subseteq> VV y"
          proof(standard,standard)
            fix y assume P: "?P a y f"
            hence V: "VV y \<in> ?M" using P F by auto
            then show "VV v \<subseteq> VV y" using VTh2_7[of y v] v vv by auto
          qed
        qed  
        then show ?thesis by auto
    qed
  qed

  have C11: "C F" unfolding C_def
  proof(intro ballI impI)
    fix a ::set fix h k ::"set \<Rightarrow> set" 
    fix x assume hk: "(\<forall>b. b \<in> a \<longrightarrow>  h b = k b)"
    obtain x where
       Q: "Q a h x" using H2 by auto
     hence "Q a k x" using  C10 hk by auto
     hence " F a h = x" " F a k = x" unfolding FDef using Q C_x by blast+
     thus "F a h = F a k" by auto
  qed

  hence C1: "(\<forall> X.?f X = F X ?f)" using Th1 by blast
qed

