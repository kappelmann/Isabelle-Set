theory KPTest

imports "../Ordinal" "../Function"

begin

(*Brown, C.E.: Reconsidering Pairs and Functions as Sets.
J. Autom. Reasoning 55(3), 199 - 210 (Oct 2015) 

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
  then show "\<forall> X. ?P X" using mem_induction[of ?P] by blast
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
  then show "\<forall> X. ?P X" using mem_induction[of ?P] by blast
qed

lemma Lm6:
 "C \<Phi> \<longrightarrow> (\<forall> X . G \<Phi> X (\<Phi> X (R_CB \<Phi>)))" using Lm1 Lm5 by blast

theorem Th1:
  "C \<Phi> \<longrightarrow> (\<forall> X . R_CB \<Phi> X = \<Phi> X (R_CB \<Phi>))" using Lm4 Lm5 Lm6 by blast

(*Chad E. Brown, Karol Pąk,	A Tale of Two Set Theories, 
   Intelligent Computer Mathematics - 12th Conference on Intelligent Computer Mathematics, CIIRC, Prague, Czech Republic, July 8-12, 2019.	*)

definition VV:: " set \<Rightarrow> set" where
  "VV = R_CB (\<lambda> X v . ( \<Union>x \<in> X. (powerset (v x))))"  

theorem VTh1:
  "\<forall> X. VV X = (\<Union>x \<in> X. powerset (VV x))"
proof
  fix X
  let ?\<Phi> = "\<lambda> X v . ( \<Union>x \<in> X. (powerset (v x)))"
  have "C ?\<Phi>" unfolding C_def by auto
  hence "R_CB ?\<Phi> X = ?\<Phi> X (R_CB ?\<Phi>)" using Th1 by auto
  then show "VV X = (\<Union>x \<in> X. powerset (VV x))" using VV_def by auto
qed

theorem VTh2_1:
  "x \<in> X \<and> y \<subseteq> VV x \<longrightarrow> y \<in> VV X"
proof
  assume "x \<in> X \<and> y \<subseteq> VV x" 
  hence " y \<in> (\<Union>x \<in> X. powerset (VV x))" by auto
  then show "y \<in> VV X" using VTh1[rule_format, of X] by auto
qed

theorem VTh2_2:
  "y \<in> VV X \<longrightarrow> (\<exists> x . x \<in> X \<and> y \<subseteq> VV x)"
proof
  assume "y \<in> VV X"
  hence "y \<in> (\<Union>x \<in> X. powerset (VV x))" using VTh1[rule_format, of X] by auto
  then show "\<exists> x . x \<in> X \<and> y \<subseteq> VV x" by auto
qed

theorem VTh2_3:
  "X \<subseteq> VV X"
proof-
  let ?P = "\<lambda> X . X \<subseteq> VV X"
  have "\<forall>X. (\<forall>x. x \<in> X \<longrightarrow> ?P x) \<longrightarrow> ?P X" using VTh2_1  by auto
  hence "\<forall>X. ?P X" using mem_induction[of ?P] by blast
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
    then show "\<forall>Y. ?PY Y" using mem_induction[of ?PY] by blast
  qed
  hence "\<forall>X. ?PX X" using mem_induction[of ?PX] by blast
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
      then show "\<forall>Y. ?PY Y" using mem_induction[of ?PY] by blast
  qed
  hence "\<forall>X. ?PX X" using mem_induction[of ?PX] by blast
  then show ?thesis by auto
qed

theorem VTh2_7:
  "VV X \<notin> VV Y \<longrightarrow> VV Y \<subseteq> VV X"
proof
  assume "VV X \<notin> VV Y"
  hence "X \<notin> VV Y" using VTh2_5 by auto
  then show "VV Y \<subseteq> VV X" using VTh2_6 by auto
qed

(*theorem in_prop:
  " x  \<notin> x"
proof-
  let ?IN = "\<lambda> x. x  \<notin> x"
  have I:"\<forall>X. (\<forall>x. x \<in> X \<longrightarrow> ?IN x) \<longrightarrow> ?IN X" by auto
  have "\<forall>X. (?IN X)" using mem_induction[rule_format,of ?IN ] by blast
  then show " x \<notin> x" by auto
qed*)


lemma contraposR: "\<not>P \<longrightarrow> \<not>Q \<Longrightarrow> Q \<longrightarrow> P" by blast

theorem Regularity:
  "x \<in> X \<longrightarrow> (\<exists> y. y \<in> X \<and> y \<inter> X={})"
proof(rule contraposR,rule impI)
  assume E: "\<not> (\<exists> y. y \<in> X \<and> y \<inter> X={})"      
  let ?IN="\<lambda> x. x \<notin> X"
  have "\<forall>A. (\<forall>x. x \<in> A \<longrightarrow> ?IN x) \<longrightarrow> ?IN A" using E by auto
  then show "x \<notin> X" using mem_induction[of ?IN] by blast
qed

theorem CB_Th_3:
  assumes "mem_transitive U" "ZF_closed U" 
  shows "\<forall>X. X  \<in> U \<longrightarrow> VV X \<in> U"
proof-
  let ?H = "\<lambda> X. X  \<in> U \<longrightarrow> VV X \<in> U"
  have "\<forall>X. (\<forall>x. x \<in> X \<longrightarrow> ?H x) \<longrightarrow> ?H X"
  proof(intro allI impI)
    let ?PV = "\<lambda> x . powerset (VV x)"
    fix X assume IH: "\<forall>x. x \<in> X \<longrightarrow> ?H x" "X \<in> U"
    have "\<forall>x. x \<in> X \<longrightarrow> ?PV x \<in> U"
    proof(intro allI impI)
      have XU: "X \<subseteq> U" using assms(1) mem_transitive_def IH by auto
      fix x assume "x \<in> X"
      hence "VV x \<in> U" using XU IH by auto
      thus  "?PV x \<in> U" using assms(2) ZF_closed_def by auto
    qed
    hence "{?PV  x| x \<in> X} \<in> U" using IH assms(2) ZF_closed_def[of U] by auto
    hence "(\<Union>x \<in> X. powerset (VV x)) \<in> U" using assms(2) ZF_closed_def[of U] by auto
    then show "VV X \<in> U" using VTh1[rule_format, of X] by auto
  qed
  then show "\<forall>X. ?H X" using mem_induction[of ?H] by blast
qed

definition AC_axiom where
 "AC_axiom \<equiv> \<forall> X. {} \<notin>  X \<longrightarrow> (\<exists> f. (f \<in> X \<rightarrow> \<Union> X) \<and> (\<forall>A. A\<in> X \<longrightarrow> f` A \<in> A))"

definition bij where 
  bij_typedef :"bij X Y \<equiv>  type( \<lambda> f . f \<in> X\<rightarrow>Y \<and> 
                        {f`x |x \<in> X} = Y \<and> 
                        (\<forall> x1 x2. x1\<in> X\<and> x2 \<in> X \<and> f`x1 = f`x2 \<longrightarrow> x1=x2) )" 

lemma bij_type_iff []: "f: bij X Y  \<longleftrightarrow> f \<in> X\<rightarrow>Y \<and> 
                        {f`x |x \<in> X} = Y \<and> 
                        (\<forall> x1 x2. x1\<in> X\<and> x2 \<in> X \<and> f`x1 = f`x2 \<longrightarrow> x1=x2)"
  using bij_typedef by unfold_types

lemma bij_typeI [intro]: "f \<in> X\<rightarrow>Y \<Longrightarrow>
                        {f`x |x \<in> X} = Y \<Longrightarrow> 
                        \<forall> x1 x2. x1\<in> X\<and> x2 \<in> X \<and> f`x1 = f`x2 \<longrightarrow> x1=x2 \<Longrightarrow> f: bij X Y"
  using bij_type_iff[of f X Y] by blast

lemma bij_typeE:  " f: bij X Y \<Longrightarrow>
                        f \<in> X \<rightarrow> Y \<and>
                        {f`x |x \<in> X} = Y \<and> 
                        (\<forall> x1 x2. x1\<in> X\<and> x2 \<in> X \<and> f`x1 = f`x2 \<longrightarrow> x1=x2)"
  using bij_type_iff[of f X Y] by blast

theorem bij_inv:
  " b:bij X Y \<Longrightarrow> \<exists> i . i:bij Y X"
proof-
   assume B: "b: bij X Y"
  have B1 :"b \<in> X\<rightarrow>Y\<and>
        {b`x |x \<in> X} = Y \<and>
        (\<forall> x1 x2. x1\<in> X\<and> x2 \<in> X \<and> b`x1 = b`x2 \<longrightarrow> x1=x2)" 
     using bij_typeE[OF B] by blast
   let ?i = "\<lambda> y. THE x. x \<in> X \<and> b`x =y"
  let ?I="\<lambda>y \<in> Y. ?i y"
  have "?I:bij Y X"
  proof
    have D1:"{?i y | y \<in> Y} \<subseteq> X"
    proof
      fix x assume "x \<in> {?i y | y \<in> Y}"
      then obtain y where
        y: "x= ?i y \<and> y\<in> Y" by auto
      then obtain a where
        a: "y= b`a \<and> a \<in> X" using B1[THEN conjunct2,THEN conjunct1] by blast
      hence "?i y = a" using a y B1 by blast
      thus "x\<in> X" using a y by auto
    qed
    have "X \<subseteq> {?i y | y \<in> Y}"
    proof
      fix x assume "x\<in>X" 
      hence "?i (b`x) = x" "b`x \<in> Y" using B1 by blast+
      thus "x\<in> {?i y | y \<in> Y}" by auto
    qed
    hence D: "X={?i y | y \<in> Y}" using D1 extensionality by auto
    have "?I \<in> Y \<rightarrow> {?i y | y \<in> Y}"  by auto
    thus "?I \<in> Y \<rightarrow> X" using D by auto
    show  "{?I`y |y \<in> Y} = X" using D extensionality by (auto simp: beta)
    show "\<forall> y1 y2. y1\<in> Y\<and> y2 \<in> Y \<and> ?I`y1 = ?I`y2 \<longrightarrow> y1=y2"
    proof(intro allI impI)
      fix y1 y2 assume  A1: "y1\<in> Y\<and> y2 \<in> Y \<and> ?I`y1 = ?I`y2"
      then obtain a1 a2 where
        a: "y1= b`a1 \<and> a1 \<in> X" "y2= b`a2 \<and> a2 \<in> X" using B1[THEN conjunct2,THEN conjunct1] by blast
      hence "?i y1 = a1" "?i y2 = a2" using a A1 B1 by blast+
      thus "y1=y2" using a A1 by (auto simp: beta)
    qed
  qed
  thus "\<exists> i . i:bij Y X" by auto
qed

theorem bij_prod:
  " b1:bij X Y \<and> b2:bij Y Z \<Longrightarrow> \<exists> i . i:bij X Z"
proof-
  assume B: "b1:bij X Y \<and> b2:bij Y Z"
  have B1 :"b1 \<in> X\<rightarrow>Y\<and>
        {b1`x |x \<in> X} = Y \<and>
        (\<forall> x1 x2. x1\<in> X\<and> x2 \<in> X \<and> b1`x1 = b1`x2 \<longrightarrow> x1=x2)" 
     using bij_typeE B by blast
  have B2 :"b2 \<in> Y\<rightarrow>Z\<and>
        {b2`x |x \<in> Y} = Z \<and>
        (\<forall> x1 x2. x1\<in>Y\<and> x2 \<in> Y \<and> b2`x1 = b2`x2 \<longrightarrow> x1=x2)" 
    using bij_typeE B by blast
  let ?p="\<lambda>x. (b2` (b1` x))"
  let ?P="\<lambda>x \<in> X. (?p x)"
  have "?P:bij X Z"
  proof
    have D1: "{?p x | x\<in>X} \<subseteq> Z"
    proof
      fix z assume z: "z \<in> {?p x | x\<in>X}"
      then obtain x where
         x:"z=?p x \<and> x \<in> X" by auto
      hence "b1`x \<in> Y" using B1[THEN conjunct2,THEN conjunct1] by auto 
      hence "b2` (b1`x) \<in> Z" using B2 by auto 
      thus "z \<in> Z" using x by auto
    qed
    have "Z \<subseteq> {?p x | x\<in>X}"
    proof
      fix z assume "z \<in> Z"
      then obtain y where
       y:"z = b2`y \<and> y \<in> Y" using B2 by blast 
      then obtain x where
       x:"y = b1`x \<and> x \<in> X" using B1 by blast 
      thus "z \<in> {?p x | x\<in>X}" using y by auto
    qed
    hence D: "{?p x | x\<in>X} = Z" using D1 extensionality by auto
    thus XZ: "?P \<in> X\<rightarrow> Z" by auto
    show "{?P` x| x\<in> X}=Z" using D extensionality by (auto simp: beta)
    show "\<forall> x1 x2. x1\<in>X\<and> x2 \<in> X \<and> ?P`x1 = ?P`x2 \<longrightarrow> x1=x2"
    proof(intro allI impI)
      fix x1 x2 assume A: "x1\<in>X\<and> x2 \<in> X \<and> ?P`x1 = ?P`x2"
      hence B: "b2`(b1`x1) = b2`(b1` x2)" using XZ by (auto simp: beta)
      have "b1`x1\<in>Y" "b1`x2\<in>Y" using A B1 by blast+ 
      hence "b1`x1 = b1`x2" using A B2[THEN conjunct2,THEN conjunct2,
       rule_format, of "b1`x1" "b1`x2"  ] B by auto
      thus "x1=x2" using A B1 [THEN conjunct2,THEN conjunct2,
       rule_format, of "x1" "x2"] by auto
    qed
  qed
  thus "\<exists> i . i:bij X Z" by auto
qed


theorem CB_Lm_1:
  assumes "mem_transitive U" "ZF_closed U" "AC_axiom"
          "X \<subseteq>  U" "X \<notin> U"
  shows   "\<exists> b . b: bij {x \<in> U | x:Ord} X"
proof-
  let ?Lamb ="{ x \<in> U |  x:Ord}"
  let ?P = "\<lambda> a x f . x \<in> X\<and> (\<forall> b. b \<in> a \<longrightarrow> f b \<noteq> x)"
  obtain  Q where 
    QDef: "Q \<equiv> \<lambda> a f x . ?P a x f \<and>(\<forall>y. ?P a y f \<longrightarrow> VV x \<subseteq> VV y)" by simp
  let ?powersetX = "(powerset X) \<setminus> {{}}"
  have ACd: "\<And> X. {} \<notin>  X \<Longrightarrow> (\<exists> f. (f \<in> X \<rightarrow> \<Union> X) \<and> (\<forall>A. A\<in> X \<longrightarrow> f` A \<in> A))" 
     using assms(3) AC_axiom_def by auto
  have "{} \<notin> ?powersetX" by auto
  then obtain AC where
    AC: "(AC \<in> ?powersetX \<rightarrow> \<Union> ?powersetX) \<and> (\<forall>A. A\<in> ?powersetX \<longrightarrow> AC` A \<in> A)" using ACd[of ?powersetX] by auto
  obtain  F where
     FDef: "F\<equiv> \<lambda> a f . AC` {x\<in>X| Q a f x}" by simp
  let ?f=  "R_CB F"
  let ?g = "\<lambda> y .THE a . a \<in> ?Lamb \<and> ?f a = y"
  have C8: "\<And> a h k. (\<forall>b. b \<in> a \<longrightarrow> h b  = k b) \<Longrightarrow> (\<forall>x. ?P a x h \<longrightarrow> ?P a x k)"
   using mem_irrefl by blast
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
    fix a assume A:"a \<in> ?Lamb"
    let ?I = "\<lambda> x. x \<in> ?Lamb \<longrightarrow> Q x ?f (?f x)"
    have " \<forall>a. (\<forall>x. x \<in> a \<longrightarrow> ?I x) \<longrightarrow> ?I a"
    proof(intro allI impI)
      fix a assume HI: "\<forall>x. x \<in> a \<longrightarrow> ?I x"
      assume a:"a \<in> ?Lamb"
      hence O: "a \<in> U \<and> a:Ord" by auto
      hence P: "powerset a \<subseteq> U" using assms ZF_closed_def mem_transitive_def[of U] by auto 
      have C13: "\<And> b. b \<in> a \<longrightarrow> Q b ?f (?f b)"
      proof(intro impI)
        have E: " mem_transitive a" using O unfolding Ord_typedef by unfold_types
        fix b assume b: "b \<in> a" 
        hence " b \<subseteq> a" using E mem_transitive_def[of a] by auto
        hence "b \<in> U" "b:Ord" using P Ord_transitive O b by auto
        then show "Q b ?f (?f b)" using b HI by auto
      qed
      have C14: "\<And> b. b \<in> a \<longrightarrow> ?f b \<in> X"
      proof
        fix b assume "b \<in> a"
        hence "Q b ?f (?f b)" using C13 by auto
        then show "?f b \<in> X"  unfolding QDef by auto
      qed      
      have C15: "{?f b|b \<in> a} \<subseteq> X" using C14 by auto
      have C14_1: "\<forall> b. b \<in> a \<longrightarrow> ?f b \<in> U" using C14 assms(4) by auto 
      have C16: "{?f b|b \<in> a} \<in> U" using assms(2) unfolding ZF_closed_def using C14_1 O by auto 
      have C17: "\<not> (\<forall> x. \<not>?P a x ?f)"
      proof
        assume "\<forall> x. \<not>?P a x ?f"
        hence "X \<subseteq> {?f b|b \<in> a}"  by auto
        hence "X = {?f b|b \<in> a}" using C15 extensionality by auto
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
      hence "{x\<in>X| Q a ?f x} \<in> ?powersetX" using x by auto
      hence A18: "AC` {x\<in>X| Q a ?f x} \<in> {x\<in>X| Q a ?f x}" using AC by auto
      have C19: "F a ?f =  AC` {x\<in>X| Q a ?f x}" using FDef by auto
      have "F a ?f = ?f a" using C1 FDef by auto
      then show "Q a ?f (?f a)" using A18 C19 by auto
    qed
    then show "Q a ?f (?f a)" using A  mem_induction[of ?I] by blast
  qed
  have C3: "\<And> a. a \<in> ?Lamb \<Longrightarrow> ?f a \<in> X"
  proof-
    fix a assume "a \<in> ?Lamb"
    hence "Q a ?f (?f a)" using C2 by auto
    then show  "?f a \<in> X" unfolding QDef by auto
  qed
  have C4:"\<And> a b. a \<in> ?Lamb \<and> b \<in> ?Lamb \<and> ?f a = ?f b \<Longrightarrow> a = b"
  proof-
    fix a b assume AS: "a \<in> ?Lamb \<and> b \<in> ?Lamb \<and> ?f a = ?f b"
    hence Q:"Q a ?f (?f a)" "Q b ?f (?f b)" using C2[of a] C2[of b] by auto
    hence P: "?P a (?f a) ?f" "?P b (?f b) ?f" unfolding QDef by auto
    have "\<not> a \<in> b" "\<not>b\<in> a" using P AS by auto
    thus "a=b" using AS Ord_trichotomy by auto
  qed
  have "\<And> x . x \<in> ?Lamb \<Longrightarrow> x \<subseteq> ?Lamb"
  proof-
    fix x assume "x \<in> ?Lamb"
    hence "x \<subseteq> U\<and> x:Ord " using mem_transitive_def assms by auto
    then show "x \<subseteq> ?Lamb" by (auto intro: Ord_transitive)
  qed
  hence E: "mem_transitive ?Lamb" using mem_transitive_def by auto
  have "\<forall> x. x \<in> ?Lamb \<longrightarrow> mem_transitive x" unfolding Ord_typedef by unfold_types auto
  hence OL: "?Lamb: Ord" using E Ord_typedef unfolding Ord_typedef by unfold_types auto
  let ?faLamb =" {?f a|a \<in> ?Lamb}"
  have C6_1: "?Lamb \<subseteq> {?g y| y \<in> ?faLamb}"
  proof
    fix x 
    assume xL: "x \<in> ?Lamb"
    hence "?g (?f x) = x" using C4 by blast
    then show "x \<in> {?g y| y \<in> ?faLamb}" using xL by auto
  qed
  have " {?g y| y \<in> ?faLamb} \<subseteq> ?Lamb"
  proof
    fix x 
    assume xG: "x\<in> {?g y| y \<in> ?faLamb}"
    then obtain y where
      y: "x = ?g y \<and> y\<in> ?faLamb" by auto
    then obtain a where
      a: "y = ?f a \<and> a \<in> ?Lamb" by auto
    hence "?g y = a" using C4 by blast
    thus "x \<in> ?Lamb" using a y by blast  
  qed
  hence C6: "?Lamb = {?g y| y \<in> ?faLamb}" using C6_1 extensionality by simp
  have C7:"\<forall>x. x \<in> X \<longrightarrow> (\<exists>a. a \<in> ?Lamb \<and> ?f a = x)"
  proof(rule allI,rule contraposR,auto)
    fix x assume A: "\<forall> a. a:Ord \<longrightarrow> a \<in> U \<longrightarrow> ?f a \<noteq> x" "x \<in> X" 
    have C20: "\<And> a . a \<in> ?Lamb \<Longrightarrow> ?P a x ?f"
    proof(intro allI impI conjI)
      fix a assume A1: "a \<in> ?Lamb" show "x \<in> X" using A by auto
      fix b assume A2: "b \<in> a"
      hence A3:"b :Ord" using A1 Ord_transitive by auto
      have "a \<subseteq> U" using A1 assms(1)  mem_transitive_def by auto
      then show "?f b \<noteq> x" using A A2 A3 by auto
    qed   
    have C21: "\<And> a . a \<in> ?Lamb \<Longrightarrow> VV (?f a) \<subseteq> VV x"
    proof-
      fix a assume "a \<in> ?Lamb" 
      hence "Q a ?f (?f a)" "?P a x ?f" using C2 C20 by auto
      then show "VV (?f a) \<subseteq> VV x" unfolding QDef by auto  
    qed
    have C22: "?faLamb \<in> U"
    proof-
      have "x \<in> U" using assms(4) A by auto
      hence "VV x \<in> U" using assms CB_Th_3 by auto
      hence "powerset (powerset (VV x)) \<in> U" using assms(2) ZF_closed_def by auto
      hence P: "powerset (powerset (VV x)) \<subseteq> U" using assms(1) mem_transitive_def by auto
      have "{?f a|a \<in> ?Lamb} \<subseteq> powerset (VV x)"
      proof
        fix fa assume "fa \<in> {?f a|a \<in> ?Lamb}"
        then obtain a where
           fa: "fa = ?f a \<and> a \<in>?Lamb" by auto
        hence "fa \<subseteq> VV fa" "VV (?f a) \<subseteq> VV x" using VTh2_3 C21 by auto
        then show "fa \<in> powerset (VV x)" using fa by auto
      qed
      then show "?faLamb \<in> U"  using P by auto
    qed
    have C23: "\<And> x. x \<in> ?faLamb \<Longrightarrow> ?g x \<in> U" 
    proof-
      fix y 
      assume "y\<in> ?faLamb"
       then obtain a where
         a: "y = ?f a \<and> a \<in> ?Lamb" by auto
      hence "?g y = a" using C4 by blast
      thus "?g y \<in> U" using a by auto
    qed
    have T1: "\<And> g. ?faLamb \<in> U \<longrightarrow> (\<forall>x. x \<in> ?faLamb \<longrightarrow> g x \<in> U) \<longrightarrow> repl ?faLamb g \<in> U" 
       using assms(2) unfolding ZF_closed_def by auto
    have "?Lamb \<in> U" using T1[of ?g, rule_format, OF C22 C23] C6 by auto
    then show "False" using mem_irrefl OL by auto  
  qed
  let ?T = "\<lambda>x \<in> ?Lamb. ?f x"
   
  have "?T: bij ?Lamb X"
  proof
    have O1: "{?f x | x \<in> ?Lamb} = X" using C3 C7 extensionality[rule_format, of "{?f x | x \<in> ?Lamb}" X] by auto
    thus T1: "?T \<in> ?Lamb \<rightarrow> X" by auto
    have V1: "{?T`x| x\<in> ?Lamb} \<subseteq> X" using C3 by (auto simp: beta)
    have "X \<subseteq> {?T`x| x\<in> ?Lamb}"
    proof
      fix t assume "t\<in>X"
      then obtain  x where
        x:  " x \<in> ?Lamb \<and> ?f x = t" using C7 by auto
      hence "?f x = ?T` x" by (auto simp: beta)  
      thus "t\<in> {?T`x| x\<in> ?Lamb}" using x by blast
    qed
    thus "{?T`x| x\<in> ?Lamb}=X" using V1 extensionality[rule_format, of "{?T`x| x\<in> ?Lamb}" X] by auto
    show "\<forall>x1 x2. x1 \<in> ?Lamb \<and> x2 \<in> ?Lamb \<and> ?T `x1 = ?T ` x2 \<longrightarrow>
       x1 = x2" using C4 by (auto simp: beta)
  qed
  thus "\<exists> b . b: bij {x \<in> U | x:Ord} X" by auto
qed

theorem CB_Th_5:
  assumes "mem_transitive U" "ZF_closed U" "AC_axiom"
      "X \<subseteq>  U" "X \<notin> U"
  shows "\<exists> b . b: bij X U" 
proof-
  have "\<exists> b . b: bij {x \<in> U | x:Ord} X" using CB_Lm_1 assms by auto
  then obtain b where
    b:  "b: bij X {x \<in> U | x:Ord}" using bij_inv by blast
  have "U \<subseteq> U" "U \<notin> U" using mem_irrefl by auto
  then obtain c where
    "c: bij {x \<in> U | x:Ord} U " using  CB_Lm_1 assms by blast
  thus "\<exists> b . b: bij X U" using bij_prod b by auto
qed

end

