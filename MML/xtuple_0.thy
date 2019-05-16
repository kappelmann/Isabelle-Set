theory xtuple_0
imports xboole_0 enumset_1
begin

reserve x,y,z,y1,y2 for object
reserve X,Y for set


  
text_raw {*\DefineSnippet{pair_def}{*}    
mdef xtuple_0_def_1 ("pair") where
 "attr pair for object means 
    (\<lambda>X. ex x1,x2 be object st X=[x1,x2])".
text_raw {*}%EndSnippet*}

theorem xtuple_0_lm_1:
   "{x} = {y1,y2} \<longrightarrow> x = y1"
proof
  assume "{ x } = { y1,y2 }"
  hence "y1 in { x }" using tarski_def_2 by simp
  thus "x = y1" using tarski_def_1 by simp
qed

theorem xtuple_0_lm_2:
   "{x} = {y1,y2} \<longrightarrow> y1 = y2"
proof
  assume A1: "{ x } = { y1,y2 }"
  hence A2: "x = y1" using A1 xtuple_0_lm_1[of "x"] by simp
  have "{y1,y2} = {y2,y1}" using tarski_def_2_commutativity by auto
  hence "x= y2" using A1 xtuple_0_lm_1[of "x"] A1 by simp
  thus "y1 = y2" using A2 by simp
qed

theorem xtuple_0_lm_3:
   "{ x1,x2 } = { y1,y2 } \<longrightarrow> x1 = y1 \<or> x1 = y2"
proof
   assume A1: "{ x1,x2 } = { y1,y2 }"
   have "x1 in {x1,x2}" using tarski_def_2 by auto
   hence "x1 in {y1,y2}" using A1 by simp
   thus "x1 = y1 \<or> x1 = y2" using tarski_def_2 by simp
qed

theorem xtuple_0_th_1:
  "[x1,x2] = [y1,y2] \<longrightarrow> x1 = y1 \<and> x2 = y2"
proof
  have A0: "{{x1,x2},{x1}} =[x1,x2]" "{{y1,y2},{y1}}=[y1,y2]" using tarski_def_5 by auto
  assume A1: "[x1,x2] = [y1,y2]"
  hence A1' : "{{x1},{x1,x2}} = {{y1,y2},{y1}}" using tarski_def_2_commutativity[of "{x1}" "{x1,x2}"] A0
    by simp
  show "x1=y1 \<and> x2=y2"
proof (cases "y1=y2")
  assume A5: "y1=y2"
  hence "{{x1,x2},{x1}} = {{y1},{y1}}" using A1 enumset1_th_29 A0 by auto
  also have "\<dots> = {{y1}}" using enumset1_th_29 by auto
  finally have "{{x1,x2},{x1}} = {{y1}}" by simp
  hence B: "{ y1 } = { x1,x2 }" using xtuple_0_lm_1[of "{y1}" "{x1,x2}" "{x1}"]  by auto
  hence "{y1}= {x2,x1}" using tarski_def_2_commutativity by auto
  hence "y1 = x1 \<and> y1 = x2" using B xtuple_0_lm_1[of "y1" "x1" "x2"] xtuple_0_lm_1[of "y1"] by infer_auto
  thus ?thesis using A5 by auto
next
   assume A2: "y1 \<noteq> y2"
   hence A3: "{x1} \<noteq> {y1,y2}" using xtuple_0_lm_2[of "x1" "y1" "y2"] by auto
   hence B1: "{x1} = {y1}" using A1 A1' xtuple_0_lm_3[of "{x1}" "{x1,x2}" "{y1,y2}"]  by auto
   have "x1 in {x1}" using tarski_def_1 by simp
   hence A4:"x1=y1" using B1 tarski_def_1 by simp
   have B2: "{y1,y2} = {x1,x2}" using A1 A1' A3 xtuple_0_lm_3[of "{y1,y2}" "{y1}" "{x1}" "{x1,x2}"] by auto
   have "y2 in {y1,y2}" using tarski_def_2 by simp
   hence "y2 in {x1,x2}" using B2 by simp
   hence "y2 = x1 \<or> y2 = x2" using tarski_def_2 by auto
   hence "x2 = y2" using A2 A4 by auto
   with A4 show ?thesis by simp
  qed
qed
lemma xtuple_0_th_1a: "[x1,x2] = [y1,y2] \<longleftrightarrow> x1 = y1 \<and> x2 = y2"
  using xtuple_0_th_1 by blast

mtheorem
  "cluster pair for object"
proof(standard,standard)
  show "[the set,the set] is pair\<bar>object" using xtuple_0_def_1 by infer_auto  
qed  
  
text_raw {*\DefineSnippet{permissive_def}{*}
mdef xtuple_0_def_2("_ `1" [90] 95) where
  mlet "x be object"
  "assume x is pair func x `1 \<rightarrow> object means
     (\<lambda>it. for y1,y2 be object st x=[y1,y2] holds it = y1)"
  text_raw {*}%EndSnippet*}
proof -
    assume [ty]: "x is pair"
    obtain x1 x2 where
       [ty]:"x1 be object" "x2 be object" and A1: "x = [x1,x2]" using xtuple_0_def_1[of x] by infer_auto
    show "ex it being object st for y1,y2 be object st x=[y1,y2] holds it = y1"
      proof(rule bexI[of _ x1],intro ballI impI)
        show "x1 be object" by simp
        fix y1 y2
        assume "y1 be object" "y2 be object" "x=[y1,y2]"
        thus "x1 = y1" using xtuple_0_th_1a A1 by simp
      qed simp_all
  next
    assume [ty]: "x is pair"
     obtain x1 x2 where
       [ty]: "x1 be object" "x2 be object" and A1: "x = [x1,x2]" using xtuple_0_def_1[of x] by infer_auto
     fix e1 e2
     assume [ty]: "e1 be object"
                "e2 be object" and
    A2: "for y1,y2 be object st x=[y1,y2] holds e1 = y1" and
    A3: "for y1,y2 be object st x=[y1,y2] holds e2 = y1"
     have "e1 = x1" "e2=x1" using A1 A2[THEN bspec,THEN bspec,of x1 x2]
                                     A3[THEN bspec,THEN bspec,of x1 x2] by auto
    thus "e1=e2" by simp
  next
     show "inhabited(object)" by auto
   qed


mdef xtuple_0_def_3 ("_ `2" [90] 95) where
 mlet "x be object"
  "assume x is pair func x `2 \<rightarrow> object means (\<lambda>it. for y1,y2 be object st x=[y1,y2] holds it = y2)"
proof -
  assume [ty]: "x is pair"
  obtain x1 x2 where
       [ty]:"x1 be object" "x2 be object" and A1: "x = [x1,x2]" using xtuple_0_def_1[of x] by infer_auto
    show "ex it being object st for y1,y2 be object st x=[y1,y2] holds it = y2"
      proof(rule bexI[of _ x2],intro ballI impI)
        show "x2 be object" by simp
        fix y1 y2
        assume "y1 be object" "y2 be object" "x=[y1,y2]"
        thus "x2 = y2" using xtuple_0_th_1[of x1 x2 y1 y2] A1 by simp
      qed simp_all
  next
    assume [ty]: "x is pair"
     obtain x1 x2 where
       [ty]: "x1 be object" "x2 be object" and A1: "x = [x1,x2]" using xtuple_0_def_1[of x] by infer_auto
     fix e1 e2
     assume [ty]: "e1 be object"
                "e2 be object" and
    A2: "for y1,y2 be object st x=[y1,y2] holds e1 = y2" and
    A3: "for y1,y2 be object st x=[y1,y2] holds e2 = y2"
     have "e1 = x2" "e2=x2" using A1 A2[THEN bspec,THEN bspec,of x1 x2]
                                     A3[THEN bspec,THEN bspec,of x1 x2] by auto
    thus "e1=e2" by simp
  next
    show "inhabited(object)" by auto
qed

theorem xtuple_0_reduce:
  "[x,y]`1 =x" "[x,y]`2=y"
proof-
  have "[x,y] is pair" using xtuple_0_def_1 by auto
  thus "[x,y]`1 =x" "[x,y]`2=y" using xtuple_0_def_3 xtuple_0_def_2 by auto
qed

mtheorem xtuple_0_th_6:
 "[x,y] in X \<longrightarrow> x in union union X"
proof
  have B: "[x,y] be set" by infer_auto
  assume A1: "[x,y] in X"
  have A0: "{{x,y},{x}} =[x,y]" using tarski_def_5 by auto
  hence "{x} in [x,y]" using tarski_def_2[of "{x,y}" "{x}" "{x}"] by auto
  hence "ex Y being set st ({x} in Y \<and> Y in X)" using bexI[of _ "[x,y]"] using A1 B by auto
  hence A2: "{x} in union X" using tarski_def_4 ty by auto
  have "x in {x}" using tarski_def_2 tarski_def_1 by simp
  hence "ex Y being set st x in Y \<and> Y in (union X)" using A2 bexI[of _ "{x}"] by infer_auto
  thus "x in union union X" using tarski_def_4 by infer_auto
qed

mtheorem xtuple_0_th_7:
 "[x,y] in X \<longrightarrow> y in union union X"
proof
  have B: "[x,y] be set " using tarski_def_5[of y x] by infer_auto
  assume A1: "[x,y] in X"
  have A0: "{{x,y},{x}} =[x,y]" using tarski_def_5 by auto
  hence "{x,y} in [x,y]" using tarski_def_2[of "{x,y}" "{x}"] by infer_auto
  hence "ex Y being set st ({x,y} in Y \<and> Y in X)" using A1 B bexI[of _ "[x,y]"] by auto
  hence A2: "{x,y} in union X" using tarski_def_4 by infer_auto
  have "y in {x,y}" using tarski_def_2 by simp
  hence "ex Y being set st y in Y \<and> Y in (union X)" using A2 exI[of _ "{x,y}"] by infer_auto
  thus "y in union union X" using tarski_def_4 by infer_auto
qed


mdef xtuple_0_def_12 ("proj1 _" [95] 95) where
  mlet "X be set"
  "func proj1 X \<rightarrow> set means \<lambda>it. (\<forall>x.  x in it \<longleftrightarrow> (ex y st [x,y] in X))"
proof
  auto[1]
    let ?Q = "\<lambda>d1. ex y st [d1,y] in X"
    obtain Y where
    [ty]: "Y be set" and A1: "for x being object holds x in Y \<longleftrightarrow> x in union union X \<and> ?Q(x)"
      using xboole_0_sch_1[of "union union X" "?Q"] by infer_auto
    show "ex Y being set st \<forall>x.  x in Y \<longleftrightarrow> (ex y st [x,y] in X)"
      proof (intro bexI[of _ Y])
        show "Y be set" using A1 by infer_simp
        show "\<forall>x.  x in Y \<longleftrightarrow> (ex y st [x,y] in X)"
           proof (intro ballI,rule iffI2)
              fix x assume "x be object"
              show "x in Y \<longrightarrow> (ex y st [x,y] in X)" using A1 by auto
              show "(ex y st [x,y] in X) \<longrightarrow> x in Y"
                proof
                   assume "ex y st [x,y] in X"
                   then obtain y where
                     A2: "y be object" "[x,y] in X" by auto
                   hence "x in union union X" using xtuple_0_th_6 by infer_auto
                   thus "x in Y" using A1 A2 by auto
                qed
           qed simp_all
      qed simp_all
next
    fix X1 X2
    assume [ty]: "X1 be set" and [ty]:"X2 be set" and
       A3: "\<forall>x.  x in X1 \<longleftrightarrow> (ex y st [x,y] in X)" and
      A4: "\<forall>x.  x in X2 \<longleftrightarrow> (ex y st [x,y] in X)"
       {
      fix x
       assume "x be object"
        have "x in X1 \<longleftrightarrow> (ex y st [x,y] in X)" using A3 by simp
        hence "x in X1 \<longleftrightarrow> x in X2" using A4 by simp
       }
    thus "X1 = X2" by (intro tarski_th_2) infer_auto
  qed


mdef xtuple_0_def_13 ("proj2 _" [95] 95) where
   mlet "X be set"
   "func proj2 X \<rightarrow> set means \<lambda>it. (\<forall>x.  x in it \<longleftrightarrow> (ex y st [y,x] in X))"
proof
    auto[1]
     let ?Q = "\<lambda>d1. ex y st [y,d1] in X"
    obtain Y where
    A1: "Y be set \<and> (for x being object holds x in Y \<longleftrightarrow> x in union union X \<and> ?Q(x))"
      using xboole_0_sch_1[of "union union X" "?Q"] by infer_auto
    show "ex Y being set st \<forall>x.  x in Y \<longleftrightarrow> (ex y st [y,x] in X)"
      proof (intro bexI[of _ Y])
        show "Y be set" using A1 by simp
        show "\<forall>x.  x in Y \<longleftrightarrow> (ex y st [y,x] in X)"
           proof (intro ballI,rule iffI2)
              fix x assume "x be object"
              show "x in Y \<longrightarrow> (ex y st [y,x] in X)" using A1 by auto
              show "(ex y st [y,x] in X) \<longrightarrow> x in Y"
                proof
                   assume "ex y st [y,x] in X"
                   then obtain y where
                     A2: "y be object" "[y,x] in X" by auto
                   hence "x in union union X" using xtuple_0_th_7 by infer_auto
                   thus "x in Y" using A1 A2 by auto
                qed
           qed simp_all
      qed simp_all
    next
    fix X1 X2
    assume T0:"X1 be set" and T1:"X2 be set" and
       A3: "\<forall>x.  x in X1 \<longleftrightarrow> (ex y st [y,x] in X)" and
      A4: "\<forall>x.  x in X2 \<longleftrightarrow> (ex y st [y,x] in X)"
       {
      fix x
       assume "x be object"
        have "x in X1 \<longleftrightarrow> (ex y st [y,x] in X)" using A3 by simp
        hence "x in X1 \<longleftrightarrow> x in X2" using A4 by simp
       }
    thus "X1 = X2" using tarski_th_2 T0 T1 by auto
qed

mtheorem xtuple_0_th_8:
 "X \<subseteq> Y \<longrightarrow> proj1 X \<subseteq> proj1 Y" using tarski_def_3 xtuple_0_def_12 by infer_auto

mtheorem xtuple_0_th_9:
 "X \<subseteq> Y \<longrightarrow> proj2 X \<subseteq> proj2 Y" using tarski_def_3 xtuple_0_def_13 by infer_auto

mtheorem xtuple_th_23:
 "proj1 (X \<union> Y) = (proj1 X) \<union> (proj1 Y)"
proof(rule xboole_0_def_10I,infer_simp)
  show "proj1 (X \<union> Y) c= (proj1 X) \<union> (proj1 Y)"
  proof(standard,auto)
    fix x
    assume "x in proj1 (X\<union>Y)"
    then obtain y where
       "y be object" and A1:"[x,y] in X\<union>Y" using xtuple_0_def_12 by infer_auto
    have "x in proj1 X \<or> x in proj1 Y" using xboole_0_def_3 A1 xtuple_0_def_12 by infer_auto
    thus "x in (proj1 X) \<union> (proj1 Y)" using xboole_0_def_3 by infer_auto
  qed infer_auto
  show "(proj1 X) \<union> (proj1 Y) c= proj1 (X \<union> Y)"
  proof(standard,auto)
    fix x
    assume "x in (proj1 X) \<union> (proj1 Y)"
    hence A: "x in proj1 X \<or> x in proj1 Y" using xboole_0_def_3 by infer_auto
     have "X c= X\<union>Y \<and> Y c= X\<union>Y" using tarski_def_3 xboole_0_def_3 by infer_auto
     hence "proj1 X c= proj1 (X\<union>Y) \<and> proj1 Y c= proj1 (X\<union>Y)"
          using xtuple_0_th_8[of _ X] using xtuple_0_th_8[of _ Y] by infer_auto
     thus "x in proj1 (X \<union> Y)" using A tarski_def_3 by infer_auto
  qed infer_auto
qed infer_auto

  mtheorem xtuple_th_24:
 "proj2 (X \<union> Y) = (proj2 X) \<union> (proj2 Y)"
proof(rule xboole_0_def_10I,infer_simp)
  show "proj2 (X \<union> Y) c= (proj2 X) \<union> (proj2 Y)"
  proof(standard,auto)
    fix x
    assume "x in proj2 (X\<union>Y)"
    then obtain y where
       "y be object" and A1:"[y,x] in X\<union>Y" using xtuple_0_def_13 by infer_auto
    have "x in proj2 X \<or> x in proj2 Y" using xboole_0_def_3 A1 xtuple_0_def_13 by infer_auto
    thus "x in (proj2 X) \<union> (proj2 Y)" using xboole_0_def_3 by infer_auto
  qed infer_auto
  show "(proj2 X) \<union> (proj2 Y) c= proj2 (X \<union> Y)"
  proof(standard,auto)
    fix x
    assume "x in (proj2 X) \<union> (proj2 Y)"
    hence A: "x in proj2 X \<or> x in proj2 Y" using xboole_0_def_3 by infer_auto
     have "X c= X\<union>Y \<and> Y c= X\<union>Y" using tarski_def_3 xboole_0_def_3 by infer_auto
     hence "proj2 X c= proj2 (X\<union>Y) \<and> proj2 Y c= proj2 (X\<union>Y)" using xtuple_0_th_9 by infer_auto
     thus "x in proj2(X \<union> Y)" using A tarski_def_3 by infer_auto
  qed infer_auto
qed infer_auto

end
