theory relat_1
imports zfmisc_1 subset_1
begin

reserve A,X,X1,X2,Y,Y1,Y2 for set
reserve a,b,c,d,x,y,z for object

mdef relat_1_def_1 ("Relation'_like")where
  "attr Relation_like for set means (\<lambda>IT. \<forall>x. x in IT \<longrightarrow> (ex y, z st x = [y, z]))" .

mtheorem relat_1_cl_1:
  "cluster empty \<rightarrow> Relation_like for set" 
  using relat_1_def_1 xboole_0_def_1 by auto
    
mtheorem relat_1_cl_0:
  "cluster Relation_like for set"
proof(standard,standard)
  show "{} be Relation_like\<bar>set" by infer_auto
qed

abbreviation "Relation \<equiv> Relation_like\<bar> set"

reserve R,P for Relation

mtheorem relat_1_cl_5:
   mlet "P be Relation", "R be Relation"
  "cluster P \<union> R \<rightarrow> Relation_like"
proof
  have A0: "\<forall>x.  x in P \<longrightarrow> (ex y, z st x = [y, z])" using relat_1_def_1 by infer_auto
  have "\<forall>x.  x in R \<longrightarrow> (ex y, z st x = [y, z])" using relat_1_def_1 by infer_auto
  hence "\<forall>x.  x in P\<union>R \<longrightarrow> (ex y, z st x = [y, z])" using A0 xboole_0_def_3 by infer_auto
  thus "(P \<union> R) is Relation_like" using relat_1_def_1 by infer_auto
qed
  

mtheorem relat_1_cl_7:
   mlet "a be object", "b be object"
   "cluster {[a,b]} \<rightarrow> Relation_like"
proof
   show "{[a,b]} is Relation_like" using relat_1_def_1 tarski_def_1 by infer_auto
qed

abbreviation(input) relat_1_syn_1("dom _" [105] 105) where
  "dom R \<equiv> proj1 R"

abbreviation(input) relat_1_syn_2("rng _" [105] 105) where
  "rng R \<equiv> proj2 R"

mtheorem relat_1_th_3:
  "R = {[x,y]} \<longrightarrow> dom R = {x} \<and> rng R = {y}"
proof(intro impI, rule conjI)
  assume A1: "R = {[x,y]}"
  have "for z being object holds z in dom R \<longleftrightarrow> z in {x}"
  proof (rule ballI,rule iffI3)
     fix z
     assume "z be object"
     show "z in dom R \<longrightarrow> z in {x}"
       proof
         assume "z in dom R"
         then obtain b where
            [ty]: "b be object" and A2: "[z,b] in R" using xtuple_0_def_12 by infer_auto
          have "[z,b] = [x,y]" using A1 A2 tarski_def_1 by simp
          hence "z=x" using xtuple_0_th_1[of z b] by simp
          thus "z in {x}" using tarski_def_1 by simp
       qed
     assume "z in {x}"
     hence "z=x" using tarski_def_1 by simp
     hence "[z,y] in R" using A1 tarski_def_1 by simp
     thus "z in dom R" using xtuple_0_def_12 by infer_auto
  qed simp_all
  thus "dom R = {x}" using tarski_th_2 by infer_auto
  have "for z being object holds z in rng R \<longleftrightarrow> z in {y}"
  proof (rule ballI,rule iffI3)
     fix z
     assume [ty]: "z be object"
     show "z in rng R \<longrightarrow> z in {y}"
       proof
         assume "z in rng R"
         then obtain b where
            T1: "b be object" and A2: "[b,z] in R" using xtuple_0_def_13 by infer_auto
          have "[b,z] = [x,y]" using A1 A2 tarski_def_1 by simp
          hence "z=y" using xtuple_0_th_1[of b z] by simp
          thus "z in {y}" using tarski_def_1 by simp
       qed
     assume "z in {y}"
     hence "z=y" using tarski_def_1 by simp
     hence "[x,z] in R" using A1 tarski_def_1 by simp
     thus "z in rng R" using xtuple_0_def_13 by infer_auto
  qed simp_all
  thus "rng R = {y}" using tarski_th_2 by infer_auto
 qed

mtheorem relat_1_th_7:
  "R \<subseteq> [:dom R, rng R:]"
proof(standard,auto)
  fix r
  assume A1: "r in R"
  then obtain x1 x2 where
     T0: "x1 be object" "x2 be object" and A2: "r = [x1,x2]"
         using A1 relat_1_def_1E[of R] by infer_auto
  have "x1 in dom R" "x2 in rng R" using A1 A2 xtuple_0_def_12 xtuple_0_def_13 by infer_auto
  thus "r in [:proj1 R, proj2 R:]" using A2 zfmisc_1_th_87 by infer_simp
qed infer_auto

mdef relat_1_def_18 ("_-defined" [110] 110) where
  mlet "X be set"
  "attr X-defined for Relation means (\<lambda>R. dom R c= X)".

mdef relat_1_def_19 ("_-valued" [110] 110) where
  mlet "X be set"
  "attr X-valued for Relation means (\<lambda>R. rng R c= X)".

theorem relat_1_sch_1:
   "A be set \<Longrightarrow> B be set
       \<Longrightarrow> ex R being Relation st (for x,y holds
  [x,y] in R \<longleftrightarrow> (x in A \<and> y in B \<and> P (x,y) ))"
proof-
   assume [ty]:"A be set" "B be set"
   let ?Q = "\<lambda> it.  ex x,y st it=[x,y] \<and> P (x,y)"
   have T2: "[:A,B:] be set" by infer_auto
   obtain X where
     T1:"X be set" and
A1: "for p being object holds p in X \<longleftrightarrow> p in [:A , B:] \<and> ?Q(p)"
   using xboole_0_sch_1[OF T2, of ?Q] by auto
   show "ex R being Relation st (for x,y holds
           [x,y] in R \<longleftrightarrow> (x in A \<and> y in B \<and> P (x,y) ))"
   proof (intro bexI[of _ X] ballI)
       have "for p being object st p in X ex x,y st p=[x,y]"
      proof(intro ballI impI)
         fix p assume "p be object"
         assume "p in X"
        hence "ex x,y st p=[x,y] \<and> P (x,y)" using A1 by simp
        thus "ex x,y st p=[x,y]" by auto
      qed simp
      thus A2: "X be Relation" using T1 relat_1_def_1 by auto
      fix x y
      assume "x be object" "y be object"
      show "[x,y] in X \<longleftrightarrow> (x in A \<and> y in B \<and> P (x,y))"
          proof (intro iffI2)
             show "[x,y] in X \<longrightarrow> x in A \<and> y in B \<and> P (x, y)"
                proof
                   assume A3: "[x,y] in X"
                    then obtain xx yy where
                     "xx be object" "yy be object"
                   and A4: "[x,y]=[xx,yy]" and
                       A5: "P (xx,yy)" using A1 by auto
                   have A6: "[x,y] in [:A,B:]" using A1 A3 by auto
                   have "x=xx \<and> y=yy" using A4 xtuple_0_th_1a by auto
                   thus "x in A \<and> y in B \<and> P (x,y)"
                      using A5 A6 zfmisc_1_th_87 by infer_auto
                qed
             show "x in A \<and> y in B \<and> P (x,y)  \<longrightarrow> [x,y] in X"
               proof (intro impI, elim conjE)
                 assume
                   A7: "x in A" "y in B" and A8: "P(x,y)"
                 have "[x,y] in [:A,B:]" using A7 zfmisc_1_th_87 by infer_auto
                 thus "[x,y] in X" using A1 A8 by auto
               qed
   qed
   qed simp_all
qed

mtheorem relat_1_def_2:
  mlet "P be Relation", "R be Relation"
   "redefine pred P = R means for a,b being object holds [a,b] in P \<longleftrightarrow> [a,b] in R"
proof
  show "P = R \<longleftrightarrow> (for a,b being object holds ([a,b] in P \<longleftrightarrow> [a,b] in R))"
     proof (intro iffI2)
        show "P = R \<longrightarrow> (for a,b being object holds ([a,b] in P \<longleftrightarrow> [a,b] in R))" by auto
        show "(for a,b being object holds ([a,b] in P \<longleftrightarrow> [a,b] in R)) \<longrightarrow> P=R"
             proof
                assume A1: "for a,b being object holds ([a,b] in P \<longleftrightarrow> [a,b] in R)"
                have T2: "P be set" "R be set" by infer_auto
                show "P = R"
                  proof (unfold xboole_0_def_10[OF T2], intro conjI)
                      show "P c= R"
                      proof (standard,auto)
                            fix x
                            assume A2: "x in P"
                            hence "ex y,z being object st x = [y,z]" using relat_1_def_1 by infer_auto
                            thus "x in R" using A1 A2 by auto
                        qed infer_auto
                       show "R c= P"
                        proof (standard,auto)
                            fix x
                            assume A2: "x in R"
                            hence "ex y,z being object st x = [y,z]" using relat_1_def_1 by infer_auto
                            thus "x in P" using A1 A2 by auto
                        qed infer_auto
                qed
            qed
     qed
qed


mdef relat_1_def_7:: "Set \<Rightarrow> Set" ("_~" [190] 190) where
  mlet "R be Relation"
  "func R~ \<rightarrow> Relation means \<lambda>it.(for x being object,y being object holds ([x,y] in it \<longleftrightarrow> ([y,x] in R)))"
proof-
      let ?Z = "\<lambda> x y.([y,x] in R)"
      obtain P where
        [ty]: "P be Relation" and
        A2: "for x,y holds [x,y] in P \<longleftrightarrow> x in rng R \<and> y in dom R \<and> ?Z (x,y)"
         using relat_1_sch_1[of "rng R" "dom R" "?Z"] by infer_auto
      show "ex P being Relation st
            for x,y holds ([x,y] in P \<longleftrightarrow> ([y,x] in R))"
       proof (intro bexI[of _ "P"])
         show "for x,y holds ([x,y] in P \<longleftrightarrow> ([y,x] in R))"
             proof (rule ballI,rule ballI,rule iffI3)
                fix x y
                assume "x be object" "y be object"
                show "[x , y] in P \<longrightarrow> [y , x] in R" using A2 by auto
                assume A3: "[x , y] in R"
                hence "x in dom R" " y in rng R" using xtuple_0_def_12 xtuple_0_def_13 by infer_auto
                thus " [y , x] in P" using A3 A2 by simp
             qed simp_all
       qed infer_auto
next
       fix P1 P2
      assume [ty]:"P1 be Relation " " P2 be Relation" and
             A2: "for x,y holds [x,y] in P1 \<longleftrightarrow> [y,x] in R" and
             A3: "for x,y holds [x,y] in P2 \<longleftrightarrow> [y,x] in R"
      show "P1=P2"
          proof (rule relat_1_def_2I,infer_simp,infer_simp,intro ballI impI )
            fix x y
            assume "x be object" "y be object"
            have "[x,y] in P1 \<longleftrightarrow> [y,x]  in R" using A2 by auto
            thus "[x,y] in P1 \<longleftrightarrow> [x,y] in P2" using A3 by auto
          qed simp_all
qed simp_all


text_raw {*\DefineSnippet{relat_1_def_7_involutiveness}{*}
theorem relat_1_def_7_involutiveness:
    "involutiveness Relation relat_1_def_7"
text_raw {*}%EndSnippet*}
proof
  fix R
  assume [ty]: "R be Relation"
  show "(R~)~ = R"
  proof (intro relat_1_def_2I ballI )
    show T1: "(R~)~ be Relation" by infer_auto
            show "R be Relation" by infer_auto
            fix x y
            assume "x be object" "y be object"
            have "[x,y] in R~~ \<longleftrightarrow> [y,x]  in R~" using relat_1_def_7[of "R~" x y] by infer_auto
            thus "[x,y] in R~~ \<longleftrightarrow> [x,y] in R" using relat_1_def_7[of "R"  y x] by infer_auto
          qed simp_all
qed simp_all



mdef relat_1_def_9:: "Set \<Rightarrow> Set \<Rightarrow> Set" (infix "*" 180) where
  mlet "P be Relation", "R be Relation"
  "func P * R \<rightarrow> Relation means \<lambda>it.(for x being object,y being object holds ([x,y] in it \<longleftrightarrow> (
ex z st [x,z] in P \<and> [z,y] in R)))"
proof-
     let ?Z = "\<lambda> x y.(ex z st [x,z] in P \<and> [z,y] in R)"
      obtain PR where
        [ty]: "PR be Relation" and
        A2: "for x,y holds [x,y] in PR \<longleftrightarrow> x in dom P \<and> y in rng R \<and> ?Z (x,y)"
        using relat_1_sch_1[of "dom P" "rng R" "?Z"] by infer_auto
      show "ex PR being Relation st
            for x,y holds ([x,y] in PR \<longleftrightarrow> (ex z st [x,z] in P \<and> [z,y] in R))"
       proof (intro bexI[of _ "PR"])
         show "for x,y holds ([x,y] in PR \<longleftrightarrow> (ex z st [x,z] in P \<and> [z,y] in R))"
             proof (rule ballI,rule ballI,rule iffI3)
                fix x y
                assume "x be object" "y be object"
                show "[x , y] in PR \<longrightarrow> (ex z st [x,z] in P \<and> [z,y] in R)" using A2 by auto
                assume A3: "ex z st [x,z] in P \<and> [z,y] in R"
                then obtain z where
                   "z be object" "[x,z] in P" "[z,y] in R" by auto
                hence "x in dom P" " y in rng R" using xtuple_0_def_12 xtuple_0_def_13 by infer_auto
                thus " [x , y] in PR" using A3 A2 by simp
             qed simp_all
       qed infer_auto
next
      fix P1 P2
      assume [ty]:"P1 be Relation " " P2 be Relation" and
             A2: "for x,y holds [x,y] in P1 \<longleftrightarrow> (ex z st [x,z] in P \<and> [z,y] in R)" and
             A3: "for x,y holds [x,y] in P2 \<longleftrightarrow> (ex z st [x,z] in P \<and> [z,y] in R)"
      show "P1=P2"
          proof (intro relat_1_def_2I ballI impI)
            fix x y
            assume "x be object" "y be object"
            have "[x,y] in P1 \<longleftrightarrow> (ex z st [x,z] in P \<and> [z,y] in R)" using A2 by auto
            thus "[x,y] in P1 \<longleftrightarrow> [x,y] in P2" using A3 by auto
          qed infer_auto
qed simp

theorem relat_1_th_26:
  assumes [ty]:"P be Relation" "R be Relation"
  shows "rng (P*R) c= rng R"
proof(standard,auto)
  fix y assume "y in rng (P*R)"
  then obtain x where
     "x be object" "[x,y] in P*R" using xtuple_0_def_13[of "P*R"] by infer_auto
   then obtain z where
    "z be object" "[x,z] in P \<and> [z,y] in R" using relat_1_def_9 by infer_auto
  thus "y in rng R" using xtuple_0_def_13 by infer_auto
qed infer_auto


mdef relat_1_def_8 ("id _" [110] 110) where
mlet "X be set"
    "func id X \<rightarrow> Relation means \<lambda>it.(for x being object,y being object holds ([x,y] in it \<longleftrightarrow> (x in X \<and> x=y)))"
proof-
  let ?Z = "\<lambda> x y.(x = y)"
      obtain R where
        [ty]: "R be Relation" and
        A2: "for x,y holds [x,y] in R \<longleftrightarrow> x in X \<and> y in X \<and> ?Z (x,y)"
         using relat_1_sch_1[of "X" "X" "?Z"] by infer_auto
      show "ex R being Relation st
            for x,y holds ([x,y] in R \<longleftrightarrow> (x in X \<and> x=y))"
       proof (intro bexI[of _ "R"])
         show "for x,y holds ([x,y] in R \<longleftrightarrow> (x in X \<and> x=y))" using A2 by auto
       qed infer_auto
next
      fix P1 P2
      assume [ty]:"P1 be Relation " " P2 be Relation" and
             A2: "for x,y holds [x,y] in P1 \<longleftrightarrow> x in X \<and> x=y" and
             A3: "for x,y holds [x,y] in P2 \<longleftrightarrow> x in X \<and> x=y"
      show "P1=P2"
          proof (intro relat_1_def_2I ballI)
            fix x y
            assume "x be object" "y be object"
            have "[x,y] in P1 \<longleftrightarrow> x in X \<and> x=y" using A2 by auto
            thus "[x,y] in P1 \<longleftrightarrow> [x,y] in P2" using A3 by auto
          qed infer_auto
qed simp

setup {*
add_miz_ident @{const_name "Reduce"}   @{thm Reduce_property} []
    @{attributes [simplified, rule_format]}
*}

text_raw {*\DefineSnippet{reduce_id_dom}{*}
mtheorem relat_1_id_dom:
   mlet "X be set" 
   "reduce dom (id X) to X"
text_raw {*}%EndSnippet*}
proof
  show "dom (id X) = X"
  proof (intro xboole_0_def_10I conjI)
       show "proj1 (id X) is set" by infer_auto
       show "dom (id X) \<subseteq> X"
       proof (standard,auto)
            fix x
            assume "x in dom (id X)"
            then obtain y where
              "y be object" " [x,y] in (id X)" using xtuple_0_def_12 by infer_auto
            thus "x in X" using relat_1_def_8 by infer_auto
          qed infer_auto
       show "X \<subseteq> dom (id X)"
       proof (standard,auto)
             fix x
            assume "x in X"
            hence "[x,x] in id X" using relat_1_def_8 by infer_auto
            thus "x in dom(id X)" using xtuple_0_def_12 by infer_auto
          qed infer_auto
     qed infer_auto
 qed

text_raw {*\DefineSnippet{reduce_id_rng}{*}
mtheorem relat_1_id_rng:
  mlet "X be set" 
  "reduce rng (id X) to X"
text_raw {*}%EndSnippet*}
proof
 show "rng (id X) = X"
 proof (intro xboole_0_def_10I conjI)
            show "(proj2 id X) is set" by infer_auto
       show "rng (id X) \<subseteq> X"
       proof (standard,auto)
            fix x
            assume "x in rng (id X)"
            then obtain y where
              "y be object" " [y,x] in (id X)" using xtuple_0_def_13 by infer_auto
            thus "x in X" using relat_1_def_8 by infer_auto
          qed infer_auto
       show "X \<subseteq> rng (id X)"
       proof (standard,auto)
            fix x
            assume "x in X"
            hence "[x,x] in id X" using relat_1_def_8 by infer_auto
            thus "x in rng(id X)" using xtuple_0_def_13 by infer_auto
          qed infer_auto
     qed infer_auto
qed

mdef relat_1_def_11:: "Set \<Rightarrow> Set \<Rightarrow> Set" (infix "|" 190) where
mlet "R be Relation", "X be set"
     "func (R | X) \<rightarrow> Relation means \<lambda>it.(for x being object,y being object holds ([x,y] in it \<longleftrightarrow> (x in X \<and> [x,y] in R)))"
proof-
      let ?Z = "\<lambda> x y.(x in X \<and> [x,y] in R)"
      obtain S where
        [ty]: "S be Relation" and
        A2: "for x,y holds [x,y] in S \<longleftrightarrow> x in dom R \<and> y in rng R \<and> ?Z (x,y)"
         using relat_1_sch_1[of "dom R" "rng R" "?Z"] by infer_auto
       show "ex S being Relation st
            for x,y holds ([x,y] in S \<longleftrightarrow> (x in X \<and> [x,y] in R))"
       proof (intro bexI[of _ "S"])
         show "for x,y holds ([x,y] in S \<longleftrightarrow> (x in X \<and> [x,y] in R))"
           proof(intro ballI)
              fix x y
              have "[x , y] in R \<Longrightarrow> x in dom R" "[x,y] in R \<Longrightarrow> y in rng R" using xtuple_0_def_12 xtuple_0_def_13 by infer_auto
              hence "[x,y] in R \<and> x in X \<Longrightarrow> [x,y] in S" using A2 by auto
              thus "[x , y] in S \<longleftrightarrow> x in X \<and> [x , y] in R" using A2 by auto
           qed simp_all
       qed infer_auto
next
      fix P1 P2
      assume [ty]:"P1 be Relation " " P2 be Relation" and
             A2: "for x,y holds [x,y] in P1 \<longleftrightarrow> x in X \<and> [x,y] in R" and
             A3: "for x,y holds [x,y] in P2 \<longleftrightarrow> x in X \<and> [x,y] in R"
      show "P1=P2"
          proof (intro relat_1_def_2I ballI)
            fix x y
            assume "x be object" "y be object"
            have "[x,y] in P1 \<longleftrightarrow> x in X \<and> [x,y] in R" using A2 by auto
            thus "[x,y] in P1 \<longleftrightarrow> [x,y] in P2" using A3 by auto
          qed infer_auto
qed simp_all

abbreviation(input) relat_1_def_11_notation ("_ \<restriction> \<^bsub>_\<^esub>" [190,0] 190) where
  "R\<restriction>\<^bsub>X\<^esub> \<equiv> R|X"  
  
mtheorem relat_1_th_51:
  "x in dom(R|X) \<longleftrightarrow> x in X \<and> x in dom R"
proof(rule iffI3)
  show "x in dom(R|X) \<longrightarrow> x in X \<and> x in dom R"
  proof
    assume "x in dom(R|X)"
    then obtain y where "y be object" and
    A1: "[x,y] in R|X" using xtuple_0_def_12[of "(R|X)"] by infer_auto
    have "x in X" "[x,y] in R" using relat_1_def_11[of R X] A1 by infer_auto
    thus "x in X \<and> x in dom R" using xtuple_0_def_12 by infer_auto
  qed
  assume
A2: "x in X \<and> x in dom R"
  then obtain y where "y be object" and
A3: "[x,y] in R" using xtuple_0_def_12 by infer_auto
  hence "[x,y] in R|X" using A2 relat_1_def_11 by infer_auto
  thus "x in dom (R|X)" using xtuple_0_def_12 by infer_auto
qed


mtheorem relat_1_th_55:
  "dom(R|X) = dom R \<inter> X"
proof-
  have "for x being object holds x in dom(R|X) \<longleftrightarrow> x in dom R \<inter> X"
  proof(rule ballI)
    fix x
    have "x in dom(R|X) \<longleftrightarrow> x in dom R \<and> x in X" using relat_1_th_51 by infer_auto
    thus "x in dom(R|X) \<longleftrightarrow> x in dom R \<inter> X" using xboole_0_def_4 by infer_auto
  qed simp_all
  thus ?thesis using tarski_th_2 all_set by auto
qed

mtheorem relat_1_th_56:
  "X \<subseteq> dom R \<longrightarrow> dom (R|X) = X"
proof
   assume A1: "X \<subseteq> dom R"
   hence A2: "dom R \<inter> X \<subseteq> X" using xboole_0_def_4 tarski_def_3 by infer_auto
   have "X \<subseteq> dom R \<inter> X" using xboole_0_def_4[of "proj1 R" X] A1 tarski_def_3[of X "proj1 R"]
     by (intro tarski_def_3I) infer_auto
   hence "dom R \<inter> X = X" using xboole_0_def_10 A2 by infer_auto
   thus "dom (R|X) = X" using relat_1_th_55 by infer_simp
qed

mtheorem relat_1_th_68:
  "dom R c= X \<longrightarrow> R = R|X"
proof
  assume A1: "(dom R) \<subseteq> X"
  have " for x being object,y being object holds ([x,y] in R \<longleftrightarrow> (x in X \<and> [x,y] in R))"
  proof(rule ballI,rule ballI,rule iffI2,auto)
    fix x y
    assume "[x,y] in R"
    hence "x in dom R" using xtuple_0_def_12 by infer_auto
    thus "x in X" using A1 tarski_def_3 by infer_auto
  qed 
  thus "R=R|X" using relat_1_def_11_uniq by infer_auto
qed

mtheorem relat_1_th75:
 "X \<subseteq> Y \<longrightarrow> R|X \<subseteq> R|Y"
proof
  assume A0:"X \<subseteq> Y"
  show "R|X \<subseteq> R|Y"
  proof(standard,auto)
      fix x
    assume A2: "x in R|X"
    then obtain a b where
       A3:"a be object" "b be object" "x=[a,b]" using relat_1_def_1[of "R|X"] by infer_auto
    have "a in X \<and> [a,b] in R" using relat_1_def_11 A2 A3 by infer_auto
    hence "a in Y \<and> [a,b] in R" using A0 tarski_def_3E[of X Y] by infer_auto
    thus "x in R|Y" using relat_1_def_11 A2 A3 by infer_auto
  qed infer_auto
qed

mtheorem relat_1_cl_10:
  mlet "R be non empty\<bar>Relation"
  "cluster dom R \<rightarrow> non empty"
proof
  let ?E="the (Element-of R)"
  have [ty]:"?E is Element-of R" by auto
  have A2: "?E in R" using subset_1_def_1[of R "?E"]  by infer_auto
  hence "ex x1,x2 be object st ?E=[x1,x2]" using relat_1_def_1 by infer_auto
  then obtain x1 x2 where
     "x1 be object" "x2 be object" and A3: "?E = [x1,x2]" by infer_auto
  thus "(dom R) is non empty" using A2 xboole_0_def_1 xtuple_0_def_12 by infer_auto
qed


mtheorem relat_1_cl_11:
  mlet "R be non empty\<bar>Relation"
  "cluster rng R \<rightarrow> non empty"
proof
  let ?E="the (Element-of R)"
  have [ty]:"?E is Element-of R" by auto  
  have A2: "?E in R" using subset_1_def_1E[of R] by infer_auto
  hence "ex x1,x2 be object st ?E =[x1,x2]" using relat_1_def_1E by infer_auto
  then obtain x1 x2 where
     "x1 be object" "x2 be object" and A3: "?E = [x1,x2]" by auto
  thus "(rng R) is non empty" using A2 xtuple_0_def_13 xboole_0_def_1 by infer_auto
qed

mtheorem relat_1_th_41:
  "dom R = {} \<or> rng R = {} \<longrightarrow> R = {}"
proof
  assume "dom R={} \<or> rng R = {}"
  hence "(dom R) is empty \<or> (rng R) is empty" by infer_auto
  hence "R be empty" thm ty thm clus
    using relat_1_cl_10[of R] relat_1_cl_11[of R] by infer_auto
  thus "R={}" using empty1 by auto
qed

mtheorem relat_1_cl_20:
   mlet "X be empty \<bar> set"
   "cluster dom X \<rightarrow> empty" 
  using xboole_0_def_1 xtuple_0_def_12_uniq by mauto
  
mtheorem relat_1_cl_21:
   mlet "X be empty \<bar> set"
   "cluster rng X \<rightarrow> empty" 
 using xboole_0_def_1 xtuple_0_def_13_uniq by mauto
  
end
