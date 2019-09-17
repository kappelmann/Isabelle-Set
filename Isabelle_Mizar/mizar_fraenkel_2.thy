theory mizar_fraenkel_2
imports mizar_fraenkel "MML/zfmisc_1"
begin  
  
    
text_raw {*\DefineSnippet{fraenkel_a2}{*}
definition Fraenkel2 where
   "func Fraenkel2 (P, L1, L2, Q) \<rightarrow> set means
      \<lambda> it. (for x being object holds (x in it \<longleftrightarrow> (ex y1 being L1, y2 being L2 st x = P(y1,y2) \<and> Q (y1,y2))))"
text_raw {*}%EndSnippet*}

syntax
  "_Fraenkel2" :: "Set \<Rightarrow> vs \<Rightarrow> Ty \<Rightarrow> vs \<Rightarrow> Ty \<Rightarrow> o \<Rightarrow> Set" ("{ _ where _ be _, _ be _ : _ }")
translations
 "{ f where x1 be D1, x2 be D2: P }" \<rightharpoonup> "CONST mizar_fraenkel_2.Fraenkel2((%x1 x2. f), D1, D2, (%x1 x2. P))"
  
  
term "{ {x, y} where x be set, y be set : x is empty }"

schematic_goal Fraenkel_A2:
  fixes P :: "Set \<Rightarrow> Set\<Rightarrow>Set" and Q :: "Set \<Rightarrow> Set \<Rightarrow> o"
  assumes [ex]:"inhabited(L1)" "inhabited(L2)" "sethood_prop(L1)" "sethood_prop(L2)" shows "?X"
proof (induct rule: func_means_property[OF Fraenkel2_def,of L1 L2 P Q, case_names existence uniqueness])
   case existence
      obtain X1 where
        SetH1[ty]: "X1 be set" and Prop1: "for x being object holds x be L1 \<longleftrightarrow> x in X1" using assms sethood by auto
      obtain X2 where
        SetH2[ty]: "X2 be set" and Prop2: "for x being object holds x be L2 \<longleftrightarrow> x in X2" using assms sethood by auto
      let ?QQ = "\<lambda>x y. (x=y \<and> (ex z1, z2 being object st y=[z1,z2] \<and> Q (z1,z2)))"
      have A1: "for x,y,z being object holds
          ?QQ (x,y) \<and> ?QQ (x,z) \<longrightarrow> y = z" by simp
      have T: "[:X1,X2:] be set" by mauto
      obtain XQ where
         A2:"XQ be set" and
         A3:"for x being object holds x in XQ iff
                 (ex y being object st y in [:X1,X2:] \<and> ?QQ (y,x))"
          using tarski_sch_1[OF T A1] by auto
      let ?R = "\<lambda>x. \<lambda> y. (ex z1, z2 being object st x=[z1,z2] \<and> y =P (z1,z2))"
      have A4: "for x,y,z being object holds
          ?R (x,y) \<and> ?R (x,z) \<longrightarrow> y = z"
         proof(intro ballI impI)
           fix x y z
           assume "x be object" "y be object" "z be object"
           assume A5:"?R (x,y) \<and> ?R (x,z)"
           then obtain y1 y2 where
               "y1 be object" "y2 be object" and A6: "x = [y1,y2] \<and> y = P (y1,y2)" by auto
           obtain z1 z2 where
               "z1 be object" "z2 be object" and A7: "x = [z1,z2] \<and> z = P(z1,z2)" using A5 by auto
           have "y1=z1 \<and> y2=z2" using A6 A7 xtuple_0_th_1[of y1 y2 z1 z2] by auto
           thus "y=z" using A6 A7 by simp
         qed simp_all
      obtain IT where
      [ty]:"IT be set" and A5: "for x being object holds (x in IT iff
         (ex y being object st y in XQ \<and> ?R (y,x)))"
            using tarski_sch_1[OF A2 A4] by auto
       show "ex IT being set st (for x being object holds (x in IT \<longleftrightarrow> (ex y1 being L1,y2 being L2 st (x = P (y1,y2)  \<and> Q(y1,y2)))))"
         proof (intro bexI[of _ "IT"] ballI)
            show "IT be set" using A5 by ty_simp
            fix x
            assume "x be object"
            show "x in IT \<longleftrightarrow> (ex y1 being L1,y2 being L2 st x = P (y1,y2)  \<and> Q(y1,y2))"
              proof (intro iffI2)
                 show "x in IT \<longrightarrow> (ex y1 being L1,y2 being L2 st x = P(y1,y2)  \<and> Q(y1,y2))"
                    proof
                       assume "x in IT"
                       then obtain y where
                         "y be object" and A6: "y in XQ \<and> ?R(y,x)" using A5 by auto
                       obtain y1 y2 where
                         "y1 be object" "y2 be object" and A7: "y =[y1,y2] \<and> x = P(y1,y2)" using A6 by auto
                       obtain z where
                         "z be object" and A8: "z in [:X1,X2:] \<and> ?QQ(z,y)" using A3 A6 by auto
                       obtain z1 z2 where
                          "z1 be object" "z2 be object" and A9: "y = [z1,z2] \<and> Q(z1,z2)" using A8 by auto
                       have "y1=z1 \<and> y2=z2" using A7 A9 xtuple_0_th_1[of y1 y2 z1 z2] by auto
                       hence A10: "Q(y1,y2)" using A9 by simp
                       have "[y1,y2] in [:X1,X2:]" using A7 A8 by auto
                       hence "y1 in X1 \<and> y2 in X2 " using zfmisc_1_th_87 SetH1 SetH2 by auto
                       hence A11: "y1 be L1 \<and> y2 be L2" using Prop1 Prop2 by auto
                      thus "ex y1 being L1 st ex y2 being L2 st x = P (y1,y2)  \<and> Q(y1,y2)" using A10 A7 by auto
                    qed
                 show " (ex y1 being L1,y2 being L2 st x = P(y1,y2)  \<and> Q(y1,y2)) \<longrightarrow> x in IT"
                    proof
                      assume "ex y1 being L1,y2 being L2 st x = P(y1,y2)  \<and> Q(y1,y2)"
                      then obtain y1 y2 where
                         A11: "y1 be L1" "y2 be L2" and A12: "x = P(y1,y2) \<and> Q(y1,y2)" by auto
                      hence "y1 in X1 \<and> y2 in X2" using Prop1 Prop2 by auto
                      hence A13: "[y1,y2] in [:X1,X2:]" using zfmisc_1_def_2 by ty_auto
                      have "?QQ([y1,y2],[y1,y2])" using A12 by auto
                      hence A14:"[y1,y2] in XQ" using A3 A13 by simp
                      have "?R ([y1,y2],x)" using A12 by auto
                      thus "x in IT" using A5 A14 by auto
                    qed
              qed
         qed simp_all
case uniqueness
  fix IT1 IT2
    assume B1[ty]: "IT1 be set" "IT2 be set" and
      B2: "for x being object holds (x in IT1 \<longleftrightarrow> (ex y1 being L1,y2 being L2 st x = P(y1,y2)  \<and> Q(y1,y2)))" and
      B3: "for x being object holds (x in IT2 \<longleftrightarrow> (ex y1 being L1,y2 being L2 st x = P(y1,y2)  \<and> Q(y1,y2)))"
    {
        fix x
        assume "x be object"
        have "x in IT1 \<longleftrightarrow> (ex y1 being L1,y2 being L2 st x = P(y1,y2)  \<and> Q (y1,y2))" using B2 by simp
        hence "x in IT1 \<longleftrightarrow> x in IT2" using B3 by simp
    }
    thus "IT1=IT2" using B1 by (intro tarski_th_2) auto
qed simp_all

  lemma [clus]:  "Fraenkel2(P, L1,L2, Q)  be set" using all_set by auto



lemmas Fraenkel_A2_ex =  Fraenkel_A2[THEN conjunct2,THEN conjunct2,THEN bspec,simplified,THEN iffD1]

theorem Fraenkel_A2_in:
   "sethood_prop(M1) \<Longrightarrow> sethood_prop(M2) \<Longrightarrow> x1 be M1\<Longrightarrow> x2 be M2 \<Longrightarrow>
     Q(x1,x2) \<Longrightarrow> P(x1,x2) in { P(x1,x2) where x1 be M1, x2 be M2 : Q(x1,x2)}"
proof-
  assume A:"sethood_prop(M1)" "sethood_prop(M2)" "x1 be M1" "x2 be M2" "x1 be M1" "Q(x1,x2)"
  hence I:"inhabited(M1)" "inhabited(M2)" using inhabited_def by blast+
    have "ex y1 be M1, y2 be M2 st P(x1,x2) = P(y1,y2) \<and> Q(y1,y2)" using A I by auto
  thus "P(x1,x2) in {P(x1,x2) where x1 be M1, x2 be M2 : Q(x1,x2)}" using Fraenkel_A2 A I
     by simp
 qed

end
