theory mizar_fraenkel_3
imports mizar_fraenkel "../3_MML/zfmisc_1"
begin

no_notation Product_Type.Times (infixr "\<times>" 80)
hide_const Prod

definition ModeProd_prefix ("_ \<times> _" [101,102] 101)
  where "A \<times> B \<equiv> define_ty(object, \<lambda>_. True, \<lambda> x.  x is pair \<and> x`1 is A \<and> x`2 is B)"

lemma [simp]:"[x,y] is pair" using xtuple_0_def_1 by auto     
     
theorem ModeProd:
  "x is A\<times>B iff x is pair \<and> x`1 is A \<and> x`2 is B"
proof
  assume "x is A\<times>B"
  thus "x is pair \<and> x`1 is A \<and> x`2 is B" using define_ty_property[OF ModeProd_prefix_def,THEN conjunct1] by auto 
next
  assume "x is pair \<and> x`1 is A \<and> x`2 is B"
  thus "x is A\<times>B" using define_ty_property[OF ModeProd_prefix_def,THEN conjunct2] by auto  
qed  

theorem ModeProd1:
  "[x,y] is A\<times>B iff x is A \<and> y is B"
proof
  assume A1: "[x,y] is A\<times>B"
  hence "[x,y]`1=x" "[x,y]`2=y" using xtuple_0_reduce by auto  
  thus " x is A \<and> y is B" using  ModeProd A1 by auto 
next
  have A2: "[x,y]`1=x" "[x,y]`2=y" using xtuple_0_reduce by auto  
  assume "x is A \<and> y is B"    
  thus "[x,y] is A\<times>B" using A2 ModeProd by auto  
qed    
  
theorem ModeProdI:
  assumes "inhabited(A)" "inhabited(B)" 
  shows "inhabited(A\<times>B)"
proof
  have "(the A) is A" "(the B) is B" using assms by auto
  thus "[the A,the B] is A\<times>B" using ModeProd1 by auto  
qed
    
lemma pair: "x is pair \<Longrightarrow> [x`1,x`2] = x"
proof-
  assume "x is pair"
  then obtain y z where
    A1: "x=[y,z]" using xtuple_0_def_1 by auto
  hence "x`1 = y" "x`2 = z" using xtuple_0_reduce by auto
  thus "[x`1,x`2] = x" using A1 by auto     
qed   
  
theorem ModeProdS:  
   assumes "inhabited(A)" "inhabited(B)" 
           "sethood_prop(A)" "sethood_prop(B)"
   shows "sethood_prop(A\<times>B)"
unfolding sethood_prop_def
proof-
  obtain X1 where
    SetH1[ty]: "X1 be set" and Prop1: "for x being object holds x be A \<longleftrightarrow> x in X1" using assms sethood by auto
  obtain X2 where
        SetH2[ty]: "X2 be set" and Prop2: "for x being object holds x be B \<longleftrightarrow> x in X2" using assms sethood by auto
  show "ex IT be set st  (\<forall>x : A\<times>B. x in IT)"
  proof(rule bexI[of _  "[:X1,X2:]"],auto)
    show "inhabited(A \<times> B)" using ModeProdI assms by auto
    fix x  
    assume "x is A\<times>B"
    hence [ty]: "x`1 is A" "x`2 is B" "x is pair" using ModeProd by auto
    hence "[x`1,x`2] in [:X1,X2:]" using Prop1 Prop2 zfmisc_1_th_87 by mauto
    thus "x in [:X1,X2:]" using pair by mauto
  qed mauto
qed  

abbreviation 
  "Prod(P) \<equiv> \<lambda> x. P(x`1,x`2)"
  
lemma Ifft: "B\<longleftrightarrow>C \<Longrightarrow> A\<longleftrightarrow>B \<Longrightarrow> A\<longleftrightarrow>C" by simp    
  
theorem ModeProdR: 
  assumes "inhabited(L1)" "inhabited(L2)" 
  shows "(\<exists> x :L1\<times>L2 . Prod(P)(x))\<longleftrightarrow> (\<exists> x1:L1 . \<exists>x2:L2 . P(x1,x2))"
proof
  assume "\<exists> x :L1\<times>L2 . Prod(P)(x)"
  then obtain x where
    A1: "x is L1\<times>L2" and A2: "Prod(P)(x)" using ModeProdI assms by auto 
  thus "\<exists> x1:L1 . \<exists>x2:L2 . P(x1,x2)" using A2 assms ModeProd by auto    
next
  assume "\<exists> x1:L1 . \<exists>x2:L2 . P(x1,x2)"
  then obtain x1 x2 where
    A1:"x1 is L1" "x2 is L2" "P(x1,x2)" using assms by auto
  hence "[x1,x2] is L1\<times>L2" using ModeProd xtuple_0_reduce by auto
  thus   "\<exists> x :L1\<times>L2 . Prod(P)(x)" using pair A1 ModeProdI[OF assms] xtuple_0_reduce by auto
qed  

definition Fraenkel2 where
  "Fraenkel2(F,L1,L2,Q) \<equiv> Fraenkel1(Prod(F),L1\<times>L2,Prod(Q))"   

syntax
  "_Fraenkel2" :: "Set \<Rightarrow> vs \<Rightarrow> Ty \<Rightarrow> vs \<Rightarrow> Ty \<Rightarrow> o \<Rightarrow> Set" ("{ _ where _ be _, _ be _ : _ }")
translations
 "{ F where x1 be D1, x2 be D2 : Q }" \<rightharpoonup> "CONST Fraenkel2((%x1 x2. F), D1, D2, (%x1 x2. Q))"
 
definition Fraenkel3 where
  "Fraenkel3(F,L1,L2,L3,Q) \<equiv> Fraenkel1(Prod(Prod(F)),L1\<times>L2\<times>L3,Prod(Prod(Q)))"   

syntax
  "_Fraenkel3" :: "Set \<Rightarrow> vs \<Rightarrow> Ty \<Rightarrow> vs \<Rightarrow> Ty \<Rightarrow> vs \<Rightarrow> Ty \<Rightarrow> o \<Rightarrow> Set" 
        ("{ _ where _ be _, _ be _ , _ be _ : _ }")
translations
 "{ F where x1 be D1, x2 be D2,x3 be D3 : Q }" \<rightharpoonup> "CONST Fraenkel3((%x1 x2 x3. F), D1, D2, D3, (%x1 x2 x3. Q))"

definition Fraenkel4 where
  "Fraenkel4(F,L1,L2,L3,L4,Q) \<equiv> Fraenkel1(Prod(Prod(Prod(F))),L1\<times>L2\<times>L3\<times>L4,Prod(Prod(Prod(Q))))"   

syntax
  "_Fraenkel4" :: "Set \<Rightarrow> vs \<Rightarrow> Ty \<Rightarrow> vs \<Rightarrow> Ty \<Rightarrow> vs \<Rightarrow> Ty \<Rightarrow>vs \<Rightarrow> Ty \<Rightarrow> o \<Rightarrow> Set" 
        ("{ _ where _ be _, _ be _ , _ be _, _ be _ : _ }")
translations
 "{ F where x1 be D1, x2 be D2,x3 be D3,x4 be D4 : Q }" \<rightharpoonup> "CONST Fraenkel4((%x1 x2 x3 x4. F), D1, D2, D3,D4, (%x1 x2 x3 x4. Q))"
 
definition Fraenkel5 where
  "Fraenkel5(F,L1,L2,L3,L4,L5,Q) \<equiv> Fraenkel1(Prod(Prod(Prod(Prod(F)))),L1\<times>L2\<times>L3\<times>L4\<times>L5,Prod(Prod(Prod(Prod(Q)))))"   

syntax
  "_Fraenkel5" :: "Set \<Rightarrow> vs \<Rightarrow> Ty \<Rightarrow> vs \<Rightarrow> Ty \<Rightarrow> vs \<Rightarrow> Ty \<Rightarrow>vs \<Rightarrow> Ty \<Rightarrow>vs \<Rightarrow> Ty \<Rightarrow> o \<Rightarrow> Set" 
        ("{ _ where _ be _, _ be _ , _ be _,_ be _, _ be _ : _ }")
translations
 "{ F where x1 be D1, x2 be D2,x3 be D3,x4 be D4,x5 be D5 : Q }" \<rightharpoonup> 
    "CONST Fraenkel5((%x1 x2 x3 x4 x5. F),D1, D2, D3,D4,D5, (%x1 x2 x3 x4 x5. Q))"

definition Fraenkel6 where
  "Fraenkel6(F,L1,L2,L3,L4,L5,L6,Q) \<equiv> Fraenkel1(Prod(Prod(Prod(Prod(Prod(F))))),L1\<times>L2\<times>L3\<times>L4\<times>L5\<times>L6,Prod(Prod(Prod(Prod(Prod(Q))))))"   

syntax
  "_Fraenkel5" :: "Set \<Rightarrow> vs \<Rightarrow> Ty \<Rightarrow> vs \<Rightarrow> Ty \<Rightarrow> vs \<Rightarrow> Ty \<Rightarrow>vs \<Rightarrow> Ty \<Rightarrow>vs\<Rightarrow> Ty \<Rightarrow>vs \<Rightarrow> Ty \<Rightarrow> o \<Rightarrow> Set" 
        ("{ _ where _ be _, _ be _ , _ be _,_ be _, _ be _, _ be _ : _ }")
translations
 "{ F where x1 be D1, x2 be D2,x3 be D3,x4 be D4,x5 be D5, x6 be D6 : Q }" \<rightharpoonup> 
    "CONST Fraenkel6((%x1 x2 x3 x4 x5 x6. F),D1,D2,D3,D4,D5,D6, (%x1 x2 x3 x4 x5 x6. Q))"

  
theorem Fraenkel1:
 assumes "inhabited(L1)" "sethood_prop(L1)"  
  shows "x in Fraenkel1(P, L1, Q) \<longleftrightarrow> (\<exists>y1 : L1. x = P(y1) \<and> Q(y1))"
using Fraenkel_A1[OF assms] by auto

theorem Fraenkel2:
    assumes "inhabited(L1)" "inhabited(L2)" 
           "sethood_prop(L1)" "sethood_prop(L2)"
   shows "x in Fraenkel2(P, L1,L2, Q) \<longleftrightarrow> 
     (\<exists>y1 : L1.\<exists>y2 : L2. x = P(y1,y2) \<and> Q(y1,y2))"
unfolding Fraenkel2_def
by (rule Ifft[OF _  Fraenkel1],rule Ifft[OF _  ModeProdR],auto simp add: assms ModeProdS ModeProdI)           
 
lemmas Fraenkel_A2_ex =  Fraenkel2[THEN iffD1]
lemma [clus]: "Fraenkel2(F, L1,L2, Q)  be set" using tarski_0_1 by auto

theorem Fraenkel_A2_in:
   "sethood_prop(L1) \<Longrightarrow> x1 be L1 \<Longrightarrow> sethood_prop(L2) \<Longrightarrow> x2 be L2
       \<Longrightarrow> Q(x1,x2) \<Longrightarrow> P(x1,x2) in {P(y1,y2) where y1 be L1,y2 be L2 : Q(y1,y2)}"
proof-
  assume A:"sethood_prop(L1)" "x1 be L1" "sethood_prop(L2)" "x2 be L2"
       "Q(x1,x2)"
  hence "inhabited(L1)" "inhabited(L2)" using inhabited_def  by auto
  thus ?thesis  using  inhabited_def Fraenkel2 A
     by auto
 qed  
   
theorem Fraenkel3:
  assumes "inhabited(L1)" "inhabited(L2)" "inhabited(L3)" 
          "sethood_prop(L1)" "sethood_prop(L2)" "sethood_prop(L3)"
  shows "x in Fraenkel3(P, L1,L2,L3, Q) \<longleftrightarrow> 
     (\<exists>y1 : L1.\<exists>y2 : L2.\<exists>y3 : L3. x = P(y1,y2,y3) \<and> Q(y1,y2,y3))"
unfolding Fraenkel3_def
by (rule Ifft[OF _  Fraenkel2[unfolded Fraenkel2_def]],rule Ifft[OF _  ModeProdR],auto simp add: assms ModeProdS ModeProdI)           
lemmas Fraenkel_A3_ex =  Fraenkel3[THEN iffD1]
lemma [clus]: "Fraenkel3(F, L1,L2,L3, Q)  be set" using tarski_0_1 by auto

theorem Fraenkel_A3_in:
   "sethood_prop(L1) \<Longrightarrow> x1 be L1 \<Longrightarrow> sethood_prop(L2) \<Longrightarrow> x2 be L2
     \<Longrightarrow> sethood_prop(L3) \<Longrightarrow> x3 be L3
       \<Longrightarrow> Q(x1,x2,x3) \<Longrightarrow> P(x1,x2,x3) in {P(y1,y2,y3) where y1 be L1,y2 be L2,y3 be L3 : Q(y1,y2,y3)}"
proof-
  assume A:"sethood_prop(L1)" "x1 be L1" "sethood_prop(L2)" "x2 be L2"
       "sethood_prop(L3)" "x3 be L3"
       "Q(x1,x2,x3)"
  hence "inhabited(L1)" "inhabited(L2)" "inhabited(L3)" using inhabited_def  by auto
  thus ?thesis  using  inhabited_def Fraenkel3 A
     by auto
 qed  
   
theorem Fraenkel4:
  assumes "inhabited(L1)" "inhabited(L2)" "inhabited(L3)" "inhabited(L4)" 
          "sethood_prop(L1)" "sethood_prop(L2)" "sethood_prop(L3)" "sethood_prop(L4)"
  shows "x in Fraenkel4(P, L1,L2,L3,L4, Q) \<longleftrightarrow> 
     (\<exists>y1 : L1.\<exists>y2 : L2.\<exists>y3 : L3.\<exists>y4 : L4. x = P(y1,y2,y3,y4) \<and> Q(y1,y2,y3,y4))"
  unfolding Fraenkel4_def
by (rule Ifft[OF _  Fraenkel3[unfolded Fraenkel3_def]],rule Ifft[OF _  ModeProdR],auto simp add: assms ModeProdS ModeProdI)           
lemmas Fraenkel_A4_ex =  Fraenkel4[THEN iffD1]
lemma [clus]: "Fraenkel4(F, L1,L2,L3,L4, Q)  be set" using tarski_0_1 by auto

theorem Fraenkel_A4_in:
   "sethood_prop(L1) \<Longrightarrow> x1 be L1 \<Longrightarrow> sethood_prop(L2) \<Longrightarrow> x2 be L2
     \<Longrightarrow> sethood_prop(L3) \<Longrightarrow> x3 be L3 \<Longrightarrow> sethood_prop(L4) \<Longrightarrow> x4 be L4
       \<Longrightarrow> Q(x1,x2,x3,x4) \<Longrightarrow> P(x1,x2,x3,x4) in {P(y1,y2,y3,y4) where y1 be L1,y2 be L2,y3 be L3,y4 be L4  : Q(y1,y2,y3,y4)}"
proof-
  assume A:"sethood_prop(L1)" "x1 be L1" "sethood_prop(L2)" "x2 be L2"
       "sethood_prop(L3)" "x3 be L3"  "sethood_prop(L4)" "x4 be L4"
       "Q(x1,x2,x3,x4)"
  hence "inhabited(L1)" "inhabited(L2)" "inhabited(L3)"  "inhabited(L4)" using inhabited_def  by auto
  thus ?thesis  using Fraenkel4 A
     by auto
 qed  
   
theorem Fraenkel5:
  assumes "inhabited(L1)" "inhabited(L2)" "inhabited(L3)" "inhabited(L4)"  "inhabited(L5)" 
          "sethood_prop(L1)" "sethood_prop(L2)" "sethood_prop(L3)" "sethood_prop(L4)"  "sethood_prop(L5)" 
  shows "x in Fraenkel5(P, L1,L2,L3,L4,L5, Q) \<longleftrightarrow> 
     (\<exists>y1 : L1.\<exists>y2 : L2.\<exists>y3 : L3.\<exists>y4 : L4. \<exists>y5 : L5. x = P(y1,y2,y3,y4,y5) \<and> Q(y1,y2,y3,y4,y5))"
  unfolding Fraenkel5_def
by (rule Ifft[OF _  Fraenkel4[unfolded Fraenkel4_def]],rule Ifft[OF _  ModeProdR],auto simp add: assms ModeProdS ModeProdI)           
lemmas Fraenkel_A5_ex =  Fraenkel5[THEN iffD1]
lemma [clus]: "Fraenkel5(F, L1,L2,L3,L4,L5, Q)  be set" using tarski_0_1 by auto

theorem Fraenkel_A5_in:
   "sethood_prop(L1) \<Longrightarrow> x1 be L1 \<Longrightarrow> sethood_prop(L2) \<Longrightarrow> x2 be L2
     \<Longrightarrow> sethood_prop(L3) \<Longrightarrow> x3 be L3 \<Longrightarrow> sethood_prop(L4) \<Longrightarrow> x4 be L4
      \<Longrightarrow> sethood_prop(L5) \<Longrightarrow> x5 be L5
       \<Longrightarrow> Q(x1,x2,x3,x4,x5) \<Longrightarrow> P(x1,x2,x3,x4,x5) in {P(y1,y2,y3,y4,y5) where y1 be L1,y2 be L2,y3 be L3,y4 be L4,y5 be L5  :
              Q(y1,y2,y3,y4,y5)}"
proof-
  assume A:"sethood_prop(L1)" "x1 be L1" "sethood_prop(L2)" "x2 be L2"
       "sethood_prop(L3)" "x3 be L3"  "sethood_prop(L4)" "x4 be L4"
       "sethood_prop(L5)" "x5 be L5"
       "Q(x1,x2,x3,x4,x5)"
  hence B: "inhabited(L1)" "inhabited(L2)" "inhabited(L3)"  "inhabited(L4)" "inhabited(L5)" using inhabited_def  by auto
  hence " \<exists>y2: L2.  \<exists>y3 : L3. \<exists>y4 : L4. \<exists>y5 : L5. P(x1,x2,x3,x4,x5) = P(x1,y2,y3,y4,y5) \<and> Q(x1,y2,y3,y4,y5) "
    using A B by auto      
  thus ?thesis  using Fraenkel5 A B bexI by auto
 qed     

theorem Fraenkel6:
  assumes "inhabited(L1)" "inhabited(L2)" "inhabited(L3)" "inhabited(L4)"  "inhabited(L5)" "inhabited(L6)"
          "sethood_prop(L1)" "sethood_prop(L2)" "sethood_prop(L3)" "sethood_prop(L4)"  "sethood_prop(L5)" "sethood_prop(L6)"
  shows "x in Fraenkel6(P, L1,L2,L3,L4,L5,L6, Q) \<longleftrightarrow> 
     (\<exists>y1 : L1.\<exists>y2 : L2.\<exists>y3 : L3.\<exists>y4 : L4. \<exists>y5 : L5.\<exists>y6 : L6. x = P(y1,y2,y3,y4,y5,y6) \<and> Q(y1,y2,y3,y4,y5,y6))"
  unfolding Fraenkel6_def
by (rule Ifft[OF _  Fraenkel5[unfolded Fraenkel5_def]],rule Ifft[OF _  ModeProdR],auto simp add: assms ModeProdS ModeProdI)           
lemmas Fraenkel_A6_ex =  Fraenkel6[THEN iffD1]
lemma [clus]: "Fraenkel6(F, L1,L2,L3,L4,L5,L6, Q)  be set" using tarski_0_1 by auto

theorem Fraenkel_A6_in:
   "sethood_prop(L1) \<Longrightarrow> x1 be L1 \<Longrightarrow> sethood_prop(L2) \<Longrightarrow> x2 be L2
     \<Longrightarrow> sethood_prop(L3) \<Longrightarrow> x3 be L3 \<Longrightarrow> sethood_prop(L4) \<Longrightarrow> x4 be L4
      \<Longrightarrow> sethood_prop(L5) \<Longrightarrow> x5 be L5 \<Longrightarrow> sethood_prop(L6) \<Longrightarrow> x6 be L6
       \<Longrightarrow> Q(x1,x2,x3,x4,x5,x6) \<Longrightarrow> P(x1,x2,x3,x4,x5,x6) in {P(y1,y2,y3,y4,y5,y6) where y1 be L1,y2 be L2,y3 be L3,y4 be L4,y5 be L5,y6 be L6  :
              Q(y1,y2,y3,y4,y5,y6)}"
proof-
  assume A:"sethood_prop(L1)" "x1 be L1" "sethood_prop(L2)" "x2 be L2"
       "sethood_prop(L3)" "x3 be L3"  "sethood_prop(L4)" "x4 be L4"
       "sethood_prop(L5)" "x5 be L5" "sethood_prop(L6)" "x6 be L6"
       "Q(x1,x2,x3,x4,x5,x6)"
  hence B: "inhabited(L1)" "inhabited(L2)" "inhabited(L3)"  "inhabited(L4)" "inhabited(L5)" "inhabited(L6)" using inhabited_def  by auto
  hence " \<exists>y3 : L3. \<exists>y4 : L4. \<exists>y5 : L5.\<exists>y6 : L6. P(x1,x2,x3,x4,x5,x6) = P(x1,x2,y3,y4,y5,y6) \<and> Q(x1,x2,y3,y4,y5,y6)"
    using A B by auto      
 hence " \<exists>y2 : L2. \<exists>y3 : L3. \<exists>y4 : L4. \<exists>y5 : L5.\<exists>y6 : L6. P(x1,x2,x3,x4,x5,x6) = P(x1,y2,y3,y4,y5,y6) \<and> Q(x1,y2,y3,y4,y5,y6)"
    using A B bexI by auto      
  thus ?thesis  using Fraenkel6 A B bexI by auto
 qed     
   
  
end

    
