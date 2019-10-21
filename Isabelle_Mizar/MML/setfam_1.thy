theory setfam_1
imports subset_1
begin


mdef setfam_1_def_1 ("meet _") where
  mlet "X be set"
  "func meet X \<rightarrow> set means \<lambda>it.
  for x being object holds x in it iff
     (\<forall>Y.  Y in X \<longrightarrow> x in Y) if X\<noteq>{} otherwise \<lambda>it. it = {}"
proof(simp)
     show "(X\<noteq>{} implies (ex it be set st
        (for x being object holds x in it iff
     (\<forall>Y.  Y in X \<longrightarrow> x in Y))))\<and>(\<not> X \<noteq> {} \<longrightarrow> (\<exists>x : set. x = {}))"
     proof(cases "X={}")
       case True
            thus ?thesis using bexI[of _ "{}"] by mauto
       next
         case A1:False
             let ?P = "\<lambda>x. for Z st Z in X holds x in Z"
             obtain Y where
             T0[ty]:"Y be set" and A2:"(for x being object holds x in Y \<longleftrightarrow> x in union X \<and> ?P(x))"
               using xboole_0_sch_1[of "union X" ?P] by mauto
             have "ex it be set st
               (for x being object holds x in it iff (\<forall>Y.  Y in X \<longrightarrow> x in Y))"
             proof(rule bexI[of _ Y])
               show "\<forall>x.  x in Y iff
                           (\<forall>Z.  Z in X \<longrightarrow> x in Z)"
               proof(standard,rule iffI3)
                 fix x
                 show "x in Y \<longrightarrow> (\<forall>Z : set. Z in X \<longrightarrow> x in Z)" using A2 by mauto
                     (*for x being object holds x in Y \<longleftrightarrow> x in union X \<and> ?P(x)*)
                 assume A3:"\<forall>Z : set. Z in X \<longrightarrow> x in Z"
                 let ?y = "the Element-of X"
                 have Y: "?y in X" using Element_of_rule2 A1 by mauto
                 hence "x in ?y" using A3 all_set by auto
                 hence "x in union X" using A1 tarski_def_4 Y all_set by mauto
                 thus "x in Y" using A2 A3 by auto
               qed mauto
             qed mauto
         thus ?thesis by auto
     qed
  next
   fix it1 it2 assume [ty]:"it1 is set" "it2 is set"
   have "(\<forall>xa : object. xa in it1 \<longleftrightarrow> (\<forall>Y : set. Y in X \<longrightarrow> xa in Y)) \<and> 
            (\<forall>x : object. x in it2 \<longleftrightarrow> (\<forall>Y : set. Y in X \<longrightarrow> x in Y)) \<longrightarrow>
            it1 = it2"
   proof
     assume A1:"(\<forall>xa : object. xa in it1 \<longleftrightarrow> (\<forall>Y : set. Y in X \<longrightarrow> xa in Y)) \<and> 
            (\<forall>x : object. x in it2 \<longleftrightarrow> (\<forall>Y : set. Y in X \<longrightarrow> x in Y))"
       {
         fix x
         assume Z1[ty]: "x be object"
         have "x in it1 \<longleftrightarrow> (\<forall>Y.  Y in X \<longrightarrow> x in Y)" using A1 by auto
         hence "x in it1 \<longleftrightarrow> x in it2" using A1 by auto
        }
       thus "it1 = it2" using tarski_th_2 by mauto
   qed
   
   thus "(X \<noteq> {} \<and>
            (\<forall>xa : object. xa in it1 \<longleftrightarrow> (\<forall>Y : set. Y in X \<longrightarrow> xa in Y)) \<and> 
            (\<forall>x : object. x in it2 \<longleftrightarrow> (\<forall>Y : set. Y in X \<longrightarrow> x in Y)) \<longrightarrow>
            it1 = it2) \<and>
           (\<not> X \<noteq> {} \<and> it1 = {} \<and> it2 = {} \<longrightarrow> it1 = it2)" by auto
  qed mauto

mtheorem setfam_1_th_3:
  "Z in X \<longrightarrow> meet X \<subseteq> Z"
proof
  assume A1:"Z in X"
  hence A2: "X\<noteq>{}" using xb by auto
  show "meet X \<subseteq> Z"
  proof(standard,auto)
    fix x assume "x in meet X"
    thus "x in Z" using A1 A2 setfam_1_def_1 by mauto
  qed
qed

end