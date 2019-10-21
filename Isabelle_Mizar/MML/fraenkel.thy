theory fraenkel
imports funct_2 "../2_Mizar/mizar_fraenkel_2"
begin

theorem Fraenkel_sch_1:
  fixes A F
  assumes T0[ty]:"A be set" and
          T1:  "\<And> x. x be object \<Longrightarrow>  F(x) be object"
  assumes A1:"for v being Element-of A holds P(v) \<longrightarrow> Q(v)"
  shows
  "{F(v) where v be Element-of A : P(v) } \<subseteq>
   {F(u) where u be Element-of A : Q(u) }"
proof(intro tarski_def_3I,auto)
  show "{F(v) where v be Element-of A : P(v) } is set"
       "{F(u) where u be Element-of A : Q(u) } is set" by mauto
  fix x
  assume B1: "x in {F(v) where v be Element-of A : P(v) }"
  obtain v where
    T2:"v be Element-of A" and
    A2: "x = F(v)" and
    A3: "P(v)" using Fraenkel_A1_ex[OF _ _ B1] by auto
  have "Q(v)" using A1 A3 T2 by auto
  thus "x in {F(u) where u be Element-of A : Q(u) }"
     using Fraenkel_A1_in T2 A2 by auto
qed

theorem Fraenkel_sch_2:
  assumes T0[ty]:"A1 be set" "A2 be set" and
             "\<And> x1 x2.  x1 be object \<Longrightarrow> x2 be object \<Longrightarrow> F(x1,x2) be object"
  assumes A1:"for v1 being Element-of A1, v2 be Element-of A2 holds P(v1,v2) \<longrightarrow> Q(v1,v2)"
  shows
  "{F(v1,v2) where v1 be Element-of A1, v2 be Element-of A2 : P(v1,v2) } \<subseteq>
   {F(v1,v2) where v1 be Element-of A1, v2 be Element-of A2 : Q(v1,v2) }"
proof(intro tarski_def_3I,auto)
  fix x
  assume B1: "x in {F(v1,v2) where v1 be Element-of A1, v2 be Element-of A2 : P(v1,v2) }"
  obtain v1 v2 where
    T2:"v1 be Element-of A1" "v2 be Element-of A2" and
    A2: "x = F(v1,v2)" and
    A3: "P(v1,v2)" using Fraenkel_A2_ex[OF _ _ _ _ B1] by auto
  have "Q(v1,v2)" using A1 A3 T2 by auto
  thus "x in {F(v1,v2) where v1 be Element-of A1, v2 be Element-of A2 : Q(v1,v2) }"
     using Fraenkel_A2_in T2 A2 by auto
qed mauto

theorem Fraenkel_sch_3:
  assumes T0[ty]:"B be set" and
          TT:   "\<And> x. x be object \<Longrightarrow>  F(x) be object"
  assumes A1:"for v being Element-of B holds P(v) \<longleftrightarrow> Q(v)"
  shows
  "{F(v) where v be Element-of B : P(v) } =
   {F(u) where u be Element-of B : Q(u) }"
proof(unfold xboole_0_def_10[OF all_set all_set],rule conjI)
  let ?A = "{F(v) where v be Element-of B : P(v) }"
  let ?B = "{F(v) where v be Element-of B : Q(v) }"
  have A2: "for v being Element-of B holds P(v) \<longrightarrow> Q(v)" using A1 by auto
  show "?A \<subseteq> ?B" using Fraenkel_sch_1[of B F, OF T0 TT A2] by auto
  have A3: "for v being Element-of B holds Q(v) \<longrightarrow> P(v)" using A1 by auto
  show "?B \<subseteq> ?A" using Fraenkel_sch_1[OF T0 TT A3] by auto
qed

theorem Fraenkel_sch_4:
  assumes O1[ty]: "A be set" and O2[ty]: "B be set"
      and T0: "\<And> x1 x2.  x1 be object \<Longrightarrow> x2 be object \<Longrightarrow> F(x1,x2) be object"
  assumes A1:"for u being Element-of A, v be Element-of B holds P(u,v) \<longleftrightarrow> Q(u,v)"
  shows
  "{F(u1,v1) where u1 be Element-of A, v1 be Element-of B : P(u1,v1) } =
    {F(u2,v2) where u2 be Element-of A, v2 be Element-of B : Q(u2,v2) }"
proof(intro xboole_0_def_10I)
   let ?A = "{F(u1,v1) where u1 be Element-of A, v1 be Element-of B : P(u1,v1) }"
  let ?B = "{F(u2,v2) where u2 be Element-of A, v2 be Element-of B : Q(u2,v2) }"
  have A2: "for u being Element-of A, v be Element-of B holds P(u,v) \<longrightarrow> Q(u,v)" using A1 by auto
  show "?A \<subseteq> ?B" using Fraenkel_sch_2[OF O1 O2 T0 A2] by auto
  have A3: "for u being Element-of A, v be Element-of B holds Q(u,v) \<longrightarrow> P(u,v)" using A1 by auto
  show "?B \<subseteq> ?A" using Fraenkel_sch_2[OF _ _ T0 A3] by auto
qed mauto

theorem Fraenkel_sch_5:
  assumes [ty]:"B be set"
     and T0: "\<And> x . x be object \<Longrightarrow>  F(x) be object"
             "\<And> x . x be object \<Longrightarrow>  G(x) be object"
  assumes A1:"for v being Element-of B holds F(v) = G(v)"
  shows
  "{F(v1) where v1 be Element-of B : P(v1) } =
   {G(v2) where v2 be Element-of B : P(v2) }"
proof(intro xboole_0_def_10I)
  let ?X = "{F(v1) where v1 be Element-of B : P(v1) }"
  let ?Y = "{G(v2) where v2 be Element-of B : P(v2) }"
  show "?X \<subseteq> ?Y"
    proof(intro tarski_def_3I,auto)
      fix x
      assume B1: "x in ?X"
      obtain v1 where
       T1: "v1 be Element-of B" and
       A3: "x = F(v1)" and
       A4: "P(v1)" using Fraenkel_A1_ex[OF _ _ B1] by auto
      have "x = G(v1)" using A1 A3 T1 by auto
      thus "x in ?Y" using Fraenkel_A1_in A4 T1 by auto
    qed mauto
  show "?Y \<subseteq> ?X"
    proof(intro tarski_def_3I,auto)
      fix x
      assume B1: "x in ?Y"
      obtain v1 where
       T1: "v1 be Element-of B" and
       A3: "x = G(v1)" and
       A4: "P(v1)" using Fraenkel_A1_ex[OF _ _ B1] by auto
      have "x = F(v1)" using A1 A3 T1 by auto
      thus "x in ?X" using Fraenkel_A1_in A4 T1 by auto
   qed mauto
qed mauto

theorem Fraenkel_sch_6:
  assumes [ty]:"B be set"
      and T0:"\<And> x . x be object \<Longrightarrow>  F(x) be object"
             "\<And> x . x be object \<Longrightarrow>  G(x) be object"
  assumes A1:"for v being Element-of B st P(v) holds F(v) = G(v)"
  shows
  "{F(v1) where v1 be Element-of B : P(v1) } =
   {G(v2) where v2 be Element-of B : P(v2) }"
proof(intro xboole_0_def_10I)
  let ?X = "{F(v1) where v1 be Element-of B : P(v1) }"
  let ?Y = "{G(v2) where v2 be Element-of B : P(v2) }"
  show "?X \<subseteq> ?Y"
    proof(intro tarski_def_3I,auto)
      fix x
      assume B1: "x in ?X"
      obtain v1 where
       T1: "v1 be Element-of B" and
       A3: "x = F(v1)" and
       A4: "P(v1)" using Fraenkel_A1_ex[OF _ _ B1] by auto
      have "x = G(v1)" using A1 A3 A4 T1 by auto
      thus "x in ?Y" using Fraenkel_A1_in A4 T1 by auto
    qed mauto
  show "?Y \<subseteq> ?X"
    proof(intro tarski_def_3I,auto)
      fix x
      assume B1: "x in ?Y"
      obtain v1 where
       T1: "v1 be Element-of B" and
       A3: "x = G(v1)" and
       A4: "P(v1)" using Fraenkel_A1_ex[OF _ _ B1] by auto
      have "x = F(v1)" using A1 A3 A4 T1 by auto
      thus "x in ?X" using Fraenkel_A1_in A4 T1 by auto
   qed mauto
qed mauto

theorem Fraenkel_sch_7:
  assumes [ty]:"A be set" "B be set"
     and T0: "\<And> x1 x2 . x1 be object \<Longrightarrow>  x2 be object \<Longrightarrow> F(x1,x2) be object"
             "\<And> x1 x2 . x1 be object \<Longrightarrow>  x2 be object \<Longrightarrow> G(x1,x2) be object"
  assumes A1:"for u being Element-of A, v be Element-of B holds F(u,v) = G(u,v)"
  shows
  "{F(u1,v1) where u1 be Element-of A, v1 be Element-of B : P(u1,v1) } =
    {G(u2,v2) where u2 be Element-of A, v2 be Element-of B : P(u2,v2) }"
proof(intro xboole_0_def_10I)
  let ?X = "{F(u1,v1) where u1 be Element-of A, v1 be Element-of B : P(u1,v1) }"
  let ?Y = "{G(u2,v2) where u2 be Element-of A, v2 be Element-of B : P(u2,v2) }"
 show "?X \<subseteq> ?Y"
  proof(intro tarski_def_3I,auto)
      fix x
      assume B1: "x in ?X"
      obtain u1 v1 where
       T1: "u1 be Element-of A" "v1 be Element-of B" and
       A3: "x = F(u1,v1)" and
       A4: "P(u1,v1)" using Fraenkel_A2_ex[OF _ _ _ _ B1] by auto
     have "x = G(u1,v1)" using A1 A3 T1 by auto
     thus "x in ?Y" using A4 Fraenkel_A2_in T1 by auto
  qed mauto
  show "?Y \<subseteq> ?X"
  proof(intro tarski_def_3I,auto)
      fix x
      assume B1: "x in ?Y"
      obtain u1 v1 where
       T1: "u1 be Element-of A" "v1 be Element-of B" and
       A3: "x = G(u1,v1)" and
       A4: "P(u1,v1)" using Fraenkel_A2_ex[OF _ _ _ _ B1] by auto
     have "x = F(u1,v1)" using A1 A3 T1 by auto
     thus "x in ?X" using A4 Fraenkel_A2_in T1 by auto
  qed mauto
qed mauto

mtheorem Fraenkel_th_1:
  "for A,B being set, F,G being Function-of A,B holds
     for X being set st F|X = G|X holds
       for x being Element-of A st x in X holds F. x = G. x"
proof(intro ballI impI)
  fix A B F G X x
  assume T1[ty]:"A be set" "B be set"
  show "inhabited(Element-of A)" by auto
  show "inhabited(Function-of A , B)" "inhabited(Function-of A , B)" by auto
  assume [ty]:"F be Function-of A,B" "G be Function-of A,B" "X be set"
  hence [ty]: "F be Function" "G be Function" by mauto (* !?! CK !?!*) (* be z tego nie idzie dalej, w tle relset_1_cl_1*)
  assume A1:"F|X = G|X" "x be Element-of A"
  assume A2:"x in X"
  hence "F. x = (G|X).x" using A1 funct_1_th_49[of F X x]  by mauto
  also have "... =  G. x" using A2 funct_1_th_49[of G X x] by mauto
  finally show "F. x = G. x" by simp
qed simp_all

text_raw {*\DefineSnippet{fraenkelsch9}{*}
theorem Fraenkel_sch_9:
  assumes [ty]: "A be set" "B be set" "X be set"
          "f be Function-of A,B" "g be Function-of A,B" and
          "(f | X) = (g | X)" 
        "for u being Element-of A st u in X holds P(u) \<longleftrightarrow> Q(u)"
  shows "{ f. u where u be Element-of A : P(u) \<and> u in X } =
         { g. v where v be Element-of A : Q(v) \<and> v in X }"
text_raw {*}%EndSnippet*}
proof-
  let ?F = "\<lambda>x1. f. x1"
  let ?G = "\<lambda>x1. g. x1"
  let ?PP = "\<lambda>x1. P(x1) \<and> x1 in X"
  let ?QQ = "\<lambda>x1. Q(x1) \<and> x1 in X"
  let ?C = "{?G(v) where v be Element-of A : ?PP(v) }"
  have A3: "for v be Element-of A holds ?PP(v) \<longleftrightarrow> ?QQ(v)" using assms by auto
  have A4: "?C = { ?G(v) where v be Element-of A : ?QQ(v) }" using Fraenkel_sch_3[OF _ _ A3] by simp
  have A5: "for v being Element-of A st ?PP(v) holds ?F(v) = ?G(v)"
    using Fraenkel_th_1[of A B f g X] assms(6) by auto
  have "{ ?F(u) where u be Element-of A : ?PP(u) } = ?C" using Fraenkel_sch_6[OF _ _ _ A5] assms by simp
  thus ?thesis using A4 by simp
qed

theorem Fraenkel_sch_8:
  assumes [ty]:"A be set" "B be set"
       and T0: "\<And> x1 x2 . x1 be object \<Longrightarrow>  x2 be object \<Longrightarrow> F(x1,x2) be object"
  assumes A1:"for u being Element-of A, v be Element-of B holds P(u,v) \<longleftrightarrow> Q(u,v)"
    and A2:"for u being Element-of A, v be Element-of B holds F(u,v) = F(v,u)"
  shows
  "{F(u1,v1) where u1 be Element-of A, v1 be Element-of B : P(u1,v1) } =
    {F(v2,u2) where u2 be Element-of A, v2 be Element-of B : Q(u2,v2) }"
proof-
  have A3: "for u being Element-of A, v being Element-of B holds Q(u,v) \<longrightarrow> P(u,v)" using A1 by simp
  have A4: "{ F(u1,v1) where u1 be Element-of A, v1 be Element-of B : Q(u1,v1)} \<subseteq>
            { F(u2,v2) where u2 be Element-of A, v2 be Element-of B : P(u2,v2)}" using Fraenkel_sch_2[OF _ _ T0 A3] by auto
  let ?H = "\<lambda>d1 d2. F(d2,d1)"
  have A5: "for u being Element-of A, v being Element-of B holds P(u,v) \<longrightarrow> Q(u,v)" using A1 by simp
  have A6: "{F(u1,v1) where u1 be Element-of A, v1 be Element-of B : P(u1,v1)} \<subseteq>
            {F(u2,v2) where u2 be Element-of A, v2 be Element-of B : Q(u2,v2)}"
          using Fraenkel_sch_2[OF _ _ T0 A5] by auto
  have A7: "for u be Element-of A, v being Element-of B holds F(u,v) = ?H(u,v)" using A2 by auto
  have A8: "{ F(u1,v1) where u1 be Element-of A, v1 be Element-of B : Q(u1,v1)} =
            {?H(u2,v2) where u2 be Element-of A, v2 be Element-of B : Q(u2,v2)}"
          using Fraenkel_sch_7[OF _ _ T0 T0 A7] by auto
  thus ?thesis using xboole_0_def_10[OF all_set all_set,THEN iffD2,rule_format,OF A4 A6] by simp
qed

theorem Fraenkel_sch_10:
  assumes T0[ty]: "A be non empty\<bar>set"
  shows "{x where x be Element-of A: P(x) } \<subseteq> A"
proof(intro tarski_def_3I,auto)
  fix x
  assume A0: "x in {x where x be Element-of A: P(x) }"
  obtain y where
    A1: "y be Element-of A" "x=y" "P(x)" using Fraenkel_A1_ex[OF _ _ A0] by auto
  show "x in A" using A1(1,2) T0 Element(7) by auto
qed mauto

theorem Fraenkel_sch_11:
  assumes [ty]: "A be set" "B be set"
      and T0: "\<And> x1 x2 . x1 be object \<Longrightarrow>  x2 be object \<Longrightarrow> F(x1,x2) be object"
  assumes A1: "for st1 being set st st1 in {F(s1,t1) where s1 be Element-of A, t1 be Element-of B:
                                            P(s1,t1) } holds Q(st1)"
  shows "for s being Element-of A, t being Element-of B st P(s,t) holds Q(F(s,t))"
proof(rule ballI, rule ballI, rule impI)
  fix s t
  assume [ty]: "s be Element-of A" "t be Element-of B"
  assume "P(s,t)"
  then have "F(s,t) in { F(s1,t1) where s1 be Element-of A,t1 be Element-of B:P(s1,t1)}" 
    using Fraenkel_A2_in by auto
  thus "Q(F(s,t))" using A1 all_set by simp
qed simp_all

theorem Fraenkel_sch_12:
  assumes [ty]: "A be set" "B be set"
      and T0:  "\<And> x1 x2 . x1 be object \<Longrightarrow>  x2 be object \<Longrightarrow> F(x1,x2) be object"
  assumes A1: "for s being Element-of A, t being Element-of B st P(s,t) holds Q(F(s,t))"

  shows "for st1 being set st st1 in { F(s1,t1) where s1 be Element-of A, t1 be Element-of B:
                                             P(s1,t1) } holds Q(st1)"
proof(rule ballI,rule impI)
  fix st1 assume "st1 be set"
  assume A2: "st1 in { F(s1,t1) where s1 be Element-of A, t1 be Element-of B:P(s1,t1) }"
  have "ex s1 be Element-of A,t1 be Element-of B st st1 = F(s1,t1) \<and> P(s1,t1)" using Fraenkel_A2_ex[OF _ _ _ _ A2] by auto
  thus "Q(st1)" using A1 by auto
qed simp_all

text_raw {*\DefineSnippet{fraenkelsch13}{*}
theorem fraenkel_sch_13:
  assumes [ty]: "A be set" "B be set" "C be set"
  and [ty_func]: "\<And> x1 x2 . x1 be object \<Longrightarrow>  x2 be object \<Longrightarrow> F(x1,x2) be Element-of C"
  shows "{ st1 where st1 be Element-of C:
             st1 in {F(s1,t1) where s1 be Element-of A,
               t1 be Element-of B: P(s1,t1) } \<and> Q(st1)} =
         { F(s2,t2) where s2 be Element-of A,t2 be Element-of B:
             P(s2,t2) \<and> Q(F(s2,t2))}"
text_raw {*}%EndSnippet*}
proof(unfold xboole_0_def_10[OF all_set all_set],rule conjI)
  let ?T = "{F(s1,t1) where s1 be Element-of A,t1 be Element-of B:P(s1,t1)}"
  let ?X = "{st1 where st1 be Element-of C: st1 in ?T \<and> Q(st1)}"
  let ?Y =  "{F(s2,t2) where s2 be Element-of A,t2 be Element-of B:
                                             P(s2,t2) \<and> Q(F(s2,t2))}"
  show "?X \<subseteq> ?Y"
  proof(intro tarski_def_3I,auto)
    fix x
    assume B1: "x in ?X"
    obtain st1 where
      A1: "st1 be Element-of C" "x = st1" and
      A2: "st1 in ?T" and
      A3: "Q(st1)" using Fraenkel_A1_ex[OF _ _ B1] by auto
    have "ex s1 be Element-of A,t1 be Element-of B st st1 = F(s1,t1) \<and> P(s1,t1)" using Fraenkel_A2_ex[OF _ _ _ _ A2] by auto
    thus "x in ?Y" using A1 A3 Fraenkel_A2_in by auto
   qed mauto
  show "?Y \<subseteq> ?X"
    proof(intro tarski_def_3I,auto)
      fix x
      assume B1: "x in ?Y"
      obtain s2 t2 where
       A4:"s2 be Element-of A" "t2 be Element-of B" "x=F(s2,t2)" and
       A5:"P(s2,t2)" and
       A6:"Q(F(s2,t2))" using Fraenkel_A2_ex[OF _ _ _ _ B1] by auto
      have T2:"F(s2,t2) be Element-of C" by mty auto
      have "F(s2,t2) in ?T" using A4 A5 Fraenkel_A2_in by auto
      thus "x in ?X" using T2 A6 A4 Fraenkel_A1_in[OF _  T2, of "\<lambda>st1. st1 in ?T \<and> Q(st1)"] by auto
    qed mauto
 qed mauto
end
