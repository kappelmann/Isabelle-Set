theory mizar_fraenkel
imports "../MML/tarski_0"

begin

definition sethood_prop where "sethood_prop(M) \<equiv> \<exists>X: set. \<forall>x: M. x in X"

definition "sethoodOfTy(ty) \<equiv> Trueprop(sethood_prop(ty))"

abbreviation (input) SethoodOfTy_p ("cluster sethood of _" [0] 10)
  where "cluster sethood of ty \<equiv> sethoodOfTy(ty)"

lemma sethoodOfTyI[intro!]:
assumes "\<exists>cover: set. \<forall>it: ty. it in cover" and "inhabited(ty)"
shows "cluster sethood of ty" 
  using sethoodOfTy_def sethood_prop_def assms
  by auto

lemma sethoodOfTy_property: "cluster sethood of ty \<Longrightarrow> sethood_prop(ty)"
  unfolding sethoodOfTy_def by simp

setup \<open>add_miz_ident @{const_name "sethoodOfTy"} @{thm sethoodOfTy_property} [] []\<close>

theorem sethood:
  "inhabited(M) \<Longrightarrow> sethood_prop(M) \<longleftrightarrow> (\<exists>X: set. \<forall>x: object. x be M \<longleftrightarrow> x in X)"
proof (rule iffI3)
  assume *: "inhabited(M)"
  show "sethood_prop(M) \<longrightarrow> (\<exists>X: set. \<forall>x: object. x be M \<longleftrightarrow> x in X)"
  proof
    assume "sethood_prop(M)"
    then obtain X where [ty]: "X be set" and A1:"\<forall>x: M. x in X"
      using sethood_prop_def by auto
    let ?P = "\<lambda>x y. x = y \<and> x be M"
    have "\<forall>x, y, z: object. ?P(x,y) \<and> ?P(x,z) \<longrightarrow> y = z"
      by auto
    then obtain S where
      [ty]: "S be set" and "\<forall>x: object. x in S \<longleftrightarrow> (\<exists>y: object. y in X \<and> ?P(y,x))"
      using tarski_0_sch_1[of X ?P] by infer_auto
    hence "\<forall>x: object. x be M \<longleftrightarrow> x in S" using A1 * by auto
    thus "\<exists>S: set. \<forall>x: object. x is M \<longleftrightarrow> x in S" using bexI[of _ S] by infer_auto
  qed
  assume "\<exists>X: set. \<forall>x: object. x be M \<longleftrightarrow> x in X"
  thus "sethood_prop(M)" using sethood_prop_def * by auto
qed

abbreviation (input) setS :: "Set \<Rightarrow> Ty" ("set''")
  where "set' \<equiv> \<lambda>it. set"

definition Fraenkel1
  where "func Fraenkel1(F, D, P) \<rightarrow> set means \<lambda>it.
    \<forall>x: object. x in it \<longleftrightarrow> (\<exists>y: D. x = F(y) \<and> P(y))"

syntax
  "_Fraenkel1" :: "Set \<Rightarrow> vs \<Rightarrow> Ty \<Rightarrow> o \<Rightarrow> Set" ("{ _ where _ be _ : _ }")
translations
  "{ f where x be D : P }" \<rightharpoonup> "CONST mizar_fraenkel.Fraenkel1((\<lambda>x. f), D, (\<lambda>x. P))"
  "mizar_fraenkel.Fraenkel1((\<lambda>x. f), D, (\<lambda>y. P))" \<rightharpoonup> "{ (\<lambda>x. f)(y) where y be D : P }"

schematic_goal Fraenkel_A1s:
fixes F :: "Set \<Rightarrow> Set" and P :: "Set => o"
assumes [ex]: "inhabited(L)" "sethood_prop(L)"
shows "?X"
proof (rule func_means_property[OF Fraenkel1_def, of L F P])
  show "\<exists>X: set. \<forall>x: object. x in X \<longleftrightarrow> (\<exists>y: L. x = F(y) \<and> P(y))"
  proof -
    obtain C where [ty]: "C be set" and Prop: "\<forall>x:object. x be L \<longleftrightarrow> x in C"
      using sethood assms by auto
    let ?R1 = "\<lambda>x y. F(x) = y \<and> P(x)"
    have A1: "\<forall>x, y, z: object. ?R1(x, y) \<and> ?R1(x, z) \<longrightarrow> y = z"
      by simp
    obtain Sep where
      [ty]: "Sep be set" and A2: "\<forall>x: object. x in Sep \<longleftrightarrow> (\<exists>y: object. y in C \<and> ?R1(y, x))"
      using tarski_0_sch_1[OF _ A1] by inst_nopass_auto
    show ?thesis
      using Prop A2 by (intro bexI[of _ Sep]) infer_auto
  qed
  next fix IT1 IT2
  assume
    B1: "IT1 be set" "IT2 be set" and
    B2: "for x being object holds (x in IT1 \<longleftrightarrow> (ex y being L st (x = F (y) \<and> P (y))))" and
    B3: "for x being object holds (x in IT2 \<longleftrightarrow> (ex y being L st (x = F (y) \<and> P (y))))"
  {
    fix x assume "x be object"
    have "x in IT1 \<longleftrightarrow> (ex y being L st (x = F (y) \<and> P (y)))" using B2 by simp
    hence "x in IT1 \<longleftrightarrow> x in IT2" using B3 by simp
  }
  thus "IT1 = IT2" using B1 tarski_0_2 by auto
qed auto

schematic_goal Fraenkel_A1:
fixes P :: "Set \<Rightarrow> Set" and Q :: "Set => o"
assumes [ex]: "inhabited(L)" "sethood_prop(L)" shows "?X"
proof
  (induct rule: func_means_property[OF Fraenkel1_def, of L P Q, case_names existence uniqueness])
  case existence
    obtain X where SetH: "X be set" and Prop: " for x being object holds (x be L \<longleftrightarrow> x in X)"
      using sethood assms by auto
    let ?QQ = "\<lambda>x y. x=y \<and> Q(x)"
    have A1: "for x, y, z being object holds ?QQ(x, y) \<and> ?QQ(x, z) \<longrightarrow> y = z"
      by simp
    obtain XQ where
      A2: "XQ be set" and
      A3: "for x being object holds x in XQ iff (ex y being object st y in X \<and> ?QQ(y, x))"
        using tarski_0_sch_1[OF SetH A1] by auto
    let ?R = "\<lambda>x y. y = P(x)"
    have A4: "for x, y, z being object holds ?R(x, y) \<and> ?R(x, z) \<longrightarrow> y = z" by simp
    obtain IT where A5:
      "IT be set"
      "for x being object holds (x in IT iff (ex y being object st y in XQ \<and> ?R(y, x)))"
      using tarski_0_sch_1[OF A2 A4] by auto
    show "ex IT being set st (for x being object holds
      (x in IT \<longleftrightarrow> (ex y being L st (x = P(y) \<and> Q(y)))))"
    proof (intro bexI[of _ IT] ballI)
      show "IT be set" using A5 by simp
      fix x assume "x be object"
      show "x in IT \<longleftrightarrow> (ex y being L st (x = P(y) \<and> Q(y)))"
      proof (intro iffI2)
        show "x in IT \<longrightarrow> (ex y being L st (x = P (y)  \<and> Q (y) ))"
          proof
          assume "x in IT"
          then obtain y where A6: "y in XQ \<and> ?R(y, x)" using A5 by auto
          show "ex y being L st (x = P(y) \<and> Q(y))"
          proof (intro bexI[of _ "y"] conjI)
            show "x = P (y)" using A6 by simp
            obtain z where "z in X \<and> ?QQ(z, y)" using A3 A6 by auto
            thus "Q (y)" and "y be L" using Prop by auto
          qed simp
        qed
        show "(ex y being L st (x = P(y) \<and> Q(y))) \<longrightarrow> x in IT"
        proof
          assume "ex y being L st (x = P(y) \<and> Q(y))"
          then obtain y where
             A8: "y be L" and A9: "x = P (y)" and A10: "Q (y)" by auto
          have "y in X" using Prop A8 by auto
          hence "y in XQ" using A3 A10 by auto
          thus "x in IT" using A5 A9 by auto
        qed
      qed
    qed simp_all
  case uniqueness
  fix IT1 IT2 assume
    B1: "IT1 be set" "IT2 be set" and
    B2: "for x being object holds (x in IT1 \<longleftrightarrow> (ex y being L st (x = P(y) \<and> Q(y))))" and
    B3: "for x being object holds (x in IT2 \<longleftrightarrow> (ex y being L st (x = P(y) \<and> Q(y))))"
  {
    fix x assume "x be object"
    have "x in IT1 \<longleftrightarrow> (ex y being L st (x = P(y) \<and> Q(y)))" using B2 by simp
    hence "x in IT1 \<longleftrightarrow> x in IT2" using B3 by simp
  }
  thus "IT1 = IT2" using B1 tarski_0_2 by auto
qed simp

lemmas Fraenkel_A1_ex = Fraenkel_A1[THEN conjunct2, THEN conjunct2, THEN bspec, simplified, THEN iffD1]

lemma [clus]: "Fraenkel1(P, L, Q) be set"
  using tarski_0_1 by auto

theorem Fraenkel_A1_in:
  "sethood_prop(M) \<Longrightarrow> x be M \<Longrightarrow> Q(x) \<Longrightarrow> P(x) in {P(x) where x be M : Q(x)}"
proof -
  assume A:"sethood_prop(M)" "x be M" "Q(x)"
  hence I: "inhabited(M)" using inhabited_def[of M] by blast
  have "ex y be M st P(x) = P(y) \<and> Q(y)" using A I by auto
  thus "P(x) in {P(x) where x be M : Q(x)}" using Fraenkel_A1 A I by auto
qed

abbreviation the_set_of_all
  where "the_set_of_all(P, M) \<equiv> Fraenkel1(P, M, \<lambda>x. True)"

syntax
  "_SetOfAll" :: "Set \<Rightarrow> vs \<Rightarrow> Ty \<Rightarrow> Set" ("the set-of-all _ where _ be _")
translations
 "the set-of-all f where x be D" \<rightleftharpoons> "CONST mizar_fraenkel.the_set_of_all((\<lambda>x. f), D)"

theorem Set_of_All_ex:
  "\<lbrakk>inhabited(M); sethood_prop(M)\<rbrakk> \<Longrightarrow>
    x in the set-of-all P(x) where x be M \<Longrightarrow> ex y be M st x = P(y)"
  using Fraenkel_A1_ex by blast

theorem Set_of_All_in:
  "sethood_prop(M) \<Longrightarrow> x be M \<Longrightarrow> P(x) in the set-of-all P(x) where x be M"
  using Fraenkel_A1_in by auto

end
