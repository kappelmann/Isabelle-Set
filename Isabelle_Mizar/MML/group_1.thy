theory group_1
imports algstr_0
begin

text_raw {*\DefineSnippet{group1def1}{*}
mdef group_1_def_1 ("unital")where
  "attr unital for multMagma means (\<lambda>S.
     ex e being Element-of-struct S st
       for h being Element-of-struct S holds
         h \<otimes>\<^sub>S e = h \<and>  e \<otimes>\<^sub>S h = h)"..
text_raw {*}%EndSnippet*}

text_raw {*\DefineSnippet{group1def2}{*}
mdef group_1_def_2 ("Group-like")where
   "attr Group-like for multMagma means
      (\<lambda>S.
          (ex e being Element-of-struct S st
            for h being Element-of-struct S holds
              h \<otimes>\<^sub>S e = h \<and> e \<otimes>\<^sub>S h = h \<and>
              (ex g being Element-of-struct S st
                 h \<otimes>\<^sub>S g = e \<and> g \<otimes>\<^sub>S h = e ) ))"..
text_raw {*}%EndSnippet*}

text_raw {*\DefineSnippet{group1def3}{*}
mdef group_1_def_3 ("associative")where
   "attr associative for multMagma means
      (\<lambda> S.
            (for x,y,z being (Element-of-struct S) holds
                  x \<otimes>\<^sub>S y \<otimes>\<^sub>S z =  x \<otimes>\<^sub>S ( y \<otimes>\<^sub>S z)))"..
text_raw {*}%EndSnippet*}


mtheorem (*group_1_lm_1:*)
  "cluster Trivial-multMagma \<rightarrow> strict (multMagma) \<bar> Group-like \<bar> associative \<bar>  non empty-struct\<bar> multMagma"
proof
   let ?T ="Trivial-multMagma"
  have [ty]: "?T be multMagma" by mauto
  have T1: "the carrier of ?T={{}}"
    using aggr by (auto intro: the_selector_of_1)
  have [ty]:"?T is associative"
    proof(standard,auto)
      fix x y z assume T2[ty]: "x be Element-of-struct ?T"  "y be (Element-of-struct ?T)"  "z be (Element-of-struct ?T)"
          show "( x \<otimes>\<^sub>?T y )  \<otimes>\<^sub>?T z =  x \<otimes>\<^sub>?T ( y \<otimes>\<^sub>?T z)" by (intro struct_0_def_10E[THEN bspec,THEN bspec,of ?T]) mauto
    qed mauto
  have [ty]:"?T is Group-like"
      proof(intro group_1_def_2I bexI[of _ "{}"] ballI conjI)
        show [ty]:"{} be Element-of-struct ?T" "{} be Element-of-struct ?T" using T1 by mauto
        fix h assume [ty]:"h be Element-of-struct ?T"
        show "h \<otimes>\<^sub>?T {} = h" by (rule struct_0_def_10E[THEN bspec,THEN bspec,of ?T]) mauto
        show "{} \<otimes>\<^sub>?T h = h" by (rule struct_0_def_10E[THEN bspec,THEN bspec,of ?T]) mauto
        show "h \<otimes>\<^sub>?T {} = {}" by (rule struct_0_def_10E[THEN bspec,THEN bspec,of ?T]) mauto
        show "{} \<otimes>\<^sub>?T h = {}" by (rule struct_0_def_10E[THEN bspec,THEN bspec,of ?T]) mauto
      qed mauto
   thus "?T be strict (multMagma) \<bar> Group-like \<bar> associative \<bar>  non empty-struct \<bar> multMagma"
       using algstr_0_cl_28 by mty auto
qed

mtheorem group_1_cl_2:
  "cluster strict (multMagma) \<bar> Group-like \<bar> associative \<bar>  non empty-struct
           for multMagma"
proof(standard,standard)
   let ?T ="Trivial-multMagma"
   show "?T be strict (multMagma) \<bar> Group-like \<bar> associative \<bar>  non empty-struct \<bar> multMagma"
          by mty auto
qed

text_raw {*\DefineSnippet{group1cl1}{*}
mtheorem group_1_cl_1:
  "cluster Group-like \<rightarrow> unital for multMagma"
text_raw {*}%EndSnippet*}
proof(standard,standard,standard)
  fix G
  assume A1[ty]: "G be multMagma"
  assume A2[ty]: "G is Group-like"
  then obtain e where
    T1:"e be (Element-of-struct G)" and
    A3: "for h being Element-of-struct G holds
        h \<otimes>\<^sub>G e = h \<and> e \<otimes>\<^sub>G h = h \<and>
            (ex g being Element-of-struct G st
            h \<otimes>\<^sub>G g = e \<and> g \<otimes>\<^sub>G h = e )" using group_1_def_2E[of G] by mauto
  have "for h being Element-of-struct G holds h \<otimes>\<^sub>G e = h \<and> e \<otimes>\<^sub>G h = h" using A3 by mauto
  thus "G is unital" using group_1_def_1 T1 A1 by auto
qed mauto

text_raw {*\DefineSnippet{groupmode}{*}
abbreviation Group where
   "Group \<equiv> Group-like \<bar> associative \<bar> non empty-struct \<bar> multMagma"
text_raw {*}%EndSnippet*}

mtheorem 
  "cluster Group-like \<bar> associative \<bar> non empty-struct for  multMagma"
proof(standard,standard)
  show "(the (strict (multMagma) \<bar> Group-like \<bar> associative \<bar>  non empty-struct \<bar> multMagma)) is Group"
    using choice_ax[OF group_1_cl_2] by auto
qed

mdef GroupFixCarrier ("_-carrier-group") where
  mlet "C be set"
  "func C -carrier-group  \<rightarrow> set means
     (\<lambda>it. for x be object holds x in it iff x be strict(addMagma) \<bar> Group & the carrier of x = C ) "  
proof-
  let ?P = "\<lambda> x . x be Group" 
  let ?AM = "C -carrier addMagma"
  let ?Q = "\<lambda> y. y be strict(addMagma) \<bar> Group \<and> the' carrier(y) = C"
  obtain X where
   [ty]: "X be set" and
   A1: "for x be object holds x in X iff x in ?AM & ?P(x)" using xboole_0_sch_1[of ?AM ?P] by mty auto
  show "\<exists>X : set. \<forall>y : object. y in X \<longleftrightarrow> ?Q(y)" 
  proof(rule bexI[of _ X],rule ballI)
    fix y   
    show "y in X \<longleftrightarrow> ?Q(y)" using A1 AddMagmaFixCarrier by mty auto     
  qed mauto
    fix IT1 IT2 assume [ty]: "IT1 be set" "IT2 be set" 

  assume A1: "for x being object holds (x in IT1 \<longleftrightarrow> ?Q(x))"
     and A2: "for x being object holds (x in IT2 \<longleftrightarrow> ?Q(x))"
  {
      fix x
      assume T1:"x be object"
      have "x in IT1 \<longleftrightarrow> ?Q(x)" using A1 T1 by auto
      then have "x in IT1 \<longleftrightarrow> x in IT2" using A2 T1 by auto
  }
  thus "IT1 = IT2" by (intro tarski_th_2) auto
qed mauto

text_raw {*\DefineSnippet{group1def4}{*}

mdef group_1_def_4 ("1'.\<^sub>_" [1000] 99) where
  mlet "G be unital \<bar> multMagma"
   "func 1.\<^sub>G \<rightarrow> Element-of-struct G means \<lambda>it.
      for h being Element-of-struct G holds
         h \<otimes>\<^sub>G it = h \<and> it \<otimes>\<^sub>G h = h"
text_raw {*}%EndSnippet*}
proof -
  show "ex it being Element-of-struct G st
         for h being Element-of-struct G holds h \<otimes>\<^sub>G it = h \<and>  it \<otimes>\<^sub>G h = h" using group_1_def_1 by mauto
next
  fix e1 e2
  assume T0: "e1 be Element-of-struct G"
             "e2 be Element-of-struct G" and
  A2: "for h being Element-of-struct G holds h \<otimes>\<^sub>G e1 = h \<and> e1 \<otimes>\<^sub>G h = h" and
  A3: "for h being Element-of-struct G holds h \<otimes>\<^sub>G e2 = h \<and> e2 \<otimes>\<^sub>G h = h"
  have "e1 = e1 \<otimes>\<^sub>G e2" using T0 A3 by simp
  also have "\<dots> = e2" using T0 A2 by simp
  finally show "e1=e2" .
qed auto
reserve G for Group
reserve f,g,h for "Element-of-struct G"


text_raw {*\DefineSnippet{group1def5}{*}
mdef group_1_def_5 ("_\<^sup>-\<^sup>1\<^sub>_" [105, 105] 105) where
  "func h\<^sup>-\<^sup>1\<^sub>G \<rightarrow> Element-of-struct G means \<lambda>it.
      h \<otimes>\<^sub>G it = 1.\<^sub>G \<and> it \<otimes>\<^sub>G h = 1.\<^sub>G"
text_raw {*}%EndSnippet*}
proof-
  obtain e where
     [ty]:"e be Element-of-struct G" and
     A1:"for h being Element-of-struct G
           holds h \<otimes>\<^sub>G e = h \<and> e \<otimes>\<^sub>G h = h \<and>
         (ex g being Element-of-struct G st
           h \<otimes>\<^sub>G g = e \<and> g \<otimes>\<^sub>G h = e)"
       using group_1_def_2E by mby auto
     have "ex g being Element-of-struct G st
     h \<otimes>\<^sub>G g = e \<and> g \<otimes>\<^sub>G h = e" using A1 by auto
   then obtain g where
[ty]: "g be Element-of-struct G" and
A2: "h \<otimes>\<^sub>G g = e \<and> g \<otimes>\<^sub>G h = e"
     by auto
   have "e = 1.\<^sub>G" using A1 group_1_def_4[of G e] A2 by mauto
   thus "ex g being Element-of-struct G st
     h \<otimes>\<^sub>G g = 1.\<^sub>G \<and> g \<otimes>\<^sub>G h = 1.\<^sub>G" using A2 bexI by auto
 next
   fix x1 x2
   assume [ty]: "x1 be Element-of-struct G"
          "x2 be Element-of-struct G" and
        A3:"h \<otimes>\<^sub>G x1 = 1.\<^sub>G \<and> x1 \<otimes>\<^sub>G h = 1.\<^sub>G" and
        A4:"h \<otimes>\<^sub>G x2 = 1.\<^sub>G \<and> x2 \<otimes>\<^sub>G h = 1.\<^sub>G"
   have "x1 = 1.\<^sub>G \<otimes>\<^sub>G x1" using group_1_def_4 by simp
   also have "... = x2 \<otimes>\<^sub>G h \<otimes>\<^sub>G x1" using A4 by simp
   also have "... = x2 \<otimes>\<^sub>G (h \<otimes>\<^sub>G x1)" using group_1_def_3E by mauto
   also have "... = x2" using group_1_def_4 A3 by simp
   finally show "x1 = x2" by simp
 qed auto
text_raw {*}%EndSnippet*}

text_raw {*\DefineSnippet{group1def5involutiveness}{*}
mtheorem group_1_def_5_involutiveness:
  "(h\<^sup>-\<^sup>1\<^sub>G)\<^sup>-\<^sup>1\<^sub>G = h"
text_raw {*}%EndSnippet*}
proof-
  have "(h\<^sup>-\<^sup>1\<^sub>G)   \<otimes>\<^sub>G h = 1.\<^sub>G \<and>  h \<otimes>\<^sub>G (h\<^sup>-\<^sup>1\<^sub>G) = 1.\<^sub>G" using group_1_def_5 by auto
  thus "(h\<^sup>-\<^sup>1\<^sub>G)\<^sup>-\<^sup>1\<^sub>G = h" using group_1_def_5_uniq[of G "h\<^sup>-\<^sup>1\<^sub>G" h] by mty auto
qed

text_raw {*\DefineSnippet{group1th5}{*}
mtheorem group_1_th_5:
  "h \<otimes>\<^sub>G g = 1.\<^sub>G \<and> g \<otimes>\<^sub>G h = 1.\<^sub>G \<longrightarrow> g = h\<^sup>-\<^sup>1\<^sub>G"
text_raw {*}%EndSnippet*}
  using group_1_def_5_uniq[of G h g] by auto

mtheorem group_1_th_6:
 "h \<otimes>\<^sub>G g = h \<otimes>\<^sub>G f \<or> g \<otimes>\<^sub>G h = f \<otimes>\<^sub>G h \<longrightarrow> g = f"
proof
  assume A1: "h \<otimes>\<^sub>G g = h \<otimes>\<^sub>G f \<or> g \<otimes>\<^sub>G h = f \<otimes>\<^sub>G h "
  show "g = f"
    proof (rule disjE[OF A1])
       assume "h \<otimes>\<^sub>G g = h \<otimes>\<^sub>G f"
       hence "(h\<^sup>-\<^sup>1\<^sub>G)  \<otimes>\<^sub>G (h \<otimes>\<^sub>G g)  =  ((h\<^sup>-\<^sup>1\<^sub>G)  \<otimes>\<^sub>G h)  \<otimes>\<^sub>G f"
           using group_1_def_3E[of G] by mty simp
         hence "(h\<^sup>-\<^sup>1\<^sub>G)  \<otimes>\<^sub>G (h \<otimes>\<^sub>G g) = 1.\<^sub>G \<otimes>\<^sub>G f" using group_1_def_5 by auto
         hence "(h\<^sup>-\<^sup>1\<^sub>G)  \<otimes>\<^sub>G (h \<otimes>\<^sub>G g) = f" using group_1_def_4 by auto
         hence "((h\<^sup>-\<^sup>1\<^sub>G)  \<otimes>\<^sub>G h)  \<otimes>\<^sub>G g = f" using group_1_def_3E by mty simp
         hence "1.\<^sub>G \<otimes>\<^sub>G g = f" using group_1_def_5 by simp
       thus "g= f" using group_1_def_4 by simp
    next
       assume "g \<otimes>\<^sub>G h = f \<otimes>\<^sub>G h"
         hence "(g \<otimes>\<^sub>G h)  \<otimes>\<^sub>G h\<^sup>-\<^sup>1\<^sub>G = f \<otimes>\<^sub>G (h \<otimes>\<^sub>G h\<^sup>-\<^sup>1\<^sub>G)" using group_1_def_3E by mty simp
         hence "(g \<otimes>\<^sub>G h)  \<otimes>\<^sub>G h\<^sup>-\<^sup>1\<^sub>G = f \<otimes>\<^sub>G 1.\<^sub>G " using group_1_def_5 by simp
         hence "(g \<otimes>\<^sub>G h)  \<otimes>\<^sub>G h\<^sup>-\<^sup>1\<^sub>G = f " using group_1_def_4 group_1_cl_1 by simp
         hence "g \<otimes>\<^sub>G (h \<otimes>\<^sub>G h\<^sup>-\<^sup>1\<^sub>G) = f " using group_1_def_3E by mty simp
         hence "g \<otimes>\<^sub>G 1.\<^sub>G = f" using group_1_def_5 by simp
       thus "g= f" using group_1_def_4 by simp
   qed
qed

text_raw {*\DefineSnippet{group1th7}{*}
mtheorem group_1_th_7:
  "h \<otimes>\<^sub>G g = h \<or> g \<otimes>\<^sub>G h = h \<longrightarrow> g = 1.\<^sub>G"
text_raw {*}%EndSnippet*}
proof -
  have "h \<otimes>\<^sub>G 1.\<^sub>G = h \<and> 1.\<^sub>G \<otimes>\<^sub>G h = h" using group_1_def_4[of G] by mauto
  thus "h \<otimes>\<^sub>G g = h \<or> g \<otimes>\<^sub>G h = h \<longrightarrow> g = 1.\<^sub>G" using group_1_th_6[of G "1.\<^sub>G" g h] by mauto
  qed

text_raw {*\DefineSnippet{group1th8}{*}
mtheorem group_1_th_8:
  "(1.\<^sub>G) \<^sup>-\<^sup>1\<^sub>G = 1.\<^sub>G"
proof -
  have "(1.\<^sub>G) \<^sup>-\<^sup>1\<^sub>G \<otimes>\<^sub>G 1.\<^sub>G = 1.\<^sub>G" using group_1_def_5 by simp
  thus "(1.\<^sub>G) \<^sup>-\<^sup>1\<^sub>G = 1.\<^sub>G" using group_1_def_4 by simp
qed
text_raw {*}%EndSnippet*}

text_raw {*\DefineSnippet{group1th9}{*}
mtheorem group_1_th_9:
  "h \<^sup>-\<^sup>1\<^sub>G = g \<^sup>-\<^sup>1\<^sub>G \<longrightarrow> h = g"
proof
  assume "h\<^sup>-\<^sup>1\<^sub>G = g\<^sup>-\<^sup>1\<^sub>G"
  hence A1: "h \<otimes>\<^sub>G g \<^sup>-\<^sup>1\<^sub>G = 1.\<^sub>G" using group_1_def_5[of G h] by mauto
  have "g \<otimes>\<^sub>G g \<^sup>-\<^sup>1\<^sub>G = 1.\<^sub>G" using group_1_def_5 by simp
  thus "h = g" using A1 group_1_th_6[of G h g "g \<^sup>-\<^sup>1\<^sub>G"]  by mauto
qed
text_raw {*}%EndSnippet*}

text_raw {*\DefineSnippet{group1th10}{*}
mtheorem group_1_th_10:
   "h\<^sup>-\<^sup>1\<^sub>G = 1.\<^sub>G \<longrightarrow> h = 1.\<^sub>G"
proof-
  have "(1.\<^sub>G) \<^sup>-\<^sup>1\<^sub>G = 1.\<^sub>G" using group_1_th_8 by mauto
  thus ?thesis using group_1_th_9[of G "1.\<^sub>G"] by mauto
qed
text_raw {*}%EndSnippet*}

text_raw {*\DefineSnippet{group1th11}{*}
mtheorem group_1_th_11:
  "h \<otimes>\<^sub>G g = 1.\<^sub>G \<longrightarrow> h = g \<^sup>-\<^sup>1\<^sub>G \<and> g = h \<^sup>-\<^sup>1\<^sub>G"
proof
  assume A1: "h \<otimes>\<^sub>G g = 1.\<^sub>G"
  have "h \<otimes>\<^sub>G h \<^sup>-\<^sup>1\<^sub>G = 1.\<^sub>G" "g \<^sup>-\<^sup>1\<^sub>G \<otimes>\<^sub>G g = 1.\<^sub>G"
    using group_1_def_5 by auto
  thus "h = g \<^sup>-\<^sup>1\<^sub>G \<and> g = h \<^sup>-\<^sup>1\<^sub>G" using
    group_1_th_6[of G "h\<^sup>-\<^sup>1\<^sub>G" g h]
    group_1_th_6[of G h "g\<^sup>-\<^sup>1\<^sub>G" g] A1 by mauto
qed
text_raw {*}%EndSnippet*} 
  
mtheorem group_1_th_12:
  "h \<otimes>\<^sub>G f = g \<longleftrightarrow> f = (h\<^sup>-\<^sup>1\<^sub>G)   \<otimes>\<^sub>G g"
proof(rule iffI3)
  have "h \<otimes>\<^sub>G ((h \<^sup>-\<^sup>1\<^sub>G) \<otimes>\<^sub>G g) = (h \<otimes>\<^sub>G h \<^sup>-\<^sup>1\<^sub>G)  \<otimes>\<^sub>G g" using group_1_def_3E by mty auto
  also have "...= 1.\<^sub>G \<otimes>\<^sub>G g" using group_1_def_5 by simp
  also have "... =  g" using group_1_def_4 by auto
  finally show "h \<otimes>\<^sub>G f = g \<longrightarrow>  f = h\<^sup>-\<^sup>1\<^sub>G \<otimes>\<^sub>G g" using group_1_th_6[of G f "h \<^sup>-\<^sup>1\<^sub> G \<otimes>\<^sub>G g" h] by mauto
  assume "f = h\<^sup>-\<^sup>1\<^sub>G \<otimes>\<^sub>G g"
  hence "h \<otimes>\<^sub>G f = h \<otimes>\<^sub>G h\<^sup>-\<^sup>1\<^sub>G \<otimes>\<^sub>G g" using group_1_def_3E by mty auto
  also have "... = 1.\<^sub>G \<otimes>\<^sub>G g" using group_1_def_5 by simp
  also have "... = g" using group_1_def_4 by auto
  finally show "h \<otimes>\<^sub>G f = g" by simp
qed

text_raw {*\DefineSnippet{group1th16}{*}
reserve G for Group
reserve h,g for "Element-of-struct G"

mtheorem group_1_th_16:
  "(h \<otimes>\<^sub>G g)\<^sup>-\<^sup>1\<^sub>G = g\<^sup>-\<^sup>1\<^sub>G \<otimes>\<^sub>G h\<^sup>-\<^sup>1\<^sub>G"
proof-

  have "(g\<^sup>-\<^sup>1\<^sub>G \<otimes>\<^sub>G h \<^sup>-\<^sup>1\<^sub>G) \<otimes>\<^sub>G (h \<otimes>\<^sub>G g) 
                 = (g\<^sup>-\<^sup>1\<^sub>G \<otimes>\<^sub>G h\<^sup>-\<^sup>1\<^sub>G) \<otimes>\<^sub>G h \<otimes>\<^sub>G g"
    using group_1_def_3E[THEN bspec,THEN bspec,of _ _ h] by auto 
  also have "... = g\<^sup>-\<^sup>1\<^sub>G \<otimes>\<^sub>G (h\<^sup>-\<^sup>1\<^sub>G \<otimes>\<^sub>G h) \<otimes>\<^sub>G g" 
    using group_1_def_3E by mty auto
  also have "... = g \<^sup>-\<^sup>1\<^sub>G \<otimes>\<^sub>G 1.\<^sub>G \<otimes>\<^sub>G g" 
    using group_1_def_5 by mauto
  also have "... = (g \<^sup>-\<^sup>1\<^sub>G)  \<otimes>\<^sub>G g" 
    using group_1_def_4 by mauto
  also have "... = 1.\<^sub>G" 
    using group_1_def_5 by mauto
  finally show ?thesis
    using group_1_th_11[of _ "h \<otimes>\<^sub>G g",
    THEN conjunct1] by mauto
qed
text_raw {*}%EndSnippet*}


mdef group_1_def_12 ("commutative")where
   "attr commutative for multMagma means (\<lambda> S. (for x,y being Element-of-struct S holds
                                         x \<otimes>\<^sub>S y = y \<otimes>\<^sub>S x))"..
text_raw {*\DefineSnippet{group_1_cl}{*}
mtheorem group_1_cl:
  "cluster strict(multMagma) \<bar> commutative for Group"
text_raw {*}%EndSnippet*}
proof(standard,standard)
  let ?T ="Trivial-multMagma"
  have [ty]: "?T be multMagma" by mauto
  have "?T is commutative"
    proof(standard,auto)
      fix x y z assume T2[ty]: "x be Element-of-struct ?T"  "y be (Element-of-struct ?T)"
      show " x \<otimes>\<^sub>?T y =  y \<otimes>\<^sub>?T x" 
        using struct_0_def_10E[THEN bspec,THEN bspec,of ?T " x \<otimes>\<^sub>?T y ""  y \<otimes>\<^sub>?T x" ] 
        by mty auto
    qed
   thus "?T be strict(multMagma) \<bar> commutative \<bar> Group"
        by mty auto
qed

end

