
theory funct_1
imports relset_1 "../2_Mizar/mizar_fraenkel"
begin

reserve x,y,z,x1,x2,y1,y2 for object
reserve X,Y,Z for set

mdef funct_1_def_1 ("Function'_like") where
  "attr Function_like for set means
     (\<lambda>IT. for x,y1,y2 being object st
          [x,y1] in IT \<and> [x,y2] in IT holds y1 = y2)" .
  
  
mtheorem funct_1_cl_1:
  "cluster empty \<rightarrow> Function_like for set" 
using xboole_0_def_1 funct_1_def_1 by mauto
print_theorems
mtheorem funct_1_cl_2:
  "cluster Function_like for Relation"
proof(standard,standard)
  show "{} be Function_like\<bar>Relation" by mauto
qed

mtheorem funct_1_cl_3:
  mlet "a be object","b be object"
  "cluster {[a,b]} \<rightarrow> Function_like"
proof
  let ?F = "{[a,b]}"
  have "for x,y1,y2 being object st [x,y1] in ?F \<and> [x,y2] in ?F holds y1 = y2"
     proof(intro ballI impI)
       fix x y1 y2
       assume "[x , y1] in ?F \<and> [x , y2] in ?F"
       hence "[x,y1] = [a,b]" "[x,y2] =[a,b]" using tarski_def_1 by auto
       thus "y1=y2" using xtuple_0_th_1[of x y1]  xtuple_0_th_1[of x y2] by auto
     qed simp_all
  thus "?F is Function_like" using funct_1_def_1I by mauto
qed


mtheorem funct_1_cl_4:
  mlet "X be set"
  "cluster id X \<rightarrow> Function_like"
proof
  show "(id X) is Function_like"
  proof (standard, auto)
       fix x y1 y2
       assume "[x,y1] in (id X)" "[x,y2] in (id X)"
       thus "y1=y2" using relat_1_def_8 by mauto
    qed mauto
qed

text_raw {*\DefineSnippet{Function}{*}
abbreviation
  "Function \<equiv> Function_like \<bar>Relation"
text_raw {*}%EndSnippet*}

mtheorem funct_1_cl:
  mlet "X be set"," F be Function"
  "cluster F | X \<rightarrow> Function_like"
proof
  have "for x,y1,y2 being object st [x,y1] in F|X \<and> [x,y2] in F|X holds y1 = y2"
  proof(intro ballI impI)
       fix x y1 y2
       assume T0: "x be object" "y1 be object " "y2 be object"
       assume "[x,y1] in F|X \<and> [x,y2] in F|X"
       hence A2: "[x,y1] in F \<and> [x,y2] in F" using relat_1_def_11[of F X] by mauto
       have A4: "for x,y1,y2 be object holds ([x,y1] in F \<and> [x,y2] in F \<longrightarrow> y1=y2)" using funct_1_def_1[of F] by mauto
       thus "y1=y2" using A2 by auto
  qed mauto
  thus "F | X is Function_like" using funct_1_def_1 by mauto
qed



  
mdef  funct_1_def_2 (infix "." 110) where
  mlet "f be Function", "x be object"
  "func f . x \<rightarrow> object means
     \<lambda>it. [x,it] in f if x in dom f otherwise \<lambda>it. it = {}"
proof
  show "(x in proj1 f \<longrightarrow> (\<exists>xa : object. [x , xa] in f)) \<and> (\<not> x in proj1 f \<longrightarrow> (\<exists>x : object. x = {}))"
  proof(intro conjI impI)
    assume "x in dom(f)"
      then obtain y where
A1:       "y be object \<and> [x,y] in f" using xtuple_0_def_12 by mauto
      thus "ex y being object st [x,y] in f" using A1 tarski_0_1 by auto
    next 
      show "(\<not> x in proj1 f \<Longrightarrow> (\<exists>x : object. x = {}))" by auto
    qed 
   show " \<And>xa y. xa is object \<Longrightarrow>
            y is object \<Longrightarrow>
            (x in dom f \<and> [x , xa] in f \<and> [x , y] in f \<longrightarrow> xa = y) \<and> (\<not> x in dom f \<and> xa = {} \<and> y = {} \<longrightarrow> xa = y)"
     using funct_1_def_1E[of f] by mauto  
 qed auto

reserve f,g for Function

mtheorem 
 mlet "x be object","f be Function"
  "cluster (f. x) \<rightarrow> set" 
   using  tarski_0_1 by auto
  
mtheorem funct_1_th_1: "[x,y] in f \<longleftrightarrow> x in dom f \<and> y = f . x"
proof(intro conjI iffI)
  assume A1: "[x,y] in f"
  thus A2: "x in dom f" using xtuple_0_def_12 by mauto
  hence "[x , f . x] in f" using A2 funct_1_def_2 by mauto
  thus "y = f . x" using A1 funct_1_def_1E by mauto
 next
  assume "x in dom f \<and> y = f . x"
  then show "[x , y] in f" using funct_1_def_2 by mauto
qed

mtheorem funct_1_th_2:
  "dom f = dom g & (for x st x in dom f holds f .x = g .x) implies f=g"
proof
  assume A1:"dom f=dom g & (for x st x in dom f holds f .x = g .x)"
  have "for a,b being object holds [a,b] in f \<longleftrightarrow> [a,b] in g" using  funct_1_th_1 A1 by mauto
  thus "f=g" using relat_1_def_2 by mauto
qed


mtheorem funct_1_th_18:
  mlet "X be set","x be object"
  "x in X \<longrightarrow> (id X).x = x"
proof
  assume "x in X"
  hence "[x,x] in id X" using relat_1_def_8 by mauto
  thus "(id X).x = x" using funct_1_th_1 by mauto
qed
  
 (*
syntax
  "COS" :: "vs \<Rightarrow> vs \<Rightarrow> Set" ("RNG _, _")
translations
 "RNG x,y " \<rightharpoonup> "proj1(x)"

theorem
  "RNG x,x = proj1(x)" by auto*)
term "redefine func rng f \<rightarrow> set means
     (\<lambda> it. for y being object holds y in it iff
        (ex x being object st x in dom f \<and> y = f . x))"
  
text_raw {*\DefineSnippet{redefine_func_rng}{*}
mtheorem funct_1_def_3:
  mlet "f be Function"
   "redefine func rng f \<rightarrow> set means
     (\<lambda> it. for y being object holds y in it iff
        (ex x being object st x in dom f \<and> y = f . x))"
text_raw {*}%EndSnippet*}
proof
  show "(rng f) be set" by mauto
  fix Y
  assume [ty]: "Y be set"
  show "Y = rng f \<longleftrightarrow> (for y being object holds y in Y iff
        (ex x being object st x in dom f \<and> y = f . x))"
        proof(rule iffI3)
          show "Y = rng f \<longrightarrow> (for y being object holds y in Y iff
            (ex x being object st x in dom f \<and> y = f . x))"
          proof
            assume A1: "Y = rng f"
            show "for y being object holds y in Y iff
              (ex x being object st x in dom f \<and> y = f . x)"
            proof (intro ballI impI)
              fix y
              assume [ty]: "y be object"
              show "y in Y iff
                (ex x being object st x in dom f \<and> y = f . x)"
              proof (intro iffI3)
                show "y in Y \<longrightarrow>
                     (ex x being object st x in dom f \<and> y = f . x)"
                 proof
                   assume "y in Y"
                   then obtain x where
                     [ty]: "x be object" and A2:"[x,y] in f" using A1 xtuple_0_def_13 by mauto
                   have "x in dom f \<and> y = f . x " using A2 funct_1_th_1[of "f" "y" "x"] by mauto
                   thus "ex x being object st x in dom f \<and> y = f . x" by auto
                 qed
                assume "ex x being object st x in dom f \<and> y = f . x"
                then obtain x where
                   "x be object" and A3:"x in dom f \<and> y = f . x" by auto
                have "[x,y] in f" using A3 funct_1_def_2 by mauto
                thus "y in Y" using A1 xtuple_0_def_13 by mauto
             qed
         qed simp
      qed
             assume A4: "for y being object holds y in Y iff
               (ex x being object st x in dom f \<and> y = f . x)"
             show "Y = rng f"
               proof (intro xboole_0_def_10I conjI)
                 show "Y \<subseteq> rng f"
                   proof (standard,auto)
                      fix y
                      assume "y in Y"
                      then obtain x where
                      T6: "x be object" and A5:"x in dom f \<and> y = f . x" using A4 by auto
                      have "[x,y] in f" using A5 funct_1_def_2 by mauto
                      thus "y in rng f" using xtuple_0_def_13 by mauto
                   qed mauto
                 show "rng f \<subseteq> Y"
              proof (standard,auto)
                fix y
                assume "y in rng f"
                then obtain x where
                   T9: "x be object" and A6: "[x,y] in f" using xtuple_0_def_13 by mauto
                hence "x in dom f \<and> y = f . x" using A6 funct_1_th_1[of f y x] by mauto
                thus "y in Y" using A4 by auto
              qed mauto
           qed mauto
          qed
  qed
    
    

theorem funct_1_sch_1:
  assumes [ty]: "X be set" and
         P1:"for x being object st x in X holds (ex y being object st P(x,y))" and
         P2:"for x,y1,y2 being object st x in X &  P(x,y1) & P(x,y2) holds y1 = y2"
  shows "ex f being Function st dom f=X &
        (for x being object st x in X holds P(x,f. x)) "     
proof-
  let ?Z = "\<lambda>x y. x in X & P(x,y)"  
  have P22:"for x,y1,y2 being object st ?Z(x,y1) & ?Z(x,y2) holds y1 = y2" using P2 by auto
  obtain Y where
        [ty]: "Y be set" and
        A1: "for y holds y in Y \<longleftrightarrow> (ex x st x in X & P(x,y))"
         using tarski_0_sch_1[of X ?Z,OF _ P22] by mauto
  obtain Q where
        T2[ty]: "Q be Relation" and
        A2: "for x,y holds [x,y] in Q \<longleftrightarrow> x in X \<and> y in Y \<and> ?Z (x,y)"
         using relat_1_sch_1[of X Y ?Z] by mauto
     have "for x,y1,y2 being object st [x,y1] in Q \<and> [x,y2] in Q holds y1 = y2"
     proof(intro ballI impI)
       fix x y1 y2
       assume "[x , y1] in Q \<and> [x , y2] in Q"
       hence "x in X & P(x,y1)" "P(x,y2)" using A2 by auto
       thus "y1=y2" using P2  by auto
     qed simp_all
     hence P[ty]: "Q is Function_like" using funct_1_def_1 all_set by simp
     show "ex f being Function st dom f=X & 
        (for x being object st x in X holds P(x,f. x))"
       proof (intro bexI[of _ Q] conjI)
         show D: "dom Q = X"
           proof (intro xboole_0_def_10I conjI)
       show "dom Q \<subseteq> X"
          proof (standard,auto)
            fix x
            assume "x in dom Q"
            then obtain y where
              "y be object" " [x,y] in Q" using xtuple_0_def_12 by mauto
            thus "x in X" using A2 by auto
          qed mauto
          show "X \<subseteq> dom Q"
           proof(standard,auto)
            fix x
            assume B: "x in X"
            then obtain y where
               B1: "P(x,y)" using P1 by auto
            hence "y in Y" using A1 B by auto
            hence "[x,y] in Q" using A2 B B1 by mauto
           thus "x in dom Q" using xtuple_0_def_12 by mauto
          qed mauto
        qed mauto
        show "for x st x in X holds P(x,Q. x)"
         proof (intro ballI impI)
            fix x
            assume B: "x in X"       
            hence "[x,Q. x] in Q" using D funct_1_def_2 by mauto  
            thus "P(x,Q. x)" using A2 by auto
         qed simp_all
    qed mauto
qed  
      
    
theorem funct_1_sch_Lambda:
  assumes [ty]:"A be set"
  shows "ex f be Function st dom f = A \<and> (for x st x in A holds f .x = P(x))"
 proof-
   let ?Z = "\<lambda> x y.(y = P(x))"
   show ?thesis using funct_1_sch_1[of A "\<lambda> x y.(y = P(x))"] by mauto
 qed 

mtheorem funct_1_th_5:
  "ex f be Function st dom f = X \<and> rng f c= {z}"
proof-
    let ?Z = "\<lambda> x y.(y=z)"
      obtain P where
        T2[ty]: "P be Relation" and
        A2: "for x,y holds [x,y] in P \<longleftrightarrow> x in X \<and> y in {z} \<and> ?Z (x,y)"
         using relat_1_sch_1[of X "{z}" "?Z"] by mauto
     have "P be Relation" using T2 by simp
     have "for x,y1,y2 being object st [x,y1] in P \<and> [x,y2] in P holds y1 = y2"
     proof(intro ballI impI)
       fix x y1 y2
       assume "[x , y1] in P \<and> [x , y2] in P"
       hence "y1=z" "y2=z" using A2 by auto
       thus "y1=y2" using xtuple_0_th_1[of x y1]  xtuple_0_th_1[of x y2] by auto
     qed simp_all
     hence P: "P is Function_like" using funct_1_def_1 all_set by simp
     show "ex f be Function st dom f = X \<and> rng f c= {z}"
       proof (intro bexI[of _ P] conjI)
         show "dom P = X"
           proof (intro xboole_0_def_10I conjI)
       show "dom P \<subseteq> X"
          proof (standard,auto)
            fix x
            assume "x in dom P"
            then obtain y where
              "y be object" " [x,y] in P" using xtuple_0_def_12 by mauto
            thus "x in X" using A2 by auto
          qed mauto
          show "X \<subseteq> dom P"
           proof(standard,auto)
            fix x
            assume "x in X"
            hence "[x,z] in P" using A2 tarski_def_1 by auto
            thus "x in dom P" using xtuple_0_def_12 by mauto
          qed mauto
        qed mauto
        show "rng P c= {z}"
         proof (standard,auto)
            fix y
            assume "y in rng P"
            then obtain x where
              "x be object" " [x,y] in P" using xtuple_0_def_13 by mauto
            thus "y in {z}" using A2 by auto
          qed mauto
        show "P be Function" using P by mauto
       qed simp
    qed

text_raw {*\DefineSnippet{product}{*}
abbreviation(input) funct_1_notation_1 ("_ *` _" [110,110] 110) where
  "f *` g \<equiv> g * f"
text_raw {*}%EndSnippet*}

abbreviation(input) funct_1_prod (infixl "\<circ>" 20) where
  "f \<circ> g \<equiv> f *` g"


text_raw {*\DefineSnippet{product_is_func}{*}
mtheorem
  mlet "f be Function","g be Function"
  "cluster  g \<circ> f \<rightarrow> Function_like"
text_raw {*}%EndSnippet*}
  proof
    have "for x,y1,y2 being object st [x,y1] in (g*`f) \<and> [x,y2] in (g*`f) holds y1 = y2"
     proof(intro ballI impI)
       fix x y1 y2
       assume A0: "[x , y1] in (g*`f) \<and> [x , y2] in (g*`f)"
       then obtain z1 where
          "z1 be object" and A1: "[x,z1] in f" "[z1,y1] in g" using relat_1_def_9[of f g]  by mauto
       obtain z2 where
          "z2 be object" and A2: "[x,z2] in f" "[z2,y2] in g" using relat_1_def_9[of f g] A0 by mauto
       have "z1=z2" using funct_1_def_1E[of f] A2 A1 by mauto
       thus "y1 = y2" using funct_1_def_1E[of g] A2 A1 by mauto
     qed simp_all
  thus "(g*`f) is Function_like" using funct_1_def_1 all_set by simp
qed

reserve f,g for Function

mtheorem funct_1_th_11:
  "x in dom(g \<circ> f) \<longleftrightarrow> x in dom f \<and> f. x in dom g"
proof(rule iffI3)
  let ?h = "g \<circ> f"
  show "x in dom ?h \<longrightarrow> x in dom f \<and> f. x in dom g"
    proof
      assume "x in dom ?h"
      then obtain y where [ty]: "y be object" and
       A1:"[x,y] in ?h" using xtuple_0_def_12 by mauto
      then obtain z where [ty]:"z be object" and
       A2: "[x,z] in f" and
       A3: "[z,y] in g" using relat_1_def_9[of f g] by mauto
      have "x in dom f" "f. x = z " using A2 xtuple_0_def_12 funct_1_def_2_uniq[of f x z]  by mauto
      thus "x in dom f \<and> f. x in dom g" using A3 xtuple_0_def_12 by mauto
    qed
  assume
A4: "x in dom f \<and> f. x in dom g"
  then obtain z where "z be object" and
A5: "[x,z] in f" using xtuple_0_def_12 by mauto
   obtain y where "y be object" and
A6: "[f. x,y] in g" using A4 xtuple_0_def_12 by mauto
   hence "[z,y] in g" using A4 A5 funct_1_def_2_uniq[of f] by mauto
   hence "[x,y] in g*`f" using relat_1_def_9[of f g] A5 by mauto
   thus "x in dom g*`f" using funct_1_th_1[of "g*`f",simplified] by mauto
qed

mtheorem funct_1_th_12:
  "x in dom(g*`f) \<longrightarrow> (g*`f).x = g.(f. x)"
proof
  let ?h = "g*`f"
  assume "x in dom ?h"
   then obtain y where
    "y be object" and A1: "[x,y] in ?h" using xtuple_0_def_12 by mauto
    then obtain z where
      T2:"z be object" and
      A2: "[x,z] in f" and
      A3: "[z,y] in g" using relat_1_def_9[of f g] by mauto
    have "x in dom f" "f. x = z " using A2 funct_1_th_1[of f z x] by mauto
    hence "g.( f. x) = y" "?h . x = y " using A3 A1 funct_1_th_1[of g] funct_1_th_1[of ?h] by mauto
    thus "(g*`f). x = g.(f. x)" by auto
qed

mtheorem funct_1_th_47:
  "x in dom(f|X) \<longrightarrow> (f|X).x = f. x"
proof
  assume
A1: "x in dom (f|X)"
  hence A2: "x in dom f" using relat_1_th_51 by mauto
  hence "[x,(f|X).x] in (f|X)" using funct_1_def_2 A1 by mauto
  hence "[x,(f|X).x] in f" "[x,f. x] in f" using relat_1_def_11[of f X] funct_1_def_2[of f x]
        A2 by mauto
  thus "(f|X).x = f. x"
    by (intro funct_1_def_1[THEN iffD1,THEN bspec,THEN bspec,THEN bspec,THEN mp]) inst_nopass_auto
qed

mtheorem funct_1_th_48:
  "x in dom f \<inter> X \<longrightarrow> (f|X). x = f. x"
proof
  assume "x in dom f \<inter> X"
  hence "x in dom(f|X)" using relat_1_th_55 by mauto
  thus "(f|X). x = f. x" using funct_1_th_47 by mauto
qed

text_raw {*\DefineSnippet{fraenkel_test}{*}
term "{f. x where x be Element-of dom f: x in X}"
text_raw {*}%EndSnippet*}

mtheorem
  "cluster non empty for Function"
proof(standard,standard)
  have "{[{},{}]} is non empty" using tarski_def_1 xboole_0_def_1 by mauto
  thus "{[{},{}]} be non empty\<bar>Function" by mauto
qed

mtheorem funct_1_th_test:
  "for f be non empty\<bar>Function holds
     rng (f|X) = { f. x where x be Element-of dom f: x in X}"
proof(intro ballI xboole_0_def_10I conjI)
  fix f assume A[ty]:"f be non empty\<bar>Function"
  show "{ f. x where x be Element-of dom f: x in X} be set" by mauto
  show "(rng (f|X)) be set" by mauto
  show "rng (f|X) \<subseteq> { f. x where x be Element-of dom f: x in X}"
  proof(standard,auto)
    fix y assume A1: "y in rng (f|X)"
    then obtain x where
      A2: "x be object" "x in dom (f|X) \<and> (f|X).x =y" using funct_1_def_3 by mauto
    have A3: "x in dom f" "x in X" using A2 relat_1_th_51 by mauto
    hence A4:"x be Element-of dom f" using Element(6) by mauto
    have "(f|X).x = f. x" using A2 funct_1_th_47 by mauto
    thus "y in { f. x where x be Element-of dom f: x in X}" using A2 Fraenkel_A1_in[of "Element-of dom f"] A3 A4 by mauto
  qed mauto
  show "{ f. x where x be Element-of dom f: x in X} \<subseteq> rng (f|X)"
  proof(standard,auto)
    fix y assume A1: "y in { f. x where x be Element-of dom f: x in X}"
    obtain x where
      A2[ty]: "x be Element-of dom f" and A22: "y = f. x \<and> x in X" using A1 Fraenkel_A1_ex[OF _ _  A1] by mauto
    have "(dom f) is non empty" by mauto
    have A3:"x in dom (f|X)" using Element(1)[of "proj1 f"] A2 A22 by (intro relat_1_th_51[THEN iffD2]) mauto
    have "x in (dom f) \<inter> X" using Element(1)[of "proj1 f"] A2 A22 xboole_0_def_4 by mauto
    hence "y = (f|X).x" using A22 funct_1_th_48 by mauto
    thus "y in rng (f|X)" using A3 funct_1_def_3 by mauto
  qed mauto
qed mauto

mtheorem funct_1_th_49:
  "x in X \<longrightarrow> (f|X).x = f. x"
proof
  have T0: "f|X be Function" using funct_1_cl relat_1_def_11[of f X] by mauto
  assume
A1: "x in X"
  show "(f|X).x = f. x"
  proof(cases "x in dom f")
    assume "x in dom f"
      hence "x in dom(f|X)" using A1 relat_1_th_55 xboole_0_def_4 by mauto
      thus ?thesis using funct_1_th_47 by mauto
    next
      assume A2: "not x in dom f"
      hence "not x in dom (f|X)" using relat_1_th_55 xboole_0_def_4 by mauto
      hence "(f|X).x = {}" using funct_1_def_2 by mauto
      also have "... = f. x" using funct_1_def_2 A2 by mauto
      finally show ?thesis by simp
  qed
qed

text_raw {*\DefineSnippet{funct_1_def_4}{*}
mdef funct_1_def_4 ("one-to-one")where
  "attr one-to-one for Function means (\<lambda>IT. for x1,x2 being object st x1 in dom IT \<and> x2 in dom IT holds x1 = x2)".
text_raw {*}%EndSnippet*}


text_raw {*\DefineSnippet{funct_1_contr_ex1}{*}
mtheorem
  "cluster one-to-one for set"
text_raw {*}%EndSnippet*}
proof(standard,standard)
  let ?L = "{[{},{}]}"
  have [ty]:"?L be non empty\<bar>Function" by mauto
  hence A1: "dom ?L = {{}}" using relat_1_th_3 by mauto
  have "?L is one-to-one"
  proof(standard,auto)
    fix x1 x2 assume "x1 in dom ?L" "x2 in dom ?L"
    hence "x1={}" "x2={}" using A1 tarski_def_1 by mauto
    thus "x1=x2" by simp
  qed mauto
  thus "{[{},{}]} be one-to-one\<bar>set" by mauto
qed


text_raw {*\DefineSnippet{funct_1_contr_ex2a}{*}
mtheorem [ex]: "inhabited(set\<bar>one-to-one)"
text_raw {*}%EndSnippet*}
  unfolding inhabited_def
proof
  let ?L = "{[{},{}]}"
  have [ty]:"?L be non empty\<bar>Function" by mauto
  hence A1: "dom ?L = {{}}" using relat_1_th_3 by mauto
  have "?L is one-to-one"
  proof(standard,auto)
    fix x1 x2 assume "x1 in dom ?L" "x2 in dom ?L"
    hence "x1={}" "x2={}" using A1 tarski_def_1 by mauto
    thus "x1=x2" by simp
  qed mauto
  thus "{[{},{}]} be set\<bar>one-to-one" by mauto
qed


text_raw {*\DefineSnippet{funct_1_contr_ex2b}{*}
theorem "\<forall>X : set\<bar>one-to-one. X is one-to-one\<bar>set"
text_raw {*}%EndSnippet*}
  by simp

mdef funct_1_def_13 ("functional")where
  "attr functional for set means (\<lambda>IT. for x be object st x in IT holds x be Function)".

mdef funct_1_def_14 ("_-compatible" [110] 110) where
  mlet "g be Function"
  "attr g -compatible for Function
    means (\<lambda>f. for x be object st x in dom f holds f .x in g .x) ".

mdef funct_1_def_9 ("non-empty")where
  "attr non-empty for Function means (\<lambda>f.  \<not> {} in rng f )".

text_raw {*\DefineSnippet{funct1th110}{*}
theorem funct_1_th_110:
  assumes [ty]:"B be non empty\<bar>functional\<bar>set"    "f be Function"
     and "f = union B"
  shows
     "dom f = union the set-of-all dom g where g be Element-of B"
     "rng f = union the set-of-all rng g where g be Element-of B"
  text_raw {*}%EndSnippet*}
proof -
  let ?D = "the set-of-all dom g where g be Element-of B"
  let ?R = "the set-of-all rng g where g be Element-of B"
  show "dom f = union ?D"
  proof(unfold xboole_0_def_10[OF all_set all_set],rule conjI)
    show "dom f \<subseteq> union ?D"
       proof(standard,auto)
         fix x
         assume "x in dom f"
         hence "[x,f. x] in f" using funct_1_th_1[of f "f. x" x] assms(2) by auto
         then obtain g where
           [ty]: "g be set" and A2: "[x, f. x] in g" "g in B" using assms(3) tarski_def_4 by mauto
         have T2: "g be Element-of B" using A2(2) Element(6) by mauto
         have [ty]:"g be Function" using A2(2) funct_1_def_13 assms(1) by mauto
         hence C1: "x in dom g" using A2 funct_1_th_1[of g "f. x" x] by auto
         have "dom g in ?D" using Set_of_All_in[OF _ T2] by mauto
         thus "x in union ?D" using tarski_def_4[of ?D x] C1 exI[of _ "proj1 g"] by inst_nopass_auto
       qed mauto
    show "union ?D \<subseteq> dom f"
       proof(standard,auto)
         fix x
         assume "x in union ?D"
         then obtain d where
           A4: "d be set" "x in d" "d in ?D" using tarski_def_4 by mauto
         obtain g where
           [ty]: "g be Element-of B" and A6: "d = dom g" using Set_of_All_ex[OF _ _ A4(3)] by mauto
         have T3: "g in B" using assms(1) Element(1)[THEN iffD1] by mauto
         hence [ty]: "g be Function" using funct_1_def_13 assms(1) A6(1)  by mauto
         hence "[x,g. x] in g" using A4(2) A6 funct_1_th_1[of g "g. x" x] by auto
         hence "[x,g. x] in union B" unfolding tarski_def_4[of B "[x, g . x]", simplified ty, OF TrueI] using assms exI[of _ g] T3 by mauto
         thus "x in dom f" using assms funct_1_th_1 by auto
       qed mauto
  qed
  show "rng f = union ?R"
  proof(unfold xboole_0_def_10[OF all_set all_set],rule conjI)
    show "rng f \<subseteq> union ?R"
       proof(standard,auto)
         fix y
         assume "y in rng f"
         then obtain x where
            "x be object" "x in dom f" "y = f. x" using funct_1_def_3 assms(2) by mauto
         hence "[x,y] in f" using funct_1_th_1[of f y x] assms(2) by auto
         then obtain g where
          [ty]: "g be set" and A2:"[x, y] in g" "g in B" using assms(3) tarski_def_4 by mauto
         have T2: "g be Element-of B" using A2 Element(6) by mauto
         have T3[ty]: "g be Function" using A2 funct_1_def_13[THEN iffD1] assms(1) by mauto
         hence C1: "x in dom g" "y=g. x" using A2 funct_1_th_1[of g y x] by auto+
         have C2: "y in rng g" using funct_1_def_3[of g] C1 T3 by mauto
         have "rng g in ?R" using Set_of_All_in[OF _ T2] by mauto
         thus "y in union ?R" using C2 tarski_def_4 all_set by auto
       qed mauto
    show "union ?R \<subseteq> rng f"
       proof(standard,auto)
         fix y
         assume "y in union ?R"
         then obtain r where
           A4: "r be set" "y in r" "r in ?R" using tarski_def_4 by mauto
         obtain g where
           A[ty]: "g be Element-of B" and A6:"r = rng g" using Set_of_All_ex[OF _ _ A4(3)] by mauto

          have T3: "g in B" using assms(1) A6 A Element(7) by auto
         hence [ty]: "g be Function" using funct_1_def_13 assms(1) A6(1)  by mauto
          then obtain x where
           A7: "x be object" "x in dom g" "y = g. x" using funct_1_def_3 A4(2) A6 by mauto
         have "[x,y] in g" using A7 funct_1_th_1[of g y x] T3 by mauto
         hence "[x,y] in union B" unfolding tarski_def_4[of B "[x, y]",simplified ty,OF TrueI] using assms exI[of _ g] T3 by mauto
         thus "y in rng f" using xtuple_0_def_13 assms by auto
       qed mauto
     qed
   qed

text_raw {*\DefineSnippet{relat_1_contr}{*}
theorem
   "for X be set st X is non (rng X)-valued holds
      \<not> X is Function"
text_raw {*}%EndSnippet*}
proof(standard,standard,standard)
  fix X assume [ty]:"X is set" and A1:"X is non (rng X)-valued" and [ty]:"X is Function"
  have "X is (rng X)-valued" using relat_1_def_19 xboole_0_def_10 by mauto
  thus "False" using A1 by simp
qed mauto


mtheorem
  mlet "X be set"
  "cluster X-valued for Function"
proof(standard,standard)
  have "rng {} is empty" by mauto
  hence "rng {} = {}" using xboole_0_lm_1 by mauto
  hence "rng {} \<subseteq> X" using xb tarski_def_3 by mauto
  thus "{} is X-valued \<bar> Function" using relat_1_def_19I by mauto
qed

  
  (*lemma impMI:" (A1\<Longrightarrow> A2 \<longrightarrow> C)\<Longrightarrow> A1 \<and> A2\<longrightarrow>C" by iprover
lemma conjMI:" C2 \<Longrightarrow> C1\<Longrightarrow> (C1 \<and> C2)" by auto
 
thm ballI
  thm bexI
  
theorem 
fixes P::" Set \<Rightarrow> o"
fixes Q::" Set \<Rightarrow> o"
fixes R::" Set \<Rightarrow> o"
shows "A=A"
proof
  {fix x 
    assume "P(x)"
    have "Q(x)" sorry
    have "R(x)" sorry
  }
  hence "for x be object st P(x) holds Q(x)" by mauto   
   
  qed
*)

end

