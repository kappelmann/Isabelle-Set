theory xboole_0
imports tarski
begin

section "XBOOLE_0"

mscheme xboole_0_sch_1:
  mlet "A be set"
  "ex X being set st for x being object holds
      x in X \<longleftrightarrow> x in A \<and> P(x)"
proof-
  let ?Q = "\<lambda>x. \<lambda>y. (x=y \<and> P(x))"
  have A1: "for x,y,z being object holds
    ?Q (x,y) \<and> ?Q (x,  z) \<longrightarrow> y = z" using ex by simp
  obtain X where
   T[ty]:"X be set" and A2: "(for x being object holds x in X iff
    (ex y being object st y in A \<and> ?Q (y,x)))"
    using tarski_sch_1[of A,OF _ A1] by infer_auto
  hence "for x being object holds x in X \<longleftrightarrow> x in A \<and> P(x)" by auto
  then show "ex X be set st
    (for x being object holds x in X \<longleftrightarrow> x in A \<and> P(x))"
    using T ex by blast
  qed

text_raw {*\DefineSnippet{xboole_0_def_1}{*}
mdef xboole_0_def_1 ("empty") where
  "attr empty for set means (\<lambda>it. \<not> (\<exists>x : object. x in it))" .
text_raw {*}%EndSnippet*}

  
mtheorem xboole_0_cl_1:
   "cluster empty for set"
proof
   let ?P = "\<lambda>x. False"
   obtain X where
   T0[ty]:"X be set" and A1:"(for x being object holds x in X \<longleftrightarrow> x in (the set) \<and> ?P(x))"
       using xboole_0_sch_1[of "the set" ?P] by auto
   hence "X is empty\<bar>set" using xboole_0_def_1I by auto
   thus "inhabited(empty \<bar> set)" using inhabited_def by auto
qed
 
  
text_raw {*\DefineSnippet{xboole_0_def_2}{*}
mdef xboole_0_def_2:xboole_0K1  ("{}") where
  "func {} \<rightarrow> set equals
     the empty\<bar>set"
text_raw {*}%EndSnippet*}
proof -
  show "(the empty \<bar>set) be set" using choice_ax[of "empty\<bar>set"] by auto
qed
print_theorems  
ML {* @{term "{}"} *}

(*lemma xboole_0_def_2d : "{} is empty"
  using choice_ax[of "empty\<bar>set"] xboole_0_def_2 by auto
*)
text_raw {*\DefineSnippet{xboole_0_def_3}{*}

mdef xboole_0_def_3     (infixl "\<union>" 65) where
  mlet "X be set", "Y be set"
  "func X \<union> Y \<rightarrow> set means \<lambda>it.
     \<forall>x. x in it \<longleftrightarrow> x in X \<or> x in Y"
text_raw {*}%EndSnippet*}
proof -
      have "(union {X,Y}) be set \<and> (for x being object holds (x in union {X,Y} \<longleftrightarrow> x in X \<or> x in Y))"
        proof (intro conjI)
          show "(union {X,Y}) be set" by infer_auto
          show "for x being object holds (x in union {X,Y} \<longleftrightarrow> x in X \<or> x in Y)"
            proof (intro ballI,rule iffI2)
              fix x
              assume Z1[ty]: "x be object"
              have H: "{X,Y} be set" by infer_auto
              show "x in union {X,Y} \<longrightarrow> x in X \<or> x in Y"
                proof
                  assume "x in union { X , Y }"
                  hence "ex Z being set st x in Z \<and> Z in {X,Y}" using tarski_def_4[of "{X,Y}" x] by infer_auto
                  thus "x in X \<or> x in Y" using tarski_def_2 by infer_auto
                qed
                have "X in {X,Y}" "Y in {X,Y}" using tarski_def_2 by infer_auto
                 then show "(x in X \<or> x in Y) \<longrightarrow> x in union {X,Y}"
                  unfolding tarski_def_4[of "{X,Y}" x,OF H] using ty ex by blast
                qed simp
        qed
        thus "ex it be set st (\<forall>x.  x in it \<longleftrightarrow> x in X \<or> x in Y)" using ex by blast
  next
  fix A1 A2
  assume A1:"A1 be set" "(for x being object holds (x in A1 \<longleftrightarrow> x in X \<or> x in Y))" and
        A2: "A2 be set" "(for x being object holds (x in A2 \<longleftrightarrow> x in X \<or> x in Y))"
    {
      fix x
      assume Z1[ty]: "x be object"
      have "x in A1 \<longleftrightarrow> (x in X \<or> x in Y)" using A1 by auto
      then have "x in A1 \<longleftrightarrow> x in A2" using A2 by auto
    }
    thus "A1 = A2" using tarski_th_2[OF A1(1) A2(1)] by auto
qed simp




text_raw {*\DefineSnippet{xboole_0_def_3_commutativity}{*}
mtheorem xboole_0_def_3_commutativity:
  "commutativity set xboole_0_def_3"
proof (intro ballI tarski_0_2a)
  fix x1 x2
  assume [ty]: "x1 is set" "x2 is set"
  show "(x1 \<union> x2) is set" by infer_auto
  show "(x2 \<union> x1) is set" by infer_auto
  fix x
  show "(x in x1 \<union> x2) \<longleftrightarrow> (x in x2 \<union> x1)" using xboole_0_def_3 by infer_auto
qed infer_auto
text_raw {*}%EndSnippet*}

text_raw {*\DefineSnippet{xboole_0_def_3_idempotence}{*}
theorem xboole_0_def_3_idempotence[rule_format,THEN bspec,simplified]:
  "idempotence set xboole_0_def_3"
proof
  fix x assume [ty]: "x is set"
  show "x\<union>x=x" using xboole_0_def_3 by (intro tarski_th_2) infer_auto
qed simp_all
text_raw {*}%EndSnippet*}

mtheorem xboole_0_def_3_assoc: "X \<union> (Y \<union> Z) = (X \<union> Y) \<union> Z"
  using xboole_0_def_3 by (intro ballI tarski_0_2a) infer_auto
mtheorem xboole_0_def_3_idem2[simp]: "X \<union> (X \<union> Z) = X \<union> Z"
  using xboole_0_def_3 by (intro ballI tarski_0_2a) infer_auto
lemmas xboole_0_def_3_ac = xboole_0_def_3_assoc xboole_0_def_3_commutativity xboole_0_def_3_idempotence xboole_0_def_3_ty

(* KP: Może ładniej robić tak później a nie zawsze rozbijać definicją unii? *)
mlemma mlet "W be set", "V be set", "M be set"
  "X \<union> Y \<union> V \<union> Z \<union> W \<union> V \<union> M = M \<union> X \<union> Z \<union> Y \<union> W \<union> V"
  using xboole_0_def_3_ac by infer_simp

text_raw {*\DefineSnippet{xboole_0_def_4}{*}
mdef xboole_0_def_4  (infixl "\<inter>" 70) where
  mlet "X be set", "Y be set"
  "func X \<inter> Y \<rightarrow> set means \<lambda>it.
    \<forall>x. x in it \<longleftrightarrow> (x in X \<and> x in Y)"
text_raw {*}%EndSnippet*}
proof -
  show "ex Z being set st for x being object holds (x in Z \<longleftrightarrow> (x in X \<and> x in Y))"
    using xboole_0_sch_1 by infer_auto
next
  fix A1 A2
  assume [ty]:"A1 be set" "A2 be set"
  assume A1: "for x being object holds (x in A1 \<longleftrightarrow> (x in X \<and> x in Y))"
     and A2: "for x being object holds (x in A2 \<longleftrightarrow> (x in X \<and> x in Y))"
  {
      fix x assume "x be object"
      have "x in A1 \<longleftrightarrow> (x in X \<and> x in Y)" using A1 by auto
      then have "x in A1 \<longleftrightarrow> x in A2" using A2 by auto
  }
  thus "A1 = A2" using tarski_th_2 by infer_auto
qed simp_all
notation xboole_0_def_4(infixl "\<inter>" 70)


mtheorem xboole_0_def_4_commutativity:
  "commutativity set xboole_0_def_4"
proof(intro ballI)
  fix X Y
  assume [ty]: "X be set" "Y be set"
  {
    fix x
    assume "x be object"
    have "x in X\<inter>Y \<longleftrightarrow> x in X \<and> x in Y" using xboole_0_def_4 by infer_auto
    hence "x in X\<inter>Y \<longleftrightarrow> x in Y\<inter>X" using xboole_0_def_4 by infer_auto
  }
  thus "X \<inter> Y = Y \<inter> X" using tarski_th_2[of "X\<inter>Y" "Y\<inter>X"] by infer_auto
qed simp_all

mtheorem xboole_0_def_4_idempotence:
  "idempotence set xboole_0_def_4"
proof(intro ballI)
   fix X
   assume [ty]: "X be set"
  {
     fix x
     assume T1:"x be object"
     have "x in X \<inter> X \<longleftrightarrow> x in X " using xboole_0_def_4 by infer_auto
   }
   thus "X \<inter> X = X" using tarski_th_2[of "X \<inter> X" "X"] all_set by auto
qed simp_all

text_raw {*\DefineSnippet{xboole_0_def_5}{*}
mdef xboole_0_def_5 (infixl "\\" 70) where
  mlet "X be set", "Y be set"
  "func X \\ Y \<rightarrow> set means \<lambda>it.
     \<forall>x. x in it \<longleftrightarrow> x in X \<and> \<not> x in Y"
text_raw {*}%EndSnippet*}
proof -
  show "ex Z being set st for x being object holds (x in Z \<longleftrightarrow> (x in X \<and> \<not> x in Y))"
    using xboole_0_sch_1 by infer_auto
  fix A1 A2
  assume [ty]: "A1 be set" "A2 be set"
  assume A1: "for x being object holds (x in A1 \<longleftrightarrow> (x in X \<and> \<not> x in Y))"
     and A2: "for x being object holds (x in A2 \<longleftrightarrow> (x in X \<and> \<not> x in Y))"
  {
      fix x
      assume T1:"x be object"
      have "x in A1 \<longleftrightarrow> (x in X \<and> \<not> x in Y)" using A1 T1 by auto
      then have "x in A1 \<longleftrightarrow> x in A2" using A2 T1 by auto
  }
  thus "A1 = A2" by (intro tarski_th_2) infer_auto
qed simp
text_raw {*\DefineSnippet{xboole_0_def_6}{*}
mdef xboole_0_def_6 (infixl "\\+\\" 65) where
  mlet "X be set", "Y be set"
  "func X \\+\\ Y \<rightarrow> set
     equals (X \\ Y) \<union> (Y \\ X)"
text_raw {*}%EndSnippet*}
proof -
  show "((X \\ Y) \<union> (Y \\ X)) be set" by infer_auto
qed


mtheorem xboole_0_def_6_commutativity:
"commutativity set xboole_0_def_6"
proof(intro ballI)
  fix X Y
  assume [ty]: "X be set" "Y be set"
  have "X \\+\\ Y = (Y \\ X) \<union> (X \\ Y)" using xboole_0_def_6 xboole_0_def_3_commutativity
    by infer_auto
  thus "X \\+\\ Y = Y \\+\\ X" using xboole_0_def_6 by infer_auto
qed infer_auto
    
mdef xboole_0_def_7 (infixl "misses" 60) where
  mlet "X be set", "Y be set"
  "pred X misses Y means X \<inter> Y = {}".

text_raw {*\DefineSnippet{xboole_0_def_7_symmetry}{*}
mtheorem xboole_0_def_7_symmetry:
  "symmetry set xboole_0_def_7"
proof(intro ballI)
  fix X Y
  assume [ty]: "X be set" "Y be set"
  thus "X misses Y \<longrightarrow> Y misses X" using xboole_0_def_7 xboole_0_def_4_commutativity by auto
qed simp_all
text_raw {*}%EndSnippet*}

mdef xboole_0_def_8 (infixl "c<" 50)
  where 
mlet "X be set","Y be set" 
 "pred (X c< Y) means X c= Y \<and> X\<noteq>Y".

syntax "xboole_0.xboole_0_def_8" :: "Set \<Rightarrow> Set \<Rightarrow> o" (infixl "\<subset>" 50)

text_raw {*\DefineSnippet{xboole_0_def_8_irreflexivity}{*}
mtheorem xboole_0_def_8_irreflexivity:
  "irreflexive set xboole_0_def_8" using xboole_0_def_8E by auto
text_raw {*}%EndSnippet*}

text_raw {*\DefineSnippet{xboole_0_def_8_asymmetry}{*}
theorem xboole_0_def_8_asymmetry:
  "asymmetry set xboole_0_def_8"
text_raw {*}%EndSnippet*}
proof(intro ballI)
  fix X Y
  assume [ty]: "X be set" "Y be set"
  have "X c< Y \<Longrightarrow> \<not> Y c< X"
    proof-
  assume A1:"X c<Y"
  show "not (Y c<X)"
   proof
    assume A2: "Y c< X"
     {
        fix x
        assume [ty]:"x be object"
        have A3:"x in X \<longrightarrow> x in Y" using tarski_def_3E A1 xboole_0_def_8E by infer_auto
        have "x in Y \<longrightarrow> x in X" using tarski_def_3E xboole_0_def_8E A2 by infer_auto
        hence "x in X \<longleftrightarrow> x in Y" using A3 by auto
     }
    hence "X = Y" by (intro tarski_th_2) infer_auto
    thus "False" using A1 xboole_0_def_8 by infer_auto
  qed
qed
  thus "not (X c< Y \<and> Y c< X)" by iprover
qed simp_all

mdef xboole_0_def_9 ("_ , _ are c= comparable"[50,50] 40) where
  mlet "X be set", "Y be set"
 "pred X,Y are c= comparable means (X c= Y \<or> Y c= X)".

theorem xboole_0_def_9_symmetry[THEN bspec,THEN bspec,rule_format,simplified]:
  "symmetry set xboole_0_def_9" using xboole_0_def_9 by auto

mtheorem xboole_0_def_10:
   mlet "X be set","Y be set"
   "redefine pred X = Y means X c= Y \<and> Y c= X"
proof 
  show "X = Y \<longleftrightarrow> (X c= Y \<and> Y c= X)"
     proof(rule iffI2)
        show "X = Y \<longrightarrow> (X c= Y \<and> Y c= X)" using tarski_def_3 by infer_auto
        show "(X c= Y \<and> Y c= X) \<longrightarrow> X=Y"
          proof
            assume A1:"X c= Y \<and> Y c= X"
              {
                 fix x
                 assume [ty]:"x be object"
                 have A2:"x in X \<longrightarrow> x in Y" using tarski_def_3E[of X Y] A1 by infer_auto
                 have "x in Y \<longrightarrow> x in X" using tarski_def_3E[of Y X] A1 by infer_auto
                 hence "x in X \<longleftrightarrow> x in Y" using A2 by auto
              }
            thus "X=Y" by (intro tarski_th_2) infer_auto
          qed
     qed
   qed

mdef xboole_0_antonym_meets (infix "meets" 60)
  where 
  mlet "X be set","Y be set" 
  "antonym pred X meets Y for X misses Y".

mtheorem xboole_0_th_1: "x in X \\+\\ Y \<longleftrightarrow> \<not> (x in X \<longleftrightarrow> x in Y)"
proof -
  have "x in X \\+\\ Y \<longleftrightarrow> x in X \\ Y \<or> x in Y \\ X" using xboole_0_def_6 xboole_0_def_3 by infer_auto
  thus "x in X \\+\\ Y \<longleftrightarrow> \<not> (x in X \<longleftrightarrow> x in Y)" using xboole_0_def_5 by infer_auto
qed

mtheorem xboole_th2:  "(\<forall>x.  (not x in X) \<longleftrightarrow> (x in Y \<longleftrightarrow> x in Z)) \<longrightarrow> X = Y \\+\\ Z"
proof(standard,rule xboole_0_def_10I,infer_simp)
  assume A1: "\<forall>x : object. \<not> x in X \<longleftrightarrow> x in Y \<longleftrightarrow> x in Z"
  show "X \<subseteq> Y \\+\\ Z"
  proof (standard,auto)
    fix x assume "x in X"
    hence "not (x in Y \<longleftrightarrow> x in Z)" using A1 by auto
    hence "x in  Y \\ Z \<or> x in Z\\Y" using xboole_0_def_5  by infer_auto    
    thus "x in  Y \\+\\ Z" using xboole_0_def_6  xboole_0_def_3 by infer_auto    
  qed infer_auto
  show "Y \\+\\ Z \<subseteq> X"
   proof (standard,auto)
     fix x assume "x in  Y \\+\\ Z"
     hence "x in  Y \\ Z \<or> x in Z\\Y" using xboole_0_def_6  xboole_0_def_3   by infer_auto  
    hence "not (x in Y \<longleftrightarrow> x in Z)" using xboole_0_def_5 by infer_auto
    thus "x in  X" using A1 by infer_auto    
  qed infer_auto
qed infer_auto
 
mtheorem xboole_0_cl_2:
  "cluster {} \<rightarrow> empty" 
proof
  have "(the (empty \<bar> set)) be empty \<bar> set" by (intro choice_ax)  auto
  thus "{} is empty" using xboole_0_def_2 by auto
qed  
  
mlemma xb: "\<not>x in {}" using xboole_0_def_1(1) by infer_auto

mtheorem xboole_0_cl_3:
   mlet "x be object"
   "cluster {x} \<rightarrow> non empty"
     using tarski_def_1 xboole_0_def_1 by infer_auto

mtheorem xboole_0_cl_4:
  mlet "x be object", "y be object"
  "cluster {x,y} \<rightarrow> non empty" using tarski_def_2 xboole_0_def_1 by infer_auto


mtheorem xboole_0_cl_5:
  "cluster non empty for set"
proof(standard,standard)
  show "{the object} is non empty \<bar> set" using xboole_0_cl_3 by infer_auto
qed  

mtheorem xboole_0_cl_6:
  mlet "D be non empty\<bar> set", "X be set"
  "cluster D \<union> X \<rightarrow> non empty"
proof
  obtain x where
    A1: "x be object " "x in D" using xboole_0_def_1[of D] by infer_auto
  hence "x in D \<union> X" using xboole_0_def_3 by infer_auto
  thus "(D \<union> X) is non empty" using xboole_0_def_1(1) ty A1 by infer_auto
qed

mtheorem xboole_0_lm_1:
   "X is empty \<longrightarrow> X={}"
proof
  assume A1: "X is empty"
  hence "not (ex x st x in X)" using xboole_0_def_1(1) by infer_auto
  hence "\<forall>x.  x in {} \<longleftrightarrow> x in X" using xboole_0_def_1(1) by infer_auto
  thus "X = {}" by (intro tarski_th_2) infer_auto
qed

lemma xb1: "x in X \<longrightarrow> X \<noteq> {}"
using xb by auto

mtheorem xboole_0_th_3:
   "(X meets Y) \<longleftrightarrow> (ex x being object st x in X \<and> x in Y)"
proof
  assume "X meets Y"
  hence "X \<inter> Y \<noteq> {}" using xboole_0_antonym_meets xboole_0_def_7I by infer_auto
  hence "(X \<inter> Y) is non empty" using xboole_0_lm_1[of "X \<inter> Y"] xboole_0_def_1 by infer_auto
  then obtain x where
    A1:"x be object \<and> x in X \<inter> Y" using xboole_0_def_1 by infer_auto
  have "x be object \<and> x in X \<and> x in Y" using A1 xboole_0_def_4 by infer_auto
  thus "ex x being object st x in X \<and> x in Y" by auto
next
  assume "ex x being object st x in X \<and> x in Y"
  then obtain x where
  A2:"x be object \<and> x in X \<and> x in Y" by auto
  have "x in X \<inter> Y" using A2 xboole_0_def_4 by infer_auto
  hence "X \<inter> Y \<noteq> {}" using A2 xb1 by auto
  thus "X meets Y" using xboole_0_antonym_meets xboole_0_def_7 by infer_auto
qed

mtheorem xboole_0_th_4:
  "(X meets Y) \<longleftrightarrow> (ex x st x in X\<inter> Y)"
proof
  assume "X meets Y"
  hence "X \<inter> Y \<noteq> {} " using xboole_0_antonym_meets xboole_0_def_7 by infer_auto
  hence "(X \<inter> Y) is non empty" using xboole_0_lm_1[of "X \<inter> Y"] xboole_0_def_1 by infer_auto
  then obtain x where
    A1:"x be object \<and> x in X\<inter>Y" using xboole_0_def_1 by infer_auto
  have "x be object \<and> x in X \<inter> Y" using A1 by auto
  thus "ex x being object st x in X \<inter> Y" by auto
next
  assume "ex x being object st x in X\<inter> Y"
  then obtain x where
  A2:"x be object \<and> x in X \<inter> Y" by auto
  have "X \<inter> Y \<noteq> {}" using A2 xb1 by auto
  thus "X meets Y" using xboole_0_antonym_meets xboole_0_def_7E by infer_auto
qed

mtheorem xboole_0_th_5:
  "X misses Y \<Longrightarrow> x in X \<union> Y \<Longrightarrow> x in X \<and> \<not> x in Y \<or> x in Y \<and> \<not> x in X"
proof-
  assume A1:"X misses Y" "x in X \<union> Y"
  hence "x in X \<or> x in Y" using xboole_0_def_3 by infer_auto
  thus "x in X \<and> \<not> x in Y \<or> x in Y \<and> \<not> x in X" using A1(1) xboole_0_th_3 xboole_0_antonym_meets[of X Y] by infer_auto
qed

mscheme xboole_0_sch_2:
  mlet "X1 be set", "X2 be set"
   "for x being object holds x in X1 \<longleftrightarrow> P(x) \<Longrightarrow>
    for x being object holds x in X2 \<longleftrightarrow> P(x) \<Longrightarrow>
    X1 = X2"
  by (intro tarski_th_2) infer_auto

lemmas xboole_0_sch_3 = xboole_0_sch_2

mtheorem xboole_0_th_6:
  "X c< Y \<Longrightarrow> ex x st x in Y \<and> \<not> x in X"
  using xboole_0_def_8 xboole_0_def_10 tarski_def_3 by infer_auto

mtheorem xboole_0_th_7:
  "X \<noteq> {} implies (ex x being object st x in X)"
    using xboole_0_lm_1[of X] xboole_0_def_1I[of X] by infer_auto

text_raw {*\DefineSnippet{impMI}{*}  
lemma  impMI:  "(A1 \<Longrightarrow> A2 \<longrightarrow> C) \<Longrightarrow> A1 \<and> A2 \<longrightarrow> C"
text_raw {*}%EndSnippet*}
by iprover      

text_raw {*\DefineSnippet{conjMI}{*}  
lemma conjMI: "C2 \<Longrightarrow> C1 \<Longrightarrow> C1 \<and> C2"
text_raw {*}%EndSnippet*}
  by simp 
    
mtheorem xboole_0_th_8:
  "for X,Y being set st X c< Y holds
     ex x being object st x in Y \<and> X c= Y\\{x}"
proof (intro ballI impI)
  fix X Y
  assume [ty]:"X be set" "Y be set"
  assume A1:"X \<subset> Y"
  then obtain x where
    [ty]: "x be object" and A2: "x in Y" and
    A3:"not x in X" using xboole_0_th_6[of Y X] by infer_auto
  have "x be object \<and> x in Y \<and> X c= Y\\{x}"
    proof (intro conjI)
      show "x be object" by infer_auto
       show "x in Y" using A2 by simp
       show "X c= Y\\{x}"
         proof (standard,auto)
            fix z
            assume A4:"z in X"
            hence "z \<noteq> x" using A3 by auto
            hence A5: "not z in {x}" using tarski_def_1 by auto
            have "X c= Y" using A1 xboole_0_def_8 by infer_simp
            hence A6: "z in Y" using A4 tarski_def_3E by infer_auto
            show "z in Y\\{x}" using A5 A6 xboole_0_def_5 by infer_auto
         qed infer_auto
    qed
  thus "ex x being object st x in Y \<and> X \<subseteq> Y\\{x}" by auto
qed infer_auto    
  
text_raw {*\DefineSnippet{xboole_0_th_8A}{*}
reserve X,Y for set
reserve x for object    
  
mtheorem xboole_0_th_8A:
 "\<forall> X. \<forall> Y. X c< Y \<longrightarrow> (\<exists> x. x in Y \<and> X c= Y \\ { x } )"
proof-    
  have "\<forall> X. \<forall> Y. X c< Y \<longrightarrow> (\<exists> t:object. t in Y \<and> X c= Y \\ { t } )"
  proof(rule ballI,rule ballI,rule impI)
    fix X assume [ty]:"X be set"
    fix Y assume [ty]:"Y be set"  
    assume A1: "X c< Y"
    then obtain x where
      [ty]: "x be object" and
      A2: "x in Y" and A3: "\<not> x in X" using xboole_0_th_6 by infer_auto
    show "\<exists> t : object. t in Y \<and> X c= Y \\ { t } "
    proof(rule bexI[of _ x],rule conjMI)
      show "x in Y" using A2 by auto
      have "\<forall> y : object. y in X \<longrightarrow> y in Y \\  { x }"
      proof(rule ballI,rule impI)
        fix y assume [ty]:"y be object"
        assume A4: "y in X"
        hence A5: "\<not> y in { x }" using A3 tarski_def_1 by auto
        have "X c= Y" using A1 xboole_0_def_8 by infer_auto
        hence "y in Y" using A4 tarski_def_3 by infer_auto
        thus "y in Y\\{ x }" using xboole_0_def_5 A5 by infer_auto
      qed infer_auto
      thus "X c= Y\\{ x }" using tarski_def_3 by infer_auto
    qed infer_auto
  qed infer_auto
  thus ?thesis by infer_auto
qed  
text_raw {*}%EndSnippet*}
  
mtheorem xboole_0_th_8B:
 " X c< Y \<longrightarrow> (\<exists> x. x in Y \<and> X c= Y \\ { x } )"
proof
   thm ty
    assume A1: "X c< Y"
    then obtain x where
      [ty]: "x be object" and
      A2: "x in Y" and A3: "\<not> x in X" using xboole_0_th_6 by infer_auto
    show "\<exists> t : object. t in Y \<and> X c= Y \\ { t } "
    proof(rule bexI[of _ x],rule conjMI)
      show "x in Y" using A2 by auto
      have "\<forall> y : object. y in X \<longrightarrow> y in Y \\  { x }"
      proof(rule ballI,rule impI)
        fix y assume [ty]:"y be object"
        assume A4: "y in X"
        hence A5: "\<not> y in { x }" using A3 tarski_def_1 by auto
        have "X c= Y" using A1 xboole_0_def_8 by infer_auto
        hence "y in Y" using A4 tarski_def_3 by infer_auto
        thus "y in Y\\{ x }" using xboole_0_def_5 A5 by infer_auto
      qed infer_auto
      thus "X c= Y\\{ x }" using tarski_def_3 by infer_auto
    qed infer_auto
qed  
  
  
mdef xboole_0_antonym_2 ("_ c\\= _" 40)where
 mlet "X be set","Y be set"
 "antonym pred X c\\= Y for X c= Y".

mdef xboole_0_antonym_3 ("_ nin _" 40)where
 mlet "x be object","X be set"
 "antonym pred x nin X for x in X".

mtheorem xboole_1_th_1:
  "X \<subseteq> Y \<and> Y \<subseteq> Z \<longrightarrow> X \<subseteq> Z" using tarski_def_3 by infer_auto

mtheorem xboole_1_th_7:
  "X \<subseteq> X \<union> Y" using tarski_def_3 xboole_0_def_3 by infer_auto

mtheorem xboole_1_th_8:
  "X \<subseteq> Z \<and> Y \<subseteq> Z \<Longrightarrow> X \<union> Y \<subseteq> Z"
proof(standard,auto)
  assume A1:"X \<subseteq> Z " " Y \<subseteq> Z"
  fix x
  assume "x in X \<union> Y"
  hence "x in X \<or> x in Y" using xboole_0_def_3 by infer_auto
  thus "x in Z" using A1 tarski_def_3E by infer_auto
qed infer_auto

mtheorem xboole_1_th_28:
  " X \<subseteq> Y implies X\<inter>Y = X"
proof(standard,rule xboole_0_def_10I)
  assume A1: "X \<subseteq>Y"
  show  "X\<inter>Y \<subseteq> X" 
    using tarski_def_3I xboole_0_def_4 by infer_auto
  show "X \<subseteq>X\<inter>Y" using tarski_def_3I xboole_0_def_4 A1 tarski_def_3 by infer_auto
qed infer_auto

mtheorem xboole_1_empty:
  "X \<subseteq> Y \<and> X\<noteq>{} \<longrightarrow> Y\<noteq>{}"
proof
  assume A1:"X \<subseteq> Y \<and> X\<noteq>{}"
  then obtain x where
     "x in X" using xboole_0_th_7[of X]  by infer_auto
  hence "x in Y" using A1 tarski_def_3 by infer_auto
  thus "Y\<noteq>{}" using xb by auto    
qed  


end
