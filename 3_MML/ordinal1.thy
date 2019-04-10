theory ordinal1
imports zfmisc_1 subset_1
begin


reserve u,v,x,x1,x2,y,y1,y2,z,p,a for object
reserve A,B,X,X1,X2,X3,X4,X5,X6,Y,Y1,Y2,Z,N,M for set

section "ordinal1"

abbreviation(input) 
  "ZeroM  \<equiv> {}" 

mtheorem ordinal1_th_1:"Y in X \<longrightarrow> \<not> X \<subseteq> Y"
proof (standard,standard)
  assume A1:"Y in X"
  assume "X \<subseteq> Y"
  hence "Y in Y" using A1 tarski_def_3 by infer_auto
  thus "False" using prefix_in_irreflexive by infer_auto
qed

text_raw {*\DefineSnippet{ordinal_1_def_1}{*}
mdef ordinal1_def_1 ("succ _" [90] 90) where
  "func succ X \<rightarrow> set equals X \<union> {X}"
text_raw {*}%EndSnippet*}
proof -
  show "(X \<union> {X}) be set" by infer_simp
qed

abbreviation (input) 
  "OneM  \<equiv> succ {}" 

abbreviation (input)
  "TwoM  \<equiv> succ OneM" 


abbreviation (input) 
  "ThreeM  \<equiv> succ TwoM" 


abbreviation (input) 
  "FourM  \<equiv> succ ThreeM" 


notation
  ZeroM ("0\<^sub>\<S>") and
  OneM ("1\<^sub>\<S>") and
  TwoM ("2\<^sub>\<S>") and
  ThreeM ("3\<^sub>\<S>") and
  FourM ("4\<^sub>\<S>")
mtheorem ordinal1_th_2:"X in succ X"
proof -
  have "X in {X}" using tarski_def_1 by infer_auto
  thus ?thesis using xboole_0_def_3 ordinal1_def_1 by infer_auto
qed
  
mtheorem ordinal1_th_2a:"X c= succ X"
proof -
  have "succ X= X\<union>{X}" using ordinal1_def_1  by infer_auto
  thus ?thesis using xboole_0_def_3 tarski_def_3  by infer_auto
qed


lemma nonempty_succ[simp]: "succ X<>{} & {}<>succ X"
proof-
  have "X in succ X" using ordinal1_th_2 all_set by auto
  thus ?thesis using xb by auto
qed
    
mtheorem ordinal1_th_4:"x in succ X \<longleftrightarrow> x in X \<or> x = X"
proof (rule iffI3)
  show "x in succ X \<longrightarrow> x in X \<or> x = X"
  proof
    assume "x in succ X"
    hence "x in X \<or> x in {X}" using xboole_0_def_3 ordinal1_def_1 by infer_auto
    thus "x in X \<or> x = X" using tarski_def_1[of X] by infer_auto
  qed
  assume "x in X \<or> x = X"
  hence "x in X \<or> x in {X}" using tarski_def_1 by infer_auto
  thus "x in succ X" using xboole_0_def_3 ordinal1_def_1 by infer_auto
qed

mtheorem ordinal1_th_5:
  "X <> succ X"
proof
  assume
A1: "X = succ X"
  have "X in succ X" using ordinal1_th_2 by infer_auto
  thus "False" using  A1 prefix_in_irreflexive by auto
qed
  
mtheorem ordinal1_succ: "X\<noteq>Y \<Longrightarrow> succ X \<noteq> succ Y"
proof
  assume A1: "X\<noteq>Y" "succ X = succ Y"
  have "Y in succ Y" using ordinal1_th_2 tarski_def_1 xboole_0_def_3 by infer_auto
  hence "Y in X \<union> { X }" using ordinal1_def_1 A1(2) by infer_auto
  hence A2: "Y in X" using A1(1) tarski_def_1 xboole_0_def_3 by infer_auto
  have "X in succ X" using ordinal1_th_2 tarski_def_1 xboole_0_def_3 by infer_auto
  hence "X in Y \<union> { Y }" using ordinal1_def_1 A1(2) by infer_auto
  hence "X in Y" using A1(1) tarski_def_1 xboole_0_def_3 by infer_auto
  thus "False" using A2 prefix_in_asymmetry[of X Y] by infer_auto
qed
  
reserve a,b,c for object
reserve X,Y,Z,x,y,z for set

mdef ordinal1_def_2 ("epsilon-transitive")where
  "attr epsilon-transitive for set means
     (\<lambda>X. for x st x in X holds x c= X)"..

mdef ordinal1_def_3 ("epsilon-connected")where
  "attr epsilon-connected for set means
     (\<lambda>X. for x,y st x in X \<and> y in X holds x in y \<or> x = y \<or> y in x)"..

mdef ordinal1_def_4 ("ordinal")where
  "attr ordinal for object means
     (\<lambda>IT. IT is epsilon-transitive \<bar> epsilon-connected \<bar> set)"..

mdef ordinal1_def_6 ("limit'_ordinal")where
  "attr limit_ordinal for set means (\<lambda>A. A = union A)"..

abbreviation (input) "Number \<equiv> object"
abbreviation (input) "number \<equiv> set"
abbreviation "Ordinal \<equiv> ordinal \<bar> number"


mtheorem Lm1:
 "cluster {} \<rightarrow> epsilon-transitive \<bar> epsilon-connected"
proof
  show "{} is epsilon-transitive \<bar> epsilon-connected"
  using xb1 ordinal1_def_2I ordinal1_def_3I by inst_nopass_auto
qed
  
mtheorem 
  "cluster ordinal for number"
proof(standard,standard)
  show "{} is Ordinal" using Lm1 ordinal1_def_4I by infer_auto
qed

mtheorem 
  "cluster epsilon-transitive for number"
proof(standard,standard)
  show "{} is epsilon-transitive \<bar> number" using Lm1 by infer_auto
qed

reserve A,B,C,D for Ordinal
mtheorem
  "cluster epsilon-transitive \<bar> epsilon-connected \<rightarrow> ordinal for set"
    using ordinal1_def_4I by infer_auto
 
mtheorem
  "cluster ordinal \<rightarrow> epsilon-transitive \<bar> epsilon-connected  for set"
using  ordinal1_def_4E by infer_auto
  
(* Are similar? *)

mtheorem ordinal1_th_6:
  "\<forall>B : number. \<forall>A : number. \<forall>C : epsilon-transitive \<bar> number. A in B \<and> B in C \<longrightarrow> A in C"
proof (standard,standard,standard,standard,elim conjE)
  fix A B
  assume [ty]: "A is number" "B is number"
  fix C
  assume [ty]: "C is epsilon-transitive \<bar> number"
  assume A1:"A in B" and A2:"B in C"
  have "B \<subseteq> C" using A2 ordinal1_def_2 by infer_auto
  thus "A in C" using A1 tarski_def_3 by infer_auto
qed infer_auto

mtheorem ordinal1_th_7:
  "\<forall>x : epsilon-transitive \<bar> number. \<forall>A : Ordinal. x \<subset> A \<longrightarrow> x in A"
proof (standard,standard,standard)
  fix x
  assume [ty]: "x is epsilon-transitive \<bar> set"
  fix A
  assume [ty]: "A is Ordinal"
  let ?a = "the Element-of (A \\ x)"
  assume A1:"x \<subset> A"
  hence A2:"x \<subseteq> A" using xboole_0_def_8 by infer_auto
  have B2: "x \<noteq> A" using A1 xboole_0_def_8 by infer_auto
  hence "not A c= x" using A2 xboole_0_def_10 by infer_auto
  hence "ex y be object st y in A\\ x" using tarski_def_3 xboole_0_def_5 by infer_auto
  hence "A \\ x \<noteq> {}" using xboole_0_def_1 by infer_auto
  hence "?a in A \\ x" using Element(4) by infer_auto
  then obtain y where [ty]: "y is number" and
A3: "y in A \\ x" and
A4: "not (ex a being object st a in A \\ x \<and> a in y)" using tarski_th_3[of ?a "A\\x"] by infer_auto
  have A5:"y in A" "\<not> y in x" using A3 xboole_0_def_5 by infer_auto
  {
    fix a
    assume "a in x"
    then obtain z where
    [ty]:"z be set" and
A6: "z = a" and
A7: "z in x" using all_set by auto
    have W1:  "z in A" using A2 A7 tarski_def_3E all_set by auto
    hence W3: "z in y \<or> z=y \<or> y in z" using A5 ordinal1_def_3E[of A] by infer_auto
    have W2: "z \<noteq> y" using A5 A7 prefix_in_irreflexive by auto
    have A8: "z c= x" using A7 ordinal1_def_2 by infer_auto
    hence "\<not> y in z" using xboole_0_def_5 A3 tarski_def_3E all_set by auto
    hence "a in y" using W3 W2 A6 by auto
  }
  hence A8:"x \<subseteq> y" by (intro tarski_def_3I[of x y]) infer_auto
  have A9:"y \<subseteq> A" using A3 ordinal1_def_2E[of A ] xboole_0_def_5 by infer_auto
  {
    fix a
    assume [ty]: "a is Number"
    assume A10:"a in y"
    hence "\<not> a in A \\ x" using A4 by infer_auto
    hence "a in x" using A9 A10 xboole_0_def_5 tarski_def_3 by infer_auto
  }
  hence A11:"y \<subseteq> x" using tarski_def_3 by infer_auto
  thus "x in A" using A5 A8 xboole_0_def_10 by infer_auto
qed infer_auto

mtheorem ordinal1_th_7a:
  "\<forall>x : epsilon-transitive \<bar> number. \<forall>A : Ordinal. x in A \<longrightarrow> x \<subset> A"
proof(standard,standard,standard)
  fix x A assume [ty]:"x is   epsilon-transitive \<bar> number" "A is Ordinal"
  assume "x in A"
  hence "x c= A" " x<>A" using ordinal1_def_2 prefix_in_irreflexive by infer_auto
  thus "x \<subset> A" using xboole_0_def_8 by infer_auto
qed infer_auto


mtheorem ordinal1_th_8:
  "\<forall>A : epsilon-transitive \<bar> number. \<forall>C : Ordinal. \<forall>B : Ordinal. A \<subseteq> B \<and> B in C \<longrightarrow> A in C"
proof (standard,standard,standard,standard,elim conjE)
  fix A
  assume [ty]: "A is epsilon-transitive \<bar> number"
  fix B C
  assume [ty]: "B is Ordinal" "C is Ordinal"
  assume A1:"A \<subseteq> B" and A2:"B in C"
  have "B \<subseteq> C" using A2 ordinal1_def_2[of C] by infer_auto
  hence A3:"A \<subseteq> C" using A1 tarski_def_3 by infer_auto
  have "A \<noteq> C" using A1 A2 ordinal1_th_1 by infer_auto
  hence "A \<subset> C" using A3 xboole_0_def_8 by infer_auto
  thus "A in C" using ordinal1_th_7 by infer_auto
qed infer_auto


mtheorem xreagular_th_7:
  "for X1,X2,X3 be set holds
      \<not> (X1 in X2 \<and> X2 in X3 \<and> X3 in X1)"
proof (intro ballI notI impI)
  fix a b c
  assume T0[ty]:"a be set" "b be set" "c be set"
  assume A1:"a in b \<and> b in c \<and> c in a"
  let ?X = "{ a , b, c }"
  have "a in ?X" using enumset1_def_1 by infer_auto
  then obtain Y where
  T1[ty]: "Y be set" and A4:"Y in ?X \<and> \<not>(\<exists>z:object. z in ?X \<and> z in Y)"
    using tarski_th_3[of a ?X] by infer_auto
  have "Y=a \<or> Y=b\<or> Y=c " using A4 enumset1_def_1 by auto
  then show False using A1 A4 enumset1_def_1 by infer_auto
qed simp_all



mtheorem ordinal1_th_9:
  "a in A \<longrightarrow> a is Ordinal"
proof
  assume
A1: "a in A"
  have [ty]: "a is set" using tarski_0_1 by auto
  have A2: "a c= A " using ordinal1_def_2E A1 by infer_auto
      {
    fix y assume [ty]: "y be set"
    assume
A3: "y in a"
    then have
A4: "y c= A" using A2 ordinal1_def_2E[of A] tarski_def_3 by inst_nopass_auto
    assume "not y c= a"
    then obtain b where
A5: "b in y \<and> \<not> b in a" using tarski_def_3 by infer_auto
    have "b in y \\ a" using A5 xboole_0_def_5 by infer_auto
    then obtain z where
A6: "z in y \\ a" and
    "not (ex c being object st c in y \\ a \<and> c in z)" using tarski_th_3[of b "y\\a"] by infer_auto
    have A7: "z in y" "not z in a" using A6 xboole_0_def_5 by infer_auto
    hence "z in A" using A4 tarski_def_3 by infer_auto
    then have W1: " (z = a) \<or> (a in z)" using A1 A4 A7 ordinal1_def_3E[of A ] all_set by infer_auto
    have W2: "z = a \<Longrightarrow> False" using prefix_in_asymmetry[of y z] A7 A3 by infer_auto
    have "a in z \<Longrightarrow>  False" using A3 A7 xreagular_th_7[of y a z] all_set by infer_auto
    hence False using W1 W2 by auto
  }
  then have
A7: "a is epsilon-transitive" using ordinal1_def_2I[of a] all_set by auto
  have "for y,z st y in a \<and> z in a holds y in z \<or> y = z \<or> z in y" using A2 ordinal1_def_3 tarski_def_3 by infer_auto
  hence "a is epsilon-connected" using ordinal1_def_3I by infer_auto
  thus "a is Ordinal" using A7 ordinal1_def_4I by infer_auto
qed

text_raw {*\DefineSnippet{ordinal1_th_10}{*}
mtheorem ordinal1_th_10:
  "\<not>A in B \<and> A \<noteq> B \<longrightarrow> B in A"
text_raw {*}%EndSnippet*}
proof(auto)
  assume
A1: "not A in B" and
A2: "A \<noteq> B"
  have "not A \<subset> B" using A1 ordinal1_th_7 by infer_auto
  hence "not A c= B" using A2 xboole_0_def_8 by infer_auto
  then obtain a where
A3: "a in A \<and> \<not> a in B" using tarski_def_3 by infer_auto
  have "a in A \\ B" using A3 xboole_0_def_5 by infer_auto
  then obtain X where
    [ty]: "X be set" and
A4: "X in A \\ B" and
A5: "not (ex a being object st a in A \\ B \<and> a in X)" using tarski_th_3[ of a "A\\B"] by infer_auto
have A6: "X c= A" using A4 ordinal1_def_2E xboole_0_def_5 by infer_auto
  {
    fix b
    assume
A7: "b in X"
    hence "not b in A \\ B" using A5 by auto
    hence "b in B" using A6 A7 xboole_0_def_5 tarski_def_3 by infer_auto
  }
  hence "X c= B" using tarski_def_3 by infer_auto
  then have
A8: "X c< B \<or> X = B" using xboole_0_def_8 by infer_auto
   have"   B is ordinal" by infer_auto
  have A9: "X in A" using A4 xboole_0_def_5 by infer_auto
  hence "not X in B" and [ty]:"X is Ordinal" using A4 ordinal1_th_9[of A X]  xboole_0_def_5 by infer_auto
  thus "B in A" using A8 ordinal1_th_7[of X B] A4 xboole_0_def_5 by infer_auto
qed

mtheorem ordinal1_def_5:
  mlet "A be Ordinal"," B be Ordinal"
  "redefine pred A c= B means
     for C be Ordinal st C in A holds C in B"
proof (standard,rule iffI3)
  show "A c= B \<longrightarrow>  (for C be Ordinal st C in A holds C in B)" using tarski_def_3 by infer_auto
  assume A1:"for C be Ordinal st C in A holds C in B"
  show "A c= B"
    proof(standard,auto)
      fix C
      assume A2:"C in A"
      hence [ty]:"C be Ordinal" using ordinal1_th_9[of A C]  by infer_auto
      show "C in B" using A1 A2 by infer_auto
    qed infer_auto
qed

theorem ordinal1_def_5c:
  "A be Ordinal \<Longrightarrow> B be Ordinal \<Longrightarrow> \<not> A c= B \<longrightarrow> B c= A"
proof
  assume T[ty]: "A be Ordinal" "B be Ordinal"
  assume A1: "not A c= B"
  show "B c= A"
  proof(standard,auto)
    obtain C where
       A2: "C in A \<and> \<not> C in B" using A1 tarski_def_3 by infer_auto
    hence [ty]:"C is Ordinal" using A2(1) ordinal1_th_9[of A] by infer_auto
    fix D assume A3: "D in B"
    hence [ty]: "D is Ordinal" using ordinal1_th_9[of B] by infer_auto
    have "A in B \<or> B in A" using ordinal1_th_10[of A B] A1 xboole_0_def_10[of A B] by infer_auto
    hence "B in A" using ordinal1_th_6[of A] A2 by infer_auto (*szkoda ze infer_auto tego nie lapie bez instancji*)
    thus "D in A" using ordinal1_th_6[of B] A3 by infer_auto
  qed infer_auto
qed

mtheorem ordinal1_th_12:
    "A c= B \<or> B in A"
proof-
  have "A in B \<or> A = B \<or> B in A" using ordinal1_th_10 by infer_auto
  thus "A c= B \<or> B in A" using xboole_0_def_10 ordinal1_def_2 all_set by infer_auto   
qed
  
mtheorem ordinal1_th_13:
  "x is Ordinal \<Longrightarrow> (succ x) is Ordinal"
proof
  assume
A3[ty]:"x is Ordinal"
  have E: "(succ x) = x \<union> {x}" using ordinal1_def_1 by infer_auto
  have "(succ x) is epsilon-transitive"
  proof(standard,auto)
    fix y
    have A4:"y = x \<longrightarrow> y c= (succ x)" using
      xboole_1_th_7[of "x\<union>{x}" x] E by infer_auto
    have A5: "y in x \<longrightarrow> y c= (succ x)"
      proof
        assume B: "y in x"
        hence [ty]:"y is Ordinal" using ordinal1_th_9[of x] by infer_auto
        have
A6:     "y c= x" using ordinal1_def_2E[of x] B by infer_auto
        have "x c= x \<union> { x }" using xboole_1_th_7 by infer_auto
        thus "y c=  succ x" using A6 xboole_1_th_1[of "succ x" x y] E by infer_auto
      qed
      assume "y in succ x"
      hence "y in x \<or> y =x " using E xboole_0_def_3 tarski_def_1 by infer_auto
      thus "y c= succ x" using A5 A4 by auto
    qed infer_auto
  then have
A7: "(succ x) is epsilon-transitive" by auto
  {
    fix y z assume [ty]: "y be set" "z be set"
    assume
A8: "y in succ x" and
A9: "z in succ x"
   have A10: "z in x \<or> z = x" using A9 E xboole_0_def_3 tarski_def_1 by infer_auto
   have "y in x \<or> y = x" using A8 xboole_0_def_3 tarski_def_1 E by infer_auto
   hence "y in z \<or> y = z \<or> z in y" using A10 ordinal1_def_3E[of x,THEN bspec,THEN bspec] by infer_auto
  }
  hence "(succ x) is epsilon-connected" using ordinal1_def_3I by infer_auto
  thus "(succ x) is ordinal" using A7 ordinal1_def_4 by infer_auto
qed infer_auto

mtheorem 
  "cluster succ A \<rightarrow> non empty \<bar> ordinal"
proof(standard,simp,intro conjI)
    have "A in succ A" using ordinal1_th_2 by infer_auto
    thus "\<not>(succ A) is empty" using xboole_0_def_1 by infer_auto
    show "(succ A) is ordinal" using ordinal1_th_13 by infer_auto
qed


mtheorem ordinal1_th_15:"(\<forall>x : set. x in X \<longrightarrow> x is ordinal \<bar> set \<and> x \<subseteq> X) \<longrightarrow>
               X is epsilon-transitive \<bar> epsilon-connected"
proof (standard,standard)
  assume A1:"\<forall>x : set. x in X \<longrightarrow> x is ordinal \<bar> set \<and> x \<subseteq> X"
  show "X is epsilon-transitive" using A1 ordinal1_def_2 by infer_auto
  show "X is epsilon-connected"
  proof(standard,infer_simp,intro ballI impI)
    fix x assume [ty]:"x is set"
    fix y assume [ty]:"y is set"
    assume "x in X\<and>y in X"
    hence [ty]: "x is ordinal \<bar> set \<and> y is ordinal \<bar> set" using A1 by infer_auto
    thus "x in y \<or> x = y \<or> y in x" using ordinal1_th_10 by inst_nopass_auto
  qed infer_auto
qed

mtheorem ordinal1_th_16:
  "X \<subseteq> A \<and> X \<noteq> {} \<longrightarrow> (\<exists>C : Ordinal. C in X \<and> (\<forall>B : Ordinal. B in X \<longrightarrow> C \<subseteq> B))"
proof (intro impI, elim conjE)
  let ?a = "the Element-of X"
  assume A1:"X \<subseteq> A" and A2:"X \<noteq> {}"
  have "?a in X" using A2 Element_of_rule2 by infer_auto
  then obtain Y where [ty]:"Y is set" and
  A3:"Y in X" and
  A4:"\<not> (\<exists>a : object. a in X \<and> a in Y)" using tarski_th_3[of _ X] by infer_auto
  have "Y in A" using A1 A3 tarski_def_3 by infer_auto
  hence "Y is Ordinal" using ordinal1_th_9[of A Y] by infer_auto
  then obtain C where [ty]:"C is Ordinal" and
  A5:"C = Y" by infer_auto
  show "\<exists>C : Ordinal. C in X \<and> (\<forall>B : Ordinal. B in X \<longrightarrow> C \<subseteq> B)"
  proof (intro bexI[of _ C] conjI ballI impI)
    show "C in X" using A3 A5 by infer_auto
    fix B
    assume [ty]:"B is Ordinal"
    assume "B in X"
    hence "\<not> B in C" using A4 A5 by infer_auto
    hence "B = C \<or> C in B" using ordinal1_th_10 by infer_auto
    thus "C \<subseteq> B" using ordinal1_def_2E[of B,simplified] tarski_def_3_reflexive by infer_auto
  qed infer_auto
qed

mtheorem ordinal1_th_17:
  "A in B \<longleftrightarrow> succ A \<subseteq> B"
proof(rule iffI3)
  show "A in B \<longrightarrow> succ A c= B"
  proof
    assume
A1: "A in B"
    hence "\<forall>a : object.  a in { A } \<longrightarrow> a in B" using tarski_def_1 by auto
    hence
A2: "{ A } c= B" using tarski_def_3 by infer_auto
    have "A c= B" using A1 ordinal1_def_2 by infer_auto
    thus "succ A c= B" using A2 xboole_1_th_8[of "{A}" B A] ordinal1_def_1 by infer_auto
  qed
  assume
A3: "succ A c= B"
  have "A in succ A" using ordinal1_th_2 by infer_auto
  thus "A in B" using A3 tarski_def_3 by infer_auto
qed

theorem ordinal1s:
  "A be Ordinal \<Longrightarrow> B be Ordinal \<Longrightarrow> A c= succ B \<Longrightarrow> A c= B \<or> A=succ B"
proof-
  assume [ty]: "A be Ordinal" "B be Ordinal" and A1:"A c= succ B"
  have "\<not> A c= B implies A=succ B"
  proof
    assume "\<not> A c= B"
    hence "B in A" using ordinal1_th_12[of B A] by infer_auto
    hence "succ B c= A" using ordinal1_th_17 by infer_auto
    thus "A = succ B" using A1 xboole_0_def_10 by infer_auto
  qed
  thus "A c= B \<or> A=succ B" by auto
qed infer_auto

mtheorem ordinal1_th_18:
  "A in succ B iff A c= B"
proof(rule iffI3)
  show "A in succ B implies A c= B"
  proof
    assume "A in succ B"
    hence "A in B or A in { B }" using xboole_0_def_3 ordinal1_def_1 by infer_auto
    hence "A c= B or A = B" using ordinal1_def_2 tarski_def_1 by infer_auto
    thus "A c= B" using xboole_0_def_10 by infer_auto
  qed
  assume
A1: "A c= B"
  show "A in succ B"
  proof(rule ccontr)  
    assume "not A in succ B"
    hence "A = succ B or succ B in A" using ordinal1_th_10 by infer_auto
    hence "A = succ B or succ B c= A" using ordinal1_def_2 by infer_auto
    hence A2: "succ B c= B" using A1 xboole_1_th_1[of B]  by infer_auto
      
    have "B in succ B" using ordinal1_th_2 by infer_auto
    hence "B c= succ B" using ordinal1_def_2 by infer_auto
    hence "succ B = B" using A2 xboole_0_def_10 by infer_auto
    thus "False" using ordinal1_th_5 by inst_nopass_auto
  qed
qed    
  
theorem ordinal1_sch_1:
  assumes A1: "ex A st P(A)"
  shows "ex A st P(A) \<and> (\<forall>B. P(B) \<longrightarrow> A c= B)"
proof -
  obtain A where [ty]: "A is Ordinal" and
  A2: "P(A)" using A1 by infer_auto
  let ?R = "\<lambda>x. ex B st x = B \<and> P(B)"
  obtain X where [ty]: "X is set" and
  A3: "for x being object holds x in X \<longleftrightarrow> x in succ A \<and> ?R(x)"
    using xboole_0_sch_1[of "succ A" ?R] by infer_auto
  hence "\<forall>a : object.  a in X \<longrightarrow> a in succ A" by infer_auto
  hence A4: "X c= succ A" by (intro tarski_def_3[THEN iffD2]) infer_auto
  have [ty]: "(succ A) is ordinal" by infer_auto
  have "A in succ A" using ordinal1_th_2 by infer_auto
  hence "X \<noteq> {}" using A2 A3[THEN bspec,of A] xb1 by infer_auto
  then obtain C where [ty]: "C is ordinal" "C is set" and
  A5: "C in X" and
  A6: "for B st B in X holds C c= B" using ordinal1_th_16[of _ X,OF _ _ A4,simplified] by infer_auto
  have [ty]: "C is number" using ordinal1_def_4 by infer_simp
  have "C in succ A" using A3 A5 by infer_auto
  hence A7: "C c= succ A" using ordinal1_def_2E by infer_auto
  show ?thesis
  proof (intro bexI[of _ C] conjI ballI impI)
    have "ex B st C = B \<and> P(B)" using A3 A5 by infer_auto
    thus "P(C)" by infer_auto
    fix B assume [ty]: "B is Ordinal"
    assume A8: "P(B)"
    show "C c= B" proof (rule ccontr)
      assume A9: "\<not>C c= B"
      hence " B c= C" " B\<noteq>C" using ordinal1_def_5c xboole_0_def_10 by infer_auto
      hence "B c< C" using xboole_0_def_8 by infer_auto
      hence "B in C" using ordinal1_th_7 by infer_auto
      hence "B in X" unfolding A3[THEN bspec,of B,simplified] using A8 tarski_def_3E A7 by infer_auto
      thus False using A6 A9 by infer_auto
    qed
  qed infer_auto
qed

  (*::$N Transfinite induction*)
theorem ordinal1_sch_2:
  assumes A1:"for A st for C st C in A holds P(C) holds P(A)"
  shows "\<forall>A. P(A)"
proof
  let ?R = "\<lambda> x. ex B st x=B \<and> P(B)"
  fix A assume [ty]:"A is Ordinal"
  let ?Y = "succ A"
  obtain Z where
    [ty]:"Z be set" and
A2: "for x being object holds x in Z \<longleftrightarrow> x in ?Y \<and> ?R(x)" using xboole_0_sch_1[of ?Y ?R] by infer_auto
   have "?Y be Ordinal" by infer_auto
  have "?Y \\ Z \<noteq> {} \<longrightarrow> False"
   proof
    have B1:"?Y \\ Z \<subseteq> ?Y" using tarski_def_3 xboole_0_def_5 by infer_auto
    assume "?Y \\ Z \<noteq> {}"
    then obtain C where
    [ty]:"C be Ordinal" and
A3: "C in ?Y \\ Z" and
A4: "for B st B in ?Y \\ Z holds C c= B" using ordinal1_th_16[of ?Y "?Y \\ Z"] B1 by infer_auto
    have "for B st B in C holds P(B)"
      proof(standard,standard)
         fix B assume [ty]:"B be Ordinal" and
A5:   "B in C"
      have "C in ?Y" using A3 B1 tarski_def_3E by infer_auto
      hence
A6:   "C c= ?Y" using ordinal1_def_2 by infer_auto
      have "not B in Z \<longrightarrow> False"
      proof
        assume "not B in Z"
        then have "B in ?Y \\ Z" using A5 A6 xboole_0_def_5 tarski_def_3E[OF _ _ A6] by infer_auto
        then have
A7:     "C c= B" using A4 by infer_auto
        have "C \<noteq> B" using A5 prefix_in_irreflexive by infer_auto
        hence "C \<subset> B" using A7 xboole_0_def_8 by infer_auto
        thus False using A5 ordinal1_th_7 prefix_in_asymmetry[of C B] by infer_auto
      qed
      then have "ex B9 being Ordinal st B = B9 \<and> P(B9)" using A2 by auto
      thus "P(B)" by auto
    qed infer_auto
    hence
A8: "P(C)" using A1 by infer_auto
    have A9: "not C in Z" using A3 xboole_0_def_5 by infer_auto
    hence "C in succ A" using A3 xboole_0_def_5 by infer_auto
    thus False using A2 A8 A9 by infer_auto
  qed infer_auto
  hence "?Y\\Z = {}" by auto
  hence "not A in ?Y \<or> A in Z" using xboole_0_def_5 xboole_0_def_1 by inst_nopass_auto
  hence "ex B st A = B \<and> P(B)" using A2 ordinal1_th_2 by infer_auto
  thus "P(A)" by auto
qed infer_auto

mtheorem ordinal1_th_24:"\<forall>A : Ordinal. A is limit_ordinal \<longleftrightarrow> (\<forall>C : ordinal \<bar> set. C in A \<longrightarrow> succ C in A)"
proof (standard,standard)
  fix A assume [ty]:"A is Ordinal"
  show "A is limit_ordinal \<Longrightarrow> (\<forall>C : Ordinal. C in A \<longrightarrow> succ C in A)"
  proof (standard, standard)
    assume "A is limit_ordinal"
    hence A1:"A = union A" using ordinal1_def_6E by infer_auto
    fix C assume [ty]:"C is Ordinal"
    assume "C in A"
    then obtain z where [ty]:"z is set" and
    A2:"C in z" and
    A3:"z in A" using A1 tarski_def_4[of A C] by infer_auto
    have "\<forall>b : object. b in {C} \<longrightarrow> b in z" using A2 tarski_def_1 by infer_auto
    hence A4:"{C} \<subseteq> z" using tarski_def_3I by infer_auto
    have A5[ty]:"z is Ordinal" using ordinal1_th_9[OF _ _ A3] by infer_auto
    hence "C \<subseteq> z" using A2 ordinal1_def_2E by infer_auto
    hence "succ C \<subseteq> z" using xboole_1_th_8[OF _ _ _ _ A4,of C] ordinal1_def_1 by infer_auto
    hence "succ C = z \<or> succ C \<subset> z" using xboole_0_def_8 by infer_auto
    hence A6:"succ C = z \<or> succ C in z" using A5 ordinal1_th_7 by infer_auto
    have "z \<subseteq> A" using A3 ordinal1_def_2 by infer_auto
    thus "succ C in A" using A3 A6 ordinal1_th_6[of _ "succ C" A] by infer_auto
  qed infer_auto
  assume A7:"\<forall>C : Ordinal. C in A \<longrightarrow> succ C in A"
  {
    fix a
    have [ty]:"a is set" using tarski_0_1 by infer_auto
    assume A8:"a in A"
    have "a is ordinal \<bar> set" using ordinal1_th_9[OF _ _ A8] by infer_auto
    hence A9:"succ a in A" using A7 A8 by infer_auto
    have "a in succ a" using ordinal1_th_2 by infer_auto
    hence "a in union A" using A9 tarski_def_4[THEN iffD2,of A a,OF _ bexI] by infer_auto
  }
  hence A10:"A \<subseteq> union A" using tarski_def_3I by infer_auto
  {
    fix a
    assume "a in union A"
    then obtain z where [ty]:"z is set" and
    A11:"a in z" and
    A12:"z in A" using tarski_def_4 by infer_auto
    have "z \<subseteq> A" using A12 ordinal1_def_2 by infer_auto
    hence "a in A" using A11 tarski_def_3E by infer_auto
  }
  hence "union A \<subseteq> A" using tarski_def_3I by infer_auto
  hence "A = union A" using A10 xboole_0_def_10 by infer_auto
  thus "A is limit_ordinal" using ordinal1_def_6I by infer_auto
qed infer_auto

text_raw {*\DefineSnippet{ordinal1_th_24A}{*}
mtheorem ordinal1_th_24A:
  "\<forall>A : Ordinal. 
     A is limit_ordinal \<longleftrightarrow> (for C be set st C in A holds succ C in A)"
text_raw {*}%EndSnippet*}
proof(standard, rule iffI3)
  fix A assume [ty]:"A is Ordinal"
  show "A is limit_ordinal \<longrightarrow> (for C be set st C in A holds succ C in A)"
  proof(standard,standard,standard)
    fix C
    assume A1: "A is limit_ordinal" and [ty]: "C is set" and A2: "C in A"
    hence "C is Ordinal" using ordinal1_th_9[of A] by infer_auto
    thus "succ C in A" using A1 A2 ordinal1_th_24[of A,THEN iffD1] by infer_auto
  qed infer_auto
  assume "for C be set st C in A holds succ C in A"
  thus "A is limit_ordinal" using ordinal1_th_24 by infer_auto
qed infer_auto



mtheorem ordinal1_th_29:
  "not (A is limit_ordinal) \<longleftrightarrow> (ex B st A = succ B)"
proof(rule iffI3)
  show "not A is limit_ordinal \<longrightarrow> (ex B st A = succ B)"
  proof
    assume "not A is limit_ordinal"
    then obtain B where
      T[ty]:"B be Ordinal" and
A1: "B in A" and
A2: "not succ B in A" using ordinal1_th_24 by infer_auto
    show "ex B st A=succ B"
      proof(intro bexI[of _ B])
        have "A\<noteq>succ B \<longrightarrow> False"
          proof
            assume
A3:           "A \<noteq> succ B"
            have "succ B \<subseteq> A" using A1 ordinal1_th_17 by infer_auto
            hence "succ B \<subset> A" using A3 xboole_0_def_8 by infer_auto
            thus False using A2 ordinal1_th_7 by infer_auto
          qed
         thus "A=succ B" by auto
       qed infer_auto
     qed
  assume "ex B st A=succ B"
  then obtain B where
    [ty]: "B be Ordinal" and
    A4: "A = succ B" by auto
  have "B in A \<and> \<not> succ B in A" using A4 ordinal1_th_2 prefix_in_irreflexive by infer_auto
  thus "not (A is limit_ordinal)" using ordinal1_th_24 by infer_auto
qed


mdef ordinal1_def_9 ("On _") where
  "func On X \<rightarrow> set means
     (\<lambda>it. for x being object holds x in it \<longleftrightarrow> x in X \<and> x is Ordinal)"
proof -
  show "\<exists>x : set. \<forall>xa : object. xa in x \<longleftrightarrow> xa in X \<and> xa is ordinal \<bar> set"
    using xboole_0_sch_1 by infer_auto
  show "\<And>x y. x is set \<Longrightarrow>
           y is set \<Longrightarrow>
           \<forall>xa : object. xa in x \<longleftrightarrow> xa in X \<and> xa is ordinal \<bar> set \<Longrightarrow>
           \<forall>x : object. x in y \<longleftrightarrow> x in X \<and> x is ordinal \<bar> set \<Longrightarrow> x = y"
    by (intro xboole_0_sch_2[of _ _ "\<lambda>xa. xa in X \<and> xa is Ordinal"]) infer_auto
qed infer_auto

text_raw {*\DefineSnippet{ordinal1_th_32}{*}
mtheorem ordinal1_th_32:
  "\<forall>D : Ordinal.  ex A be Ordinal st D in A \<and> A is limit_ordinal"
text_raw {*}%EndSnippet*}

proof
  fix D
  assume [ty]: "D is Ordinal"
  have dset: "D is set" by infer_auto
  obtain Field where [ty]:"Field is set" and
  A1:"D in Field" and
  A2:"\<forall>X : set. \<forall>Y : set. X in Field \<and> Y \<subseteq> X \<longrightarrow> Y in Field" and
  A3:"\<forall>X : set. X in Field \<longrightarrow> bool X in Field"
  "\<forall>X : set. X \<subseteq> Field \<longrightarrow> X,Field areequipotent \<or> X in Field"
    thm ty
    using zfmisc_1_th_112[of D,OF dset,THEN bexE,OF set_exists,of thesis] by blast
  have C: "\<forall>X : set. (X in On Field) \<longrightarrow> X is Ordinal \<and> X \<subseteq> On Field"
  proof (standard,standard,standard)
    fix X
    assume [ty]:"X is set"
    let ?A = X
    assume A4:"X in On Field"
    hence [ty]:"?A is Ordinal" using ordinal1_def_9 by infer_auto
    have A5:"?A in Field" using A4 ordinal1_def_9 by infer_auto
    show "X is Ordinal" using A4 ordinal1_def_9 by infer_auto
    show "X \<subseteq> On Field"
    proof(standard,auto)
      fix y
      assume A6:"y in X"
      have B: "y in ?A" using A6 by infer_auto
      let ?B = y
      have [ty]:"?B is Ordinal" using ordinal1_th_9[OF _ _ B] by infer_auto
      have "?B \<subseteq> ?A" using A6 ordinal1_def_2 by infer_auto
      hence "?B in Field" using A2[THEN bspec,THEN bspec,of X _] A5 by infer_auto
      thus "y in On Field" using ordinal1_def_9 by infer_auto
    qed infer_auto
  qed infer_auto
  let ?ON = "On Field"
  show "\<exists>A : ordinal \<bar> set. D in A \<and> A is limit_ordinal"
  proof (intro bexI[of _ ?ON] conjI)
    have [ty]:"?ON is epsilon-transitive \<bar> epsilon-connected \<bar> set" using C ordinal1_th_15 by infer_auto
    show "D in ?ON" using A1 ordinal1_def_9 by infer_auto
    have "\<forall>A : ordinal \<bar> set. A in ?ON \<longrightarrow> succ A in ?ON"
    proof (standard,standard)
      fix A assume [ty]: "A is Ordinal"
      have A7:"succ A \<subseteq> bool A"
      proof(standard,auto)
        fix x
        have [ty]:"x is set" using tarski_0_1 by infer_auto
        assume "x in succ A"
        hence "x in A \<or> x = A" using ordinal1_th_4 by infer_auto
        hence "x \<subseteq> A" using ordinal1_def_2 tarski_def_3_reflexive by infer_auto
        thus "x in bool A" using zfmisc_1_def_1 by infer_auto
      qed infer_auto
      assume "A in ?ON"
      hence "A in Field" using ordinal1_def_9 by infer_auto
      hence "bool A in Field" using A3 by infer_auto
      hence "succ A in Field" using A2[THEN bspec,THEN bspec,of _ "succ A"] A7 by infer_auto
      thus "succ A in ?ON" by (intro ordinal1_def_9[THEN iffD2]) infer_auto
    qed infer_auto
    thus "?ON is limit_ordinal" using ordinal1_th_24 by infer_auto
    thus "?ON is Ordinal" by infer_auto
  qed infer_auto
qed infer_auto

text_raw {*\DefineSnippet{omega}{*}
mdef ordinal1_def_11 ("omega") where
  "func omega \<rightarrow> set means (\<lambda>it.
  0\<^sub>\<S> in it \<and> it be limit_ordinal \<and> it be Ordinal \<and> 
   (\<forall>A:Ordinal. 0\<^sub>\<S> in A \<and> A is limit_ordinal \<longrightarrow> it \<subseteq> A))"
text_raw {*}%EndSnippet*}
proof -
  have A: "{} is ordinal" using Lm1 by (intro ordinal1_def_4I) infer_auto
  show "\<exists>A : set. {} in A \<and>
              A is limit_ordinal \<and>
              A is Ordinal \<and> (\<forall>B : ordinal \<bar> set. {} in B \<and> B is limit_ordinal \<longrightarrow> A \<subseteq> B)"
    using ordinal1_sch_1[OF ordinal1_th_32,OF A] by infer_auto
  show "\<And>x y. x is set \<Longrightarrow> y is set \<Longrightarrow>
       {} in x \<and> x is limit_ordinal \<and>
       x is Ordinal \<and> (\<forall>A : ordinal \<bar> set. {} in A \<and> A is limit_ordinal \<longrightarrow> x \<subseteq> A) \<Longrightarrow>
       {} in y \<and> y is limit_ordinal \<and>
       y is Ordinal \<and> (\<forall>A : ordinal \<bar> set. {} in A \<and> A is limit_ordinal \<longrightarrow> y \<subseteq> A) \<Longrightarrow> x = y"
    proof (elim conjE)
      fix x y
      assume [ty]: "x is set" "y is set" "x is limit_ordinal" "y is limit_ordinal" "x is Ordinal" "y is Ordinal"
      assume E: "{} in x" "{} in y"
      assume U: "\<forall>A : ordinal \<bar> set. {} in A \<and> A is limit_ordinal \<longrightarrow> x \<subseteq> A"
                "\<forall>A : ordinal \<bar> set. {} in A \<and> A is limit_ordinal \<longrightarrow> y \<subseteq> A"
      have "x c= y \<and> y c= x" using U(1)[THEN bspec,of y,simplified] U(2)[THEN bspec,of x,simplified] E by infer_auto
      thus "x = y" using xboole_0_def_10 by infer_auto
    qed
qed infer_auto

mtheorem
  "cluster omega \<rightarrow> ordinal" 
 using ordinal1_def_11 by infer_auto

mdef ordinal1_def_12 ("natural")where
  "attr natural for object means (\<lambda>A. A in omega)"..

mtheorem
  "cluster omega \<rightarrow> non empty" 
 using ordinal1_def_11 xboole_0_def_1 by infer_auto

abbreviation (input) "NAT \<equiv> omega"


abbreviation "Nat \<equiv> natural \<bar> set"

mtheorem "cluster {} \<rightarrow> Nat"
 using ordinal1_def_11 ordinal1_def_12I by infer_auto
   
mtheorem 
 "cluster  natural \<rightarrow> Element-of NAT for object"
proof(standard,standard,standard)
  fix x 
  assume "x is natural"
  hence "x in NAT" using ordinal1_def_12 by auto
  thus "x is Element-of NAT" using Element_of_rule3 by infer_auto
qed infer_auto

mtheorem
  "cluster \<rightarrow> natural for Element-of NAT"
proof(standard,auto)
  fix x 
  have N: "NAT \<noteq> {}" using xb ordinal1_def_11 by infer_auto
  assume "x is Element-of NAT"
  hence "x in NAT" using N Element_of_rule2[of NAT x] by infer_auto
  thus "x is natural" using ordinal1_def_12 by infer_auto
qed
  
mtheorem
  "cluster natural for set"
proof(standard,standard)
  show "{} is Nat" by infer_auto
qed

mtheorem 
  "cluster natural \<rightarrow> ordinal for Number"
proof(standard,auto)
  fix x assume "x be natural"
  hence "x in omega" using ordinal1_def_12 by auto
  thus "x is ordinal" using ordinal1_th_9[of omega] by infer_auto
qed  

mdef ordinal1_def_16 ("with'_zero")where
  "attr with_zero for set means (\<lambda>IT. {} in IT)"..

mtheorem with_zero_cl:
  "cluster with_zero \<rightarrow> non empty for set"
proof(standard,intro ballI impI)
  fix X assume [ty]: "X be set" "X is with_zero"
  have "{} in X" using ordinal1_def_16 by infer_auto
  thus "X is non empty" using xboole_0_def_1 by infer_auto
qed infer_auto

mtheorem
  "cluster with_zero for set"
proof(standard,standard)
  show "{{}} is with_zero\<bar>set" using ordinal1_def_16 tarski_def_1 by infer_auto
qed

text_raw {*\DefineSnippet{ordinal2_sch_1}{*}
theorem ordinal2_sch_1:
  assumes A1: "P({})"
      and A2: "\<forall>A. P(A) \<longrightarrow> P(succ A)"
      and A3: "\<forall>A. A \<noteq> {} \<and> A is limit_ordinal \<and>
                 (\<forall>B. B in A \<longrightarrow> P(B)) \<longrightarrow> P(A)"
  shows "\<forall>A.  P(A)"
text_raw {*}%EndSnippet*}
proof-
have A4: "for A st for B st B in A holds P(B) holds P(A)"
  proof(standard,standard)
    fix A assume [ty]:"A be Ordinal" and
   A5: "for B st B in A holds P(B)"
    show "P(A)"
    proof(cases "A={}" )
      case True thus "P(A)" using A1 by auto
    next
      case C1: False
         show "P(A)"
         proof(cases "(\<forall>B.  A \<noteq> succ B)")
           case True
              hence "A is limit_ordinal" using ordinal1_th_29[of A] by infer_auto
              thus "P(A)" using C1 A3 A5 by infer_auto
           next
           case C2:False
              then obtain B where
              [ty]: "B is Ordinal" and
              A7:   "A = succ B" by auto
              have "B in A" using A7 ordinal1_def_1[of B] xboole_0_def_3 tarski_def_1 by infer_auto
              thus "P(A)" using A2 A5 A7 by infer_auto
         qed
       qed
 qed infer_auto
 thus "\<forall>A.  P(A)" using ordinal1_sch_2 by simp
qed


text_raw {*\DefineSnippet{OmegaInd}{*}
theorem ordinal_2_sch_19:
  assumes [ty]: "a is Nat"
    and A1: "P({})"
    and A2: "\<forall>n : Nat. P(n) \<longrightarrow> P(succ n)"
  shows "P(a)"
text_raw {*}%EndSnippet*}
proof-
  have [ty]:"a is set" using all_set by auto
  let ?P= "\<lambda>x . x is natural \<longrightarrow> P(x)"
  have
A3:"for A st ?P(A) holds ?P(succ A)"
  proof(standard,standard)
    fix A assume [ty]:"A be Ordinal" and
A4: "?P(A)"
    show "?P(succ A)"
    proof
      have "omega is set" by infer_auto
         assume "(succ A) is natural"
      hence
A5:     "(succ A) in omega" using ordinal1_def_12 by auto
       have B1: "A in succ A" using xboole_0_def_3 tarski_def_1 ordinal1_def_1[of A] by infer_auto
       hence "A in omega" using A5 prefix_in_asymmetry[of A "succ A"] A5 ordinal1_th_6[of "succ A" A omega] by infer_auto
      thus "P(succ A)" using A2 A4 ordinal1_def_12[of A] by infer_auto
    qed
  qed infer_auto
  have
A6: "for A st A \<noteq> {} \<and> A is limit_ordinal \<and> (for B st B in A holds ?P(B))
           holds ?P(A)"
  proof(intro ballI, rule impI)
    fix A
    assume
    [ty]: "A is Ordinal" and
     A7:"A \<noteq> {} \<and> A is limit_ordinal \<and> (for B st B in A holds ?P(B))"
    have "{} c= A" using tarski_def_3I xb by infer_auto
    hence "{} \<subset> A" using A7 xboole_0_def_8 by infer_auto
    hence
A8: "{} in A" using ordinal1_th_7[of "{}" A] Lm1 by infer_auto
    have
A9: "not A in A" using prefix_in_irreflexive by auto
    have "omega c= A" using A8 A7 ordinal1_def_11 by infer_auto
    hence "not A in omega" using A9 tarski_def_3E[of omega A] by infer_auto
    thus "?P(A)" using ordinal1_def_12 by auto
  qed infer_auto
  have A10: "?P({})" using A1 by auto
   have "a is Ordinal"  by infer_auto
   have "\<forall>A.  ?P(A)" using ordinal2_sch_1[OF A10 A3 A6] by auto
 thus "P(a)" by infer_auto
qed

end