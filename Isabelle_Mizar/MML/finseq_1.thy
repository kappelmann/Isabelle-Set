theory finseq_1
  imports nat_1

begin

mdef finseq_1_def_1 ("Seg _" [120] 120) where
  mlet "n be Nat"
  "func Seg n \<rightarrow> set equals
     { i where i be Element-of NAT: 1\<^sub>\<S> c= i \<and> i c= n }"
    by mauto

reserve n,i for Nat

mtheorem finseq_1_th_1:
  "i in Seg n \<longleftrightarrow> (1\<^sub>\<S> c= i \<and> i c= n)"
proof(rule iffI3)
  show "i in Seg n \<longrightarrow> 1\<^sub>\<S> c= i \<and> i c= n"
  proof
    assume "i in Seg n"
    hence B1: "i in {x where x be Element-of NAT: 1\<^sub>\<S> c= x \<and> x c= n}" using finseq_1_def_1 by mauto
    have J: " ex x be Element-of NAT st i = x \<and> 1\<^sub>\<S> c= x \<and> x c= n" using Fraenkel_A1_ex[OF _ _ B1] by mauto
     obtain x where
      [ty]: "x be Element-of NAT"and
     A2: "i = x \<and> 1\<^sub>\<S> c= x \<and> x c= n" using bexE[OF J,of thesis] by auto
     thus "1\<^sub>\<S> c= i \<and> i c= n" by mauto
   qed
  have [ty]:"i be Element-of NAT" by mauto
  assume "1\<^sub>\<S> c= i \<and> i c= n"
  hence "i in {x where x be Element-of NAT: 1\<^sub>\<S> c= x \<and> x c= n}" using Fraenkel_A1_in[of "Element-of NAT" i
           "\<lambda>x. 1\<^sub>\<S> c= x \<and> x c= n" ] by mauto
  thus "i in Seg n" using finseq_1_def_1 by simp
qed


theorem finseq_1_cl_1:
  "Seg 0\<^sub>\<S> = 0\<^sub>\<S>"
proof(rule ccontr)
  assume "Seg {} \<noteq> {}"
  hence "ex x be object st x in Seg {}" using xboole_0_th_7 by mauto
  then obtain i where
     A1: "i in Seg {}" by auto
     hence B1: "i in {x where x be Element-of NAT: 1\<^sub>\<S> c= x \<and> x c= {}}" using finseq_1_def_1 by mauto
     have J: " ex x be Element-of NAT st i = x \<and> 1\<^sub>\<S> c= x \<and> x c= {}" using Fraenkel_A1_ex[OF _ _ B1] by mauto
     obtain x where
      [ty]: "x be Element-of NAT"and
     A3: "i = x \<and> 1\<^sub>\<S> c= x \<and> x c= {}" using bexE[OF J,of thesis] by auto
     have A4: "{} in x" using A3 one1 by mty auto
     have "{} c= x" using tarski_def_3 xb by mauto
     hence "x={}" using A3 xboole_0_def_10 by mauto    
     thus "False" using  A4 xb by mty auto
qed

theorem finseq_1_cl:
  "n be Element-of NAT \<longrightarrow> Seg n c=  NAT"
proof(standard,standard,auto)
  assume A1[ty]:"n be Element-of NAT"
  fix x
  assume "x in Seg n"
  hence B1: "x in { i where i be Element-of NAT: 1\<^sub>\<S> c= i \<and> i c= n }" using finseq_1_def_1 A1 by mauto
   obtain i where
    T2[ty]:"i be Element-of NAT" and
    A2: "i = x" and
    A3: "1\<^sub>\<S> c= i \<and> i c= n" using Fraenkel_A1_ex[OF _ _ B1] by mauto
  have "NAT is non empty" by mauto
  thus "x in NAT" using A2 Element_of1 by mauto
next show "n is Element-of omega \<Longrightarrow> Seg n is set"
  proof-
    assume [ty]:"n is Element-of omega"
    show "Seg n is set" by mauto
  qed
qed mauto

reserve x for object  
  
mtheorem finseq_1_el:
  "x in Seg n implies x is Nat"
proof  
  have S: "Seg n c= NAT" using finseq_1_cl by mty auto
  assume "x in Seg n"
  hence " x in NAT" using S tarski_def_3E[of "Seg n" NAT] by mty auto
  thus "x is Nat" using ordinal1_def_12 all_set by mty auto 
qed

theorem finseq_1_th_2:
    "Seg 1\<^sub>\<S> = {1\<^sub>\<S>}"
proof(rule xboole_0_def_10I)
  show "Seg 1\<^sub>\<S> \<subseteq> {1\<^sub>\<S>}"
  proof(standard,mauto)
    fix x assume A:"x in Seg 1\<^sub>\<S>"
    hence [ty]:"x is Nat" using finseq_1_el[of "1\<^sub>\<S>"] by auto  
    have "1\<^sub>\<S> c= x & x c= 1\<^sub>\<S>" using finseq_1_th_1 A by mty auto 
    hence "1\<^sub>\<S>=x" using xboole_0_def_10 by auto
    thus "x in {1\<^sub>\<S>}" using tarski_def_1 by auto     
    qed
    show "{1\<^sub>\<S>} \<subseteq>  Seg 1\<^sub>\<S>"
    proof(standard,mauto)
      fix x assume "x in {1\<^sub>\<S>}"
      hence "1\<^sub>\<S> = x" "1\<^sub>\<S> c= 1\<^sub>\<S>" using tarski_def_1 xboole_0_def_10E by mty auto
      thus "x in Seg 1\<^sub>\<S>" using finseq_1_th_1[of "1\<^sub>\<S>" "1\<^sub>\<S>"] by mty auto 
    qed
qed mauto

mtheorem finseq_1_th_5:
  "n c= m iff Seg n c= Seg m"
proof(rule iffI3)
  show "n \<subseteq> m implies Seg n \<subseteq> Seg m"
  proof(standard,standard, auto)
    fix x assume A:"n \<subseteq> m" "x in Seg n"
    hence [ty]:"x be Nat" using finseq_1_el[of n x] by mauto  
    have B: "1\<^sub>\<S> \<subseteq> x & x \<subseteq> n" using finseq_1_th_1 A by mty auto 
    hence "x \<subseteq> m" using A xboole_1_th_1[of m n x] by auto
    thus "x in Seg m" using B finseq_1_th_1[of m x] by mty auto  
  qed
  assume A: "Seg n c= Seg m"
  have E:"{} c= n" using xb tarski_def_3I by mty auto 
  have "n<>{} implies n \<subseteq> m"
  proof 
    assume "n<>{}"
    hence "not n c= {}" using E xboole_0_def_10[of n "{}"] by mty auto 
    hence "{} in n" using  ordinal1_th_12[of "{}" n] E by mty auto  
    hence "1\<^sub>\<S> c= n" "n \<subseteq>n" using one1 xboole_0_def_10[of n n] by mty auto
    hence "n in Seg n" using finseq_1_th_1 by auto
    hence "n in Seg m" using A tarski_def_3 by auto
    thus "n \<subseteq> m" using finseq_1_th_1 by auto
    qed
  thus "n c= m" using xb tarski_def_3 by auto   
qed  

mtheorem finseq_1_th_6:
  "Seg n = Seg m implies n=m"
proof
  assume "Seg n = Seg m"
  hence "Seg n c= Seg m" " Seg m c= Seg n" using xboole_0_def_10 by auto
  hence "n c= m" "m c= n" using finseq_1_th_5 by auto
  thus "n=m" using xboole_0_def_10 by auto
qed

mtheorem finseq_1_th_7:
  "n \<subseteq> m implies Seg n \<inter> Seg m = Seg n"
proof(standard,rule xboole_0_def_10I,auto)
  assume A1: "n c= m"
  show "Seg n \<inter> Seg m \<subseteq> Seg n" using xboole_0_def_4 tarski_def_3I by auto
  show "Seg n \<subseteq> Seg n \<inter> Seg m"
  proof(standard,auto)
    fix x assume A2:"x in Seg n"
    hence [ty]:"x is Nat" using finseq_1_el[of n x] by auto
    have A3: "1\<^sub>\<S> c= x & x c= n" using finseq_1_th_1 A2 by mty auto
    hence "x c= m" using xboole_1_th_1[of m n] A1 by mty auto
    hence "x in Seg m" using A3 finseq_1_th_1 by auto    
    thus "x in Seg n \<inter>Seg m" using A2 xboole_0_def_4 by auto    
  qed
qed 

mtheorem finseq_1_th_60a:
  "n in Seg m implies n in Seg (k +\<^sub>\<S>\<^sup>\<nat> m)"
proof
  assume "n in Seg m"
  hence A1: "1\<^sub>\<S> c= n & n c= m" using finseq_1_th_1 by auto
  have "m c= k +\<^sub>\<S>\<^sup>\<nat> m" using Add_10 Add_6 by auto
  hence "n c= k +\<^sub>\<S>\<^sup>\<nat> m" using xboole_1_th_1[of _ m n] A1 by mty auto
  thus "n in Seg (k +\<^sub>\<S>\<^sup>\<nat> m)" using A1 finseq_1_th_1 by auto
qed

mtheorem finseq_1_th_60:
  "n in Seg m implies (k +\<^sub>\<S>\<^sup>\<nat> n) in Seg (k +\<^sub>\<S>\<^sup>\<nat> m)"
proof
  assume "n in Seg m"
  hence A1: "1\<^sub>\<S> c= n & n c= m" using finseq_1_th_1 by auto
  have "n c= k +\<^sub>\<S>\<^sup>\<nat> n" using Add_10 Add_6 by auto
  hence A2: "1\<^sub>\<S> c= k +\<^sub>\<S>\<^sup>\<nat> n" using xboole_1_th_1[of _ n "1\<^sub>\<S>"] A1 by mty auto
  have "k +\<^sub>\<S>\<^sup>\<nat> n c= k +\<^sub>\<S>\<^sup>\<nat> m" using A1 Add_13[of _ m n] by auto
  thus "(k+\<^sub>\<S>\<^sup>\<nat> n) in Seg (k +\<^sub>\<S>\<^sup>\<nat> m)" using A2 finseq_1_th_1 by auto
qed

mdef finseq_1_def_2 ("FinSequence-like")where
 "attr FinSequence-like for Relation means (\<lambda>F. ex n be Element-of NAT st dom F = Seg n)"..

mtheorem finseq_1_cl_2:
  "cluster empty \<rightarrow> FinSequence-like for Relation"
proof(standard,standard,standard,standard)
  fix X assume A1[ty]: "X be Relation" "X is empty"
  have "dom X is empty" by mauto
  hence H:"dom X={}" using xboole_0_lm_1 by mauto
  hence H:"dom X=Seg {}" using finseq_1_cl_1 by auto
  have "{} is Element-of NAT" by mauto
  thus "ex n be Element-of NAT st dom X=Seg n" using H by auto
qed mauto

  
mtheorem
  "cluster FinSequence-like for Function"
proof(standard,standard)
  show "{} is FinSequence-like \<bar> Function" by mauto
qed

abbreviation
  "FinSequence \<equiv> FinSequence-like\<bar> Function"
  
mdef finseq_1_def_3 ("len _" [150]150) where
  mlet "f be FinSequence"  
  "func len f \<rightarrow> Element-of NAT means
      (\<lambda>it. dom f = Seg it)"
proof-
  show "\<exists>x : Element-of NAT. dom f = Seg x" using finseq_1_def_2E by auto
  fix x y assume [ty]:"x be Element-of NAT" "y be Element-of NAT"
  assume "dom f = Seg x" "dom f = Seg y"
  thus "x=y" using finseq_1_th_6[of x y] by mty auto  
qed mauto 

reserve p,q,r for FinSequence 

mtheorem finseq_1_th_14:
  "len p = len q & (for n st 1\<^sub>\<S> c= n & n c= len p holds p .n = q .n) implies p=q"
proof
  assume A1: "len p = len q & (for n st 1\<^sub>\<S> c= n & n c= len p holds p .n = q .n)"
  have A2: "dom p = Seg len p" "dom q=Seg len q" using finseq_1_def_3 by auto
  have "for x st x in dom p holds p .x = q .x"
  proof(standard,standard)
    fix x assume A3: "x in dom p"
    hence [ty]:"x is Nat" using finseq_1_el[of "len p"] A2 by mty auto
    have "1\<^sub>\<S> c= x & x c= len p" using A1 A2 A3 finseq_1_th_1 by auto
    thus "p .x = q .x" using A1 by mty auto
  qed mauto
  thus "p=q" using funct_1_th_2[of q p] A1 A2 by mty auto
qed

mdef finseq_1_def_4 ("FinSequence-of _")  where
  mlet "D be object"
  "mode FinSequence-of D \<rightarrow> FinSequence means
     (\<lambda>it. rng it c= D)" 
proof-
  have [ty]: "D be set" using all_set by simp
  have K: "{} c= D" using xb tarski_def_3I by mty auto
  have "{} is empty" by mauto
  hence A1[ty]: "{} be FinSequence" by mauto
  have "rng {} is empty" by mauto
  hence "rng {}={}" using xboole_0_lm_1 by mauto
  hence "rng {} c= D" using K by auto
  thus "ex x be FinSequence st rng x \<subseteq> D" using bexI[of _ "{}" FinSequence] by auto
qed mauto

mdef finseq_1_def_5 ("<* _ *>") where
  mlet "x be object"
  "func <* x *> \<rightarrow> FinSequence equals
    {[1\<^sub>\<S>,x]}"
proof-
  have "dom {[1\<^sub>\<S>,x]} = {1\<^sub>\<S>}" using relat_1_th_3 by auto
  hence "dom {[1\<^sub>\<S>,x]}= Seg 1\<^sub>\<S>" using finseq_1_th_2 by auto
  thus "{[1\<^sub>\<S>,x]} is FinSequence" using finseq_1_def_2 bexI by mty auto    
qed 

mtheorem finseq_1_def_8:
  mlet "x be object"
 "redefine func <* x *> \<rightarrow> Function means
    (\<lambda>it . dom it = Seg 1\<^sub>\<S> & it. 1\<^sub>\<S> =x)"
proof(standard,rule iffI3)
  fix f assume [ty]:"f be Function"
  have H1: "[1\<^sub>\<S>,x] in <*x*>" "dom (<* x *>) = Seg 1\<^sub>\<S>" 
     using tarski_def_1  finseq_1_def_5[of x] finseq_1_th_2 relat_1_th_3 by mty auto
  hence H2: "<* x*>. 1\<^sub>\<S> = x" using funct_1_th_1 by auto
  show "f = <* x *> \<longrightarrow> dom f = Seg 1\<^sub>\<S> \<and> f . 1\<^sub>\<S> = x" using H1 H2 by auto
  assume A1: "dom f = Seg 1\<^sub>\<S> \<and> f . 1\<^sub>\<S> = x"
  have "for a being object st a in dom f holds f .a = (<*x *>) .a"
    using H2  A1 finseq_1_th_2 tarski_def_1 by mty auto
  thus "f = <* x *>" using funct_1_th_2[of f "<*x *>"] A1 H1  by mty auto
qed mauto

mtheorem 
  mlet "d be non empty\<bar>set", "x be Element-of d"
  "cluster <* x *> \<rightarrow> FinSequence-of d"
proof
  let ?X="<* x *>"
  have "rng ?X c= d"
  proof(intro tarski_def_3I ballI impI)
    fix y assume "y in rng ?X"
    then obtain i where
        A2:"i in dom ?X & y = ?X. i" using funct_1_def_3 by auto
    hence "i = 1\<^sub>\<S>" using finseq_1_th_2 finseq_1_def_8 tarski_def_1[of "1\<^sub>\<S>" i] by auto 
    hence "y = x" "x in d" using A2 finseq_1_def_8 Element(7) by mty auto
    thus "y in d" by simp
  qed mauto
  thus "?X is FinSequence-of d" using finseq_1_def_4 by auto
qed

mdef finseq_1_def_6 ("<*>") where
  "func <*> \<rightarrow> FinSequence equals {}"
proof-
  show "{} is FinSequence" by mauto
qed

mlemma finseq_1_lm_1:
  "<*x*> \<noteq> <*>" using finseq_1_def_5[of x] finseq_1_def_6 tarski_def_1[of "[1\<^sub>\<S> ,x]" "[1\<^sub>\<S> ,x]" ] xb by mty auto

mtheorem finseq_1_def_6_p:
  "p =<*> iff len p = {}"
proof
  assume "p=<*>"
  hence "dom p is empty " using finseq_1_def_6 relat_1_cl_20 by auto
  hence "dom p =Seg {}" using xboole_0_lm_1 finseq_1_cl_1 by mty auto
  thus "len p={}" using finseq_1_def_3_uniq[of p "{}"] by mty auto
next 
  assume "len p={}"
  hence "dom p = {}" using finseq_1_def_3 finseq_1_cl_1 by auto
  thus "p=<*>" using finseq_1_def_6 relat_1_th_41 by auto
qed
   

ML {* @{term "x ^ y"}*}

no_notation power ( infixr "^" 80)

mdef finseq_1_def_7 ("_ ^ _") where
  mlet "p be FinSequence","q be FinSequence"
  "func p^q \<rightarrow> FinSequence means
  (\<lambda> it. dom it = Seg ((len p) +\<^sub>\<S>\<^sup>\<nat> (len q)) & 
     (for k st k in dom p holds it .k = p .k) &
     (for k st k in dom q holds it.((len p) +\<^sub>\<S>\<^sup>\<nat> k) = q .k))"
proof-
  let ?P = "\<lambda> k it. (k in dom p implies p .k = it) &
                    (for n st k = (len p)+\<^sub>\<S>\<^sup>\<nat> n & n in dom q holds q .n = it)"
  let ?L="(len p) +\<^sub>\<S>\<^sup>\<nat> (len q)"
  let ?X = "Seg (?L)"
  have A1:"Seg len p= dom p" "Seg len q=dom q" using finseq_1_def_3 by mty auto
  have P1:"for x being object st x in ?X holds (ex y being object st ?P(x,y))"
  proof(standard,standard)
    fix x assume A: "x in ?X"
    hence [ty]: "x is Nat" using finseq_1_el[of "?L"] by auto
    hence A2: "1\<^sub>\<S> c= x & x c= ?L" using finseq_1_th_1 A by mty auto
    show "ex y being object st ?P(x,y)"
    proof(cases "x c= len p")
      case T: True
        show "ex y being object st ?P(x,y)"
        proof(rule bexI[of _ "p. x"],rule conjI,simp,rule ballI,rule impI)
          fix n assume [ty]:"n be Nat" and A3:"x = (len p) +\<^sub>\<S>\<^sup>\<nat> n \<and> n in dom q"
          hence "1\<^sub>\<S> c= n" using finseq_1_th_1[of "len q" n] A1 by mty auto
          hence "n\<noteq> {}" using one1 xb by mty auto
          hence "len p in x" using Add_8[of x "len p"] bexI[of _ n Nat] A3 by mty auto
          thus "q .n = p .x" using T ordinal1_th_1 by auto
        qed mauto
      next
        case F: False
          hence "len p in x" using ordinal1_th_12[of "len p" x] by mty auto
          then obtain n where
             [ty]:"n be Nat"  and A4: "n\<noteq>{} & x= (len p) +\<^sub>\<S>\<^sup>\<nat> n"  using Add_8 by auto
          show "ex y being object st ?P(x,y)"
          proof(rule bexI[of _ "q. n"],rule conjI)
            show "x in dom p \<longrightarrow> p . x = q . n" using F A1 finseq_1_th_1[of "len p" x] by mty auto
            show "for na be Nat st x = (len p) +\<^sub>\<S>\<^sup>\<nat> na \<and> na in proj1 q holds q . na = q . n"
            proof(intro ballI impI)
              fix na assume [ty]:"na be Nat" and A5: "x = (len p) +\<^sub>\<S>\<^sup>\<nat> na \<and> na in dom q"
              thus "q . na = q . n" using A4 Add_11[of n na "len p"] by mty auto
            qed mauto
          qed mauto
    qed
  qed mauto
  have P2:"for x,y1,y2 being object st x in ?X &  ?P(x,y1) & ?P(x,y2) holds y1 = y2"
  proof(intro ballI impI)
    fix x y1 y2 
    assume A2:"x in ?X & ?P(x,y1) & ?P(x,y2)"
    hence [ty]:"x is Nat" using finseq_1_el[of ?L x] by auto
    have A3: "1\<^sub>\<S> c= x" " x c= ?L" using A2 finseq_1_th_1 by auto
    show "y1=y2"
    proof(cases "x c= len p")
      case T: True
        hence "x in dom p" using A1 A3 finseq_1_th_1[of "len p" x] by auto
        thus "y1=y2" using A2 by auto
      next
        case F: False
          hence "len p in x" using ordinal1_th_12[of "len p" x] by mty auto
          then obtain n where
             [ty]:"n be Nat"  and A4: "n\<noteq>{} & x= (len p) +\<^sub>\<S>\<^sup>\<nat> n"  using Add_8 by auto
          have A5: "1\<^sub>\<S> c= n" using one2 A4 by auto
          have "not not n c= len q"
          proof
            assume "not n c= len q"
            hence "len q in n" using ordinal1_th_12[of "len q" n] by mauto
            hence "?L in x" using A4 Add_12 by auto
            thus "False" using A3 ordinal1_th_1 F by auto
          qed
          hence A6: "n in dom q" using A1 A5 finseq_1_th_1[of "len q" n] by auto
          hence "q. n =y2" using A2[THEN conjunct2,THEN conjunct2] A4 by mty auto
          thus "y1 =y2" using A2 A4 A6 by mty auto
        qed
  qed mauto
  obtain f where 
       [ty]: "f be Function" and A2: "dom f=?X"
        "for x being object st x in ?X holds ?P(x,f. x)" using funct_1_sch_1[of ?X ?P,OF _ P1 P2] by auto
  have [ty]: "f is FinSequence-like" using A2(1) finseq_1_def_2 bexI[of _ ?L]by mty auto 
  show "ex it be FinSequence st dom it = ?X &
     (for k st k in dom p holds it .k = p .k) &
     (for k st k in dom q holds it.((len p) +\<^sub>\<S>\<^sup>\<nat> k) = q .k)"
  proof(rule bexI[of _ f],intro conjI ballI impI)
    show "dom f = ?X"  using A2 by simp
    fix k assume [ty]:"k be Nat" and A3: "k in dom p"
    hence "k in ?X" using A1 finseq_1_th_60a[of "len q" "len p" k] Add_6 by mty auto 
    thus "f .k = p .k" using A2(2) A3 by auto
  next    
    fix k assume [ty]:"k be Nat" and A3: "k in dom q"
    hence "(len p)+\<^sub>\<S>\<^sup>\<nat> k in ?X" using A1 finseq_1_th_60[of "len p" "len q" k] by mty auto 
    thus "f .((len p) +\<^sub>\<S>\<^sup>\<nat> k) = q .k" using A2(2) A3 by auto
  qed mauto
  fix it1 it2 assume [ty]:"it1 be FinSequence" "it2 be FinSequence" and
   A2: "dom it1 = ?X & 
     (for k st k in dom p holds it1 .k = p .k) &
     (for k st k in dom q holds it1.((len p) +\<^sub>\<S>\<^sup>\<nat> k) = q .k)"
    "dom it2 = ?X & 
     (for k st k in dom p holds it2 .k = p .k) &
     (for k st k in dom q holds it2.((len p) +\<^sub>\<S>\<^sup>\<nat> k) = q .k)"
  have A1:"dom it1 =Seg len it1" "dom it2 = Seg len it2" "dom it1 =dom it2"
          "Seg len p= dom p" "Seg len q=dom q" using finseq_1_def_3 A2 by auto
  hence A1A:"len it1 = len it2" using finseq_1_th_6[of "len it1" "len it2"] by mty auto
  have "Seg len it1 = ?X" using A2 A1 by simp
  hence L0:"len it1 = ?L" using finseq_1_th_6[of ?L "len it1"] by mty auto
  have "for n st 1\<^sub>\<S> c= n & n c= len it1 holds it1 .n = it2 .n"
  proof(standard,standard)
    fix x assume [ty]: "x be Nat" and A3:"1\<^sub>\<S> c= x & x c= len it1"
    show "it1 .x = it2 .x"
    proof(cases "x c= len p")
      case T: True
        hence "x in dom p" using A1 A3 finseq_1_th_1[of "len p" x] by auto
        thus "it1 .x = it2 .x" using A2 by auto
      next
        case F: False
          hence "len p in x" using ordinal1_th_12[of "len p" x] by mty auto
          then obtain n where
             [ty]:"n be Nat"  and A4: "n\<noteq>{} & x= (len p) +\<^sub>\<S>\<^sup>\<nat> n"  using Add_8 by auto
          have A5: "1\<^sub>\<S> c= n" using one2 A4 by auto
          have "not not n c= len q"
          proof
            assume "not n c= len q"
            hence "len q in n" using ordinal1_th_12[of "len q" n] by mauto
            hence "?L in x" using A4 Add_12 by auto
            thus "False" using A3 ordinal1_th_1[of x ?L] L0 by mty auto
          qed
          hence A6: "n in dom q" using A1 A5 finseq_1_th_1[of "len q" n] by auto
          hence "q. n =it2. x" using A2[THEN conjunct2,THEN conjunct2] A4 by mty auto
          thus "it1 .x =it2 .x" using A2 A4 A6 by mty auto
        qed
  qed mauto
  thus "it1=it2" using A1A finseq_1_th_14 by auto
qed mauto

mtheorem finseq_1_th_22:
  "len (p^q) = (len p) +\<^sub>\<S>\<^sup>\<nat> (len q)"
proof-
  have "dom (p^q) = Seg ((len p) +\<^sub>\<S>\<^sup>\<nat> (len q))" using finseq_1_def_7 by auto
  hence "Seg len (p^q) = Seg ((len p) +\<^sub>\<S>\<^sup>\<nat> (len q))" using finseq_1_def_3 by auto
  thus "len (p^q) = (len p) +\<^sub>\<S>\<^sup>\<nat> (len q)" using finseq_1_th_6 by auto
qed

mtheorem finseq_1_th_C:
  "p \<noteq> <*> implies 1\<^sub>\<S> in dom p"
proof
  assume "p\<noteq><*>"
  hence "len p<>{}" using finseq_1_def_6_p by auto
  hence "1\<^sub>\<S> c= len p" using one2[of "len p"] by mty auto
  hence "1\<^sub>\<S> in Seg len p" using finseq_1_th_1 xboole_0_def_10[of "1\<^sub>\<S>" "1\<^sub>\<S>"] 
    by mty auto
  then show "1\<^sub>\<S> in dom p" using finseq_1_def_3 by auto
qed


mtheorem finseq_1_th_25:
  "n in dom (p^q) iff (n in dom p or (ex k st k in dom q & n = (len p)+\<^sub>\<S>\<^sup>\<nat> k))"
proof
  assume A1: "n in dom (p ^ q)"
  hence A2: "1\<^sub>\<S> c= n & n c= len (p^q)" using finseq_1_th_1 finseq_1_def_3 by mty auto
  have A3:"len (p^q) = (len p)+\<^sub>\<S>\<^sup>\<nat> len q" using finseq_1_th_22 by auto
  have "not  n in dom p implies (ex k st k in dom q & n = (len p)+\<^sub>\<S>\<^sup>\<nat> k)"
  proof
    assume "not n in dom p"
    hence "not n c= len p" using finseq_1_th_1 finseq_1_def_3 A2 by mty auto
    hence "len p in n" using ordinal1_th_12[of "len p" n] by mty auto
    then obtain k where [ty]:"k be Nat" and 
      A4: "k<>{} & n = (len p) +\<^sub>\<S>\<^sup>\<nat> k" using Add_8 by mty auto
    hence A5: "1\<^sub>\<S> c= k" using one2 by auto
    have "k c= len q" using A4 A2 A3 Add_13[of "len p" "len q" k] by mty auto
    hence "k in dom q" using A5 finseq_1_th_1 finseq_1_def_3 by mty auto 
    thus "ex k st k in dom q & n = (len p)+\<^sub>\<S>\<^sup>\<nat> k" using A4 bexI[of _ k Nat] by auto
  qed
  thus "n in dom p or (ex k st k in dom q & n = (len p)+\<^sub>\<S>\<^sup>\<nat> k)" by blast
next
  assume A1:"n in dom p or (ex k st k in dom q & n = (len p)+\<^sub>\<S>\<^sup>\<nat> k)"
  have A3:"len (p^q) = (len p)+\<^sub>\<S>\<^sup>\<nat> len q" using finseq_1_th_22 by auto
  hence "len p c= len (p^q)" using Add_10 by mty auto
  hence A4:"Seg len p c= Seg len (p^q)" using finseq_1_th_5 by mty auto
  show "n in dom (p ^ q)"
  proof (cases "n in dom p")
    case True
      hence "n in Seg (len p)" using finseq_1_def_3 by auto
      thus " n in dom (p^q)" using A4 tarski_def_3E[OF _ _ A4] finseq_1_def_3 by mty auto
  next
    case False
    then obtain  k where [ty]:"k be Nat" and
        A5: "k in dom q & n = (len p)+\<^sub>\<S>\<^sup>\<nat> k" using A1 by auto
    have "k in Seg len q" using A5 finseq_1_def_3 by auto
    thus "n in dom (p^q)" using A3 A5 finseq_1_th_60 finseq_1_def_3 by mty auto
  qed
qed


mtheorem finseq_1_th_31:
  "rng (p^q) = (rng p)\<union> rng q"
proof(intro xboole_0_def_10I tarski_def_3I ballI impI)
  fix y assume "y in rng (p^q)"
  then obtain x where
     A1: "x in dom (p^q) & (p^q) .x = y" using funct_1_def_3 by mty auto
  have [ty]:"x is Nat" using finseq_1_el[of "len (p^q)" x] finseq_1_def_3[of "p^q"] A1 by mty auto 
  show "y in (rng p)\<union> rng q"
  proof(cases "x in dom p")
    case T:True
    hence "p. x =  y" using A1 finseq_1_def_7 by auto 
    thus "y in (rng p)\<union> rng q" using xboole_0_def_3 funct_1_def_3 bexI[of _ x] T by mty auto
  next
    case F:False
    then obtain k where [ty]:"k be Nat" and
        A2: "k in dom q & x = (len p)+\<^sub>\<S>\<^sup>\<nat> k" using A1 finseq_1_th_25 by auto
    hence "y = q. k" using A1 finseq_1_def_7 by auto
    thus "y in (rng p)\<union> rng q" using xboole_0_def_3 funct_1_def_3 bexI[of _ x] A2 by mty auto
  qed
  next
    fix y assume A1: "y in (rng p)\<union> rng q" 
    show "y in rng (p^q)"
    proof(cases "y in rng p")    
      case True
        then obtain x where
        A2: "x in dom p & p .x = y" using funct_1_def_3 by mty auto
        hence [ty]: "x is Nat" using finseq_1_def_3[of p] finseq_1_el[of "len p" x] by mty auto
        have "x in dom (p^q)" " (p^q) .x = y" using A2 finseq_1_th_25[of q p] finseq_1_def_7 by mty auto
        thus "y in rng (p^q)" using funct_1_def_3 by auto
    next
      case False
          hence "y in (rng q)" using xboole_0_def_3 A1 by auto    
       then obtain x where
        A2: "x in dom q & q .x = y" using funct_1_def_3 by mty auto
        hence [ty]: "x is Nat" using finseq_1_def_3[of q] finseq_1_el[of "len q" x] by mty auto
        have "((len p) +\<^sub>\<S>\<^sup>\<nat> x) in dom (p^q)" " (p^q) .((len p) +\<^sub>\<S>\<^sup>\<nat> x) = y" using bexI[of _ x Nat] 
            A2 finseq_1_th_25[of q p] finseq_1_def_7[of p q] by mty auto
        thus "y in rng (p^q)" using funct_1_def_3 by auto
     qed
qed mauto

mtheorem
  mlet "d be object", "p be FinSequence-of d", "q be FinSequence-of d"
  "cluster p^q \<rightarrow> FinSequence-of d"
proof
  have "rng p c= d" "rng q c= d" using finseq_1_def_4E by mty auto
  hence "(rng p) \<union> (rng q) c= d" using xboole_1_th_8 all_set by mty auto
  thus "(p^q) is FinSequence-of d" using finseq_1_th_31 finseq_1_def_4 by auto
qed

mtheorem finseq_1_th_32:
  "(p ^ q) ^ r = p ^ (q ^ r)" 
proof-
  let ?pq = "p^q" let ?qr="q^r" let ?pqR = "?pq^r" let ?Pqr = "p^?qr"
  have A1: "len ?pq = (len p) +\<^sub>\<S>\<^sup>\<nat> (len q)"
       "len ?qr = (len q) +\<^sub>\<S>\<^sup>\<nat> (len r)" 
       "len ?pqR = (len ?pq) +\<^sub>\<S>\<^sup>\<nat> len r" 
       "len ?Pqr = (len p) +\<^sub>\<S>\<^sup>\<nat> len ?qr" using  finseq_1_th_22 by mty auto
  hence L1: "len ?pqR = len ?Pqr" using Add_7 by mty auto
  have "for n st 1\<^sub>\<S> c= n & n c= len ?pqR holds ?pqR .n = ?Pqr .n"
  proof(intro ballI impI)
    fix n assume [ty]:"n be Nat" and
      "1\<^sub>\<S> c= n & n c= len ?pqR"
    hence T0: "n in dom ?pqR" using finseq_1_th_1[of "len ?pqR" n] finseq_1_def_3 by mty auto
    show "?pqR .n = ?Pqr .n"
    proof(cases "n in dom ?pq")
      case T1: True
        hence T2: "?pqR .n = ?pq .n" using finseq_1_def_7 by auto
        show "?pqR .n = ?Pqr .n"
        proof(cases "n in dom p")
          case True
            thus "?pqR .n = ?Pqr .n" using T2 finseq_1_def_7 by auto
          next 
            case False
            then obtain k where [ty]:"k be Nat" and
              T3:"k in dom q & n = (len p)+\<^sub>\<S>\<^sup>\<nat> k" using T1 finseq_1_th_25 by auto
            hence T4: "?pq .n = q .k" "?qr .k = q .k" using finseq_1_def_7 by auto
            have "k in dom ?qr" using T3  finseq_1_th_25 by auto
            thus "?pqR .n = ?Pqr .n" using T2 T4 T3 finseq_1_def_7 by auto
          qed
      next
        case T1:False
          then obtain k where [ty]:"k be Nat" and
          T3:"k in dom r & n = (len ?pq)+\<^sub>\<S>\<^sup>\<nat> k" using T0 finseq_1_th_25 by auto
          hence T4: "?pqR .n = r. k" using finseq_1_def_7 by auto
          
          have T5: "?qr . ((len q) +\<^sub>\<S>\<^sup>\<nat> k) = r .k" using T3 finseq_1_def_7 by mty auto
          have "(len q) +\<^sub>\<S>\<^sup>\<nat> k in dom ?qr" using finseq_1_th_25[of r q] bexI[of _ k Nat ] T3 by mty auto
          hence T6:"?Pqr. ((len p) +\<^sub>\<S>\<^sup>\<nat> ((len q) +\<^sub>\<S>\<^sup>\<nat> k)) = ?qr . ((len q) +\<^sub>\<S>\<^sup>\<nat> k)" using finseq_1_def_7[of p ?qr] by mty auto
          have "(len p) +\<^sub>\<S>\<^sup>\<nat> ((len q) +\<^sub>\<S>\<^sup>\<nat> k) = n" using A1 T3 Add_7[of k "len q"] by mty auto
          thus "?pqR .n = ?Pqr .n" using T4 T5 T6 by auto
    qed
  qed mauto
  thus "?pqR = ?Pqr" using L1 finseq_1_th_14 by mty auto
qed



mtheorem finseq_1_th_34:
  "p^<*> = p & <*>^p=p"
proof
  let ?pE = "p^<*>"
  have "len ?pE = (len p) +\<^sub>\<S>\<^sup>\<nat> {}" using finseq_1_th_22 finseq_1_def_6_p[of "<*>"] by mty auto
  hence L1: "len ?pE = len p" using Add_3 by mty auto 
  have "for n st 1\<^sub>\<S> c= n & n c= len p holds p .n = ?pE .n"
  proof(rule ballI,rule impI)
    fix n assume [ty]:"n be Nat" and
      A1:"1\<^sub>\<S> c= n & n c= len p"
    hence "n in dom p" using finseq_1_th_1 finseq_1_def_3 by mty auto
    thus "p. n = ?pE. n " using finseq_1_def_7 by auto
  qed mauto
  thus "?pE = p" using finseq_1_th_14 L1 by auto
next
  let ?Ep = "<*>^p"
  have L0:"len ?Ep = {}+\<^sub>\<S>\<^sup>\<nat> (len p)" "len (<*>) = {}" using finseq_1_th_22 finseq_1_def_6_p[of "<*>"] by mty auto
  hence L2: "len ?Ep = len p" using Add_4 by mty auto 
  have "for n st 1\<^sub>\<S> c= n & n c= len p holds p .n = ?Ep .n"
  proof(rule ballI,rule impI)
    fix n assume [ty]:"n be Nat" and
      A1:"1\<^sub>\<S> c= n & n c= len p"
    hence "n in dom p" using finseq_1_th_1 finseq_1_def_3 by mty auto
    hence " ?Ep.({} +\<^sub>\<S>\<^sup>\<nat> n) = p. n" using L0(2) finseq_1_def_7[of "<*>" p] by mty auto   
    thus "p. n = ?Ep. n " using Add_4 by auto
  qed mauto
  thus "?Ep = p" using finseq_1_th_14 L2 by auto
qed

mtheorem finseq_1_th_35:
  "p^q = <*> implies p = <*> & q = <*>"
proof
  assume "p^q = <*>"
  hence E: "{} = (len p) +\<^sub>\<S>\<^sup>\<nat> (len q)" using finseq_1_th_22 finseq_1_def_6_p by mty auto 
  hence "len p c= {}" "{} c= len p" using Add_10[of "len q" "len p"] tarski_def_3 xb by mty auto
  hence P: "len p={}" using xboole_0_def_10 by mty auto
  hence "len q={}" using E Add_4 by mty auto
  thus "p = <*> & q = <*>" using finseq_1_def_6_p P by mty auto 
qed


mtheorem finseq_1_def_15:
  mlet "p be FinSequence", "n be Nat"
  "cluster p | (Seg n) \<rightarrow> FinSequence"
proof(standard,cases "n c= len p")
  case True
    hence "Seg n c= dom p" using finseq_1_def_3 finseq_1_th_5 by mty auto 
    hence "dom (p | (Seg n)) = Seg n" using relat_1_th_56 by auto
    thus "p | (Seg n) is FinSequence" using finseq_1_def_2 bexI[of _ n]by mty auto
next
  case False
  hence "len p c= n" using ordinal1_def_5c by mty auto
  hence "dom p c= Seg n" using finseq_1_def_3 finseq_1_th_5 by mty auto
  hence "dom p \<inter> Seg n = dom p" using  xboole_1_th_28[of "Seg n" "dom p"] by mty auto
  hence "dom (p | (Seg n)) = Seg len p" using relat_1_th_55 finseq_1_def_3 by mty auto
  thus "p | (Seg n) is FinSequence" using finseq_1_def_2 bexI[of _ "len p"]by mty auto
qed

mtheorem finseq_1_th_58:
  "len p c= n implies p|(Seg n) = p"
proof
  assume "len p c= n" 
  hence "dom p c= Seg n" using finseq_1_def_3 finseq_1_th_5 by mty auto
  thus "p|(Seg n) = p" using relat_1_th_68 by auto
qed

mtheorem finseq_1_th_59:
  "n c= len p implies len(p|(Seg n)) = n"
proof
  assume "n c= len p"
  hence "Seg n c= dom p" using finseq_1_def_3 finseq_1_th_5 by mty auto 
  hence "dom (p | (Seg n)) = Seg n" using relat_1_th_56 by auto
  thus "len (p | (Seg n)) =n" using finseq_1_def_3_uniq[of _ n] by mty auto
qed

text_raw {*\DefineSnippet{rfinseq1def1}{*}
mdef rfinseq_1_def_1 (" _ '/^ _ ") where
  mlet "i be Nat", "p be FinSequence"
  "func p /^ i \<rightarrow> FinSequence means
    (\<lambda>it . i +\<^sub>\<S>\<^sup>\<nat> len it =\<^sub>\<S> len p & 
        (\<forall>n:Nat. n in dom it \<longrightarrow> it .n =\<^sub>\<S> p .(i +\<^sub>\<S>\<^sup>\<nat> n))) 
      if i \<subseteq> len p 
      otherwise (\<lambda>it . it =\<^sub>\<S> <*>)"  
text_raw {*}%EndSnippet*}
proof-
  show " (i \<subseteq> len p \<longrightarrow> (\<exists>x : FinSequence. i +\<^sub>\<S>\<^sup>\<nat> (len x) = len p \<and> (\<forall>n : Nat. n in dom x \<longrightarrow> x . n = p . (i +\<^sub>\<S>\<^sup>\<nat> n)))) \<and>
    (\<not> i \<subseteq> len p \<longrightarrow> (\<exists>x : FinSequence. x = <*>))"
  proof(intro conjI impI)
    assume A1: "i \<subseteq> len p"
    then obtain k where [ty]:"k be Nat" and
       A2: "i +\<^sub>\<S>\<^sup>\<nat> k = len p" using Add_9 by auto 
    let ?P = "\<lambda> x. p.(i +\<^sub>\<S>\<^sup>\<nat> x)"
    obtain f where [ty]: "f be Function" and
       A3: "dom f = Seg k" and A4: "(for x st x in Seg k holds f .x = ?P(x))"
      using funct_1_sch_Lambda[of "Seg k" ?P] by mty auto
    have [ty]: "f is FinSequence" using finseq_1_def_2I A3 bexI[of _ k ]by mty auto
    show "\<exists>x : FinSequence. i +\<^sub>\<S>\<^sup>\<nat> (len x) = len p \<and> (\<forall>n : Nat. n in dom x \<longrightarrow> x . n = p . (i +\<^sub>\<S>\<^sup>\<nat> n))"
    proof(rule bexI[of _ f],intro conjI ballI impI)
       have "len f = k" using A3 finseq_1_def_3_uniq[of f k] by mty auto
       show "i +\<^sub>\<S>\<^sup>\<nat> len f = len p" using A3 finseq_1_def_3_uniq[of f k] A2 by mty auto
       fix n assume [ty]: "n is Nat" and "n in dom f"
       thus "f . n = p . (i +\<^sub>\<S>\<^sup>\<nat> n)" using A3 A4 by auto
    qed mauto
  next assume "\<not> i \<subseteq> len p"  
    show "\<exists>x : FinSequence. x = <*>" using bexI[of _ "<*>"]  by mty auto
  qed 
  fix x y assume [ty]:"x be FinSequence" "y be FinSequence"
  show  "(i \<subseteq> len p \<and>
            ((i +\<^sub>\<S>\<^sup>\<nat> (len x)) = len p \<and> (\<forall>n : Nat. n in dom x \<longrightarrow> (x . n = p . (i +\<^sub>\<S>\<^sup>\<nat> n)))) \<and>
            (i +\<^sub>\<S>\<^sup>\<nat> (len y)) = len p \<and> (\<forall>n : Nat. n in dom y \<longrightarrow> (y . n = p . (i +\<^sub>\<S>\<^sup>\<nat> n))) \<longrightarrow>
            x = y) \<and>
           ((\<not> i \<subseteq> (len p) \<and> x = <*> \<and> y = <*>) \<longrightarrow> x = y)"
  proof(intro impI conjI)
    assume A1: "i \<subseteq> len p \<and>
            ((i +\<^sub>\<S>\<^sup>\<nat> (len x)) = len p \<and> (\<forall>n : Nat. n in dom x \<longrightarrow> (x . n = p . (i +\<^sub>\<S>\<^sup>\<nat> n)))) \<and>
            (i +\<^sub>\<S>\<^sup>\<nat> (len y)) = len p \<and> (\<forall>n : Nat. n in dom y \<longrightarrow> (y . n = p . (i +\<^sub>\<S>\<^sup>\<nat> n)))"
    hence "i +\<^sub>\<S>\<^sup>\<nat> (len x) = i +\<^sub>\<S>\<^sup>\<nat> (len y)" by auto
    hence L:"len x=len y" using Add_11[of _ _ i] by mty auto
    have "for n st 1\<^sub>\<S> c= n & n c= len x holds x . n = y .n"
    proof(intro ballI impI)
      fix n assume [ty]: "n be Nat" and A2: " 1\<^sub>\<S> c= n & n c= len x"
      hence A3: "n in Seg len x" using finseq_1_th_1[of "len x" n] by mty auto
      have "dom x = Seg len x" "dom y = Seg len y" using finseq_1_def_3 by auto
      hence "x . n = p . (i +\<^sub>\<S>\<^sup>\<nat> n)" "y . n = p . (i +\<^sub>\<S>\<^sup>\<nat> n)" using A1 L A3 by auto
      thus "x .n = y. n" by simp 
    qed mauto
    thus "x=y" using finseq_1_th_14 L by mty auto 
  next 
    assume "\<not> i \<subseteq> len p \<and> x = <*> \<and> y = <*>"
    thus "x=y" by simp
  qed
qed mauto


mtheorem finseq_rng: 
  "rng (p/^i) c= rng p"
proof(intro ballI impI tarski_def_3I)
  fix y assume "y in rng (p/^i)"
  then obtain x where
     A1: "x in dom (p/^i) & (p/^i) .x = y" using funct_1_def_3 by mty auto
  have A3: "x in Seg len (p/^i)" using A1 finseq_1_def_3 by auto 
  hence [ty]:"x be Nat" using finseq_1_el[of "len (p/^i)" x] by mty auto
  hence "dom (p/^i) is non empty" using A1 xboole_0_def_1 by mty auto
  hence "p/^i \<noteq> <*>" using finseq_1_def_6 relat_1_cl_20[of "p/^i"] by mty auto
  hence "i c= len p" using  rfinseq_1_def_1[of i p] by mty auto
  hence A4: "i +\<^sub>\<S>\<^sup>\<nat> (len (p/^i)) = len p" "y = p. (i +\<^sub>\<S>\<^sup>\<nat> x)" 
      using rfinseq_1_def_1 A1 by mty auto
  hence  "i+\<^sub>\<S>\<^sup>\<nat> x in Seg (len p)" using finseq_1_th_60[of i "len (p/^i)" x] A3 by mty auto
  thus "y in rng p" using A4 finseq_1_def_3 funct_1_def_3 by mty auto
qed mauto


mtheorem
  mlet "i be Nat", "d be object", "p be FinSequence-of d"
  "cluster p/^i \<rightarrow> FinSequence-of d"
proof
  have "rng p c= d" "rng (p/^i) c= rng p" 
    using finseq_1_def_4[of d p] finseq_rng all_set by mty auto  
  hence "rng (p/^i) c= d" using xboole_1_th_1[of d] all_set by mty auto
  thus "p/^i is FinSequence-of d" using finseq_1_def_4 by auto
qed

(*mtheorem rfinseq_dom:
  "dom (p/^i) c= dom p"
proof(cases "i c= len p")
  case True
    hence "i +\<^sub>\<S>\<^sup>\<nat> (len (p/^i)) = len p" using rfinseq_1_def_1 by mty auto
    hence "len (p/^i) c= len p" using Add_10[of i "len (p/^i)"] Add_6[of i "len (p/^i)"] by mty auto
    thus "dom (p/^i) c= dom p" using finseq_1_def_3 finseq_1_th_5 by mty auto
  next
    case False
    hence "p/^i = {}" using rfinseq_1_def_1 finseq_1_def_6 by auto
    hence [ty]: "p/^i is empty" by mty auto
    hence "dom (p/^i) ={}" using xboole_0_lm_1 by mty auto
    thus "dom (p/^i) c= dom p" using xb tarski_def_3I by mty auto
qed
*)


mtheorem rfinseq_th_a:
  "len p c= n implies p /^ n = <*>"
proof
  assume A1: "len p c= n"
  show "p /^ n = <*>"
  proof(cases "n c= len p")
    case T: True
      hence "len p = n" using A1 xboole_0_def_10 by auto
      hence "(len p) +\<^sub>\<S>\<^sup>\<nat> len (p/^ n) = (len p)+\<^sub>\<S>\<^sup>\<nat> {}" using T rfinseq_1_def_1 Add_3 by mty auto
      hence "len (p/^ n) = {}" using Add_11[of "{}" _ "len p"] by mty auto
      thus "p/^n =<*>" using finseq_1_def_6_p by auto
    next
      case False
      thus "p/^n =<*>" using rfinseq_1_def_1 by auto          
  qed 
qed

mtheorem rfinseq_th_8:
  "(p| (Seg n)) ^ (p /^ n) = p"
proof(cases "len p c= n")
  case True
    hence "p /^ n =<*>" "(p| (Seg n)) = p" using rfinseq_th_a finseq_1_th_58 by auto
    thus "(p| (Seg n)) ^ (p /^ n) = p" using finseq_1_th_34 by auto
next 
  case False
    hence A1:"n c= len p" using ordinal1_def_5c by mty auto
    then obtain k where [ty]:"k be Nat" and
       A2: "len p = n +\<^sub>\<S>\<^sup>\<nat> k" using Add_9 by mty auto
    let ?pn = "p/^n" let ?ps = "p|(Seg n)" 
    have " n +\<^sub>\<S>\<^sup>\<nat> len ?pn = len p" using A1 rfinseq_1_def_1 by auto
    hence A3:"len ?pn = k" using A2 Add_11[of k _ n ] by mty auto
    have A4: "len ?ps = n" using finseq_1_th_59 A1 by mty auto 
    hence A5: "len (?ps ^ ?pn) = len p" using A2 A3 finseq_1_th_22 by auto


    have "for k st 1\<^sub>\<S> c= k & k c= len p holds p .k = (?ps ^ ?pn) .k"
    proof(standard,standard)
      fix k assume [ty]:"k be Nat" and
        B1: "1\<^sub>\<S> c= k & k c= len p"
      hence B2: "k in dom (?ps ^ ?pn)" using A5 finseq_1_th_1[of _ k] finseq_1_def_3 by mty auto
      show "p .k = (?ps ^ ?pn) .k"
      proof (cases "k in dom ?ps")
        case True
           hence "?ps .k = p. k" "(?ps ^ ?pn). k = ?ps. k" using funct_1_th_47 finseq_1_def_7 by auto
           thus "p .k = (?ps ^ ?pn) .k" by simp
      next
        case False
          then obtain m where [ty]: "m be Nat" and
            B3: "m in dom ?pn & k = (len ?ps) +\<^sub>\<S>\<^sup>\<nat> m" using B2 finseq_1_th_25 by mty auto
          have B4: "(?ps ^ ?pn) . k = ?pn. m" using B3 finseq_1_def_7 by auto
          have "?pn .m = p. k" using B3 A3 A4 rfinseq_1_def_1 A1 by mty auto
          thus "p .k = (?ps ^ ?pn) .k" using B4 by simp
        qed
    qed mauto
    thus "(p| (Seg n)) ^ (p /^ n) = p" using finseq_1_th_14 A5 by mty auto
qed

mtheorem rfinseq_th_c:
  "len p =succ n implies len (p/^1\<^sub>\<S>) =n"
proof
  assume "len p = succ n"
  hence "1\<^sub>\<S> c= len p" "len p = 1\<^sub>\<S> +\<^sub>\<S>\<^sup>\<nat> n" using one2 Add_5 by auto
  hence "1\<^sub>\<S> +\<^sub>\<S>\<^sup>\<nat> len (p/^1\<^sub>\<S>) = 1\<^sub>\<S> +\<^sub>\<S>\<^sup>\<nat> n" using rfinseq_1_def_1 by auto
  thus "len (p/^1\<^sub>\<S>) =n" using Add_11[of n "len (p/^1\<^sub>\<S>)" "1\<^sub>\<S>"] by mty auto
qed

mtheorem rfinseq_th_b:
  "len p \<noteq> {} implies (p/^1\<^sub>\<S>) ^q = (p^q) /^ 1\<^sub>\<S>"
proof
  let ?pL="predecessor (len p)"
  assume a0: "len p<>{}"
  hence A1: "succ ?pL = len p" "1\<^sub>\<S> c= len p" 
      using NAT_1_5 one2 by auto
  hence a1: "len (p/^1\<^sub>\<S>) = ?pL" using rfinseq_th_c by mty auto

  have A2: "len (p^q) = (len p) +\<^sub>\<S>\<^sup>\<nat> (len q)" using finseq_1_th_22 by auto
  hence "len (p^q) = succ((?pL) +\<^sub>\<S>\<^sup>\<nat> (len q))" using Add_2[of "len q" ?pL]
     A1 by mty auto
  hence A3: "len((p^q) /^ 1\<^sub>\<S>) = ?pL +\<^sub>\<S>\<^sup>\<nat> (len q)" using rfinseq_th_c by mty auto 
  have A4:"len ((p/^1\<^sub>\<S>) ^q) = ?pL +\<^sub>\<S>\<^sup>\<nat> (len q)" using finseq_1_th_22 a1 by auto
  
  have "p<><*>" using finseq_1_def_6_p a0 by auto
  hence "p^q <> <*>" using finseq_1_th_35[of q p] by mty auto
  hence "len (p^q) <>{}" using finseq_1_def_6_p by auto
  hence A5: "1\<^sub>\<S> c= len (p^q)" using one2 by mty auto
  have "for k st 1\<^sub>\<S> c= k & k c= len((p^q) /^ 1\<^sub>\<S>)
     holds ((p^q) /^ 1\<^sub>\<S>) .k = ((p/^1\<^sub>\<S>) ^q) .k"
    proof(standard,standard)
      fix k assume [ty]:"k be Nat" and
        B1: "1\<^sub>\<S> c= k & k c= len ((p^q) /^ 1\<^sub>\<S>)"
      hence B2: "k in dom ((p/^1\<^sub>\<S>) ^q) " "k in dom ((p^q)/^1\<^sub>\<S>) "
          using A4 A3 finseq_1_th_1[of _ k] finseq_1_def_3 by mty auto
      have B3:"dom (p/^1\<^sub>\<S>) = Seg ?pL" using a1 finseq_1_def_3 by auto       
      have B4:"len p = 1\<^sub>\<S>+\<^sub>\<S>\<^sup>\<nat> ?pL" using A1 Add_5 by mty auto
      show "((p^q) /^ 1\<^sub>\<S>) .k = ((p/^1\<^sub>\<S>) ^q) .k"
      proof (cases "k in dom (p/^1\<^sub>\<S>)")
        case T:True
           hence B5: "((p/^1\<^sub>\<S>) ^q) .k = (p/^1\<^sub>\<S>). k" "(p/^1\<^sub>\<S>). k = p.(1\<^sub>\<S>+\<^sub>\<S>\<^sup>\<nat> k)"
               using finseq_1_def_7 rfinseq_1_def_1[of "1\<^sub>\<S>" p] A1 by auto

           have "1\<^sub>\<S> +\<^sub>\<S>\<^sup>\<nat> k in Seg (len p)" 
             using finseq_1_th_60[of "1\<^sub>\<S>" "?pL" k] a1 B4 T B3 by mty auto
           hence "1\<^sub>\<S> +\<^sub>\<S>\<^sup>\<nat> k in dom p" using finseq_1_def_3 by auto
           hence "(p^q). (1\<^sub>\<S> +\<^sub>\<S>\<^sup>\<nat> k) = p.(1\<^sub>\<S> +\<^sub>\<S>\<^sup>\<nat> k)" using finseq_1_def_7 by mty auto
           then show "((p^q)/^1\<^sub>\<S>).k =  ((p/^1\<^sub>\<S>) ^q) .k" using A5 B2 B5 rfinseq_1_def_1[of "1\<^sub>\<S>" "p^q"] by mty auto        
         next
        case False
          then obtain m where [ty]: "m be Nat" and
            B3: "m in dom q & k = (len (p/^1\<^sub>\<S>)) +\<^sub>\<S>\<^sup>\<nat> m" using B2 finseq_1_th_25 by mty auto
         
          have B4: "((p/^1\<^sub>\<S>) ^q).k = q. m" using B3 finseq_1_def_7 by auto
          have B5: "((p^q)/^1\<^sub>\<S>).k =  (p^q) .(1\<^sub>\<S> +\<^sub>\<S>\<^sup>\<nat> k)" using A5 B2 rfinseq_1_def_1[of "1\<^sub>\<S>" "p^q"] by mty auto

          have "1\<^sub>\<S> +\<^sub>\<S>\<^sup>\<nat> k = succ k" using Add_5 by auto
          also have "... = succ (?pL +\<^sub>\<S>\<^sup>\<nat> m)" using a1 B3 by auto
          also have "... = (succ ?pL) +\<^sub>\<S>\<^sup>\<nat> m" using Add_2 by mty auto
          also have "... = (len p) +\<^sub>\<S>\<^sup>\<nat> m" using A1 by auto
          finally have "((p^q)/^1\<^sub>\<S>).k = q .m" using B5 B3  finseq_1_def_7 by auto
          then show "((p^q)/^1\<^sub>\<S>).k =  ((p/^1\<^sub>\<S>) ^q) .k" using B4 by auto
        qed
    qed mauto
 thus "(p/^1\<^sub>\<S>) ^q = (p^q) /^ 1\<^sub>\<S>" using finseq_1_th_14[of "(p/^1\<^sub>\<S>) ^q" "(p^q) /^ 1\<^sub>\<S>" ] A3 A4 by mty auto
qed

mtheorem rfinseq_th_d:
  "(<*x*>^p)/^1\<^sub>\<S> =p" 
proof-
  let ?xp = "<*x*> ^ p"
  have L1: "len ?xp = (len <*x*>) +\<^sub>\<S>\<^sup>\<nat> (len p)" "len <*x*> = 1\<^sub>\<S>" using finseq_1_th_22 finseq_1_def_8[of x] 
    finseq_1_def_3_uniq[of "<*x *>" "1\<^sub>\<S>"] by auto
  hence L2: "len ?xp = succ (len p)" using Add_5 by mty auto
  hence L3:"len (?xp /^ 1\<^sub>\<S>) = len p" using rfinseq_th_c by mty auto
  have "for n st 1\<^sub>\<S> c= n & n c= len p holds p. n = (?xp /^ 1\<^sub>\<S>). n"
  proof(rule ballI, rule impI)
    fix n assume [ty]:"n be Nat"
    have L4:"1\<^sub>\<S> c= len ?xp" using one2 L2 by mty auto
    assume "1\<^sub>\<S> c= n & n c= len p" 
    hence "n in dom p" "n in dom (?xp /^ 1\<^sub>\<S>)" using L3 finseq_1_def_3 finseq_1_th_1 by mty auto
    hence "?xp . (1\<^sub>\<S> +\<^sub>\<S>\<^sup>\<nat> n) = p. n" "(?xp /^ 1\<^sub>\<S>). n = ?xp . (1\<^sub>\<S> +\<^sub>\<S>\<^sup>\<nat> n)"
       using finseq_1_def_7[of "<*x*>" p] L1 rfinseq_1_def_1[of "1\<^sub>\<S>" ] L4 by mty auto
    thus  "p. n = (?xp /^ 1\<^sub>\<S>). n" by simp
  qed mauto
  thus ?thesis using finseq_1_th_14 L3 by auto
qed

mtheorem rfinseq_th_e:
  "(<*x*>^ p). 1\<^sub>\<S> =x"
proof-
  have "1\<^sub>\<S> in dom <*x*>" using finseq_1_th_C finseq_1_lm_1 by auto
  thus "(<*x*>^ p). 1\<^sub>\<S> = x" using finseq_1_def_7 finseq_1_def_8 by auto
qed

mtheorem finseq_5_th_20:
  "p \<noteq> <*> implies p| (Seg 1\<^sub>\<S>) = <* p .1\<^sub>\<S> *>"
proof
  let ?p1 = "p|(Seg 1\<^sub>\<S>)"
  assume "p \<noteq> <*>"
  hence "len p <> {}" using finseq_1_def_6_p finseq_1_def_6 by mty auto
  hence "1\<^sub>\<S> c= len p" using one2 by mty auto
  hence "Seg 1\<^sub>\<S> c= Seg len p" "Seg len p = dom p" using finseq_1_def_3 finseq_1_th_5 by mty auto
  hence H: "dom ?p1 = Seg 1\<^sub>\<S>" using relat_1_th_56 by auto
  hence "1\<^sub>\<S> in dom ?p1" using finseq_1_th_2 tarski_def_1 by auto
  hence "?p1 .1\<^sub>\<S> = p. 1\<^sub>\<S>" using funct_1_th_47 by auto
  thus "?p1 = <* p .1\<^sub>\<S> *>" using finseq_1_def_8_uniq[of "p. 1\<^sub>\<S>" ?p1] H by mty auto
qed










text_raw {*\DefineSnippet{finseqe}{*}
mdef finseq_e (" _ ending-of _ ") where
  mlet "p be FinSequence","q be FinSequence"
  "pred p ending-of q means
     (len p in len q & 
      (\<exists>n: Nat. n \<noteq> 0\<^sub>\<S> \<and> q /^ n =\<^sub>\<S> p))"..
text_raw {*}%EndSnippet*}

lemma ending_prop: 
   "x be FinSequence \<Longrightarrow> x\<noteq> <*> \<Longrightarrow> x /^1\<^sub>\<S> ending-of x"
proof-
  assume [ty]:"x be FinSequence" and A1:"x\<noteq> <*>"
  hence "len x <> {}" using finseq_1_def_6_p by auto
  hence "1\<^sub>\<S> c= len x" using one2 by mty auto
  hence "(len (x /^1\<^sub>\<S>))+\<^sub>\<S>\<^sup>\<nat> 1\<^sub>\<S> = len x" using rfinseq_1_def_1 Add_6 by mty auto
  hence "(len (x /^1\<^sub>\<S>)) in len x" using Add_8 bexI[of _ "1\<^sub>\<S>" Nat] by mty auto 
  thus "x /^1\<^sub>\<S> ending-of x"  using finseq_eI bexI[of _ "1\<^sub>\<S>" Nat] by mty auto
qed
text_raw {*\DefineSnippet{endinginduct}{*}
theorem ending_induct:
  assumes [ty]: "a is FinSequence"
    and "\<forall>n:FinSequence. (\<forall>m:FinSequence. m ending-of n \<longrightarrow> P(m)) \<longrightarrow> P(n)"
  shows "P(a)"
text_raw {*}%EndSnippet*}
proof-
  let ?R="\<lambda>it. for p be FinSequence st len p = it holds P(p)"
  have Rn:"for k st (for m st m \<subset> k holds ?R(m)) holds ?R(k)" 
  proof(intro ballI impI)
    fix k p assume [ty]:"k is Nat" "p be FinSequence"
    assume R2:"for m st m \<subset> k holds ?R(m)" "len p= k"
    have "\<forall>q:  FinSequence. q ending-of p  \<longrightarrow> P(q)"
    proof(intro ballI impI)
      fix q assume [ty]: "q be FinSequence"
      assume "q ending-of p"
      hence "len q \<subset> k" using ordinal1_th_7a finseq_eE R2 by mty auto
      thus "P(q)" using R2(1)[THEN bspec,of "len q"] by mty auto  
    qed mauto
    thus "P(p)" using assms(2) by auto
  qed mauto 
  have "?R(len a)" using CompleteInduction[of "len a" ?R,OF _ Rn] by mty auto    
  thus "P(a)" by simp
qed




mdef finseq_1_def_11 ("_*" [130] 130) where
  mlet "D be set"
  "func D* \<rightarrow> set means
     \<lambda>it. \<forall>x : object. 
         x in it \<longleftrightarrow> x be FinSequence-of D"
proof-
    let ?P = "\<lambda>p . p be FinSequence-of D"
    have A0: "bool [:NAT,D:] be set" using all_set by auto
    obtain IT where
   [ty]:"IT be set" and A1: "for x being object holds x in IT \<longleftrightarrow> x in bool [:NAT,D:] \<and> ?P(x)"
        using xboole_0_sch_1[OF A0, of ?P] by auto
     show "ex IT be set st \<forall>x : object.  x in IT \<longleftrightarrow> x be FinSequence-of D"
     proof(rule bexI[of _ IT],rule ballI,rule iffI3)
       fix x assume "x be object"
       show "x in IT \<longrightarrow> x be FinSequence-of D" using A1 by mty auto
       assume A2[ty]: "x be FinSequence-of D"
         thm ty
       then obtain n where
         A3:"n be Element-of NAT" "dom x = Seg n" using finseq_1_def_2 by mauto
       have A4: "rng x c= D" using A2 finseq_1_def_4E by mty auto
       have "dom x c= NAT" using A3 finseq_1_cl[of n] A3 by auto
       hence A5: "[:dom x,rng x:] c= [:NAT,D:]" using A4 A3(1) zfmisc_1_th_96[of D "rng x" NAT "dom x"] all_set by auto
       have A6: "x c= [:dom x,rng x:]" using relat_1_th_7[of x] A2 finseq_1_def_4 all_set by auto
       have "x c= [:NAT,D:]"
       proof(standard,auto)
         fix a assume "a in x"
         hence "a in [:dom x,rng x:]" using A6 tarski_def_3E by mauto
         thus "a in [:NAT,D:]" using A5 tarski_def_3 by mauto
       qed mauto
       hence "x in bool [:NAT,D:]" using all_set zfmisc_1_def_1 by auto
       thus "x in IT" using A1 A2 by auto
     qed mauto
   next
  fix A1 A2
  assume A1:"A1 be set" "(\<forall>x : object. 
         x in A1 \<longleftrightarrow> x be FinSequence-of D)" and
        A2: "A2 be set" "\<forall>x : object. 
         x in A2 \<longleftrightarrow> x be FinSequence-of D"
    {
      fix x
      assume Z1: "x be object"
      have "x in A1 \<longleftrightarrow> (x be FinSequence-of D)" using Z1 A1 by auto
      then have "x in A1 \<longleftrightarrow> x in A2" using Z1 A2 by auto
    }
  thus "A1 = A2" using tarski_th_2[OF A1(1) A2(1)] by auto
qed mauto

reserve D for set

mtheorem finseq_1_def_6_d:
  "<*> is FinSequence-of D"
proof-
  have [ty]:"{} be FinSequence" by mauto
  have "rng {} is empty" by mauto
  hence "rng {}={}" using xboole_0_lm_1 by mauto
  hence H:"rng (<*>) \<subseteq> D" using xb tarski_def_3 finseq_1_def_6 by mauto
  thus ?thesis using finseq_1_def_4 by auto
qed

mtheorem finseq_1_th:
  "{} in D*"
proof-
  have A1[ty]:"{} be FinSequence" by mauto
  have "rng {} is empty" by mauto
  hence H:"rng {}={}" using xboole_0_lm_1 by mauto
  hence H:"rng {} \<subseteq> D" using xb tarski_def_3 by mauto
  thus "{} in D*" using finseq_1_def_11 finseq_1_def_4 by mauto
qed

mtheorem
  mlet "D be set"
  "cluster D* \<rightarrow> non empty"
  using xboole_0_def_1 finseq_1_th[of D] by mty auto

(*theorem finseq_1_sch_3:
  assumes "for p be Finsequence holds 
             (for x be object st P(p) holds P(p^<*x*>))"
  shows "for p be Finsequence holds P[p]"
proof
qed
 P[{}] and
 for p,x st P[p] holds P[p^<*x*>];
*)
end