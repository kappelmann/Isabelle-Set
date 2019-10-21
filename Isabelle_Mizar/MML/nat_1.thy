theory nat_1
  imports ordinal1 funct_2
(*    "~~/src/HOL/Number_Theory/Primes" *)
    
begin

reserve x,y,n,k,m for Nat  
  
  
mtheorem NAT_1_1: 
  "for x st x<>{} holds
     ex y st succ y = x" 
proof(rule ballI,rule impI)
  fix x assume [ty]: "x be Nat" and A0: "x<>{}"
  let ?P = "\<lambda>it. it = {} or  (ex y be Nat st succ y = it)"
  have A1: "?P({})" by simp
  have A2: "\<forall>n : Nat. ?P(n) \<longrightarrow> ?P(succ n)" by auto
  have "?P(x)" using ordinal_2_sch_19[of x ?P, OF _ A1 A2] by mauto
  thus "ex y be Nat st succ y = x" using A0 by auto   
qed mauto
  
theorem  NAT_1_2: "X\<noteq>Y \<Longrightarrow> succ X \<noteq> succ Y"
proof
  assume A1: "X\<noteq>Y" "succ X = succ Y"
  have "Y in succ Y" using ordinal1_def_1 tarski_def_1 xboole_0_def_3 all_set by auto
  hence "Y in X \<union> { X }" using ordinal1_def_1 A1(2) all_set by auto
  hence A2: "Y in X" using A1(1) tarski_def_1 xboole_0_def_3 all_set by auto
  have "X in succ X" using ordinal1_def_1 tarski_def_1 xboole_0_def_3 all_set by auto
  hence "X in Y \<union> { Y }" using ordinal1_def_1 A1(2) all_set by auto
  hence "X in Y" using A1(1) tarski_def_1 xboole_0_def_3 all_set by auto
  thus "False" using A2 prefix_in_asymmetry[of X Y] all_set by mauto
qed  

mtheorem
  mlet "m be Nat"
  "cluster succ m \<rightarrow> Nat" 
proof
  let ?P="\<lambda>it. (succ it) in omega"
  have "{} is Ordinal" by mauto
  hence A0: "?P({})" using ordinal1_th_24 ordinal1_def_11 by ty_auto
  have An:"\<forall>n : Nat. ?P(n) \<longrightarrow> ?P(succ n)"
   proof(standard,standard)
     fix n assume [ty]:"n be Nat"
     hence N: "n in omega" using ordinal1_def_12 all_set by mauto
     assume "?P(n)"
     thus "?P(succ n)" using N ordinal1_th_24 ordinal1_def_11 by mauto
   qed  mauto
  have "?P(m)" using ordinal_2_sch_19[of m ?P,OF _ A0 An] by ty_auto
  thus "(succ m) is Nat" using ordinal1_def_12 by ty_auto  
qed

text_raw {*\DefineSnippet{predec}{*}
mdef predec ("predecessor _" [90] 90) where
 mlet "n be Nat"  
 "assume n \<noteq> 0\<^sub>\<S>
  func predecessor n \<rightarrow> Nat means 
    \<lambda>it. succ it = n"
text_raw {*}%EndSnippet*}
proof -
  show " n \<noteq> {} \<Longrightarrow> \<exists>x : Nat. succ x = n" using NAT_1_1 by ty_auto
  fix x y  assume "n \<noteq> {}" "x be Nat" "y be Nat" 
        "succ x = n" "succ y = n" 
  thus "x=y" using NAT_1_2[of x y] by auto     
qed mauto

mtheorem NAT_1_4:
  "n<>{} implies  (predecessor n) c< n"
proof
  assume "n<>{}"
  hence  "succ (predecessor n) = n" using predec by ty_auto
  hence "(predecessor n) in n" using ordinal1_th_2 by mauto
  thus "(predecessor n) c< n" using ordinal1_th_7a by ty_auto
qed
  
mtheorem NAT_1_5:
  "n<>{} implies succ (predecessor n) = n" using predec by ty_auto

mtheorem NAT_1_6:
  "predecessor (succ n) = n"
proof-
  have "succ n <>{}" by mauto
  hence "succ  predecessor (succ n) = succ n" using predec by mauto
  thus ?thesis using ordinal1_succ by inst_nopass_auto
qed
        
theorem NAT_sch:
  fixes S x
  assumes SS:"for x be Nat holds S(x) is Nat"
  assumes [ty]:"n is Nat" "m is Nat"
  shows "ex f be  Function-of NAT,NAT st 
          f.{} = n & (for k be Nat st k in m holds f. (succ k) = S(f. k))"
proof-
    have [ty]:"omega is non empty\<bar>set" by mauto 
  let ?P="\<lambda>it.  ex f be  Function-of NAT,NAT st 
          f.{} = n &  (for k be Nat st k in it holds f. (succ k) = S (f. k))"
  have A0: "?P({})"
   proof-
     let ?Q="\<lambda>x. n"
     have "n be Element-of NAT" by mauto  
     hence "\<exists>f:Function-of NAT,NAT. \<forall>x:Element-of NAT. (f . x) = ?Q(x)" using  
         funct_2_sch_4[of NAT NAT] by mauto
     then obtain f where
       [ty]:"f be Function-of NAT,NAT" and A1:"\<forall>x:Element-of NAT. (f . x) = ?Q(x)" by auto
     show "ex f be  Function-of NAT,NAT st 
          f.{} = n &  (for k be Nat st k in {} holds f. (succ k) = S (f. k))"
     proof(rule bexI[of _ f],auto)
       show "f . {} = n" using A1 by ty_auto
       fix n assume [ty]:"n be natural" "n be set"
       assume "n in {}"
       thus "f. (succ n) = S (f. n)" using xb by auto  
     qed ty_auto
   qed    
  have An: "for m st ?P(m) holds ?P(succ m)" 
  proof(standard,standard)
    fix m assume [ty]:"m be Nat" 
    hence M:"m in NAT" using ordinal1_def_12 by auto
    assume "?P(m)"
    then obtain f where 
       [ty]:" f be  Function-of NAT,NAT" 
       and   
       B1: "f.{} = n &  (for k be Nat st k in m holds f. (succ k) = S (f. k))" by ty_auto
    let ?R = "\<lambda>x y. (x c= m implies y= f. x) & (not x c= m implies y = S (f. m))"
    have [ty]:"f be set" using all_set by mauto 
    have R:"rng f c= NAT" using relat_1_def_19E[of NAT f] by ty_auto  
    have P1:"for x being object st x in NAT holds (ex y being object st y in NAT & ?R(x,y))"
    proof(standard,standard)
      fix x assume X: "x in omega"
      hence "omega<>{}" using xb by auto
      hence "f. x in rng f" "f. m in rng f" using funct_2_th_4[of _ NAT NAT] X M by ty_auto
      hence K: "f. x in NAT" "f. m in NAT" using R tarski_def_3 by inst_pass_auto
      hence "f. m is Nat" using ordinal1_def_12 by mauto    
      hence "(S (f. m)) is Nat" using SS by mauto    
      hence L:"S (f. m) in NAT" using ordinal1_def_12 by ty_auto
      show "ex y being object st y in NAT & ?R(x,y)" using bexI[of _ "S (f. m)"] L bexI[of _ "f. x"] K by(cases "x c= m",auto)
    qed mauto
    have P2:"for x,y1,y2 being object st x in NAT &  ?R(x,y1) & ?R(x,y2) holds y1 = y2"  by auto
    obtain g where 
       [ty]:"g be Function-of NAT, NAT" and
       B2: "for x being object st x in NAT holds ?R(x,g. x)" using  funct_2_sch_1[OF _ _ P1 P2] by ty_auto
     show "ex h be  Function-of NAT,NAT st 
          h.{} = n &  (for k be Nat st k in succ m holds h. (succ k) = S (h. k))"
     proof(rule bexI[of _ g],auto)
       have "{} in NAT" using ordinal1_def_12[of "{}"] by ty_auto
       hence "?R({},g. {})" "{} c= m" using xb tarski_def_3I B2 by ty_auto
       thus "g. {} = n" using B1 by auto
       fix x assume [ty]:"x be natural" "x be set"
       have X: "x in NAT" "succ x in NAT" using ordinal1_def_12[of x] ordinal1_def_12[of "succ x"] by mauto
       hence X1: "?R(x,g. x)" "?R(succ x,g. (succ x))" using B2 by auto    
       assume X2: "x in succ m"  
       show "g . (succ x) = S (g . x)"
       proof(cases "x in  m")
         case A: True
           hence "x c< m" "succ x c= m" using ordinal1_th_7a ordinal1_th_17 by ty_auto
           hence "g . (succ x) = f . (succ x)" "f. x= g. x" using xboole_0_def_8 X1 by ty_auto   
           thus ?thesis using A B1 by ty_auto
         next 
           case A:False
             hence G1: "x=m" using X2 ordinal1_th_4 by ty_auto
             hence G2: "f. x= g. x" using xboole_0_def_10 X1 by ty_auto
             have "not (succ x) c= m" using ordinal1_th_17[of m m] G1 prefix_in_irreflexive by ty_auto
             hence "g.(succ x)  = S (f. m)" using X1 by auto 
             thus ?thesis using G2 G1 by auto
       qed                
     qed ty_auto
  qed mauto
  show "?P(m)" using ordinal_2_sch_19[of _ ?P,OF _ A0 An] by ty_auto
qed  
     
text_raw {*\DefineSnippet{addM}{*}
mdef addM ("_ +\<^sub>\<S>\<^sup>\<nat> _" [60,61]60) where
 mlet "n be Nat", "m be Nat"   
 "func n +\<^sub>\<S>\<^sup>\<nat> m \<rightarrow> Nat means
    \<lambda>it. \<exists> f: Function-of NAT,NAT. 
          (f.0\<^sub>\<S> =\<^sub>\<S> n \<and> f. m = it \<and> (
   \<forall>k:Nat. k in m \<longrightarrow> f. (succ k) =\<^sub>\<S> succ (f. k)))"  
text_raw {*}%EndSnippet*}
proof-
  have H: "for k be Nat holds (succ k) is Nat"
  proof fix k assume [ty]:"k be Nat" thus "(succ k) be Nat" by mauto
    qed mauto
  obtain  f where [ty]:"f be  Function-of NAT,NAT" and
     A1: "f.{} = n & (for k be Nat st k in m holds f. (succ k) = succ (f. k))" 
    using NAT_sch[of "\<lambda>it. succ it" n m,OF H] by ty_auto
  show "ex IT be Nat st 
 ex f be  Function-of NAT,NAT st 
          f.{} = n & f. m = IT & (for k be Nat st k in m holds f. (succ k) = succ (f. k))"
  proof(rule bexI[of _ "f. m"],rule  bexI[of _ f],intro conjI)
    show "f . {} = n" "\<forall>k : Nat. k in m \<longrightarrow> f . (succ k) = succ f . k" using A1 by auto
    have R:"rng f c= NAT" using relat_1_def_19 by mauto            
        
      have X: "m in omega" using ordinal1_def_12[of m] by ty_auto
      hence "omega<>{}" using xb by auto
      hence "f. m in rng f"  using funct_2_th_4[of _ NAT NAT] X by ty_auto
      hence "f. m in NAT" using R tarski_def_3 by inst_pass_auto
      thus "f. m is Nat" using ordinal1_def_12[of "f. m"] by mauto
  qed mauto 
  fix it1 it2 assume [ty]:"it1 is Nat" "it2 is Nat"
 and B1:
    " ex f be  Function-of NAT,NAT st 
          f.{} = n & f. m = it1 & (for k be Nat st k in m holds f. (succ k) = succ (f. k))"  
    and B2: " ex f be  Function-of NAT,NAT st 
          f.{} = n & f. m = it2 & (for k be Nat st k in m holds f. (succ k) = succ (f. k))"   
  obtain f1 where [ty]:"f1 be  Function-of NAT,NAT" and
       B3:   "f1.{} = n & f1. m = it1 & (for k be Nat st k in m holds f1. (succ k) = succ (f1. k))" using B1 by auto  
  obtain f2 where [ty]:"f2 be  Function-of NAT,NAT" and
       B4:   "f2.{} = n & f2. m = it2 & (for k be Nat st k in m holds f2. (succ k) = succ (f2. k))" using B2 by auto  
  let ?R="\<lambda>it. it c= m implies f1. it=f2. it"
  have R0:"?R({})" using B3 B4 by simp
  have Rn:"for k st ?R(k) holds ?R(succ k)" 
  proof(standard,standard,standard)
    fix k assume [ty]:"k is Nat"
    assume R2:"k \<subseteq> m \<longrightarrow> f1 . k = f2 . k" "succ k \<subseteq> m"
    hence "k in m" using ordinal1_th_17 by ty_auto
    hence "k c<m"" f1. (succ k) = succ (f1. k)" "f2. (succ k) = succ (f2. k)" using B3 B4 ordinal1_th_7a by ty_auto
    thus "f1 . (succ k) = f2 . (succ k)" using xboole_0_def_8 R2 by ty_auto    
  qed mauto
  have "?R(m)" using ordinal_2_sch_19[of _ ?R,OF _ R0 Rn] by ty_auto    
  thus "it1=it2" using xboole_0_def_10[of m m] B3 B4 by ty_auto
qed mauto


lemma [simp]: "1\<^sub>\<S> <>2\<^sub>\<S>" using ordinal1_th_5 by mauto
  
mtheorem Add_1:
  "n +\<^sub>\<S>\<^sup>\<nat> succ m = succ (n +\<^sub>\<S>\<^sup>\<nat> m)"  
proof-
  obtain f1 where [ty]:"f1 be  Function-of NAT,NAT" and
       A1:   "f1.{} = n & f1. (succ m) = n +\<^sub>\<S>\<^sup>\<nat> succ m & (for k be Nat st k in succ m holds f1. (succ k) = succ (f1. k))" 
    using addM[of n "succ m"] by ty_auto
 obtain f2 where [ty]:"f2 be  Function-of NAT,NAT" and
       A2:   "f2.{} = n & f2. m = n +\<^sub>\<S>\<^sup>\<nat> m & (for k be Nat st k in m holds f2. (succ k) = succ (f2. k))" 
   using addM[of n m] by mauto  
  let ?R="\<lambda>it. it c= m implies f1. it=f2. it"
  have R0:"?R({})" using A1 A2 by simp
  have Rn:"for k st ?R(k) holds ?R(succ k)" 
  proof(standard,standard,standard)
    fix k assume [ty]:"k is Nat"
    assume R2:"k \<subseteq> m \<longrightarrow> f1 . k = f2 . k" "succ k \<subseteq> m"
    hence R3: "k in m" using ordinal1_th_17 by ty_auto
    hence "k in succ m" using ordinal1_th_4 by ty_auto
    hence "k c<m" "f1. (succ k) = succ (f1. k)"
       "f2. (succ k) = succ (f2. k)" using A1 A2 ordinal1_th_7a R3 by ty_auto
    thus "f1 . (succ k) = f2 . (succ k)" using xboole_0_def_8 R2 by ty_auto    
  qed mauto
  have "?R(m)" using ordinal_2_sch_19[of _ ?R,OF _ R0 Rn] by ty_auto    
  hence L: "f1. m=f2. m" using xboole_0_def_10[of m m] by ty_auto
  have "m in succ m" using ordinal1_th_4 by ty_auto
  hence "f1. (succ m) = succ (f1. m)" using A1 by ty_auto
  thus ?thesis using L A1 A2 by auto    
qed
  
mtheorem Add_2:
  "(succ n) +\<^sub>\<S>\<^sup>\<nat> m = succ (n +\<^sub>\<S>\<^sup>\<nat> m)"  
proof-
  obtain f1 where [ty]:"f1 be  Function-of NAT,NAT" and
       A1:   "f1.{} = succ n & f1. m = (succ n) +\<^sub>\<S>\<^sup>\<nat>  m & (for k be Nat st k in m holds f1. (succ k) = succ (f1. k))" 
    using addM[of "succ n" m] by ty_auto
 obtain f2 where [ty]:"f2 be  Function-of NAT,NAT" and
       A2:   "f2.{} = n & f2. m = n +\<^sub>\<S>\<^sup>\<nat> m & (for k be Nat st k in m holds f2. (succ k) = succ (f2. k))" 
   using addM[of n m] by mauto  
  let ?R="\<lambda>it. it c= m implies f1. it=succ (f2. it)"
  have R0:"?R({})" using A1 A2 by simp
  have Rn:"for k st ?R(k) holds ?R(succ k)" 
  proof(standard,standard,standard)
    fix k assume [ty]:"k is Nat"
    assume R2:"k \<subseteq> m \<longrightarrow> f1 . k = succ(f2 . k)" "succ k \<subseteq> m"
    hence R3: "k in m" using ordinal1_th_17 by ty_auto
    hence "k in succ m" using ordinal1_th_4 by ty_auto
    hence "k c<m" "f1. (succ k) = succ (f1. k)"
       "f2. (succ k) = succ (f2. k)" using A1 A2 ordinal1_th_7a R3 by ty_auto
    thus "f1 . (succ k) = succ f2 . (succ k)" using xboole_0_def_8 R2 by ty_auto
  qed mauto
  have "?R(m)" using ordinal_2_sch_19[of _ ?R,OF _ R0 Rn] by ty_auto
  hence "f1. m=succ (f2. m)" using xboole_0_def_10[of m m] by ty_auto
  thus ?thesis using A1 A2 by auto    
qed  

mtheorem Add_3:
  "n +\<^sub>\<S>\<^sup>\<nat> {} = n"
proof-
  obtain f1 where [ty]:"f1 be  Function-of NAT,NAT" and
       A1:   "f1.{} = n & f1. {} = n +\<^sub>\<S>\<^sup>\<nat> {} & (for k be Nat st k in {} holds f1. (succ k) = succ (f1. k))" 
    using addM[of n "{}"] by ty_auto
  thus ?thesis by auto
qed  

mtheorem Add_4:
  "{} +\<^sub>\<S>\<^sup>\<nat> n = n"
proof-  
  obtain f1 where [ty]:"f1 be  Function-of NAT,NAT" and
       A1:   "f1.{} = {} & f1. n = {} +\<^sub>\<S>\<^sup>\<nat>  n & (for k be Nat st k in n holds f1. (succ k) = succ (f1. k))" 
    using addM[of "{}" n] by ty_auto
  let ?R="\<lambda>it. it c= n implies f1. it= it"
  have R0:"?R({})" using A1 by simp
  have Rn:"for k st ?R(k) holds ?R(succ k)" 
  proof(standard,standard,standard)
    fix k assume [ty]:"k is Nat"
    assume R2:"k \<subseteq> n \<longrightarrow> f1 . k = k" "succ k \<subseteq> n"
    hence R3: "k in n" using ordinal1_th_17 by ty_auto
    hence "k in succ n" using ordinal1_th_4 by ty_auto
    hence "k c<n" "f1. (succ k) = succ (f1. k)" using A1 ordinal1_th_7a R3 by ty_auto
    thus "f1 . (succ k) = succ k" using xboole_0_def_8 R2 by ty_auto    
  qed mauto
  have "?R(n)" using ordinal_2_sch_19[of _ ?R,OF _ R0 Rn] by ty_auto
  hence "f1. n=n" using xboole_0_def_10[of n n] by ty_auto
  thus ?thesis using A1 by auto    
qed  
  
mtheorem Add_5:
  "(n +\<^sub>\<S>\<^sup>\<nat> 1\<^sub>\<S>) = succ n & 1\<^sub>\<S> +\<^sub>\<S>\<^sup>\<nat> n = succ n"  
proof
  have "n +\<^sub>\<S>\<^sup>\<nat> 1\<^sub>\<S> = succ (n +\<^sub>\<S>\<^sup>\<nat> {})" using Add_1 by ty_auto
  thus "n +\<^sub>\<S>\<^sup>\<nat> 1\<^sub>\<S> = succ n" using Add_3 by ty_auto
  have "1\<^sub>\<S> +\<^sub>\<S>\<^sup>\<nat> n = succ ({} +\<^sub>\<S>\<^sup>\<nat> n)" using Add_2 by ty_auto
  thus "1\<^sub>\<S> +\<^sub>\<S>\<^sup>\<nat> n = succ n" using Add_4 by ty_auto
qed  
  
mtheorem Add_6:
  "n +\<^sub>\<S>\<^sup>\<nat> m = m +\<^sub>\<S>\<^sup>\<nat> n"
proof-
  let ?P="\<lambda>it. n +\<^sub>\<S>\<^sup>\<nat> it = it +\<^sub>\<S>\<^sup>\<nat> n"
  have R0:"?P({})" using Add_3 Add_4 by ty_auto
  have Rn:"for k st ?P(k) holds ?P(succ k)" 
  proof(standard,standard)
    fix k assume [ty]:"k is Nat"
    assume R2:"n +\<^sub>\<S>\<^sup>\<nat> k = k +\<^sub>\<S>\<^sup>\<nat> n"
    have "n +\<^sub>\<S>\<^sup>\<nat> (succ k) = succ (n+\<^sub>\<S>\<^sup>\<nat> k)" "(succ k) +\<^sub>\<S>\<^sup>\<nat> n = succ (k+\<^sub>\<S>\<^sup>\<nat> n)"
      using Add_2 Add_1 by ty_auto
    thus "n +\<^sub>\<S>\<^sup>\<nat> (succ k) = (succ k) +\<^sub>\<S>\<^sup>\<nat> n" using R2 by auto    
  qed mauto
  show "n +\<^sub>\<S>\<^sup>\<nat> m = m +\<^sub>\<S>\<^sup>\<nat> n" using ordinal_2_sch_19[of _ ?P,OF _ R0 Rn] by ty_auto
qed  

mtheorem Add_7:
  "(n +\<^sub>\<S>\<^sup>\<nat> m) +\<^sub>\<S>\<^sup>\<nat> k = n +\<^sub>\<S>\<^sup>\<nat> (m +\<^sub>\<S>\<^sup>\<nat> k)"
proof-
  let ?P="\<lambda>it. for m,k be Nat holds (it +\<^sub>\<S>\<^sup>\<nat> m)+\<^sub>\<S>\<^sup>\<nat> k = it +\<^sub>\<S>\<^sup>\<nat> (m +\<^sub>\<S>\<^sup>\<nat> k)"
  have R0:"?P({})" 
  proof(standard,standard)
    fix m k assume [ty]:"m be Nat" "k be Nat"
    have "{} +\<^sub>\<S>\<^sup>\<nat> m = m" "{}+\<^sub>\<S>\<^sup>\<nat> (m+\<^sub>\<S>\<^sup>\<nat> k) = m +\<^sub>\<S>\<^sup>\<nat> k" using Add_3 Add_4 by infer_auto
    thus "({} +\<^sub>\<S>\<^sup>\<nat> m)+\<^sub>\<S>\<^sup>\<nat> k = {} +\<^sub>\<S>\<^sup>\<nat> (m +\<^sub>\<S>\<^sup>\<nat> k)" by auto   
  qed mauto
  have Rn:"for n st ?P(n) holds ?P(succ n)" 
  proof(intro ballI impI)
    fix n m k assume [ty]:"n is Nat" "m be Nat" "k be Nat" 
    assume R1:"?P(n)"
    have  "((succ n) +\<^sub>\<S>\<^sup>\<nat> m)+\<^sub>\<S>\<^sup>\<nat> k = (succ(n +\<^sub>\<S>\<^sup>\<nat> m))+\<^sub>\<S>\<^sup>\<nat> k" using Add_2 by ty_auto
    also have  "\<dots>= (succ n) +\<^sub>\<S>\<^sup>\<nat> (m+\<^sub>\<S>\<^sup>\<nat> k)" using R1 Add_2 by infer_auto
    finally show  "((succ n) +\<^sub>\<S>\<^sup>\<nat> m)+\<^sub>\<S>\<^sup>\<nat> k = (succ n) +\<^sub>\<S>\<^sup>\<nat> (m+\<^sub>\<S>\<^sup>\<nat> k)" by auto    
  qed mauto
  show ?thesis using ordinal_2_sch_19[of _ ?P,OF _ R0 Rn] by ty_auto
qed  
  
mtheorem Add_8:
  "n in m iff (ex k st k<>{} & m = n+\<^sub>\<S>\<^sup>\<nat> k)"
proof
  let ?P="\<lambda>it. it in m implies  (ex k st k<>{} & m = it+\<^sub>\<S>\<^sup>\<nat> k)"
  have R0:"?P({})" 
  proof(standard)
    assume "{} in m"
    hence "m <> {}" "m={}+\<^sub>\<S>\<^sup>\<nat> m" using xb Add_4 by ty_auto
    thus "ex k st k<>{} & m = {}+\<^sub>\<S>\<^sup>\<nat> k" using bexI[of _ m Nat] by ty_auto
    qed
  have Rn:"for n st ?P(n) holds ?P(succ n)" 
  proof(intro ballI impI)
    fix n assume [ty]:"n is Nat" 
    assume R1:"?P(n)" "succ n in m"
    have "n in succ n" using ordinal1_th_2 by ty_auto
    hence "n in m" using R1 ordinal1_th_6 all_set by ty_auto
    then obtain k where
      [ty]:"k be Nat" and R2: "k<>{} & m = n+\<^sub>\<S>\<^sup>\<nat> k" using R1 by auto
    have "succ (predecessor k) = k" using R2 NAT_1_5 by ty_auto
    hence "m = n +\<^sub>\<S>\<^sup>\<nat> succ(predecessor k)" using R2 by ty_auto
    also have "\<dots> =succ(n +\<^sub>\<S>\<^sup>\<nat> predecessor k)" using Add_1 by infer_auto
    also have "\<dots>=(succ(n))+\<^sub>\<S>\<^sup>\<nat> predecessor k" using Add_2 by infer_auto
    finally have R3: "m = (succ(n))+\<^sub>\<S>\<^sup>\<nat> predecessor k" by simp
    have "m <> succ(n)" using R1 prefix_in_irreflexive by auto    
    hence " predecessor k <> {}" using Add_3 R3 by infer_auto
    thus "ex k st k<>{} & m = (succ n)+\<^sub>\<S>\<^sup>\<nat> k" using R3 bexI[of _ "predecessor k" Nat] by infer_auto
  qed mauto
  show "n in m \<Longrightarrow> \<exists>k : Nat. k \<noteq> {} \<and> m = n +\<^sub>\<S>\<^sup>\<nat> k" using ordinal_2_sch_19[of _ ?P,OF _ R0 Rn] by ty_auto
next 
  assume "\<exists>k : Nat. k \<noteq> {} \<and> m = n +\<^sub>\<S>\<^sup>\<nat> k"
  then obtain k where [ty]:"k be Nat" and
    A0: "k <>{} & m = n+\<^sub>\<S>\<^sup>\<nat> k" by auto
  obtain f1 where [ty]:"f1 be  Function-of NAT,NAT" and
       A1:   "f1.{} = n & f1. k = n +\<^sub>\<S>\<^sup>\<nat> k & (for i be Nat st i in k holds f1. (succ i) = succ (f1. i))" 
    using addM[of n k] by ty_auto

       let ?R="\<lambda>it. it <>{} & it c= k implies n in f1. it"
       have R0:"?R({})" by auto
       have Rn:"for i be Nat st ?R(i) holds ?R(succ i)"
       proof(standard,standard,standard)
         fix i assume [ty]:"i be Nat" and A2:"?R(i)" "succ i <>{} & succ i c= k"
         have "i in k" using ordinal1_th_17 A2 by ty_auto
          hence I: "f1. (succ i) = succ (f1. i)" using A1 by ty_auto
         show "n in f1. (succ i)" 
         proof (cases "i={}")
           case T: True
             thus "n in  f1. (succ i)" using T ordinal1_th_2 A1 I by ty_auto
           next 
             case F: False
             have "i c= succ i" using ordinal1_th_2a by ty_auto
             hence "i c= k" using A2(2) xboole_1_th_1[of k "succ i" i ] by infer_auto
             hence N: "n in f1. i" using A2 F by auto
             have "f1. i  c= succ (f1. i)" using ordinal1_th_2a by infer_auto
             thus "n in f1. (succ i)" using I N tarski_def_3E all_set by ty_auto     
          qed    
        qed mauto
     
  have "?R(k)" using ordinal_2_sch_19[of _ ?R,OF _ R0 Rn] by ty_auto
  thus "n in m" using xboole_0_def_10[of k k] all_set A0 A1 by ty_auto 
qed  

mtheorem Add_9:
  "n c= m iff (ex k st m = n+\<^sub>\<S>\<^sup>\<nat> k)"
proof
  assume A: "n c= m"
  thus "ex k st m = n+\<^sub>\<S>\<^sup>\<nat> k"
  proof(cases "n={}")
    case True
      hence "n+\<^sub>\<S>\<^sup>\<nat> m = m" using Add_4 by mauto
      thus ?thesis using bexI[of _ m Nat] by ty_auto
    next
      let ?p = "predecessor n"
    case False
      hence S: "succ ?p = n" using predec by ty_auto
      hence "?p in m" using ordinal1_th_17 A by infer_auto
      then obtain k where 
         [ty]: "k is Nat" and
         A2: " k<>{} & m = ?p+\<^sub>\<S>\<^sup>\<nat> k" using Add_8[of m] by mauto
      let ?K = "predecessor k"        
      have "succ ?K = k" using predec A2 by mauto 
      hence "m = succ( ?p +\<^sub>\<S>\<^sup>\<nat> ?K)" using A2 Add_1 by inst_pass_auto
      hence "m = n +\<^sub>\<S>\<^sup>\<nat> ?K" using S Add_2 by inst_pass_auto
      thus ?thesis using bexI[of _ ?K Nat] by mauto    
    qed
  next
    assume "ex k st m = n+\<^sub>\<S>\<^sup>\<nat> k"
    then obtain k where 
      [ty]: "k be Nat" and
       A1:"m = n +\<^sub>\<S>\<^sup>\<nat> k" by auto
    show "n c= m"
    proof(cases "k={}")
      case True
        hence "m = n" using A1 Add_3 by ty_auto
        thus ?thesis using xboole_0_def_10 by mauto
    next
       let ?p = "predecessor n"
       case False
         hence "ex k be Nat st k \<noteq> {} \<and> m = n +\<^sub>\<S>\<^sup>\<nat> k" using A1 bexI[of _ k Nat]by mauto
         hence "n in m" using Add_8[of m n,THEN iffD2] A1 by mauto  
         thus ?thesis using ordinal1_def_2E by ty_auto
   qed   
 qed  
   
mtheorem Add_10:
  "n c= n +\<^sub>\<S>\<^sup>\<nat> m"
proof-
  have "ex k st n+\<^sub>\<S>\<^sup>\<nat> m = n+\<^sub>\<S>\<^sup>\<nat> k" using bexI[of _ m Nat] by ty_auto
  thus "n c= n+\<^sub>\<S>\<^sup>\<nat> m" using Add_9 by ty_auto
qed  
  
mtheorem Add_11:
  "n +\<^sub>\<S>\<^sup>\<nat> m = n +\<^sub>\<S>\<^sup>\<nat> k implies m=k"
proof
  assume AS: "n +\<^sub>\<S>\<^sup>\<nat> m = n +\<^sub>\<S>\<^sup>\<nat> k"
  let ?P="\<lambda>it. for m,k be Nat st m c= it & k c= it & n +\<^sub>\<S>\<^sup>\<nat> m = n +\<^sub>\<S>\<^sup>\<nat> k holds m=k"
  have R0:"?P({})" 
  proof(intro ballI impI)
    fix m k assume [ty]:"m be Nat" "k be Nat"
    have A1: "{} c= m" "{} c= k" using xb tarski_def_3I by ty_auto
    assume "m \<subseteq> {} \<and> k \<subseteq> {} \<and> n +\<^sub>\<S>\<^sup>\<nat> m = n +\<^sub>\<S>\<^sup>\<nat> k"
    hence "m={} \<and> k={}" using A1 xboole_0_def_10 by ty_auto
    thus "m=k" by simp
  qed mauto
  have Rn:"for k st ?P(k) holds ?P(succ k)" 
  proof(standard,standard,intro ballI impI)
    fix k assume [ty]:"k is Nat"
    assume R2:"?P(k)"
    fix m ka assume [ty]:"m be Nat" "ka be Nat"
    assume A1: "m \<subseteq> succ k \<and> ka \<subseteq> succ k \<and> n +\<^sub>\<S>\<^sup>\<nat> m = n +\<^sub>\<S>\<^sup>\<nat> ka"
    show "m=ka"
    proof(cases "m c= k")
      case T:True
         show "m=ka"
         proof(cases "ka c= k")
           case True 
             thus "m=ka" using T A1 R2 by ty_auto
           next
             case False
               hence A: "ka = succ k" using A1  ordinal1s[of ka k] by ty_auto
               hence A3:" n +\<^sub>\<S>\<^sup>\<nat> m = n +\<^sub>\<S>\<^sup>\<nat> succ k" using A1 Add_1 by auto 
               hence A4: "n +\<^sub>\<S>\<^sup>\<nat> m =succ(n +\<^sub>\<S>\<^sup>\<nat> k)" using Add_1 by ty_auto
               have "succ k <>{}" using xb ordinal1_th_2 by auto
               hence " n in n +\<^sub>\<S>\<^sup>\<nat> m" using A3 Add_8[of "n +\<^sub>\<S>\<^sup>\<nat> m" n] bexI[of _ "succ k" Nat] by infer_auto
               hence "m<>{}" using prefix_in_irreflexive Add_3 by ty_auto
               hence A7: "m = succ (predecessor m)" using NAT_1_5 by ty_auto
               hence "n +\<^sub>\<S>\<^sup>\<nat> m = succ(n +\<^sub>\<S>\<^sup>\<nat> predecessor m)" using Add_1[of "predecessor m" n] by infer_auto
               hence A6:"n +\<^sub>\<S>\<^sup>\<nat> predecessor m = n +\<^sub>\<S>\<^sup>\<nat> k" using A4 ordinal1_succ[of  "n +\<^sub>\<S>\<^sup>\<nat> k" "n +\<^sub>\<S>\<^sup>\<nat> predecessor m"]  all_set by ty_auto
              
               have "predecessor m in succ k" using ordinal1_th_17 A1 A7 by infer_auto
               hence "predecessor m c= k" "k c=k" using ordinal1_th_18 xboole_0_def_10[of k k ] by infer_auto
               hence "predecessor m = k " using A6 R2 by infer_auto
               thus "m=ka" using A7 A by auto
          qed
        next
          case T:False
          hence T1:"m=succ k" using A1  ordinal1s[of m k] by ty_auto
          hence A3:" n +\<^sub>\<S>\<^sup>\<nat> succ k = n +\<^sub>\<S>\<^sup>\<nat> ka" using A1 Add_1 by auto 
          hence A4: "succ(n +\<^sub>\<S>\<^sup>\<nat> k) =n +\<^sub>\<S>\<^sup>\<nat> ka" using Add_1 by ty_auto
          have "succ k <>{}" using xb ordinal1_th_2 by auto
          hence " n in n +\<^sub>\<S>\<^sup>\<nat> ka" using A3 Add_8[of "n +\<^sub>\<S>\<^sup>\<nat> ka" n] bexI[of _ "succ k" Nat] by infer_auto
          hence "ka<>{}" using prefix_in_irreflexive Add_3 by ty_auto
          hence A7: "ka = succ (predecessor ka)" using NAT_1_5 by ty_auto
          hence "n +\<^sub>\<S>\<^sup>\<nat> ka= succ(n +\<^sub>\<S>\<^sup>\<nat> predecessor ka)" using Add_1[of "predecessor ka" n] by infer_auto
          hence A6:"n +\<^sub>\<S>\<^sup>\<nat> predecessor ka = n +\<^sub>\<S>\<^sup>\<nat> k" using A4 ordinal1_succ[of  "n +\<^sub>\<S>\<^sup>\<nat> k" "n +\<^sub>\<S>\<^sup>\<nat> predecessor ka"]  all_set by ty_auto
          have "predecessor ka in succ k" using ordinal1_th_17 A1 A7 by infer_auto
          hence "predecessor ka c= k" "k c=k" using ordinal1_th_18 xboole_0_def_10[of k k ] by infer_auto
          hence "predecessor ka = k " using A6 R2 by infer_auto
          thus "m=ka" using A7 T1 by auto
        qed
  qed mauto
  have A[THEN bspec,THEN bspec]: "?P(k)" "?P(m)" using ordinal_2_sch_19[of k ?P,OF _ R0 Rn] ordinal_2_sch_19[of m ?P,OF _ R0 Rn] 
      by ty_auto
  have A1: "k c= k" "m c= m" using xboole_0_def_10[of k k] xboole_0_def_10[of m m] by ty_auto
  have "m c= k \<or> k c= m" using ordinal1_def_5c by ty_auto
  thus "m=k" using A(1)[of m k] A(2)[of m k] A1 AS by ty_auto 
qed

mtheorem Add_12:
  "n in m implies k +\<^sub>\<S>\<^sup>\<nat> n in k +\<^sub>\<S>\<^sup>\<nat> m"
proof
  assume A1: "n in m"
  then obtain w where
    [ty]:"w be Nat" and A2: "w<>{} & m = n+\<^sub>\<S>\<^sup>\<nat> w" using Add_8 by ty_auto
  have "k +\<^sub>\<S>\<^sup>\<nat> m = (k +\<^sub>\<S>\<^sup>\<nat> n) +\<^sub>\<S>\<^sup>\<nat> w" using A2 Add_7 by ty_auto
  thus "k +\<^sub>\<S>\<^sup>\<nat> n in k +\<^sub>\<S>\<^sup>\<nat> m" using Add_8 A2 bexI[of _ w Nat] by infer_auto
qed

mtheorem Add_13:
  "n c= m iff k +\<^sub>\<S>\<^sup>\<nat> n c= k +\<^sub>\<S>\<^sup>\<nat> m"
proof
  assume A1: "n c= m"
  then obtain w where
    [ty]:"w be Nat" and A2: "m = n+\<^sub>\<S>\<^sup>\<nat> w" using Add_9 by ty_auto
  have "k +\<^sub>\<S>\<^sup>\<nat> m = (k +\<^sub>\<S>\<^sup>\<nat> n) +\<^sub>\<S>\<^sup>\<nat> w" using A2 Add_7 by ty_auto
  thus "k +\<^sub>\<S>\<^sup>\<nat> n c= k +\<^sub>\<S>\<^sup>\<nat> m" using Add_9 A2 bexI[of _ w Nat] by infer_auto
next 
  assume "k +\<^sub>\<S>\<^sup>\<nat> n c= k +\<^sub>\<S>\<^sup>\<nat> m"
  then obtain w where
    [ty]:"w be Nat" and A2: "k +\<^sub>\<S>\<^sup>\<nat> m = (k +\<^sub>\<S>\<^sup>\<nat> n)+\<^sub>\<S>\<^sup>\<nat> w" using Add_9 by ty_auto
  have "(k +\<^sub>\<S>\<^sup>\<nat> n)+\<^sub>\<S>\<^sup>\<nat> w = k +\<^sub>\<S>\<^sup>\<nat> (n +\<^sub>\<S>\<^sup>\<nat> w)" using Add_7 by ty_auto
  hence "m = n+\<^sub>\<S>\<^sup>\<nat> w" using A2 Add_11[of "n+\<^sub>\<S>\<^sup>\<nat> w" m k] by infer_auto
  thus "n c= m" using Add_9 bexI[of _ w Nat] by infer_auto
qed

mtheorem Add_14:
  "n +\<^sub>\<S>\<^sup>\<nat> m ={} implies n={} & m={}" 
proof(rule impI)
  have A1: "{} c= n"  "{} c= m" using tarski_def_3 xb by ty_auto
  assume "n+\<^sub>\<S>\<^sup>\<nat> m ={}"
  hence "n c= {}" "m c= {}" using Add_10[of n m] Add_10[of m n] Add_6[of n m] by ty_auto
  then show "n={} & m={}" using A1 xboole_0_def_10 by ty_auto
qed
text_raw {*\DefineSnippet{multM}{*}
mdef multNat ("_ *\<^sub>\<S>\<^sup>\<nat> _" [91,90] 90) where
 mlet "n be Nat", "m be Nat"   
 "func n *\<^sub>\<S>\<^sup>\<nat> m \<rightarrow> Nat means
    \<lambda>it. \<exists> f:Function-of NAT,NAT. 
          (f.0\<^sub>\<S> =\<^sub>\<S> 0\<^sub>\<S> & f. m =\<^sub>\<S> it & (\<forall> k:Nat. k in m \<longrightarrow> f. (succ k) =\<^sub>\<S> (f. k) +\<^sub>\<S>\<^sup>\<nat> n))"  
text_raw {*}%EndSnippet*}
proof-
  have H: "for k be Nat holds (k+\<^sub>\<S>\<^sup>\<nat> n) is Nat"
  proof fix k assume [ty]:"k be Nat" thus "(k+\<^sub>\<S>\<^sup>\<nat> n) be Nat" by mauto
    qed mauto
  obtain  f where [ty]:"f be  Function-of NAT,NAT" and
     A1: "f.{} = {} & (for k be Nat st k in m holds f. (succ k) =  (f. k)+\<^sub>\<S>\<^sup>\<nat> n)" 
    using NAT_sch[of "\<lambda>it. it+\<^sub>\<S>\<^sup>\<nat> n" "{}" m,OF H] by ty_auto
  show "ex IT be Nat st 
 ex f be  Function-of NAT,NAT st 
          f.{} = {} & f. m = IT & (for k be Nat st k in m holds f. (succ k) = (f. k)+\<^sub>\<S>\<^sup>\<nat> n)"
  proof(rule bexI[of _ "f. m"],rule  bexI[of _ f],intro conjI)
    show "f . {} = {}" "\<forall>k : Nat. k in m \<longrightarrow> f . (succ k) = (f . k) +\<^sub>\<S>\<^sup>\<nat> n" using A1 by auto
    have R:"rng f c= NAT" using relat_1_def_19 by mauto            
        
      have X: "m in omega" using ordinal1_def_12[of m] by ty_auto
      hence "omega<>{}" using xb by auto
      hence "f. m in rng f"  using funct_2_th_4[of _ NAT NAT] X by ty_auto
      hence "f. m in NAT" using R tarski_def_3 by infer_auto
      thus "f. m is Nat" using ordinal1_def_12[of "f. m"] by infer_auto 
  qed mauto 
  fix it1 it2 assume [ty]:"it1 is Nat" "it2 is Nat"
 and B1:
    " ex f be  Function-of NAT,NAT st 
          f.{} = {} & f. m = it1 & (for k be Nat st k in m holds f. (succ k) = (f. k)+\<^sub>\<S>\<^sup>\<nat> n)"  
    and B2: " ex f be  Function-of NAT,NAT st 
          f.{} = {} & f. m = it2 & (for k be Nat st k in m holds f. (succ k) = (f. k)+\<^sub>\<S>\<^sup>\<nat> n)"   
  obtain f1 where [ty]:"f1 be  Function-of NAT,NAT" and
       B3:   "f1.{} = {} & f1. m = it1 & (for k be Nat st k in m holds f1. (succ k) = (f1. k)+\<^sub>\<S>\<^sup>\<nat> n)" using B1 by auto  
  obtain f2 where [ty]:"f2 be  Function-of NAT,NAT" and
       B4:   "f2.{} = {} & f2. m = it2 & (for k be Nat st k in m holds f2. (succ k) = (f2. k)+\<^sub>\<S>\<^sup>\<nat> n)" using B2 by auto  
  let ?R="\<lambda>it. it c= m implies f1. it=f2. it"
  have R0:"?R({})" using B3 B4 by simp
  have Rn:"for k st ?R(k) holds ?R(succ k)" 
  proof(standard,standard,standard)
    fix k assume [ty]:"k is Nat"
    assume R2:"k \<subseteq> m \<longrightarrow> f1 . k = f2 . k" "succ k \<subseteq> m"
    hence "k in m" using ordinal1_th_17 by ty_auto
    hence "k c<m"" f1. (succ k) = (f1. k)+\<^sub>\<S>\<^sup>\<nat> n " "f2. (succ k) = (f2. k)+\<^sub>\<S>\<^sup>\<nat> n" using B3 B4 ordinal1_th_7a by ty_auto
    thus "f1 . (succ k) = f2 . (succ k)" using xboole_0_def_8 R2 by ty_auto    
  qed mauto
  have "?R(m)" using ordinal_2_sch_19[of _ ?R,OF _ R0 Rn] by ty_auto
  thus "it1=it2" using xboole_0_def_10[of m m] B3 B4 by ty_auto
qed mauto 

mtheorem Mult_1:
  "{} *\<^sub>\<S>\<^sup>\<nat> n = {}"
proof-  
  obtain f1 where [ty]:"f1 be  Function-of NAT,NAT" and
       A1:   "f1.{} = {} & f1. n = {} *\<^sub>\<S>\<^sup>\<nat>  n & (for k be Nat st k in n holds f1. (succ k) = (f1. k)+\<^sub>\<S>\<^sup>\<nat> {})" 
    using multNat[of "{}" n] by ty_auto
  let ?R="\<lambda>it. it c= n implies f1. it= {}"
  have R0:"?R({})" using A1 by simp
  have Rn:"for k st ?R(k) holds ?R(succ k)" 
  proof(standard,standard,standard)
    fix k assume [ty]:"k is Nat"
    assume R2:"k \<subseteq> n \<longrightarrow> f1 . k = {}" "succ k \<subseteq> n"
    hence R3: "k in n" using ordinal1_th_17 by ty_auto
    hence "k in succ n" using ordinal1_th_4 by ty_auto
    hence "k c<n" "f1. (succ k) = (f1. k)+\<^sub>\<S>\<^sup>\<nat> {}" using A1 ordinal1_th_7a R3 by ty_auto
    thus "f1 . (succ k) = {}" using Add_3 xboole_0_def_8 R2 by ty_auto    
  qed mauto
  have "?R(n)" using ordinal_2_sch_19[of _ ?R,OF _ R0 Rn] by ty_auto
  hence "f1. n={}" using xboole_0_def_10[of n n] by ty_auto
  thus ?thesis using A1 by auto    
qed  
  
mtheorem Mult_2:
  "n *\<^sub>\<S>\<^sup>\<nat> {} = {}"
proof-
  obtain f1 where [ty]:"f1 be  Function-of NAT,NAT" and
       A1:   "f1.{} = {} & f1. {} = n *\<^sub>\<S>\<^sup>\<nat> {} & (for k be Nat st k in {} holds f1. (succ k) = (f1. k)+\<^sub>\<S>\<^sup>\<nat> n)" 
    using multNat[of n "{}"] by ty_auto
  thus ?thesis by auto
qed 

mtheorem Mult_3:
  "(n *\<^sub>\<S>\<^sup>\<nat> succ m) = (n *\<^sub>\<S>\<^sup>\<nat> m) +\<^sub>\<S>\<^sup>\<nat> n"  
proof-
  obtain f1 where [ty]:"f1 be  Function-of NAT,NAT" and
       A1:   "f1.{} = {} & f1. (succ m) = n *\<^sub>\<S>\<^sup>\<nat> succ m & (for k be Nat st k in succ m holds 
   f1. (succ k) = (f1. k)+\<^sub>\<S>\<^sup>\<nat> n)" 
    using multNat[of n "succ m"] by ty_auto
 obtain f2 where [ty]:"f2 be  Function-of NAT,NAT" and
       A2:   "f2.{} = {} & f2. m = n *\<^sub>\<S>\<^sup>\<nat> m & (for k be Nat st k in m holds f2. (succ k) = (f2. k)+\<^sub>\<S>\<^sup>\<nat> n)" 
   using multNat[of n m] by mauto  
  let ?R="\<lambda>it. it c= m implies f1. it=f2. it"
  have R0:"?R({})" using A1 A2 by simp
  have Rn:"for k st ?R(k) holds ?R(succ k)" 
  proof(standard,standard,standard)
    fix k assume [ty]:"k is Nat"
    assume R2:"k \<subseteq> m \<longrightarrow> f1 . k = f2 . k" "succ k \<subseteq> m"
    hence R3: "k in m" using ordinal1_th_17 by ty_auto
    hence "k in succ m" using ordinal1_th_4 by ty_auto
    hence "k c<m" "f1. (succ k) = (f1. k)+\<^sub>\<S>\<^sup>\<nat> n"
       "f2. (succ k) = (f2. k)+\<^sub>\<S>\<^sup>\<nat> n" using A1 A2 ordinal1_th_7a R3 by ty_auto
    thus "f1 . (succ k) = f2 . (succ k)" using xboole_0_def_8 R2 by ty_auto    
  qed mauto
  have "?R(m)" using ordinal_2_sch_19[of _ ?R,OF _ R0 Rn] by ty_auto
  hence L: "f1. m=f2. m" using xboole_0_def_10[of m m] by ty_auto
  have "m in succ m" using ordinal1_th_4 by ty_auto
  hence "f1. (succ m) = (f1. m)+\<^sub>\<S>\<^sup>\<nat> n" using A1 by ty_auto
  thus ?thesis using L A1 A2 by auto    
qed
  
mtheorem Mult_4:
  "(succ n) *\<^sub>\<S>\<^sup>\<nat> m = (n *\<^sub>\<S>\<^sup>\<nat> m) +\<^sub>\<S>\<^sup>\<nat> m"  
proof-
  obtain f1 where [ty]:"f1 be  Function-of NAT,NAT" and
       A1:   "f1.{} = {} & f1. m = (succ n) *\<^sub>\<S>\<^sup>\<nat>  m & (for k be Nat st k in m holds f1. (succ k) = 
        (f1. k)+\<^sub>\<S>\<^sup>\<nat> (succ n))" 
    using multNat[of "succ n" m] by ty_auto
 obtain f2 where [ty]:"f2 be  Function-of NAT,NAT" and
       A2:   "f2.{} = {} & f2. m = n *\<^sub>\<S>\<^sup>\<nat> m & (for k be Nat st k in m holds 
        f2. (succ k) = (f2. k)+\<^sub>\<S>\<^sup>\<nat> n)" 
   using multNat[of n m] by mauto  
  let ?R="\<lambda>it. it c= m implies f1. it = (f2. it)+\<^sub>\<S>\<^sup>\<nat> it"
  have "{} +\<^sub>\<S>\<^sup>\<nat> {} = {}" using Add_4 by ty_auto
  hence R0:"?R({})" using A1 A2 by simp
  have Rn:"for k st ?R(k) holds ?R(succ k)" 
  proof(standard,standard,standard)
    fix k assume [ty]:"k is Nat"
    assume R2:"k \<subseteq> m \<longrightarrow> f1 . k = (f2 . k)+\<^sub>\<S>\<^sup>\<nat> k" "succ k \<subseteq> m"
    hence R3: "k in m" using ordinal1_th_17 by ty_auto
    hence "k in succ m" using ordinal1_th_4 by ty_auto
    hence R4:"k c<m" "f1. (succ k) = (f1. k)+\<^sub>\<S>\<^sup>\<nat> (succ n)"
       "f2. (succ k) = (f2. k)+\<^sub>\<S>\<^sup>\<nat> n" using A1 A2 ordinal1_th_7a R3 by ty_auto
    hence "f1.(succ k) = succ (((f2. k)+\<^sub>\<S>\<^sup>\<nat> k)+\<^sub>\<S>\<^sup>\<nat> n)" using xboole_0_def_8 R2 Add_1 by infer_auto
    also have "\<dots> = succ ((f2. (succ k))+\<^sub>\<S>\<^sup>\<nat> k)"
      apply infer_ty using Add_6 Add_7 R4 by ty_auto
      (* !!! Do this for now until I figure out how to programatically add thms as [intro] *)
    finally show "f1 . (succ k) = (f2 . (succ k)) +\<^sub>\<S>\<^sup>\<nat> (succ k) " using Add_1 Add_2 by infer_auto
  qed mauto
  have "?R(m)" using ordinal_2_sch_19[of _ ?R,OF _ R0 Rn] by ty_auto
  hence "f1. m=(f2. m)+\<^sub>\<S>\<^sup>\<nat> m" using xboole_0_def_10[of m m] by ty_auto
  thus ?thesis using A1 A2 by auto    
qed    

mtheorem Mult_5:
  "n *\<^sub>\<S>\<^sup>\<nat> 1\<^sub>\<S> = n & 1\<^sub>\<S> *\<^sub>\<S>\<^sup>\<nat> n = n"  
proof
  have "n *\<^sub>\<S>\<^sup>\<nat> 1\<^sub>\<S> = (n *\<^sub>\<S>\<^sup>\<nat> {}) +\<^sub>\<S>\<^sup>\<nat> n" using Mult_3 by ty_auto
  thus "n *\<^sub>\<S>\<^sup>\<nat> 1\<^sub>\<S> = n" using Add_4 Mult_2 by ty_auto
  have "1\<^sub>\<S> *\<^sub>\<S>\<^sup>\<nat> n = ({} *\<^sub>\<S>\<^sup>\<nat> n)+\<^sub>\<S>\<^sup>\<nat> n" using Mult_4 by ty_auto
  thus "1\<^sub>\<S> *\<^sub>\<S>\<^sup>\<nat> n = n" using Add_4 Mult_1 by ty_auto
qed  
  
mtheorem Mult_6:
  "n *\<^sub>\<S>\<^sup>\<nat> m = m *\<^sub>\<S>\<^sup>\<nat> n"
proof-
  let ?P="\<lambda>it. n *\<^sub>\<S>\<^sup>\<nat> it = it *\<^sub>\<S>\<^sup>\<nat> n"
  have R0:"?P({})" using Mult_1 Mult_2 by ty_auto
  have Rn:"for k st ?P(k) holds ?P(succ k)" 
  proof(standard,standard)
    fix k assume [ty]:"k is Nat"
    assume R2:"n *\<^sub>\<S>\<^sup>\<nat> k = k *\<^sub>\<S>\<^sup>\<nat> n"
    have "n *\<^sub>\<S>\<^sup>\<nat> (succ k) = (n*\<^sub>\<S>\<^sup>\<nat> k)+\<^sub>\<S>\<^sup>\<nat> n" "(succ k) *\<^sub>\<S>\<^sup>\<nat> n = (k*\<^sub>\<S>\<^sup>\<nat> n)+\<^sub>\<S>\<^sup>\<nat> n"
      using Mult_3[of  k n] Mult_4[of n k] by ty_auto
    thus "n *\<^sub>\<S>\<^sup>\<nat> (succ k) = (succ k) *\<^sub>\<S>\<^sup>\<nat> n" using R2 by auto    
  qed mauto
  show "n *\<^sub>\<S>\<^sup>\<nat> m = m *\<^sub>\<S>\<^sup>\<nat> n" using ordinal_2_sch_19[of _ ?P,OF _ R0 Rn] by ty_auto    
qed  

mtheorem Mult_7:
  "m <> {} implies n c= n *\<^sub>\<S>\<^sup>\<nat> m"
proof-
   let ?R="\<lambda>it. it <> {} implies n c= n *\<^sub>\<S>\<^sup>\<nat> it"
   have R0:"?R({})" by simp
  have Rn:"for k st ?R(k) holds ?R(succ k)" 
  proof(standard,standard,standard)
    fix k assume [ty]:"k is Nat"
    assume R2:"k <> {} implies n c= n *\<^sub>\<S>\<^sup>\<nat> k" "succ k <> {}"
    show "n c= n *\<^sub>\<S>\<^sup>\<nat> succ k"
    proof(cases "k={}")
      case True
        hence "n *\<^sub>\<S>\<^sup>\<nat> succ k = n" using Mult_5 by mauto
        thus ?thesis using xboole_0_def_10 by mauto
      next case False
        hence N1: "n c= n *\<^sub>\<S>\<^sup>\<nat> k" using R2 by auto
        have "n *\<^sub>\<S>\<^sup>\<nat> k = k *\<^sub>\<S>\<^sup>\<nat> n" using Mult_6[of n k] by mauto
        hence "(n *\<^sub>\<S>\<^sup>\<nat> k) +\<^sub>\<S>\<^sup>\<nat> n = (succ k) *\<^sub>\<S>\<^sup>\<nat> n" using Mult_4 by mauto 
        hence " n *\<^sub>\<S>\<^sup>\<nat> k c= (succ k) *\<^sub>\<S>\<^sup>\<nat> n" using Add_10 by mauto
        hence "n c=  (succ k) *\<^sub>\<S>\<^sup>\<nat> n" using N1 xboole_1_th_1[of "(succ k) *\<^sub>\<S>\<^sup>\<nat> n" "n *\<^sub>\<S>\<^sup>\<nat> k"] 
          by infer_auto
         thus ?thesis using Mult_6[of n] by infer_auto
    qed     
  qed mauto
  have "?R(m)" using ordinal_2_sch_19[of _ ?R,OF _ R0 Rn] by ty_auto
   thus ?thesis by auto    
 qed


lemma one:"1\<^sub>\<S> ={ {} }" 
proof
  fix x 
  have "x in 1\<^sub>\<S> iff x = {} or x in {}" using  ordinal1_th_4 by infer_auto
  hence "x in 1\<^sub>\<S> iff x = {}" using xb by auto
  thus "x in 1\<^sub>\<S> iff x in {{}}" using tarski_def_1 by auto
qed mauto

mlemma one1: "1\<^sub>\<S> c= n iff {} in n"
proof(rule iffI3)
  have "{} in 1\<^sub>\<S>" using one tarski_def_1 by auto  
  thus "1\<^sub>\<S> \<subseteq> n \<longrightarrow> {} in n" using tarski_def_3E[of "1\<^sub>\<S>" n] by ty_auto
  assume "{} in n"
  thus "1\<^sub>\<S> c= n" using one tarski_def_3I[of "1\<^sub>\<S>" n] tarski_def_1 by infer_auto
qed  

mlemma one2:" 1\<^sub>\<S> c= n iff n\<noteq> {}"
proof(rule iffI3)
  have "{} in 1\<^sub>\<S>" using one tarski_def_1 by auto  
  thus "1\<^sub>\<S> \<subseteq> n \<longrightarrow> n\<noteq>{}" using tarski_def_3E[of "1\<^sub>\<S>" n] xb by ty_auto
  assume "n\<noteq>{}"
  hence "{} in n" using xb ordinal1_th_10 by ty_auto
  thus "1\<^sub>\<S> c= n" using one1 by ty_auto
qed
  
mtheorem Mult_8:
  "n *\<^sub>\<S>\<^sup>\<nat> m = 1\<^sub>\<S> implies n=1\<^sub>\<S> & m=1\<^sub>\<S>"
proof
  assume A1: "n *\<^sub>\<S>\<^sup>\<nat> m = 1\<^sub>\<S>"
  hence A2: "m<>{}" "n<>{}" using Mult_1 Mult_2 by ty_auto
  hence "m c= 1\<^sub>\<S>" "n c= 1\<^sub>\<S>" "1\<^sub>\<S>={{}}" using A1 Mult_7[of m n] Mult_7[of  n m] Mult_6[of n m] one by ty_auto
  thus "n=1\<^sub>\<S> & m=1\<^sub>\<S>" using zfmisc_1_th_33 A2 by ty_auto
qed

mtheorem Mult_9:
  "n *\<^sub>\<S>\<^sup>\<nat> m = {} implies n={} or m={}"
proof
  assume A1: "n *\<^sub>\<S>\<^sup>\<nat> m ={}"
  have "n<>{} implies m={}"
  proof
    assume "n<>{}"
    then have "m c= {}" "{} c= m" using A1 Mult_6[of n m] Mult_7[of m n] tarski_def_3 xb by ty_auto
    then show "m = {}" using xboole_0_def_10 by ty_auto
  qed
  then show "n={} or m={}" by blast  
qed

mtheorem Mult_10:
  "n *\<^sub>\<S>\<^sup>\<nat> m = n & n<>{} implies m = 1\<^sub>\<S>"
proof
  let ?p = "predecessor m"
  assume A1: "n *\<^sub>\<S>\<^sup>\<nat> m = n & n<>{}"
  hence "m<>{}" using Mult_2 by ty_auto
  hence A2: "succ ?p  = m" using NAT_1_5 by ty_auto
  hence "n = (n *\<^sub>\<S>\<^sup>\<nat> ?p) +\<^sub>\<S>\<^sup>\<nat> n" using Mult_3[of ?p n] A1 by infer_auto
  hence "n = n +\<^sub>\<S>\<^sup>\<nat> (n *\<^sub>\<S>\<^sup>\<nat> ?p)" using Add_6 by infer_auto
  hence "n in n or n *\<^sub>\<S>\<^sup>\<nat> ?p ={}" using Add_8 bexI[of _ "n *\<^sub>\<S>\<^sup>\<nat> ?p" Nat] A1 by infer_auto
  hence "n *\<^sub>\<S>\<^sup>\<nat> ?p = {}" using prefix_in_irreflexive by auto
  hence "?p={}" using A1 Mult_9[of ?p n] by infer_auto
  then show "m=1\<^sub>\<S>" using A2 by auto
qed


  
mdef div (infixl "divides" 60) where
  mlet "n be Nat", "k be Nat"
  "pred n divides k means ex m be Nat st n *\<^sub>\<S>\<^sup>\<nat> m = k".

mtheorem div_1:
  " n divides {}"
proof-
  have " n *\<^sub>\<S>\<^sup>\<nat> {} = {}" using Mult_2 by mauto
  thus ?thesis using divI[of n "{}"] bexI[of _ "{}" Nat] by ty_auto
qed  
 
  
mtheorem div_2:
  " n divides k & k<>{} implies n c= k & n <> {}"
proof
  assume A1: "n divides k & k <>{}"
  then obtain m where
      [ty]: "m be Nat" and
       A2:  "n *\<^sub>\<S>\<^sup>\<nat> m = k" using div by ty_auto
  hence "m<>{}" using Mult_2 A1 by mauto    
  thus "n c= k & n<>{}" using A1 A2 Mult_7[of n m] Mult_1 by ty_auto
qed  
  
mdef primeS ("prime\<^sub>\<S>") where
  "attr prime\<^sub>\<S> for Nat means 
     (\<lambda>it. 1\<^sub>\<S> in it & (for n be Nat st n divides it holds (n = 1\<^sub>\<S> or n=\<^sub>\<S>it)))".

reserve p for Nat
mtheorem div_one:
  " n divides 1\<^sub>\<S> iff n = 1\<^sub>\<S>"
proof(standard)
  assume A1: "n divides 1\<^sub>\<S>"
  then obtain m where
      [ty]: "m be Nat" and
       A2:  "n *\<^sub>\<S>\<^sup>\<nat> m = 1\<^sub>\<S>" using div by ty_auto
  show "n=1\<^sub>\<S>" using Mult_8[OF _ _ A2] by ty_auto
next
  assume "n = 1\<^sub>\<S>"
  hence "n *\<^sub>\<S>\<^sup>\<nat> 1\<^sub>\<S> = 1\<^sub>\<S>" using Mult_5 by ty_auto
  thus "n divides 1\<^sub>\<S>" using divI bexI[of _ "1\<^sub>\<S>" Nat] by ty_auto
qed

mtheorem prime_eq_irreducible:
  "p is primeS iff p <> {} & not p divides 1\<^sub>\<S> & (for n,m be Nat st p = n*\<^sub>\<S>\<^sup>\<nat> m holds n divides 1\<^sub>\<S> or m divides 1\<^sub>\<S>)"
proof(rule iffI2)
  show "p is primeS implies p <> {} & not p divides 1\<^sub>\<S> & (for n,m be Nat st p = n*\<^sub>\<S>\<^sup>\<nat> m holds n divides 1\<^sub>\<S> or m divides 1\<^sub>\<S>)"
  proof(intro impI conjI ballI)
    assume A1:"p is primeS"
    then show P0: "p<>{}" using xb primeS by ty_auto
    have "1\<^sub>\<S> in p" using A1 primeS by ty_auto
    have "p<>1\<^sub>\<S>" using A1 primeS prefix_in_irreflexive by ty_auto
    then show "not p divides 1\<^sub>\<S>" using div_one by ty_auto
    fix n m
    assume [ty]: "n be Nat" "m be Nat" and A3: "p = n*\<^sub>\<S>\<^sup>\<nat> m"
    hence "n divides p" using div bexI[of _ m Nat]  by infer_auto
    hence N: "n= 1\<^sub>\<S> or n=p" using A1 primeS by ty_auto
    have "not n divides 1\<^sub>\<S> implies m divides 1\<^sub>\<S>"
    proof
      assume "not n divides 1\<^sub>\<S>"
      hence "n<>1\<^sub>\<S>" using div_one by ty_auto
      hence "n=p" using N by auto
      hence "m=1\<^sub>\<S>" using Mult_10[of m p] P0 A3 by ty_auto
      then show "m divides 1\<^sub>\<S>" using div_one by ty_auto
    qed
    then show "n divides 1\<^sub>\<S> or m divides 1\<^sub>\<S>" by blast
  qed mauto
  show "p <> {} & not p divides 1\<^sub>\<S> & (for n,m be Nat st p = n*\<^sub>\<S>\<^sup>\<nat> m holds n divides 1\<^sub>\<S> or m divides 1\<^sub>\<S>) 
      implies p is primeS"
  proof(standard,rule primeSI,simp)
    assume A1:"p <> {} & not p divides 1\<^sub>\<S> & (for n,m be Nat st p = n*\<^sub>\<S>\<^sup>\<nat> m holds n divides 1\<^sub>\<S> or m divides 1\<^sub>\<S>)"
    hence "not p in 1\<^sub>\<S> & p <>1\<^sub>\<S>" using div_one one tarski_def_1 by ty_auto
    then show "1\<^sub>\<S> in p" using ordinal1_th_10 by ty_auto
    show "for n be Nat st n divides p holds n = 1\<^sub>\<S> or n = p"
    proof(intro ballI impI)
      fix n assume [ty]: "n be Nat" and A2: "n divides p"
      have "n <> 1\<^sub>\<S> implies n = p"
      proof
        assume A3: "n<>1\<^sub>\<S>"
       then obtain m where
      [ty]: "m be Nat" and
       A4:  "n *\<^sub>\<S>\<^sup>\<nat> m = p" using div A2 by ty_auto
       then have "n divides 1\<^sub>\<S> or m divides 1\<^sub>\<S>" using A1 by ty_auto
       then have "m=1\<^sub>\<S>" using div_one A3 by ty_auto
       then show "n=p" using Mult_5 A4 by ty_auto
     qed
     then show "n = 1\<^sub>\<S> or n = p" by blast
  qed mauto
   qed ty_auto
qed


mtheorem
  "2\<^sub>\<S> is primeS"  
proof(standard,auto)
  show "1\<^sub>\<S> in 2\<^sub>\<S>" using ordinal1_th_2 by mauto
  fix n assume [ty]:"n be natural" "n be set"
  assume  A1: "n divides 2\<^sub>\<S>" "n \<noteq> 2\<^sub>\<S>"
  hence "n c= 2\<^sub>\<S>"  using div_2 A1 by ty_auto
  hence "n \<subset> 2\<^sub>\<S>" using A1 xboole_0_def_8 by ty_auto  
  hence " n in 2\<^sub>\<S>" using ordinal1_th_7 by ty_auto
  hence A2: "n in 1\<^sub>\<S> or n=1\<^sub>\<S>" using ordinal1_th_4 by mauto
  have "not n in 1\<^sub>\<S>"
  proof
    assume "n in 1\<^sub>\<S>"
    hence " n in {} or n ={}" using ordinal1_th_4 by mauto 
    hence "n={}" using xb by auto
    thus "False" using div_2 A1 by mauto
  qed    
  thus "n=1\<^sub>\<S>" using A2 by simp
qed ty_auto
  
  
text_raw {*\DefineSnippet{CompleteInduction}{*}
theorem CompleteInduction:
  assumes [ty]: "a is Nat"
    and A1: "\<forall>n : Nat. (\<forall>m: Nat. m \<subset> n  \<longrightarrow> P(m)) \<longrightarrow> P(n)"
  shows "P(a)"
text_raw {*}%EndSnippet*}
proof-
  let ?R="\<lambda>it. for m be Nat st m c= it holds P(m)"
  have R0: "?R({})"
  proof(infer_ty, standard,standard)
    fix m assume "m be Nat" "m c= {}" 
    hence "m c= {}" "{} c= m" using xboole_0_def_8 xb tarski_def_3I all_set by auto
    hence M:"m={}" using xboole_0_def_10 all_set by auto 
    have "\<forall>n: Nat. n c< {}  \<longrightarrow> P(n)" 
      proof(standard,standard)
        fix n assume "n be Nat" "n c< {}" 
        hence "n c= {}" "n<>{}" "{} c= n" using xboole_0_def_8 xb tarski_def_3I all_set by auto
        thus "P(n)" using xboole_0_def_10 all_set by auto   
      qed mauto
    thus "P(m)" using A1 M by ty_auto
      (* Confusing: if we remove the infer_ty call on line 950 and put it in the line above,
         the proof doesn't go through, even though the contents of [ty] are the same... *)
  qed mauto
  have Rn:"\<forall>n : Nat. ?R(n) \<longrightarrow> ?R(succ n)"
  proof(standard,standard,standard,standard)
    fix n m assume [ty]:"n be Nat"
    assume B1: "\<forall>m : Nat. m \<subseteq> n \<longrightarrow> P(m)"
    assume [ty]:"m be Nat"
    assume B2:"m c= succ n"
    have  "m in succ n or succ n c= m" using ordinal1_th_12[of m "succ n"] by infer_auto
    hence "m in succ n or succ n = m" using B2 xboole_0_def_10 all_set by auto
    hence P1: "m c= n or succ n = m" using ordinal1_th_18 by ty_auto
    have "\<forall>k: Nat. k c< succ n  \<longrightarrow> P(k)"
    proof(standard,standard)
      fix k assume [ty]:"k be Nat"
      have [ty]:"k is Ordinal" "n is Ordinal" by mauto
      assume  L: "k c< succ n"    
      have  "k in succ n or succ n c= k" using ordinal1_th_12[of k "succ n"] by infer_auto
      hence "k in succ n" using L xboole_0_def_8 xboole_0_def_10 by infer_auto
      hence OR: "k in n or k in {n}" using ordinal1_def_1 xboole_0_def_3 by infer_auto
      have or1: "k in n \<longrightarrow> P(k)"
      proof
        assume "k in n"
        hence "k c= n" using ordinal1_def_2[of n] by ty_auto
        thus "P(k)" using B1 by ty_simp    
      qed
      have "k in {n} \<longrightarrow> P(k)"
      proof
        assume "k in {n}"
        hence K: "k=n" using tarski_def_1 by auto   
        have "(\<forall>m: Nat. m c< n  \<longrightarrow> P(m))" using  B1 xboole_0_def_8 by ty_auto
        thus "P(k)" using A1 K by ty_auto
      qed
      thus "P(k)" using or1 OR by auto   
    qed mauto
    hence "P(succ n)" using A1 by infer_auto
    thus "P(m)" using P1 B1 by ty_auto
  qed mauto
  have "?R(a)" "a c= a" using  ordinal_2_sch_19[of a ?R,OF _ R0 Rn] xboole_0_def_10 all_set by ty_auto
  thus "P(a)" by ty_simp    
qed    

end  
 
